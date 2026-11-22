// Tiny stack VM: a faithful interpreter of make.fun's tiny stack ISA v1.
// Reads every /input/<id>/program.bin + input.bin, writes /output/<id>/stdout.bin
// and /output/<id>/exit.txt. Hand-written, no dependencies, deterministic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per opcode: immediate bytes, values popped, values pushed.
const SPEC: [number, number, number, number][] = [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0],
  [0x04, 0, 1, 2], [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1],
  [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1],
  [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1],
  [0x21, 0, 2, 1], [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0],
  [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0], [0x40, 0, 1, 1],
  [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1],
  [0x53, 0, 1, 0],
];
const IMM = new Uint8Array(256);
const POP = new Uint8Array(256);
const PSH = new Uint8Array(256);
const OK = new Uint8Array(256);
for (const [op, imm, pops, pushes] of SPEC) {
  IMM[op] = imm; POP[op] = pops; PSH[op] = pushes; OK[op] = 1;
}

function run(p: Uint8Array, inp: Uint8Array): [Uint8Array, number] {
  const S = new Int32Array(256); // data stack
  const K = new Int32Array(64); // call stack (return addresses)
  const M = new Int32Array(256); // memory words
  const out = new Uint8Array(65536);
  let sp = 0, kp = 0, ip = 0, pc = 0, steps = 0, olen = 0;
  const done = (code: number): [Uint8Array, number] => [out.subarray(0, olen), code];
  for (;;) {
    if (steps === 1000000) return done(10); // step limit
    if (pc < 0 || pc >= p.length) return done(9); // pc outside program
    const op = p[pc];
    if (!OK[op]) return done(5); // unknown opcode
    const imm = IMM[op];
    if (pc + imm >= p.length) return done(9); // immediate cut off
    steps++;
    const next = pc + 1 + imm;
    const pops = POP[op], pushes = PSH[op];
    if (sp < pops) return done(2); // stack underflow
    if (sp - pops + pushes > 256) return done(3); // stack overflow
    pc = next;
    switch (op) {
      case 0x00: return done(0); // HALT
      case 0x01: S[sp++] = (p[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: // PUSH32, little-endian signed
        S[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24);
        break;
      case 0x03: sp--; break; // POP
      case 0x04: S[sp] = S[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; } // SWAP
      case 0x06: S[sp] = S[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break; } // ROT
      case 0x17: S[sp - 1] = -S[sp - 1] | 0; break; // NEG (wraps)
      case 0x1b: S[sp - 1] = ~S[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = S[sp - 1], a = S[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b); // exact low 32 bits
        else if (op === 0x13) {
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0; // remainder keeps a's sign
        } else if (op === 0x15) {
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0; // unsigned
        } else if (op === 0x16) {
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0; // unsigned
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31); // arithmetic
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0; // logical
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
        sp -= 2;
        S[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        const take = op === 0x30 || (op === 0x31) === (S[--sp] === 0);
        if (take) pc = next + rel; // target unchecked; traps 9 next step if outside
        break;
      }
      case 0x33: // CALL
        if (kp === 64) return done(7);
        K[kp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34: // RET
        if (kp === 0) return done(8);
        pc = K[--kp];
        break;
      case 0x40: { // LOAD
        const addr = S[sp - 1];
        if (addr < 0 || addr >= 256) return done(6);
        S[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE (v addr --)
        const addr = S[sp - 1], v = S[sp - 2];
        if (addr < 0 || addr >= 256) return done(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no newline
        const s = String(S[sp - 1]);
        if (olen + s.length > 65536) return done(11); // writes nothing
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC: low byte
        if (olen + 1 > 65536) return done(11);
        out[olen++] = S[--sp] & 255;
        break;
      case 0x52: // IN: -1 once input is used up
        S[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: return done(S[--sp] & 255); // EXIT: low byte
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const prog = new Uint8Array(readFileSync(join(I, id, 'program.bin')));
  let inp = new Uint8Array(0);
  try { inp = new Uint8Array(readFileSync(join(I, id, 'input.bin'))); } catch { /* no input: IN reads -1 */ }
  const [out, code] = run(prog, inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
