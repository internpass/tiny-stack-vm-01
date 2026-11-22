// A tiny stack virtual machine for make.fun's tiny-stack-vm-01: an exact interpreter of the kit's ISA
// (generator/subject/ISA.md; vm.mjs rules where the two could be read two ways), traps included.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per opcode byte: immediate bytes, values popped, values pushed; -1 marks a byte no opcode names.
const IMM = new Int8Array(256).fill(-1);
const POPN = new Int8Array(256);
const PUSHN = new Int8Array(256);
for (const [op, imm, pops, pushes] of [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0], [0x04, 0, 1, 2],
  [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3], [0x30, 2, 0, 0], [0x31, 2, 1, 0],
  [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0], [0x40, 0, 1, 1], [0x41, 0, 2, 0],
  [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1], [0x53, 0, 1, 0],
]) {
  IMM[op] = imm;
  POPN[op] = pops;
  PUSHN[op] = pushes;
}
// The arithmetic block 0x10..0x22 is all ( a b -- r ), but for NEG and NOT, ( a -- r ).
for (let op = 0x10; op <= 0x22; op++) {
  IMM[op] = 0;
  POPN[op] = 2;
  PUSHN[op] = 1;
}
POPN[0x17] = POPN[0x1b] = 1;
IMM[0x1f] = -1; // 0x1f names no opcode: it traps 5 like any other unnamed byte

function run(p: Uint8Array, inp: Uint8Array) {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const fin = (code: number) => ({ out: out.slice(0, olen), code });
  for (;;) {
    if (steps === 1000000) return fin(10);
    if (pc < 0 || pc >= n) return fin(9);
    const op = p[pc];
    const imm = IMM[op];
    if (imm < 0) return fin(5);
    if (pc + imm >= n) return fin(9);
    steps++;
    if (sp < POPN[op]) return fin(2);
    if (sp - POPN[op] + PUSHN[op] > 256) return fin(3);
    const next = pc + 1 + imm;
    pc = next;
    switch (op) {
      case 0x00: // HALT
        return fin(0);
      case 0x01: // PUSH8, sign-extended
        D[sp++] = (p[next - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32, little-endian
        D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04: // DUP
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: { // SWAP
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 0x06: // OVER
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: { // ROT
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 0x17: // NEG
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 0x1b: // NOT
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: { // binary operators: ( a b -- r )
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b); // MUL: low 32 bits of the exact product
        else if (op === 0x13) { // DIV, truncated toward zero; INT_MIN / -1 is INT_MIN
          if (b === 0) return fin(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) { // MOD, the sign of a; x % -1 is 0
          if (b === 0) return fin(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) { // DIVU: a and b read as unsigned
          if (b === 0) return fin(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) { // MODU
          if (b === 0) return fin(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31); // shift counts: the low 5 bits only
        else if (op === 0x1d) r = a >> (b & 31); // SHR arithmetic, SHRU logical
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        sp--;
        D[sp - 1] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ: target is next + signed offset
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL: push the return address, jump to the unsigned immediate
        if (csp === 64) return fin(7);
        C[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return fin(8);
        pc = C[--csp];
        break;
      case 0x40: { // LOAD
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return fin(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return fin(6);
        M[addr] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: the value in decimal ASCII
        let v = D[--sp];
        const digits: number[] = [];
        if (v === 0) digits.push(48);
        const neg = v < 0;
        while (v !== 0) {
          const d = v % 10;
          digits.push(48 + (d < 0 ? -d : d));
          v = ((v - d) / 10) | 0;
        }
        if (neg) digits.push(45);
        if (olen + digits.length > 65536) return fin(11); // past the output limit: writes nothing
        for (let i = digits.length - 1; i >= 0; i--) out[olen++] = digits[i];
        break;
      }
      case 0x51: // PUTC: one byte, v AND 255
        if (olen + 1 > 65536) return fin(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: // IN: the next input byte, -1 once the input is used up
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: // EXIT: the low byte of the value
        return fin(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
