// Tiny stack VM, Builder B (Heri). Table-driven dispatch, trap via throw.
// Reads /input/<id>/program.bin + input.bin, writes /output/<id>/stdout.bin + exit.txt.
// ISA: 32-bit wrapping ints, data stack 256, call stack 64, memory 256 words.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Immediate length per opcode (0 unless listed).
const IMM = new Uint8Array(256);
IMM[0x01] = 1; IMM[0x02] = 4;
IMM[0x30] = 2; IMM[0x31] = 2; IMM[0x32] = 2; IMM[0x33] = 2;

function run(prog, input) {
  const st = new Int32Array(256);
  let sp = 0;
  const cs = new Int32Array(64);
  let cp = 0;
  const mem = new Int32Array(256);
  const out = [];
  let pc = 0;
  let ip = 0;
  let steps = 0;
  // Trap: throw the trap code; the caller keeps prior output.
  const T = (c) => { throw c; };
  const need = (n) => { if (sp < n) T(2); };
  const push = (v) => { if (sp >= 256) T(3); st[sp++] = v | 0; };
  const pop = () => { need(1); return st[--sp]; };
  const peek = () => { need(1); return st[sp - 1]; };
  const outByte = (b) => { if (out.length >= 65536) T(11); out.push(b & 255); };
  const outText = (s) => { if (out.length + s.length > 65536) T(11); for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i)); };
  const u32 = (v) => v >>> 0;
  let done = -1;
  // Binary op: pop b (top) then a, push f(a,b). Traps inside f propagate.
  const bin = (f) => { const b = pop(); const a = pop(); push(f(a, b)); };
  const divTrap = (a, b) => { if (b === 0) T(4); return a; };
  // Dispatch table: opcode -> handler(nxt, i0, i1, i2, i3).
  const H = new Array(256);
  H[0x00] = () => { done = 0; };
  H[0x01] = (n, i0) => { push(i0 >= 128 ? i0 - 256 : i0); };
  H[0x02] = (n, i0, i1, i2, i3) => { push(i0 | (i1 << 8) | (i2 << 16) | (i3 << 24)); };
  H[0x03] = () => { pop(); };
  H[0x04] = () => { push(peek()); };
  H[0x05] = () => { need(2); const a = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = a; };
  H[0x06] = () => { need(2); push(st[sp - 2]); };
  H[0x07] = () => { need(3); const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; };
  H[0x10] = () => bin((a, b) => (a + b) | 0);
  H[0x11] = () => bin((a, b) => (a - b) | 0);
  H[0x12] = () => bin((a, b) => Math.imul(a, b));
  H[0x13] = () => bin((a, b) => { divTrap(a, b); return a === -2147483648 && b === -1 ? -2147483648 : (a / b | 0); });
  H[0x14] = () => bin((a, b) => { divTrap(a, b); return a % b | 0; });
  H[0x15] = () => bin((a, b) => { divTrap(a, b); return Math.floor(u32(a) / u32(b)) | 0; });
  H[0x16] = () => bin((a, b) => { divTrap(a, b); return (u32(a) % u32(b)) | 0; });
  H[0x17] = () => { push((-pop()) | 0); };
  H[0x18] = () => bin((a, b) => a & b);
  H[0x19] = () => bin((a, b) => a | b);
  H[0x1a] = () => bin((a, b) => a ^ b);
  H[0x1b] = () => { push(~pop()); };
  H[0x1c] = () => bin((a, b) => a << (b & 31));
  H[0x1d] = () => bin((a, b) => a >> (b & 31));
  H[0x1e] = () => bin((a, b) => (a >>> (b & 31)) | 0);
  H[0x20] = () => bin((a, b) => (a === b ? 1 : 0));
  H[0x21] = () => bin((a, b) => (a < b ? 1 : 0));
  H[0x22] = () => bin((a, b) => (u32(a) < u32(b) ? 1 : 0));
  const off = (i0, i1) => { let o = i0 | (i1 << 8); return o >= 32768 ? o - 65536 : o; };
  H[0x30] = (n, i0, i1) => { pc = n + off(i0, i1); };
  H[0x31] = (n, i0, i1) => { if (pop() === 0) pc = n + off(i0, i1); };
  H[0x32] = (n, i0, i1) => { if (pop() !== 0) pc = n + off(i0, i1); };
  H[0x33] = (n, i0, i1) => { if (cp >= 64) T(7); cs[cp++] = n; pc = i0 | (i1 << 8); };
  H[0x34] = () => { if (cp === 0) T(8); pc = cs[--cp]; };
  H[0x40] = () => { const a = pop(); if (a < 0 || a > 255) T(6); push(mem[a]); };
  H[0x41] = () => { const a = pop(); const v = pop(); if (a < 0 || a > 255) T(6); mem[a] = v | 0; };
  H[0x50] = () => { outText(String(pop())); };
  H[0x51] = () => { outByte(pop()); };
  H[0x52] = () => { push(ip < input.length ? input[ip++] : -1); };
  H[0x53] = () => { done = pop() & 255; };
  try {
    while (done < 0) {
      if (steps >= 1000000) T(10);
      if (pc < 0 || pc >= prog.length) T(9);
      const op = prog[pc];
      const h = H[op];
      if (!h) T(5);
      const imm = IMM[op];
      if (pc + 1 + imm > prog.length) T(9);
      const nxt = pc + 1 + imm;
      const i0 = prog[pc + 1] | 0, i1 = prog[pc + 2] | 0, i2 = prog[pc + 3] | 0, i3 = prog[pc + 4] | 0;
      steps++;
      pc = nxt;
      h(nxt, i0, i1, i2, i3);
    }
    return { exit: done, out };
  } catch (e) {
    if (typeof e === 'number') return { exit: e, out };
    throw e;
  }
}

for (const id of readdirSync(I).sort()) {
  const prog = readFileSync(join(I, id, 'program.bin'));
  const input = readFileSync(join(I, id, 'input.bin'));
  const r = run(prog, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), Buffer.from(r.out));
  writeFileSync(join(O, id, 'exit.txt'), String(r.exit) + '\n');
}
