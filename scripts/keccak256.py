#!/usr/bin/env python3
"""Compute Solidity-style function selectors (keccak256, first 4 bytes).

Usage:
  keccak256.py "transfer(address,uint256)" "balanceOf(address)"

Outputs one selector per line as 0xXXXXXXXX.
"""

import sys
from typing import List

# Keccak-f[1600] parameters
RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]

R = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
]

MASK64 = (1 << 64) - 1


def _rotl(x: int, n: int) -> int:
    return ((x << n) & MASK64) | (x >> (64 - n))


def keccak_f(state: List[int]) -> None:
    for rc in RC:
        # Theta
        c = [state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rotl(c[(x + 1) % 5], 1) for x in range(5)]
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] ^= d[x]

        # Rho + Pi
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = _rotl(state[x + 5 * y], R[x][y])

        # Chi
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] = b[x + 5 * y] ^ ((~b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y])

        # Iota
        state[0] ^= rc


def keccak_256(data: bytes) -> bytes:
    rate = 1088 // 8  # 136 bytes
    state = [0] * 25

    # Absorb
    offset = 0
    while offset < len(data):
        block = data[offset:offset + rate]
        offset += rate
        if len(block) < rate:
            # Padding: 0x01 ... 0x80
            block = block + b"\x01" + b"\x00" * (rate - len(block) - 2) + b"\x80"
            last = True
        else:
            last = False

        for i in range(0, rate, 8):
            word = int.from_bytes(block[i:i + 8], byteorder="little")
            state[i // 8] ^= word

        keccak_f(state)
        if last:
            break

    # Squeeze
    out = bytearray()
    while len(out) < 32:
        for i in range(0, rate, 8):
            out += state[i // 8].to_bytes(8, byteorder="little")
            if len(out) >= 32:
                return bytes(out[:32])
        keccak_f(state)

    return bytes(out[:32])


def selector(sig: str) -> str:
    digest = keccak_256(sig.encode("utf-8"))
    return "0x" + digest[:4].hex()


def main() -> int:
    args = sys.argv[1:]
    if not args:
        print("Usage: keccak256.py <signature> [signature...]", file=sys.stderr)
        return 2
    for sig in args:
        print(selector(sig))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
