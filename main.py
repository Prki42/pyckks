#!/usr/bin/env python
from __future__ import annotations

import random
import secrets
from collections.abc import Sequence as SequenceClass
from math import cos, exp, pi, sin, sqrt, log2
from typing import Sequence

type Numeric = complex | float | int


def complex_exp(x: complex) -> complex:
    return exp(x.real) * complex(cos(x.imag), sin(x.imag))


def poly_eval(coefs: Sequence[Numeric], p: Numeric) -> Numeric:
    return sum(map(lambda x: x[1] * (p ** x[0]), enumerate(coefs)))


def inner_product(a: Sequence[complex], b: Sequence[complex]) -> complex:
    return sum(map(lambda x: x[0] * x[1].conjugate(), zip(a, b)))


def norm(a: Sequence[complex]) -> float:
    return sqrt(inner_product(a, a).real)


def distance(a: Sequence[complex], b: Sequence[complex]) -> float:
    return norm(list(map(lambda x: x[0] - x[1], zip(a, b))))


def symmetric_mod(val: int, modulus: int) -> int:
    half = modulus // 2
    res = val % modulus
    return res - modulus if res > half else res


# Product in Z[x]\<x^n + 1>
def poly_ring_product(a: Sequence[int], b: Sequence[int]) -> list[int]:
    n = len(a)
    assert len(b) == n

    res = [0] * n
    for i in range(n):
        for j in range(n):
            if i + j < n:
                res[i + j] += a[i] * b[j]
            else:
                k = i + j - n
                res[k] += a[i] * b[j] * (-1)
    return res


# Currently replaces HWT and ZO from the original paper
def sample_ternary(n: int) -> list[int]:
    return [random.choice([-1, 0, 1]) for _ in range(n)]


# Sigma constant from Microsoft SEAL
def sample_noise(n: int, sigma=3.2):
    return [int(round(random.gauss(0, sigma))) for _ in range(n)]


def sample_uniform_mod(n: int, modulus: int):
    return [secrets.randbelow(modulus) for _ in range(n)]


def random_msg(n: int) -> list[complex]:
    assert n > 0

    minval = -1_000
    maxval = 1_000

    return [
        complex(random.uniform(minval, maxval), random.uniform(minval, maxval))
        for _ in range(n)
    ]


class PolyRingQ(SequenceClass):
    def __init__(self, coefs: list[int], modulus: int):
        self.coefs = list(coefs)
        self.N = len(self.coefs)
        self.modulus = modulus
        self._reduce_mod()

    def _reduce_mod(self) -> None:
        self.coefs[:] = [symmetric_mod(x, self.modulus) for x in self.coefs]

    def __str__(self) -> str:
        return (
            "PolyRingQ{"
            + self.coefs.__str__()
            + ", log2(q): "
            + str(log2(self.modulus))
            + "}"
        )

    def add(self, other: PolyRingQ) -> None:
        self.coefs[:] = [
            symmetric_mod(p[0] + p[1], self.modulus)
            for p in zip(self.coefs, other.coefs)
        ]

    def mul(self, other: PolyRingQ) -> None:
        self.coefs[:] = [
            symmetric_mod(x, self.modulus)
            for x in poly_ring_product(self.coefs, other.coefs)
        ]

    def negate(self) -> None:
        self.coefs[:] = [symmetric_mod(-x, self.modulus) for x in self.coefs]

    def __getitem__(self, index):
        return self.coefs[index]

    def __len__(self) -> int:
        return self.N

    def __add__(self, other: PolyRingQ) -> PolyRingQ:
        assert type(other) is PolyRingQ
        res = PolyRingQ(self.coefs, self.modulus)
        res.add(other)
        return res

    def __sub__(self, other: PolyRingQ) -> PolyRingQ:
        assert type(other) is PolyRingQ
        res = PolyRingQ(other.coefs, self.modulus)
        res.negate()
        res.add(self)
        return res

    def __mul__(self, other: PolyRingQ) -> PolyRingQ:
        assert type(other) is PolyRingQ
        res = PolyRingQ(self.coefs, self.modulus)
        res.mul(other)
        return res


type Plaintext = PolyRingQ

type PrivateKey = PolyRingQ
type PublicKey = tuple[PolyRingQ, PolyRingQ]


def keygen(modulus: int, N: int) -> tuple[PrivateKey, PublicKey]:
    s = PolyRingQ(sample_ternary(N), modulus)
    a = PolyRingQ(sample_uniform_mod(N, modulus), modulus)
    e = PolyRingQ(sample_noise(N), modulus)

    b = e - (a * s)

    return (s, (b, a))


def encrypt(p: Plaintext, pk: PublicKey) -> Ciphertext:
    N = p.N
    q = p.modulus
    e0 = PolyRingQ(sample_noise(N), q)
    e1 = PolyRingQ(sample_noise(N), q)
    v = PolyRingQ(sample_ternary(N), q)
    (b, a) = pk

    c = ((v * b) + p + e0, (v * a) + e1)

    return Ciphertext(c, 0)


class Ciphertext:
    def __init__(self, value: tuple[PolyRingQ, PolyRingQ], level: int):
        self.value = value
        self.modulus = value[0].modulus
        self.level = level

    def decrypt(self, s: PrivateKey) -> Plaintext:
        return self.value[0] + (self.value[1] * s)

    def __str__(self) -> str:
        return self.value[0].__str__() + " | " + self.value[1].__str__()

    def __add__(self, other: Ciphertext) -> Ciphertext:
        assert type(other) is Ciphertext
        res = Ciphertext(self.value, self.level)
        res.value[0].add(other.value[0])
        res.value[1].add(other.value[1])
        return res


class Ecnoder:
    def __init__(self, n: int, delta: float):
        self.N = 2**n
        self.M = 2 * self.N
        self.delta = delta

        zeta: complex = complex_exp(complex(0, -2 * pi / self.M))
        self.roots: list[complex] = list(map(lambda i: zeta**i, range(1, self.M, 2)))

        assert len(self.roots) == self.N

        self.poly_basis: list[list[int]] = [
            [1 if i == j else 0 for j in range(0, self.N)] for i in range(0, self.N)
        ]

        self.lattice_basis: list[list[complex]] = list(map(self.sigma, self.poly_basis))

    def sigma(self, a: Sequence[int]) -> list[complex]:
        assert len(a) == self.N
        return list(map(lambda r: poly_eval(a, r), self.roots))

    def decode(self, a: Sequence[int]) -> list[complex]:
        a = list(map(lambda x: x / self.delta, a))
        return self.sigma(a)[0 : self.N // 2]

    def conjugate_extend(self, m: Sequence[complex]) -> list[complex]:
        return list(m) + list(map(lambda x: x.conjugate(), m[::-1]))

    def encode(self, m: Sequence[complex]) -> list[int]:
        assert len(m) == self.N // 2
        m = list(map(lambda x: x * self.delta, self.conjugate_extend(m)))
        return list(
            map(
                lambda x: round(inner_product(m, x).real / inner_product(x, x).real),
                self.lattice_basis,
            )
        )


def main():
    enc = Ecnoder(2, 2**40)
    N: int = enc.N

    # # Example from the paper
    # m = [3 + 4j, 2 - 1j]
    # p = enc.encode(m)
    # m_rec = enc.decode(p)
    # print(p)
    # print(m_rec)

    m1 = random_msg(enc.N // 2)
    m2 = random_msg(enc.N // 2)

    q = 3656693795042607789140164492751593724976092146573208355242015434624228226595185798866687250879120069

    p1 = PolyRingQ(enc.encode(m1), q)
    p2 = PolyRingQ(enc.encode(m2), q)

    (s, pk) = keygen(q, N)

    c1 = encrypt(p1, pk)
    c2 = encrypt(p2, pk)
    c = c1 + c2

    p = c.decrypt(s)

    m_dec = enc.decode(p)
    m_exp = list(map(lambda x: x[0] + x[1], zip(m1, m2)))

    print(f"Got: {m_exp}")
    print(f"Expected: {m_dec}")
    print(f"Err: {distance(m_dec, m_exp)}")


if __name__ == "__main__":
    main()
