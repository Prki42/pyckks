#!/usr/bin/env python
from __future__ import annotations

import copy
import random
import secrets
from collections.abc import Sequence
from dataclasses import dataclass
from math import cos, exp, log2, pi, sin, sqrt
from typing import overload, override

type Numeric = complex | float | int


def complex_exp(x: complex) -> complex:
    return exp(x.real) * complex(cos(x.imag), sin(x.imag))


def poly_eval(coefs: Sequence[Numeric], p: Numeric) -> Numeric:
    return sum(c * (p**i) for i, c in enumerate(coefs))


def inner_product(a: Sequence[complex], b: Sequence[complex]) -> complex:
    return sum(x * y.conjugate() for x, y in zip(a, b))


def norm(a: Sequence[complex]) -> float:
    return sqrt(inner_product(a, a).real)


def distance(a: Sequence[complex], b: Sequence[complex]) -> float:
    return norm([x - y for x, y in zip(a, b)])


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
                res[k] -= a[i] * b[j]
    return res


# Currently replaces HWT and ZO from the original paper
def sample_ternary(n: int) -> list[int]:
    return [random.choice([-1, 0, 1]) for _ in range(n)]


def sample_noise(n: int, sigma: float = 3.2) -> list[int]:
    return [int(round(random.gauss(0, sigma))) for _ in range(n)]


def sample_uniform_mod(n: int, modulus: int) -> list[int]:
    return [secrets.randbelow(modulus) for _ in range(n)]


def random_msg(n: int) -> list[complex]:
    assert n > 0

    minval = -100
    maxval = 100

    return [
        complex(random.uniform(minval, maxval), random.uniform(minval, maxval))
        for _ in range(n)
    ]


class PolyRingQ(Sequence[int]):
    def __init__(self, coefs: list[int], modulus: int):
        self.coefs: list[int] = list(coefs)
        self.N: int = len(self.coefs)
        self.modulus: int = modulus
        self.reduce_mod()

    def reduce_mod(self) -> None:
        self.coefs[:] = [symmetric_mod(x, self.modulus) for x in self.coefs]

    def change_mod(self, new_modulus: int) -> None:
        self.modulus = new_modulus
        self.reduce_mod()

    @override
    def __str__(self) -> str:
        return f"PolyRingQ{{{self.coefs}, log2(q): {log2(self.modulus)}}}"

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

    def scale_down_by(self, factor: int) -> None:
        self.coefs[:] = [x // factor for x in self.coefs]

    def scale_up_by(self, factor: int) -> None:
        self.coefs[:] = [x * factor for x in self.coefs]

    def negate(self) -> None:
        self.coefs[:] = [symmetric_mod(-x, self.modulus) for x in self.coefs]

    def __neg__(self) -> PolyRingQ:
        res = PolyRingQ(self.coefs, self.modulus)
        res.negate()
        return res

    @overload
    def __getitem__(self, index: int) -> int: ...
    @overload
    def __getitem__(self, index: slice) -> Sequence[int]: ...
    @override
    def __getitem__(self, index: int | slice) -> int | Sequence[int]:
        return self.coefs[index]

    @override
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


@dataclass
class CKKSParams:
    N: int
    ql: list[int]
    n_of_levels: int
    scale: int
    P: int


def paramsgen(n: int) -> CKKSParams:
    scale = 3926640043
    q = 68098092032511344671558473187653224988251802726347
    n_of_levels = 5

    ql: list[int] = [q] * n_of_levels
    for i in range(1, n_of_levels):
        ql[i] = ql[i - 1] * scale

    P = ql[-1] * 2

    return CKKSParams(1 << n, ql, n_of_levels, scale, P)


type Plaintext = PolyRingQ

# s
type PrivateKey = PolyRingQ

# (b, a)
type PublicKey = tuple[PolyRingQ, PolyRingQ]

# (b', a')
type EvalKey = tuple[PolyRingQ, PolyRingQ]


def keygen(params: CKKSParams) -> tuple[PrivateKey, PublicKey, EvalKey]:
    qL = params.ql[-1]
    N = params.N
    P = params.P

    s = PolyRingQ(sample_ternary(N), qL)
    a = PolyRingQ(sample_uniform_mod(N, qL), qL)
    e = PolyRingQ(sample_noise(N), qL)
    b = e - (a * s)

    ap = PolyRingQ(sample_uniform_mod(N, qL * P), qL * P)
    ep = PolyRingQ(sample_noise(N), qL * P)

    Ps2 = s * s
    Ps2.change_mod(qL * P)
    Ps2.scale_up_by(params.P)

    bp = ep + Ps2 - (ap * s)

    return (s, (b, a), (bp, ap))


def encrypt(p: Plaintext, pk: PublicKey, params: CKKSParams) -> Ciphertext:
    N = p.N
    q = p.modulus
    e0 = PolyRingQ(sample_noise(N), q)
    e1 = PolyRingQ(sample_noise(N), q)
    v = PolyRingQ(sample_ternary(N), q)
    (b, a) = pk

    c = ((v * b) + p + e0, (v * a) + e1)

    return Ciphertext(c, params.n_of_levels - 1, params)


class Ciphertext:
    def __init__(
        self, value: tuple[PolyRingQ, PolyRingQ], level: int, params: CKKSParams
    ):
        self.value: tuple[PolyRingQ, PolyRingQ] = value
        self.level: int = level
        self.params: CKKSParams = params

        assert value[1].modulus == value[0].modulus

    def decrypt(self, s: PrivateKey) -> Plaintext:
        return self.value[0] + (self.value[1] * s)

    def rescale(self) -> None:
        assert self.level > 0

        self.level -= 1
        modulus = self.params.ql[self.level]

        self.value[0].scale_down_by(self.params.scale)
        self.value[1].scale_down_by(self.params.scale)

        self.value[0].change_mod(modulus)
        self.value[1].change_mod(modulus)

    @override
    def __str__(self) -> str:
        return f"{self.value[0]} | {self.value[1]}"

    def __add__(self, other: Ciphertext) -> Ciphertext:
        assert type(other) is Ciphertext
        assert other.level == self.level

        res = Ciphertext(copy.deepcopy(self.value), self.level, self.params)
        res.value[0].add(other.value[0])
        res.value[1].add(other.value[1])

        return res

    def mul(self, other: Ciphertext, evk: EvalKey) -> Ciphertext:
        assert type(other) is Ciphertext
        assert other.level == self.level

        d0 = self.value[0] * other.value[0]
        d1 = (self.value[0] * other.value[1]) + (self.value[1] * other.value[0])
        d2 = self.value[1] * other.value[1]

        (bp, ap) = evk

        P = self.params.P

        d2.change_mod(bp.modulus)

        c0 = d2 * bp
        c0.scale_down_by(P)
        c0 += d0

        c1 = d2 * ap
        c1.scale_down_by(P)
        c1 += d1

        res = Ciphertext((c0, c1), self.level, self.params)
        res.rescale()
        return res


# CIPHERTEXT ADD
#
# c  = (c1,  c2 )
# c' = (c1', c2')
#
# Dec(c+c') = Dec(c) + Dec(c')
#           = c1 + s*c2 + c1' + s*c2'
#           = (c1 + c2) + s*(c1' + c2')
#
# c_add := (c1+c2, c1'+c2')
#
# => Dec(c_add) = Dec(c+c')


# CONSTANT ADD/MUL
#
# c = (c1, c2)
# p plaintext
#
# ----------------------------
#
# Dec(c + p) = Dec(c) + p = c1 + p + s*c2
#
# => c_addconst = (c1 + p, c2)
#
# ----------------------------
#
# Dec(c*p) = Dec(c)*p = (c1 + s*c2)*p
#          = c1*p + s*c2*p
#
# => c_mulconst = (c1*p, c2*p)
#
# Requires rescale


# CIPHERTEXT MUL
#
# c  = (c1,  c2 )
# c' = (c1', c2')
#
# Dec(c*c') = Dec(c)*Dec(c') = (c1 + s*c2)*(c1' + s*c2')
#           = c1*c1' + s*(c1*c2' + c2*c1') + (s^2)*(c2*c2')
#
# d0 := c1*c1'
# d1 := c1*c2' + c2*c1'
# d2 := c2*c2'
#
# => Dec(c*c') = d0 + s*d1 + (s^2)*d2
#
# We want (s^2)*d2 "≈" g0 + s*g1 for some g0, g1
#
# a' <- R_q
# e' <- DG(sigma^2)
# b' := -a'*s + e' + P*(s^2)  (mod P*q)
#
# c_mul := (d0, d1) + [Pinv * d2 * (b', a')]
#        ≈ (d0 + Pinv * d2 * b', d1 + Pinv * d2 * a')
#        = (d0 + Pinv * d2 * (-a'*s + e' + P*s^2), d1 + Pinv * d2 * a')
#        = (d0 + d2*s^2 + Pinv*d2*(-a'*s + e'), d1 + Pinv * d2 * a')
#
# => Dec(c_mul) = d0 + (s^2)*d2 + Pinv*d2*(-a'*s + e') + s*(d1 + Pinv*d2*a')
#               = d0 + (s^2)*d2 + Pinv*d2*e' + s*d1
#               = d0 + s*d1 + (s^2)*d2 + Pinv*d2*e'
#               ≈ Dec(c*c')
#
# Dec(c_mult) - Dec(c*c') ≈ Pinv*d2*e'
#
# Comment: If P=1 then Pinv*d2*e' would be d2*e' which can be "large"
#          (since d2 can be).
#          For that reason: log P ≈ log q
#
# evk := (b', a')  <->  "evaluation key"
#                       precomputed and used for (every) relinearization
#
# Requires rescale!


class Encoder:
    def __init__(self, n: int, delta: int):
        self.N: int = 2**n
        self.M: int = 2 * self.N
        self.delta: int = delta

        zeta: complex = complex_exp(complex(0, -2 * pi / self.M))
        self.roots: list[complex] = [zeta**i for i in range(1, self.M, 2)]

        assert len(self.roots) == self.N

        self.poly_basis: list[list[int]] = [
            [1 if i == j else 0 for j in range(0, self.N)] for i in range(0, self.N)
        ]

        self.lattice_basis: list[list[complex]] = [
            self.sigma(p) for p in self.poly_basis
        ]

    def sigma(self, a: Sequence[int | float]) -> list[complex]:
        assert len(a) == self.N
        return [poly_eval(a, r) for r in self.roots]

    def decode(self, a: Sequence[int]) -> list[complex]:
        return self.sigma([x / self.delta for x in a])[: self.N // 2]

    def conjugate_extend(self, m: Sequence[complex]) -> list[complex]:
        return list(m) + [x.conjugate() for x in reversed(m)]

    def encode(self, m: Sequence[complex]) -> list[int]:
        assert len(m) == self.N // 2
        m = [x * self.delta for x in self.conjugate_extend(m)]
        return [
            round(inner_product(m, x).real / inner_product(x, x).real)
            for x in self.lattice_basis
        ]


def main():
    n = 2
    params = paramsgen(n)
    enc = Encoder(n, params.scale)

    # N = 2^n
    N = params.N
    qL = params.ql[-1]

    # # Example from the paper
    # m = [3 + 4j, 2 - 1j]
    # p = enc.encode(m)
    # m_rec = enc.decode(p)
    # print(p)
    # print(m_rec)

    m1 = random_msg(N // 2)
    m2 = random_msg(N // 2)

    p1 = PolyRingQ(enc.encode(m1), qL)
    p2 = PolyRingQ(enc.encode(m2), qL)

    (s, pk, evk) = keygen(params)

    c1 = encrypt(p1, pk, params)
    c2 = encrypt(p2, pk, params)

    c_add = c1 + c2
    c_mul = c1.mul(c2, evk)

    p_add = c_add.decrypt(s)
    p_mul = c_mul.decrypt(s)

    m_add_dec = enc.decode(p_add)
    m_mul_dec = enc.decode(p_mul)

    m_add_exp = [a + b for a, b in zip(m1, m2)]
    m_mul_exp = [a * b for a, b in zip(m1, m2)]

    print("ADDITION")
    print(f"Got: {m_add_dec}")
    print(f"Expected: {m_add_exp}")
    print(f"Err: {distance(m_add_dec, m_add_exp)}")

    print("\n\nMULTIPLICATION")
    print(f"Got: {m_mul_dec}")
    print(f"Expected: {m_mul_exp}")
    print(f"Err: {distance(m_mul_dec, m_mul_exp)}")


if __name__ == "__main__":
    main()
