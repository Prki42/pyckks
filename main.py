#!/usr/bin/env python
from __future__ import annotations
import copy
from dataclasses import dataclass

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


def sample_noise(n: int, sigma=3.2):
    return [int(round(random.gauss(0, sigma))) for _ in range(n)]


def sample_uniform_mod(n: int, modulus: int):
    return [secrets.randbelow(modulus) for _ in range(n)]


def random_msg(n: int) -> list[complex]:
    assert n > 0

    # minval = -1_000
    # maxval = 1_000

    minval = -10
    maxval = 10

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

    def setcoefs(self, coefs: list[int]) -> None:
        self.coefs = list(coefs)

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

    def add(self, other: PolyRingQ) -> PolyRingQ:
        self.coefs[:] = [
            symmetric_mod(p[0] + p[1], self.modulus)
            for p in zip(self.coefs, other.coefs)
        ]
        return self

    def mul(self, other: PolyRingQ) -> PolyRingQ:
        self.coefs[:] = [
            symmetric_mod(x, self.modulus)
            for x in poly_ring_product(self.coefs, other.coefs)
        ]
        return self

    def scale_down_by(self, factor: int) -> PolyRingQ:
        self.coefs[:] = [x // factor for x in self.coefs]
        return self

    def scale_up_by(self, factor: int) -> PolyRingQ:
        self.coefs[:] = [x * factor for x in self.coefs]
        return self

    def negate(self) -> PolyRingQ:
        self.coefs[:] = [symmetric_mod(-x, self.modulus) for x in self.coefs]
        return self

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


@dataclass(repr=True, init=True)
class CKKSParams:
    N: int
    ql: list[int]
    n_of_levels: int
    delta: int
    P: int


def paramsgen(n: int) -> CKKSParams:
    delta = 2**60
    q = 88570805546739013601
    n_of_levels = 5

    ql: list[int] = [q] * n_of_levels
    for i in range(1, n_of_levels):
        ql[i] = ql[i - 1] * delta

    P = 94322762397470840257

    return CKKSParams(2**n, ql, n_of_levels, delta, P)


type Plaintext = PolyRingQ

# s
type PrivateKey = PolyRingQ

# (b, a)
type PublicKey = tuple[PolyRingQ, PolyRingQ]

# (b', a')
type EvalKey = tuple[PolyRingQ, PolyRingQ]


# a' <- R_q
# e' <- DG(sigma^2)
# b' := -a'*s + e' + P*(s^2)  (mod P*q)
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
    Ps2.modulus = qL * P
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
        self.level = level
        self.modulus = params.ql[level]
        self.params = params

        assert self.modulus == value[0].modulus
        assert self.modulus == value[1].modulus

    def decrypt(self, s: PrivateKey) -> Plaintext:
        return self.value[0] + (self.value[1] * s)

    def rescale(self) -> None:
        assert self.level > 0

        self.level -= 1
        self.modulus = self.params.ql[self.level]

        self.value[0].scale_down_by(self.params.delta)
        self.value[1].scale_down_by(self.params.delta)

    def __str__(self) -> str:
        return self.value[0].__str__() + " | " + self.value[1].__str__()

    def __add__(self, other: Ciphertext) -> Ciphertext:
        assert type(other) is Ciphertext
        assert other.level == self.level

        res = Ciphertext(copy.deepcopy(self.value), self.level, self.params)
        res.value[0].add(other.value[0])
        res.value[1].add(other.value[1])

        return res

    # d0 := c1*c1'
    # d1 := c1*c2' + c2*c1'
    # d2 := c2*c2'

    def mul(self, other: Ciphertext, evk: EvalKey) -> Ciphertext:
        assert type(other) is Ciphertext
        assert other.level == self.level

        d0 = self.value[0] * other.value[0]
        d1 = self.value[0] * other.value[1] + self.value[1] * other.value[0]
        d2 = self.value[1] * other.value[1]

        (bp, ap) = evk

        # c_mul := (d0, d1) + [Pinv * d2 * (b', a')]

        P = self.params.P

        d2.modulus = bp.modulus
        c0 = d0 + (d2 * bp).scale_down_by(P)
        c1 = d1 + (d2 * ap).scale_down_by(P)

        self.value = (c0, c1)
        self.rescale()

        return self


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
# Requires rescale (i guess?)


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
# Note: Multiplying by P is not ring multiplication,
#       but scaling of coefficients by P. Multuplying by Pinv
#       is just dividing coefficients by P and rounding
#
# evk := (b', a')  <->  "evaluation key"
#                       precomputed and used for (every) relinearization
#
# Requires rescale!


class Ecnoder:
    def __init__(self, n: int):
        self.N = 2**n
        self.M = 2 * self.N

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

    def decode(self, a: Sequence[int], delta: int) -> list[complex]:
        a = list(map(lambda x: x / delta, a))
        return self.sigma(a)[0 : self.N // 2]

    def conjugate_extend(self, m: Sequence[complex]) -> list[complex]:
        return list(m) + list(map(lambda x: x.conjugate(), m[::-1]))

    def encode(self, m: Sequence[complex], delta: int) -> list[int]:
        assert len(m) == self.N // 2
        m = list(map(lambda x: x * delta, self.conjugate_extend(m)))
        return list(
            map(
                lambda x: round(inner_product(m, x).real / inner_product(x, x).real),
                self.lattice_basis,
            )
        )


# ----- TODO -----
# Bootstrapping
# RNS
# ----------------


def main():
    n = 2
    params = paramsgen(n)
    delta = params.delta
    levels = params.n_of_levels
    enc = Ecnoder(2)

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

    p1 = PolyRingQ(enc.encode(m1, delta ** (levels)), qL)
    p2 = PolyRingQ(enc.encode(m2, delta ** (levels)), qL)

    (s, pk, evk) = keygen(params)

    c1 = encrypt(p1, pk, params)
    c2 = encrypt(p2, pk, params)

    c_add = c1 + c2
    c_mul = c1.mul(c2, evk)

    p_add = c_add.decrypt(s)
    p_mul = c_mul.decrypt(s)

    m_add_dec = enc.decode(p_add, delta ** (c_add.level + 1))
    m_mul_dec = enc.decode(p_mul, delta ** (c_mul.level + 1))

    m_add_exp = list(map(lambda x: x[0] + x[1], zip(m1, m2)))
    m_mul_exp = list(map(lambda x: x[0] * x[1], zip(m1, m2)))

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
