#!/usr/bin/env python3
"""
R003 — A5^r satisfies the Herzog–Schönheim conjecture for every r.

The result rests on one exact number: the reciprocal mass of the multiplicative
monoid of subgroup indices of A5,

    M(A5) = <5, 6, 10, 12, 15, 20>,        sum_{m in M(A5)} 1/m = 11463/5852,

which is below 2. That gives J(A5^r) <= 1 + (11463/5852 - 1) < 2 for every r at
once, and the published criterion (Garonzi–Margolis, arXiv:2509.25118,
Lemma 2.1(1): J(G) < 2 implies G is HS) then settles every power.

This script checks that number three ways, in exact rational arithmetic.

Run: python3 verify/R003.py
"""

from fractions import Fraction as F

GENERATORS = [5, 6, 10, 12, 15, 20]
A5_SUBGROUP_ORDERS = [1, 2, 3, 4, 5, 6, 10, 12, 60]
CLAIMED_MASS = F(11463, 5852)
ENUM_BOUND = 10 ** 12
FAILURES = []


def check(name, condition, detail=""):
    print(("PASS " if condition else "FAIL ") + name + (f" :: {detail}" if detail else ""))
    if not condition:
        FAILURES.append(name)


def kappa_closed(i, j):
    return (j - i) if j > i else max(0, (i + 1) // 2 - j)


def kappa_brute(i, j):
    best = None
    for b in range(j + 1):
        for d in range(j - b + 1):
            for f in range((i - b - 2 * d) // 2 + 1):
                if b + 2 * d + 2 * f <= i:
                    k = i + j - 2 * b - 3 * d - f
                    if best is None or k < best:
                        best = k
    return best


def enclose_monoid(bound):
    seen, stack = set(), [1]
    while stack:
        value = stack.pop()
        if value in seen:
            continue
        seen.add(value)
        for g in GENERATORS:
            product = value * g
            if product <= bound:
                stack.append(product)
    return seen


def in_superset(m):
    i = j = k = 0
    rest = m
    while rest % 2 == 0:
        rest //= 2
        i += 1
    while rest % 3 == 0:
        rest //= 3
        j += 1
    while rest % 5 == 0:
        rest //= 5
        k += 1
    if rest != 1:
        return False
    return i <= 2 * j + 2 * k if k >= 1 else 1 <= j <= i <= 2 * j


def region_sums():
    r1 = F(1, 14) * F(6, 5)
    r2 = F(3, 2) * ((F(12, 11) - F(12, 35)) + (F(2, 11) - F(2, 35)))
    r3 = F(3, 2) * (F(14, 11) - F(22, 19))
    return r1, r2, r3


def tail_bound(bound, c_max=40, b_max=80):
    total = F(0)

    def first_alpha(beta, c):
        if F(3) ** beta * F(5) ** c > bound:
            return 0
        alpha = 0
        while F(2) ** alpha * F(3) ** beta * F(5) ** c <= bound:
            alpha += 1
        return alpha

    for c in range(1, c_max + 1):
        for beta in range(0, b_max + 1):
            high = 2 * beta + 2 * c
            low = first_alpha(beta, c)
            if low > high:
                continue
            total += (F(2) ** (1 - low) - F(2) ** (-high)) * F(3) ** (-beta) * F(5) ** (-c)
    total += F(3, 4) * F(5) ** (-c_max)
    total += F(3) ** (-b_max) / 4

    for beta in range(1, b_max + 1):
        low = max(beta, first_alpha(beta, 0))
        high = 2 * beta
        if low > high:
            continue
        total += (F(2) ** (1 - low) - F(2) ** (-high)) * F(3) ** (-beta)
    total += F(2, 5) * F(6) ** (-b_max)
    return total


def main():
    print("=== (a) the index monoid of A5 ===")
    indices = sorted({60 // order for order in A5_SUBGROUP_ORDERS})
    check("I(A5) = {1,5,6,10,12,15,20,30,60}",
          indices == [1, 5, 6, 10, 12, 15, 20, 30, 60], str(indices))
    j_ac5 = sum((F(1, m) for m in indices), F(0))
    check("J(A5) = 103/60 < 2", j_ac5 == F(103, 60), f"{j_ac5} = {float(j_ac5):.9f}")

    wrong = [(i, j) for i in range(40) for j in range(40)
             if kappa_closed(i, j) != kappa_brute(i, j)]
    check("kappa closed form = exhaustive search over the generators (i, j < 40)",
          not wrong, f"{len(wrong)} mismatches")

    monoid = enclose_monoid(10 ** 6)
    predicted = {2 ** i * 3 ** j * 5 ** k
                 for i in range(25) for j in range(25) for k in range(25)
                 if 2 ** i * 3 ** j * 5 ** k <= 10 ** 6 and k >= kappa_closed(i, j)}
    check("M(A5) below 10^6 equals {2^i 3^j 5^k : k >= kappa(i,j)}",
          monoid == predicted, f"|M(A5) and [1,1e6]| = {len(monoid)}")
    check("every index of A5 lies in the monoid, and 2, 3 do not",
          all(m == 1 or (m & (m - 1)) == 0 or m in monoid for m in indices)
          and 2 not in monoid and 3 not in monoid and 30 in monoid and 60 in monoid)

    print("\n=== (b) closed form for the mass ===")
    r1, r2, r3 = region_sums()
    check("R1 = 3/35", r1 == F(3, 35), str(r1))
    check("R2 = 72/55", r2 == F(72, 55), str(r2))
    check("R3 = 36/209", r3 == F(36, 209), str(r3))
    mass = F(5, 4) * (r1 + r2 + r3)
    check("the mass is exactly 11463/5852", mass == CLAIMED_MASS, str(mass))
    check("Lambda({A5}) = 5611/5852 < 1", mass - 1 == F(5611, 5852) and mass - 1 < 1,
          f"{float(mass - 1):.12f}")

    print("\n=== (c) independent cross-check ===")
    big = enclose_monoid(ENUM_BOUND)
    above_one = sorted(m for m in big if m > 1)
    partial = sum((F(1, m) for m in above_one), F(0))
    outside = [m for m in above_one if not in_superset(m)]
    check("every enumerated element lies in the superset used for the tail", not outside,
          f"{len(outside)} counterexamples")
    tail = tail_bound(ENUM_BOUND)
    upper = partial + tail
    claimed_lambda = CLAIMED_MASS - 1
    check("enumeration and tail bracket the exact value", partial < claimed_lambda < upper,
          f"{float(partial):.12f} < {float(claimed_lambda):.12f} < {float(upper):.12f}")
    check("the independent bound is below 2", upper < 2, f"{float(upper):.12f}")

    print("\n=== (d) the deduction ===")
    check("J(A5^r) <= 1 + Lambda({A5}) < 2 for every r, so the criterion applies",
          mass < 2 and 1 + upper < 2, f"1 + Lambda = {float(mass):.12f} < 2")
    squared = sorted({a * b for a in indices for b in indices})
    small = sum((F(1, n) for n in squared if n > 1), F(0))
    check("independent confirmation at r = 2: 33 index values, sum of reciprocals 1639/1800",
          len(squared) == 33 and small == F(1639, 1800),
          f"J(A5 x A5) = 1 + 1639/1800 = {float(1 + small):.6f} < 2")

    print("\n================ SUMMARY ================")
    if FAILURES:
        print("FAILURES:", FAILURES)
        raise SystemExit(1)
    print("all checks passed")
    raise SystemExit(0)


if __name__ == "__main__":
    main()
