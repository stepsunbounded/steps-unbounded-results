#!/usr/bin/env python3
"""Reproduce the computational claims of R002 — the doubling identity.

For a prime r > 3 and c >= 1 with P = 2cr - 1, R002 asserts

    R(2) - R(1) = -c * q_r(2)      in F_r,

where H_j = 1 + 1/2 + ... + 1/j in F_r, M = (P-1)/2,
F(x) = H[floor(rho(x) / (2c))] for x = 1..M, with rho(y) = min(y mod P, P - (y mod P)),
and R(a) = sum_x F(x) F(rho(a x)); q_r(2) = (2^(r-1) - 1)/r mod r.

Everything here is recomputed from the construction. The identity is used nowhere.

Usage:
    python3 verify/R002.py

Exit status 0 means every check passed.
"""

from __future__ import annotations


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for sp in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % sp == 0:
            return n == sp
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def primes_upto(n: int) -> list[int]:
    return [q for q in range(5, n + 1) if is_prime(q)]


def harmonic_staircase(r: int) -> list[int]:
    H = [0] * r
    for j in range(1, r):
        H[j] = (H[j - 1] + pow(j, -1, r)) % r
    return H


def residue(y: int, P: int) -> int:
    t = y % P
    return t if t <= P - t else P - t


def correlation_defect(r: int, c: int) -> tuple[int, int]:
    P = 2 * c * r - 1
    M = (P - 1) // 2
    H = harmonic_staircase(r)
    F = [H[residue(x, P) // (2 * c)] for x in range(M + 1)]

    def R(a: int) -> int:
        s = 0
        for x in range(1, M + 1):
            s += F[x] * F[residue(a * x, P)]
        return s % r

    q = (pow(2, r - 1, r * r) - 1) // r % r
    return (R(2) - R(1)) % r, (-c * q) % r


R_MAX, C_MAX = 97, 12


def check_identity() -> bool:
    print(f"check 1 — the identity, primes 5 <= r <= {R_MAX}, 1 <= c <= {C_MAX}")
    rows = []
    for r in primes_upto(R_MAX):
        for c in range(1, C_MAX + 1):
            lhs, rhs = correlation_defect(r, c)
            rows.append((r, c, lhs, rhs))
    bad = [x for x in rows if x[2] != x[3]]
    for x in bad[:5]:
        print(f"    MISMATCH r={x[0]} c={x[1]}: {x[2]} != {x[3]}")
    print(f"    {len(rows)} pairs over {len({x[0] for x in rows})} primes, {len(bad)} mismatches\n")
    return not bad


def check_wieferich_primes() -> bool:
    print("check 2 — the known base-2 Wieferich primes 1093 and 3511")
    ok = True
    for r, c in ((1093, 10), (3511, 4)):
        P = 2 * c * r - 1
        M = (P - 1) // 2
        H = harmonic_staircase(r)
        F = [H[residue(x, P) // (2 * c)] for x in range(M + 1)]

        def R(a: int) -> int:
            s = 0
            for x in range(1, M + 1):
                s += F[x] * F[residue(a * x, P)]
            return s % r

        q = (pow(2, r - 1, r * r) - 1) // r % r
        r1, r2 = R(1), R(2)
        good = r1 == r2 and q == 0
        ok &= good
        print(f"    r = {r:5d}  c = {c:2d}  P = {P:6d}  R(1) = {r1:5d}  "
              f"R(2) = {r2:5d}  q_r(2) = {q}  -> {good}")
    print()
    return ok


def check_r_divides_c() -> bool:
    print("check 3 — the r | c cases (identity holds, both sides vanish)")
    hits, ok = 0, True
    for r in primes_upto(R_MAX):
        for c in range(1, C_MAX + 1):
            if c % r:
                continue
            lhs, rhs = correlation_defect(r, c)
            hits += 1
            if lhs != 0 or rhs != 0:
                ok = False
                print(f"    UNEXPECTED r={r} c={c}: {lhs} vs {rhs}")
    print(f"    {hits} case(s) with r | c in range, both sides zero: {ok}\n")
    return ok


def check_composite_P() -> bool:
    print("check 4 — composite P (the counting form needs no primality)")
    rows, bad = 0, 0
    for r in primes_upto(60):
        for c in range(1, 8):
            P = 2 * c * r - 1
            if is_prime(P):
                continue
            lhs, rhs = correlation_defect(r, c)
            rows += 1
            if lhs != rhs:
                bad += 1
                print(f"    MISMATCH r={r} c={c} P={P}: {lhs} != {rhs}")
    print(f"    {rows} composite-P pairs, {bad} mismatches\n")
    return bad == 0


def main() -> int:
    print("=" * 72)
    print("R002 — the doubling identity: independent verification")
    print("=" * 72 + "\n")
    results = {
        "identity over admissible (r, c)": check_identity(),
        "known Wieferich primes": check_wieferich_primes(),
        "r | c cases vanish on both sides": check_r_divides_c(),
        "counting form with composite P": check_composite_P(),
    }
    print("=" * 72)
    for name, passed in results.items():
        print(f"  {'PASS' if passed else 'FAIL'}   {name}")
    print("=" * 72)
    all_ok = all(results.values())
    print("  ALL CHECKS PASSED" if all_ok else "  THERE WERE FAILURES")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
