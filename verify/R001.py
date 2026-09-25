#!/usr/bin/env python3
"""Reproduce the computational claims of R001 — the cyclotomic totient oracle.

For p prime and N = 2^p - 1, the theorem asserts

    Phi_N(2) == 1 + (2*phi(N)/p) * N   (mod N^2),

and the no-wrap bound 0 < 2*phi(N)/p <= N-1 then forces c = (R-1)/N exactly,
where R is the residue of Phi_N(2) modulo N^2.

This script recomputes R *from the definition*

    Phi_n(a) = prod_{d | n} (a^d - 1)^{mu(n/d)}

evaluated modulo N^2. Each factor a^d - 1 is coprime to N (it is == 1 mod N),
so it is invertible modulo N^2 and the Mobius product is exact.

Nothing here is imported from a research workspace: every number is recomputed
from scratch with integer arithmetic only.

Usage:
    python3 verify/R001.py

Exit status 0 means every check passed.
"""

from __future__ import annotations

import random
from math import gcd


def is_prime(n: int) -> bool:
    """Deterministic Miller-Rabin for n < 3.3e24."""
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


def pollard_rho(n: int) -> int:
    """Return a non-trivial factor of composite n."""
    if n % 2 == 0:
        return 2
    while True:
        x = random.randrange(2, n)
        y, c, d = x, random.randrange(1, n), 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = gcd(abs(x - y), n)
        if d != n:
            return d


def factorise(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    stack = [n]
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if is_prime(m):
            out[m] = out.get(m, 0) + 1
            continue
        d = pollard_rho(m)
        stack.extend((d, m // d))
    return out


def divisors(n: int) -> list[int]:
    ds = [1]
    for q, e in sorted(factorise(n).items()):
        ds = [d * q**k for d in ds for k in range(e + 1)]
    return sorted(ds)


def mobius(n: int) -> int:
    f = factorise(n)
    if any(e > 1 for e in f.values()):
        return 0
    return -1 if len(f) % 2 else 1


def totient(n: int) -> int:
    r = n
    for q in factorise(n):
        r -= r // q
    return r


def cyclotomic_eval_exact(n: int, a: int) -> int:
    """Phi_n(a) as an exact integer."""
    num, den = 1, 1
    for d in divisors(n):
        mu = mobius(n // d)
        if mu == 0:
            continue
        v = pow(a, d) - 1
        if mu == 1:
            num *= v
        else:
            den *= v
    q, rem = divmod(num, den)
    if rem != 0:
        raise ValueError(f"non-exact division for n={n}, a={a}")
    return q


def cyclotomic_eval_mod(n: int, a: int, m: int) -> int:
    """Phi_n(a) mod m, from the Mobius product, using inverse factors."""
    acc = 1
    for d in divisors(n):
        mu = mobius(n // d)
        if mu == 0:
            continue
        base = (pow(a, d, m) - 1) % m
        if base == 0:
            raise ValueError(f"factor a^d-1 is not a unit mod {m}")
        acc = acc * base % m if mu == 1 else acc * pow(base, -1, m) % m
    return acc


PRIME_EXPONENTS = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]


def check_main_identity() -> bool:
    print("check 1 — the main identity, prime exponents p <= 47")
    print(f"  {'p':>3} {'N = 2^p - 1':>21} {'c = (R-1)/N':>21} {'2*phi(N)/p':>21}   ok")
    ok = True
    for p in PRIME_EXPONENTS:
        n = 2**p - 1
        m = n * n
        r = cyclotomic_eval_mod(n, 2, m)
        c = (r - 1) // n
        target = 2 * totient(n) // p
        good = r % n == 1 and c == target and 1 <= target <= n - 1
        ok &= good
        print(f"  {p:>3} {str(n):>21} {str(c):>21} {str(target):>21}   {good}")
    print(f"  all prime exponents p <= 47 reproduce the identity: {ok}\n")
    return ok


def check_p61() -> bool:
    print("check 2 — the p = 61 case (N is a Mersenne prime, so Phi_N(2) = 2^N - 1)")
    p = 61
    n = 2**p - 1
    assert is_prime(n), "2^61 - 1 should be prime"
    r = (pow(2, n, n * n) - 1) % (n * n)
    c = (r - 1) // n
    target = 2 * (n - 1) // p
    ok = c == target == 75_601_410_138_153_900
    print(f"  N            = {n}")
    print(f"  c = (R-1)/N  = {c}")
    print(f"  2*phi(N)/p   = {target}")
    print(f"  matches both the theorem and the recorded value 75601410138153900: {ok}\n")
    return ok


def check_no_wrap() -> bool:
    print("check 3 — the no-wrap bound 0 < 2*phi(N)/p <= N-1")
    ok = True
    for p in PRIME_EXPONENTS + [61]:
        n = 2**p - 1
        c = 2 * totient(n) // p
        good = 0 < c <= n - 1
        ok &= good
        if not good:
            print(f"  FAIL p={p}: c={c}, N-1={n-1}")
    print(f"  the decoded coefficient never reaches N: {ok}\n")
    return ok


def check_counterexamples() -> bool:
    print("check 4 — the hypotheses are necessary (recorded counterexamples)")
    ok = True
    n = 15
    r = cyclotomic_eval_mod(n, 2, n * n)
    c = (r - 1) // n
    bad = c != 2 * totient(n) // 4
    ok &= bad
    print(f"  p=4 (composite): Phi_15(2) mod 225 = {r}, c = {c}, "
          f"but 2*phi(15)/4 = {2 * totient(n) // 4}  -> identity fails: {bad}")
    n = 26
    r = cyclotomic_eval_exact(n, 3) % (n * n)
    c = (r - 1) // n
    bad = c != totient(n)
    ok &= bad
    print(f"  a=3, p=3:        Phi_26(3) = {cyclotomic_eval_exact(n, 3)}, "
          f"mod 676 = {r}, c = {c},")
    print(f"                   but 3*phi(26)/3 = {totient(n)}  -> identity fails: {bad}")
    print(f"  both failures reproduce: {ok}\n")
    return ok


def check_small_case() -> bool:
    print("check 5 — worked example p = 11, N = 2047 = 23 * 89")
    p, n = 11, 2047
    m = n * n
    r = cyclotomic_eval_mod(n, 2, m)
    c = (r - 1) // n
    phi = totient(n)
    ok = r % n == 1 and c == 2 * phi // p == 352 and phi == 1936
    print(f"  Phi_2047(2) mod 2047^2 = {r}")
    print(f"  c = (R-1)/N            = {c}")
    print(f"  phi(2047) = 2047*(1-1/23)*(1-1/89) = {phi}, and p*c/2 = {p * c // 2}")
    print(f"  decoded totient matches: {ok}\n")
    return ok


def main() -> int:
    print("=" * 72)
    print("R001 — the cyclotomic totient oracle: independent verification")
    print("=" * 72 + "\n")
    results = {
        "main identity (p <= 47)": check_main_identity(),
        "p = 61 case": check_p61(),
        "no-wrap bound": check_no_wrap(),
        "counterexamples": check_counterexamples(),
        "worked example": check_small_case(),
    }
    print("=" * 72)
    for name, passed in results.items():
        print(f"  {'PASS' if passed else 'FAIL'}   {name}")
    all_ok = all(results.values())
    print("=" * 72)
    print("  ALL CHECKS PASSED" if all_ok else "  THERE WERE FAILURES")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
