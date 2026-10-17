#!/usr/bin/env python3
"""Generate exact certificates for P20 Lean formalization.

Implements Appendix A of the paper (exact integer / rational arithmetic)
and dumps Lean-ready certificate arrays.
"""
from fractions import Fraction as F
from math import comb, factorial, prod, lcm
from collections import Counter
import json
from pathlib import Path

OUT = Path.cwd() / "certs"


def partitions(n, cap=None):
    if n == 0:
        yield ()
    else:
        for a in range(min(n, n if cap is None else cap), 0, -1):
            for tail in partitions(n - a, a):
                yield (a,) + tail


def shape(lam):
    col = [sum(a > j for a in lam) for j in range(lam[0])]
    hooks = [a - j + col[j] - i - 1
             for i, a in enumerate(lam) for j in range(a)]
    nu = sum(i * a for i, a in enumerate(lam))
    c = sum(a * (a - 1) // 2 - i * a for i, a in enumerate(lam))
    f, rem = divmod(factorial(sum(lam)), prod(hooks))
    assert rem == 0
    return hooks, nu, c, f


def bps_coefficients(r, k=1):
    assert r >= 2 and k >= 1
    d = k * r * (r - 1) // 2
    H = [0] * (d + 1)
    for lam in partitions(r):
        hooks, nu, c, f = shape(lam)
        E = d + (k + 1) * c + nu
        assert E >= 0
        if E > d:
            continue
        t = [1] + [0] * (d - E)
        for a in hooks:
            for j in range(a, len(t)):
                t[j] += t[j - a]
        for j, value in enumerate(t):
            H[E + j] += f * value
    for _ in range(r):
        H = [H[0]] + [H[j] - H[j - 1] for j in range(1, d + 1)]
    n = [0] * (d + 1)
    for ell in range(d + 1):
        h = d - ell
        n[h] = H[ell]
        for j in range(min(2 * h, d - ell) + 1):
            H[ell + j] -= n[h] * (-1) ** j * comb(2 * h, j)
    assert not any(H)
    return n


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def contact_polynomials(r, H):
    assert r >= 2 and H >= 0
    D = [[F(0)] * (H + 1) for _ in range(r + 1)]
    D[1][0] = D[2][0] = F(1)
    for a, coeffs in ((3, (3, 1)), (4, (2, 1))):
        if a <= r:
            for j, value in enumerate(coeffs[: H + 1]):
                D[a][j] = F(value)
    for a in range(5, r + 1):
        for j in range(H + 1):
            D[a][j] = 2 * D[a - 2][j] - D[a - 4][j]
            if j:
                D[a][j] += D[a - 2][j - 1]
    g = [[F(0)] * H for _ in range(r + 1)]
    for a in range(1, r + 1):
        for j in range(H):
            g[a][j] = (-(j + 1) * D[a][j + 1] - sum(
                D[a][t] * g[a][j - t] for t in range(1, j + 1))) / D[a][0]
    by_content = {}
    order = factorial(r)
    dimension_sum = 0
    for lam in partitions(r):
        hooks, nu, c, f = shape(lam)
        dimension_sum += f * f
        even = sum(a % 2 == 0 for a in hooks)
        assert (even - c) % 2 == 0
        count = Counter(hooks)
        log = [F(0)] + [sum(m * g[a][j - 1] for a, m in count.items())
                        + F((even // 2) * (-1) ** j, 4 ** j) for j in range(1, H + 1)]
        R = [F(1)] + [F(0)] * H
        for j in range(1, H + 1):
            R[j] = sum(log[t] * R[j - t] for t in range(1, j + 1)) / j
        total = by_content.setdefault(abs(c), [F(0)] * (H + 1))
        weight = F(f * f, order)
        for j in range(H + 1):
            total[j] += weight * R[j]
    assert dimension_sum == order
    Q = [[F(0)] * (h + 1) for h in range(H + 1)]
    for c, R in by_content.items():
        A = [F(1)]
        for j in range(H + 1):
            if j:
                t = 2 * j - 1 if c % 2 else 2 * (j - 1)
                den = 4 * (2 * j) * (2 * j - 1)
                A = mul(A, [F(c * c - t * t, den), F(4 * c * c, den)])
            for h in range(j, H + 1):
                for power, value in enumerate(A):
                    Q[h][power] += value * R[h - j]
    return Q


def rat_to_pair(x: F):
    return [x.numerator, x.denominator]


def main():
    OUT.mkdir(parents=True, exist_ok=True)

    # --- Theorem 1.1: C_{43,1} ---
    n43 = bps_coefficients(43)
    a = 46743830419465000460525749853426296821511513919267
    b = 4478706954001198396797888969114794682889954544660295
    c = 429147501803199891064835526788080765663004079176388506
    assert n43[23:26] == [a, b, c]
    assert len(n43) == 904 and min(n43) > 0 and n43[0] == n43[-1] == 1
    assert 20000 * b * b < 19999 * a * c
    print("ordinary43 PASS", len(n43), "min", min(n43))

    (OUT / "n43.json").write_text(json.dumps({
        "r": 43, "k": 1, "d": 903,
        "n": n43,
        "n23": a, "n24": b, "n25": c,
    }) + "\n")

    # Lean-friendly: only the three named values + positivity witness list length
    (OUT / "thm11_vals.lean.txt").write_text(
        "def n23val : Nat := " + str(a) + "\n"
        "def n24val : Nat := " + str(b) + "\n"
        "def n25val : Nat := " + str(c) + "\n"
    )

    # --- Theorem 1.2: C_{36,k} ---
    Q = contact_polynomials(36, 22)
    for h in range(23):
        assert Q[h][0] == (1 if h == 0 else 0)
    left, right = mul(Q[21], Q[21]), mul(Q[20], Q[22])
    G = [x - y for x, y in zip(left, right)]
    assert len(G) == 43
    shifted = [sum(G[i] * comb(i, j) * 110 ** (i - j)
                   for i in range(j, len(G))) for j in range(len(G))]
    assert all(x < 0 for x in shifted)
    den = lcm(*(x.denominator for x in shifted))
    expected = (2 ** 63 * 3 ** 32 * 5 ** 16 * 7 ** 10 * 11 ** 7 * 13 ** 6
                * 17 ** 4 * 19 ** 4 * (23 * 29 * 31 * 37 * 41) ** 2 * 43)
    assert den == expected
    bj = [-den * x for x in shifted]
    assert all(x.denominator == 1 and x > 0 for x in bj)
    bj = [int(x) for x in bj]

    print("uniform36 PASS, D =", den)
    print("b_j count", len(bj), "b0", bj[0], "b42", bj[42])

    def q_to_json(coeffs):
        return [[x.numerator, x.denominator] for x in coeffs]

    (OUT / "q36.json").write_text(json.dumps({
        "r": 36,
        "H": 22,
        "Q20": q_to_json(Q[20]),
        "Q21": q_to_json(Q[21]),
        "Q22": q_to_json(Q[22]),
        "G": q_to_json(G),
        "shifted": q_to_json(shifted),
        "D": den,
        "b": bj,
    }) + "\n")

    # Compact Lean literals for G shifted numerator
    (OUT / "thm12_b.lean.txt").write_text(
        "def Dval : Nat := " + str(den) + "\n"
        "def bVals : List Nat :=\n  [" + ",\n   ".join(str(x) for x in bj) + "]\n"
    )

    # moments for (26)
    moments = [0, 0, 0]
    for lam in partitions(36):
        hooks, nu, c, f = shape(lam)
        for j, h in enumerate((20, 21, 22)):
            moments[j] += f * f * c ** (2 * h)
    moments = [F(t, factorial(36)) for t in moments]
    assert all(t.denominator == 1 for t in moments)
    for h, t in zip((20, 21, 22), moments):
        assert Q[h][h] == t / factorial(2 * h)
    a2, b2, c2 = moments
    ratio = F(44 * 43, 42 * 41) * b2 * b2 / (a2 * c2)
    assert F(99993, 100000) < ratio < F(99994, 100000)
    print("moments PASS", [int(x) for x in moments], "ratio", ratio)

    (OUT / "moments.json").write_text(json.dumps({
        "T20_over_fact": int(moments[0]),
        "T21_over_fact": int(moments[1]),
        "T22_over_fact": int(moments[2]),
        "leading20": q_to_json(Q[20][-1:])[0] if False else rat_to_pair(Q[20][20]),
        "leading21": rat_to_pair(Q[21][21]),
        "leading22": rat_to_pair(Q[22][22]),
        "ratio_num": ratio.numerator,
        "ratio_den": ratio.denominator,
    }) + "\n")

    print("ALL CERTS WRITTEN to", OUT)


if __name__ == "__main__":
    main()
