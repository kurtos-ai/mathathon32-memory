#!/usr/bin/env python3
"""Exact rational certificates for the arbitrary-N convex-quadratic example.

No third-party packages, floating-point arithmetic, or optimizer are used.
Coefficient arrays are in ascending powers. This verifies the polynomial upper
certificate and its explicit Gram representation, not general quantifier
elimination or the lower-bound proof (which is in the accompanying paper).

Example:
    python3 quadratic-memory-certificates.py --N 10 --threshold 1/800
"""

import argparse
from fractions import Fraction as F
import json


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    out = [F(0)] * max(len(p), len(q))
    for i, x in enumerate(p):
        out[i] += x
    for i, x in enumerate(q):
        out[i] += x
    return trim(out)


def scale(p, scalar):
    return trim([scalar * x for x in p])


def multiply(p, q):
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    return trim(out)


def check_equal(p, q, label):
    if trim(p) != trim(q):
        raise ArithmeticError(f"Failed coefficient identity: {label}")


def chebyshev(degree, second_kind=False):
    previous = [F(1)]
    if degree == 0:
        return previous
    current = [F(0), F(2 if second_kind else 1)]
    for _ in range(1, degree):
        following = add([F(0)] + scale(current, F(2)), scale(previous, F(-1)))
        previous, current = current, following
    return current


def gram_polynomial(matrix):
    size = len(matrix)
    out = [F(0)] * (2 * size - 1)
    for i in range(size):
        for j in range(size):
            out[i + j] += matrix[i][j]
    return trim(out)


def certify(n, threshold=None):
    if n < 1:
        raise ValueError("N must be a positive integer")
    m = 2 * n + 1
    c = chebyshev(m)
    u = chebyshev(2 * n, second_kind=True)
    if any(c[i] for i in range(0, len(c), 2)):
        raise ArithmeticError("Expected an odd first-kind polynomial")
    if any(u[i] for i in range(1, len(u), 2)):
        raise ArithmeticError("Expected an even second-kind polynomial")
    p = [F((-1) ** n, m) * c[2 * j + 1] for j in range(n + 1)]
    s = [u[2 * j] / m for j in range(n + 1)]
    if p[0] != 1 or len(trim(p)) != n + 1 or len(trim(s)) != n + 1:
        raise ArithmeticError("Residual degree or normalization failed")
    bound = F(1, 2 * m * m)
    z_p_squared = [F(0)] + multiply(p, p)
    lhs = add([F(1, m * m)], scale(z_p_squared, F(-1)))
    rhs = multiply([F(1), F(-1)], multiply(s, s))
    check_equal(lhs, rhs, "M^(-2) - z p(z)^2 = (1-z) s(z)^2")
    out = {
        "N": n,
        "M": m,
        "risk_bound": str(bound),
        "p_star_ascending_coefficients": [str(x) for x in p],
        "s_N_ascending_coefficients": [str(x) for x in s],
        "polynomial_identity": "verified exactly",
    }
    if threshold is not None:
        threshold = F(threshold)
        epsilon = threshold - bound
        if epsilon <= 0:
            raise ValueError(f"Strict certificate requires threshold > {bound}")
        a = [[F(0) for _ in range(n + 1)] for _ in range(n + 1)]
        b = [[s[i] * s[j] for j in range(n + 1)] for i in range(n + 1)]
        a[0][0] = epsilon
        b[0][0] += epsilon
        lhs = add([2 * threshold - epsilon], scale(z_p_squared, F(-1)))
        rhs = add([F(0)] + gram_polynomial(a),
                  multiply([F(1), F(-1)], gram_polynomial(b)))
        check_equal(lhs, rhs, "strict Gram certificate")
        out.update({
            "threshold": str(threshold),
            "epsilon": str(epsilon),
            "strict_Gram_identity": "verified exactly",
            "PSD_reason": "A = epsilon e0 e0^T; B = A + s s^T; epsilon > 0",
            "A": [[str(x) for x in row] for row in a],
            "B": [[str(x) for x in row] for row in b],
        })
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--N", type=int, required=True, help="arbitrary positive query horizon")
    parser.add_argument("--threshold", type=str, help="optional exact rational threshold, e.g. 1/800")
    parser.add_argument("--include-matrices", action="store_true", help="print the explicit Gram matrices")
    args = parser.parse_args()
    try:
        out = certify(args.N, args.threshold)
    except (ValueError, ZeroDivisionError) as exc:
        parser.error(str(exc))
    if not args.include_matrices:
        out.pop("A", None)
        out.pop("B", None)
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
