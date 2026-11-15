#!/usr/bin/env python3
"""Rank and memory-locus checks: H_k cut rank, S_k minors, product formula.

Fixed ranges N=1..8, deterministic formula-generated test matrices.
Verifies:
- rank H_k = 1 + rank S_k after invertible row operation
- Sample: zero matrix is in Q0; Qm defined by vanishing (m+1)-minors
- At T=0, product formula p_N = prod(1+d_i lambda) holds
- Bound s(W) <= 1+ floor(N/2)
Exact rational arithmetic where possible; numeric rank via Fraction Gaussian elimination.
"""
from fractions import Fraction as F
import itertools, math, sys
from pathlib import Path

LOGDIR = Path(__file__).parent / "logs"
LOGDIR.mkdir(exist_ok=True)

def rank_fraction(matrix):
    """Rank over Q via Gaussian elimination on Fractions."""
    if not matrix or not matrix[0]:
        return 0
    m = [row[:] for row in matrix]
    rows, cols = len(m), len(m[0])
    r = 0
    for c in range(cols):
        # find pivot
        piv = None
        for i in range(r, rows):
            if m[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        # normalize pivot row (not needed for rank but keeps numbers small)
        piv_val = m[r][c]
        # eliminate below
        for i in range(r+1, rows):
            if m[i][c] != 0:
                factor = m[i][c] / piv_val
                for j in range(c, cols):
                    m[i][j] -= factor * m[r][j]
        r += 1
        if r == rows:
            break
    return r

def build_H(W, N):
    """W is (N+1)x(N+1) strictly lower triangular dict a[i][j]. Return H_k list."""
    H = []
    for k in range(N+1):
        # rows: k..N inclusive
        rows = N - k + 1
        cols = k+1
        mat = []
        for i in range(k, N+1):
            row = []
            # col0 is 1
            row.append(F(1))
            for j in range(k):
                # a_{i,j}
                row.append(F(W[i][j] if j < i else 0))
            mat.append(row)
        H.append(mat)
    return H

def build_S(T, N):
    """T is NxN strictly lower triangular dict. Return list of S_k matrices."""
    S = []
    for k in range(N+1):
        if k==0 or k==N:
            S.append([])  # empty
        else:
            mat = []
            for i in range(k, N):
                row = []
                for j in range(k):
                    row.append(F(T[i][j] if j < i else 0))
                mat.append(row)
            S.append(mat)
    return S

def d_T_from_W(W, N):
    """Convert W to (d,T) per eq: d_j=W_{j+1,j}, T_{ij}=W_{i+1,j}-W_{i,j} for j<i, else 0"""
    d = [F(0)]*N
    T = [[F(0)]*N for _ in range(N)]
    for j in range(N):
        d[j] = F(W[j+1][j])
    for i in range(N):
        for j in range(N):
            if j < i:
                T[i][j] = F(W[i+1][j] - W[i][j])
            else:
                T[i][j] = F(0)
    return d, T

def W_from_d_T(d, T, N):
    """Inverse: a_{ij}= d_j + sum_{l=j+1}^{i-1} T_{l j} for j<i else 0"""
    W = [[F(0)]*(N+1) for _ in range(N+1)]
    for i in range(N+1):
        for j in range(N+1):
            if j < i:
                s = F(d[j])
                for l in range(j+1, i):
                    if l < N:
                        s += F(T[l][j])
                W[i][j] = s
            else:
                W[i][j] = F(0)
    return W

def minors_vanish(mat, m):
    """Check all (m+1)-minors vanish (rank <= m). Empty matrix has rank 0."""
    if not mat or not mat[0]:
        return True
    rows, cols = len(mat), len(mat[0])
    if min(rows, cols) <= m:
        return True
    # brute force all (m+1) row/col combos - small N only
    from itertools import combinations
    k = m+1
    for rs in combinations(range(rows), k):
        for cs in combinations(range(cols), k):
            # determinant of kxk minor
            sub = [[mat[r][c] for c in cs] for r in rs]
            det = det_fraction(sub)
            if det != 0:
                return False
    return True

def det_fraction(mat):
    n = len(mat)
    if n==1:
        return mat[0][0]
    if n==2:
        return mat[0][0]*mat[1][1] - mat[0][1]*mat[1][0]
    # expand via Fraction elimination
    m = [row[:] for row in mat]
    det = F(1)
    for c in range(n):
        # pivot
        piv = None
        for i in range(c, n):
            if m[i][c] != 0:
                piv=i; break
        if piv is None:
            return F(0)
        if piv != c:
            m[c], m[piv] = m[piv], m[c]
            det = -det
        det *= m[c][c]
        piv_val = m[c][c]
        for i in range(c+1, n):
            if m[i][c] != 0:
                factor = m[i][c]/piv_val
                for j in range(c+1, n):
                    m[i][j] -= factor*m[c][j]
        # continue
    return det

def test_rank_formula():
    print("=== Rank checks: H_k vs S_k ===")
    ok = 0
    tot = 0
    failures = []
    for N in range(1, 9):
        # deterministic W: use pattern W[i][j]= (i*j + i + j) mod 5 -2 over Q
        W = [[F(0)]*(N+1) for _ in range(N+1)]
        for i in range(N+1):
            for j in range(i):
                W[i][j] = F((i*j + i + j) % 5 - 2)
        d, T = d_T_from_W(W, N)
        # reconstruct check
        W2 = W_from_d_T(d, T, N)
        assert W2 == W, f"reconstruction failed N={N}"
        H = build_H(W, N)
        S = build_S(T, N)
        for k in range(N+1):
            hk = rank_fraction(H[k]) if H[k] else 0
            if k==0 or k==N:
                sk = 0
            else:
                sk = rank_fraction(S[k])
            if hk != 1+sk:
                print(f"FAIL N={N} k={k} rank H={hk} rank S={sk} expected 1+sk")
                failures.append((N,k))
                tot+=1
            else:
                ok+=1; tot+=1
        # also check bound s(W) <=1+floor(N/2)
        sW = max(rank_fraction(H[k]) if H[k] else 0 for k in range(N+1)) if N>=0 else 0
        bound = 1+ N//2
        if sW > bound:
            raise AssertionError(f"cut-rank bound failed N={N}: sample maximum {sW} > {bound}")
        else:
            print(f"N={N:2d} sample max rank H={sW} bound={bound}  H_ranks={[rank_fraction(H[k]) if H[k] else 0 for k in range(N+1)]} S_ranks={[rank_fraction(S[k]) if S[k] else 0 for k in range(N+1)]} OK")
    print(f"Rank checks: {ok}/{tot} sampled cut-rank identities passed")
    return not failures and ok==tot

def test_loci():
    print("\n=== Memory loci Q_m ===")
    for N in [3,4,5,6]:
        # Sampled zero-matrix membership in Q0
        T0 = [[F(0)]*N for _ in range(N)]
        S0 = build_S(T0, N)
        assert all(rank_fraction(S0[k])==0 if S0[k] else True for k in range(N+1)), "Q0 not zero"
        print(f"N={N} zero-matrix membership in Q0 verified (all S_k zero; not a proof of converse)")
        # random T via deterministic pattern should generally have rank>0
        T1 = [[F((i*3+j*2+1)%4) if j<i else F(0) for j in range(N)] for i in range(N)]
        S1 = build_S(T1, N)
        ranks = [rank_fraction(S1[k]) if S1[k] else 0 for k in range(N+1)]
        print(f"N={N} sample T ranks per k: {ranks}")
        for m in [0,1,2]:
            # check minor vanishing equivalence
            for k in range(1,N):
                mat = S1[k]
                vanish = minors_vanish(mat, m)
                rk = rank_fraction(mat) if mat else 0
                if (rk <= m) != vanish:
                    print(f"  FAIL m={m} k={k} rank {rk} vs minors {vanish}")
                    return False
            print(f"  m={m} minor-vanish equivalence holds")
    # explicit construction of rank-1 witness (OGM-like)
    print("\nRank-1 witness: T_{ij}= u_i v_j for j<i (factored)")
    for N in [4,6]:
        u = [F(i+1) for i in range(N)]
        v = [F(j+1) for j in range(N)]
        T = [[u[i]*v[j] if j<i else F(0) for j in range(N)] for i in range(N)]
        S = build_S(T, N)
        for k in range(1,N):
            rk = rank_fraction(S[k]) if S[k] else 0
            assert rk <=1, f"factored T should have rank<=1 k={k} rk={rk}"
        print(f"N={N} factored rank-1 T verified: ranks {[rank_fraction(S[k]) if S[k] else 0 for k in range(1,N)]}")
    return True

def test_product():
    print("\n=== Product formula at T=0 ===")
    for N in [1,3,5]:
        d = [F(-1, i+2) for i in range(N)]  # arbitrary steps
        T = [[F(0)]*N for _ in range(N)]
        W = W_from_d_T(d, T, N)
        # check via polynomial product
        # p_N(lambda)= prod(1+d_i lambda)
        # test at lambda= F(1,3) and via recurrence
        from fractions import Fraction
        # brute force error propagation check: p via recurrence eq polynomials
        def p_via_recurrence(lam):
            p = [F(1)]  # p0
            # we need iterative: p_{i+1}= (1+d_i lam) p_i + lam sum_{j<i} T_{ij} p_j
            # at T=0 this is product
            cur = F(1)
            polys = [F(1)]
            for i in range(N):
                cur = (F(1)+ d[i]*lam)* (polys[-1] if polys else F(1))
                # Actually need to maintain p_i correctly; simpler direct product
                polys.append(cur)
                # But for T=0, recurrence reduces to product; verify
            return cur
        # direct product
        lam = F(1,3)
        prod = F(1)
        for i in range(N):
            prod *= (F(1)+ d[i]*lam)
        # recurrence computed via W_from_d_T then building p_N via definition (eq polynomial)
        # Build p_N coefficients from d,T via same recurrence on polynomial coefficients
        # Use coefficient list ascending
        def build_p_coeffs(d,T,N):
            # p_i as list len i+1
            p = [[F(1)]]  # p0
            for i in range(N):
                # p_{i+1}(lam)= (1+d_i lam) p_i(lam) + lam sum_{j<i} T_{ij} p_j(lam)
                pi = p[i]
                # (1+d_i lam)* pi
                ext = [F(0)]*(len(pi)+1)
                for idx, coeff in enumerate(pi):
                    ext[idx] += coeff
                    ext[idx+1] += d[i]*coeff
                # add lam* sum T_{ij} p_j
                add_term = [F(0)]*len(ext)
                for j in range(i):
                    if T[i][j]==0:
                        continue
                    pj = p[j]
                    # lam * pj -> shift by 1
                    for idx, coeff in enumerate(pj):
                        if idx+1 < len(add_term):
                            add_term[idx+1] += T[i][j]*coeff
                        else:
                            add_term.append(T[i][j]*coeff)
                            ext.append(F(0))
                # ensure same length
                L = max(len(ext), len(add_term))
                ext += [F(0)]*(L-len(ext))
                add_term += [F(0)]*(L-len(add_term))
                nxt = [ext[k]+ add_term[k] for k in range(L)]
                # trim
                while len(nxt)>1 and nxt[-1]==0:
                    nxt.pop()
                p.append(nxt)
            return p[N]
        pcoeff = build_p_coeffs(d,T,N)
        # evaluate at lam
        val = sum(c* (lam**i) for i,c in enumerate(pcoeff))
        assert val == prod, f"product mismatch N={N} {val} vs {prod}"
        print(f"N={N} d={d} lam=1/3 product {prod} == recurrence {val} OK")
    return True

def main():
    import io, contextlib
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        a = test_rank_formula()
        b = test_loci()
        c = test_product()
        print("\nAll rank checks:", "PASS" if (a and b and c) else "FAIL")
    out = buf.getvalue()
    print(out, end="")
    (LOGDIR / "rank_checks.log").write_text(out)
    print(f"Log written to {LOGDIR / 'rank_checks.log'}")
    if not (a and b and c):
        sys.exit(1)

if __name__ == "__main__":
    main()
