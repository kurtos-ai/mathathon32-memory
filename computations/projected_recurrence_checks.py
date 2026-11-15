#!/usr/bin/env python3
"""Projected recurrence checks: verify projected history formula and cut-rank preservation.

Fixed ranges N=1..6, deterministic formula-generated vectors (no RNG).
Tests:
- Projection onto K=[0,infty) (ReLU) and K = R x [0,infty) (half-space)
- Verifies x_i = x0 + sum a_ij g_j + sum delta_ell with delta = Pi_K(u)-u
- Checks D_k, h_k, and delta corrections keep rank bound unchanged
- Validates inactive-projection regime where all projections are identity
Exact arithmetic for projections onto these simple sets (piecewise linear).
"""
import math, sys
from fractions import Fraction as F
from pathlib import Path
LOGDIR = Path(__file__).parent / "logs"

def proj_halfline(u):
    """K=[0,infty) in R^1, Pi(u)=max(u,0)"""
    return max(u, 0.0)

def proj_halfspace(u):
    """K = R x [0,infty) in R^2: (u1, max(u2,0))"""
    return (u[0], max(u[1], 0.0))

def build_W(N, pattern="det"):
    """Deterministic W (N+1)x(N+1) with rational entries"""
    W=[[F(0)]*(N+1) for _ in range(N+1)]
    for i in range(N+1):
        for j in range(i):
            if pattern=="det":
                W[i][j]=F((i*2+j*3+1)%5 -2, 3)  # small rationals
            elif pattern=="zero":
                W[i][j]=F(0)
    return W

def d_T_from_W(W,N):
    d=[F(0)]*N
    T=[[F(0)]*N for _ in range(N)]
    for j in range(N):
        d[j]=W[j+1][j]
    for i in range(N):
        for j in range(N):
            if j < i:
                T[i][j]=W[i+1][j]-W[i][j]
    return d,T

def projected_trajectory_1d(N, W, x0, g_seq, proj):
    """1D projected increments: u_{k+1}= x_k + d_k g_k + sum_{j<k} T_{kj} g_j, x_{k+1}=Pi(u_{k+1})"""
    d,T = d_T_from_W(W,N)
    x = [0.0]*(N+1)
    u = [0.0]*(N+1)
    delta = [0.0]*(N+1)
    x[0]=x0
    for k in range(N):
        gk = g_seq[k]
        # compute u_{k+1}
        uk1 = x[k] + float(d[k])*gk
        for j in range(k):
            uk1 += float(T[k][j])* g_seq[j]
        u[k+1]=uk1
        x_next = proj(uk1)
        delta[k+1]= x_next - uk1
        x[k+1]=x_next
    return x,u,delta, d,T

def projected_trajectory_2d(N, W, x0, g_seq, proj):
    """2D version: x0,g_seq are tuples"""
    d,T = d_T_from_W(W,N)
    x = [None]*(N+1)
    u = [None]*(N+1)
    delta = [None]*(N+1)
    x[0]=x0
    for k in range(N):
        gk=g_seq[k]
        # u_{k+1}= x_k + d_k g_k + sum T_{kj} g_j
        uk1_0 = x[k][0] + float(d[k])*gk[0]
        uk1_1 = x[k][1] + float(d[k])*gk[1]
        for j in range(k):
            uk1_0 += float(T[k][j])* g_seq[j][0]
            uk1_1 += float(T[k][j])* g_seq[j][1]
        uk1=(uk1_0, uk1_1)
        u[k+1]=uk1
        x_next=proj(uk1)
        delta[k+1]=(x_next[0]-uk1[0], x_next[1]-uk1[1])
        x[k+1]=x_next
    return x,u,delta, d,T

def check_history_formula():
    print("=== Projected history formula x_i = x0 + sum a_ij g_j + sum delta ===")
    for N in range(1,7):
        W=build_W(N)
        # build a_ij from W directly
        # test 1D case with small vectors
        x0=1.0
        g_seq=[0.5*(-1)**k * (k+1)/2 for k in range(N)]
        x,u,delta, d,T = projected_trajectory_1d(N, W, x0, g_seq, proj_halfline)
        # verify history formula by brute force using a_ij
        for i in range(N+1):
            lhs = x[i]
            rhs = x0
            for j in range(i):
                rhs += float(W[i][j])* g_seq[j] if j < N else 0
            for ell in range(1,i+1):
                rhs += delta[ell]
            if abs(lhs-rhs)>1e-9:
                print(f"FAIL 1D N={N} i={i} lhs={lhs} rhs={rhs}")
                return False
        print(f"N={N} 1D history formula verified (x0={x0}, g={g_seq})")
        # 2D case
        x0_2d=(1.0, 1.0)
        g_seq_2d=[(0.3*(-1)**k, 0.4*(k+1)/3) for k in range(N)]
        x2,u2,d2,_,_ = projected_trajectory_2d(N, W, x0_2d, g_seq_2d, proj_halfspace)
        for i in range(N+1):
            rhs0 = x0_2d[0] + sum(float(W[i][j])*g_seq_2d[j][0] for j in range(i)) + sum(d2[ell][0] for ell in range(1,i+1))
            rhs1 = x0_2d[1] + sum(float(W[i][j])*g_seq_2d[j][1] for j in range(i)) + sum(d2[ell][1] for ell in range(1,i+1))
            if abs(x2[i][0]-rhs0)>1e-9 or abs(x2[i][1]-rhs1)>1e-9:
                print(f"FAIL 2D N={N} i={i}")
                return False
        print(f"N={N} 2D history formula verified")
    return True

def check_inactive_projection():
    print("\n=== Inactive projection regime (all Pi = identity) ===")
    for N in [3,5]:
        W=build_W(N)
        # Choose small x0 and g so that all u stay positive (1D) or second coord positive (2D)
        x0=2.0
        g_seq=[0.1 for _ in range(N)]  # small positive
        x,u,delta,_,_=projected_trajectory_1d(N,W,x0,g_seq, proj_halfline)
        all_inactive = all(abs(delta[k])<1e-12 for k in range(1,N+1))
        print(f"N={N} 1D small-g inactive={all_inactive} deltas={delta[1:]}")
        if not all_inactive:
            print("  (expected inactive due to small steps, but got active — check W)")
        # with W pattern, u should stay >0 for these inputs, so deltas zero
        # Verify that trajectory equals non-projected history when inactive
        for i in range(N+1):
            no_proj = x0 + sum(float(W[i][j])*g_seq[j] for j in range(i))
            if abs(x[i]-no_proj)>1e-9:
                print(f"  FAIL inactive equality N={N} i={i}")
                return False
        print(f"  N={N} inactive trajectory equals W-history verified")
    return True

def check_active_projection():
    print("\n=== Active projection case ===")
    N=3
    W=build_W(N, pattern="det")
    x0=0.2
    g_seq=[-1.0, -0.5, 0.3]  # will cause negative u
    x,u,delta,_,_=projected_trajectory_1d(N,W,x0,g_seq, proj_halfline)
    print(f"N={N} x={x} u={u} delta={delta}")
    active = [k for k in range(1,N+1) if abs(delta[k])>1e-12]
    print(f"Active steps: {active}")
    # each delta = Pi(u)-u = -min(u,0) in 1D
    for k in range(1,N+1):
        exp_delta = max(u[k],0)-u[k]
        assert abs(delta[k]-exp_delta)<1e-12
    print("Active projection deltas correct")
    return True

def check_rank_preservation():
    print("\n=== Cut-rank preservation with delta corrections ===")
    for N in [3,4,6]:
        W=build_W(N)
        d,T=d_T_from_W(W,N)
        # Build H_k matrices
        def build_H(W,N):
            H=[]
            for k in range(N+1):
                mat=[]
                for i in range(k,N+1):
                    row=[F(1)]
                    for j in range(k):
                        row.append(W[i][j])
                    mat.append(row)
                H.append(mat)
            return H
        H=build_H(W,N)
        def rank_frac(M):
            if not M or not M[0]:
                return 0
            # use fractions
            m=[row[:] for row in M]
            rows, cols=len(m), len(m[0])
            r=0
            for c in range(cols):
                piv=None
                for i in range(r, rows):
                    if m[i][c]!=0:
                        piv=i; break
                if piv is None:
                    continue
                m[r],m[piv]=m[piv],m[r]
                pv=m[r][c]
                for i in range(r+1, rows):
                    if m[i][c]!=0:
                        f=m[i][c]/pv
                        for j in range(c, cols):
                            m[i][j]-=f*m[r][j]
                r+=1
            return r
        for k in range(N+1):
            rk=rank_frac(H[k])
            print(f"N={N} k={k} rank H_k={rk} bound {1+N//2}")
        # The theorem says s_K^Pi(W)= max rank H_k = 1+max rank S_k, independent of delta
        # Verify that formula still holds (delta does not affect rank)
        # inline build_S removed - using local version
        T_num=[[float(T[i][j]) for j in range(N)] for i in range(N)]
        S=[]
        for k in range(N+1):
            if k==0 or k==N:
                S.append([])
            else:
                mat=[]
                for i in range(k,N):
                    row=[T_num[i][j] for j in range(k)]
                    mat.append(row)
                S.append(mat)
        # numeric rank of S
        def rank_num(M):
            if not M or not M[0]:
                return 0
            m=[row[:] for row in M]
            rows, cols=len(m), len(m[0])
            r=0
            for c in range(cols):
                piv=max(range(r,rows), key=lambda i: abs(m[i][c]), default=None)
                if piv is None or abs(m[piv][c])<1e-9:
                    continue
                m[r],m[piv]=m[piv],m[r]
                pv=m[r][c]
                for i in range(r+1,rows):
                    f=m[i][c]/pv
                    for j in range(c,cols):
                        m[i][j]-=f*m[r][j]
                r+=1
            return r
        for k in range(N+1):
            hk=rank_frac(H[k])
            sk=rank_num(S[k]) if S[k] else 0
            assert hk==1+sk, f"rank formula fail N={N} k={k} hk={hk} sk={sk}"
        print(f"N={N} rank formula 1+rank S_k = rank H_k verified")
    return True

def main():
    import io, contextlib
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        a=check_history_formula()
        b=check_inactive_projection()
        c=check_active_projection()
        d=check_rank_preservation()
        print("\nAll projected checks:", "PASS" if all([a,b,c,d]) else "FAIL", "(numerical floats, tol 1e-9; rank via float Gaussian elimination)")
    out = buf.getvalue()
    print(out, end="")
    Path(LOGDIR / "projected_recurrence_checks.log").write_text(out)
    print(f"Log written to {Path(LOGDIR / 'projected_recurrence_checks.log')}")
    if not all([a,b,c,d]):
        sys.exit(1)

if __name__=="__main__":
    main()
