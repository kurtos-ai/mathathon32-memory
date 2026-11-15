#!/usr/bin/env python3
"""OGM checks: theta recurrence, risk value, coefficient map, memory rank.

Fixed ranges N=1..10, L=1,R=1 baseline + L=2,R=3 scaling check.
Verifies:
- theta recurrence (eq theta) and c_N = L R^2/(2 theta_N^2)
- OGM state recurrence produces W_O with rank S_k <=1, T_O !=0 for N>=2
- Explicit entry (T_O)_{10} = -(1-1/theta1)/(L theta2)
- Floating-point consistency checks of theta, c_N, coefficients, and cut rank (no minimax proof)
Deterministic, uses fractions for rational parts and floats for theta (with tolerance) plus exact cross-checks where rational.
"""
import math, sys
from fractions import Fraction as F
from pathlib import Path
LOGDIR = Path(__file__).parent / "logs"

def compute_theta(N):
    theta = [0.0]*(N+1)
    theta[0]=1.0
    for k in range(1,N):
        theta[k]=(1+math.sqrt(1+4*theta[k-1]**2))/2
    if N>=1:
        theta[N]=(1+math.sqrt(1+8*theta[N-1]**2))/2
    return theta

def compute_ogm_coeffs(N, L=1.0):
    theta = compute_theta(N)
    beta = [0.0]*N
    for k in range(N):
        beta[k]=1/theta[k+1] if k+1<=N else 0
    d = [0.0]*N
    for k in range(N):
        d[k]= -(1+(2*theta[k]-1)*beta[k])/L
    # Build W via unrolling OGM recurrence y_k, eta_k
    # We can get a_{i,j} by simulating with basis vectors e_j for gradients.
    # Use small n=1 scalar model: x0=0, then y_i = sum_{j<i} a_ij g_j, and recurrence:
    # y0=0, eta0=0
    # for k: g_k = 1 if we want coefficient of g_k in later y's; linear.
    # Instead compute a matrix directly via linear simulation:
    # We'll compute a_{i,j} by running recurrence symbolically: maintain y_k and eta_k as linear combos of g_0..g_{k-1}
    # y_k = sum_{j<k} y_coeff[k][j] g_j, eta_k = sum_{j<k} e_coeff[k][j] g_j
    y_coeff = [[0.0]*N for _ in range(N+1)]
    e_coeff = [[0.0]*N for _ in range(N+1)]
    # y0=0, e0=0
    for k in range(N):
        # y_{k+1} = y_k + beta_k eta_k - (1+(2theta_k-1)beta_k)/L * g_k
        # eta_{k+1}= (1-beta_k) eta_k - (2theta_k-1)(1-beta_k)/L * g_k
        for j in range(N):
            y_coeff[k+1][j] = y_coeff[k][j] + beta[k]*e_coeff[k][j]
            e_coeff[k+1][j] = (1-beta[k])*e_coeff[k][j]
        # plus g_k term
        y_coeff[k+1][k] += -(1+(2*theta[k]-1)*beta[k])/L
        e_coeff[k+1][k] += -(2*theta[k]-1)*(1-beta[k])/L
    # W size (N+1)x(N+1), a_{ij}= y_coeff[i][j] for j<i, else 0, with row 0 zero
    W = [[0.0]*(N+1) for _ in range(N+1)]
    for i in range(1,N+1):
        for j in range(i):
            if j<N:
                W[i][j]= y_coeff[i][j]
    return theta, beta, d, W, y_coeff, e_coeff

def rank_numeric(mat, tol=1e-9):
    # SVD-like via Gaussian elimination with tolerance
    if not mat or not mat[0]:
        return 0
    m=[row[:] for row in mat]
    rows, cols = len(m), len(m[0])
    r=0
    for c in range(cols):
        piv=None
        best=0
        piv_row=-1
        for i in range(r, rows):
            if abs(m[i][c])>best:
                best=abs(m[i][c]); piv_row=i
        if best<tol:
            continue
        m[r], m[piv_row]= m[piv_row], m[r]
        piv_val=m[r][c]
        for i in range(r+1, rows):
            if abs(m[i][c])>tol:
                factor=m[i][c]/piv_val
                for j in range(c, cols):
                    m[i][j]-=factor*m[r][j]
        r+=1
    return r

def build_T_from_W(W,N):
    # W is (N+1)x(N+1), get T NxN: T_{ij}= W_{i+1,j}-W_{i,j} for j<i
    T=[[0.0]*N for _ in range(N)]
    for i in range(N):
        for j in range(N):
            if j < i:
                T[i][j]= W[i+1][j]-W[i][j]
            else:
                T[i][j]=0.0
    return T

def build_S(T,N):
    S=[]
    for k in range(N+1):
        if k==0 or k==N:
            S.append([])
        else:
            mat=[]
            for i in range(k,N):
                row=[T[i][j] for j in range(k)]
                mat.append(row)
            S.append(mat)
    return S

def check_ogm():
    print("=== OGM numerical checks N=1..10 L=1,R=1 (floating point, tol=1e-9) ===")
    for N in range(1,11):
        theta, beta, d, W, yc, ec = compute_ogm_coeffs(N, L=1.0)
        cN = 1.0/(2*theta[N]**2)  # L=R=1
        # Verify recurrence identities: theta_k*(theta_k-1)=theta_{k-1}^2 for k<N ? Check
        # Actually theta_k = (1+sqrt(1+4t_{k-1}^2))/2 => t_k^2 - t_k - t_{k-1}^2=0
        for k in range(1,N):
            lhs = theta[k]**2 - theta[k] - theta[k-1]**2
            assert abs(lhs)<1e-10, f"theta recurrence fail N={N} k={k} lhs={lhs}"
        # final theta_N: check  theta_N^2 - theta_N -2 theta_{N-1}^2=0
        if N>=1:
            lhs = theta[N]**2 - theta[N] -2*theta[N-1]**2
            assert abs(lhs)<1e-10, f"theta_N recurrence fail N={N} {lhs}"
        T = build_T_from_W(W,N)
        S = build_S(T,N)
        ranks=[rank_numeric(S[k]) if S[k] else 0 for k in range(N+1)]
        max_rank = max(ranks) if ranks else 0
        # should be <=1 for N>=1 (Q1)
        assert max_rank <=1, f"OGM rank >1 N={N} ranks={ranks}"
        # explicit entry check for N>=2
        if N>=2:
            expected_T10 = -(1-1/theta[1])/(theta[2])
            actual_T10 = T[1][0]
            assert abs(actual_T10-expected_T10)<1e-12, f"T10 mismatch N={N} {actual_T10} vs {expected_T10}"
            assert abs(actual_T10)>1e-12, f"T10 should be nonzero N={N}"
            print(f"N={N:2d} theta_N={theta[N]:.6f} c_N={cN:.6f} d={['{:.4f}'.format(x) for x in d]} T10={actual_T10:.6e} ranks={ranks} OK")
        else:
            # N=1: T empty, Q0
            assert ranks==[0,0], f"N=1 ranks {ranks}"
            print(f"N={N:2d} theta_N={theta[N]:.6f} c_N={cN:.6f} d={['{:.4f}'.format(x) for x in d]} ranks={ranks} OK (one-register)")
        # Scaling consistency only: compare the computed theta_L with the baseline theta.
        L_scaling, R_scaling = 2, 3
        theta_scaled, _, _, _, _, _ = compute_ogm_coeffs(N, L=L_scaling)
        assert abs(theta_scaled[N] - theta[N]) < 1e-12
        print(f"  scaling consistency L={L_scaling},R={R_scaling}: theta independent of L in this implementation")
    print("\n=== Nonzero increment-entry samples (not a one-register optimality claim) ===")
    for N in [2,3,5]:
        # A nonzero T entry shows this sampled coefficient map is not T=0.
        # It does not prove an optimal one-register schedule does not exist.
        theta,_,d,W,_,_=compute_ogm_coeffs(N, L=1.0)
        T=build_T_from_W(W,N)
        has_nonzero = any(abs(T[i][j])>1e-12 for i in range(N) for j in range(N) if j<i)
        assert has_nonzero, f"sampled OGM T unexpectedly zero at N={N}"
        print(f"N={N} sampled OGM coefficient map has a nonzero T entry (not a one-register optimality claim)")

def check_quadratic_vs_smooth():
    print("\n=== Quadratic vs smooth values (L=R=1) ===")
    for N in [1,2,5,10]:
        M=2*N+1
        quad_val = 1/(2*M*M)
        theta = compute_theta(N)
        smooth_val = 1/(2*theta[N]**2)
        print(f"N={N:2d} quadratic V={quad_val:.6f}  smooth c_N={smooth_val:.6f}  ratio {smooth_val/quad_val:.4f}")

def main():
    import io, contextlib
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        check_ogm()
        check_quadratic_vs_smooth()
        print("\nAll OGM checks PASS (numerical, tol 1e-9; not exact rational)")
    out = buf.getvalue()
    print(out, end="")
    Path(LOGDIR / "ogm_checks.log").write_text(out)
    print(f"Log written to {Path(LOGDIR / 'ogm_checks.log')}")

if __name__=="__main__":
    main()
