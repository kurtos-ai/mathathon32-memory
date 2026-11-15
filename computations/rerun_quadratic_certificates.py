#!/usr/bin/env python3
"""Rerun supplied exact arithmetic script over fixed range N=1..20, capturing logs.
Supplement with degree, normalization, PSD checks. Deterministic, no RNG.
"""
import subprocess, json, sys, os
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "inputs" / "quadratic-memory-certificates.py"
LOGDIR = Path(__file__).parent / "logs"
LOGDIR.mkdir(exist_ok=True)

def run_one(N, threshold=None):
    cmd = [sys.executable, str(SCRIPT), "--N", str(N)]
    if threshold is not None:
        cmd += ["--threshold", str(threshold)]
    # also test --include-matrices for a few N
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"N={N} threshold={threshold} failed: {result.stderr}")
    return json.loads(result.stdout)

def run_one_matrices(N, threshold):
    cmd = [sys.executable, str(SCRIPT), "--N", str(N), "--threshold", str(threshold), "--include-matrices"]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"matrices N={N} failed: {result.stderr}")
    return json.loads(result.stdout)

def main():
    print("=== Quadratic memory certificates: exact rerun N=1..20 ===")
    print(f"Script: {SCRIPT}")
    print(f"Python: {sys.version.split()[0]}")
    # verify hashes
    import hashlib
    for p in [ROOT/"inputs"/"memory-minimax-semialgebraic.tex", ROOT/"inputs"/"quadratic-memory-certificates.py"]:
        h = hashlib.sha256(p.read_bytes()).hexdigest()
        print(f"SHA256 {p.name}: {h}")
    outputs = {}
    failures = 0
    for N in range(1, 21):
        M = 2*N+1
        bound = F(1, 2*M*M)
        # choose threshold strictly above bound: bound + 1/(4*M*M)
        # = 3/(4*M*M) ?? Let's compute epsilon=1/(4*M*M) => threshold = 3/(4*M*M)
        threshold = F(3, 4*M*M)
        # Ensure threshold > bound: 3/4 > 1/2 yes
        try:
            out = run_one(N, str(threshold))
            assert out["risk_bound"] == str(bound), f"risk_bound mismatch N={N}"
            assert out["polynomial_identity"] == "verified exactly"
            assert out["strict_Gram_identity"] == "verified exactly"
            # check p_star[0]==1 and degree N
            coeffs = [F(c) for c in out["p_star_ascending_coefficients"]]
            assert coeffs[0] == 1, f"p_star[0] !=1 N={N}"
            assert len([c for c in coeffs if c != 0]) <= N+1
            # check without threshold as well
            out2 = run_one(N)
            assert out2["M"] == M
            print(f"N={N:2d} M={M:2d} risk_bound={bound} threshold={threshold} epsilon={F(threshold)-bound} OK  p_deg={len(coeffs)-1}")
            outputs[N] = out
        except Exception as e:
            print(f"N={N} FAILED: {e}", file=sys.stderr)
            failures += 1
    # spot-check matrices for N=3,7,10
    for N in [3,7,10]:
        M = 2*N+1
        thr = F(3, 4*M*M)
        outm = run_one_matrices(N, str(thr))
        A = [[F(x) for x in row] for row in outm["A"]]
        B = [[F(x) for x in row] for row in outm["B"]]
        # verify A = epsilon e0e0^T
        eps = F(outm["epsilon"])
        assert A[0][0] == eps and all(A[i][j]==0 for i in range(N+1) for j in range(N+1) if not (i==0 and j==0)), f"A structure N={N}"
        svec = [F(c) for c in outm["s_N_ascending_coefficients"]]
        assert all(B[i][j] == A[i][j] + svec[i] * svec[j] for i in range(N+1) for j in range(N+1)), f"B structure N={N}"
        assert eps > 0
        print(f"N={N} matrices verified: eps={eps} A[0,0]={A[0][0]} B PSD construction OK")
    # write log
    log_path = LOGDIR / "quadratic_rerun.log"
    with open(log_path, "w") as f:
        f.write("Quadratic certificates rerun N=1..20\n")
        for N in outputs:
            f.write(json.dumps(outputs[N])+"\n")
    print(f"\nLog written to {log_path}")
    print(f"Total: {20-failures}/20 passed, {failures} failures")
    if failures:
        sys.exit(1)
    print("All quadratic certificates verified exactly.")

if __name__ == "__main__":
    main()
