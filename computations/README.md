# Reproducibility — computations/

Exact and numerical reproduction for Mathathon 32: Memory-constrained minimax first-order optimization.

## Verified clean inputs (unchanged)
- `inputs/memory-minimax-semialgebraic.tex`: 65031 bytes, SHA-256 `529107e716e5ad5c100d5371b7275eeb3da7041a46ebe998ab154aabab86630e`
- `inputs/quadratic-memory-certificates.py`: SHA-256 `0698f6bff883c1a797dd3f31088ea5eb803f2049a9d848311d0f1af4a27fde33`

## Dependencies
- Python 3.10+ (tested locally on 3.12.8), standard library only: `fractions.Fraction`, `json`, `itertools`, `math`, `pathlib`
- No third-party packages for exact checks; numpy optional for numeric cross-checks only

## Fixed ranges and deterministic inputs (no RNG)
- Quadratic certificates: `N = 1..20` deterministic; threshold = 3/(4 M^2) with M=2N+1
- Rank locus checks: `N = 1..8`, witness matrices via deterministic formula `W[i][j]=(i*j+i+j) mod 5 -2` (or `W[i][j]=(i*2+j*3+1)%5 -2`), factored witness `T_ij=u_i v_j`, product formula with `d_i=-1/(i+2)`
- OGM checks: `N = 1..10`, `L=1,R=1` baseline + `L=2,R=3` scaling, deterministic theta recurrence
- Projected recurrence: `N = 1..6`, deterministic vectors `g_k=0.5*(-1)^k (k+1)/2` and fixed x0, projections onto ReLU `[0,inf)` and half-space `R x [0,inf)` via max(.,0)

All inputs are fixed deterministic formulas; no random seeding.

## What is verified and how
1. **Quadratic polynomial certificate — exact rational:** identity `M^{-2} - z p(z)^2 = (1-z)s(z)^2` and strict Gram PSD `A=ε e0e0ᵀ, B=A+ssᵀ` via `Fraction`. Reruns supplied `quadratic-memory-certificates.py` unchanged plus Gram-matrix inspection for N=3,7,10. Exact rational, no floats.
2. **Cut-rank / memory loci — exact rational:** rank of `H_k` and `S_k` via Fraction Gaussian elimination, sampled checks of `rank H_k = 1+rank S_k`, zero-matrix membership (not `Q0={0}`) and minor-vanishing equivalence, factored rank-1 witness, product formula at `T=0`. Exact rational on fixed ranges; no universal proof.
3. **OGM construction — numerical (tolerance 1e-9):** theta recurrence, `c_N=LR^2/2θ_N^2`, coefficients `d_O`, increment `T_O` and non-zero `T_10`, rank ≤1 via float Gaussian elimination with tolerance. Not exact rational (theta involves sqrt). Numerical evidence retained.
4. **Projected recurrence — numerical (tolerance 1e-9):** history formula `x_i = x0 + Σ a_ij g_j + Σ δ_ℓ` with `δ=Π_K(u)-u`, inactive vs active cases, cut-rank preservation with δ corrections via float elimination. Not exact rational.

Checks supplement report proofs; they do not replace them.

## How to rerun (each script writes its own log)
```bash
python3 computations/rerun_quadratic_certificates.py  # writes computations/logs/quadratic_rerun.log (exact)
python3 computations/rank_checks.py               # writes computations/logs/rank_checks.log (exact)
python3 computations/ogm_checks.py                # writes computations/logs/ogm_checks.log (numerical)
python3 computations/projected_recurrence_checks.py # writes computations/logs/projected_recurrence_checks.log (numerical)
# Or via shell redirection:
python3 computations/rank_checks.py | tee computations/logs/rank_checks.log
```

All scripts exit 0 on success, non-zero on failure. Logs are also produced by shell redirection as shown; both methods retained.

## Provenance and AI disclosure
Computations executed Nov 15 2026 UTC. All current paper development occurred Nov 13 8PM–Nov 15 noon Pacific 2026. Code assistance via Ultramath `meta/muse-spark-open` (reasoning_effort=max) under author direction; outputs reviewed by the coordinating agents and rerun locally; human author review is not asserted. No unprovided minimax values used; no cohomology.
