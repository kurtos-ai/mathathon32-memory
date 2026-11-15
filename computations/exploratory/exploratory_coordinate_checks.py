"""EXPLORATORY numpy coordinate checks on the normalization conjugation.

**NOT a proof certificate.** These are numeric probes used by the coordinator while writing its hand-off notes.
One of them (the very first attempt) is mathematically wrong in a way worth keeping visible: it took an arbitrary
matrix `A` that satisfied neither `A ones = e1` nor `e1ᵀ A = e1ᵀ` simultaneously, so it tested the identity on a
matrix outside the actual hypotheses. The correct example the person then supplied literally, `A = [[1,0],[-1,1]]`,
passes both identities. The inline probes are reconstructed below, with explanatory comments.

Rough sources: the original one-liners were inline `python3 - <<'PY'` snippets inside shell commands;
this file collects the probes and their output.
"""
import numpy as np

print("=== 1. WRONG / RETRACTED probe — arbitrary matrices violating the hypotheses ===")
# This is a non-example.  A = [[.5,.5],[.5,-.5]]:  A ones = (1,0) = e1, but its first row is [0.5, 0.5],
# so e1ᵀ A = [0.5,0.5] ≠ e1ᵀ.  The earlier estimate printed "e1^T A = [ 0.5 -0.5]":  this was from the
# OTHER candidate where A ones = [0,1], also broken.  Do not quote any conclusion this section draws.
A = np.array([[.5,.5],[.5,-.5]])
Ai = np.linalg.inv(A)
e1 = np.array([1.,0.]); ones = np.array([1.,1.])
print("A ones =", A@ones, "(=e1), but first row of A =", A[0], "so e1ᵀ A =", e1@A, "≠ e1ᵀ")
print("Ainv e1 =", Ai@e1)
print("FIRST ROW of the probe actually used instead of A_fixed:")
A = np.array([[.5,-.5],[.5,.5]])
print("A =", A, " with A ones =", A@ones, " (INVALID for the hypotheses)")
# The erroneous conclusion I drew from this erroneous A — reproduced as a historical note only.
F = np.array([[2.,-1],[3,-2]])
Fp = A@F@np.linalg.inv(A)
print("F' = A F Ainv =", np.round(Fp,3))
print("e1ᵀ F' A =", np.round(e1@Fp@A,3), " versus e1ᵀ F =", e1@F)
# This is why 'identity e1ᵀ(A F Ainv)v = e1ᵀ(F v)' looked violated: my A wasn't in the stated class.

print("=== 2. CORRECT examples: 2×2 and a general [[a,b],[c,d]] parameterization ===")
# The corrected pair that DOES satisfy both identities, as the person supplied:
A = np.array([[1.,0.],[-1.,1.]])
Ai = np.array([[1.,0.],[1.,1.]])
print("A =", A.tolist(), " Ainv =", Ai.tolist())
print("A ones =", A@ones, "(should be e1)")
print("e1ᵀ A =", e1@A, "(should be e1ᵀ)")
print("A Ainv =", A@Ai, " Ainv A =", Ai@A)
F = np.array([[2.,-1],[3,-2]])
print("F ones =", F@ones)
Fp = A@F@Ai
print("F' = A F Ainv =", Fp)
print("F' e1 =", Fp@e1, "(should be e1)")
print("e1ᵀ F' A =", e1@(Fp@A), "versus e1ᵀ F =", e1@F, "(should be equal)")
print("e1ᵀ (A v) == e1ᵀ v for random v :", np.allclose(e1@(A@np.array([3.,7.])), e1@np.array([3.,7.])))

print("=== 3. General a+b=1 form (for reference) ===")
# A = [[1,0],[-1,1]] is the special case [[a,b],[c,d]] with a+b=1, c+d=0, determinant a·d-b·c ≠ 0.
# This member satisfies A ones=e1, but fails first-row preservation.
A = np.array([[.5,.5],[.5,-.5]])
Ai = np.linalg.inv(A)
print("A =", A, " satisfies A ones =", A@ones, " (=e1) and first row = e1ᵀ? first row =", A[0])
print("Ainv e1 =", Ai@e1, "(should be ones)")
# F' = A F Ainv does NOT generically have ones as a right eigenvector; it has e1.
print("F' e1 (should be e1):", (A@F@Ai)@e1, " F' ones (not fixed, expected not ones):", (A@F@Ai)@ones)

print("=== DONE ===")
