module
public import Submission2026.QuadraticReplacement.RealFactors
@[expose] public section
noncomputable section
namespace QuadraticReplacement
open Polynomial

abbrev Step := ℝ × ℝ

def stepPolynomial (s : Step) (z : ℝ[X] × ℝ[X]) : ℝ[X] × ℝ[X] :=
  (z.2,(1+C s.1*X)*z.2+C s.2*X*z.1)

def runPolynomial : List Step → (ℝ[X] × ℝ[X]) → (ℝ[X] × ℝ[X])
  | [],z => z
  | s::ss,z => runPolynomial ss (stepPolynomial s z)

lemma runPolynomial_append (a b : List Step) (z : ℝ[X] × ℝ[X]) :
    runPolynomial (a++b) z=runPolynomial b (runPolynomial a z) := by
  induction a generalizing z  <;> simp_all [runPolynomial]

def factorSteps (p : ℝ[X]) : List Step :=
  if p.natDegree  ≤  1 then [(p.coeff 1,0)]
  else [(1,0),(p.coeff 2,p.coeff 1-p.coeff 2-1)]

lemma factorSteps_length (p : ℝ[X]) (hd : 1  ≤  p.natDegree ∧ p.natDegree  ≤  2) :
    (factorSteps p).length=p.natDegree := by
  unfold factorSteps
  split  <;> simp only [List.length_cons,List.length_nil]  <;> omega

lemma run_factorSteps (p : ℝ[X]) (hp : p.eval 0=1) (hd : p.natDegree  ≤  2)
    (z : ℝ[X] × ℝ[X]) : (runPolynomial (factorSteps p) z).2=p*z.2 := by
  by_cases h : p.natDegree  ≤  1
  · rw [factorSteps,ite_eq_left h]
    simp only [runPolynomial,stepPolynomial,map_zero,mul_zero,zero_mul,add_zero]
    rw [← linear_form p hp h]
  · rw [factorSteps,ite_eq_right h]
    simp only [runPolynomial,stepPolynomial,map_zero,map_one,mul_zero,zero_mul,add_zero]
    conv_rhs => rw [low_degree_form p hp hd]
    simp only [map_sub,map_one]
    ring

def allFactorSteps (fs : List ℝ[X]) : List Step := fs.flatMap factorSteps

lemma allFactorSteps_length (fs : List ℝ[X])
    (hd : ∀ f ∈ fs,1  ≤  f.natDegree ∧ f.natDegree  ≤  2) :
    (allFactorSteps fs).length=(fs.map Polynomial.natDegree).sum := by
  induction fs with
  | nil => simp [allFactorSteps]
  | cons p ps ih =>
    simp only [allFactorSteps,List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons]
    rw [factorSteps_length p (hd p (by simp))]
    exact congrArg (p.natDegree + ·) (ih (fun f hf => hd f (by simp [hf])))

lemma run_allFactorSteps (fs : List ℝ[X])
    (h : ∀ f ∈ fs,f.eval 0=1 ∧ f.natDegree  ≤  2) (z : ℝ[X] × ℝ[X]) :
    (runPolynomial (allFactorSteps fs) z).2=fs.prod*z.2 := by
  induction fs generalizing z with
  | nil => simp [allFactorSteps,runPolynomial]
  | cons p ps ih =>
    rw [show allFactorSteps (p::ps)=factorSteps p++allFactorSteps ps from rfl,
      runPolynomial_append,ih (fun f hf => h f (by simp [hf])),
      run_factorSteps p (h p (by simp)).1 (h p (by simp)).2]
    simp only [List.prod_cons]
    ring

lemma run_zero_steps (k : ℕ) (z : ℝ[X] × ℝ[X]) :
    (runPolynomial (List.replicate k (0,0)) z).2=z.2 := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ,runPolynomial,stepPolynomial] using ih (z.2,z.2)

/-- Every normalized real residual polynomial is implemented by a sequence of
one- or two-call blocks, with zero steps padding to the prescribed budget. -/
theorem exists_factor_steps (N : ℕ) (p : ℝ[X]) (hp : p.eval 0=1) (hd : p.natDegree  ≤  N) :
    ∃ ss : List Step,ss.length=N ∧ (runPolynomial ss (0,1)).2=p := by
  obtain ⟨fs,hprod,hall,hdeg⟩ := exists_normalized_factors p hp
  let ss := allFactorSteps fs
  have hs : ss.length=p.natDegree :=
    (allFactorSteps_length fs (fun f hf => (hall f hf).2)).trans hdeg
  refine ⟨ss++List.replicate (N-ss.length) (0,0),?_,?_⟩
  · simp only [List.length_append,List.length_replicate]
    omega
  · rw [runPolynomial_append,run_zero_steps,
      run_allFactorSteps fs (fun f hf => ⟨(hall f hf).1,(hall f hf).2.2⟩),hprod,mul_one]

end QuadraticReplacement
