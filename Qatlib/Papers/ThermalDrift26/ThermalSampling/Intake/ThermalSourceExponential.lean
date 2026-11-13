/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.IdealThermalInstrument
import Qatlib.Concepts.RandCompile.ReferenceModel.LocalPauliEvolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exponential Form of Thermal Source Branches

This module identifies the weak-reflection instrument with exponential thermal updates in the
source construction of [JiangEtAl2026]. `signedPauliFamily` instantiates `ReflectionFamily` with
signed Pauli strings, while `reflection_exp` expresses the exponential of any involution using
hyperbolic functions.

For `a = Real.tanh (tau/2)`, `thermalStep_eq_weak` and `thermal_normalization` translate
individual and repeated instrument branches into products of `thermalStep`. The path probability
then becomes a product of index weights times the trace of the unnormalized thermal output.

## Main statements

- `reflection_exp` gives `exp(t*S) = cosh(t)*1 + sinh(t)*S` when `S*S = 1`.
- `idealInstrument_branch_thermal` gives the single-step exponential branch formula.
* `pathInstrument_branch_thermal` and `pathBornLaw_thermal` give the path branch and probability
  formulas.

## References

* [Jiang et al., 2026][JiangEtAl2026], *Thermal-Drift Sampling: Generating Thermal Ensembles for
  Learning Many-Body Systems*.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling

/-- The reflection family formed from `n`-qubit Pauli strings, negating the string at each index
where `negative` is true; Pauli Hermiticity and involutivity supply the required properties. -/
def signedPauliFamily (L n : ℕ) (negative : Fin L → Bool)
    (word : Fin L → Fin n → Fin 4) : ReflectionFamily L (2 ^ n) where
  sigma j := if negative j then -(Qatlib.Concepts.RandCompile.ReferenceModel.pauliStringMatrix n (word j)) else Qatlib.Concepts.RandCompile.ReferenceModel.pauliStringMatrix n (word j)
  hermitian j := by
    have hh :=
        (Qatlib.Concepts.RandCompile.ReferenceModel.local_pauli_string_contract_and_support n (word j)).1
    split
    · exact hh.neg
    · exact hh
  square j := by
    have hc :=
        Qatlib.Concepts.RandCompile.ReferenceModel.local_pauli_string_contract_and_support n
        (word j)
    have hsq : Qatlib.Concepts.RandCompile.ReferenceModel.pauliStringMatrix n (word j) * Qatlib.Concepts.RandCompile.ReferenceModel.pauliStringMatrix n (word j) = 1 := by
      have hu := (Matrix.mem_unitaryGroup_iff').mp hc.2.1
      simpa only [Matrix.star_eq_conjTranspose, hc.1.eq] using hu
    split
    · simpa only [neg_mul_neg] using hsq
    · exact hsq

/-- For an idempotent matrix `P` and complex scalar `t`, `exp(t*P) = I + (exp(t)-1)*P`. -/
private theorem exp_idempotent {d : ℕ} (P : Qatlib.Foundations.PureStateMath.Operator d) (hP : IsIdempotentElem P) (t : ℂ) :
    NormedSpace.exp (t • P) = 1 + (Complex.exp t - 1) • P := by
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) t).smul_const P
  have hz := hasSum_ite_eq (0 : ℕ) ((1 : Qatlib.Foundations.PureStateMath.Operator d) - P)
  have hsum := hs.add hz
  have he : (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (t • P) ^ n) =
      (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • t ^ n) • P + if n = 0 then 1 - P else 0) := by
    funext n
    cases n with
    | zero => simp
    | succ n => simp [smul_pow, hP.pow_succ_eq, smul_smul]
  have hm := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (t • P)
  rw [he] at hm
  have hu := hm.unique hsum
  rw [← Complex.exp_eq_exp_ℂ] at hu
  calc
    _ = Complex.exp t • P + (1 - P) := hu
    _ = _ := by
      simp only [sub_smul, one_smul]
      abel

/-- For any complex matrix `S` satisfying `S*S = I`, its exponential is `exp(t*S) = cosh(t)*I +
sinh(t)*S` for every complex `t`. -/
theorem reflection_exp {d : ℕ} (S : Qatlib.Foundations.PureStateMath.Operator d) (hS : S * S = 1) (t : ℂ) :
    NormedSpace.exp (t • S) = Complex.cosh t • (1 : Qatlib.Foundations.PureStateMath.Operator d) + Complex.sinh t • S := by
  let P : Qatlib.Foundations.PureStateMath.Operator d := (1 / 2 : ℂ) • (1 + S)
  let Q : Qatlib.Foundations.PureStateMath.Operator d := (1 / 2 : ℂ) • (1 - S)
  have hP : IsIdempotentElem P := by
    change P * P = P
    dsimp [P]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hS]
    ext i k
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hQ : IsIdempotentElem Q := by
    change Q * Q = Q
    dsimp [Q]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hS]
    ext i k
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hPQ : P * Q = 0 := by
    dsimp [P, Q]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hS]
    ext i k
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply,
        smul_eq_mul]
    ring
  have hQP : Q * P = 0 := by
    dsimp [P, Q]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hS]
    ext i k
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply,
        smul_eq_mul]
    ring
  have hx : t • S = t • P + (-t) • Q := by
    dsimp [P, Q]
    ext i k
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hc : Commute (t • P) ((-t) • Q) := by
    change (t • P) * ((-t) • Q) = ((-t) • Q) * (t • P)
    simp only [Matrix.smul_mul, Matrix.mul_smul, hPQ, hQP, smul_zero]
  calc
    _ = NormedSpace.exp (t • P + (-t) • Q) := congrArg NormedSpace.exp hx
    _ = _ := Matrix.exp_add_of_commute _ _ hc
    _ = (1 + (Complex.exp t - 1) • P) * (1 + (Complex.exp (-t) - 1) • Q) :=
      congrArg₂ (· * ·) (exp_idempotent P hP t) (exp_idempotent Q hQ (-t))
    _ = _ := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, hPQ, smul_zero, add_zero]
      dsimp [P, Q]
      ext i k
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.cosh, Complex.sinh]
      ring

/-- The exponential update `exp((tau/2)*sigma_j)` for sign `false` and `exp((-tau/2)*sigma_j)`
for sign `true`. -/
def thermalStep {L d : ℕ} (F : ReflectionFamily L d) (tau : ℝ) (j : Fin L) (b : Bool) : Qatlib.Foundations.PureStateMath.Operator d :=
  NormedSpace.exp (((if b then -tau / 2 else tau / 2 : ℝ) : ℂ) • F.sigma j)

/-- A thermal exponential step equals `cosh(tau/2)` times the weak-reflection operator with
parameter `tanh(tau/2)` and the same index and sign. -/
theorem thermalStep_eq_weak {L d : ℕ} (F : ReflectionFamily L d) (tau : ℝ)
    (j : Fin L) (b : Bool) :
    thermalStep F tau j b = (Real.cosh (tau / 2) : ℂ) •
      weakOperator F (Real.tanh (tau / 2)) j b := by
  have hc : Real.cosh (tau / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hmul : Real.cosh (tau / 2) * Real.tanh (tau / 2) = Real.sinh (tau / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  cases b <;>
    simp only [thermalStep, Bool.false_eq_true, reduceIte, weakOperator] <;>
    rw [reflection_exp _ (F.square j)]
  · rw [← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    simp only [smul_add, smul_smul, ← Complex.ofReal_mul, hmul]
  · have he : -tau / 2 = -(tau / 2) := by ring
    rw [he, Complex.ofReal_neg, Complex.cosh_neg, Complex.sinh_neg,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    simp only [smul_add, Complex.ofReal_neg, neg_smul, smul_neg, smul_smul,
      ← Complex.ofReal_mul, hmul]

/-- Each thermal exponential step equals its conjugate transpose for every real `tau`. -/
theorem thermalStep_hermitian {L d : ℕ} (F : ReflectionFamily L d) (tau : ℝ)
    (j : Fin L) (b : Bool) : (thermalStep F tau j b)ᴴ = thermalStep F tau j b := by
  have hj : (F.sigma j)ᴴ = F.sigma j := F.hermitian j
  unfold thermalStep
  rw [← Matrix.exp_conjTranspose]
  congr 1
  simp only [Matrix.conjTranspose_smul, hj, Complex.star_def, Complex.conj_ofReal]

/-- The hyperbolic normalization identity `2*(1+tanh(tau/2)^2)*cosh(tau/2)^2 = 2*cosh(tau)`
relates the weak and exponential source normalizations. -/
theorem thermal_normalization (tau : ℝ) :
    2 * (1 + Real.tanh (tau / 2) ^ 2) * Real.cosh (tau / 2) ^ 2 = 2 * Real.cosh tau := by
  have hc : Real.cosh (tau / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have ht : tau = 2 * (tau / 2) := by ring
  conv_rhs => rw [ht, Real.cosh_two_mul]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- At weak parameter `tanh(tau/2)`, the ideal branch `(j,b)` is the sandwich by `thermalStep F
tau j b`, scaled by `p_j/(2*cosh(tau))`. This is the exponential thermal branch form used in
[JiangEtAl2026]. -/
theorem idealInstrument_branch_thermal {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (tau : ℝ) (j : Fin L) (b : Bool) (rho : Qatlib.Foundations.PureStateMath.Operator d) :
    (idealInstrument F p (Real.tanh (tau / 2))).branch (j, b) rho =
      ((p.prob j / (2 * Real.cosh tau) : ℝ) : ℂ) •
        (thermalStep F tau j b * rho * thermalStep F tau j b) := by
  rw [idealInstrument_branch_weak, thermalStep_eq_weak]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  have hc : Real.cosh (tau / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hd : 2 * (1 + Real.tanh (tau / 2) ^ 2) ≠ 0 := by positivity
  have hn : 2 * Real.cosh tau =
      2 * (1 + Real.tanh (tau / 2) ^ 2) * Real.cosh (tau / 2) ^ 2 :=
    (thermal_normalization tau).symm
  exact_mod_cast (show p.prob j / (2 * (1 + Real.tanh (tau / 2) ^ 2)) =
      p.prob j / (2 * Real.cosh tau) * (Real.cosh (tau / 2) * Real.cosh (tau / 2)) by
    rw [hn]
    field_simp)

/-- At weak parameter `tanh(tau/2)`, a path branch is the sandwich by its ordered thermal-step
product, scaled by the product of `p_j/(2*cosh(tau))` over the path's indices. -/
theorem pathInstrument_branch_thermal {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (tau : ℝ) (N : ℕ) (w : Fin N → Fin L × Bool) (rho : Qatlib.Foundations.PureStateMath.Operator d) :
    (pathInstrument F p (Real.tanh (tau / 2)) N).branch w rho =
      ((∏ k : Fin N, p.prob (w k).1 / (2 * Real.cosh tau) : ℝ) : ℂ) •
        (pathKraus (fun o : Fin L × Bool => thermalStep F tau o.1 o.2) N w * rho *
          (pathKraus (fun o : Fin L × Bool => thermalStep F tau o.1 o.2) N w)ᴴ) := by
  induction N generalizing rho with
  | zero => simp [pathInstrument_branch, pathKraus]
  | succ N ih =>
    rw [pathInstrument_branch_succ, ih, idealInstrument_branch_thermal,
      Fin.prod_univ_succ]
    simp only [pathKraus, Matrix.conjTranspose_mul, Complex.ofReal_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [thermalStep_hermitian]
    simp only [Matrix.mul_assoc]
    congr 1
    ring

/-- A thermal path's Born probability equals the product of its index normalization weights
`p_j/(2*cosh(tau))` times the real trace of the input density sandwiched by the ordered
thermal-step product. -/
theorem pathBornLaw_thermal {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (tau : ℝ) (N : ℕ) (w : Fin N → Fin L × Bool) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) :
    (pathBornLaw F p (Real.tanh (tau / 2)) N rho).prob w =
      (∏ k : Fin N, p.prob (w k).1 / (2 * Real.cosh tau)) *
        (Matrix.trace
          (pathKraus (fun o : Fin L × Bool => thermalStep F tau o.1 o.2) N w * rho.val *
            (pathKraus (fun o : Fin L × Bool => thermalStep F tau o.1 o.2) N w)ᴴ)).re := by
  change Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb
      (pathInstrument F p (Real.tanh (tau / 2)) N) rho.val w = _
  rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb, pathInstrument_branch_thermal,
      Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end Qatlib.Papers.ThermalDrift26.ThermalSampling
