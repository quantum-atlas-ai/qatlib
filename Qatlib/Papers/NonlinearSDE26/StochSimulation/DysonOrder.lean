/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CommutLCHS26.MainResults.TimeOrderedPicard
public import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
public import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Short-time Dyson cutoff in Lemma 35

For arXiv:2603.12398v1, Eq. (224) gives order two at error tolerance
`exp (-3)`. A constant one-dimensional Hamiltonian violates Eq. (219)
at that order even on the specified short interval. A dyadic precision
budget and factorial search give a sufficient replacement.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.InteractionEvo.DysonGrid
open Qatlib.Papers.CommutLCHS26.MainResults.TimeOrderedPicard
open Qatlib.Concepts.CoherentSim.FactorialTaylor
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.NonlinearSDE26.StochSimulation

/-- The expression printed in Eq. (224), with its outer natural ceiling. -/
def printedDysonOrder (ε : ℝ) : ℕ :=
  Nat.ceil (-1 + 2 * Real.log (1 / ε) / (Real.log (Real.log (1 / ε)) + 1))

/-- The printed cutoff at tolerance `exp (-3)` only includes degrees zero, one, and two. -/
theorem lemma35_printed_order_at_exp_neg_three : printedDysonOrder (Real.exp (-3)) = 2 := by
  have hlog : Real.log (1 / Real.exp (-3)) = 3 := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hlower : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (Real.exp_one_lt_d9.trans (by norm_num))
  have hupper : Real.log 3 < 2 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    nlinarith [Real.exp_one_gt_d9]
  have hden : 0 < Real.log 3 + 1 := by linarith
  rw [printedDysonOrder, hlog, Nat.ceil_eq_iff (by decide : (2 : ℕ) ≠ 0)]
  constructor
  · norm_num only [Nat.reduceSub, Nat.cast_one]
    have h : 2 < (2 * 3 : ℝ) / (Real.log 3 + 1) := by
      rw [lt_div_iff₀ hden]
      linarith
    linarith
  · norm_num only [Nat.cast_ofNat]
    have h : (2 * 3 : ℝ) / (Real.log 3 + 1) ≤ 3 := by
      rw [div_le_iff₀ hden]
      linarith
    linarith

/-- The degree-one term of the actual ordered series for a unit scalar Hamiltonian. -/
private theorem scalar_term_one (t : ℝ) :
    orderedDysonTerm (fun _ : ℝ => Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 1 t =
      (-Complex.I * (t : ℂ)) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [orderedDysonTerm, intervalIntegral.integral_const]
  rw [← Complex.coe_smul, smul_smul]

/-- The degree-two term of the actual ordered series for a unit scalar Hamiltonian. -/
private theorem scalar_term_two (t : ℝ) :
    orderedDysonTerm (fun _ : ℝ => Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 2 t =
      (-((t ^ 2 / 2 : ℝ) : ℂ)) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [orderedDysonTerm]
  have hint :
      (fun u : ℝ => -(Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ) *
        orderedDysonTerm (fun _ => Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 1 u)) =
      (fun u : ℝ => u • (-(1 : Matrix (Fin 1) (Fin 1) ℂ))) := by
    funext u
    rw [scalar_term_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      ← Complex.coe_smul]
    have h : Complex.I * (-Complex.I * (u : ℂ)) = (u : ℂ) := by
      rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
    rw [h, smul_neg]
  rw [hint, intervalIntegral.integral_smul_const, integral_id]
  rw [← Complex.coe_smul]
  simp

/-- For a constant identity Hamiltonian, the norm of the order-two Dyson
error is at least the imaginary-part gap `t - sin t`. -/
private theorem scalar_order_two_error_lower (t : ℝ) :
    t - Real.sin t ≤
      ‖orderedEvolution (fun _ : ℝ => Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 t -
        dysonPrefix (fun _ => Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 t 2‖ := by
  have hexp (z : ℂ) :
      NormedSpace.exp (z • (1 : Matrix (Fin 1) (Fin 1) ℂ)) =
        Complex.exp z • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    have h := NormedSpace.map_exp (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ))
      (continuous_algebraMap _ _) z
    simpa only [Algebra.algebraMap_eq_smul_one, Complex.exp_eq_exp_ℂ] using h.symm
  have hprefix :
      dysonPrefix (fun _ : ℝ => Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 t 2 =
        (1 + (-Complex.I * (t : ℂ)) + -((t ^ 2 / 2 : ℝ) : ℂ)) •
          (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    rw [dysonPrefix, show (2 : ℕ) + 1 = 3 from rfl,
      Finset.sum_range_succ _ 2, Finset.sum_range_succ _ 1, Finset.sum_range_one,
      scalar_term_one, scalar_term_two, add_smul, add_smul, one_smul]
    rfl
  rw [orderedEvolution_constant_hamiltonian, sub_zero, HamiltonianEvolution, hexp, hprefix,
    ← sub_smul, norm_smul, CStarRing.norm_one, mul_one]
  let z : ℂ := Complex.exp (-Complex.I * (t : ℂ)) -
    (1 + (-Complex.I * (t : ℂ)) + -((t ^ 2 / 2 : ℝ) : ℂ))
  change t - Real.sin t ≤ ‖z‖
  have hi : z.im = t - Real.sin t := by
    have hre : (((t : ℂ) ^ 2)).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
    simp [z, Complex.exp_im, Complex.mul_im, hre]
    ring
  rw [← hi]
  exact (le_abs_self z.im).trans (Complex.abs_im_le_norm z)

/-- The printed cutoff fails for a constant unit Hamiltonian at time `11/16`.
Both the short-time and the proof's small-tolerance restrictions hold. -/
theorem lemma35_printed_cutoff_counterexample :
    let t : ℝ := 11 / 16
    let ε : ℝ := Real.exp (-3)
    let A : ℝ → Matrix (Fin 1) (Fin 1) ℂ := fun _ => Complex.I • 1
    0 < t ∧ t ≤ Real.log 2 ∧ 0 < ε ∧ ε ≤ Real.exp (-Real.exp 1 * Real.log 2) ∧
      ε < ‖orderedEvolution A 0 t - dysonPrefix A 0 t (printedDysonOrder ε)‖ := by
  dsimp
  refine ⟨by norm_num, (by norm_num : (11 / 16 : ℝ) ≤ 0.6931471803).trans
    Real.log_two_gt_d9.le, Real.exp_pos _, ?_, ?_⟩
  · apply Real.exp_le_exp.mpr
    have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
    have hl : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
    have h : Real.exp 1 * Real.log 2 ≤ 3 :=
      (mul_le_of_le_one_right (Real.exp_pos _).le hl).trans he
    linarith
  · rw [lemma35_printed_order_at_exp_neg_three]
    have he : 20 < Real.exp 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      refine (by norm_num : (20 : ℝ) < (2718 / 1000) ^ 3).trans ?_
      exact pow_lt_pow_left₀ ((by norm_num : (2718 / 1000 : ℝ) < 2.7182818283).trans
        Real.exp_one_gt_d9) (by norm_num) (by decide : (3 : ℕ) ≠ 0)
    have hε : Real.exp (-3) < 1 / 20 := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_lt_one_div_of_lt (by norm_num) he
    have hsin := (abs_le.mp (Real.sin_bound (x := 11 / 16) (by norm_num))).2
    norm_num at hsin
    exact hε.trans_le ((by linarith : (1 / 20 : ℝ) ≤ 11 / 16 - Real.sin (11 / 16)).trans
      (scalar_order_two_error_lower (11 / 16)))

/-- Number of dyadic precision bits sufficient for tolerance `ε`. -/
def dysonPrecisionBits (ε : ℝ) : ℕ := Nat.ceil (Real.log (1 / ε) / Real.log 2)

/-- Find the first order whose successor factorial reaches the dyadic target. -/
def certifiedDysonOrder (ε : ℝ) : ℕ := factorialTaylorCutoff (dysonPrecisionBits ε)

/-- A corrected short-time cutoff for an arbitrary continuous Hermitian field.
It bounds the error against the actual ordered evolution in Eq. (219). -/
theorem lemma35_certified_dyson_order {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t Λ ε : ℝ) (ht : 0 ≤ t) (hΛ : 0 ≤ Λ) (hε : 0 < ε)
    (hcont : Continuous H) (hherm : ∀ u, (H u).IsHermitian)
    (hbound : ∀ u ∈ Set.Icc 0 t, ‖H u‖ ≤ Λ) (hshort : Λ * t ≤ Real.log 2) :
    ‖orderedEvolution (fun u => Complex.I • H u) 0 t -
      dysonPrefix (fun u => Complex.I • H u) 0 t (certifiedDysonOrder ε)‖ ≤ ε := by
  let m := dysonPrecisionBits ε
  let K := certifiedDysonOrder ε
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hbits : Real.log (1 / ε) ≤ (m : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).mp (Nat.le_ceil _)
  have htwo : 1 / ε ≤ (2 : ℝ) ^ m := by
    have h := Real.exp_le_exp.mpr hbits
    rwa [Real.exp_log (by positivity : (0 : ℝ) < 1 / ε), Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  have hfac : (2 : ℝ) ^ m ≤ ((K + 1).factorial : ℝ) := by
    exact_mod_cast ((factorial_taylor_native_cutoff_and_rate.1 m).1)
  have hanti (u : ℝ) : Complex.I • H u + (Complex.I • H u)ᴴ = 0 := by
    simp [Matrix.conjTranspose_smul, (hherm u).eq]
  have hcont' : Continuous (fun u => Complex.I • H u) := hcont.const_smul Complex.I
  have h := norm_dysonPrefix_error_le (fun u => Complex.I • H u) hcont'
    (fun u => by rw [hanti u]; exact Matrix.PosSemidef.zero) 0 t Λ ht hΛ
    (fun u hu => by simpa [norm_smul] using hbound u hu) K
  rw [sub_zero, norm_sub_rev] at h
  refine h.trans ?_
  have hpow : (Λ * t) ^ (K + 1) ≤ 1 :=
    pow_le_one₀ (mul_nonneg hΛ ht) (hshort.trans (Real.log_two_lt_d9.le.trans (by norm_num)))
  have hden : (0 : ℝ) < (K + 1).factorial := by positivity
  apply (div_le_iff₀ hden).mpr
  have hbudget := (div_le_iff₀ hε).mp (htwo.trans hfac)
  linarith

/-- The factorial cutoff has the sublinear-in-bits order growth of the source rate. -/
theorem certified_dyson_order_rate :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ ε : ℝ, m₀ ≤ dysonPrecisionBits ε →
      certifiedDysonOrder ε * Nat.log 2 (dysonPrecisionBits ε) ≤ C * dysonPrecisionBits ε := by
  obtain ⟨C, m₀, hC, hm₀, h⟩ := factorial_taylor_native_cutoff_and_rate.2
  exact ⟨C, m₀, hC, hm₀, fun ε hε => h (dysonPrecisionBits ε) hε⟩

end Qatlib.Papers.NonlinearSDE26.StochSimulation
