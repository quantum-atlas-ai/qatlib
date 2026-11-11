/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MixedDyson
import Qatlib.Papers.CommutLCHS26.MainResults.MultilinearSums

/-!
# Dyson coefficients in inverse repetition powers

The coefficients `powerCoefficient` collect fixed-depth Dyson terms by their inverse-even-power
dependence on the repetition count. Under odd-coefficient control, these coefficients give
convergent series for the perturbative simulation analysis of [AftabAnTrivisa2026], with norms
bounded by `massProfile` divided by a factorial.

## Main statements

* `tuple_factor`: extracts the repetition factor from a multilinear term.
* `depth_hasSum`: expands a Dyson term in inverse repetition powers.
* `powerCoefficient_norm`: bounds each collected coefficient.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.DysonCoefficients

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator NNReal ENNReal
open BCHControlled BCHCommMass BCHMassProducts BCHPerturbation MixedDyson
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The antidiagonal sum of mixed multilinear terms built from odd BCH perturbation coefficients
with total index n and depth l. -/
def powerCoefficient (xs : List (Matrix I I ℂ)) (t : ℝ) (l n : ℕ) : Matrix I I ℂ :=
  ∑ v ∈ Finset.finAntidiagonal l n,
    mixedMultilinear (t • ((-Complex.I) • xs.sum)) l 1
      (fun i => t ^ (2 * v i + 3) • BCHPerturbation.coefficient xs (2 * v i + 3))

/-- The norm of the time-scaled odd BCH coefficient is bounded by its scalar mass term. -/
theorem input_norm_le (xs : List (Matrix I I ℂ)) (t : ℝ) (j : ℕ) :
    ‖t ^ (2 * j + 3) • BCHPerturbation.coefficient xs (2 * j + 3)‖ ≤ massTerm xs t j := by
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  calc
    _ ≤ |t| ^ (2 * j + 3) *
        (Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf xs (2 * j + 3) /
          ((2 * j + 3 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (BCHPerturbation.coefficient_norm xs _ (by omega))
        (pow_nonneg (abs_nonneg _) _)
    _ = _ := by unfold massTerm; ring

/-- On a length-l antidiagonal of total n, the product of inverse repetition powers equals
q^(-2(n + l)). -/
theorem fiber_scalar (q l n : ℕ) (v : Fin l → ℕ) (hv : v ∈ Finset.finAntidiagonal l n) :
    (∏ i, (1 / (q : ℝ) ^ (2 * v i + 2))) = 1 / (q : ℝ) ^ (2 * (n + l)) := by
  have he : ∑ i, (2 * v i + 2) = 2 * (n + l) := by
    have hn : ∑ i, v i = n := Finset.mem_finAntidiagonal.mp hv
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hn, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const_one]
  rw [Finset.prod_pow_eq_pow_sum, he]

/-- A mixed Dyson term for a tuple of total n factors into q^(-2(n + l)) times a multilinear
expression independent of q. -/
theorem tuple_factor (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (t : ℝ) (q l n : ℕ) (v : Fin l → ℕ) (hv : v ∈ Finset.finAntidiagonal l n) :
    mixedMap (t • ((-Complex.I) • xs.sum)) (target_skew xs hxs t) l 1
      (fun i => perturbationTerm xs q t (v i)) =
      (1 / (q : ℝ) ^ (2 * (n + l))) •
        mixedMultilinear (t • ((-Complex.I) • xs.sum)) l 1
          (fun i => t ^ (2 * v i + 3) • BCHPerturbation.coefficient xs (2 * v i + 3)) := by
  have hi : (fun i => perturbationTerm xs q t (v i)) =
      (fun i => (1 / (q : ℝ) ^ (2 * v i + 2)) •
        (t ^ (2 * v i + 3) • BCHPerturbation.coefficient xs (2 * v i + 3))) := by
    funext i
    rw [smul_smul]
    unfold perturbationTerm
    congr 1
    ring
  rw [hi, ContinuousMultilinearMap.map_smul_univ, fiber_scalar q l n v hv]
  rfl

/-- Under odd-coefficient control and Hermitian generators, the inverse-power series of depth-l
coefficients sums to the depth-l Dyson term. -/
theorem depth_hasSum (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (q : ℕ) (hq : 0 < q)
    (t : ℝ) (ht : |t| ≤ r) (l : ℕ) :
    HasSum (fun n => (1 / (q : ℝ) ^ (2 * (n + l))) • powerCoefficient xs t l n)
      (PerturbationDyson.term (t • ((-Complex.I) • xs.sum)) (perturbation xs q t) l 1) := by
  let f := mixedMap (t • ((-Complex.I) • xs.sum)) (target_skew xs hxs t) l 1
  have h := MultilinearSums.grouped_hasSum l f (perturbationTerm xs q t)
    (perturbation_norm_summable xs r J hc q hq t ht) (perturbation xs q t)
    (perturbation_hasSum xs r J hc q hq t ht)
  have hf := mixedMap_constant (t • ((-Complex.I) • xs.sum)) (perturbation xs q t)
    (target_skew xs hxs t) l 1
  change f (fun _ => perturbation xs q t) = _ at hf
  have h' : HasSum (fun n => ∑ v ∈ Finset.finAntidiagonal l n,
      f (fun i => perturbationTerm xs q t (v i)))
      (PerturbationDyson.term (t • ((-Complex.I) • xs.sum)) (perturbation xs q t) l 1) := hf ▸ h
  convert! h' using 1
  funext n
  rw [powerCoefficient, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact (tuple_factor xs hxs t q l n v hv).symm

/-- For Hermitian generators, the norm of a depth-l coefficient is at most its mass profile
divided by l factorial. -/
theorem powerCoefficient_norm (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (t : ℝ) (l n : ℕ) :
    ‖powerCoefficient xs t l n‖ ≤ massProfile xs t l n / (l.factorial : ℝ) := by
  unfold powerCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ v ∈ Finset.finAntidiagonal l n,
        (1 / (l.factorial : ℝ)) * ∏ i, massTerm xs t (v i) := by
      apply Finset.sum_le_sum
      intro v _
      have hm := mixed_norm _ (target_skew xs hxs t) l
        (fun i => t ^ (2 * v i + 3) • BCHPerturbation.coefficient xs (2 * v i + 3)) 1
      simp only [abs_one, one_pow] at hm
      exact hm.trans (mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => input_norm_le xs t (v i)))
          (by positivity))
    _ = _ := by rw [← Finset.mul_sum]; unfold massProfile; ring

end Qatlib.Papers.CommutLCHS26.MainResults.DysonCoefficients
