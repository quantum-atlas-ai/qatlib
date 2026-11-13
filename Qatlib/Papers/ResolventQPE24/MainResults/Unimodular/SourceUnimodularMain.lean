/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ResolventQPE24.MainResults.Prelude

set_option backward.isDefEq.respectTransparency false

/-!
# Eigenvalue Estimation Failure Propagation, Normalised Difference, and QEUE Complexity

This module formalizes Section 3 (Lemma 3.10, Lemma 3.11, and Theorem 3.12) of Alase
and Karuvade on failure propagation across non-orthogonal eigenvector superpositions
with condition number `κ_S = σ_max / σ_min`, Lipschitz continuity of vector normalisation,
and the query-complexity scaling of Quantum Eigenvalue Estimation for Unitary Evolutions.

## Main statements

* `failure_propagation`: Lemma 3.10, Eq. (80), two-sided `κ_S` norm bounds for entangled eigenvector states.
* `normalized_difference_bound`: Lemma 3.11, Eq. (89), `‖x/‖x‖ - x̃/‖x̃‖‖ ≤ 2 ε / ‖x‖`.
* `theorem3_12_query_complexity`: Theorem 3.12, Eq. (91), QEUE query-count scaling bound.

## References

* [Alase and Karuvade, 2024][AlaseKaruvade2024], Section 3, Lemmas 3.10--3.11, Theorem 3.12, pp. 17--20.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ResolventQPE24.MainResults.Unimodular

open Qatlib.Papers.ResolventQPE24.MainResults.Prelude

/-- **c013 — Lemma 3.10 (propagation of failure), p. 17, Eq. (80).**
Let `|ψ⟩ = ∑_l β_l |λ_l⟩` have unit norm, let `S` be the matrix whose columns
are the eigenvectors `|λ_l⟩`, and let `χ_l` be arbitrary ancilla states.  With
operator-norm bounds `σmin`, `σmax` for `S` and condition number
`κ_S = σmax/σmin`,

`min_l ‖χ_l‖/κ_S ≤ ‖∑_l β_l |χ_l⟩|λ_l⟩‖ ≤ κ_S max_l ‖χ_l‖`.

The state `∑_l β_l |χ_l⟩|λ_l⟩` is represented as the vector
`(a,i) ↦ ∑_l β_l χ_l(a) S(i,l)` on `H' × Fin m`; `stateNormSq` is the squared
Euclidean norm and `sInf`/`sSup` are the min/max over `l`. -/
theorem failure_propagation
    {m k h : ℕ} (hk : 0 < k) (S : Matrix (Fin m) (Fin k) ℂ)
    (β : Fin k → ℂ) (χ : Fin k → Fin h → ℂ) (σmax σmin : ℝ)
    (hσmin : 0 < σmin)
    (hSmax : ∀ v : Fin k → ℂ,
      Real.sqrt (stateNormSq (S.mulVec v)) ≤ σmax * Real.sqrt (stateNormSq v))
    (hSmin : ∀ v : Fin k → ℂ,
      σmin * Real.sqrt (stateNormSq v) ≤ Real.sqrt (stateNormSq (S.mulVec v)))
    (hψ : stateNormSq (fun i => ∑ l, β l * S i l) = 1) :
    sInf (Set.range fun l => Real.sqrt (stateNormSq (χ l))) / (σmax / σmin) ≤
        Real.sqrt (stateNormSq (fun p : Fin h × Fin m =>
          ∑ l, β l * χ l p.1 * S p.2 l)) ∧
      Real.sqrt (stateNormSq (fun p : Fin h × Fin m =>
          ∑ l, β l * χ l p.1 * S p.2 l)) ≤
        (σmax / σmin) * sSup (Set.range fun l => Real.sqrt (stateNormSq (χ l))) := by
  have hnorm_nonneg {ι : Type} [Fintype ι] (v : ι → ℂ) : 0 ≤ stateNormSq v :=
    Finset.sum_nonneg fun j _ => sq_nonneg ‖v j‖
  have hψS : stateNormSq (S.mulVec β) = 1 := by
    change stateNormSq (fun i => ∑ l, S i l * β l) = 1
    simpa only [mul_comm] using hψ
  have hψsqrt : Real.sqrt (stateNormSq (S.mulVec β)) = 1 := by
    rw [hψS, Real.sqrt_one]
  have hβsqrt : 0 < Real.sqrt (stateNormSq β) := by
    have hmax := hSmax β
    rw [hψsqrt] at hmax
    by_contra hnot
    have hz : Real.sqrt (stateNormSq β) = 0 :=
      le_antisymm (le_of_not_gt hnot) (Real.sqrt_nonneg _)
    rw [hz, mul_zero] at hmax
    norm_num at hmax
  have hσmax : 0 < σmax := by
    have hmax := hSmax β
    rw [hψsqrt] at hmax
    exact ((mul_pos_iff.mp (lt_of_lt_of_le zero_lt_one hmax)).resolve_right
      (fun hneg => (not_lt_of_ge hβsqrt.le) hneg.2)).1
  have hsquared (v : Fin k → ℂ) :
      σmin ^ 2 * stateNormSq v ≤ stateNormSq (S.mulVec v) ∧
        stateNormSq (S.mulVec v) ≤ σmax ^ 2 * stateNormSq v := by
    constructor
    · have hsq := (sq_le_sq₀ (mul_nonneg hσmin.le (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)).2 (hSmin v)
      simpa only [mul_pow, Real.sq_sqrt (hnorm_nonneg v),
        Real.sq_sqrt (hnorm_nonneg (S.mulVec v))] using hsq
    · have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _)
        (mul_nonneg hσmax.le (Real.sqrt_nonneg _))).2 (hSmax v)
      simpa only [mul_pow, Real.sq_sqrt (hnorm_nonneg v),
        Real.sq_sqrt (hnorm_nonneg (S.mulVec v))] using hsq
  have hβbounds : 1 / σmax ^ 2 ≤ stateNormSq β ∧
      stateNormSq β ≤ 1 / σmin ^ 2 := by
    have hb := hsquared β
    rw [hψS] at hb
    constructor
    · exact (div_le_iff₀ (sq_pos_of_pos hσmax)).2 (by nlinarith [hb.2])
    · exact (le_div_iff₀ (sq_pos_of_pos hσmin)).2 (by nlinarith [hb.1])
  let v : Fin h → Fin k → ℂ := fun a l => β l * χ l a
  have htensor : stateNormSq (fun p : Fin h × Fin m =>
      ∑ l, β l * χ l p.1 * S p.2 l) =
        ∑ a : Fin h, stateNormSq (S.mulVec (v a)) := by
    simp only [stateNormSq, Fintype.sum_prod_type, Matrix.mulVec, dotProduct, v,
      mul_comm]
  have hweights : (∑ a : Fin h, stateNormSq (v a)) =
      ∑ l : Fin k, ‖β l‖ ^ 2 * stateNormSq (χ l) := by
    simp only [stateNormSq, v, norm_mul, mul_pow, Finset.mul_sum]
    exact Finset.sum_comm
  have htensor_bounds :
      σmin ^ 2 * (∑ l : Fin k, ‖β l‖ ^ 2 * stateNormSq (χ l)) ≤
          stateNormSq (fun p : Fin h × Fin m => ∑ l, β l * χ l p.1 * S p.2 l) ∧
        stateNormSq (fun p : Fin h × Fin m => ∑ l, β l * χ l p.1 * S p.2 l) ≤
          σmax ^ 2 * (∑ l : Fin k, ‖β l‖ ^ 2 * stateNormSq (χ l)) := by
    rw [htensor, ← hweights, Finset.mul_sum, Finset.mul_sum]
    exact ⟨Finset.sum_le_sum (fun a _ => (hsquared (v a)).1),
      Finset.sum_le_sum (fun a _ => (hsquared (v a)).2)⟩
  let R := Set.range fun l : Fin k => Real.sqrt (stateNormSq (χ l))
  obtain ⟨l₀⟩ := Fin.pos_iff_nonempty.mp hk
  have hRne : R.Nonempty := ⟨_, ⟨l₀, rfl⟩⟩
  have hRfinite : R.Finite := Set.finite_range _
  have hRnonneg : ∀ x ∈ R, 0 ≤ x := by
    rintro x ⟨l, rfl⟩
    exact Real.sqrt_nonneg _
  have hinf : 0 ≤ sInf R := Real.sInf_nonneg hRnonneg
  have hsup : 0 ≤ sSup R :=
    (hRnonneg _ hRne.choose_spec).trans (le_csSup hRfinite.bddAbove hRne.choose_spec)
  have hχbounds (l : Fin k) :
      (sInf R) ^ 2 ≤ stateNormSq (χ l) ∧ stateNormSq (χ l) ≤ (sSup R) ^ 2 := by
    constructor
    · have hsq := (sq_le_sq₀ hinf (Real.sqrt_nonneg _)).2
        (csInf_le hRfinite.bddBelow (Set.mem_range_self l))
      simpa only [Real.sq_sqrt (hnorm_nonneg (χ l))] using hsq
    · have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) hsup).2
        (le_csSup hRfinite.bddAbove (Set.mem_range_self l))
      simpa only [Real.sq_sqrt (hnorm_nonneg (χ l))] using hsq
  have hweighted_bounds :
      (sInf R) ^ 2 * stateNormSq β ≤ ∑ l, ‖β l‖ ^ 2 * stateNormSq (χ l) ∧
        (∑ l, ‖β l‖ ^ 2 * stateNormSq (χ l)) ≤ (sSup R) ^ 2 * stateNormSq β := by
    change (sInf R) ^ 2 * (∑ l, ‖β l‖ ^ 2) ≤
        (∑ l, ‖β l‖ ^ 2 * stateNormSq (χ l)) ∧
      (∑ l, ‖β l‖ ^ 2 * stateNormSq (χ l)) ≤ (sSup R) ^ 2 * (∑ l, ‖β l‖ ^ 2)
    rw [Finset.mul_sum, Finset.mul_sum]
    constructor
    · exact Finset.sum_le_sum fun l _ => by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (hχbounds l).1 (sq_nonneg ‖β l‖)
    · exact Finset.sum_le_sum fun l _ => by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (hχbounds l).2 (sq_nonneg ‖β l‖)
  have hκ : 0 < σmax / σmin := div_pos hσmax hσmin
  have hlower : (sInf R / (σmax / σmin)) ^ 2 ≤
      stateNormSq (fun p : Fin h × Fin m => ∑ l, β l * χ l p.1 * S p.2 l) := by
    calc
      _ = σmin ^ 2 * ((sInf R) ^ 2 * (1 / σmax ^ 2)) := by field_simp
      _ ≤ σmin ^ 2 * ((sInf R) ^ 2 * stateNormSq β) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hβbounds.1 (sq_nonneg _)) (sq_nonneg _)
      _ ≤ σmin ^ 2 * (∑ l, ‖β l‖ ^ 2 * stateNormSq (χ l)) :=
        mul_le_mul_of_nonneg_left hweighted_bounds.1 (sq_nonneg _)
      _ ≤ _ := htensor_bounds.1
  have hupper :
      stateNormSq (fun p : Fin h × Fin m => ∑ l, β l * χ l p.1 * S p.2 l) ≤
        ((σmax / σmin) * sSup R) ^ 2 := by
    calc
      _ ≤ σmax ^ 2 * (∑ l, ‖β l‖ ^ 2 * stateNormSq (χ l)) := htensor_bounds.2
      _ ≤ σmax ^ 2 * ((sSup R) ^ 2 * stateNormSq β) :=
        mul_le_mul_of_nonneg_left hweighted_bounds.2 (sq_nonneg _)
      _ ≤ σmax ^ 2 * ((sSup R) ^ 2 * (1 / σmin ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hβbounds.2 (sq_nonneg _)) (sq_nonneg _)
      _ = _ := by field_simp
  constructor
  · simpa only [Real.sqrt_sq (div_nonneg hinf hκ.le)] using Real.sqrt_le_sqrt hlower
  · simpa only [Real.sqrt_sq (mul_nonneg hκ.le hsup)] using Real.sqrt_le_sqrt hupper

/-- **c014 — Lemma 3.11 (normalised difference bound), p. 18, Eq. (89).**
If `‖x - xt‖ ≤ ε` and `x`, `xt` are nonzero, then
`‖x/‖x‖ - xt/‖xt‖‖ ≤ 2ε/‖x‖`. -/
theorem normalized_difference_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x xt : E) (ε : ℝ) (hε : 0 ≤ ε) (h : ‖x - xt‖ ≤ ε)
    (hx : x ≠ 0) (hxt : xt ≠ 0) :
    ‖((‖x‖ : ℝ)⁻¹) • x - ((‖xt‖ : ℝ)⁻¹) • xt‖ ≤ 2 * ε / ‖x‖ := by
  have hx0 : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hxt0 : (0 : ℝ) < ‖xt‖ := norm_pos_iff.mpr hxt
  have ha : ((‖x‖ : ℝ)⁻¹) • x - ((‖xt‖ : ℝ)⁻¹) • xt =
      ((‖x‖ : ℝ)⁻¹) • (x - xt) +
        (((‖x‖ : ℝ)⁻¹) - ((‖xt‖ : ℝ)⁻¹)) • xt := by
    rw [smul_sub]
    module
  have hq : |((‖x‖ : ℝ)⁻¹) - ((‖xt‖ : ℝ)⁻¹)| * ‖xt‖ =
      |(‖xt‖ : ℝ) - ‖x‖| / ‖x‖ := by
    rw [show ((‖x‖ : ℝ)⁻¹) - ((‖xt‖ : ℝ)⁻¹) =
      ((‖xt‖ : ℝ) - ‖x‖) / (‖x‖ * ‖xt‖) by
        field_simp]
    rw [abs_div, abs_mul, abs_of_pos hx0, abs_of_pos hxt0]
    field_simp
  have hstep : ‖((‖x‖ : ℝ)⁻¹) • x - ((‖xt‖ : ℝ)⁻¹) • xt‖ ≤
      (‖x‖ : ℝ)⁻¹ * ε + |(‖xt‖ : ℝ) - ‖x‖| / ‖x‖ := by
    rw [ha]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hx0)]
    rw [hq]
    have h1 : (‖x‖ : ℝ)⁻¹ * ‖x - xt‖ ≤ (‖x‖ : ℝ)⁻¹ * ε := by
      simpa only [mul_comm] using
        mul_le_mul h (le_refl (‖x‖ : ℝ)⁻¹) (inv_nonneg.mpr hx0.le) hε
    linarith
  have hdiff : |(‖xt‖ : ℝ) - ‖x‖| ≤ ε := by
    calc |(‖xt‖ : ℝ) - ‖x‖| = |‖x‖ - ‖xt‖| := abs_sub_comm _ _
      _ ≤ ‖x - xt‖ := abs_norm_sub_norm_le x xt
      _ ≤ ε := h
  have hinv : (‖x‖ : ℝ)⁻¹ * ε + |(‖xt‖ : ℝ) - ‖x‖| / ‖x‖ ≤ 2 * ε / ‖x‖ := by
    rw [div_eq_inv_mul, div_eq_inv_mul]
    have h2 : |(‖xt‖ : ℝ) - ‖x‖| * (‖x‖ : ℝ)⁻¹ ≤ ε * (‖x‖ : ℝ)⁻¹ := by
      gcongr
    rw [mul_comm (‖x‖ : ℝ)⁻¹ ε]
    linarith
  exact hstep.trans hinv

/-- **c015 — Theorem 3.12 (complexity of solving QEUE), p. 19, Eq. (91).**
There is a constant `C` such that for every `ε_st ∈ (0,1]` one can choose
`δ ∈ Θ(ε_eig ε_st²/κ_S⁴)` (both bounds with constants recorded through `C`)
for which the QEUE query count `α_A K_δ°(A)/δ · log(1/ε_st)` is bounded by
`C · α_A κ_S⁴ K_δ°(A)/(ε_eig ε_st²) · log(1/ε_st)`.

This is the query-count consequence of Lemma 3.6 and Eq. (102); the circuit
construction and the state-accuracy analysis are not formalised. -/
theorem theorem3_12_query_complexity
    (αA κS Kδ εeig : ℝ) (hαA : 0 < αA) (hκS : 0 < κS) (hKδ : 0 ≤ Kδ)
    (hεeig : 0 < εeig) :
    ∃ C : ℝ, 0 < C ∧ ∀ εst : ℝ, 0 < εst → εst ≤ 1 →
      ∃ δ : ℝ, 0 < δ ∧
        (εeig * εst ^ 2 / κS ^ 4) / C ≤ δ ∧
        δ ≤ C * (εeig * εst ^ 2 / κS ^ 4) ∧
        αA * Kδ / δ * Real.log (1 / εst) ≤ C * qeueQueryBound αA κS Kδ εeig εst := by
  refine ⟨2, by norm_num, ?_⟩
  intro εst hεst hεst1
  have hx0 : 0 < εeig * εst ^ 2 / κS ^ 4 := by positivity
  refine ⟨εeig * εst ^ 2 / κS ^ 4, hx0, ?_, ?_, ?_⟩
  · linarith
  · nlinarith
  · rw [qeueQueryBound]
    have hlog : 0 ≤ Real.log (1 / εst) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hεst]
      linarith
    have hkl : 0 ≤ αA * κS ^ 4 * Kδ / (εeig * εst ^ 2) := by positivity
    have hcost : 0 ≤ αA * κS ^ 4 * Kδ / (εeig * εst ^ 2) * Real.log (1 / εst) :=
      mul_nonneg hkl hlog
    rw [show αA * Kδ / (εeig * εst ^ 2 / κS ^ 4) * Real.log (1 / εst) =
        αA * κS ^ 4 * Kδ / (εeig * εst ^ 2) * Real.log (1 / εst) by
      field_simp]
    linarith

end Qatlib.Papers.ResolventQPE24.MainResults.Unimodular
