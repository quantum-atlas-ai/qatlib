/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GWSpeedupYuan25.MainResults.Definitions
import Qatlib.Papers.GWSpeedupYuan25.MainResults.Relaxation.DiagonalConstraints
import Mathlib.Analysis.Matrix.PosDef

set_option backward.isDefEq.respectTransparency false

/-!
# Monotonicity and Eigenvalue-QUBO Sandwich for Relaxed Goemans-Williamson Programs

This module proves Lemma 12: the relaxed Goemans-Williamson optimum `gwValue n C S ε`
is antitone in the diagonal Pauli constraint set `S`, monotone in the tolerance `ε`,
and satisfies the sandwich chain
`lambdaMax n C / ‖C‖ = gwValue n C ∅ 0 ≥ gwValue n C S 0 ≥ gwValue n C (fullConstraints n) 0 ≥ quboValue n C / (2^n ‖C‖)`.

## Main statements

* `lemma12_mono_constraints`: `S₁ ⊆ S₂ → gwValue n C S₂ ε ≤ gwValue n C S₁ ε`.
* `lemma12_mono_epsilon`: `ε₁ ≤ ε₂ → gwValue n C S ε₁ ≤ gwValue n C S ε₂`.
* `lemma12_sandwich`: full Eq. (28) sandwich relating `lambdaMax`, `gwValue`, and `quboValue`.

## References

* [Yuan et al., 2025][YuanEtAl2025GWSpeedup], Lemma 12, Eq. (28), Section III.A, p. 11.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GWSpeedupYuan25.MainResults.Relaxation

open Matrix Qatlib.Papers.GWSpeedupYuan25.MainResults
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

private def vectorMass {n : ℕ} (v : Reg n → ℂ) : ℝ :=
  (∑ i, star (v i) * v i).re

private lemma vectorMass_eq_norm {n : ℕ} (v : Reg n → ℂ) :
    vectorMass v = ‖WithLp.toLp 2 v‖ ^ 2 := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (WithLp.toLp 2 v)
  change (∑ i, v i * star (v i)).re = ‖WithLp.toLp 2 v‖ ^ 2 at h
  simpa only [vectorMass, mul_comm] using h

private lemma vectorMass_pos {n : ℕ} {v : Reg n → ℂ} (hv : v ≠ 0) :
    0 < vectorMass v := by
  rw [vectorMass_eq_norm]
  exact sq_pos_of_pos (norm_pos_iff.mpr (by simpa using hv))

private lemma vectorMass_cast {n : ℕ} (v : Reg n → ℂ) :
    (vectorMass v : ℂ) = ∑ i, star (v i) * v i := by
  simp [vectorMass, Complex.conj_mul', ← Complex.ofReal_pow]

private def rankOneDensity {n : ℕ} (v : Reg n → ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  ((vectorMass v : ℂ))⁻¹ • Matrix.vecMulVec v (star v)

private lemma rankOneDensity_isDensity {n : ℕ} {v : Reg n → ℂ} (hv : v ≠ 0) :
    IsDensity (rankOneDensity v) := by
  refine ⟨(Matrix.posSemidef_vecMulVec_self_star v).smul
    (inv_nonneg.mpr (by exact_mod_cast (vectorMass_pos hv).le)), ?_⟩
  have hm : (vectorMass v : ℂ) ≠ 0 := by exact_mod_cast (vectorMass_pos hv).ne'
  change Matrix.trace ((↑(vectorMass v) : ℂ)⁻¹ • Matrix.vecMulVec v (star v)) = 1
  rw [Matrix.trace_smul]
  change (↑(vectorMass v) : ℂ)⁻¹ * (∑ i, v i * star (v i)) = 1
  simp_rw [mul_comm (v _) (star (v _))]
  rw [← vectorMass_cast v]
  exact inv_mul_cancel₀ hm

private lemma trace_rankOneDensity {n : ℕ} (C : Matrix (Reg n) (Reg n) ℂ)
    (v : Reg n → ℂ) :
    ((C * rankOneDensity v).trace).re = rayleigh C v := by
  have he : (C * Matrix.vecMulVec v (star v)).trace =
      ∑ i, ∑ j, star (v i) * C i j * v j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Pi.star_apply]
    congr 1
    funext i
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [rankOneDensity, Matrix.mul_smul, Matrix.trace_smul, he, ← Complex.ofReal_inv]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, rayleigh, div_eq_mul_inv]
  exact mul_comm _ _

private lemma rayleigh_le_norm {n : ℕ} (C : Matrix (Reg n) (Reg n) ℂ)
    {v : Reg n → ℂ} (hv : v ≠ 0) : rayleigh C v ≤ ‖C‖ := by
  let x : EuclideanSpace ℂ (Reg n) := WithLp.toLp 2 v
  let y : EuclideanSpace ℂ (Reg n) := WithLp.toLp 2 (C *ᵥ v)
  have he : (∑ i, ∑ j, star (v i) * C i j * v j) = inner ℂ x y := by
    simp only [x, y, EuclideanSpace.inner_toLp_toLp, dotProduct, Matrix.mulVec,
      Pi.star_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have hy : ‖y‖ ≤ ‖C‖ * ‖x‖ := Matrix.l2_opNorm_mulVec C x
  change (∑ i, ∑ j, star (v i) * C i j * v j).re / vectorMass v ≤ ‖C‖
  rw [he, div_le_iff₀ (vectorMass_pos hv)]
  have hi := re_inner_le_norm (𝕜 := ℂ) x y
  change (inner ℂ x y).re ≤ ‖x‖ * ‖y‖ at hi
  calc (inner ℂ x y).re ≤ ‖x‖ * ‖y‖ := hi
    _ ≤ ‖x‖ * (‖C‖ * ‖x‖) := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = ‖C‖ * vectorMass v := by rw [vectorMass_eq_norm]; dsimp [x]; ring

private lemma rayleigh_bddAbove {n : ℕ} (C : Matrix (Reg n) (Reg n) ℂ) :
    BddAbove {r : ℝ | ∃ v : Reg n → ℂ, v ≠ 0 ∧ r = rayleigh C v} := by
  refine ⟨‖C‖, ?_⟩
  rintro r ⟨v, hv, rfl⟩
  exact rayleigh_le_norm C hv

private lemma rayleigh_le_lambdaMax {n : ℕ} (C : Matrix (Reg n) (Reg n) ℂ)
    {v : Reg n → ℂ} (hv : v ≠ 0) : rayleigh C v ≤ lambdaMax n C :=
  le_csSup (rayleigh_bddAbove C) ⟨v, hv, rfl⟩

private lemma density_trace_le_lambdaMax {n : ℕ} (C : Matrix (Reg n) (Reg n) ℂ)
    {ρ : Matrix (Reg n) (Reg n) ℂ} (hρ : IsDensity ρ) :
    ((C * ρ).trace).re ≤ lambdaMax n C := by
  classical
  let hH := hρ.1.isHermitian
  let μ := hH.eigenvalues
  let v : Reg n → Reg n → ℂ := fun k i => hH.eigenvectorBasis k i
  have hm (k : Reg n) : vectorMass (v k) = 1 := by
    rw [vectorMass_eq_norm]
    change ‖hH.eigenvectorBasis k‖ ^ 2 = 1
    rw [hH.eigenvectorBasis.orthonormal.norm_eq_one k, one_pow]
  have hv (k : Reg n) : v k ≠ 0 := by
    intro he
    have hh := hm k
    simp [he, vectorMass] at hh
  have hdecomp : ρ = ∑ k, (μ k : ℂ) • rankOneDensity (v k) := by
    have hp (k : Reg n) : rankOneDensity (v k) = Matrix.vecMulVec (v k) (star (v k)) := by
      simp [rankOneDensity, hm k]
    simp_rw [hp]
    rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      smul_eq_mul, Function.comp_apply]
    exact Finset.sum_congr rfl fun k _ => by dsimp [μ, v]; ring
  have hsum : ∑ k, μ k = 1 := by
    have he := hH.trace_eq_sum_eigenvalues
    rw [hρ.2] at he
    have hr := congrArg Complex.re he
    simpa [μ] using hr.symm
  calc
    ((C * ρ).trace).re = (∑ k, μ k * rayleigh C (v k)) := by
      rw [hdecomp]
      simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
        smul_eq_mul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, trace_rankOneDensity]
    _ ≤ ∑ k, μ k * lambdaMax n C := by
      exact Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (rayleigh_le_lambdaMax C (hv k))
          (hρ.1.eigenvalues_nonneg k)
    _ = lambdaMax n C := by rw [← Finset.sum_mul, hsum, one_mul]

private lemma plusMinus_mass {n : ℕ} {x : Reg n → ℝ} (hx : IsPlusMinus x) :
    vectorMass (fun i => (x i : ℂ)) = (2 : ℝ) ^ n := by
  have he (i : Reg n) : star (x i : ℂ) * (x i : ℂ) = 1 := by
    rcases hx i with hi | hi <;> simp [hi]
  unfold vectorMass
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Complex.natCast_re]
  simp [Reg]

private lemma plusMinus_feasible {n : ℕ} {x : Reg n → ℝ} (hx : IsPlusMinus x) :
    GwFeasible n (fullConstraints n) 0 (rankOneDensity (fun i => (x i : ℂ))) := by
  have hv : (fun i => (x i : ℂ)) ≠ 0 := by
    intro he
    have hm := plusMinus_mass hx
    rw [he] at hm
    have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    exact hp (by simpa [vectorMass] using hm.symm)
  have hd := rankOneDensity_isDensity hv
  refine ⟨hd, fun A hA => ?_⟩
  have hdiag (i : Reg n) : rankOneDensity (fun j => (x j : ℂ)) i i =
      ((2 : ℂ) ^ n)⁻¹ := by
    change ((vectorMass (fun j => (x j : ℂ)) : ℂ))⁻¹ *
      ((x i : ℂ) * star (x i : ℂ)) = _
    rcases hx i with hi | hi <;> simp [plusMinus_mass hx, hi]
  rw [lemma10_diagonal_implies_traces n _ hd hdiag A hA]
  simp

private lemma plusMinus_objective {n : ℕ} (C : Matrix (Reg n) (Reg n) ℂ)
    {x : Reg n → ℝ} (hx : IsPlusMinus x) :
    gwObjective C (rankOneDensity (fun i => (x i : ℂ))) =
      (∑ i, ∑ j, x i * (C i j).re * x j) / ((2 : ℝ) ^ n * ‖C‖) := by
  rw [gwObjective, trace_rankOneDensity]
  change ((∑ i, ∑ j, star (x i : ℂ) * C i j * (x j : ℂ)).re /
    vectorMass (fun i => (x i : ℂ))) / ‖C‖ = _
  rw [plusMinus_mass hx]
  have he : (∑ i, ∑ j, star (x i : ℂ) * C i j * (x j : ℂ)).re =
      ∑ i, ∑ j, x i * (C i j).re * x j := by
    simp [Complex.mul_re]
  rw [he]
  exact div_div (∑ i, ∑ j, x i * (C i j).re * x j) ((2 : ℝ) ^ n) ‖C‖

private lemma gwObjSet_nonempty {n : ℕ} (C : Matrix (Reg n) (Reg n) ℂ)
    {T : Set (Finset (Fin n))} (hT : T ⊆ fullConstraints n) :
    (gwObjSet n C T 0).Nonempty := by
  have hf := plusMinus_feasible (n := n) (x := fun _ => 1) (fun _ => Or.inl rfl)
  exact ⟨_, _, ⟨hf.1, fun A hA => hf.2 A (hT hA)⟩, rfl⟩

private lemma gwObjSet_bddAbove {n : ℕ} (C : Matrix (Reg n) (Reg n) ℂ)
    (T : Set (Finset (Fin n))) (hC : 0 < ‖C‖) : BddAbove (gwObjSet n C T 0) := by
  refine ⟨lambdaMax n C / ‖C‖, ?_⟩
  rintro r ⟨ρ, hρ, rfl⟩
  exact div_le_div_of_nonneg_right (density_trace_le_lambdaMax C hρ.1) hC.le

/-- **Lemma 12 (constraint-set monotonicity)**: enlarging the diagonal constraint set
from `S₁` to `S₂` can only decrease the relaxed GW optimum. -/
theorem lemma12_mono_constraints (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (S₁ S₂ : Set (Finset (Fin n))) (h : S₁ ⊆ S₂) (ε : ℝ)
    (hne : (gwObjSet n C S₂ ε).Nonempty)
    (hbdd : BddAbove (gwObjSet n C S₁ ε)) :
    gwValue n C S₂ ε ≤ gwValue n C S₁ ε := by
  unfold gwValue
  refine csSup_le hne ?_
  intro b hb
  refine le_csSup hbdd ?_
  rcases hb with ⟨ρ, hfeas, rfl⟩
  exact ⟨ρ, ⟨hfeas.1, fun A hA => hfeas.2 A (h hA)⟩, rfl⟩

/-- **Lemma 12 (tolerance monotonicity)**: increasing the trace tolerance from `ε₁`
to `ε₂` can only increase the relaxed GW optimum. -/
theorem lemma12_mono_epsilon (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (S : Set (Finset (Fin n))) (ε₁ ε₂ : ℝ) (h : ε₁ ≤ ε₂)
    (hne : (gwObjSet n C S ε₁).Nonempty)
    (hbdd : BddAbove (gwObjSet n C S ε₂)) :
    gwValue n C S ε₁ ≤ gwValue n C S ε₂ := by
  unfold gwValue
  refine csSup_le hne ?_
  intro b hb
  refine le_csSup hbdd ?_
  rcases hb with ⟨ρ, hfeas, rfl⟩
  exact ⟨ρ, ⟨hfeas.1, fun A hA => le_trans (hfeas.2 A hA) h⟩, rfl⟩

/-- **Lemma 12 (sandwich chain)**: for every `S ⊆ fullConstraints n` and `‖C‖ ≠ 0`,
`lambdaMax n C / ‖C‖ = gwValue n C ∅ 0 ≥ gwValue n C S 0 ≥ gwValue n C (fullConstraints n) 0 ≥ quboValue n C / (2^n ‖C‖)`. -/
theorem lemma12_sandwich (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (S : Set (Finset (Fin n))) (hS : S ⊆ fullConstraints n)
    (hC : ‖C‖ ≠ 0) :
    lambdaMax n C / ‖C‖ = gwValue n C (∅ : Set (Finset (Fin n))) 0 ∧
      gwValue n C (∅ : Set (Finset (Fin n))) 0 ≥ gwValue n C S 0 ∧
      gwValue n C S 0 ≥ gwValue n C (fullConstraints n) 0 ∧
      gwValue n C (fullConstraints n) 0 ≥ quboValue n C / ((2 : ℝ) ^ n * ‖C‖) := by
  have hpos : 0 < ‖C‖ := lt_of_le_of_ne (norm_nonneg C) hC.symm
  have hne (T : Set (Finset (Fin n))) (hT : T ⊆ fullConstraints n) :=
    gwObjSet_nonempty C hT
  have hbdd (T : Set (Finset (Fin n))) := gwObjSet_bddAbove C T hpos
  refine ⟨?_, lemma12_mono_constraints n C ∅ S (Set.empty_subset S) 0
    (hne S hS) (hbdd ∅),
    lemma12_mono_constraints n C S (fullConstraints n) hS 0
      (hne _ (Set.Subset.refl _)) (hbdd S), ?_⟩
  · apply le_antisymm
    · apply (div_le_iff₀ hpos).mpr
      change sSup {r : ℝ | ∃ v : Reg n → ℂ, v ≠ 0 ∧ r = rayleigh C v} ≤ _
      refine csSup_le ?_ ?_
      · refine ⟨_, (fun _ => 1), ?_, rfl⟩
        intro he
        exact one_ne_zero (congrFun he (fun _ => false))
      · rintro r ⟨v, hv, rfl⟩
        have he : gwObjective C (rankOneDensity v) ≤ gwValue n C ∅ 0 := by
          exact le_csSup (hbdd ∅)
            ⟨rankOneDensity v, ⟨rankOneDensity_isDensity hv, by simp⟩, rfl⟩
        rw [gwObjective, trace_rankOneDensity] at he
        exact (div_le_iff₀ hpos).mp he
    · refine csSup_le (hne ∅ (Set.empty_subset _)) ?_
      rintro r ⟨ρ, hρ, rfl⟩
      exact div_le_div_of_nonneg_right (density_trace_le_lambdaMax C hρ.1) hpos.le
  · have hden : 0 < (2 : ℝ) ^ n * ‖C‖ := mul_pos (by positivity) hpos
    apply (div_le_iff₀ hden).mpr
    change sSup {r : ℝ | ∃ x : Reg n → ℝ, IsPlusMinus x ∧
      r = ∑ i, ∑ j, x i * (C i j).re * x j} ≤ _
    refine csSup_le ?_ ?_
    · exact ⟨_, (fun _ => 1), (fun _ => Or.inl rfl), rfl⟩
    · rintro r ⟨x, hx, rfl⟩
      have he : gwObjective C (rankOneDensity (fun i => (x i : ℂ))) ≤
          gwValue n C (fullConstraints n) 0 := by
        exact le_csSup (hbdd _) ⟨_, plusMinus_feasible hx, rfl⟩
      rw [plusMinus_objective C hx] at he
      exact (div_le_iff₀ hden).mp he

end Qatlib.Papers.GWSpeedupYuan25.MainResults.Relaxation
