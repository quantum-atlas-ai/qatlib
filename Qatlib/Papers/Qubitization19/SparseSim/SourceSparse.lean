/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.SparseSim.SparseSimCorrectedRestrictedLowc

set_option backward.isDefEq.respectTransparency false

/-!
# Standard-Form Encoding and Simulation of Sparse Hamiltonians

This module formalizes Lemma 6 and Corollary 15 in frame form: every `d`-sparse
Hermitian matrix `H` with entrywise max-norm bound `b` admits a finite workspace
carrying two isometries `L, R` and a self-adjoint unitary reflection/swap `S`
such that `Lᴴ * R = (d * b)⁻¹ • H` and `S * L = R`, combining with Theorem 1 to
yield `d`-sparse Hamiltonian simulation.

## Main statements

* `SparseFrameWitness`: workspace frame witness `(W, L, R, S)` realizing
  `Lᴴ * R = (d * b)⁻¹ • H` and `S * L = R`.
* `Lemma6SparseStandardFormEncoding`: universal existence predicate for
  `d`-sparse Hermitian Hamiltonians of max-norm at most `b`.
* `lemma6_sparse_standard_form`: proof of `Lemma6SparseStandardFormEncoding`.
* `corollary15_sparse_simulation`: `d`-sparse Hamiltonian simulation in the
  frame model.

## References

* [Low and Chuang, 2019][LowChuang2019], Lemma 6, Eqs. (11)--(13), p. 8, and
  Corollary 15, p. 16.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.SignalPrimitive.SparseSim

namespace Qatlib.Papers.Qubitization19.SparseSim

/-- Frame-form standard-form encoding witness for a `d`-sparse Hamiltonian `H` at
scale `d * b`: a finite workspace `W` with isometries `L, R : Matrix W I ℂ`
whose inner-product block `Lᴴ * R` equals `(d * b)⁻¹ • H`, together with a
self-adjoint unitary `S` satisfying `S * L = R`. -/
structure SparseFrameWitness (I : Type*) [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (d : ℕ) (b : ℝ) where
  /-- Workspace dimension carrier. -/
  W : Type
  /-- The workspace carrier is finite. -/
  instFintype : Fintype W
  /-- The workspace carrier has decidable equality. -/
  instDecidableEq : DecidableEq W
  /-- Left state-preparation isometry `T₁`. -/
  L : Matrix W I ℂ
  /-- Right state-preparation isometry `T₂`. -/
  R : Matrix W I ℂ
  /-- Self-adjoint unitary swap/reflection on the workspace. -/
  S : Matrix W W ℂ
  /-- `L` is an isometry (`Lᴴ * L = 1`). -/
  isIsometry_L : IsIsometry L
  /-- `R` is an isometry (`Rᴴ * R = 1`). -/
  isIsometry_R : IsIsometry R
  /-- Projected overlap `Lᴴ * R = (d * b)⁻¹ • H`. -/
  corner : Lᴴ * R = ((((d : ℝ) * b)⁻¹ : ℝ) : ℂ) • H
  /-- `S` is unitary. -/
  S_mem_unitaryGroup : S ∈ Matrix.unitaryGroup W ℂ
  /-- `S` is Hermitian. -/
  S_conjTranspose : Sᴴ = S
  /-- `S` is an involution (`S * S = 1`). -/
  S_mul_self : S * S = 1
  /-- `S` maps `L` to `R`. -/
  S_mul_L : S * L = R

attribute [instance] SparseFrameWitness.instFintype SparseFrameWitness.instDecidableEq

/-- Statement of Lemma 6 in frame form: every `d`-sparse Hermitian matrix `H`
with entrywise max-norm at most `b > 0` and sparsity `d > 0` admits a
`SparseFrameWitness` at scale `d * b`. -/
def Lemma6SparseStandardFormEncoding : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H : Matrix I I ℂ) (d : ℕ) (b : ℝ),
    H.IsHermitian → 0 < d → 0 < b →
    (∀ o, (Finset.univ.filter fun i => H o i ≠ 0).card ≤ d) →
    (∀ i, (Finset.univ.filter fun o => H o i ≠ 0).card ≤ d) →
    (∀ o i, ‖H o i‖ ≤ b) →
    Nonempty (SparseFrameWitness I H d b)

/-- **Lemma 6**: every `d`-sparse Hermitian Hamiltonian `H` with entrywise norm at
most `b` admits a standard-form frame encoding at normalization `d * b`. -/
theorem lemma6_sparse_standard_form : Lemma6SparseStandardFormEncoding := by
  intro I _ _ H d b hH hd hb _hrow hcol hmax
  classical
  let M : ℝ := (d : ℝ) * b
  have hM : 0 < M := by dsimp [M]; positivity
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  have hmass (j : I) : (∑ k, ‖H k j‖) ≤ M := by
    calc
      (∑ k, ‖H k j‖) = ∑ k ∈ Finset.univ.filter (fun k => H k j ≠ 0), ‖H k j‖ := by
        symm
        exact Finset.sum_filter_of_ne fun k _ hk => by simpa using hk
      _ ≤ ∑ _k ∈ Finset.univ.filter (fun k => H k j ≠ 0), b :=
        Finset.sum_le_sum fun k _ => hmax k j
      _ = ((Finset.univ.filter (fun k => H k j ≠ 0)).card : ℝ) * b := by simp
      _ ≤ M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcol j) hb.le
  -- A real amplitude and a phase, with division by zero giving phase zero.
  let a (z : ℂ) : ℂ := (Real.sqrt (‖z‖ / (2 * M)) : ℝ)
  let p (z : ℂ) : ℂ := z / (‖z‖ : ℂ)
  have ha (z : ℂ) : star (a z) * a z = (‖z‖ / (2 * M) : ℝ) := by
    change star ((Real.sqrt (‖z‖ / (2 * M)) : ℝ) : ℂ) *
      (Real.sqrt (‖z‖ / (2 * M)) : ℝ) = _
    rw [show star ((Real.sqrt (‖z‖ / (2 * M)) : ℝ) : ℂ) =
      (Real.sqrt (‖z‖ / (2 * M)) : ℝ) from RCLike.conj_ofReal _]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  have hp (z : ℂ) : star (a z * p z) * (a z * p z) = (‖z‖ / (2 * M) : ℝ) := by
    by_cases hz : z = 0
    · simp [hz, a, p]
    · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      have hpz : star (p z) * p z = 1 := by
        change star (z / (‖z‖ : ℂ)) * (z / (‖z‖ : ℂ)) = 1
        rw [star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_div_comm,
          ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
          Complex.ofReal_pow, pow_two, div_self (mul_ne_zero hn hn)]
      calc
        star (a z * p z) * (a z * p z) = (star (a z) * a z) * (star (p z) * p z) := by
          rw [star_mul]; ring
        _ = (‖z‖ / (2 * M) : ℝ) := by rw [ha, hpz, mul_one]
  let Y : Type := I ⊕ Unit
  let W : Type := Y × Y × Bool
  let ψ (j : I) (y : Y) (f : Bool) : ℂ := match y with
    | Sum.inl k => if f then a (H k j) * p (H k j) else a (H k j)
    | Sum.inr _ => if f then 0 else (Real.sqrt (1 - (∑ k, ‖H k j‖) / M) : ℝ)
  have hψ (j : I) : ∑ y, ∑ f, star (ψ j y f) * ψ j y f = 1 := by
    have hr : 0 ≤ 1 - (∑ k, ‖H k j‖) / M := by
      exact sub_nonneg.mpr ((div_le_one hM).mpr (hmass j))
    dsimp only [Y]
    simp only [Fintype.sum_sum_type, ψ, Fintype.sum_bool, Bool.false_eq_true,
      ↓reduceIte, hp, ha, star_zero, mul_zero, Fintype.sum_unique]
    rw [show star ((Real.sqrt (1 - (∑ k, ‖H k j‖) / M) : ℝ) : ℂ) *
        (Real.sqrt (1 - (∑ k, ‖H k j‖) / M) : ℝ) =
        ((1 - (∑ k, ‖H k j‖) / M : ℝ) : ℂ) by
      rw [show star ((Real.sqrt (1 - (∑ k, ‖H k j‖) / M) : ℝ) : ℂ) =
        (Real.sqrt (1 - (∑ k, ‖H k j‖) / M) : ℝ) from RCLike.conj_ofReal _]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]]
    push_cast
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    field_simp
    ring
  let L : Matrix W I ℂ := fun w j => if w.1 = Sum.inl j then ψ j w.2.1 w.2.2 else 0
  have hL : Lᴴ * L = 1 := by
    ext k j
    dsimp only [W, Y] at L ⊢
    by_cases hkj : k = j
    · subst j
      have hψk := hψ k
      dsimp only [Y] at hψk
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, L, Fintype.sum_prod_type,
        Fintype.sum_sum_type, Matrix.one_apply] using hψk
    · rw [Matrix.mul_apply, Matrix.one_apply_ne hkj]
      apply Finset.sum_eq_zero
      intro w _
      by_cases hw : w.1 = Sum.inl k
      · have hwj : w.1 ≠ Sum.inl j := by
          intro hwj
          exact hkj (Sum.inl.inj (hw.symm.trans hwj))
        simp [Matrix.conjTranspose_apply, L, hwj]
      · simp [Matrix.conjTranspose_apply, L, hw]
  -- Swapping the registers and flipping the flag is an involution.
  let τ : W → W := fun w => (w.2.1, w.1, !w.2.2)
  have hτ (w : W) : τ (τ w) = w := by simp [τ]
  let S : Matrix W W ℂ := fun w z => if z = τ w then 1 else 0
  have hSM {T : Type} (A : Matrix W T ℂ) (w : W) (j : T) : (S * A) w j = A (τ w) j := by
    dsimp only [W, Y] at S A w ⊢
    simp only [Matrix.mul_apply, S, ite_mul, one_mul, zero_mul]
    exact Fintype.sum_ite_eq' (τ w) (fun x => A x j)
  have hSstar : Sᴴ = S := by
    ext w z
    have he : w = τ z ↔ z = τ w :=
      ⟨fun h => by rw [h, hτ], fun h => by rw [h, hτ]⟩
    simp [Matrix.conjTranspose_apply, S, he]
  have hSS : S * S = 1 := by
    ext w z
    rw [hSM]
    simp [S, hτ, Matrix.one_apply, eq_comm]
  -- The two surviving flag terms each contribute H k j / (2 * M).
  have hoverlap (k j : I) :
      (∑ f, star (ψ k (Sum.inl j) f) * ψ j (Sum.inl k) (!f)) =
        (M⁻¹ : ℝ) * H k j := by
    have hn : ‖H j k‖ = ‖H k j‖ := by rw [← hH.apply k j, norm_star]
    have has : a (H j k) = a (H k j) := by simp only [a, hn]
    have hps : star (p (H j k)) = p (H k j) := by
      simp only [p, star_div₀, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.star_def, hH.apply k j, hn]
    simp only [Fintype.sum_bool, ψ, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte, star_mul, has, hps]
    calc
      p (H k j) * star (a (H k j)) * a (H k j) +
          star (a (H k j)) * (a (H k j) * p (H k j)) =
          2 * (star (a (H k j)) * a (H k j)) * p (H k j) := by ring
      _ = (M⁻¹ : ℝ) * H k j := by
        rw [ha]
        by_cases hz : H k j = 0
        · simp [hz, p]
        · have hnz : (‖H k j‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
          dsimp [p]
          push_cast
          field_simp
  have hcorner : Lᴴ * (S * L) = ((M⁻¹ : ℝ) : ℂ) • H := by
    ext k j
    dsimp only [W, Y] at L S τ ⊢
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hSM,
      Matrix.smul_apply, smul_eq_mul]
    simpa [L, τ, Fintype.sum_prod_type, Fintype.sum_sum_type, apply_ite]
      using hoverlap k j
  exact ⟨{
    W := W
    instFintype := inferInstance
    instDecidableEq := inferInstance
    L := L
    R := S * L
    S := S
    isIsometry_L := hL
    isIsometry_R := by
      change (S * L)ᴴ * (S * L) = 1
      rw [Matrix.conjTranspose_mul, hSstar, Matrix.mul_assoc, ← Matrix.mul_assoc S S L,
        hSS, Matrix.one_mul, hL]
    corner := hcorner
    S_mem_unitaryGroup := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hSstar, hSS]
    S_conjTranspose := hSstar
    S_mul_self := hSS
    S_mul_L := rfl }⟩

/-- **Corollary 15**: Hamiltonian simulation of a `d`-sparse Hermitian matrix in
the walk-frame model. -/
theorem corollary15_sparse_simulation :
    Qatlib.Concepts.SignalPrimitive.SparseSim.SparseSimulationCorrectedRestricted :=
  Qatlib.Concepts.SignalPrimitive.SparseSim.sparseSimulationCorrectedRestricted

end Qatlib.Papers.Qubitization19.SparseSim
