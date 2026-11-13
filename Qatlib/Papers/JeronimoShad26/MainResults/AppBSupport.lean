/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JeronimoShad26.MainResults.SourceModel.Basic
import Mathlib.Analysis.Matrix.PosDef

set_option backward.isDefEq.respectTransparency false

/-!
# Bipartite Support Inclusion, Trace-Distance Duality, and Fidelity Bounds

This module formalizes Lemma B.1 of Jeronimo and Shad collecting four basic
properties of finite-dimensional quantum states: kernel/support inclusion of a
bipartite positive semidefinite operator inside the tensor product of its
marginals, the variational characterization of trace distance over quantum
effects, the Fuchs--van de Graaf upper bound via root fidelity, and trace
distance contraction under quantum channels.

## Main statements

* `lemma_B_1_support`: Eq. (38), `ker(ω_U ⊗ ω_V) ⊆ ker(ω_{UV})` for `ω ⪰ 0`.
* `lemma_B_1_trace_variational`: Eq. (39), variational formula for `traceDistOn`.
* `lemma_B_1_distance_fidelity`: Eq. (40), Fuchs--van de Graaf upper bound.
* `lemma_B_1_contraction`: monotonicity of `traceDistOn` under `QuantumChannel`.

## References

* [Jeronimo and Shad, 2026][JeronimoShad2026Shadow], Appendix B.1, Lemma B.1,
  Eqs. (38)--(40), p. 34.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Papers.JeronimoShad26.MainResults.AppBSupport

open Matrix
open Qatlib.Papers.JeronimoShad26.MainResults.SourceModel
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.AdaptiveCP.BranchTrace

/-- First partial trace of a bipartite matrix on `Fin D × Fin E`. -/
noncomputable def pTrace1 {D E : ℕ}
    (ω : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : Op D :=
  fun i j => ∑ b : Fin E, ω (i, b) (j, b)

/-- Second partial trace of a bipartite matrix on `Fin D × Fin E`. -/
noncomputable def pTrace2 {D E : ℕ}
    (ω : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : Op E :=
  fun a b => ∑ i : Fin D, ω (i, a) (i, b)

/-- Kronecker product of two square matrices indexed by `Fin m × Fin n`. -/
noncomputable def kronMat {m n : ℕ} (A : Op m) (B : Op n) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  fun i j => A i.1 j.1 * B i.2 j.2

private lemma marginal_kernel_product {D E : ℕ}
    (ω : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hω : ω.PosSemidef)
    (u : Fin D → ℂ) (hu : pTrace1 ω *ᵥ u = 0) (w : Fin E → ℂ) :
    ω *ᵥ (fun p => u p.1 * w p.2) = 0 := by
  classical
  let T : Matrix (Fin D × Fin E) (Fin E) ℂ :=
    fun p b => u p.1 * (1 : Op E) p.2 b
  have hentry (b : Fin E) : (Tᴴ * ω * T) b b =
      ∑ i, ∑ j, star (u i) * ω (i, b) (j, b) * u j := by
    simp [T, mul_apply, conjTranspose_apply, Fintype.sum_prod_type, Finset.sum_mul,
      Matrix.one_apply]
    rw [Finset.sum_comm]
    simp [apply_ite]
  have htrace : (Tᴴ * ω * T).trace = star u ⬝ᵥ (pTrace1 ω *ᵥ u) := by
    simp only [trace, diag_apply, hentry]
    simp only [dotProduct, mulVec, pTrace1, Pi.star_apply, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hzero : Tᴴ * ω * T = 0 :=
    (hω.conjTranspose_mul_mul_same T).trace_eq_zero_iff.mp (by simp [htrace, hu])
  have hq : star (T *ᵥ w) ⬝ᵥ (ω *ᵥ (T *ᵥ w)) = 0 := by
    have hz : star w ⬝ᵥ ((Tᴴ * ω * T) *ᵥ w) = 0 := by simp [hzero]
    simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hz
  have ht : T *ᵥ w = fun p => u p.1 * w p.2 := by
    ext p
    simp [T, mulVec, dotProduct, Matrix.one_apply]
  rw [← ht]
  exact hω.dotProduct_mulVec_zero_iff.mp hq

private lemma marginal_kernel_product_right {D E : ℕ}
    (ω : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hω : ω.PosSemidef)
    (u : Fin D → ℂ) (w : Fin E → ℂ) (hw : pTrace2 ω *ᵥ w = 0) :
    ω *ᵥ (fun p => u p.1 * w p.2) = 0 := by
  have hz := marginal_kernel_product (ω.submatrix Prod.swap Prod.swap)
    (hω.submatrix Prod.swap) w hw u
  ext p
  have hh := congrFun hz p.swap
  simp only [mulVec, dotProduct, submatrix_apply, Prod.swap_prod_mk,
    Prod.swap_swap, Fintype.sum_prod_type, Pi.zero_apply] at hh ⊢
  rw [Finset.sum_comm] at hh
  simpa only [mul_comm] using hh

/-- Lemma B.1, Eq. (38): for any bipartite positive semidefinite matrix `ω`, the
kernel of `pTrace1 ω ⊗ pTrace2 ω` is contained in the kernel of `ω`. -/
theorem lemma_B_1_support {D E : ℕ}
    (ω : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hω : ω.PosSemidef) :
    ∀ v : Fin D × Fin E → ℂ,
      Matrix.mulVec (kronMat (pTrace1 ω) (pTrace2 ω)) v = 0 →
      Matrix.mulVec ω v = 0 := by
  classical
  have h₁ : (pTrace1 ω).PosSemidef := by
    have heq : pTrace1 ω = ∑ b : Fin E,
        ω.submatrix (fun i => (i, b)) (fun j => (j, b)) := by
      ext i j
      simp [pTrace1, Matrix.sum_apply]
    rw [heq]
    exact posSemidef_sum _ (fun b _ => hω.submatrix (fun i => (i, b)))
  have h₂ : (pTrace2 ω).PosSemidef := by
    have heq : pTrace2 ω = ∑ i : Fin D,
        ω.submatrix (fun a => (i, a)) (fun b => (i, b)) := by
      ext a b
      simp [pTrace2, Matrix.sum_apply]
    rw [heq]
    exact posSemidef_sum _ (fun i _ => hω.submatrix (fun a => (i, a)))
  let U := h₁.1.eigenvectorUnitary
  let V := h₂.1.eigenvectorUnitary
  let W := Matrix.kronecker U.val V.val
  let d : Fin D × Fin E → ℂ :=
    fun p => (h₁.1.eigenvalues p.1 : ℂ) * (h₂.1.eigenvalues p.2 : ℂ)
  have hW : W ∈ Matrix.unitaryGroup (Fin D × Fin E) ℂ :=
    kronecker_mem_unitary U.property V.property
  have hWl : Wᴴ * W = 1 := mem_unitaryGroup_iff'.mp hW
  have hWr : W * Wᴴ = 1 := mem_unitaryGroup_iff.mp hW
  have hspec : kronMat (pTrace1 ω) (pTrace2 ω) = W * diagonal d * Wᴴ := by
    have hs₁ : pTrace1 ω =
        U.val * diagonal (fun i => (h₁.1.eigenvalues i : ℂ)) * U.valᴴ :=
      h₁.1.spectral_theorem
    have hs₂ : pTrace2 ω =
        V.val * diagonal (fun a => (h₂.1.eigenvalues a : ℂ)) * V.valᴴ :=
      h₂.1.spectral_theorem
    calc
      kronMat (pTrace1 ω) (pTrace2 ω) = Matrix.kronecker
          (U.val * diagonal (fun i => (h₁.1.eigenvalues i : ℂ)) * U.valᴴ)
          (V.val * diagonal (fun a => (h₂.1.eigenvalues a : ℂ)) * V.valᴴ) :=
        congrArg₂ Matrix.kronecker hs₁ hs₂
      _ = W * diagonal d * Wᴴ := by
        simp only [W, d, Matrix.kronecker, mul_kronecker_mul,
          diagonal_kronecker_diagonal, conjTranspose_kronecker]
  have hcol (p : Fin D × Fin E) (hp : d p = 0) :
      ω *ᵥ (fun r => W r p) = 0 := by
    rcases mul_eq_zero.mp hp with hp | hp
    · have he : h₁.1.eigenvalues p.1 = 0 := Complex.ofReal_eq_zero.mp hp
      apply marginal_kernel_product ω hω (fun x => U.val x p.1) _
        (fun y => V.val y p.2)
      simpa only [U, IsHermitian.eigenvectorUnitary_apply, he, zero_smul] using
        h₁.1.mulVec_eigenvectorBasis p.1
    · have he : h₂.1.eigenvalues p.2 = 0 := Complex.ofReal_eq_zero.mp hp
      apply marginal_kernel_product_right ω hω (fun x => U.val x p.1)
        (fun y => V.val y p.2)
      simpa only [V, IsHermitian.eigenvectorUnitary_apply, he, zero_smul] using
        h₂.1.mulVec_eigenvectorBasis p.2
  intro v hv
  let c := Wᴴ *ᵥ v
  have hvc : v = W *ᵥ c := by simp only [c, mulVec_mulVec, hWr, one_mulVec]
  have hc : diagonal d *ᵥ c = 0 := by
    have hh := congrArg (fun z => Wᴴ *ᵥ z) hv
    rw [hspec] at hh
    simpa only [c, mulVec_mulVec, mul_assoc, ← mul_assoc Wᴴ W,
      hWl, one_mul, mulVec_zero] using hh
  rw [hvc]
  ext r
  simp only [mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : c p = 0
  · simp [hp]
  · have hd : d p = 0 := (mul_eq_zero.mp (by
        simpa only [mulVec_diagonal, Pi.zero_apply] using congrFun hc p)).resolve_right hp
    have hh := congrFun (hcol p hd) r
    simpa only [mulVec, dotProduct, Finset.sum_mul, mul_assoc, Pi.zero_apply, zero_mul] using
      congrArg (fun z => z * c p) hh

/-- Lemma B.1, Eq. (39): for density matrices `ρ` and `σ`, `traceDistOn ρ σ`
equals the supremum of `|bornOn E (ρ - σ)|` over all effects `0 ⪯ E ⪯ I`. -/
theorem lemma_B_1_trace_variational {D : ℕ} (ρ σ : Op D)
    (hρ : IsDensityOn ρ) (hσ : IsDensityOn σ) :
    traceDistOn ρ σ =
      sSup (Set.range (fun E : {E : Op D // IsEffectOn E} =>
        |bornOn E.1 (ρ - σ)|)) := by
  classical
  let X := ρ - σ
  have hX : X.IsHermitian := hρ.1.1.sub hσ.1.1
  let U := hX.eigenvectorUnitary
  let l := hX.eigenvalues
  let p : Fin D → ℝ := fun i => if 0 ≤ l i then l i else 0
  let P : ℝ := ∑ i, p i
  have hUl : U.valᴴ * U.val = 1 := (mem_unitaryGroup_iff').mp U.property
  have hUr : U.val * U.valᴴ = 1 := (mem_unitaryGroup_iff).mp U.property
  have hspec : X = U.val * diagonal (fun i => (l i : ℂ)) * U.valᴴ :=
    hX.spectral_theorem
  have hsum : ∑ i, l i = 0 := by
    have ht : X.trace = 0 := by simp [X, trace_sub, hρ.2, hσ.2]
    simpa [l] using
      congrArg Complex.re (hX.trace_eq_sum_eigenvalues.symm.trans ht)
  have hdist : traceDistOn ρ σ = P := by
    have habs : ∑ i, |l i| = 2 * P := by
      have hi (i : Fin D) : |l i| = 2 * p i - l i := by
        by_cases h : 0 ≤ l i
        · simp [p, h, abs_of_nonneg h]; ring
        · simp [p, h, abs_of_neg (lt_of_not_ge h)]
      simp_rw [hi]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, sub_zero]
    change X.traceNorm / 2 = P
    rw [traceNorm_Hermitian_eq_sum_abs_eigenvalues hX]
    change (∑ i, |l i|) / 2 = P
    rw [habs]
    ring
  have hborn (A : Op D) :
      bornOn A X = ∑ i, ((U.valᴴ * A * U.val) i i).re * l i := by
    have ht : (A * X).trace =
        ((U.valᴴ * A * U.val) * diagonal (fun i => (l i : ℂ))).trace := by
      rw [hspec, ← mul_assoc, trace_mul_cycle]
      simp only [mul_assoc]
    unfold bornOn
    rw [ht]
    simp only [trace, diag_apply, mul_diagonal, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hbound (A : {A : Op D // IsEffectOn A}) : |bornOn A.1 X| ≤ P := by
    let B := U.valᴴ * A.1 * U.val
    have hB : B.PosSemidef := A.2.1.conjTranspose_mul_mul_same U.val
    have hC : (1 - B).PosSemidef := by
      have hc := A.2.2.conjTranspose_mul_mul_same U.val
      simpa only [mul_sub, sub_mul, mul_one, hUl] using hc
    have hd (i : Fin D) : 0 ≤ (B i i).re ∧ (B i i).re ≤ 1 := by
      have hb := (Complex.nonneg_iff.mp (hB.diag_nonneg (i := i))).1
      have hc := (Complex.nonneg_iff.mp (hC.diag_nonneg (i := i))).1
      simp only [Matrix.sub_apply, Complex.sub_re, Matrix.one_apply_eq,
        Complex.one_re] at hc
      exact ⟨hb, by linarith⟩
    have hi (i : Fin D) :
        -(p i - l i) ≤ (B i i).re * l i ∧ (B i i).re * l i ≤ p i := by
      have hh := hd i
      by_cases h : 0 ≤ l i <;> simp only [p, h, ite_true, ite_false] <;> constructor <;>
        nlinarith
    rw [hborn]
    apply abs_le.mpr
    constructor
    · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hi i).1)
      simpa only [Finset.sum_neg_distrib, Finset.sum_sub_distrib, hsum, sub_zero] using hh
    · exact Finset.sum_le_sum (fun i _ => (hi i).2)
  let q : Fin D → ℂ := fun i => if 0 ≤ l i then 1 else 0
  let A : Op D := U.val * diagonal q * U.valᴴ
  have hA : IsEffectOn A := by
    constructor
    · apply PosSemidef.mul_mul_conjTranspose_same _ U.val
      exact PosSemidef.diagonal (fun i => by by_cases h : 0 ≤ l i <;> simp [q, h])
    · have heq : 1 - A = U.val * diagonal (fun i => 1 - q i) * U.valᴴ := by
        rw [← diagonal_sub, diagonal_one, mul_sub, sub_mul, mul_one,
          hUr]
      rw [heq]
      apply PosSemidef.mul_mul_conjTranspose_same _ U.val
      exact PosSemidef.diagonal (fun i => by by_cases h : 0 ≤ l i <;> simp [q, h])
  have hattain : |bornOn A X| = P := by
    have ha : U.valᴴ * A * U.val = diagonal q := by
      simp only [A, mul_assoc]
      rw [← mul_assoc U.valᴴ U.val, hUl, one_mul, mul_one]
    have hb : bornOn A X = P := by
      rw [hborn, ha]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : 0 ≤ l i <;> simp [q, p, h]
    rw [hb, abs_of_nonneg]
    exact Finset.sum_nonneg (fun i _ => by by_cases h : 0 ≤ l i <;> simp [p, h])
  have hbd : BddAbove (Set.range (fun A : {A : Op D // IsEffectOn A} =>
      |bornOn A.1 X|)) := ⟨P, by rintro _ ⟨A, rfl⟩; exact hbound A⟩
  rw [hdist]
  apply le_antisymm
  · rw [← hattain]
    exact le_csSup hbd (Set.mem_range_self (⟨A, hA⟩ : {A : Op D // IsEffectOn A}))
  · apply csSup_le ⟨_, Set.mem_range_self (⟨A, hA⟩ : {A : Op D // IsEffectOn A})⟩
    rintro _ ⟨B, rfl⟩
    exact hbound B

/-- Lemma B.1, Eq. (40): Fuchs--van de Graaf upper bound relating trace distance
and root fidelity. -/
theorem lemma_B_1_distance_fidelity {D : ℕ} (ρ σ : Op D)
    (hρ : IsDensityOn ρ) (hσ : IsDensityOn σ) :
    traceDistOn ρ σ ≤ Real.sqrt (1 - (rootFidelity ρ σ) ^ 2) := by
  have h := (Qatlib.Concepts.MixedFidelity.FidelityMetric.g3 D ρ σ hρ hσ).1.2
  simpa only [traceDistOn, rootFidelity,
    Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance,
    Qatlib.Concepts.MixedFidelity.FidelityMetric.Froot] using h

/-- Lemma B.1: trace distance contracts under quantum channels. -/
theorem lemma_B_1_contraction {D E : ℕ} (ρ σ : Op D)
    (hρ : IsDensityOn ρ) (hσ : IsDensityOn σ) (Λ : QuantumChannel D E) :
    traceDistOn (Λ.map ρ) (Λ.map σ) ≤ traceDistOn ρ σ := by
  have h := (Qatlib.Concepts.MixedFidelity.FidelityMetric.g3 D ρ σ hρ hσ).2 E Λ
  simpa only [traceDistOn,
    Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance] using h.1

end Qatlib.Papers.JeronimoShad26.MainResults.AppBSupport
