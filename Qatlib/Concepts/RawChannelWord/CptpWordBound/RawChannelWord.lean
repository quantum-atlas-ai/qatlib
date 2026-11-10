/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RawChannelWord.CptpWordBound.RawChannelWordDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ReferenceError.DensityToRaw
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.SchattenDiamond.DiamondNorm

namespace Qatlib.Concepts.RawChannelWord.CptpWordBound
open Matrix
open scoped BigOperators ComplexOrder ENNReal
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

def dilation {I : Type} (X : Matrix I I ℂ) : Matrix (I ⊕ I) (I ⊕ I) ℂ :=
  Matrix.fromBlocks 0 X Xᴴ 0

theorem dilation_hermitian {I : Type} (X : Matrix I I ℂ) : (dilation X).IsHermitian :=
  Matrix.IsHermitian.fromBlocks (by simp) rfl (by simp)

private theorem trace_blocks {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I I ℂ) (B : Matrix I J ℂ) (C : Matrix J I ℂ) (D : Matrix J J ℂ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem dilation_traceNorm {I : Type} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) :
    (dilation X).traceNorm = 2 * X.traceNorm := by
  classical
  letI : DecidableEq I := Classical.decEq I
  letI : DecidableEq (I ⊕ I) := Classical.decEq (I ⊕ I)
  let L : Matrix (I ⊕ I) I ℂ := fun a b => match a with
    | .inl i => if i=b then 1 else 0
    | .inr _ => 0
  let R : Matrix (I ⊕ I) I ℂ := fun a b => match a with
    | .inl _ => 0
    | .inr i => if i=b then 1 else 0
  have hL : L.Isometry := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, L, Fintype.sum_sum_type,
      Matrix.one_apply, eq_comm]
  have hR : R.Isometry := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, R, Fintype.sum_sum_type,
      Matrix.one_apply, eq_comm]
  have hsplit : dilation X = L*X*Rᴴ + R*Xᴴ*Lᴴ := by
    ext a b
    cases a <;> cases b <;>
      simp [dilation, L, R, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hupper : (dilation X).traceNorm ≤ 2*X.traceNorm := by
    rw [hsplit]
    have h := Matrix.traceNorm_add_le (L*X*Rᴴ) (R*Xᴴ*Lᴴ)
    rw [Matrix.traceNorm_isometry_right hR, Matrix.traceNorm_isometry_left hL,
      Matrix.traceNorm_isometry_right hL, Matrix.traceNorm_isometry_left hR,
      Matrix.traceNorm_conjTranspose] at h
    linarith
  obtain ⟨U, hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U X).1
  let W : Matrix (I ⊕ I) (I ⊕ I) ℂ := Matrix.fromBlocks 0 U.valᴴ U.val 0
  have hUU : U.valᴴ * U.val = 1 := Matrix.UnitaryGroup.star_mul_self U
  have hUU' : U.val * U.valᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp U.property
  have hW : W.Isometry := by
    change Wᴴ * W = 1
    simp [W, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hUU, hUU',
      Matrix.fromBlocks_one]
    ext a b
    by_cases hab : a=b <;> simp [Matrix.one_apply, hab]
  have htrace : ((W * dilation X).trace).re = 2*X.traceNorm := by
    have hc : (U.valᴴ*Xᴴ).trace = star ((U.val*X).trace) := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.trace_mul_comm]
    simp only [W, dilation, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero, trace_blocks]
    change ((U.valᴴ*Xᴴ).trace + (U.val*X).trace).re = _
    rw [hc, Complex.add_re, Complex.star_def, Complex.conj_re, hU]
    ring
  have hlower : 2*X.traceNorm ≤ (dilation X).traceNorm := by
    rw [← htrace]
    exact (Complex.re_le_norm _).trans ((Matrix.abs_trace_le_traceNorm _).trans_eq
      (Matrix.traceNorm_isometry_left hW))
  exact le_antisymm hupper hlower

private theorem kraus_blocks {I J K : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K]
    (A : K → Matrix J I ℂ) (X Y Z V : Matrix I I ℂ) :
    (MatrixMap.of_kraus (fun k => Matrix.fromBlocks (A k) 0 0 (A k))
      (fun k => Matrix.fromBlocks (A k) 0 0 (A k))) (Matrix.fromBlocks X Y Z V) =
    Matrix.fromBlocks ((MatrixMap.of_kraus A A) X) ((MatrixMap.of_kraus A A) Y)
      ((MatrixMap.of_kraus A A) Z) ((MatrixMap.of_kraus A A) V) := by
  simp only [MatrixMap.of_kraus_eq_sum_conj, LinearMap.sum_apply, MatrixMap.conj,
    LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, zero_add, add_zero]
  ext a b
  cases a <;> cases b <;> simp [Matrix.sum_apply]

theorem cp_tp_raw_contraction {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (T : MatrixMap I J ℂ)
    (hcp : T.IsCompletelyPositive) (htp : T.IsTracePreserving) (X : Matrix I I ℂ) :
    (T X).traceNorm ≤ X.traceNorm := by
  classical
  obtain ⟨A, hA⟩ := MatrixMap.IsCompletelyPositive.exists_kraus T hcp
  subst T
  let B := fun k => Matrix.fromBlocks (A k) 0 0 (A k)
  let S := MatrixMap.of_kraus B B
  have hSpos : S.IsPositive := MatrixMap.of_kraus_isPositive B
  have hStp : S.IsTracePreserving := by
    intro Y
    have he := kraus_blocks A (Matrix.toBlocks₁₁ Y) (Matrix.toBlocks₁₂ Y)
      (Matrix.toBlocks₂₁ Y) (Matrix.toBlocks₂₂ Y)
    rw [Matrix.fromBlocks_toBlocks] at he
    change (S Y).trace = Y.trace
    rw [he, trace_blocks, htp, htp]
    simp [Matrix.trace, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]
  have hstar : (MatrixMap.of_kraus A A) Xᴴ = ((MatrixMap.of_kraus A A) X)ᴴ := by
    simp [MatrixMap.of_kraus_eq_sum_conj, MatrixMap.conj, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have he : S (dilation X) = dilation ((MatrixMap.of_kraus A A) X) := by
    simpa only [map_zero, hstar, dilation, S, B] using kraus_blocks A 0 X Xᴴ 0
  have h := positive_trace_preserving_hermitian_trace_contraction S hSpos hStp
    (dilation_hermitian X)
  rw [he, dilation_traceNorm, dilation_traceNorm] at h
  linarith

theorem channel_raw_contraction {D E : ℕ} (T : QuantumChannel D E) (r : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    (tensorLeft T.map X).traceNorm ≤ X.traceNorm := by
  let S :=
      CPTPMap.prod (Qatlib.Concepts.ChannelTheory.Stinespring.toPhyslib T)
      (CPTPMap.id (dIn := Fin r))
  have h := cp_tp_raw_contraction S.map S.cp S.TP X
  have he : S.map X = tensorLeft T.map X := by
    ext ⟨i,a⟩ ⟨j,b⟩
    exact Qatlib.Concepts.ChannelTheory.Stinespring.kron_id_apply T.map r X i j a b
  rwa [he] at h

theorem g1 : ∀ (D E : ℕ) (T : QuantumChannel D E),
    (∀ (r : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      Matrix.traceNorm (tensorLeft T.map X) ≤ Matrix.traceNorm X) ∧
    finiteDiamondNorm T.map ≤ 1 ∧ (0 < D → finiteDiamondNorm T.map = 1) := by
  intro D E T
  have hc := channel_raw_contraction T
  have hn : finiteDiamondNorm T.map ≤ 1 := by
    simpa using (finiteDiamondNorm_le_iff_uniform D E T.map 1 (by norm_num)).2
      (by simpa using hc)
  refine ⟨hc, hn, ?_⟩
  intro hD
  let i : Fin D := ⟨0,hD⟩
  let ρ := outerProduct (Qatlib.Foundations.PureStateMath.Ket i)
  have hρ : IsDensityOperator ρ := outerProduct_density (normalized_ket i)
  have hout := T.preservesDensity hρ
  have hnorm {d : ℕ} {Y : Operator d} (hY : IsDensityOperator Y) : Y.traceNorm = 1 := by
    have h := hY.1.traceNorm_eq_trace.trans hY.2
    simpa using congrArg Complex.re h
  let e : (Fin D × Fin 1) ≃ Fin D :=
    ⟨Prod.fst, (fun a => (a,0)), (fun a => by ext <;> simp [Subsingleton.elim a.2 0]), fun _ => rfl⟩
  let f : (Fin E × Fin 1) ≃ Fin E :=
    ⟨Prod.fst, (fun a => (a,0)), (fun a => by ext <;> simp [Subsingleton.elim a.2 0]), fun _ => rfl⟩
  let X := Matrix.reindex e.symm e.symm ρ
  have hx : X.traceNorm = 1 := by rw [diamond_traceNorm_reindex]; exact hnorm hρ
  have he : tensorLeft T.map X = Matrix.reindex f.symm f.symm (T.map ρ) := by
    ext a b
    rfl
  have ho : (tensorLeft T.map X).traceNorm = 1 := by
    rw [he, diamond_traceNorm_reindex]; exact hnorm hout
  apply le_antisymm hn
  unfold finiteDiamondNorm
  exact le_iSup_of_le 1 (le_iSup_of_le X (by simp [hx, ho]))

theorem run_append {D : ℕ} (p q : List (QuantumChannel D D)) :
    (run (p++q)).map = ((run q).comp (run p)).map := by
  induction p with
  | nil => change (run q).map = (run q).map.comp LinearMap.id; simp
  | cons a p ih =>
    change (run ((a::p)++q)).map = (run q).map.comp ((run p).map.comp a.map)
    change ((run (p++q)).map.comp a.map) = _
    rw [ih]
    rfl

theorem budget_nonneg {D : ℕ} (p : List (ApproxStep D))
    (hp : ∀ s ∈ p, 0 ≤ s.error) : 0 ≤ budget p := by
  unfold budget
  apply List.sum_nonneg
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  exact hp s hs

private theorem word_error {D : ℕ} (p : List (ApproxStep D))
    (hp : ∀ s ∈ p, 0 ≤ s.error ∧
      finiteDiamondNorm (s.actual.map-s.ideal.map) ≤ ENNReal.ofReal s.error) :
    finiteDiamondNorm ((actualWord p).map-(idealWord p).map) ≤ ENNReal.ofReal (budget p) := by
  induction p with
  | nil => simp [actualWord, idealWord, run, budget]
  | cons s p ih =>
    have hs := hp s (by simp)
    have ht : ∀ a ∈ p, 0 ≤ a.error ∧
        finiteDiamondNorm (a.actual.map-a.ideal.map) ≤ ENNReal.ofReal a.error :=
      fun a ha => hp a (by simp [ha])
    have hb := budget_nonneg p (fun a ha => (ht a ha).1)
    have hrec := ih ht
    let A := (actualWord p).map
    let I := (idealWord p).map
    have he : (actualWord (s::p)).map-(idealWord (s::p)).map =
        (A-I).comp s.actual.map + I.comp (s.actual.map-s.ideal.map) := by
      apply LinearMap.ext
      intro X
      change A (s.actual.map X)-I (s.ideal.map X) = _
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, map_sub]
      abel
    rw [he]
    have htriangle := (finiteDiamondNorm_algebra D D D
      ((A-I).comp s.actual.map) (I.comp (s.actual.map-s.ideal.map)) I).1
    have hleft := (finiteDiamondNorm_algebra D D D s.actual.map s.actual.map (A-I)).2.1
    have hright := (finiteDiamondNorm_algebra D D D (s.actual.map-s.ideal.map) s.ideal.map I).2.1
    have hA := (g1 D D s.actual).2.1
    have hI := (g1 D D (idealWord p)).2.1
    have hl : finiteDiamondNorm ((A-I).comp s.actual.map) ≤ ENNReal.ofReal (budget p) := by
      exact hleft.trans ((mul_le_mul hrec hA bot_le bot_le).trans_eq (mul_one _))
    have hr : finiteDiamondNorm (I.comp (s.actual.map-s.ideal.map)) ≤ ENNReal.ofReal s.error := by
      exact hright.trans ((mul_le_mul hI hs.2 bot_le bot_le).trans_eq (one_mul _))
    exact (htriangle.trans (add_le_add hl hr)).trans_eq (by
      change ENNReal.ofReal (budget p) + ENNReal.ofReal s.error =
        ENNReal.ofReal (s.error + budget p)
      rw [ENNReal.ofReal_add hs.1 hb, add_comm])

theorem g2 : ∀ (D : ℕ) (p : List (ApproxStep D)),
    (∀ s ∈ p, 0 ≤ s.error ∧
      finiteDiamondNorm (s.actual.map-s.ideal.map) ≤ ENNReal.ofReal s.error) →
    finiteDiamondNorm ((actualWord p).map-(idealWord p).map) ≤ ENNReal.ofReal (budget p) ∧
    finiteDiamondDistance (actualWord p).map (idealWord p).map ≤ ENNReal.ofReal (budget p/2) ∧
    (∀ (r : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      Matrix.traceNorm (tensorLeft ((actualWord p).map-(idealWord p).map) X) ≤
        budget p * Matrix.traceNorm X) ∧
    (∀ q : List (QuantumChannel D D),
      (run (q++p.map ApproxStep.actual)).map = ((actualWord p).comp (run q)).map) := by
  intro D p hp
  have hn := word_error p hp
  have hb := budget_nonneg p (fun s hs => (hp s hs).1)
  refine ⟨hn, ?_, (finiteDiamondNorm_le_iff_uniform D D _ _ hb).1 hn, ?_⟩
  · unfold finiteDiamondDistance
    calc
      _ ≤ (1/2 : ℝ≥0∞)*ENNReal.ofReal (budget p) := mul_le_mul_right hn _
      _ = _ := by
        rw [show (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2 : ℝ) by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
        congr 1
        ring
  · intro q
    exact run_append q (p.map ApproxStep.actual)

end
end Qatlib.Concepts.RawChannelWord.CptpWordBound
