/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ParityMbqc.ParityFrames.ParityMbqcDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork

namespace Qatlib.Concepts.ParityMbqc.ParityFrames
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem frame_unitary {n : ℕ} (x z : Reg n) :
    frame x z ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  have h := teleportRelabelGate_mem_unitaryGroup
    (pauliFrameGate_unitary n (x,z)) (bitVecEquiv n).symm
  simpa [pauliFrameGate, frame, pauliFrameGateB, relabelGate,
    Matrix.reindex_apply, Matrix.submatrix_submatrix, Function.comp_def] using! h

theorem frame_mul {n : ℕ} (x z x' z' : Reg n) :
    frame x z * frame x' z' =
      (∏ i, (if z i && x' i then (-1 : ℂ) else 1)) •
        frame (bxor x x') (bxor z z') := by
  have hs (v : Reg n) :
      frameShift (x,z) (frameShift (x',z') v) =
        frameShift (bxor x x', bxor z z') v := by
    funext i
    simp only [frameShift, bxor]
    cases v i <;> cases x i <;> cases x' i <;> rfl
  have hp (v : Reg n) :
      frameSign (x,z) (frameShift (x',z') v) * frameSign (x',z') v =
        (∏ i, (if z i && x' i then (-1 : ℂ) else 1)) *
          frameSign (bxor x x', bxor z z') v := by
    simp only [frameSign, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [frameShift, bxor, frameBitSign]
    have hsign (a b c d : Bool) :
        ((if a && (d ^^ b) then (-1 : ℂ) else 1) *
          (if c && d then (-1 : ℂ) else 1)) =
        (if a && b then (-1 : ℂ) else 1) *
          (if (a ^^ c) && d then (-1 : ℂ) else 1) := by
      cases a <;> cases b <;> cases c <;> cases d <;> norm_num
    exact hsign (z i) (x' i) (z' i) (v i)
  ext w v
  simp only [Matrix.mul_apply, frame, pauliFrameGateB_entry,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (frameShift (x',z') v)]
  · rw [if_pos rfl, hs]
    by_cases hw : w = frameShift (bxor x x', bxor z z') v
    · rw [if_pos hw, if_pos hw, hp]
    · simp [hw]
  · intro u _ hu
    rw [if_neg hu, mul_zero]
  · intro hu
    exact (hu (Finset.mem_univ _)).elim

theorem frame_zero (n : ℕ) : frame (fun _ : Fin n => false) (fun _ => false) = 1 := by
  have hs (v : Reg n) : frameShift (fun _ => false, fun _ => false) v = v := by
    funext i
    simp [frameShift]
  ext w v
  simp [frame, pauliFrameGateB_entry, hs, frameSign, frameBitSign,
    Matrix.one_apply]

theorem frame_square {n : ℕ} (x z : Reg n) :
    frame x z * frame x z =
      (∏ i, (if z i && x i then (-1 : ℂ) else 1)) •
        (1 : Matrix (Reg n) (Reg n) ℂ) := by
  rw [frame_mul]
  have hx : bxor x x = fun _ => false := by funext i; simp [bxor]
  have hz : bxor z z = fun _ => false := by funext i; simp [bxor]
  rw [hx, hz, frame_zero]

theorem g1 :
    (∀ (n : ℕ) (x z : Reg n), frame x z ∈ Matrix.unitaryGroup (Reg n) ℂ) ∧
    (∀ (n : ℕ) (x z x' z' : Reg n),
      frame x z * frame x' z' =
        (∏ i, (if z i && x' i then (-1 : ℂ) else 1)) • frame (bxor x x') (bxor z z')) ∧
    (∀ (n : ℕ) (x z : Reg n), frame x z * frame x z =
      (∏ i, (if z i && x i then (-1 : ℂ) else 1)) •
        (1 : Matrix (Reg n) (Reg n) ℂ)) :=
  ⟨fun _ => frame_unitary, fun _ => frame_mul, fun _ => frame_square⟩

theorem g2 :
    ∀ (n : ℕ) (F : Flow n) (s t : Reg n) (v : Fin n),
      (∀ u, F.rank u < F.rank v → s u = t u) →
      xCorrection F s v = xCorrection F t v ∧
        zCorrection F s v = zCorrection F t v := by
  intro n F s t v h
  constructor
  · unfold xCorrection
    congr 1
    apply List.filterMap_congr
    intro u _
    split_ifs with hu
    · rw [h u (by simpa [hu.2] using! (F.valid u hu.1).2.2.1)]
    · rfl
  · unfold zCorrection
    congr 1
    apply List.filterMap_congr
    intro u _
    split_ifs with hu
    · have hv := (F.valid u hu.1).2.2.2 v hu.2.2
      have hr : F.rank u < F.rank v := hv.resolve_left (Ne.symm hu.2.1)
      rw [h u hr]
    · rfl

theorem bra_eq_gate (θ : ℝ) (s b : Bool) :
    bra θ s b = (Hadamard * Rz (-θ)) s b := by
  rw [Rz, Matrix.mul_diagonal]
  cases s <;> cases b <;>
    simp [bra, Hadamard, div_eq_mul_inv, mul_comm, Complex.ofReal_neg]

noncomputable def braMatrix {m : ℕ} (θ : Fin m → ℝ) : Matrix (Reg m) (Reg m) ℂ :=
  fun s r => ∏ i, bra (θ i) (s i) (r i)

theorem braMatrix_unitary {m : ℕ} (θ : Fin m → ℝ) :
    braMatrix θ ∈ Matrix.unitaryGroup (Reg m) ℂ := by
  let A : Fin m → Operator 2 := fun i =>
    relabelGate boolEquivFin2 (Hadamard * Rz (-θ i))
  have hu (i : Fin m) : A i ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    teleportRelabelGate_mem_unitaryGroup
      ((Matrix.unitaryGroup Bool ℂ).mul_mem hadamard_unitary (rz_unitary _)) _
  have he : braMatrix θ = pauliProductDensity A := by
    ext s r
    simp [braMatrix, pauliProductDensity, A, bra_eq_gate, relabelGate,
      Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [he, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    pauliProductDensity_conjTranspose, pauliProductDensity_mul]
  have hh : (fun i => (A i)ᴴ * A i) = fun _ => (1 : Operator 2) := by
    funext i
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp (hu i)
  rw [hh, pauliProductDensity_one]

def joinEquiv (m o : ℕ) : (Reg m × Reg o) ≃ Reg (m+o) where
  toFun p := join p.1 p.2
  invFun q := (fun i => q ⟨i.val, by omega⟩, fun j => q ⟨m+j.val, by omega⟩)
  left_inv p := by
    apply Prod.ext
    · funext i
      simp [join, i.isLt]
    · funext j
      simp [join, show ¬ (m + j.val < m) from by omega]
  right_inv q := by
    funext i
    simp only [join]
    split_ifs with hi
    · rfl
    · congr 1
      apply Fin.ext
      change m + (i.val - m) = i.val
      omega

theorem g3 :
    ∀ (m o : ℕ) (ψ : QState (Reg (m+o))) (θ : Fin m → ℝ),
      (∑ s : Reg m, ∑ z : Reg o, ‖branch ψ θ s z‖^2) =
        ∑ q : Reg (m+o), ‖ψ q‖^2 := by
  intro m o ψ θ
  rw [Finset.sum_comm]
  calc
    (∑ z : Reg o, ∑ s : Reg m, ‖branch ψ θ s z‖^2) =
        ∑ z : Reg o, ∑ r : Reg m, ‖ψ (join r z)‖^2 := by
      apply Finset.sum_congr rfl
      intro z _
      simpa only [branch, braMatrix, Matrix.mulVec, dotProduct,
        Complex.normSq_eq_norm_sq] using!
        sum_normSq_mulVec_of_mem_unitaryGroup (braMatrix_unitary θ) (fun r => ψ (join r z))
    _ = ∑ q : Reg (m+o), ‖ψ q‖^2 := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ p : Reg m × Reg o, ‖ψ (join p.1 p.2)‖^2 :=
          (Fintype.sum_prod_type _).symm
        _ = _ := Equiv.sum_comp (joinEquiv m o) (fun q => ‖ψ q‖^2)

end Qatlib.Concepts.ParityMbqc.ParityFrames
