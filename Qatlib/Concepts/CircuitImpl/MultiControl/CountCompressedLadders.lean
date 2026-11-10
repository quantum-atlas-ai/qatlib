/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.CountLadders
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSimpArgs false
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl.CountCompressedLadders
open Matrix
open scoped Classical BigOperators

def sourceRelativeMiddle {N : ℕ} (a b t : Fin N) : List (ReflectionGate N) :=
  let R := qubitEulerRotation (-Real.pi/4);
  [.inr (b,t), .inl (t,R), .inr (a,t), .inl (t,Rᴴ), .inr (b,t)]

theorem sourceRelativeMiddle_legal {N : ℕ} (a b t : Fin N)
    (hat : a ≠ t) (hbt : b ≠ t) : reflectionLegal (sourceRelativeMiddle a b t) := by
  intro g hg
  simp only [sourceRelativeMiddle, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact hbt
  · exact qubitEulerRotation_unitary _
  · exact hat
  · rw [qubitEulerRotation_conjTranspose]; exact qubitEulerRotation_unitary _
  · exact hbt

theorem sourceRelativeToffoliSteps_avoids {N : ℕ} (a b t z : Fin N)
    (hza : z ≠ a) (hzb : z ≠ b) (hzt : z ≠ t) :
    ∀ g ∈ sourceRelativeToffoliSteps a b t, z ∉ reflectionGateWires g := by
  intro g hg
  simp only [sourceRelativeToffoliSteps, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [reflectionGateWires, hza, hzb, hzt]

theorem sourcePrefixRaw_avoids {N : ℕ} (c w : ℕ → Fin N) (r : ℕ) (z : Fin N)
    (hc : ∀ i < r+1, z ≠ c i) (hw : ∀ j < r, z ≠ w j) :
    ∀ g ∈ sourcePrefixRaw c w r, z ∉ reflectionGateWires g := by
  induction r using Nat.twoStepInduction with
  | zero => simp [sourcePrefixRaw]
  | one =>
    exact sourceRelativeToffoliSteps_avoids _ _ _ _
      (hc 0 (by omega)) (hc 1 (by omega)) (hw 0 (by omega))
  | more r _ ih =>
    intro g hg
    simp only [sourcePrefixRaw, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact sourceRelativeToffoliSteps_avoids _ _ _ _ (hc _ (by omega)) (hw _ (by omega))
        (hw _ (by omega)) g hg
    · exact ih (fun i hi => hc i (by omega)) (fun j hj => hw j (by omega)) g hg
    · exact sourceRelativeToffoliSteps_avoids _ _ _ _ (hc _ (by omega)) (hw _ (by omega))
        (hw _ (by omega)) g hg

def sourcePrefixCompressed {N : ℕ} (c w : ℕ → Fin N) : ℕ → List (ReflectionGate N)
  | 0 => []
  | 1 => sourceRelativeToffoliSteps (c 0) (c 1) (w 0)
  | r+2 =>
      let R := qubitEulerRotation (-Real.pi/4);
      [.inl (w (r+1),R)] ++ sourceRelativeMiddle (c (r+2)) (w r) (w (r+1)) ++
        sourcePrefixCompressed c w (r+1) ++ sourceRelativeMiddle (c (r+2)) (w r) (w (r+1)) ++
        [.inl (w (r+1),Rᴴ)]

theorem sourcePrefixCompressed_length {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (hr : 1 ≤ r) : (sourcePrefixCompressed c w r).length = 12*r-5 := by
  induction r using Nat.twoStepInduction with
  | zero => omega
  | one => rfl
  | more r _ ih =>
    simp only [sourcePrefixCompressed, List.length_append, List.length_singleton]
    have hm : (sourceRelativeMiddle (c (r+2)) (w r) (w (r+1))).length = 5 := rfl
    rw [hm, ih (by omega)]
    omega

private theorem singleton_matrix {N : ℕ} (g : ReflectionGate N) :
    reflectionProgramMatrix [g] = reflectionGateMatrix g := by simp [reflectionProgramMatrix]

theorem sourcePrefixCompressed_matrix {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) :
    reflectionProgramMatrix (sourcePrefixCompressed c w r) =
      reflectionProgramMatrix (sourcePrefixRaw c w r) := by
  induction r using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more r _ ih =>
    have hsub : noWorkDirtyPrefixLayout c w (r+1) := by
      refine ⟨?_, ?_, ?_⟩
      · intro i hi j hj he
        exact h.1 (by change i < r+3; change i < r+2 at hi; omega)
          (by change j < r+3; change j < r+2 at hj; omega) he
      · intro i hi j hj he
        exact h.2.1 (by change i < r+2; change i < r+1 at hi; omega)
          (by change j < r+2; change j < r+1 at hj; omega) he
      · intro i hi j hj
        exact h.2.2 i (by omega) j (by omega)
    let R : Matrix (Reg N) (Reg N) ℂ := wireGate N (w (r+1)) (qubitEulerRotation (-Real.pi/4))
    let S : Matrix (Reg N) (Reg N) ℂ := wireGate N (w (r+1)) ((qubitEulerRotation (-Real.pi/4))ᴴ)
    let K := reflectionProgramMatrix (sourceRelativeMiddle (c (r+2)) (w r) (w (r+1)))
    let F := reflectionProgramMatrix (sourcePrefixRaw c w (r+1))
    let G := reflectionProgramMatrix (sourceRelativeToffoliSteps (c (r+2)) (w r) (w (r+1)))
    have hRS : R*S=1 := by
      dsimp only [R,S]
      rw [wireGate_mul]
      have hu : qubitEulerRotation (-Real.pi/4) * (qubitEulerRotation (-Real.pi/4))ᴴ = 1 := by
        simpa only [Matrix.star_eq_conjTranspose] using!
          Matrix.mem_unitaryGroup_iff.mp (qubitEulerRotation_unitary (-Real.pi/4))
      rw [hu, wireGate_one]
    have hav : ∀ g ∈ sourcePrefixRaw c w (r+1), w (r+1) ∉ reflectionGateWires g :=
      sourcePrefixRaw_avoids c w (r+1) (w (r+1))
        (fun i hi => (h.2.2 i (by omega) (r+1) (by omega)).symm)
        (fun j hj he => by have hv := h.2.1 (by simp) (by change j < r+2; omega) he; omega)
    have hcomm : R*F=F*R := source_wireGate_commute_table (w (r+1)) (qubitEulerRotation (-Real.pi/4))
      (sourcePrefixRaw c w (r+1)) (sourcePrefixRaw_legal c w _ hsub) hav
    have hRF (D : Matrix (Reg N) (Reg N) ℂ) : R*(F*(S*D)) = F*D := by
      rw [← Matrix.mul_assoc R F (S*D), hcomm, Matrix.mul_assoc F R (S*D),
        ← Matrix.mul_assoc R S D, hRS, Matrix.one_mul]
    have hG : G = S*(K*R) := by
      have hs : sourceRelativeToffoliSteps (c (r+2)) (w r) (w (r+1)) =
          [.inl (w (r+1),qubitEulerRotation (-Real.pi/4))] ++
            sourceRelativeMiddle (c (r+2)) (w r) (w (r+1)) ++
          [.inl (w (r+1),(qubitEulerRotation (-Real.pi/4))ᴴ)] := rfl
      dsimp only [G]
      rw [hs]
      simp only [reflectionProgramMatrix_append, singleton_matrix, reflectionGateMatrix,
          Matrix.mul_assoc]
      rfl
    have hC : reflectionProgramMatrix (sourcePrefixCompressed c w (r+2)) =
        S*(K*(reflectionProgramMatrix (sourcePrefixCompressed c w (r+1))*(K*R))) := by
      rw [sourcePrefixCompressed]
      simp only [reflectionProgramMatrix_append, singleton_matrix, reflectionGateMatrix,
          Matrix.mul_assoc]
      rfl
    have hraw : reflectionProgramMatrix (sourcePrefixRaw c w (r+2)) = G*(F*G) := by
      rw [sourcePrefixRaw]
      simp only [reflectionProgramMatrix_append, Matrix.mul_assoc]
      rfl
    rw [hC, hraw, ih hsub, hG]
    simp only [Matrix.mul_assoc, hRF]
    rfl

theorem sourcePrefixCompressed_legal {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) : reflectionLegal (sourcePrefixCompressed c w r) := by
  induction r using Nat.twoStepInduction with
  | zero => simp [sourcePrefixCompressed, reflectionLegal]
  | one =>
    exact sourceRelativeToffoliSteps_legal _ _ _
      (h.2.2 0 (by omega) 0 (by omega)) (h.2.2 1 (by omega) 0 (by omega))
  | more r _ ih =>
    have hm := sourceRelativeMiddle_legal (c (r+2)) (w r) (w (r+1))
      (h.2.2 _ (by omega) _ (by omega))
      (fun he => by have hv := h.2.1 (by simp) (by simp) he; omega)
    have hR : reflectionLegal [.inl (w (r+1),qubitEulerRotation (-Real.pi/4))] := by
      simpa [reflectionLegal, reflectionGateLegal] using! qubitEulerRotation_unitary (-Real.pi/4)
    have hS : reflectionLegal [.inl (w (r+1),(qubitEulerRotation (-Real.pi/4))ᴴ)] := by
      simp only [qubitEulerRotation_conjTranspose]
      simpa [reflectionLegal, reflectionGateLegal] using! qubitEulerRotation_unitary (-(-Real.pi/4))
    have hF := ih (sourcePrefixLayout_mono h (by omega))
    simp only [sourcePrefixCompressed, reflectionLegal_append]
    exact ⟨⟨⟨⟨hR, hm⟩, hF⟩, hm⟩, hS⟩

theorem sourcePrefixCompressed_ket {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (sourcePrefixCompressed c w r))
      (Qatlib.Foundations.PureStateMath.Ket x) = sourcePrefixSign c w r x • Qatlib.Foundations.PureStateMath.Ket (noWorkDirtyPrefixTransform c w r x) := by
  rw [run_reflectionCompile, sourcePrefixCompressed_matrix c w r h, ← run_reflectionCompile]
  exact sourcePrefixRaw_ket c w r h x

theorem sourcePrefixRaw_hermitian {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) :
    (reflectionProgramMatrix (sourcePrefixRaw c w r))ᴴ = reflectionProgramMatrix (sourcePrefixRaw c w r) := by
  induction r using Nat.twoStepInduction with
  | zero => simp [sourcePrefixRaw, reflectionProgramMatrix]
  | one =>
    rw [show sourcePrefixRaw c w 1 = sourceRelativeToffoliSteps (c 0) (c 1) (w 0) from rfl,
      ← reflectionAdjoint_matrix (sourceRelativeToffoliSteps (c 0) (c 1) (w 0))
        (sourceRelativeToffoliSteps_legal _ _ _ (h.2.2 0 (by omega) 0 (by omega))
          (h.2.2 1 (by omega) 0 (by omega))), sourceRelativeToffoliSteps_adjoint]
  | more r _ ih =>
    have hsub := sourcePrefixLayout_mono h (show r+1 ≤ r+2 from by omega)
    let g := sourceRelativeToffoliSteps (c (r+2)) (w r) (w (r+1))
    have hg : reflectionLegal g := sourceRelativeToffoliSteps_legal _ _ _
      (h.2.2 _ (by omega) _ (by omega))
      (fun he => by have hv := h.2.1 (by simp) (by simp) he; omega)
    have hG : (reflectionProgramMatrix g)ᴴ = reflectionProgramMatrix g := by
      rw [← reflectionAdjoint_matrix g hg]
      change reflectionProgramMatrix (reflectionAdjoint (sourceRelativeToffoliSteps _ _ _)) = _
      rw [sourceRelativeToffoliSteps_adjoint]
    have heq : reflectionProgramMatrix (sourcePrefixRaw c w (r+2)) =
        reflectionProgramMatrix g * (reflectionProgramMatrix (sourcePrefixRaw c w (r+1))*reflectionProgramMatrix g) := by
      rw [sourcePrefixRaw]
      simp only [reflectionProgramMatrix_append, Matrix.mul_assoc]
      rfl
    rw [heq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG, ih hsub]
    simp only [Matrix.mul_assoc]

theorem sourcePrefixCompressed_square {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) :
    reflectionProgramMatrix (sourcePrefixCompressed c w r) *
      reflectionProgramMatrix (sourcePrefixCompressed c w r) = 1 := by
  rw [sourcePrefixCompressed_matrix c w r h]
  have hu : (reflectionProgramMatrix (sourcePrefixRaw c w r))ᴴ *
      reflectionProgramMatrix (sourcePrefixRaw c w r) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using!
      Matrix.mem_unitaryGroup_iff'.mp (reflectionProgramMatrix_unitary _ (sourcePrefixRaw_legal c w r h))
  rwa [sourcePrefixRaw_hermitian c w r h] at hu

theorem sourcePrefixCompressed_wire_commute {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) (z : Fin N) (U : Matrix Bool Bool ℂ)
    (hc : ∀ i < r+1, z ≠ c i) (hw : ∀ j < r, z ≠ w j) :
    wireGate N z U * reflectionProgramMatrix (sourcePrefixCompressed c w r) =
      reflectionProgramMatrix (sourcePrefixCompressed c w r) * wireGate N z U := by
  rw [sourcePrefixCompressed_matrix c w r h]
  exact source_wireGate_commute_table z U _ (sourcePrefixRaw_legal c w r h)
    (sourcePrefixRaw_avoids c w r z hc hw)

theorem sourceRelativeMiddle_avoids {N : ℕ} (a b t z : Fin N)
    (hza : z ≠ a) (hzb : z ≠ b) (hzt : z ≠ t) :
    ∀ g ∈ sourceRelativeMiddle a b t, z ∉ reflectionGateWires g := by
  intro g hg
  simp only [sourceRelativeMiddle, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;>
    simp [reflectionGateWires, hza, hzb, hzt]

theorem sourcePrefixCompressed_avoids {N : ℕ} (c w : ℕ → Fin N) (r : ℕ) (z : Fin N)
    (hc : ∀ i < r+1, z ≠ c i) (hw : ∀ j < r, z ≠ w j) :
    ∀ g ∈ sourcePrefixCompressed c w r, z ∉ reflectionGateWires g := by
  induction r using Nat.twoStepInduction with
  | zero => simp [sourcePrefixCompressed]
  | one =>
    exact sourceRelativeToffoliSteps_avoids _ _ _ _ (hc 0 (by omega)) (hc 1 (by omega))
        (hw 0 (by omega))
  | more r _ ih =>
    intro g hg
    simp only [sourcePrefixCompressed, List.mem_append, List.mem_singleton] at hg
    rcases hg with (((rfl | hg) | hg) | hg) | rfl
    · simpa [reflectionGateWires] using! hw (r+1) (by omega)
    · exact sourceRelativeMiddle_avoids _ _ _ _ (hc _ (by omega)) (hw _ (by omega))
        (hw _ (by omega)) g hg
    · exact ih (fun i hi => hc i (by omega)) (fun j hj => hw j (by omega)) g hg
    · exact sourceRelativeMiddle_avoids _ _ _ _ (hc _ (by omega)) (hw _ (by omega))
        (hw _ (by omega)) g hg
    · simpa [reflectionGateWires] using! hw (r+1) (by omega)

theorem sourcePrefixSign_return {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) (x : Reg N) :
    sourcePrefixSign c w r x * sourcePrefixSign c w r (noWorkDirtyPrefixTransform c w r x) = 1 := by
  let M := reflectionProgramMatrix (sourcePrefixRaw c w r)
  have hsquare : M*M=1 := by
    have hu : Mᴴ*M=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using!
        Matrix.mem_unitaryGroup_iff'.mp (reflectionProgramMatrix_unitary _ (sourcePrefixRaw_legal c w r h))
    rwa [sourcePrefixRaw_hermitian c w r h] at hu
  have hact (y : Reg N) : ApplyGate M (Qatlib.Foundations.PureStateMath.Ket y) = sourcePrefixSign c w r y • Qatlib.Foundations.PureStateMath.Ket (noWorkDirtyPrefixTransform c w r y) := by
    rw [show M = reflectionProgramMatrix (sourcePrefixRaw c w r) from rfl, ← run_reflectionCompile]
    exact sourcePrefixRaw_ket c w r h y
  have hi : ApplyGate M (ApplyGate M (Qatlib.Foundations.PureStateMath.Ket x)) = Qatlib.Foundations.PureStateMath.Ket x := by
    rw [← applyGate_mul, hsquare, applyGate_one]
  rw [hact, reflectionApplyGate_smul, hact, smul_smul,
    noWorkDirtyPrefixTransform_involutive c w r h x] at hi
  have he := congrFun hi x
  simpa only [Pi.smul_apply, smul_eq_mul, Qatlib.Foundations.PureStateMath.Ket, if_true,
      mul_one] using! he

end Qatlib.Concepts.CircuitImpl.MultiControl.CountCompressedLadders
