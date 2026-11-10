/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.CountGateMergers
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl
open Matrix
open scoped Classical BigOperators

theorem sourcePrefixLayout_mono {N : ℕ} {c w : ℕ → Fin N} {r s : ℕ}
    (h : noWorkDirtyPrefixLayout c w r) (hs : s ≤ r) : noWorkDirtyPrefixLayout c w s := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj he
    exact h.1 (by change i < r+1; change i < s+1 at hi; omega)
      (by change j < r+1; change j < s+1 at hj; omega) he
  · intro i hi j hj he
    exact h.2.1 (by change i < r; change i < s at hi; omega)
      (by change j < r; change j < s at hj; omega) he
  · intro i hi j hj
    exact h.2.2 i (by omega) j (by omega)

def sourceRelativeSign {N : ℕ} (a b t : Fin N) (x : Reg N) : ℂ :=
  if x a && !x b && x t then -1 else 1

theorem sourceRelativeSign_sq {N : ℕ} (a b t : Fin N) (x : Reg N) :
    sourceRelativeSign a b t x * sourceRelativeSign a b t x = 1 := by
  unfold sourceRelativeSign
  split <;> norm_num

def sourcePrefixRaw {N : ℕ} (c w : ℕ → Fin N) : ℕ → List (ReflectionGate N)
  | 0 => []
  | 1 => sourceRelativeToffoliSteps (c 0) (c 1) (w 0)
  | r+2 => sourceRelativeToffoliSteps (c (r+2)) (w r) (w (r+1)) ++
      sourcePrefixRaw c w (r+1) ++
      sourceRelativeToffoliSteps (c (r+2)) (w r) (w (r+1))

def sourcePrefixSign {N : ℕ} (c w : ℕ → Fin N) : ℕ → Reg N → ℂ
  | 0, _ => 1
  | 1, x => sourceRelativeSign (c 0) (c 1) (w 0) x
  | r+2, x =>
      let q := noWorkToffoliUpdate (c (r+2)) (w r) (w (r+1)) x
      sourceRelativeSign (c (r+2)) (w r) (w (r+1)) x *
        sourcePrefixSign c w (r+1) q *
        sourceRelativeSign (c (r+2)) (w r) (w (r+1))
          (noWorkDirtyPrefixTransform c w (r+1) q)

theorem sourcePrefixRaw_legal {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) : reflectionLegal (sourcePrefixRaw c w r) := by
  induction r using Nat.twoStepInduction with
  | zero => simp [sourcePrefixRaw, reflectionLegal]
  | one =>
    exact sourceRelativeToffoliSteps_legal _ _ _
      (h.2.2 0 (by omega) 0 (by omega)) (h.2.2 1 (by omega) 0 (by omega))
  | more r _ ih =>
    have hg := sourceRelativeToffoliSteps_legal (c (r+2)) (w r) (w (r+1))
      (h.2.2 _ (by omega) _ (by omega))
      (fun he => by have hv := h.2.1 (by simp) (by simp) he; omega)
    simp only [sourcePrefixRaw, reflectionLegal_append]
    exact ⟨⟨hg, ih (sourcePrefixLayout_mono h (by omega))⟩, hg⟩

theorem sourcePrefixRaw_ket {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (sourcePrefixRaw c w r))
      (Qatlib.Foundations.PureStateMath.Ket x) = sourcePrefixSign c w r x • Qatlib.Foundations.PureStateMath.Ket (noWorkDirtyPrefixTransform c w r x) := by
  induction r using Nat.twoStepInduction generalizing x with
  | zero => simp [sourcePrefixRaw, sourcePrefixSign, noWorkDirtyPrefixTransform, reflectionCompile]
  | one =>
    exact sourceRelativeToffoliSteps_ket _ _ _
      (h.2.2 0 (by omega) 0 (by omega)) (h.2.2 1 (by omega) 0 (by omega)) x
  | more r _ ih =>
    have hwt : w r ≠ w (r+1) := fun he => by
      have hv := h.2.1 (by simp) (by simp) he
      omega
    have hg (y : Reg N) :
        Run (1 : Matrix (Reg N) (Reg N) ℂ)
          (reflectionCompile (sourceRelativeToffoliSteps (c (r+2)) (w r) (w (r+1))))
          (Qatlib.Foundations.PureStateMath.Ket y) = sourceRelativeSign (c (r+2)) (w r) (w (r+1)) y •
            Qatlib.Foundations.PureStateMath.Ket (noWorkToffoliUpdate (c (r+2)) (w r) (w (r+1)) y) :=
      sourceRelativeToffoliSteps_ket _ _ _ (h.2.2 _ (by omega) _ (by omega)) hwt y
    simp only [sourcePrefixRaw, reflectionCompile_append, run_append]
    rw [hg]
    simp only [source_run_smul]
    rw [ih (sourcePrefixLayout_mono h (by omega))]
    simp only [source_run_smul]
    rw [hg]
    simp only [sourcePrefixSign, noWorkDirtyPrefixTransform, smul_smul, mul_assoc]

theorem sourcePrefixSign_sq {N : ℕ} (c w : ℕ → Fin N) (r : ℕ) (x : Reg N) :
    sourcePrefixSign c w r x * sourcePrefixSign c w r x = 1 := by
  induction r using Nat.twoStepInduction generalizing x with
  | zero => simp [sourcePrefixSign]
  | one => exact sourceRelativeSign_sq _ _ _ _
  | more r _ ih =>
    dsimp only [sourcePrefixSign]
    rw [show ∀ a b d : ℂ, (a*b*d)*(a*b*d) = (a*a)*(b*b)*(d*d) from fun a b d => by ring]
    rw [sourceRelativeSign_sq, ih, sourceRelativeSign_sq]
    norm_num

private theorem relativeSign_update {N : ℕ} (a b z t : Fin N)
    (hat : a ≠ t) (hbt : b ≠ t) (hzt : z ≠ t) (x : Reg N) (v : Bool) :
    sourceRelativeSign a b z (Function.update x t v) = sourceRelativeSign a b z x := by
  simp only [sourceRelativeSign, Function.update_of_ne hat, Function.update_of_ne hbt,
    Function.update_of_ne hzt]

theorem sourceToffoliUpdate_update {N : ℕ} (a b z t : Fin N)
    (hat : a ≠ t) (hbt : b ≠ t) (hzt : z ≠ t) (x : Reg N) (v : Bool) :
    noWorkToffoliUpdate a b z (Function.update x t v) =
      Function.update (noWorkToffoliUpdate a b z x) t v := by
  simp only [noWorkToffoliUpdate, Function.update_of_ne hat, Function.update_of_ne hbt,
    Function.update_of_ne hzt]
  exact (Function.update_comm hzt _ _ x).symm

theorem sourcePrefixSign_update {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) (t : Fin N)
    (hc : ∀ i < r+1, c i ≠ t) (hw : ∀ j < r, w j ≠ t)
    (x : Reg N) (v : Bool) :
    sourcePrefixSign c w r (Function.update x t v) = sourcePrefixSign c w r x := by
  induction r using Nat.twoStepInduction generalizing x with
  | zero => rfl
  | one => exact relativeSign_update _ _ _ _ (hc 0 (by omega)) (hc 1 (by omega)) (hw 0 (by omega)) x v
  | more r _ ih =>
    have hsub := sourcePrefixLayout_mono h (show r+1 ≤ r+2 from by omega)
    have hct : ∀ i < r+2, c i ≠ t := fun i hi => hc i (by omega)
    have hwt : ∀ j < r+1, w j ≠ t := fun j hj => hw j (by omega)
    dsimp only [sourcePrefixSign]
    rw [relativeSign_update _ _ _ _ (hc _ (by omega)) (hw _ (by omega)) (hw _ (by omega)),
      sourceToffoliUpdate_update _ _ _ _ (hc _ (by omega)) (hw _ (by omega)) (hw _ (by omega)),
      ih hsub hct hwt,
      noWorkDirtyPrefixTransform_update c w (r+1) hsub t hct hwt,
      relativeSign_update _ _ _ _ (hc _ (by omega)) (hw _ (by omega)) (hw _ (by omega))]

end Qatlib.Concepts.CircuitImpl.MultiControl
