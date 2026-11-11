/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.CountCompressedLadders
import Qatlib.Concepts.CircuitImpl.MultiControl.CountToffoliFrames

/-!
# Borrowed-work conjunction words and relative signs

`sourceBorrowedExact` and `sourceBorrowedRelative` combine a compressed dirty-prefix ladder with
framed exact or relative Toffoli words. Their basis-state theorems implement a
conjunction-controlled target toggle under explicit layout and wire-separation hypotheses,
supporting the multi-control decompositions of [BarencoEtAl1995].

The relative construction carries the explicit sign `sourceBorrowedSign`, whose square is one.
The module also proves legality and avoidance of unused wires.

## Main statements

* `sourceBorrowedExact_ket`: Exact conjunction-toggle action on basis states.
* `sourceBorrowedRelative_ket`: Conjunction-toggle action with its accumulated sign.
* `sourceBorrowedSign_sq`: The accumulated sign squares to one.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl.CountCompressedLadders
open Qatlib.Concepts.CircuitImpl.MultiControl.CountToffoliFrames
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl
open Matrix
open scoped Classical BigOperators

/-- The exact borrowed-work word alternating a framed Toffoli, the compressed prefix ladder, the
adjoint framed Toffoli, and the same ladder. -/
def sourceBorrowedExact {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) : List (ReflectionGate N) :=
  let g := sourceToffoliFramed (c (r+1)) (w (r-1)) t;
  let F := sourcePrefixCompressed c w r;
  g ++ F ++ reflectionAdjoint g ++ F

/-- The relative borrowed-work word formed by two repetitions of a relative Toffoli followed by
the compressed prefix ladder. -/
def sourceBorrowedRelative {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) : List (ReflectionGate N) :=
  let g := sourceRelativeToffoliSteps (c (r+1)) (w (r-1)) t;
  let F := sourcePrefixCompressed c w r;
  g ++ F ++ g ++ F

/-- The product of the four relative signs accumulated along the basis-state path of
`sourceBorrowedRelative`. -/
def sourceBorrowedSign {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) (x : Reg N) : ℂ :=
  let a := c (r+1);
  let b := w (r-1);
  let q := noWorkToffoliUpdate a b t x;
  let y := noWorkDirtyPrefixTransform c w r q;
  sourceRelativeSign a b t x * sourcePrefixSign c w r q *
    sourceRelativeSign a b t y * sourcePrefixSign c w r (noWorkToffoliUpdate a b t y)

/-- Under the dirty-prefix layout and wire separation hypotheses, the alternating pair of
Toffoli updates and prefix transforms toggles only the target by the conjunction of the
first `r + 2` controls. -/
private theorem old_boolean_result {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ)
    (hr : 1 ≤ r) (h : noWorkDirtyPrefixLayout c w r)
    (hlast : ∀ j < r, c (r+1) ≠ w j)
    (hc : ∀ i < r+2, c i ≠ t) (hw : ∀ j < r, w j ≠ t) (x : Reg N) :
    Ket (noWorkDirtyPrefixTransform c w r
      (noWorkToffoliUpdate (c (r+1)) (w (r-1)) t
        (noWorkDirtyPrefixTransform c w r (noWorkToffoliUpdate (c (r+1)) (w (r-1)) t x)))) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) (r+2))) := by
  have ht (y : Reg N) : Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (toffoliLocalSteps (c (r+1)) (w (r-1)) t)) (Qatlib.Foundations.PureStateMath.Ket y) =
      Qatlib.Foundations.PureStateMath.Ket (noWorkToffoliUpdate (c (r+1)) (w (r-1)) t y) :=
    (local_toffoli_fifteen_exact N _ _ _ (hlast _ (by omega)) (hc _ (by omega)) (hw _ (by omega))).2.2 y
  have hb := noWorkBorrowedAndSteps_ket c w t r hr h hlast hc hw x
  simp only [noWorkBorrowedAndSteps, reflectionCompile_append, run_append] at hb
  rw [ht, noWorkDirtyPrefixSteps_ket c w r h, ht, noWorkDirtyPrefixSteps_ket c w r h] at hb
  exact hb

/-- For a valid dirty-prefix layout with the stated wire separations, the exact borrowed-work
word toggles the target by the conjunction of `r + 2` control bits and restores every other
bit. -/
theorem sourceBorrowedExact_ket {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ)
    (hr : 1 ≤ r) (h : noWorkDirtyPrefixLayout c w r)
    (hlast : ∀ j < r, c (r+1) ≠ w j)
    (hc : ∀ i < r+2, c i ≠ t) (hw : ∀ j < r, w j ≠ t) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (sourceBorrowedExact c w t r))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) (r+2))) := by
  let a := c (r+1)
  let b := w (r-1)
  let q := noWorkToffoliUpdate a b t x
  let y := noWorkDirtyPrefixTransform c w r q
  have hab : a ≠ b := hlast _ (by omega)
  have hat : a ≠ t := hc _ (by omega)
  have hbt : b ≠ t := hw _ (by omega)
  have hct : ∀ i < r+1, c i ≠ t := fun i hi => hc i (by omega)
  have hq : sourcePrefixSign c w r q = sourcePrefixSign c w r x :=
    sourcePrefixSign_update c w r h t hct hw x _
  have hy : sourcePrefixSign c w r (noWorkToffoliUpdate a b t y) =
      sourcePrefixSign c w r (noWorkDirtyPrefixTransform c w r x) := by
    rw [show noWorkToffoliUpdate a b t y = Function.update y t (y t ^^ (y a && y b)) from rfl,
      sourcePrefixSign_update c w r h t hct hw]
    dsimp only [y, q, noWorkToffoliUpdate]
    rw [noWorkDirtyPrefixTransform_update c w r h t hct hw,
      sourcePrefixSign_update c w r h t hct hw]
  have ht (z : Reg N) := sourceToffoliFramed_ket a b t hab hat hbt z
  have hta (z : Reg N) := sourceToffoliFramed_adjoint_ket a b t hab hat hbt z
  simp only [sourceBorrowedExact, reflectionCompile_append, run_append]
  rw [ht, sourcePrefixCompressed_ket c w r h]
  simp only [source_run_smul]
  rw [hta]
  rw [sourcePrefixCompressed_ket c w r h]
  simp only [smul_smul]
  change (sourcePrefixSign c w r q * sourcePrefixSign c w r (noWorkToffoliUpdate a b t y)) • _ = _
  rw [hq, hy, sourcePrefixSign_return c w r h x, one_smul]
  exact old_boolean_result c w t r hr h hlast hc hw x

/-- For a valid dirty-prefix layout with the stated wire separations, the relative borrowed-work
word performs the conjunction-controlled target toggle with scalar factor
`sourceBorrowedSign`. -/
theorem sourceBorrowedRelative_ket {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ)
    (hr : 1 ≤ r) (h : noWorkDirtyPrefixLayout c w r)
    (hlast : ∀ j < r, c (r+1) ≠ w j)
    (hc : ∀ i < r+2, c i ≠ t) (hw : ∀ j < r, w j ≠ t) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (sourceBorrowedRelative c w t r))
      (Qatlib.Foundations.PureStateMath.Ket x) = sourceBorrowedSign c w t r x •
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) (r+2))) := by
  have ht (z : Reg N) : Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (sourceRelativeToffoliSteps (c (r+1)) (w (r-1)) t)) (Qatlib.Foundations.PureStateMath.Ket z) =
      sourceRelativeSign (c (r+1)) (w (r-1)) t z • Qatlib.Foundations.PureStateMath.Ket (noWorkToffoliUpdate (c (r+1)) (w (r-1)) t z) :=
    sourceRelativeToffoliSteps_ket _ _ _ (hc _ (by omega)) (hw _ (by omega)) z
  simp only [sourceBorrowedRelative, reflectionCompile_append, run_append]
  rw [ht]
  simp only [source_run_smul]
  rw [sourcePrefixCompressed_ket c w r h]
  simp only [source_run_smul]
  rw [ht]
  simp only [source_run_smul]
  rw [sourcePrefixCompressed_ket c w r h]
  simp only [smul_smul]
  rw [old_boolean_result c w t r hr h hlast hc hw x]
  simp only [sourceBorrowedSign, mul_assoc]

/-- The square of the accumulated borrowed-work sign is one. -/
theorem sourceBorrowedSign_sq {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) (x : Reg N) :
    sourceBorrowedSign c w t r x * sourceBorrowedSign c w t r x = 1 := by
  dsimp only [sourceBorrowedSign]
  rw [show ∀ a b d e : ℂ, (a*b*d*e)*(a*b*d*e) = (a*a)*(b*b)*(d*d)*(e*e) from fun a b d e => by ring]
  rw [sourceRelativeSign_sq, sourcePrefixSign_sq, sourceRelativeSign_sq, sourcePrefixSign_sq]
  norm_num

/-- The relative borrowed-work word is legal for a nonempty valid prefix layout whose control
and work wires avoid the target. -/
theorem sourceBorrowedRelative_legal {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ)
    (hr : 1 ≤ r) (h : noWorkDirtyPrefixLayout c w r)
    (hc : ∀ i < r+2, c i ≠ t) (hw : ∀ j < r, w j ≠ t) :
    reflectionLegal (sourceBorrowedRelative c w t r) := by
  have hg := sourceRelativeToffoliSteps_legal (c (r+1)) (w (r-1)) t
    (hc _ (by omega)) (hw _ (by omega))
  have hF := sourcePrefixCompressed_legal c w r h
  simp only [sourceBorrowedRelative, reflectionLegal_append]
  exact ⟨⟨⟨hg,hF⟩,hg⟩,hF⟩

/-- The exact borrowed-work word is legal under the nonempty prefix layout and the stated
control, work, and target separation hypotheses. -/
theorem sourceBorrowedExact_legal {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ)
    (hr : 1 ≤ r) (h : noWorkDirtyPrefixLayout c w r)
    (hlast : ∀ j < r, c (r+1) ≠ w j)
    (hc : ∀ i < r+2, c i ≠ t) (hw : ∀ j < r, w j ≠ t) :
    reflectionLegal (sourceBorrowedExact c w t r) := by
  have hg := sourceToffoliFramed_legal (c (r+1)) (w (r-1)) t
    (hlast _ (by omega)) (hc _ (by omega)) (hw _ (by omega))
  have hF := sourcePrefixCompressed_legal c w r h
  have hga := reflectionAdjoint_legal _ hg
  simp only [sourceBorrowedExact, reflectionLegal_append]
  exact ⟨⟨⟨hg,hF⟩,hga⟩,hF⟩

/-- Every gate of the relative borrowed-work word avoids any wire outside its control wires,
work wires, and target. -/
theorem sourceBorrowedRelative_avoids {N : ℕ} (c w : ℕ → Fin N) (s z : Fin N) (r : ℕ)
    (hr : 1 ≤ r) (hc : ∀ i < r+2, z ≠ c i) (hw : ∀ j < r, z ≠ w j) (hs : z ≠ s) :
    ∀ g ∈ sourceBorrowedRelative c w s r, z ∉ reflectionGateWires g := by
  have hg := sourceRelativeToffoliSteps_avoids (c (r+1)) (w (r-1)) s z
    (hc _ (by omega)) (hw _ (by omega)) hs
  have hF := sourcePrefixCompressed_avoids c w r z (fun i hi => hc i (by omega)) hw
  intro g hm
  simp only [sourceBorrowedRelative, List.mem_append] at hm
  rcases hm with ((hm | hm) | hm) | hm
  · exact hg g hm
  · exact hF g hm
  · exact hg g hm
  · exact hF g hm

end Qatlib.Concepts.CircuitImpl.MultiControl
