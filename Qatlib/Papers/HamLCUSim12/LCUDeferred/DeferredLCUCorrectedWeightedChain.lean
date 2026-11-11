/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.DeferredLCUCorrectedFibers

/-!
# Weighted success amplitudes of corrected LCU chains

This module evaluates the all-zero ancilla fiber of corrected positive-weight LCU chains, as
used in the construction of Theorem 3 in [ChildsWiebe2012]. `lcuListWeight` sums the scalar
weights and `lcuListWeighted` sums the weighted system matrices.

`chainGateCorrected_zero_corner` gives the weighted update for one level. Iteration yields
`chainFoldCorrected_zero_corner` and, for a nonempty list of positive weights,
`chainCircuitCorrected_zero_corner`, whose amplitude is the weighted matrix sum applied to the
input and divided by the total weight. These identities do not require normalized input or
unitary payloads.

## Main statements

- `lcuListWeight_nonneg` proves nonnegativity of the total for positive listed weights.
- `chainGateCorrected_zero_corner` evaluates a single weighted update.
- `chainFoldCorrected_zero_corner` includes an initial accumulator with positive weight.
- `chainCircuitCorrected_zero_corner` evaluates the full nonempty chain.

## References

- [Childs and Wiebe, 2012][ChildsWiebe2012], Theorem 3.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The sum of the real weights in a list of ancilla positions and weighted system matrices. -/
def lcuListWeight {k : ℕ} (L : List (Fin k×(ℝ×Matrix I I ℂ))) : ℝ := (L.map fun t=>t.2.1).sum

/-- The sum of each listed system matrix multiplied by its real weight. -/
def lcuListWeighted {k : ℕ} (L : List (Fin k×(ℝ×Matrix I I ℂ))) : Matrix I I ℂ :=
  (L.map fun t=>t.2.1 • t.2.2).sum

omit [Fintype I] [DecidableEq I] in

/-- If every listed weight is positive, the list's total weight is nonnegative, including for
the empty list. -/
theorem lcuListWeight_nonneg {k : ℕ} (L : List (Fin k×(ℝ×Matrix I I ℂ)))
    (hL : ∀ t∈L,0<t.2.1) : 0≤lcuListWeight L := by
  induction L with
  | nil => simp [lcuListWeight]
  | cons t L ih =>
    change 0≤t.2.1+lcuListWeight L
    exact add_nonneg (hL t (List.mem_cons_self)).le
      (ih (fun t ht=>hL t (List.mem_cons_of_mem _ ht)))

omit [DecidableEq I] in

/-- A lifted system matrix applied to zero ancillas and `ψ` has zero ancilla fiber equal to `U
*ᵥ ψ`. -/
theorem liftSys_zero_corner (k : ℕ) (U : Matrix I I ℂ) (ψ : QState I) (x : I) :
    (liftSys k U*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)=(U*ᵥψ) x := by
  rw [mask_zero_corner]
  simp only [liftSys,Matrix.of_apply]
  rfl

/-- For positive `W` and `w`, the corrected chain level's zero ancilla amplitude is `W / (W +
w)` times the accumulator's zero fiber plus `w / (W + w)` times `U *ᵥ ψ`. -/
theorem chainGateCorrected_zero_corner {k : ℕ} (bit : Fin k) (W w : ℝ) (hW : 0<W) (hw : 0<w)
    (acc : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) (U : Matrix I I ℂ)
    (ψ : QState I) (x : I) :
    (chainGateCorrected k bit W w acc U*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)=
      ((W:ℂ)/(W+w))*(acc*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)+
      ((w:ℂ)/(W+w))*(U*ᵥψ) x := by
  unfold chainGateCorrected
  rw [lcuLevelGateCorrected_zero_corner bit (W/w) (div_nonneg hW.le hw.le) acc (liftSys k U)
    (independentLCUBit_liftSys bit U),liftSys_zero_corner]
  have hκ : (W/w)/(W/w+1)=W/(W+w) := by field_simp
  have hκ' : (1:ℝ)/(W/w+1)=w/(W+w) := by field_simp
  have hc : (((W/w:ℝ):ℂ))/(((W/w:ℝ):ℂ)+1)=(W:ℂ)/(W+w) := by exact_mod_cast hκ
  have hc' : (1:ℂ)/(((W/w:ℝ):ℂ)+1)=(w:ℂ)/(W+w) := by exact_mod_cast hκ'
  rw [hc,hc']

/-- With positive initial and listed weights, the corrected fold's zero ancilla amplitude is the
initial fiber multiplied by `W`, plus the listed weighted matrix sum applied to `ψ`, all
divided by `W + lcuListWeight L`. -/
theorem chainFoldCorrected_zero_corner {k : ℕ} (L : List (Fin k×(ℝ×Matrix I I ℂ)))
    (W : ℝ) (hW : 0<W) (acc : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (hL : ∀ t∈L,0<t.2.1) (ψ : QState I) (x : I) :
    (chainFoldCorrected k W acc L*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)=
      ((W:ℂ)*(acc*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)+
        (lcuListWeighted L*ᵥψ) x)/((W+lcuListWeight L:ℝ):ℂ) := by
  induction L generalizing W acc with
  | nil =>
    have hWC : (W:ℂ)≠0 := by exact_mod_cast hW.ne'
    simp [chainFoldCorrected,lcuListWeight,lcuListWeighted,hWC]
  | cons t L ih =>
    rcases t with ⟨bit,w,U⟩
    have hw : 0<w := hL _ (List.mem_cons_self)
    have hL' : ∀ t∈L,0<t.2.1 := fun t ht=>hL t (List.mem_cons_of_mem _ ht)
    rw [chainFoldCorrected,ih (W+w) (by linarith) (chainGateCorrected k bit W w acc U) hL',
      chainGateCorrected_zero_corner bit W w hW hw]
    have hc : ((W+w:ℝ):ℂ)≠0 := by exact_mod_cast (show W+w≠0 by linarith)
    have hs : ((W+w+lcuListWeight L:ℝ):ℂ)≠0 := by
      exact_mod_cast (ne_of_gt (by linarith [lcuListWeight_nonneg L hL'] : 0<W+w+lcuListWeight L))
    simp only [lcuListWeight,lcuListWeighted,List.map_cons,List.sum_cons,Matrix.add_mulVec,
      Matrix.smul_mulVec,Pi.add_apply,Pi.smul_apply,Complex.real_smul]
    push_cast at hc hs ⊢
    simp only [lcuListWeight] at hs
    ring_nf at hc hs ⊢
    field_simp [hc,hs]; ring

/-- For a nonempty positive-weight list, the corrected chain's zero ancilla amplitude equals
`lcuListWeighted L` applied to `ψ` and divided by `lcuListWeight L`. This exact weighted-sum
identity is the chain step in the construction associated with Theorem 3 of
[ChildsWiebe2012]. -/
theorem chainCircuitCorrected_zero_corner {k : ℕ} (L : List (Fin k×(ℝ×Matrix I I ℂ)))
    (hne : L≠[]) (hL : ∀ t∈L,0<t.2.1) (ψ : QState I) (x : I) :
    (chainCircuitCorrected k L*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)=
      (lcuListWeighted L*ᵥψ) x/(lcuListWeight L:ℂ) := by
  cases L with
  | nil => exact False.elim (hne rfl)
  | cons t L =>
    rcases t with ⟨bit,w,U⟩
    rw [chainCircuitCorrected,chainFoldCorrected_zero_corner L w (hL _ (List.mem_cons_self))
      (liftSys k U) (fun t ht=>hL t (List.mem_cons_of_mem _ ht)),liftSys_zero_corner]
    simp only [lcuListWeight,lcuListWeighted,List.map_cons,List.sum_cons,Matrix.add_mulVec,
      Matrix.smul_mulVec,Pi.add_apply,Pi.smul_apply,Complex.real_smul]
end Qatlib.Papers.HamLCUSim12.LCUDeferred
