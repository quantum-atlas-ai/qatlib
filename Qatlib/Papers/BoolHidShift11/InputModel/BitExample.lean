/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolHidShift11.InputModel.SupportMath

@[expose] public section


/-! # An actual aperiodic input with positive minimum influence

This instance satisfies the full legacy promise nonvacuously. It also keeps
free zero-cost existential records distinct from an executable oracle word.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolHidShift11.InputModel.BitExample
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel
open Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier
open scoped BigOperators

/-- The one-bit identity with the nonzero hidden shift is genuinely aperiodic. -/
def oneInst : BHSPInstance 1 where
  f := fun x => x 0
  g := fun x => !(x 0)
  shift := fun _ => true
  aperiodic := by
    intro t ht
    have hz := ht (ZeroStr 1)
    have h : t 0=false := by simpa [ZeroStr,regXor] using hz.symm
    funext i
    have hi : i=(0:Fin 1) := Subsingleton.elim _ _
    subst i
    exact h
  shifted := by
    intro x
    cases h : x 0 <;> simp [regXor,h]

/-- Every nonzero one-bit direction is the actual all-one register. -/
theorem nonzeroBit (v : Reg 1) (hv : v≠ZeroStr 1) : v 0=true := by
  cases h : v 0 with
  | false =>
    exfalso
    apply hv
    funext i
    have hi : i=(0:Fin 1) := Subsingleton.elim _ _
    subst i
    exact h
  | true => rfl

/-- Its actual uniform flip probability is one in every nonzero direction. -/
theorem oneInfluence (v : Reg 1) (hv : v≠ZeroStr 1) :
    influence (signedFun oneInst.f) v=1 := by
  have ht : ∀ x : Reg 1, (if signedFun oneInst.f x=
      signedFun oneInst.f (regXor x v) then (0:ℝ) else 1)=1 := by
    intro x
    cases h : x 0 <;> norm_num [signedFun,oneInst,regXor,nonzeroBit v hv,h]
  unfold influence
  simp_rw [ht]
  rw [sum_one]
  norm_num [uniformWeight]

/-- The nonzero direction family is nonempty in this positive example. -/
theorem trueNonzero : (fun _ : Fin 1 => true)≠ZeroStr 1 := by
  intro h
  have hh := congrFun h 0
  simp [ZeroStr] at hh

/-- The actual infimum is one, so the old positive-minimum promise is satisfiable. -/
theorem minimumOne : minInfluence (signedFun oneInst.f)=1 := by
  have hs : influence (signedFun oneInst.f) '' {v : Reg 1 | v≠ZeroStr 1}={1} := by
    ext z
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact oneInfluence v hv
    · intro hz
      have hz1 : z=1 := hz
      subst z
      exact ⟨fun _ => true,trueNonzero,oneInfluence _ trueNonzero⟩
  unfold minInfluence
  rw [hs,csInf_singleton]

end Qatlib.Papers.BoolHidShift11.InputModel.BitExample
