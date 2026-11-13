/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.CountBorrowed

/-!
# Cancellation of signs in dirty-work commutators

`source_signed_dirty_combine` proves an exact conjunction-toggle rule for the commutator of two
legal gate words. A signed toggle on the spectator and a second toggle controlled by that
spectator combine with their adjoints to cancel the sign, under explicit invariance and
wire-avoidance hypotheses. This is an algebraic ingredient for the borrowed-work constructions
of [BarencoEtAl1995].

## Main statements

* `source_signed_dirty_combine`: Exact target toggle controlled by `A && B` after sign
  cancellation.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

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

/-- For distinct wires `s` and `t`, a commutator of a signed toggle on `s` and an exact toggle
on `t` controlled by `B` and `s` toggles `t` by `A && B` with no residual sign. This holds
under legality, avoidance of `t` by the first word, invariance of `B` under updates at `s`
and `t`, and the condition `z x * z x = 1`. -/
theorem source_signed_dirty_combine {N : ℕ} (s t : Fin N) (hst : s ≠ t)
    (A B : Reg N → Bool)
    (hb : ∀ (x : Reg N) (v : Bool), B (Function.update x s v) = B x ∧ B (Function.update x t v) = B x)
    (as bs : List (ReflectionGate N)) (has : reflectionLegal as) (hbs : reflectionLegal bs)
    (hav : ∀ g ∈ as, t ∉ reflectionGateWires g) (z : Reg N → ℂ)
    (hz : ∀ x, z x * z x = 1)
    (hrA : ∀ x, Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile as) (Qatlib.Foundations.PureStateMath.Ket x) =
      z x • Qatlib.Foundations.PureStateMath.Ket (Function.update x s (x s ^^ A x)))
    (hrB : ∀ x, Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile bs) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (B x && x s)))) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (as ++ bs ++ reflectionAdjoint as ++ reflectionAdjoint bs)) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (A x && B x))) := by
  let F : Reg N → Reg N := fun y => Function.update y t (y t ^^ (B y && y s))
  have hF : Function.Involutive F := by
    intro y
    funext k
    by_cases hkt : k = t
    · subst k
      simp only [F, Function.update_self, (hb _ _).2, Function.update_of_ne hst,
        Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    · simp only [F, Function.update_of_ne hkt]
  have hrBadj (y : Reg N) :
      Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (reflectionAdjoint bs)) (Qatlib.Foundations.PureStateMath.Ket y) = Qatlib.Foundations.PureStateMath.Ket (F y) :=
    source_adjoint_involutive_action bs hbs F hF hrB y
  let ax := Function.update x s (x s ^^ A x)
  have hax : ax t = x t := Function.update_of_ne hst.symm _ _
  have hrAinv (v : Bool) :
      Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (reflectionAdjoint as))
        (Qatlib.Foundations.PureStateMath.Ket (Function.update ax t v)) = z x • Qatlib.Foundations.PureStateMath.Ket (Function.update x t v) :=
    source_signed_spectator_inverse as has t hav x ax (z x) (hz x) hax (hrA x) v
  simp only [reflectionCompile_append, run_append]
  rw [hrA x]
  simp only [source_run_smul]
  rw [hrB]
  rw [hrAinv]
  simp only [source_run_smul, smul_smul, hz, one_smul]
  rw [hrBadj]
  simp only [F, ax, (hb _ _).1, (hb _ _).2, Function.update_self,
    Function.update_of_ne hst, Function.update_of_ne hst.symm, Function.update_idem]
  congr 1
  funext k
  by_cases hkt : k = t
  · subst k
    simp only [Function.update_self]
    cases A x <;> cases B x <;> cases x s <;> cases x t <;> rfl
  · simp only [Function.update_of_ne hkt]

end Qatlib.Concepts.CircuitImpl.MultiControl
