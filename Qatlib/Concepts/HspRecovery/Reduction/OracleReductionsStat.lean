/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.Reductions

/-!
# Statement of oracle promise reductions

`SourceOracleReductions` collects five implications between hidden shift, abelian reflection,
dihedral reflection hiding, and Simon promises. The statement includes the doubling condition
for constructing an injective hidden shift pair and the exponent-two alternative.

These are oracle promise transformations in the setting of [Kuperberg2005].

## Main statements

* `SourceOracleReductions`: packages the five reductions as a conjunction.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore

/-- The conjunction of five oracle promise reductions between hidden shifts, abelian
reflections, dihedral reflection hiding, and Simon promises, with the stated doubling
hypotheses. -/
def SourceOracleReductions : Prop := by
  classical
  exact
  (∀ (A S : Type) [AddCommGroup A] (f g : A → S) (s : A),
    HiddenShift f g s → AbelianReflectionHides (shiftToDihedralOracle f g) s) ∧
  (∀ (A S : Type) [AddCommGroup A] (f g : A → S) (s : A),
    HiddenShift f g s → AbelianReflection (shiftToReflectionOracle f g) s) ∧
  (∀ (A S : Type) [AddCommGroup A] (h : A → S) (s v : A),
    AbelianReflection h s → v + v ≠ 0 →
      HiddenShift (reflectionToShiftLeft h v) (reflectionToShiftRight h v) s) ∧
  (∀ (A S : Type) [AddCommGroup A] (h : A → S) (s : A),
    AbelianReflection h s → (∀ v : A, v + v = 0) → SimonShiftPromise h s) ∧
  (∀ (A S : Type) [AddCommGroup A] (h : AbelianDihedralReg A → S) (s : A),
    AbelianReflectionHides h s →
      HiddenShift (fun a => h (a, false)) (fun a => h (a, true)) s)

end Qatlib.Concepts.HspRecovery.ReductionCore
