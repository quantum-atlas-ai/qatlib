/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPartit08.MainResults.Defs
import Qatlib.Papers.IsingPartit08.MainResults.ParityCollapse
import Qatlib.Papers.IsingPartit08.MainResults.Containment
import Qatlib.Papers.IsingPartit08.MainResults.GateExpansion
import Qatlib.Papers.IsingPartit08.MainResults.QWGT
import Qatlib.Papers.IsingPartit08.MainResults.Universality
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.IsingPartit08.MainResults

structure AdditiveProblem where

  Inst : Type

  obj : Inst → ℝ

  acc : Inst → ℝ

def HasNumericalEstimate (P : AdditiveProblem) : Prop :=
  ∃ est : P.Inst → ℝ, ∀ x, |est x - P.obj x| ≤ P.acc x

noncomputable def isingAdditiveProblem {R N : ℕ}
    (B : Matrix (Fin N) (Fin N) (ZMod 2)) (CH : Matrix (Fin R) (Fin N) (ZMod 2))
    (lam acc : ℝ) : AdditiveProblem where
  Inst := PUnit
  obj := fun _ => signedEulerianSum B CH lam
  acc := fun _ => acc

theorem containment_problem {R N : ℕ} {B : Matrix (Fin N) (Fin N) (ZMod 2)}
    {CH : Matrix (Fin R) (Fin N) (ZMod 2)} {lam q normalizer ptest m : ℝ}
    (hN : 0 < normalizer)
    (hmaster : MasterCorrespondence q normalizer (signedEulerianSum B CH lam))
    (hm : HadamardTestEstimate q ptest m) :
    HasNumericalEstimate (isingAdditiveProblem B CH lam (normalizer * ptest)) := by
  refine ⟨fun _ => normalizer * m, ?_⟩
  intro x
  simpa [isingAdditiveProblem] using containment_additive hN hmaster hm

theorem containment_problem_normalizer {R N : ℕ}
    {B : Matrix (Fin N) (Fin N) (ZMod 2)} {CH : Matrix (Fin R) (Fin N) (ZMod 2)}
    {lam q ptest m : ℝ} (edges : ℕ)
    (hmaster : MasterCorrespondence q (normalizerOf lam edges)
      (signedEulerianSum B CH lam))
    (hm : HadamardTestEstimate q ptest m) :
    HasNumericalEstimate
      (isingAdditiveProblem B CH lam (normalizerOf lam edges * ptest)) := by
  refine ⟨fun _ => normalizerOf lam edges * m, ?_⟩
  intro x
  simpa [isingAdditiveProblem] using
    containment_additive_normalizer lam edges hmaster hm

end Qatlib.Papers.IsingPartit08.MainResults
