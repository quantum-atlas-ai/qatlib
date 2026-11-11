/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Budget
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Diagnostic

set_option backward.isDefEq.respectTransparency false

/-! A necessary same-run link for the existing enumerative legacy backend.

The Frozen program type and all of its old predicates remain unchanged. Its
numeric `bitCost` field is checked here against the explicit primitive model
of this enumerative execution. This link is not a host-bit complexity theorem,
a new polynomial backend, or a lower bound on other recovery algorithms.
The honest baseline certifies its full trace-derived arithmetic/access budget
directly through `CertifiedBudget`, without relabeling it as host bit time.
-/
set_option autoImplicit false

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis

/-- Preserve the legacy total-return convention, including its actual failure default. -/
def returnedPacket (p : List ℚ) (degree : ℕ) (eps : ℚ) : PhaseData :=
  ((produce p degree eps).value).value.getD ⟨gone,[]⟩

/-- Link one legacy packet and claimed numeric budget to the same enumerative execution. -/
def LegacyEnumLinkedAt (model : PriceModel) (program : PhaseRecoveryProgram)
    (input : EffectivePhaseInput) : Prop :=
  program.recover input = returnedPacket input.coeffs input.deg input.tol ∧
    CertifiedBudget model input.coeffs input.deg input.tol
      (produce input.coeffs input.deg input.tol) (program.bitCost input)

/-- The old independent cost fields can still be relabeled without changing the old values. -/
def zeroLegacyCost (program : PhaseRecoveryProgram) : PhaseRecoveryProgram :=
  { program with bitCost := fun _ => 0, costConst := 1, degExp := 0, tolExp := 0 }

/-- This is the old declared numeric polynomial predicate, not execution certification. -/
theorem zeroLegacyCost_poly (program : PhaseRecoveryProgram) :
    (zeroLegacyCost program).PolyBounded := by
  constructor
  · norm_num [zeroLegacyCost]
  · intro input
    simp [zeroLegacyCost]

/-- Relabeling independent costs preserves every old output-correctness premise verbatim. -/
theorem zeroLegacyCost_certified_iff (program : PhaseRecoveryProgram)
    (input : EffectivePhaseInput) :
    (zeroLegacyCost program).CertifiedAt input ↔ program.CertifiedAt input := Iff.rfl

/-- Relabeling independent costs preserves every old actual-word premise verbatim. -/
theorem zeroLegacyCost_word_iff (program : PhaseRecoveryProgram)
    (input : EffectivePhaseInput) :
    (zeroLegacyCost program).WordConnectedAt input ↔ program.WordConnectedAt input := Iff.rfl

/-- The same relabeling cannot pass the new necessary execution link. -/
theorem zeroLegacyCost_not_linked (model : PriceModel) (program : PhaseRecoveryProgram)
    (input : EffectivePhaseInput) :
    ¬ LegacyEnumLinkedAt model (zeroLegacyCost program) input := by
  intro h
  exact no_zero_certified_budget model input.coeffs input.deg input.tol
    (produce input.coeffs input.deg input.tol) h.2

/-- The original linear declared formula cannot pay this actual fixed-degree sign run. -/
theorem sign_declared_formula_not_linked (model : PriceModel)
    (program : PhaseRecoveryProgram) (eps : ℚ) (heps : 0<eps) (hsmall : eps<1)
    (hcost : program.bitCost (signPhaseInput 1 eps) =
      ((signPhaseInput 1 eps).deg+1)*(phaseToleranceBits eps+1)) :
    ¬ LegacyEnumLinkedAt model program (signPhaseInput 1 eps) := by
  intro h
  have hpaid := certifiedBudget_pays_table model (signPhaseInput 1 eps).coeffs
    (signPhaseInput 1 eps).deg (signPhaseInput 1 eps).tol
    (produce (signPhaseInput 1 eps).coeffs (signPhaseInput 1 eps).deg
      (signPhaseInput 1 eps).tol) (program.bitCost (signPhaseInput 1 eps)) h.2
  have hactual := (fixed_sign_fallback_cost eps heps hsmall).2.2
  rw [hcost] at hpaid
  exact (not_le_of_gt hactual) hpaid

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
