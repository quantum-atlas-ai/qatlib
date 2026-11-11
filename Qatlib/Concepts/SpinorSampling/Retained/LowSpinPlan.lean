/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.HighConfidencePlan
import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellPlanExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Low Spin Plan

Low Spin Plan constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open scoped BigOperators
open Matched

/-- Data and invariants for Low Spin Plan Q in the low spin plan model. -/
structure LowSpinPlanQ where
  velocity : HighConfidencePlanQ
  spin : Option BellPlanQ
  copies : ℕ
  targetQueries : ℕ
  deriving Repr

-- Literal low_spin_plan: retain the original current/cross/norm schedules,
/-- erase its signed-Pauli branch and use Bell only when gamma is nonzero. -/
def lowSpinPlanQ (side d M : ℕ) (rootM α β U γ η δ p₀ : ℚ) : LowSpinPlanQ :=
  let old := highConfidencePlanQ d M rootM α β U γ η δ
  let velocity := { old with spin := none, copies := d*(old.current.copies+old.crossRecords) }
  let spin := if γ=0 then none else
    some (bellPlanQ side M p₀ (η/(32*(d : ℚ)*γ)) (δ/(4*(d : ℚ))))
  { velocity := velocity
    spin := spin
    copies := velocity.copies+(match spin with | none => 0 | some q => d*q.copies)
    targetQueries := velocity.targetQueries }

-- The source's other parameters are already checked by its existing entry.
/-- This extra public-mean guard runs even in the gamma=0 branch, as in Python. -/
def checkedLowSpinPlanQ (side d M : ℕ) (rootM α β U γ η δ p₀ : ℚ) : Option LowSpinPlanQ :=
  if 0≤p₀ ∧ p₀≤1/2 then some (lowSpinPlanQ side d M rootM α β U γ η δ p₀) else none

/-- Construction for grid Low Spin Plan Q in the low spin plan model. -/
def gridLowSpinPlanQ (d r : ℕ) (α β U γ η δ p₀ : ℚ) : Option LowSpinPlanQ :=
  checkedLowSpinPlanQ (2^r) d (2^(d*r)) ((2^((d*r+1)/2) : ℕ) : ℚ) α β U γ η δ p₀

/-- Complete original `low_plan_velocity_fields` guarantee for `LowSpinPlan`; all source hypotheses and output obligations are retained. -/
theorem low_plan_velocity_fields (side d M : ℕ) (rootM α β U γ η δ p₀ : ℚ) :
    let p := lowSpinPlanQ side d M rootM α β U γ η δ p₀
    p.velocity.current=(highConfidencePlanQ d M rootM α β U γ η δ).current ∧
    p.velocity.crossRecords=(highConfidencePlanQ d M rootM α β U γ η δ).crossRecords ∧
    p.velocity.norm=(highConfidencePlanQ d M rootM α β U γ η δ).norm ∧
    p.velocity.spin=none ∧
    p.velocity.copies=d*(p.velocity.current.copies+p.velocity.crossRecords) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Complete original `low_plan_zero_spin` guarantee for `LowSpinPlan`; all source hypotheses and output obligations are retained. -/
theorem low_plan_zero_spin (side d M : ℕ) (rootM α β U η δ p₀ : ℚ) :
    (lowSpinPlanQ side d M rootM α β U 0 η δ p₀).spin=none := rfl

/-- Complete original `low_plan_bell_fields` guarantee for `LowSpinPlan`; all source hypotheses and output obligations are retained. -/
theorem low_plan_bell_fields (side d M : ℕ) (rootM α β U γ η δ p₀ : ℚ) (hγ : γ≠0) :
    (lowSpinPlanQ side d M rootM α β U γ η δ p₀).spin=
      some (bellPlanQ side M p₀ (η/(32*(d : ℚ)*γ)) (δ/(4*(d : ℚ)))) := by
  simp only [lowSpinPlanQ,ite_eq_right hγ]

/-- Complete original `low_plan_account_fields` guarantee for `LowSpinPlan`; all source hypotheses and output obligations are retained. -/
theorem low_plan_account_fields (side d M : ℕ) (rootM α β U γ η δ p₀ : ℚ) :
    let p := lowSpinPlanQ side d M rootM α β U γ η δ p₀
    p.copies=p.velocity.copies+(match p.spin with | none => 0 | some q => d*q.copies) ∧
    p.targetQueries=p.velocity.targetQueries := by
  exact ⟨rfl,rfl⟩

variable {S : Type} [DecidableEq S]

-- Direction-dependent carriers retain the actual shifted matching domains.
/-- No Bell data or dummy Pauli records are supplied in the None branch. -/
def LowSpinBellData (S : Type) [DecidableEq S] (d : ℕ) (e : Fin d → Equiv.Perm S)
    (spin : Option BellPlanQ) : Type :=
  match spin with
  | none => Unit
  | some q => (j : Fin d) → Fin q.blocks → CohortObservation q.records q.records (e j)

noncomputable instance [Fintype S] (d : ℕ) (e : Fin d → Equiv.Perm S) (spin : Option BellPlanQ) :
    Fintype (LowSpinBellData S d e spin) := by
  cases spin <;> dsimp only [LowSpinBellData] <;> infer_instance

noncomputable instance (d : ℕ) (e : Fin d → Equiv.Perm S) (spin : Option BellPlanQ) :
    DecidableEq (LowSpinBellData S d e spin) := by
  classical
  cases spin <;> dsimp only [LowSpinBellData] <;> infer_instance

/-- Construction for Low Spin Data in the low spin plan model. -/
def LowSpinData (S : Type) [DecidableEq S] (d : ℕ) (e : Fin d → Equiv.Perm S)
    (p : LowSpinPlanQ) : Type :=
  (Fin d → VelocityData S p.velocity.current p.velocity.crossRecords p.velocity.norm) ×
    LowSpinBellData S d e p.spin

noncomputable instance [Fintype S] (d : ℕ) (e : Fin d → Equiv.Perm S) (p : LowSpinPlanQ) :
    Fintype (LowSpinData S d e p) := by
  unfold LowSpinData
  infer_instance

noncomputable instance (d : ℕ) (e : Fin d → Equiv.Perm S) (p : LowSpinPlanQ) :
    DecidableEq (LowSpinData S d e p) := by
  unfold LowSpinData
  infer_instance

/-- Construction for low Spin Velocity Value Q in the low spin plan model. -/
def lowSpinVelocityValueQ [Fintype S] {d : ℕ} (p : HighConfidencePlanQ)
    (u : Fin d → S → ℚ) (α β U : ℚ)
    (z : Fin d → VelocityData S p.current p.crossRecords p.norm) : ℚ :=
  ∑ j : Fin d,intervalClipQ 0 ((α+β*U)^2)
    (velocityRawOutputQ p.current p.crossRecords p.norm (Fintype.card S) (u j) α β (z j))

noncomputable section

/-- Construction for low Spin Bell Value Q in the low spin plan model. -/
def lowSpinBellValueQ {d : ℕ} (e : Fin d → Equiv.Perm S) (γ : ℚ)
    (spin : Option BellPlanQ) : LowSpinBellData S d e spin → ℚ :=
  match spin with
  | none => fun _ => 0
  | some q => fun ω => intervalClipQ 0 (2*(d : ℚ)*γ)
      (4*γ*(∑ j : Fin d,(executePlannedBellQ q (e j) (ω j)).value))

-- This dispatches on the actual Option, not on gamma inside the old Pauli
/-- full-output definition. The velocity component is consumed directly. -/
def lowSpinOutputQ [Fintype S] {d : ℕ} (p : LowSpinPlanQ) (u : Fin d → S → ℚ)
    (e : Fin d → Equiv.Perm S) (α β U γ : ℚ) (z : LowSpinData S d e p) : ℚ :=
  lowSpinVelocityValueQ p.velocity u α β U z.1+lowSpinBellValueQ e γ p.spin z.2

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_plan_velocity_fields
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_plan_zero_spin
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_plan_bell_fields
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_plan_account_fields
