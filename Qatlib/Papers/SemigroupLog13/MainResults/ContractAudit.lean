/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SemigroupLog13.MainResults.SemigroupTasks.SourceSemigroupTasks
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section


/-! Literal budget and readout diagnostics, with no source-algorithm cost credit. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SemigroupLog13.MainResults.ContractAudit
open Qatlib.Papers.SemigroupLog13.MainResults
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBounds
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CopyEvolution.Discriminate

/-- The identity matrix is an actual admissible multiplication oracle on the unit semigroup. -/
def unitOracle : MulOracleAccess Unit (fun _ _ => ()) () where
  oracle := 1
  unitary := (Matrix.unitaryGroup (Option (Unit × Unit × Unit × Unit)) ℂ).one_mem
  action := by
    intro x y z
    cases x
    cases y
    cases z
    simp

/-- Every finite budget meets the legacy fixed-size polylog predicate.
The existential constants occur after the size, so this is no uniform bound. -/
theorem everyBudget (B : Budget) (N : ℕ) : PolyLogBudget B N := by
  refine ⟨B.queries + B.macroGates + B.depth + 1, 1, by omega, by omega, ?_, ?_, ?_⟩
  all_goals simp only [pow_one]
  all_goals nlinarith [Nat.zero_le (Nat.log 2 N)]

/-- The empty program exposes any supplied basis-label readout without charging it. -/
theorem freeReadout {S Out : Type} [Fintype S] [DecidableEq S]
    (mul : S → S → S) (clean : S) (readout : Option (S × S × S × S) → Out)
    (M : MulOracleAccess S mul clean) (j : Option (S × S × S × S)) :
    inputLaw mul clean (idleProgram (Ket none) (normalized_ket none) readout)
      M (Ket j) (normalized_ket j) = PMF.pure (readout j) := by
  simp [inputLaw, idleProgram, bornDistribution_ket, PMF.pure_map]
/-- A point mass gives unit mass to every event containing its point. -/
theorem pureEvent {Y : Type} (a : Y) (ok : Y → Prop) (ha : ok a) :
    pmfEventProb (PMF.pure a) ok = 1 := by
  classical
  unfold pmfEventProb
  rw [tsum_eq_single a]
  · simp [ha, PMF.pure_apply]
  · intro y hy
    simp [PMF.pure_apply, hy]

/-- Any exact basis-label lookup passes the literal success contract at zero circuit cost. -/
theorem lookupSuccess {S X Out : Type} [Fintype S] [DecidableEq S]
    (mul : S → S → S) (clean : S) (enc : X → Option (S × S × S × S))
    (readout : Option (S × S × S × S) → Out) (ok : X → Out → Prop)
    (correct : ∀ x, ok x (readout (enc x))) :
    UniformSuccess mul clean (idleProgram (Ket none) (normalized_ket none) readout)
      ⟨0,0,0⟩ (fun x => Ket (enc x)) (fun x => normalized_ket (enc x)) ok := by
  refine ⟨(within_iff _ _).mpr ⟨le_rfl,le_rfl,le_rfl⟩, ?_⟩
  intro M x
  rw [freeReadout, pureEvent _ _ (correct x)]
  exact (ENNReal.div_le_iff (by norm_num) (by simp)).mpr (by norm_num)

/-- The original Lemma 1 header admits an uncharged lookup of the algebraic specification.
This is a defect probe for the literal model, not a period-finding algorithm. -/
theorem indexLookup {S : Type} [Semigroup S] [Fintype S] [DecidableEq S] (clean : S) :
    ∃ (P : MeasuredProgram (Option (S × S × S × S)) (ℕ × ℕ)) (B : Budget),
      PolyLogBudget B (Fintype.card S) ∧
      UniformSuccess (fun a b : S => a * b) clean P B
        (fun g : S => Ket (some (g,g,g,clean))) (fun _ => normalized_ket _)
        (fun g out => out = (indexOf g,periodOf g)) := by
  let readout : Option (S × S × S × S) → ℕ × ℕ :=
    fun j => match j with
    | none => (0,0)
    | some p => (indexOf p.1,periodOf p.1)
  refine ⟨idleProgram (Ket none) (normalized_ket none) readout, ⟨0,0,0⟩,
    everyBudget _ _, ?_⟩
  exact lookupSuccess _ clean (fun g => some (g,g,g,clean)) readout _ (fun _ => rfl)

/-- The original DLP header admits an uncharged lookup of the least positive logarithm.
The readout is a noncomputable specification and earns no algorithmic cost credit. -/
theorem dlogLookup {S : Type} [Semigroup S] [Fintype S] [DecidableEq S] (clean : S) :
    ∃ (P : MeasuredProgram (Option (S × S × S × S)) (Option ℕ)) (B : Budget),
      PolyLogBudget B (Fintype.card S) ∧
      UniformSuccess (fun a b : S => a * b) clean P B
        (fun p : S × S => Ket (some (p.1,p.2,p.1,clean))) (fun _ => normalized_ket _)
        (fun p out => out = dlogValue p.1 p.2) := by
  let readout : Option (S × S × S × S) → Option ℕ :=
    fun j => match j with
    | none => none
    | some p => dlogValue p.1 p.2.1
  refine ⟨idleProgram (Ket none) (normalized_ket none) readout, ⟨0,0,0⟩,
    everyBudget _ _, ?_⟩
  exact lookupSuccess _ clean (fun p : S × S => some (p.1,p.2,p.1,clean)) readout _
    (fun _ => rfl)
/-- Both shifted-DLP resource clauses allow the same uncharged specification lookup.
The two source algorithms are not implemented by this literal-model witness. -/
theorem shiftedLookup {S : Type} [Semigroup S] [Fintype S] [DecidableEq S] (clean : S) :
    (∃ (P : MeasuredProgram (Option (S × S × S × S)) (Option ℕ)) (B : Budget),
      SubExpTimeBudget B (Fintype.card S) ∧
      UniformSuccess (fun a b : S => a * b) clean P B
        (fun p : {p : S × S × S // shiftValue p.2.1 p.2.2 p.1 ≠ none} =>
          Ket (some (p.1.1,p.1.2.1,p.1.2.2,clean))) (fun _ => normalized_ket _)
        (fun p out => out = shiftValue p.1.2.1 p.1.2.2 p.1.1)) ∧
    (∃ (P : MeasuredProgram (Option (S × S × S × S)) (Option ℕ)) (B : Budget),
      PolyLogQueries B (Fintype.card S) ∧
      UniformSuccess (fun a b : S => a * b) clean P B
        (fun p : {p : S × S × S // shiftValue p.2.1 p.2.2 p.1 ≠ none} =>
          Ket (some (p.1.1,p.1.2.1,p.1.2.2,clean))) (fun _ => normalized_ket _)
        (fun p out => out = shiftValue p.1.2.1 p.1.2.2 p.1.1)) := by
  let readout : Option (S × S × S × S) → Option ℕ :=
    fun j => match j with
    | none => none
    | some p => shiftValue p.2.1 p.2.2.1 p.1
  have hs := lookupSuccess (fun a b : S => a * b) clean
    (fun p : {p : S × S × S // shiftValue p.2.1 p.2.2 p.1 ≠ none} =>
      some (p.1.1,p.1.2.1,p.1.2.2,clean)) readout
    (fun p out => out = shiftValue p.1.2.1 p.1.2.2 p.1.1) (fun _ => rfl)
  constructor
  · refine ⟨_, ⟨0,0,0⟩, ?_, hs⟩
    intro ε _
    change ((0 : ℕ) : ℝ) ≤ _
    rw [Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card S)) _
  · refine ⟨_, ⟨0,0,0⟩, ⟨1,1,by decide,by decide,?_⟩, hs⟩
    exact Nat.zero_le _

/-- An uncharged choice readout satisfies the literal promised-membership target.
No executable search, implementation of choice, or source complexity is credited. -/
theorem memberLookup {S : Type} [CommSemigroup S] [Fintype S] [DecidableEq S]
    (k : ℕ) (hk : 2 ≤ k) (g : Fin k → S) (clean : S) :
    ∃ (P : MeasuredProgram (Option (S × S × S × S)) (Fin k → ℕ)) (B : Budget),
      Theorem3TimeBudget k (Fintype.card S) B ∧
      Theorem3QueryBudget k (Fintype.card S) B ∧
      UniformSuccess (fun a b : S => a * b) clean P B
        (fun x : {x : S // ∃ a : Fin k → ℕ, MembershipOK g x a} =>
          Ket (some (g ⟨0,by omega⟩,x.1,g ⟨0,by omega⟩,clean))) (fun _ => normalized_ket _)
        (fun x out => MembershipOK g x.1 out) := by
  classical
  let pick (x : S) : Fin k → ℕ :=
    if h : ∃ a : Fin k → ℕ, MembershipOK g x a then Classical.choose h else fun _ => 0
  let readout : Option (S × S × S × S) → Fin k → ℕ :=
    fun j => match j with
    | none => fun _ => 0
    | some p => pick p.2.1
  refine ⟨idleProgram (Ket none) (normalized_ket none) readout, ⟨0,0,0⟩, ?_, ?_, ?_⟩
  · intro ε _
    change ((0 : ℕ) : ℝ) ≤ _
    rw [Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card S)) _
  · refine ⟨1,1,by decide,by decide,?_⟩
    change ((0 : ℕ) : ℝ) ≤ _ * _
    rw [Nat.cast_zero]
    positivity
  · apply lookupSuccess
    intro x
    dsimp [readout]
    simp only [pick, dite_eq_left x.2]
    exact Classical.choose_spec x.2
end Qatlib.Papers.SemigroupLog13.MainResults.ContractAudit
