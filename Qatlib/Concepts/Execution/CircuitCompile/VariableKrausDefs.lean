/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitDefs

/-!
# Adaptive Kraus circuits with variable outcome counts

`VariableKrausCircuit` describes finite adaptive circuits whose Kraus nodes may have different
numbers of outcomes. It provides mixed branch traces, event masses, expected query counts, and
structural bounds on query use and outcome counts, within the finite quantum operation framework
of [Kraus1983].

`padVariableKraus` extends every Kraus family to a common outcome count by adding zero
operators. The module proves that a sufficient width bound preserves completeness and the
worst-case query budget.

## Main statements

* `variableKraus_fits_of_width_le`: a structural width bound controls every outcome count.
* `padVariableKraus_wellFormed`: padding preserves well-formedness when the width fits.
* `padVariableKraus_budget`: padding preserves the query budget when the width fits.

## References

* [Kraus, 1983][Kraus1983]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.Execution.CircuitCompile

open Matrix

/-- A finite adaptive circuit with gate or query steps, Boolean halting outcomes, and Kraus
nodes whose outcome counts may vary. -/
inductive VariableKrausCircuit (d : ℕ) where
  | halt (accepted : Bool)
  | step (action : Step (Fin d)) (next : VariableKrausCircuit d)
  | instrument (s : ℕ) (K : Fin s → Operator d)
      (next : Fin s → VariableKrausCircuit d)

/-- Requires known gates to be unitary, each Kraus family to satisfy completeness, and every
continuation to be well-formed. -/
def variableKrausWellFormed {d : ℕ} : VariableKrausCircuit d → Prop
  | .halt _ => True
  | .step (.gate G) P => G ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ variableKrausWellFormed P
  | .step .query P => variableKrausWellFormed P
  | .instrument _ K next => (∑ a, (K a).conjTranspose * K a = 1) ∧
      ∀ a, variableKrausWellFormed (next a)

/-- The largest number of Kraus outcomes at any node of the circuit, with value zero for a
circuit without Kraus nodes. -/
def variableKrausWidth {d : ℕ} : VariableKrausCircuit d → ℕ
  | .halt _ => 0
  | .step _ P => variableKrausWidth P
  | .instrument s _ next =>
      max s (Finset.univ.sup fun a => variableKrausWidth (next a))

/-- Requires every Kraus node in the circuit to have at most `S` outcomes. -/
def variableKrausFits {d : ℕ} (S : ℕ) : VariableKrausCircuit d → Prop
  | .halt _ => True
  | .step _ P => variableKrausFits S P
  | .instrument s _ next => s ≤ S ∧ ∀ a, variableKrausFits S (next a)

/-- The largest number of query steps along a circuit branch. -/
def variableKrausBudget {d : ℕ} : VariableKrausCircuit d → ℕ
  | .halt _ => 0
  | .step (.gate _) P => variableKrausBudget P
  | .step .query P => variableKrausBudget P + 1
  | .instrument _ _ next =>
      Finset.univ.sup fun a => variableKrausBudget (next a)

/-- Enumerates terminal mixed branch traces with unnormalized operators, outcomes, and resource
counts. Each Kraus node contributes two gates and one measurement. -/
noncomputable def variableKrausMixedTraces {d : ℕ} (O : Operator d) :
    VariableKrausCircuit d → Operator d → List (MixedBranchTrace d)
  | .halt b, rho => [⟨rho, b, 0, 0, 0, []⟩]
  | .step (.gate G) P, rho =>
      (variableKrausMixedTraces O P (conjBranch G rho)).map fun t =>
        {t with gates := t.gates + 1}
  | .step .query P, rho =>
      (variableKrausMixedTraces O P (conjBranch O rho)).map fun t =>
        {t with queries := t.queries + 1}
  | .instrument s K next, rho =>
      (List.ofFn fun a : Fin s =>
        (variableKrausMixedTraces O (next a) (conjBranch (K a) rho)).map fun t =>
          {t with gates := t.gates + 2, measurements := t.measurements + 1, outcomes := (s, a.val) :: t.outcomes}).flatten

/-- The sum of mixed branch masses selected by an event on acceptance flags and outcome records. -/
noncomputable def variableKrausEventMass {d : ℕ} (O : Operator d)
    (P : VariableKrausCircuit d) (rho : Operator d)
    (event : Bool → List (ℕ × ℕ) → Bool) : ℝ :=
  ((variableKrausMixedTraces O P rho).map fun t =>
    if event t.accepted t.outcomes then mixedMass t else 0).sum

/-- The sum of terminal query counts weighted by their mixed branch masses. -/
noncomputable def variableKrausExpectedQueries {d : ℕ} (O : Operator d)
    (P : VariableKrausCircuit d) (rho : Operator d) : ℝ :=
  ((variableKrausMixedTraces O P rho).map fun t => mixedMass t * t.queries).sum

/-- Restores each outcome count in a record to the count of the corresponding variable Kraus
node. -/
def restoreVariableKrausRecord {d : ℕ} : VariableKrausCircuit d →
    List (ℕ × ℕ) → List (ℕ × ℕ)
  | .halt _, record => record
  | .step _ next, record => restoreVariableKrausRecord next record
  | .instrument _ _ _, [] => []
  | .instrument s _ next, (_, a) :: rest =>
      if h : a < s then
        (s, a) :: restoreVariableKrausRecord (next ⟨a, h⟩) rest
      else []

/-- Pads each Kraus node to `S` outcomes using zero operators and rejecting halts for added
outcomes. -/
def padVariableKraus {d : ℕ} (S : ℕ) :
    VariableKrausCircuit d → KrausCircuit d S
  | .halt b => .halt b
  | .step action P => .step action (padVariableKraus S P)
  | .instrument s K next =>
      .instrument
        (fun a : Fin S => if h : a.val < s then K ⟨a.val, h⟩ else 0)
        (fun a : Fin S =>
          if h : a.val < s then padVariableKraus S (next ⟨a.val, h⟩)
          else .halt false)

/-- Extending a finite sum by zero terms to any larger finite index set preserves its value. -/
theorem sum_fin_zero_padding {M : Type*} [AddCommMonoid M]
    {s S : ℕ} (h : s ≤ S) (f : Fin s → M) :
    (∑ a : Fin S, if ha : a.val < s then f ⟨a.val, ha⟩ else 0) =
      ∑ a : Fin s, f a := by
  classical
  induction S generalizing s with
  | zero =>
      have hs : s = 0 := Nat.eq_zero_of_le_zero h
      subst s
      simp
  | succ S ih =>
      by_cases heq : s = S + 1
      · subst s
        simp only [Fin.isLt, dif_pos]
      · have hs : s ≤ S := by omega
        rw [Fin.sum_univ_castSucc]
        simpa [Fin.val_castSucc, Fin.val_last, Nat.not_lt_of_ge hs] using ih hs f

/-- The width of any child circuit is bounded by the supremum of all child widths. -/
private theorem variableKrausWidth_child_le {d s : ℕ}
    (next : Fin s → VariableKrausCircuit d) (a : Fin s) :
    variableKrausWidth (next a) ≤ Finset.univ.sup
      (fun b : Fin s => variableKrausWidth (next b)) :=
  Finset.le_sup (f := fun b : Fin s => variableKrausWidth (next b))
    (Finset.mem_univ a)

/-- A circuit whose structural width is at most `S` satisfies the bound `variableKrausFits S`. -/
theorem variableKraus_fits_of_width_le {d : ℕ}
    (P : VariableKrausCircuit d) (S : ℕ)
    (h : variableKrausWidth P ≤ S) : variableKrausFits S P := by
  induction P with
  | halt b => trivial
  | step action P ih => exact ih h
  | instrument s K next ih =>
      constructor
      · exact le_trans (Nat.le_max_left _ _) h
      · intro a
        apply ih a
        exact le_trans (variableKrausWidth_child_le next a)
          (le_trans (Nat.le_max_right _ _) h)

/-- Extending a finite family of natural numbers by zeros preserves its supremum. -/
private theorem nat_fin_sup_zero_padding {s S : ℕ}
    (h : s ≤ S) (f : Fin s → ℕ) :
    Finset.univ.sup
        (fun a : Fin S => if ha : a.val < s then f ⟨a.val, ha⟩ else 0) =
      Finset.univ.sup f := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro a _
    by_cases ha : a.val < s
    · simp only [dif_pos ha]
      exact Finset.le_sup (f := f) (Finset.mem_univ (⟨a.val, ha⟩ : Fin s))
    · simp [ha]
  · apply Finset.sup_le
    intro a _
    let b : Fin S := ⟨a.val, lt_of_lt_of_le a.isLt h⟩
    have hb : b.val < s := a.isLt
    calc
      f a = (if hb' : b.val < s then f ⟨b.val, hb'⟩ else 0) := by simp [b, hb]
      _ ≤ Finset.univ.sup
          (fun x : Fin S => if hx : x.val < s then f ⟨x.val, hx⟩ else 0) :=
        Finset.le_sup (f := fun x : Fin S =>
          if hx : x.val < s then f ⟨x.val, hx⟩ else 0) (Finset.mem_univ b)

/-- Padding a well-formed variable Kraus circuit preserves well-formedness when every outcome
count is at most the padding width. -/
theorem padVariableKraus_wellFormed {d : ℕ}
    (P : VariableKrausCircuit d) (S : ℕ)
    (hfit : variableKrausFits S P) (hP : variableKrausWellFormed P) :
    krausCircuitWellFormed (padVariableKraus S P) := by
  induction P with
  | halt b => simp [padVariableKraus, krausCircuitWellFormed]
  | step action P ih =>
      cases action with
      | gate G =>
          rcases hP with ⟨hG, hP⟩
          exact ⟨hG, ih hfit hP⟩
      | query => exact ih hfit hP
  | instrument s K next ih =>
      rcases hfit with ⟨hs, hfitNext⟩
      rcases hP with ⟨hcomplete, hnext⟩
      constructor
      · calc
          (∑ a : Fin S,
            (if ha : a.val < s then K ⟨a.val, ha⟩ else 0).conjTranspose *
              (if ha : a.val < s then K ⟨a.val, ha⟩ else 0)) =
              ∑ a : Fin S,
                if ha : a.val < s then
                  (K ⟨a.val, ha⟩).conjTranspose * K ⟨a.val, ha⟩ else 0 := by
                    apply Finset.sum_congr rfl
                    intro a _
                    by_cases ha : a.val < s <;> simp [ha]
          _ = ∑ a : Fin s, (K a).conjTranspose * K a := sum_fin_zero_padding hs (fun a : Fin s => (K a).conjTranspose * K a)
          _ = 1 := hcomplete
      · intro a
        by_cases ha : a.val < s
        · simpa [padVariableKraus, ha] using
            (ih ⟨a.val, ha⟩ (hfitNext ⟨a.val, ha⟩) (hnext ⟨a.val, ha⟩))
        · simp [padVariableKraus, ha, krausCircuitWellFormed]

/-- Padding to a width that fits the circuit preserves its worst-case query budget. -/
theorem padVariableKraus_budget {d : ℕ}
    (P : VariableKrausCircuit d) (S : ℕ)
    (hfit : variableKrausFits S P) :
    krausCircuitBudget (padVariableKraus S P) = variableKrausBudget P := by
  induction P with
  | halt b => rfl
  | step action P ih =>
      cases action <;>
        simp [padVariableKraus, krausCircuitBudget, variableKrausBudget, ih hfit]
  | instrument s K next ih =>
      rcases hfit with ⟨hs, hfitNext⟩
      change Finset.univ.sup (fun a : Fin S =>
        krausCircuitBudget
          (if ha : a.val < s then padVariableKraus S (next ⟨a.val, ha⟩)
           else KrausCircuit.halt false)) =
        Finset.univ.sup (fun a : Fin s => variableKrausBudget (next a))
      calc
        Finset.univ.sup (fun a : Fin S =>
          krausCircuitBudget
            (if ha : a.val < s then padVariableKraus S (next ⟨a.val, ha⟩)
             else KrausCircuit.halt false)) =
            Finset.univ.sup (fun a : Fin S =>
              if ha : a.val < s then variableKrausBudget (next ⟨a.val, ha⟩) else 0) := by
                apply Finset.sup_congr rfl
                intro a _
                by_cases ha : a.val < s
                · simp only [dif_pos ha]
                  exact ih ⟨a.val, ha⟩ (hfitNext ⟨a.val, ha⟩)
                · simp [ha, krausCircuitBudget]
        _ = Finset.univ.sup (fun a : Fin s => variableKrausBudget (next a)) :=
          nat_fin_sup_zero_padding hs (fun a : Fin s => variableKrausBudget (next a))

end Qatlib.Concepts.Execution.CircuitCompile
