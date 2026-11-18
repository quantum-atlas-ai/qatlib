/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TrotterError19.MainResults.ContractBounds
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum

@[expose] public section


/-!
# Counterexamples to complete legacy Trotter contracts

Each `Legacy*Contract` preserves an unrestricted legacy library contract, and
its `not_legacy_*_contract` theorem supplies a concrete counterexample. These
refutations concern the library interfaces, not certified statements of the
source paper.
-/

set_option autoImplicit false
open Filter Asymptotics
open Qatlib.Papers.TrotterError19.MainResults

namespace Qatlib.Papers.TrotterError19.MainResults.ContractChecks

/-- The source asymptotic notation is Big O along natural system sizes. -/
abbrev BigO (f g : ℕ → ℝ) : Prop := f =O[atTop] g

/-- A claimed bound of the unit constant by an identically zero function is impossible. -/
private theorem violates_zero_bound {g : ℕ → ℝ}
    (h : BigO (fun _ => (1 : ℝ)) g) (hg : ∀ n, g n = 0) : False := by
  have hfun : g = fun _ => 0 := funext hg
  rw [hfun] at h
  exact one_not_bigO_zero h

/-- Legacy bilinear commutator contract for arbitrary ring-valued families, without commutation hypotheses. -/
def LegacyBilinearCommutatorContract : Prop :=
  ∀ {R : Type} [Ring R] (ι : Type) [DecidableEq ι]
    (A Adag : ι → R) (j k l m : ι),
    brk (Adag j * A k) (Adag l * A m) =
      (if k = l then (1 : R) else 0) * (Adag j * A m) -
      (if j = m then (1 : R) else 0) * (Adag l * A k)

/-- Legacy number-operator commutator contract with only the factorization hypothesis, without commutation relations. -/
def LegacyNumberCommutatorContract : Prop :=
  ∀ {R : Type} [Ring R] (ι : Type) [DecidableEq ι]
    (A Adag : ι → R) (N : ι → R) (_hN : ∀ l, N l = Adag l * A l) (j k l : ι),
    brk (Adag j * A k) (N l) =
      (if k = l then (1 : R) else 0) * (Adag j * A l) -
      (if j = l then (1 : R) else 0) * (Adag l * A k)

/-- Legacy contract deriving Trotter and gate bounds from an error bound and the gate-count identity alone. -/
def LegacyTrotterGateBoundFromErrorContract : Prop :=
  ∀ (p : ℕ) (t ε : ℝ) (err tro gate : ℕ → ℝ)
    (_hp : 1 ≤ p) (_ht : 0 ≤ t) (_hε : 0 < ε)
    (_herr : BigO err (fun n => ((n : ℝ) * t) ^ (p + 1)))
    (_hgate : ∀ n, gate n = (n : ℝ) ^ 2 * tro n),
    BigO tro (fun n => ((n : ℝ) * t) ^ (1 + (1 : ℝ) / p) / ε ^ ((1 : ℝ) / p)) ∧
      BigO gate (fun n => (n : ℝ) ^ (2 + 1 + (1 : ℝ) / p) *
        t ^ (1 + (1 : ℝ) / p) / ε ^ ((1 : ℝ) / p))

/-- Legacy error-bound contract assuming only nonnegativity of the error and norm sequences. -/
def LegacyErrorFromNormsContract : Prop :=
  ∀ (p : ℕ) (_hp : 1 ≤ p)
    (err sumNorm coeffNorm : ℕ → ℝ)
    (_hsum : ∀ n, 0 ≤ sumNorm n) (_hcoeff : ∀ n, 0 ≤ coeffNorm n)
    (_hErr : ∀ n, 0 ≤ err n),
    BigO err (fun n => sumNorm n ^ p * coeffNorm n)

/-- Legacy Trotter-bound contract with nonnegative norm sequences and an unrestricted Trotter sequence. -/
def LegacyTrotterBoundFromNormsContract : Prop :=
  ∀ (p : ℕ) (t ε : ℝ) (_hp : 1 ≤ p) (_ht : 0 ≤ t) (_hε : 0 < ε)
    (tro sumNorm coeffNorm : ℕ → ℝ)
    (_hsum : ∀ n, 0 ≤ sumNorm n) (_hcoeff : ∀ n, 0 ≤ coeffNorm n),
    BigO tro (fun n => sumNorm n * coeffNorm n ^ ((1 : ℝ) / p) *
      t ^ (1 + (1 : ℝ) / p) / ε ^ ((1 : ℝ) / p))

/-- Legacy gate-bound contract with unrestricted gate and norm sequences. -/
def LegacyGateBoundFromNormsContract : Prop :=
  ∀ (k : ℕ) (t : ℝ) (_ht : 0 ≤ t)
    (gate sumNorm coeffNorm : ℕ → ℝ),
    BigO gate (fun n => (n : ℝ) ^ k * sumNorm n * coeffNorm n)

/-- Legacy subcritical-exponent error, Trotter and gate contract with unrestricted cost sequences. -/
def LegacySubcriticalErrorTrotterGateContract : Prop :=
  ∀ (α : ℝ) (d p : ℕ) (t ε : ℝ)
    (_hd : 1 ≤ d) (_hp : 1 ≤ p) (_hα : 0 ≤ α) (_hαd : α < (d : ℝ))
    (_ht : 0 ≤ t) (_hε : 0 < ε)
    (err tro gate : ℕ → ℝ),
    BigO err (fun n => Real.rpow (n : ℝ) (1 + ((p : ℝ) + 1) * (1 - α / (d : ℝ))) *
        t ^ (p + 1)) ∧
      BigO tro (fun n => Real.rpow (n : ℝ)
          (1 - α / (d : ℝ) + (1 / (p : ℝ)) * (2 - α / (d : ℝ))) *
        t ^ (1 + 1 / (p : ℝ)) / ε ^ (1 / (p : ℝ))) ∧
      BigO gate (fun n => Real.rpow (n : ℝ)
          (3 - α / (d : ℝ)) * t)

/-- Legacy logarithmic critical-regime error, Trotter and gate contract with unrestricted cost sequences. -/
def LegacyCriticalErrorTrotterGateContract : Prop :=
  ∀ (d p : ℕ) (t ε : ℝ)
    (_hd : 1 ≤ d) (_hp : 1 ≤ p) (_ht : 0 ≤ t) (_hε : 0 < ε)
    (err tro gate : ℕ → ℝ),
    BigO err (fun n => (n : ℝ) * Real.log (n : ℝ) ^ (p + 1) * t ^ (p + 1)) ∧
      BigO tro (fun n => Real.rpow (n : ℝ) (1 / (p : ℝ)) *
          Real.log (n : ℝ) ^ (1 + 1 / (p : ℝ)) *
        t ^ (1 + 1 / (p : ℝ)) / ε ^ (1 / (p : ℝ))) ∧
      BigO gate (fun n => Real.rpow (n : ℝ) 2 * t)

/-- Legacy supercritical-exponent error, Trotter and gate contract with unrestricted cost sequences. -/
def LegacySupercriticalErrorTrotterGateContract : Prop :=
  ∀ (α : ℝ) (d p : ℕ) (t ε : ℝ)
    (_hd : 1 ≤ d) (_hp : 1 ≤ p) (_hαd : (d : ℝ) < α) (_ht : 0 ≤ t) (_hε : 0 < ε)
    (err tro gate : ℕ → ℝ),
    BigO err (fun n => (n : ℝ) * t ^ (p + 1)) ∧
      BigO tro (fun n => Real.rpow (n : ℝ) (1 / (p : ℝ)) *
        t ^ (1 + 1 / (p : ℝ)) / ε ^ (1 / (p : ℝ))) ∧
      BigO gate (fun n => Real.rpow (n : ℝ) 2 * t)

/-- Legacy Trotter and gate contract conditional on an error bound and an exact supercritical cutoff formula. -/
def LegacyCutoffTrotterGateContract : Prop :=
  ∀ (α : ℝ) (d p : ℕ) (t ε : ℝ)
    (_hd : 1 ≤ d) (_hp : 1 ≤ p) (_hαd : (d : ℝ) < α) (_ht : 0 ≤ t) (_hε : 0 < ε)
    (err tro gate : ℕ → ℝ) (ℓ : ℕ → ℝ),
    BigO err (fun n => (n : ℝ) * t ^ (p + 1)) ∧
      (∀ n, ℓ n = Real.rpow ((n : ℝ) * t / ε) (1 / (α - (d : ℝ)))) →
      BigO tro (fun n => Real.rpow (n : ℝ) (1 / (p : ℝ)) *
        t ^ (1 + 1 / (p : ℝ)) / ε ^ (1 / (p : ℝ))) ∧
      BigO gate (fun n => Real.rpow ((n : ℝ) * t)
        (1 + (d : ℝ) / (α - (d : ℝ))))

/-- Legacy error, Trotter and arbitrarily near-linear gate-bound contract with unrestricted cost sequences. -/
def LegacyNearLinearGateCostContract : Prop :=
  ∀ (β : ℝ) (d p : ℕ) (t ε : ℝ)
    (_hd : 1 ≤ d) (_hp : 1 ≤ p) (_hβ : 0 < β) (_ht : 0 ≤ t) (_hε : 0 < ε)
    (err tro gate : ℕ → ℝ) (_ℓ : ℕ → ℝ),
    BigO err (fun n => (n : ℝ) * t ^ (p + 1)) ∧
      BigO tro (fun n => Real.rpow (n : ℝ) (1 / (p : ℝ)) *
        t ^ (1 + 1 / (p : ℝ)) / ε ^ (1 / (p : ℝ))) ∧
      (∀ δ : ℝ, 0 < δ → BigO gate (fun n => Real.rpow ((n : ℝ) * t) (1 + δ)))

/-- Legacy error-bound contract depending on nonnegative connectivity and interaction strength, with unrestricted errors. -/
def LegacyConnectivityErrorContract : Prop :=
  ∀ (p : ℕ) (_hp : 1 ≤ p) (t hB : ℝ) (_ht : 0 ≤ t) (_hhB : 0 ≤ hB)
    (err : ℕ → ℝ) (dprime : ℕ → ℝ) (_hd : ∀ n, 0 ≤ dprime n),
    BigO err (fun n => Real.rpow (dprime n) (((p : ℝ) + 1) * (p : ℝ) / 2) * hB *
      t ^ (p + 1))

/-- Legacy Trotter-bound contract depending on nonnegative interaction strength, with an unrestricted Trotter sequence. -/
def LegacyInteractionTrotterContract : Prop :=
  ∀ (p : ℕ) (t ε hB : ℝ) (_hp : 1 ≤ p)
    (_ht : 0 ≤ t) (_hε : 0 < ε) (_hhB : 0 ≤ hB) (tro : ℕ → ℝ),
    BigO tro (fun _ => Real.rpow hB (1 / (p : ℝ)) * t ^ (1 + 1 / (p : ℝ)) /
      ε ^ (1 / (p : ℝ)))

/-- Legacy Trotter-bound contract quantified over every positive asymptotic exponent, with an unrestricted Trotter sequence. -/
def LegacyArbitraryExponentTrotterContract : Prop :=
  ∀ (t ε hB : ℝ) (_ht : 0 ≤ t) (_hε : 0 < ε) (_hhB : 0 ≤ hB)
    (tro : ℕ → ℝ),
    ∀ δ : ℝ, 0 < δ →
      BigO tro (fun _ => Real.rpow hB δ * t ^ (1 + δ) / ε ^ δ)


/-- The real constant-family counterexample refutes the legacy bilinear commutator contract. -/
theorem not_legacy_bilinear_commutator_contract : ¬ LegacyBilinearCommutatorContract := by
  intro h
  have hc := h (R := ℝ) (Fin 2) (fun _ => 1) (fun _ => 1) 0 1 1 1
  norm_num [brk] at hc

/-- The real constant-family counterexample refutes the legacy number-operator commutator contract. -/
theorem not_legacy_number_commutator_contract : ¬ LegacyNumberCommutatorContract := by
  intro h
  have hc := h (R := ℝ) (Fin 2) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (by intro l; norm_num) 0 1 1
  norm_num [brk] at hc

/-- A zero-time counterexample refutes the legacy error-to-Trotter-and-gate contract. -/
theorem not_legacy_trotter_gate_bound_from_error_contract : ¬ LegacyTrotterGateBoundFromErrorContract := by
  intro h
  have hc := h 1 0 1 (fun _ => 0) (fun _ => 1) (fun n => (n : ℝ) ^ 2)
    (by norm_num) (by norm_num) (by norm_num)
    (by exact Asymptotics.isBigO_zero _ _) (by intro n; simp)
  exact violates_zero_bound hc.1 (by intro n; norm_num)

/-- A unit error and zero norms refute the legacy error-from-norms contract. -/
theorem not_legacy_error_from_norms_contract : ¬ LegacyErrorFromNormsContract := by
  intro h
  have hc := h 1 (by norm_num) (fun _ => 1) (fun _ => 0) (fun _ => 0)
    (by intro n; norm_num) (by intro n; norm_num) (by intro n; norm_num)
  exact violates_zero_bound hc (by intro n; norm_num)

/-- The allowed zero-time endpoint gives a counterexample to the legacy Trotter-from-norms contract. -/
theorem not_legacy_trotter_bound_from_norms_contract : ¬ LegacyTrotterBoundFromNormsContract := by
  intro h
  have hc := h 1 0 1 (by norm_num) (by norm_num) (by norm_num)
    (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (by intro n; norm_num) (by intro n; norm_num)
  exact violates_zero_bound hc (by intro n; norm_num)

/-- A unit gate sequence and zero norms refute the legacy gate-from-norms contract. -/
theorem not_legacy_gate_bound_from_norms_contract : ¬ LegacyGateBoundFromNormsContract := by
  intro h
  have hc := h 1 0 (by norm_num) (fun _ => 1) (fun _ => 0) (fun _ => 0)
  exact violates_zero_bound hc (by intro n; norm_num)

/-- A zero-time counterexample refutes the legacy subcritical error, Trotter and gate contract. -/
theorem not_legacy_subcritical_error_trotter_gate_contract : ¬ LegacySubcriticalErrorTrotterGateContract := by
  intro h
  have hc := h 0 1 1 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun _ => 1) (fun _ => 0) (fun _ => 0)
  exact violates_zero_bound hc.1 (by intro n; norm_num)

/-- A zero-time counterexample refutes the legacy critical-regime error, Trotter and gate contract. -/
theorem not_legacy_critical_error_trotter_gate_contract : ¬ LegacyCriticalErrorTrotterGateContract := by
  intro h
  have hc := h 1 1 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => 1) (fun _ => 0) (fun _ => 0)
  exact violates_zero_bound hc.1 (by intro n; norm_num)

/-- A zero-time counterexample refutes the legacy supercritical error, Trotter and gate contract. -/
theorem not_legacy_supercritical_error_trotter_gate_contract : ¬ LegacySupercriticalErrorTrotterGateContract := by
  intro h
  have hc := h 2 1 1 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun _ => 1) (fun _ => 0) (fun _ => 0)
  exact violates_zero_bound hc.1 (by intro n; norm_num)

/-- A counterexample satisfying both antecedents refutes the legacy cutoff Trotter and gate contract. -/
theorem not_legacy_cutoff_trotter_gate_contract : ¬ LegacyCutoffTrotterGateContract := by
  intro h
  have hc := h 2 1 1 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 0)
    ⟨Asymptotics.isBigO_zero _ _, by intro n; norm_num⟩
  exact violates_zero_bound hc.1 (by intro n; norm_num)

/-- A zero-time counterexample refutes the legacy near-linear gate-cost contract. -/
theorem not_legacy_near_linear_gate_cost_contract : ¬ LegacyNearLinearGateCostContract := by
  intro h
  have hc := h 1 1 1 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0)
  exact violates_zero_bound hc.1 (by intro n; norm_num)

/-- A unit error at zero interaction strength refutes the legacy connectivity-error contract. -/
theorem not_legacy_connectivity_error_contract : ¬ LegacyConnectivityErrorContract := by
  intro h
  have hc := h 1 (by norm_num) 1 0 (by norm_num) (by norm_num)
    (fun _ => 1) (fun _ => 1) (by intro n; norm_num)
  exact violates_zero_bound hc (by intro n; norm_num)

/-- A unit Trotter sequence at zero interaction strength refutes the legacy interaction-Trotter contract. -/
theorem not_legacy_interaction_trotter_contract : ¬ LegacyInteractionTrotterContract := by
  intro h
  have hc := h 1 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => 1)
  exact violates_zero_bound hc (by intro n; norm_num)

/-- The positive exponent one gives a counterexample to the legacy arbitrary-exponent Trotter contract. -/
theorem not_legacy_arbitrary_exponent_trotter_contract : ¬ LegacyArbitraryExponentTrotterContract := by
  intro h
  have hc := h 1 1 0 (by norm_num) (by norm_num) (by norm_num)
    (fun _ => 1) 1 (by norm_num)
  exact violates_zero_bound hc (by intro n; norm_num)


end Qatlib.Papers.TrotterError19.MainResults.ContractChecks
