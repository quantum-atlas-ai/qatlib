/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section


/-!
The unrestricted legacy amplitude-function model admits a one-copy solver. This
refutes its exponential copy lower bound; no quantum copy-complexity claim is made.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.ShadowHam24.MainResults.CopyBoundary

/-- The componentwise conjugate state `|ψ̄⟩`, with amplitudes `conj(ψ_i)`. -/
def conjugateState {n : ℕ} (ψ : Fin (2 ^ n) → ℂ) : Fin (2 ^ n) → ℂ :=
  fun i => star (ψ i)

/-- The conjugate overlap `⟨ψ|ψ̄⟩ = ∑_i conj(ψ_i)^2`. -/
def conjugateOverlap {n : ℕ} (ψ : Fin (2 ^ n) → ℂ) : ℂ :=
  ∑ i, star (ψ i) * conjugateState ψ i

/-- Normalisation of an `n`-qubit state vector. -/
def stateNormalised {n : ℕ} (ψ : Fin (2 ^ n) → ℂ) : Prop :=
  (∑ i, Complex.normSq (ψ i)) = 1

/-- The promise of Theorem 4: `|⟨ψ|ψ̄⟩| ≤ 1/3` or `|⟨ψ|ψ̄⟩| ≥ 2/3`. -/
def conjugateOverlapPromise {n : ℕ} (ψ : Fin (2 ^ n) → ℂ) : Prop :=
  ‖conjugateOverlap ψ‖ ≤ 1 / 3 ∨ 2 / 3 ≤ ‖conjugateOverlap ψ‖

/-- A `k`-copy algorithm acting on `n`-qubit states (only copies of `|ψ⟩`). -/
def ConjugateCopyAlgorithm (n k : ℕ) : Type :=
  (Fin k → Fin (2 ^ n) → ℂ) → Bool

/-- A pair algorithm acting on one copy of `|ψ⟩` and one copy of `|ψ̄⟩`. -/
def ConjugatePairAlgorithm (n : ℕ) : Type :=
  (Fin (2 ^ n) → ℂ) → (Fin (2 ^ n) → ℂ) → Bool

/-- Correctness of a `k`-copy algorithm on the promised conjugate-overlap
problem. -/
def SolvesWithCopies (n k : ℕ) (alg : ConjugateCopyAlgorithm n k) : Prop :=
  ∀ ψ : Fin (2 ^ n) → ℂ, stateNormalised ψ → conjugateOverlapPromise ψ →
    ((‖conjugateOverlap ψ‖ ≤ 1 / 3 → alg (fun _ => ψ) = false) ∧
      (2 / 3 ≤ ‖conjugateOverlap ψ‖ → alg (fun _ => ψ) = true))

/-- Correctness of a pair algorithm on the promised conjugate-overlap
problem. -/
def SolvesWithPair (n : ℕ) (alg : ConjugatePairAlgorithm n) : Prop :=
  ∀ ψ : Fin (2 ^ n) → ℂ, stateNormalised ψ → conjugateOverlapPromise ψ →
    ((‖conjugateOverlap ψ‖ ≤ 1 / 3 → alg ψ (conjugateState ψ) = false) ∧
      (2 / 3 ≤ ‖conjugateOverlap ψ‖ → alg ψ (conjugateState ψ) = true))

/-- The legacy algorithm type exposes amplitudes and hence admits a one-copy threshold test. -/
theorem oneCopySolver (n : ℕ) :
    ∃ alg : ConjugateCopyAlgorithm n 1, SolvesWithCopies n 1 alg := by
  classical
  refine ⟨fun input => if ‖conjugateOverlap (input 0)‖ ≤ 1 / 3 then false else true, ?_⟩
  intro ψ _ _
  constructor
  · intro h
    exact ite_eq_left h
  · intro h
    have hnot : ¬ ‖conjugateOverlap ψ‖ ≤ 1 / 3 := by linarith
    exact ite_eq_right hnot

/-- A one-copy solver contradicts every positive eventual exponential lower bound. -/
theorem noCopyLowerBound :
    ¬ (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (k : ℕ) (alg : ConjugateCopyAlgorithm n k),
        SolvesWithCopies n k alg → c * Real.sqrt ((2 : ℝ) ^ n) ≤ (k : ℝ)) := by
  rintro ⟨c, hc, hbound⟩
  have hdiv : Filter.Tendsto (fun n : ℕ => c * Real.sqrt ((2 : ℝ) ^ n))
      Filter.atTop Filter.atTop :=
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).const_mul_atTop hc
  have hlarge := hdiv.eventually_gt_atTop 1
  obtain ⟨n, hn, hlt⟩ := (hbound.and hlarge).exists
  obtain ⟨alg, halg⟩ := oneCopySolver n
  have hle := hn 1 alg halg
  norm_num at hle
  linarith


end Qatlib.Papers.ShadowHam24.MainResults.CopyBoundary
