/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Pair potential circuits

Defines occupation-controlled pair phases and compiles lists of pairs into `potentialWord`,
following the interaction phases in [BoghosianTaylor1998]. The module proves exact amplitude
semantics, unitarity, preservation of fixed occupation sectors, and the all-pairs lattice gate
bound.

## Main statements

* `potentialWord_preserves_sector`: The potential circuit preserves support on configurations
  with a fixed occupation count.
* `lattice_potential_resources`: The all-pairs lattice potential circuit is unitary, uses no
  queries, and has at most `4 * d ^ 2 * l ^ (2 * d)` gates [BoghosianTaylor1998].

## References

* [Boghosian and Taylor, 1998][BoghosianTaylor1998]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QMechSim97.MainResults.PotentialWord
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QMechSim97.MainResults.Defs
open Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum
open scoped Classical BigOperators

/-- The scalar `exp (-θ * I)` when both Boolean occupations are true, and one otherwise. -/
def pairScalar (θ : ℝ) (b c : Bool) : ℂ :=
  if b && c then Complex.exp (-θ * Complex.I) else 1

/-- The diagonal two-bit operator whose entries are given by `pairScalar θ`. -/
def localPairPhase (θ : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.diagonal (fun z => pairScalar θ z.1 z.2)

/-- The diagonal register operator applying the pair phase determined by occupation bits `i` and
`j`. -/
def pairPhaseOn {N : ℕ} (i j : Fin N) (θ : ℝ) : Matrix (Reg N) (Reg N) ℂ :=
  Matrix.diagonal (fun x => pairScalar θ (x i) (x j))

/-- The predicate that two register configurations agree at every wire other than `i` and `j`. -/
def OutsideAgree {N : ℕ} (i j : Fin N) (x y : Reg N) : Prop :=
  ∀ k, k ≠ i → k ≠ j → x k = y k

/-- Each matrix entry of the register pair phase equals the local two-bit matrix entry when the
configurations agree outside the selected wires, and is zero otherwise. -/
theorem pairPhaseOn_local {N : ℕ} (i j : Fin N) (θ : ℝ) (x y : Reg N) :
    pairPhaseOn i j θ x y =
      if OutsideAgree i j x y then localPairPhase θ (x i, x j) (y i, y j) else 0 := by
  by_cases hxy : x = y
  · subst y
    simp [pairPhaseOn, localPairPhase, OutsideAgree]
  · by_cases ho : OutsideAgree i j x y
    · have hp : (x i, x j) ≠ (y i, y j) := by
        intro h
        apply hxy
        funext k
        by_cases hi : k = i
        · subst k; exact congrArg Prod.fst h
        · by_cases hj : k = j
          · subst k; exact congrArg Prod.snd h
          · exact ho k hi hj
      simp [pairPhaseOn, localPairPhase, hxy, ho, hp]
    · simp [pairPhaseOn, hxy, ho]

/-- Every occupation-dependent pair phase scalar has squared modulus one. -/
theorem pairScalar_normSq (θ : ℝ) (b c : Bool) : Complex.normSq (pairScalar θ b c) = 1 := by
  have hphase := normSq_exp_pure_imaginary (-θ)
  simp only [Complex.ofReal_neg, neg_mul] at hphase
  cases b <;> cases c <;> simp [pairScalar, hphase]

/-- The local two-bit pair phase matrix is unitary. -/
theorem localPairPhase_unitary (θ : ℝ) :
    localPairPhase θ ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact diagonal_phase_unitary _ (fun z => pairScalar_normSq θ z.1 z.2)

/-- The pair phase acting on a full register is unitary. -/
theorem pairPhaseOn_unitary {N : ℕ} (i j : Fin N) (θ : ℝ) :
    pairPhaseOn i j θ ∈ Matrix.unitaryGroup (Reg N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact diagonal_phase_unitary _ (fun x => pairScalar_normSq θ (x i) (x j))

/-- Applying the pair phase multiplies each amplitude by the scalar selected by its two
occupation bits. -/
theorem pairPhaseOn_apply {N : ℕ} (i j : Fin N) (θ : ℝ) (ψ : QState (Reg N)) (x : Reg N) :
    ApplyGate (pairPhaseOn i j θ) ψ x = pairScalar θ (x i) (x j) * ψ x := by
  simp [pairPhaseOn, ApplyGate, Matrix.mulVec_diagonal]

/-- The list of wire pairs with first index strictly smaller than the second. -/
def wirePairs (N : ℕ) : List (Fin N × Fin N) :=
  (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)).toList

/-- The two indices in every pair belonging to `wirePairs N` are distinct. -/
theorem wirePairs_distinct {N : ℕ} (p : Fin N × Fin N) (hp : p ∈ wirePairs N) :
    p.1 ≠ p.2 := by
  have h : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2
  exact h.ne

/-- The list `wirePairs N` contains at most `N ^ 2` pairs. -/
theorem wirePairs_length (N : ℕ) : (wirePairs N).length ≤ N ^ 2 := by
  rw [wirePairs, Finset.length_toList]
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin N × Fin N))
    (fun p => p.1 < p.2)
  simpa [Fintype.card_prod, pow_two] using h

/-- The circuit obtained by mapping each listed wire pair to its occupation-dependent phase
gate. -/
def potentialWord {N : ℕ} (pairs : List (Fin N × Fin N))
    (θ : Fin N → Fin N → ℝ) : Circuit (Reg N) :=
  pairs.map fun p => Step.gate (pairPhaseOn p.1 p.2 (θ p.1 p.2))

/-- The potential circuit is unitary, uses no queries, and contains exactly one gate per listed
pair. -/
theorem potentialWord_resources {N : ℕ} (pairs : List (Fin N × Fin N))
    (θ : Fin N → Fin N → ℝ) :
    IsUnitaryCircuit (potentialWord pairs θ) ∧
    QueryCount (potentialWord pairs θ) = 0 ∧
    GateCount (potentialWord pairs θ) = pairs.length := by
  refine ⟨?_,?_,?_⟩
  · intro U hU
    obtain ⟨p,_,hp⟩ := List.mem_map.mp hU
    cases hp
    exact pairPhaseOn_unitary _ _ _
  · induction pairs with
    | nil => rfl
    | cons p pairs ih =>
      change QueryCount (potentialWord pairs θ) = 0
      exact ih
  · induction pairs with
    | nil => rfl
    | cons p pairs ih =>
      change GateCount (potentialWord pairs θ) + 1 = pairs.length + 1
      exact congrArg (· + 1) ih

/-- Running the potential circuit multiplies each amplitude by the product of its pair phase
scalars. -/
theorem potentialWord_apply {N : ℕ} (pairs : List (Fin N × Fin N))
    (θ : Fin N → Fin N → ℝ) (ψ : QState (Reg N)) (x : Reg N) :
    Run 1 (potentialWord pairs θ) ψ x =
      (pairs.map (fun p => pairScalar (θ p.1 p.2) (x p.1) (x p.2))).prod * ψ x := by
  induction pairs generalizing ψ with
  | nil => simp [potentialWord]
  | cons p pairs ih =>
    change Run 1 (potentialWord pairs θ)
      (ApplyGate (pairPhaseOn p.1 p.2 (θ p.1 p.2)) ψ) x = _
    rw [ih, pairPhaseOn_apply]
    simp only [List.map_cons, List.prod_cons]
    ring

/-- The potential circuit preserves support on configurations with a fixed occupation count. -/
theorem potentialWord_preserves_sector {N : ℕ} (pairs : List (Fin N × Fin N))
    (θ : Fin N → Fin N → ℝ) (ψ : QState (Reg N)) (n : ℕ)
    (hψ : ∀ x, occupationCount x ≠ n → ψ x = 0) :
    ∀ x, occupationCount x ≠ n → Run 1 (potentialWord pairs θ) ψ x = 0 := by
  intro x hx
  rw [potentialWord_apply, hψ x hx, mul_zero]

/-- The all-pairs lattice potential circuit is unitary, uses no queries, and has at most `4 * d
^ 2 * l ^ (2 * d)` gates [BoghosianTaylor1998]. -/
theorem lattice_potential_resources (d l : ℕ)
    (θ : Fin (qubitCount d l) → Fin (qubitCount d l) → ℝ) :
    IsUnitaryCircuit (potentialWord (wirePairs (qubitCount d l)) θ) ∧
    QueryCount (potentialWord (wirePairs (qubitCount d l)) θ) = 0 ∧
    GateCount (potentialWord (wirePairs (qubitCount d l)) θ) ≤
      4 * d ^ 2 * l ^ (2 * d) := by
  have h := potentialWord_resources (wirePairs (qubitCount d l)) θ
  refine ⟨h.1,h.2.1,?_⟩
  rw [h.2.2]
  calc
    (wirePairs (qubitCount d l)).length ≤ (qubitCount d l) ^ 2 := wirePairs_length _
    _ = 4 * d ^ 2 * l ^ (2 * d) := by
      unfold qubitCount
      rw [mul_pow, mul_pow, ← pow_mul]
      ring

end Qatlib.Papers.QMechSim97.MainResults.PotentialWord
