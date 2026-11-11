/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.SearchStopping.QueryLowerBound.Theorem7CorrectedTigh
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Transport from query circuits to unitary blocks

This module separates a query circuit into an initial gate block and one gate block for each
oracle call using `splitQueries`. It proves preservation of the query count, unitarity, and
execution semantics.

The blocks are then transported to linear isometries of Euclidean space, relating circuit
execution to `UnitaryEvolution`. This gives a block formulation of the query algorithms studied
in [BealsEtAl2001].

## Main statements

* `splitQueries_count`: The number of post-query blocks equals the query count.
* `splitQueries_semantics`: Block execution agrees with the original circuit.
* `blocks_evolution`: Euclidean unitary evolution agrees with block execution.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.QueryLowerBound
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The complex linear isometric equivalence of Euclidean space induced by multiplication by a
unitary matrix. -/
noncomputable def unitaryEuclidean (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ I where
  toFun := U.toEuclideanLin
  invFun := Uᴴ.toEuclideanLin
  map_add' := U.toEuclideanLin.map_add
  map_smul' := U.toEuclideanLin.map_smul
  left_inv := by
    intro x
    change WithLp.toLp 2 (Uᴴ *ᵥ (U *ᵥ x.ofLp)) = x
    have hInv : Uᴴ * U = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
    rw [Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
  right_inv := by
    intro x
    change WithLp.toLp 2 (U *ᵥ (Uᴴ *ᵥ x.ofLp)) = x
    have hInv : U * Uᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
    rw [Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
  norm_map' := by
    intro x
    exact norm_toEuclideanCLM_of_mem_unitaryGroup hU x

/-- Applying the Euclidean equivalence induced by a unitary matrix is matrix-vector
multiplication transported through `WithLp`. -/
theorem unitaryEuclidean_apply (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (x : EuclideanSpace ℂ I) :
    unitaryEuclidean U hU x = WithLp.toLp 2 (U *ᵥ x.ofLp) := rfl

/-- Decomposes a circuit into an initial gate matrix and a list of gate matrices applied after
successive oracle calls. -/
noncomputable def splitQueries : Circuit I → Matrix I I ℂ × List (Matrix I I ℂ)
  | [] => (1, [])
  | Step.gate U :: C =>
      let parts := splitQueries C
      (parts.1 * U, parts.2)
  | Step.query :: C =>
      let parts := splitQueries C
      (1, parts.1 :: parts.2)

/-- The list of post-query blocks has length equal to the circuit's query count. -/
theorem splitQueries_count (C : Circuit I) : (splitQueries C).2.length = QueryCount C := by
  induction C with
  | nil => rfl
  | cons step C ih =>
    cases step <;> simp [splitQueries, QueryCount, ih, Nat.add_comm]

/-- A unitary circuit decomposes into a unitary initial block and unitary post-query blocks. -/
theorem splitQueries_unitary (C : Circuit I) (hC : IsUnitaryCircuit C) :
    (splitQueries C).1 ∈ Matrix.unitaryGroup I ℂ ∧
      ∀ G ∈ (splitQueries C).2, G ∈ Matrix.unitaryGroup I ℂ := by
  induction C with
  | nil => simp [splitQueries]
  | cons step C ih =>
    cases step with
    | gate U =>
      obtain ⟨hU, htail⟩ := (isUnitaryCircuit_gate U C).mp hC
      obtain ⟨hP, hB⟩ := ih htail
      exact ⟨mul_mem hP hU, hB⟩
    | query =>
      obtain ⟨hP, hB⟩ := ih ((isUnitaryCircuit_query C).mp hC)
      refine ⟨by simp [splitQueries], ?_⟩
      intro G hG
      rcases List.mem_cons.mp hG with he | he
      · simpa [he] using hP
      · exact hB G he

/-- Executes a list of blocks by applying the oracle and then the next gate matrix at each step. -/
noncomputable def runQueryBlocks (O : Matrix I I ℂ) :
    List (Matrix I I ℂ) → QState I → QState I
  | [], ψ => ψ
  | G :: gs, ψ => runQueryBlocks O gs (G *ᵥ (O *ᵥ ψ))

/-- Executing a circuit agrees with applying its initial block and then running its post-query
blocks. -/
theorem splitQueries_semantics (C : Circuit I) (O : Matrix I I ℂ) (ψ : QState I) :
    Run O C ψ = runQueryBlocks O (splitQueries C).2 ((splitQueries C).1 *ᵥ ψ) := by
  induction C generalizing ψ with
  | nil => simp [Run, splitQueries, runQueryBlocks]
  | cons step C ih =>
    cases step <;> simp [Run, ApplyGate, splitQueries, runQueryBlocks, ih, Matrix.mulVec_mulVec]

/-- Selecting a matrix from a list of unitary blocks, with identity as the out-of-range default,
always gives a unitary matrix. -/
theorem block_get_unitary (gs : List (Matrix I I ℂ))
    (hgs : ∀ G ∈ gs, G ∈ Matrix.unitaryGroup I ℂ) (n : ℕ) :
    gs.getD n 1 ∈ Matrix.unitaryGroup I ℂ := by
  induction gs generalizing n with
  | nil => simp
  | cons G gs ih =>
    cases n with
    | zero => simpa using hgs G List.mem_cons_self
    | succ n =>
      simpa using ih (fun H hH => hgs H (List.mem_cons_of_mem G hH)) n

omit [DecidableEq I] in

/-- Unitary evolution for `n + 1` steps equals evolution for `n` steps with the shifted sequence
after applying the first unitary. -/
theorem evolution_shift (U : ℕ → EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ I)
    (ψ : EuclideanSpace ℂ I) (n : ℕ) :
    UnitaryEvolution U ψ (n + 1) = UnitaryEvolution (fun k => U (k + 1)) (U 0 ψ) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change U (n + 1) (UnitaryEvolution U ψ (n + 1)) =
      U (n + 1) (UnitaryEvolution (fun k => U (k + 1)) (U 0 ψ) n)
    rw [ih]

/-- The sequence of Euclidean linear isometries obtained by composing each post-query gate block
with the oracle, using identity for missing gate blocks. -/
noncomputable def blockEvolution (gs : List (Matrix I I ℂ))
    (hgs : ∀ G ∈ gs, G ∈ Matrix.unitaryGroup I ℂ) (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (n : ℕ) :
    EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ I :=
  unitaryEuclidean (gs.getD n 1 * O) (mul_mem (block_get_unitary gs hgs n) hO)

/-- Euclidean unitary evolution over the block list equals the Euclidean image of the state
produced by `runQueryBlocks`. -/
theorem blocks_evolution (gs : List (Matrix I I ℂ))
    (hgs : ∀ G ∈ gs, G ∈ Matrix.unitaryGroup I ℂ) (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) :
    UnitaryEvolution (blockEvolution gs hgs O hO) (toEuclidean_fromVec ψ) gs.length =
      toEuclidean_fromVec (runQueryBlocks O gs ψ) := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons G gs ih =>
    let htail := fun H hH => hgs H (List.mem_cons_of_mem G hH)
    rw [List.length_cons, evolution_shift]
    have hshift : (fun n => blockEvolution (G :: gs) hgs O hO (n + 1)) =
        blockEvolution gs htail O hO := by
      funext n
      apply LinearIsometryEquiv.ext
      intro x
      simp [blockEvolution, unitaryEuclidean_apply]
    rw [hshift]
    have hfirst : blockEvolution (G :: gs) hgs O hO 0 (toEuclidean_fromVec ψ) =
        toEuclidean_fromVec (G *ᵥ (O *ᵥ ψ)) := by
      simp [blockEvolution, unitaryEuclidean_apply, Matrix.mulVec_mulVec, toEuclidean_fromVec]
    rw [hfirst]
    rw [ih htail]
    rfl

end Qatlib.Concepts.QueryComplexity.DegreeMethod
