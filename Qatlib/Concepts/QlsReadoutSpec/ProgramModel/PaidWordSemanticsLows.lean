/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.ProgramModel.PaidWordSemanticsStat

/-!
# Semantics of paid oracle words

This module proves algebraic and probabilistic laws for paid oracle words, including sequential
composition, adjoints, legality, and oracle-call counts. Executing a legal word on a normalized
clean input produces a normalized state whose unconditional output density is positive
semidefinite with trace one. Related mathematical background is given in [Watrous2018].

## Main statements

* `wordMatrix_append`: Execution order for concatenated words.
* `wordMatrix_wordAdjoint`: Matrix semantics of the adjoint word.
* `Clause1PaidWordSemantics_answer`: Combined paid-word semantics theorem.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QlsReadoutSpec.Amplification

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.ProgramModel

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The matrix of a paid-word step, using a known gate directly or a controlled oracle or
adjoint for a call. -/
private def stepMatrix {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (oracles : ℕ → Matrix H H ℂ) (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) :
    Matrix (Space H r) (Space H r) ℂ :=
  match s with
  | .known U => U
  | .call i T adj => controlled (if adj then (oracles i)ᴴ else oracles i) T

/-- The adjoint of a paid-word step, conjugate-transposing known gates and reversing the adjoint
flag of oracle calls. -/
private def adjStep {H : Type} {r : ℕ} (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r :=
  match s with
  | .known U => .known Uᴴ
  | .call i T a => .call i T (!a)

/-- The matrix of a paid word is the product of its step matrices in reverse list order. -/
theorem wordMatrix_eq_map {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (oracles : ℕ → Matrix H H ℂ) (C : Word H r) :
    wordMatrix oracles C = (C.map (stepMatrix oracles)).reverse.prod := rfl

/-- The adjoint word is obtained by reversing the word and taking each step's adjoint. -/
theorem wordAdjoint_eq {H : Type} {r : ℕ} (C : Word H r) :
    wordAdjoint C = C.reverse.map adjStep := rfl

/-- Conjugate transpose commutes with forming a controlled matrix on a fixed control set. -/
theorem controlled_conjTranspose {H : Type} [DecidableEq H] {r : ℕ}
    (U : Matrix H H ℂ) (T : Finset (Fin r)) :
    (controlled U T)ᴴ = controlled Uᴴ T := by
  ext p q
  rcases p with ⟨h, k⟩
  rcases q with ⟨h', k'⟩
  show star (if k' = k then (if k' ∈ T then U h' h else if h' = h then (1 : ℂ) else 0) else 0)
      = if k = k' then (if k ∈ T then Uᴴ h h' else if h = h' then (1 : ℂ) else 0) else 0
  by_cases hk : k = k'
  · rw [← hk]
    by_cases hT : k ∈ T
    · simp [hT, Matrix.conjTranspose_apply]
    · by_cases hh : h = h'
      · rw [← hh]
        simp [hT]
      · have hh2 : h' ≠ h := fun e => hh e.symm
        simp [hT, hh, hh2, star_zero]
  · have hk2 : k' ≠ k := fun e => hk e.symm
    simp [hk, hk2]

/-- Rows of a matrix whose product with its conjugate transpose is the identity have the stated
Kronecker-delta inner products. -/
theorem sum_mul_star_conjTranspose {H : Type} [Fintype H] [DecidableEq H] {U : Matrix H H ℂ}
    (hU : U * Uᴴ = 1) (h h' : H) :
    (∑ g, U h g * star (U h' g)) = if h = h' then (1 : ℂ) else 0 := by
  have key : (∑ g, U h g * star (U h' g)) = (U * Uᴴ) h h' := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [key, hU, Matrix.one_apply]

/-- The sum of products of two Kronecker-delta rows equals the Kronecker delta of their row
indices. -/
theorem sum_ite_delta {H : Type} [Fintype H] [DecidableEq H] (h h' : H) :
    (∑ g, ((if h = g then (1 : ℂ) else 0)) * ((if h' = g then (1 : ℂ) else 0)))
    = if h = h' then (1 : ℂ) else 0 := by
  by_cases hh : h = h'
  · subst hh
    have hterm : ∀ g : H,
        ((if h = g then (1 : ℂ) else 0)) * ((if h = g then (1 : ℂ) else 0))
        = if h = g then (1 : ℂ) else 0 := by
      intro g
      by_cases hg : h = g <;> simp [hg]
    rw [Finset.sum_congr rfl fun g _ => hterm g]
    rw [Finset.sum_ite_eq]
    simp
  · have hterm : ∀ g : H,
        ((if h = g then (1 : ℂ) else 0)) * ((if h' = g then (1 : ℂ) else 0)) = 0 := by
      intro g
      by_cases hg : h = g
      · have hg2 : ¬ h' = g := fun e => hh (hg.trans e.symm)
        simp [hg, hg2]
      · simp [hg]
    rw [Finset.sum_congr rfl fun g _ => hterm g, if_neg hh]
    simp

/-- A controlled unitary multiplied by its conjugate transpose is the identity. -/
theorem controlled_mul_conjTranspose {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) (T : Finset (Fin r)) :
    controlled U T * (controlled U T)ᴴ = 1 := by
  have hUU : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff).mp hU
  have hUapp := sum_mul_star_conjTranspose hUU
  ext p q
  rcases p with ⟨h, k⟩
  rcases q with ⟨h', k'⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have hprod : (∑ x : H × Fin r,
      controlled U T (h, k) x * star (controlled U T (h', k') x))
      = if k = k' then (if h = h' then (1 : ℂ) else 0) else 0 := by
    rw [Fintype.sum_prod_type]
    show (∑ g : H, ∑ j : Fin r,
        (if k = j then (if k ∈ T then U h g else if h = g then (1 : ℂ) else 0) else 0)
          * star (if k' = j then (if k' ∈ T then U h' g else if h' = g then (1 : ℂ) else 0)
            else 0)) = _
    by_cases hk : k = k'
    · rw [← hk]
      rw [if_pos rfl]
      have hstep : ∀ g : H,
          (∑ j : Fin r,
            (if k = j then (if k ∈ T then U h g else if h = g then (1 : ℂ) else 0) else 0)
              * star (if k = j then (if k ∈ T then U h' g else if h' = g then (1 : ℂ) else 0)
                else 0))
          = (if k ∈ T then U h g else if h = g then (1 : ℂ) else 0)
              * star (if k ∈ T then U h' g else if h' = g then (1 : ℂ) else 0) := by
        intro g
        have hstepj : ∀ j : Fin r,
            (if k = j then (if k ∈ T then U h g else if h = g then (1 : ℂ) else 0) else 0)
              * star (if k = j then (if k ∈ T then U h' g else if h' = g then (1 : ℂ) else 0)
                else 0)
            = if k = j then
                ((if k ∈ T then U h g else if h = g then (1 : ℂ) else 0)
                  * star (if k ∈ T then U h' g else if h' = g then (1 : ℂ) else 0)) else 0 := by
          intro j
          by_cases hkj : k = j <;> simp [hkj, star_zero]
        rw [Finset.sum_congr rfl fun j _ => hstepj j]
        rw [Finset.sum_ite_eq]
        simp
      rw [Finset.sum_congr rfl fun g _ => hstep g]
      by_cases hT : k ∈ T
      · simp only [hT, if_true]
        exact hUapp h h'
      · simp only [hT, if_false]
        have hrew : ∀ x : H,
            ((if h = x then (1 : ℂ) else 0)) * star ((if h' = x then (1 : ℂ) else 0))
            = ((if h = x then (1 : ℂ) else 0)) * ((if h' = x then (1 : ℂ) else 0)) := by
          intro x
          by_cases hx : h = x <;> by_cases hx2 : h' = x <;> simp [hx, hx2, star_zero]
        rw [Finset.sum_congr rfl fun x _ => hrew x]
        exact sum_ite_delta h h'
    · have hz : (∑ g : H, ∑ j : Fin r,
          (if k = j then (if k ∈ T then U h g else if h = g then (1 : ℂ) else 0) else 0)
            * star (if k' = j then (if k' ∈ T then U h' g else if h' = g then (1 : ℂ) else 0)
              else 0)) = 0 := by
        refine Finset.sum_eq_zero fun g _ => ?_
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases h1 : k = j
        · have h2 : ¬ k' = j := fun e => hk (h1.trans e.symm)
          simp [h1, h2]
        · simp [h1]
      rw [hz, if_neg hk]
  rw [hprod]
  by_cases hk : k = k' <;> by_cases hh : h = h' <;> simp [hk, hh]

/-- Controlling a unitary matrix on a finite set of control labels gives a unitary matrix. -/
theorem controlled_unitary {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) (T : Finset (Fin r)) :
    controlled U T ∈ Matrix.unitaryGroup (Space H r) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact controlled_mul_conjTranspose hU T

/-- A paid-word step has unitary matrix semantics when its known gate is unitary or its oracle
index is in the unitary-oracle range. -/
theorem stepMatrix_unitary {H : Type} [Fintype H] [DecidableEq H] {r slots : ℕ}
    (oracles : ℕ → Matrix H H ℂ) (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r)
    (hOracle : ∀ j < slots, oracles j ∈ Matrix.unitaryGroup H ℂ)
    (h : match s with | .known U => U ∈ Matrix.unitaryGroup _ ℂ | .call i _ _ => i < slots) :
    stepMatrix oracles s ∈ Matrix.unitaryGroup (Space H r) ℂ := by
  cases s with
  | known U => exact h
  | call i T adj =>
    have hi : i < slots := h
    have hU : oracles i ∈ Matrix.unitaryGroup H ℂ := hOracle i hi
    cases adj with
    | true => exact controlled_unitary (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hU) T
    | false => exact controlled_unitary hU T

/-- A legal paid word over unitary oracles has unitary matrix semantics. -/
theorem wordMatrix_unitary {H : Type} [Fintype H] [DecidableEq H] {r slots : ℕ}
    (oracles : ℕ → Matrix H H ℂ) (C : Word H r)
    (hOracle : ∀ j < slots, oracles j ∈ Matrix.unitaryGroup H ℂ)
    (hlegal : legal slots C) :
    wordMatrix oracles C ∈ Matrix.unitaryGroup (Space H r) ℂ := by
  rw [wordMatrix_eq_map]
  refine (Matrix.unitaryGroup (Space H r) ℂ).list_prod_mem ?_
  intro m hm
  have hex : ∃ s ∈ C, stepMatrix oracles s = m := by
    rw [← List.mem_map, ← List.mem_reverse]
    exact hm
  obtain ⟨s, hs, rfl⟩ := hex
  exact stepMatrix_unitary oracles s hOracle (hlegal s hs)

/-- The matrix of concatenated paid words is the matrix of the second word multiplied by that of
the first. -/
theorem wordMatrix_append {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (oracles : ℕ → Matrix H H ℂ) (C D : Word H r) :
    wordMatrix oracles (C ++ D) = wordMatrix oracles D * wordMatrix oracles C := by
  rw [wordMatrix_eq_map, wordMatrix_eq_map, wordMatrix_eq_map]
  simp only [List.map_append, List.reverse_append, List.prod_append]

/-- The matrix of an adjoint step is the conjugate transpose of the original step matrix. -/
theorem stepMatrix_adjStep {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (oracles : ℕ → Matrix H H ℂ) (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) :
    stepMatrix oracles (adjStep s) = (stepMatrix oracles s)ᴴ := by
  cases s with
  | known U => rfl
  | call i T a =>
    cases a with
    | true =>
      have h1 : stepMatrix oracles (adjStep (Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.call i T true))
          = controlled (oracles i) T := rfl
      have h2 : (stepMatrix oracles (Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.call i T true))ᴴ
          = (controlled (oracles i)ᴴ T)ᴴ := rfl
      rw [h1, h2, ← controlled_conjTranspose, Matrix.conjTranspose_conjTranspose]
    | false =>
      have h1 : stepMatrix oracles (adjStep (Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.call i T false))
          = controlled (oracles i)ᴴ T := rfl
      have h2 : (stepMatrix oracles (Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.call i T false))ᴴ
          = (controlled (oracles i) T)ᴴ := rfl
      rw [h1, h2]
      exact (controlled_conjTranspose (oracles i) T).symm

/-- The product of the conjugate transposes of a list of matrices equals the conjugate transpose
of the product in reverse order. -/
theorem prod_map_conjTranspose {n : Type} [Fintype n] [DecidableEq n]
    (L : List (Matrix n n ℂ)) :
    (L.map (fun m => mᴴ)).prod = (L.reverse.prod)ᴴ := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.reverse_cons, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one, Matrix.conjTranspose_mul]

/-- The matrix of an adjoint paid word is the conjugate transpose of the original word matrix. -/
theorem wordMatrix_wordAdjoint {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (oracles : ℕ → Matrix H H ℂ) (C : Word H r) :
    wordMatrix oracles (wordAdjoint C) = (wordMatrix oracles C)ᴴ := by
  rw [wordMatrix_eq_map, wordAdjoint_eq, wordMatrix_eq_map, List.map_map]
  have hcomp : ∀ s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r,
      stepMatrix oracles (adjStep s) = (stepMatrix oracles s)ᴴ :=
    fun s => stepMatrix_adjStep (r := r) oracles s
  have hmap1 : C.reverse.map (stepMatrix oracles ∘ adjStep)
      = C.reverse.map (fun s => (stepMatrix oracles s)ᴴ) :=
    List.map_congr_left fun s _ => hcomp s
  rw [hmap1, List.map_reverse, List.reverse_reverse]
  have hmap2 : C.map (fun s => (stepMatrix oracles s)ᴴ)
      = (C.map (stepMatrix oracles)).map (fun m => mᴴ) := by
    rw [List.map_map]
    rfl
  rw [hmap2]
  exact prod_map_conjTranspose _

/-- Taking the adjoint of a legal paid word preserves legality. -/
theorem legal_wordAdjoint {H : Type} [Fintype H] [DecidableEq H] {r slots : ℕ}
    (C : Word H r) (h : legal slots C) : legal slots (wordAdjoint C) := by
  intro t ht
  rw [wordAdjoint_eq, List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  rw [List.mem_reverse] at hs
  have hP := h s hs
  cases s with
  | known U =>
    show Uᴴ ∈ Matrix.unitaryGroup (Space H r) ℂ
    exact Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hP
  | call i T a =>
    show i < slots
    exact hP

/-- Taking the adjoint of a paid word preserves the number of calls to each oracle slot. -/
theorem calls_wordAdjoint {H : Type} {r : ℕ} (C : Word H r) (j : ℕ) :
    calls (wordAdjoint C) j = calls C j := by
  show (wordAdjoint C).countP
        (fun s => match s with | .call i _ _ => decide (i = j) | _ => false)
      = C.countP (fun s => match s with | .call i _ _ => decide (i = j) | _ => false)
  rw [wordAdjoint_eq, List.countP_map, List.countP_reverse]
  congr 1
  funext s
  cases s with
  | known U => rfl
  | call i T a =>
    cases a with
    | true => rfl
    | false => rfl

/-- The number of calls to an oracle slot in concatenated words is the sum of their call counts. -/
theorem calls_append {H : Type} {r : ℕ} (C D : Word H r) (j : ℕ) :
    calls (C ++ D) j = calls C j + calls D j := by
  show (C ++ D).countP
        (fun s => match s with | .call i _ _ => decide (i = j) | _ => false)
      = C.countP (fun s => match s with | .call i _ _ => decide (i = j) | _ => false)
        + D.countP (fun s => match s with | .call i _ _ => decide (i = j) | _ => false)
  exact List.countP_append

/-- The clean embedding into a positive-size auxiliary register preserves normalization. -/
theorem clean_normalized {H : Type} [Fintype H] {r : ℕ} (hr : 0 < r) (ω : QState H)
    (hω : Normalized ω) : Normalized (clean r hr ω) := by
  show ∑ p : H × Fin r, ‖clean r hr ω p‖ ^ 2 = 1
  have hsplit : (∑ p : H × Fin r, ‖clean r hr ω p‖ ^ 2)
      = ∑ h : H, ∑ k : Fin r, ‖(if k = ⟨0, hr⟩ then ω h else (0 : ℂ))‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun h _ =>
      Finset.sum_congr rfl fun k _ => by
        show ‖clean r hr ω (h, k)‖ ^ 2 = _
        simp only [clean]
  rw [hsplit]
  have hinner : ∀ h : H,
      (∑ k : Fin r, ‖(if k = ⟨0, hr⟩ then ω h else (0 : ℂ))‖ ^ 2) = ‖ω h‖ ^ 2 := by
    intro h
    rw [Finset.sum_eq_single ⟨0, hr⟩]
    · simp
    · intro k _ hk
      simp [hk]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [Finset.sum_congr rfl fun h _ => hinner h]
  exact hω

/-- With identity output map, the branch at a control label is the corresponding slice of the
state. -/
theorem outputBranch_one {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (ψ : QState (Space H r)) (k : Fin r) :
    outputBranch (1 : Matrix H H ℂ) ψ k = fun h => ψ (h, k) := by
  show (1 : Matrix H H ℂ)ᴴ *ᵥ (fun h => ψ (h, k)) = _
  rw [Matrix.conjTranspose_one, Matrix.one_mulVec]

/-- For a normalized state, the output mass with identity output map over all control labels is
one. -/
theorem outputMass_one_univ {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (ψ : QState (Space H r)) (hψ : Normalized ψ) :
    outputMass (1 : Matrix H H ℂ) Finset.univ ψ = 1 := by
  have hbr : ∀ k : Fin r, outputBranch (1 : Matrix H H ℂ) ψ k = fun h => ψ (h, k) :=
    fun k => outputBranch_one ψ k
  show ∑ k ∈ Finset.univ, (normVec (outputBranch (1 : Matrix H H ℂ) ψ k)) ^ 2 = 1
  simp only [hbr, normVec, norm_toEuclidean_fromVec_sq]
  have hswap : (∑ k : Fin r, ∑ h : H, ‖ψ (h, k)‖ ^ 2)
      = (∑ h : H, ∑ k : Fin r, ‖ψ (h, k)‖ ^ 2) := Finset.sum_comm
  rw [hswap, ← Fintype.sum_prod_type (fun p : H × Fin r => ‖ψ p‖ ^ 2)]
  exact hψ

/-- For a normalized state, the output density with identity output map over all control labels
is the sum of the pure densities of its slices. -/
theorem outputDensity_one_univ {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (ψ : QState (Space H r)) (hψ : Normalized ψ) :
    outputDensity (1 : Matrix H H ℂ) Finset.univ ψ
      = ∑ k : Fin r, pureDensity (fun h => ψ (h, k)) := by
  have hmass : outputMass (1 : Matrix H H ℂ) Finset.univ ψ = 1 :=
    outputMass_one_univ ψ hψ
  have hbr : ∀ k : Fin r, outputBranch (1 : Matrix H H ℂ) ψ k = fun h => ψ (h, k) :=
    fun k => outputBranch_one ψ k
  show ((outputMass (1 : Matrix H H ℂ) Finset.univ ψ : ℂ)⁻¹)
      • ∑ k ∈ Finset.univ, pureDensity (outputBranch (1 : Matrix H H ℂ) ψ k) = _
  rw [hmass]
  show ((1 : ℂ)⁻¹) • ∑ k ∈ Finset.univ, pureDensity (outputBranch (1 : Matrix H H ℂ) ψ k) = _
  rw [inv_one, one_smul]
  exact Finset.sum_congr rfl fun k _ => by rw [hbr k]

/-- The pure-state density matrix equals the outer-product matrix. -/
theorem pureDensity_eq_outerProduct {I : Type} (ψ : QState I) :
    pureDensity ψ = outerProduct ψ := rfl

/-- The unconditional output density with identity output map is positive semidefinite for a
normalized state. -/
theorem outputDensity_posSemidef {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (ψ : QState (Space H r)) (hψ : Normalized ψ) :
    (outputDensity (1 : Matrix H H ℂ) Finset.univ ψ).PosSemidef := by
  rw [outputDensity_one_univ ψ hψ]
  refine posSemidef_sum _ ?_
  intro k _
  rw [pureDensity_eq_outerProduct]
  exact outerProduct_posSemidef _

/-- The unconditional output density with identity output map has trace one for a normalized
state. -/
theorem outputDensity_trace {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (ψ : QState (Space H r)) (hψ : Normalized ψ) :
    Matrix.trace (outputDensity (1 : Matrix H H ℂ) Finset.univ ψ) = 1 := by
  rw [outputDensity_one_univ ψ hψ, Matrix.trace_sum]
  have htr : ∀ k : Fin r,
      Matrix.trace (pureDensity (fun h => ψ (h, k)))
        = ((∑ h : H, ‖ψ (h, k)‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [pureDensity_eq_outerProduct, trace_outerProduct]
  rw [Finset.sum_congr rfl fun k _ => htr k, ← Complex.ofReal_sum]
  have hswap : (∑ k : Fin r, ∑ h : H, ‖ψ (h, k)‖ ^ 2)
      = (∑ p : H × Fin r, ‖ψ p‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hswap, hψ]
  norm_num

/-- Running a paid word applies its matrix to the clean embedding of the input state. -/
theorem run_eq_applyGate {H : Type} [Fintype H] [DecidableEq H] {r : ℕ} (hr : 0 < r)
    (oracles : ℕ → Matrix H H ℂ) (C : Word H r) (ω : QState H) :
    run hr oracles C ω = ApplyGate (wordMatrix oracles C) (clean r hr ω) := rfl

/-- Running a legal paid word over unitary oracles preserves normalization of the clean input. -/
theorem run_normalized {H : Type} [Fintype H] [DecidableEq H] {r slots : ℕ}
    (hr : 0 < r) (oracles : ℕ → Matrix H H ℂ) (C : Word H r) (ω : QState H)
    (hOracle : ∀ j < slots, oracles j ∈ Matrix.unitaryGroup H ℂ)
    (hlegal : legal slots C) (hω : Normalized ω) :
    Normalized (run hr oracles C ω) := by
  rw [run_eq_applyGate]
  exact normalized_applyGate (wordMatrix_unitary oracles C hOracle hlegal)
    (clean_normalized hr ω hω)

/-- Legal paid words over unitary oracles satisfy the stated unitarity, composition, adjoint,
call-count, normalization, and unconditional-density laws. -/
theorem Clause1PaidWordSemantics_answer : Clause1PaidWordSemantics := by
  intro H _instF _instD r slots oracles C D horacle hlegal
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact wordMatrix_unitary oracles C horacle hlegal
  · exact wordMatrix_append oracles C D
  · exact wordMatrix_wordAdjoint oracles C
  · exact legal_wordAdjoint C hlegal
  · intro j
    exact ⟨calls_wordAdjoint C j, calls_append C D j⟩
  · intro hr ω hω
    have hrun : Normalized (run hr oracles C ω) :=
      run_normalized hr oracles C ω horacle hlegal hω
    exact ⟨hrun, outputMass_one_univ _ hrun, outputDensity_posSemidef _ hrun,
      outputDensity_trace _ hrun⟩

end Qatlib.Concepts.QlsReadoutSpec.ProgramModel
