/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Independently sampled mixture paths

This module defines the circuit and ordered operator product associated with a finite sequence
of mixture choices. It proves their execution semantics and costs, then expresses an iterated
mixture as an average over independently sampled paths. These identities describe the
fresh-sample circuit model used in random compilation [Campbell2019].

## Main statements

* `mixture_path_circuit_semantics_cost`: path execution, zero queries, gate count, and
  conditional unitarity.
* `mixturePowerMap_eq_sum_paths`: expansion as a weighted sum of path conjugation maps.
* `mixture_fresh_paths_actual_output` and `mixture_fresh_paths_reference_output`: system and
  finite-reference output formulas.

## References

* [Campbell, 2019][Campbell2019]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ReferenceError.MixturePaths

open Matrix

open scoped Matrix.Norms.L2Operator ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The circuit applying `U (ω i)` in increasing sample-index order. -/
def mixturePathCircuit {J : Type} {D : ℕ} [Fintype J] [DecidableEq J]
    (U : J → Operator D) {n : ℕ} (ω : Fin n → J) : Circuit (Fin D) :=
  List.ofFn (fun i => Step.gate (U (ω i)))

/-- The ordered product of the sampled operators, with each later operator multiplying on the
left. -/
noncomputable def mixturePathOperator {J : Type} {D : ℕ} [Fintype J] [DecidableEq J]
    (U : J → Operator D) {n : ℕ} (ω : Fin n → J) : Operator D :=
  (List.ofFn (fun i => U (ω i))).foldl (fun A B => B * A) 1

/-- A matrix factor on the right of the initial accumulator remains on the right throughout a
left-multiplication fold. -/
private lemma foldl_append_right {D : ℕ} (L : List (Operator D)) (A B : Operator D) :
    L.foldl (fun X Y => Y * X) (A * B) = (L.foldl (fun X Y => Y * X) A) * B := by
  induction L generalizing A B with
  | nil => rfl
  | cons M L ih =>
      rw [List.foldl_cons, List.foldl_cons, ← Matrix.mul_assoc, ih]

/-- A left-multiplication fold starting at `X` equals the fold starting at identity followed by
multiplication by `X`. -/
private lemma foldl_init {D : ℕ} (L : List (Operator D)) (X : Operator D) :
    L.foldl (fun A B => B * A) X = (L.foldl (fun A B => B * A) 1) * X := by
  rw [← foldl_append_right L 1 X, Matrix.one_mul]

/-- Running a list of gate steps equals applying their ordered matrix product. -/
private theorem run_mapGate {D : ℕ} (L : List (Operator D)) (ψ : QState (Fin D)) :
    Run 1 (L.map Step.gate) ψ = ApplyGate (L.foldl (fun A B => B * A) 1) ψ := by
  induction L generalizing ψ with
  | nil =>
      rw [List.map_nil]
      exact (Matrix.one_mulVec ψ).symm
  | cons M L ih =>
      rw [List.map_cons, run_gate, ih, List.foldl_cons, foldl_init L (M * 1), Matrix.mul_one]
      simp only [ApplyGate, ← Matrix.mulVec_mulVec]

/-- A circuit consisting entirely of gate steps has zero query count. -/
private theorem queryCount_mapGate {D : ℕ} (L : List (Operator D)) :
    QueryCount (L.map Step.gate) = 0 := by
  induction L with
  | nil => rfl
  | cons M L ih => exact ih

/-- The gate count of a list of gate steps equals the list length. -/
private theorem gateCount_mapGate {D : ℕ} (L : List (Operator D)) :
    GateCount (L.map Step.gate) = L.length := by
  induction L with
  | nil => rfl
  | cons M L ih => simp [ih]

/-- The sampled path circuit equals the sampled operator list mapped to gate steps. -/
theorem mixturePathCircuit_eq_map {J : Type} {D : ℕ} [Fintype J] [DecidableEq J]
    (U : J → Operator D) {n : ℕ} (ω : Fin n → J) :
    mixturePathCircuit U ω = (List.ofFn (fun i => U (ω i))).map Step.gate :=
  List.ofFn_comp' _ _

/-- A sampled path circuit applies its path operator, uses zero queries, and has exactly `n`
gates. It is unitary when every branch operator is unitary. -/
theorem mixture_path_circuit_semantics_cost {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (U : J → Operator D) (n : ℕ) (ω : Fin n → J) (ψ : QState (Fin D)) :
    Run 1 (mixturePathCircuit U ω) ψ = ApplyGate (mixturePathOperator U ω) ψ ∧
    QueryCount (mixturePathCircuit U ω) = 0 ∧
    GateCount (mixturePathCircuit U ω) = n ∧
    ((∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) → IsUnitaryCircuit (mixturePathCircuit U ω)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mixturePathCircuit_eq_map]
    exact run_mapGate _ ψ
  · rw [mixturePathCircuit_eq_map, queryCount_mapGate]
  · rw [mixturePathCircuit_eq_map, gateCount_mapGate, List.length_ofFn]
  · intro hU V hV
    rw [mixturePathCircuit, List.mem_ofFn] at hV
    obtain ⟨i, hi⟩ := hV
    cases hi
    exact hU (ω i)

/-- Prepending a sampled branch puts its operator on the right of the remaining path product. -/
theorem mixturePathOperator_cons {J : Type} {D : ℕ} [Fintype J] [DecidableEq J]
    (U : J → Operator D) {n : ℕ} (j : J) (ω : Fin n → J) :
    mixturePathOperator U (Fin.cons j ω) = mixturePathOperator U ω * U j := by
  have hlist : List.ofFn (fun i => U ((Fin.cons j ω : Fin (n + 1) → J) i))
      = U j :: List.ofFn (fun i => U (ω i)) := by
    simp_rw [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  rw [mixturePathOperator, hlist, List.foldl_cons, foldl_init, Matrix.mul_one]
  rfl

/-- The probability of a path with a prepended sample factors into the first-sample probability
and the remaining path probability. -/
theorem independentSampleLaw_prob_cons {J : Type} [Fintype J] [DecidableEq J]
    (d : FinDist J) {n : ℕ} (j : J) (ω : Fin n → J) :
    (independentSampleLaw (fun _ : Fin (n + 1) => d)).prob (Fin.cons j ω)
      = d.prob j * (independentSampleLaw (fun _ : Fin n => d)).prob ω := by
  have hprod : (independentSampleLaw (fun _ : Fin (n + 1) => d)).prob (Fin.cons j ω)
      = ∏ i : Fin (n + 1), d.prob ((Fin.cons j ω : Fin (n + 1) → J) i) := rfl
  rw [hprod, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [← (independent_sample_product_law (fun _ : Fin n => d) ω).1]

/-- The iterated mixture map equals the sum of path conjugation maps weighted by the independent
sample law. -/
theorem mixturePowerMap_eq_sum_paths {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (n : ℕ) :
    mixturePowerMap d U n = ∑ ω : Fin n → J,
      ((independentSampleLaw (fun _ : Fin n => d)).prob ω : ℂ) •
        conjBranch (mixturePathOperator U ω) := by
  induction n with
  | zero =>
      apply LinearMap.ext
      intro ρ
      have hP : mixturePathOperator U (default : Fin 0 → J) = 1 := by
        simp [mixturePathOperator, List.ofFn_zero]
      have hprob : ((independentSampleLaw (fun _ : Fin 0 => d)).prob
          (default : Fin 0 → J) : ℂ) = 1 := by
        simp [(independent_sample_product_law _ _).1, Fin.prod_univ_zero]
      have hsingle : ∑ ω : Fin 0 → J,
          ((independentSampleLaw (fun _ : Fin 0 => d)).prob ω : ℂ) •
            (mixturePathOperator U ω * ρ * (mixturePathOperator U ω)ᴴ)
          = ρ := by
        rw [Finset.univ_unique, Finset.sum_singleton, hP, hprob, Matrix.one_mul,
          Matrix.conjTranspose_one, Matrix.mul_one, one_smul]
      simp only [mixturePowerMap, LinearMap.id_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, conjBranch_apply]
      rw [hsingle]
  | succ n ih =>
      apply LinearMap.ext
      intro ρ
      have hstep : mixturePowerMap d U (n + 1) ρ
          = mixturePowerMap d U n (ChannelMixture d U ρ) := rfl
      have hexpand : ∀ ω : Fin n → J,
          (mixturePathOperator U ω * (ChannelMixture d U ρ)
            * (mixturePathOperator U ω)ᴴ)
          = ∑ j : J, ((d.prob j : ℂ)) •
              (mixturePathOperator U ω * U j * ρ * (U j)ᴴ * (mixturePathOperator U ω)ᴴ) := by
        intro ω
        have hC : ChannelMixture d U ρ
            = ∑ j : J, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ) := rfl
        rw [hC, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      rw [hstep, ih]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, conjBranch_apply, hexpand,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm, ← (Fin.consEquiv (fun _ : Fin (n + 1) => J)).sum_comp
        (fun ω' : Fin (n + 1) → J =>
          ((independentSampleLaw (fun _ : Fin (n + 1) => d)).prob ω' : ℂ) •
            (mixturePathOperator U ω' * ρ * (mixturePathOperator U ω')ᴴ)),
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ω _ => ?_
      rw [show (Fin.consEquiv (fun _ : Fin (n + 1) => J)) (j, ω) = Fin.cons j ω from rfl,
        independentSampleLaw_prob_cons d j ω, mixturePathOperator_cons,
        Matrix.conjTranspose_mul, ← Complex.ofReal_mul, mul_comm]
      simp only [Matrix.mul_assoc, Complex.ofReal_mul, mul_comm]

/-- The iterated mixture output equals the independent-law average of conjugations by actual
path operators. This identifies the fresh-sample output used in [Campbell2019]. -/
theorem mixture_fresh_paths_actual_output {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D)
    (n : ℕ) (ρ : Operator D) :
    mixturePowerMap d U n ρ = ∑ ω : Fin n → J,
      ((independentSampleLaw (fun _ : Fin n => d)).prob ω : ℂ) •
        (mixturePathOperator U ω * ρ * (mixturePathOperator U ω)ᴴ) := by
  rw [mixturePowerMap_eq_sum_paths d U n]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, conjBranch_apply]

/-- The iterated reference mixture equals the independent-law average of conjugations by path
operators tensored with the reference identity. -/
theorem mixture_fresh_paths_reference_output {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D)
    (n r : ℕ) (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    referenceMixturePower d U r n ρ = ∑ ω : Fin n → J,
      ((independentSampleLaw (fun _ : Fin n => d)).prob ω : ℂ) •
        (TensorGate (mixturePathOperator U ω) (1 : Operator r) * ρ *
          (TensorGate (mixturePathOperator U ω) (1 : Operator r))ᴴ) := by
  rw [← tensorLeft_mixturePowerMap d U r n ρ, mixturePowerMap_eq_sum_paths d U n,
    tensorLeft_sum]
  exact Finset.sum_congr rfl fun ω _ => by
    rw [tensorLeft_smul, tensorLeft_conjBranch]

end Qatlib.Concepts.ReferenceError.MixturePaths
