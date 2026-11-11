/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Concepts.ProbabilityCore.Concentration.CubeQueryDefs
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeMvPolynomial
import Qatlib.Concepts.ProbabilityCore.DistributionAA.DegreeInfluenceBounds
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeProductPoincare
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSlicePoincare

/-!
# Query algorithms and cube influence

The module relates decision tree execution and finite cube laws to acceptance polynomials,
degree bounds, and influence estimates. It also bounds the acceptance degree and total influence
of normalized quantum query circuits with unitary gates.

The circuit degree statement implements the polynomial method of [BealsEtAl2001].

## Main statements

* `FiniteDecisionTree.polynomial_eval` and `FiniteDecisionTree.polynomial_degree`: correctness
  and degree of tree polynomials.
* `randomized_cube_degree`: the acceptance degree bound for randomized trees.
* `circuit_total_influence`: a total influence bound in terms of the circuit query count.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.Concentration
open Matrix
open scoped Classical BigOperators

namespace FiniteDecisionTree

/-- A leaf outputs its stored Boolean value. -/
@[simp] theorem output_leaf {n : ℕ} (b : Bool) (x : Fin n → Bool) : (leaf b).output x = b := rfl

/-- Executing a leaf makes no queries. -/
@[simp] theorem queries_leaf {n : ℕ} (b : Bool) (x : Fin n → Bool) : (leaf b).queries x = 0 := rfl

/-- A query node returns the output of the branch selected by the queried input bit. -/
theorem output_query {n : ℕ} (i : Fin n) (l r : FiniteDecisionTree n) (x : Fin n → Bool) :
    (query i l r).output x = if x i then r.output x else l.output x := by
  cases h : x i <;> simp [output, execute, h]

/-- A query node makes one query followed by the queries of the selected branch. -/
theorem queries_query {n : ℕ} (i : Fin n) (l r : FiniteDecisionTree n) (x : Fin n → Bool) :
    (query i l r).queries x = 1+(if x i then r.queries x else l.queries x) := by
  cases h : x i <;> simp [queries, execute, h, Nat.add_comm]

/-- The number of queries on any input is at most the tree depth. -/
theorem queries_le_depth {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool) :
    t.queries x ≤ t.depth := by
  induction t with
  | leaf b => simp [depth]
  | query i l r hl hr =>
    rw [queries_query]
    cases x i <;> simp only [Bool.false_eq_true, if_false, if_true, depth] <;> omega

/-- Every answer in an execution trace equals the corresponding input bit. -/
theorem execute_answers {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool) :
    ∀ v ∈ (t.execute x).2, v.2 = x v.1 := by
  induction t with
  | leaf b => simp [execute]
  | query i l r hl hr =>
    cases h : x i
    · simp only [execute, h, Bool.false_eq_true, if_false]
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · subst v; exact h.symm
      · exact hl v hv
    · simp only [execute, h, if_true]
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · subst v; exact h.symm
      · exact hr v hv

/-- Relabeling a tree and its input preserves the output and relabels each coordinate in the
execution trace. -/
theorem execute_relabel {n : ℕ} (e : Equiv.Perm (Fin n)) (t : FiniteDecisionTree n)
    (x : Fin n → Bool) :
    (t.relabel e).execute (fun i => x (e.symm i)) =
      ((t.execute x).1, (t.execute x).2.map (fun v => (e v.1,v.2))) := by
  induction t with
  | leaf b => rfl
  | query i l r hl hr =>
    cases h : x i <;> simp [relabel, execute, Equiv.symm_apply_apply, h, hl, hr]

/-- Relabeling query coordinates preserves tree depth. -/
theorem depth_relabel {n : ℕ} (e : Equiv.Perm (Fin n)) (t : FiniteDecisionTree n) :
    (t.relabel e).depth = t.depth := by
  induction t <;> simp_all [relabel, depth]

/-- A decision tree acceptance indicator lies in `[0, 1]`. -/
theorem accept_range {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool) :
    t.accept x ∈ Set.Icc 0 1 := by
  unfold accept
  split <;> norm_num

/-- Evaluating the tree polynomial on the zero and one encoding of an input gives its acceptance
indicator. -/
theorem polynomial_eval {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) t.polynomial = t.accept x := by
  induction t with
  | leaf b => cases b <;> simp [polynomial, accept, output, execute]
  | query i l r hl hr =>
    cases h : x i <;> simp [polynomial, h, hl, hr, accept, output, execute]

/-- The total degree of a tree acceptance polynomial is at most the tree depth. -/
theorem polynomial_degree {n : ℕ} (t : FiniteDecisionTree n) :
    t.polynomial.totalDegree ≤ t.depth := by
  induction t with
  | leaf b => cases b <;> simp [polynomial, depth]
  | query i l r hl hr =>
    have h1 : (1-(MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) (by simp))
    have hL := (MvPolynomial.totalDegree_mul (1-MvPolynomial.X i) l.polynomial).trans
      (Nat.add_le_add h1 hl)
    have hR := (MvPolynomial.totalDegree_mul (MvPolynomial.X i) r.polynomial).trans
      (Nat.add_le_add (show (MvPolynomial.X i : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 by simp) hr)
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le (hL.trans (Nat.add_le_add_left (Nat.le_max_left _ _) 1))
        (hR.trans (Nat.add_le_add_left (Nat.le_max_right _ _) 1)))

/-- A tree acceptance indicator has cube degree at most its depth. -/
theorem cube_degree {n : ℕ} (t : FiniteDecisionTree n) : CubeDegreeLE t.depth t.accept := by
  have h := cube_degree_of_mv_polynomial t.polynomial t.polynomial_degree
  have he : (fun x : Fin n → Bool => MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0)
      t.polynomial) = t.accept := funext t.polynomial_eval
  rwa [he] at h

end FiniteDecisionTree

/-- Expectation under `cubeLaw` equals the weighted cube expectation. -/
theorem cubeLaw_expect (n : ℕ) (w : (Fin n → Bool) → ℝ) (hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ) : (cubeLaw n w hw).expect f = cubeExpect n w f := rfl

/-- Variance under `cubeLaw` equals the weighted cube variance. -/
theorem cubeLaw_variance (n : ℕ) (w : (Fin n → Bool) → ℝ) (hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ) : (cubeLaw n w hw).variance f = cubeVar n w f := rfl

/-- The expected squared difference under a coordinate flip equals that coordinate's cube
influence. -/
theorem cubeLaw_influence (n : ℕ) (w : (Fin n → Bool) → ℝ) (hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    (cubeLaw n w hw).expect (fun x => (f x-f (cubeFlip x i))^2) = cubeInf n w f i := rfl

/-- The product Bernoulli cube law has point probabilities `muWeight p n`. -/
theorem biasedCubeLaw_prob (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) (x : Fin n → Bool) :
    (biasedCubeLaw n p hp).prob x = muWeight p n x := rfl

/-- Expectation under the biased cube law equals expectation with weight `muWeight p n`. -/
theorem biasedCubeLaw_expect (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (f : (Fin n → Bool) → ℝ) : (biasedCubeLaw n p hp).expect f = cubeExpect n (muWeight p n) f := rfl

/-- Every Boolean input has probability `2⁻ⁿ` under the cube law with bias one half. -/
theorem uniformCubeLaw_prob (n : ℕ) (x : Fin n → Bool) :
    (biasedCubeLaw n (1/2) (by constructor <;> norm_num)).prob x = (2 : ℝ)⁻¹^n := by
  rw [biasedCubeLaw_prob]
  simp only [muWeight, show (1 : ℝ)-1/2 = 1/2 by norm_num, ite_self]
  simp

/-- The slice cube law has point probabilities `sliceWeight n k`. -/
theorem sliceCubeLaw_prob (n k : ℕ) (hk : k ≤ n) (x : Fin n → Bool) :
    (sliceCubeLaw n k hk).prob x = sliceWeight n k x := rfl

/-- The randomized tree polynomial evaluates to the seed averaged acceptance probability. -/
theorem randomized_polynomial_eval {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (randomizedTreePolynomial p t) =
      randomizedTreeAccept p t x := by
  simp only [randomizedTreePolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, FiniteDecisionTree.polynomial_eval, randomizedTreeAccept, FinDist.expect]

/-- The randomized tree polynomial has total degree at most the maximum tree depth. -/
theorem randomized_polynomial_degree {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) :
    (randomizedTreePolynomial p t).totalDegree ≤ forestDepth t := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ω hω
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simp only [MvPolynomial.totalDegree_C, Nat.zero_add]
    exact (t ω).polynomial_degree.trans (Finset.le_sup (f := fun ω => (t ω).depth) hω))

/-- The acceptance function of randomized trees has cube degree at most their maximum depth. -/
theorem randomized_cube_degree {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) :
    CubeDegreeLE (forestDepth t) (randomizedTreeAccept p t) := by
  have h := cube_degree_of_mv_polynomial (randomizedTreePolynomial p t)
    (randomized_polynomial_degree p t)
  have he : (fun x : Fin n → Bool => MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0)
      (randomizedTreePolynomial p t)) = randomizedTreeAccept p t := funext (randomized_polynomial_eval p t)
  rwa [he] at h

/-- The seed averaged tree acceptance probability lies in `[0, 1]`. -/
theorem randomized_accept_range {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) (x : Fin n → Bool) :
    randomizedTreeAccept p t x ∈ Set.Icc 0 1 := by
  constructor
  · exact Finset.sum_nonneg (fun ω _ => mul_nonneg (p.nonneg ω) ((t ω).accept_range x).1)
  · calc
      _ ≤ ∑ ω, p.prob ω * 1 := Finset.sum_le_sum (fun ω _ =>
        mul_le_mul_of_nonneg_left ((t ω).accept_range x).2 (p.nonneg ω))
      _ = 1 := by simpa only [mul_one] using p.sum_one

/-- The seed averaged query count is nonnegative and at most the maximum tree depth. -/
theorem randomized_queries_bound {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) (x : Fin n → Bool) :
    0 ≤ randomizedTreeQueries p t x ∧ randomizedTreeQueries p t x ≤ forestDepth t := by
  constructor
  · exact Finset.sum_nonneg (fun ω _ => mul_nonneg (p.nonneg ω) (Nat.cast_nonneg _))
  · have hb (ω : Ω) : ((t ω).queries x : ℝ) ≤ forestDepth t := by
      have hd : (t ω).depth ≤ forestDepth t :=
        Finset.le_sup (f := fun z => (t z).depth) (Finset.mem_univ ω)
      exact_mod_cast ((t ω).queries_le_depth x).trans hd
    calc
      _ ≤ ∑ ω, p.prob ω * (forestDepth t : ℝ) := Finset.sum_le_sum (fun ω _ =>
        mul_le_mul_of_nonneg_left (hb ω) (p.nonneg ω))
      _ = _ := by rw [← Finset.sum_mul, p.sum_one, one_mul]

/-- Expectation under the seed and input product law is the iterated input and seed expectation. -/
theorem seed_input_expect {Ω : Type*} [Fintype Ω] {n : ℕ} (p : FinDist Ω)
    (q : FinDist (Fin n → Bool)) (g : Ω → (Fin n → Bool) → ℝ) :
    (seedInputLaw p q).expect (fun z => g z.1 z.2) = q.expect (fun x => p.expect (fun ω => g ω x)) := by
  simp only [FinDist.expect, seedInputLaw, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- A Boolean bit oracle circuit has acceptance cube degree at most twice its query count, as in
[BealsEtAl2001]. -/
theorem circuit_cube_degree (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (E : Finset (PolynomialWorkspace (Fin n) W)) :
    CubeDegreeLE (2*QueryCount C) (fun f =>
      MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E) := by
  obtain ⟨hd, _hm, he⟩ := acceptance_boolean_multilinearization_preserves_run C ψ E
  have h := cube_degree_of_mv_polynomial (booleanAcceptancePolynomial C ψ E) hd
  have hf : (fun f : Fin n → Bool => MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0)
      (booleanAcceptancePolynomial C ψ E)) =
      (fun f => MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E) := funext he
  rwa [hf] at h

/-- The total influence of a tree acceptance indicator is at most eight times its squared depth
under any cube probability weight. -/
theorem tree_total_influence {n : ℕ} (t : FiniteDecisionTree n)
    (w : (Fin n → Bool) → ℝ) (hw : CubeWeight n w) :
    cubeTotalInf n w t.accept ≤ 8*(t.depth : ℝ)^2 :=
  cube_total_inf_le hw t.accept_range t.cube_degree

/-- The total influence of randomized tree acceptance is at most eight times the squared maximum
tree depth. -/
theorem randomized_total_influence {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) (w : (Fin n → Bool) → ℝ)
    (hw : CubeWeight n w) :
    cubeTotalInf n w (randomizedTreeAccept p t) ≤ 8*(forestDepth t : ℝ)^2 :=
  cube_total_inf_le hw (randomized_accept_range p t) (randomized_cube_degree p t)

/-- A circuit with unitary gates and normalized initial state has acceptance probability in `[0,
1]`. -/
theorem circuit_accept_range (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (E : Finset (PolynomialWorkspace (Fin n) W))
    (hC : ∀ U, Step.gate U ∈ C → U ∈ Matrix.unitaryGroup (PolynomialWorkspace (Fin n) W) ℂ)
    (hψ : Normalized ψ) (f : Fin n → Bool) :
    MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E ∈ Set.Icc 0 1 := by
  refine ⟨measureProb_nonneg _ E, measureProb_le_one ?_ E⟩
  exact normalized_run _ (tensorGate_unitary (bitOracleOn_unitary f) (by simp)) C hC hψ

/-- For unitary gates and a normalized initial state, total acceptance influence is at most `8 *
(2 * QueryCount C)²` under any cube probability weight. -/
theorem circuit_total_influence (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (E : Finset (PolynomialWorkspace (Fin n) W))
    (hC : ∀ U, Step.gate U ∈ C → U ∈ Matrix.unitaryGroup (PolynomialWorkspace (Fin n) W) ℂ)
    (hψ : Normalized ψ) (w : (Fin n → Bool) → ℝ) (hw : CubeWeight n w) :
    cubeTotalInf n w (fun f => MeasureProb
      (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E) ≤
        8*((2*QueryCount C : ℕ) : ℝ)^2 :=
  cube_total_inf_le hw (circuit_accept_range n W C ψ E hC hψ) (circuit_cube_degree n W C ψ E)

end Qatlib.Concepts.ProbabilityCore.Concentration
