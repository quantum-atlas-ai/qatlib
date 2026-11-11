/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse

set_option backward.isDefEq.respectTransparency false

/-!
# QLSVerify20 — QSV vocabulary and the hybrid counting core

Fixed source: Somma–Subaşı, *Complexity of quantum state verification in the
quantum linear systems problem*, arXiv:2007.15698v2 (23 Feb 2021).

This file contains the shared model used by every claim of the paper:

* the QLSP instance data, its solution state `|x⟩ ∝ A⁺|b⟩`, the condition
  number `κ` and the solution norm `‖A⁻¹|b⟩‖` (Section II, Eq. (1));
* a quantum state verification protocol as a family of laws on execution
  transcripts with an output bit `r` and a controlled-preparation count
  `q_{A,b}` (Section III, Fig. 1);
* the two access models: `ControlledUnitaryAccess` (Fig. 1, `cU_b^{±1}`)
  and `PrepareMeasureAccess` (Fig. 2, fresh copies of `|b⟩`);
* the generic hybrid counting lemma (Appendix A, Eqs. (A5)–(A10)) in the
  purely probabilistic form used by Theorems 1, 3 and 4.

Boundary: this is the paper's abstract information-theoretic model. It does
not construct the controlled unitaries themselves; the quantitative distance
between `cU_b^{±1}` and `cU_{b'}^{±1}` enters through the access predicates.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLSVerify20.MainResults

open MeasureTheory Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.MixedFidelity.FidelityMetric

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-! ## QLSP instance data (Section II) -/

/-- Euclidean squared norm `∑_i ‖v i‖²` of an `n`-qubit state vector. -/
def stateNormSq (v : QState (Fin N)) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- Euclidean norm `√(∑_i ‖v i‖²)`; `QState` is a bare function, so the
generic `‖·‖` (sup norm) is not the physical norm and we spell it out. -/
def stateEuclideanNorm (v : QState (Fin N)) : ℝ := Real.sqrt (stateNormSq v)

/-- Euclidean distance between two state vectors, `‖|b⟩ − |b'⟩‖`. This is the
quantity controlled in Appendix A, Eq. (A21)–(A25). -/
def stateDistance (b b' : QState (Fin N)) : ℝ := stateEuclideanNorm (b - b')

/-- The condition number `κ = ‖A‖·‖A⁺‖` of a Hermitian operator (Section II:
`κ` is the ratio of the largest to the smallest absolute eigenvalue, and
`A` is assumed to have operator norm one). -/
def qlspConditionNumber (A : Operator N) : ℝ :=
  OperatorSpectralNorm A * OperatorSpectralNorm (matrixPseudoinverse A)

/-- The solution norm `‖A⁻¹|b⟩‖` of Section II and Eq. (A4). -/
def qlspSolutionNorm (A : Operator N) (b : QState (Fin N)) : ℝ :=
  stateEuclideanNorm (matrixPseudoinverse A *ᵥ b)

/-- The solution state `|x⟩ = A⁻¹|b⟩ / ‖A⁻¹|b⟩‖` of Eq. (1). -/
def qlspSolution (A : Operator N) (b : QState (Fin N)) : QState (Fin N) :=
  ((qlspSolutionNorm A b)⁻¹ : ℂ) • (matrixPseudoinverse A *ᵥ b)

/-! ## QSV protocols (Section III, Fig. 1) -/

/-- A quantum state verification protocol. `Ω` is the source of the
protocol's internal randomness (the coupled coin flips / measurement
outcomes), with law `law σ` for input state `σ`; `accept b σ ω` is the
output bit `r` of the execution `ω`; and `uses b σ ω` is `q_{A,b}`, the
number of controlled preparation unitaries `cU_b^{±1}` used on that
execution (Section III, around Eq. (5)).

The law is indexed only by the input state, not by the preparation state
`|b⟩`: the operations `E` and `E'` of two instances differ only by
`cU_b^{±1} → cU_{b'}^{±1}` and are compared on the same randomness (the
coupling used in the hybrid argument of Appendix A). -/
structure QsvProtocol (N : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- Law of the execution transcript for input state `σ`. -/
  law : QState (Fin N) → Measure Ω
  /-- Every execution law is a probability measure. -/
  isProbability : ∀ σ, IsProbabilityMeasure (law σ)
  /-- The output bit `r`; `true` means `r = 1` (accept). -/
  accept : QState (Fin N) → QState (Fin N) → Ω → Bool
  /-- `q_{A,b}`: controlled preparation unitaries used on the execution.
  The algorithms `E` and `E'` of two instances differ only in substituting
  `cU_b^{±1}` by `cU_{b'}^{±1}`; their classical control is identical, so the
  count is the same random variable on a coupled pair of executions and
  depends only on the input state `σ`. -/
  uses : QState (Fin N) → Ω → ℕ
  /-- The output bit is measurable. -/
  measurable_accept : ∀ b σ, Measurable (accept b σ)
  /-- The query count is measurable. -/
  measurable_uses : ∀ σ, Measurable (uses σ)

/-- Acceptance probability `Pr(r = 1)`. -/
def acceptProbability (P : QsvProtocol N Ω) (b σ : QState (Fin N)) : ℝ :=
  (P.law σ {ω | P.accept b σ ω = true}).toReal

/-- Acceptance probability restricted to executions using at most `t`
controlled preparation unitaries. -/
def acceptWithin (P : QsvProtocol N Ω) (b σ : QState (Fin N)) (t : ℝ) : ℝ :=
  (P.law σ {ω | (P.uses σ ω : ℝ) ≤ t ∧ P.accept b σ ω = true}).toReal

/-- Tail probability `Pr(q_{A,b} > t)`. -/
def tailProbability (P : QsvProtocol N Ω) (b σ : QState (Fin N)) (t : ℝ) : ℝ :=
  (P.law σ {ω | t < (P.uses σ ω : ℝ)}).toReal

/-- The QSV specification of Eq. (3), stated for a "good" set of states:
the protocol accepts every good state with probability at least `2/3` and
rejects every state at trace distance greater than `1/2` from the solution
with probability at most `1/3`. For Theorem 1 the good set is
`D_{ρ,x} ≤ 1/8`; for Theorem 4 it is `C(ρ) ≤ C_min` (Section VI). -/
def SatisfiesQsvSpec (P : QsvProtocol N Ω) (b x : QState (Fin N))
    (Good : QState (Fin N) → Prop) : Prop :=
  (∀ ρ, Good ρ → 2 / 3 ≤ acceptProbability P b ρ) ∧
  (∀ ρ, 1 / 2 < traceDistance (outerProduct ρ) (outerProduct x) →
    acceptProbability P b ρ ≤ 1 / 3)

/-- A protocol that implements QSV for every preparation state of the fixed
matrix `A` (Section III: the protocol on input `A` and `b` returns `E`). -/
def IsQsvProtocolFor (P : QsvProtocol N Ω) (A : Operator N) : Prop :=
  ∀ b : QState (Fin N), Normalized b →
    SatisfiesQsvSpec P b (qlspSolution A b)
      (fun ρ => traceDistance (outerProduct ρ) (outerProduct (qlspSolution A b)) ≤ 1 / 8)

/-- Access model of Fig. 1: two preparations that are `d` apart in Euclidean
distance give, on the same input and via the hybrid chain of Eqs. (A5)–(A10),
acceptance probabilities that differ by at most `t·d` on the executions using
at most `t` controlled unitaries. The diamond norm of the controlled
unitaries is bounded by `‖|b⟩ − |b'⟩‖` in Eqs. (A23)–(A25). -/
def ControlledUnitaryAccess (P : QsvProtocol N Ω) : Prop :=
  ∀ (b b' σ : QState (Fin N)) (t : ℝ),
    |acceptWithin P b σ t - acceptWithin P b' σ t| ≤ t * stateDistance b b'

/-- Access model of Fig. 2 (prepare-and-measure): replacing each fresh copy
of `|b⟩` by `|b'⟩` changes the truncated acceptance probability by at most
the trace distance of the copy registers, Eq. (D2)–(D4). -/
def PrepareMeasureAccess (P : QsvProtocol N Ω) : Prop :=
  ∀ (b b' σ : QState (Fin N)) (t : ℝ), 0 ≤ t →
    |acceptWithin P b σ t - acceptWithin P b' σ t| ≤
      Real.sqrt (t * (1 - ‖Inner b b'‖ ^ 2))

/-! ## Cost functions and the weaker QSV specification (Section VI) -/

/-- The cost function `C(ρ) = Tr(ρH)` of Section VI around Eq. (10). -/
def costValue (H : Operator N) (ρ : QState (Fin N)) : ℝ :=
  (outerProduct ρ * H).trace.re

/-- The threshold property required in Section VI: every state with
`C(ρ) ≤ Cmin` is within trace distance `1/8` of the solution. -/
def IsCostThreshold (H : Operator N) (x : QState (Fin N)) (Cmin : ℝ) : Prop :=
  ∀ ρ : QState (Fin N),
    costValue H ρ ≤ Cmin → traceDistance (outerProduct ρ) (outerProduct x) ≤ 1 / 8

/-- The weaker QSV specification of Eq. (10): accept good (low-cost) states
with probability at least `2/3`, reject states farther than `1/2` with
probability at most `1/3`. -/
def SatisfiesCostSpec (P : QsvProtocol N Ω) (b x : QState (Fin N))
    (H : Operator N) (Cmin : ℝ) : Prop :=
  (∀ ρ, costValue H ρ ≤ Cmin → 2 / 3 ≤ acceptProbability P b ρ) ∧
  (∀ ρ, 1 / 2 < traceDistance (outerProduct ρ) (outerProduct x) →
    acceptProbability P b ρ ≤ 1 / 3)

/-! ## Elementary metric facts -/

/-- The Euclidean norm is nonnegative. -/
theorem stateEuclideanNorm_nonneg (v : QState (Fin N)) : 0 ≤ stateEuclideanNorm v :=
  Real.sqrt_nonneg _

/-- Trace distance is symmetric. -/
theorem traceDistance_comm (ρ σ : Operator N) : traceDistance ρ σ = traceDistance σ ρ := by
  unfold traceDistance
  rw [← Matrix.traceNorm_neg, neg_sub]

/-- Trace distance satisfies the triangle inequality. -/
theorem traceDistance_triangle (ρ σ τ : Operator N) :
    traceDistance ρ τ ≤ traceDistance ρ σ + traceDistance σ τ := by
  unfold traceDistance
  have h := Matrix.traceNorm_add_le (ρ - σ) (σ - τ)
  have he : ρ - τ = (ρ - σ) + (σ - τ) := by abel
  rw [he]
  linarith

/-- Reverse triangle inequality for trace distance, the form used in
Appendix A, Eq. (A1)–(A3): `D_{ρ,x'} ≥ D_{x,x'} − D_{ρ,x}`. -/
theorem traceDistance_sub_le_traceDistance (ρ x x' : Operator N)
    (h : traceDistance ρ x ≤ 1 / 8) (hdev : 5 / 8 < traceDistance x x') :
    1 / 2 < traceDistance ρ x' := by
  have htri := traceDistance_triangle x' ρ x
  rw [traceDistance_comm x' ρ, traceDistance_comm x' x] at htri
  linarith

/-- Appendix D, Eqs. (D2)–(D4): for normalized preparations
`1 − |⟨b|b'⟩|² ≤ ‖|b⟩ − |b'⟩‖²`. This converts the trace distance of `q`
fresh copies of `|b⟩` and `|b'⟩` into the Euclidean distance of the
preparations, which is what the PM access model of Fig. 2 controls. -/
theorem one_sub_inner_normSq_le_stateDistance_sq (b b' : QState (Fin N))
    (hb : Normalized b) (hb' : Normalized b') :
    1 - ‖Inner b b'‖ ^ 2 ≤ stateDistance b b' ^ 2 := by
  have hdist : stateDistance b b' ^ 2 = ∑ i, ‖b i - b' i‖ ^ 2 := by
    unfold stateDistance stateEuclideanNorm stateNormSq
    have hnn : 0 ≤ ∑ i, ‖(b - b') i‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => by positivity)
    rw [Real.sq_sqrt hnn]
    rfl
  rw [hdist]
  have hterm : ∀ i : Fin N, ‖b i - b' i‖ ^ 2
      = ‖b i‖ ^ 2 + ‖b' i‖ ^ 2
        - 2 * (((starRingEnd ℂ) (b i) * b' i).re) := by
    intro i
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    have hconj : b i * (starRingEnd ℂ) (b' i)
        = (starRingEnd ℂ) ((starRingEnd ℂ) (b i) * b' i) := by
      simp
    rw [hconj, Complex.conj_re, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hsum : (∑ i : Fin N, ((starRingEnd ℂ) (b i) * b' i).re)
      = (Qatlib.Foundations.PureStateMath.Inner b b').re := by
    rw [Qatlib.Foundations.PureStateMath.inner_apply]
    simp [Complex.re_sum]
  have hb1 : (∑ i : Fin N, ‖b i‖ ^ 2) = 1 := hb
  have hb1' : (∑ i : Fin N, ‖b' i‖ ^ 2) = 1 := hb'
  rw [hb1, hb1']
  rw [← Finset.mul_sum]
  rw [hsum]
  set z : ℂ := Qatlib.Foundations.PureStateMath.Inner b b'
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hz]
  nlinarith [sq_nonneg (1 - z.re), sq_nonneg z.im]

/-- Tail probabilities are antitone in the threshold. -/
theorem tailProbability_antitone (P : QsvProtocol N Ω) (b σ : QState (Fin N))
    {t t' : ℝ} (htt' : t ≤ t') :
    tailProbability P b σ t' ≤ tailProbability P b σ t := by
  haveI : IsProbabilityMeasure (P.law σ) := P.isProbability σ
  unfold tailProbability
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono (fun ω hω => lt_of_le_of_lt htt' hω)

/-! ## Hybrid counting core (Appendix A, Eqs. (A5)–(A10)) -/

/-- **Counting core.** Suppose on a common sample space two acceptance bits
`accept`, `accept'` agree on average on the executions using at most `t`
controlled unitaries to within `ε` (this is the trace-distance hybrid bound
of Eqs. (A5)–(A10)), the first accepts with probability at least `2/3` and
the second with probability at most `1/3`. Then the probability that more
than `t` controlled unitaries are used is at least `1/6`.

This is the probabilistic skeleton of the proofs of Theorems 1, 3 and 4;
the instance-specific part is only the choice of `t` and `ε`. -/
theorem hybrid_tail_lower_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    (accept accept' : Ω → Bool) (uses : Ω → ℕ)
    (_hacc : Measurable accept) (_hacc' : Measurable accept')
    (_huses : Measurable uses)
    (t ε : ℝ)
    (hstable : |(μ {ω | (uses ω : ℝ) ≤ t ∧ accept ω = true}).toReal
                 - (μ {ω | (uses ω : ℝ) ≤ t ∧ accept' ω = true}).toReal| ≤ ε)
    (hε : ε ≤ 1 / 6)
    (hgood : 2 / 3 ≤ (μ {ω | accept ω = true}).toReal)
    (hbad : (μ {ω | accept' ω = true}).toReal ≤ 1 / 3) :
    1 / 6 ≤ (μ {ω | t < (uses ω : ℝ)}).toReal := by
  let A : Set Ω := {ω | accept ω = true}
  let B : Set Ω := {ω | accept' ω = true}
  let S : Set Ω := {ω | (uses ω : ℝ) ≤ t ∧ accept ω = true}
  let S' : Set Ω := {ω | (uses ω : ℝ) ≤ t ∧ accept' ω = true}
  let T : Set Ω := {ω | t < (uses ω : ℝ)}
  have hA_sub : A ⊆ S ∪ T := by
    intro ω hω
    by_cases hq : (uses ω : ℝ) ≤ t
    · exact Or.inl ⟨hq, hω⟩
    · exact Or.inr (lt_of_not_ge hq)
  have h1 : (μ A).toReal ≤ (μ S).toReal + (μ T).toReal := by
    calc (μ A).toReal ≤ (μ (S ∪ T)).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hA_sub)
      _ ≤ (μ S + μ T).toReal :=
          ENNReal.toReal_mono (by simp [measure_ne_top]) (measure_union_le S T)
      _ = (μ S).toReal + (μ T).toReal :=
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
  have hS : (μ S).toReal ≤ (μ S').toReal + ε := by
    have h := (abs_le.mp (by simpa only [S, S'] using hstable)).2
    linarith
  have hS' : (μ S').toReal ≤ (μ B).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun ω h => h.2))
  have hA : (μ A).toReal ≤ (μ B).toReal + ε + (μ T).toReal := by linarith
  have hB : (μ B).toReal ≤ 1 / 3 := hbad
  have hgood' : 2 / 3 ≤ (μ A).toReal := hgood
  show 1 / 6 ≤ (μ T).toReal
  linarith

end Qatlib.Papers.QLSVerify20.MainResults
