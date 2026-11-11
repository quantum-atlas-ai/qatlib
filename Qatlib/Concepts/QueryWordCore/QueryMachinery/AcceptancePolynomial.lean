/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Acceptance polynomials for query circuits

This module represents circuit amplitudes by complex multivariate polynomials in Boolean oracle
bits. Evaluation recovers circuit execution, each query increases amplitude degree by at most
one, and summing squared real and imaginary parts gives a real acceptance polynomial of degree
at most twice the query count. Boolean multilinearization preserves its values and degree bound.

The mathematical background is described in [BealsEtAl2001].

## Main statements

* `amplitude_polynomial_boolean_run_evaluation`: polynomial evaluation equals circuit amplitude.
* `acceptance_polynomial_actual_born_and_degree`: Born probability and the degree bound.
* `acceptance_boolean_multilinearization_preserves_run`: a multilinear acceptance polynomial.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryWordCore.QueryMachinery

open Matrix

open scoped Classical BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The query-index, answer-bit, and auxiliary-register basis used for polynomial circuit
semantics. -/
abbrev PolynomialWorkspace (I W : Type) := (I × Bool) × W

/-- Converts a Boolean function to its zero-one values in a commutative semiring. -/
def boolValue {σ : Type} {R : Type} [CommSemiring R] (f : σ → Bool) : σ → R :=
  fun i => if f i then 1 else 0

/-- Casting the real zero-one values of a Boolean function to the complexes gives its complex
zero-one values. -/
theorem boolValue_cast (f : I → Bool) :
    (fun i => ((boolValue f : I → ℝ) i : ℂ)) = fun i => if f i then (1 : ℂ) else 0 := by
  funext i
  cases h : f i <;> simp [boolValue, h]

/-- Flips the answer bit according to the oracle value at the query index, preserving the
auxiliary register. -/
def flipWorkspace (f : I → Bool) (p : PolynomialWorkspace I W) : PolynomialWorkspace I W :=
  ((p.1.1, p.1.2 ^^ f p.1.1), p.2)

/-- Updates a family of amplitude polynomials by a gate's linear action or by polynomial
interpolation between unflipped and flipped answer bits. -/
noncomputable def amplitudeStep (s : Step (PolynomialWorkspace I W))
    (P : PolynomialWorkspace I W → MvPolynomial I ℂ) :
    PolynomialWorkspace I W → MvPolynomial I ℂ :=
  match s with
  | .gate U => fun q => ∑ r, MvPolynomial.C (U q r) * P r
  | .query => fun q =>
      (1 - MvPolynomial.X q.1.1) * P q + MvPolynomial.X q.1.1 * P ((q.1.1, !q.1.2), q.2)

/-- Propagates an initial family of amplitude polynomials through a circuit in execution order. -/
noncomputable def amplitudeFold (P : PolynomialWorkspace I W → MvPolynomial I ℂ) :
    Circuit (PolynomialWorkspace I W) → PolynomialWorkspace I W → MvPolynomial I ℂ :=
  fun C => (C.reverse.foldr (fun s Q => amplitudeStep s Q)) P

/-- The family of amplitude polynomials obtained by executing a circuit from constant
polynomials representing the initial state. -/
noncomputable def amplitudePolynomial (C : Circuit (PolynomialWorkspace I W))
    (ψ : QState (PolynomialWorkspace I W)) : PolynomialWorkspace I W → MvPolynomial I ℂ :=
  amplitudeFold (fun q => MvPolynomial.C (ψ q)) C

/-- The amplitude polynomial of the empty circuit is the constant initial amplitude. -/
@[simp] theorem amplitudePolynomial_nil (ψ : QState (PolynomialWorkspace I W))
    (q : PolynomialWorkspace I W) : amplitudePolynomial [] ψ q = MvPolynomial.C (ψ q) := rfl

/-- The amplitude-polynomial family after applying one instruction to the constant polynomials
of an initial state. -/
noncomputable def amplitudeState' (s : Step (PolynomialWorkspace I W))
    (ψ : QState (PolynomialWorkspace I W)) : PolynomialWorkspace I W → MvPolynomial I ℂ :=
  fun r => amplitudeStep s (fun t => MvPolynomial.C (ψ t)) r

/-- Folding a circuit with a first instruction equals folding its tail after the corresponding
polynomial update. -/
theorem amplitudeFold_cons (P : PolynomialWorkspace I W → MvPolynomial I ℂ)
    (s : Step (PolynomialWorkspace I W)) (C : Circuit (PolynomialWorkspace I W))
    (q : PolynomialWorkspace I W) :
    amplitudeFold P (s :: C) q = amplitudeFold (fun r => amplitudeStep s P r) C q := by
  simp only [amplitudeFold, List.reverse_cons, List.foldr_append, List.foldr_cons,
    List.foldr_nil]

/-- The amplitude polynomials of a nonempty circuit are obtained by folding the tail from the
first instruction's polynomial state. -/
theorem amplitudePolynomial_cons (s : Step (PolynomialWorkspace I W))
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (q : PolynomialWorkspace I W) :
    amplitudePolynomial (s :: C) ψ q
      = amplitudeFold (amplitudeState' s ψ) C q := by
  rw [amplitudePolynomial, amplitudeFold_cons]
  rfl

/-- Appending one instruction to a circuit applies its polynomial update to the circuit's
amplitude polynomials. -/
theorem amplitudePolynomial_append_last (C : Circuit (PolynomialWorkspace I W))
    (s : Step (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W)) :
    amplitudePolynomial (C ++ [s]) ψ = amplitudeStep s (amplitudePolynomial C ψ) := by
  simp only [amplitudePolynomial, amplitudeFold, List.reverse_append, List.reverse_singleton,
    List.foldr_append, List.foldr_cons, List.foldr_nil]

/-- Gives the empty-circuit, gate, and query recurrences for the amplitude polynomial at a
workspace basis label; see [Beals et al., Lemma 4.1][BealsEtAl2001]. -/
theorem amplitude_polynomial_actual_step_recursion
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (U : Matrix (PolynomialWorkspace I W) (PolynomialWorkspace I W) ℂ) (i : I) (b : Bool)
    (w : W) :
    amplitudePolynomial [] ψ ((i, b), w) = MvPolynomial.C (ψ ((i, b), w)) ∧
      amplitudePolynomial (C ++ [Step.gate U]) ψ ((i, b), w) =
        ∑ q, MvPolynomial.C (U ((i, b), w) q) * amplitudePolynomial C ψ q ∧
      amplitudePolynomial (C ++ [Step.query]) ψ ((i, b), w) =
        (1 - MvPolynomial.X i) * amplitudePolynomial C ψ ((i, b), w) +
          MvPolynomial.X i * amplitudePolynomial C ψ ((i, !b), w) := by
  have hgate : amplitudePolynomial (C ++ [Step.gate U]) ψ ((i, b), w)
      = ∑ q, MvPolynomial.C (U ((i, b), w) q) * amplitudePolynomial C ψ q := by
    rw [amplitudePolynomial_append_last]
    rfl
  have hquery : amplitudePolynomial (C ++ [Step.query]) ψ ((i, b), w)
      = (1 - MvPolynomial.X i) * amplitudePolynomial C ψ ((i, b), w) +
        MvPolynomial.X i * amplitudePolynomial C ψ ((i, !b), w) := by
    rw [amplitudePolynomial_append_last]
    rfl
  exact ⟨amplitudePolynomial_nil ψ _, hgate, hquery⟩

/-- The single-instruction state update for a Boolean oracle, using matrix action for gates and
answer-bit relabeling for queries. -/
noncomputable def amplitudeState (f : I → Bool) (s : Step (PolynomialWorkspace I W))
    (χ : QState (PolynomialWorkspace I W)) : QState (PolynomialWorkspace I W) :=
  match s with
  | .gate U => ApplyGate U χ
  | .query => χ ∘ flipWorkspace f

/-- A gate instruction in `amplitudeState` acts by `ApplyGate`. -/
@[simp] theorem amplitudeState_gate (f : I → Bool)
    (U : Matrix (PolynomialWorkspace I W) (PolynomialWorkspace I W) ℂ)
    (χ : QState (PolynomialWorkspace I W)) (q : PolynomialWorkspace I W) :
    amplitudeState f (Step.gate U) χ q = ApplyGate U χ q := rfl

/-- A query instruction in `amplitudeState` acts by composition with `flipWorkspace`. -/
@[simp] theorem amplitudeState_query (f : I → Bool) (χ : QState (PolynomialWorkspace I W))
    (q : PolynomialWorkspace I W) : amplitudeState f Step.query χ q = χ (flipWorkspace f q) := rfl

/-- A matrix tensored with the identity acts independently on each slice of the auxiliary
register. -/
theorem polynomial_applyGate_tensorGate_one (U : Matrix (I × Bool) (I × Bool) ℂ)
    (ψ : QState ((I × Bool) × W)) :
    ApplyGate (TensorGate U 1) ψ = fun p => ApplyGate U (fun k => ψ (k, p.2)) p.1 := by
  funext p
  obtain ⟨x, w⟩ := p
  have hone : ∀ (a : ℂ) (c : W → ℂ),
      (∑ x_2 : W, a * (1 : Matrix W W ℂ) w x_2 * c x_2) = a * c w := by
    intro a c
    have h0 : ∀ (x_2 : W), a * (1 : Matrix W W ℂ) w x_2 * c x_2
        = if w = x_2 then a * c x_2 else 0 := by
      intro x_2
      by_cases h : w = x_2
      · rw [Matrix.one_apply, if_pos h, mul_one, if_pos h]
      · rw [Matrix.one_apply, if_neg h, if_neg h]
        simp
    rw [show (∑ x_2 : W, a * (1 : Matrix W W ℂ) w x_2 * c x_2)
        = ∑ x_2 ∈ (Finset.univ : Finset W), (if w = x_2 then a * c x_2 else 0) from
      Finset.sum_congr rfl fun x_2 _ => h0 x_2]
    rw [Finset.sum_eq_single w]
    · simp
    · intro b _ hb
      have hnb : ¬ (w = b) := fun e => hb e.symm
      simp [hnb]
    · simp
  simp only [ApplyGate, TensorGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker_apply]
  simp_rw [hone]

/-- Applying the workspace bit oracle evaluates the input state at the corresponding flipped
answer-bit label. -/
theorem applyGate_bitOracleOn_workspace (f : I → Bool)
    (ψ : QState (PolynomialWorkspace I W)) (p : PolynomialWorkspace I W) :
    ApplyGate (TensorGate (BitOracleOn f) 1) ψ p = ψ (flipWorkspace f p) := by
  rw [polynomial_applyGate_tensorGate_one]
  obtain ⟨x, w⟩ := p
  obtain ⟨i, b⟩ := x
  show ApplyGate (BitOracleOn f) (fun k => ψ (k, w)) (i, b) = ψ (flipWorkspace f ((i, b), w))
  rw [applyGate_bitOracleOn]
  rfl

/-- The workspace bit-oracle action is composition with `flipWorkspace`. -/
theorem applyGate_bitOracleOn_workspace' (f : I → Bool)
    (ψ : QState (PolynomialWorkspace I W)) :
    ApplyGate (TensorGate (BitOracleOn f) 1) ψ = ψ ∘ flipWorkspace f := by
  funext p
  exact applyGate_bitOracleOn_workspace f ψ p

/-- Executing a singleton circuit with the workspace bit oracle agrees with its `amplitudeState`
update. -/
theorem amplitudeState_run (f : I → Bool) (s : Step (PolynomialWorkspace I W))
    (χ : QState (PolynomialWorkspace I W)) :
    Run (TensorGate (BitOracleOn f) 1) [s] χ = amplitudeState f s χ := by
  cases s with
  | gate U => simp [amplitudeState, run_gate, run_nil]
  | query =>
    simp only [amplitudeState, run_query, run_nil]
    exact applyGate_bitOracleOn_workspace' f χ

/-- Executing a nonempty circuit equals executing its tail from the first instruction's
`amplitudeState` update. -/
theorem amplitudeState_run_cons (f : I → Bool) (s : Step (PolynomialWorkspace I W))
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W)) :
    Run (TensorGate (BitOracleOn f) 1) (s :: C) ψ = Run (TensorGate (BitOracleOn f) 1) C
      (amplitudeState f s ψ) := by
  cases s with
  | gate U => exact run_gate _ _ _ _
  | query =>
    show Run (TensorGate (BitOracleOn f) 1) C (ApplyGate (TensorGate (BitOracleOn f) 1) ψ) = _
    rw [← amplitudeState_run f Step.query ψ]
    exact run_query _ _ _

/-- Evaluation of a polynomial step at Boolean oracle values agrees with the corresponding state
update whenever the input polynomials evaluate to the input state. -/
theorem amplitudeStep_eval (s : Step (PolynomialWorkspace I W)) (f : I → Bool)
    (P : PolynomialWorkspace I W → MvPolynomial I ℂ) (χ : QState (PolynomialWorkspace I W))
    (hP : ∀ q, MvPolynomial.eval (boolValue f) (P q) = χ q) (q : PolynomialWorkspace I W) :
    MvPolynomial.eval (boolValue f) (amplitudeStep s P q) = amplitudeState f s χ q := by
  cases s with
  | gate U =>
    show MvPolynomial.eval (boolValue f) (∑ r, MvPolynomial.C (U q r) * P r) = ApplyGate U χ q
    have hsum : MvPolynomial.eval (boolValue f) (∑ r, MvPolynomial.C (U q r) * P r)
        = ∑ r, U q r * χ r := by
      rw [show (∑ r, MvPolynomial.C (U q r) * P r)
          = ∑ r ∈ (Finset.univ : Finset (PolynomialWorkspace I W)),
            MvPolynomial.C (U q r) * P r from rfl]
      simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
      exact Finset.sum_congr rfl fun r _ => by rw [hP r]
    rw [hsum, ApplyGate, Matrix.mulVec, dotProduct]
  | query =>
    cases q with
    | mk x w =>
      cases x with
      | mk i b =>
        show MvPolynomial.eval (boolValue f)
            ((1 - MvPolynomial.X i) * P ((i, b), w) + MvPolynomial.X i * P ((i, !b), w))
          = χ (flipWorkspace f ((i, b), w))
        cases hfi : f i <;> cases hb : b <;>
          simp [boolValue, flipWorkspace, hP, hfi, MvPolynomial.eval_sub,
            MvPolynomial.eval_add]

/-- The amplitude polynomial evaluated at a Boolean oracle's zero-one values equals the
corresponding amplitude of the executed circuit; see [BealsEtAl2001]. -/
theorem amplitude_polynomial_boolean_run_evaluation
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (f : I → Bool) (q : PolynomialWorkspace I W) :
    MvPolynomial.eval (fun i => if f i then (1 : ℂ) else 0) (amplitudePolynomial C ψ q) =
      Run (TensorGate (BitOracleOn f) 1) C ψ q := by
  have key : ∀ (D : Circuit (PolynomialWorkspace I W)),
      ∀ (P : PolynomialWorkspace I W → MvPolynomial I ℂ) (f : I → Bool)
        (χ : QState (PolynomialWorkspace I W)),
        (∀ r, MvPolynomial.eval (boolValue f) (P r) = χ r) → ∀ (q :
          PolynomialWorkspace I W),
          MvPolynomial.eval (boolValue f) (amplitudeFold P D q) =
            Run (TensorGate (BitOracleOn f) 1) D χ q := by
    intro D
    induction D with
    | nil =>
      intro P f χ hP q
      simpa [amplitudeFold] using hP q
    | cons s D ih =>
      intro P f χ hP q
      rw [amplitudeFold_cons, amplitudeState_run_cons]
      exact ih _ f (amplitudeState f s χ) (fun r => amplitudeStep_eval s f P χ hP r) q
  have hcast : (fun i => if f i then (1 : ℂ) else 0) = (fun i => (boolValue f : I → ℂ) i) := by
    funext i
    rfl
  rw [hcast, amplitudePolynomial]
  exact key C (fun q => MvPolynomial.C (ψ q)) f ψ (fun r => by simp) q

/-- The degree cost of an instruction: zero for a gate and one for an oracle query. -/
def stepDegreeCost : Step (PolynomialWorkspace I W) → ℕ
  | .gate _ => 0
  | .query => 1

/-- A polynomial instruction increases a uniform amplitude-degree bound by at most
`stepDegreeCost`. -/
theorem amplitudeStep_totalDegree_le {s : Step (PolynomialWorkspace I W)}
    {P : PolynomialWorkspace I W → MvPolynomial I ℂ} {t : ℕ}
    (hP : ∀ r, (P r).totalDegree ≤ t) (q : PolynomialWorkspace I W) :
    (amplitudeStep s P q).totalDegree ≤ t + stepDegreeCost s := by
  cases s with
  | gate U =>
    show (∑ r, MvPolynomial.C (U q r) * P r).totalDegree ≤ t + stepDegreeCost (Step.gate U)
    refine (MvPolynomial.totalDegree_finsetSum_le
      (d := t + stepDegreeCost (Step.gate U))
      (s := (Finset.univ : Finset (PolynomialWorkspace I W)))
      (f := fun r => MvPolynomial.C (U q r) * P r) ?_).trans le_rfl
    intro r _
    have h1 : ((MvPolynomial.C (U q r) : MvPolynomial I ℂ) * P r).totalDegree
        ≤ (MvPolynomial.C (U q r) : MvPolynomial I ℂ).totalDegree + (P r).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    have h2 : (MvPolynomial.C (U q r) : MvPolynomial I ℂ).totalDegree = 0 :=
      MvPolynomial.totalDegree_C _
    have h3 : (P r).totalDegree ≤ t := hP r
    show (MvPolynomial.C (U q r) * P r).totalDegree ≤ t
    calc (MvPolynomial.C (U q r) * P r).totalDegree
        ≤ (MvPolynomial.C (U q r) : MvPolynomial I ℂ).totalDegree + (P r).totalDegree := h1
      _ = (P r).totalDegree := by rw [h2, Nat.zero_add]
      _ ≤ t := h3
  | query =>
    have hA : (1 - (MvPolynomial.X q.1.1 : MvPolynomial I ℂ) : MvPolynomial I ℂ).totalDegree ≤ 1 := by
      refine (MvPolynomial.totalDegree_sub (1 : MvPolynomial I ℂ) (MvPolynomial.X q.1.1)).trans ?_
      exact max_le (by simp) (MvPolynomial.totalDegree_X q.1.1).le
    have hB : ((1 - (MvPolynomial.X q.1.1 : MvPolynomial I ℂ)) * P q).totalDegree ≤ t + 1 := by
      have hmul := MvPolynomial.totalDegree_mul
        (1 - (MvPolynomial.X q.1.1 : MvPolynomial I ℂ)) (P q)
      have hPq : (P q).totalDegree ≤ t := hP q
      omega
    have hC : ((MvPolynomial.X q.1.1 : MvPolynomial I ℂ) * P ((q.1.1, !q.1.2), q.2)).totalDegree
        ≤ t + 1 := by
      calc (MvPolynomial.X q.1.1 * P ((q.1.1, !q.1.2), q.2)).totalDegree
          ≤ (MvPolynomial.X q.1.1).totalDegree + (P ((q.1.1, !q.1.2), q.2)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
        _ = 1 + (P ((q.1.1, !q.1.2), q.2)).totalDegree := by rw [MvPolynomial.totalDegree_X]
        _ ≤ 1 + t := Nat.add_le_add_left (hP _) 1
        _ = t + 1 := Nat.add_comm 1 t
    have hsub : ((1 - (MvPolynomial.X q.1.1 : MvPolynomial I ℂ)) * P q
        + (MvPolynomial.X q.1.1 : MvPolynomial I ℂ) * P ((q.1.1, !q.1.2), q.2)).totalDegree
      ≤ t + 1 := by
      refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · exact hB
      · exact hC
    exact hsub

/-- Every circuit amplitude polynomial has total degree at most the circuit's oracle-query
count; see [BealsEtAl2001]. -/
theorem amplitude_polynomial_actual_query_degree
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (q : PolynomialWorkspace I W) :
    (amplitudePolynomial C ψ q).totalDegree ≤ QueryCount C := by
  have key : ∀ (D : Circuit (PolynomialWorkspace I W))
      (P : PolynomialWorkspace I W → MvPolynomial I ℂ) (t : ℕ),
      (∀ r, (P r).totalDegree ≤ t) → ∀ (q : PolynomialWorkspace I W),
        (amplitudeFold P D q).totalDegree ≤ t + QueryCount D := by
    intro D
    induction D with
    | nil =>
      intro P t hP q
      have hq : amplitudeFold P [] q = P q := by simp [amplitudeFold]
      rw [hq]
      exact hP q
    | cons s D ih =>
      intro P t hP q
      cases s with
      | gate U =>
        rw [amplitudeFold_cons]
        have h1 := ih (fun r => amplitudeStep (Step.gate U) P r) (t + 0)
          (fun r => amplitudeStep_totalDegree_le hP r) q
        have hq1 : QueryCount (Step.gate U :: D) = QueryCount D := by simp [QueryCount]
        rw [hq1] at ⊢
        omega
      | query =>
        rw [amplitudeFold_cons]
        have h1 := ih (fun r => amplitudeStep Step.query P r) (t + 1)
          (fun r => amplitudeStep_totalDegree_le hP r) q
        have hq1 : QueryCount (Step.query :: D) = QueryCount D + 1 := by simp [QueryCount]
        rw [hq1] at ⊢
        omega
  rw [amplitudePolynomial]
  simpa using key C (fun q => MvPolynomial.C (ψ q)) 0
    (fun r => by simp [MvPolynomial.totalDegree_C]) q

/-- The real polynomial obtained by taking the real part of each coefficient of a complex
polynomial. -/
noncomputable def realPart (p : MvPolynomial I ℂ) : MvPolynomial I ℝ :=
  ∑ d ∈ p.support, MvPolynomial.C (p.coeff d).re * MvPolynomial.monomial d 1

/-- The real polynomial obtained by taking the imaginary part of each coefficient of a complex
polynomial. -/
noncomputable def imagPart (p : MvPolynomial I ℂ) : MvPolynomial I ℝ :=
  ∑ d ∈ p.support, MvPolynomial.C (p.coeff d).im * MvPolynomial.monomial d 1

/-- Expands the complex cast of a real coefficientwise polynomial evaluation as a sum of cast
coefficients times complex monomial values. -/
private theorem cast_eval_part (k : ℂ → ℝ) (s : Finset (I →₀ ℕ)) (c : (I →₀ ℕ) → ℂ) (x : I → ℝ) :
    ((MvPolynomial.eval x (∑ d ∈ s, MvPolynomial.C (k (c d)) * MvPolynomial.monomial d 1) : ℝ) :
      ℂ) = ∑ d ∈ s, (k (c d) : ℂ) * ∏ i, (x i : ℂ) ^ (d i) := by
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_monomial, Finsupp.prod_pow]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hpow : ∀ (j : I →₀ ℕ), (∏ i, ((x i ^ (j i) : ℝ) : ℂ)) = ∏ i, ((x i : ℂ) ^ (j i)) :=
    fun j => Finset.prod_congr rfl fun i _ => Complex.ofReal_pow (x i) (j i)
  simp only [Complex.ofReal_mul, one_mul, Complex.ofReal_prod, hpow]

/-- At real inputs, the evaluations of the coefficientwise real and imaginary parts reconstruct
the complex polynomial's evaluation. -/
private theorem realImag_eval_complex (p : MvPolynomial I ℂ) (x : I → ℝ) :
    ((MvPolynomial.eval x (realPart p) : ℝ) : ℂ)
      + Complex.I * ((MvPolynomial.eval x (imagPart p) : ℝ) : ℂ)
      = MvPolynomial.eval (fun i => (x i : ℂ)) p := by
  have key : ∀ (c : ℂ) (z : ℂ),
      ((c.re : ℂ)) * z + Complex.I * ((c.im : ℂ) * z) = c * z := by
    intro c z
    calc ((c.re : ℂ)) * z + Complex.I * ((c.im : ℂ) * z)
        = (((c.re : ℝ) : ℂ) + Complex.I * ((c.im : ℝ) : ℂ)) * z := by ring
      _ = c * z := by
        apply congrArg (fun w : ℂ => w * z)
        apply Complex.ext <;> simp
  have hrw : MvPolynomial.eval (fun i => (x i : ℂ)) p
      = ∑ d ∈ p.support, p.coeff d * ∏ i, (x i : ℂ) ^ (d i) := MvPolynomial.eval_eq' _ _
  rw [hrw, realPart, imagPart, cast_eval_part Complex.re, cast_eval_part Complex.im,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => key _ _

/-- The sum of the squared real and imaginary parts of a complex number equals its squared norm. -/
private theorem re_im_sq_eq_normSq (z : ℂ) : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
  calc z.re ^ 2 + z.im ^ 2 = z.re * z.re + z.im * z.im := by ring
    _ = Complex.normSq z := Complex.normSq_apply z
    _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z

/-- Evaluation of the coefficientwise real part at real inputs equals the real part of the
complex evaluation. -/
theorem realPart_eval (p : MvPolynomial I ℂ) (x : I → ℝ) :
    MvPolynomial.eval x (realPart p) = (MvPolynomial.eval (fun i => (x i : ℂ)) p).re := by
  have h := congrArg Complex.re (realImag_eval_complex p x)
  simpa using h

/-- Evaluation of the coefficientwise imaginary part at real inputs equals the imaginary part of
the complex evaluation. -/
theorem imagPart_eval (p : MvPolynomial I ℂ) (x : I → ℝ) :
    MvPolynomial.eval x (imagPart p) = (MvPolynomial.eval (fun i => (x i : ℂ)) p).im := by
  have h := congrArg Complex.im (realImag_eval_complex p x)
  simpa using h

/-- Taking real parts of polynomial coefficients cannot increase total degree. -/
theorem realPart_totalDegree_le (p : MvPolynomial I ℂ) :
    (realPart p).totalDegree ≤ p.totalDegree := by
  refine (MvPolynomial.totalDegree_finsetSum_le (s := p.support) (d := p.totalDegree) ?_).trans
    le_rfl
  intro d hd
  have h1 : ((MvPolynomial.C (p.coeff d).re * MvPolynomial.monomial d 1 :
      MvPolynomial I ℝ).totalDegree)
      ≤ (MvPolynomial.C (p.coeff d).re : MvPolynomial I ℝ).totalDegree
        + (MvPolynomial.monomial d 1 : MvPolynomial I ℝ).totalDegree :=
    MvPolynomial.totalDegree_mul _ _
  have h2 : (MvPolynomial.C (p.coeff d).re : MvPolynomial I ℝ).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  have h3 : (MvPolynomial.monomial d 1 : MvPolynomial I ℝ).totalDegree ≤ d.sum (fun _ e => e) :=
    MvPolynomial.totalDegree_monomial_le d 1
  have h4 : d.sum (fun _ e => e) ≤ p.totalDegree := MvPolynomial.le_totalDegree hd
  omega

/-- Taking imaginary parts of polynomial coefficients cannot increase total degree. -/
theorem imagPart_totalDegree_le (p : MvPolynomial I ℂ) :
    (imagPart p).totalDegree ≤ p.totalDegree := by
  refine (MvPolynomial.totalDegree_finsetSum_le (s := p.support) (d := p.totalDegree) ?_).trans
    le_rfl
  intro d hd
  have h1 : ((MvPolynomial.C (p.coeff d).im * MvPolynomial.monomial d 1 :
      MvPolynomial I ℝ).totalDegree)
      ≤ (MvPolynomial.C (p.coeff d).im : MvPolynomial I ℝ).totalDegree
        + (MvPolynomial.monomial d 1 : MvPolynomial I ℝ).totalDegree :=
    MvPolynomial.totalDegree_mul _ _
  have h2 : (MvPolynomial.C (p.coeff d).im : MvPolynomial I ℝ).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  have h3 : (MvPolynomial.monomial d 1 : MvPolynomial I ℝ).totalDegree ≤ d.sum (fun _ e => e) :=
    MvPolynomial.totalDegree_monomial_le d 1
  have h4 : d.sum (fun _ e => e) ≤ p.totalDegree := MvPolynomial.le_totalDegree hd
  omega

/-- The sum, over accepted basis labels, of the squared real and imaginary amplitude
polynomials. -/
noncomputable def rawAcceptancePolynomial (C : Circuit (PolynomialWorkspace I W))
    (ψ : QState (PolynomialWorkspace I W)) (E : Finset (PolynomialWorkspace I W)) :
    MvPolynomial I ℝ :=
  Finset.sum E fun q =>
    (realPart (amplitudePolynomial C ψ q)) ^ 2 + (imagPart (amplitudePolynomial C ψ q)) ^ 2

/-- The raw acceptance polynomial evaluates to the circuit's Born probability on every Boolean
oracle and has degree at most twice its query count; see [BealsEtAl2001]. -/
theorem acceptance_polynomial_actual_born_and_degree
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (E : Finset (PolynomialWorkspace I W)) (f : I → Bool) :
    MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0) (rawAcceptancePolynomial C ψ E) =
        MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E ∧
      (rawAcceptancePolynomial C ψ E).totalDegree ≤ 2 * QueryCount C := by
  constructor
  · have hsum : MvPolynomial.eval (boolValue f) (rawAcceptancePolynomial C ψ E)
        = ∑ q ∈ E, ‖Run (TensorGate (BitOracleOn f) 1) C ψ q‖ ^ 2 := by
      unfold rawAcceptancePolynomial
      rw [MvPolynomial.eval_sum E (fun q =>
          (realPart (amplitudePolynomial C ψ q)) ^ 2 +
            (imagPart (amplitudePolynomial C ψ q)) ^ 2) (boolValue f)]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hx : MvPolynomial.eval (fun i => ((boolValue f : I → ℝ) i : ℂ))
          (amplitudePolynomial C ψ q) = Run (TensorGate (BitOracleOn f) 1) C ψ q := by
        have h := amplitude_polynomial_boolean_run_evaluation C ψ f q
        rw [← boolValue_cast] at h
        exact h
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_pow]
      rw [realPart_eval, imagPart_eval, hx, re_im_sq_eq_normSq]
    have hcast : (fun i => if f i then (1 : ℝ) else 0) = (fun i => (boolValue f : I → ℝ) i) := by
      funext i
      rfl
    rw [hcast, hsum]
    rfl
  · refine (MvPolynomial.totalDegree_finsetSum_le (s := E) (d := 2 * QueryCount C) ?_).trans
      le_rfl
    intro q _
    have hamp : (amplitudePolynomial C ψ q).totalDegree ≤ QueryCount C :=
      amplitude_polynomial_actual_query_degree C ψ q
    have hre : (realPart (amplitudePolynomial C ψ q)).totalDegree ≤ QueryCount C :=
      (realPart_totalDegree_le _).trans hamp
    have him : (imagPart (amplitudePolynomial C ψ q)).totalDegree ≤ QueryCount C :=
      (imagPart_totalDegree_le _).trans hamp
    have h1 : (((realPart (amplitudePolynomial C ψ q)) ^ 2
        + (imagPart (amplitudePolynomial C ψ q)) ^ 2 : MvPolynomial I ℝ).totalDegree)
        ≤ max ((realPart (amplitudePolynomial C ψ q)) ^ 2 : MvPolynomial I ℝ).totalDegree
          ((imagPart (amplitudePolynomial C ψ q)) ^ 2 : MvPolynomial I ℝ).totalDegree :=
      MvPolynomial.totalDegree_add _ _
    have h2 : max ((realPart (amplitudePolynomial C ψ q)) ^ 2 : MvPolynomial I ℝ).totalDegree
        ((imagPart (amplitudePolynomial C ψ q)) ^ 2 : MvPolynomial I ℝ).totalDegree
        ≤ 2 * QueryCount C := by
      refine max_le ?_ ?_
      · calc ((realPart (amplitudePolynomial C ψ q)) ^ 2).totalDegree
          ≤ 2 * (realPart (amplitudePolynomial C ψ q)).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
        _ ≤ 2 * QueryCount C := Nat.mul_le_mul_left 2 hre
      · calc ((imagPart (amplitudePolynomial C ψ q)) ^ 2).totalDegree
          ≤ 2 * (imagPart (amplitudePolynomial C ψ q)).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
        _ ≤ 2 * QueryCount C := Nat.mul_le_mul_left 2 him
    exact h1.trans h2

/-- Replaces each positive exponent of a finitely supported monomial by one. -/
noncomputable def clampExponent (d : I →₀ ℕ) : I →₀ ℕ :=
  Finsupp.indicator d.support (fun i _ => 1)

/-- A clamped exponent is zero exactly when the original exponent is zero, and is one otherwise. -/
@[simp] theorem clampExponent_apply (d : I →₀ ℕ) (i : I) :
    clampExponent d i = if d i = 0 then 0 else 1 := by
  classical
  by_cases h : d i = 0
  · rw [clampExponent, Finsupp.indicator_apply,
      dif_neg (Finsupp.notMem_support_iff.mpr h)]
    simp [h]
  · rw [clampExponent, Finsupp.indicator_apply,
      dif_pos (Finsupp.mem_support_iff.mpr h)]
    simp [h]

/-- Clamping an exponent cannot increase any coordinate. -/
theorem clampExponent_le (d : I →₀ ℕ) (i : I) : clampExponent d i ≤ d i := by
  rw [clampExponent_apply]
  by_cases h : d i = 0
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

/-- Every coordinate of an exponent equal to `clampExponent d` is at most one. -/
theorem clampExponent_mul_le (d : I →₀ ℕ) (e : I →₀ ℕ) (h : clampExponent d = e) (i : I) :
    e i ≤ 1 := by
  rw [← h, clampExponent_apply]
  split_ifs with hi <;> omega

/-- Replaces each monomial's positive exponents by one, combining coefficients of monomials with
the same clamped exponent. -/
noncomputable def multilinearize (p : MvPolynomial I ℝ) : MvPolynomial I ℝ :=
  ∑ d ∈ p.support, MvPolynomial.monomial (clampExponent d) (p.coeff d)

/-- Multilinearization cannot increase the total degree of a real polynomial. -/
theorem multilinearize_totalDegree_le (p : MvPolynomial I ℝ) :
    (multilinearize p).totalDegree ≤ p.totalDegree := by
  refine (MvPolynomial.totalDegree_finsetSum_le (s := p.support) (d := p.totalDegree) ?_).trans
    le_rfl
  intro d hd
  have h1 : (MvPolynomial.monomial (clampExponent d) (p.coeff d)).totalDegree
      ≤ (clampExponent d).sum (fun _ e => e) := MvPolynomial.totalDegree_monomial_le _ _
  have h2 : (clampExponent d).sum (fun _ e => e) = ∑ i, clampExponent d i :=
    Finsupp.sum_fintype _ _ (fun _ => rfl)
  have h3 : (∑ i, clampExponent d i) ≤ ∑ i, d i :=
    Finset.sum_le_sum fun i _ => clampExponent_le d i
  have h4 : d.sum (fun _ e => e) = ∑ i, d i := Finsupp.sum_fintype _ _ (fun _ => rfl)
  have h5 : d.sum (fun _ e => e) ≤ p.totalDegree := MvPolynomial.le_totalDegree hd
  omega

/-- Every monomial with nonzero coefficient after multilinearization has exponent at most one in
each variable. -/
theorem multilinearize_coeff_multilinear (p : MvPolynomial I ℝ) (d : I →₀ ℕ)
    (hd : (multilinearize p).coeff d ≠ 0) (i : I) : d i ≤ 1 := by
  have hne : ∑ d' ∈ p.support,
      (MvPolynomial.monomial (clampExponent d') (p.coeff d')).coeff d ≠ 0 := by
    have h1 : (multilinearize p).coeff d
        = ∑ x ∈ p.support,
            (MvPolynomial.monomial (clampExponent x) (p.coeff x)).coeff d := by
      show (∑ x ∈ p.support, MvPolynomial.monomial (clampExponent x) (p.coeff x)).coeff d = _
      exact MvPolynomial.coeff_sum _ _ _
    rw [← h1]
    exact hd
  obtain ⟨d', hd', hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hne'' : clampExponent d' = d ∧ p.coeff d' ≠ 0 := by
    simpa [MvPolynomial.coeff_monomial, ne_eq] using hne'
  exact clampExponent_mul_le d' d hne''.1 i

/-- At a zero-one input coordinate, clamping a monomial exponent preserves its power value. -/
private theorem boolPow_clamp (x : I → ℝ) (d : I →₀ ℕ) (i : I)
    (h : x i = 0 ∨ x i = 1) : x i ^ (clampExponent d i) = x i ^ d i := by
  by_cases hd : d i = 0
  · simp [clampExponent_apply, hd]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hd
    cases h with
    | inl hx => simp [hx, clampExponent_apply, hk]
    | inr hx => simp [hx, clampExponent_apply, hk]

/-- Multilinearization preserves polynomial evaluation at every zero-one assignment. -/
theorem multilinearize_eval (p : MvPolynomial I ℝ) (x : I → ℝ) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    MvPolynomial.eval x (multilinearize p) = MvPolynomial.eval x p := by
  have hpow : ∀ (j : I →₀ ℕ), (∏ i, x i ^ (clampExponent j i)) = ∏ i, x i ^ (j i) :=
    fun j => Finset.prod_congr rfl fun i _ => boolPow_clamp x j i (hx i)
  rw [multilinearize]
  rw [MvPolynomial.eval_sum p.support
    (fun d => MvPolynomial.monomial (clampExponent d) (p.coeff d)) x]
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow, hpow]

/-- The multilinearization of a circuit's raw real acceptance polynomial. -/
noncomputable def booleanAcceptancePolynomial (C : Circuit (PolynomialWorkspace I W))
    (ψ : QState (PolynomialWorkspace I W)) (E : Finset (PolynomialWorkspace I W)) :
    MvPolynomial I ℝ :=
  multilinearize (rawAcceptancePolynomial C ψ E)

/-- The Boolean acceptance polynomial is multilinear, has degree at most twice the query count,
and evaluates to the executed circuit's Born probability; see [BealsEtAl2001]. -/
theorem acceptance_boolean_multilinearization_preserves_run
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (E : Finset (PolynomialWorkspace I W)) :
    (booleanAcceptancePolynomial C ψ E).totalDegree ≤ 2 * QueryCount C ∧
      (∀ d : I →₀ ℕ, (booleanAcceptancePolynomial C ψ E).coeff d ≠ 0 → ∀ i, d i ≤ 1) ∧
      ∀ f : I → Bool,
        MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0)
            (booleanAcceptancePolynomial C ψ E) =
          MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E := by
  refine ⟨(multilinearize_totalDegree_le (rawAcceptancePolynomial C ψ E)).trans
      (acceptance_polynomial_actual_born_and_degree C ψ E (fun _ => false)).2, ?_, ?_⟩
  · intro d hd i
    exact multilinearize_coeff_multilinear (rawAcceptancePolynomial C ψ E) d hd i
  · intro f
    have h1' : MvPolynomial.eval (boolValue f) (booleanAcceptancePolynomial C ψ E)
        = MeasureProb (Run (TensorGate (BitOracleOn f) 1) C ψ) E := by
      rw [booleanAcceptancePolynomial]
      rw [multilinearize_eval (rawAcceptancePolynomial C ψ E) (boolValue f) (fun i => by
        by_cases h : f i <;> simp [boolValue, h])]
      exact (acceptance_polynomial_actual_born_and_degree C ψ E f).1
    have h1 := (acceptance_polynomial_actual_born_and_degree C ψ E f).1
    have hcast : (fun i => if f i then (1 : ℝ) else 0) = (fun i => (boolValue f : I → ℝ) i) := by
      funext i
      rfl
    have h2 := multilinearize_eval (rawAcceptancePolynomial C ψ E) (boolValue f) (fun i => by
      by_cases h : f i <;> simp [boolValue, h])
    rw [hcast]
    exact h1'

end Qatlib.Concepts.QueryWordCore.QueryMachinery
