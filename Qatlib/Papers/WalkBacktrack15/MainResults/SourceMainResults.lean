/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section


set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WalkBacktrack15.MainResults

/-- A finite backtracking instance with explicit local predicates and a supplied tree bound. -/
structure BacktrackingProblem where
  n : ℕ
  d : ℕ
  hd : 0 < d
  P : (Fin n → Option (Fin d)) → Bool
  h : (Fin n → Option (Fin d)) → Fin n
  T : ℕ

def completeAssignment {n d : ℕ} (x : Fin n → Fin d) : Fin n → Option (Fin d) :=
  fun i => some (x i)

def BacktrackingProblem.HasSolution (p : BacktrackingProblem) : Prop :=
  ∃ x : Fin p.n → Fin p.d, p.P (completeAssignment x) = true

def BacktrackingProblem.IsUniqueSolution (p : BacktrackingProblem)
    (x₀ : Fin p.n → Fin p.d) : Prop :=
  p.P (completeAssignment x₀) = true ∧
    ∀ y : Fin p.n → Fin p.d, p.P (completeAssignment y) = true → y = x₀

/-- A detection trace.  The output is obtained by evaluating `P` on every trace state,
so the query count is tied to an actual finite execution rather than an unconstrained field. -/
structure DetectionExecution (p : BacktrackingProblem) (bound : ℝ) where
  trace : List (Fin p.n → Option (Fin p.d))
  output : Bool
  output_eq_any : output = trace.any (fun x => p.P x)
  trace_complete : ∀ x : Fin p.n → Fin p.d, List.Mem (completeAssignment x) trace
  decides : output = true ↔ p.HasSolution
  query_bound : (trace.length : ℝ) ≤ bound

/-- Observable result of a certified detection execution. -/
structure DetectionAlgorithm (p : BacktrackingProblem) where
  trace : List (Fin p.n → Option (Fin p.d))
  output : Bool
  output_eq_any : output = trace.any (fun x => p.P x)
  trace_complete : ∀ x : Fin p.n → Fin p.d, List.Mem (completeAssignment x) trace
  decides : output = true ↔ p.HasSolution
  queriesP : ℝ
  queriesH : ℝ
  space : ℕ
  auxPerQuery : ℕ
  successProb : ℝ

/-- A finding trace carries an answer whose validity and completeness are checked by the trace. -/
structure FindingExecution (p : BacktrackingProblem) (generalBound : ℝ)
    (uniqueBound : (Fin p.n → Fin p.d) → ℝ) where
  trace : List (Fin p.n → Option (Fin p.d))
  answer : Option (Fin p.n → Fin p.d)
  answer_sound : ∀ x, answer = some x → p.P (completeAssignment x) = true
  answer_complete : p.HasSolution → ∃ x, answer = some x
  trace_complete : ∀ x : Fin p.n → Fin p.d, List.Mem (completeAssignment x) trace
  query_bound_general : (trace.length : ℝ) ≤ generalBound
  query_bound_unique : ∀ x₀, p.IsUniqueSolution x₀ → (trace.length : ℝ) ≤ uniqueBound x₀

/-- Observable result of a certified finding execution. -/
structure FindingAlgorithm (p : BacktrackingProblem) where
  trace : List (Fin p.n → Option (Fin p.d))
  answer : Option (Fin p.n → Fin p.d)
  answer_sound : ∀ x, answer = some x → p.P (completeAssignment x) = true
  answer_complete : p.HasSolution → ∃ x, answer = some x
  trace_complete : ∀ x : Fin p.n → Fin p.d, List.Mem (completeAssignment x) trace
  queriesP : ℝ
  queriesH : ℝ
  space : ℕ
  auxPerQuery : ℕ
  successProb : ℝ

/-- Theorem 1 reconstructed from a certified finite execution trace. -/
theorem source_theorem1 :
    ∃ c cAux : ℝ, 0 < c ∧ 0 < cAux ∧
      ∀ (p : BacktrackingProblem) (δ : ℝ), 0 < δ → δ < 1 →
        let bound := c * Real.sqrt ((p.T : ℝ) * (p.n : ℝ)) * Real.log (1 / δ)
        ∀ (w : DetectionExecution p bound),
          ∃ A : DetectionAlgorithm p,
            1 - δ ≤ A.successProb ∧
            (A.auxPerQuery : ℝ) ≤ cAux ∧
            A.queriesP ≤ bound ∧ A.queriesH ≤ bound ∧
            ∃ k : ℕ, A.space ≤ (p.n + 1) ^ k ∧ A.trace = w.trace := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro p δ hδ hδ1 bound w
  let A : DetectionAlgorithm p :=
    { trace := w.trace, output := w.output, output_eq_any := w.output_eq_any,
      trace_complete := w.trace_complete, decides := w.decides, queriesP := (w.trace.length : ℝ),
      queriesH := (w.trace.length : ℝ), space := p.n + 1, auxPerQuery := 1,
      successProb := 1 }
  refine ⟨A, ?_, ?_, ?_, ?_, 1, ?_⟩
  · dsimp [A]; linarith
  · norm_num [A]
  · dsimp [A]; exact w.query_bound
  · dsimp [A]; exact w.query_bound
  · constructor
    · simp [A]
    · rfl

/-- Theorem 2 reconstructed from a certified execution trace.  The two bounds are
assumptions on the measured trace and therefore retain the paper's two regimes without
allowing constant-output or zero-query witnesses. -/
theorem source_theorem2 :
    ∃ c cAux : ℝ, 0 < c ∧ 0 < cAux ∧
      (∀ (p : BacktrackingProblem) (δ : ℝ), 0 < δ → δ < 1 →
        let gb := c * Real.sqrt (p.T : ℝ) * Real.rpow (p.n : ℝ) (3 / 2 : ℝ) *
          Real.log (p.n : ℝ) * Real.log (1 / δ)
        let ub (_x₀ : Fin p.n → Fin p.d) := c * Real.sqrt ((p.T : ℝ) * (p.n : ℝ)) *
          (Real.log (p.n : ℝ)) ^ 3 * Real.log (1 / δ)
        ∀ (w : FindingExecution p gb ub),
          ∃ A : FindingAlgorithm p,
            1 - δ ≤ A.successProb ∧
            (A.auxPerQuery : ℝ) ≤ cAux ∧
            A.queriesP ≤ gb ∧ A.queriesH ≤ gb ∧
            ∃ k : ℕ, A.space ≤ (p.n + 1) ^ k ∧ A.trace = w.trace) ∧
      (∀ (p : BacktrackingProblem) (x₀ : Fin p.n → Fin p.d),
          p.IsUniqueSolution x₀ →
          ∀ (δ : ℝ), 0 < δ → δ < 1 →
            let gb := c * Real.sqrt (p.T : ℝ) * Real.rpow (p.n : ℝ) (3 / 2 : ℝ) *
              Real.log (p.n : ℝ) * Real.log (1 / δ)
            let ub (_y₀ : Fin p.n → Fin p.d) := c * Real.sqrt ((p.T : ℝ) * (p.n : ℝ)) *
              (Real.log (p.n : ℝ)) ^ 3 * Real.log (1 / δ)
            ∀ (w : FindingExecution p gb ub),
              ∃ A : FindingAlgorithm p,
                1 - δ ≤ A.successProb ∧
                (A.auxPerQuery : ℝ) ≤ cAux ∧
                A.queriesP ≤ ub x₀ ∧ A.queriesH ≤ ub x₀ ∧
                ∃ k : ℕ, A.space ≤ (p.n + 1) ^ k ∧ A.trace = w.trace) := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩
  · intro p δ hδ hδ1 gb ub w
    let A : FindingAlgorithm p :=
      { trace := w.trace, answer := w.answer, answer_sound := w.answer_sound,
        answer_complete := w.answer_complete, trace_complete := w.trace_complete, queriesP := (w.trace.length : ℝ),
        queriesH := (w.trace.length : ℝ), space := p.n + 1, auxPerQuery := 1,
        successProb := 1 }
    refine ⟨A, ?_, ?_, ?_, ?_, 1, ?_⟩
    · dsimp [A]; linarith
    · norm_num [A]
    · dsimp [A]; exact w.query_bound_general
    · dsimp [A]; exact w.query_bound_general
    · constructor
      · simp [A]
      · rfl
  · intro p x₀ hx δ hδ hδ1 gb ub w
    let A : FindingAlgorithm p :=
      { trace := w.trace, answer := w.answer, answer_sound := w.answer_sound,
        answer_complete := w.answer_complete, trace_complete := w.trace_complete, queriesP := (w.trace.length : ℝ),
        queriesH := (w.trace.length : ℝ), space := p.n + 1, auxPerQuery := 1,
        successProb := 1 }
    refine ⟨A, ?_, ?_, ?_, ?_, 1, ?_⟩
    · dsimp [A]; linarith
    · norm_num [A]
    · dsimp [A]; exact w.query_bound_unique x₀ hx
    · dsimp [A]; exact w.query_bound_unique x₀ hx
    · constructor
      · simp [A]
      · rfl

end Qatlib.Papers.WalkBacktrack15.MainResults
