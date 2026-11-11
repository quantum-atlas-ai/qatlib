/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Hybrid error bounds for query circuits

Gate application and circuit execution satisfy Euclidean norm bounds. For unitary oracles and
unitary circuits, replacing the oracle changes the output by at most the query count times the
operator norm difference times the input norm. `norm_repeatRun_sub_repeatRun_le` specializes
this bound to repeated circuits.

The mathematical background is described in [NielsenChuang2010].

## Main statements

* `norm_run_sub_run_le_queryCount`: bounds output error by oracle error and query count.
* `norm_repeatRun_sub_repeatRun_le`: gives the corresponding repeated-circuit estimate.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath.Reflection
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.LchsSimulation.StaticLchs

open Matrix

open scoped Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The Euclidean norm after applying a matrix is at most its operator norm times the input
Euclidean norm. -/
theorem norm_applyGate_le (U : Matrix I I ℂ) (ψ : QState I) :
    ‖toEuclidean_fromVec (ApplyGate U ψ)‖ ≤ ‖U‖ * ‖toEuclidean_fromVec ψ‖ := by
  have h := Matrix.l2_opNorm_mulVec U (toEuclidean_fromVec ψ)
  rwa [show (EuclideanSpace.equiv I ℂ).symm (U *ᵥ toEuclidean_fromVec ψ)
      = toEuclidean_fromVec (ApplyGate U ψ) from rfl] at h

/-- Applying a unitary matrix preserves the Euclidean norm of a state. -/
theorem norm_applyGate_of_mem_unitaryGroup {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) :
    ‖toEuclidean_fromVec (ApplyGate U ψ)‖ = ‖toEuclidean_fromVec ψ‖ := by
  have h := norm_toEuclideanCLM_of_mem_unitaryGroup hU (toEuclidean_fromVec ψ)
  rw [toEuclideanCLM_applyGate] at h
  exact h

omit [DecidableEq I] in

/-- Circuit execution preserves subtraction of input states. -/
theorem run_sub (oracle : Matrix I I ℂ) : ∀ (C : Circuit I) (ψ φ : QState I),
    Run oracle C (ψ - φ) = Run oracle C ψ - Run oracle C φ := by
  intro C
  induction C with
  | nil => intro ψ φ; rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      intro ψ φ
      show Run oracle C (ApplyGate U (ψ - φ))
        = Run oracle C (ApplyGate U ψ) - Run oracle C (ApplyGate U φ)
      simp only [ApplyGate, Matrix.mulVec_sub]
      exact ih (ApplyGate U ψ) (ApplyGate U φ)
    | query =>
      intro ψ φ
      show Run oracle C (ApplyGate oracle (ψ - φ))
        = Run oracle C (ApplyGate oracle ψ) - Run oracle C (ApplyGate oracle φ)
      simp only [ApplyGate, Matrix.mulVec_sub]
      exact ih (ApplyGate oracle ψ) (ApplyGate oracle φ)

/-- Execution with a unitary oracle and a unitary circuit does not increase the Euclidean norm. -/
theorem norm_run_le (oracle : Matrix I I ℂ) (horacle : oracle ∈ Matrix.unitaryGroup I ℂ)
    {C : Circuit I} (hC : IsUnitaryCircuit C) (ψ : QState I) :
    ‖toEuclidean_fromVec (Run oracle C ψ)‖ ≤ ‖toEuclidean_fromVec ψ‖ := by
  induction C generalizing ψ with
  | nil => exact le_rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      have hU : U ∈ Matrix.unitaryGroup I ℂ := hC U List.mem_cons_self
      have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
      have h := ih (ψ := ApplyGate U ψ) (hC := hC')
      simpa only [Run, norm_applyGate_of_mem_unitaryGroup hU] using h
    | query =>
      have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
      have h := ih (ψ := ApplyGate oracle ψ) (hC := hC')
      simpa only [Run, norm_applyGate_of_mem_unitaryGroup horacle] using h

/-- Replacing one unitary oracle by another in a unitary circuit changes the output by at most
the query count times the oracle operator norm difference times the input norm. -/
theorem norm_run_sub_run_le_queryCount (O P : Matrix I I ℂ) (C : Circuit I) (ψ : QState I)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (hP : P ∈ Matrix.unitaryGroup I ℂ)
    (hC : IsUnitaryCircuit C) :
    ‖toEuclidean_fromVec (Run O C ψ - Run P C ψ)‖
      ≤ (QueryCount C : ℝ) * ‖O - P‖ * ‖toEuclidean_fromVec ψ‖ := by
  induction C generalizing ψ with
  | nil => simp [toEuclidean_fromVec]
  | cons s C ih =>
    cases s with
    | gate U =>

      have hU : U ∈ Matrix.unitaryGroup I ℂ := hC U List.mem_cons_self
      have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
      have h := ih (ψ := ApplyGate U ψ) (hC := hC')
      rw [norm_applyGate_of_mem_unitaryGroup hU] at h
      simpa only [Run, QueryCount] using h
    | query =>
      have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)

      have hsplit :
          Run O (Step.query :: C) ψ - Run P (Step.query :: C) ψ
            = Run O C (ApplyGate O ψ - ApplyGate P ψ)
              + (Run O C (ApplyGate P ψ) - Run P C (ApplyGate P ψ)) := by
        show Run O C (ApplyGate O ψ) - Run P C (ApplyGate P ψ)
          = Run O C (ApplyGate O ψ - ApplyGate P ψ)
            + (Run O C (ApplyGate P ψ) - Run P C (ApplyGate P ψ))
        rw [run_sub O C]
        module
      have hstep : ‖toEuclidean_fromVec (ApplyGate O ψ - ApplyGate P ψ)‖
          ≤ ‖O - P‖ * ‖toEuclidean_fromVec ψ‖ := by
        have hsub : ApplyGate O ψ - ApplyGate P ψ = ApplyGate (O - P) ψ := by
          show O.mulVec ψ - P.mulVec ψ = (O - P).mulVec ψ
          rw [Matrix.sub_mulVec]
        rw [hsub]
        exact norm_applyGate_le (O - P) ψ
      have hhead : ‖toEuclidean_fromVec (Run O C (ApplyGate O ψ - ApplyGate P ψ))‖
          ≤ ‖O - P‖ * ‖toEuclidean_fromVec ψ‖ :=
        (norm_run_le O hO hC' _).trans hstep
      have htail : ‖toEuclidean_fromVec (Run O C (ApplyGate P ψ) - Run P C (ApplyGate P ψ))‖
          ≤ (QueryCount C : ℝ) * ‖O - P‖ * ‖toEuclidean_fromVec ψ‖ := by
        have h := ih (ψ := ApplyGate P ψ) (hC := hC')
        rw [norm_applyGate_of_mem_unitaryGroup hP] at h
        exact h
      have hsum :
          ‖toEuclidean_fromVec (Run O C (ApplyGate O ψ - ApplyGate P ψ)
            + (Run O C (ApplyGate P ψ) - Run P C (ApplyGate P ψ)))‖
            ≤ ‖toEuclidean_fromVec (Run O C (ApplyGate O ψ - ApplyGate P ψ))‖
              + ‖toEuclidean_fromVec (Run O C (ApplyGate P ψ) - Run P C (ApplyGate P ψ))‖ := by
        have h := norm_add_le (toEuclidean_fromVec (Run O C (ApplyGate O ψ - ApplyGate P ψ)))
          (toEuclidean_fromVec (Run O C (ApplyGate P ψ) - Run P C (ApplyGate P ψ)))
        rw [show toEuclidean_fromVec (Run O C (ApplyGate O ψ - ApplyGate P ψ))
              + toEuclidean_fromVec (Run O C (ApplyGate P ψ) - Run P C (ApplyGate P ψ))
            = toEuclidean_fromVec (Run O C (ApplyGate O ψ - ApplyGate P ψ)
              + (Run O C (ApplyGate P ψ) - Run P C (ApplyGate P ψ))) from rfl] at h
        exact h
      rw [hsplit]
      calc ‖toEuclidean_fromVec (Run O C (ApplyGate O ψ - ApplyGate P ψ)
              + (Run O C (ApplyGate P ψ) - Run P C (ApplyGate P ψ)))‖
            ≤ ‖toEuclidean_fromVec (Run O C (ApplyGate O ψ - ApplyGate P ψ))‖
                + ‖toEuclidean_fromVec (Run O C (ApplyGate P ψ) - Run P C (ApplyGate P ψ))‖ :=
          hsum
        _ ≤ ‖O - P‖ * ‖toEuclidean_fromVec ψ‖
              + ((QueryCount C : ℝ) * ‖O - P‖ * ‖toEuclidean_fromVec ψ‖) :=
          add_le_add hhead htail
        _ = ((QueryCount (Step.query :: C) : ℕ) : ℝ) * ‖O - P‖
              * ‖toEuclidean_fromVec ψ‖ := by
              simp only [queryCount_query, Nat.cast_add, Nat.cast_one]
              ring

/-- For `k` repetitions of a unitary circuit, the output difference under two unitary oracles is
bounded by `k * QueryCount C` times their operator norm difference times the input norm. -/
theorem norm_repeatRun_sub_repeatRun_le (O P : Matrix I I ℂ) (C : Circuit I) (ψ : QState I)
    (k : ℕ) (hO : O ∈ Matrix.unitaryGroup I ℂ) (hP : P ∈ Matrix.unitaryGroup I ℂ)
    (hC : IsUnitaryCircuit C) :
    ‖toEuclidean_fromVec (Run O (RepeatCircuit C k) ψ - Run P (RepeatCircuit C k) ψ)‖
      ≤ ((k * QueryCount C : ℕ) : ℝ) * ‖O - P‖ * ‖toEuclidean_fromVec ψ‖ := by
  have h := norm_run_sub_run_le_queryCount O P (RepeatCircuit C k) ψ hO hP (hC.repeatCircuit k)
  rw [queryCount_repeatCircuit] at h
  simpa using h

end Qatlib.Concepts.LchsSimulation.StaticLchs
