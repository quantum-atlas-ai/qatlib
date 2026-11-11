/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Quaternion
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Range
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The computable integer Cayley recurrence

These definitions contain no real numbers or classical choice. Query labels
are exactly the chronological rational times j/D and the requested precision.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Data and hypotheses for Cayley Integer State in the Rational Flow construction. -/
structure CayleyIntegerState where
  numerator : Quaternion ℤ
  denominator : ℤ

/-- Definition of cayley Integer Factor in the Rational Flow construction. -/
def cayleyIntegerFactor (D p : ℕ) (a : Fin 3 → ℤ) : CayleyIntegerState :=
  let base : ℤ := 4*(D : ℤ)^2*(2^p : ℤ)^2
  let sq : ℤ := (a 0)^2+(a 1)^2+(a 2)^2
  ⟨⟨base-sq,4*(D : ℤ)*(2^p : ℤ)*a 0,4*(D : ℤ)*(2^p : ℤ)*a 1,4*(D : ℤ)*(2^p : ℤ)*a 2⟩,base+sq⟩

/-- Definition of cayley Integer Step in the Rational Flow construction. -/
def cayleyIntegerStep (s f : CayleyIntegerState) : CayleyIntegerState :=
  ⟨s.numerator*f.numerator,s.denominator*f.denominator⟩

/-- Definition of cayley Integer Run in the Rational Flow construction. -/
def cayleyIntegerRun (D p : ℕ) (a : ℕ → Fin 3 → ℤ) : ℕ → CayleyIntegerState
  | 0 => ⟨1,1⟩
  | n+1 => cayleyIntegerStep (cayleyIntegerRun D p a n) (cayleyIntegerFactor D p (a n))

/-- Original `cayleyIntegerFactor_den_pos` guarantee for the `CayleyIntegers` construction; the complete source hypotheses are retained. -/
theorem cayleyIntegerFactor_den_pos (D p : ℕ) (hD : 0<D) (a : Fin 3 → ℤ) :
    0<(cayleyIntegerFactor D p a).denominator := by
  have hd : (0 : ℤ)<D := by exact_mod_cast hD
  have hp : (0 : ℤ)<2^p := pow_pos (by norm_num) p
  change 0<4*(D : ℤ)^2*(2^p : ℤ)^2+((a 0)^2+(a 1)^2+(a 2)^2)
  positivity

/-- Original `cayleyIntegerFactor_normSq` guarantee for the `CayleyIntegers` construction; the complete source hypotheses are retained. -/
theorem cayleyIntegerFactor_normSq (D p : ℕ) (a : Fin 3 → ℤ) :
    Quaternion.normSq (cayleyIntegerFactor D p a).numerator=(cayleyIntegerFactor D p a).denominator^2 := by
  simp [cayleyIntegerFactor,Quaternion.normSq_def']
  ring

/-- Original `cayleyIntegerRun_certificate` guarantee for the `CayleyIntegers` construction; the complete source hypotheses are retained. -/
theorem cayleyIntegerRun_certificate (D p : ℕ) (hD : 0<D) (a : ℕ → Fin 3 → ℤ) (n : ℕ) :
    0<(cayleyIntegerRun D p a n).denominator ∧
      Quaternion.normSq (cayleyIntegerRun D p a n).numerator=(cayleyIntegerRun D p a n).denominator^2 := by
  induction n with
  | zero => simp [cayleyIntegerRun]
  | succ n ih =>
    refine ⟨mul_pos ih.1 (cayleyIntegerFactor_den_pos D p hD (a n)),?_⟩
    change Quaternion.normSq ((cayleyIntegerRun D p a n).numerator*
      (cayleyIntegerFactor D p (a n)).numerator)=
      ((cayleyIntegerRun D p a n).denominator*(cayleyIntegerFactor D p (a n)).denominator)^2
    rw [map_mul,ih.2,cayleyIntegerFactor_normSq]
    ring


/-- Definition of cayley Query Schedule in the Rational Flow construction. -/
def cayleyQuerySchedule (D p : ℕ) : List (ℚ × ℕ) :=
  (List.range D).map (fun j : ℕ => ((j : ℚ)/(D : ℚ),p))

/-- Original `cayleyQuerySchedule_length` guarantee for the `CayleyIntegers` construction; the complete source hypotheses are retained. -/
@[simp] theorem cayleyQuerySchedule_length (D p : ℕ) : (cayleyQuerySchedule D p).length=D := by
  simp [cayleyQuerySchedule]

/-- Definition of cayley Run Samples in the Rational Flow construction. -/
def cayleyRunSamples (D p : ℕ) (samples : List (Fin 3 → ℤ)) : CayleyIntegerState :=
  samples.foldl (fun state sample => cayleyIntegerStep state (cayleyIntegerFactor D p sample)) ⟨1,1⟩

/-- Definition of cayley Oracle Execution in the Rational Flow construction. -/
def cayleyOracleExecution (D p : ℕ) (oracle : ℚ × ℕ → Fin 3 → ℤ) : CayleyIntegerState :=
  cayleyRunSamples D p ((cayleyQuerySchedule D p).map oracle)

/-- Original `cayleyRunSamples_range` guarantee for the `CayleyIntegers` construction; the complete source hypotheses are retained. -/
theorem cayleyRunSamples_range (D p : ℕ) (a : ℕ → Fin 3 → ℤ) (n : ℕ) :
    cayleyRunSamples D p ((List.range n).map a)=cayleyIntegerRun D p a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [cayleyRunSamples,cayleyIntegerRun,List.range_succ,List.foldl_append] using
      congrArg (fun s => cayleyIntegerStep s (cayleyIntegerFactor D p (a n))) ih

/-- Original `cayleyOracleExecution_eq` guarantee for the `CayleyIntegers` construction; the complete source hypotheses are retained. -/
theorem cayleyOracleExecution_eq (D p : ℕ) (oracle : ℚ × ℕ → Fin 3 → ℤ) :
    cayleyOracleExecution D p oracle=cayleyIntegerRun D p (fun j : ℕ => oracle ((j : ℚ)/(D : ℚ),p)) D := by
  simp only [cayleyOracleExecution,cayleyQuerySchedule,List.map_map,Function.comp_def]
  exact cayleyRunSamples_range D p _ D

/-- The source runtime charge is explicit and uses the same query labels
that determine the returned integer samples. It is not an arithmetic cost. -/
def cayleyOracleCharge (D p : ℕ) (cost : ℚ × ℕ → ℕ) : ℕ :=
  ((cayleyQuerySchedule D p).map cost).sum

/-- Original `cayleyOracleCharge_le` guarantee for the `CayleyIntegers` construction; the complete source hypotheses are retained. -/
theorem cayleyOracleCharge_le (D p T : ℕ) (cost : ℚ × ℕ → ℕ)
    (hcost : ∀ j < D, cost ((j : ℚ)/(D : ℚ),p) ≤ T) : cayleyOracleCharge D p cost ≤ D*T := by
  simp only [cayleyOracleCharge,cayleyQuerySchedule,List.map_map,Function.comp_def]
  let f := fun j : ℕ => cost ((j : ℚ)/(D : ℚ),p)
  have hs : ∀ n : ℕ, (∀ j < n, f j ≤ T) → ((List.range n).map f).sum ≤ n*T := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro h
      rw [List.range_succ,List.map_append,List.sum_append]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      calc
        _ ≤ n*T+T := Nat.add_le_add (ih (fun j hj => h j (Nat.lt_succ_of_lt hj))) (h n (Nat.lt_succ_self n))
        _ = (n+1)*T := by ring
  exact hs D hcost

/-- Both fields are computed from the same finite list of callback answers.
The fee is reported by the callback, not inferred to be its actual runtime. -/
structure CayleyChargedResult where
  state : CayleyIntegerState
  sourceFee : ℕ

/-- Definition of cayley Charged Execution in the Rational Flow construction. -/
def cayleyChargedExecution (D p : ℕ) (oracle : ℚ × ℕ → (Fin 3 → ℤ) × ℕ) : CayleyChargedResult :=
  let answers := (cayleyQuerySchedule D p).map oracle
  ⟨cayleyRunSamples D p (answers.map Prod.fst),(answers.map Prod.snd).sum⟩

/-- Original `cayleyChargedExecution_state` guarantee for the `CayleyIntegers` construction; the complete source hypotheses are retained. -/
theorem cayleyChargedExecution_state (D p : ℕ) (oracle : ℚ × ℕ → (Fin 3 → ℤ) × ℕ) :
    (cayleyChargedExecution D p oracle).state=cayleyOracleExecution D p (fun label => (oracle label).1) := by
  simp only [cayleyChargedExecution,cayleyOracleExecution,List.map_map,Function.comp_def]

/-- Original `cayleyChargedExecution_fee` guarantee for the `CayleyIntegers` construction; the complete source hypotheses are retained. -/
theorem cayleyChargedExecution_fee (D p : ℕ) (oracle : ℚ × ℕ → (Fin 3 → ℤ) × ℕ) :
    (cayleyChargedExecution D p oracle).sourceFee=cayleyOracleCharge D p (fun label => (oracle label).2) := by
  simp only [cayleyChargedExecution,cayleyOracleCharge,List.map_map,Function.comp_def]

/-- Original `cayleyChargedExecution_fee_le` guarantee for the `CayleyIntegers` construction; the complete source hypotheses are retained. -/
theorem cayleyChargedExecution_fee_le (D p T : ℕ) (oracle : ℚ × ℕ → (Fin 3 → ℤ) × ℕ)
    (hfee : ∀ j < D, (oracle ((j : ℚ)/(D : ℚ),p)).2 ≤ T) :
    (cayleyChargedExecution D p oracle).sourceFee ≤ D*T := by
  rw [cayleyChargedExecution_fee]
  exact cayleyOracleCharge_le D p T _ hfee

end Qatlib.Concepts.EffectiveGauge.RationalFlow
