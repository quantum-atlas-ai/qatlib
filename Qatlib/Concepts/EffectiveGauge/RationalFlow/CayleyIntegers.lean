/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.List.Range
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

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

/-- A positive grid size makes the integer Cayley factor's denominator strictly positive for every
precision and integer triple. -/
theorem cayleyIntegerFactor_den_pos (D p : ℕ) (hD : 0<D) (a : Fin 3 → ℤ) :
    0<(cayleyIntegerFactor D p a).denominator := by
  have hd : (0 : ℤ)<D := by exact_mod_cast hD
  have hp : (0 : ℤ)<2^p := pow_pos (by norm_num) p
  change 0<4*(D : ℤ)^2*(2^p : ℤ)^2+((a 0)^2+(a 1)^2+(a 2)^2)
  positivity

/-- The squared norm of the integer factor's numerator equals the square of its denominator for
every grid size, precision, and sample. -/
theorem cayleyIntegerFactor_normSq (D p : ℕ) (a : Fin 3 → ℤ) :
    Quaternion.normSq (cayleyIntegerFactor D p a).numerator=(cayleyIntegerFactor D p a).denominator^2 := by
  simp [cayleyIntegerFactor,Quaternion.normSq_def']
  ring

/-- Every prefix of the integer Cayley run with positive grid size has positive denominator and
squared numerator norm equal to the squared denominator. -/
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

/-- The schedule contains one query label for each of the `D` left grid endpoints. -/
@[simp] theorem cayleyQuerySchedule_length (D p : ℕ) : (cayleyQuerySchedule D p).length=D := by
  simp [cayleyQuerySchedule]

/-- Definition of cayley Run Samples in the Rational Flow construction. -/
def cayleyRunSamples (D p : ℕ) (samples : List (Fin 3 → ℤ)) : CayleyIntegerState :=
  samples.foldl (fun state sample => cayleyIntegerStep state (cayleyIntegerFactor D p sample)) ⟨1,1⟩

/-- Definition of cayley Oracle Execution in the Rational Flow construction. -/
def cayleyOracleExecution (D p : ℕ) (oracle : ℚ × ℕ → Fin 3 → ℤ) : CayleyIntegerState :=
  cayleyRunSamples D p ((cayleyQuerySchedule D p).map oracle)

/-- Folding the ordered list of the first `n` samples gives the same integer state as running the
recurrence for `n` steps. -/
theorem cayleyRunSamples_range (D p : ℕ) (a : ℕ → Fin 3 → ℤ) (n : ℕ) :
    cayleyRunSamples D p ((List.range n).map a)=cayleyIntegerRun D p a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [cayleyRunSamples,cayleyIntegerRun,List.range_succ,List.foldl_append] using
      congrArg (fun s => cayleyIntegerStep s (cayleyIntegerFactor D p (a n))) ih

/-- The oracle execution equals the `D`-step integer recurrence with sample `j` taken from the query
at rational time `j / D` and precision `p`. -/
theorem cayleyOracleExecution_eq (D p : ℕ) (oracle : ℚ × ℕ → Fin 3 → ℤ) :
    cayleyOracleExecution D p oracle=cayleyIntegerRun D p (fun j : ℕ => oracle ((j : ℚ)/(D : ℚ),p)) D := by
  simp only [cayleyOracleExecution,cayleyQuerySchedule,List.map_map,Function.comp_def]
  exact cayleyRunSamples_range D p _ D

/-- The source runtime charge is explicit and uses the same query labels
that determine the returned integer samples. It is not an arithmetic cost. -/
def cayleyOracleCharge (D p : ℕ) (cost : ℚ × ℕ → ℕ) : ℕ :=
  ((cayleyQuerySchedule D p).map cost).sum

/-- If each scheduled query costs at most `T`, the total charge is at most `D * T`. -/
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

/-- The charged execution's state is exactly the oracle execution that uses the sample component of
every query result. -/
theorem cayleyChargedExecution_state (D p : ℕ) (oracle : ℚ × ℕ → (Fin 3 → ℤ) × ℕ) :
    (cayleyChargedExecution D p oracle).state=cayleyOracleExecution D p (fun label => (oracle label).1) := by
  simp only [cayleyChargedExecution,cayleyOracleExecution,List.map_map,Function.comp_def]

/-- The charged execution's source fee is the sum of the fee components over the scheduled queries. -/
theorem cayleyChargedExecution_fee (D p : ℕ) (oracle : ℚ × ℕ → (Fin 3 → ℤ) × ℕ) :
    (cayleyChargedExecution D p oracle).sourceFee=cayleyOracleCharge D p (fun label => (oracle label).2) := by
  simp only [cayleyChargedExecution,cayleyOracleCharge,List.map_map,Function.comp_def]

/-- A per-query fee bound `T` at all `D` scheduled labels bounds the recorded source fee by `D * T`. -/
theorem cayleyChargedExecution_fee_le (D p T : ℕ) (oracle : ℚ × ℕ → (Fin 3 → ℤ) × ℕ)
    (hfee : ∀ j < D, (oracle ((j : ℚ)/(D : ℚ),p)).2 ≤ T) :
    (cayleyChargedExecution D p oracle).sourceFee ≤ D*T := by
  rw [cayleyChargedExecution_fee]
  exact cayleyOracleCharge_le D p T _ hfee

end Qatlib.Concepts.EffectiveGauge.RationalFlow
