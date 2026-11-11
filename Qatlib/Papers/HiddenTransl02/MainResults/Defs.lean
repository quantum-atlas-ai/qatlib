/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Circuit models and probabilities for hidden translation

This module defines the circuit data `QAlg`, its measurement-based extension `MeasQAlg`, and
elementary algebraic and size predicates for hidden translation. It develops event
probabilities, decoded good and bad outcomes, and the identity
`MeasQAlg.successProb_eq_one_sub_failProb` under normalization and unitarity hypotheses.

The development follows [FriedlEtAl2014].

## Main statements

* `QAlg`: Circuit data with instance-dependent designated outputs and failure values, together
  with query and gate costs certified to equal the circuit counts.
* `MeasQAlg`: A circuit algorithm equipped with an instance-dependent oracle, an initial state,
  a decoder, and a proof that its failure value is the Born weight of incorrectly decoded
  outcomes.
* `MeasQAlg.successProb_eq_one_sub_failProb`: For normalized input and unitary oracle and
  circuit, success probability equals one minus failure probability.

## References

* [Friedl et al., 2014][FriedlEtAl2014]
-/

namespace Qatlib.Papers.HiddenTransl02.MainResults.Defs

open Qatlib.Foundations.QueryWordCore.Circuit
open scoped Classical

set_option autoImplicit false

/-- Circuit data with instance-dependent designated outputs and failure values, together with
query and gate costs certified to equal the circuit counts. -/
structure QAlg (Reg Inst Out : Type*) [Fintype Reg] [DecidableEq Reg] where

  circuit : Circuit Reg

  out : Inst → Out

  failProb : Inst → ℝ

  qcost : ℕ

  tcost : ℕ

  qcost_eq : qcost = QueryCount circuit

  tcost_eq : tcost = GateCount circuit

/-- The coordinate dot product of two vectors over `ZMod p`. -/
def dot {p n : ℕ} (y u : Fin n → ZMod p) : ZMod p :=
  ∑ i, y i * u i

/-- The condition that the false branch of `f` at every `x` equals the true branch at `x + u`. -/
def IsTranslation {p n : ℕ} {S : Type*} (f : (Fin n → ZMod p) × Bool → S)
    (u : Fin n → ZMod p) : Prop :=
  ∀ x, f (x, false) = f (x + u, true)

/-- The predicate that some positive real constant c satisfies ca ≤ t. -/
def IsOmega (t : ℕ) (a : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ c * a ≤ (t : ℝ)

/-- The amplitude function equal to the inverse square root of the cardinality of `S` on `S` and
zero elsewhere. -/
noncomputable def uniformState {I : Type*} [DecidableEq I] (S : Finset I) : I → ℂ :=
  fun i => if i ∈ S then (((Real.sqrt (S.card : ℝ) : ℝ)) : ℂ)⁻¹ else 0

/-- The condition that a finite subset of a group contains the identity and is closed under
multiplication and inverses. -/
def IsSubgroupSet {G : Type*} [Group G] (S : Finset G) : Prop :=
  1 ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧ (∀ a ∈ S, a⁻¹ ∈ S)

/-- The condition that one natural exponent c bounds `f m` by (m + 1)^c for every m. -/
def PolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ m, f m ≤ (m + 1) ^ c

/-- The predicate that t ≤ (n + p)^(cp) for some natural exponent parameter c. -/
def PolyP (n p t : ℕ) : Prop :=
  ∃ c : ℕ, t ≤ (n + p) ^ (c * p)

/-- The predicate that t ≤ (ℓ + 1)^c for some natural exponent c. -/
def PolyEll (ℓ t : ℕ) : Prop :=
  ∃ c : ℕ, t ≤ (ℓ + 1) ^ c

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

noncomputable section

variable {Reg Inst Out : Type*}

section Events

variable [Fintype Reg] [DecidableEq Reg]

/-- The sum of Born weights of the amplitude function `ψ` over the event `S`. -/
def outcomeProb (ψ : QState Reg) (S : Finset Reg) : ℝ := MeasureProb ψ S

/-- Every event has nonnegative Born weight. -/
theorem outcomeProb_nonneg (ψ : QState Reg) (S : Finset Reg) :
    0 ≤ outcomeProb ψ S := measureProb_nonneg ψ S

/-- Inclusion of finite outcome events implies an inequality between their Born weights. -/
theorem outcomeProb_mono {ψ : QState Reg} {S T : Finset Reg} (hST : S ⊆ T) :
    outcomeProb ψ S ≤ outcomeProb ψ T := by
  unfold outcomeProb MeasureProb
  exact Finset.sum_le_sum_of_subset_of_nonneg hST
    (fun i _ _ => bornProb_nonneg ψ i)

/-- A normalized state assigns probability one to the universal event. -/
theorem outcomeProb_univ {ψ : QState Reg} (hψ : Normalized ψ) :
    outcomeProb ψ Finset.univ = 1 :=
  measureProb_univ hψ

/-- Every event in a normalized state has probability at most one. -/
theorem outcomeProb_le_one {ψ : QState Reg} (hψ : Normalized ψ) (S : Finset Reg) :
    outcomeProb ψ S ≤ 1 := by
  rw [← outcomeProb_univ hψ]
  exact outcomeProb_mono (Finset.subset_univ S)

/-- The Born weight of a union is at most the sum of the Born weights of the two events. -/
theorem outcomeProb_union_le (ψ : QState Reg) (S T : Finset Reg) :
    outcomeProb ψ (S ∪ T) ≤ outcomeProb ψ S + outcomeProb ψ T := by
  unfold outcomeProb MeasureProb
  rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union Finset.disjoint_sdiff]
  have h : ∑ i ∈ T \ S, BornProb ψ i ≤ ∑ i ∈ T, BornProb ψ i :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i _ _ => bornProb_nonneg ψ i)
  linarith

/-- The Born weights of an event and its complement sum to the Born weight of the universal
event. -/
theorem outcomeProb_add_compl (ψ : QState Reg) (S : Finset Reg) :
    outcomeProb ψ S + outcomeProb ψ (Finset.univ \ S) = outcomeProb ψ Finset.univ := by
  unfold outcomeProb MeasureProb
  rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
  rw [show S ∪ (Finset.univ : Finset Reg) = Finset.univ by ext i; simp]

end Events

section CircuitEvents

variable [Fintype Reg] [DecidableEq Reg]

/-- The Born weight of `S` after running the circuit with the supplied oracle and initial
amplitude function. -/
def circuitOutcomeProb (oracle : Matrix Reg Reg ℂ) (C : Circuit Reg)
    (init : QState Reg) (S : Finset Reg) : ℝ :=
  outcomeProb (Run oracle C init) S

/-- The Born weight of every circuit output event is nonnegative. -/
theorem circuitOutcomeProb_nonneg (oracle : Matrix Reg Reg ℂ) (C : Circuit Reg)
    (init : QState Reg) (S : Finset Reg) : 0 ≤ circuitOutcomeProb oracle C init S :=
  outcomeProb_nonneg _ _

/-- A circuit output event has probability at most one when the final state is normalized. -/
theorem circuitOutcomeProb_le_one (oracle : Matrix Reg Reg ℂ) (C : Circuit Reg)
    (init : QState Reg) (S : Finset Reg)
    (hψ : Normalized (Run oracle C init)) :
    circuitOutcomeProb oracle C init S ≤ 1 :=
  outcomeProb_le_one hψ S

/-- A circuit output event has probability at most one for a unitary oracle, a unitary circuit,
and a normalized input. -/
theorem circuitOutcomeProb_le_one_of_unitary (oracle : Matrix Reg Reg ℂ)
    (C : Circuit Reg) (init : QState Reg) (S : Finset Reg)
    (horacle : oracle ∈ Matrix.unitaryGroup Reg ℂ) (hC : IsUnitaryCircuit C)
    (hinit : Normalized init) :
    circuitOutcomeProb oracle C init S ≤ 1 :=
  circuitOutcomeProb_le_one _ _ _ _ (IsUnitaryCircuit.normalized_run hC horacle hinit)

/-- The probability weight of a union of circuit output events is at most the sum of their
individual weights. -/
theorem circuitOutcomeProb_union_le (oracle : Matrix Reg Reg ℂ) (C : Circuit Reg)
    (init : QState Reg) (S T : Finset Reg) :
    circuitOutcomeProb oracle C init (S ∪ T) ≤
      circuitOutcomeProb oracle C init S + circuitOutcomeProb oracle C init T :=
  outcomeProb_union_le _ _ _

/-- The event weight after the appended circuit `C ++ D` equals that after running `D` on the
state produced by `C`. -/
theorem circuitOutcomeProb_append (oracle : Matrix Reg Reg ℂ) (C D : Circuit Reg)
    (init : QState Reg) (S : Finset Reg) :
    circuitOutcomeProb oracle (C ++ D) init S =
      circuitOutcomeProb oracle D (Run oracle C init) S := by
  unfold circuitOutcomeProb
  rw [run_append]

end CircuitEvents

section Faithful

variable [Fintype Reg] [DecidableEq Reg] [DecidableEq Out]

/-- The finite set of register outcomes whose decoded value differs from the designated answer. -/
def badOutcomes (decode : Reg → Out) (answer : Out) : Finset Reg :=
  Finset.univ.filter fun i => decode i ≠ answer

/-- The finite set of register outcomes whose decoded value equals the designated answer. -/
def goodOutcomes (decode : Reg → Out) (answer : Out) : Finset Reg :=
  Finset.univ.filter fun i => decode i = answer

/-- The bad outcomes are the complement of the good outcomes in the universal register set. -/
theorem badOutcomes_eq_sdiff (decode : Reg → Out) (answer : Out) :
    badOutcomes decode answer = Finset.univ \ goodOutcomes decode answer := by
  unfold badOutcomes goodOutcomes
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]

/-- A circuit algorithm equipped with an instance-dependent oracle, an initial state, a decoder,
and a proof that its failure value is the Born weight of incorrectly decoded outcomes. -/
structure MeasQAlg (Reg Inst Out : Type*) [Fintype Reg] [DecidableEq Reg]
    [DecidableEq Out] extends QAlg Reg Inst Out where

  oracle : Inst → Matrix Reg Reg ℂ

  init : QState Reg

  decode : Reg → Out

  failProb_eq : ∀ inst : Inst,
    failProb inst = circuitOutcomeProb (oracle inst) circuit init
      (badOutcomes decode (out inst))

/-- The Born weight of outcomes decoding to the algorithm’s designated output on the given
instance. -/
def MeasQAlg.successProb (A : MeasQAlg Reg Inst Out) (inst : Inst) : ℝ :=
  circuitOutcomeProb (A.oracle inst) A.circuit A.init
    (goodOutcomes A.decode (A.out inst))

/-- The failure value of a measurement-based algorithm is nonnegative. -/
theorem MeasQAlg.failProb_nonneg (A : MeasQAlg Reg Inst Out) (inst : Inst) :
    0 ≤ A.failProb inst := by
  rw [A.failProb_eq inst]
  exact circuitOutcomeProb_nonneg _ _ _ _

/-- For normalized input and unitary oracle and circuit, the failure probability of a
measurement-based algorithm is at most one ([Theorem 3.5][FriedlEtAl2014]). -/
theorem MeasQAlg.failProb_le_one (A : MeasQAlg Reg Inst Out) (inst : Inst)
    (hinit : Normalized A.init)
    (horacle : A.oracle inst ∈ Matrix.unitaryGroup Reg ℂ)
    (hC : IsUnitaryCircuit A.circuit) :
    A.failProb inst ≤ 1 := by
  rw [A.failProb_eq inst]
  exact circuitOutcomeProb_le_one_of_unitary _ _ _ _ horacle hC hinit

/-- For normalized input and unitary oracle and circuit, success probability equals one minus
failure probability ([Theorem 3.5][FriedlEtAl2014]). -/
theorem MeasQAlg.successProb_eq_one_sub_failProb (A : MeasQAlg Reg Inst Out)
    (inst : Inst) (hinit : Normalized A.init)
    (horacle : A.oracle inst ∈ Matrix.unitaryGroup Reg ℂ)
    (hC : IsUnitaryCircuit A.circuit) :
    A.successProb inst = 1 - A.failProb inst := by
  have hnorm : Normalized (Run (A.oracle inst) A.circuit A.init) :=
    IsUnitaryCircuit.normalized_run hC horacle hinit
  have hpart := outcomeProb_add_compl (Run (A.oracle inst) A.circuit A.init)
    (goodOutcomes A.decode (A.out inst))
  rw [outcomeProb_univ hnorm] at hpart
  have hbad : A.failProb inst =
      circuitOutcomeProb (A.oracle inst) A.circuit A.init
        (Finset.univ \ goodOutcomes A.decode (A.out inst)) := by
    rw [A.failProb_eq inst, badOutcomes_eq_sdiff]
  unfold MeasQAlg.successProb
  rw [hbad]
  unfold circuitOutcomeProb
  linarith

end Faithful

section Identity

variable [Fintype Reg] [DecidableEq Reg] [Inhabited Reg]

/-- The measurement-based algorithm with empty circuit, identity oracle, default basis input,
constant unit-valued decoder, and zero failure and resource costs. -/
def identityQAlg (Inst : Type*) : MeasQAlg Reg Inst Unit where
  circuit := []
  out := fun _ => ()
  failProb := fun _ => 0
  qcost := 0
  tcost := 0
  qcost_eq := rfl
  tcost_eq := rfl
  oracle := fun _ => 1
  init := Ket (default : Reg)
  decode := fun _ => ()
  failProb_eq := by
    intro inst
    have hbad : badOutcomes (fun _ : Reg => ()) () = ∅ := by
      unfold badOutcomes
      rw [Finset.filter_false_of_mem]
      simp
    rw [hbad]
    unfold circuitOutcomeProb outcomeProb
    simp [MeasureProb, Run]

/-- The identity algorithm succeeds with probability one on every instance. -/
theorem identityQAlg_successProb (Inst : Type*) (inst : Inst) :
    (identityQAlg (Reg := Reg) Inst).successProb inst = 1 := by
  have hgood : goodOutcomes (fun _ : Reg => ()) () = Finset.univ := by
    unfold goodOutcomes
    rw [Finset.filter_true_of_mem]
    simp
  unfold MeasQAlg.successProb
  rw [hgood]
  unfold circuitOutcomeProb outcomeProb
  have hrun : Run ((identityQAlg (Reg := Reg) Inst).oracle inst)
      (identityQAlg (Reg := Reg) Inst).circuit
      (identityQAlg (Reg := Reg) Inst).init = Ket (default : Reg) := rfl
  rw [hrun]
  exact measureProb_univ (normalized_ket (default : Reg))

end Identity

end
end Qatlib.Papers.HiddenTransl02.MainResults.Defs
