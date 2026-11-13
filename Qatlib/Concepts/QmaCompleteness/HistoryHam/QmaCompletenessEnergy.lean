/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessDefs
import Qatlib.Concepts.QmaCompleteness.HistoryHam.SpectralForrelation

/-!
# Energy estimates for rounded history Hamiltonians

This module constructs the exact circuit history `qmaExactHistory` and its uniform clock
superposition `qmaHistoryState`. It proves normalization, boundary energy identities, support
bounds, and entry bounds for the history Hamiltonian. A one-gate example in
`clause2_counter_clause5` shows that the real dyadic predicate `qmaIsDyadic` cannot describe
every rounded complex entry.

The main soundness estimate `g2c2_clause2` bounds the energy of every normalized history vector
using an acceptance bound for all legal normalized inputs. Its proof controls propagation
residuals, initialization violations, and rounding errors, following the history-Hamiltonian
method of [KempeKitaevRegev2006].

## Main statements

* `normalized_qmaHistoryState`: normalization of the uniform history of a normalized input.
* `qmaEnergy_outTerm`: output energy equals rejection weight divided by the number of clock
  positions.
* `clause2_clause3` and `clause2_clause4`: declared support bounds and matrix entry bounds.
* `g2c2_clause2`: a variational NO energy lower bound with an explicit rounding correction.
* `clause2_counter_clause5`: failure of a universal real dyadic entry claim.

## References

* [Kempe, Kitaev and Regev, 2006][KempeKitaevRegev2006]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.QmaCompleteness.HistoryHam

/-- A tensor gate entry is the product of the corresponding entries of its two factors. -/
private theorem tensorGate_entry {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (U : Matrix I I ℂ) (V : Matrix J J ℂ) (p q : I × J) :
    TensorGate U V p q = U p.1 q.1 * V p.2 q.2 := by
  cases p
  cases q
  exact tensorGate_apply U V _ _ _ _

/-- The single-qubit circuit consisting of one T gate, with no initialized wires and output wire
zero. -/
private def counterC : QmaHistoryCircuit where
  qubits := 1
  gates := [FiniteGateCode.t 0]
  legal := by simp [finiteWordLegal, finiteCodeLegal]
  initZeroWires := ∅
  outputWire := 0

/-- The basis pair with final clock position and a true work bit in the one-gate counterexample. -/
private def cP : Fin 2 × Reg 1 := ((0 : Fin 1).succ, fun _ => true)

/-- The basis pair with initial clock position and a true work bit in the one-gate
counterexample. -/
private def cQ : Fin 2 × Reg 1 := ((0 : Fin 1).castSucc, fun _ => true)

/-- The true-to-true entry of the T gate is `exp (π * I / 4)`. -/
private theorem tGate_true_true :
    tGate true true = Complex.exp ((Real.pi / 4 : ℂ) * Complex.I) := by
  simp [tGate, Rz]

/-- The rounded gate family of `counterC` at precision 70 is the constant family containing its
rounded T gate. -/
private theorem counter_U_fun :
    qmaRoundedGates counterC 70 = fun _ : Fin 1 => qmaRoundedGate 1 70 (FiniteGateCode.t 0) := by
  funext t
  rw [Fin.eq_zero t]
  rfl

/-- The true-to-true entry of the encoded single-qubit T gate is `exp (π * I / 4)`. -/
private theorem counter_gateEntry :
    finiteCodeMatrix 1 (FiniteGateCode.t 0) (fun _ => true) (fun _ => true)
      = Complex.exp ((Real.pi / 4 : ℂ) * Complex.I) := by
  have h01 : (0 : ℕ) < 1 := by norm_num
  rw [finiteCodeMatrix, dif_pos h01, wireGate_apply,
    if_pos (fun (k : Fin 1) (_ : k ≠ (⟨0, h01⟩ : Fin 1)) => rfl), tGate_true_true]

/-- The selected propagation entry of the counterexample is minus one half of the rounded T
phase. -/
private theorem counter_propEntry :
    qmaPropTerm 1 1 (qmaRoundedGates counterC 70) 0 cP cQ
      = -(1 / 2 : ℂ) * qmaRoundC 70 (Complex.exp ((Real.pi / 4 : ℂ) * Complex.I)) := by
  rw [counter_U_fun]
  have hsucc : (0 : Fin 1).succ = (1 : Fin 2) := rfl
  have hcast : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
  have hne10 : ¬ ((1 : Fin 2) = 0) := by decide
  have hne01 : ¬ ((0 : Fin 2) = 1) := by decide
  have hOne : (1 : Matrix (Reg 1) (Reg 1) ℂ) (fun _ => true) (fun _ => true) = 1 := by
    simp
  simp only [cP, cQ, qmaPropTerm, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, tensorGate_entry, qmaClockTerm, Qatlib.Foundations.PureStateMath.Ket, hsucc, hcast, hne10, hne01,
    Matrix.of_apply, Matrix.conjTranspose_apply, qmaRoundedGate, hOne, reduceIte,
    counter_gateEntry, zero_mul, mul_zero, one_mul, zero_add, sub_zero, mul_one]
  ring

/-- The real and imaginary parts of the counterexample's T phase both equal `sqrt 2 / 2`. -/
private theorem counter_exp_re_im :
    (Complex.exp ((Real.pi / 4 : ℂ) * Complex.I)).re = Real.sqrt 2 / 2 ∧
    (Complex.exp ((Real.pi / 4 : ℂ) * Complex.I)).im = Real.sqrt 2 / 2 := by
  rw [show ((Real.pi : ℂ) / 4) * Complex.I = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I from by
      push_cast
      ring, Complex.exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four]
  constructor <;> simp

/-- The scaled T-phase component used in precision-70 rounding is at least one after adding one
half. -/
private theorem counter_floor_ge_one :
    (1 : ℝ) ≤ (Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2 := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt ((by norm_num : (1 : ℝ) ≤ 2))
    rwa [Real.sqrt_one] at h
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 70 := by
    have hn := Nat.one_le_two_pow (n := 70)
    exact_mod_cast hn
  have h3 : (1 : ℝ) / 2 * (2 : ℝ) ^ 70 ≤ (Real.sqrt 2 / 2) * (2 : ℝ) ^ 70 := by
    apply mul_le_mul_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 70)
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hhalf : (1 : ℝ) / 2 * 2 = 1 := by ring
    rw [hhalf]
    exact h1
  have h4 : (1 : ℝ) / 2 ≤ (1 : ℝ) / 2 * (2 : ℝ) ^ 70 := by
    calc (1 : ℝ) / 2 = (1 : ℝ) / 2 * 1 := by ring
      _ ≤ (1 : ℝ) / 2 * (2 : ℝ) ^ 70 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  linarith

/-- Expands the precision-70 rounded T phase using the common integer floor numerator for its
real and imaginary parts. -/
private theorem counter_round_val :
    qmaRoundC 70 (Complex.exp ((Real.pi / 4 : ℂ) * Complex.I))
      = (((Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) : ℤ) : ℂ)
          + Complex.I * ((Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) : ℤ) : ℂ))
        / ((2 : ℂ) ^ 70) := by
  rw [qmaRoundC, counter_exp_re_im.1, counter_exp_re_im.2]

/-- The imaginary part of minus twice a Gaussian integer is minus twice its imaginary integer
component. -/
private theorem im_neg2_mul (n₁ n₂ : ℤ) :
    Complex.im ((-2 : ℂ) * (((n₁ : ℤ) : ℂ) + Complex.I * ((n₂ : ℤ) : ℂ)))
      = -(2 : ℝ) * ((n₂ : ℤ) : ℝ) := by
  have hexp : (-2 : ℂ) * (((n₁ : ℤ) : ℂ) + Complex.I * ((n₂ : ℤ) : ℂ))
      = ((-2 : ℂ) * ((n₁ : ℤ) : ℂ)) + Complex.I * ((-2 : ℂ) * ((n₂ : ℤ) : ℂ)) := by
    ring
  rw [hexp]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp

/-- An integer cast to the complex numbers has zero imaginary part. -/
private theorem im_intCast_zero (num : ℤ) : Complex.im ((num : ℤ) : ℂ) = 0 := by
  simp

/-- The rounded history terms do not universally have real dyadic entries at the proposed
precision. -/
theorem clause2_counter_clause5 :
    ¬ (∀ C : QmaHistoryCircuit,
        ∀ t ∈ qmaHistoryTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64)),
          ∀ p : Fin (C.gates.length + 1) × Reg C.qubits,
            ∀ q : Fin (C.gates.length + 1) × Reg C.qubits,
              qmaIsDyadic (3 * (C.qubits + C.gates.length) + 64 + 2) (t.matrix p q)) := by
  intro h
  have hb : 3 * (counterC.qubits + counterC.gates.length) + 64 = 70 := rfl
  have hb2 : 3 * (counterC.qubits + counterC.gates.length) + 64 + 2 = 72 := rfl
  specialize h counterC
  rw [hb2, hb] at h
  have hmem : (⟨{(0 : Fin 1).castSucc, (0 : Fin 1).succ},
      (qmaGateWires 1 (FiniteGateCode.t 0)).toFinset,
      qmaPropTerm 1 1 (qmaRoundedGates counterC 70) (0 : Fin 1)⟩ : QmaHistoryTerm 1 1)
      ∈ qmaHistoryTerms counterC (qmaRoundedGates counterC 70) := by
    have h1 : qmaHistoryTerms counterC (qmaRoundedGates counterC 70)
        = qmaHistoryPropTerms counterC (qmaRoundedGates counterC 70)
          ++ qmaHistoryInTerms counterC ++ qmaHistoryOutTerm counterC := rfl
    have h2 : qmaHistoryPropTerms counterC (qmaRoundedGates counterC 70)
        = [⟨{(0 : Fin 1).castSucc, (0 : Fin 1).succ},
           (qmaGateWires 1 (FiniteGateCode.t 0)).toFinset,
           qmaPropTerm 1 1 (qmaRoundedGates counterC 70) (0 : Fin 1)⟩] := by
      show (List.finRange 1).map
        (fun i : Fin 1 =>
          { clockSupport := {i.castSucc, i.succ}
            workSupport := (qmaGateWires 1 (qmaGateAt [FiniteGateCode.t 0] i.val)).toFinset
            matrix := qmaPropTerm 1 1 (qmaRoundedGates counterC 70) i :
              QmaHistoryTerm 1 1 }) = _
      rfl
    have h3 : qmaHistoryInTerms counterC = [] := by simp [qmaHistoryInTerms, counterC]
    rw [h1, h2, h3]
    exact List.Mem.head _
  specialize h _ hmem cP cQ
  have h' : qmaIsDyadic 72
      (qmaPropTerm 1 1 (qmaRoundedGates counterC 70) 0 cP cQ) := h
  rw [counter_propEntry] at h'
  obtain ⟨num, hnum⟩ := h'
  rw [counter_round_val] at hnum
  have h72 : ((2 : ℂ) ^ 72) = 4 * ((2 : ℂ) ^ 70) := by
    have h : ((2 : ℂ) ^ 72) = ((2 : ℂ) ^ 70) * ((2 : ℂ) ^ 2) := by rw [← pow_add]
    rw [h]
    norm_num
  have hne0 : ((2 : ℂ) ^ 70) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hmul : ((-(1 / 2 : ℂ)) *
      ((((Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) : ℤ) : ℂ)
          + Complex.I * ((Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) : ℤ) : ℂ))
        / ((2 : ℂ) ^ 70))) * ((2 : ℂ) ^ 72) = (num : ℂ) := by
    have hcancel : ∀ a : ℂ, a / ((2 : ℂ) ^ 72) * ((2 : ℂ) ^ 72) = a :=
      fun a => div_mul_cancel₀ a (pow_ne_zero 72 (two_ne_zero : (2 : ℂ) ≠ 0))
    rw [hnum, hcancel]
  have hL : ((-(1 / 2 : ℂ)) *
      ((((Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) : ℤ) : ℂ)
          + Complex.I * ((Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) : ℤ) : ℂ))
        / ((2 : ℂ) ^ 70))) * ((2 : ℂ) ^ 72)
      = (-2 : ℂ) * (((Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) : ℤ) : ℂ)
          + Complex.I * ((Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) : ℤ) : ℂ)) := by
    rw [h72]
    field_simp
    ring
  rw [hL] at hmul
  have hn2 : (1 : ℤ) ≤ Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) := by
    have h := counter_floor_ge_one
    exact Int.le_floor.mpr (by exact_mod_cast h)
  have him := im_neg2_mul
    (Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) : ℤ)
    (Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) : ℤ)
  have h2 := congrArg Complex.im hmul
  rw [him, im_intCast_zero] at h2
  have hpos : (0 : ℝ) < ((Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) : ℤ) : ℝ) := by
    have hc : (1 : ℝ) ≤ ((Int.floor ((Real.sqrt 2 / 2) * ((2 : ℝ) ^ 70) + 1 / 2) : ℤ) : ℝ) := by
      exact_mod_cast hn2
    linarith
  linarith

section Clause2Clause6

/-- The rounded history term list has length at most the gate count plus the qubit count plus
one. -/
theorem clause2_clause6 :
    ∀ C : QmaHistoryCircuit,
      (qmaHistoryTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))).length
        ≤ C.gates.length + C.qubits + 1 := by
  intro C
  rw [qmaHistoryTerms, List.length_append, List.length_append, qmaHistoryPropTerms,
    qmaHistoryInTerms, qmaHistoryOutTerm, List.length_map, List.length_map,
    List.length_singleton]
  have hm : (List.finRange C.gates.length).length = C.gates.length := by simp
  have hcard : C.initZeroWires.toList.length ≤ C.qubits := by
    rw [Finset.length_toList]
    exact Nat.le_trans (Finset.card_le_card (Finset.subset_univ C.initZeroWires))
      (le_of_eq (Fintype.card_fin C.qubits))
  omega

end Clause2Clause6

/-- The conjunction of the two energy bounds, support bounds, entry bounds, real dyadic entry
claim, and term-count bound fails as a universal statement over history circuits. -/
theorem clause2_counter : ¬
    (∀ C : QmaHistoryCircuit,
      (∀ a : ℝ,
        (∃ φ : QState (Reg C.qubits), QmaInitLegal C φ ∧ Normalized φ ∧
          a ≤ qmaHistoryAcceptProb C φ) →
        ∃ η : QState (Fin (C.gates.length + 1) × Reg C.qubits), Normalized η ∧
          qmaEnergy (qmaHistoryHamiltonian C
            (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))) η
            ≤ (1 - a) / (C.gates.length + 1)
              + qmaTiny (C.qubits + C.gates.length + 2))
      ∧ (∀ ε : ℝ,
        (∀ φ : QState (Reg C.qubits), QmaInitLegal C φ → Normalized φ →
          qmaHistoryAcceptProb C φ ≤ ε) →
        ∀ η : QState (Fin (C.gates.length + 1) × Reg C.qubits), Normalized η →
          (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3)
            - qmaTiny (C.qubits + C.gates.length + 2)
            ≤ qmaEnergy (qmaHistoryHamiltonian C
                (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))) η)
      ∧ (∀ t ∈ qmaHistoryTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64)),
          qmaActsOn C.qubits C.gates.length t.matrix t.clockSupport t.workSupport
            ∧ t.clockSupport.card ≤ 2 ∧ t.workSupport.card ≤ 2)
      ∧ (∀ t ∈ qmaHistoryTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64)),
          ∀ p : Fin (C.gates.length + 1) × Reg C.qubits,
            ∀ q : Fin (C.gates.length + 1) × Reg C.qubits, ‖t.matrix p q‖ ≤ 1)
      ∧ (∀ t ∈ qmaHistoryTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64)),
          ∀ p : Fin (C.gates.length + 1) × Reg C.qubits,
            ∀ q : Fin (C.gates.length + 1) × Reg C.qubits,
              qmaIsDyadic (3 * (C.qubits + C.gates.length) + 64 + 2) (t.matrix p q))
      ∧ (qmaHistoryTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))).length
          ≤ C.gates.length + C.qubits + 1) := by
  intro h
  exact clause2_counter_clause5 (fun C => (((h C).2).2).2.2.1)

/-- Entrywise complex rounding sends zero to zero at every precision. -/
theorem qmaRoundC_zero (b : ℕ) : qmaRoundC b 0 = 0 := by
  unfold qmaRoundC
  have h1 : (Int.floor ((0 : ℝ) * 2 ^ b + 1 / 2) : ℤ) = 0 := by norm_num
  rw [Complex.zero_re, Complex.zero_im, h1]
  push_cast
  simp

/-- The norm of a rounded complex number is at most the sum of its absolute components plus
`2⁻ᵇ`. -/
theorem qmaRoundC_norm_le (b : ℕ) (z : ℂ) :
    ‖qmaRoundC b z‖ ≤ |z.re| + |z.im| + 1 / 2 ^ b := by
  have hre : ∀ x : ℝ, |(Int.floor (x + 1 / 2) : ℝ)| ≤ |x| + 1 / 2 := by
    intro x
    have h1 : (Int.floor (x + 1 / 2) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
    have h2 : x + 1 / 2 < (Int.floor (x + 1 / 2) : ℝ) + 1 := Int.lt_floor_add_one _
    have h4 : |(Int.floor (x + 1 / 2) : ℝ) - x| ≤ 1 / 2 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    calc |(Int.floor (x + 1 / 2) : ℝ)|
          = |x + ((Int.floor (x + 1 / 2) : ℝ) - x)| := by ring_nf
      _ ≤ |x| + |(Int.floor (x + 1 / 2) : ℝ) - x| := abs_add_le _ _
      _ ≤ |x| + 1 / 2 := by linarith
  have hpowb : (0 : ℝ) < 2 ^ b := pow_pos two_pos b
  have hI : Complex.I * ((Int.floor (z.im * 2 ^ b + 1 / 2) : ℤ) : ℂ)
      = ((Int.floor (z.im * 2 ^ b + 1 / 2) : ℤ) : ℂ) * Complex.I := by ring
  have hnum : ‖((Int.floor (z.re * 2 ^ b + 1 / 2) : ℤ) : ℂ)
      + Complex.I * ((Int.floor (z.im * 2 ^ b + 1 / 2) : ℤ) : ℂ)‖
      ≤ |z.re| * 2 ^ b + 1 / 2 + (|z.im| * 2 ^ b + 1 / 2) := by
    rw [hI]
    calc ‖((Int.floor (z.re * 2 ^ b + 1 / 2) : ℤ) : ℂ)
          + ((Int.floor (z.im * 2 ^ b + 1 / 2) : ℤ) : ℂ) * Complex.I‖
          ≤ ‖((Int.floor (z.re * 2 ^ b + 1 / 2) : ℤ) : ℂ)‖
            + ‖((Int.floor (z.im * 2 ^ b + 1 / 2) : ℤ) : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ = |(Int.floor (z.re * 2 ^ b + 1 / 2) : ℝ)|
            + |(Int.floor (z.im * 2 ^ b + 1 / 2) : ℝ)| * ‖Complex.I‖ := by
          rw [Complex.norm_intCast, norm_mul, Complex.norm_intCast]
      _ = |(Int.floor (z.re * 2 ^ b + 1 / 2) : ℝ)|
            + |(Int.floor (z.im * 2 ^ b + 1 / 2) : ℝ)| := by
          rw [Complex.norm_I]
          ring
      _ ≤ (|z.re * 2 ^ b| + 1 / 2) + (|z.im * 2 ^ b| + 1 / 2) := by
          have a1 := hre (z.re * 2 ^ b)
          have a2 := hre (z.im * 2 ^ b)
          linarith
      _ = |z.re| * 2 ^ b + 1 / 2 + (|z.im| * 2 ^ b + 1 / 2) := by
          rw [abs_mul, abs_of_pos hpowb, abs_mul, abs_of_pos hpowb]
  have hnormden : ‖(2 ^ b : ℂ)‖ = (2 ^ b : ℝ) := by
    have hc : ((2 ^ b : ℕ) : ℂ) = (2 ^ b : ℂ) := by
      rw [Nat.cast_pow]
      simp
    rw [← hc, Complex.norm_natCast, Nat.cast_pow]
    norm_num
  have hrew : (|z.re| * 2 ^ b + 1 / 2 + (|z.im| * 2 ^ b + 1 / 2)) / (2 ^ b : ℝ)
      = |z.re| + |z.im| + 1 / 2 ^ b := by
    have h1 : (|z.re| * 2 ^ b + 1 / 2) / (2 ^ b : ℝ) = |z.re| + 1 / (2 * 2 ^ b) := by
      rw [add_div]
      have hz : (|z.re| * 2 ^ b) / (2 ^ b : ℝ) = |z.re| := by
        rw [mul_div_assoc, div_self (ne_of_gt hpowb), mul_one]
      rw [hz]
      ring
    have h2 : (|z.im| * 2 ^ b + 1 / 2) / (2 ^ b : ℝ) = |z.im| + 1 / (2 * 2 ^ b) := by
      rw [add_div]
      have hz : (|z.im| * 2 ^ b) / (2 ^ b : ℝ) = |z.im| := by
        rw [mul_div_assoc, div_self (ne_of_gt hpowb), mul_one]
      rw [hz]
      ring
    rw [add_div, h1, h2]
    have h3 : (1 / (2 * 2 ^ b) : ℝ) + 1 / (2 * 2 ^ b) = 1 / 2 ^ b := by
      field_simp
      ring
    linarith
  unfold qmaRoundC
  rw [norm_div, hnormden]
  have hnum' : ‖((Int.floor (z.re * 2 ^ b + 1 / 2) : ℤ) : ℂ)
      + Complex.I * ((Int.floor (z.im * 2 ^ b + 1 / 2) : ℤ) : ℂ)‖ / (2 ^ b : ℝ)
      ≤ (|z.re| * 2 ^ b + 1 / 2 + (|z.im| * 2 ^ b + 1 / 2)) / (2 ^ b : ℝ) :=
    div_le_div_of_nonneg_right hnum (le_of_lt hpowb)
  rw [hrew] at hnum'
  exact hnum'

/-- At precision at least one, rounding a number with absolute component sum at most 3/2 gives
norm at most two. -/
theorem qmaRoundC_norm_le_two {b : ℕ} {z : ℂ} (hb : 1 ≤ b)
    (hz : |z.re| + |z.im| ≤ 3 / 2) : ‖qmaRoundC b z‖ ≤ 2 := by
  have h1 : (1 : ℝ) / 2 ^ b ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ^ 1 ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hb
    rw [pow_one] at h2
    exact one_div_le_one_div_of_le (by norm_num) h2
  have := qmaRoundC_norm_le b z
  linarith

/-- The successor and the unchanged embedding of a finite index into `Fin (m + 1)` are distinct. -/
theorem fin_succ_ne_castSucc {m : ℕ} (i : Fin m) :
    (i.succ : Fin (m + 1)) ≠ i.castSucc := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_succ, Fin.val_castSucc] at this
  omega

/-- Expands a propagation entry as the half-scaled sum of its two diagonal clock blocks and two
negative transition blocks. -/
theorem qmaPropTerm_apply (n m : ℕ) (U : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (i : Fin m) (p q : Fin (m + 1) × Reg n) :
    qmaPropTerm n m U i p q
      = (1 / 2 : ℂ) *
        ((if p.1 = i.succ ∧ q.1 = i.succ then (1 : Matrix (Reg n) (Reg n) ℂ) p.2 q.2 else 0)
        + (if p.1 = i.castSucc ∧ q.1 = i.castSucc then (1 : Matrix (Reg n) (Reg n) ℂ) p.2 q.2 else 0)
        - (if p.1 = i.succ ∧ q.1 = i.castSucc then U i p.2 q.2 else 0)
        - (if p.1 = i.castSucc ∧ q.1 = i.succ then star (U i q.2 p.2) else 0)) := by
  have hs : (i.succ : Fin (m + 1)) ≠ i.castSucc := fin_succ_ne_castSucc i
  have h1 : Qatlib.Foundations.PureStateMath.Ket i.succ p.1 * Qatlib.Foundations.PureStateMath.Ket i.succ q.1 * (1 : Matrix (Reg n) (Reg n) ℂ) p.2 q.2
      = if p.1 = i.succ ∧ q.1 = i.succ then (1 : Matrix (Reg n) (Reg n) ℂ) p.2 q.2 else 0 := by
    by_cases hp : p.1 = i.succ <;> by_cases hq : q.1 = i.succ <;> simp [Qatlib.Foundations.PureStateMath.Ket, hp, hq]
  have h2 : Qatlib.Foundations.PureStateMath.Ket i.castSucc p.1 * Qatlib.Foundations.PureStateMath.Ket i.castSucc q.1 * (1 : Matrix (Reg n) (Reg n) ℂ) p.2 q.2
      = if p.1 = i.castSucc ∧ q.1 = i.castSucc then (1 : Matrix (Reg n) (Reg n) ℂ) p.2 q.2
        else 0 := by
    by_cases hp : p.1 = i.castSucc <;> by_cases hq : q.1 = i.castSucc <;> simp [Qatlib.Foundations.PureStateMath.Ket, hp, hq]
  have h3 : Qatlib.Foundations.PureStateMath.Ket i.succ p.1 * Qatlib.Foundations.PureStateMath.Ket i.castSucc q.1 * U i p.2 q.2
      = if p.1 = i.succ ∧ q.1 = i.castSucc then U i p.2 q.2 else 0 := by
    by_cases hp : p.1 = i.succ <;> by_cases hq : q.1 = i.castSucc <;> simp [Qatlib.Foundations.PureStateMath.Ket, hp, hq]
  have h4 : Qatlib.Foundations.PureStateMath.Ket i.castSucc p.1 * Qatlib.Foundations.PureStateMath.Ket i.succ q.1 * star (U i q.2 p.2)
      = if p.1 = i.castSucc ∧ q.1 = i.succ then star (U i q.2 p.2) else 0 := by
    by_cases hp : p.1 = i.castSucc <;> by_cases hq : q.1 = i.succ <;> simp [Qatlib.Foundations.PureStateMath.Ket, hp, hq]
  have hexp : qmaPropTerm n m U i p q
      = (1 / 2 : ℂ) *
        (Qatlib.Foundations.PureStateMath.Ket i.succ p.1 * Qatlib.Foundations.PureStateMath.Ket i.succ q.1 * (1 : Matrix (Reg n) (Reg n) ℂ) p.2 q.2
        + Qatlib.Foundations.PureStateMath.Ket i.castSucc p.1 * Qatlib.Foundations.PureStateMath.Ket i.castSucc q.1 * (1 : Matrix (Reg n) (Reg n) ℂ) p.2 q.2
        - Qatlib.Foundations.PureStateMath.Ket i.succ p.1 * Qatlib.Foundations.PureStateMath.Ket i.castSucc q.1 * U i p.2 q.2
        - Qatlib.Foundations.PureStateMath.Ket i.castSucc p.1 * Qatlib.Foundations.PureStateMath.Ket i.succ q.1 * star (U i q.2 p.2)) := by
    simp only [qmaPropTerm, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    rw [tensorGate_entry, tensorGate_entry, tensorGate_entry, tensorGate_entry]
    simp only [qmaClockTerm, Matrix.of_apply, Matrix.conjTranspose_apply]
  rw [hexp, h1, h2, h3, h4]

/-- A nonzero finite gate matrix entry has equal basis bits on every wire outside
`qmaGateWires`. -/
theorem finiteCodeMatrix_agree {n : ℕ} (g : FiniteGateCode) (x y : Reg n)
    (h : finiteCodeMatrix n g x y ≠ 0) :
    ∀ j : Fin n, j ∉ qmaGateWires n g → x j = y j := by
  intro j hj
  cases g with
  | h w =>
    by_cases hw : w < n
    · have hw2 : finiteCodeMatrix n (FiniteGateCode.h w) x y
          = wireGate n ⟨w, hw⟩ Hadamard x y := by
        simp [finiteCodeMatrix, hw]
      have hj' : j ≠ ⟨w, hw⟩ := by
        intro hh
        apply hj
        rw [qmaGateWires, dif_pos hw]
        simp [hh]
      rw [hw2, wireGate_apply] at h
      by_cases hall : ∀ k : Fin n, k ≠ ⟨w, hw⟩ → x k = y k
      · exact hall j hj'
      · exact absurd (by simp [hall]) h
    · have hw2 : finiteCodeMatrix n (FiniteGateCode.h w) = 1 := by
        simp [finiteCodeMatrix, hw]
      rw [hw2, Matrix.one_apply] at h
      by_cases he : x = y
      · rw [he]
      · exact absurd (by simp [he]) h
  | x w =>
    by_cases hw : w < n
    · have hw2 : finiteCodeMatrix n (FiniteGateCode.x w) x y
          = wireGate n ⟨w, hw⟩ PauliX x y := by
        simp [finiteCodeMatrix, hw]
      have hj' : j ≠ ⟨w, hw⟩ := by
        intro hh
        apply hj
        rw [qmaGateWires, dif_pos hw]
        simp [hh]
      rw [hw2, wireGate_apply] at h
      by_cases hall : ∀ k : Fin n, k ≠ ⟨w, hw⟩ → x k = y k
      · exact hall j hj'
      · exact absurd (by simp [hall]) h
    · have hw2 : finiteCodeMatrix n (FiniteGateCode.x w) = 1 := by
        simp [finiteCodeMatrix, hw]
      rw [hw2, Matrix.one_apply] at h
      by_cases he : x = y
      · rw [he]
      · exact absurd (by simp [he]) h
  | t w =>
    by_cases hw : w < n
    · have hw2 : finiteCodeMatrix n (FiniteGateCode.t w) x y
          = wireGate n ⟨w, hw⟩ tGate x y := by
        simp [finiteCodeMatrix, hw]
      have hj' : j ≠ ⟨w, hw⟩ := by
        intro hh
        apply hj
        rw [qmaGateWires, dif_pos hw]
        simp [hh]
      rw [hw2, wireGate_apply] at h
      by_cases hall : ∀ k : Fin n, k ≠ ⟨w, hw⟩ → x k = y k
      · exact hall j hj'
      · exact absurd (by simp [hall]) h
    · have hw2 : finiteCodeMatrix n (FiniteGateCode.t w) = 1 := by
        simp [finiteCodeMatrix, hw]
      rw [hw2, Matrix.one_apply] at h
      by_cases he : x = y
      · rw [he]
      · exact absurd (by simp [he]) h
  | tdg w =>
    by_cases hw : w < n
    · have hw2 : finiteCodeMatrix n (FiniteGateCode.tdg w) x y
          = wireGate n ⟨w, hw⟩ tGateAdj x y := by
        simp [finiteCodeMatrix, hw]
      have hj' : j ≠ ⟨w, hw⟩ := by
        intro hh
        apply hj
        rw [qmaGateWires, dif_pos hw]
        simp [hh]
      rw [hw2, wireGate_apply] at h
      by_cases hall : ∀ k : Fin n, k ≠ ⟨w, hw⟩ → x k = y k
      · exact hall j hj'
      · exact absurd (by simp [hall]) h
    · have hw2 : finiteCodeMatrix n (FiniteGateCode.tdg w) = 1 := by
        simp [finiteCodeMatrix, hw]
      rw [hw2, Matrix.one_apply] at h
      by_cases he : x = y
      · rw [he]
      · exact absurd (by simp [he]) h
  | cx c t =>
    by_cases hw : c < n ∧ t < n ∧ c ≠ t
    · have hw2 : finiteCodeMatrix n (FiniteGateCode.cx c t) x y
          = cnotGate n ⟨c, hw.1⟩ ⟨t, hw.2.1⟩ x y := by
        simp [finiteCodeMatrix, hw]
      have hjt : (j : Fin n) ≠ ⟨t, hw.2.1⟩ := by
        intro hh
        apply hj
        rw [qmaGateWires, dif_pos hw]
        simp [hh]
      rw [hw2] at h
      simp only [cnotGate, permMatrix, Matrix.of_apply] at h
      by_cases he : x = Function.update y ⟨t, hw.2.1⟩ (y ⟨t, hw.2.1⟩ ^^ y ⟨c, hw.1⟩)
      · rw [he]
        simp [Function.update, hjt]
      · exact absurd (by simp [he]) h
    · have hw2 : finiteCodeMatrix n (FiniteGateCode.cx c t) = 1 := by
        simp [finiteCodeMatrix, hw]
      rw [hw2, Matrix.one_apply] at h
      by_cases he : x = y
      · rw [he]
      · exact absurd (by simp [he]) h

/-- A nonzero rounded gate entry comes from a nonzero exact gate entry. -/
theorem qmaRoundedGate_ne_zero {n : ℕ} (g : FiniteGateCode) (b : ℕ) (x y : Reg n)
    (h : qmaRoundedGate n b g x y ≠ 0) : finiteCodeMatrix n g x y ≠ 0 := by
  intro hh
  apply h
  have hform : qmaRoundedGate n b g x y = qmaRoundC b (finiteCodeMatrix n g x y) := by
    simp [qmaRoundedGate, Matrix.of_apply]
  rw [hform, hh, qmaRoundC_zero]

/-- A nonzero rounded gate entry has equal basis bits outside the gate's listed wire support. -/
theorem qmaRoundedGate_agree {n : ℕ} (g : FiniteGateCode) (b : ℕ) (x y : Reg n)
    (h : qmaRoundedGate n b g x y ≠ 0) :
    ∀ j : Fin n, j ∉ (qmaGateWires n g).toFinset → x j = y j := by
  intro j hj
  apply finiteCodeMatrix_agree g x y (qmaRoundedGate_ne_zero g b x y h) j
  intro hj'
  apply hj
  simpa [List.mem_toFinset] using! hj'

/-- The sum of the absolute real and imaginary parts of a Hadamard entry is at most 3/2. -/
theorem hadamard_entry_abs (a b : Bool) :
    |(Hadamard a b).re| + |(Hadamard a b).im| ≤ 3 / 2 := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt ((by norm_num : (1 : ℝ) ≤ 2))
    rwa [Real.sqrt_one] at h
  have hinv : (Real.sqrt 2 : ℝ)⁻¹ ≤ 3 / 2 := by
    have h2 : (Real.sqrt 2 : ℝ)⁻¹ ≤ 1 :=
      (inv_le_one₀ (Real.sqrt_pos.mpr (by norm_num))).mpr h1
    linarith
  have hre : ((Real.sqrt 2 : ℂ)⁻¹).re = (Real.sqrt 2 : ℝ)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.ofReal_re]
  have him : ((Real.sqrt 2 : ℂ)⁻¹).im = 0 := by
    rw [← Complex.ofReal_inv, Complex.ofReal_im]
  unfold Hadamard
  simp only [Matrix.of_apply]
  by_cases hab : a && b
  · rw [if_pos hab]
    have hval : ((Real.sqrt 2 : ℂ)⁻¹ * (-1 : ℂ)) = -((Real.sqrt 2 : ℂ)⁻¹) := by ring
    rw [hval, Complex.neg_re, Complex.neg_im, hre, him, neg_zero, abs_zero, abs_neg]
    rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    linarith
  · rw [if_neg hab]
    have hval : ((Real.sqrt 2 : ℂ)⁻¹ * (1 : ℂ)) = ((Real.sqrt 2 : ℂ)⁻¹) := by ring
    rw [hval, hre, him, abs_zero]
    rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    linarith

/-- The square root of two is at most 3/2. -/
theorem sqrt_two_le_three_halves : Real.sqrt 2 ≤ 3 / 2 := by
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · norm_num

/-- The phase `exp (π * I / 4)` has real and imaginary parts equal to `sqrt 2 / 2`. -/
theorem exp_pi_div_four_re_im :
    (Complex.exp ((Real.pi / 4 : ℂ) * Complex.I)).re = Real.sqrt 2 / 2 ∧
    (Complex.exp ((Real.pi / 4 : ℂ) * Complex.I)).im = Real.sqrt 2 / 2 := by
  rw [show ((Real.pi : ℂ) / 4) * Complex.I = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I from by
      push_cast
      ring, Complex.exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four]
  constructor <;> simp

/-- The phase `exp (-π * I / 4)` has real part `sqrt 2 / 2` and imaginary part `-sqrt 2 / 2`. -/
theorem exp_neg_pi_div_four_re_im :
    (Complex.exp ((-(Real.pi / 4 : ℝ) : ℂ) * Complex.I)).re = Real.sqrt 2 / 2 ∧
    (Complex.exp ((-(Real.pi / 4 : ℝ) : ℂ) * Complex.I)).im = -(Real.sqrt 2 / 2) := by
  rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  constructor <;> simp

/-- The sum of the absolute real and imaginary parts of a T gate entry is at most 3/2. -/
theorem tGate_entry_abs (a b : Bool) :
    |(tGate a b).re| + |(tGate a b).im| ≤ 3 / 2 := by
  rcases a with _|_ <;> rcases b with _|_
  · have h : tGate false false = 1 := by simp [tGate, Rz]
    rw [h]; norm_num
  · have h : tGate false true = 0 := by simp [tGate, Rz]
    rw [h]; norm_num
  · have h : tGate true false = 0 := by simp [tGate, Rz]
    rw [h]; norm_num
  · have h : tGate true true = Complex.exp ((Real.pi / 4 : ℂ) * Complex.I) := by
      simp [tGate, Rz]
    rw [h, exp_pi_div_four_re_im.1, exp_pi_div_four_re_im.2]
    have hnn : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
    rw [abs_of_nonneg hnn]
    have hs : Real.sqrt 2 / 2 + Real.sqrt 2 / 2 = Real.sqrt 2 := by ring
    rw [hs]
    exact sqrt_two_le_three_halves

/-- The sum of the absolute real and imaginary parts of an adjoint T gate entry is at most 3/2. -/
theorem tGateAdj_entry_abs (a b : Bool) :
    |(tGateAdj a b).re| + |(tGateAdj a b).im| ≤ 3 / 2 := by
  rcases a with _|_ <;> rcases b with _|_
  · have h : tGateAdj false false = 1 := by simp [tGateAdj, Rz]
    rw [h]; norm_num
  · have h : tGateAdj false true = 0 := by simp [tGateAdj, Rz]
    rw [h]; norm_num
  · have h : tGateAdj true false = 0 := by simp [tGateAdj, Rz]
    rw [h]; norm_num
  · have h : tGateAdj true true = Complex.exp ((-(Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
      simp [tGateAdj, Rz]
    rw [h]
    rw [exp_neg_pi_div_four_re_im.1, exp_neg_pi_div_four_re_im.2]
    have hnn : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
    rw [abs_of_nonneg hnn, abs_neg, abs_of_nonneg hnn]
    have hs : Real.sqrt 2 / 2 + Real.sqrt 2 / 2 = Real.sqrt 2 := by ring
    rw [hs]
    exact sqrt_two_le_three_halves

/-- The sum of the absolute real and imaginary parts of a `permMatrix` entry is at most 3/2. -/
theorem permMatrix_entry_abs {I : Type} [Fintype I] [DecidableEq I] (σ : I → I) (i j : I) :
    |((permMatrix σ : Matrix I I ℂ) i j).re| + |((permMatrix σ : Matrix I I ℂ) i j).im|
      ≤ 3 / 2 := by
  simp only [permMatrix, Matrix.of_apply]
  by_cases h : i = σ j
  · rw [if_pos h]
    norm_num
  · rw [if_neg h]
    norm_num

/-- Both zero and one have absolute component sum at most 3/2 in the complex numbers. -/
theorem one_zero_entry_abs : (|(0 : ℂ).re| + |(0 : ℂ).im| ≤ 3 / 2) ∧
    (|(1 : ℂ).re| + |(1 : ℂ).im| ≤ 3 / 2) := by
  norm_num

/-- Every encoded finite gate entry has absolute component sum at most 3/2. -/
theorem finiteCodeMatrix_entry_abs (n : ℕ) (g : FiniteGateCode) (x y : Reg n) :
    |(finiteCodeMatrix n g x y).re| + |(finiteCodeMatrix n g x y).im| ≤ 3 / 2 := by
  cases g with
  | h w =>
    by_cases hw : w < n
    · have hE : finiteCodeMatrix n (FiniteGateCode.h w) x y
          = wireGate n ⟨w, hw⟩ Hadamard x y := by
        simp [finiteCodeMatrix, hw]
      rw [hE, wireGate_apply]
      by_cases hall : ∀ k : Fin n, k ≠ ⟨w, hw⟩ → x k = y k
      · rw [if_pos hall]
        exact hadamard_entry_abs _ _
      · rw [if_neg hall]
        exact one_zero_entry_abs.1
    · have hE : finiteCodeMatrix n (FiniteGateCode.h w) = 1 := by
        simp [finiteCodeMatrix, hw]
      rw [hE, Matrix.one_apply]
      by_cases he : x = y
      · rw [if_pos he]
        exact one_zero_entry_abs.2
      · rw [if_neg he]
        exact one_zero_entry_abs.1
  | x w =>
    by_cases hw : w < n
    · have hE : finiteCodeMatrix n (FiniteGateCode.x w) x y
          = wireGate n ⟨w, hw⟩ PauliX x y := by
        simp [finiteCodeMatrix, hw]
      rw [hE, wireGate_apply]
      by_cases hall : ∀ k : Fin n, k ≠ ⟨w, hw⟩ → x k = y k
      · rw [if_pos hall]
        have hval : PauliX (x ⟨w, hw⟩) (y ⟨w, hw⟩)
            = (permMatrix Bool.not : Matrix Bool Bool ℂ) (x ⟨w, hw⟩) (y ⟨w, hw⟩) := rfl
        rw [hval]
        exact permMatrix_entry_abs _ _ _
      · rw [if_neg hall]
        exact one_zero_entry_abs.1
    · have hE : finiteCodeMatrix n (FiniteGateCode.x w) = 1 := by
        simp [finiteCodeMatrix, hw]
      rw [hE, Matrix.one_apply]
      by_cases he : x = y
      · rw [if_pos he]
        exact one_zero_entry_abs.2
      · rw [if_neg he]
        exact one_zero_entry_abs.1
  | t w =>
    by_cases hw : w < n
    · have hE : finiteCodeMatrix n (FiniteGateCode.t w) x y
          = wireGate n ⟨w, hw⟩ tGate x y := by
        simp [finiteCodeMatrix, hw]
      rw [hE, wireGate_apply]
      by_cases hall : ∀ k : Fin n, k ≠ ⟨w, hw⟩ → x k = y k
      · rw [if_pos hall]
        exact tGate_entry_abs _ _
      · rw [if_neg hall]
        exact one_zero_entry_abs.1
    · have hE : finiteCodeMatrix n (FiniteGateCode.t w) = 1 := by
        simp [finiteCodeMatrix, hw]
      rw [hE, Matrix.one_apply]
      by_cases he : x = y
      · rw [if_pos he]
        exact one_zero_entry_abs.2
      · rw [if_neg he]
        exact one_zero_entry_abs.1
  | tdg w =>
    by_cases hw : w < n
    · have hE : finiteCodeMatrix n (FiniteGateCode.tdg w) x y
          = wireGate n ⟨w, hw⟩ tGateAdj x y := by
        simp [finiteCodeMatrix, hw]
      rw [hE, wireGate_apply]
      by_cases hall : ∀ k : Fin n, k ≠ ⟨w, hw⟩ → x k = y k
      · rw [if_pos hall]
        exact tGateAdj_entry_abs _ _
      · rw [if_neg hall]
        exact one_zero_entry_abs.1
    · have hE : finiteCodeMatrix n (FiniteGateCode.tdg w) = 1 := by
        simp [finiteCodeMatrix, hw]
      rw [hE, Matrix.one_apply]
      by_cases he : x = y
      · rw [if_pos he]
        exact one_zero_entry_abs.2
      · rw [if_neg he]
        exact one_zero_entry_abs.1
  | cx c t =>
    by_cases hw : c < n ∧ t < n ∧ c ≠ t
    · have hE : finiteCodeMatrix n (FiniteGateCode.cx c t) x y
          = cnotGate n ⟨c, hw.1⟩ ⟨t, hw.2.1⟩ x y := by
        simp [finiteCodeMatrix, hw]
      rw [hE]
      have hval : cnotGate n ⟨c, hw.1⟩ ⟨t, hw.2.1⟩ x y
          = (permMatrix (fun z : Reg n => Function.update z ⟨t, hw.2.1⟩
              (z ⟨t, hw.2.1⟩ ^^ z ⟨c, hw.1⟩)) : Matrix (Reg n) (Reg n) ℂ) x y := rfl
      rw [hval]
      exact permMatrix_entry_abs _ _ _
    · have hE : finiteCodeMatrix n (FiniteGateCode.cx c t) = 1 := by
        simp [finiteCodeMatrix, hw]
      rw [hE, Matrix.one_apply]
      by_cases he : x = y
      · rw [if_pos he]
        exact one_zero_entry_abs.2
      · rw [if_neg he]
        exact one_zero_entry_abs.1

/-- Every rounded finite gate entry has norm at most two when the precision is at least one. -/
theorem qmaRoundedGate_entry_norm_le_two {n : ℕ} (g : FiniteGateCode) (b : ℕ) (hb : 1 ≤ b)
    (x y : Reg n) : ‖qmaRoundedGate n b g x y‖ ≤ 2 := by
  have habs := finiteCodeMatrix_entry_abs n g x y
  have hform : qmaRoundedGate n b g x y = qmaRoundC b (finiteCodeMatrix n g x y) := by
    simp [qmaRoundedGate, Matrix.of_apply]
  rw [hform]
  exact qmaRoundC_norm_le_two hb habs

/-- Gives a disjoint case formula for a propagation entry according to its two clock
coordinates. -/
theorem qmaPropTerm_entry (n m : ℕ) (U : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (i : Fin m) (p q : Fin (m + 1) × Reg n) :
    qmaPropTerm n m U i p q =
      if p.1 = i.succ ∧ q.1 = i.succ then (1 / 2 : ℂ) * (1 : Matrix (Reg n) (Reg n) ℂ) p.2 q.2
      else if p.1 = i.castSucc ∧ q.1 = i.castSucc then
        (1 / 2 : ℂ) * (1 : Matrix (Reg n) (Reg n) ℂ) p.2 q.2
      else if p.1 = i.succ ∧ q.1 = i.castSucc then -((1 / 2 : ℂ) * U i p.2 q.2)
      else if p.1 = i.castSucc ∧ q.1 = i.succ then
        -((1 / 2 : ℂ) * star (U i q.2 p.2))
      else 0 := by
  have hs : (i.succ : Fin (m + 1)) ≠ i.castSucc := fin_succ_ne_castSucc i
  by_cases h1 : p.1 = i.succ ∧ q.1 = i.succ
  · rw [qmaPropTerm_apply]
    simp [h1, hs, hs.symm]
  by_cases h2 : p.1 = i.castSucc ∧ q.1 = i.castSucc
  · rw [qmaPropTerm_apply]
    simp [h1, h2, hs, hs.symm]
  by_cases h3 : p.1 = i.succ ∧ q.1 = i.castSucc
  · rw [qmaPropTerm_apply]
    simp [h1, h2, h3, hs, hs.symm]
  by_cases h4 : p.1 = i.castSucc ∧ q.1 = i.succ
  · rw [qmaPropTerm_apply]
    simp [h1, h2, h3, h4, hs, hs.symm]
  · rw [qmaPropTerm_apply]
    simp [h1, h2, h3, h4]

/-- A propagation term has the declared adjacent clock support and gate wire support when its
gate matrix agrees outside those wires. -/
theorem qmaPropTerm_actsOn (n m : ℕ) (g : FiniteGateCode)
    (U : Fin m → Matrix (Reg n) (Reg n) ℂ) (i : Fin m)
    (hU : ∀ x y : Reg n, U i x y ≠ 0 →
      ∀ j : Fin n, j ∉ (qmaGateWires n g).toFinset → x j = y j) :
    qmaActsOn n m (qmaPropTerm n m U i) {i.castSucc, i.succ} ((qmaGateWires n g).toFinset) := by
  intro p q hne
  rw [qmaPropTerm_entry] at hne
  split_ifs at hne with h1 h2 h3 h4
  · refine ⟨?_, ?_, ?_⟩
    · simp [h1]
    · simp [h1]
    · have hone : (1 : Matrix (Reg n) (Reg n) ℂ) p.2 q.2 ≠ 0 := by
        intro hh
        apply hne
        rw [hh]
        ring
      have hp2 : p.2 = q.2 := by
        by_contra hxy
        apply hone
        rw [Matrix.one_apply, if_neg hxy]
      intro j _
      exact congrFun hp2 j
  · refine ⟨?_, ?_, ?_⟩
    · simp [h2]
    · simp [h2]
    · have hone : (1 : Matrix (Reg n) (Reg n) ℂ) p.2 q.2 ≠ 0 := by
        intro hh
        apply hne
        rw [hh]
        ring
      have hp2 : p.2 = q.2 := by
        by_contra hxy
        apply hone
        rw [Matrix.one_apply, if_neg hxy]
      intro j _
      exact congrFun hp2 j
  · refine ⟨?_, ?_, ?_⟩
    · simp [h3]
    · simp [h3]
    · have hU0 : U i p.2 q.2 ≠ 0 := by
        intro hh
        apply hne
        rw [hh]
        ring
      exact hU p.2 q.2 hU0
  · refine ⟨?_, ?_, ?_⟩
    · simp [h4]
    · simp [h4]
    · have hU0 : star (U i q.2 p.2) ≠ 0 := by
        intro hh
        apply hne
        rw [hh]
        ring
      have hU0' : U i q.2 p.2 ≠ 0 := by
        intro hh
        apply hU0
        rw [hh]
        simp
      intro j hj
      exact (hU q.2 p.2 hU0' j hj).symm
  · exact absurd rfl hne

/-- The two adjacent clock positions and the finite gate's wire set each have cardinality at
most two. -/
theorem qmaPropTerm_cards (n m : ℕ) (g : FiniteGateCode) (i : Fin m) :
    ({i.castSucc, i.succ} : Finset (Fin (m + 1))).card ≤ 2 ∧
    ((qmaGateWires n g).toFinset : Finset (Fin n)).card ≤ 2 := by
  constructor
  · have h := Finset.card_insert_le i.castSucc ({i.succ} : Finset (Fin (m + 1)))
    simp only [Finset.card_singleton] at h
    omega
  · cases g with
    | h w =>
      by_cases hw : w < n <;> simp [qmaGateWires, hw]
    | x w =>
      by_cases hw : w < n <;> simp [qmaGateWires, hw]
    | t w =>
      by_cases hw : w < n <;> simp [qmaGateWires, hw]
    | tdg w =>
      by_cases hw : w < n <;> simp [qmaGateWires, hw]
    | cx c t =>
      by_cases hw : c < n ∧ t < n ∧ c ≠ t
      · have hE : qmaGateWires n (FiniteGateCode.cx c t) = [⟨c, hw.1⟩, ⟨t, hw.2.1⟩] := by
          simp [qmaGateWires, hw]
        rw [hE]
        have hA : ([⟨c, hw.1⟩, ⟨t, hw.2.1⟩] : List (Fin n)).toFinset
            = insert (⟨c, hw.1⟩ : Fin n) (insert (⟨t, hw.2.1⟩ : Fin n) ∅) := by
          simp
        rw [hA]
        have hB : (insert (⟨t, hw.2.1⟩ : Fin n) (∅ : Finset (Fin n))).card ≤ 1 :=
          le_trans (Finset.card_insert_le _ _) (by simp)
        have hC : (insert (⟨c, hw.1⟩ : Fin n)
            (insert (⟨t, hw.2.1⟩ : Fin n) (∅ : Finset (Fin n)))).card
            ≤ (insert (⟨t, hw.2.1⟩ : Fin n) (∅ : Finset (Fin n))).card + 1 :=
          Finset.card_insert_le _ _
        omega
      · have hE : qmaGateWires n (FiniteGateCode.cx c t) = [] := by
          simp [qmaGateWires, hw]
        rw [hE]
        simp

/-- An input penalty entry is the product of the initial clock indicators and the diagonal
true-bit indicator on wire `j`. -/
theorem qmaInTerm_entry (n m : ℕ) (j : Fin n) (p q : Fin (m + 1) × Reg n) :
    qmaInTerm n m j p q
      = Qatlib.Foundations.PureStateMath.Ket 0 p.1 * Qatlib.Foundations.PureStateMath.Ket 0 q.1 *
          (if p.2 = q.2 then (if p.2 j then (1 : ℂ) else 0) else 0) := by
  simp [qmaInTerm, tensorGate_entry, qmaClockTerm, Matrix.of_apply, Matrix.diagonal_apply]

/-- An input penalty satisfies `qmaActsOn` with initial clock support and the singleton work
support `{j}`. -/
theorem qmaInTerm_actsOn (n m : ℕ) (j : Fin n) :
    qmaActsOn n m (qmaInTerm n m j) ({0} : Finset (Fin (m + 1))) ({j} : Finset (Fin n)) := by
  intro p q hne
  rw [qmaInTerm_entry] at hne
  have hK1 : Qatlib.Foundations.PureStateMath.Ket 0 p.1 ≠ 0 := by
    intro hh
    apply hne
    rw [hh]
    ring
  have hK2 : Qatlib.Foundations.PureStateMath.Ket 0 q.1 ≠ 0 := by
    intro hh
    apply hne
    rw [hh]
    ring
  have hp : p.1 = (0 : Fin (m + 1)) := by
    by_contra hh
    apply hK1
    simp [Qatlib.Foundations.PureStateMath.Ket, hh]
  have hq : q.1 = (0 : Fin (m + 1)) := by
    by_contra hh
    apply hK2
    simp [Qatlib.Foundations.PureStateMath.Ket, hh]
  have he : p.2 = q.2 := by
    by_contra hh
    apply hne
    simp [hh]
  refine ⟨?_, ?_, ?_⟩
  · simp [hp]
  · simp [hq]
  · intro k _
    exact congrFun he k

/-- The singleton clock and work supports of an input penalty each have cardinality at most two. -/
theorem qmaInTerm_cards (n m : ℕ) (j : Fin n) :
    ({0} : Finset (Fin (m + 1))).card ≤ 2 ∧ ({j} : Finset (Fin n)).card ≤ 2 := by
  simp

/-- An output penalty entry is the product of the final clock indicators and the diagonal
false-output indicator. -/
theorem qmaOutTerm_entry (n m : ℕ) (out : Fin n) (p q : Fin (m + 1) × Reg n) :
    qmaOutTerm n m out p q
      = Qatlib.Foundations.PureStateMath.Ket (Fin.last m) p.1 * Qatlib.Foundations.PureStateMath.Ket (Fin.last m) q.1 *
          (if p.2 = q.2 then (if p.2 out then (0 : ℂ) else 1) else 0) := by
  simp [qmaOutTerm, tensorGate_entry, qmaClockTerm, Matrix.of_apply, Matrix.diagonal_apply]

/-- An output penalty satisfies `qmaActsOn` with final clock support and the singleton output
wire support. -/
theorem qmaOutTerm_actsOn (n m : ℕ) (out : Fin n) :
    qmaActsOn n m (qmaOutTerm n m out) ({Fin.last m} : Finset (Fin (m + 1)))
      ({out} : Finset (Fin n)) := by
  intro p q hne
  rw [qmaOutTerm_entry] at hne
  have hK1 : Qatlib.Foundations.PureStateMath.Ket (Fin.last m) p.1 ≠ 0 := by
    intro hh
    apply hne
    rw [hh]
    ring
  have hK2 : Qatlib.Foundations.PureStateMath.Ket (Fin.last m) q.1 ≠ 0 := by
    intro hh
    apply hne
    rw [hh]
    ring
  have hp : p.1 = Fin.last m := by
    by_contra hh
    apply hK1
    simp [Qatlib.Foundations.PureStateMath.Ket, hh]
  have hq : q.1 = Fin.last m := by
    by_contra hh
    apply hK2
    simp [Qatlib.Foundations.PureStateMath.Ket, hh]
  have he : p.2 = q.2 := by
    by_contra hh
    apply hne
    simp [hh]
  refine ⟨?_, ?_, ?_⟩
  · simp [hp]
  · simp [hq]
  · intro k _
    exact congrFun he k

/-- The singleton clock and work supports of an output penalty each have cardinality at most
two. -/
theorem qmaOutTerm_cards (n m : ℕ) (out : Fin n) :
    ({Fin.last m} : Finset (Fin (m + 1))).card ≤ 2 ∧ ({out} : Finset (Fin n)).card ≤ 2 := by
  simp

/-- Every rounded history term satisfies its declared support condition, with at most two clock
positions and two work wires. -/
theorem clause2_clause3 :
    ∀ C : QmaHistoryCircuit,
      ∀ t ∈ qmaHistoryTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64)),
        qmaActsOn C.qubits C.gates.length t.matrix t.clockSupport t.workSupport
          ∧ t.clockSupport.card ≤ 2 ∧ t.workSupport.card ≤ 2 := by
  intro C t ht
  have hsplit :
      qmaHistoryTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))
      = qmaHistoryPropTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))
        ++ qmaHistoryInTerms C ++ qmaHistoryOutTerm C := rfl
  have h3 : t ∈ qmaHistoryPropTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))
      ∨ t ∈ qmaHistoryInTerms C ∨ t ∈ qmaHistoryOutTerm C := by
    have h := ht
    rw [hsplit, List.mem_append, List.mem_append, or_assoc] at h
    exact h
  rcases h3 with hprop | hin | hout
  · rw [qmaHistoryPropTerms, List.mem_map] at hprop
    obtain ⟨i, _, heq⟩ := hprop
    rw [← heq]
    show qmaActsOn C.qubits C.gates.length
        (qmaPropTerm C.qubits C.gates.length
          (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64)) i)
        {i.castSucc, i.succ}
        ((qmaGateWires C.qubits (qmaGateAt C.gates i.val)).toFinset)
      ∧ ({i.castSucc, i.succ} : Finset (Fin (C.gates.length + 1))).card ≤ 2
      ∧ ((qmaGateWires C.qubits (qmaGateAt C.gates i.val)).toFinset).card ≤ 2
    refine ⟨?_, (qmaPropTerm_cards C.qubits C.gates.length
      (qmaGateAt C.gates i.val) i).1, (qmaPropTerm_cards C.qubits C.gates.length
      (qmaGateAt C.gates i.val) i).2⟩
    refine qmaPropTerm_actsOn C.qubits C.gates.length (qmaGateAt C.gates i.val)
      (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64)) i ?_
    intro x y hxy
    apply qmaRoundedGate_agree (qmaGateAt C.gates i.val)
      (3 * (C.qubits + C.gates.length) + 64) x y
    simpa [qmaRoundedGates] using! hxy
  · have hdef : qmaHistoryInTerms C
        = C.initZeroWires.toList.map
            (fun j : Fin C.qubits =>
              ({ clockSupport := ({0} : Finset (Fin (C.gates.length + 1))),
                 workSupport := ({j} : Finset (Fin C.qubits)),
                 matrix := qmaInTerm C.qubits C.gates.length j } :
                QmaHistoryTerm C.qubits C.gates.length)) := rfl
    rw [hdef, List.mem_map] at hin
    obtain ⟨j, _, heq⟩ := hin
    rw [← heq]
    show qmaActsOn C.qubits C.gates.length
        (qmaInTerm C.qubits C.gates.length j) ({0} : Finset (Fin (C.gates.length + 1)))
          ({j} : Finset (Fin C.qubits))
      ∧ ({0} : Finset (Fin (C.gates.length + 1))).card ≤ 2
      ∧ ({j} : Finset (Fin C.qubits)).card ≤ 2
    exact ⟨qmaInTerm_actsOn C.qubits C.gates.length j,
      (qmaInTerm_cards C.qubits C.gates.length j).1,
      (qmaInTerm_cards C.qubits C.gates.length j).2⟩
  · have hdef : qmaHistoryOutTerm C
        = [{ clockSupport := ({Fin.last C.gates.length} : Finset (Fin (C.gates.length + 1))),
             workSupport := ({C.outputWire} : Finset (Fin C.qubits)),
             matrix := qmaOutTerm C.qubits C.gates.length C.outputWire }] := rfl
    rw [hdef, List.mem_singleton] at hout
    rw [hout]
    show qmaActsOn C.qubits C.gates.length
        (qmaOutTerm C.qubits C.gates.length C.outputWire)
          ({Fin.last C.gates.length} : Finset (Fin (C.gates.length + 1)))
          ({C.outputWire} : Finset (Fin C.qubits))
      ∧ ({Fin.last C.gates.length} : Finset (Fin (C.gates.length + 1))).card ≤ 2
      ∧ ({C.outputWire} : Finset (Fin C.qubits)).card ≤ 2
    exact ⟨qmaOutTerm_actsOn C.qubits C.gates.length C.outputWire,
      (qmaOutTerm_cards C.qubits C.gates.length C.outputWire).1,
      (qmaOutTerm_cards C.qubits C.gates.length C.outputWire).2⟩

/-- Every entry of the identity matrix on a qubit register has norm at most one. -/
theorem one_entry_norm_le {n : ℕ} (x y : Reg n) :
    ‖(1 : Matrix (Reg n) (Reg n) ℂ) x y‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> norm_num

/-- Every coefficient of a computational basis ket has norm at most one. -/
theorem ket_norm_le_one {I : Type} [Fintype I] [DecidableEq I] (i j : I) : ‖Qatlib.Foundations.PureStateMath.Ket i j‖ ≤ 1 := by
  show ‖(if j = i then (1 : ℂ) else 0)‖ ≤ 1
  split_ifs <;> norm_num

/-- A product of three complex numbers of norm at most one has norm at most one. -/
theorem norm_prod3_le_one (a b c : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ‖a * b * c‖ ≤ 1 := by
  rw [norm_mul, norm_mul]
  have h1 : ‖a‖ * ‖b‖ ≤ 1 := mul_le_one₀ ha (norm_nonneg b) hb
  exact mul_le_one₀ h1 (norm_nonneg c) hc

/-- Multiplication by one half reduces a complex number of norm at most two to norm at most one. -/
theorem half_mul_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 2) : ‖(1 / 2 : ℂ) * z‖ ≤ 1 := by
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h12, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h := mul_le_mul_of_nonneg_left hz (by norm_num : (0 : ℝ) ≤ 1 / 2)
  linarith

/-- A propagation term has entries of norm at most one when its gate matrix entries have norm at
most two. -/
theorem qmaPropTerm_matrix_norm_le_one (n m : ℕ) (U : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (i : Fin m) (hU : ∀ x y : Reg n, ‖U i x y‖ ≤ 2)
    (p q : Fin (m + 1) × Reg n) : ‖qmaPropTerm n m U i p q‖ ≤ 1 := by
  rw [qmaPropTerm_entry]
  split_ifs with h1 h2 h3 h4
  · exact half_mul_norm_le_one
      (le_trans (one_entry_norm_le p.2 q.2) (by norm_num))
  · exact half_mul_norm_le_one
      (le_trans (one_entry_norm_le p.2 q.2) (by norm_num))
  · rw [norm_neg]
    exact half_mul_norm_le_one (hU p.2 q.2)
  · rw [norm_neg]
    exact half_mul_norm_le_one (by rw [norm_star]; exact hU q.2 p.2)
  · norm_num

/-- Every input penalty entry has norm at most one. -/
theorem qmaInTerm_matrix_norm_le_one (n m : ℕ) (j : Fin n)
    (p q : Fin (m + 1) × Reg n) : ‖qmaInTerm n m j p q‖ ≤ 1 := by
  rw [qmaInTerm_entry]
  refine norm_prod3_le_one _ _ _ (ket_norm_le_one _ _) (ket_norm_le_one _ _) ?_
  split_ifs <;> norm_num

/-- Every output penalty entry has norm at most one. -/
theorem qmaOutTerm_matrix_norm_le_one (n m : ℕ) (out : Fin n)
    (p q : Fin (m + 1) × Reg n) : ‖qmaOutTerm n m out p q‖ ≤ 1 := by
  rw [qmaOutTerm_entry]
  refine norm_prod3_le_one _ _ _ (ket_norm_le_one _ _) (ket_norm_le_one _ _) ?_
  split_ifs <;> norm_num

/-- Every entry of every history term at the prescribed rounding precision has norm at most one. -/
theorem clause2_clause4 :
    ∀ C : QmaHistoryCircuit,
      ∀ t ∈ qmaHistoryTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64)),
        ∀ p : Fin (C.gates.length + 1) × Reg C.qubits,
          ∀ q : Fin (C.gates.length + 1) × Reg C.qubits, ‖t.matrix p q‖ ≤ 1 := by
  intro C t ht p q
  have hb : (1 : ℕ) ≤ 3 * (C.qubits + C.gates.length) + 64 := by omega
  have hsplit :
      qmaHistoryTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))
      = qmaHistoryPropTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))
        ++ qmaHistoryInTerms C ++ qmaHistoryOutTerm C := rfl
  have h3 : t ∈ qmaHistoryPropTerms C (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))
      ∨ t ∈ qmaHistoryInTerms C ∨ t ∈ qmaHistoryOutTerm C := by
    have h := ht
    rw [hsplit, List.mem_append, List.mem_append, or_assoc] at h
    exact h
  rcases h3 with hprop | hin | hout
  · rw [qmaHistoryPropTerms, List.mem_map] at hprop
    obtain ⟨i, _, heq⟩ := hprop
    rw [← heq]
    show ‖(qmaPropTerm C.qubits C.gates.length
        (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64)) i) p q‖ ≤ 1
    refine qmaPropTerm_matrix_norm_le_one C.qubits C.gates.length
      (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64)) i ?_ p q
    intro x y
    simpa [qmaRoundedGates] using!
      qmaRoundedGate_entry_norm_le_two (qmaGateAt C.gates i.val)
        (3 * (C.qubits + C.gates.length) + 64) hb x y
  · have hdef : qmaHistoryInTerms C
        = C.initZeroWires.toList.map
            (fun j : Fin C.qubits =>
              ({ clockSupport := ({0} : Finset (Fin (C.gates.length + 1))),
                 workSupport := ({j} : Finset (Fin C.qubits)),
                 matrix := qmaInTerm C.qubits C.gates.length j } :
                QmaHistoryTerm C.qubits C.gates.length)) := rfl
    rw [hdef, List.mem_map] at hin
    obtain ⟨j, _, heq⟩ := hin
    rw [← heq]
    show ‖(qmaInTerm C.qubits C.gates.length j) p q‖ ≤ 1
    exact qmaInTerm_matrix_norm_le_one C.qubits C.gates.length j p q
  · have hdef : qmaHistoryOutTerm C
        = [{ clockSupport := ({Fin.last C.gates.length} : Finset (Fin (C.gates.length + 1))),
             workSupport := ({C.outputWire} : Finset (Fin C.qubits)),
             matrix := qmaOutTerm C.qubits C.gates.length C.outputWire }] := rfl
    rw [hdef, List.mem_singleton] at hout
    rw [hout]
    show ‖(qmaOutTerm C.qubits C.gates.length C.outputWire) p q‖ ≤ 1
    exact qmaOutTerm_matrix_norm_le_one C.qubits C.gates.length C.outputWire p q

/-- Every prefix of a legal finite gate word is legal. -/
theorem finiteWordLegal_take {n k : ℕ} {gs : List FiniteGateCode}
    (h : finiteWordLegal n gs = true) : finiteWordLegal n (gs.take k) = true := by
  simp only [finiteWordLegal] at h ⊢
  apply List.all_eq_true.mpr
  intro x hx
  exact List.all_eq_true.mp h x (List.mem_of_mem_take hx)

/-- The work state at each clock position obtained by applying the corresponding exact gate
prefix to `φ`. -/
noncomputable def qmaExactHistory (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits)) :
    Fin (C.gates.length + 1) → QState (Reg C.qubits) :=
  fun t => (finiteWordMatrix C.qubits (C.gates.take t.val)).mulVec φ

/-- Every exact history slice of a normalized input state is normalized. -/
theorem normalized_qmaExactHistory {C : QmaHistoryCircuit} {φ : QState (Reg C.qubits)}
    (hφ : Normalized φ) (t : Fin (C.gates.length + 1)) :
    Normalized (qmaExactHistory C φ t) := by
  have hlegal : finiteWordLegal C.qubits (C.gates.take t.val) = true :=
    finiteWordLegal_take C.legal
  have hU : finiteWordMatrix C.qubits (C.gates.take t.val)
      ∈ Matrix.unitaryGroup (Reg C.qubits) ℂ :=
    finiteWordMatrix_unitary C.qubits (C.gates.take t.val) hlegal
  have h := normalized_applyGate hU hφ
  show Normalized ((finiteWordMatrix C.qubits (C.gates.take t.val)).mulVec φ)
  exact h

/-- The uniform clock superposition of the exact work history, scaled by the inverse square root
of the number of clock positions. -/
noncomputable def qmaHistoryState (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits)) :
    QState (Fin (C.gates.length + 1) × Reg C.qubits) :=
  fun p => (((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) : ℂ) * qmaExactHistory C φ p.1 p.2

/-- The norm of a complex number is at most the sum of the absolute values of its real and
imaginary parts. -/
theorem norm_le_abs_re_add_abs_im (w : ℂ) : ‖w‖ ≤ |w.re| + |w.im| := by
  have hde : ‖((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I‖ = ‖w‖ := by
    rw [Complex.re_add_im]
  rw [← hde]
  calc ‖((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I‖
        ≤ ‖((w.re : ℝ) : ℂ)‖ + ‖((w.im : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |w.re| + |w.im| * ‖Complex.I‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ = |w.re| + |w.im| := by
        rw [Complex.norm_I]
        ring

/-- The squared norm of a scaled history amplitude factors into the squared real scaling factor
and the squared work amplitude norm. -/
theorem norm_c_hist (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits))
    (t : Fin (C.gates.length + 1)) (y : Reg C.qubits) :
    ‖((((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) : ℂ) * qmaExactHistory C φ t y)‖ ^ 2
      = ((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) ^ 2 * ‖qmaExactHistory C φ t y‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]

/-- The uniform history state of a normalized input is normalized. -/
theorem normalized_qmaHistoryState {C : QmaHistoryCircuit} {φ : QState (Reg C.qubits)}
    (hφ : Normalized φ) : Normalized (qmaHistoryState C φ) := by
  have hnorm : ∀ t : Fin (C.gates.length + 1), Normalized (qmaExactHistory C φ t) :=
    fun t => normalized_qmaExactHistory hφ t
  have hN : (0 : ℝ) < C.gates.length + 1 := by positivity
  have hsq : ((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) ^ 2 = 1 / (C.gates.length + 1) := by
    rw [inv_pow, Real.sq_sqrt (by positivity), one_div]
  unfold Normalized
  unfold qmaHistoryState
  rw [Fintype.sum_prod_type]
  have hmul : ∀ t : Fin (C.gates.length + 1), ∀ y : Reg C.qubits,
      ‖((((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) : ℂ) * qmaExactHistory C φ t y)‖ ^ 2
        = (1 / (C.gates.length + 1) : ℝ) * ‖qmaExactHistory C φ t y‖ ^ 2 := by
    intro t y
    rw [norm_c_hist, hsq]
  conv_lhs =>
    simp only [hmul]
  have hpull : ∀ x : Fin (C.gates.length + 1),
      (∑ y : Reg C.qubits, (1 / (C.gates.length + 1) : ℝ) * ‖qmaExactHistory C φ x y‖ ^ 2)
        = (1 / (C.gates.length + 1) : ℝ) * ∑ y : Reg C.qubits, ‖qmaExactHistory C φ x y‖ ^ 2 := by
    intro x
    exact (Finset.mul_sum _ _ _).symm
  conv_lhs =>
    simp only [hpull]
  have hpull2 :
      (∑ x : Fin (C.gates.length + 1),
          (1 / (C.gates.length + 1) : ℝ) * ∑ y : Reg C.qubits, ‖qmaExactHistory C φ x y‖ ^ 2)
        = (1 / (C.gates.length + 1) : ℝ) *
            ∑ x : Fin (C.gates.length + 1), ∑ y : Reg C.qubits, ‖qmaExactHistory C φ x y‖ ^ 2 :=
    (Finset.mul_sum _ _ _).symm
  have hsum : ∑ t : Fin (C.gates.length + 1), ∑ y : Reg C.qubits,
      ‖qmaExactHistory C φ t y‖ ^ 2
      = ∑ t : Fin (C.gates.length + 1), (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro t _
    exact hnorm t
  rw [hpull2, hsum, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  field_simp

/-- Matrix-vector multiplication distributes over addition of matrices. -/
theorem mulVec_add {I : Type*} [Fintype I] (A B : Matrix I I ℂ) (v : I → ℂ) :
    (A + B) *ᵥ v = A *ᵥ v + B *ᵥ v := by
  ext i
  unfold mulVec dotProduct
  simp only [Matrix.add_apply, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

/-- The finite complex inner product is additive in its second argument. -/
theorem inner_add_right {I : Type*} [Fintype I] (u v w : I → ℂ) :
    Qatlib.Foundations.PureStateMath.Inner u (v + w) = Qatlib.Foundations.PureStateMath.Inner u v + Qatlib.Foundations.PureStateMath.Inner u w := by
  unfold Qatlib.Foundations.PureStateMath.Inner
  show star u ⬝ᵥ (v + w) = star u ⬝ᵥ v + star u ⬝ᵥ w
  simp [dotProduct, Pi.add_apply, Finset.sum_add_distrib, mul_add]

/-- The finite complex inner product with zero in its second argument vanishes. -/
theorem inner_zero_right {I : Type*} [Fintype I] (u : I → ℂ) :
    Qatlib.Foundations.PureStateMath.Inner u 0 = 0 := by
  unfold Qatlib.Foundations.PureStateMath.Inner
  simp [dotProduct]

/-- The energy quadratic form is additive in the matrix argument. -/
theorem qmaEnergy_add {I : Type*} [Fintype I] (A B : Matrix I I ℂ) (η : QState I) :
    qmaEnergy (A + B) η = qmaEnergy A η + qmaEnergy B η := by
  unfold qmaEnergy
  rw [mulVec_add, inner_add_right]
  simp [Complex.add_re]

/-- The zero matrix has zero energy on every state. -/
theorem qmaEnergy_zero {I : Type*} [Fintype I] (η : QState I) :
    qmaEnergy (0 : Matrix I I ℂ) η = 0 := by
  unfold qmaEnergy
  have hz : (0 : Matrix I I ℂ) *ᵥ η = 0 := by
    ext i
    simp
  rw [hz, inner_zero_right]
  simp

/-- The energy of a list sum of history term matrices equals the sum of their individual
energies. -/
theorem qmaEnergy_foldr {n m : ℕ}
    (η : QState (Fin (m + 1) × Reg n)) :
    ∀ ts : List (QmaHistoryTerm n m),
      qmaEnergy (ts.foldr (fun t M => t.matrix + M)
          (0 : Matrix (Fin (m + 1) × Reg n) (Fin (m + 1) × Reg n) ℂ)) η
        = (ts.map fun t => qmaEnergy t.matrix η).sum := by
  intro ts
  induction ts with
  | nil => exact qmaEnergy_zero _
  | cons t ts ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [qmaEnergy_add, ih]

/-- A computational basis ket is one at its basis index and zero elsewhere. -/
theorem ket_apply' {ι : Type*} [DecidableEq ι] (i p : ι) :
    Qatlib.Foundations.PureStateMath.Ket i p = if p = i then (1 : ℂ) else 0 := by
  unfold Qatlib.Foundations.PureStateMath.Ket
  simp

/-- The exact history at time zero equals the initial work state. -/
theorem qmaExactHistory_zero (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits)) :
    qmaExactHistory C φ ⟨0, by omega⟩ = φ := by
  unfold qmaExactHistory
  simp [finiteWordMatrix]

/-- An input penalty retains precisely the initial-time amplitudes whose bit on wire `j` is
true. -/
theorem qmaInTerm_mulVec' (n m : ℕ) (j : Fin n)
    (η : QState (Fin (m + 1) × Reg n)) (p : Fin (m + 1) × Reg n) :
    (qmaInTerm n m j *ᵥ η) p
      = (if p.1 = 0 then (1 : ℂ) else 0) * (if p.2 j then (1 : ℂ) else 0) * η p := by
  unfold mulVec
  show (∑ q, qmaInTerm n m j p q * η q)
    = (if p.1 = 0 then (1 : ℂ) else 0) * (if p.2 j then (1 : ℂ) else 0) * η p
  rw [Finset.sum_congr rfl (fun q _ => by rw [qmaInTerm_entry])]
  classical
  set q0 : Fin (m + 1) × Reg n := ⟨⟨0, by omega⟩, p.2⟩ with hq0def
  have hterm : ∀ q : Fin (m + 1) × Reg n,
      Qatlib.Foundations.PureStateMath.Ket 0 p.1 * Qatlib.Foundations.PureStateMath.Ket 0 q.1 *
        (if p.2 = q.2 then (if p.2 j then (1 : ℂ) else 0) else 0) * η q
      = if q = q0 then
          (if p.1 = 0 then (1 : ℂ) else 0) * (if p.2 j then (1 : ℂ) else 0) * η q
        else 0 := by
    intro q
    rw [ket_apply', ket_apply']
    by_cases hq : q = q0
    · rw [if_pos hq, hq]
      simp [hq0def]
    · rw [if_neg hq]
      by_cases hq1 : q.1 = 0
      · by_cases hq2 : q.2 = p.2
        · exfalso
          apply hq
          apply Prod.ext
          · apply Fin.ext
            show (q.1 : ℕ) = 0
            rw [hq1, Fin.val_zero]
          · exact hq2
        · have hne : ¬(p.2 = q.2) := fun h => hq2 h.symm
          simp [hq1, hne]
      · simp [hq1]
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [hq0def]
  by_cases hp1 : p.1 = 0
  · have hp : p = (⟨0, by omega⟩, p.2) := by
      apply Prod.ext
      · apply Fin.ext
        show (p.1 : ℕ) = 0
        rw [hp1, Fin.val_zero]
      · rfl
    rw [hp]
  · simp [hp1]

/-- An initialized wire contributes zero input energy to the history state of a legal input. -/
theorem qmaEnergy_inTerm_zero (C : QmaHistoryCircuit)
    (φ : QState (Reg C.qubits)) (j : Fin C.qubits)
    (hj : j ∈ C.initZeroWires) (hleg : QmaInitLegal C φ) :
    qmaEnergy (qmaInTerm C.qubits C.gates.length j) (qmaHistoryState C φ) = 0 := by
  unfold qmaEnergy
  have hmv : qmaInTerm C.qubits C.gates.length j *ᵥ qmaHistoryState C φ
      = fun p => (if p.1 = 0 then (1 : ℂ) else 0)
          * (if p.2 j then (1 : ℂ) else 0) * qmaHistoryState C φ p := by
    funext p
    exact qmaInTerm_mulVec' C.qubits C.gates.length j (qmaHistoryState C φ) p
  rw [hmv]
  unfold Qatlib.Foundations.PureStateMath.Inner dotProduct
  have hzero : ∀ p : Fin (C.gates.length + 1) × Reg C.qubits,
      p.1 = 0 → p.2 j = true → qmaHistoryState C φ p = 0 := by
    intro p hp1 hpj
    unfold qmaHistoryState
    have h0 : qmaExactHistory C φ p.1 = φ := by
      rw [hp1]
      exact qmaExactHistory_zero C φ
    rw [h0]
    have hlegj : ∀ y : Reg C.qubits, y j = true → φ y = 0 := by
      intro y hyj
      by_contra hne
      have hfalse := hleg y hne j hj
      simp [hfalse] at hyj
    rw [hlegj p.2 hpj, mul_zero]
  have hsum : ∀ p : Fin (C.gates.length + 1) × Reg C.qubits,
      (star (qmaHistoryState C φ) p) *
          ((if p.1 = 0 then (1 : ℂ) else 0)
            * (if p.2 j then (1 : ℂ) else 0) * qmaHistoryState C φ p) = 0 := by
    intro p
    by_cases hp1 : p.1 = 0
    · by_cases hpj : p.2 j
      · rw [hzero p hp1 hpj]
        simp
      · simp [hp1, hpj]
    · simp [hp1]
  rw [Finset.sum_eq_zero (fun x _ => hsum x)]
  simp

/-- An output penalty retains precisely the final-time amplitudes whose output bit is false. -/
theorem qmaOutTerm_mulVec' (n m : ℕ) (out : Fin n)
    (η : QState (Fin (m + 1) × Reg n)) (p : Fin (m + 1) × Reg n) :
    (qmaOutTerm n m out *ᵥ η) p
      = (if p.1 = Fin.last m then (1 : ℂ) else 0)
          * (if p.2 out then (0 : ℂ) else 1) * η p := by
  unfold mulVec
  show (∑ q, qmaOutTerm n m out p q * η q)
    = (if p.1 = Fin.last m then (1 : ℂ) else 0)
        * (if p.2 out then (0 : ℂ) else 1) * η p
  rw [Finset.sum_congr rfl (fun q _ => by rw [qmaOutTerm_entry])]
  classical
  set q0 : Fin (m + 1) × Reg n := ⟨Fin.last m, p.2⟩ with hq0def
  have hterm : ∀ q : Fin (m + 1) × Reg n,
      Qatlib.Foundations.PureStateMath.Ket (Fin.last m) p.1 * Qatlib.Foundations.PureStateMath.Ket (Fin.last m) q.1 *
        (if p.2 = q.2 then (if p.2 out then (0 : ℂ) else 1) else 0) * η q
      = if q = q0 then
          (if p.1 = Fin.last m then (1 : ℂ) else 0)
            * (if p.2 out then (0 : ℂ) else 1) * η q
        else 0 := by
    intro q
    rw [ket_apply', ket_apply']
    by_cases hq : q = q0
    · rw [if_pos hq, hq]
      simp [hq0def]
    · rw [if_neg hq]
      by_cases hq1 : q.1 = Fin.last m
      · by_cases hq2 : q.2 = p.2
        · exfalso
          apply hq
          apply Prod.ext
          · exact hq1
          · exact hq2
        · have hne : ¬(p.2 = q.2) := fun h => hq2 h.symm
          simp [hq1, hne]
      · simp [hq1]
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [hq0def]
  by_cases hp1 : p.1 = Fin.last m
  · have hp : p = (Fin.last m, p.2) := by
      apply Prod.ext
      · exact hp1
      · rfl
    rw [hp]
  · simp [hp1]

/-- The final-clock history amplitude is the final exact work amplitude scaled by the inverse
square root of the clock length. -/
theorem qmaHistoryState_at_last (C : QmaHistoryCircuit)
    (φ : QState (Reg C.qubits)) (y : Reg C.qubits) :
    qmaHistoryState C φ (Fin.last C.gates.length, y)
      = (((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) : ℂ)
          * qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩ y := by
  unfold qmaHistoryState
  rfl

/-- The last exact history slice equals the full gate word applied to the initial state. -/
theorem qmaExactHistory_last (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits)) :
    qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩
      = (finiteWordMatrix C.qubits C.gates).mulVec φ := by
  unfold qmaExactHistory
  have hval : (⟨Fin.last C.gates.length, by omega⟩ : Fin (C.gates.length + 1)).val
      = C.gates.length := by simp [Fin.val_last]
  rw [hval]
  have h : C.gates.take C.gates.length = C.gates :=
    List.take_of_length_le (Nat.le_refl _)
  rw [h]

/-- A basis outcome's Born weight equals the squared norm of its amplitude. -/
theorem bornProb_eq_normSq {I : Type*} [Fintype I] (ψ : QState I) (i : I) :
    BornProb ψ i = ‖ψ i‖ ^ 2 := by
  unfold BornProb
  simp [Complex.normSq_eq_norm_sq]

/-- The real part of a product of two real numbers cast to the complex numbers equals their real
product. -/
theorem ofReal_mul_re (a b : ℝ) :
    (((a : ℝ) : ℂ) * ((b : ℝ) : ℂ)).re = a * b := by
  rw [← Complex.ofReal_mul]
  simp

/-- The real part of a power of a real number cast to the complex numbers equals its real power. -/
theorem ofReal_pow_re (a : ℝ) (n : ℕ) :
    (((a : ℝ) : ℂ) ^ n).re = a ^ n := by
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- For positive `N`, the square of the inverse square root of `N` equals `1 / N`. -/
theorem inv_sqrt_sq (N : ℕ) (hN : 0 < N) :
    ((Real.sqrt N)⁻¹) ^ (2 : ℕ) = (1 / N : ℝ) := by
  rw [inv_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- The real part of the clock normalization factor squared times `1 - S` equals `(1 - S) / (m +
1)`. -/
theorem qmaOutEnergy_algebra (m : ℕ) (S : ℝ) :
    ((((Real.sqrt (m + 1))⁻¹ : ℝ) : ℂ) ^ (2 : ℕ) * ((1 - S : ℝ) : ℂ)).re
      = (1 - S) / (m + 1) := by
  have hN : 0 < m + 1 := by positivity
  rw [← Complex.ofReal_pow, inv_pow]
  have h2 : (((Real.sqrt (m + 1)) ^ (2 : ℕ))⁻¹ : ℝ) = (1 / (m + 1) : ℝ) := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  rw [h2, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- The product of a complex number's conjugate with itself is its squared norm cast to the
complex numbers. -/
theorem star_mul_self (ψ : ℂ) : star ψ * ψ = (↑(‖ψ‖ ^ 2) : ℂ) := by
  have h1 := (Complex.normSq_eq_conj_mul_self (z := ψ)).symm
  rw [Complex.normSq_eq_norm_sq] at h1
  exact h1

/-- Complex conjugation fixes a real number cast to the complex numbers. -/
theorem star_ofReal (r : ℝ) : star (r : ℂ) = r :=
  Complex.conj_ofReal r

/-- The squared modulus of a real-scaled complex number factors into the square of the scalar
and the squared modulus. -/
theorem star_smul_self (r : ℝ) (ψ : ℂ) :
    star (((r : ℝ) : ℂ) * ψ) * (((r : ℝ) : ℂ) * ψ)
      = (((r : ℝ) : ℂ) ^ 2) * (↑(‖ψ‖ ^ 2) : ℂ) := by
  rw [star_mul', mul_mul_mul_comm, star_ofReal, star_mul_self]
  ring

set_option autoImplicit false

/-- The history circuit's acceptance weight is the sum of final-state Born weights over true
output bits. -/
theorem qmaHistoryAcceptProb_eq (C : QmaHistoryCircuit)
    (φ : QState (Reg C.qubits)) :
    qmaHistoryAcceptProb C φ
      = ∑ y : Reg C.qubits, if y C.outputWire then
          BornProb ((finiteWordMatrix C.qubits C.gates).mulVec φ) y else 0 := by
  unfold qmaHistoryAcceptProb MeasureProb
  have hrun : Run (1 : Matrix (Reg C.qubits) (Reg C.qubits) ℂ)
      (finiteCodeCircuit C.qubits C.gates) φ
      = (finiteWordMatrix C.qubits C.gates).mulVec φ := run_finiteCodeCircuit C.qubits C.gates φ
  rw [hrun]
  classical
  rw [Finset.sum_filter]

/-- The Born weights of a normalized finite state sum to one. -/
theorem sum_bornProb {I : Type*} [Fintype I] (ψ : QState I) (hψ : Normalized ψ) :
    ∑ y : I, BornProb ψ y = 1 := by
  unfold Normalized at hψ
  unfold BornProb
  exact hψ

/-- For a normalized input, the history state's output energy is its rejection weight divided by
the number of clock positions. -/
theorem qmaEnergy_outTerm (C : QmaHistoryCircuit)
    (φ : QState (Reg C.qubits)) (hφ : Normalized φ) :
    qmaEnergy (qmaOutTerm C.qubits C.gates.length C.outputWire) (qmaHistoryState C φ)
      = (1 - qmaHistoryAcceptProb C φ) / (C.gates.length + 1) := by
  have hm : Normalized (qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩) :=
    normalized_qmaExactHistory hφ _
  unfold qmaEnergy
  have hmv : qmaOutTerm C.qubits C.gates.length C.outputWire *ᵥ qmaHistoryState C φ
      = fun p => (if p.1 = Fin.last C.gates.length then (1 : ℂ) else 0)
          * (if p.2 C.outputWire then (0 : ℂ) else 1) * qmaHistoryState C φ p := by
    funext p
    exact qmaOutTerm_mulVec' C.qubits C.gates.length C.outputWire (qmaHistoryState C φ) p
  rw [hmv]
  unfold Qatlib.Foundations.PureStateMath.Inner dotProduct

  have hsum : ∀ p : Fin (C.gates.length + 1) × Reg C.qubits,
      (star (qmaHistoryState C φ) p) *
          ((if p.1 = Fin.last C.gates.length then (1 : ℂ) else 0)
            * (if p.2 C.outputWire then (0 : ℂ) else 1) * qmaHistoryState C φ p)
        = if p.1 = Fin.last C.gates.length ∧ ¬ p.2 C.outputWire then
            star (qmaHistoryState C φ p) * qmaHistoryState C φ p else 0 := by
    intro p
    by_cases hp1 : p.1 = Fin.last C.gates.length
    · by_cases hpj : p.2 C.outputWire <;> simp [hp1, hpj]
    · simp [hp1]
  rw [Finset.sum_congr rfl (fun p _ => hsum p)]
  classical
  rw [Fintype.sum_prod_type]

  have honly : ∀ t : Fin (C.gates.length + 1),
      (∑ y : Reg C.qubits,
        if t = Fin.last C.gates.length ∧ ¬ y C.outputWire then
          star (qmaHistoryState C φ (t, y)) * qmaHistoryState C φ (t, y) else 0)
      = if t = Fin.last C.gates.length then
          (∑ y : Reg C.qubits,
            if ¬ y C.outputWire then
              star (qmaHistoryState C φ (Fin.last C.gates.length, y))
                * qmaHistoryState C φ (Fin.last C.gates.length, y) else 0)
        else 0 := by
    intro t
    by_cases ht : t = Fin.last C.gates.length
    · rw [ht]
      simp only [true_and, if_true]
    · rw [if_neg ht]
      apply Finset.sum_eq_zero
      intro y _
      rw [if_neg (fun h => ht h.1)]
  rw [Finset.sum_congr rfl (fun t _ => honly t), Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]

  have hη : ∀ y : Reg C.qubits,
      star (qmaHistoryState C φ (Fin.last C.gates.length, y))
        * qmaHistoryState C φ (Fin.last C.gates.length, y)
      = (((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) : ℂ) ^ 2
          * (↑(‖qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩ y‖ ^ 2) : ℂ) := by
    intro y
    rw [qmaHistoryState_at_last]
    exact star_smul_self _ _

  have hterm : ∀ y : Reg C.qubits,
      (if ¬ y C.outputWire then
          star (qmaHistoryState C φ (Fin.last C.gates.length, y))
            * qmaHistoryState C φ (Fin.last C.gates.length, y)
        else 0)
        = (((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) : ℂ) ^ 2
            * (↑(if ¬ y C.outputWire then
              ‖qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩ y‖ ^ 2 else 0) : ℂ) := by
    intro y
    split_ifs with h
    · rw [Complex.ofReal_zero, mul_zero]
    · exact hη y
  rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum, ← Complex.ofReal_sum]

  have hsplit : (∑ y : Reg C.qubits, if ¬ y C.outputWire then
      ‖qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩ y‖ ^ 2 else 0)
      = (1 : ℝ) - ∑ y : Reg C.qubits, if y C.outputWire then
          ‖qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩ y‖ ^ 2 else 0 := by
    have h1 : (∑ y, if ¬ y C.outputWire then
        ‖qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩ y‖ ^ 2 else 0)
        + (∑ y, if y C.outputWire then
          ‖qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩ y‖ ^ 2 else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      have hcongr : ∀ y : Reg C.qubits,
          (if ¬ y C.outputWire then
            ‖qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩ y‖ ^ 2 else 0)
          + (if y C.outputWire then
            ‖qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩ y‖ ^ 2 else 0)
          = ‖qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩ y‖ ^ 2 := by
        intro y
        by_cases hy : y C.outputWire <;> simp [hy]
      rw [Finset.sum_congr rfl (fun y _ => hcongr y)]
      exact sum_bornProb _ hm
    linarith

  have happ : qmaHistoryAcceptProb C φ
      = ∑ y : Reg C.qubits, if y C.outputWire then
          ‖qmaExactHistory C φ ⟨Fin.last C.gates.length, by omega⟩ y‖ ^ 2 else 0 := by
    rw [qmaHistoryAcceptProb_eq, qmaExactHistory_last]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases hy : y C.outputWire <;> simp [hy, bornProb_eq_normSq]
  rw [hsplit, ← happ]
  exact qmaOutEnergy_algebra C.gates.length (qmaHistoryAcceptProb C φ)

open Matrix
open scoped BigOperators

set_option maxHeartbeats 800000

/-- The sum of the squared norms of the coordinates of a finite complex vector. -/
noncomputable def vn {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- The Euclidean norm of a finite complex vector, defined as `sqrt (vn v)`. -/
noncomputable def nm {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := Real.sqrt (vn v)

/-- The squared coordinate norm `vn v` is nonnegative. -/
theorem vn_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) : 0 ≤ vn v :=
  Finset.sum_nonneg (fun _ _ => by positivity)

/-- The Euclidean norm `nm v` is nonnegative. -/
theorem nm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) : 0 ≤ nm v :=
  Real.sqrt_nonneg _

/-- The square of `nm v` equals `vn v`. -/
theorem nm_sq {ι : Type*} [Fintype ι] (v : ι → ℂ) : nm v ^ 2 = vn v :=
  Real.sq_sqrt (vn_nonneg v)

/-- The squared coordinate norm of the zero vector is zero. -/
theorem vn_zero {ι : Type*} [Fintype ι] : vn (0 : ι → ℂ) = 0 := by
  simp [vn]

/-- Scaling a vector by `c` multiplies its squared coordinate norm by `‖c‖²`. -/
theorem vn_smul {ι : Type*} [Fintype ι] (c : ℂ) (v : ι → ℂ) :
    vn (fun i => c * v i) = ‖c‖ ^ 2 * vn v := by
  unfold vn
  simp only [norm_mul, mul_pow]
  rw [Finset.mul_sum]

/-- The modulus of a finite complex inner product is at most the sum of the products of
coordinate norms. -/
theorem abs_cinner_le {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ i, star (a i) * b i‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
  have h := norm_sum_le (Finset.univ) (fun i : ι => star (a i) * b i)

  have h3 : (∑ i ∈ Finset.univ, ‖star (a i) * b i‖) = ∑ i, ‖a i‖ * ‖b i‖ := by
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_mul, norm_star]
  rw [← h3]
  simpa using! h

/-- The square of the sum of coordinate norm products is bounded by `vn a * vn b`. -/
theorem sum_norm_mul_le {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    (∑ i, ‖a i‖ * ‖b i‖) ^ 2 ≤ vn a * vn b := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : ι => ‖a i‖) (fun i : ι => ‖b i‖)
  have h1 : (∑ i, ‖a i‖ * ‖b i‖) ^ 2
      ≤ (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
    simpa [mul_comm] using! h
  simpa [vn] using! h1

/-- The real part of a finite complex inner product is at most `sqrt (vn a * vn b)`. -/
theorem re_cinner_le {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    (∑ i, star (a i) * b i).re ≤ Real.sqrt (vn a * vn b) := by
  have h1 : (∑ i, star (a i) * b i).re ≤ ‖∑ i, star (a i) * b i‖ := Complex.re_le_norm _
  have h2 : ‖∑ i, star (a i) * b i‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := abs_cinner_le a b
  have h3 : (∑ i, ‖a i‖ * ‖b i‖) ^ 2 ≤ vn a * vn b := sum_norm_mul_le a b
  have h4 : 0 ≤ ∑ i, ‖a i‖ * ‖b i‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have h5 : 0 ≤ vn a * vn b := mul_nonneg (vn_nonneg a) (vn_nonneg b)
  have h6 : ∑ i, ‖a i‖ * ‖b i‖ ≤ Real.sqrt (vn a * vn b) :=
    (Real.le_sqrt h4 h5).mpr h3
  linarith

/-- Rounding a complex number at precision `b` changes it by norm at most `2⁻ᵇ`. -/
theorem g13n_roundC_dist (b : ℕ) (z : ℂ) :
    ‖qmaRoundC b z - z‖ ≤ 1 / (2 : ℝ) ^ b := by
  have hpowb : (0 : ℝ) < 2 ^ b := pow_pos two_pos b
  have hfloor : ∀ x : ℝ, |(Int.floor (x + 1 / 2) : ℝ) - x| ≤ 1 / 2 := by
    intro x
    have h1 : (Int.floor (x + 1 / 2) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
    have h2 : x + 1 / 2 < (Int.floor (x + 1 / 2) : ℝ) + 1 := Int.lt_floor_add_one _
    rw [abs_sub_le_iff]
    constructor <;> linarith
  set fr : ℝ := (Int.floor (z.re * 2 ^ b + 1 / 2) : ℝ) with hfr
  set fi : ℝ := (Int.floor (z.im * 2 ^ b + 1 / 2) : ℝ) with hfi
  have hdre : |fr - z.re * 2 ^ b| ≤ 1 / 2 := by
    rw [hfr]
    have := hfloor (z.re * 2 ^ b)
    simpa using! this
  have hdri : |fi - z.im * 2 ^ b| ≤ 1 / 2 := by
    rw [hfi]
    have := hfloor (z.im * 2 ^ b)
    simpa using! this

  have key : qmaRoundC b z - z
      = (((fr / 2 ^ b : ℝ) : ℂ) - ((z.re : ℝ) : ℂ))
        + Complex.I * (((fi / 2 ^ b : ℝ) : ℂ) - ((z.im : ℝ) : ℂ)) := by
    unfold qmaRoundC
    have hfrC : ((Int.floor (z.re * 2 ^ b + 1 / 2) : ℤ) : ℂ) = ((fr : ℝ) : ℂ) := by
      rw [hfr]; norm_cast
    have hfiC : ((Int.floor (z.im * 2 ^ b + 1 / 2) : ℤ) : ℂ) = ((fi : ℝ) : ℂ) := by
      rw [hfi]; norm_cast
    rw [hfrC, hfiC]
    have hpowC : (((2 : ℝ) ^ b : ℝ) : ℂ) = ((2 : ℂ) ^ b) := by
      rw [Complex.ofReal_pow]; norm_num
    have hreD : ((fr / 2 ^ b : ℝ) : ℂ) = ((fr : ℝ) : ℂ) / ((2 : ℂ) ^ b) := by
      rw [Complex.ofReal_div, hpowC]
    have hfiD : ((fi / 2 ^ b : ℝ) : ℂ) = ((fi : ℝ) : ℂ) / ((2 : ℂ) ^ b) := by
      rw [Complex.ofReal_div, hpowC]
    rw [hreD, hfiD]
    conv_lhs => rw [(Complex.re_add_im z).symm]
    rw [mul_sub, add_div, mul_div_assoc]
    ring
  rw [key]
  have hre : ‖((fr / 2 ^ b : ℝ) : ℂ) - ((z.re : ℝ) : ℂ)‖ = |fr - z.re * 2 ^ b| / (2 ^ b : ℝ) := by
    have h1 : ((fr / 2 ^ b : ℝ) : ℂ) - ((z.re : ℝ) : ℂ)
        = ((((fr - z.re * 2 ^ b : ℝ) / 2 ^ b : ℝ) : ℝ) : ℂ) := by
      have h2 : ((fr / 2 ^ b : ℝ) : ℂ) - ((z.re : ℝ) : ℂ)
          = (((fr / 2 ^ b - z.re : ℝ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_sub]
      rw [h2]
      congr 1
      rw [sub_div]
      have h3 : (z.re * 2 ^ b / 2 ^ b : ℝ) = z.re := by
        rw [mul_div_assoc, div_self (ne_of_gt hpowb), mul_one]
      rw [h3]
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hpowb]
  have him : ‖Complex.I * (((fi / 2 ^ b : ℝ) : ℂ) - ((z.im : ℝ) : ℂ))‖
      = |fi - z.im * 2 ^ b| / (2 ^ b : ℝ) := by
    rw [norm_mul, Complex.norm_I, one_mul]
    have h1 : ((fi / 2 ^ b : ℝ) : ℂ) - ((z.im : ℝ) : ℂ)
        = ((((fi - z.im * 2 ^ b : ℝ) / 2 ^ b : ℝ) : ℝ) : ℂ) := by
      have h2 : ((fi / 2 ^ b : ℝ) : ℂ) - ((z.im : ℝ) : ℂ)
          = (((fi / 2 ^ b - z.im : ℝ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_sub]
      rw [h2]
      congr 1
      rw [sub_div]
      have h3 : (z.im * 2 ^ b / 2 ^ b : ℝ) = z.im := by
        rw [mul_div_assoc, div_self (ne_of_gt hpowb), mul_one]
      rw [h3]
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hpowb]
  have hsum : ‖((fr / 2 ^ b : ℝ) : ℂ) - ((z.re : ℝ) : ℂ)
      + Complex.I * (((fi / 2 ^ b : ℝ) : ℂ) - ((z.im : ℝ) : ℂ))‖
      ≤ ‖((fr / 2 ^ b : ℝ) : ℂ) - ((z.re : ℝ) : ℂ)‖
        + ‖Complex.I * (((fi / 2 ^ b : ℝ) : ℂ) - ((z.im : ℝ) : ℂ))‖ := norm_add_le _ _
  have htot : |fr - z.re * 2 ^ b| / (2 ^ b : ℝ) + |fi - z.im * 2 ^ b| / (2 ^ b : ℝ)
      ≤ 1 / (2 : ℝ) ^ b := by
    have h1 : |fr - z.re * 2 ^ b| + |fi - z.im * 2 ^ b| ≤ 1 := by linarith
    calc |fr - z.re * 2 ^ b| / (2 ^ b : ℝ) + |fi - z.im * 2 ^ b| / (2 ^ b : ℝ)
          = (|fr - z.re * 2 ^ b| + |fi - z.im * 2 ^ b|) / (2 ^ b : ℝ) := by ring
        _ ≤ 1 / (2 : ℝ) ^ b := by
          rw [div_le_div_iff_of_pos_right hpowb]
          nlinarith
  calc ‖((fr / 2 ^ b : ℝ) : ℂ) - ((z.re : ℝ) : ℂ)
        + Complex.I * (((fi / 2 ^ b : ℝ) : ℂ) - ((z.im : ℝ) : ℂ))‖
      ≤ ‖((fr / 2 ^ b : ℝ) : ℂ) - ((z.re : ℝ) : ℂ)‖
        + ‖Complex.I * (((fi / 2 ^ b : ℝ) : ℂ) - ((z.im : ℝ) : ℂ))‖ := hsum
    _ = |fr - z.re * 2 ^ b| / (2 ^ b : ℝ) + |fi - z.im * 2 ^ b| / (2 ^ b : ℝ) := by
        rw [hre, him]
    _ ≤ 1 / (2 : ℝ) ^ b := htot

/-- Expands the energy quadratic form as the real part of a double sum over matrix entries. -/
theorem qmaEnergy_entrywise {I : Type*} [Fintype I] (T : Matrix I I ℂ) (η : QState I) :
    qmaEnergy T η = (∑ p : I, ∑ q : I, star (η p) * (T p q * η q)).re := by
  unfold qmaEnergy Qatlib.Foundations.PureStateMath.Inner
  show (∑ p, star (η p) * (∑ q, T p q * η q)).re = _
  rw [Finset.sum_congr rfl (fun p _ => Finset.mul_sum _ _ _)]

/-- Multiplying a complex number by its image under `starRingEnd` gives its squared norm cast to
the complex numbers. -/
theorem starRingEnd_mul_self (ψ : ℂ) : (starRingEnd ℂ) ψ * ψ = (↑(‖ψ‖ ^ 2) : ℂ) := by
  have h1 := (Complex.normSq_eq_conj_mul_self (z := ψ)).symm
  rw [Complex.normSq_eq_norm_sq] at h1
  exact h1

/-- The output penalty energy is the squared amplitude mass at final time with a false output
bit. -/
theorem g13n_out_energy (n m : ℕ) (out : Fin n) (η : QState (Fin (m + 1) × Reg n)) :
    qmaEnergy (qmaOutTerm n m out) η
      = ∑ y : Reg n, if y out then (0 : ℝ) else ‖η (Fin.last m, y)‖ ^ 2 := by
  unfold qmaEnergy Qatlib.Foundations.PureStateMath.Inner dotProduct
  simp only [Pi.star_apply]
  have hpoint : ∀ p : Fin (m + 1) × Reg n,
      (qmaOutTerm n m out *ᵥ η) p
        = (if p.1 = Fin.last m then (1 : ℂ) else 0)
            * (if p.2 out then (0 : ℂ) else 1) * η p :=
    fun p => qmaOutTerm_mulVec' n m out η p
  rw [Finset.sum_congr rfl (fun p _ => by rw [hpoint p])]
  have hsum : ∀ p : Fin (m + 1) × Reg n,
      (star (η p) *
          ((if p.1 = Fin.last m then (1 : ℂ) else 0)
            * (if p.2 out then (0 : ℂ) else 1) * η p))
        = if p.1 = Fin.last m ∧ ¬ p.2 out then (↑(‖η p‖ ^ 2) : ℂ) else 0 := by
    intro p
    by_cases hp1 : p.1 = Fin.last m
    · by_cases hpj : p.2 out
      · simp [hp1, hpj]
      · simp [hp1, hpj, starRingEnd_mul_self]
    · simp [hp1]
  rw [Finset.sum_congr rfl (fun p _ => hsum p)]
  classical
  rw [Fintype.sum_prod_type]
  have honly : ∀ t : Fin (m + 1),
      (∑ y : Reg n, if t = Fin.last m ∧ ¬ y out then (↑(‖η (t, y)‖ ^ 2) : ℂ) else 0)
      = if t = Fin.last m then
          (∑ y : Reg n, if ¬ y out then (↑(‖η (t, y)‖ ^ 2) : ℂ) else 0)
        else 0 := by
    intro t
    by_cases ht : t = Fin.last m
    · rw [ht]
      simp only [true_and, if_true]
    · rw [if_neg ht]
      apply Finset.sum_eq_zero
      intro y _
      rw [if_neg (fun h => ht h.1)]
  rw [Finset.sum_congr rfl (fun t _ => honly t), Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have hterm : ∀ y : Reg n,
      (if ¬ y out then (↑(‖η (Fin.last m, y)‖ ^ 2) : ℂ) else 0)
        = (↑(if y out then (0 : ℝ) else ‖η (Fin.last m, y)‖ ^ 2) : ℂ) := by
    intro y
    by_cases hy : y out <;> simp [hy]
  rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Complex.ofReal_sum, Complex.ofReal_re]

/-- The input penalty on wire `j` is the squared amplitude mass at time zero with that bit true. -/
theorem g13n_in_energy (n m : ℕ) (j : Fin n) (η : QState (Fin (m + 1) × Reg n)) :
    qmaEnergy (qmaInTerm n m j) η
      = ∑ y : Reg n, if y j then ‖η ((0 : Fin (m + 1)), y)‖ ^ 2 else (0 : ℝ) := by
  unfold qmaEnergy Qatlib.Foundations.PureStateMath.Inner dotProduct
  simp only [Pi.star_apply]
  have hpoint : ∀ p : Fin (m + 1) × Reg n,
      (qmaInTerm n m j *ᵥ η) p
        = (if p.1 = 0 then (1 : ℂ) else 0) * (if p.2 j then (1 : ℂ) else 0) * η p :=
    fun p => qmaInTerm_mulVec' n m j η p
  rw [Finset.sum_congr rfl (fun p _ => by rw [hpoint p])]
  have hsum : ∀ p : Fin (m + 1) × Reg n,
      (star (η p) *
          ((if p.1 = 0 then (1 : ℂ) else 0) * (if p.2 j then (1 : ℂ) else 0) * η p))
        = if p.1 = 0 ∧ p.2 j then (↑(‖η p‖ ^ 2) : ℂ) else 0 := by
    intro p
    by_cases hp1 : p.1 = 0
    · by_cases hpj : p.2 j
      · simp [hp1, hpj, starRingEnd_mul_self]
      · simp [hp1, hpj]
    · simp [hp1]
  rw [Finset.sum_congr rfl (fun p _ => hsum p)]
  classical
  rw [Fintype.sum_prod_type]
  have honly : ∀ t : Fin (m + 1),
      (∑ y : Reg n, if t = 0 ∧ y j then (↑(‖η (t, y)‖ ^ 2) : ℂ) else 0)
      = if t = 0 then
          (∑ y : Reg n, if y j then (↑(‖η (t, y)‖ ^ 2) : ℂ) else 0)
        else 0 := by
    intro t
    by_cases ht : t = 0
    · rw [ht]
      simp only [true_and, if_true]
    · rw [if_neg ht]
      apply Finset.sum_eq_zero
      intro y _
      rw [if_neg (fun h => ht h.1)]
  rw [Finset.sum_congr rfl (fun t _ => honly t), Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have hterm : ∀ y : Reg n,
      (if y j then (↑(‖η ((0 : Fin (m + 1)), y)‖ ^ 2) : ℂ) else 0)
        = (↑(if y j then ‖η ((0 : Fin (m + 1)), y)‖ ^ 2 else (0 : ℝ)) : ℂ) := by
    intro y
    by_cases hy : y j <;> simp [hy]
  rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Complex.ofReal_sum, Complex.ofReal_re]

/-- The work-register slice of a joint clock and work state at clock position `t`. -/
noncomputable def sl {n m : ℕ} (η : QState (Fin (m + 1) × Reg n)) (t : Fin (m + 1)) :
    QState (Reg n) := fun y => η (t, y)

/-- A finite sum supported at the single index `a` equals `f a`. -/
theorem g13n_sum_ite_fun {α : Type*} [Fintype α] [DecidableEq α] (a : α) (f : α → ℂ) :
    (∑ y : α, (if y = a then f y else (0 : ℂ))) = f a := by
  have h : ∀ y : α, (if y = a then f y else (0 : ℂ)) = if y = a then f a else (0 : ℂ) := by
    intro y
    by_cases hy : y = a
    · rw [if_pos hy, if_pos hy, hy]
    · rw [if_neg hy, if_neg hy]
  rw [Finset.sum_congr rfl (fun y _ => h y), Finset.sum_ite_eq']
  simp

/-- A finite sum with the condition `a = y` equals its single selected value `f a`. -/
theorem g13n_sum_ite_left {α : Type*} [Fintype α] [DecidableEq α] (a : α) (f : α → ℂ) :
    (∑ y : α, (if a = y then f y else (0 : ℂ))) = f a := by
  have key : ∀ y : α, (if a = y then f y else (0 : ℂ)) = (if y = a then f y else (0 : ℂ)) := by
    intro y
    by_cases hy : a = y
    · rw [if_pos hy, if_pos hy.symm]
    · rw [if_neg hy, if_neg (fun h => hy h.symm)]
  rw [Finset.sum_congr rfl (fun y _ => key y), g13n_sum_ite_fun]

/-- A finite sum supported at two distinct indices equals the sum of the two assigned values. -/
theorem g13n_sum_two {α : Type*} [Fintype α] [DecidableEq α] {a b : α} (hab : a ≠ b)
    (A B : ℂ) :
    (∑ t : α, (if t = a then A else if t = b then B else (0 : ℂ))) = A + B := by
  have h : ∀ t : α, (if t = a then A else if t = b then B else (0 : ℂ))
      = (if t = a then A else (0 : ℂ)) + (if t = b then B else (0 : ℂ)) := by
    intro t
    by_cases h1 : t = a
    · have h2 : ¬ t = b := fun hh => hab (h1.symm.trans hh)
      simp only [if_pos h1, if_neg h2]
      ring
    · by_cases h2 : t = b
      · have h3 : ¬ t = a := h1
        simp only [if_neg h3, if_pos h2]
        ring
      · simp only [if_neg h1, if_neg h2]
        ring
  rw [Finset.sum_congr rfl (fun t _ => h t), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- A propagation term acts only at its two adjacent clock slices, coupling them by the gate
matrix and its adjoint. -/
theorem g13n_prop_mulVec (n m : ℕ) (U : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (i : Fin m) (η : QState (Fin (m + 1) × Reg n)) (p : Fin (m + 1) × Reg n) :
    (qmaPropTerm n m U i *ᵥ η) p
      = if p.1 = i.succ then
          (1 / 2 : ℂ) * η p - (1 / 2 : ℂ) * (U i *ᵥ sl η i.castSucc) p.2
        else if p.1 = i.castSucc then
          (1 / 2 : ℂ) * η p - (1 / 2 : ℂ) * ((U i)ᴴ *ᵥ sl η i.succ) p.2
        else 0 := by
  unfold mulVec
  show (∑ q, qmaPropTerm n m U i p q * η q) = _
  rw [Finset.sum_congr rfl (fun q _ => by rw [qmaPropTerm_entry])]
  classical
  rw [Fintype.sum_prod_type]
  have hentry : ∀ t : Fin (m + 1), ∀ y : Reg n,
      ((if p.1 = i.succ ∧ t = i.succ then (1 / 2 : ℂ) * (1 : Matrix (Reg n) (Reg n) ℂ) p.2 y
        else if p.1 = i.castSucc ∧ t = i.castSucc then
          (1 / 2 : ℂ) * (1 : Matrix (Reg n) (Reg n) ℂ) p.2 y
        else if p.1 = i.succ ∧ t = i.castSucc then -((1 / 2 : ℂ) * U i p.2 y)
        else if p.1 = i.castSucc ∧ t = i.succ then -((1 / 2 : ℂ) * star (U i y p.2))
        else 0) * η (t, y))
      = (if p.1 = i.succ ∧ t = i.succ then
            (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
        else if p.1 = i.castSucc ∧ t = i.castSucc then
            (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
        else if p.1 = i.succ ∧ t = i.castSucc then
            -((1 / 2 : ℂ) * U i p.2 y * η (t, y))
        else if p.1 = i.castSucc ∧ t = i.succ then
            -((1 / 2 : ℂ) * star (U i y p.2) * η (t, y))
        else 0) := by
    intro t y
    by_cases c1 : p.1 = i.succ ∧ t = i.succ
    · have n2 : ¬ (p.1 = i.castSucc ∧ t = i.castSucc) :=
        fun h => fin_succ_ne_castSucc i (c1.1.symm.trans h.1)
      have n3 : ¬ (p.1 = i.succ ∧ t = i.castSucc) :=
        fun h => fin_succ_ne_castSucc i (c1.2.symm.trans h.2)
      have n4 : ¬ (p.1 = i.castSucc ∧ t = i.succ) :=
        fun h => fin_succ_ne_castSucc i (c1.1.symm.trans h.1)
      simp only [if_pos c1, if_neg n2, if_neg n3, if_neg n4, Matrix.one_apply, mul_ite, mul_zero]
      by_cases hy : p.2 = y
      · simp only [if_pos hy]
        ring
      · simp only [if_neg hy]
        ring
    · by_cases c2 : p.1 = i.castSucc ∧ t = i.castSucc
      · have n3 : ¬ (p.1 = i.succ ∧ t = i.castSucc) :=
          fun h => fin_succ_ne_castSucc i (h.1.symm.trans c2.1)
        have n4 : ¬ (p.1 = i.castSucc ∧ t = i.succ) :=
          fun h => fin_succ_ne_castSucc i (h.2.symm.trans c2.2)
        simp only [if_neg c1, if_pos c2, if_neg n3, if_neg n4, Matrix.one_apply, mul_ite, mul_zero]
        by_cases hy : p.2 = y
        · simp only [if_pos hy]
          ring
        · simp only [if_neg hy]
          ring
      · by_cases c3 : p.1 = i.succ ∧ t = i.castSucc
        · have n4 : ¬ (p.1 = i.castSucc ∧ t = i.succ) :=
            fun h => fin_succ_ne_castSucc i (c3.1.symm.trans h.1)
          simp only [if_neg c1, if_neg c2, if_pos c3, if_neg n4]
          ring
        · by_cases c4 : p.1 = i.castSucc ∧ t = i.succ
          · simp only [if_neg c1, if_neg c2, if_neg c3, if_pos c4]
            ring
          · simp only [if_neg c1, if_neg c2, if_neg c3, if_neg c4]
            ring
  rw [Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun y _ => hentry t y))]

  by_cases hp1 : p.1 = i.succ
  · have hpne : p.1 ≠ i.castSucc := fun hh => fin_succ_ne_castSucc i (hp1.symm.trans hh)
    rw [if_pos hp1]
    have hpq : (i.succ, p.2) = p := Prod.ext hp1.symm rfl
    have hsumt : ∀ t : Fin (m + 1),
        (∑ y : Reg n,
          (if p.1 = i.succ ∧ t = i.succ then (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
            else if p.1 = i.castSucc ∧ t = i.castSucc then
              (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
            else if p.1 = i.succ ∧ t = i.castSucc then
              -((1 / 2 : ℂ) * U i p.2 y * η (t, y))
            else if p.1 = i.castSucc ∧ t = i.succ then
              -((1 / 2 : ℂ) * star (U i y p.2) * η (t, y))
            else 0))
        = if t = i.succ then (1 / 2 : ℂ) * η p
          else if t = i.castSucc then
            -((1 / 2 : ℂ) * ∑ y : Reg n, U i p.2 y * η (i.castSucc, y))
          else 0 := by
      intro t
      by_cases ht1 : t = i.succ
      · have c1 : p.1 = i.succ ∧ t = i.succ := ⟨hp1, ht1⟩
        have n2 : ¬ (p.1 = i.castSucc ∧ t = i.castSucc) := fun h => hpne h.1
        have n3 : ¬ (p.1 = i.succ ∧ t = i.castSucc) :=
            fun h => fin_succ_ne_castSucc i (ht1.symm.trans h.2)
        have n4 : ¬ (p.1 = i.castSucc ∧ t = i.succ) := fun h => hpne h.1
        have hterm : ∀ y : Reg n,
            (if p.1 = i.succ ∧ t = i.succ then (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
              else if p.1 = i.castSucc ∧ t = i.castSucc then
                (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
              else if p.1 = i.succ ∧ t = i.castSucc then
                -((1 / 2 : ℂ) * U i p.2 y * η (t, y))
              else if p.1 = i.castSucc ∧ t = i.succ then
                -((1 / 2 : ℂ) * star (U i y p.2) * η (t, y))
              else 0) = (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0) := by
          intro y
          simp only [if_pos c1, if_neg n2, if_neg n3, if_neg n4]
        rw [Finset.sum_congr rfl (fun y _ => hterm y), g13n_sum_ite_left, if_pos ht1, ht1, hpq]
      · by_cases ht2 : t = i.castSucc
        · have n1 : ¬ (p.1 = i.succ ∧ t = i.succ) := fun h => ht1 h.2
          have n2 : ¬ (p.1 = i.castSucc ∧ t = i.castSucc) := fun h => hpne h.1
          have c3 : p.1 = i.succ ∧ t = i.castSucc := ⟨hp1, ht2⟩
          have n4 : ¬ (p.1 = i.castSucc ∧ t = i.succ) := fun h => hpne h.1
          have hterm : ∀ y : Reg n,
              (if p.1 = i.succ ∧ t = i.succ then (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
                else if p.1 = i.castSucc ∧ t = i.castSucc then
                  (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
                else if p.1 = i.succ ∧ t = i.castSucc then
                  -((1 / 2 : ℂ) * U i p.2 y * η (t, y))
                else if p.1 = i.castSucc ∧ t = i.succ then
                  -((1 / 2 : ℂ) * star (U i y p.2) * η (t, y))
                else 0) = -((1 / 2 : ℂ) * U i p.2 y * η (t, y)) := by
            intro y
            simp only [if_neg n1, if_neg n2, if_pos c3, if_neg n4]
          rw [Finset.sum_congr rfl (fun y _ => hterm y), if_neg ht1, if_pos ht2, ht2]
          rw [Finset.sum_neg_distrib]
          have hm : ∀ y : Reg n, (1 / 2 : ℂ) * U i p.2 y * η (i.castSucc, y)
              = (1 / 2 : ℂ) * (U i p.2 y * η (i.castSucc, y)) := by
            intro y; ring
          rw [Finset.sum_congr rfl (fun y _ => hm y), ← Finset.mul_sum]
        · have n1 : ¬ (p.1 = i.succ ∧ t = i.succ) := fun h => ht1 h.2
          have n2 : ¬ (p.1 = i.castSucc ∧ t = i.castSucc) := fun h => ht2 h.2
          have n3 : ¬ (p.1 = i.succ ∧ t = i.castSucc) := fun h => ht2 h.2
          have n4 : ¬ (p.1 = i.castSucc ∧ t = i.succ) := fun h => ht1 h.2
          have hterm : ∀ y : Reg n,
              (if p.1 = i.succ ∧ t = i.succ then (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
                else if p.1 = i.castSucc ∧ t = i.castSucc then
                  (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
                else if p.1 = i.succ ∧ t = i.castSucc then
                  -((1 / 2 : ℂ) * U i p.2 y * η (t, y))
                else if p.1 = i.castSucc ∧ t = i.succ then
                  -((1 / 2 : ℂ) * star (U i y p.2) * η (t, y))
                else 0) = (0 : ℂ) := by
            intro y
            simp only [if_neg n1, if_neg n2, if_neg n3, if_neg n4]
          rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_const, smul_zero,
            if_neg ht1, if_neg ht2]
    rw [Finset.sum_congr rfl (fun t _ => hsumt t), g13n_sum_two (fin_succ_ne_castSucc i)]
    show (1 / 2 : ℂ) * η p + -((1 / 2 : ℂ) * ∑ y : Reg n, U i p.2 y * η (i.castSucc, y))
        = (1 / 2 : ℂ) * η p - (1 / 2 : ℂ) * (∑ y : Reg n, U i p.2 y * η (i.castSucc, y))
    ring
  · by_cases hp2 : p.1 = i.castSucc
    · have hpne : p.1 ≠ i.succ := hp1
      rw [if_neg hp1, if_pos hp2]
      have hpq : (i.castSucc, p.2) = p := Prod.ext hp2.symm rfl
      have hsumt : ∀ t : Fin (m + 1),
          (∑ y : Reg n,
            (if p.1 = i.succ ∧ t = i.succ then (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
              else if p.1 = i.castSucc ∧ t = i.castSucc then
                (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
              else if p.1 = i.succ ∧ t = i.castSucc then
                -((1 / 2 : ℂ) * U i p.2 y * η (t, y))
              else if p.1 = i.castSucc ∧ t = i.succ then
                -((1 / 2 : ℂ) * star (U i y p.2) * η (t, y))
              else 0))
          = if t = i.castSucc then (1 / 2 : ℂ) * η p
            else if t = i.succ then
              -((1 / 2 : ℂ) * ∑ y : Reg n, star (U i y p.2) * η (i.succ, y))
            else 0 := by
        intro t
        by_cases ht2 : t = i.castSucc
        · have n1 : ¬ (p.1 = i.succ ∧ t = i.succ) := fun h => hpne h.1
          have c2 : p.1 = i.castSucc ∧ t = i.castSucc := ⟨hp2, ht2⟩
          have n3 : ¬ (p.1 = i.succ ∧ t = i.castSucc) := fun h => hpne h.1
          have n4 : ¬ (p.1 = i.castSucc ∧ t = i.succ) :=
            fun h => fin_succ_ne_castSucc i (h.2.symm.trans ht2)
          have hterm : ∀ y : Reg n,
              (if p.1 = i.succ ∧ t = i.succ then (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
                else if p.1 = i.castSucc ∧ t = i.castSucc then
                  (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
                else if p.1 = i.succ ∧ t = i.castSucc then
                  -((1 / 2 : ℂ) * U i p.2 y * η (t, y))
                else if p.1 = i.castSucc ∧ t = i.succ then
                  -((1 / 2 : ℂ) * star (U i y p.2) * η (t, y))
                else 0) = (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0) := by
            intro y
            simp only [if_neg n1, if_pos c2, if_neg n3, if_neg n4]
          rw [Finset.sum_congr rfl (fun y _ => hterm y), g13n_sum_ite_left, if_pos ht2, ht2, hpq]
        · by_cases ht1 : t = i.succ
          · have n1 : ¬ (p.1 = i.succ ∧ t = i.succ) := fun h => hpne h.1
            have n2 : ¬ (p.1 = i.castSucc ∧ t = i.castSucc) := fun h => ht2 h.2
            have n3 : ¬ (p.1 = i.succ ∧ t = i.castSucc) := fun h => ht2 h.2
            have c4 : p.1 = i.castSucc ∧ t = i.succ := ⟨hp2, ht1⟩
            have hterm : ∀ y : Reg n,
                (if p.1 = i.succ ∧ t = i.succ then (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
                  else if p.1 = i.castSucc ∧ t = i.castSucc then
                    (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
                  else if p.1 = i.succ ∧ t = i.castSucc then
                    -((1 / 2 : ℂ) * U i p.2 y * η (t, y))
                  else if p.1 = i.castSucc ∧ t = i.succ then
                    -((1 / 2 : ℂ) * star (U i y p.2) * η (t, y))
                  else 0) = -((1 / 2 : ℂ) * star (U i y p.2) * η (t, y)) := by
              intro y
              simp only [if_neg n1, if_neg n2, if_neg n3, if_pos c4]
            rw [Finset.sum_congr rfl (fun y _ => hterm y), if_neg ht2, if_pos ht1, ht1]
            rw [Finset.sum_neg_distrib]
            have hm : ∀ y : Reg n, (1 / 2 : ℂ) * star (U i y p.2) * η (i.succ, y)
                = (1 / 2 : ℂ) * (star (U i y p.2) * η (i.succ, y)) := by
              intro y; ring
            rw [Finset.sum_congr rfl (fun y _ => hm y), ← Finset.mul_sum]
          · have n1 : ¬ (p.1 = i.succ ∧ t = i.succ) := fun h => ht1 h.2
            have n2 : ¬ (p.1 = i.castSucc ∧ t = i.castSucc) := fun h => ht2 h.2
            have n3 : ¬ (p.1 = i.succ ∧ t = i.castSucc) := fun h => hpne h.1
            have n4 : ¬ (p.1 = i.castSucc ∧ t = i.succ) := fun h => ht1 h.2
            have hterm : ∀ y : Reg n,
                (if p.1 = i.succ ∧ t = i.succ then (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
                  else if p.1 = i.castSucc ∧ t = i.castSucc then
                    (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
                  else if p.1 = i.succ ∧ t = i.castSucc then
                    -((1 / 2 : ℂ) * U i p.2 y * η (t, y))
                  else if p.1 = i.castSucc ∧ t = i.succ then
                    -((1 / 2 : ℂ) * star (U i y p.2) * η (t, y))
                  else 0) = (0 : ℂ) := by
              intro y
              simp only [if_neg n1, if_neg n2, if_neg n3, if_neg n4]
            rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_const, smul_zero,
              if_neg ht1, if_neg ht2]
      rw [Finset.sum_congr rfl (fun t _ => hsumt t)]
      have hswap : (∑ t : Fin (m + 1),
            (if t = i.castSucc then (1 / 2 : ℂ) * η p
              else if t = i.succ then
                -((1 / 2 : ℂ) * ∑ y : Reg n, star (U i y p.2) * η (i.succ, y))
              else 0))
          = (1 / 2 : ℂ) * η p
              + -((1 / 2 : ℂ) * ∑ y : Reg n, star (U i y p.2) * η (i.succ, y)) := by
        rw [g13n_sum_two (fin_succ_ne_castSucc i).symm]
      rw [hswap]
      show (1 / 2 : ℂ) * η p + -((1 / 2 : ℂ) * ∑ y : Reg n, star (U i y p.2) * η (i.succ, y))
          = (1 / 2 : ℂ) * η p - (1 / 2 : ℂ) * (∑ y : Reg n, star (U i y p.2) * η (i.succ, y))
      ring
    · rw [if_neg hp1, if_neg hp2]
      have hsumt : ∀ t : Fin (m + 1),
          (∑ y : Reg n,
            (if p.1 = i.succ ∧ t = i.succ then (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
              else if p.1 = i.castSucc ∧ t = i.castSucc then
                (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
              else if p.1 = i.succ ∧ t = i.castSucc then
                -((1 / 2 : ℂ) * U i p.2 y * η (t, y))
              else if p.1 = i.castSucc ∧ t = i.succ then
                -((1 / 2 : ℂ) * star (U i y p.2) * η (t, y))
              else 0)) = (0 : ℂ) := by
        intro t
        have n1 : ¬ (p.1 = i.succ ∧ t = i.succ) := fun h => hp1 h.1
        have n2 : ¬ (p.1 = i.castSucc ∧ t = i.castSucc) := fun h => hp2 h.1
        have n3 : ¬ (p.1 = i.succ ∧ t = i.castSucc) := fun h => hp1 h.1
        have n4 : ¬ (p.1 = i.castSucc ∧ t = i.succ) := fun h => hp2 h.1
        have hterm : ∀ y : Reg n,
            (if p.1 = i.succ ∧ t = i.succ then (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
              else if p.1 = i.castSucc ∧ t = i.castSucc then
                (if p.2 = y then (1 / 2 : ℂ) * η (t, y) else 0)
              else if p.1 = i.succ ∧ t = i.castSucc then
                -((1 / 2 : ℂ) * U i p.2 y * η (t, y))
              else if p.1 = i.castSucc ∧ t = i.succ then
                -((1 / 2 : ℂ) * star (U i y p.2) * η (t, y))
              else 0) = (0 : ℂ) := by
          intro y
          simp only [if_neg n1, if_neg n2, if_neg n3, if_neg n4]
        rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_const, smul_zero]
      rw [Finset.sum_congr rfl (fun t _ => hsumt t), Finset.sum_const, smul_zero]

/-- The cross term formed with an adjoint matrix is the complex conjugate of the corresponding
forward cross term. -/
theorem g13n_conj_cross (n : ℕ) (U : Matrix (Reg n) (Reg n) ℂ) (a b : QState (Reg n)) :
    (∑ y : Reg n, star (b y) * (U ᴴ *ᵥ a) y)
      = star (∑ y : Reg n, star (a y) * (U *ᵥ b) y) := by
  have hA : (∑ y : Reg n, star (b y) * (U ᴴ *ᵥ a) y)
      = ∑ y : Reg n, ∑ z : Reg n, star (U z y) * star (b y) * a z := by
    apply Finset.sum_congr rfl
    intro y _
    have hy : (U ᴴ *ᵥ a) y = ∑ z : Reg n, star (U z y) * a z := by
      simp only [Matrix.mulVec, Matrix.conjTranspose_apply, dotProduct]
    rw [hy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  have hB : star (∑ y : Reg n, star (a y) * (U *ᵥ b) y)
      = ∑ y : Reg n, ∑ z : Reg n, star (U y z) * star (b z) * a y := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro y _
    have hy : (U *ᵥ b) y = ∑ z : Reg n, U y z * b z := by
      simp only [Matrix.mulVec, dotProduct]
    rw [hy, star_mul', star_star, star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [star_mul']
    ring
  rw [hA, hB, Finset.sum_comm]
  try rfl

/-- A propagation energy equals half the sum of adjacent slice squared norms minus the real
forward cross term. -/
theorem g13n_prop_energy (n m : ℕ) (U : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (i : Fin m) (η : QState (Fin (m + 1) × Reg n)) :
    qmaEnergy (qmaPropTerm n m U i) η
      = (1 / 2 : ℝ) * (vn (sl η i.succ) + vn (sl η i.castSucc))
        - (∑ y : Reg n, star (sl η i.succ y) * (U i *ᵥ sl η i.castSucc) y).re := by

  set S1 : ℂ := ∑ y : Reg n, (↑(‖η (i.succ, y)‖ ^ 2) : ℂ) with hS1
  set S2 : ℂ := ∑ y : Reg n, (↑(‖η (i.castSucc, y)‖ ^ 2) : ℂ) with hS2
  set w : ℂ := ∑ y : Reg n, star (η (i.succ, y)) * (U i *ᵥ sl η i.castSucc) y with hw
  set w' : ℂ := ∑ y : Reg n, star (η (i.castSucc, y)) * ((U i)ᴴ *ᵥ sl η i.succ) y with hw'
  have hw're : w'.re = w.re := by
    rw [hw', hw, g13n_conj_cross]
    exact Complex.conj_re _
  have hS1re : S1.re = vn (sl η i.succ) := by
    rw [hS1, Complex.re_sum]
    simp only [Complex.ofReal_re]
    unfold vn sl
    rfl
  have hS2re : S2.re = vn (sl η i.castSucc) := by
    rw [hS2, Complex.re_sum]
    simp only [Complex.ofReal_re]
    unfold vn sl
    rfl
  unfold qmaEnergy Qatlib.Foundations.PureStateMath.Inner dotProduct
  simp only [Pi.star_apply]
  have hpoint : ∀ p : Fin (m + 1) × Reg n,
      (qmaPropTerm n m U i *ᵥ η) p
        = if p.1 = i.succ then
            (1 / 2 : ℂ) * η p - (1 / 2 : ℂ) * (U i *ᵥ sl η i.castSucc) p.2
          else if p.1 = i.castSucc then
            (1 / 2 : ℂ) * η p - (1 / 2 : ℂ) * ((U i)ᴴ *ᵥ sl η i.succ) p.2
          else 0 :=
    fun p => g13n_prop_mulVec n m U i η p
  rw [Finset.sum_congr rfl (fun p _ => by rw [hpoint p])]
  classical
  rw [Fintype.sum_prod_type]

  have hsumt : ∀ t : Fin (m + 1),
      (∑ y : Reg n, star (η (t, y)) *
          (if t = i.succ then
            (1 / 2 : ℂ) * η (t, y) - (1 / 2 : ℂ) * (U i *ᵥ sl η i.castSucc) y
          else if t = i.castSucc then
            (1 / 2 : ℂ) * η (t, y) - (1 / 2 : ℂ) * ((U i)ᴴ *ᵥ sl η i.succ) y
          else 0))
      = if t = i.succ then ((1 / 2 : ℂ) * S1 - (1 / 2 : ℂ) * w)
        else if t = i.castSucc then ((1 / 2 : ℂ) * S2 - (1 / 2 : ℂ) * w')
        else 0 := by
    intro t
    by_cases ht1 : t = i.succ
    · have hterm : ∀ y : Reg n,
          (star (η (t, y)) *
            (if t = i.succ then
              (1 / 2 : ℂ) * η (t, y) - (1 / 2 : ℂ) * (U i *ᵥ sl η i.castSucc) y
            else if t = i.castSucc then
              (1 / 2 : ℂ) * η (t, y) - (1 / 2 : ℂ) * ((U i)ᴴ *ᵥ sl η i.succ) y
            else 0))
          = star (η (t, y)) *
              ((1 / 2 : ℂ) * η (t, y) - (1 / 2 : ℂ) * (U i *ᵥ sl η i.castSucc) y) := by
        intro y
        rw [if_pos ht1]
      rw [Finset.sum_congr rfl (fun y _ => hterm y), if_pos ht1]
      rw [Finset.sum_congr rfl (fun y _ => by rw [mul_sub]), Finset.sum_sub_distrib]
      have hA : (∑ y : Reg n, star (η (t, y)) * ((1 / 2 : ℂ) * η (t, y)))
          = (1 / 2 : ℂ) * S1 := by
        rw [ht1, hS1, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        have hmul : star (η (i.succ, y)) * ((1 / 2 : ℂ) * η (i.succ, y))
            = (1 / 2 : ℂ) * (star (η (i.succ, y)) * η (i.succ, y)) := by ring
        rw [hmul, star_mul_self]
      have hB : (∑ y : Reg n, star (η (t, y)) * ((1 / 2 : ℂ) * (U i *ᵥ sl η i.castSucc) y))
          = (1 / 2 : ℂ) * w := by
        rw [ht1, hw, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      rw [hA, hB]
    · by_cases ht2 : t = i.castSucc
      · have hterm : ∀ y : Reg n,
            (star (η (t, y)) *
              (if t = i.succ then
                (1 / 2 : ℂ) * η (t, y) - (1 / 2 : ℂ) * (U i *ᵥ sl η i.castSucc) y
              else if t = i.castSucc then
                (1 / 2 : ℂ) * η (t, y) - (1 / 2 : ℂ) * ((U i)ᴴ *ᵥ sl η i.succ) y
              else 0))
            = star (η (t, y)) *
                ((1 / 2 : ℂ) * η (t, y) - (1 / 2 : ℂ) * ((U i)ᴴ *ᵥ sl η i.succ) y) := by
          intro y
          rw [if_neg ht1, if_pos ht2]
        rw [Finset.sum_congr rfl (fun y _ => hterm y), if_neg ht1, if_pos ht2]
        rw [Finset.sum_congr rfl (fun y _ => by rw [mul_sub]), Finset.sum_sub_distrib]
        have hA : (∑ y : Reg n, star (η (t, y)) * ((1 / 2 : ℂ) * η (t, y)))
            = (1 / 2 : ℂ) * S2 := by
          rw [ht2, hS2, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          have hmul : star (η (i.castSucc, y)) * ((1 / 2 : ℂ) * η (i.castSucc, y))
              = (1 / 2 : ℂ) * (star (η (i.castSucc, y)) * η (i.castSucc, y)) := by ring
          rw [hmul, star_mul_self]
        have hB : (∑ y : Reg n, star (η (t, y)) * ((1 / 2 : ℂ) * ((U i)ᴴ *ᵥ sl η i.succ) y))
            = (1 / 2 : ℂ) * w' := by
          rw [ht2, hw', Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
        rw [hA, hB]
      · have hterm : ∀ y : Reg n,
            (star (η (t, y)) *
              (if t = i.succ then
                (1 / 2 : ℂ) * η (t, y) - (1 / 2 : ℂ) * (U i *ᵥ sl η i.castSucc) y
              else if t = i.castSucc then
                (1 / 2 : ℂ) * η (t, y) - (1 / 2 : ℂ) * ((U i)ᴴ *ᵥ sl η i.succ) y
              else 0)) = (0 : ℂ) := by
          intro y
          rw [if_neg ht1, if_neg ht2]
          ring
        rw [Finset.sum_congr rfl (fun y _ => hterm y), if_neg ht1, if_neg ht2,
          Finset.sum_const, smul_zero]
  rw [Finset.sum_congr rfl (fun t _ => hsumt t)]
  have hfold : (∑ t : Fin (m + 1),
        (if t = i.succ then ((1 / 2 : ℂ) * S1 - (1 / 2 : ℂ) * w)
        else if t = i.castSucc then ((1 / 2 : ℂ) * S2 - (1 / 2 : ℂ) * w')
        else 0)).re
      = (1 / 2 : ℝ) * (vn (sl η i.succ) + vn (sl η i.castSucc))
        - (∑ y : Reg n, star (sl η i.succ y) * (U i *ᵥ sl η i.castSucc) y).re := by
    rw [g13n_sum_two (fin_succ_ne_castSucc i)]
    rw [Complex.add_re, Complex.sub_re, Complex.sub_re]
    have hh : ∀ z : ℂ, ((1 / 2 : ℂ) * z).re = (1 / 2 : ℝ) * z.re := by
      intro z
      rw [Complex.mul_re]
      simp
    rw [hh, hh, hh, hh]
    rw [hS1re, hS2re, hw're, hw]
    simp only [sl]
    ring
  rw [hfold]

/-- The squared norm of a vector difference is the sum of squared norms minus twice the real
inner product. -/
theorem g13n_vn_sub {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    vn (fun y => a y - b y) = vn a + vn b - 2 * (∑ y, star (a y) * (b y)).re := by
  have h : ∀ y : ι, ‖a y - b y‖ ^ 2 = ‖a y‖ ^ 2 + ‖b y‖ ^ 2
        - 2 * (star (a y) * (b y)).re := by
    intro y
    have h1 : ‖a y - b y‖ ^ 2 = (star (a y - b y) * (a y - b y)).re := by
      rw [star_mul_self, Complex.ofReal_re]
    have h3 : (star (a y) * a y).re = ‖a y‖ ^ 2 := by
      rw [star_mul_self, Complex.ofReal_re]
    have h4 : (star (b y) * b y).re = ‖b y‖ ^ 2 := by
      rw [star_mul_self, Complex.ofReal_re]
    have h5 : (star (b y) * a y).re = (star (a y) * (b y)).re := by
      have key : star (b y) * a y = star (star (a y) * (b y)) := by
        rw [star_mul', star_star]
        ring
      rw [key]
      exact Complex.conj_re _
    rw [h1, star_sub]
    have h2 : (star (a y) - star (b y)) * (a y - b y)
        = star (a y) * a y - star (a y) * b y - star (b y) * a y + star (b y) * b y := by
      ring
    rw [h2]
    simp only [Complex.add_re, Complex.sub_re]
    rw [h3, h4, h5]
    ring
  have hs : (∑ y : ι, ‖a y - b y‖ ^ 2)
      = (∑ y : ι, (‖a y‖ ^ 2 + ‖b y‖ ^ 2 - 2 * (star (a y) * (b y)).re)) := by
    apply Finset.sum_congr rfl
    intro y _
    exact h y
  unfold vn
  rw [hs, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hm : (∑ y : ι, (2 : ℝ) * (star (a y) * (b y)).re)
      = 2 * (∑ y : ι, star (a y) * (b y)).re := by
    rw [← Finset.mul_sum, ← Complex.re_sum]
  rw [hm]

/-- A propagation energy is half the squared propagation residual plus half the change in
squared norm under the gate. -/
theorem g13n_prop_energy_residual (n m : ℕ) (U : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (i : Fin m) (η : QState (Fin (m + 1) × Reg n)) :
    qmaEnergy (qmaPropTerm n m U i) η
      = (1 / 2 : ℝ) * vn (fun y => sl η i.succ y - (U i *ᵥ sl η i.castSucc) y)
        + (1 / 2 : ℝ) * (vn (sl η i.castSucc) - vn (U i *ᵥ sl η i.castSucc)) := by
  rw [g13n_prop_energy, g13n_vn_sub]
  ring

/-- The history Hamiltonian energy splits into the sum of propagation energies, input energies,
and the output energy. -/
theorem g13n_energy_split (C : QmaHistoryCircuit)
    (U : Fin C.gates.length → Matrix (Reg C.qubits) (Reg C.qubits) ℂ)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) :
    qmaEnergy (qmaHistoryHamiltonian C U) η
      = (∑ i : Fin C.gates.length, qmaEnergy (qmaPropTerm C.qubits C.gates.length U i) η)
        + (∑ j ∈ C.initZeroWires, qmaEnergy (qmaInTerm C.qubits C.gates.length j) η)
        + qmaEnergy (qmaOutTerm C.qubits C.gates.length C.outputWire) η := by
  unfold qmaHistoryHamiltonian
  rw [qmaEnergy_foldr]
  unfold qmaHistoryTerms
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append]
  have hp : ((qmaHistoryPropTerms C U).map fun t => qmaEnergy t.matrix η).sum
      = ∑ i : Fin C.gates.length, qmaEnergy (qmaPropTerm C.qubits C.gates.length U i) η := by
    unfold qmaHistoryPropTerms
    rw [List.map_map]
    exact (Fin.sum_univ_def _).symm
  have hin : ((qmaHistoryInTerms C).map fun t => qmaEnergy t.matrix η).sum
      = ∑ j ∈ C.initZeroWires, qmaEnergy (qmaInTerm C.qubits C.gates.length j) η := by
    unfold qmaHistoryInTerms
    rw [List.map_map]
    exact Finset.sum_map_toList _ _
  have hout : ((qmaHistoryOutTerm C).map fun t => qmaEnergy t.matrix η).sum
      = qmaEnergy (qmaOutTerm C.qubits C.gates.length C.outputWire) η := by
    unfold qmaHistoryOutTerm
    simp
  rw [hp, hin, hout]

/-- The acceptance weight equals the squared amplitude mass of the exact final state on true
output bits. -/
theorem g13n_accept_eq (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits)) :
    qmaHistoryAcceptProb C φ
      = ∑ y : Reg C.qubits, if y C.outputWire then
          ‖(finiteWordMatrix C.qubits C.gates).mulVec φ y‖ ^ 2 else 0 := by
  rw [qmaHistoryAcceptProb_eq]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y C.outputWire <;> simp [hy, bornProb_eq_normSq]

/-- The output penalty energy is the total final-slice mass minus its accepting mass. -/
theorem g13n_out_energy_sub (n m : ℕ) (out : Fin n) (η : QState (Fin (m + 1) × Reg n)) :
    qmaEnergy (qmaOutTerm n m out) η
      = (∑ y : Reg n, ‖η (Fin.last m, y)‖ ^ 2)
        - (∑ y : Reg n, if y out then ‖η (Fin.last m, y)‖ ^ 2 else (0 : ℝ)) := by
  rw [g13n_out_energy]
  have h : (∑ y : Reg n, if y out then (0 : ℝ) else ‖η (Fin.last m, y)‖ ^ 2)
      = (∑ y : Reg n, ‖η (Fin.last m, y)‖ ^ 2)
        - (∑ y : Reg n, if y out then ‖η (Fin.last m, y)‖ ^ 2 else (0 : ℝ)) := by
    have h1 : (∑ y : Reg n, if y out then (0 : ℝ) else ‖η (Fin.last m, y)‖ ^ 2)
        + (∑ y : Reg n, if y out then ‖η (Fin.last m, y)‖ ^ 2 else (0 : ℝ))
        = ∑ y : Reg n, ‖η (Fin.last m, y)‖ ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y out <;> simp [hy]
    linarith
  rw [h]

/-- The squared norm of a vector sum is the sum of squared norms plus twice the real inner
product. -/
theorem g13n2_vn_add {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    vn (fun y => a y + b y) = vn a + vn b + 2 * (∑ y, star (a y) * (b y)).re := by
  have hpt : ∀ y : ι, ‖a y + b y‖ ^ 2 = ‖a y‖ ^ 2 + ‖b y‖ ^ 2
        + 2 * (star (a y) * (b y)).re := by
    intro y
    have h1 : ‖a y + b y‖ ^ 2 = (star (a y + b y) * (a y + b y)).re := by
      rw [star_mul_self, Complex.ofReal_re]
    have h3 : (star (a y) * a y).re = ‖a y‖ ^ 2 := by
      rw [star_mul_self, Complex.ofReal_re]
    have h4 : (star (b y) * b y).re = ‖b y‖ ^ 2 := by
      rw [star_mul_self, Complex.ofReal_re]
    rw [h1, star_add]
    have h2 : (star (a y) + star (b y)) * (a y + b y)
        = star (a y) * a y + star (a y) * b y + star (b y) * a y + star (b y) * b y := by
      ring
    rw [h2]
    simp only [Complex.add_re]
    have h5 : (star (b y) * a y).re = (star (a y) * (b y)).re := by
      have key : star (b y) * a y = star (star (a y) * (b y)) := by
        rw [star_mul', star_star]
        ring
      rw [key]
      exact Complex.conj_re _
    rw [h5, h3, h4]
    ring
  unfold vn
  have hs : (∑ y : ι, ‖a y + b y‖ ^ 2)
      = ∑ y : ι, (‖a y‖ ^ 2 + ‖b y‖ ^ 2 + 2 * (star (a y) * (b y)).re) := by
    apply Finset.sum_congr rfl
    intro y _
    exact hpt y
  rw [hs, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hm : (∑ y : ι, (2 : ℝ) * (star (a y) * (b y)).re)
      = 2 * (∑ y : ι, star (a y) * (b y)).re := by
    rw [← Finset.mul_sum, ← Complex.re_sum]
  rw [hm]

/-- The Euclidean norm `nm` satisfies the triangle inequality. -/
theorem g13n2_nm_add {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    nm (fun y => a y + b y) ≤ nm a + nm b := by
  have hre : (∑ y : ι, star (a y) * (b y)).re ≤ nm a * nm b := by
    have h := re_cinner_le a b
    simpa [nm, Real.sqrt_mul (vn_nonneg a)] using! h
  have hcross : (2 : ℝ) * (∑ y, star (a y) * (b y)).re ≤ 2 * (nm a * nm b) :=
    mul_le_mul_of_nonneg_left hre (by norm_num)
  have hvn : vn (fun y => a y + b y) ≤ (nm a + nm b) ^ 2 := by
    rw [g13n2_vn_add]
    have hsq : (nm a + nm b) ^ 2 = vn a + vn b + 2 * (nm a * nm b) := by
      rw [add_sq, nm_sq, nm_sq]
      ring
    rw [hsq]
    linarith
  have hnn : 0 ≤ nm a + nm b := add_nonneg (nm_nonneg a) (nm_nonneg b)
  calc nm (fun y => a y + b y) = Real.sqrt (vn (fun y => a y + b y)) := rfl
    _ ≤ Real.sqrt ((nm a + nm b) ^ 2) := Real.sqrt_le_sqrt hvn
    _ = nm a + nm b := Real.sqrt_sq hnn

/-- Scaling a vector by `c` multiplies its Euclidean norm by `‖c‖`. -/
theorem g13n2_nm_smul {ι : Type*} [Fintype ι] (c : ℂ) (v : ι → ℂ) :
    nm (fun y => c * v y) = ‖c‖ * nm v := by
  have h : vn (fun y => c * v y) = ‖c‖ ^ 2 * vn v := vn_smul c v
  unfold nm
  rw [h]
  have h1 : Real.sqrt (‖c‖ ^ 2 * vn v) = ‖c‖ * Real.sqrt (vn v) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]
  exact h1

/-- A matrix with entries bounded by nonnegative `δ` increases `nm` by at most the index
cardinality times `δ`. -/
theorem g13n2_entrywise_op {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (v : ι → ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hA : ∀ x y : ι, ‖A x y‖ ≤ δ) :
    nm (A *ᵥ v) ≤ (Fintype.card ι) * δ * nm v := by

  have hrow : ∀ y : ι, ‖(A *ᵥ v) y‖ ≤ δ * ∑ x : ι, ‖v x‖ := by
    intro y
    have h1 : (A *ᵥ v) y = ∑ x : ι, A y x * v x := by
      simp only [Matrix.mulVec, dotProduct]
    rw [h1]
    have h2 : ‖∑ x : ι, A y x * v x‖ ≤ ∑ x : ι, ‖A y x * v x‖ := norm_sum_le _ _
    have h3 : (∑ x : ι, ‖A y x * v x‖) = ∑ x : ι, ‖A y x‖ * ‖v x‖ := by
      apply Finset.sum_congr rfl
      intro x _
      exact norm_mul (A y x) (v x)
    rw [h3] at h2
    have h4 : (∑ x : ι, ‖A y x‖ * ‖v x‖) ≤ ∑ x : ι, δ * ‖v x‖ := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_right (hA y x) (norm_nonneg _)
    have h5 : (∑ x : ι, δ * ‖v x‖) = δ * ∑ x : ι, ‖v x‖ := (Finset.mul_sum _ _ _).symm
    linarith

  have h1sum : (∑ x : ι, ‖v x‖) ^ 2 ≤ Fintype.card ι * vn v := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : ι => (1 : ℝ)) (fun x : ι => ‖v x‖)
    have h1 : (∑ x : ι, (1 : ℝ) * ‖v x‖) ^ 2
        ≤ (∑ x : ι, (1 : ℝ) ^ 2) * (∑ x : ι, ‖v x‖ ^ 2) := by
      simpa using! h
    have h2 : (∑ x : ι, (1 : ℝ) * ‖v x‖) = ∑ x : ι, ‖v x‖ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [one_mul]
    have h3 : (∑ x : ι, (1 : ℝ) ^ 2) = Fintype.card ι := by
      simp
    rw [h2, h3] at h1
    exact h1
  have h1nn : 0 ≤ ∑ x : ι, ‖v x‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h1 : ∑ x : ι, ‖v x‖ ≤ Real.sqrt (Fintype.card ι) * nm v := by
    have := (Real.le_sqrt h1nn (mul_nonneg (Nat.cast_nonneg _) (vn_nonneg v))).mpr h1sum
    rw [Real.sqrt_mul (Nat.cast_nonneg _)] at this
    simpa [nm] using! this

  have hvn : vn (A *ᵥ v) ≤ (Fintype.card ι) * δ ^ 2 * (∑ x : ι, ‖v x‖) ^ 2 := by
    unfold vn
    have hle : ∀ y : ι, ‖(A *ᵥ v) y‖ ^ 2 ≤ (δ * ∑ x : ι, ‖v x‖) ^ 2 := by
      intro y
      exact pow_le_pow_left₀ (norm_nonneg _) (hrow y) 2
    calc (∑ y : ι, ‖(A *ᵥ v) y‖ ^ 2)
          ≤ ∑ y : ι, (δ * ∑ x : ι, ‖v x‖) ^ 2 := Finset.sum_le_sum (fun y _ => hle y)
      _ = (Fintype.card ι) * (δ * ∑ x : ι, ‖v x‖) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card ι) * δ ^ 2 * (∑ x : ι, ‖v x‖) ^ 2 := by ring
  have htot : vn (A *ᵥ v) ≤ (Fintype.card ι) ^ 2 * δ ^ 2 * vn v := by
    have hsq1 : (∑ x : ι, ‖v x‖) ^ 2 ≤ (Real.sqrt (Fintype.card ι) * nm v) ^ 2 :=
      pow_le_pow_left₀ h1nn h1 2
    have h2 : (Fintype.card ι) * δ ^ 2 * (∑ x : ι, ‖v x‖) ^ 2
        ≤ (Fintype.card ι) * δ ^ 2 * ((Real.sqrt (Fintype.card ι) * nm v) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq1 (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    have h3 : (Fintype.card ι) * δ ^ 2 * ((Real.sqrt (Fintype.card ι) * nm v) ^ 2)
        = (Fintype.card ι) ^ 2 * δ ^ 2 * vn v := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), nm_sq]
      ring
    linarith
  have hnn : 0 ≤ (Fintype.card ι) * δ * nm v :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ) (nm_nonneg v)
  have hnn2 : 0 ≤ (Fintype.card ι) * δ :=
    mul_nonneg (Nat.cast_nonneg _) hδ
  unfold nm at *
  calc Real.sqrt (vn (A *ᵥ v))
        ≤ Real.sqrt ((Fintype.card ι) ^ 2 * δ ^ 2 * vn v) := Real.sqrt_le_sqrt htot
    _ = Real.sqrt (((Fintype.card ι) * δ) ^ 2 * vn v) := by
        congr 1
        ring
    _ = Real.sqrt (((Fintype.card ι) * δ) ^ 2) * Real.sqrt (vn v) := by
        rw [Real.sqrt_mul (sq_nonneg _)]
    _ = (Fintype.card ι) * δ * Real.sqrt (vn v) := by
        rw [Real.sqrt_sq hnn2]

/-- A unitary matrix preserves the squared coordinate norm `vn`. -/
theorem g13n2_unitary_vn {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) : vn (U *ᵥ v) = vn v := by
  have h := sum_normSq_mulVec_of_mem_unitaryGroup hU v
  have h2 : ∀ w : ι → ℂ, (∑ i, Complex.normSq (w i)) = vn w := by
    intro w
    unfold vn
    apply Finset.sum_congr rfl
    intro i _
    exact Complex.normSq_eq_norm_sq (w i)
  rw [← h2, ← h2]
  exact h

/-- A unitary matrix preserves the Euclidean norm `nm`. -/
theorem g13n2_unitary_nm {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) : nm (U *ᵥ v) = nm v := by
  unfold nm
  rw [g13n2_unitary_vn hU v]

/-- Each rounded gate entry differs from the exact entry by norm at most `2⁻ᵇ`. -/
theorem g13n2_round_gate_entry {n b : ℕ} (g : FiniteGateCode) (x y : Reg n) :
    ‖qmaRoundedGate n b g x y - finiteCodeMatrix n g x y‖ ≤ 1 / (2 : ℝ) ^ b := by
  have h : qmaRoundedGate n b g x y = qmaRoundC b (finiteCodeMatrix n g x y) := rfl
  rw [h]
  exact g13n_roundC_dist b (finiteCodeMatrix n g x y)

/-- The action of `A` splits as the action of `B` plus the action of `A - B`. -/
theorem g13n2_split_mulVec {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    A *ᵥ v = fun y => (B *ᵥ v) y + ((A - B) *ᵥ v) y := by
  have h1 : (B + (A - B) : Matrix ι ι ℂ) = A := add_sub_cancel B A
  have h2 : ((B + (A - B) : Matrix ι ι ℂ) *ᵥ v) = A *ᵥ v := by rw [h1]
  rw [Matrix.add_mulVec] at h2
  funext y
  exact (congrFun h2 y).symm

/-- The rounding error scale equal to the register cardinality times `2⁻ᵇ`. -/
noncomputable def g13n2_kappa (n b : ℕ) : ℝ :=
  (Fintype.card (Reg n)) * (1 / (2 : ℝ) ^ b)

/-- The rounding error scale `g13n2_kappa n b` is nonnegative. -/
theorem g13n2_kappa_nonneg (n b : ℕ) : 0 ≤ g13n2_kappa n b := by
  unfold g13n2_kappa
  exact mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- The difference between rounded and exact gate actions has norm at most `g13n2_kappa n b * nm
v`. -/
theorem g13n2_round_gate_vec (n b : ℕ) (g : FiniteGateCode) (v : QState (Reg n)) :
    nm ((qmaRoundedGate n b g - finiteCodeMatrix n g) *ᵥ v)
      ≤ g13n2_kappa n b * nm v := by
  have hentry : ∀ x y : Reg n,
      ‖(qmaRoundedGate n b g - finiteCodeMatrix n g) x y‖ ≤ 1 / (2 : ℝ) ^ b := by
    intro x y
    rw [Matrix.sub_apply]
    exact g13n2_round_gate_entry g x y
  have h := g13n2_entrywise_op (qmaRoundedGate n b g - finiteCodeMatrix n g) v
    (1 / (2 : ℝ) ^ b) (by positivity) hentry
  unfold g13n2_kappa at *
  linarith

/-- A rounded legal gate increases vector norm by a factor at most `1 + g13n2_kappa n b`. -/
theorem g13n2_round_gate_action (n b : ℕ) (g : FiniteGateCode)
    (hg : finiteCodeLegal n g = true) (v : QState (Reg n)) :
    nm (qmaRoundedGate n b g *ᵥ v) ≤ (1 + g13n2_kappa n b) * nm v := by
  have hE : finiteCodeMatrix n g ∈ Matrix.unitaryGroup (Reg n) ℂ :=
    finiteCodeMatrix_unitary n g hg
  have hsplit : qmaRoundedGate n b g *ᵥ v
      = fun y => (finiteCodeMatrix n g *ᵥ v) y
          + ((qmaRoundedGate n b g - finiteCodeMatrix n g) *ᵥ v) y :=
    g13n2_split_mulVec (qmaRoundedGate n b g) (finiteCodeMatrix n g) v
  rw [hsplit]
  have htri := g13n2_nm_add (finiteCodeMatrix n g *ᵥ v)
    ((qmaRoundedGate n b g - finiteCodeMatrix n g) *ᵥ v)
  have hU := g13n2_unitary_nm hE v
  have hD : nm ((qmaRoundedGate n b g - finiteCodeMatrix n g) *ᵥ v)
      ≤ g13n2_kappa n b * nm v := g13n2_round_gate_vec n b g v
  have h1 : nm (fun y => (finiteCodeMatrix n g *ᵥ v) y
      + ((qmaRoundedGate n b g - finiteCodeMatrix n g) *ᵥ v) y)
      ≤ (1 + g13n2_kappa n b) * nm v := by
    calc nm (fun y => (finiteCodeMatrix n g *ᵥ v) y
          + ((qmaRoundedGate n b g - finiteCodeMatrix n g) *ᵥ v) y)
          ≤ nm (finiteCodeMatrix n g *ᵥ v)
            + nm ((qmaRoundedGate n b g - finiteCodeMatrix n g) *ᵥ v) := htri
      _ = nm v + nm ((qmaRoundedGate n b g - finiteCodeMatrix n g) *ᵥ v) := by rw [hU]
      _ ≤ nm v + g13n2_kappa n b * nm v := add_le_add (le_refl (nm v)) hD
      _ = (1 + g13n2_kappa n b) * nm v := by ring
  exact h1

/-- A rounded legal gate increases squared vector norm by a factor at most `(1 + g13n2_kappa n
b)^2`. -/
theorem g13n2_round_gate_vn (n b : ℕ) (g : FiniteGateCode)
    (hg : finiteCodeLegal n g = true) (v : QState (Reg n)) :
    vn (qmaRoundedGate n b g *ᵥ v) ≤ (1 + g13n2_kappa n b) ^ 2 * vn v := by
  have h := g13n2_round_gate_action n b g hg v
  have hnn : 0 ≤ 1 + g13n2_kappa n b := by
    have := g13n2_kappa_nonneg n b
    linarith
  have h2 : vn (qmaRoundedGate n b g *ᵥ v) ≤ ((1 + g13n2_kappa n b) * nm v) ^ 2 := by
    rw [← nm_sq]
    exact pow_le_pow_left₀ (nm_nonneg _) h 2
  rw [mul_pow, nm_sq] at h2
  exact h2

/-- The squared norm of a clock slice is the sum of squared joint-state amplitudes at that clock
position. -/
theorem g13n2_sl_vn {n m : ℕ} (η : QState (Fin (m + 1) × Reg n)) (t : Fin (m + 1)) :
    vn (sl η t) = ∑ y : Reg n, ‖η (t, y)‖ ^ 2 := by
  unfold vn sl
  rfl

/-- The squared norms of all clock slices of a normalized joint state sum to one. -/
theorem g13n2_sum_sl_vn {n m : ℕ} {η : QState (Fin (m + 1) × Reg n)} (hη : Normalized η) :
    ∑ t : Fin (m + 1), vn (sl η t) = 1 := by
  unfold Normalized at hη
  rw [Fintype.sum_prod_type] at hη
  have h : (∑ x : Fin (m + 1), ∑ y : Reg n, ‖η (x, y)‖ ^ 2)
      = ∑ t : Fin (m + 1), vn (sl η t) := by
    apply Finset.sum_congr rfl
    intro t _
    exact (g13n2_sl_vn η t).symm
  rw [← h]
  exact hη

/-- At an in-range position, `qmaGateAt` equals list indexing. -/
theorem g13n2_qmaGateAt_eq (gs : List FiniteGateCode) {t : ℕ} (ht : t < gs.length) :
    qmaGateAt gs t = gs[t] := by
  unfold qmaGateAt
  have hdrop : gs.drop t = gs[t] :: gs.drop (t + 1) := List.drop_eq_getElem_cons ht
  rw [hdrop]

/-- Every in-range gate of a legal finite gate word is legal. -/
theorem g13n2_gateAt_legal {n : ℕ} {gs : List FiniteGateCode}
    (h : finiteWordLegal n gs = true) {t : ℕ} (ht : t < gs.length) :
    finiteCodeLegal n (qmaGateAt gs t) = true := by
  rw [g13n2_qmaGateAt_eq gs ht]
  exact List.all_eq_true.mp h _ (List.get_mem _ _)

/-- Every in-range gate of a history circuit is legal on its work register. -/
theorem g13n2_hist_gateAt_legal (C : QmaHistoryCircuit) {t : ℕ} (ht : t < C.gates.length) :
    finiteCodeLegal C.qubits (qmaGateAt C.gates t) = true :=
  g13n2_gateAt_legal C.legal ht

/-- Every exact gate matrix of a history circuit is unitary. -/
theorem g13n2_exactGate_unitary (C : QmaHistoryCircuit) (i : Fin C.gates.length) :
    qmaExactGates C i ∈ Matrix.unitaryGroup (Reg C.qubits) ℂ := by
  unfold qmaExactGates
  exact finiteCodeMatrix_unitary C.qubits (qmaGateAt C.gates i.val)
    (g13n2_hist_gateAt_legal C i.isLt)

/-- For a normalized joint state, a uniform squared-norm growth bound yields a propagation
energy lower bound by half the total squared residual minus `κ + κ² / 2`. -/
theorem g13n2_prop_lower (n m : ℕ) (U : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (η : QState (Fin (m + 1) × Reg n)) (hη : Normalized η) (κ : ℝ) (hκ : 0 ≤ κ)
    (hU : ∀ i : Fin m, vn (U i *ᵥ sl η i.castSucc) ≤ (1 + κ) ^ 2 * vn (sl η i.castSucc)) :
    (1 / 2 : ℝ) * (∑ i : Fin m, vn (fun y => sl η i.succ y - (U i *ᵥ sl η i.castSucc) y))
        - (κ + κ ^ 2 / 2)
      ≤ ∑ i : Fin m, qmaEnergy (qmaPropTerm n m U i) η := by
  have hres : ∀ i : Fin m, qmaEnergy (qmaPropTerm n m U i) η
      = (1 / 2 : ℝ) * vn (fun y => sl η i.succ y - (U i *ᵥ sl η i.castSucc) y)
        + (1 / 2 : ℝ) * (vn (sl η i.castSucc) - vn (U i *ᵥ sl η i.castSucc)) :=
    fun i => g13n_prop_energy_residual n m U i η
  have hstep : ∑ i : Fin m, qmaEnergy (qmaPropTerm n m U i) η
      = (1 / 2 : ℝ) * ∑ i : Fin m, vn (fun y => sl η i.succ y - (U i *ᵥ sl η i.castSucc) y)
        + (1 / 2 : ℝ) * ∑ i : Fin m, (vn (sl η i.castSucc) - vn (U i *ᵥ sl η i.castSucc)) := by
    rw [Finset.sum_congr rfl (fun i _ => hres i)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hT : (1 / 2 : ℝ) * ∑ i : Fin m, (vn (sl η i.castSucc) - vn (U i *ᵥ sl η i.castSucc))
      ≥ - (κ + κ ^ 2 / 2) := by
    have hle : ∀ i : Fin m, (vn (sl η i.castSucc) - vn (U i *ᵥ sl η i.castSucc))
        ≥ -((1 + κ) ^ 2 - 1) * vn (sl η i.castSucc) := by
      intro i
      have hU' := hU i
      have hnn : 0 ≤ vn (sl η i.castSucc) := vn_nonneg _
      nlinarith
    have hsum : ∑ i : Fin m, (vn (sl η i.castSucc) - vn (U i *ᵥ sl η i.castSucc))
        ≥ -((1 + κ) ^ 2 - 1) * ∑ i : Fin m, vn (sl η i.castSucc) := by
      have h1 : ∑ i : Fin m, (vn (sl η i.castSucc) - vn (U i *ᵥ sl η i.castSucc))
          ≥ ∑ i : Fin m, (-((1 + κ) ^ 2 - 1) * vn (sl η i.castSucc)) :=
        Finset.sum_le_sum (fun i _ => hle i)
      have h2 : (∑ i : Fin m, (-((1 + κ) ^ 2 - 1) * vn (sl η i.castSucc)))
          = -((1 + κ) ^ 2 - 1) * ∑ i : Fin m, vn (sl η i.castSucc) :=
        (Finset.mul_sum _ _ _).symm
      linarith
    have hS : ∑ i : Fin m, vn (sl η i.castSucc) ≤ 1 := by
      have hcast := Fin.sum_univ_castSucc (fun t : Fin (m + 1) => vn (sl η t))
      have htot := g13n2_sum_sl_vn hη
      have hnn : 0 ≤ vn (sl η (Fin.last m)) := vn_nonneg _
      linarith
    have hκ1 : 0 ≤ (1 + κ) ^ 2 - 1 := by nlinarith
    nlinarith
  have hR : 0 ≤ ∑ i : Fin m, vn (fun y => sl η i.succ y - (U i *ᵥ sl η i.castSucc) y) :=
    Finset.sum_nonneg (fun i _ => vn_nonneg _)
  nlinarith [hstep, hT, hR]

/-- The rounded propagation energy of a normalized state is bounded below by half the total
squared residual minus the prescribed `g13n2_kappa` correction. -/
theorem g13n2_prop_lower_C (C : QmaHistoryCircuit) (η : QState (Fin (C.gates.length + 1) × Reg C.qubits))
    (hη : Normalized η) (b : ℕ) :
    (1 / 2 : ℝ) *
        (∑ i : Fin C.gates.length,
          vn (fun y => sl η i.succ y - (qmaRoundedGates C b i *ᵥ sl η i.castSucc) y))
        - (g13n2_kappa C.qubits b + g13n2_kappa C.qubits b ^ 2 / 2)
      ≤ ∑ i : Fin C.gates.length,
          qmaEnergy (qmaPropTerm C.qubits C.gates.length (qmaRoundedGates C b) i) η := by
  have hκ : 0 ≤ g13n2_kappa C.qubits b := g13n2_kappa_nonneg _ _
  have hU : ∀ i : Fin C.gates.length,
      vn (qmaRoundedGates C b i *ᵥ sl η i.castSucc)
        ≤ (1 + g13n2_kappa C.qubits b) ^ 2 * vn (sl η i.castSucc) := by
    intro i
    have hg : finiteCodeLegal C.qubits (qmaGateAt C.gates i.val) = true :=
      g13n2_hist_gateAt_legal C i.isLt
    have h := g13n2_round_gate_vn C.qubits b (qmaGateAt C.gates i.val) hg (sl η i.castSucc)
    simpa [qmaRoundedGates] using! h
  exact g13n2_prop_lower C.qubits C.gates.length (qmaRoundedGates C b) η hη
    (g13n2_kappa C.qubits b) hκ hU
set_option autoImplicit false
open Matrix
open scoped BigOperators
set_option maxHeartbeats 800000

/-- Under the stated scale, normalization, and small-error assumptions, the combined residual
and boundary expression is at least `(1 - 2 * ρ²) / (2^10 * ν^6)` when both individual
contributions lie below that threshold. -/
theorem g2c2_scale_core (ν ρ u d β s κ : ℝ)
    (hν : 1 ≤ ν) (hρ : 0 ≤ ρ) (hρ2 : ρ ^ 2 ≤ 1 / 2)
    (hu : 0 ≤ u) (hβ0 : 0 ≤ β) (hs0 : 0 ≤ s) (hκ0 : 0 ≤ κ)
    (hd : d ≤ ν * (u + κ))
    (hs : 1 ≤ ν ^ 2 * (s + ν * (u + κ)) ^ 2)
    (hκ : κ ≤ 1 / (2 ^ 10 * ν ^ 6))
    (hbranch : (1 / 2) * u ^ 2 < (1 - 2 * ρ ^ 2) / (2 ^ 10 * ν ^ 6)
        ∧ β ^ 2 < (1 - 2 * ρ ^ 2) / (2 ^ 10 * ν ^ 6)) :
    (1 - 2 * ρ ^ 2) / (2 ^ 10 * ν ^ 6)
      ≤ (1 / 2) * u ^ 2 + (s - d) ^ 2 - (ρ * s + β + d) ^ 2 + β ^ 2 := by
  have hνpos : 0 < ν := lt_of_lt_of_le (by norm_num) hν
  have hden6 : 0 < (2 : ℝ) ^ 10 * ν ^ 6 := by positivity
  have hden2 : 0 < (2 : ℝ) ^ 10 * ν ^ 2 := by positivity
  have hν2 : (1 : ℝ) ≤ ν ^ 2 := by
    have := pow_le_pow_right₀ hν (show (0:ℕ) ≤ 2 by norm_num)
    rwa [pow_zero] at this
  have hν4 : (1 : ℝ) ≤ ν ^ 4 := by
    have := pow_le_pow_right₀ hν (show (0:ℕ) ≤ 4 by norm_num)
    rwa [pow_zero] at this
  have hν26 : ν ^ 2 ≤ ν ^ 6 := pow_le_pow_right₀ hν (by norm_num)
  have h10 : (2 : ℝ) ^ 10 = 1024 := by norm_num
  have hρle : ρ ≤ 3 / 4 := by nlinarith [hρ2, sq_nonneg (ρ - 3 / 4)]

  have hTle : (1 - 2 * ρ ^ 2) / (2 ^ 10 * ν ^ 6) ≤ 1 / (2 ^ 10 * ν ^ 6) := by
    have h1 : 1 - 2 * ρ ^ 2 ≤ 1 := by nlinarith
    exact div_le_div_of_nonneg_right h1 (le_of_lt hden6)

  have huc : u ^ 2 * (2 ^ 10 * ν ^ 6) ≤ 2 := by
    have h1 : u ^ 2 < 2 * ((1 - 2 * ρ ^ 2) / (2 ^ 10 * ν ^ 6)) := by nlinarith [hbranch.1]
    rw [← mul_div_assoc] at h1
    have h2 : u ^ 2 * (2 ^ 10 * ν ^ 6) < 2 * (1 - 2 * ρ ^ 2) :=
      (lt_div_iff₀ hden6).mp h1
    nlinarith
  have hβc : β ^ 2 * (2 ^ 10 * ν ^ 6) ≤ 1 := by
    have h1 : β ^ 2 < (1 - 2 * ρ ^ 2) / (2 ^ 10 * ν ^ 6) := hbranch.2
    have h2 : β ^ 2 * (2 ^ 10 * ν ^ 6) < 1 - 2 * ρ ^ 2 :=
      (lt_div_iff₀ hden6).mp h1
    nlinarith
  have hκc : κ * (2 ^ 10 * ν ^ 6) ≤ 1 := (le_div_iff₀ hden6).mp hκ
  have hκle : κ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ 2 ^ 10 * ν ^ 6 := by
      rw [h10]
      nlinarith [hν2, hν26]
    have h2 : κ * 1 ≤ κ * (2 ^ 10 * ν ^ 6) :=
      mul_le_mul_of_nonneg_left h1 hκ0
    nlinarith

  have hk2 : κ ^ 2 * (2 ^ 10 * ν ^ 6) ≤ 1 := by
    have h4 : κ ^ 2 * (2 ^ 10 * ν ^ 6) = κ * (κ * (2 ^ 10 * ν ^ 6)) := by ring
    rw [h4]
    have h5 : κ * (κ * (2 ^ 10 * ν ^ 6)) ≤ κ * 1 :=
      mul_le_mul_of_nonneg_left hκc hκ0
    nlinarith
  have htc : (u + κ) ^ 2 * (2 ^ 10 * ν ^ 6) ≤ 6 := by
    have h1 : (u + κ) ^ 2 ≤ 2 * u ^ 2 + 2 * κ ^ 2 := by nlinarith [sq_nonneg (u - κ)]
    have h2 : (u + κ) ^ 2 * (2 ^ 10 * ν ^ 6)
        ≤ (2 * u ^ 2 + 2 * κ ^ 2) * (2 ^ 10 * ν ^ 6) :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hden6)
    have h3 : (2 * u ^ 2 + 2 * κ ^ 2) * (2 ^ 10 * ν ^ 6)
        = 2 * (u ^ 2 * (2 ^ 10 * ν ^ 6)) + 2 * (κ ^ 2 * (2 ^ 10 * ν ^ 6)) := by ring
    rw [h3] at h2
    nlinarith [huc, hk2]

  have hx : (ν ^ 2 * (u + κ)) ^ 2 * (2 ^ 10 * ν ^ 2) ≤ 6 := by
    have h1 : (ν ^ 2 * (u + κ)) ^ 2 * (2 ^ 10 * ν ^ 2)
        = (u + κ) ^ 2 * (2 ^ 10 * ν ^ 6) := by ring
    rw [h1]
    exact htc
  have hx144 : (ν ^ 2 * (u + κ)) ^ 2 * 144 ≤ 1 := by
    have key : (ν ^ 2 * (u + κ)) ^ 2 * 144 * (2 ^ 10 * ν ^ 2)
        ≤ 1 * (2 ^ 10 * ν ^ 2) := by
      have h2 : (ν ^ 2 * (u + κ)) ^ 2 * 144 * (2 ^ 10 * ν ^ 2)
          = 144 * ((ν ^ 2 * (u + κ)) ^ 2 * (2 ^ 10 * ν ^ 2)) := by ring
      rw [h2]
      have h3 : 144 * ((ν ^ 2 * (u + κ)) ^ 2 * (2 ^ 10 * ν ^ 2)) ≤ 144 * 6 :=
        mul_le_mul_of_nonneg_left hx (by norm_num)
      have h4 : (144 : ℝ) * 6 ≤ 2 ^ 10 * ν ^ 2 := by
        rw [h10]
        nlinarith [hν2]
      linarith
    exact le_of_mul_le_mul_right key hden2
  have hY : ν ^ 2 * (u + κ) ≤ 1 / 12 := by
    have h1 : 0 ≤ ν ^ 2 * (u + κ) := by positivity
    have h2 : (ν ^ 2 * (u + κ) * 12) ^ 2 = (ν ^ 2 * (u + κ)) ^ 2 * 144 := by ring
    have h3 : (ν ^ 2 * (u + κ) * 12) ^ 2 ≤ (1 : ℝ) ^ 2 := by
      rw [h2, one_pow]
      exact hx144
    have h4 : ν ^ 2 * (u + κ) * 12 ≤ 1 := le_of_sq_le_sq h3 (by norm_num)
    nlinarith

  have hxsum : 1 ≤ (ν * s + ν ^ 2 * (u + κ)) ^ 2 := by
    have h1 : ν ^ 2 * (s + ν * (u + κ)) ^ 2 = (ν * s + ν ^ 2 * (u + κ)) ^ 2 := by ring
    rw [h1] at hs
    exact hs
  have hsum : 1 ≤ ν * s + ν ^ 2 * (u + κ) := by
    have h1 : (1 : ℝ) ≤ |ν * s + ν ^ 2 * (u + κ)| :=
      (one_le_sq_iff_one_le_abs _).mp hxsum
    rw [le_abs] at h1
    cases h1 with
    | inl h => exact h
    | inr h => nlinarith
  have hνs : 11 / 12 ≤ ν * s := by nlinarith [hY, hsum]

  have hD : ν * d ≤ 1 / 12 := by
    have h1 := mul_le_mul_of_nonneg_left hd (le_of_lt hνpos)
    have h2 : ν * (ν * (u + κ)) = ν ^ 2 * (u + κ) := by ring
    rw [h2] at h1
    nlinarith [hY, h1]
  have hB : ν * β ≤ 1 / 32 := by
    have h1 : (ν * β) ^ 2 * (2 ^ 10 * ν ^ 4) ≤ 1 := by
      have h2 : (ν * β) ^ 2 * (2 ^ 10 * ν ^ 4) = β ^ 2 * (2 ^ 10 * ν ^ 6) := by ring
      rw [h2]
      exact hβc
    rw [h10] at h1
    have h2 : (1024 : ℝ) ≤ 1024 * ν ^ 4 := by nlinarith [hν4]
    have h3 : 0 ≤ (ν * β) ^ 2 := sq_nonneg _
    have h4 : (ν * β) ^ 2 * 1024 ≤ (ν * β) ^ 2 * (1024 * ν ^ 4) :=
      mul_le_mul_of_nonneg_left h2 h3
    have h5 : (ν * β) ^ 2 * 1024 ≤ 1 := by linarith
    have h6 : (ν * β) ^ 2 ≤ 1 / 1024 := by nlinarith
    have h7 : ((1:ℝ) / 32) ^ 2 = 1 / 1024 := by norm_num
    have h8 : (ν * β) ^ 2 ≤ ((1:ℝ) / 32) ^ 2 := by
      rw [h7]
      exact h6
    have h9 : 0 ≤ ν * β := by positivity
    exact le_of_sq_le_sq h8 (by norm_num)

  have hρ1 : (1 / 4 : ℝ) ≤ 1 - ρ := by nlinarith
  have hA : (1 / 32 : ℝ) ≤ ν * s * (1 - ρ) - ν * β - 2 * (ν * d) := by
    have h1 : (11 / 48 : ℝ) ≤ ν * s * (1 - ρ) := by
      have := mul_le_mul hνs hρ1 (by norm_num) (by nlinarith [hνs])
      have h2 : (11 / 12 : ℝ) * (1 / 4) = 11 / 48 := by norm_num
      rw [h2] at this
      exact this
    nlinarith
  have hB1 : (11 / 12 : ℝ) ≤ ν * s * (1 + ρ) + ν * β := by
    have h1 : 0 ≤ (ν * s) * ρ := mul_nonneg (by nlinarith [hνs]) hρ
    nlinarith [hνs]
  have hprod : (11 / 384 : ℝ)
      ≤ (ν * s * (1 - ρ) - ν * β - 2 * (ν * d)) * (ν * s * (1 + ρ) + ν * β) := by
    have h1 := mul_le_mul hA hB1 (by norm_num) (by nlinarith [hA])
    have h2 : (1 / 32 : ℝ) * (11 / 12) = 11 / 384 := by norm_num
    rw [h2] at h1
    exact h1
  have hfact : (s - d) ^ 2 - (ρ * s + β + d) ^ 2
      = (s * (1 - ρ) - β - 2 * d) * (s * (1 + ρ) + β) := by
    rw [sq_sub_sq]
    ring_nf
  have hprod2 : (11 / 384 : ℝ)
      ≤ ν ^ 2 * ((s * (1 - ρ) - β - 2 * d) * (s * (1 + ρ) + β)) := by
    have h1 : ν ^ 2 * ((s * (1 - ρ) - β - 2 * d) * (s * (1 + ρ) + β))
        = (ν * s * (1 - ρ) - ν * β - 2 * (ν * d)) * (ν * s * (1 + ρ) + ν * β) := by
      ring_nf
    rw [h1]
    exact hprod
  have hmain : (11 / (384 * ν ^ 2) : ℝ)
      ≤ (s * (1 - ρ) - β - 2 * d) * (s * (1 + ρ) + β) := by
    have h1 : 0 < ν ^ 2 := pow_pos hνpos 2
    have h4 : (ν ^ 2 * ((s * (1 - ρ) - β - 2 * d) * (s * (1 + ρ) + β))) / ν ^ 2
        = (s * (1 - ρ) - β - 2 * d) * (s * (1 + ρ) + β) := by
      have h4a : (ν ^ 2 * ((s * (1 - ρ) - β - 2 * d) * (s * (1 + ρ) + β)))
          = ((s * (1 - ρ) - β - 2 * d) * (s * (1 + ρ) + β)) * ν ^ 2 := by ring
      rw [h4a, mul_div_cancel_right₀ _ (ne_of_gt h1)]
    have h3 : ((11 / 384 : ℝ) / ν ^ 2)
        ≤ ((ν ^ 2 * ((s * (1 - ρ) - β - 2 * d) * (s * (1 + ρ) + β))) / ν ^ 2) :=
      div_le_div_of_nonneg_right hprod2 (le_of_lt h1)
    rw [h4] at h3
    have h5 : ((11:ℝ) / 384) / ν ^ 2 = 11 / (384 * ν ^ 2) := by
      rw [div_div]
    rw [h5] at h3
    exact h3
  have hExpr : (s * (1 - ρ) - β - 2 * d) * (s * (1 + ρ) + β)
      ≤ (1 / 2) * u ^ 2 + (s - d) ^ 2 - (ρ * s + β + d) ^ 2 + β ^ 2 := by
    have hrearr : (1 / 2 : ℝ) * u ^ 2 + (s - d) ^ 2 - (ρ * s + β + d) ^ 2 + β ^ 2
        = (1 / 2) * u ^ 2 + ((s - d) ^ 2 - (ρ * s + β + d) ^ 2) + β ^ 2 := by ring
    rw [hrearr, hfact]
    have hpos : 0 ≤ (1 / 2) * u ^ 2 + β ^ 2 := by positivity
    linarith
  have hExpr' : (11 / (384 * ν ^ 2) : ℝ)
      ≤ (1 / 2) * u ^ 2 + (s - d) ^ 2 - (ρ * s + β + d) ^ 2 + β ^ 2 :=
    le_trans hmain hExpr
  have hident : (11 / (384 * ν ^ 2) : ℝ) * (2 ^ 10 * ν ^ 6) = 11 * 2 ^ 10 * ν ^ 4 / 384 := by
    rw [div_mul_eq_mul_div₀]
    rw [div_eq_div_iff
      (mul_ne_zero (by norm_num : (384:ℝ) ≠ 0) (pow_ne_zero _ (ne_of_gt hνpos)))
      (by norm_num : (384:ℝ) ≠ 0)]
    ring
  have hfinal : (1 - 2 * ρ ^ 2)
      ≤ ((1 / 2) * u ^ 2 + (s - d) ^ 2 - (ρ * s + β + d) ^ 2 + β ^ 2) * (2 ^ 10 * ν ^ 6) := by
    clear hν hρ hρ2 hu hβ0 hs0 hκ0 hd hs hκ hbranch hden2 hν2 hν26 hρle hTle
      huc hβc hκc hκle hk2 htc hx hx144 hY hxsum hsum hνs hD hB hA hB1 hprod hfact
      hprod2 hmain hExpr
    have h1 : (11 / (384 * ν ^ 2) : ℝ) * (2 ^ 10 * ν ^ 6)
        ≤ ((1 / 2) * u ^ 2 + (s - d) ^ 2 - (ρ * s + β + d) ^ 2 + β ^ 2) * (2 ^ 10 * ν ^ 6) :=
      mul_le_mul_of_nonneg_right hExpr' (le_of_lt hden6)
    rw [hident] at h1
    have h2 : (1 - 2 * ρ ^ 2) ≤ 1 := by nlinarith [sq_nonneg ρ]
    have h3 : (1:ℝ) ≤ 11 * 2 ^ 10 * ν ^ 4 / 384 := by
      rw [h10]
      have h3a : (1:ℝ) * 384 ≤ 11 * 1024 * ν ^ 4 := by nlinarith [hν4]
      exact (le_div_iff₀ (by norm_num : (0:ℝ) < 384)).mpr h3a
    exact le_trans (le_trans h2 h3) h1
  exact (div_le_iff₀ hden6).mpr hfinal
set_option autoImplicit false
open Matrix
open scoped BigOperators
set_option maxHeartbeats 800000
open scoped BigOperators Classical

/-- Extends the clock slices to natural indices, returning the zero vector after the final clock
position. -/
noncomputable def g2c2_slN {n m : ℕ} (η : QState (Fin (m + 1) × Reg n)) (t : ℕ) : QState (Reg n) :=
  if h : t ≤ m then sl η ⟨t, by omega⟩ else 0

/-- Extends a finite gate family to natural indices, returning the zero matrix outside its
range. -/
noncomputable def g2c2_gateN (n m : ℕ) (U : Fin m → Matrix (Reg n) (Reg n) ℂ) (i : ℕ) :
    Matrix (Reg n) (Reg n) ℂ :=
  if h : i < m then U ⟨i, h⟩ else 0

/-- The product of the first `t` naturally indexed gate matrices, with each new gate multiplying
on the left. -/
noncomputable def g2c2_prodN {n m : ℕ} (E : Fin m → Matrix (Reg n) (Reg n) ℂ) :
    ℕ → Matrix (Reg n) (Reg n) ℂ
  | 0 => 1
  | t + 1 => g2c2_gateN n m E t * g2c2_prodN E t

/-- The natural-index gate extension agrees with the original family at an in-range index. -/
theorem g2c2_gateN_eq {n m : ℕ} (U : Fin m → Matrix (Reg n) (Reg n) ℂ) (i : ℕ) (hi : i < m) :
    g2c2_gateN n m U i = U ⟨i, hi⟩ := by
  unfold g2c2_gateN
  rw [dif_pos hi]

/-- The natural-index extension of a unitary gate family is unitary at each in-range index. -/
theorem g2c2_gateN_unitary {n m : ℕ} (E : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (hE : ∀ i : Fin m, E i ∈ Matrix.unitaryGroup (Reg n) ℂ) {i : ℕ} (hi : i < m) :
    g2c2_gateN n m E i ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [g2c2_gateN_eq _ _ hi]
  exact hE ⟨i, hi⟩

/-- For unitary gates and `t ≤ m`, the distance from the gate-evolved initial vector is bounded
by the sum of the step residual norms. -/
theorem g2c2_telescope_N (n m : ℕ) (E : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (hE : ∀ i : Fin m, E i ∈ Matrix.unitaryGroup (Reg n) ℂ)
    (ψ : ℕ → QState (Reg n)) (t : ℕ) (ht : t ≤ m) :
    nm (fun y => ψ t y - (g2c2_prodN E t *ᵥ ψ 0) y)
      ≤ ∑ i ∈ Finset.range t, nm (fun y => ψ (i + 1) y - (g2c2_gateN n m E i *ᵥ ψ i) y) := by
  induction t with
  | zero =>
    have h1 : g2c2_prodN E 0 = (1 : Matrix (Reg n) (Reg n) ℂ) := rfl
    rw [h1, Matrix.one_mulVec]
    have h2 : (fun y : Reg n => ψ 0 y - (ψ 0) y) = 0 := by
      funext y
      simp
    rw [h2]
    have h3 : nm (0 : QState (Reg n)) = 0 := by
      unfold nm vn
      simp
    rw [h3]
    simp
  | succ t ih =>
    have htt : t < m := Nat.lt_of_succ_le ht
    have hprod : g2c2_prodN E (t + 1) = g2c2_gateN n m E t * g2c2_prodN E t := rfl
    have hunit : g2c2_gateN n m E t ∈ Matrix.unitaryGroup (Reg n) ℂ :=
      g2c2_gateN_unitary E hE htt

    have hsplit : (fun y : Reg n => ψ (t + 1) y - (g2c2_prodN E (t + 1) *ᵥ ψ 0) y)
        = (fun y => ψ (t + 1) y - (g2c2_gateN n m E t *ᵥ ψ t) y)
            + fun y => (g2c2_gateN n m E t *ᵥ (fun z => ψ t z - (g2c2_prodN E t *ᵥ ψ 0) z)) y := by
      funext y
      have h1 : (g2c2_prodN E (t + 1) *ᵥ ψ 0) y
          = (g2c2_gateN n m E t *ᵥ (g2c2_prodN E t *ᵥ ψ 0)) y := by
        rw [hprod, Matrix.mulVec_mulVec]
      have h2a : (fun z : Reg n => ψ t z - (g2c2_prodN E t *ᵥ ψ 0) z)
          = ψ t - g2c2_prodN E t *ᵥ ψ 0 := by
        funext z
        simp
      have h3 : (g2c2_gateN n m E t *ᵥ (fun z => ψ t z - (g2c2_prodN E t *ᵥ ψ 0) z)) y
          = (g2c2_gateN n m E t *ᵥ ψ t) y
              - (g2c2_gateN n m E t *ᵥ (g2c2_prodN E t *ᵥ ψ 0)) y := by
        rw [h2a, Matrix.mulVec_sub]
        rfl
      show ψ (t + 1) y - (g2c2_prodN E (t + 1) *ᵥ ψ 0) y
        = (ψ (t + 1) y - (g2c2_gateN n m E t *ᵥ ψ t) y)
            + (g2c2_gateN n m E t *ᵥ (fun z => ψ t z - (g2c2_prodN E t *ᵥ ψ 0) z)) y
      rw [h1, h3]
      ring

    set A : ℝ := nm (fun y : Reg n => ψ (t + 1) y - (g2c2_gateN n m E t *ᵥ ψ t) y) with hA
    set D : ℝ := nm (fun z : Reg n => ψ t z - (g2c2_prodN E t *ᵥ ψ 0) z) with hD
    set G : ℝ := (∑ i ∈ Finset.range t,
        nm (fun y : Reg n => ψ (i + 1) y - (g2c2_gateN n m E i *ᵥ ψ i) y)) with hG
    have hunitnm : nm (g2c2_gateN n m E t *ᵥ (fun z => ψ t z - (g2c2_prodN E t *ᵥ ψ 0) z)) = D := by
      rw [hD]
      exact g13n2_unitary_nm hunit _
    have htri : nm ((fun y : Reg n => ψ (t + 1) y - (g2c2_gateN n m E t *ᵥ ψ t) y)
        + fun y => (g2c2_gateN n m E t *ᵥ (fun z => ψ t z - (g2c2_prodN E t *ᵥ ψ 0) z)) y) ≤ A + D := by
      rw [hA, hD]
      have hcast : ((fun y : Reg n => ψ (t + 1) y - (g2c2_gateN n m E t *ᵥ ψ t) y)
          + fun y => (g2c2_gateN n m E t *ᵥ (fun z => ψ t z - (g2c2_prodN E t *ᵥ ψ 0) z)) y)
          = (fun y : Reg n => ψ (t + 1) y - (g2c2_gateN n m E t *ᵥ ψ t) y
              + (g2c2_gateN n m E t *ᵥ (fun z => ψ t z - (g2c2_prodN E t *ᵥ ψ 0) z)) y) := by
        funext y
        simp [Pi.add_apply]
      rw [hcast]
      have := g13n2_nm_add (fun y : Reg n => ψ (t + 1) y - (g2c2_gateN n m E t *ᵥ ψ t) y)
        (g2c2_gateN n m E t *ᵥ (fun z => ψ t z - (g2c2_prodN E t *ᵥ ψ 0) z))
      rw [hunitnm] at this
      exact this
    have hle : D ≤ G := by
      rw [hD, hG]
      exact ih (le_of_lt htt)
    have step1 : nm (fun y : Reg n => ψ (t + 1) y - (g2c2_prodN E (t + 1) *ᵥ ψ 0) y) ≤ A + D := by
      rw [hsplit]
      exact htri
    have step2 : A + D ≤ A + G := add_le_add_right hle A
    have step3 : A + G = ∑ i ∈ Finset.range (t + 1),
        nm (fun y : Reg n => ψ (i + 1) y - (g2c2_gateN n m E i *ᵥ ψ i) y) := by
      rw [add_comm, Finset.sum_range_succ]
    exact le_trans step1 (le_trans step2 (le_of_eq step3))

/-- Appending one gate to a word multiplies its matrix on the left by the appended gate matrix. -/
theorem g2c2_word_append_one (n : ℕ) (l : List FiniteGateCode) (g : FiniteGateCode) :
    finiteWordMatrix n (l ++ [g]) = finiteCodeMatrix n g * finiteWordMatrix n l := by
  induction l with
  | nil =>
    rw [List.nil_append]
    show finiteWordMatrix n [g] = _
    simp only [finiteWordMatrix, one_mul, mul_one]
  | cons g' l' ih =>
    have h1 : finiteWordMatrix n ((g' :: l') ++ [g])
        = finiteWordMatrix n (l' ++ [g]) * finiteCodeMatrix n g' := rfl
    rw [h1, ih, mul_assoc]
    show finiteCodeMatrix n g * (finiteWordMatrix n l' * finiteCodeMatrix n g')
        = finiteCodeMatrix n g * finiteWordMatrix n (g' :: l')
    rw [finiteWordMatrix]

/-- The matrix of a prefix of length `t + 1` is the next gate matrix times the matrix of the
prefix of length `t`. -/
theorem g2c2_word_succ (n : ℕ) (gs : List FiniteGateCode) (t : ℕ) (ht : t < gs.length) :
    finiteWordMatrix n (gs.take (t + 1))
      = finiteCodeMatrix n gs[t] * finiteWordMatrix n (gs.take t) := by
  rw [← List.take_concat_get' gs t ht, g2c2_word_append_one]

/-- The distance of a clock slice from exact evolution is bounded by the sum of rounded
propagation residuals plus the rounding scale times the sum of earlier slice norms. -/
theorem g2c2_telescope_C (C : QmaHistoryCircuit) (b : ℕ)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) :
    ∀ t : ℕ, t ≤ C.gates.length →
      nm (fun y => g2c2_slN η t y - (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ g2c2_slN η 0) y)
        ≤ (∑ i ∈ Finset.range t,
            nm (fun y => g2c2_slN η (i + 1) y
              - (g2c2_gateN C.qubits C.gates.length (qmaRoundedGates C b) i
                  *ᵥ g2c2_slN η i) y))
          + g13n2_kappa C.qubits b * (∑ i ∈ Finset.range t, nm (g2c2_slN η i)) := by
  intro t
  induction t with
  | zero =>
    intro ht
    have h1 : C.gates.take 0 = ([] : List FiniteGateCode) := rfl
    rw [h1]
    have h2 : finiteWordMatrix C.qubits ([] : List FiniteGateCode) = 1 := rfl
    rw [h2, Matrix.one_mulVec]
    have h3 : (fun y : Reg C.qubits => g2c2_slN η 0 y - (g2c2_slN η 0) y) = 0 := by
      funext y
      simp
    rw [h3]
    have h4 : nm (0 : QState (Reg C.qubits)) = 0 := by
      unfold nm vn
      simp
    rw [h4]
    simp
  | succ t ih =>
    intro ht
    have htt : t < C.gates.length := Nat.lt_of_succ_le ht

    set ψ : ℕ → QState (Reg C.qubits) := g2c2_slN η with hψ
    set Ug : ℕ → Matrix (Reg C.qubits) (Reg C.qubits) ℂ :=
      g2c2_gateN C.qubits C.gates.length (qmaRoundedGates C b) with hUg
    set Mt : Matrix (Reg C.qubits) (Reg C.qubits) ℂ :=
      finiteCodeMatrix C.qubits (qmaGateAt C.gates t) with hMt
    have hunit : Mt ∈ Matrix.unitaryGroup (Reg C.qubits) ℂ := by
      rw [hMt]
      exact finiteCodeMatrix_unitary C.qubits (qmaGateAt C.gates t)
        (g13n2_hist_gateAt_legal C htt)
    have hUgeq : Ug t = qmaRoundedGate C.qubits b (qmaGateAt C.gates t) := by
      rw [hUg, g2c2_gateN_eq _ _ htt, qmaRoundedGates]
    have hMpert : nm ((Ug t - Mt) *ᵥ ψ t) ≤ g13n2_kappa C.qubits b * nm (ψ t) := by
      rw [hUgeq, hMt, hψ]
      exact g13n2_round_gate_vec C.qubits b (qmaGateAt C.gates t) (g2c2_slN η t)

    have hword : finiteWordMatrix C.qubits (C.gates.take (t + 1))
        = Mt * finiteWordMatrix C.qubits (C.gates.take t) := by
      rw [g2c2_word_succ C.qubits C.gates t htt, hMt, g13n2_qmaGateAt_eq C.gates htt]

    have hsplit : (fun y : Reg C.qubits =>
        ψ (t + 1) y - (finiteWordMatrix C.qubits (C.gates.take (t + 1)) *ᵥ ψ 0) y)
        = (fun y => ψ (t + 1) y - (Mt *ᵥ ψ t) y)
            + fun y => (Mt *ᵥ (fun z => ψ t z - (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ ψ 0) z)) y := by
      funext y
      have h1 : (finiteWordMatrix C.qubits (C.gates.take (t + 1)) *ᵥ ψ 0) y
          = (Mt *ᵥ (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ ψ 0)) y := by
        rw [hword, Matrix.mulVec_mulVec]
      have h2a : (fun z : Reg C.qubits =>
          ψ t z - (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ ψ 0) z)
          = ψ t - finiteWordMatrix C.qubits (C.gates.take t) *ᵥ ψ 0 := by
        funext z
        simp
      have h3 : (Mt *ᵥ (fun z => ψ t z - (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ ψ 0) z)) y
          = (Mt *ᵥ ψ t) y - (Mt *ᵥ (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ ψ 0)) y := by
        rw [h2a, Matrix.mulVec_sub]
        rfl
      show ψ (t + 1) y - (finiteWordMatrix C.qubits (C.gates.take (t + 1)) *ᵥ ψ 0) y
        = (ψ (t + 1) y - (Mt *ᵥ ψ t) y)
            + (Mt *ᵥ (fun z => ψ t z - (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ ψ 0) z)) y
      rw [h1, h3]
      ring

    set A : ℝ := nm (fun y : Reg C.qubits => ψ (t + 1) y - (Mt *ᵥ ψ t) y) with hA
    set D : ℝ := nm (fun y : Reg C.qubits => ψ t y
      - (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ ψ 0) y) with hD
    set R : ℝ := (∑ i ∈ Finset.range t,
      nm (fun y : Reg C.qubits => ψ (i + 1) y - (Ug i *ᵥ ψ i) y)) with hR
    set S : ℝ := (∑ i ∈ Finset.range t, nm (ψ i)) with hS
    have hunitnm : nm (Mt *ᵥ (fun z : Reg C.qubits =>
        ψ t z - (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ ψ 0) z)) = D := by
      rw [hD]
      exact g13n2_unitary_nm hunit _

    set Rt : ℝ := nm (fun y : Reg C.qubits => ψ (t + 1) y - (Ug t *ᵥ ψ t) y) with hRt
    set St : ℝ := nm (ψ t) with hSt

    have hsplit2 : (fun y : Reg C.qubits => ψ (t + 1) y - (Mt *ᵥ ψ t) y)
        = (fun y => ψ (t + 1) y - (Ug t *ᵥ ψ t) y)
            + fun y => ((Ug t - Mt) *ᵥ ψ t) y := by
      funext y
      have h1 : ((Ug t - Mt) *ᵥ ψ t) y = (Ug t *ᵥ ψ t) y - (Mt *ᵥ ψ t) y := by
        rw [Matrix.sub_mulVec, Pi.sub_apply]
      show ψ (t + 1) y - (Mt *ᵥ ψ t) y
        = (ψ (t + 1) y - (Ug t *ᵥ ψ t) y) + ((Ug t - Mt) *ᵥ ψ t) y
      rw [h1]
      ring
    have hAle : A ≤ Rt + g13n2_kappa C.qubits b * St := by
      rw [hA, hsplit2]
      have hcast : ((fun y : Reg C.qubits => ψ (t + 1) y - (Ug t *ᵥ ψ t) y)
          + fun y => ((Ug t - Mt) *ᵥ ψ t) y)
          = (fun y : Reg C.qubits =>
              ψ (t + 1) y - (Ug t *ᵥ ψ t) y + ((Ug t - Mt) *ᵥ ψ t) y) := by
        funext y
        simp [Pi.add_apply]
      rw [hcast, hRt, hSt]
      have htri := g13n2_nm_add
        (fun y : Reg C.qubits => ψ (t + 1) y - (Ug t *ᵥ ψ t) y)
        ((Ug t - Mt) *ᵥ ψ t)
      exact le_trans htri (add_le_add_right hMpert _)

    have hih : D ≤ R + g13n2_kappa C.qubits b * S := by
      rw [hD, hR, hS, hψ, hUg]
      exact ih (le_of_lt htt)
    have hstep : nm (fun y : Reg C.qubits =>
        ψ (t + 1) y - (finiteWordMatrix C.qubits (C.gates.take (t + 1)) *ᵥ ψ 0) y)
        ≤ A + D := by
      rw [hsplit]
      have hcast : ((fun y : Reg C.qubits => ψ (t + 1) y - (Mt *ᵥ ψ t) y)
          + fun y => (Mt *ᵥ (fun z => ψ t z
            - (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ ψ 0) z)) y)
          = (fun y : Reg C.qubits => ψ (t + 1) y - (Mt *ᵥ ψ t) y
              + (Mt *ᵥ (fun z => ψ t z
                - (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ ψ 0) z)) y) := by
        funext y
        simp [Pi.add_apply]
      rw [hcast, hA, hD]
      have htri := g13n2_nm_add
        (fun y : Reg C.qubits => ψ (t + 1) y - (Mt *ᵥ ψ t) y)
        (Mt *ᵥ (fun z => ψ t z - (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ ψ 0) z))
      rw [hunitnm] at htri
      exact htri
    have hfin : A + D ≤ (∑ i ∈ Finset.range (t + 1),
        nm (fun y : Reg C.qubits => ψ (i + 1) y - (Ug i *ᵥ ψ i) y))
          + g13n2_kappa C.qubits b * (∑ i ∈ Finset.range (t + 1), nm (ψ i)) := by
      have hs1 : (∑ i ∈ Finset.range (t + 1),
          nm (fun y : Reg C.qubits => ψ (i + 1) y - (Ug i *ᵥ ψ i) y))
          = R + Rt := by
        rw [Finset.sum_range_succ, hR, hRt]
      have hs2 : (∑ i ∈ Finset.range (t + 1), nm (ψ i)) = S + St := by
        rw [Finset.sum_range_succ, hS, hSt]
      rw [hs1, hs2]
      nlinarith
    exact le_trans hstep hfin

/-- A work basis register violates initialization when at least one designated initially zero
wire is true. -/
def g2c2_illAt (C : QmaHistoryCircuit) (y : Reg C.qubits) : Prop :=
  ∃ j ∈ C.initZeroWires, y j = true

open Classical in

/-- The initial-slice mass violating initialization is at most the sum of all input penalty
energies. -/
theorem g2c2_in_mass (C : QmaHistoryCircuit)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) :
    (∑ y : Reg C.qubits,
        if g2c2_illAt C y then ‖η ((0 : Fin (C.gates.length + 1)), y)‖ ^ 2 else (0 : ℝ))
      ≤ ∑ j ∈ C.initZeroWires,
          qmaEnergy (qmaInTerm C.qubits C.gates.length j) η := by
  have hterm : ∀ j ∈ C.initZeroWires,
      qmaEnergy (qmaInTerm C.qubits C.gates.length j) η
        = ∑ y : Reg C.qubits, if y j = true then ‖η ((0 : Fin (C.gates.length + 1)), y)‖ ^ 2
            else (0 : ℝ) :=
    fun j _ => g13n_in_energy C.qubits C.gates.length j η
  rw [Finset.sum_congr rfl (fun j hj => hterm j hj)]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun y _ => ?_)
  by_cases hy : g2c2_illAt C y
  · rw [if_pos hy]
    obtain ⟨j, hj, hyj⟩ := hy
    have h1 : (if y j = true then ‖η ((0 : Fin (C.gates.length + 1)), y)‖ ^ 2 else (0 : ℝ))
        ≤ ∑ k ∈ C.initZeroWires,
            (if y k = true then ‖η ((0 : Fin (C.gates.length + 1)), y)‖ ^ 2 else (0 : ℝ)) :=
      Finset.single_le_sum
        (f := fun k => if y k = true then ‖η ((0 : Fin (C.gates.length + 1)), y)‖ ^ 2 else (0 : ℝ))
        (fun k _ => by by_cases h : y k = true <;> simp [h, sq_nonneg]) hj
    rw [if_pos hyj] at h1
    exact h1
  · rw [if_neg hy]
    exact Finset.sum_nonneg
      (fun k _ => by by_cases h : y k = true <;> simp [h, sq_nonneg])

/-- Under the stated scale, normalization, and rounding bounds, `(1 - 2 * ρ²) / (2^10 * ν^6)` is
at most the maximum of `u² / 2`, `β²`, and the combined boundary expression. -/
theorem g2c2_scale_apply (ν ρ u d β s κ : ℝ)
    (hν : 1 ≤ ν) (hρ : 0 ≤ ρ) (hρ2 : ρ ^ 2 ≤ 1 / 2)
    (hu : 0 ≤ u) (hβ0 : 0 ≤ β) (hs0 : 0 ≤ s) (hκ0 : 0 ≤ κ)
    (hd : d ≤ ν * (u + κ))
    (hs : 1 ≤ ν ^ 2 * (s + ν * (u + κ)) ^ 2)
    (hκ : κ ≤ 1 / (2 ^ 10 * ν ^ 6)) :
    (1 - 2 * ρ ^ 2) / (2 ^ 10 * ν ^ 6)
      ≤ max ((1 / 2) * u ^ 2)
          (max (β ^ 2) ((1 / 2) * u ^ 2 + (s - d) ^ 2 - (ρ * s + β + d) ^ 2 + β ^ 2)) := by
  set T : ℝ := (1 - 2 * ρ ^ 2) / (2 ^ 10 * ν ^ 6) with hT
  by_cases h1 : (1 / 2) * u ^ 2 < T
  · by_cases h2 : β ^ 2 < T
    · have hmain : T ≤ (1 / 2) * u ^ 2 + (s - d) ^ 2 - (ρ * s + β + d) ^ 2 + β ^ 2 := by
        rw [hT]
        exact g2c2_scale_core ν ρ u d β s κ hν hρ hρ2 hu hβ0 hs0 hκ0 hd hs hκ ⟨h1, h2⟩
      exact le_trans hmain
        (le_trans (le_max_right (β ^ 2) _) (le_max_right _ (max (β ^ 2) _)))
    · exact le_trans (not_lt.mp h2)
        (le_trans (le_max_left (β ^ 2) _) (le_max_right _ (max (β ^ 2) _)))
  · exact le_trans (not_lt.mp h1) (le_max_left _ _)

/-- The absolute difference of two Euclidean norms is at most the norm of the vector difference. -/
theorem g2c2_nm_rev {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    |nm a - nm b| ≤ nm (fun y => a y - b y) := by
  have hneg : ∀ v : ι → ℂ, nm (fun y => - v y) = nm v := by
    intro v
    unfold nm vn
    apply congr_arg Real.sqrt
    apply Finset.sum_congr rfl
    intro y _
    show ‖- v y‖ ^ 2 = ‖v y‖ ^ 2
    rw [norm_neg]
  have h1 : nm a ≤ nm b + nm (fun y => a y - b y) := by
    have h := g13n2_nm_add (fun y => a y - b y) b
    have key : (fun y => (a y - b y) + b y) = a := by
      funext y
      ring
    rw [key] at h
    linarith
  have h2 : nm b ≤ nm a + nm (fun y => a y - b y) := by
    have h := g13n2_nm_add (fun y => b y - a y) a
    have key : (fun y => (b y - a y) + a y) = b := by
      funext y
      ring
    rw [key] at h
    have flip : (fun y : ι => b y - a y) = (fun y : ι => - (a y - b y)) := by
      funext y
      ring
    rw [flip, hneg] at h
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- An `n`-qubit basis register has cardinality `2^n`. -/
theorem g2c2_card_reg (n : ℕ) : Fintype.card (Reg n) = 2 ^ n := by
  have h1 : Fintype.card (Reg n) = Fintype.card (Fin n → Bool) := rfl
  rw [h1, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- At precision `3 * (n + m) + 64`, the correction `κ + κ² / 2` is at most `qmaTiny (n + m +
2)`. -/
theorem g2c2_tiny_absorb (n m : ℕ) :
    g13n2_kappa n (3 * (n + m) + 64) + g13n2_kappa n (3 * (n + m) + 64) ^ 2 / 2
      ≤ qmaTiny (n + m + 2) := by
  have hcard : (Fintype.card (Reg n) : ℝ) = (2 : ℝ) ^ n := by
    rw [g2c2_card_reg]
    norm_num [Nat.cast_pow]
  set κ : ℝ := g13n2_kappa n (3 * (n + m) + 64) with hκ0
  set τ : ℝ := qmaTiny (n + m + 2) with hτ0
  have hκ1 : κ = (2 : ℝ) ^ n * (1 / (2 : ℝ) ^ (3 * (n + m) + 64)) := by
    rw [hκ0]
    unfold g13n2_kappa
    rw [hcard]
  have hτ1 : τ = (1 / (2 : ℝ) ^ (n + m + 2)) := by
    rw [hτ0]
    unfold qmaTiny
    rw [inv_pow, ← one_div]
  have hκ2 : κ = (1 / (2 : ℝ) ^ (2 * n + 3 * m + 64)) := by
    have step : (2:ℝ) ^ n * (1 / (2:ℝ) ^ (3 * (n + m) + 64))
        = 1 / (2:ℝ) ^ (2 * n + 3 * m + 64) := by
      have hexp : 3 * (n + m) + 64 = n + (2 * n + 3 * m + 64) := by omega
      have hpe : (2:ℝ) ^ (n + (2 * n + 3 * m + 64))
          = (2:ℝ) ^ n * (2:ℝ) ^ (2 * n + 3 * m + 64) := pow_add _ _ _
      rw [hexp, hpe, div_mul_eq_div_mul_one_div]
      have hne : (2:ℝ) ^ n ≠ 0 := by positivity
      rw [← mul_assoc, mul_one_div_cancel hne, one_mul]
    rw [hκ1]
    exact step
  have hτ2 : τ = (1 / (2 : ℝ) ^ (n + m + 2)) := hτ1
  have hA : κ ≤ τ / 2 := by
    have h3 : (n + m + 2) + 1 = n + m + 3 := by omega
    have h4 : ((2:ℝ) ^ (n + m + 2)) * 2 = (2:ℝ) ^ (n + m + 3) := by
      rw [← pow_succ, h3]
    have h5 : τ / 2 = 1 / (2:ℝ) ^ (n + m + 3) := by
      rw [hτ2, div_div, h4]
    have h6 : (1 / (2:ℝ) ^ (2 * n + 3 * m + 64)) ≤ 1 / (2:ℝ) ^ (n + m + 3) :=
      one_div_pow_le_one_div_pow_of_le (by norm_num) (by omega)
    rw [hκ2, h5]
    exact h6
  have hB : κ ≤ 1 / 2 := by
    have h6 : (1 / (2:ℝ) ^ (2 * n + 3 * m + 64)) ≤ 1 / (2:ℝ) ^ 1 :=
      one_div_pow_le_one_div_pow_of_le (by norm_num) (by omega)
    have h7 : (1:ℝ) / (2:ℝ) ^ 1 = 1 / 2 := by rw [pow_one]
    rw [hκ2, ← h7]
    exact h6
  have hk0 : 0 ≤ κ := by
    rw [hκ2]
    positivity
  have ht0 : 0 ≤ τ := by
    rw [hτ2]
    positivity
  have hsq : κ ^ 2 / 2 ≤ τ / 8 := by
    have h : κ * κ ≤ (τ / 2) * (1 / 2) :=
      mul_le_mul hA hB hk0 (by nlinarith)
    nlinarith
  nlinarith

/-- The Euclidean norm of the step residual between successive natural-index clock slices using
the rounded gate family. -/
noncomputable def g2c2_res (C : QmaHistoryCircuit) (b : ℕ)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) (i : ℕ) : ℝ :=
  nm (fun y => g2c2_slN η (i + 1) y
    - (g2c2_gateN C.qubits C.gates.length (qmaRoundedGates C b) i
        *ᵥ g2c2_slN η i) y)

/-- At an index at most `m`, the natural-index slice equals the corresponding finite clock
slice. -/
theorem g2c2_slN_eq {n m : ℕ} (η : QState (Fin (m + 1) × Reg n)) {i : ℕ} (hi : i ≤ m) :
    g2c2_slN η i = sl η ⟨i, by omega⟩ := by
  unfold g2c2_slN
  rw [dif_pos hi]

/-- The absolute sum of a real function over a finite set is at most the square root of the
cardinality times the square root of the sum of squares. -/
theorem g2c2_cs (s : Finset ℕ) (f : ℕ → ℝ) :
    |∑ i ∈ s, f i| ≤ Real.sqrt s.card * Real.sqrt (∑ i ∈ s, f i ^ 2) := by
  have hcs : (∑ i ∈ s, f i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * s.card := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s f (fun _ => (1:ℝ))
    have h1 : (∑ i ∈ s, f i * (fun _ => (1:ℝ)) i) = ∑ i ∈ s, f i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h2 : (∑ i ∈ s, (fun _ => (1:ℝ)) i ^ 2) = s.card := by
      have h2a : (∑ i ∈ s, (fun _ => (1:ℝ)) i ^ 2) = ∑ i ∈ s, (1:ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        norm_num
      rw [h2a, Finset.sum_const, nsmul_one]
    rw [h1, h2] at h
    exact h
  have hsq : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h3 : |∑ i ∈ s, f i| ≤ Real.sqrt ((∑ i ∈ s, f i ^ 2) * s.card) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [sq_abs]
    exact hcs
  have h4 : Real.sqrt ((∑ i ∈ s, f i ^ 2) * s.card)
      = Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt s.card :=
    Real.sqrt_mul hsq _
  rw [h4] at h3
  linarith

/-- For a normalized joint state, the distance of slice `t` from exact evolution is at most
`sqrt t * (u + g13n2_kappa C.qubits b)` when `u` is the nonnegative total residual norm. -/
theorem g2c2_dist_le (C : QmaHistoryCircuit) (b : ℕ)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) (hη : Normalized η)
    (u : ℝ) (hu : 0 ≤ u)
    (hu2 : u ^ 2 = ∑ i ∈ Finset.range C.gates.length, g2c2_res C b η i ^ 2) :
    ∀ t : ℕ, t ≤ C.gates.length →
      nm (fun y => g2c2_slN η t y
          - (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ g2c2_slN η 0) y)
        ≤ Real.sqrt t * (u + g13n2_kappa C.qubits b) := by
  intro t ht
  have hκ : 0 ≤ g13n2_kappa C.qubits b := g13n2_kappa_nonneg _ _
  have htel := g2c2_telescope_C C b η t ht
  have hres : ∀ i ∈ Finset.range t,
      g2c2_res C b η i
        = nm (fun y => g2c2_slN η (i + 1) y
          - (g2c2_gateN C.qubits C.gates.length (qmaRoundedGates C b) i
              *ᵥ g2c2_slN η i) y) := fun i _ => rfl
  rw [← Finset.sum_congr rfl hres] at htel
  have hres_le : (∑ i ∈ Finset.range t, g2c2_res C b η i) ≤ Real.sqrt t * u := by
    have hsubm : Finset.range t ⊆ Finset.range C.gates.length := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hsub : ∑ i ∈ Finset.range t, g2c2_res C b η i ^ 2
        ≤ ∑ i ∈ Finset.range C.gates.length, g2c2_res C b η i ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubm (fun i _ _ => sq_nonneg _)
    have h2u : Real.sqrt (∑ i ∈ Finset.range t, g2c2_res C b η i ^ 2) ≤ u := by
      have h := Real.sqrt_le_sqrt hsub
      rw [← hu2, Real.sqrt_sq hu] at h
      exact h
    have hcs := g2c2_cs (Finset.range t) (g2c2_res C b η)
    rw [Finset.card_range] at hcs
    have hm : Real.sqrt t * Real.sqrt (∑ i ∈ Finset.range t, g2c2_res C b η i ^ 2)
        ≤ Real.sqrt t * u :=
      mul_le_mul_of_nonneg_left h2u (Real.sqrt_nonneg _)
    calc ∑ i ∈ Finset.range t, g2c2_res C b η i
        ≤ |∑ i ∈ Finset.range t, g2c2_res C b η i| := le_abs_self _
      _ ≤ Real.sqrt t * Real.sqrt (∑ i ∈ Finset.range t, g2c2_res C b η i ^ 2) := hcs
      _ ≤ Real.sqrt t * u := hm
  have hsl_le : (∑ i ∈ Finset.range t, nm (g2c2_slN η i)) ≤ Real.sqrt t := by
    have hfull : (∑ i ∈ Finset.range (C.gates.length + 1), nm (g2c2_slN η i) ^ 2) = 1 := by
      have hconv : ∀ i : ℕ, i < C.gates.length + 1 →
          nm (g2c2_slN η i) ^ 2 = vn (g2c2_slN η i) := fun i _ => nm_sq _
      rw [Finset.sum_congr rfl (fun i hi => hconv i (Finset.mem_range.mp hi))]
      have hpt2 : ∀ i : Fin (C.gates.length + 1),
          vn (g2c2_slN η i.val) = vn (sl η i) := by
        intro i
        have hi' : i.val ≤ C.gates.length := by
          have := i.isLt
          omega
        rw [g2c2_slN_eq η hi']
      rw [← Fin.sum_univ_eq_sum_range (fun i => vn (g2c2_slN η i)) (C.gates.length + 1)]
      have h3 : (∑ i : Fin (C.gates.length + 1), vn (g2c2_slN η ↑i))
          = ∑ i : Fin (C.gates.length + 1), vn (sl η i) :=
        Finset.sum_congr rfl (fun i _ => hpt2 i)
      rw [h3]
      exact g13n2_sum_sl_vn hη
    have hsubm : Finset.range t ⊆ Finset.range (C.gates.length + 1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hsub : ∑ i ∈ Finset.range t, nm (g2c2_slN η i) ^ 2
        ≤ ∑ i ∈ Finset.range (C.gates.length + 1), nm (g2c2_slN η i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubm (fun i _ _ => sq_nonneg _)
    have hsq1 : ∑ i ∈ Finset.range t, nm (g2c2_slN η i) ^ 2 ≤ 1 := by
      linarith
    have h2s : Real.sqrt (∑ i ∈ Finset.range t, nm (g2c2_slN η i) ^ 2) ≤ 1 := by
      have hh := Real.sqrt_le_sqrt hsq1
      rwa [Real.sqrt_one] at hh
    have hcs := g2c2_cs (Finset.range t) (fun i => nm (g2c2_slN η i))
    rw [Finset.card_range] at hcs
    have hm : Real.sqrt t * Real.sqrt (∑ i ∈ Finset.range t, nm (g2c2_slN η i) ^ 2)
        ≤ Real.sqrt t * 1 :=
      mul_le_mul_of_nonneg_left h2s (Real.sqrt_nonneg _)
    calc ∑ i ∈ Finset.range t, nm (g2c2_slN η i)
        ≤ |∑ i ∈ Finset.range t, nm (g2c2_slN η i)| := le_abs_self _
      _ ≤ Real.sqrt t * Real.sqrt (∑ i ∈ Finset.range t, nm (g2c2_slN η i) ^ 2) := hcs
      _ ≤ Real.sqrt t := by linarith
  have hsum : (∑ i ∈ Finset.range t, g2c2_res C b η i)
      + g13n2_kappa C.qubits b * (∑ i ∈ Finset.range t, nm (g2c2_slN η i))
      ≤ Real.sqrt t * (u + g13n2_kappa C.qubits b) := by
    have h1 := hres_le
    have h2 := mul_le_mul_of_nonneg_left hsl_le hκ
    nlinarith
  exact le_trans htel hsum

/-- The final slice's distance from exact evolution is at most `sqrt (C.gates.length + 1) * (u +
g13n2_kappa C.qubits b)` under the total residual norm assumptions. -/
theorem g2c2_dist_C (C : QmaHistoryCircuit) (b : ℕ)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) (hη : Normalized η)
    (u : ℝ) (hu : 0 ≤ u)
    (hu2 : u ^ 2 = ∑ i ∈ Finset.range C.gates.length, g2c2_res C b η i ^ 2) :
    nm (fun y => g2c2_slN η C.gates.length y
        - (finiteWordMatrix C.qubits C.gates *ᵥ g2c2_slN η 0) y)
      ≤ Real.sqrt (C.gates.length + 1) * (u + g13n2_kappa C.qubits b) := by
  have h := g2c2_dist_le C b η hη u hu hu2 C.gates.length (le_refl _)
  rw [List.take_length] at h
  have h2 : Real.sqrt (C.gates.length : ℕ) ≤ Real.sqrt (C.gates.length + 1) := by
    apply Real.sqrt_le_sqrt
    have : (C.gates.length : ℝ) ≤ (C.gates.length : ℝ) + 1 := by linarith
    exact this
  have hκ : 0 ≤ g13n2_kappa C.qubits b := g13n2_kappa_nonneg _ _
  have h3 : Real.sqrt (C.gates.length : ℕ) * (u + g13n2_kappa C.qubits b)
      ≤ Real.sqrt (C.gates.length + 1) * (u + g13n2_kappa C.qubits b) :=
    mul_le_mul_of_nonneg_right h2 (add_nonneg hu hκ)
  exact le_trans h h3

/-- Normalization gives `1 ≤ (C.gates.length + 1) * (nm (g2c2_slN η 0) + sqrt (C.gates.length +
1) * (u + g13n2_kappa C.qubits b))²` under the total residual norm assumptions. -/
theorem g2c2_norm_C (C : QmaHistoryCircuit) (b : ℕ)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) (hη : Normalized η)
    (u : ℝ) (hu : 0 ≤ u)
    (hu2 : u ^ 2 = ∑ i ∈ Finset.range C.gates.length, g2c2_res C b η i ^ 2) :
    1 ≤ ((C.gates.length + 1 : ℕ) : ℝ) *
      (nm (g2c2_slN η 0)
        + Real.sqrt (C.gates.length + 1) * (u + g13n2_kappa C.qubits b)) ^ 2 := by
  set s : ℝ := nm (g2c2_slN η 0) with hs
  set κ : ℝ := g13n2_kappa C.qubits b with hκ0
  have hκ : 0 ≤ κ := by
    rw [hκ0]
    exact g13n2_kappa_nonneg _ _
  set X : ℝ := s + Real.sqrt (C.gates.length + 1) * (u + κ) with hX
  have hX0 : 0 ≤ X := by
    have h1 : 0 ≤ Real.sqrt (C.gates.length + 1) * (u + κ) :=
      mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hu hκ)
    have h2 : 0 ≤ s := by
      rw [hs]
      exact nm_nonneg _
    nlinarith
  have hpt : ∀ t : ℕ, t ≤ C.gates.length → nm (g2c2_slN η t) ≤ X := by
    intro t ht
    have hdist := g2c2_dist_le C b η hη u hu hu2 t ht
    rw [← hκ0] at hdist
    have hU : finiteWordMatrix C.qubits (C.gates.take t)
        ∈ Matrix.unitaryGroup (Reg C.qubits) ℂ :=
      finiteWordMatrix_unitary C.qubits (C.gates.take t) (finiteWordLegal_take C.legal)
    have hnmW : nm (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ g2c2_slN η 0)
        = nm (g2c2_slN η 0) := g13n2_unitary_nm hU _
    have hrev := g2c2_nm_rev (g2c2_slN η t)
      (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ g2c2_slN η 0)
    have habs : nm (g2c2_slN η t)
        - nm (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ g2c2_slN η 0)
        ≤ nm (fun y => g2c2_slN η t y
          - (finiteWordMatrix C.qubits (C.gates.take t) *ᵥ g2c2_slN η 0) y) :=
      le_trans (le_abs_self _) hrev
    have hsqrt : Real.sqrt t ≤ Real.sqrt (C.gates.length + 1) := by
      apply Real.sqrt_le_sqrt
      have : t ≤ C.gates.length + 1 := Nat.le_succ_of_le ht
      exact_mod_cast this
    have hκ' : Real.sqrt t * (u + κ) ≤ Real.sqrt (C.gates.length + 1) * (u + κ) :=
      mul_le_mul_of_nonneg_right hsqrt (add_nonneg hu hκ)
    nlinarith [habs, hdist, hκ', hnmW, hs, hX,
      nm_nonneg (g2c2_slN η t), nm_nonneg (g2c2_slN η 0)]
  have hfull : (∑ i ∈ Finset.range (C.gates.length + 1), nm (g2c2_slN η i) ^ 2) = 1 := by
    have hconv : ∀ i : ℕ, i < C.gates.length + 1 →
        nm (g2c2_slN η i) ^ 2 = vn (g2c2_slN η i) := fun i _ => nm_sq _
    rw [Finset.sum_congr rfl (fun i hi => hconv i (Finset.mem_range.mp hi))]
    have hpt2 : ∀ i : Fin (C.gates.length + 1),
        vn (g2c2_slN η i.val) = vn (sl η i) := by
      intro i
      have hi' : i.val ≤ C.gates.length := by
        have := i.isLt
        omega
      rw [g2c2_slN_eq η hi']
    rw [← Fin.sum_univ_eq_sum_range (fun i => vn (g2c2_slN η i)) (C.gates.length + 1)]
    rw [Finset.sum_congr rfl (fun i _ => hpt2 i)]
    exact g13n2_sum_sl_vn hη
  have hpt' : ∀ i ∈ Finset.range (C.gates.length + 1),
      nm (g2c2_slN η i) ^ 2 ≤ X ^ 2 := by
    intro i hi
    have hi' : i ≤ C.gates.length := by
      have hi2 := Finset.mem_range.mp hi
      omega
    exact pow_le_pow_left₀ (nm_nonneg _) (hpt i hi') 2
  have hle : (∑ i ∈ Finset.range (C.gates.length + 1), nm (g2c2_slN η i) ^ 2)
      ≤ ((C.gates.length + 1 : ℕ) : ℝ) * X ^ 2 := by
    have h := Finset.sum_le_card_nsmul
      (Finset.range (C.gates.length + 1)) (fun i => nm (g2c2_slN η i) ^ 2) (X ^ 2) hpt'
    rw [Finset.card_range, nsmul_eq_mul] at h
    exact h
  have hfinal : (1:ℝ) ≤ ((C.gates.length + 1 : ℕ) : ℝ) *
      (nm (g2c2_slN η 0)
        + Real.sqrt (C.gates.length + 1) * (u + g13n2_kappa C.qubits b)) ^ 2 := by
    rw [← hκ0, ← hs, ← hX]
    linarith [hfull, hle]
  exact hfinal

open Qatlib
open Qatlib.Concepts.QmaCompleteness.HistoryHam

/-- Retains the amplitudes whose designated output bit is true and sets the others to zero. -/
noncomputable def g2c2_proj {n : ℕ} (out : Fin n) (v : QState (Reg n)) : QState (Reg n) :=
  fun y => if y out then v y else 0

/-- The squared norm of the accepting projection equals the squared amplitude mass on true
output bits. -/
theorem g2c2_proj_vn {n : ℕ} (out : Fin n) (v : QState (Reg n)) :
    vn (g2c2_proj out v) = ∑ y : Reg n, if y out then ‖v y‖ ^ 2 else 0 := by
  unfold g2c2_proj vn
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y out <;> simp [hy]

/-- The accepting projection does not increase the Euclidean norm. -/
theorem g2c2_proj_le {n : ℕ} (out : Fin n) (v : QState (Reg n)) :
    nm (g2c2_proj out v) ≤ nm v := by
  have h1 : vn (g2c2_proj out v) ≤ vn v := by
    rw [g2c2_proj_vn]
    unfold vn
    refine Finset.sum_le_sum (fun y _ => ?_)
    by_cases hy : y out <;> simp [hy]
  unfold nm
  exact Real.sqrt_le_sqrt h1

/-- The accepting projection preserves addition of vectors. -/
theorem g2c2_proj_add {n : ℕ} (out : Fin n) (a b : QState (Reg n)) :
    g2c2_proj out (a + b) = g2c2_proj out a + g2c2_proj out b := by
  funext y
  unfold g2c2_proj
  by_cases hy : y out <;> simp [hy]

/-- The accepting projection commutes with complex scalar multiplication. -/
theorem g2c2_proj_smul {n : ℕ} (out : Fin n) (c : ℂ) (v : QState (Reg n)) :
    g2c2_proj out (c • v) = c • g2c2_proj out v := by
  funext y
  unfold g2c2_proj
  by_cases hy : y out <;> simp [hy]

open Classical in

/-- Retains precisely the amplitudes on basis registers that violate initialization. -/
noncomputable def g2c2_illPart (C : QmaHistoryCircuit) (v : QState (Reg C.qubits)) :
    QState (Reg C.qubits) :=
  fun y => if g2c2_illAt C y then v y else 0

open Classical in

/-- Retains precisely the amplitudes on basis registers that satisfy initialization. -/
noncomputable def g2c2_legPart (C : QmaHistoryCircuit) (v : QState (Reg C.qubits)) :
    QState (Reg C.qubits) :=
  fun y => if g2c2_illAt C y then 0 else v y

open Classical in

/-- The squared norm of the legal part equals the mass on basis registers satisfying
initialization. -/
theorem g2c2_legPart_vn (C : QmaHistoryCircuit) (v : QState (Reg C.qubits)) :
    vn (g2c2_legPart C v)
      = ∑ y : Reg C.qubits, if g2c2_illAt C y then (0 : ℝ) else ‖v y‖ ^ 2 := by
  unfold g2c2_legPart vn
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : g2c2_illAt C y <;> simp [hy]

open Classical in

/-- The squared norm of the illegal part equals the mass on basis registers violating
initialization. -/
theorem g2c2_illPart_vn (C : QmaHistoryCircuit) (v : QState (Reg C.qubits)) :
    vn (g2c2_illPart C v)
      = ∑ y : Reg C.qubits, if g2c2_illAt C y then ‖v y‖ ^ 2 else (0 : ℝ) := by
  unfold g2c2_illPart vn
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : g2c2_illAt C y <;> simp [hy]

open Classical in

/-- The legal and illegal parts sum to the original vector. -/
theorem g2c2_leg_ill_add (C : QmaHistoryCircuit) (v : QState (Reg C.qubits)) :
    (fun y => g2c2_legPart C v y + g2c2_illPart C v y) = v := by
  funext y
  unfold g2c2_legPart g2c2_illPart
  by_cases hy : g2c2_illAt C y <;> simp [hy]

open Classical in

/-- The squared norms of the legal and illegal parts sum to the original squared norm. -/
theorem g2c2_leg_ill_vn (C : QmaHistoryCircuit) (v : QState (Reg C.qubits)) :
    vn (g2c2_legPart C v) + vn (g2c2_illPart C v) = vn v := by
  rw [g2c2_legPart_vn, g2c2_illPart_vn]
  unfold vn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : g2c2_illAt C y <;> simp [hy]

open Classical in

/-- The legal part of every work vector satisfies `QmaInitLegal`. -/
theorem g2c2_legPart_legal (C : QmaHistoryCircuit) (v : QState (Reg C.qubits)) :
    QmaInitLegal C (g2c2_legPart C v) := by
  intro p hp
  by_cases hy : g2c2_illAt C p
  · have h0 : g2c2_legPart C v p = 0 := by
      unfold g2c2_legPart
      rw [if_pos hy]
    rw [h0] at hp
    exact absurd rfl hp
  · intro j hj
    by_cases hpj : p j = true
    · exact absurd ⟨j, hj, hpj⟩ hy
    · exact Bool.eq_false_iff.mpr hpj

/-- The natural-index slice at time zero evaluates to the initial-clock amplitude. -/
theorem g2c2_slN_zero {n m : ℕ} (η : QState (Fin (m + 1) × Reg n)) (y : Reg n) :
    g2c2_slN η 0 y = η (0, y) := rfl

/-- The natural-index slice at the gate count equals the final finite clock slice. -/
theorem g2c2_slN_last (C : QmaHistoryCircuit)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) :
    g2c2_slN η C.gates.length = sl η (Fin.last C.gates.length) := by
  rw [g2c2_slN_eq η (le_refl C.gates.length)]
  rfl

/-- Every history circuit possesses a normalized work state satisfying its initialization
condition. -/
theorem g2c2_exists_legal (C : QmaHistoryCircuit) :
    ∃ φ : QState (Reg C.qubits), QmaInitLegal C φ ∧ Normalized φ := by
  classical
  refine ⟨Qatlib.Foundations.PureStateMath.Ket (fun _ => false), ?_, normalized_ket _⟩
  intro p hp
  by_cases h : p = (fun _ => false)
  · intro j hj
    simp [h]
  · have h0 : Qatlib.Foundations.PureStateMath.Ket (fun _ => false) p = 0 := by
      simp [Qatlib.Foundations.PureStateMath.Ket, h]
    exact absurd h0 hp

/-- The history circuit acceptance weight is nonnegative for every work state. -/
theorem g2c2_accept_nonneg (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits)) :
    0 ≤ qmaHistoryAcceptProb C φ := by
  unfold qmaHistoryAcceptProb
  exact measureProb_nonneg _ _

/-- The Euclidean distance between the final clock slice and the exact circuit applied to the
initial slice. -/
noncomputable def g2c2_dC (C : QmaHistoryCircuit)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) : ℝ :=
  nm (fun y => g2c2_slN η C.gates.length y
    - (finiteWordMatrix C.qubits C.gates *ᵥ g2c2_slN η 0) y)

/-- The square root of the sum of squared rounded propagation residual norms. -/
noncomputable def g2c2_u (C : QmaHistoryCircuit) (b : ℕ)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) : ℝ :=
  Real.sqrt (∑ i ∈ Finset.range C.gates.length, g2c2_res C b η i ^ 2)

/-- The total propagation residual norm `g2c2_u C b η` is nonnegative. -/
theorem g2c2_u_nonneg (C : QmaHistoryCircuit) (b : ℕ)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) :
    0 ≤ g2c2_u C b η :=
  Real.sqrt_nonneg _

/-- The square of the total residual norm equals the sum of squared step residual norms. -/
theorem g2c2_u_sq (C : QmaHistoryCircuit) (b : ℕ)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) :
    g2c2_u C b η ^ 2 = ∑ i ∈ Finset.range C.gates.length, g2c2_res C b η i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

open Classical in

/-- The square root of the initial-slice mass violating the initialization condition. -/
noncomputable def g2c2_beta (C : QmaHistoryCircuit)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) : ℝ :=
  Real.sqrt (∑ y : Reg C.qubits,
    if g2c2_illAt C y then ‖η ((0 : Fin (C.gates.length + 1)), y)‖ ^ 2 else (0 : ℝ))

/-- The initialization violation norm `g2c2_beta C η` is nonnegative. -/
theorem g2c2_beta_nonneg (C : QmaHistoryCircuit)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) :
    0 ≤ g2c2_beta C η :=
  Real.sqrt_nonneg _

open Classical in

/-- The square of `g2c2_beta C η` equals the initial-slice mass violating initialization. -/
theorem g2c2_beta_sq (C : QmaHistoryCircuit)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) :
    g2c2_beta C η ^ 2 = ∑ y : Reg C.qubits,
      if g2c2_illAt C y then ‖η ((0 : Fin (C.gates.length + 1)), y)‖ ^ 2 else (0 : ℝ) := by
  refine Real.sq_sqrt ?_
  refine Finset.sum_nonneg (fun y _ => ?_)
  by_cases hy : g2c2_illAt C y
  · simp [hy]
  · simp [hy]

/-- At an in-range step, the squared natural-index residual norm equals the squared coordinate
norm of the finite-slice propagation residual. -/
theorem g2c2_res_sq_eq (C : QmaHistoryCircuit) (b : ℕ)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) (i : Fin C.gates.length) :
    g2c2_res C b η i.val ^ 2
      = vn (fun y => sl η i.succ y
          - (qmaRoundedGates C b i *ᵥ sl η i.castSucc) y) := by
  unfold g2c2_res
  rw [nm_sq]
  have h1 : g2c2_slN η (i.val + 1) = sl η i.succ := by
    rw [g2c2_slN_eq η (by omega : i.val + 1 ≤ C.gates.length)]
    rfl
  have h2 : g2c2_slN η i.val = sl η i.castSucc := by
    rw [g2c2_slN_eq η (by omega : i.val ≤ C.gates.length)]
    rfl
  have h3 : g2c2_gateN C.qubits C.gates.length (qmaRoundedGates C b) i.val
      = qmaRoundedGates C b i := by
    rw [g2c2_gateN_eq _ _ i.isLt]
  rw [h1, h2, h3]

/-- Summing finite-slice squared propagation residuals equals the sum of squared natural-index
residual norms over the gate range. -/
theorem g2c2_res_sq_sum (C : QmaHistoryCircuit) (b : ℕ)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) :
    (∑ i : Fin C.gates.length,
      vn (fun y => sl η i.succ y
        - (qmaRoundedGates C b i *ᵥ sl η i.castSucc) y))
      = ∑ i ∈ Finset.range C.gates.length, g2c2_res C b η i ^ 2 := by
  have hsum : (∑ i : Fin C.gates.length,
      vn (fun y => sl η i.succ y
        - (qmaRoundedGates C b i *ᵥ sl η i.castSucc) y))
      = ∑ i : Fin C.gates.length, g2c2_res C b η i.val ^ 2 :=
    Finset.sum_congr rfl (fun i _ => (g2c2_res_sq_eq C b η i).symm)
  rw [hsum]
  exact Fin.sum_univ_eq_sum_range (fun j => g2c2_res C b η j ^ 2) C.gates.length

open Classical in

/-- Under the soundness and initialization mass assumptions, final accepting mass is at most
`(sqrt ε * nm (g2c2_slN η 0) + β + g2c2_dC C η)²`. -/
theorem g2c2_accept_mass (C : QmaHistoryCircuit) (ε : ℝ) (hε : 0 ≤ ε)
    (hsnd : ∀ φ : QState (Reg C.qubits), QmaInitLegal C φ → Normalized φ →
      qmaHistoryAcceptProb C φ ≤ ε)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) (_hη : Normalized η)
    (β : ℝ) (hβ : 0 ≤ β)
    (hβ2 : β ^ 2 = ∑ y : Reg C.qubits,
      if g2c2_illAt C y then ‖η ((0 : Fin (C.gates.length + 1)), y)‖ ^ 2 else (0 : ℝ)) :
    (∑ y : Reg C.qubits,
        if y C.outputWire then ‖η (Fin.last C.gates.length, y)‖ ^ 2 else (0 : ℝ))
      ≤ (Real.sqrt ε * nm (g2c2_slN η 0) + β + g2c2_dC C η) ^ 2 := by
  set W : Matrix (Reg C.qubits) (Reg C.qubits) ℂ := finiteWordMatrix C.qubits C.gates with hW
  set ψ0 : QState (Reg C.qubits) := g2c2_slN η 0 with hψ0
  set ψm : QState (Reg C.qubits) := g2c2_slN η C.gates.length with hψm
  set leg : QState (Reg C.qubits) := g2c2_legPart C ψ0 with hleg
  set ill : QState (Reg C.qubits) := g2c2_illPart C ψ0 with hill
  have hU : W ∈ Matrix.unitaryGroup (Reg C.qubits) ℂ := by
    rw [hW]
    exact finiteWordMatrix_unitary C.qubits C.gates C.legal

  have hvnill : vn ill = β ^ 2 := by
    rw [hill, g2c2_illPart_vn, hβ2]
    apply Finset.sum_congr rfl
    intro y _
    rw [hψ0, g2c2_slN_zero]
  have hnmill : nm ill = β := by
    have h1 : nm ill ^ 2 = β ^ 2 := by rw [nm_sq, hvnill]
    have h2 : Real.sqrt (nm ill ^ 2) = Real.sqrt (β ^ 2) := congr_arg Real.sqrt h1
    rw [Real.sqrt_sq (nm_nonneg _), Real.sqrt_sq hβ] at h2
    exact h2

  have hα2 : nm leg ^ 2 + β ^ 2 = nm ψ0 ^ 2 := by
    rw [nm_sq, nm_sq, ← hvnill, ← g2c2_leg_ill_vn C ψ0]
  have hαle : nm leg ≤ nm ψ0 := by
    have h1 : nm leg ^ 2 ≤ nm ψ0 ^ 2 := by nlinarith [sq_nonneg β, hα2]
    have h2 : |nm leg| ≤ |nm ψ0| := sq_le_sq.mp h1
    rw [abs_of_nonneg (nm_nonneg _), abs_of_nonneg (nm_nonneg _)] at h2
    exact h2

  have hlegnm : nm (g2c2_proj C.outputWire (W *ᵥ leg))
      ≤ Real.sqrt ε * nm leg := by
    by_cases hα0 : nm leg = 0
    · have hleg0 : leg = 0 := by
        funext y
        have h1 : ‖leg y‖ ^ 2 = 0 := by
          have h2 : vn leg = 0 := by
            rw [← nm_sq, hα0]
            ring
          have h3 : ‖leg y‖ ^ 2 ≤ vn leg := by
            unfold vn
            exact Finset.single_le_sum
              (fun z _ => sq_nonneg (‖leg z‖)) (Finset.mem_univ y)
          linarith [sq_nonneg (‖leg y‖)]
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp h1)
      rw [hleg0, Matrix.mulVec_zero]
      have h5 : g2c2_proj C.outputWire (0 : QState (Reg C.qubits)) = 0 := by
        funext y
        unfold g2c2_proj
        by_cases hy : y C.outputWire <;> simp [hy]
      have h6 : nm (0 : QState (Reg C.qubits)) = 0 := by
        unfold nm
        rw [vn_zero]
        exact Real.sqrt_zero
      rw [h5, h6]
      nlinarith [Real.sqrt_nonneg ε]
    · have hαpos : 0 < nm leg := lt_of_le_of_ne (nm_nonneg _) (Ne.symm hα0)
      set φ : QState (Reg C.qubits) := fun y => leg y / (nm leg : ℂ) with hφ
      have hmul : ((nm leg : ℂ)) • φ = leg := by
        funext y
        show (nm leg : ℂ) * (leg y / (nm leg : ℂ)) = leg y
        rw [mul_div_cancel₀]
        exact_mod_cast (ne_of_gt hαpos)
      have hφleg : QmaInitLegal C φ := by
        intro p hp
        have hpleg : leg p ≠ 0 := by
          intro h0
          have : φ p = 0 := by
            simp [hφ, h0]
          exact hp this
        exact g2c2_legPart_legal C ψ0 p hpleg
      have hφnorm : Normalized φ := by
        unfold Normalized
        have h1 : ∀ y, ‖φ y‖ ^ 2 = ‖leg y‖ ^ 2 / (nm leg : ℝ) ^ 2 := by
          intro y
          show ‖leg y / (nm leg : ℂ)‖ ^ 2 = _
          rw [norm_div, div_pow]
          have hn : ‖((nm leg : ℝ) : ℂ)‖ = nm leg := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact abs_of_nonneg (nm_nonneg _)
          rw [hn]
        rw [Finset.sum_congr rfl (fun y _ => h1 y), ← Finset.sum_div]
        have h2 : (∑ y : Reg C.qubits, ‖leg y‖ ^ 2) = (nm leg) ^ 2 := (nm_sq _).symm
        rw [h2]
        exact div_self (pow_ne_zero 2 (ne_of_gt hαpos))
      have hφacc : qmaHistoryAcceptProb C φ ≤ ε := hsnd φ hφleg hφnorm
      have hφproj : nm (g2c2_proj C.outputWire (W *ᵥ φ)) ^ 2 ≤ ε := by
        have h1 : nm (g2c2_proj C.outputWire (W *ᵥ φ)) ^ 2
            = qmaHistoryAcceptProb C φ := by
          rw [nm_sq, g2c2_proj_vn, hW, g13n_accept_eq]
        rw [h1]
        exact hφacc
      have hφle : nm (g2c2_proj C.outputWire (W *ᵥ φ)) ≤ Real.sqrt ε :=
        (Real.le_sqrt (nm_nonneg _) hε).mpr hφproj
      have hWleg : W *ᵥ leg = ((nm leg : ℂ)) • (W *ᵥ φ) := by
        conv_lhs => rw [← hmul]
        exact Matrix.mulVec_smul W (nm leg : ℂ) φ
      have hproj : g2c2_proj C.outputWire (W *ᵥ leg)
          = ((nm leg : ℂ)) • g2c2_proj C.outputWire (W *ᵥ φ) := by
        rw [hWleg, g2c2_proj_smul]
      rw [hproj]
      show nm (fun y => (nm leg : ℂ) * g2c2_proj C.outputWire (W *ᵥ φ) y) ≤ _
      rw [g13n2_nm_smul]
      have h1 : ‖((nm leg : ℝ) : ℂ)‖ = nm leg := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (nm_nonneg _)
      rw [h1]
      nlinarith [hφle, nm_nonneg (g2c2_proj C.outputWire (W *ᵥ φ))]

  have hillnm : nm (g2c2_proj C.outputWire (W *ᵥ ill)) ≤ β :=
    calc nm (g2c2_proj C.outputWire (W *ᵥ ill))
        ≤ nm (W *ᵥ ill) := g2c2_proj_le _ _
      _ = nm ill := g13n2_unitary_nm hU _
      _ = β := hnmill

  have hψ0split : g2c2_proj C.outputWire (W *ᵥ ψ0)
      = g2c2_proj C.outputWire (W *ᵥ leg) + g2c2_proj C.outputWire (W *ᵥ ill) := by
    have h1 : ψ0 = leg + ill := (g2c2_leg_ill_add C ψ0).symm
    rw [h1, Matrix.mulVec_add, g2c2_proj_add]
  have hψ0nm : nm (g2c2_proj C.outputWire (W *ᵥ ψ0))
      ≤ Real.sqrt ε * nm ψ0 + β := by
    rw [hψ0split]
    have h1 := g13n2_nm_add (g2c2_proj C.outputWire (W *ᵥ leg))
      (g2c2_proj C.outputWire (W *ᵥ ill))
    calc nm (g2c2_proj C.outputWire (W *ᵥ leg)
          + g2c2_proj C.outputWire (W *ᵥ ill))
        ≤ nm (g2c2_proj C.outputWire (W *ᵥ leg))
          + nm (g2c2_proj C.outputWire (W *ᵥ ill)) := h1
      _ ≤ Real.sqrt ε * nm leg + β := add_le_add hlegnm hillnm
      _ ≤ Real.sqrt ε * nm ψ0 + β := by
          nlinarith [hαle, Real.sqrt_nonneg ε]

  set e : QState (Reg C.qubits) := fun y => ψm y - (W *ᵥ ψ0) y with he
  have hdecomp : ψm = (W *ᵥ ψ0) + e := by
    funext y
    simp [e]
  have hψmnm : nm (g2c2_proj C.outputWire ψm)
      ≤ Real.sqrt ε * nm ψ0 + β + g2c2_dC C η := by
    rw [hdecomp, g2c2_proj_add]
    have h1 := g13n2_nm_add (g2c2_proj C.outputWire (W *ᵥ ψ0))
      (g2c2_proj C.outputWire e)
    have h2 : nm (g2c2_proj C.outputWire e) ≤ g2c2_dC C η := by
      have h3 : nm e = g2c2_dC C η := by
        rw [he, hψm, hψ0, hW]
        rfl
      exact le_trans (g2c2_proj_le _ _) (le_of_eq h3)
    calc nm (g2c2_proj C.outputWire (W *ᵥ ψ0) + g2c2_proj C.outputWire e)
        ≤ nm (g2c2_proj C.outputWire (W *ᵥ ψ0))
          + nm (g2c2_proj C.outputWire e) := h1
      _ ≤ (Real.sqrt ε * nm ψ0 + β) + g2c2_dC C η := add_le_add hψ0nm h2

  have hAm : (∑ y : Reg C.qubits,
        if y C.outputWire then ‖η (Fin.last C.gates.length, y)‖ ^ 2 else (0 : ℝ))
      = vn (g2c2_proj C.outputWire ψm) := by
    rw [g2c2_proj_vn, hψm, g2c2_slN_last]
    apply Finset.sum_congr rfl
    intro y _
    rfl
  have hsq : vn (g2c2_proj C.outputWire ψm)
      ≤ (Real.sqrt ε * nm ψ0 + β + g2c2_dC C η) ^ 2 := by
    rw [← nm_sq]
    exact pow_le_pow_left₀ (nm_nonneg _) hψmnm 2
  rw [hAm]
  exact hsq
set_option autoImplicit false
open Matrix
open scoped BigOperators
set_option maxHeartbeats 800000
open scoped BigOperators Classical
open Classical in
open Qatlib
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib

/-- At the prescribed precision, the rounding scale is at most `1 / (2^10 * (m + 1)^3)`. -/
theorem g2c2_kappa_le (n m : ℕ) :
    g13n2_kappa n (3 * (n + m) + 64) ≤ 1 / (2 ^ 10 * ((m + 1 : ℕ) : ℝ) ^ 3) := by
  have hcard : (Fintype.card (Reg n) : ℝ) = (2 : ℝ) ^ n := by
    have h1 : Fintype.card (Reg n) = Fintype.card (Fin n → Bool) := rfl
    rw [h1, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    norm_num [Nat.cast_pow]
  have hκ : g13n2_kappa n (3 * (n + m) + 64) = 1 / (2 : ℝ) ^ (2 * n + 3 * m + 64) := by
    unfold g13n2_kappa
    rw [hcard]
    have step : (2:ℝ) ^ n * (1 / (2:ℝ) ^ (3 * (n + m) + 64))
        = 1 / (2:ℝ) ^ (2 * n + 3 * m + 64) := by
      have hexp : 3 * (n + m) + 64 = n + (2 * n + 3 * m + 64) := by omega
      have hpe : (2:ℝ) ^ (n + (2 * n + 3 * m + 64))
          = (2:ℝ) ^ n * (2:ℝ) ^ (2 * n + 3 * m + 64) := pow_add _ _ _
      rw [hexp, hpe, div_mul_eq_div_mul_one_div]
      have hne : (2:ℝ) ^ n ≠ 0 := by positivity
      rw [← mul_assoc, mul_one_div_cancel hne, one_mul]
    exact step
  rw [hκ]
  have hposL : (0:ℝ) < 2 ^ (2 * n + 3 * m + 64) := by positivity
  have hposR : (0:ℝ) < 2 ^ 10 * ((m + 1 : ℕ) : ℝ) ^ 3 := by positivity
  rw [div_le_div_iff₀ hposL hposR]
  simp only [one_mul]
  have hmlt : (m + 1 : ℕ) ≤ 2 ^ m := by
    have h := Nat.lt_pow_self (show (1:ℕ) < 2 by norm_num) (n := m)
    omega
  have hcube : ((m + 1 : ℕ) : ℝ) ^ 3 ≤ (2 : ℝ) ^ (3 * m) := by
    have h1 : ((m+1:ℕ):ℝ) ≤ (2:ℝ) ^ m := by exact_mod_cast hmlt
    have h2 : ((m+1:ℕ):ℝ) ^ 3 ≤ ((2:ℝ) ^ m) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    have h3 : ((2:ℝ) ^ m) ^ 3 = (2:ℝ) ^ (3 * m) := by
      rw [← pow_mul]
      congr 1
      ring
    linarith
  have hle : (2:ℝ) ^ 10 * ((m + 1 : ℕ) : ℝ) ^ 3 ≤ (2:ℝ) ^ (2 * n + 3 * m + 64) := by
    have h1 : (2:ℝ) ^ 10 * ((m + 1 : ℕ) : ℝ) ^ 3 ≤ (2:ℝ) ^ 10 * (2:ℝ) ^ (3 * m) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    have h2 : (2:ℝ) ^ 10 * (2:ℝ) ^ (3 * m) = (2:ℝ) ^ (3 * m + 10) := by
      rw [pow_add]
      ring
    have h3 : (2:ℝ) ^ (3 * m + 10) ≤ (2:ℝ) ^ (2 * n + 3 * m + 64) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    linarith
  linarith

/-- The stated normalization and small residual assumptions force the boundary difference `s -
d` to be nonnegative. -/
theorem g2c2_sd_nonneg (ν u d s κ : ℝ)
    (hν : 1 ≤ ν) (hu : 0 ≤ u) (hs0 : 0 ≤ s) (hκ0 : 0 ≤ κ)
    (hd : d ≤ ν * (u + κ))
    (hs : 1 ≤ ν ^ 2 * (s + ν * (u + κ)) ^ 2)
    (hκ : κ ≤ 1 / (2 ^ 10 * ν ^ 6))
    (hu2 : u ^ 2 ≤ 1 / (2 ^ 9 * ν ^ 6)) :
    0 ≤ s - d := by
  have hνpos : 0 < ν := lt_of_lt_of_le (by norm_num) hν
  have h4 : (1 / (4 * ν ^ 2)) ^ 2 = 1 / (16 * ν ^ 4) := by
    field_simp; ring
  have h5 : 1 / (2 ^ 9 * ν ^ 6) ≤ (1 / (4 * ν ^ 2)) ^ 2 := by
    rw [h4, div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [one_mul]
    have h10 : (2:ℝ) ^ 9 = 512 := by norm_num
    rw [h10]
    have h1 : (16:ℝ) * ν ^ 4 ≤ (512:ℝ) * ν ^ 6 := by
      have h2 : (16:ℝ) * ν ^ 4 ≤ (16:ℝ) * ν ^ 6 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hν (by norm_num)) (by norm_num)
      have h3 : (16:ℝ) * ν ^ 6 ≤ (512:ℝ) * ν ^ 6 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith
    exact h1
  have hu_le : u ≤ 1 / (4 * ν ^ 2) := by
    have h1 : u ^ 2 ≤ (1 / (4 * ν ^ 2)) ^ 2 := le_trans hu2 h5
    have h2 : Real.sqrt (u ^ 2) ≤ Real.sqrt ((1 / (4 * ν ^ 2)) ^ 2) := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq hu, Real.sqrt_sq (by positivity)] at h2
    exact h2
  have hκ_le : κ ≤ 1 / (4 * ν ^ 2) := by
    have h1 : 1 / (2 ^ 10 * ν ^ 6) ≤ 1 / (4 * ν ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      simp only [one_mul]
      have h10 : (2:ℝ) ^ 10 = 1024 := by norm_num
      rw [h10]
      have h2 : (4:ℝ) * ν ^ 2 ≤ (4:ℝ) * ν ^ 6 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hν (by norm_num)) (by norm_num)
      have h3 : (4:ℝ) * ν ^ 6 ≤ (1024:ℝ) * ν ^ 6 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith
    linarith
  have huk : u + κ ≤ 1 / (2 * ν ^ 2) := by
    have h1 : 1 / (4 * ν ^ 2) + 1 / (4 * ν ^ 2) = 1 / (2 * ν ^ 2) := by
      field_simp; ring
    linarith
  have hX2 : (1:ℝ) / ν ^ 2 ≤ (s + ν * (u + κ)) ^ 2 := by
    have h1 : (1:ℝ) / ν ^ 2 ≤ ν ^ 2 * (s + ν * (u + κ)) ^ 2 / ν ^ 2 :=
      div_le_div_of_nonneg_right hs (by positivity)
    have h2 : ν ^ 2 * (s + ν * (u + κ)) ^ 2 / ν ^ 2 = (s + ν * (u + κ)) ^ 2 := by
      field_simp
    rw [h2] at h1
    exact h1
  have hX0 : 0 ≤ s + ν * (u + κ) := by
    have h1 : 0 ≤ ν * (u + κ) := mul_nonneg (le_of_lt hνpos) (add_nonneg hu hκ0)
    nlinarith
  have hX : 1 / ν ≤ s + ν * (u + κ) := by
    have h1 : 0 ≤ 1 / ν := by positivity
    have h3 : (1 / ν) ^ 2 ≤ (s + ν * (u + κ)) ^ 2 := by
      have h4' : (1 / ν) ^ 2 = 1 / ν ^ 2 := by field_simp
      rw [h4']
      exact hX2
    have h5' : Real.sqrt ((1 / ν) ^ 2) ≤ Real.sqrt ((s + ν * (u + κ)) ^ 2) :=
      Real.sqrt_le_sqrt h3
    rw [Real.sqrt_sq h1, Real.sqrt_sq hX0] at h5'
    exact h5'
  have hnu : ν * (u + κ) ≤ 1 / (2 * ν) := by
    have h1 : ν * (u + κ) ≤ ν * (1 / (2 * ν ^ 2)) :=
      mul_le_mul_of_nonneg_left huk (le_of_lt hνpos)
    have h2 : ν * (1 / (2 * ν ^ 2)) = 1 / (2 * ν) := by
      field_simp
    linarith
  have hfin : (0:ℝ) ≤ 1 / ν - 2 * (ν * (u + κ)) := by
    have h1 : 2 * (ν * (u + κ)) ≤ 2 * (1 / (2 * ν)) :=
      mul_le_mul_of_nonneg_left hnu (by norm_num)
    have h2 : (1:ℝ) / ν - 2 * (1 / (2 * ν)) = 0 := by
      field_simp; ring
    linarith
  have hmid : 1 / ν - 2 * (ν * (u + κ)) ≤ s - d := by
    linarith
  linarith [hfin, hmid]

open Classical in

/-- The rounded history energy is at least half the total squared residual minus the rounding
correction, plus the initialization violation mass and final rejecting mass. -/
theorem g2c2_energy_bound (C : QmaHistoryCircuit) (b : ℕ)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) (hη : Normalized η) :
    (1 / 2 : ℝ) * (∑ i ∈ Finset.range C.gates.length, g2c2_res C b η i ^ 2)
      - (g13n2_kappa C.qubits b + g13n2_kappa C.qubits b ^ 2 / 2)
      + (∑ y : Reg C.qubits,
          if g2c2_illAt C y then ‖η ((0 : Fin (C.gates.length + 1)), y)‖ ^ 2 else (0 : ℝ))
      + (∑ y : Reg C.qubits, ‖η (Fin.last C.gates.length, y)‖ ^ 2)
      - (∑ y : Reg C.qubits,
          if y C.outputWire then ‖η (Fin.last C.gates.length, y)‖ ^ 2 else (0 : ℝ))
      ≤ qmaEnergy (qmaHistoryHamiltonian C (qmaRoundedGates C b)) η := by
  rw [g13n_energy_split]
  have hprop := g13n2_prop_lower_C C η hη b
  have hres := g2c2_res_sq_sum C b η
  have hin := g2c2_in_mass C η
  have hout := g13n_out_energy_sub C.qubits C.gates.length C.outputWire η
  have hprop' : (1 / 2 : ℝ) * (∑ i ∈ Finset.range C.gates.length, g2c2_res C b η i ^ 2)
      - (g13n2_kappa C.qubits b + g13n2_kappa C.qubits b ^ 2 / 2)
      ≤ ∑ i : Fin C.gates.length,
          qmaEnergy (qmaPropTerm C.qubits C.gates.length (qmaRoundedGates C b) i) η := by
    rw [← hres]
    exact hprop
  linarith

/-- A soundness bound `ε` on all legal normalized inputs yields energy at least `(1 - 2 * ε) /
(2^10 * (C.gates.length + 1)^3) - qmaTiny (C.qubits + C.gates.length + 2)` for every
normalized vector of the prescribed rounded history Hamiltonian. This is a rounded
variational form of the soundness direction in [Kempe et al., Lemma
2][KempeKitaevRegev2006]. -/
theorem g2c2_clause2 (C : QmaHistoryCircuit) (ε : ℝ)
    (hsnd : ∀ φ : QState (Reg C.qubits), QmaInitLegal C φ → Normalized φ →
      qmaHistoryAcceptProb C φ ≤ ε)
    (η : QState (Fin (C.gates.length + 1) × Reg C.qubits)) (hη : Normalized η) :
    (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3)
      - qmaTiny (C.qubits + C.gates.length + 2)
      ≤ qmaEnergy (qmaHistoryHamiltonian C
          (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))) η := by
  set b : ℕ := 3 * (C.qubits + C.gates.length) + 64 with hb
  set ρ : ℝ := Real.sqrt ε with hρdef
  set ν : ℝ := Real.sqrt (C.gates.length + 1) with hνdef
  set u : ℝ := g2c2_u C b η with hudef
  set β : ℝ := g2c2_beta C η with hβdef
  set s : ℝ := nm (g2c2_slN η 0) with hsdef
  set d : ℝ := g2c2_dC C η with hddef
  set κ : ℝ := g13n2_kappa C.qubits b with hκdef

  have hEbound : (1 / 2 : ℝ) * u ^ 2
      - (κ + κ ^ 2 / 2)
      + β ^ 2
      + (∑ y : Reg C.qubits, ‖η (Fin.last C.gates.length, y)‖ ^ 2)
      - (∑ y : Reg C.qubits,
          if y C.outputWire then ‖η (Fin.last C.gates.length, y)‖ ^ 2 else (0 : ℝ))
      ≤ qmaEnergy (qmaHistoryHamiltonian C (qmaRoundedGates C b)) η := by
    have h := g2c2_energy_bound C b η hη
    rw [← g2c2_u_sq C b η, ← g2c2_beta_sq C η, ← hudef, ← hβdef, ← hκdef] at h
    exact h
  have htiny : κ + κ ^ 2 / 2 ≤ qmaTiny (C.qubits + C.gates.length + 2) := by
    have h := g2c2_tiny_absorb C.qubits C.gates.length
    rw [← hb, ← hκdef] at h
    exact h
  have hout0 : 0 ≤ qmaEnergy (qmaOutTerm C.qubits C.gates.length C.outputWire) η := by
    rw [g13n_out_energy]
    refine Finset.sum_nonneg (fun y _ => ?_)
    by_cases hy : y C.outputWire <;> simp [hy]
  have houtE : qmaEnergy (qmaOutTerm C.qubits C.gates.length C.outputWire) η
      = (∑ y : Reg C.qubits, ‖η (Fin.last C.gates.length, y)‖ ^ 2)
        - (∑ y : Reg C.qubits,
            if y C.outputWire then ‖η (Fin.last C.gates.length, y)‖ ^ 2 else (0 : ℝ)) :=
    g13n_out_energy_sub C.qubits C.gates.length C.outputWire η
  have hSm_nn : 0 ≤ ∑ y : Reg C.qubits, ‖η (Fin.last C.gates.length, y)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hβ_nn : 0 ≤ β ^ 2 := sq_nonneg _

  by_cases hneg : ε < 0
  · obtain ⟨φ, hφl, hφn⟩ := g2c2_exists_legal C
    linarith [hsnd φ hφl hφn, g2c2_accept_nonneg C φ]
  by_cases hhalf : 1 / 2 ≤ ε
  · have hT0 : (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · positivity
    have hEge : - (κ + κ ^ 2 / 2)
        ≤ qmaEnergy (qmaHistoryHamiltonian C (qmaRoundedGates C b)) η := by
      have h1 : 0 ≤ (1 / 2 : ℝ) * u ^ 2 := by positivity
      linarith [hEbound, hβ_nn, hSm_nn, houtE, hout0, h1]
    linarith [hEge, htiny, hT0]
  · have hε0 : 0 ≤ ε := not_lt.mp hneg
    have hε12 : ε < 1 / 2 := not_le.mp hhalf

    have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg ε
    have hρ2 : ρ ^ 2 = ε := Real.sq_sqrt hε0
    have hν1 : 1 ≤ ν := by
      rw [hνdef]
      refine (Real.le_sqrt (by norm_num) (by positivity)).mpr ?_
      have hkey : (1:ℝ) ^ 2 ≤ (C.gates.length + 1) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le C.gates.length)
      exact hkey
    have hν2 : ν ^ 2 = (C.gates.length + 1) := by
      rw [hνdef, Real.sq_sqrt]
      exact_mod_cast Nat.zero_le (C.gates.length + 1)
    have hν6 : ν ^ 6 = (C.gates.length + 1) ^ 3 := by
      rw [show (6:ℕ) = 2 * 3 by norm_num, pow_mul, hν2]
    have hu0 : 0 ≤ u := by rw [hudef]; exact g2c2_u_nonneg C b η
    have hβ0 : 0 ≤ β := by rw [hβdef]; exact g2c2_beta_nonneg C η
    have hs0 : 0 ≤ s := by rw [hsdef]; exact nm_nonneg _
    have hκ0 : 0 ≤ κ := by rw [hκdef]; exact g13n2_kappa_nonneg _ _

    have hdC : d ≤ ν * (u + κ) := by
      rw [hddef, hudef, hκdef, hνdef]
      exact g2c2_dist_C C b η hη (g2c2_u C b η) (g2c2_u_nonneg C b η) (g2c2_u_sq C b η)
    have hsnorm : 1 ≤ ν ^ 2 * (s + ν * (u + κ)) ^ 2 := by
      have h := g2c2_norm_C C b η hη (g2c2_u C b η) (g2c2_u_nonneg C b η) (g2c2_u_sq C b η)
      push_cast at h
      rw [← hνdef, ← hν2, ← hsdef, ← hudef, ← hκdef] at h
      exact h
    have hκle0 : g13n2_kappa C.qubits b
        ≤ 1 / (2 ^ 10 * ((C.gates.length + 1 : ℕ) : ℝ) ^ 3) := by
      have h := g2c2_kappa_le C.qubits C.gates.length
      rw [← hb] at h
      exact h
    have hκle : κ ≤ 1 / (2 ^ 10 * ν ^ 6) := by
      rw [hκdef, hν6]
      have h := hκle0
      push_cast at h
      exact h

    by_cases h1 : (1 / 2 : ℝ) * u ^ 2 < (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3)
    · by_cases h2 : β ^ 2 < (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3)
      · have h5den : (2 ^ 10 * (C.gates.length + 1) ^ 3 : ℝ) = 2 ^ 10 * ν ^ 6 := by
          rw [hν6]
        have hTle : (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3)
            ≤ 1 / (2 ^ 10 * ν ^ 6) := by
          rw [h5den]
          have h1' : 1 - 2 * ε ≤ (1:ℝ) := by linarith
          have h2' : (0:ℝ) < 2 ^ 10 * ν ^ 6 := by positivity
          exact div_le_div_of_nonneg_right h1' (le_of_lt h2')
        have hu2' : u ^ 2 ≤ 1 / (2 ^ 9 * ν ^ 6) := by
          have h3 : u ^ 2 < 2 * ((1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3)) := by
            linarith
          have h4' : (2:ℝ) * ((1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3))
              ≤ 2 * (1 / (2 ^ 10 * ν ^ 6)) :=
            mul_le_mul_of_nonneg_left hTle (by norm_num)
          have h5' : (2:ℝ) * (1 / (2 ^ 10 * ν ^ 6)) = 1 / (2 ^ 9 * ν ^ 6) := by
            have h6' : (2:ℝ) ^ 10 = 2 * 2 ^ 9 := by norm_num
            rw [h6', mul_one_div]
            field_simp
          have h6' : u ^ 2 < 1 / (2 ^ 9 * ν ^ 6) := by
            linarith
          exact le_of_lt h6'
        have hsd : 0 ≤ s - d :=
          g2c2_sd_nonneg ν u d s κ hν1 hu0 hs0 hκ0 hdC hsnorm hκle hu2'

        have hA : (∑ y : Reg C.qubits,
              if y C.outputWire then ‖η (Fin.last C.gates.length, y)‖ ^ 2 else (0 : ℝ))
            ≤ (Real.sqrt ε * nm (g2c2_slN η 0) + g2c2_beta C η + g2c2_dC C η) ^ 2 :=
          g2c2_accept_mass C ε hε0 hsnd η hη (g2c2_beta C η)
            (g2c2_beta_nonneg C η) (g2c2_beta_sq C η)

        have hSm : (s - d) ^ 2 ≤ ∑ y : Reg C.qubits, ‖η (Fin.last C.gates.length, y)‖ ^ 2 := by
          have hrev : |nm (g2c2_slN η C.gates.length)
              - nm (finiteWordMatrix C.qubits C.gates *ᵥ g2c2_slN η 0)| ≤ d := by
            rw [hddef]
            exact g2c2_nm_rev _ _
          have hnmW : nm (finiteWordMatrix C.qubits C.gates *ᵥ g2c2_slN η 0) = s := by
            rw [hsdef]
            exact g13n2_unitary_nm
              (finiteWordMatrix_unitary C.qubits C.gates C.legal) _
          rw [hnmW] at hrev
          have hge : s - d ≤ nm (g2c2_slN η C.gates.length) := by
            have h2' := abs_le.mp hrev
            nlinarith
          have h1' : (s - d) ^ 2 ≤ nm (g2c2_slN η C.gates.length) ^ 2 :=
            pow_le_pow_left₀ hsd hge 2
          have h2' : nm (g2c2_slN η C.gates.length) ^ 2
              = ∑ y : Reg C.qubits, ‖η (Fin.last C.gates.length, y)‖ ^ 2 := by
            rw [nm_sq, g2c2_slN_last, g13n2_sl_vn]
          linarith

        have hcore : (1 - 2 * ρ ^ 2) / (2 ^ 10 * ν ^ 6)
            ≤ (1 / 2 : ℝ) * u ^ 2 + (s - d) ^ 2 - (ρ * s + β + d) ^ 2 + β ^ 2 := by
          refine g2c2_scale_core ν ρ u d β s κ hν1 hρ0 ?_ hu0 hβ0 hs0 hκ0 hdC hsnorm hκle ?_
          · rw [hρ2]
            exact le_of_lt hε12
          · have hT' : (1 - 2 * ρ ^ 2) / (2 ^ 10 * ν ^ 6)
                = (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3) := by
              rw [hρ2, h5den]
            rw [hT']
            exact ⟨h1, h2⟩

        have hTge : (1 - 2 * ρ ^ 2) / (2 ^ 10 * ν ^ 6)
            ≥ (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3) := by
          rw [hρ2, h5den]
        have hsum : (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3)
            ≤ (1 / 2 : ℝ) * u ^ 2 + (s - d) ^ 2 - (ρ * s + β + d) ^ 2 + β ^ 2 :=
          le_trans hTge hcore
        have hA' : (∑ y : Reg C.qubits,
              if y C.outputWire then ‖η (Fin.last C.gates.length, y)‖ ^ 2 else (0 : ℝ))
            ≤ (ρ * s + β + d) ^ 2 := by
          rw [hsdef, hβdef, hddef, hρdef]
          exact hA
        linarith [hEbound, hSm, hA', hsum, htiny]
      · have hβge : (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3) ≤ β ^ 2 :=
          not_lt.mp h2
        have h1' : 0 ≤ (1 / 2 : ℝ) * u ^ 2 := by positivity
        linarith [hEbound, hSm_nn, houtE, hout0, h1', hβge, htiny]
    · have huge : (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3)
          ≤ (1 / 2 : ℝ) * u ^ 2 := not_lt.mp h1
      linarith [hEbound, hβ_nn, hSm_nn, houtE, hout0, huge, htiny]

/-- Packages the rounded history Hamiltonian's NO energy lower bound as an implication from a
soundness bound on all legal normalized inputs. -/
theorem g2c2_clause2_frozen (C : QmaHistoryCircuit) :
    (∀ ε : ℝ,
      (∀ φ : QState (Reg C.qubits), QmaInitLegal C φ → Normalized φ →
        qmaHistoryAcceptProb C φ ≤ ε) →
      ∀ η : QState (Fin (C.gates.length + 1) × Reg C.qubits), Normalized η →
        (1 - 2 * ε) / (2 ^ 10 * (C.gates.length + 1) ^ 3)
          - qmaTiny (C.qubits + C.gates.length + 2)
          ≤ qmaEnergy (qmaHistoryHamiltonian C
              (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))) η) := by
  intro ε hsnd η hη
  exact g2c2_clause2 C ε hsnd η hη
end Qatlib.Concepts.QmaCompleteness.HistoryHam
