/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.CoherentSimulation
import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorConsumers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Nat.Size
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary

/-!
# Coherent Taylor arithmetic and circuit resources

The module supplies bounded-scale amplification budgets and workspace error estimates, dyadic
quantization bounds, and binary arithmetic with explicit Boolean-operation counts. It groups
grid-time matrix products by sorted words with multiplicities and transports this grouping
through a truncated Taylor sum. Three-CNOT swaps and phase words provide explicit finite-gate
implementations of register exchanges and phases on a clean wire.

These constructions belong to the formalization of [YoderLowChuang2014].

## Main statements

* `boundedScale_workspace_error_and_cost`: amplified workspace accuracy and exact circuit
  counts.
* `binaryFactorial_correct`: factorial computation with size and operation bounds.
* `taylor_gridCube_transport`: regrouping of the finite Taylor expression.
* `exchangeWord_correct`: register-prefix exchange in `3 * k` gates.
* `boundedCleanPhaseWord_resources`: a phase word with at most nine gates and no queries.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.RandCompile.ChannelBudget

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib Matrix Encoding SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator

/-- The base-three ceiling logarithm of `2 * bound + 1`, used as the amplification level count. -/
def boundedScaleLevels (bound : ℕ) : ℕ := Nat.clog 3 (2 * bound + 1)

/-- Twice the real-valued bound is at most three raised to the selected amplification level
count. -/
private theorem twice_bound_le_three_pow (bound : ℕ) :
    2 * (bound : ℝ) ≤ (3 : ℝ) ^ boundedScaleLevels bound := by
  have hp := Nat.le_pow_clog (by norm_num : 1 < (3 : ℕ)) (2 * bound + 1)
  exact_mod_cast (show 2 * bound ≤ 3 ^ boundedScaleLevels bound from
    (Nat.le_succ _).trans hp)

/-- Three raised to the selected amplification level count is at most `6 * bound + 3`. -/
theorem boundedScale_degree_le (bound : ℕ) :
    3 ^ boundedScaleLevels bound ≤ 6 * bound + 3 := by
  by_cases hb : bound = 0
  · subst bound
    norm_num [boundedScaleLevels]
  · have harg : 1 < 2 * bound + 1 := by omega
    have hk : 0 < boundedScaleLevels bound :=
      Nat.clog_pos (by norm_num) harg
    have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (3 : ℕ)) harg
    have he : 3 ^ boundedScaleLevels bound =
        3 ^ (boundedScaleLevels bound).pred * 3 := by
      rw [← pow_succ, show (boundedScaleLevels bound).pred + 1 =
        boundedScaleLevels bound from by
          simpa only [Nat.succ_eq_add_one] using! Nat.succ_pred_eq_of_pos hk]
    rw [he]
    change 3 ^ (boundedScaleLevels bound).pred < 2 * bound + 1 at hp
    nlinarith

/-- The selected level count is admissible for every nonnegative scale `s` bounded by `bound`. -/
theorem boundedScaleLevels_admissible (s : ℝ) (bound : ℕ)
    (hs : 0 ≤ s) (hbound : s ≤ bound) :
    generalScaleAdmissible s (boundedScaleLevels bound) := by
  refine ⟨hs, ?_⟩
  have hangle := (generalScaleAngle_bounds (boundedScaleLevels bound)).1.le
  have hsin := Real.sin_le hangle
  have hpow := twice_bound_le_three_pow bound
  have hpi := Real.pi_lt_four
  have hd : (0 : ℝ) < 2 * 3 ^ boundedScaleLevels bound := by positivity
  calc
    s * Real.sin (generalScaleAngle (boundedScaleLevels bound)) ≤
        s * generalScaleAngle (boundedScaleLevels bound) :=
      mul_le_mul_of_nonneg_left hsin hs
    _ ≤ 1 := by
      unfold generalScaleAngle
      rw [← mul_div_assoc, div_le_iff₀ hd]
      nlinarith

/-- The block-encoding error budget `δ ^ 2 / (2 * 15 ^ boundedScaleLevels bound)`. -/
noncomputable def boundedScaleBlockBudget (bound : ℕ) (δ : ℝ) : ℝ :=
  δ ^ 2 / (2 * (15 : ℝ) ^ boundedScaleLevels bound)

/-- For nonnegative `δ`, the workspace error expression obtained from the selected block budget
simplifies to `δ`. -/
theorem boundedScaleBlockBudget_sqrt (bound : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    Real.sqrt (2 * ((15 : ℝ) ^ boundedScaleLevels bound *
      boundedScaleBlockBudget bound δ)) = δ := by
  have hp : (15 : ℝ) ^ boundedScaleLevels bound ≠ 0 := by positivity
  have he : 2 * ((15 : ℝ) ^ boundedScaleLevels bound *
      boundedScaleBlockBudget bound δ) = δ ^ 2 := by
    unfold boundedScaleBlockBudget
    field_simp
  rw [he, Real.sqrt_sq hδ]

/-- Under the unitary, circuit, scale, and block-encoding hypotheses, the amplified word is well
formed, has the stated exact query and gate counts for itself and its adjoint, and has
workspace error at most `δ` times the input norm. -/
theorem boundedScale_workspace_error_and_cost
    {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (O : Matrix H H ℂ) (R : Matrix H I ℂ) (cs : List (AdjointStep H))
    (V : Matrix I I ℂ) (s δ : ℝ) (bound : ℕ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hcs : WellFormedAdjointCircuit cs)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hs : 0 ≤ s) (hbound : s ≤ bound) (hδ : 0 ≤ δ)
    (henc : BlockEncoding V (evaluate O cs) R R s (boundedScaleBlockBudget bound δ)) :
    let k := boundedScaleLevels bound
    let word := generalScaleAmplifyWord s k R cs
    WellFormedAdjointCircuit word ∧
      adjointQueryCount word = 3 ^ k * adjointQueryCount cs ∧
      adjointGateCount word + 2 = 3 ^ k * (adjointGateCount cs + 3) ∧
      adjointQueryCount (adjointCircuit word) = 3 ^ k * adjointQueryCount cs ∧
      adjointGateCount (adjointCircuit word) + 2 =
        3 ^ k * (adjointGateCount cs + 3) ∧
      ∀ ψ : QState I,
        ‖toEuclidean_fromVec
          (evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) word *ᵥ
            (scaleEightFrame R *ᵥ ψ) - scaleEightFrame R *ᵥ (V *ᵥ ψ))‖ ≤
          δ * ‖toEuclidean_fromVec ψ‖ := by
  have ha := boundedScaleLevels_admissible s bound hs hbound
  obtain ⟨hwf, hq, hg⟩ :=
    generalScaleAmplifyWord_counts ha R cs henc.right_isometry hcs
  refine ⟨hwf, hq, hg, by simpa using! hq, by simpa using! hg, ?_⟩
  intro ψ
  have he := generalScale_workspace_bound O R cs V (boundedScaleBlockBudget bound δ)
    hO hcs hV ha henc ψ
  simpa only [boundedScaleBlockBudget_sqrt bound δ hδ] using! he

/-- Dyadic quantization to `bits` fractional bits has absolute error strictly less than `(1 / 2)
^ bits`. -/
theorem quantizedReal_error (θ : ℝ) (bits : ℕ) :
    |θ - quantizedReal θ bits| < (1 / 2 : ℝ) ^ bits := by
  have hp : (0 : ℝ) < 2 ^ bits := by positivity
  have hlo := Int.floor_le (θ * 2 ^ bits)
  have hhi := Int.lt_floor_add_one (θ * 2 ^ bits)
  have hnonneg : 0 ≤ θ - quantizedReal θ bits := by
    unfold quantizedReal
    have := (div_le_iff₀ hp).2 hlo
    linarith
  rw [abs_of_nonneg hnonneg]
  have he : θ - quantizedReal θ bits < 1 / (2 : ℝ) ^ bits := by
    unfold quantizedReal
    apply (lt_div_iff₀ hp).2
    field_simp at *
    nlinarith
  simpa only [_root_.one_div_pow] using! he

/-- Replacing an angle by its dyadic quantization changes both its sine and cosine by strictly
less than `(1 / 2) ^ bits`. -/
theorem quantizedReal_trig_error (θ : ℝ) (bits : ℕ) :
    |Real.sin θ - Real.sin (quantizedReal θ bits)| < (1 / 2 : ℝ) ^ bits ∧
      |Real.cos θ - Real.cos (quantizedReal θ bits)| < (1 / 2 : ℝ) ^ bits := by
  exact ⟨(Real.abs_sin_sub_sin_le _ _).trans_lt (quantizedReal_error θ bits),
    (Real.abs_cos_sub_cos_le _ _).trans_lt (quantizedReal_error θ bits)⟩

/-- For nonnegative `a` and `b`, the real cast of the maximum of their natural ceilings plus one
and four is at most `max (a + 2) (max 4 (b + 2))`. -/
theorem max_natCeil_degree_upper (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((max (⌈a⌉₊ + 1) (max 4 (⌈b⌉₊ + 1)) : ℕ) : ℝ) ≤
      max (a + 2) (max 4 (b + 2)) := by
  push_cast
  apply max_le_max
  · linarith [Nat.ceil_lt_add_one ha]
  · apply max_le_max le_rfl
    linarith [Nat.ceil_lt_add_one hb]

/-- The natural number represented by a list of Boolean bits in least-significant-bit-first
order. -/
def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * binaryValue bs

/-- A binary computation result consisting of its output bits and a recorded Boolean-operation
count. -/
structure BinaryRun where
  bits : List Bool
  booleanOps : ℕ
  deriving Repr, DecidableEq

/-- The sum bit of a full adder, given by the exclusive-or of the two input bits and carry bit. -/
def fullAdderSum (a b carry : Bool) : Bool := xor (xor a b) carry

/-- The carry bit of a full adder, true exactly when at least two of the three input bits are
true. -/
def fullAdderCarry (a b carry : Bool) : Bool :=
  (a && b) || (a && carry) || (b && carry)

/-- The full-adder sum bit plus twice the carry bit equals the sum of the three input bits as
natural numbers. -/
theorem fullAdder_value (a b carry : Bool) :
    (fullAdderSum a b carry).toNat + 2 * (fullAdderCarry a b carry).toNat =
      a.toNat + b.toNat + carry.toNat := by
  cases a <;> cases b <;> cases carry <;> decide

/-- Recursive binary addition with an input carry, returning the output bit list and charging
seven Boolean operations per processed position. -/
def binaryAdd : List Bool → List Bool → Bool → BinaryRun
  | [], [], carry => ⟨[carry], 0⟩
  | a :: as, [], carry =>
      let rest := binaryAdd as [] (fullAdderCarry a false carry)
      ⟨fullAdderSum a false carry :: rest.bits, rest.booleanOps + 7⟩
  | [], b :: bs, carry =>
      let rest := binaryAdd [] bs (fullAdderCarry false b carry)
      ⟨fullAdderSum false b carry :: rest.bits, rest.booleanOps + 7⟩
  | a :: as, b :: bs, carry =>
      let rest := binaryAdd as bs (fullAdderCarry a b carry)
      ⟨fullAdderSum a b carry :: rest.bits, rest.booleanOps + 7⟩
termination_by as bs _ => as.length + bs.length

/-- Binary addition represents the input sum plus carry, has output length `max as.length
bs.length + 1`, and records `7 * max as.length bs.length` Boolean operations. -/
theorem binaryAdd_correct (as bs : List Bool) (carry : Bool) :
    binaryValue (binaryAdd as bs carry).bits =
      binaryValue as + binaryValue bs + carry.toNat ∧
    (binaryAdd as bs carry).bits.length = max as.length bs.length + 1 ∧
    (binaryAdd as bs carry).booleanOps = 7 * max as.length bs.length := by
  cases as with
  | nil =>
      cases bs with
      | nil => simp [binaryAdd, binaryValue]
      | cons b bs =>
          have ih := binaryAdd_correct [] bs (fullAdderCarry false b carry)
          have hv := fullAdder_value false b carry
          simp only [binaryAdd, binaryValue, List.length_cons, List.length_nil,
            Bool.toNat_false] at *
          omega
  | cons a as =>
      cases bs with
      | nil =>
          have ih := binaryAdd_correct as [] (fullAdderCarry a false carry)
          have hv := fullAdder_value a false carry
          simp only [binaryAdd, binaryValue, List.length_cons, List.length_nil,
            Bool.toNat_false] at *
          omega
      | cons b bs =>
          have ih := binaryAdd_correct as bs (fullAdderCarry a b carry)
          have hv := fullAdder_value a b carry
          simp only [binaryAdd, binaryValue, List.length_cons] at *
          omega
termination_by as.length + bs.length

/-- Recursive shift-and-add multiplication of two least-significant-bit-first bit lists,
recording the operation counts of its additions. -/
def binaryMultiply : List Bool → List Bool → BinaryRun
  | [], _ => ⟨[], 0⟩
  | a :: as, bs =>
      let rest := binaryMultiply as bs
      if a then
        let added := binaryAdd bs (false :: rest.bits) false
        ⟨added.bits, rest.booleanOps + added.booleanOps⟩
      else ⟨false :: rest.bits, rest.booleanOps⟩

/-- Binary multiplication represents the product, uses at most `2 * as.length + bs.length`
output bits, and records at most `7 * as.length * (2 * as.length + bs.length + 1)` Boolean
operations. -/
theorem binaryMultiply_correct (as bs : List Bool) :
    binaryValue (binaryMultiply as bs).bits = binaryValue as * binaryValue bs ∧
    (binaryMultiply as bs).bits.length ≤ 2 * as.length + bs.length ∧
    (binaryMultiply as bs).booleanOps ≤
      7 * as.length * (2 * as.length + bs.length + 1) := by
  induction as with
  | nil => simp [binaryMultiply, binaryValue]
  | cons a as ih =>
      have ha := binaryAdd_correct bs (false :: (binaryMultiply as bs).bits) false
      cases a <;>
        simp only [binaryMultiply, Bool.false_eq_true, ↓reduceIte, binaryValue,
          Bool.toNat_false, Bool.toNat_true, List.length_cons, zero_add] at *
      · refine ⟨by nlinarith [ih.1], by omega, ?_⟩
        nlinarith [ih.2.2]
      · refine ⟨by nlinarith [ih.1, ha.1], by omega, ?_⟩
        have hm : max bs.length ((binaryMultiply as bs).bits.length + 1) ≤
            2 * as.length + bs.length + 1 := by omega
        nlinarith [ih.2.2, ha.2.2]

/-- The binary value of the canonical bit list of a natural number is that number. -/
theorem binaryValue_bits (n : ℕ) : binaryValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [Nat.zero_bits, binaryValue]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp only [binaryValue, ih, Nat.bit_val]
      omega

/-- Recursive factorial computation using binary multiplication and accumulating the recorded
Boolean-operation counts. -/
def binaryFactorial : ℕ → BinaryRun
  | 0 => ⟨[true], 0⟩
  | n + 1 =>
      let rest := binaryFactorial n
      let product := binaryMultiply (n + 1).bits rest.bits
      ⟨product.bits, rest.booleanOps + product.booleanOps⟩

/-- Binary factorial represents `n.factorial`, uses at most `n * (n + 1) + 1` output bits, and
records at most `28 * n * (n + 1) ^ 3` Boolean operations. -/
theorem binaryFactorial_correct (n : ℕ) :
    binaryValue (binaryFactorial n).bits = n.factorial ∧
      (binaryFactorial n).bits.length ≤ n * (n + 1) + 1 ∧
      (binaryFactorial n).booleanOps ≤ 28 * n * (n + 1) ^ 3 := by
  induction n with
  | zero => norm_num [binaryFactorial, binaryValue]
  | succ n ih =>
      have hm := binaryMultiply_correct (n + 1).bits (binaryFactorial n).bits
      have hbits : (n + 1).bits.length ≤ n + 1 := by
        rw [Nat.size_eq_bits_len]
        exact Nat.size_le.2 (Nat.lt_two_pow_self)
      simp only [binaryFactorial]
      refine ⟨?_, ?_, ?_⟩
      · rw [hm.1, binaryValue_bits, ih.1, Nat.factorial_succ]
      · nlinarith [hm.2.1, ih.2.1]
      · have hcost : (binaryMultiply (n + 1).bits (binaryFactorial n).bits).booleanOps ≤
            7 * (n + 1) * (2 * (n + 1) + (n * (n + 1) + 1) + 1) := by
          refine hm.2.2.trans ?_
          gcongr
          exact ih.2.1
        nlinarith [ih.2.2]

/-- The list of grid indices obtained by sorting the values of `times` in increasing order. -/
def orderedGridTimes {l M : ℕ} (times : Fin l → Fin M) : List (Fin M) :=
  (List.ofFn times).mergeSort (fun a b => a ≤ b)

/-- Sorting the grid times gives a permutation of their original list. -/
theorem orderedGridTimes_perm {l M : ℕ} (times : Fin l → Fin M) :
    (orderedGridTimes times).Perm (List.ofFn times) :=
  List.mergeSort_perm _ _

/-- Sorting the grid times preserves the number of occurrences of each grid index. -/
theorem orderedGridTimes_count {l M : ℕ} (times : Fin l → Fin M) (j : Fin M) :
    (orderedGridTimes times).count j = (List.ofFn times).count j :=
  (orderedGridTimes_perm times).count_eq j

/-- The sum over all grid-time assignments of the matrix products in reverse sorted time order. -/
noncomputable def gridCube {I : Type} [Fintype I] [DecidableEq I]
    {M : ℕ} (H : Fin M → Matrix I I ℂ) (l : ℕ) : Matrix I I ℂ :=
  ∑ times : Fin l → Fin M, ((orderedGridTimes times).map H).reverse.prod

/-- The number of grid-time assignments whose sorted index list equals `word`. -/
def gridWordMultiplicity (l M : ℕ) (word : List (Fin M)) : ℕ :=
  (Finset.univ.filter (fun times : Fin l → Fin M => orderedGridTimes times = word)).card

/-- Summing multiplicities over all attainable sorted words gives the total number `M ^ l` of
grid-time assignments. -/
theorem gridWordMultiplicity_total (l M : ℕ) :
    (∑ word ∈ Finset.univ.image (fun times : Fin l → Fin M => orderedGridTimes times),
      gridWordMultiplicity l M word) = M ^ l := by
  classical
  unfold gridWordMultiplicity
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun times : Fin l → Fin M =>
    orderedGridTimes times) (s := Finset.univ)
    (fun _ ht => Finset.mem_image_of_mem _ ht)]
  simp

/-- The sum over attainable sorted grid words of their reverse-ordered matrix products weighted
by their multiplicities. -/
noncomputable def canonicalGridCube {I : Type} [Fintype I] [DecidableEq I]
    {M : ℕ} (H : Fin M → Matrix I I ℂ) (l : ℕ) : Matrix I I ℂ :=
  ∑ word ∈ Finset.univ.image (fun times : Fin l → Fin M => orderedGridTimes times),
    gridWordMultiplicity l M word • (word.map H).reverse.prod

/-- Grouping grid-time assignments by their sorted words gives the canonical
multiplicity-weighted matrix sum. -/
theorem gridCube_eq_canonicalGridCube
    {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}
    (H : Fin M → Matrix I I ℂ) (l : ℕ) :
    gridCube H l = canonicalGridCube H l := by
  classical
  unfold gridCube canonicalGridCube gridWordMultiplicity
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image
      (fun times : Fin l → Fin M => orderedGridTimes times))
    (g := fun times : Fin l → Fin M => orderedGridTimes times)
    (fun times ht => Finset.mem_image_of_mem _ ht)
    (fun times => ((orderedGridTimes times).map H).reverse.prod)]
  apply Finset.sum_congr rfl
  intro word _
  calc
    (∑ times ∈ Finset.univ.filter (fun times : Fin l → Fin M =>
        orderedGridTimes times = word), ((orderedGridTimes times).map H).reverse.prod) =
        ∑ _times ∈ Finset.univ.filter (fun times : Fin l → Fin M =>
          orderedGridTimes times = word), (word.map H).reverse.prod := by
      apply Finset.sum_congr rfl
      intro times ht
      rw [(Finset.mem_filter.mp ht).2]
    _ = _ := by rw [Finset.sum_const]

/-- Every truncated Taylor sum built from `gridCube` equals the corresponding sum built from
`canonicalGridCube` with the same coefficients. -/
theorem taylor_gridCube_transport
    {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}
    (H : Fin M → Matrix I I ℂ) (τ : ℝ) (K : ℕ) :
    (∑ l ∈ Finset.range (K + 1),
      ((-Complex.I * (τ : ℂ) / M) ^ l / (l.factorial : ℂ)) • gridCube H l) =
    ∑ l ∈ Finset.range (K + 1),
      ((-Complex.I * (τ : ℂ) / M) ^ l / (l.factorial : ℂ)) •
        canonicalGridCube H l := by
  apply Finset.sum_congr rfl
  intro l _
  rw [gridCube_eq_canonicalGridCube]

/-- The three-CNOT gate word with control-target pairs `(c, t)`, `(t, c)`, and `(c, t)`. -/
def swapWireWord (c t : ℕ) : List FiniteGateCode := [.cx c t, .cx t c, .cx c t]

/-- The register obtained by exchanging the values at positions `c` and `t`. -/
def swappedRecord {n : ℕ} (c t : Fin n) (x : Reg n) : Reg n :=
  Function.update (Function.update x c (x t)) t (x c)

/-- Three alternating exclusive-or updates at distinct positions exchange their original
register values. -/
theorem three_xors_swap {n : ℕ} (c t : Fin n) (hct : c ≠ t) (x : Reg n) :
    (let x₁ := Function.update x t (x t ^^ x c)
     let x₂ := Function.update x₁ c (x₁ c ^^ x₁ t)
     Function.update x₂ t (x₂ t ^^ x₂ c)) = swappedRecord c t x := by
  funext j
  by_cases hjc : j = c
  · subst j
    cases hxc : x c <;> cases hxt : x t <;>
      simp [swappedRecord, Function.update, hct, hxc, hxt]
  · by_cases hjt : j = t
    · subst j
      cases hxc : x c <;> cases hxt : x t <;>
        simp [swappedRecord, Function.update, hct, Ne.symm hct, hxc]
    · simp [swappedRecord, Function.update, hjc, hjt]

/-- The three-CNOT swap word is legal when its two wire indices are distinct and within the
register. -/
theorem swapWireWord_legal (n : ℕ) (c t : Fin n) (hct : c ≠ t) :
    finiteWordLegal n (swapWireWord c.val t.val) = true := by
  have hne : c.val ≠ t.val := fun h => hct (Fin.ext h)
  simp [finiteWordLegal, swapWireWord, finiteCodeLegal, c.isLt, t.isLt, hne, Ne.symm hne]

/-- Running the three-CNOT swap word on a basis vector gives the basis vector with the selected
register bits exchanged. -/
theorem swapWireWord_run (n : ℕ) (c t : Fin n) (hct : c ≠ t) (x : Reg n) :
    finiteWordRun n (swapWireWord c.val t.val) (Ket x) =
      some (Ket (swappedRecord c t x)) := by
  have hlegal := swapWireWord_legal n c t hct
  have hne : c.val ≠ t.val := fun h => hct (Fin.ext h)
  simp only [finiteWordRun, hlegal, ↓reduceIte]
  simp only [finiteCodeCircuit, swapWireWord, List.map_cons, List.map_nil, Run]
  simp only [finiteCodeMatrix, dif_pos (show c.val < n ∧ t.val < n ∧ c.val ≠ t.val from ⟨c.isLt, t.isLt, hne⟩),
    dif_pos (show t.val < n ∧ c.val < n ∧ t.val ≠ c.val from ⟨t.isLt, c.isLt, Ne.symm hne⟩)]
  rw [applyGate_cnotGate_ket n c t hct,
    applyGate_cnotGate_ket n t c (Ne.symm hct), applyGate_cnotGate_ket n c t hct]
  rw [three_xors_swap c t hct]

/-- The register obtained by exchanging corresponding positions below `k` between two blocks of
length `n`. -/
def exchangePrefix (n k : ℕ) (x : Reg (n + n)) : Reg (n + n) := fun i =>
  if hi : i.val < n then
    if i.val < k then x ⟨n + i.val, by omega⟩ else x i
  else
    if i.val - n < k then x ⟨i.val - n, by omega⟩ else x i

/-- The concatenation of three-CNOT swaps exchanging the first `k` corresponding wire pairs
between two length-`n` blocks. -/
def exchangeWord (n : ℕ) : ℕ → List FiniteGateCode
  | 0 => []
  | k + 1 => exchangeWord n k ++ swapWireWord k (n + k)

/-- Exchanging a prefix of length zero leaves the register unchanged. -/
theorem exchangePrefix_zero (n : ℕ) (x : Reg (n + n)) : exchangePrefix n 0 x = x := by
  funext i
  simp [exchangePrefix]

/-- Swapping the next corresponding wire pair extends the exchanged prefix from length `k` to
length `k + 1` when `k < n`. -/
theorem exchangePrefix_step (n k : ℕ) (hk : k < n) (x : Reg (n + n)) :
    swappedRecord ⟨k, by omega⟩ ⟨n + k, by omega⟩ (exchangePrefix n k x) =
      exchangePrefix n (k + 1) x := by
  funext i
  by_cases hleft : i.val = k
  · have hi : i = (⟨k, by omega⟩ : Fin (n + n)) := Fin.ext hleft
    rw [hi]
    simp [swappedRecord, exchangePrefix, Function.update, hk,
      show ¬n + k < n by omega, show n ≠ 0 by omega]
  · by_cases hright : i.val = n + k
    · have hi : i = (⟨n + k, by omega⟩ : Fin (n + n)) := Fin.ext hright
      rw [hi]
      simp [swappedRecord, exchangePrefix, Function.update, hk,
        show ¬n + k < n by omega]
    · have hci : i ≠ (⟨k, by omega⟩ : Fin (n + n)) := fun h => hleft (congrArg Fin.val h)
      have hti : i ≠ (⟨n + k, by omega⟩ : Fin (n + n)) := fun h => hright (congrArg Fin.val h)
      simp only [swappedRecord, Function.update_of_ne hti, Function.update_of_ne hci]
      unfold exchangePrefix
      by_cases hi : i.val < n
      · simp only [dif_pos hi]
        have he : (i.val < k) = (i.val < k + 1) := propext (by omega)
        simp only [he]
      · simp only [dif_neg hi]
        have he : (i.val - n < k) = (i.val - n < k + 1) := propext (by omega)
        simp only [he]

/-- Running a concatenation of finite gate words is sequential execution composed through
`Option.bind`. -/
theorem finiteWordRun_append (n : ℕ) (gs hs : List FiniteGateCode) (ψ : QState (Reg n)) :
    finiteWordRun n (gs ++ hs) ψ =
      (finiteWordRun n gs ψ).bind (finiteWordRun n hs) := by
  have happ : finiteWordLegal n (gs ++ hs) =
      (finiteWordLegal n gs && finiteWordLegal n hs) := by
    simp [finiteWordLegal, List.all_append]
  by_cases hg : finiteWordLegal n gs = true <;>
    by_cases hh : finiteWordLegal n hs = true <;>
    simp [finiteWordRun, happ, hg, hh, finiteCodeCircuit, List.map_append, run_append]

/-- For `k ≤ n`, the exchange word is legal, has length `3 * k`, and maps each basis vector to
the basis vector with the corresponding block prefixes exchanged. -/
theorem exchangeWord_correct (n k : ℕ) (hk : k ≤ n) :
    finiteWordLegal (n + n) (exchangeWord n k) = true ∧
      (exchangeWord n k).length = 3 * k ∧
      ∀ x : Reg (n + n), finiteWordRun (n + n) (exchangeWord n k) (Ket x) =
        some (Ket (exchangePrefix n k x)) := by
  induction k with
  | zero => simp [exchangeWord, finiteWordLegal, finiteWordRun, finiteCodeCircuit,
      exchangePrefix_zero]
  | succ k ih =>
      have hkn : k < n := by omega
      obtain ⟨hl, hlen, hrun⟩ := ih (by omega)
      let c : Fin (n + n) := ⟨k, by omega⟩
      let t : Fin (n + n) := ⟨n + k, by omega⟩
      have hct : c ≠ t := by intro he; have hv := congrArg Fin.val he; dsimp [c,t] at hv; omega
      have hlocal := swapWireWord_legal (n + n) c t hct
      refine ⟨?_, ?_, ?_⟩
      · simpa only [exchangeWord, finiteWordLegal, List.all_append, Bool.and_eq_true]
          using! And.intro hl hlocal
      · simp [exchangeWord, swapWireWord, hlen, Nat.mul_add]
      · intro x
        rw [exchangeWord, finiteWordRun_append, hrun, Option.bind_some,
          swapWireWord_run (n + n) c t hct]
        congr 2
        exact exchangePrefix_step n k hkn x

/-- A finite gate word is legal on a register with zero wires exactly when it is empty. -/
theorem zeroWire_legal_iff (gs : List FiniteGateCode) :
    finiteWordLegal 0 gs = true ↔ gs = [] := by
  cases gs with
  | nil => simp [finiteWordLegal]
  | cons g gs => cases g <;> simp [finiteWordLegal, finiteCodeLegal]

/-- The T-gate phase `exp (i * π / 4)`. -/
noncomputable def fixedTPhase : ℂ := Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- The gate word applying X, then `k` T gates, then X again on the selected wire. -/
def cleanPhaseWord (wire k : ℕ) : List FiniteGateCode :=
  [.x wire] ++ List.replicate k (.t wire) ++ [.x wire]

/-- The matrix of a concatenated gate word is the matrix of its second word multiplied by the
matrix of its first word. -/
theorem finiteCodeWordMatrix_append (n : ℕ) (gs hs : List FiniteGateCode) :
    finiteCodeWordMatrix n (gs ++ hs) =
      finiteCodeWordMatrix n hs * finiteCodeWordMatrix n gs := by
  induction gs with
  | nil => simp [finiteCodeWordMatrix]
  | cons g gs ih =>
      simp only [List.cons_append, finite_phase_word_cons, ih, Matrix.mul_assoc]

/-- Placing a diagonal one-qubit gate at a wire gives the register-diagonal matrix whose entry
depends on that wire's bit. -/
theorem wireGate_diagonal (n : ℕ) (w : Fin n) (f : Bool → ℂ) :
    wireGate n w (Matrix.diagonal f) = Matrix.diagonal (fun x : Reg n => f (x w)) := by
  ext x y
  rw [wireGate_apply]
  by_cases hxy : x = y
  · subst y
    simp
  · rw [Matrix.diagonal_apply_ne _ hxy]
    by_cases hs : ∀ i : Fin n, i ≠ w → x i = y i
    · have hw : x w ≠ y w := by
        intro h
        apply hxy
        funext i
        by_cases hi : i = w
        · simpa [hi] using! h
        · exact hs i hi
      simp [Matrix.diagonal_apply_ne _ hw]
    · simp [hs]

/-- The `k`th power of the T gate is diagonal with entry one at false and `fixedTPhase ^ k` at
true. -/
theorem tGate_pow_diagonal (k : ℕ) :
    tGate ^ k = Matrix.diagonal (fun b : Bool => if b then fixedTPhase ^ k else 1) := by
  rw [tGate, Rz, Matrix.diagonal_pow]
  congr 1
  funext b
  cases b <;> simp [fixedTPhase]

/-- Conjugating the `k`th T-gate power by Pauli X gives the diagonal phase `fixedTPhase ^ k` at
false and one at true. -/
theorem x_tGate_pow_x (k : ℕ) :
    PauliX * tGate ^ k * PauliX =
      Matrix.diagonal (fun b : Bool => if b then 1 else fixedTPhase ^ k) := by
  rw [tGate_pow_diagonal]
  ext a b
  cases a <;> cases b <;> simp [Matrix.mul_apply, PauliX, permMatrix]

/-- A word of `k` T gates on one wire has the matrix of the `k`th T-gate power placed on that
wire. -/
theorem tWord_matrix (n : ℕ) (w : Fin n) (k : ℕ) :
    finiteCodeWordMatrix n (List.replicate k (.t w.val)) = wireGate n w (tGate ^ k) := by
  induction k with
  | zero => simp [finiteCodeWordMatrix, wireGate_one]
  | succ k ih =>
      rw [List.replicate_succ, finite_phase_word_cons, ih]
      simp only [finiteCodeMatrix, w.isLt, dite_true]
      change wireGate n w (tGate ^ k) * wireGate n w tGate = _
      rw [wireGate_mul, ← pow_succ]

/-- The clean phase word is diagonal, applying `fixedTPhase ^ k` when the selected bit is false
and one when it is true. -/
theorem cleanPhaseWord_matrix (n : ℕ) (w : Fin n) (k : ℕ) :
    finiteCodeWordMatrix n (cleanPhaseWord w.val k) =
      Matrix.diagonal (fun x : Reg n => if x w then 1 else fixedTPhase ^ k) := by
  have hx : finiteCodeWordMatrix n [.x w.val] = wireGate n w PauliX := by
    rw [finite_phase_word_cons]
    change 1 * finiteCodeMatrix n (.x w.val) = _
    simp [finiteCodeMatrix, w.isLt]
  rw [cleanPhaseWord, finiteCodeWordMatrix_append, finiteCodeWordMatrix_append,
    tWord_matrix, hx, ← Matrix.mul_assoc, wireGate_mul, wireGate_mul,
    x_tGate_pow_x, wireGate_diagonal]

/-- The clean phase word on a valid wire is legal, makes zero queries, and has gate count `k +
2`. -/
theorem cleanPhaseWord_legal_counts (n : ℕ) (w : Fin n) (k : ℕ) :
    finiteWordLegal n (cleanPhaseWord w.val k) = true ∧
      QueryCount (finiteCodeCircuit n (cleanPhaseWord w.val k)) = 0 ∧
      GateCount (finiteCodeCircuit n (cleanPhaseWord w.val k)) = k + 2 := by
  have hcounts := finiteCodeCircuit_counts n (cleanPhaseWord w.val k)
  refine ⟨?_, hcounts.1, ?_⟩
  · simp [cleanPhaseWord, finiteWordLegal, finiteCodeLegal, w.isLt]
  · simpa [cleanPhaseWord] using! hcounts.2

/-- On a state supported where the selected wire is false, the clean phase word multiplies the
whole state by `fixedTPhase ^ k`. -/
theorem cleanPhaseWord_run_support (n : ℕ) (w : Fin n) (k : ℕ)
    (ψ : QState (Reg n)) (hclean : ∀ x : Reg n, x w = true → ψ x = 0) :
    finiteWordRun n (cleanPhaseWord w.val k) ψ = some (fixedTPhase ^ k • ψ) := by
  have hl := (cleanPhaseWord_legal_counts n w k).1
  rw [finiteWordRun, if_pos hl, finite_phase_word_run, cleanPhaseWord_matrix]
  congr 1
  funext x
  change (Matrix.diagonal (fun y : Reg n => if y w then 1 else fixedTPhase ^ k) *ᵥ ψ) x = _
  rw [Matrix.mulVec_diagonal]
  cases hx : x w <;> simp [hx, hclean x, Pi.smul_apply, smul_eq_mul]

/-- The fourth power of the T-gate phase is negative one. -/
theorem fixedTPhase_four : fixedTPhase ^ 4 = -1 := by
  rw [fixedTPhase, ← Complex.exp_nat_mul]
  convert! Complex.exp_pi_mul_I using 1
  congr 1
  push_cast
  ring

/-- The eighth power of the T-gate phase is one. -/
theorem fixedTPhase_eighth : fixedTPhase ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 by decide, pow_mul, fixedTPhase_four]
  norm_num

/-- Powers of the T-gate phase depend only on their exponent modulo eight. -/
theorem fixedTPhase_pow_mod (k : ℕ) : fixedTPhase ^ k = fixedTPhase ^ (k % 8) := by
  calc
    fixedTPhase ^ k = fixedTPhase ^ (k % 8 + 8 * (k / 8)) := by rw [Nat.mod_add_div]
    _ = fixedTPhase ^ (k % 8) := by rw [pow_add, pow_mul, fixedTPhase_eighth, one_pow, mul_one]

/-- The clean phase word with its T-gate repetition count reduced modulo eight. -/
def boundedCleanPhaseWord (wire k : ℕ) : List FiniteGateCode :=
  cleanPhaseWord wire (k % 8)

/-- On a state supported where the selected wire is false, reducing the phase-word repetition
count modulo eight still applies the scalar `fixedTPhase ^ k`. -/
theorem boundedCleanPhaseWord_run (n : ℕ) (w : Fin n) (k : ℕ)
    (ψ : QState (Reg n)) (hclean : ∀ x : Reg n, x w = true → ψ x = 0) :
    finiteWordRun n (boundedCleanPhaseWord w.val k) ψ = some (fixedTPhase ^ k • ψ) := by
  rw [fixedTPhase_pow_mod k]
  exact cleanPhaseWord_run_support n w (k % 8) ψ hclean

/-- The bounded clean phase word on a valid wire is legal, makes zero queries, and uses exactly
`k % 8 + 2` gates, hence at most nine. -/
theorem boundedCleanPhaseWord_resources (n : ℕ) (w : Fin n) (k : ℕ) :
    finiteWordLegal n (boundedCleanPhaseWord w.val k) = true ∧
      QueryCount (finiteCodeCircuit n (boundedCleanPhaseWord w.val k)) = 0 ∧
      GateCount (finiteCodeCircuit n (boundedCleanPhaseWord w.val k)) = k % 8 + 2 ∧
      GateCount (finiteCodeCircuit n (boundedCleanPhaseWord w.val k)) ≤ 9 := by
  obtain ⟨hl, hq, hg⟩ := cleanPhaseWord_legal_counts n w (k % 8)
  refine ⟨hl, hq, hg, ?_⟩
  change GateCount (finiteCodeCircuit n (cleanPhaseWord w.val (k % 8))) ≤ 9
  rw [hg]
  have hm := Nat.mod_lt k (by decide : 0 < 8)
  omega

/-- Running `k` T gates on a valid wire multiplies each amplitude by `fixedTPhase ^ k` exactly
when that wire's bit is true. -/
theorem tWord_run (n : ℕ) (w : Fin n) (k : ℕ) (ψ : QState (Reg n)) :
    finiteWordRun n (List.replicate k (.t w.val)) ψ =
      some (fun x => (if x w then fixedTPhase ^ k else 1) * ψ x) := by
  have hl : finiteWordLegal n (List.replicate k (.t w.val)) = true := by
    simp [finiteWordLegal, finiteCodeLegal, w.isLt]
  rw [finiteWordRun, if_pos hl, finite_phase_word_run, tWord_matrix,
    tGate_pow_diagonal, wireGate_diagonal]
  congr 1
  funext x
  exact Matrix.mulVec_diagonal _ _ _

end Qatlib.Papers.FixedPtSearch14.FixedPoint
