/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost

/-!
# Finite execution of fair-bit rejection sampling

`fairBitsCosted` generates a uniform bit register with an exact bit cost. The decoder
`decodeBoundedBits` accepts integers below `m`, and `finiteCoinRun` repeats this step up to a
finite fuel limit while charging for the bits actually drawn.

The module proves exact return and pending probabilities, a geometric formula for expected bit
cost, and an explicit cutoff using `Nat.clog 2 m`. This gives a finite operational account of
randomized computation in the setting described by [KitaevShenVyalyi2002].

## Main statements

* `fair_bit_program_joint_distribution`: the register is uniform and its cost is exactly its
  length.
* `finite_coin_return_and_pending`: bounded rejection sampling has uniform returned labels and
  geometric pending mass.
* `finite_coin_effective_cutoff`: ceiling-logarithmic bit blocks give geometric tail and
  expected-cost bounds.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline

namespace PMF

open scoped ENNReal Classical

/-- The uniform probability mass function on a nonempty finite set. -/
noncomputable def uniformOfFinset {α : Type*} (s : Finset α) (hs : s.Nonempty) : PMF α :=
  ofFinset (fun a => if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0) s
    (by
      have h1 : (∑ a ∈ s, if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0) = ∑ _a ∈ s, (s.card : ℝ≥0∞)⁻¹ :=
        Finset.sum_congr rfl (fun _ ha => if_pos ha)
      rw [h1, Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hs.card_pos.ne')
          (ENNReal.natCast_ne_top _))
    (fun _ ha => if_neg ha)

/-- The uniform finite-set law assigns reciprocal cardinality to members and zero to nonmembers. -/
@[simp]
theorem uniformOfFinset_apply {α : Type*} {s : Finset α} (hs : s.Nonempty) (a : α) [Decidable (a ∈ s)] :
    uniformOfFinset s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  dsimp [uniformOfFinset]
  congr

/-- The outer measure of a set under the uniform finite-set law is its intersection cardinality
divided by the support cardinality. -/
@[simp]
theorem toOuterMeasure_uniformOfFinset'_apply {α : Type*} {s : Finset α} (hs : s.Nonempty)
    (t : Set α) [DecidablePred (· ∈ t)] :
    (uniformOfFinset s hs).toOuterMeasure t = (s.filter (· ∈ t)).card / s.card := by
  rw [uniformOfFinset, toOuterMeasure_ofFinset_apply]
  have h1 : (∑' x, t.indicator (fun a => if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0) x) =
      ∑ x ∈ s.filter (· ∈ t), (s.card : ℝ≥0∞)⁻¹ := by
    rw [tsum_eq_sum (s := s.filter (· ∈ t))]
    · refine Finset.sum_congr rfl (fun x hx => ?_)
      simp only [Finset.mem_filter] at hx
      simp [Set.indicator_of_mem hx.2, hx.1]
    · intro x hx
      simp only [Finset.mem_filter, not_and] at hx
      by_cases hxt : x ∈ t
      · simp [Set.indicator_of_mem hxt, show x ∉ s from fun hxs => hx hxs hxt]
      · simp [Set.indicator_of_notMem hxt]
  rw [h1, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- The uniform probability mass function on a nonempty finite type. -/
noncomputable def uniformOfFintype' (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  ofFintype (fun _ => (Fintype.card α : ℝ≥0∞)⁻¹)
    (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _))

/-- Each point of the uniform finite-type law has mass equal to the reciprocal of the type's
cardinality. -/
@[simp]
theorem uniformOfFintype'_apply {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    uniformOfFintype' α a = (Fintype.card α : ℝ≥0∞)⁻¹ := rfl

/-- Every element of a nonempty finite type belongs to the support of its uniform law. -/
@[simp]
theorem mem_support_uniformOfFintype' {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    a ∈ (uniformOfFintype' α).support := by
  rw [uniformOfFintype', mem_support_ofFintype_iff]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

/-- The uniform law assigns a set its cardinality divided by the cardinality of the ambient
finite type. -/
@[simp]
theorem toOuterMeasure_uniformOfFintype'_apply {α : Type*} [Fintype α] [Nonempty α]
    (s : Set α) [Fintype s] :
    (uniformOfFintype' α).toOuterMeasure s = Fintype.card s / Fintype.card α := by
  classical
  rw [uniformOfFintype', toOuterMeasure_ofFintype_apply, tsum_fintype]
  have h1 : (∑ x : α, s.indicator (fun _ => (Fintype.card α : ℝ≥0∞)⁻¹) x) =
      ∑ _x ∈ Finset.univ.filter (· ∈ s), (Fintype.card α : ℝ≥0∞)⁻¹ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hxs : x ∈ s <;> simp [hxs]
  have hcard : (Finset.univ.filter (· ∈ s)).card = Fintype.card s :=
    (Fintype.card_of_subtype (Finset.univ.filter (· ∈ s)) (by simp)).symm
  rw [h1, Finset.sum_const, nsmul_eq_mul, hcard, div_eq_mul_inv]

end PMF

namespace Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical

instance instNonemptyReg (n : ℕ) : Nonempty (Reg n) := ⟨fun _ => false⟩

/-- Every natural power of an extended nonnegative real at most one is at most one. -/
private theorem pow_le_one' {q : ℝ≥0∞} (hq : q ≤ 1) (j : ℕ) : q ^ j ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc q ^ (j + 1) = q ^ j * q := pow_succ q j
        _ ≤ 1 * 1 := mul_le_mul' ih hq
        _ = 1 := by simp

/-- Generate `k` independent fair bits while recording the number of sampled bits as cost. -/
noncomputable def fairBitsCosted : (k : ℕ) → CostedLaw (Reg k)
  | 0 => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (ZeroStr 0)
  | k + 1 => CostedLaw.bind (fairBitsCosted k) fun ω =>
      (PMF.uniformOfFintype' Bool).map fun b => ((regSuccEquiv k).symm (ω, b), 1)

/-- Append one uniform Boolean to a bit register and increase the accumulated cost by one. -/
private noncomputable def fairBitCont (k : ℕ) (x : Reg k × ℕ) : PMF (Reg (k + 1) × ℕ) :=
  (PMF.uniformOfFintype' Bool).map fun b => ((regSuccEquiv k).symm (x.1, b), x.2 + 1)

/-- The point mass of the one-bit continuation is the sum of the matching Boolean branch masses. -/
private theorem fairBitCont_apply (k : ℕ) (x : Reg k × ℕ) (z : Reg (k + 1) × ℕ) :
    fairBitCont k x z = ∑' b : Bool,
      @ite ℝ≥0∞ (z = ((regSuccEquiv k).symm (x.1, b), x.2 + 1)) (Classical.propDecidable _)
        ((PMF.uniformOfFintype' Bool) b) 0 :=
  PMF.map_apply _ _ _

/-- Generating `k + 1` fair bits equals generating `k` fair bits and applying the one-bit
continuation. -/
private theorem fairBitsCosted_succ (k : ℕ) :
    fairBitsCosted (k + 1) = PMF.bind (fairBitsCosted k) (fairBitCont k) := by
  refine congrArg (PMF.bind (fairBitsCosted k)) ?_
  funext x
  have h1 : CostedLaw.charge x.2 ((PMF.uniformOfFintype' Bool).map
        fun b => ((regSuccEquiv k).symm (x.1, b), 1)) = fairBitCont k x := by
    show (PMF.map (fun y : Reg (k + 1) × ℕ => (y.1, x.2 + y.2))
        ((PMF.uniformOfFintype' Bool).map fun b => ((regSuccEquiv k).symm (x.1, b), 1))) = _
    rw [PMF.map_comp]
    rfl
  rw [h1]

/-- The fair-bit program produces a uniform `k`-bit register and has cost exactly `k`. -/
theorem fair_bit_program_joint_distribution (k n : ℕ) (ω : Reg k) :
    fairBitsCosted k (ω, n) = if n = k then PMF.uniformOfFintype' (Reg k) ω else 0 := by
  induction k generalizing n with
  | zero =>
      show (PMF.pure (ZeroStr 0, 0)) (ω, n)
        = if n = 0 then PMF.uniformOfFintype' (Reg 0) ω else 0
      have hω : ω = ZeroStr 0 := funext fun i => Fin.elim0 i
      rw [hω, PMF.pure_apply]
      by_cases hn : n = 0
      · subst hn
        simp [PMF.uniformOfFintype'_apply]
      · have hne : ¬ ((ZeroStr 0, n) = (ZeroStr 0, 0)) := by
          intro h
          have h2 := congrArg Prod.snd h
          simp at h2
          omega
        rw [if_neg hn, if_neg hne]
  | succ k ih =>
      rw [fairBitsCosted_succ, PMF.bind_apply, tsum_prod_type']
      have hinner : ∀ ω' : Reg k,
          (∑' m : ℕ, fairBitsCosted k (ω', m) * fairBitCont k (ω', m) (ω, n))
            = PMF.uniformOfFintype' (Reg k) ω' * fairBitCont k (ω', k) (ω, n) := by
        intro ω'
        refine Eq.trans (tsum_eq_single k fun b hb => ?_) ?_
        · rw [ih b ω', if_neg hb, zero_mul]
        · rw [ih k ω', if_pos rfl]
      rw [tsum_congr hinner]
      have hpre : ∀ ω' : Reg k, ω' ≠ (regSuccEquiv k ω).1 →
          PMF.uniformOfFintype' (Reg k) ω' * fairBitCont k (ω', k) (ω, n) = 0 := by
        intro ω' hne'
        have hcond : ∀ b : Bool,
            ¬ ((ω, n) = ((regSuccEquiv k).symm (ω', b), k + 1)) := by
          intro b hc
          have hfst : ω = (regSuccEquiv k).symm (ω', b) := by
            have := congrArg Prod.fst hc
            simpa using this
          have h2 : (regSuccEquiv k ω).1 = ω' := by
            rw [hfst]
            simp
          exact hne' h2.symm
        rw [fairBitCont_apply]
        (try dsimp only)
        exact mul_eq_zero.mpr (Or.inr (ENNReal.tsum_eq_zero.mpr fun b => if_neg (hcond b)))
      rw [tsum_eq_single (regSuccEquiv k ω).1 (fun ω' hne' => hpre ω' hne')]
      by_cases hn : n = k + 1
      · subst hn
        have hbne : ∀ b : Bool, b ≠ (regSuccEquiv k ω).2 →
            ¬ ((ω, k + 1) = ((regSuccEquiv k).symm ((regSuccEquiv k ω).1, b), k + 1)) := by
          intro b hb hc
          have hfst : ω = (regSuccEquiv k).symm ((regSuccEquiv k ω).1, b) := by
            have := congrArg Prod.fst hc
            simpa using this
          have h5 : ((regSuccEquiv k ω).1, b) = regSuccEquiv k ω := by
            rw [hfst]
            simp
          have h6 : ((regSuccEquiv k ω).1, b)
              = ((regSuccEquiv k ω).1, (regSuccEquiv k ω).2) :=
            h5.trans Prod.mk.eta.symm
          exact hb (congrArg Prod.snd h6)
        rw [if_pos rfl]
        have hEq : ((regSuccEquiv k).symm ((regSuccEquiv k ω).1, (regSuccEquiv k ω).2),
            k + 1) = (ω, k + 1) := by
          have he : ((regSuccEquiv k ω).1, (regSuccEquiv k ω).2) = regSuccEquiv k ω :=
            Prod.mk.eta.symm
          rw [he]
          exact congrArg (fun z => (z, k + 1)) (Equiv.symm_apply_apply (regSuccEquiv k) ω)
        have hsum : fairBitCont k ((regSuccEquiv k ω).1, k) (ω, k + 1)
            = (PMF.uniformOfFintype' Bool) (regSuccEquiv k ω).2 := by
          rw [fairBitCont_apply]
          (try dsimp only)
          refine Eq.trans (tsum_eq_single (regSuccEquiv k ω).2 fun b hb => ?_) ?_
          · rw [if_neg (hbne b hb)]
          · rw [hEq, if_pos rfl]
        have h2k : ((2:ℕ)^(k+1)) = 2^k * 2 := by rw [Nat.pow_succ]
        rw [hsum, PMF.uniformOfFintype'_apply, PMF.uniformOfFintype'_apply,
          PMF.uniformOfFintype'_apply, Fintype.card_bool, card_reg, card_reg, h2k,
          Nat.cast_mul]
        exact (ENNReal.mul_inv (by simp) (by simp)).symm
      · rw [if_neg hn]
        have hcond : ∀ b : Bool,
            ¬ ((ω, n) = ((regSuccEquiv k).symm ((regSuccEquiv k ω).1, b), k + 1)) := by
          intro b hc
          have h2 := congrArg Prod.snd hc
          simp at h2
          omega
        rw [fairBitCont_apply]
        (try dsimp only)
        exact mul_eq_zero.mpr (Or.inr (ENNReal.tsum_eq_zero.mpr fun b => if_neg (hcond b)))

/-- Summing the fair-bit joint law over costs gives the uniform law on bit registers. -/
theorem fairBitsCosted_marginal (k : ℕ) (ω : Reg k) :
    ∑' n, fairBitsCosted k (ω, n) = PMF.uniformOfFintype' (Reg k) ω := by
  have h : ∀ n, fairBitsCosted k (ω, n)
      = if n = k then PMF.uniformOfFintype' (Reg k) ω else 0 :=
    fun n => fair_bit_program_joint_distribution k n ω
  rw [tsum_congr h]
  refine Eq.trans (tsum_eq_single k fun b hb => if_neg hb) ?_
  rw [if_pos rfl]

/-- Discarding the recorded cost from the fair-bit program yields the uniform bit-register law. -/
@[simp] theorem fairBitsCosted_output (k : ℕ) :
    (fairBitsCosted k).map Prod.fst = PMF.uniformOfFintype' (Reg k) := by
  ext ω
  rw [PMF.map_apply, tsum_prod_type']
  rw [tsum_eq_single ω (fun b hb => by simp [Ne.symm hb])]
  simpa using fairBitsCosted_marginal k ω

/-- Interpret a bit register as a natural number and return it as a label precisely when it is
below `m`. -/
def decodeBoundedBits (k m : ℕ) (bits : Reg k) : Option (Fin m) :=
  if h : (bitVecEquiv k bits).val < m then some ⟨(bitVecEquiv k bits).val, h⟩ else none

/-- When `m ≤ 2 ^ k`, decoding returns `i` exactly on the unique bit register representing `i`. -/
theorem decodeBoundedBits_eq_some_iff {k m : ℕ} (hm : m ≤ 2 ^ k) (b : Reg k) (i : Fin m) :
    decodeBoundedBits k m b = some i
      ↔ b = (bitVecEquiv k).symm (Fin.castLE hm i) := by
  constructor
  · intro h
    by_cases hb : (bitVecEquiv k b).val < m
    · rw [decodeBoundedBits, dif_pos hb] at h
      have hv : (bitVecEquiv k b).val = i.val := by
        injection h with h'
        exact congrArg Fin.val h'
      have hbe : bitVecEquiv k b = Fin.castLE hm i := Fin.ext hv
      exact (Equiv.symm_apply_eq _).mp hbe
    · rw [decodeBoundedBits, dif_neg hb] at h
      simp at h
  · intro h
    rw [decodeBoundedBits]
    have hbe : bitVecEquiv k b = Fin.castLE hm i := by
      rw [h, Equiv.apply_symm_apply]
    have hb : (bitVecEquiv k b).val < m := by
      have : (bitVecEquiv k b).val = i.val := by rw [hbe, Fin.val_castLE]
      rw [this]
      exact i.isLt
    rw [dif_pos hb]
    have hv : (bitVecEquiv k b).val = i.val := by rw [hbe, Fin.val_castLE]
    exact congrArg some (Fin.ext hv)

/-- The cardinalities of a predicate and its complement sum to the cardinality of the ambient
finite type. -/
private theorem card_filter_partition {α : Type} [Fintype α] [DecidableEq α]
    (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card + (Finset.univ.filter fun a => ¬P a).card = Fintype.card α := by
  have hU : (Finset.univ.filter P) ∪ (Finset.univ.filter fun a => ¬P a) = Finset.univ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_union, true_and]
    by_cases hP : P a <;> simp [hP]
  have hI : ((Finset.univ.filter P) ∩ (Finset.univ.filter fun a => ¬P a)) = ∅ := by
    ext a
    simp
  calc (Finset.univ.filter P).card + (Finset.univ.filter fun a => ¬P a).card
      = ((Finset.univ.filter P) ∪ (Finset.univ.filter fun a => ¬P a)).card +
          ((Finset.univ.filter P) ∩ (Finset.univ.filter fun a => ¬P a)).card :=
        (Finset.card_union_add_card_inter _ _).symm
    _ = Fintype.card α := by
        rw [hU, hI, Finset.card_empty, add_zero, Finset.card_univ]

/-- Each accepted label has one decoding preimage, and rejection has exactly `2 ^ k - m`
preimages. -/
theorem bounded_bit_decoder_fibers (k m : ℕ) (hm : m ≤ 2 ^ k) :
    (∀ i : Fin m,
      (Finset.univ.filter fun b : Reg k => decodeBoundedBits k m b = some i).card = 1) ∧
      (Finset.univ.filter fun b : Reg k => decodeBoundedBits k m b = none).card = 2 ^ k - m := by
  constructor
  · intro i
    have hset : (Finset.univ.filter fun b : Reg k => decodeBoundedBits k m b = some i)
        = {(bitVecEquiv k).symm (Fin.castLE hm i)} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [decodeBoundedBits_eq_some_iff hm b i]
    rw [hset]
    rfl
  · have hinj : ∀ i j : Fin m, (bitVecEquiv k).symm (Fin.castLE hm i)
          = (bitVecEquiv k).symm (Fin.castLE hm j) → i = j := by
      intro i j h
      have h1 : Fin.castLE hm i = Fin.castLE hm j := by
        rw [← Equiv.apply_symm_apply (bitVecEquiv k) (Fin.castLE hm i),
          ← Equiv.apply_symm_apply (bitVecEquiv k) (Fin.castLE hm j), h]
      have h2 := congrArg Fin.val h1
      simp only [Fin.val_castLE] at h2
      exact Fin.ext h2
    have hsome : (Finset.univ.filter fun b : Reg k => decodeBoundedBits k m b ≠ none)
        = Finset.image (fun i : Fin m => (bitVecEquiv k).symm (Fin.castLE hm i)) Finset.univ := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        rcases Option.ne_none_iff_exists.mp h with ⟨i, hi⟩
        exact ⟨i, ((decodeBoundedBits_eq_some_iff hm b i).mp hi.symm).symm⟩
      · rintro ⟨i, rfl⟩
        rw [show decodeBoundedBits k m ((bitVecEquiv k).symm (Fin.castLE hm i)) = some i from
            (decodeBoundedBits_eq_some_iff hm _ i).mpr rfl]
        exact Option.some_ne_none i
    have hcardSome : (Finset.univ.filter fun b : Reg k => decodeBoundedBits k m b ≠ none).card
        = m := by
      rw [hsome, Finset.card_image_of_injOn
        (fun i _ j _ hij => hinj i j hij), Finset.card_univ, Fintype.card_fin]
    have hpart := card_filter_partition (fun b : Reg k => decodeBoundedBits k m b = none)
    have hne : (Finset.univ.filter fun b : Reg k => ¬(decodeBoundedBits k m b = none))
        = (Finset.univ.filter fun b : Reg k => decodeBoundedBits k m b ≠ none) := by
      refine Finset.filter_congr fun b _ => ?_
      simp
    rw [hne, card_reg] at hpart
    omega

/-- The rejection probability `(2 ^ k - m) / 2 ^ k` for a bounded bit decoder. -/
noncomputable def coinRejectMass (k m : ℕ) : ℝ≥0∞ :=
  ((2 ^ k - m : ℕ) : ℝ≥0∞) / ((2 ^ k : ℕ) : ℝ≥0∞)

/-- Turn a bounded decoding result into either a returned label or the pending unit
configuration. -/
def coinStep (k m : ℕ) (bits : Reg k) : RandomizedExecution.Configuration Unit (Fin m) :=
  match decodeBoundedBits k m bits with
  | some i => Sum.inl i
  | none => Sum.inr ()

/-- A coin step returns `i` exactly when the bounded bit decoder returns `some i`. -/
theorem coinStep_inl (k m : ℕ) (bits : Reg k) (i : Fin m) :
    coinStep k m bits = Sum.inl i ↔ decodeBoundedBits k m bits = some i := by
  show (match decodeBoundedBits k m bits with
      | some j => Sum.inl j
      | none => Sum.inr ()) = Sum.inl i ↔ decodeBoundedBits k m bits = some i
  cases hd : decodeBoundedBits k m bits with
  | some j => simp
  | none => simp

/-- A coin step remains pending exactly when the bounded bit decoder rejects. -/
theorem coinStep_inr (k m : ℕ) (bits : Reg k) :
    coinStep k m bits = Sum.inr () ↔ decodeBoundedBits k m bits = none := by
  show (match decodeBoundedBits k m bits with
      | some j => Sum.inl j
      | none => Sum.inr ()) = Sum.inr () ↔ decodeBoundedBits k m bits = none
  cases hd : decodeBoundedBits k m bits with
  | some j => simp
  | none => simp

/-- The transition law that draws a fresh uniform bit block and applies the bounded decoder. -/
noncomputable def finiteCoinNext (k m : ℕ) :
    Unit → PMF (RandomizedExecution.Configuration Unit (Fin m)) :=
  fun _ => ((fairBitsCosted k).map Prod.fst).map (coinStep k m)

/-- Each accepted label has mass `1 / 2 ^ k`, and the pending configuration has mass
`coinRejectMass k m`. -/
theorem finite_coin_step_distribution (k m : ℕ) (hm : m ≤ 2 ^ k) :
    (∀ i : Fin m, finiteCoinNext k m () (Sum.inl i) = ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹) ∧
      finiteCoinNext k m () (Sum.inr ()) = coinRejectMass k m := by
  have hkernel : finiteCoinNext k m () =
      (PMF.uniformOfFintype' (Reg k)).map (coinStep k m) := by
    simp only [finiteCoinNext, fairBitsCosted_output]
  have hu : ∀ b : Reg k, (PMF.uniformOfFintype' (Reg k)) b
      = ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := fun b => by
    rw [PMF.uniformOfFintype'_apply, card_reg]
  have h1 : ∀ i : Fin m, finiteCoinNext k m () (Sum.inl i) = ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := by
    intro i
    rw [hkernel]
    have hval : ((bitVecEquiv k).symm (Fin.castLE hm i))
        = (bitVecEquiv k).symm (Fin.castLE hm i) := rfl
    refine Eq.trans ?_ (hu ((bitVecEquiv k).symm (Fin.castLE hm i)))
    show ((PMF.uniformOfFintype' (Reg k)).map (coinStep k m)) (Sum.inl i) = _
    rw [PMF.map_apply]
    refine Eq.trans (tsum_eq_single ((bitVecEquiv k).symm (Fin.castLE hm i))
      fun b hb => ?_) ?_
    · refine if_neg fun hc => hb ?_
      exact (decodeBoundedBits_eq_some_iff hm b i).mp
        ((coinStep_inl k m b i).mp hc.symm)
    · rw [if_pos (((coinStep_inl k m _ i).mpr
        ((decodeBoundedBits_eq_some_iff hm _ i).mpr rfl)).symm)]
  refine ⟨h1, ?_⟩
  have htotal : ∑' c : RandomizedExecution.Configuration Unit (Fin m),
      finiteCoinNext k m () c = 1 := PMF.tsum_coe _
  rw [tsum_sum_type'] at htotal
  have hinl : (∑' i : Fin m, finiteCoinNext k m () (Sum.inl i))
      = ((m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [tsum_fintype, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const]
    simp
  have hinr : (∑' t : Unit, finiteCoinNext k m () (Sum.inr t))
      = finiteCoinNext k m () (Sum.inr ()) :=
    tsum_eq_single () fun t ht => by
      cases t
      exact absurd rfl ht
  rw [hinl, hinr] at htotal
  have hsplit : ((m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹
      + (((2 ^ k - m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹) = 1 := by
    have hmul : (((m : ℕ) : ℝ≥0∞) + ((2 ^ k - m : ℕ) : ℝ≥0∞))
          * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹
        = ((2 ^ k : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := by
      rw [← Nat.cast_add, show m + (2 ^ k - m) = 2 ^ k from by omega]
    calc ((m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹
          + ((2 ^ k - m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹
        = (((m : ℕ) : ℝ≥0∞) + ((2 ^ k - m : ℕ) : ℝ≥0∞))
            * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := (add_mul _ _ _).symm
      _ = ((2 ^ k : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := hmul
      _ = 1 := ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)
  have hne : ((m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    intro h
    rw [h] at htotal
    simp at htotal
  have hqsub : (1 : ℝ≥0∞) - ((m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹
      = finiteCoinNext k m () (Sum.inr ()) := by
    refine (ENNReal.eq_sub_of_add_eq hne ?_).symm
    rw [add_comm]
    exact htotal
  have hXsub : (1 : ℝ≥0∞) - ((m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹
      = ((2 ^ k - m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := by
    refine (ENNReal.eq_sub_of_add_eq hne ?_).symm
    rw [add_comm]
    exact hsplit
  calc finiteCoinNext k m () (Sum.inr ())
      = (1 : ℝ≥0∞) - ((m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := hqsub.symm
    _ = ((2 ^ k - m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := hXsub
    _ = coinRejectMass k m := by
      show ((2 ^ k - m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹
        = ((2 ^ k - m : ℕ) : ℝ≥0∞) / ((2 ^ k : ℕ) : ℝ≥0∞)
      rw [div_eq_mul_inv]

/-- The total mass of all accepted labels plus the rejection mass equals one. -/
theorem finiteCoinNext_total (k m : ℕ) (hm : m ≤ 2 ^ k) :
    ((m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ + coinRejectMass k m = 1 := by
  have h1 : ∑' c : RandomizedExecution.Configuration Unit (Fin m),
      finiteCoinNext k m () c = 1 := PMF.tsum_coe _
  rw [tsum_sum_type'] at h1
  have h2 : (∑' i : Fin m, finiteCoinNext k m () (Sum.inl i))
      = ((m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [tsum_fintype, Finset.sum_congr rfl fun i _ => (finite_coin_step_distribution k m hm).1 i]
    simp
  have h3 : (∑' t : Unit, finiteCoinNext k m () (Sum.inr t)) = coinRejectMass k m := by
    refine Eq.trans (tsum_eq_single () fun b hb => by
      cases b
      exact absurd rfl hb) ?_
    exact (finite_coin_step_distribution k m hm).2
  rw [h2, h3] at h1
  exact h1

/-- A one-step payoff expectation splits into a uniform sum over returned labels and a
rejection-weighted pending payoff. -/
theorem finiteCoinNext_expectation (k m : ℕ) (hm : m ≤ 2 ^ k)
    (W : RandomizedExecution.Configuration Unit (Fin m) → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (finiteCoinNext k m ()) W
      = ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ * (∑ i : Fin m, W (Sum.inl i))
        + coinRejectMass k m * W (Sum.inr ()) := by
  show ∑' c : RandomizedExecution.Configuration Unit (Fin m),
      finiteCoinNext k m () c * W c = _
  rw [tsum_sum_type']
  have h1 : (∑' i : Fin m, finiteCoinNext k m () (Sum.inl i) * W (Sum.inl i))
      = ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ * ∑ i : Fin m, W (Sum.inl i) := by
    rw [tsum_fintype, Finset.sum_congr rfl fun i _ => by
        rw [(finite_coin_step_distribution k m hm).1 i], ← Finset.mul_sum]
  have h2 : (∑' t : Unit, finiteCoinNext k m () (Sum.inr t) * W (Sum.inr t))
      = coinRejectMass k m * W (Sum.inr ()) := by
    refine Eq.trans (tsum_eq_single () fun b hb => by
      cases b
      exact absurd rfl hb) ?_
    rw [(finite_coin_step_distribution k m hm).2]
  rw [h1, h2]

/-- Adding a fixed cost preserves the probability of every event that is independent of the cost
coordinate. -/
theorem event_charge_cost_blind {α : Type} (n : ℕ) (q : CostedLaw α) (P : α × ℕ → Prop)
    (hP : ∀ (y : α × ℕ) (c c' : ℕ), P (y.1, c) ↔ P (y.1, c')) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (CostedLaw.charge n q) P
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event q fun y : α × ℕ => P y := by
  have h1 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (CostedLaw.charge n q) P
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event q (fun y : α × ℕ => P (y.1, n + y.2)) :=
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_charge_general n q P
  have h2 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event q (fun y : α × ℕ => P (y.1, n + y.2))
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event q (fun y : α × ℕ => P y) := by
    refine Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr fun y => ?_
    exact (hP y (n + y.2) y.2).trans Iff.rfl
  exact h1.trans h2

/-- Run the bounded decoder for at most `fuel` attempts, recording `k` bits of cost per executed
attempt. -/
noncomputable def finiteCoinRun (k m fuel : ℕ) :
    CostedLaw (RandomizedExecution.Configuration Unit (Fin m)) :=
  (runFor (finiteCoinNext k m) fuel (Sum.inr ())).map fun x => (x.1, k * x.2)

/-- Scaling the attempt count into a bit cost preserves each configuration event's probability. -/
theorem event_coinRun (k m fuel : ℕ) (c : RandomizedExecution.Configuration Unit (Fin m)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k m fuel) (fun z => z.1 = c)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (finiteCoinNext k m) fuel (Sum.inr ())) (fun x => x.1 = c) := by
  rw [finiteCoinRun, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]

/-- After `fuel` attempts, the pending probability is the rejection probability raised to
`fuel`. -/
theorem finiteCoinRun_pending (k m fuel : ℕ) (hm : m ≤ 2 ^ k) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (finiteCoinNext k m) fuel (Sum.inr ())) (fun x => x.1 = Sum.inr ())
      = (coinRejectMass k m) ^ fuel := by
  induction fuel with
  | zero =>
      rw [runFor_zero, pow_zero]
      exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret_one (Sum.inr ()) rfl
  | succ fuel ih =>
      have hbind : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
            (PMF.bind (tick (finiteCoinNext k m) (Sum.inr ()))
              fun x => CostedLaw.charge x.2 (runFor (finiteCoinNext k m) fuel x.1))
            (fun y => y.1 = Sum.inr ())
          = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (tick (finiteCoinNext k m) (Sum.inr ()))
            (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
              (CostedLaw.charge x.2 (runFor (finiteCoinNext k m) fuel x.1))
              (fun y => y.1 = Sum.inr ())) :=
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_bind_general _ _ _
      have hWinl : ∀ i : Fin m,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (CostedLaw.charge 1 (runFor (finiteCoinNext k m) fuel (Sum.inl i)))
              (fun y => y.1 = Sum.inr ())
            = 0 := by
        intro i
        rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_charge_general,
            runFor_halted]
        exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret_zero _
            (fun h => by simp at h)
      have hWinr : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
            (CostedLaw.charge 1 (runFor (finiteCoinNext k m) fuel (Sum.inr ())))
            (fun y => y.1 = Sum.inr ())
          = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (finiteCoinNext k m) fuel (Sum.inr ()))
              (fun x => x.1 = Sum.inr ()) :=
        event_charge_cost_blind 1 _ (fun z => z.1 = Sum.inr ()) fun _ _ _ => Iff.rfl
      show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (finiteCoinNext k m) (fuel + 1) (Sum.inr ()))
          (fun x => x.1 = Sum.inr ()) = _
      rw [show runFor (finiteCoinNext k m) (fuel + 1) (Sum.inr ())
          = PMF.bind (tick (finiteCoinNext k m) (Sum.inr ()))
              fun x => CostedLaw.charge x.2 (runFor (finiteCoinNext k m) fuel x.1) from rfl,
        hbind, show tick (finiteCoinNext k m) (Sum.inr ())
          = PMF.map (fun c => (c, 1)) (finiteCoinNext k m ()) from rfl,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map, finiteCoinNext_expectation k m hm]
      (try dsimp only)
      rw [Finset.sum_eq_zero fun i _ => hWinl i, hWinr, ih, mul_zero, zero_add, pow_succ,
        mul_comm]

/-- For each label, its return probability multiplied by `m`, plus the geometric pending mass,
equals one. -/
theorem finiteCoinRun_halt_invariant (k m fuel : ℕ) (hm : m ≤ 2 ^ k) (i : Fin m) :
    ((m : ℕ) : ℝ≥0∞) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (runFor (finiteCoinNext k m) fuel (Sum.inr ())) (fun x => x.1 = Sum.inl i)
      + (coinRejectMass k m) ^ fuel = 1 := by
  induction fuel with
  | zero =>
      rw [runFor_zero,
          Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret_zero _
          (fun h => by simp at h), pow_zero]
      simp
  | succ fuel ih =>
      have hbind : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
            (PMF.bind (tick (finiteCoinNext k m) (Sum.inr ()))
              fun x => CostedLaw.charge x.2 (runFor (finiteCoinNext k m) fuel x.1))
            (fun y => y.1 = Sum.inl i)
          = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (tick (finiteCoinNext k m) (Sum.inr ()))
            (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
              (CostedLaw.charge x.2 (runFor (finiteCoinNext k m) fuel x.1))
              (fun y => y.1 = Sum.inl i)) :=
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_bind_general _ _ _
      have hWinl : ∀ j : Fin m,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (CostedLaw.charge 1 (runFor (finiteCoinNext k m) fuel (Sum.inl j)))
              (fun z => z.1 = Sum.inl i)
            = if j = i then 1 else 0 := by
        intro j
        rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_charge_general,
            runFor_halted, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret]
        by_cases hji : j = i
        · subst hji
          simp
        · rw [if_neg hji, if_neg]
          intro h
          exact hji (by simpa using h)
      have hWinr : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (CostedLaw.charge 1 (runFor (finiteCoinNext k m) fuel
              (Sum.inr ()))) (fun z => z.1 = Sum.inl i)
          = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (finiteCoinNext k m) fuel (Sum.inr ()))
              (fun x => x.1 = Sum.inl i) :=
        event_charge_cost_blind 1 _ (fun z => z.1 = Sum.inl i) fun _ _ _ => Iff.rfl
      show ((m : ℕ) : ℝ≥0∞) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
          (runFor (finiteCoinNext k m) (fuel + 1) (Sum.inr ())) (fun x => x.1 = Sum.inl i)
        + (coinRejectMass k m) ^ (fuel + 1) = 1
      rw [show runFor (finiteCoinNext k m) (fuel + 1) (Sum.inr ())
          = PMF.bind (tick (finiteCoinNext k m) (Sum.inr ()))
              fun x => CostedLaw.charge x.2 (runFor (finiteCoinNext k m) fuel x.1) from rfl,
        hbind, show tick (finiteCoinNext k m) (Sum.inr ())
          = PMF.map (fun c => (c, 1)) (finiteCoinNext k m ()) from rfl,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map, finiteCoinNext_expectation k m hm]
      (try dsimp only)
      rw [Finset.sum_congr rfl (fun j _ => hWinl j), hWinr,
        Finset.sum_ite_eq' Finset.univ i fun _ => (1 : ℝ≥0∞), if_pos (Finset.mem_univ i),
        pow_succ]
      have htotal := finiteCoinNext_total k m hm
      calc ((m : ℕ) : ℝ≥0∞) * (((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ * 1
              + coinRejectMass k m * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
                (runFor (finiteCoinNext k m) fuel (Sum.inr ())) (fun x => x.1 = Sum.inl i))
          + (coinRejectMass k m) ^ fuel * coinRejectMass k m
          = (((m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹)
              + coinRejectMass k m * (((m : ℕ) : ℝ≥0∞) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
                  (runFor (finiteCoinNext k m) fuel (Sum.inr ())) (fun x => x.1 = Sum.inl i)
                + (coinRejectMass k m) ^ fuel) := by ring
        _ = ((m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ + coinRejectMass k m * 1 := by rw [ih]
        _ = 1 := by rw [mul_one]; exact htotal

/-- The pending mass is geometric, and every label has return probability `(1 - coinRejectMass k
m ^ fuel) / m`. -/
theorem finite_coin_return_and_pending (k m fuel : ℕ) (hm0 : 0 < m) (hm : m ≤ 2 ^ k) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k m fuel) (fun x => x.1 = Sum.inr ())
      = (coinRejectMass k m) ^ fuel ∧
      ∀ i : Fin m, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k m fuel) (fun x => x.1 = Sum.inl i)
        = (1 - (coinRejectMass k m) ^ fuel) / ((m : ℕ) : ℝ≥0∞) := by
  refine ⟨(event_coinRun k m fuel (Sum.inr ())).trans (finiteCoinRun_pending k m fuel hm), ?_⟩
  intro i
  have hinv := finiteCoinRun_halt_invariant k m fuel hm i
  rw [← event_coinRun k m fuel (Sum.inl i)] at hinv
  have hne : ((m : ℕ) : ℝ≥0∞) ≠ 0 := by
    intro h
    have h0 := Nat.cast_eq_zero.mp h
    omega
  have hntop : ((m : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hq : coinRejectMass k m ≤ 1 := by
    have hb0 : ((2 ^ k : ℕ) : ℝ≥0∞) ≠ 0 := by simp
    have h1 : ((2 ^ k - m : ℕ) : ℝ≥0∞) ≤ ((2 ^ k : ℕ) : ℝ≥0∞) :=
      Nat.cast_le.mpr (Nat.sub_le _ _)
    rw [coinRejectMass, div_eq_mul_inv]
    calc ((2 ^ k - m : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹
        ≤ ((2 ^ k : ℕ) : ℝ≥0∞) * ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := mul_le_mul' h1 (le_refl _)
      _ = 1 := ENNReal.mul_inv_cancel hb0 (ENNReal.natCast_ne_top _)
  have hqtop : (coinRejectMass k m) ^ fuel ≠ ⊤ := by
    intro h
    have h2 : (⊤ : ℝ≥0∞) ≤ 1 := by
      rw [← h]
      exact pow_le_one' hq fuel
    exact absurd h2 (by simp)
  have hMX : ((m : ℕ) : ℝ≥0∞)
        * ((1 - (coinRejectMass k m) ^ fuel) * ((m : ℕ) : ℝ≥0∞)⁻¹)
      + (coinRejectMass k m) ^ fuel = 1 := by
    rw [mul_comm ((1 - (coinRejectMass k m) ^ fuel)) ((m : ℕ) : ℝ≥0∞)⁻¹, ← mul_assoc,
      ENNReal.mul_inv_cancel hne hntop, one_mul, tsub_add_cancel_of_le (pow_le_one' hq fuel)]
  have hEqM : ((m : ℕ) : ℝ≥0∞) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k m fuel)
        (fun z => z.1 = Sum.inl i)
      = ((m : ℕ) : ℝ≥0∞)
          * ((1 - (coinRejectMass k m) ^ fuel) * ((m : ℕ) : ℝ≥0∞)⁻¹) :=
    ((WithTop.add_right_inj hqtop).mp (hinv.trans hMX.symm))
  have hle1 := (ENNReal.mul_le_mul_iff_right hne hntop).mp (le_of_eq hEqM)
  have hle2 := (ENNReal.mul_le_mul_iff_right hne hntop).mp (le_of_eq hEqM.symm)
  rw [div_eq_mul_inv]
  exact le_antisymm hle1 hle2

/-- The probability of surviving `n` bounded-decoder attempts is the `n`th power of the
rejection mass. -/
theorem finiteSurvival_finiteCoinNext (k m n : ℕ) (hm : m ≤ 2 ^ k) :
    finiteSurvival (finiteCoinNext k m) n (Sum.inr ())
      = (coinRejectMass k m) ^ n := by
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (finiteCoinNext k m) n (Sum.inr ()))
      (fun x => ∃ s, x.1 = Sum.inr s) = _
  have hiff : ∀ x : RandomizedExecution.Configuration Unit (Fin m) × ℕ,
      (∃ s, x.1 = Sum.inr s) ↔ (x.1 = Sum.inr ()) := by
    intro x
    rcases x with ⟨c, _⟩
    cases c with
    | inl i => simp
    | inr t =>
        cases t
        simp
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr hiff]
  exact finiteCoinRun_pending k m n hm

/-- The run costs at most `fuel * k` bits, with expected cost `k` times the finite geometric
survival sum. -/
theorem finite_coin_actual_bit_cost (k m fuel : ℕ) (hm : m ≤ 2 ^ k) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (finiteCoinRun k m fuel) (fuel * k) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (finiteCoinRun k m fuel)
        = ((k : ℕ) : ℝ≥0∞) * ∑ n ∈ Finset.range fuel, (coinRejectMass k m) ^ n := by
  constructor
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    have hy2 : y.2 ≤ fuel := RandomizedExecution.runFor_bounded _ fuel _ y hy
    calc k * y.2 ≤ k * fuel := Nat.mul_le_mul_left k hy2
      _ = fuel * k := Nat.mul_comm k fuel
  · have h1 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (finiteCoinRun k m fuel)
        = ((k : ℕ) : ℝ≥0∞)
            * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (runFor (finiteCoinNext k m) fuel (Sum.inr ())) := by
      show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
          (PMF.map (fun x : RandomizedExecution.Configuration Unit (Fin m) × ℕ =>
              (x.1, k * x.2)) _)
          (fun x => (x.2 : ℝ≥0∞))
        = ((k : ℕ) : ℝ≥0∞) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
            (runFor (finiteCoinNext k m) fuel (Sum.inr ())) (fun x => (x.2 : ℝ≥0∞))
      have hcongr : ∀ a : RandomizedExecution.Configuration Unit (Fin m) × ℕ,
          (((a.1, k * a.2).2 : ℕ) : ℝ≥0∞)
            = ((k : ℕ) : ℝ≥0∞) * ((a.2 : ℕ) : ℝ≥0∞) :=
        fun a => Nat.cast_mul k a.2
      rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hcongr,
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
    rw [h1, finite_stopping_cost_tail_sum]
    exact congrArg (fun t => ((k : ℕ) : ℝ≥0∞) * t)
      (Finset.sum_congr rfl fun n _ => finiteSurvival_finiteCoinNext k m n hm)

/-- Every finite sum of powers of one half is at most two in the extended nonnegative reals. -/
private theorem half_pow_sum_le_two (fuel : ℕ) :
    ∑ n ∈ Finset.range fuel, ((1 / 2 : ℝ≥0∞) ^ n) ≤ 2 := by
  have hinv : ∀ j : ℕ, ∑ n ∈ Finset.range j, ((1 / 2 : ℝ≥0∞) ^ n)
      + 2 * ((1 / 2 : ℝ≥0∞) ^ j) = 2 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Finset.sum_range_succ]
        have h2 : 2 * ((1 / 2 : ℝ≥0∞) ^ (j + 1)) = (1 / 2 : ℝ≥0∞) ^ j := by
          calc 2 * ((1 / 2 : ℝ≥0∞) ^ (j + 1))
              = 2 * ((1 / 2 : ℝ≥0∞) ^ j * (1 / 2 : ℝ≥0∞)) := by rw [pow_succ]
            _ = (2 * (1 / 2 : ℝ≥0∞)) * (1 / 2 : ℝ≥0∞) ^ j := by
                rw [mul_comm ((1 / 2 : ℝ≥0∞) ^ j) ((1 / 2 : ℝ≥0∞)), ← mul_assoc]
            _ = (1 / 2 : ℝ≥0∞) ^ j := by
                rw [show (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 from by
                  rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by simp)], one_mul]
        rw [h2, add_assoc, ← two_mul, ih]
  calc ∑ n ∈ Finset.range fuel, ((1 / 2 : ℝ≥0∞) ^ n)
      ≤ (∑ n ∈ Finset.range fuel, ((1 / 2 : ℝ≥0∞) ^ n)) + 2 * ((1 / 2 : ℝ≥0∞) ^ fuel) :=
        le_add_right le_rfl
    _ = 2 := hinv fuel

/-- Using `Nat.clog 2 m` bits per attempt gives rejection probability at most one half, pending
mass at most `2⁻fuel`, and expected cost at most twice that bit length. -/
theorem finite_coin_effective_cutoff (m fuel : ℕ) (hm0 : 0 < m) :
    m ≤ 2 ^ Nat.clog 2 m ∧ coinRejectMass (Nat.clog 2 m) m ≤ 1 / 2 ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun (Nat.clog 2 m) m fuel) (fun x => x.1 = Sum.inr ())
        ≤ (1 / 2 : ℝ≥0∞) ^ fuel ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (finiteCoinRun (Nat.clog 2 m) m fuel)
        ≤ ((2 * Nat.clog 2 m : ℕ) : ℝ≥0∞) := by
  have hb : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num : 1 < 2) m
  have hq : coinRejectMass (Nat.clog 2 m) m ≤ 1 / 2 := by
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · have hm1 : m = 1 := by omega
        subst hm1
        rw [Nat.clog_one_right]
        norm_num [coinRejectMass]
      · have hK1 : 1 ≤ Nat.clog 2 m :=
          Nat.clog_pos (by norm_num : 1 < 2) (by omega : 1 < m)
        set hK := Nat.clog 2 m with hKdef
        have hlt : 2 ^ (hK - 1) < m :=
          Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (by omega : 1 < m)
        have hgen : ∀ K : ℕ, 1 ≤ K → 2 ^ (K - 1) * 2 = 2 ^ K := by
          intro K hK1'
          conv_rhs => rw [show K = (K - 1) + 1 from by omega]
          rw [Nat.pow_succ, Nat.mul_comm]
        have h4 : 2 ^ (hK - 1) * 2 = 2 ^ hK := hgen hK hK1
        have hsub : 2 ^ hK - m ≤ 2 ^ (hK - 1) := by
          have h5 := Nat.sub_le_sub_left (le_of_lt hlt)
          have h6 : 2 ^ hK - 2 ^ (hK - 1) = 2 ^ (hK - 1) := by
            rw [← h4]
            omega
          rw [← h6]
          exact h5 _
        have h2r : (2 ^ hK - m) * 2 ≤ 2 ^ hK := by omega
        have hhalf : (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 := by
          rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by simp)]
        have h7 : 2 * (2 ^ hK - m) ≤ 2 ^ hK := by omega
        have hY : ((2 ^ hK - m : ℕ) : ℝ≥0∞)
            ≤ (1 / 2 : ℝ≥0∞) * ((2 ^ hK : ℕ) : ℝ≥0∞) := by
          have key : ((2 : ℝ≥0∞)) * ((2 ^ hK - m : ℕ) : ℝ≥0∞)
              ≤ ((2 : ℝ≥0∞)) * ((1 / 2 : ℝ≥0∞) * ((2 ^ hK : ℕ) : ℝ≥0∞)) := by
            have h6 : (2 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) * ((2 ^ hK : ℕ) : ℝ≥0∞))
                = ((2 ^ hK : ℕ) : ℝ≥0∞) := by
              rw [← mul_assoc, hhalf, one_mul]
            rw [h6]
            calc ((2 : ℝ≥0∞)) * ((2 ^ hK - m : ℕ) : ℝ≥0∞)
                = (((2 : ℕ) : ℝ≥0∞) * ((2 ^ hK - m : ℕ) : ℝ≥0∞)) := rfl
              _ ≤ ((2 ^ hK : ℕ) : ℝ≥0∞) := by exact_mod_cast h7
          exact (ENNReal.mul_le_mul_iff_right
            (by norm_num : ((2 : ℕ) : ℝ≥0∞) ≠ 0) (by simp)).mp key
        rw [coinRejectMass, div_eq_mul_inv]
        calc ((2 ^ hK - m : ℕ) : ℝ≥0∞) * ((2 ^ hK : ℕ) : ℝ≥0∞)⁻¹
            ≤ ((1 / 2 : ℝ≥0∞) * ((2 ^ hK : ℕ) : ℝ≥0∞)) * ((2 ^ hK : ℕ) : ℝ≥0∞)⁻¹ :=
              mul_le_mul' hY (le_refl _)
          _ = 1 / 2 := by
              rw [mul_assoc, ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _),
                mul_one]
  refine ⟨hb, hq, ?_, ?_⟩
  · rw [event_coinRun _ _ _ (Sum.inr ()), finiteCoinRun_pending _ _ _ hb]
    exact ENNReal.pow_le_pow_left hq
  · have h8 := (finite_coin_actual_bit_cost (Nat.clog 2 m) m fuel hb).2
    rw [h8]
    have hsum : ∑ n ∈ Finset.range fuel, (coinRejectMass (Nat.clog 2 m) m) ^ n
        ≤ ∑ n ∈ Finset.range fuel, ((1 / 2 : ℝ≥0∞) ^ n) :=
      Finset.sum_le_sum fun n _ => ENNReal.pow_le_pow_left hq
    have hgeo := half_pow_sum_le_two fuel
    calc ((Nat.clog 2 m : ℕ) : ℝ≥0∞)
          * ∑ n ∈ Finset.range fuel, (coinRejectMass (Nat.clog 2 m) m) ^ n
        ≤ ((Nat.clog 2 m : ℕ) : ℝ≥0∞) * ∑ n ∈ Finset.range fuel, ((1 / 2 : ℝ≥0∞) ^ n) :=
          mul_le_mul' (le_refl _) hsum
      _ ≤ ((Nat.clog 2 m : ℕ) : ℝ≥0∞) * 2 :=
          mul_le_mul' (le_refl _) hgeo
      _ = ((2 * Nat.clog 2 m : ℕ) : ℝ≥0∞) := by
          have h2m : ((Nat.clog 2 m : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)
              = (((Nat.clog 2 m) * 2 : ℕ) : ℝ≥0∞) := by
            rw [show ((2 : ℝ≥0∞)) = ((2 : ℕ) : ℝ≥0∞) from rfl, Nat.cast_mul]
          have h3m : (((Nat.clog 2 m) * 2 : ℕ) : ℝ≥0∞)
              = ((2 * Nat.clog 2 m : ℕ) : ℝ≥0∞) := by
            rw [Nat.mul_comm]
          rw [h2m, h3m]
