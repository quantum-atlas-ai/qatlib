/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.HspRecovery.OpenSieve.RepresentationSieveContinuationDefs

/-!
# Representation transport and sieve continuation

This module connects actual dihedral record measurements to irreducible representation labels
and fixed-subspace rows. It proves the transported mass formulas associated with Proposition 8.1
of [Kuperberg2005], together with staged marginal laws and record extraction identities.

The continuation results give exact probabilities before any combining layers, bounds on record
counts, and the shape and resource ledger of bitwise descent. Decorated labels and their shadows
establish `topBitCoupling` through disjoint supports and affine top-bit formulas.

## Main statements

* `clause1_endpoint`: representation transport, marginal laws, extraction, and circuit counts.
* `clause2_endpoint`: staged combining laws, width bounds, fresh probabilities, and record
  counts.
* `topBitCoupling`: coupling of skeleton top bits to disjoint support bundles.
* `clause3_endpoint`: candidate reconstruction and descent resource accounting.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open Qatlib.Concepts.HspRecovery.SieveAlgorithm

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.HspRecovery.OpenSieve

open Qatlib
open scoped Classical BigOperators ENNReal

/-- Every nonzero modulus satisfies the representation transport target for reflection-hiding
dihedral oracles. -/
theorem clause1_representation_record_bridge (N : ℕ) [NeZero N] :
    RepTransportTarget N := by
  intro S _ _ _ f s hf Label _ _ family
  obtain ⟨toLabel, toRowNat, stages, hrow, hjoint, hlabel, hst0, hst1, hst2,
    hgamma, hextract, hq, hg⟩ :=
    g1 N S (inferInstance : Fintype S) (inferInstance : DecidableEq S)
      (inferInstance : AddCommGroup S) f s hf Label
      (inferInstance : Fintype Label) (inferInstance : DecidableEq Label) family
  let w : RepTransportWitness f s family :=
    { toLabel := toLabel, toRowNat := toRowNat, stages := stages,
      row_lt := hrow, joint := hjoint, labelMass := hlabel, stage0 := hst0,
      stage1 := hst1, stage2 := hst2, extraction := hgamma }
  exact ⟨w, hst0, hst1, hst2, hq, hg⟩

/-- A reflection-hiding oracle has a representation transport witness whose initial stage is
`actualRecordFiniteLaw`. -/
theorem clause1_bridge_stage0_is_actual_record {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S)
    {Label : Type} [Fintype Label] [DecidableEq Label]
    (family : IrrepFamily N Label) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) :
    ∃ w : RepTransportWitness f s family, w.stages.law 0 = actualRecordFiniteLaw f := by
  obtain ⟨w, hst0, _, _, _, _⟩ :=
    clause1_representation_record_bridge N S f s hf Label family
  exact ⟨w, hst0⟩

/-- Each fixed-subspace row has representation joint mass equal to the representation dimension
divided by `N`, as in [Kuperberg, Proposition 8.1][Kuperberg2005]. -/
theorem clause1_joint_mass_is_prop8_1 {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) {Label : Type}
    [Fintype Label] [DecidableEq Label] (family : IrrepFamily N Label)
    (s : ZMod N) (w : RepTransportWitness f s family) (V : Label)
    (row : Fin (dimFixed (family.irrep V) s)) :
    repJointMass (family.irrep V) row.val = ((family.irrep V).dim : ℝ) / N := by
  have h := w.joint V row
  simpa only [repJointMass] using! h

/-- Summing the actual record masses over a transported representation label and row gives the
representation dimension divided by `N`. -/
theorem clause1_transported_joint_law {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) {Label : Type}
    [Fintype Label] [DecidableEq Label] (family : IrrepFamily N Label)
    (s : ZMod N) (w : RepTransportWitness f s family) (V : Label)
    (row : Fin (dimFixed (family.irrep V) s)) :
    (∑' q : ZMod N × Bool × S,
        if w.toLabel q.1 = V ∧ w.toRowNat (q.1, q.2.1) = row.val then
          ENNReal.toReal (actualRecordFiniteLaw f q) else 0)
      = ((family.irrep V).dim : ℝ) / N := by
  have h := w.joint V row
  simpa only [repJointMass] using! h.symm

/-- The transported label marginal equals `repLabelMass`, which is the representation dimension
times its fixed-subspace dimension divided by `N` [Kuperberg, Proposition
8.1][Kuperberg2005]. -/
theorem clause1_label_mass_is_prop8_1 {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) {Label : Type}
    [Fintype Label] [DecidableEq Label] (family : IrrepFamily N Label)
    (s : ZMod N) (w : RepTransportWitness f s family) (V : Label) :
    (∑' q : ZMod N × Bool × S,
        if w.toLabel q.1 = V then ENNReal.toReal (actualRecordFiniteLaw f q) else 0)
      = repLabelMass (family.irrep V) s ∧
    repLabelMass (family.irrep V) s =
      ((family.irrep V).dim : ℝ) * dimFixed (family.irrep V) s / N := by
  refine ⟨(w.labelMass V).symm, ?_⟩
  unfold repLabelMass
  field_simp

/-- The row assigned by a transport witness lies below the corresponding fixed-subspace
dimension. -/
theorem clause1_row_index_in_fixed_subspace {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) {Label : Type}
    [Fintype Label] [DecidableEq Label] (family : IrrepFamily N Label)
    (s : ZMod N) (w : RepTransportWitness f s family) (k : ZMod N) (t : Bool) :
    w.toRowNat (k, t) < dimFixed (family.irrep (w.toLabel k)) s :=
  w.row_lt k t

/-- A transport witness has uniform label-bit masses `1 / (2 * N)` at stage one and uniform
label masses `1 / N` at stage two. -/
theorem clause1_staged_marginals {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) {Label : Type}
    [Fintype Label] [DecidableEq Label] (family : IrrepFamily N Label)
    (s : ZMod N) (w : RepTransportWitness f s family) :
    (∀ k : ZMod N, ∀ t : Bool, ENNReal.toReal (w.stages.law 1 (k, t)) = 1 / (2 * N)) ∧
      (∀ k : ZMod N, ENNReal.toReal (w.stages.law 2 k) = 1 / N) :=
  ⟨w.stage1, w.stage2⟩

/-- An actual combining layer applies `actualLayerCombineLaw` to the pairs selected by
`pairWindowMod`. -/
theorem clause2_actual_layer_is_layer_combine {N : ℕ} (a q : ℕ)
    (L : List (ActualHalfWidthRecord N)) :
    actualLayerCombine a q L =
      actualLayerCombineLaw a
        (pairWindowMod (N := N) (q := q) ActualHalfWidthRecord.label L) := rfl

/-- The actual combining run has intermediate laws starting at the fresh-record distribution and
evolving by one combining layer per stage. -/
theorem clause2_actual_stage_law {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 m : ℕ) :
    ∃ (stageLaw : Fin (m + 1) → PMF (List (ActualHalfWidthRecord N))),
      stageLaw 0 = actualHalfWidthRecordLaw f w L0 ∧
      (∀ j : Fin m, stageLaw j.succ = (stageLaw j.castSucc).bind (actualLayerCombine a q)) ∧
      stageLaw ⟨m, by omega⟩ =
        (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q m) := by
  refine ⟨fun j => (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q j.val),
    ?_, ?_, rfl⟩
  · show (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q 0) = _
    exact PMF.bind_pure _
  · intro j
    show (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q (j.val + 1)) =
      ((actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q j.val)).bind
        (actualLayerCombine a q)
    rw [PMF.bind_bind]
    rfl

/-- Combining two actual records subtracts their labels and divides the sum of their widths by
`a` using natural-number division. -/
theorem clause2_combine_actual_records {N : ℕ} (a : ℕ) (r₁ r₂ : ActualHalfWidthRecord N) :
    combineActualRecords a r₁ r₂ =
      ⟨r₁.label - r₂.label, (r₁.width + r₂.width) / a⟩ := rfl

/-- For positive `a`, the combined width satisfies the lower and strict upper inequalities
characterizing the floor of the parent-width sum divided by `a`. -/
theorem clause2_child_width_floor_division {N : ℕ} (a : ℕ) (r₁ r₂ : ActualHalfWidthRecord N)
    (ha : 1 ≤ a) :
    a * (combineActualRecords a r₁ r₂).width ≤ r₁.width + r₂.width ∧
      r₁.width + r₂.width < a * ((combineActualRecords a r₁ r₂).width + 1) := by
  have ha0 : 0 < a := by omega
  change a * ((r₁.width + r₂.width) / a) ≤ r₁.width + r₂.width ∧
    r₁.width + r₂.width < a * ((r₁.width + r₂.width) / a + 1)
  constructor
  · calc a * ((r₁.width + r₂.width) / a) = ((r₁.width + r₂.width) / a) * a :=
        Nat.mul_comm _ _
    _ ≤ r₁.width + r₂.width := Nat.div_mul_le_self _ _
  · have hlt : (r₁.width + r₂.width) / a < (r₁.width + r₂.width) / a + 1 :=
      Nat.lt_succ_self _
    have h' : r₁.width + r₂.width < ((r₁.width + r₂.width) / a + 1) * a :=
      (Nat.div_lt_iff_lt_mul ha0).mp hlt
    rw [Nat.mul_comm]
    exact h'

/-- For positive `a`, the combined width is at most the sum of the parent widths; for `a ≥ 2`,
twice the combined width is at most that sum. -/
theorem clause2_width_reduction {N : ℕ} (a : ℕ) (r₁ r₂ : ActualHalfWidthRecord N)
    (ha : 1 ≤ a) :
    (combineActualRecords a r₁ r₂).width ≤ r₁.width + r₂.width ∧
      (2 ≤ a → 2 * (combineActualRecords a r₁ r₂).width ≤ r₁.width + r₂.width) := by
  have ha0 : 0 < a := by omega
  change (r₁.width + r₂.width) / a ≤ r₁.width + r₂.width ∧
    (2 ≤ a → 2 * ((r₁.width + r₂.width) / a) ≤ r₁.width + r₂.width)
  constructor
  · exact Nat.div_le_self _ _
  · intro h2
    calc 2 * ((r₁.width + r₂.width) / a) = ((r₁.width + r₂.width) / a) * 2 :=
          Nat.mul_comm _ _
      _ ≤ ((r₁.width + r₂.width) / a) * a :=
          Nat.mul_le_mul_left ((r₁.width + r₂.width) / a) h2
      _ ≤ r₁.width + r₂.width := Nat.div_mul_le_self _ _

/-- Twice the number of selected pairs is at most the input length, and the resulting unpaired
count is at most the input length. -/
theorem clause2_pair_window_odd_even {N : ℕ} (q : ℕ) {α : Type} [DecidableEq α]
    (label : α → ZMod N) (L : List α) :
    (pairWindowMod q label L).length * 2 ≤ L.length ∧
      L.length - (pairWindowMod q label L).length * 2 ≤ L.length :=
  clause2_pairWindowMod_length q label L

/-- An element returned by `List.find?` satisfies the Boolean search predicate. -/
private theorem find?_eq_some_pred {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), l.find? p = some a → p a = true := by
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons b l ih =>
    intro a h
    by_cases hb : p b = true
    · simp [hb] at h
      subst h
      exact hb
    · simp [hb] at h
      exact ih a h

/-- Every pair selected by `pairWindowMod` has labels satisfying `windowAgreeMod`. -/
theorem clause6_pair_window_agrees {N q : ℕ} {α : Type} [DecidableEq α]
    (label : α → ZMod N) (L : List α) (p : α × α)
    (hp : p ∈ pairWindowMod q label L) :
    windowAgreeMod N q (label p.1) (label p.2) := by
  fun_induction pairWindowMod q label L
  case case1 => simp at hp
  case case2 r rest h ih =>
    exact ih hp
  case case3 r rest r' h ih =>
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · have hdec : (fun r' => decide (windowAgreeMod N q (label r) (label r'))) r' = true :=
        find?_eq_some_pred (fun r' => decide (windowAgreeMod N q (label r) (label r')))
          rest r' h
      exact of_decide_eq_true hdec
    · exact ih hp

/-- Agreement of the parent labels modulo `q` makes their combined label divisible by `q` in
`ZMod N`. -/
theorem clause6_combined_label_divisible {N : ℕ} [NeZero N] (a q : ℕ)
    (r₁ r₂ : ActualHalfWidthRecord N)
    (h : windowAgreeMod N q r₁.label r₂.label) :
    (q : ZMod N) ∣ (combineActualRecords a r₁ r₂).label :=
  h

/-- Every child formed from a pair selected by an actual layer has label divisible by `q` in
`ZMod N`. -/
theorem clause6_actual_layer_children_divisible {N : ℕ} [NeZero N] (a q : ℕ)
    (L : List (ActualHalfWidthRecord N)) :
    ∀ p ∈ pairWindowMod (N := N) (q := q) ActualHalfWidthRecord.label L,
      (q : ZMod N) ∣ (combineActualRecords a p.1 p.2).label := by
  intro p hp
  exact clause6_combined_label_divisible a q p.1 p.2 (clause6_pair_window_agrees _ L p hp)

/-- Choosing `L0` as the fresh-record count gives twice `L0` as the total sieve record count. -/
theorem clause2_sample_and_record_counts (m L0 : ℕ) (h : L0 = sieveFreshRecordCount m) :
    L0 = sieveFreshRecordCount m ∧ 2 * L0 = sieveRecordCount m := by
  constructor
  · exact h
  · rw [h]
    rfl

/-- With zero combining layers, the actual run is exactly the fresh half-width record law. -/
theorem clause2_actual_run_at_zero {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 : ℕ) :
    (actualCombinedRun f a q w L0 0) = actualHalfWidthRecordLaw f w L0 := by
  show (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q 0) = _
  exact PMF.bind_pure _

/-- The ideal-hit mass is the probability of `true` in the Boolean ideal-hit event law. -/
theorem clause2_ideal_hit_mass_is_computed {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 m : ℕ) :
    actualIdealHitMass f a q w L0 m = actualIdealHitEvent f a q w L0 m true := rfl

/-- The actual failure mass is one minus the actual ideal-hit mass. -/
theorem clause2_failure_mass_eq {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 m : ℕ) :
    actualFailureMass f a q w L0 m = 1 - actualIdealHitMass f a q w L0 m := rfl

/-- The actual ideal-hit mass is at most one. -/
theorem clause2_ideal_hit_mass_le_one {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (a q w L0 m : ℕ) :
    actualIdealHitMass f a q w L0 m ≤ 1 := by
  unfold actualIdealHitMass actualIdealHitEvent
  exact PMF.coe_le_one
    ((actualCombinedRun f a q w L0 m).map
      (fun L => decide (hasIdealHit L))) true

/-- Summing a probability mass function against the indicator of a singleton returns its mass at
that point. -/
private theorem pmf_single_mass {α : Type} [Fintype α] (p : PMF α) (a : α) :
    (∑' y : α, p y * massIndicator (y = a)) = p a := by
  refine Eq.trans (tsum_eq_single a ?_) (by simp [massIndicator])
  intro y hy
  by_cases h : y = a
  · exact absurd h hy
  · simp [massIndicator, h]

/-- For a reflection-hiding oracle, each actual record label has mass `1 / N`. -/
theorem clause2_actual_label_mass {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : ZMod N) :
    actualLabelLaw f k = ENNReal.ofReal (1 / (N : ℝ)) := by
  have hbit : ∀ t : Bool,
      (∑' z : S, actualRecordFiniteLaw f (k, (t, z))) =
        ENNReal.ofReal (1 / (2 * (N : ℝ))) :=
    fun t => clause27_bitMarginal S f s hf k t
  have hmarg : ∀ t : Bool,
      (actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => (q.1, q.2.1)) (k, t) =
        ∑' z : S, actualRecordFiniteLaw f (k, (t, z)) :=
    fun t => clause27_map_fst2_apply (actualRecordFiniteLaw f) k t
  have hlabel : actualLabelLaw f
      = ((actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => (q.1, q.2.1))).map
        Prod.fst := by
    ext k'
    show (actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => q.1) k' = _
    rw [PMF.map_comp]
    congr 1
  rw [hlabel, clause27_map_fst_apply]
  simp_rw [hmarg, hbit]
  have hbool : (∑' t : Bool, ENNReal.ofReal (1 / (2 * (N : ℝ))))
      = ENNReal.ofReal (1 / (2 * (N : ℝ))) + ENNReal.ofReal (1 / (2 * (N : ℝ))) := by
    rw [tsum_fintype, Fintype.sum_bool]
  rw [hbool]
  rw [← ENNReal.ofReal_add (p := 1 / (2 * (N : ℝ))) (q := 1 / (2 * (N : ℝ)))
    (by positivity) (by positivity)]
  have hval : (1 / (2 * (N : ℝ))) + (1 / (2 * (N : ℝ))) = 1 / (N : ℝ) := by
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.pos N).ne'
    field_simp [hN']; ring
  rw [hval]

/-- For a reflection-hiding oracle, the label marginal of a fresh actual record is uniform on
`ZMod N`. -/
theorem clause2_fresh_record_label_mass {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (w : ℕ) (k : ZMod N) :
    (∑' r : ActualHalfWidthRecord N, (actualFreshRecord f w) r *
      massIndicator (r.label = k)) = ENNReal.ofReal (1 / (N : ℝ)) := by
  have hmap := pmf_map_expectation (actualRecordFiniteLaw f)
    (fun q : ZMod N × Bool × S => ⟨q.1, w⟩)
    (fun r : ActualHalfWidthRecord N => massIndicator (r.label = k))
  have hlab := pmf_map_expectation (actualRecordFiniteLaw f)
    (fun q : ZMod N × Bool × S => q.1)
    (fun k' : ZMod N => massIndicator (k' = k))
  have hmap' : (∑' r : ActualHalfWidthRecord N, (actualFreshRecord f w) r *
        massIndicator (r.label = k))
      = ∑' x : ZMod N × Bool × S, (actualRecordFiniteLaw f) x * massIndicator (x.1 = k) := by
    simpa only [actualFreshRecord, ActualHalfWidthRecord.label] using! hmap
  have hlab' : (∑' y : ZMod N, (actualLabelLaw f) y * massIndicator (y = k))
      = ∑' x : ZMod N × Bool × S, (actualRecordFiniteLaw f) x * massIndicator (x.1 = k) := by
    simpa only [actualLabelLaw] using! hlab
  calc (∑' r : ActualHalfWidthRecord N, (actualFreshRecord f w) r *
        massIndicator (r.label = k))
      = ∑' x : ZMod N × Bool × S, (actualRecordFiniteLaw f) x * massIndicator (x.1 = k) := hmap'
    _ = ∑' y : ZMod N, (actualLabelLaw f) y * massIndicator (y = k) := hlab'.symm
    _ = (actualLabelLaw f) k := pmf_single_mass (actualLabelLaw f) k
    _ = ENNReal.ofReal (1 / (N : ℝ)) := clause2_actual_label_mass f s hf k

/-- A fresh record from a reflection-hiding oracle misses the ideal label with probability `1 -
1 / N`. -/
theorem clause2_actual_miss_prob_one {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (w : ℕ) :
    actualMissProbOne f w = ENNReal.ofReal (1 - 1 / (N : ℝ)) := by
  have hmap := pmf_map_expectation (actualRecordFiniteLaw f)
    (fun q : ZMod N × Bool × S => ⟨q.1, w⟩)
    (fun r : ActualHalfWidthRecord N => massIndicator (¬ isActualIdealHit r))
  have hlab := pmf_map_expectation (actualRecordFiniteLaw f)
    (fun q : ZMod N × Bool × S => q.1)
    (fun k : ZMod N => massIndicator (¬ (k = actualIdealLabel N)))
  have hmap' : (∑' r : ActualHalfWidthRecord N, (actualFreshRecord f w) r *
        massIndicator (¬ isActualIdealHit r))
      = ∑' x : ZMod N × Bool × S, (actualRecordFiniteLaw f) x *
        massIndicator (¬ (x.1 = actualIdealLabel N)) := by
    simpa only [actualFreshRecord, isActualIdealHit, ActualHalfWidthRecord.label] using! hmap
  have hlab' : (∑' y : ZMod N, (actualLabelLaw f) y * massIndicator (¬ (y = actualIdealLabel N)))
      = ∑' x : ZMod N × Bool × S, (actualRecordFiniteLaw f) x *
        massIndicator (¬ (x.1 = actualIdealLabel N)) := by
    simpa only [actualLabelLaw] using! hlab
  have hC : (∑' k : ZMod N, (actualLabelLaw f) k * massIndicator (k = actualIdealLabel N))
      = (actualLabelLaw f) (actualIdealLabel N) :=
    pmf_single_mass (actualLabelLaw f) (actualIdealLabel N)
  have htotal : (∑' k : ZMod N, (actualLabelLaw f) k * massIndicator (¬ (k = actualIdealLabel N)))
      + (actualLabelLaw f) (actualIdealLabel N) = 1 := by
    calc (∑' k : ZMod N, (actualLabelLaw f) k * massIndicator (¬ (k = actualIdealLabel N)))
        + (actualLabelLaw f) (actualIdealLabel N)
        = (∑' k : ZMod N, (actualLabelLaw f) k * massIndicator (¬ (k = actualIdealLabel N)))
            + (∑' k : ZMod N, (actualLabelLaw f) k * massIndicator (k = actualIdealLabel N)) := by
              rw [hC]
      _ = ∑' k : ZMod N, (actualLabelLaw f) k := by
            have h2 : (∑' k : ZMod N,
                ((actualLabelLaw f) k * massIndicator (¬ (k = actualIdealLabel N))
                  + (actualLabelLaw f) k * massIndicator (k = actualIdealLabel N)))
                = ∑' k : ZMod N, (actualLabelLaw f) k := by
              apply tsum_congr
              intro k
              by_cases hk : k = actualIdealLabel N <;> simp [massIndicator, hk]
            rw [← h2]
            exact ENNReal.tsum_add.symm
      _ = 1 := PMF.tsum_coe (actualLabelLaw f)
  have hA : (∑' k : ZMod N, (actualLabelLaw f) k * massIndicator (¬ (k = actualIdealLabel N)))
      = 1 - (actualLabelLaw f) (actualIdealLabel N) :=
    ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top (actualLabelLaw f) (actualIdealLabel N)) htotal
  calc actualMissProbOne f w
      = ∑' r : ActualHalfWidthRecord N, (actualFreshRecord f w) r *
          massIndicator (¬ isActualIdealHit r) := rfl
    _ = ∑' x : ZMod N × Bool × S, (actualRecordFiniteLaw f) x *
        massIndicator (¬ (x.1 = actualIdealLabel N)) := hmap'
    _ = ∑' y : ZMod N, (actualLabelLaw f) y * massIndicator (¬ (y = actualIdealLabel N)) :=
      hlab'.symm
    _ = 1 - (actualLabelLaw f) (actualIdealLabel N) := hA
    _ = 1 - ENNReal.ofReal (1 / (N : ℝ)) := by rw [clause2_actual_label_mass f s hf]
    _ = ENNReal.ofReal (1 - 1 / (N : ℝ)) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (p := 1) (q := 1 / (N : ℝ)) (by positivity)]

/-- Prepending an ideal-hit record makes the miss weight zero; otherwise the miss weight is that
of the remaining list. -/
private theorem missWeight_cons {N : ℕ} (r : ActualHalfWidthRecord N)
    (L : List (ActualHalfWidthRecord N)) :
    idealMissWeight (r :: L) =
      if isActualIdealHit r then 0 else idealMissWeight L := by
  have hequiv : hasIdealHit (r :: L) ↔ isActualIdealHit r ∨ hasIdealHit L := by
    constructor
    · rintro ⟨r', hmem, hp⟩
      rcases List.mem_cons.mp hmem with h | h
      · exact Or.inl (h ▸ hp)
      · exact Or.inr ⟨r', h, hp⟩
    · rintro (h | ⟨r', h, hp⟩)
      · exact ⟨r, by simp, h⟩
      · exact ⟨r', by simp [h], hp⟩
  by_cases hr : isActualIdealHit r
  · have hex : hasIdealHit (r :: L) := ⟨r, by simp, hr⟩
    simp [idealMissWeight, massIndicator, hex, hr]
  · have hequiv' : hasIdealHit (r :: L) ↔ hasIdealHit L := by
      constructor
      · rintro ⟨r', hmem, hp⟩
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd (h ▸ hp) hr
        · exact ⟨r', h, hp⟩
      · rintro ⟨r', hmem, hp⟩
        exact ⟨r', by simp [hmem], hp⟩
    simp [idealMissWeight, massIndicator, hequiv', hr]

/-- For a reflection-hiding oracle, the probability that all `L0` fresh records miss the ideal
label is `(1 - 1 / N) ^ L0`. -/
theorem clause2_actual_miss_mass {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (w L0 : ℕ) :
    actualMissMass f w L0 = ENNReal.ofReal ((1 - 1 / (N : ℝ)) ^ L0) := by
  have hone : actualMissProbOne f w = ENNReal.ofReal (1 - 1 / (N : ℝ)) :=
    clause2_actual_miss_prob_one f s hf w
  have hstep : ∀ (i : ℕ), actualMissMass f w (i + 1)
      = actualMissMass f w i * actualMissProbOne f w := by
    intro i
    have hmap : ∀ (r : ActualHalfWidthRecord N),
        (∑' L : List (ActualHalfWidthRecord N),
          ((actualHalfWidthRecords f w i).map (fun L' => r :: L')) L * idealMissWeight L)
          = ∑' L : List (ActualHalfWidthRecord N),
            (actualHalfWidthRecords f w i) L * idealMissWeight (r :: L) := by
      intro r
      exact pmf_map_expectation (actualHalfWidthRecords f w i)
        (fun L' : List (ActualHalfWidthRecord N) => r :: L') idealMissWeight
    have hinner : ∀ (r : ActualHalfWidthRecord N),
        (∑' L : List (ActualHalfWidthRecord N),
          (actualHalfWidthRecords f w i) L * idealMissWeight (r :: L))
        = if isActualIdealHit r then 0 else actualMissMass f w i := by
      intro r
      by_cases hr : isActualIdealHit r
      · have hz : (∑' L : List (ActualHalfWidthRecord N),
            (actualHalfWidthRecords f w i) L * idealMissWeight (r :: L))
            = ∑' _L : List (ActualHalfWidthRecord N), (0 : ℝ≥0∞) := by
          apply tsum_congr
          intro L
          rw [missWeight_cons, if_pos hr]
          simp
        rw [hz]
        simp [hr]
      · have hz : (∑' L : List (ActualHalfWidthRecord N),
            (actualHalfWidthRecords f w i) L * idealMissWeight (r :: L))
            = ∑' L : List (ActualHalfWidthRecord N),
              (actualHalfWidthRecords f w i) L * idealMissWeight L := by
          apply tsum_congr
          intro L
          rw [missWeight_cons, if_neg hr]
        rw [hz]
        simp [actualMissMass, hr]
    have hbind := pmf_bind_expectation (actualFreshRecord f w)
      (fun r : ActualHalfWidthRecord N =>
        (actualHalfWidthRecords f w i).map (fun L => r :: L))
      idealMissWeight
    calc (∑' L : List (ActualHalfWidthRecord N),
          (actualHalfWidthRecords f w (i + 1)) L * idealMissWeight L)
        = ∑' L : List (ActualHalfWidthRecord N),
          ((actualFreshRecord f w).bind (fun r : ActualHalfWidthRecord N =>
            (actualHalfWidthRecords f w i).map (fun L => r :: L))) L * idealMissWeight L := by
              rw [actualHalfWidthRecords]
      _ = ∑' r : ActualHalfWidthRecord N, (actualFreshRecord f w) r *
          (∑' L : List (ActualHalfWidthRecord N),
            ((actualHalfWidthRecords f w i).map (fun L => r :: L)) L * idealMissWeight L) := hbind
      _ = ∑' r : ActualHalfWidthRecord N, (actualFreshRecord f w) r *
          (∑' L : List (ActualHalfWidthRecord N),
            (actualHalfWidthRecords f w i) L * idealMissWeight (r :: L)) := by
            apply tsum_congr
            intro r
            rw [hmap r]
      _ = ∑' r : ActualHalfWidthRecord N, (actualFreshRecord f w) r *
          (if isActualIdealHit r then 0 else actualMissMass f w i) := by
            apply tsum_congr
            intro r
            rw [hinner r]
      _ = actualMissMass f w i * actualMissProbOne f w := by
        have hpoint : ∀ r : ActualHalfWidthRecord N,
            (actualFreshRecord f w) r * (if isActualIdealHit r then 0 else actualMissMass f w i)
            = ((actualFreshRecord f w) r * massIndicator (¬ isActualIdealHit r))
                * actualMissMass f w i := by
          intro r
          by_cases hr : isActualIdealHit r <;> simp [hr, massIndicator]
        calc (∑' r : ActualHalfWidthRecord N, (actualFreshRecord f w) r *
              (if isActualIdealHit r then 0 else actualMissMass f w i))
            = ∑' r : ActualHalfWidthRecord N,
                ((actualFreshRecord f w) r * massIndicator (¬ isActualIdealHit r))
                  * actualMissMass f w i := tsum_congr hpoint
          _ = (∑' r : ActualHalfWidthRecord N, (actualFreshRecord f w) r *
                massIndicator (¬ isActualIdealHit r)) * actualMissMass f w i :=
              ENNReal.tsum_mul_right
          _ = actualMissProbOne f w * actualMissMass f w i := by rw [actualMissProbOne]
          _ = actualMissMass f w i * actualMissProbOne f w := mul_comm _ _
  induction L0 with
  | zero =>
    have hzero : (∑' L : List (ActualHalfWidthRecord N),
        (actualHalfWidthRecords f w 0) L * idealMissWeight L) = 1 := by
      have hsingle : (∑' L : List (ActualHalfWidthRecord N),
          (PMF.pure ([] : List (ActualHalfWidthRecord N))) L * idealMissWeight L)
          = idealMissWeight ([] : List (ActualHalfWidthRecord N)) := by
        refine Eq.trans (tsum_eq_single [] ?_) (by simp)
        intro L hL
        rw [PMF.pure_apply]
        by_cases h : L = []
        · exact absurd h hL
        · simp [h]
      rw [show actualHalfWidthRecords f w 0 = PMF.pure [] by rfl, hsingle]
      simp [idealMissWeight, massIndicator, hasIdealHit]
    unfold actualMissMass
    rw [hzero]
    simp [ENNReal.ofReal_one]
  | succ i ih =>
    rw [hstep i, ih, hone]
    have hN1 : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    have hbase : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by
      have hinv1 : (1 : ℝ) / (N : ℝ) ≤ 1 :=
        (div_le_one hN1).2 (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
      linarith
    have hpow : (0 : ℝ) ≤ (1 - 1 / (N : ℝ)) ^ i := by positivity
    calc ENNReal.ofReal ((1 - 1 / (N : ℝ)) ^ i) * ENNReal.ofReal (1 - 1 / (N : ℝ))
        = ENNReal.ofReal ((1 - 1 / (N : ℝ)) ^ i * (1 - 1 / (N : ℝ))) :=
          (ENNReal.ofReal_mul hpow).symm
      _ = ENNReal.ofReal ((1 - 1 / (N : ℝ)) ^ (i + 1)) := by rw [pow_succ]

/-- Before combining, the actual ideal-hit probability for a reflection-hiding oracle is `1 - (1
- 1 / N) ^ L0`. -/
theorem clause2_actual_ideal_hit_mass_zero {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (a q w L0 : ℕ) :
    actualIdealHitMass f a q w L0 0 = ENNReal.ofReal (1 - (1 - 1 / (N : ℝ)) ^ L0) := by
  have hrun : actualCombinedRun f a q w L0 0 = actualHalfWidthRecordLaw f w L0 := by
    unfold actualCombinedRun
    show (actualHalfWidthRecordLaw f w L0).bind PMF.pure = actualHalfWidthRecordLaw f w L0
    rw [PMF.bind_pure]
  have hmap : (actualCombinedRun f a q w L0 0).map (fun L => decide (hasIdealHit L)) true
      = ∑' L : List (ActualHalfWidthRecord N), (actualHalfWidthRecordLaw f w L0) L *
          massIndicator (hasIdealHit L) := by
    rw [hrun, PMF.map_apply]
    apply tsum_congr
    intro L
    by_cases h : hasIdealHit L
    · simp [massIndicator, h]
    · simp [massIndicator, h]
  have hmiss : (∑' L : List (ActualHalfWidthRecord N),
        (actualHalfWidthRecordLaw f w L0) L * massIndicator (¬ hasIdealHit L))
      = actualMissMass f w L0 := by
    unfold actualMissMass idealMissWeight
    rfl
  have htot : (∑' L : List (ActualHalfWidthRecord N),
        (actualHalfWidthRecordLaw f w L0) L * massIndicator (hasIdealHit L))
      + (∑' L : List (ActualHalfWidthRecord N),
        (actualHalfWidthRecordLaw f w L0) L * massIndicator (¬ hasIdealHit L)) = 1 := by
    have h2 : (∑' L : List (ActualHalfWidthRecord N),
        ((actualHalfWidthRecordLaw f w L0) L * massIndicator (hasIdealHit L)
          + (actualHalfWidthRecordLaw f w L0) L * massIndicator (¬ hasIdealHit L)))
        = ∑' L : List (ActualHalfWidthRecord N), (actualHalfWidthRecordLaw f w L0) L := by
      apply tsum_congr
      intro L
      by_cases h : hasIdealHit L <;> simp [massIndicator, h]
    rw [← PMF.tsum_coe (actualHalfWidthRecordLaw f w L0), ← h2]
    exact ENNReal.tsum_add.symm
  have hmissle : (∑' L : List (ActualHalfWidthRecord N),
        (actualHalfWidthRecordLaw f w L0) L * massIndicator (¬ hasIdealHit L)) ≤ 1 := by
    calc (∑' L : List (ActualHalfWidthRecord N),
          (actualHalfWidthRecordLaw f w L0) L * massIndicator (¬ hasIdealHit L))
        ≤ (∑' L : List (ActualHalfWidthRecord N),
            (actualHalfWidthRecordLaw f w L0) L * massIndicator (hasIdealHit L))
            + (∑' L : List (ActualHalfWidthRecord N),
              (actualHalfWidthRecordLaw f w L0) L * massIndicator (¬ hasIdealHit L)) :=
        le_add_of_nonneg_left bot_le
      _ = 1 := htot
  have hhit : (∑' L : List (ActualHalfWidthRecord N),
        (actualHalfWidthRecordLaw f w L0) L * massIndicator (hasIdealHit L))
      = 1 - actualMissMass f w L0 := by
    rw [← hmiss]
    refine ENNReal.eq_sub_of_add_eq ?_ ?_
    · exact ne_of_lt (lt_of_le_of_lt hmissle ENNReal.one_lt_top)
    · exact htot
  calc actualIdealHitMass f a q w L0 0
      = (actualCombinedRun f a q w L0 0).map (fun L => decide (hasIdealHit L)) true := by
        unfold actualIdealHitMass actualIdealHitEvent
        rfl
    _ = ∑' L : List (ActualHalfWidthRecord N), (actualHalfWidthRecordLaw f w L0) L *
        massIndicator (hasIdealHit L) := hmap
    _ = 1 - actualMissMass f w L0 := hhit
    _ = 1 - ENNReal.ofReal ((1 - 1 / (N : ℝ)) ^ L0) := by rw [clause2_actual_miss_mass f s hf w]
    _ = ENNReal.ofReal (1 - (1 - 1 / (N : ℝ)) ^ L0) := by
      rw [← ENNReal.ofReal_one]
      have hN1 : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
      have hbase : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by
        have hinv1 : (1 : ℝ) / (N : ℝ) ≤ 1 :=
          (div_le_one hN1).2 (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
        linarith
      have hpow0 : (0 : ℝ) ≤ (1 - 1 / (N : ℝ)) ^ L0 := by positivity
      rw [← ENNReal.ofReal_sub (p := 1) (q := (1 - 1 / (N : ℝ)) ^ L0) hpow0]

/-- Before combining, the actual failure probability for a reflection-hiding oracle is `(1 - 1 /
N) ^ L0`. -/
theorem clause2_actual_failure_mass_zero {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (a q w L0 : ℕ) :
    actualFailureMass f a q w L0 0 = ENNReal.ofReal ((1 - 1 / (N : ℝ)) ^ L0) := by
  unfold actualFailureMass
  rw [clause2_actual_ideal_hit_mass_zero f s hf a q w L0]
  have hN1 : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hbase : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by
    have hinv1 : (1 : ℝ) / (N : ℝ) ≤ 1 :=
      (div_le_one hN1).2 (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
    linarith
  have hpow0 : (0 : ℝ) ≤ (1 - 1 / (N : ℝ)) ^ L0 := by positivity
  have hinv0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have hpow1 : (1 - 1 / (N : ℝ)) ^ L0 ≤ 1 := pow_le_one₀ hbase (by linarith)
  rw [← ENNReal.ofReal_one]
  rw [← ENNReal.ofReal_sub (p := 1) (q := 1 - (1 - 1 / (N : ℝ)) ^ L0) (by linarith)]
  congr 1
  ring

/-- One additional descent iteration applies the stage transformation to the preceding descent
law. -/
theorem descentFold_succ (stage : PMF (Option (List Bool)) → PMF (Option (List Bool)))
    (k : ℕ) :
    descentFold stage (k + 1) = stage (descentFold stage k) := by
  rw [descentFold, List.range_succ, List.foldl_append]
  rfl

/-- Extending a bit-list law maps failure to failure and appends each successfully sampled bit
to the given list. -/
theorem descentExtend_eq_bind (inner : PMF (Option Bool)) (bs : List Bool) :
    descentExtend inner bs
      = inner.bind (fun o' => match o' with
          | none => PMF.pure none
          | some b => PMF.pure (some (bs ++ [b]))) := by
  unfold descentExtend
  show (inner.bind (pure ∘ extendOpt bs))
      = inner.bind (fun o' => match o' with
          | none => pure none
          | some b => pure (some (bs ++ [b])))
  congr 1
  funext o'
  cases o' <;> rfl

/-- Every successful list in a descent-stage support extends a successful input list by one bit. -/
theorem descentStage_shape (inner : List Bool → PMF (Option Bool))
    (st : PMF (Option (List Bool))) (bs : List Bool)
    (h : some bs ∈ (descentStage inner st).support) :
    ∃ (bs' : List Bool) (b : Bool),
      some bs' ∈ st.support ∧ bs = bs' ++ [b] := by
  unfold descentStage at h
  rw [PMF.mem_support_bind_iff] at h
  obtain ⟨o, ho, hmem⟩ := h
  cases o with
  | none =>
    exfalso
    have hn : (PMF.pure none : PMF (Option (List Bool))) (some bs) ≠ 0 := by
      have h1 : some bs ∈ (PMF.pure none).support := by
        show some bs ∈ (PMF.pure none).support
        exact hmem
      rw [PMF.mem_support_iff] at h1
      exact h1
    rw [PMF.pure_apply] at hn
    simp at hn
  | some bs0 =>
    have hinner : some bs ∈ (descentExtend (inner bs0) bs0).support := by
      show some bs ∈ (descentExtend (inner bs0) bs0).support
      rw [stageOpt] at hmem
      exact hmem
    unfold descentExtend at hinner
    rw [PMF.mem_support_map_iff] at hinner
    obtain ⟨o', ho', hmem'⟩ := hinner
    cases o' with
    | none =>
      exfalso
      rw [extendOpt] at hmem'
      exact absurd hmem' (by simp)
    | some b =>
      rw [extendOpt] at hmem'
      injection hmem' with hmem'
      subst hmem'
      exact ⟨bs0, b, ho, rfl⟩

/-- Every successful actual descent output appends one bit to a supported input list and
increases its length by one. -/
theorem actualDescentStage_shape {n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) (st : PMF (Option (List Bool)))
    (bs : List Bool) (h : some bs ∈ (actualDescentStage f st).support) :
    ∃ (bs' : List Bool) (b : Bool),
      some bs' ∈ st.support ∧ bs = bs' ++ [b] ∧ bs.length = bs'.length + 1 := by
  obtain ⟨bs', b, hbs, heq⟩ :=
    descentStage_shape
      (fun bs => dihedralSieveActual (n - bs.length) (descentDepth (n - bs.length))
        (f ∘ descentEmbedding n bs)) st bs h
  refine ⟨bs', b, hbs, heq, ?_⟩
  rw [heq]
  simp

/-- Every successful ideal descent output appends one bit to a supported input list and
increases its length by one. -/
theorem idealDescentStage_shape {n : ℕ} (s : ZMod (2 ^ n))
    (st : PMF (Option (List Bool))) (bs : List Bool)
    (h : some bs ∈ (idealDescentStage n s st).support) :
    ∃ (bs' : List Bool) (b : Bool),
      some bs' ∈ st.support ∧ bs = bs' ++ [b] ∧ bs.length = bs'.length + 1 := by
  obtain ⟨bs', b, hbs, heq⟩ :=
    descentStage_shape
      (fun bs => (dihedralSieveRun (n - bs.length) (descentDepth (n - bs.length))
        (descentSlope n bs.length s)).1) st bs h
  refine ⟨bs', b, hbs, heq, ?_⟩
  rw [heq]
  simp

/-- The fold of actual shift-stage steps from the empty successful list equals the iterated
actual descent law. -/
theorem foldl_range_eq_descentFold {n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) :
    (List.range n).foldl (fun acc _ => actualShiftStageStep n f acc)
        (PMF.pure (some ([] : List Bool)))
      = descentFold (actualDescentStage f) n := by
  have hstage : (fun acc (_ : ℕ) => actualShiftStageStep n f acc)
      = (fun acc (_ : ℕ) => actualDescentStage f acc) := by
    funext acc _
    unfold actualShiftStageStep actualDescentStage descentStage stageOpt
    congr 1
    funext o
    cases o with
    | none => rfl
    | some bs =>
      show (dihedralSieveActual (n - bs.length) (descentDepth (n - bs.length))
          (f ∘ descentEmbedding n bs)).bind
            (fun o' => match o' with
              | none => PMF.pure none
              | some b => PMF.pure (some (bs ++ [b])))
          = descentExtend (dihedralSieveActual (n - bs.length)
              (descentDepth (n - bs.length)) (f ∘ descentEmbedding n bs)) bs
      rw [← descentExtend_eq_bind]
  unfold descentFold
  rw [hstage]

/-- The fold of ideal shift-stage steps from the empty successful list equals the iterated ideal
descent law. -/
theorem foldl_range_eq_descentFold_ideal (n : ℕ) (s : ZMod (2 ^ n)) :
    (List.range n).foldl (fun acc _ => shiftStageStep n s acc)
        (PMF.pure (some ([] : List Bool)))
      = descentFold (idealDescentStage n s) n := by
  have hstage : (fun acc (_ : ℕ) => shiftStageStep n s acc)
      = (fun acc (_ : ℕ) => idealDescentStage n s acc) := by
    funext acc _
    unfold shiftStageStep idealDescentStage descentStage stageOpt
    congr 1
    funext o
    cases o with
    | none => rfl
    | some bs =>
      show ((dihedralSieveRun (n - bs.length) (descentDepth (n - bs.length))
          (descentSlope n bs.length s)).1).bind
            (fun o' => match o' with
              | none => PMF.pure none
              | some b => PMF.pure (some (bs ++ [b])))
          = descentExtend ((dihedralSieveRun (n - bs.length) (descentDepth (n - bs.length))
              (descentSlope n bs.length s)).1) bs
      rw [← descentExtend_eq_bind]
  unfold descentFold
  rw [hstage]

/-- Every successful list supported after `k` actual descent stages has length `k`. -/
theorem descentFold_length_actual {n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) (k : ℕ) :
    ∀ (bs : List Bool), some bs ∈ (descentFold (actualDescentStage f) k).support →
      bs.length = k := by
  induction k with
  | zero =>
    intro bs h
    rw [descentFold, List.range_zero, List.foldl_nil] at h
    rw [PMF.mem_support_pure_iff] at h
    injection h with h
    subst h
    rfl
  | succ k ih =>
    intro bs h
    rw [descentFold_succ] at h
    obtain ⟨bs', b, hbs, hbs', hlen⟩ :=
      actualDescentStage_shape f (descentFold (actualDescentStage f) k) bs h
    have hlen' : bs'.length = k := ih bs' hbs
    rw [hlen'] at hlen
    omega

/-- Every successful list supported after `k` ideal descent stages has length `k`. -/
theorem descentFold_length_ideal {n : ℕ} (s : ZMod (2 ^ n)) (k : ℕ) :
    ∀ (bs : List Bool), some bs ∈ (descentFold (idealDescentStage n s) k).support →
      bs.length = k := by
  induction k with
  | zero =>
    intro bs h
    rw [descentFold, List.range_zero, List.foldl_nil] at h
    rw [PMF.mem_support_pure_iff] at h
    injection h with h
    subst h
    rfl
  | succ k ih =>
    intro bs h
    rw [descentFold_succ] at h
    obtain ⟨bs', b, hbs, hbs', hlen⟩ :=
      idealDescentStage_shape s (descentFold (idealDescentStage n s) k) bs h
    have hlen' : bs'.length = k := ih bs' hbs
    rw [hlen'] at hlen
    omega

/-- Every candidate with nonzero mass in the actual recovery run is assembled from a list of
exactly `n` bits. -/
theorem clause3_candidate_from_learned_bits {n : ℕ} {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg (2 ^ n) → S)
    (u : ZMod (2 ^ n)) (h : actualShiftRecoveryRun n f (some u) ≠ 0) :
    ∃ bs : List Bool, bs.length = n ∧ u = assembleCandidate n bs := by
  unfold actualShiftRecoveryRun at h
  have hmap : some u ∈ ((descentFold (actualDescentStage f) n).map
      (Option.map (assembleCandidate n))).support := by
    rw [PMF.mem_support_iff]
    show (PMF.map (Option.map (assembleCandidate n))
        (descentFold (actualDescentStage f) n)) (some u) ≠ 0
    rw [← foldl_range_eq_descentFold f]
    exact h
  rw [PMF.mem_support_map_iff] at hmap
  obtain ⟨a, ha, hfa⟩ := hmap
  cases a with
  | none =>
    simp only [Option.map_none] at hfa
    exact absurd hfa (by simp)
  | some bs =>
    simp only [Option.map_some] at hfa
    have hfa' : assembleCandidate n bs = u := Option.some.inj hfa
    rw [← hfa']
    exact ⟨bs, descentFold_length_actual f n bs ha, rfl⟩

/-- Every candidate with nonzero mass in the ideal recovery run is assembled from a list of
exactly `n` bits. -/
theorem clause3_ideal_candidate_from_learned_bits {n : ℕ} (s : ZMod (2 ^ n))
    (u : ZMod (2 ^ n)) (h : shiftRecoveryRun n s (some u) ≠ 0) :
    ∃ bs : List Bool, bs.length = n ∧ u = assembleCandidate n bs := by
  unfold shiftRecoveryRun at h
  have hmap : some u ∈ ((descentFold (idealDescentStage n s) n).map
      (Option.map (assembleCandidate n))).support := by
    rw [PMF.mem_support_iff]
    show (PMF.map (Option.map (assembleCandidate n))
        (descentFold (idealDescentStage n s) n)) (some u) ≠ 0
    rw [← foldl_range_eq_descentFold_ideal n s]
    exact h
  rw [PMF.mem_support_map_iff] at hmap
  obtain ⟨a, ha, hfa⟩ := hmap
  cases a with
  | none =>
    simp only [Option.map_none] at hfa
    exact absurd hfa (by simp)
  | some bs =>
    simp only [Option.map_some] at hfa
    have hfa' : assembleCandidate n bs = u := Option.some.inj hfa
    rw [← hfa']
    exact ⟨bs, descentFold_length_ideal s n bs ha, rfl⟩

/-- The parity macro ledger has the stated exact query, macro, and measurement counts in terms
of `descentDepth`. -/
theorem clause3_parity_macro_ledger (w : ℕ) :
    (parityMacroLedger w).1 = 24 * 2 ^ (3 * descentDepth w) ∧
      (parityMacroLedger w).2.1 = 48 * 2 ^ (3 * descentDepth w) + 1 ∧
      (parityMacroLedger w).2.2 = 48 * 2 ^ (3 * descentDepth w) + 1 := by
  refine ⟨rfl, rfl, rfl⟩

/-- The recovery ledger records the sums of the per-width descent costs, together with the
specified sorting, integer-size, and workspace costs. -/
theorem clause3_resource_ledger {n : ℕ} :
    (recoveryLedger n).queries = ∑ j ∈ Finset.range n, (parityMacroLedger (n - j)).1 ∧
      (recoveryLedger n).macros = ∑ j ∈ Finset.range n, (parityMacroLedger (n - j)).2.1 ∧
      (recoveryLedger n).measurements = ∑ j ∈ Finset.range n, (parityMacroLedger (n - j)).2.2 ∧
      (recoveryLedger n).samples = ∑ j ∈ Finset.range n, stageSamples (n - j) ∧
      (recoveryLedger n).comparisons =
        sortCompareSteps (∑ j ∈ Finset.range n, stageSamples (n - j)) ∧
      (recoveryLedger n).bitOps =
        sortBitOps (∑ j ∈ Finset.range n, stageSamples (n - j)) (labelBits (2 ^ n)) ∧
      (recoveryLedger n).integerBits = labelBits (2 ^ n) ∧
      (recoveryLedger n).workspaceBits = workspaceBits (stageSamples 1) (labelBits (2 ^ n)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The recovery ledger bounds its sample, comparison, and bit-operation requirements and has
positive workspace. -/
theorem clause3_ledger_side_conditions {n : ℕ} :
    (recoveryLedger n).samples ≤ (recoveryLedger n).queries ∧
      sortCompareSteps (recoveryLedger n).samples ≤ (recoveryLedger n).comparisons ∧
      sortBitOps (recoveryLedger n).samples (recoveryLedger n).integerBits ≤
        (recoveryLedger n).bitOps ∧
      0 < (recoveryLedger n).workspaceBits := by
  have h1 : (recoveryLedger n).samples = (recoveryLedger n).queries := rfl
  have h2 : (recoveryLedger n).comparisons = sortCompareSteps (recoveryLedger n).samples := rfl
  have h3 : (recoveryLedger n).bitOps =
      sortBitOps (recoveryLedger n).samples (recoveryLedger n).integerBits := rfl
  have h4 : 0 < (recoveryLedger n).workspaceBits := by
    unfold recoveryLedger
    dsimp [workspaceBits]
    have hpos : 0 < stageSamples 1 := by
      unfold stageSamples
      positivity
    nlinarith
  refine ⟨h1.le, h2.le, h3.le, h4⟩

/-- The amplified recovery ledger bounds its sample, comparison, and bit-operation requirements
and has positive workspace. -/
theorem clause3_amplified_ledger_side_conditions {n : ℕ} :
    (amplifiedRecoveryLedger n).samples ≤ (amplifiedRecoveryLedger n).queries ∧
      sortCompareSteps (amplifiedRecoveryLedger n).samples ≤
        (amplifiedRecoveryLedger n).comparisons ∧
      sortBitOps (amplifiedRecoveryLedger n).samples
        (amplifiedRecoveryLedger n).integerBits ≤ (amplifiedRecoveryLedger n).bitOps ∧
      0 < (amplifiedRecoveryLedger n).workspaceBits := by
  have h1 : (amplifiedRecoveryLedger n).samples = (amplifiedRecoveryLedger n).queries := rfl
  have h2 : (amplifiedRecoveryLedger n).comparisons =
      sortCompareSteps (amplifiedRecoveryLedger n).samples := rfl
  have h3 : (amplifiedRecoveryLedger n).bitOps =
      sortBitOps (amplifiedRecoveryLedger n).samples
        (amplifiedRecoveryLedger n).integerBits := rfl
  have h4 : 0 < (amplifiedRecoveryLedger n).workspaceBits := by
    unfold amplifiedRecoveryLedger
    dsimp [workspaceBits]
    have hpos : 0 < stageSamples 1 := by
      unfold stageSamples
      positivity
    nlinarith
  refine ⟨h1.le, h2.le, h3.le, h4⟩

/-- Every list in the support of the fresh actual record law has exactly `L0` entries. -/
theorem clause2_actual_fresh_length {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S)
    (w L0 : ℕ) :
    ∀ L ∈ (actualHalfWidthRecordLaw f w L0).support, L.length = L0 := by
  induction L0 with
  | zero =>
      intro L hL
      have hlaw : actualHalfWidthRecordLaw f w 0 = pure [] := by
        simp [actualHalfWidthRecordLaw, actualHalfWidthRecords]
      rw [hlaw] at hL
      have hL' : L = [] := (PMF.mem_support_pure_iff [] L).mp hL
      simp [hL']
  | succ i ih =>
      intro L hL
      have hlaw : actualHalfWidthRecordLaw f w (Nat.succ i) =
          (actualFreshRecord f w).bind fun r =>
            (actualHalfWidthRecords f w i).map fun L' => r :: L' := by
        simp [actualHalfWidthRecordLaw, actualHalfWidthRecords]
      rw [hlaw] at hL
      rcases (PMF.mem_support_bind_iff (actualFreshRecord f w)
        (fun r => (actualHalfWidthRecords f w i).map fun L' => r :: L') L).mp hL with
        ⟨r, hr, hmap⟩
      rcases (PMF.mem_support_map_iff (fun L' => r :: L')
        (actualHalfWidthRecords f w i) L).mp hmap with ⟨L', hL', heq⟩
      have hlen : L.length = L'.length + 1 := by
        have hcons : L = r :: L' := heq.symm
        simp [hcons]
      rw [hlen]
      have hlen' := ih L' hL'
      omega

/-- Twice the number of pairs selected from actual records is at most the number of input
records. -/
theorem clause2_actual_pairing_bound {N : ℕ} (q : ℕ)
    (L : List (ActualHalfWidthRecord N)) :
    (pairWindowMod (N := N) (q := q) ActualHalfWidthRecord.label L).length * 2
      ≤ L.length :=
  (clause2_pairWindowMod_length q ActualHalfWidthRecord.label L).1

/-- An output supported by the combining law contains at most one child per input pair. -/
private theorem clause2_actual_layer_law_length {N : ℕ} (a : ℕ) :
    ∀ (pairs : List (ActualHalfWidthRecord N × ActualHalfWidthRecord N))
      (L' : List (ActualHalfWidthRecord N)),
      L' ∈ (actualLayerCombineLaw a pairs).support → L'.length ≤ pairs.length := by
  intro pairs
  induction pairs with
  | nil =>
      intro L' hL'
      have hlaw : actualLayerCombineLaw (N := N) a [] = pure [] := by
        simp [actualLayerCombineLaw]
      rw [hlaw] at hL'
      have hL' : L' = [] := (PMF.mem_support_pure_iff [] L').mp hL'
      simp [hL']
  | cons p ps ih =>
      intro L' hL'
      have hlaw : actualLayerCombineLaw a (p :: ps) =
          (PMF.uniformOfFintype' (Fin 2)).bind fun b =>
            (actualLayerCombineLaw a ps).map fun tail =>
              if b = 1 then combineActualRecords a p.1 p.2 :: tail else tail := by
        simp [actualLayerCombineLaw]
      rw [hlaw] at hL'
      rcases (PMF.mem_support_bind_iff (PMF.uniformOfFintype' (Fin 2))
        (fun b : Fin 2 => (actualLayerCombineLaw a ps).map fun tail =>
          if b = 1 then combineActualRecords a p.1 p.2 :: tail else tail) L').mp hL' with
        ⟨b, hb, hmap⟩
      rcases (PMF.mem_support_map_iff (fun tail : List (ActualHalfWidthRecord N) =>
          if b = 1 then combineActualRecords a p.1 p.2 :: tail else tail)
        (actualLayerCombineLaw a ps) L').mp hmap with ⟨tail, htail, heq⟩
      have htail' := ih tail htail
      have hcons : (p :: ps).length = ps.length + 1 := by simp
      by_cases hb1 : b = 1
      · simp [hb1] at heq
        have hlen : tail.length + 1 = L'.length := by
          rw [← heq]
          simp
        omega
      · simp [hb1] at heq
        have hlen : tail.length = L'.length := by
          rw [← heq]
        omega

/-- Every output supported by one actual combining layer has length at most half the input
length, rounded down. -/
theorem clause2_actual_layer_length {N : ℕ} (a q : ℕ)
    (L : List (ActualHalfWidthRecord N)) :
    ∀ L' ∈ (actualLayerCombine a q L).support, L'.length ≤ L.length / 2 := by
  intro L' hL'
  have hlaw : actualLayerCombine a q L =
      actualLayerCombineLaw a
        (pairWindowMod (N := N) (q := q) ActualHalfWidthRecord.label L) := rfl
  rw [hlaw] at hL'
  have h1 := clause2_actual_layer_law_length a _ L' hL'
  have h2 := clause2_actual_pairing_bound q L
  have h3 : (pairWindowMod (N := N) (q := q) ActualHalfWidthRecord.label L).length
      ≤ L.length / 2 := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    exact h2
  omega

/-- After `m` actual combining layers, each supported output length multiplied by `2 ^ m` is at
most the input length. -/
theorem clause2_actual_layered_length {N : ℕ} (a q : ℕ) (m : ℕ)
    (L : List (ActualHalfWidthRecord N)) :
    ∀ L' ∈ (actualLayeredCombine a q m L).support, 2 ^ m * L'.length ≤ L.length := by
  induction m with
  | zero =>
      intro L' hL'
      have hlaw : actualLayeredCombine a q 0 L = pure L := rfl
      rw [hlaw] at hL'
      have hL' : L' = L := (PMF.mem_support_pure_iff L L').mp hL'
      rw [hL']
      simp
  | succ j ih =>
      intro L' hL'
      have hlaw : actualLayeredCombine a q (Nat.succ j) L =
          (actualLayeredCombine a q j L).bind (actualLayerCombine a q) := rfl
      rw [hlaw] at hL'
      rcases (PMF.mem_support_bind_iff (actualLayeredCombine a q j L)
        (actualLayerCombine a q) L').mp hL' with ⟨M, hM, hML⟩
      have h1 : 2 * L'.length ≤ M.length := by
        have h := clause2_actual_layer_length a q M L' hML
        rw [Nat.le_div_iff_mul_le (by omega)] at h
        omega
      have h2 := ih M hM
      calc (2 ^ (j + 1)) * L'.length = 2 ^ j * (2 * L'.length) := by rw [pow_succ]; ring
        _ ≤ 2 ^ j * M.length := Nat.mul_le_mul_left _ h1
        _ ≤ L.length := h2

/-- At actual stage `j`, each supported list has length at most `L0 / 2 ^ j`, expressed as a
multiplicative inequality. -/
theorem clause2_actual_stage_length {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S)
    (a q w L0 j : ℕ) :
    ∀ L ∈ (actualStageLaw f a q w L0 j).support, 2 ^ j * L.length ≤ L0 := by
  intro L hL
  have hlaw : actualStageLaw f a q w L0 j =
      (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q j) := rfl
  rw [hlaw] at hL
  rcases (PMF.mem_support_bind_iff (actualHalfWidthRecordLaw f w L0)
    (actualLayeredCombine a q j) L).mp hL with ⟨M, hM, hML⟩
  have hMlen := clause2_actual_fresh_length f w L0 M hM
  have h2 := clause2_actual_layered_length a q j M L hML
  calc 2 ^ j * L.length ≤ M.length := h2
    _ = L0 := hMlen

/-- For a natural-valued sequence that halves at each step, its partial sum plus twice the next
term is at most twice the initial term. -/
private theorem clause2_halving_sum_le_two {a : ℕ → ℕ} (m : ℕ)
    (hhalving : ∀ j, 2 * a (j + 1) ≤ a j) :
    (∑ j ∈ Finset.range (m + 1), a j) + 2 * a (m + 1) ≤ 2 * a 0 := by
  induction m with
  | zero =>
      have h := hhalving 0
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      omega
  | succ m ih =>
      have h := hhalving (m + 1)
      rw [Finset.sum_range_succ]
      omega

/-- The sum of the halved record budgets through stage `m` is at most twice the initial budget. -/
theorem clause2_kept_record_ledger_le (m L0 : ℕ) :
    sieveKeptRecordCount m L0 ≤ 2 * L0 := by
  have htwo (j : ℕ) : 2 * 2 ^ j = 2 ^ (j + 1) := by
    rw [pow_succ]
    ring
  have hhalving : ∀ j : ℕ, 2 * (L0 / 2 ^ (j + 1)) ≤ L0 / 2 ^ j := by
    intro j
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc 2 * (L0 / 2 ^ (j + 1)) * 2 ^ j = (L0 / 2 ^ (j + 1)) * (2 * 2 ^ j) := by ring
      _ = (L0 / 2 ^ (j + 1)) * 2 ^ (j + 1) := by rw [htwo]
      _ ≤ L0 := Nat.div_mul_le_self L0 (2 ^ (j + 1))
  have hmain : ∀ k : ℕ,
      (∑ j ∈ Finset.range (k + 1), L0 / 2 ^ j) + 2 * (L0 / 2 ^ (k + 1)) ≤ 2 * L0 := by
    intro k
    induction k with
    | zero =>
        have h := hhalving 0
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]
        omega
    | succ k ih =>
        have h := hhalving (k + 1)
        rw [Finset.sum_range_succ]
        omega
  have h := hmain m
  unfold sieveKeptRecordCount

  omega

/-- A reflection-hiding oracle has a transport witness with the representation mass formulas,
staged marginals, qubit factorization, and one-query, one-gate record circuit counts
[Kuperberg2005]. -/
theorem clause1_endpoint (N : ℕ) [NeZero N] :
    ∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg N → S) (s : ZMod N), DihedralReflectionHides N f s →
      ∀ (Label : Type) [Fintype Label] [DecidableEq Label]
        (family : IrrepFamily N Label),
      ∃ w : RepTransportWitness f s family,

        (∀ V : Label, ∀ row : Fin (dimFixed (family.irrep V) s),
          repJointMass (family.irrep V) row.val = ((family.irrep V).dim : ℝ) / N) ∧

        (∀ V : Label, ∀ row : Fin (dimFixed (family.irrep V) s),
          (∑' q : ZMod N × Bool × S,
              if w.toLabel q.1 = V ∧ w.toRowNat (q.1, q.2.1) = row.val then
                ENNReal.toReal (actualRecordFiniteLaw f q) else 0)
            = ((family.irrep V).dim : ℝ) / N) ∧

        (∀ V : Label,
          repLabelMass (family.irrep V) s =
            ((family.irrep V).dim : ℝ) * dimFixed (family.irrep V) s / N) ∧

        (∀ k : ZMod N, ∀ t : Bool,
          w.toRowNat (k, t) < dimFixed (family.irrep (w.toLabel k)) s) ∧

        w.stages.law 0 = actualRecordFiniteLaw f ∧
        (∀ k : ZMod N, ∀ t : Bool,
          ENNReal.toReal (w.stages.law 1 (k, t)) = 1 / (2 * N)) ∧
        (∀ k : ZMod N, ENNReal.toReal (w.stages.law 2 k) = 1 / N) ∧

        (∀ k : ZMod N, ∃ γ : S → ℂ, (∑ z : S, ‖γ z‖ ^ 2) = 1 / (N : ℝ) ∧
          ∀ t : Bool, ∀ z : S,
            dihedralRecordJoint N f ((k, t), z) = γ z * dihedralQubitState N s k t) ∧

        (QueryCount (dihedralRecordCircuit (N := N) (S := S)) = 1) ∧
        (GateCount (dihedralRecordCircuit (N := N) (S := S)) = 1) := by
  intro S _ _ _ f s hf Label _ _ family
  obtain ⟨w, hstage0, hstage1, hstage2, hquery, hgate⟩ :=
    clause1_representation_record_bridge N S f s hf Label family
  refine ⟨w, ?_, ?_, ?_, ?_, hstage0, hstage1, hstage2, ?_, hquery, hgate⟩
  · intro V row
    exact clause1_joint_mass_is_prop8_1 f family s w V row
  · intro V row
    exact clause1_transported_joint_law f family s w V row
  · intro V
    exact (clause1_label_mass_is_prop8_1 f family s w V).2
  · intro k t
    exact clause1_row_index_in_fixed_subspace f family s w k t
  · intro k
    exact w.extraction k

/-- The actual sieve satisfies the stated staged-law, width, fresh-probability, and
record-budget properties, including both even and odd stage counts. -/
theorem clause2_endpoint (N : ℕ) [NeZero N] :

    (∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg N → S) (a q w L0 m : ℕ),
      ∃ (stageLaw : Fin (m + 1) → PMF (List (ActualHalfWidthRecord N))),
        stageLaw 0 = actualHalfWidthRecordLaw f w L0 ∧
        (∀ j : Fin m, stageLaw j.succ = (stageLaw j.castSucc).bind (actualLayerCombine a q)) ∧
        stageLaw ⟨m, by omega⟩ =
          (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q m)) ∧

    (∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg N → S) (a q w L0 k : ℕ),
      (∃ (evenLaw : Fin (2 * k + 1) → PMF (List (ActualHalfWidthRecord N))),
        evenLaw 0 = actualHalfWidthRecordLaw f w L0 ∧
        (∀ j : Fin (2 * k), evenLaw j.succ = (evenLaw j.castSucc).bind (actualLayerCombine a q)) ∧
        evenLaw ⟨2 * k, by omega⟩ =
          (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q (2 * k))) ∧
      (∃ (oddLaw : Fin (2 * k + 2) → PMF (List (ActualHalfWidthRecord N))),
        oddLaw 0 = actualHalfWidthRecordLaw f w L0 ∧
        (∀ j : Fin (2 * k + 1), oddLaw j.succ = (oddLaw j.castSucc).bind (actualLayerCombine a q)) ∧
        oddLaw ⟨2 * k + 1, by omega⟩ =
          (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q (2 * k + 1)))) ∧

    (∀ (a : ℕ) (r₁ r₂ : ActualHalfWidthRecord N), 1 ≤ a →
      combineActualRecords a r₁ r₂ = ⟨r₁.label - r₂.label, (r₁.width + r₂.width) / a⟩ ∧
        a * (combineActualRecords a r₁ r₂).width ≤ r₁.width + r₂.width ∧
        r₁.width + r₂.width < a * ((combineActualRecords a r₁ r₂).width + 1) ∧
        (combineActualRecords a r₁ r₂).width ≤ r₁.width + r₂.width ∧
        (2 ≤ a → 2 * (combineActualRecords a r₁ r₂).width ≤ r₁.width + r₂.width)) ∧

    (∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg N → S) (s : ZMod N) (a q w L0 m : ℕ),
      DihedralReflectionHides N f s →
      actualFailureMass f a q w L0 m = 1 - actualIdealHitMass f a q w L0 m ∧
        (0 : ℝ≥0∞) ≤ actualIdealHitMass f a q w L0 m ∧
        actualIdealHitMass f a q w L0 m ≤ 1 ∧
        actualIdealHitMass f a q w L0 0 = ENNReal.ofReal (1 - (1 - 1 / (N : ℝ)) ^ L0) ∧
        actualFailureMass f a q w L0 0 = ENNReal.ofReal ((1 - 1 / (N : ℝ)) ^ L0)) ∧

    (∀ (m : ℕ),
      2 * sieveFreshRecordCount m = sieveRecordCount m ∧
        sieveKeptRecordCount m (sieveFreshRecordCount m) ≤ 2 * sieveFreshRecordCount m) ∧
    (∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg N → S) (a q w L0 j : ℕ),
      (∀ L ∈ (actualHalfWidthRecordLaw f w L0).support, L.length = L0) ∧
        (∀ L ∈ (actualStageLaw f a q w L0 j).support, 2 ^ j * L.length ≤ L0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S _ _ _ f a q w L0 m
    exact clause2_actual_stage_law f a q w L0 m
  · intro S _ _ _ f a q w L0 k
    obtain ⟨evenLaw, he0, he1, he2⟩ := clause2_actual_stage_law f a q w L0 (2 * k)
    obtain ⟨oddLaw, ho0, ho1, ho2⟩ := clause2_actual_stage_law f a q w L0 (2 * k + 1)
    refine ⟨⟨evenLaw, he0, ?_, he2⟩, ⟨oddLaw, ho0, ?_, ho2⟩⟩
    · intro j
      exact he1 j
    · intro j
      exact ho1 j
  · intro a r₁ r₂ ha
    refine ⟨clause2_combine_actual_records a r₁ r₂, ?_, ?_, ?_, ?_⟩
    · exact clause2_child_width_floor_division a r₁ r₂ ha |>.1
    · exact clause2_child_width_floor_division a r₁ r₂ ha |>.2
    · exact clause2_width_reduction a r₁ r₂ ha |>.1
    · exact clause2_width_reduction a r₁ r₂ ha |>.2
  · intro S _ _ _ f s a q w L0 m hf
    refine ⟨clause2_failure_mass_eq f a q w L0 m, bot_le,
        clause2_ideal_hit_mass_le_one f a q w L0 m, ?_, ?_⟩
    · exact clause2_actual_ideal_hit_mass_zero f s hf a q w L0
    · exact clause2_actual_failure_mass_zero f s hf a q w L0
  · intro m
    obtain ⟨_, hrec⟩ := clause2_sample_and_record_counts m (sieveFreshRecordCount m) rfl
    exact ⟨hrec, clause2_kept_record_ledger_le m (sieveFreshRecordCount m)⟩
  · intro S _ _ _ f a q w L0 j
    refine ⟨clause2_actual_fresh_length f w L0, clause2_actual_stage_length f a q w L0 j⟩

/-- For positive `n`, `2 ^ n` is twice `2 ^ (n - 1)`. -/
theorem pow_two_decomp (n : ℕ) (hn : 1 ≤ n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  have h : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h]
  ring

/-- For positive `n`, dividing a label representative by `2 ^ (n - 1)` gives a natural number
below two. -/
theorem highPart_lt_two {n : ℕ} (hn : 1 ≤ n) (x : ZMod (2 ^ n)) :
    x.val / 2 ^ (n - 1) < 2 := by
  have hlt : x.val < 2 ^ n := ZMod.val_lt x
  refine Nat.div_lt_of_lt_mul ?_
  have : 2 ^ (n - 1) * 2 = 2 ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  rw [this]
  exact hlt

/-- For positive `n`, the high part of a label is at most one. -/
theorem highPart_le_one {n : ℕ} (hn : 1 ≤ n) (x : ZMod (2 ^ n)) : highPart x ≤ 1 := by
  unfold highPart
  have h := highPart_lt_two hn x
  omega

/-- For positive `n`, `topBit` is the high part regarded as an element of `Fin 2`. -/
theorem topBit_eq_highPart {n : ℕ} (hn : 1 ≤ n) (x : ZMod (2 ^ n)) :
    topBit n x = ⟨highPart x, by have h := highPart_le_one hn x; omega⟩ := by
  apply Fin.ext
  have hhigh : x.val / 2 ^ (n - 1) < 2 := highPart_lt_two hn x
  show (x.val / 2 ^ (n - 1)) % 2 = highPart x
  unfold highPart
  exact Nat.mod_eq_of_lt hhigh

/-- A label representative decomposes into its high part times `2 ^ (n - 1)` plus its low part. -/
theorem val_eq_high_mul_add_low {n : ℕ} (x : ZMod (2 ^ n)) :
    x.val = 2 ^ (n - 1) * highPart x + lowPart x := by
  unfold highPart lowPart
  rw [Nat.div_add_mod]

/-- The low part of a label is strictly below `2 ^ (n - 1)`. -/
theorem lowPart_lt {n : ℕ} (x : ZMod (2 ^ n)) : lowPart x < 2 ^ (n - 1) := by
  unfold lowPart
  exact Nat.mod_lt _ (by positivity)

/-- The representative of `y - x` is the ordinary difference when the representatives are
ordered, and the wrapped difference otherwise. -/
theorem val_sub_formula {n : ℕ} [NeZero n] (x y : ZMod n) :
    (y - x).val = if x.val ≤ y.val then y.val - x.val else n - (x.val - y.val) := by
  by_cases hx : x = 0
  · subst x
    simp
  · haveI : NeZero x := ⟨hx⟩
    rw [show y - x = y + (-x) from sub_eq_add_neg _ _, ZMod.val_add,
      ZMod.val_neg_of_ne_zero x]
    have hxnlt : x.val < n := ZMod.val_lt x
    have hynlt : y.val < n := ZMod.val_lt y
    by_cases h : x.val ≤ y.val
    · rw [if_pos h]
      have hlt : y.val - x.val < n := by omega
      have heq : y.val + (n - x.val) = (y.val - x.val) + n := by omega
      rw [heq, Nat.mod_eq_sub_mod (by omega), Nat.add_sub_cancel, Nat.mod_eq_of_lt hlt]
    · rw [if_neg h]
      have hlt : n - (x.val - y.val) < n := by omega
      have heq : y.val + (n - x.val) = n - (x.val - y.val) := by omega
      rw [heq, Nat.mod_eq_of_lt hlt]

/-- A natural number strictly smaller than the divisor has quotient zero. -/
theorem div_eq_zero_of_lt {H k : ℕ} (h : k < H) : k / H = 0 := Nat.div_eq_of_lt h

/-- A natural number between `H` and `2 * H`, with the upper endpoint excluded, has quotient one
upon division by `H`. -/
theorem div_eq_one_of_lt_two_mul {H k : ℕ} (h1 : H ≤ k) (h2 : k < 2 * H) : k / H = 1 := by
  have hlt : k / H < 2 := Nat.div_lt_of_lt_mul (by omega)
  have hge : 1 ≤ k / H := by
    have hdm := Nat.div_add_mod k H
    by_contra hcon
    have hz : k / H = 0 := Nat.eq_zero_of_not_pos hcon
    rw [hz] at hdm
    have hmlt : k % H < H := Nat.mod_lt _ (by omega)
    omega
  omega

/-- For positive `n`, the top bit of `y - x` is the sum in `Fin 2` of the parent top bits and
the low-part borrow bit. -/
theorem topBit_sub {n : ℕ} (hn : 1 ≤ n) (x y : ZMod (2 ^ n)) :
    topBit n (y - x) = topBit n y + topBit n x + borrowBit x y := by
  have hM := pow_two_decomp n hn
  have hXlt : x.val < 2 ^ n := ZMod.val_lt x
  have hYlt : y.val < 2 ^ n := ZMod.val_lt y
  have hX := val_eq_high_mul_add_low x
  have hY := val_eq_high_mul_add_low y
  have hτ : highPart x ≤ 1 := highPart_le_one hn x
  have hτ' : highPart y ≤ 1 := highPart_le_one hn y
  have ha : lowPart x < 2 ^ (n - 1) := lowPart_lt x
  have ha' : lowPart y < 2 ^ (n - 1) := lowPart_lt y
  have hsub := val_sub_formula (x := x) (y := y) (n := 2 ^ n)
  have hmain : (y - x).val / 2 ^ (n - 1) =
      (highPart y + highPart x + (if lowPart y < lowPart x then 1 else 0)) % 2 := by
    have hτc : highPart x = 0 ∨ highPart x = 1 := by omega
    have hτ'c : highPart y = 0 ∨ highPart y = 1 := by omega
    rcases hτc with hτ0 | hτ1
    · rcases hτ'c with hτ'0 | hτ'1
      · simp only [hτ0, hτ'0] at hX hY ⊢
        by_cases hle : x.val ≤ y.val
        · rw [hsub, if_pos hle]
          have hlt : y.val - x.val < 2 ^ (n - 1) := by omega
          rw [div_eq_zero_of_lt hlt]
          simp only [if_neg (by omega : ¬ lowPart y < lowPart x)]
        · rw [hsub, if_neg (by omega : ¬ x.val ≤ y.val)]
          have h1 : 0 < x.val - y.val := by omega
          have h2 : x.val - y.val < 2 ^ (n - 1) := by omega
          have h3 : 2 ^ (n - 1) ≤ 2 ^ n - (x.val - y.val) := by omega
          have h4 : 2 ^ n - (x.val - y.val) < 2 ^ n := by omega
          rw [div_eq_one_of_lt_two_mul h3 (by omega)]
          simp only [if_pos (by omega : lowPart y < lowPart x)]
      · simp only [hτ0, hτ'1] at hX hY ⊢
        have hle' : x.val ≤ y.val := by omega
        rw [hsub, if_pos hle']
        by_cases h : lowPart x ≤ lowPart y
        · have hlt : 2 ^ (n - 1) ≤ y.val - x.val := by omega
          have hlt2 : y.val - x.val < 2 ^ n := by omega
          rw [div_eq_one_of_lt_two_mul hlt (by omega)]
          simp only [if_neg (by omega : ¬ lowPart y < lowPart x)]
        · have hlt : y.val - x.val < 2 ^ (n - 1) := by omega
          rw [div_eq_zero_of_lt hlt]
          simp only [if_pos (by omega : lowPart y < lowPart x)]
    · rcases hτ'c with hτ'0 | hτ'1
      · simp only [hτ1, hτ'0] at hX hY ⊢
        have hgt' : y.val < x.val := by omega
        rw [hsub, if_neg (by omega : ¬ x.val ≤ y.val)]
        by_cases h : lowPart x ≤ lowPart y
        · have hlt : 2 ^ (n - 1) ≤ 2 ^ n - (x.val - y.val) := by omega
          have hlt2 : 2 ^ n - (x.val - y.val) < 2 ^ n := by omega
          rw [div_eq_one_of_lt_two_mul hlt (by omega)]
          simp only [if_neg (by omega : ¬ lowPart y < lowPart x)]
        · have hlt : 2 ^ n - (x.val - y.val) < 2 ^ (n - 1) := by omega
          rw [div_eq_zero_of_lt hlt]
          simp only [if_pos (by omega : lowPart y < lowPart x)]
      · simp only [hτ1, hτ'1] at hX hY ⊢
        by_cases hle : x.val ≤ y.val
        · rw [hsub, if_pos hle]
          have hlt : y.val - x.val < 2 ^ (n - 1) := by omega
          rw [div_eq_zero_of_lt hlt]
          simp only [if_neg (by omega : ¬ lowPart y < lowPart x)]
        · rw [hsub, if_neg (by omega : ¬ x.val ≤ y.val)]
          have h1 : 0 < x.val - y.val := by omega
          have h2 : x.val - y.val < 2 ^ (n - 1) := by omega
          have h3 : 2 ^ (n - 1) ≤ 2 ^ n - (x.val - y.val) := by omega
          have h4 : 2 ^ n - (x.val - y.val) < 2 ^ n := by omega
          rw [div_eq_one_of_lt_two_mul h3 (by omega)]
          simp only [if_pos (by omega : lowPart y < lowPart x)]
  rw [topBit_eq_highPart hn (y - x), topBit_eq_highPart hn y, topBit_eq_highPart hn x]
  apply Fin.ext
  show (y - x).val / 2 ^ (n - 1) = ((highPart y + highPart x) % 2 + (borrowBit x y).val) % 2
  rw [hmain]
  let c : ℕ := if lowPart y < lowPart x then 1 else 0
  have hc : c % 2 = c := by
    unfold c
    split <;> rfl
  have h2 : (borrowBit x y).val = c := by
    unfold c borrowBit
    split <;> rfl
  calc (highPart y + highPart x + c) % 2
      = ((highPart y + highPart x) % 2 + c % 2) % 2 := Nat.add_mod _ _ _
    _ = ((highPart y + highPart x) % 2 + c) % 2 := by rw [hc]
    _ = ((highPart y + highPart x) % 2 + (borrowBit x y).val) % 2 := by rw [h2]

/-- A bit window lying below the top bit can be computed entirely from the label's low part. -/
theorem windowKey_eq_low {n w t : ℕ} (hw : t + w ≤ n - 1) (x : ZMod (2 ^ n)) :
    windowKey n w t x = (lowPart x % 2 ^ (t + w)) / 2 ^ t := by
  unfold windowKey lowPart
  have hdvd : 2 ^ (t + w) ∣ 2 ^ (n - 1) := by
    refine ⟨2 ^ (n - 1 - (t + w)), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  rw [← Nat.mod_mul_right_div_self x.val (2 ^ t) (2 ^ w)]
  rw [← pow_add]
  rw [Nat.mod_mod_of_dvd x.val hdvd]

/-- Labels with equal low parts have equal keys for every window lying below the top bit. -/
theorem windowKey_eq_of_lowPart_eq {n w t : ℕ} (hw : t + w ≤ n - 1)
    {x y : ZMod (2 ^ n)} (h : lowPart x = lowPart y) :
    windowKey n w t x = windowKey n w t y := by
  rw [windowKey_eq_low hw, windowKey_eq_low hw, h]

/-- Replacing both labels by labels with the same low parts preserves agreement in a window
below the top bit. -/
theorem windowAgree_iff_of_lowPart_eq {n w t : ℕ} (hw : t + w ≤ n - 1)
    {x y x' y' : ZMod (2 ^ n)} (hx : lowPart x = lowPart x') (hy : lowPart y = lowPart y') :
    windowAgree n w t x y ↔ windowAgree n w t x' y' := by
  show windowKey n w t x = windowKey n w t y ↔ windowKey n w t x' = windowKey n w t y'
  rw [windowKey_eq_of_lowPart_eq hw hx, windowKey_eq_of_lowPart_eq hw hy]

/-- If a layer's window starts below the top bit, its prescribed width keeps the whole window
below that bit. -/
theorem layer_window_lt {n m j : ℕ} (hj : m * j ≤ n - 1) :
    m * j + sieveWindowWidth n m j ≤ n - 1 := by
  unfold sieveWindowWidth
  have h := Nat.min_le_right m (n - 1 - m * j)
  omega

/-- A Boolean whose negation is true is false. -/
private theorem bool_not_true_is_false {b : Bool} (h : !b = true) : b = false := by
  cases b <;> simp at h ⊢

/-- When the first label has no matching partner, `sievePairWith` skips it and continues on the
tail. -/
private theorem sievePairWith_cons_none {n : ℕ} {α : Type} [DecidableEq α]
    (label : α → ZMod (2 ^ n)) (w t : ℕ) (r : α) (rest : List α)
    (h : rest.find? (fun x => decide (windowAgree n w t (label r) (label x))) = none) :
    sievePairWith n label w t (r :: rest) = sievePairWith n label w t rest := by
  rw [sievePairWith.eq_2, h]

/-- When the first label has a matching partner, `sievePairWith` emits that pair and recurses
after erasing the partner. -/
private theorem sievePairWith_cons_some {n : ℕ} {α : Type} [DecidableEq α]
    (label : α → ZMod (2 ^ n)) (w t : ℕ) (r : α) (rest : List α) (r' : α)
    (h : rest.find? (fun x => decide (windowAgree n w t (label r) (label x))) = some r') :
    sievePairWith n label w t (r :: rest)
      = (r, r') :: sievePairWith n label w t (rest.erase r') := by
  rw [sievePairWith.eq_2, h]

/-- Erasing an element immediately after a prefix that does not contain it removes that
occurrence and preserves the prefix. -/
private theorem erase_junction {α : Type} [DecidableEq α] (as bs : List α) (a : α)
    (hno : ∀ x ∈ as, x ≠ a) : (as ++ a :: bs).erase a = as ++ bs := by
  induction as with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.erase_cons]
    have hxa : x ≠ a := hno x (by simp)
    rw [if_neg (by simp [hxa])]
    congr 1
    exact ih (fun y hy => hno y (by simp [hy]))

/-- Failure of window agreement implies that the two labels are unequal. -/
private theorem label_ne_of_key_ne {n w t : ℕ} {α : Type} [DecidableEq α]
    (f : α → ZMod (2 ^ n)) (r : α) (x : α)
    (h : decide (windowAgree n w t (f r) (f x)) = false) : f x ≠ f r := by
  intro hx
  have hsame : decide (windowAgree n w t (f r) (f x))
      = decide (windowAgree n w t (f r) (f r)) := by rw [hx]
  have hself : decide (windowAgree n w t (f r) (f r)) = true := by
    simp [windowAgree]
  have htrue : decide (windowAgree n w t (f r) (f x)) = true := by
    rw [hsame]
    exact hself
  simp [h] at htrue

/-- Projecting decorated pairs to their values gives the pairs selected from the projected list
of values. -/
theorem decPair_values {n w t : ℕ} {R : ℕ} :
    ∀ (k : ℕ) (L : List (DecLabel n R)), L.length = k →
      (sievePairWith n (fun x : DecLabel n R => x.val) w t L).map
          (fun p => (p.1.val, p.2.val))
        = sievePairWith n (α := ZMod (2 ^ n)) id w t (L.map (fun x => x.val)) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro L hL
    cases L with
    | nil => simp [sievePairWith.eq_1]
    | cons r rest =>
      have hrest : rest.length + 1 = k := by omega
      have hrestlt : rest.length < k := by omega
      set pf : DecLabel n R → Bool := fun r' =>
        decide (windowAgree n w t r.val r'.val) with hpf_eq
      set pg : ZMod (2 ^ n) → Bool := fun v =>
        decide (windowAgree n w t r.val v) with hpg_eq
      simp only [List.map_cons]
      by_cases hnone : rest.find? pf = none
      · have hnone' : (rest.map (fun x => x.val)).find? pg = none := by
          rw [List.find?_eq_none] at hnone ⊢
          intro v hv
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
          exact hnone x hx
        rw [sievePairWith_cons_none _ _ _ _ _ hnone, sievePairWith_cons_none _ _ _ _ _ hnone']
        have hrec := ih rest.length (by omega) rest (by omega)
        exact hrec
      · obtain ⟨r', hsome⟩ : ∃ r' : DecLabel n R, rest.find? pf = some r' := by
          obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists.mp hnone
          exact ⟨r', hr'.symm⟩
        obtain ⟨hpf', hsplit⟩ := List.find?_eq_some_iff_append.mp hsome
        obtain ⟨as, bs, hrs, hfail⟩ := hsplit
        have hpf : pf r' = true := by
          rw [hpf_eq]
          exact hpf'
        have hmem : r' ∈ rest := by
          rw [hrs]
          simp
        have hpg : pg r'.val = true := by
          rw [hpg_eq]
          exact hpf'
        have hfail' : ∀ y ∈ as.map (fun x : DecLabel n R => x.val), (!pg y) = true := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          rw [hpg_eq]
          exact hfail x hx
        have hfound' : (rest.map (fun x : DecLabel n R => x.val)).find? pg = some r'.val := by
          rw [List.find?_eq_some_iff_append]
          refine ⟨hpg, as.map (fun x : DecLabel n R => x.val),
              bs.map (fun x : DecLabel n R => x.val), ?_, hfail'⟩
          simp [hrs]

        have hnod : ∀ x ∈ as, x ≠ r' := by
          intro x hx hxe
          have hxf : pf x = false := by
            cases hp : pf x with
            | false => rfl
            | true =>
              have h2 : (!pf x) = false := by rw [hp]; rfl
              exact Bool.noConfusion (h2.symm.trans (hfail x hx))
          have hxt : pf x = true := by rw [hxe]; exact hpf
          have hcontra : (true : Bool) = false := hxt.symm.trans hxf
          exact Bool.noConfusion hcontra
        have herase : rest.erase r' = as ++ bs := by
          rw [hrs]
          exact erase_junction as bs r' hnod
        have hnod' : ∀ y ∈ as.map (fun x : DecLabel n R => x.val), y ≠ r'.val := by
          intro y hy hye
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          have hne : pf x = false := by
            cases hp : pf x with
            | false => rfl
            | true =>
              have h2 : (!pf x) = false := by rw [hp]; rfl
              exact Bool.noConfusion (h2.symm.trans (hfail x hx))
          have hpx : decide (windowAgree n w t r.val x.val) = false := by
            rw [hpf_eq] at hne
            exact hne
          have hpart : decide (windowAgree n w t r.val r'.val) = true := by
            rw [hpf_eq] at hpf
            exact hpf
          have : x.val ≠ r'.val := by
            intro hxe
            have h1 : decide (windowAgree n w t r.val x.val)
                = decide (windowAgree n w t r.val r'.val) := by rw [hxe]
            have hcontra : (true : Bool) = false := by
              have h3 : decide (windowAgree n w t r.val x.val) = true := by
                rw [h1, hpart]
              exact h3.symm.trans hpx
            exact Bool.noConfusion hcontra
          exact this hye
        have herase' : (rest.map (fun x : DecLabel n R => x.val)).erase r'.val
            = (rest.erase r').map (fun x : DecLabel n R => x.val) := by
          rw [herase, hrs, List.map_append, List.map_cons]
          rw [erase_junction (as.map (fun x : DecLabel n R => x.val))
            (bs.map (fun x : DecLabel n R => x.val)) r'.val hnod']
          rw [List.map_append]
        rw [sievePairWith_cons_some (fun x : DecLabel n R => x.val) w t r rest r' hsome,
          sievePairWith_cons_some (id : ZMod (2 ^ n) → ZMod (2 ^ n)) w t r.val
            (rest.map (fun x : DecLabel n R => x.val)) r'.val hfound']
        rw [List.map_cons]
        rw [herase']
        have hlenlt : (rest.erase r').length < k := by
          have hle := List.length_erase_add_one hmem
          omega
        have hrec := ih (rest.erase r').length hlenlt (rest.erase r') rfl
        rw [hrec]

/-- Form a decorated child by subtracting the first label from the second, taking the union of
supports, and adding offsets and the borrow bit. -/
def decChild {n R : ℕ} (p : DecLabel n R × DecLabel n R) : DecLabel n R :=
  ⟨p.2.val - p.1.val, p.2.sup ∪ p.1.sup, p.2.off + p.1.off + borrowBit p.1.val p.2.val⟩

/-- Apply one pairing layer to decorated labels, retaining children exactly at tape positions
carrying one. -/
noncomputable def decTapeLayer (n m j : ℕ) {R : ℕ} (tape : List (Fin 2))
    (L : List (DecLabel n R)) : List (DecLabel n R) :=
  List.filterMap (fun p => if p.2 = 1 then some (decChild (p.1.1, p.1.2)) else none)
    ((sievePairWith n (fun x : DecLabel n R => x.val) (sieveWindowWidth n m j) (m * j) L).zip tape)

/-- Projecting the retained decorated children to values agrees with retaining the corresponding
differences of paired values under the same tape. -/
private theorem zip_filterMap_congr {n : ℕ} {R : ℕ} :
    ∀ (P : List (DecLabel n R × DecLabel n R)) (Q : List (ZMod (2 ^ n) × ZMod (2 ^ n)))
      (t : List (Fin 2)),
      P.map (fun p => (p.1.val, p.2.val)) = Q →
      ((P.zip t).filterMap (fun p => if p.2 = 1 then some (decChild (p.1.1, p.1.2)) else none)).map
          (fun x => x.val)
        = (Q.zip t).filterMap (fun p => if p.2 = 1 then some (p.1.2 - p.1.1) else none) := by
  intro P
  induction P with
  | nil =>
    intro Q t h
    simp at h
    subst h
    rfl
  | cons p P ih =>
    intro Q t h
    cases Q with
    | nil => simp at h
    | cons q Q =>
      simp only [List.map_cons] at h
      rcases List.cons.inj h with ⟨hp, hrest⟩
      have hp1 : p.1.val = q.1 := congrArg Prod.fst hp
      have hp2 : p.2.val = q.2 := congrArg Prod.snd hp
      cases t with
      | nil => rfl
      | cons c t =>
        have hz : List.zip (p :: P) (c :: t) = (p, c) :: List.zip P t := rfl
        have hz2 : List.zip (q :: Q) (c :: t) = (q, c) :: List.zip Q t := rfl
        by_cases hc : c = 1
        · have hfl : List.filterMap
              (fun p => if p.2 = 1 then some (decChild (p.1.1, p.1.2)) else none) ((p, c) :: List.zip P t)
              = (decChild (p.1, p.2)) :: List.filterMap
                  (fun p => if p.2 = 1 then some (decChild (p.1.1, p.1.2)) else none) (List.zip P t) := by
            simp [List.filterMap, hc]
          have hfr : List.filterMap
              (fun p => if p.2 = 1 then some (p.1.2 - p.1.1) else none) ((q, c) :: List.zip Q t)
              = (q.2 - q.1) :: List.filterMap
                  (fun p => if p.2 = 1 then some (p.1.2 - p.1.1) else none) (List.zip Q t) := by
            simp [List.filterMap, hc]
          rw [hz, hfl, hz2, hfr, List.map_cons]
          have hchild : (decChild (p.1, p.2)).val = q.2 - q.1 := by
            simp [decChild, hp1, hp2]
          rw [hchild]
          congr 1
          exact ih Q t hrest
        · have hfl : List.filterMap
              (fun p => if p.2 = 1 then some (decChild (p.1.1, p.1.2)) else none) ((p, c) :: List.zip P t)
              = List.filterMap
                  (fun p => if p.2 = 1 then some (decChild (p.1.1, p.1.2)) else none) (List.zip P t) := by
            simp [List.filterMap, hc]
          have hfr : List.filterMap
              (fun p => if p.2 = 1 then some (p.1.2 - p.1.1) else none) ((q, c) :: List.zip Q t)
              = List.filterMap
                  (fun p => if p.2 = 1 then some (p.1.2 - p.1.1) else none) (List.zip Q t) := by
            simp [List.filterMap, hc]
          rw [hz, hfl, hz2, hfr]
          exact ih Q t hrest

/-- Projecting a decorated tape layer to values gives the ordinary tape layer on the projected
input. -/
theorem decTapeLayer_values {n m j : ℕ} {R : ℕ} (tape : List (Fin 2))
    (L : List (DecLabel n R)) :
    (decTapeLayer n m j tape L).map (fun x => x.val)
      = tapeLayer n m j tape (L.map (fun x => x.val)) := by
  unfold decTapeLayer tapeLayer
  have hpair := decPair_values (n := n) (w := sieveWindowWidth n m j) (t := m * j)
    L.length L rfl
  exact zip_filterMap_congr _ _ _ hpair

/-- A symmetric relation holding pairwise along a list holds between any two distinct members of
that list. -/
theorem pairwise_mem_ne {α : Type} {R : α → α → Prop} :
    ∀ (l : List α), (symm : ∀ a b, R a b → R b a) → List.Pairwise R l →
      ∀ {x y : α}, x ∈ l → y ∈ l → x ≠ y → R x y := by
  intro l
  induction l with
  | nil => intro symm h x y hx hy hxy; simp at hx
  | cons a l ih =>
    intro symm h x y hx hy hxy
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with hxa | hx
    · have hy' : y ∈ l := by
        rcases List.mem_cons.mp hy with hya | hy
        · exact absurd (hxa.trans hya.symm) hxy
        · exact hy
      rw [hxa]
      exact h.1 y hy'
    · rcases List.mem_cons.mp hy with hya | hy
      · rw [hya]
        exact symm a x (h.1 x hx)
      · exact ih symm h.2 hx hy hxy

/-- Two unions of finite sets are disjoint when each constituent of one is disjoint from each
constituent of the other. -/
theorem disjoin4 {R : ℕ} {a b c d : Finset (Fin R)}
    (hac : Disjoint a c) (had : Disjoint a d) (hbc : Disjoint b c) (hbd : Disjoint b d) :
    Disjoint (a ∪ b) (c ∪ d) := by
  refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
  · exact Finset.disjoint_union_right.mpr ⟨hac, had⟩
  · exact Finset.disjoint_union_right.mpr ⟨hbc, hbd⟩

/-- Adding a multiple of `M` to a remainder below `M` leaves that remainder modulo `M`. -/
private theorem mod_mul_add (M k r : ℕ) (hr : r < M) : (r + M * k) % M = r := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- Adding `M` to a natural number preserves its remainder modulo `M`. -/
private theorem mod_add_self (M r : ℕ) : (M + r) % M = r % M := by
  rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

/-- The low part of a label difference is the difference of the low parts reduced modulo `2 ^ (n
- 1)`. -/
theorem lowPart_sub {n : ℕ} (hn : 1 ≤ n) (x y : ZMod (2 ^ n)) :
    lowPart (y - x) = (lowPart y + 2 ^ (n - 1) - lowPart x) % 2 ^ (n - 1) := by
  have hM : 0 < 2 ^ (n - 1) := by positivity
  have hly : lowPart y < 2 ^ (n - 1) := lowPart_lt y
  have hlx : lowPart x < 2 ^ (n - 1) := lowPart_lt x
  have hX := val_eq_high_mul_add_low x
  have hY := val_eq_high_mul_add_low y
  have hτx : highPart x ≤ 1 := highPart_le_one hn x
  have hτy : highPart y ≤ 1 := highPart_le_one hn y
  have hsub := val_sub_formula (x := x) (y := y) (n := 2 ^ n)
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := pow_two_decomp n hn
  have hlow : lowPart (y - x) = (y - x).val % 2 ^ (n - 1) := rfl
  rw [hlow, hsub]
  by_cases hx0 : highPart x = 0
  · by_cases hy0 : highPart y = 0
    · simp only [hx0, hy0] at hX hY
      have hxv : x.val = lowPart x := by omega
      have hyv : y.val = lowPart y := by omega
      rw [hxv, hyv]
      by_cases hle : lowPart x ≤ lowPart y
      · rw [if_pos hle]
        have hlt : lowPart y - lowPart x < 2 ^ (n - 1) := by omega
        rw [Nat.mod_eq_of_lt hlt]
        have h1 : lowPart y + 2 ^ (n - 1) - lowPart x = 2 ^ (n - 1) + (lowPart y - lowPart x) := by
          omega
        rw [h1, mod_add_self, Nat.mod_eq_of_lt hlt]
      · rw [if_neg hle]
        have h1 : 2 ^ n - (lowPart x - lowPart y)
            = (2 ^ (n - 1) - lowPart x + lowPart y) + 2 ^ (n - 1) * 1 := by
          rw [h2n]
          omega
        rw [h1, mod_mul_add _ _ _ (by omega)]
        have h2 : lowPart y + 2 ^ (n - 1) - lowPart x = 2 ^ (n - 1) - lowPart x + lowPart y := by
          omega
        rw [h2, Nat.mod_eq_of_lt (by omega)]
    · have hy1 : highPart y = 1 := by omega
      simp only [hx0, hy1] at hX hY
      have hxv : x.val = lowPart x := by omega
      have hyv : y.val = 2 ^ (n - 1) + lowPart y := by omega
      rw [hxv, hyv]
      have hle : lowPart x ≤ 2 ^ (n - 1) + lowPart y := by omega
      rw [if_pos hle]
      by_cases hle' : lowPart x ≤ lowPart y
      · have h1 : (2 ^ (n - 1) + lowPart y) - lowPart x = 2 ^ (n - 1) + (lowPart y - lowPart x) := by
          omega
        rw [h1, mod_add_self]
        have hlt : lowPart y - lowPart x < 2 ^ (n - 1) := by omega
        rw [Nat.mod_eq_of_lt hlt]
        have h2 : lowPart y + 2 ^ (n - 1) - lowPart x = 2 ^ (n - 1) + (lowPart y - lowPart x) := by
          omega
        rw [h2, mod_add_self, Nat.mod_eq_of_lt hlt]
      · have h1 : (2 ^ (n - 1) + lowPart y) - lowPart x = 2 ^ (n - 1) - lowPart x + lowPart y := by
          omega
        rw [h1, Nat.mod_eq_of_lt (by omega)]
        have h2 : lowPart y + 2 ^ (n - 1) - lowPart x = 2 ^ (n - 1) - lowPart x + lowPart y := by
          omega
        rw [h2, Nat.mod_eq_of_lt (by omega)]
  · by_cases hy0 : highPart y = 0
    · have hx1 : highPart x = 1 := by omega
      simp only [hx1, hy0] at hX hY
      have hxv : x.val = 2 ^ (n - 1) + lowPart x := by omega
      have hyv : y.val = lowPart y := by omega
      rw [hxv, hyv]
      have hgt : 2 ^ (n - 1) + lowPart x > lowPart y := by omega
      rw [if_neg (by omega : ¬ 2 ^ (n - 1) + lowPart x ≤ lowPart y)]
      by_cases hle' : lowPart x ≤ lowPart y
      · have h1 : 2 ^ n - ((2 ^ (n - 1) + lowPart x) - lowPart y)
            = 2 ^ (n - 1) + (lowPart y - lowPart x) := by
          rw [h2n]
          omega
        rw [h1, mod_add_self]
        have hlt : lowPart y - lowPart x < 2 ^ (n - 1) := by omega
        rw [Nat.mod_eq_of_lt hlt]
        have h2 : lowPart y + 2 ^ (n - 1) - lowPart x = 2 ^ (n - 1) + (lowPart y - lowPart x) := by
          omega
        rw [h2, mod_add_self, Nat.mod_eq_of_lt hlt]
      · have h1 : 2 ^ n - ((2 ^ (n - 1) + lowPart x) - lowPart y)
            = 2 ^ (n - 1) - lowPart x + lowPart y := by
          rw [h2n]
          omega
        rw [h1, Nat.mod_eq_of_lt (by omega)]
        have h2 : lowPart y + 2 ^ (n - 1) - lowPart x = 2 ^ (n - 1) - lowPart x + lowPart y := by
          omega
        rw [h2, Nat.mod_eq_of_lt (by omega)]
    · have hx1 : highPart x = 1 := by omega
      have hy1 : highPart y = 1 := by omega
      simp only [hx1, hy1] at hX hY
      have hxv : x.val = 2 ^ (n - 1) + lowPart x := by omega
      have hyv : y.val = 2 ^ (n - 1) + lowPart y := by omega
      rw [hxv, hyv]
      by_cases hle : 2 ^ (n - 1) + lowPart x ≤ 2 ^ (n - 1) + lowPart y
      · rw [if_pos hle]
        have h1 : (2 ^ (n - 1) + lowPart y) - (2 ^ (n - 1) + lowPart x) = lowPart y - lowPart x := by
          omega
        rw [h1]
        have hlt : lowPart y - lowPart x < 2 ^ (n - 1) := by omega
        rw [Nat.mod_eq_of_lt hlt]
        have h2 : lowPart y + 2 ^ (n - 1) - lowPart x = 2 ^ (n - 1) + (lowPart y - lowPart x) := by
          omega
        rw [h2, mod_add_self, Nat.mod_eq_of_lt hlt]
      · rw [if_neg hle]
        have h1 : 2 ^ n - ((2 ^ (n - 1) + lowPart x) - (2 ^ (n - 1) + lowPart y))
            = (2 ^ (n - 1) - lowPart x + lowPart y) + 2 ^ (n - 1) * 1 := by
          rw [h2n]
          omega
        rw [h1, mod_mul_add _ _ _ (by omega)]
        have h2 : lowPart y + 2 ^ (n - 1) - lowPart x = 2 ^ (n - 1) - lowPart x + lowPart y := by
          omega
        rw [h2, Nat.mod_eq_of_lt (by omega)]

/-- For positive `n`, the top bit of `skeletonLabel` is its prescribed bit. -/
theorem topBit_skeletonLabel {n : ℕ} (hn : 1 ≤ n) (low : ZMod (2 ^ (n - 1))) (t : Fin 2) :
    topBit n (skeletonLabel n low t) = t := by
  have hM : 0 < 2 ^ (n - 1) := by positivity
  have hlow : low.val < 2 ^ (n - 1) := ZMod.val_lt low
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := pow_two_decomp n hn
  have hval : (skeletonLabel n low t).val = low.val + 2 ^ (n - 1) * t.val := by
    unfold skeletonLabel
    have hlt : low.val + 2 ^ (n - 1) * t.val < 2 ^ n := by
      have ht : t.val = 0 ∨ t.val = 1 := by omega
      rcases ht with ht | ht
      · rw [ht, Nat.mul_zero, Nat.add_zero]
        omega
      · rw [ht, Nat.mul_one, h2n]
        omega
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  apply Fin.ext
  show (skeletonLabel n low t).val / 2 ^ (n - 1) % 2 = t.val
  rw [hval]
  have ht : t.val = 0 ∨ t.val = 1 := by omega
  rcases ht with ht | ht
  · rw [ht, Nat.mul_zero, Nat.add_zero, Nat.div_eq_of_lt (by omega), Nat.zero_mod]
  · rw [ht, Nat.mul_one, div_eq_one_of_lt_two_mul (by omega) (by omega), Nat.one_mod]

/-- Both parents of every pair selected by `sievePairWith` belong to the input list. -/
private theorem sievePairWith_mem {α : Type} [DecidableEq α] (n : ℕ)
    (label : α → ZMod (2 ^ n)) (w t : ℕ) (L : List α) :
    ∀ p ∈ sievePairWith n label w t L, p.1 ∈ L ∧ p.2 ∈ L := by
  fun_induction sievePairWith n label w t L
  · intro p hp
    simp at hp
  · rename_i r rest h ih
    intro p hp
    obtain ⟨h1, h2⟩ := ih p hp
    exact ⟨List.Mem.tail r h1, List.Mem.tail r h2⟩
  · rename_i r rest r' h ih
    have hmem : r' ∈ rest := List.mem_of_find?_eq_some h
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with hpr | hp
    · subst hpr
      exact ⟨by simp, by simp [hmem]⟩
    · obtain ⟨h1, h2⟩ := ih p hp
      exact ⟨List.Mem.tail r (List.mem_of_mem_erase h1),
        List.Mem.tail r (List.mem_of_mem_erase h2)⟩

/-- On an input list without duplicates, distinct selected pairs share no parent. -/
private theorem sievePairWith_pairwise {α : Type} [DecidableEq α] (n : ℕ)
    (label : α → ZMod (2 ^ n)) (w t : ℕ) :
    ∀ (k : ℕ) (L : List α), L.length = k → L.Nodup →
      List.Pairwise (fun p q : α × α =>
        p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)
        (sievePairWith n label w t L) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro L hlen hnd
    cases L with
    | nil =>
      rw [sievePairWith.eq_1]
      exact .nil
    | cons r rest =>
      have hrest : rest.length + 1 = k := by omega
      have hrestnd : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hnr : r ∉ rest := (List.nodup_cons.mp hnd).1
      by_cases hnone :
          rest.find? (fun r' => decide (windowAgree n w t (label r) (label r'))) = none
      · rw [sievePairWith.eq_2, hnone]
        exact ih rest.length (by omega) rest (by omega) hrestnd
      · obtain ⟨r', hsome⟩ : ∃ r' : α,
            rest.find? (fun r' => decide (windowAgree n w t (label r) (label r'))) = some r' := by
          obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists.mp hnone
          exact ⟨r', hr'.symm⟩
        rw [sievePairWith.eq_2, hsome]
        have hmem : r' ∈ rest := List.mem_of_find?_eq_some hsome
        have heraseND : (rest.erase r').Nodup := hrestnd.erase r'
        have hlenlt : (rest.erase r').length < k := by
          have h1 := List.length_erase_add_one hmem
          omega
        have htail : List.Pairwise (fun p q : α × α =>
              p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)
              (sievePairWith n label w t (rest.erase r')) :=
          ih (rest.erase r').length hlenlt (rest.erase r') rfl heraseND
        rw [List.pairwise_cons]
        refine ⟨?_, htail⟩
        intro q hq
        obtain ⟨hq1, hq2⟩ := sievePairWith_mem n label w t (rest.erase r') q hq
        have hq1' : q.1 ∈ rest := List.mem_of_mem_erase hq1
        have hq2' : q.2 ∈ rest := List.mem_of_mem_erase hq2
        have hnr' : r' ∉ rest.erase r' := by
          intro hmem'
          have h1 := (hrestnd.mem_erase_iff).mp hmem'
          exact h1.1 rfl
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro h
          simp only [Prod.fst, Prod.snd] at h
          exact hnr (h ▸ hq1')
        · intro h
          simp only [Prod.fst, Prod.snd] at h
          exact hnr (h ▸ hq2')
        · intro h
          simp only [Prod.fst, Prod.snd] at h
          exact hnr' (h ▸ hq1)
        · intro h
          simp only [Prod.fst, Prod.snd] at h
          exact hnr' (h ▸ hq2)

/-- On an input list without duplicates, each selected pair has distinct parents. -/
private theorem sievePairWith_parents_ne {α : Type} [DecidableEq α] (n : ℕ)
    (label : α → ZMod (2 ^ n)) (w t : ℕ) :
    ∀ (k : ℕ) (L : List α), L.length = k → L.Nodup →
      ∀ p ∈ sievePairWith n label w t L, p.1 ≠ p.2 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro L hlen hnd
    cases L with
    | nil => intro p hp; rw [sievePairWith.eq_1] at hp; simp at hp
    | cons r rest =>
      have hrestnd : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hnr : r ∉ rest := (List.nodup_cons.mp hnd).1
      have hrest : rest.length + 1 = k := by omega
      by_cases hnone :
          rest.find? (fun r' => decide (windowAgree n w t (label r) (label r'))) = none
      · rw [sievePairWith.eq_2, hnone]
        intro p hp
        exact ih rest.length (by omega) rest (by omega) hrestnd p hp
      · obtain ⟨r', hsome⟩ : ∃ r' : α,
            rest.find? (fun r' => decide (windowAgree n w t (label r) (label r'))) = some r' := by
          obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists.mp hnone
          exact ⟨r', hr'.symm⟩
        rw [sievePairWith.eq_2, hsome]
        have hmem : r' ∈ rest := List.mem_of_find?_eq_some hsome
        have hlenlt : (rest.erase r').length < k := by
          have h1 := List.length_erase_add_one hmem
          omega
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hpr | hp
        · subst hpr
          intro hEq
          simp only [Prod.fst, Prod.snd] at hEq
          exact hnr (hEq ▸ hmem)
        · exact ih (rest.erase r').length hlenlt (rest.erase r') rfl (hrestnd.erase r') p hp

/-- Pairing a duplicate-free list of decorated labels produces pairs with no parents shared
between different pairs. -/
theorem sievePairWith_matching {n R : ℕ} (w t : ℕ) (L : List (DecLabel n R)) (hL : L.Nodup) :
    List.Pairwise (fun p q : DecLabel n R × DecLabel n R =>
      p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)
      (sievePairWith n (fun x : DecLabel n R => x.val) w t L) := by
  exact sievePairWith_pairwise n (fun x : DecLabel n R => x.val) w t L.length L rfl hL

/-- The decorated-label invariant requires pairwise disjoint nonempty supports and expresses
each top bit as its support's input-bit sum plus its offset. -/
structure DecInvariant {n R : ℕ} (top : Fin R → Fin 2) (L : List (DecLabel n R)) : Prop where

  pairwise : List.Pairwise (fun x y : DecLabel n R => Disjoint x.sup y.sup) L

  nonempty : ∀ x ∈ L, x.sup.Nonempty

  top_bit : ∀ x ∈ L, topBit n x.val = (∑ j ∈ x.sup, top j) + x.off

/-- Distinct members of a list satisfying `DecInvariant` have disjoint supports. -/
theorem DecInvariant.disjoint_of_mem {n R : ℕ} {top : Fin R → Fin 2}
    {L : List (DecLabel n R)} (h : DecInvariant top L) :
    ∀ x ∈ L, ∀ y ∈ L, x ≠ y → Disjoint x.sup y.sup := by
  intro x hx y hy hxy
  refine pairwise_mem_ne L (fun a b hab => Finset.disjoint_right.mpr
      (fun z hz ha => (Finset.disjoint_left.mp hab) hz ha)) h.pairwise hx hy hxy

/-- A list satisfying `DecInvariant` has no duplicate decorated labels. -/
private theorem DecInvariant.nodup {n R : ℕ} {top : Fin R → Fin 2}
    {L : List (DecLabel n R)} (h : DecInvariant top L) : L.Nodup := by
  refine h.pairwise.imp_of_mem (fun hx hy hxy hEq => ?_)
  subst hEq
  obtain ⟨a, ha⟩ := h.nonempty _ hx
  exact ((Finset.disjoint_left.mp hxy) ha ha).elim

/-- Zipping a pairwise-related list with another list preserves the relation on the first
components. -/
private theorem pairwise_zip {α β : Type} {R : α → α → Prop} :
    ∀ (l₁ : List α) (l₂ : List β), List.Pairwise R l₁ →
      List.Pairwise (fun u v : α × β => R u.1 v.1) (l₁.zip l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; simp
  | cons a as ih =>
    intro l₂ h
    cases l₂ with
    | nil => simp
    | cons b bs =>
      show List.Pairwise (fun u v : α × β => R u.1 v.1) ((a, b) :: as.zip bs)
      rw [List.pairwise_cons]
      have hhead := (List.pairwise_cons.mp h).1
      constructor
      · intro u hu
        have hmem := List.of_mem_zip hu
        exact hhead u.1 hmem.1
      · exact ih bs (List.pairwise_cons.mp h).2

/-- For positive `n`, a decorated tape layer preserves `DecInvariant`. -/
theorem decTapeLayer_invariant {n m j R : ℕ} (hn : 1 ≤ n) (tape : List (Fin 2))
    (top : Fin R → Fin 2) (L : List (DecLabel n R)) (hL : DecInvariant top L) :
    DecInvariant top (decTapeLayer n m j tape L) := by
  set w := sieveWindowWidth n m j with hw
  set t := m * j with ht
  set P := sievePairWith n (fun x : DecLabel n R => x.val) w t L with hP
  set f : (DecLabel n R × DecLabel n R) × Fin 2 → Option (DecLabel n R) := fun u =>
    if u.2 = 1 then some (decChild (u.1.1, u.1.2)) else none with hf
  have hchildren : decTapeLayer n m j tape L = List.filterMap f (P.zip tape) := by
    unfold decTapeLayer
    simp only [hP, hw, ht, hf]

  have hmatch : List.Pairwise (fun p q : DecLabel n R × DecLabel n R =>
        p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) P :=
    sievePairWith_matching w t L hL.nodup
  have hmem : ∀ p ∈ P, p.1 ∈ L ∧ p.2 ∈ L :=
    sievePairWith_mem n (fun x : DecLabel n R => x.val) w t L

  have hchildrel : List.Pairwise (fun p q : DecLabel n R × DecLabel n R =>
        Disjoint (p.2.sup ∪ p.1.sup) (q.2.sup ∪ q.1.sup)) P := by
    refine hmatch.imp_of_mem (fun {a b} hp hq hpq => ?_)
    have hp1m : a.1 ∈ L := (hmem a hp).1
    have hp2m : a.2 ∈ L := (hmem a hp).2
    have hq1m : b.1 ∈ L := (hmem b hq).1
    have hq2m : b.2 ∈ L := (hmem b hq).2
    obtain ⟨h11, h12, h21, h22⟩ := hpq
    have d12 := hL.disjoint_of_mem a.1 hp1m b.1 hq1m h11
    have d13 := hL.disjoint_of_mem a.1 hp1m b.2 hq2m h12
    have d21 := hL.disjoint_of_mem a.2 hp2m b.1 hq1m h21
    have d22 := hL.disjoint_of_mem a.2 hp2m b.2 hq2m h22
    have d4 : Disjoint (a.1.sup ∪ a.2.sup) (b.1.sup ∪ b.2.sup) :=
      disjoin4 d12 d13 d21 d22
    simpa [Finset.union_comm] using! d4

  have hzip : List.Pairwise (fun u v : (DecLabel n R × DecLabel n R) × Fin 2 =>
        ∀ b, f u = some b → ∀ b', f v = some b' → Disjoint b.sup b'.sup) (P.zip tape) := by
    refine (pairwise_zip (l₁ := P) (l₂ := tape) hchildrel).imp (fun huv => ?_)
    intro b hb b' hb'
    simp only [hf] at hb hb'
    split at hb
    · split at hb'
      · simp only [Option.some.injEq] at hb hb'
        subst hb
        subst hb'
        simpa [decChild] using! huv
      · exact absurd hb' (by simp)
    · exact absurd hb (by simp)
  have hpair : List.Pairwise (fun x y : DecLabel n R => Disjoint x.sup y.sup)
      (List.filterMap f (P.zip tape)) :=
    (List.pairwise_filterMap.mpr hzip)

  have hchild : ∀ x ∈ List.filterMap f (P.zip tape), ∃ p q : DecLabel n R,
      (p, q) ∈ P ∧ x = decChild (p, q) := by
    intro x hx
    obtain ⟨u, hu, heq⟩ := List.mem_filterMap.mp hx
    have hmem' := List.of_mem_zip hu
    simp only [hf] at heq
    split at heq
    · simp only [Option.some.injEq] at heq
      refine ⟨u.1.1, u.1.2, hmem'.1, heq.symm⟩
    · exact absurd heq (by simp)
  refine ⟨?_, ?_, ?_⟩
  · rw [hchildren]
    exact hpair
  · intro x hx
    rw [hchildren] at hx
    obtain ⟨p, q, hpq, hx⟩ := hchild x hx
    subst hx
    have hp1 : p ∈ L := (hmem (p, q) hpq).1
    have hq2 : q ∈ L := (hmem (p, q) hpq).2
    have hne : p ≠ q := sievePairWith_parents_ne n (fun x : DecLabel n R => x.val) w t
      L.length L rfl hL.nodup (p, q) hpq
    have hdisj : Disjoint q.sup p.sup := hL.disjoint_of_mem q hq2 p hp1 (Ne.symm hne)
    simp only [decChild]
    obtain ⟨a, ha⟩ := hL.nonempty q hq2
    exact ⟨a, by rw [Finset.mem_union]; exact Or.inl ha⟩
  · intro x hx
    rw [hchildren] at hx
    obtain ⟨p, q, hpq, hx⟩ := hchild x hx
    subst hx
    have hp1 : p ∈ L := (hmem (p, q) hpq).1
    have hq2 : q ∈ L := (hmem (p, q) hpq).2
    have hne : p ≠ q := sievePairWith_parents_ne n (fun x : DecLabel n R => x.val) w t
      L.length L rfl hL.nodup (p, q) hpq
    have hdisj : Disjoint q.sup p.sup := hL.disjoint_of_mem q hq2 p hp1 (Ne.symm hne)
    simp only [decChild]
    rw [topBit_sub hn p.val q.val]
    rw [hL.top_bit p hp1, hL.top_bit q hq2]
    rw [Finset.sum_union hdisj]
    ac_rfl

/-- Construct the initial decorated labels from low parts and top bits, with singleton supports
and zero offsets. -/
def decFresh {n R : ℕ} (low : Fin R → ZMod (2 ^ (n - 1))) (top : Fin R → Fin 2) :
    List (DecLabel n R) :=
  List.ofFn fun i : Fin R => ⟨skeletonLabel n (low i) (top i), {i}, 0⟩

/-- For positive `n`, the fresh decorated labels satisfy `DecInvariant` for the supplied top
bits. -/
theorem decFresh_invariant {n R : ℕ} (hn : 1 ≤ n) (low : Fin R → ZMod (2 ^ (n - 1)))
    (top : Fin R → Fin 2) : DecInvariant top (decFresh low top) := by
  refine ⟨?_, ?_, ?_⟩
  · refine (List.pairwise_ofFn).2 ?_
    intro i j hij
    simp only [decFresh]
    exact Finset.disjoint_singleton.mpr (by omega)
  · intro x hx
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
    rw [← hi]
    simp only [decFresh]
    exact ⟨i, Finset.mem_singleton_self i⟩
  · intro x hx
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
    rw [← hi]
    simp only [decFresh]
    rw [topBit_skeletonLabel hn (low i) (top i)]
    rw [Finset.sum_singleton]
    simp

/-- Run the decorated sieve skeleton by folding its tape layers over the fresh decorated labels. -/
noncomputable def decSkel {n m R : ℕ} (low : Fin R → ZMod (2 ^ (n - 1)))
    (tape : Fin m → List (Fin 2)) (top : Fin R → Fin 2) : List (DecLabel n R) :=
  List.foldl (fun L j => decTapeLayer n m j.val (tape j) L) (decFresh low top) (List.finRange m)

/-- For positive `n`, folding any list of decorated tape layers preserves `DecInvariant`. -/
private theorem decFold_invariant {n m R : ℕ} (hn : 1 ≤ n) (top : Fin R → Fin 2)
    (tape : Fin m → List (Fin 2)) :
    ∀ (js : List (Fin m)) (L : List (DecLabel n R)), DecInvariant top L →
      DecInvariant top
        (List.foldl (fun L j => decTapeLayer n m j.val (tape j) L) L js) := by
  intro js
  induction js with
  | nil => intro L hL; exact hL
  | cons j js ih =>
    intro L hL
    have hstep : DecInvariant top (decTapeLayer n m j.val (tape j) L) :=
      decTapeLayer_invariant hn (tape j) top L hL
    exact ih _ hstep

/-- For positive `n`, the decorated sieve skeleton satisfies `DecInvariant`. -/
theorem decSkel_invariant {n m R : ℕ} (hn : 1 ≤ n) (low : Fin R → ZMod (2 ^ (n - 1)))
    (tape : Fin m → List (Fin 2)) (top : Fin R → Fin 2) :
    DecInvariant top (decSkel low tape top) :=
  decFold_invariant hn top tape _ _ (decFresh_invariant hn low top)

/-- Projecting the values after a fold of decorated tape layers agrees with folding ordinary
tape layers over the projected input. -/
private theorem decFold_values {n m R : ℕ} (tape : Fin m → List (Fin 2)) :
    ∀ (js : List (Fin m)) (L : List (DecLabel n R)) (V : List (ZMod (2 ^ n))),
      (L.map (fun x => x.val) = V) →
      (List.foldl (fun L j => decTapeLayer n m j.val (tape j) L) L js).map (fun x => x.val)
        = List.foldl (fun L j => tapeLayer n m j.val (tape j) L) V js := by
  intro js
  induction js with
  | nil => intro L V h; exact h
  | cons j js ih =>
    intro L V h
    rw [List.foldl, List.foldl]
    have hstep : (decTapeLayer n m j.val (tape j) L).map (fun x => x.val)
        = tapeLayer n m j.val (tape j) (L.map (fun x => x.val)) :=
      decTapeLayer_values (tape := tape j) L
    exact ih _ _ (by rw [hstep, h])

/-- The values of the decorated sieve skeleton are exactly the ordinary `sieveSkeleton` output. -/
theorem decSkel_values {n m R : ℕ} (low : Fin R → ZMod (2 ^ (n - 1)))
    (tape : Fin m → List (Fin 2)) (top : Fin R → Fin 2) :
    (decSkel low tape top).map (fun x => x.val) = sieveSkeleton n m R low tape top := by
  have hfresh : (decFresh low top).map (fun x => x.val)
      = List.ofFn fun i : Fin R => skeletonLabel n (low i) (top i) := by
    have hcomp : (fun x : DecLabel n R => x.val)
          ∘ (fun i : Fin R => ⟨skeletonLabel n (low i) (top i), {i}, 0⟩)
        = (fun i : Fin R => skeletonLabel n (low i) (top i)) := by
      funext i
      rfl
    simp only [decFresh, List.map_ofFn, hcomp]
  unfold decSkel sieveSkeleton
  exact decFold_values tape (List.finRange m) (decFresh low top)
    (List.ofFn fun i : Fin R => skeletonLabel n (low i) (top i)) hfresh

/-- Mapping labels by a function that preserves window keys commutes with the pairing procedure. -/
private theorem sievePairWith_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (n w t : ℕ) (label : α → ZMod (2 ^ n)) (label' : β → ZMod (2 ^ n)) (φ : α → β)
    (hkey : ∀ x, windowKey n w t (label x) = windowKey n w t (label' (φ x))) :
    ∀ (k : ℕ) (L : List α), L.length = k →
      (sievePairWith n label w t L).map (fun p => (φ p.1, φ p.2))
        = sievePairWith n label' w t (L.map φ) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro L hlen
    cases L with
    | nil =>
      simp [sievePairWith.eq_1]
    | cons r rest =>
      have hrest : rest.length + 1 = k := by omega

      have hpred : ∀ x : α,
          decide (windowAgree n w t (label r) (label x))
            = decide (windowAgree n w t (label' (φ r)) (label' (φ x))) := by
        intro x
        by_cases h : windowAgree n w t (label r) (label x)
        · have h1 : windowKey n w t (label r) = windowKey n w t (label x) :=
            (windowAgree_iff_windowKey n w t (label r) (label x)).mp h
          have h2 : windowKey n w t (label' (φ r)) = windowKey n w t (label' (φ x)) := by
            rw [← hkey x, ← hkey r]
            exact h1
          have h3 : windowAgree n w t (label' (φ r)) (label' (φ x)) :=
            (windowAgree_iff_windowKey n w t (label' (φ r)) (label' (φ x))).mpr h2
          simp [h, h3]
        · have h3 : ¬ windowAgree n w t (label' (φ r)) (label' (φ x)) := by
            intro hh
            have h1 := (windowAgree_iff_windowKey n w t (label r) (label x)).not.mp h
            have h2 := (windowAgree_iff_windowKey n w t (label' (φ r)) (label' (φ x))).mp hh
            rw [← hkey x, ← hkey r] at h2
            exact h1 h2
          simp [h, h3]
      rw [List.map_cons]
      by_cases hnone :
          rest.find? (fun x => decide (windowAgree n w t (label r) (label x))) = none
      · have hnone' : (rest.map φ).find?
            (fun y : β => decide (windowAgree n w t (label' (φ r)) (label' y))) = none := by
          rw [List.find?_eq_none] at hnone ⊢
          intro y hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          intro hz
          rw [← hpred x] at hz
          exact hnone x hx hz
        rw [sievePairWith_cons_none (label := label) w t r rest hnone]
        rw [sievePairWith_cons_none (label := label') w t (φ r) (rest.map φ) hnone']
        exact ih rest.length (by omega) rest (by omega)
      · obtain ⟨r', hsome⟩ : ∃ r' : α,
            rest.find? (fun x => decide (windowAgree n w t (label r) (label x))) = some r' := by
          obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists.mp hnone
          exact ⟨r', hr'.symm⟩
        obtain ⟨hpf', hsplit⟩ := List.find?_eq_some_iff_append.mp hsome
        obtain ⟨as, bs, hrs, hfail⟩ := hsplit

        have hfound' : (rest.map φ).find?
            (fun y : β => decide (windowAgree n w t (label' (φ r)) (label' y))) = some (φ r') := by
          rw [List.find?_eq_some_iff_append]
          refine ⟨?_, ⟨as.map φ, bs.map φ, ?_, ?_⟩⟩
          · have hr'' : decide (windowAgree n w t (label r) (label r')) = true := hpf'
            rw [← hpred r']
            exact hr''
          · rw [hrs]
            simp
          · intro y hy
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
            have hx' : !decide (windowAgree n w t (label r) (label x)) := hfail x hx
            rw [← hpred x]
            exact hx'

        have hnod : ∀ x ∈ as, x ≠ r' := by
          intro x hx hxe
          have hx' : decide (windowAgree n w t (label r) (label x)) = false := by
            have hh := hfail x hx
            cases hb : decide (windowAgree n w t (label r) (label x)) with
            | true => simp [hb] at hh
            | false => rfl
          have hr' : decide (windowAgree n w t (label r) (label r')) = true := hpf'
          rw [hxe] at hx'
          exact Bool.noConfusion (hx'.symm.trans hr')
        have hnod' : ∀ y ∈ as.map φ, y ≠ φ r' := by
          intro y hy hye
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          have hfalse : decide (windowAgree n w t (label' (φ r)) (label' (φ x))) = false := by
            have hh := hfail x hx
            have hx' : decide (windowAgree n w t (label r) (label x)) = false := by
              cases hb : decide (windowAgree n w t (label r) (label x)) with
              | true => simp [hb] at hh
              | false => rfl
            rw [← hpred x]
            exact hx'
          have htrue : decide (windowAgree n w t (label' (φ r)) (label' (φ r'))) = true := by
            have hr'' : decide (windowAgree n w t (label r) (label r')) = true := hpf'
            rw [← hpred r']
            exact hr''
          rw [← hye] at htrue
          exact Bool.noConfusion (hfalse.symm.trans htrue)
        have herase : rest.erase r' = as ++ bs := by
          rw [hrs]
          exact erase_junction as bs r' hnod
        have herase' : (rest.map φ).erase (φ r') = (as ++ bs).map φ := by
          rw [hrs]
          simp only [List.map_append, List.map_cons]
          exact erase_junction (as.map φ) (bs.map φ) (φ r') hnod'
        rw [sievePairWith_cons_some (label := label) w t r rest r' hsome]
        rw [sievePairWith_cons_some (label := label') w t (φ r) (rest.map φ) (φ r') hfound']
        rw [herase, herase']
        have hlenlt : (as ++ bs).length < k := by
          have h1 := List.length_erase_add_one (List.mem_of_find?_eq_some hsome)
          rw [herase] at h1
          have hrestlen : rest.length = (as ++ r' :: bs).length := by rw [hrs]
          simp only [List.length_append, List.length_cons] at hrestlen h1
          rw [List.length_append]
          omega
        simp only [List.map_cons]
        exact congrArg (fun l => (φ r, φ r') :: l)
          (ih (as ++ bs).length hlenlt (as ++ bs) rfl)

/-- Lists of equal length are equal if their defaulted entries agree at every valid index. -/
private theorem list_ext_getD {α : Type} :
    ∀ (l₁ l₂ : List α) (d : α), l₁.length = l₂.length →
      (∀ (i : ℕ), i < l₁.length → l₁.getD i d = l₂.getD i d) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ d hlen h
      cases l₂ with
      | nil => rfl
      | cons b l₂ => simp at hlen
  | cons a l₁ ih =>
      intro l₂ d hlen h
      cases l₂ with
      | nil => simp at hlen
      | cons b l₂ =>
          have hlen' : l₁.length = l₂.length := by simp at hlen; omega
          have hcons : (a :: l₁).length = l₁.length + 1 := rfl
          have hab : a = b := by
            have hh := h 0 (by exact Nat.zero_lt_succ _)
            simpa using! hh
          subst hab
          congr 1
          exact ih l₂ d hlen' (fun i hi => h (i + 1) (by omega))

/-- At a valid index, defaulted lookup in `List.ofFn` returns the corresponding function value. -/
private theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (d : α) (h : i < n) :
    (List.ofFn f).getD i d = f ⟨i, h⟩ := by
  have hq : (List.ofFn f)[i]? = some (f ⟨i, h⟩) := by
    rw [List.getElem?_ofFn, dif_pos h]
  show (List.ofFn f)[i]?.getD d = f ⟨i, h⟩
  rw [hq]
  rfl

/-- Pointwise equal functions on `Fin n` produce equal lists under `List.ofFn`. -/
private theorem ofFn_congr {α : Type} {n : ℕ} {f g : Fin n → α} (h : ∀ i, f i = g i) :
    List.ofFn f = List.ofFn g := by
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_ofFn]
  · intro i h1 h2
    rw [List.getElem_ofFn h1, List.getElem_ofFn h2]
    have hlt : i < n := by rw [List.length_ofFn] at h1; exact h1
    have hh := h ⟨i, hlt⟩
    rw [hh]

/-- Distinct valid indices in a list without duplicates have unequal defaulted entries. -/
private theorem nodup_getD_ne {α : Type} :
    ∀ (L : List α) (h : L.Nodup) (d : α) (i j : ℕ), i ≠ j → i < L.length → j < L.length →
      L.getD i d ≠ L.getD j d := by
  intro L
  induction L with
  | nil => intro h d i j hij hi hj; simp at hi
  | cons a L ih =>
      intro h d i j hij hi hj
      have hlen : (a :: L).length = L.length + 1 := rfl
      have hnil : a ∉ L := (List.nodup_cons.mp h).1
      by_cases hi0 : i = 0
      · by_cases hj0 : j = 0
        · exact absurd (hi0.trans hj0.symm) hij
        · have hj1 : ∃ k, j = k + 1 := by
            cases j with
            | zero => exact (hj0 rfl).elim
            | succ k => exact ⟨k, rfl⟩
          obtain ⟨k, rfl⟩ := hj1
          have hk : k < L.length := by omega
          have hmem : L.getD k d ∈ L := by
            have hget : L.getD k d = L[k] := by
              show (L[k]?).getD d = L[k]
              rw [List.getElem?_eq_getElem hk]
              rfl
            rw [hget]
            exact List.getElem_mem hk
          intro he
          rw [hi0] at he
          have h1 : (a :: L).getD (k + 1) d = L.getD k d := rfl
          have h0 : (a :: L).getD 0 d = a := rfl
          rw [h0, h1] at he
          exact hnil (he ▸ hmem)
      · by_cases hj0 : j = 0
        · have hi1 : ∃ k, i = k + 1 := by
            cases i with
            | zero => exact (hi0 rfl).elim
            | succ k => exact ⟨k, rfl⟩
          obtain ⟨k, rfl⟩ := hi1
          have hk : k < L.length := by omega
          have hmem : L.getD k d ∈ L := by
            have hget : L.getD k d = L[k] := by
              show (L[k]?).getD d = L[k]
              rw [List.getElem?_eq_getElem hk]
              rfl
            rw [hget]
            exact List.getElem_mem hk
          intro he
          rw [hj0] at he
          have h1 : (a :: L).getD (k + 1) d = L.getD k d := rfl
          have h0 : (a :: L).getD 0 d = a := rfl
          rw [h0, h1] at he
          exact hnil (he ▸ hmem)
        · have hi1 : ∃ k, i = k + 1 := by
            cases i with
            | zero => exact (hi0 rfl).elim
            | succ k => exact ⟨k, rfl⟩
          obtain ⟨ki, rfl⟩ := hi1
          have hj1 : ∃ k, j = k + 1 := by
            cases j with
            | zero => exact (hj0 rfl).elim
            | succ k => exact ⟨k, rfl⟩
          obtain ⟨kj, rfl⟩ := hj1
          have hki : ki < L.length := by omega
          have hkj : kj < L.length := by omega
          have hkij : ki ≠ kj := by omega
          have hrest : L.Nodup := (List.nodup_cons.mp h).2
          have hne := ih hrest d ki kj hkij hki hkj
          intro he
          have h1 : (a :: L).getD (ki + 1) d = L.getD ki d := rfl
          have h2 : (a :: L).getD (kj + 1) d = L.getD kj d := rfl
          rw [h1, h2] at he
          exact hne he

/-- Filtering and mapping a cons list either discards its head or prepends the mapped head,
according to the optional result. -/
private theorem filterMap_cons {α β : Type} (f : α → Option β) (a : α) (l : List α) :
    (a :: l).filterMap f = match f a with | none => l.filterMap f | some b => b :: l.filterMap f := by
  simp only [List.filterMap]
  rfl

/-- Replacing equal tail lists preserves the optional operation that prepends a value when
present. -/
private theorem match_congr {α : Type} (x : Option α) (l l' : List α) (h : l = l') :
    (match x with | none => l | some b => b :: l)
      = (match x with | none => l' | some b => b :: l') := by
  cases x <;> simp [h]

/-- Corresponding pair lists zipped with the same tape have equal filtered images when their
filtering functions agree under the correspondence. -/
private theorem filterMap_zip_congr {α β γ : Type} :
    ∀ (P : List (α × α)) (Q : List (β × β)) (t : List (Fin 2)) (g : α → β),
      P.map (fun p => (g p.1, g p.2)) = Q →
      ∀ (F : (α × α) × Fin 2 → Option γ) (G : (β × β) × Fin 2 → Option γ),
        (∀ (p : α × α) (c : Fin 2), F (p, c) = G ((g p.1, g p.2), c)) →
        (P.zip t).filterMap F = (Q.zip t).filterMap G := by
  intro P
  induction P with
  | nil =>
      intro Q t g h F G hFG
      simp at h
      subst h
      rfl
  | cons p P ih =>
      intro Q t g h F G hFG
      cases Q with
      | nil => simp at h
      | cons q Q =>
          simp only [List.map_cons] at h
          rcases List.cons.inj h with ⟨hp, hrest⟩
          cases t with
          | nil => rfl
          | cons c t =>
              have hz : List.zip (p :: P) (c :: t) = (p, c) :: List.zip P t := rfl
              have hz2 : List.zip (q :: Q) (c :: t) = (q, c) :: List.zip Q t := rfl
              have hhead : F (p, c) = G (q, c) := by
                have hh := hFG p c
                rw [hp] at hh
                exact hh
              have htail : (List.zip P t).filterMap F = (List.zip Q t).filterMap G :=
                ih Q t g hrest F G hFG
              rw [hz, hz2, filterMap_cons, filterMap_cons, hhead]
              exact match_congr _ _ _ htail

/-- For positive `n`, the low part of `skeletonLabel` is the representative of its prescribed
low label. -/
theorem lowPart_skeletonLabel {n : ℕ} (hn : 1 ≤ n) (low : ZMod (2 ^ (n - 1))) (t : Fin 2) :
    lowPart (skeletonLabel n low t) = low.val := by
  have hlow : low.val < 2 ^ (n - 1) := ZMod.val_lt low
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := pow_two_decomp n hn
  have hval : (skeletonLabel n low t).val = low.val + 2 ^ (n - 1) * t.val := by
    unfold skeletonLabel
    have hlt : low.val + 2 ^ (n - 1) * t.val < 2 ^ n := by
      have ht : t.val = 0 ∨ t.val = 1 := by omega
      rcases ht with ht | ht
      · rw [ht, Nat.mul_zero, Nat.add_zero]
        have h1 : low.val < 2 * 2 ^ (n - 1) := by omega
        rwa [← h2n] at h1
      · rw [ht, Nat.mul_one]
        have h1 : low.val + 2 ^ (n - 1) < 2 * 2 ^ (n - 1) := by omega
        rwa [← h2n] at h1
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  show (skeletonLabel n low t).val % 2 ^ (n - 1) = low.val
  rw [hval, Nat.add_mod, Nat.mod_eq_of_lt hlow, Nat.mul_mod_right, Nat.add_zero,
    Nat.mod_eq_of_lt hlow]

/-- Reconstructing a label from a decorated label's shadow preserves its low part. -/
theorem lowPart_shadowLabel {n R : ℕ} (x : DecLabel n R) :
    lowPart (shadowLabel (decShadow x)) = lowPart x.val := by
  have hlt : lowPart x.val < 2 ^ (n - 1) := lowPart_lt x.val
  have h2n : 2 ^ (n - 1) ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by decide : 2 > 0) (by omega : n - 1 ≤ n)
  show (shadowLabel (decShadow x)).val % 2 ^ (n - 1) = lowPart x.val
  rw [shadowLabel, ZMod.val_natCast, Nat.mod_mod]
  rw [show (decShadow x).low = lowPart x.val from rfl]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hlt h2n)]
  exact Nat.mod_eq_of_lt hlt

/-- In a window below the top bit, a decorated label and the label reconstructed from its shadow
have equal keys. -/
theorem windowKey_eq_shadow {n w t : ℕ} (hw : t + w ≤ n - 1) {R : ℕ} (x : DecLabel n R) :
    windowKey n w t x.val = windowKey n w t (shadowLabel (decShadow x)) := by
  exact windowKey_eq_of_lowPart_eq hw (lowPart_shadowLabel x).symm

/-- Every window key of width zero is zero. -/
theorem windowKey_eq_zero {n w t : ℕ} (hw : w = 0) (x : ZMod (2 ^ n)) :
    windowKey n w t x = 0 := by
  unfold windowKey
  rw [hw, Nat.pow_zero, Nat.mod_one]

/-- A decorated label and its reconstructed shadow have equal window keys when the window lies
below the top bit or has width zero. -/
private theorem windowKey_shadow {n w t : ℕ} (hw : t + w ≤ n - 1 ∨ w = 0) {R : ℕ}
    (x : DecLabel n R) :
    windowKey n w t x.val = windowKey n w t (shadowLabel (decShadow x)) := by
  rcases hw with hw | hw
  · exact windowKey_eq_shadow hw x
  · rw [windowKey_eq_zero hw x.val, windowKey_eq_zero hw (shadowLabel (decShadow x))]

/-- For positive `n`, taking the shadow of a decorated child agrees with forming the child of
its parent shadows. -/
theorem decShadow_decChild {n : ℕ} (hn : 1 ≤ n) {R : ℕ} (a b : DecLabel n R) :
    decShadow (decChild (a, b)) = shChild (decShadow a, decShadow b) := by
  simp only [decShadow, shChild, decChild, borrowBit]
  rw [lowPart_sub hn a.val b.val]

/-- For positive `n`, the shadows of fresh decorated labels are the fresh shadow labels and do
not depend on the input top bits. -/
private theorem decFresh_shadow {n R : ℕ} (hn : 1 ≤ n) (low : Fin R → ZMod (2 ^ (n - 1)))
    (top : Fin R → Fin 2) : (decFresh low top).map decShadow = shFresh low := by
  have hlow : ∀ i : Fin R, lowPart (skeletonLabel n (low i) (top i)) = (low i).val :=
    fun i => lowPart_skeletonLabel hn (low i) (top i)
  unfold decFresh shFresh
  rw [List.map_ofFn]
  apply ofFn_congr
  intro i
  show decShadow ⟨skeletonLabel n (low i) (top i), {i}, 0⟩ = ⟨(low i).val, {i}, 0⟩
  have hval : decShadow ⟨skeletonLabel n (low i) (top i), {i}, 0⟩
      = ⟨lowPart (skeletonLabel n (low i) (top i)), {i}, 0⟩ := rfl
  rw [hval, hlow i]

/-- For positive `n`, taking shadows commutes with a decorated tape layer when the input shadows
agree. -/
private theorem decTapeLayer_shadow {n m j R : ℕ} (hn : 1 ≤ n) (tape : List (Fin 2))
    (L : List (DecLabel n R)) (S : List (DecShadow n R)) (h : L.map decShadow = S) :
    (decTapeLayer n m j tape L).map decShadow = shTapeLayer n m j tape S := by
  set w := sieveWindowWidth n m j with hw
  set t := m * j with ht

  have hpair : (sievePairWith n (fun x : DecLabel n R => x.val) w t L).map
        (fun p => (decShadow p.1, decShadow p.2))
      = sievePairWith n (fun s : DecShadow n R => shadowLabel s) w t S := by
    have hkey : ∀ x : DecLabel n R,
        windowKey n w t x.val = windowKey n w t (shadowLabel (decShadow x)) := by
      intro x
      by_cases hj : m * j ≤ n - 1
      · have hbound : m * j + sieveWindowWidth n m j ≤ n - 1 := layer_window_lt hj
        exact windowKey_shadow (Or.inl hbound) x
      · have hw0 : sieveWindowWidth n m j = 0 := by
          have hz : n - 1 - m * j = 0 := by omega
          unfold sieveWindowWidth
          simp [hz]
        exact windowKey_shadow (Or.inr hw0) x
    calc
      (sievePairWith n (fun x : DecLabel n R => x.val) w t L).map
          (fun p => (decShadow p.1, decShadow p.2))
        = sievePairWith n (fun s : DecShadow n R => shadowLabel s) w t (L.map decShadow) :=
          sievePairWith_map (n := n) (w := w) (t := t)
            (label := fun x : DecLabel n R => x.val)
            (label' := fun s : DecShadow n R => shadowLabel s)
            (φ := decShadow) hkey L.length L rfl
      _ = sievePairWith n (fun s : DecShadow n R => shadowLabel s) w t S := by rw [h]

  have hsh : (decTapeLayer n m j tape L).map decShadow
      = ((sievePairWith n (fun x : DecLabel n R => x.val) w t L).zip tape).filterMap
          (fun p : (DecLabel n R × DecLabel n R) × Fin 2 =>
            if p.2 = 1 then some (shChild (decShadow p.1.1, decShadow p.1.2)) else none) := by
    unfold decTapeLayer
    rw [List.map_filterMap]
    have hfun : (fun x : (DecLabel n R × DecLabel n R) × Fin 2 => Option.map decShadow
          (if x.2 = 1 then some (decChild (x.1.1, x.1.2)) else none))
        = (fun p : (DecLabel n R × DecLabel n R) × Fin 2 =>
            if p.2 = 1 then some (shChild (decShadow p.1.1, decShadow p.1.2)) else none) := by
      funext x
      by_cases h : x.2 = 1
      · simp only [h, if_pos, Option.map_some]
        rw [decShadow_decChild hn]
      · simp [h]
    rw [hfun]

  have h3 : ((sievePairWith n (fun x : DecLabel n R => x.val) w t L).zip tape).filterMap
        (fun p : (DecLabel n R × DecLabel n R) × Fin 2 =>
          if p.2 = 1 then some (shChild (decShadow p.1.1, decShadow p.1.2)) else none)
      = ((sievePairWith n (fun s : DecShadow n R => shadowLabel s) w t S).zip tape).filterMap
        (fun p : (DecShadow n R × DecShadow n R) × Fin 2 =>
          if p.2 = 1 then some (shChild (p.1.1, p.1.2)) else none) := by
    have hFG : ∀ (p : DecLabel n R × DecLabel n R) (c : Fin 2),
        (if c = 1 then some (shChild (decShadow p.1, decShadow p.2)) else none)
          = (if c = 1 then some (shChild ((decShadow p.1, decShadow p.2).1,
            (decShadow p.1, decShadow p.2).2)) else none) := by
      intro p c
      rfl
    calc
      ((sievePairWith n (fun x : DecLabel n R => x.val) w t L).zip tape).filterMap
          (fun p : (DecLabel n R × DecLabel n R) × Fin 2 =>
            if p.2 = 1 then some (shChild (decShadow p.1.1, decShadow p.1.2)) else none)
        = List.filterMap
          (fun p : (DecShadow n R × DecShadow n R) × Fin 2 =>
            if p.2 = 1 then some (shChild (p.1.1, p.1.2)) else none)
          (((sievePairWith n (fun x : DecLabel n R => x.val) w t L).map
            (fun p : DecLabel n R × DecLabel n R => (decShadow p.1, decShadow p.2))).zip tape) :=
          filterMap_zip_congr _ _ tape decShadow rfl _ _ hFG
      _ = ((sievePairWith n (fun s : DecShadow n R => shadowLabel s) w t S).zip tape).filterMap
          (fun p : (DecShadow n R × DecShadow n R) × Fin 2 =>
            if p.2 = 1 then some (shChild (p.1.1, p.1.2)) else none) := by rw [hpair]
  rw [hsh, h3]
  rfl

/-- For positive `n`, the shadows of the decorated skeleton equal `shSkel`, independently of the
input top bits. -/
theorem decSkel_shadow {n m R : ℕ} (hn : 1 ≤ n) (low : Fin R → ZMod (2 ^ (n - 1)))
    (tape : Fin m → List (Fin 2)) (top : Fin R → Fin 2) :
    (decSkel low tape top).map decShadow = shSkel low tape := by
  have hfold : ∀ (js : List (Fin m)) (L : List (DecLabel n R)) (S : List (DecShadow n R)),
      L.map decShadow = S →
      (List.foldl (fun L j => decTapeLayer n m j.val (tape j) L) L js).map decShadow
        = List.foldl (fun S j => shTapeLayer n m j.val (tape j) S) S js := by
    intro js
    induction js with
    | nil => intro L S h; simpa using! h
    | cons j js ih =>
        intro L S h
        rw [List.foldl, List.foldl]
        have hstep : (decTapeLayer n m j.val (tape j) L).map decShadow
            = shTapeLayer n m j.val (tape j) S :=
          decTapeLayer_shadow hn (tape j) L S h
        exact ih _ _ hstep
  unfold decSkel shSkel
  exact hfold (List.finRange m) (decFresh low top) (shFresh low) (decFresh_shadow hn low top)

/-- The default decorated label has zero value, empty support, and zero offset. -/
private def decDefault (R : ℕ) {n : ℕ} : DecLabel n R := ⟨0, ∅, 0⟩

/-- Look up a decorated label by natural index, using `decDefault` outside the list. -/
private def decGet {n R : ℕ} (L : List (DecLabel n R)) (i : ℕ) : DecLabel n R :=
  L.getD i (decDefault R)

/-- Look up a shadow skeleton entry by natural index, using the shadow of `decDefault` outside
the list. -/
private def shGet {n m R : ℕ} (low : Fin R → ZMod (2 ^ (n - 1)))
    (tape : Fin m → List (Fin 2)) (i : ℕ) : DecShadow n R :=
  (shSkel low tape).getD i (decShadow (decDefault R))

/-- Defaulted lookup at a valid index returns a member of the list. -/
private theorem getD_mem {α : Type} (L : List α) (d : α) (i : ℕ) (h : i < L.length) :
    L.getD i d ∈ L := by
  have hget : L.getD i d = L[i] := by
    show (L[i]?).getD d = L[i]
    rw [List.getElem?_eq_getElem h]
    rfl
  rw [hget]
  exact List.getElem_mem h

/-- For positive `n`, the shadow of a defaulted decorated-skeleton entry equals the
corresponding defaulted shadow-skeleton entry. -/
private theorem decSkel_shadow_getD {n m R : ℕ} (hn : 1 ≤ n)
    (low : Fin R → ZMod (2 ^ (n - 1))) (tape : Fin m → List (Fin 2))
    (top : Fin R → Fin 2) (i : ℕ) :
    decShadow (decGet (decSkel low tape top) i) = shGet low tape i := by
  have hsh := decSkel_shadow hn low tape top
  have hget := List.getD_map (decSkel low tape top) (decDefault R) decShadow (n := i)
  rw [hsh] at hget
  exact hget.symm

/-- For positive `n`, every valid shadow-skeleton entry has nonempty support. -/
theorem topBitBundle_nonempty {n m R : ℕ} (hn : 1 ≤ n)
    (low : Fin R → ZMod (2 ^ (n - 1))) (tape : Fin m → List (Fin 2))
    (i : Fin (shSkel low tape).length) :
    (shGet low tape i.val).sup.Nonempty := by
  set top₀ : Fin R → Fin 2 := fun _ => (0 : Fin 2) with htop₀
  have hinv := decSkel_invariant hn low tape top₀
  have hsh := decSkel_shadow hn low tape top₀
  have hlen : (decSkel low tape top₀).length = (shSkel low tape).length := by
    have h1 := congrArg List.length hsh
    rw [List.length_map] at h1
    exact h1
  have hmem : decGet (decSkel low tape top₀) i.val ∈ decSkel low tape top₀ :=
    getD_mem _ _ _ (by omega)
  have hne : (decGet (decSkel low tape top₀) i.val).sup.Nonempty :=
    hinv.nonempty _ hmem
  have hshI := decSkel_shadow_getD hn low tape top₀ i.val
  have hsupI : (decGet (decSkel low tape top₀) i.val).sup = (shGet low tape i.val).sup := by
    calc (decGet (decSkel low tape top₀) i.val).sup
        = (decShadow (decGet (decSkel low tape top₀) i.val)).sup := rfl
      _ = (shGet low tape i.val).sup := by rw [hshI]
  rw [hsupI] at hne
  exact hne

/-- For positive `n`, shadow-skeleton entries at distinct valid indices have disjoint supports. -/
theorem topBitBundle_disjoint {n m R : ℕ} (hn : 1 ≤ n)
    (low : Fin R → ZMod (2 ^ (n - 1))) (tape : Fin m → List (Fin 2))
    (i j : Fin (shSkel low tape).length) (hij : i ≠ j) :
    Disjoint (shGet low tape i.val).sup (shGet low tape j.val).sup := by
  set top₀ : Fin R → Fin 2 := fun _ => (0 : Fin 2) with htop₀
  have hinv := decSkel_invariant hn low tape top₀
  have hsh0 := decSkel_shadow hn low tape top₀
  have hlen : (decSkel low tape top₀).length = (shSkel low tape).length := by
    have h1 := congrArg List.length hsh0
    rw [List.length_map] at h1
    exact h1
  have hmemI : decGet (decSkel low tape top₀) i.val ∈ decSkel low tape top₀ :=
    getD_mem _ _ _ (by omega)
  have hmemJ : decGet (decSkel low tape top₀) j.val ∈ decSkel low tape top₀ :=
    getD_mem _ _ _ (by omega)
  have hpos : i.val ≠ j.val := fun hv => hij (Fin.ext hv)
  have hne : decGet (decSkel low tape top₀) i.val ≠ decGet (decSkel low tape top₀) j.val :=
    nodup_getD_ne _ hinv.nodup _ i.val j.val hpos (by omega) (by omega)
  have hdisj := hinv.disjoint_of_mem _ hmemI _ hmemJ hne
  have hshI := decSkel_shadow_getD hn low tape top₀ i.val
  have hshJ := decSkel_shadow_getD hn low tape top₀ j.val
  have hsupI : (decGet (decSkel low tape top₀) i.val).sup = (shGet low tape i.val).sup := by
    calc (decGet (decSkel low tape top₀) i.val).sup
        = (decShadow (decGet (decSkel low tape top₀) i.val)).sup := rfl
      _ = (shGet low tape i.val).sup := by rw [hshI]
  have hsupJ : (decGet (decSkel low tape top₀) j.val).sup = (shGet low tape j.val).sup := by
    calc (decGet (decSkel low tape top₀) j.val).sup
        = (decShadow (decGet (decSkel low tape top₀) j.val)).sup := rfl
      _ = (shGet low tape j.val).sup := by rw [hshJ]
  rw [hsupI, hsupJ] at hdisj
  exact hdisj

/-- Construct a top-bit bundle from the nonempty, pairwise disjoint supports and offsets of the
shadow skeleton. -/
noncomputable def topBitBundle {n m R : ℕ} (hn : 1 ≤ n)
    (low : Fin R → ZMod (2 ^ (n - 1))) (tape : Fin m → List (Fin 2)) :
    TopBitBundle R (shSkel low tape).length where
  sup := fun i => (shGet low tape i.val).sup
  off := fun i => (shGet low tape i.val).off
  nonempty := fun i => topBitBundle_nonempty hn low tape i
  disjoint := fun i j hij => topBitBundle_disjoint hn low tape i j hij

/-- Every choice of `n`, `m`, and `R` satisfies `TopBitCoupling`, relating skeleton top bits to
disjoint support bundles. -/
theorem topBitCoupling (n m R : ℕ) : TopBitCoupling n m R := by
  intro hn low tape
  refine ⟨(shSkel low tape).length, topBitBundle hn low tape, ?_⟩
  intro top
  have hinv := decSkel_invariant hn low tape top
  have hsh0 := decSkel_shadow hn low tape top
  have hlen : (decSkel low tape top).length = (shSkel low tape).length := by
    have h1 := congrArg List.length hsh0
    rw [List.length_map] at h1
    exact h1
  have hmap : (sieveSkeleton n m R low tape top).map (topBit n)
      = (decSkel low tape top).map (fun x => topBit n x.val) := by
    rw [← decSkel_values low tape top, List.map_map]
    rfl
  rw [hmap]
  apply list_ext_getD _ _ (topBit n (decDefault R).val)
  · rw [List.length_map, List.length_ofFn]
    exact hlen
  · intro i hi
    have hmaplen : (List.map (fun x => topBit n x.val) (decSkel low tape top)).length
        = (decSkel low tape top).length := List.length_map _

    have hL : ((decSkel low tape top).map (fun x => topBit n x.val)).getD i
        (topBit n (decDefault R).val) = topBit n (decGet (decSkel low tape top) i).val := by
      rw [List.getD_map]
      rfl

    have hi' : i < (shSkel low tape).length := by omega
    have hR : (List.ofFn ((topBitBundle hn low tape).apply top)).getD i
        (topBit n (decDefault R).val) = (topBitBundle hn low tape).apply top ⟨i, hi'⟩ :=
      getD_ofFn _ i _ hi'

    have hmem : decGet (decSkel low tape top) i ∈ decSkel low tape top :=
      getD_mem _ _ _ (by omega)
    have htop : topBit n (decGet (decSkel low tape top) i).val
        = (∑ j ∈ (decGet (decSkel low tape top) i).sup, top j)
          + (decGet (decSkel low tape top) i).off :=
      hinv.top_bit _ hmem

    have hshI := decSkel_shadow_getD hn low tape top i
    have hsupI : (decGet (decSkel low tape top) i).sup = (shGet low tape i).sup := by
      calc (decGet (decSkel low tape top) i).sup
          = (decShadow (decGet (decSkel low tape top) i)).sup := rfl
        _ = (shGet low tape i).sup := by rw [hshI]
    have hoffI : (decGet (decSkel low tape top) i).off = (shGet low tape i).off := by
      calc (decGet (decSkel low tape top) i).off
          = (decShadow (decGet (decSkel low tape top) i)).off := rfl
        _ = (shGet low tape i).off := by rw [hshI]

    have hBsup : (topBitBundle hn low tape).sup ⟨i, hi'⟩ = (shGet low tape i).sup := rfl
    have hBoff : (topBitBundle hn low tape).off ⟨i, hi'⟩ = (shGet low tape i).off := rfl
    have hApp : (topBitBundle hn low tape).apply top ⟨i, hi'⟩
        = (∑ j ∈ (topBitBundle hn low tape).sup ⟨i, hi'⟩, top j)
          + (topBitBundle hn low tape).off ⟨i, hi'⟩ := rfl
    rw [hL, hR, htop, hsupI, hoffI, hApp, hBsup, hBoff]

/-- The descent endpoint combines top-bit coupling, reconstruction from `n` learned bits, exact
parity and recovery ledgers, and their resource side conditions [Kuperberg2005]. -/
theorem clause3_endpoint :

    (∀ n m R : ℕ, TopBitCoupling n m R) ∧

    (∀ (n : ℕ) {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg (2 ^ n) → S) (u : ZMod (2 ^ n)),
      actualShiftRecoveryRun n f (some u) ≠ 0 →
      ∃ bs : List Bool, bs.length = n ∧ u = assembleCandidate n bs) ∧

    (∀ w : ℕ, (parityMacroLedger w).1 = 24 * 2 ^ (3 * descentDepth w) ∧
      (parityMacroLedger w).2.1 = 48 * 2 ^ (3 * descentDepth w) + 1 ∧
      (parityMacroLedger w).2.2 = 48 * 2 ^ (3 * descentDepth w) + 1) ∧

    (∀ n : ℕ,
      (recoveryLedger n).queries = ∑ j ∈ Finset.range n, (parityMacroLedger (n - j)).1 ∧
        (recoveryLedger n).macros = ∑ j ∈ Finset.range n, (parityMacroLedger (n - j)).2.1 ∧
        (recoveryLedger n).measurements = ∑ j ∈ Finset.range n, (parityMacroLedger (n - j)).2.2 ∧
        (recoveryLedger n).samples = ∑ j ∈ Finset.range n, stageSamples (n - j) ∧
        (recoveryLedger n).comparisons =
          sortCompareSteps (∑ j ∈ Finset.range n, stageSamples (n - j)) ∧
        (recoveryLedger n).bitOps =
          sortBitOps (∑ j ∈ Finset.range n, stageSamples (n - j)) (labelBits (2 ^ n)) ∧
        (recoveryLedger n).integerBits = labelBits (2 ^ n) ∧
        (recoveryLedger n).workspaceBits = workspaceBits (stageSamples 1) (labelBits (2 ^ n))) ∧

    (∀ n : ℕ,
      (recoveryLedger n).samples ≤ (recoveryLedger n).queries ∧
        sortCompareSteps (recoveryLedger n).samples ≤ (recoveryLedger n).comparisons ∧
        sortBitOps (recoveryLedger n).samples (recoveryLedger n).integerBits ≤
          (recoveryLedger n).bitOps ∧
        0 < (recoveryLedger n).workspaceBits) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n m R
    exact topBitCoupling n m R
  · intro n S _ _ _ f u h
    exact clause3_candidate_from_learned_bits f u h
  · intro w
    exact clause3_parity_macro_ledger w
  · intro n
    exact clause3_resource_ledger
  · intro n
    exact clause3_ledger_side_conditions

/-- With fuel at least one greater than the input length, `devPairWith` equals `sievePairWith`. -/
theorem devPairWith_eq {n : ℕ} {α : Type} [DecidableEq α] (label : α → ZMod (2 ^ n))
    (w t : ℕ) :
    ∀ (fuel : ℕ) (L : List α), L.length + 1 ≤ fuel →
      devPairWith fuel n label w t L = sievePairWith n label w t L := by
  intro fuel
  induction fuel with
  | zero => intro L h; omega
  | succ fuel ih =>
      intro L h
      cases L with
      | nil =>
          rw [devPairWith, sievePairWith.eq_1]
      | cons r rest =>
          have hcons : (r :: rest).length = rest.length + 1 := rfl
          by_cases hnone :
              rest.find? (fun r' => decide (windowAgree n w t (label r) (label r'))) = none
          · rw [devPairWith]
            simp only [hnone]
            rw [sievePairWith_cons_none _ _ _ _ _ hnone]
            exact ih rest (by omega)
          · obtain ⟨r', hsome⟩ : ∃ r' : α,
                rest.find? (fun r' => decide (windowAgree n w t (label r) (label r'))) = some r' := by
              obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists.mp hnone
              exact ⟨r', hr'.symm⟩
            rw [devPairWith]
            simp only [hsome]
            rw [sievePairWith_cons_some _ _ _ _ _ r' hsome]
            have hmem : r' ∈ rest := List.mem_of_find?_eq_some hsome
            have h1 := List.length_erase_add_one hmem
            have hlen : (rest.erase r').length + 1 ≤ fuel := by omega
            rw [ih (rest.erase r') hlen]

/-- Compute a decorated tape layer using the pairing procedure with fuel equal to the input
length plus one. -/
def devTapeLayer (n m j : ℕ) {R : ℕ} (tape : List (Fin 2))
    (L : List (DecLabel n R)) : List (DecLabel n R) :=
  List.filterMap (fun p => if p.2 = 1 then some (decChild (p.1.1, p.1.2)) else none)
    ((devPairWith (L.length + 1) n (fun x : DecLabel n R => x.val)
      (sieveWindowWidth n m j) (m * j) L).zip tape)

/-- The fuel-based decorated tape layer equals `decTapeLayer`. -/
theorem devTapeLayer_eq (n m j : ℕ) {R : ℕ} (tape : List (Fin 2))
    (L : List (DecLabel n R)) : devTapeLayer n m j tape L = decTapeLayer n m j tape L := by
  unfold devTapeLayer decTapeLayer
  have hpair : devPairWith (L.length + 1) n (fun x : DecLabel n R => x.val)
      (sieveWindowWidth n m j) (m * j) L
      = sievePairWith n (fun x : DecLabel n R => x.val) (sieveWindowWidth n m j) (m * j) L :=
    devPairWith_eq _ _ _ (L.length + 1) L (by omega)
  rw [hpair]

/-- Compute the decorated sieve skeleton by folding the fuel-based decorated tape layers over
fresh labels. -/
def devSkel {n m R : ℕ} (low : Fin R → ZMod (2 ^ (n - 1)))
    (tape : Fin m → List (Fin 2)) (top : Fin R → Fin 2) : List (DecLabel n R) :=
  List.foldl (fun L j => devTapeLayer n m j.val (tape j) L) (decFresh low top) (List.finRange m)

/-- The fuel-based decorated skeleton equals `decSkel`. -/
theorem devSkel_eq {n m R : ℕ} (low : Fin R → ZMod (2 ^ (n - 1)))
    (tape : Fin m → List (Fin 2)) (top : Fin R → Fin 2) :
    devSkel low tape top = decSkel low tape top := by
  have hfold : ∀ (js : List (Fin m)) (L : List (DecLabel n R)),
      List.foldl (fun L j => devTapeLayer n m j.val (tape j) L) L js
        = List.foldl (fun L j => decTapeLayer n m j.val (tape j) L) L js := by
    intro js
    induction js with
    | nil => intro L; rfl
    | cons j js ih =>
        intro L
        rw [List.foldl, List.foldl]
        rw [devTapeLayer_eq]
        exact ih _
  unfold devSkel decSkel
  exact hfold (List.finRange m) (decFresh low top)

/-- For positive `n`, the shadows of the fuel-based decorated skeleton equal `shSkel`. -/
theorem devSkel_shadow {n m R : ℕ} (hn : 1 ≤ n) (low : Fin R → ZMod (2 ^ (n - 1)))
    (tape : Fin m → List (Fin 2)) (top : Fin R → Fin 2) :
    (devSkel low tape top).map decShadow = shSkel low tape := by
  rw [devSkel_eq]
  exact decSkel_shadow hn low tape top

/-- Projecting the fuel-based decorated skeleton to values yields `sieveSkeleton`. -/
theorem devSkel_values {n m R : ℕ} (low : Fin R → ZMod (2 ^ (n - 1)))
    (tape : Fin m → List (Fin 2)) (top : Fin R → Fin 2) :
    (devSkel low tape top).map (fun x => x.val) = sieveSkeleton n m R low tape top := by
  rw [devSkel_eq]
  exact decSkel_values low tape top

end Qatlib.Concepts.HspRecovery.OpenSieve
