/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkAccessConstructionDefs
import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkAccessConstructionCircuitLemmas

/-!
# Lazy matching kernel and register identities

This module computes the lazy matching kernel, its two-element support, and its row record
state. For a positive register width, agreement below the top bit characterizes the two
neighbors, so each row record is an equal-amplitude sum of two basis states.

The CNOT block identities describe the copied lower bits and the unchanged top bit in
`lazyRowRecord`. They also prove that the same block maps a base neighbor index to the
corresponding neighbor of the given vertex. These access constructions support the quantum walk
framework of [Szegedy2004].

## Main statements

* `rowBasisRecordState_lazy`: The explicit two-term row preparation target.
* `lazySupport_card`: The support has two elements for positive width.
* `cnotFold_baseRecord`: The CNOT block implements the neighbor update on basis registers.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false

open Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open scoped Classical BigOperators

universe u v

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.WalkSearch.MnrsAmplify

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- If two registers agree below the top bit, their lazy matching kernel entry is one half. -/
lemma lazyKernel_eq_half {m : ℕ} {x y : Reg m} (h : lazyLowAgrees x y) :
    lazyMatchingKernel m x y = (1 / 2 : ℝ) := by
  rw [lazyMatchingKernel]
  rw [if_pos h]

/-- If two registers fail to agree below the top bit, their lazy matching kernel entry is zero. -/
lemma lazyKernel_eq_zero {m : ℕ} {x y : Reg m} (h : ¬ lazyLowAgrees x y) :
    lazyMatchingKernel m x y = 0 := by
  rw [lazyMatchingKernel]
  rw [if_neg h]

/-- Lower-bit agreement gives a lazy matching kernel entry of one half. -/
lemma lazyKernel_of_lowAgrees {m : ℕ} {x y : Reg m} (h : lazyLowAgrees x y) :
    lazyMatchingKernel m x y = (1 / 2 : ℝ) :=
  lazyKernel_eq_half h

/-- Failure of lower-bit agreement gives a zero lazy matching kernel entry. -/
lemma lazyKernel_of_not_lowAgrees {m : ℕ} {x y : Reg m} (h : ¬ lazyLowAgrees x y) :
    lazyMatchingKernel m x y = 0 :=
  lazyKernel_eq_zero h

/-- The top bit of `lazyRowBasis x b` is `b` for a nonempty register. -/
lemma lazyRowBasis_top {m : ℕ} (hm : 1 ≤ m) (x : Reg m) (b : Bool) :
    lazyRowBasis x b (lazyTopIndex m hm) = b := by
  have htop : (lazyTopIndex m hm).val = m - 1 := rfl
  have h : m - 1 + 1 = m := by omega
  show (if (lazyTopIndex m hm).val + 1 = m then b else x (lazyTopIndex m hm)) = b
  rw [htop]
  rw [if_pos h]

/-- Replacing the top bit of a register preserves agreement with the original register at all
lower coordinates. -/
lemma lazyRowBasis_lowAgrees {m : ℕ} (x : Reg m) (b : Bool) :
    lazyLowAgrees x (lazyRowBasis x b) := by
  intro i hi
  simp only [lazyRowBasis]
  rw [if_neg (by omega : ¬ i.val + 1 = m)]

/-- For positive register width, replacing the top bit by false and by true gives distinct
registers. -/
lemma lazyRowBasis_ne {m : ℕ} (x : Reg m) (hm : 1 ≤ m) :
    lazyRowBasis x false ≠ lazyRowBasis x true := by
  intro h
  have h1 := congrFun h (lazyTopIndex m hm)
  rw [lazyRowBasis_top hm x false, lazyRowBasis_top hm x true] at h1
  exact Bool.noConfusion h1

/-- For positive width, lower-bit agreement holds exactly when the second register is obtained
from the first by choosing its top bit. -/
lemma lazyLowAgrees_iff {m : ℕ} (x y : Reg m) (hm : 1 ≤ m) :
    lazyLowAgrees x y ↔ y = lazyRowBasis x (y (lazyTopIndex m hm)) := by
  constructor
  · intro h
    funext i
    by_cases hi : i.val + 1 = m
    · have htop : (lazyTopIndex m hm).val = m - 1 := rfl
      have hieq : i = lazyTopIndex m hm := by
        refine Fin.ext ?_
        rw [htop]
        omega
      rw [hieq, lazyRowBasis_top hm x _]
    · have hi2 : i.val + 1 < m := by omega
      simp only [lazyRowBasis]
      rw [if_neg hi]
      exact h i hi2
  · intro h i hi
    rw [h]
    simp only [lazyRowBasis]
    rw [if_neg (by omega : ¬ i.val + 1 = m)]

/-- The real square root of one half is the reciprocal of the square root of two. -/
lemma real_sqrt_half : Real.sqrt (1 / 2 : ℝ) = (Real.sqrt 2 : ℝ)⁻¹ := by
  rw [Real.sqrt_div (by norm_num) 2, Real.sqrt_one]
  exact one_div _

/-- The complex embedding of the square root of one half equals the reciprocal of the embedded
square root of two. -/
lemma cast_sqrt_half : ((Real.sqrt (1 / 2 : ℝ) : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  rw [real_sqrt_half]
  norm_cast

/-- For positive width, the lazy matching row record is the sum of the two neighbor basis
states, each with amplitude `sqrt (1 / 2)`. -/
lemma rowBasisRecordState_lazy {m : ℕ} (hm : 1 ≤ m) (x : Reg m) :
    rowBasisRecordState (lazyMatchingKernel m) m (m + m) (fun y => y) x =
      ((Real.sqrt (1 / 2 : ℝ) : ℝ) : ℂ) • Qatlib.Foundations.PureStateMath.Ket (regCat x (lazyRowBasis x false)) +
        ((Real.sqrt (1 / 2 : ℝ) : ℝ) : ℂ) • Qatlib.Foundations.PureStateMath.Ket (regCat x (lazyRowBasis x true)) := by
  classical
  have hdef : rowBasisRecordState (lazyMatchingKernel m) m (m + m) (fun y => y) x
      = ∑ y : Reg m, ((Real.sqrt (lazyMatchingKernel m x y) : ℝ) : ℂ) •
          Qatlib.Foundations.PureStateMath.Ket (regPad (m + m) (m + m) (regCat x y)) := rfl
  rw [hdef]
  have hpad (y : Reg m) : regPad (m + m) (m + m) (regCat x y) = regCat x y :=
    regPad_self (regCat x y)
  simp only [hpad]
  set f : Reg m → QState (Reg (m + m)) := fun y =>
    ((Real.sqrt (lazyMatchingKernel m x y) : ℝ) : ℂ) • Qatlib.Foundations.PureStateMath.Ket (regCat x y) with hf
  have hzero : ∀ y : Reg m, ¬ lazyLowAgrees x y → f y = 0 := by
    intro y hy
    have hk : lazyMatchingKernel m x y = 0 := lazyKernel_of_not_lowAgrees hy
    simp [f, hk, Real.sqrt_zero]
  have hfilter : Finset.univ.filter (fun y : Reg m => lazyLowAgrees x y)
      = {lazyRowBasis x false, lazyRowBasis x true} := by
    ext y
    constructor
    · intro hy
      have hlow : y = lazyRowBasis x (y (lazyTopIndex m hm)) :=
        (lazyLowAgrees_iff x y hm).mp ((Finset.mem_filter.mp hy).2)
      rw [hlow]
      cases hb : y (lazyTopIndex m hm) with
      | false => simp
      | true => simp
    · intro hy
      rcases Finset.mem_insert.mp hy with h1 | h2
      · rw [h1]
        exact (Finset.mem_filter).2 ⟨Finset.mem_univ _, lazyRowBasis_lowAgrees x false⟩
      · rw [Finset.mem_singleton.mp h2]
        exact (Finset.mem_filter).2 ⟨Finset.mem_univ _, lazyRowBasis_lowAgrees x true⟩
  have hsum : (∑ y : Reg m, f y) = f (lazyRowBasis x false) + f (lazyRowBasis x true) := by
    have hsub : Finset.sum (Finset.univ.filter (fun y : Reg m => lazyLowAgrees x y)) f
        = Finset.sum (Finset.univ) f :=
      Finset.sum_subset (Finset.filter_subset _ _) (by
        intro y hy hyn
        exact hzero y (fun hla => hyn ((Finset.mem_filter).2 ⟨Finset.mem_univ _, hla⟩)))
    rw [← hsub, hfilter]
    rw [Finset.sum_insert (by simp [lazyRowBasis_ne x hm]), Finset.sum_singleton]
  rw [hsum]
  simp only [f, lazyKernel_of_lowAgrees (lazyRowBasis_lowAgrees x false),
    lazyKernel_of_lowAgrees (lazyRowBasis_lowAgrees x true)]

/-- The doubled register obtained by zero padding `x` and applying the lower-bit CNOT block. -/
def lazyRowRecord (m : ℕ) (x : Reg m) : Reg (m + m) :=
  cnotFold (highCnotPairs m) (regPad (m + m) m x)

/-- Every listed CNOT pair has both wire values within the doubled register and has distinct
control and target values. -/
lemma highCnotPairs_bound {m : ℕ} {p : Fin (m + m) × Fin (m + m)} (hp : p ∈ highCnotPairs m) :
    p.1.val < m + m ∧ p.2.val < m + m ∧ p.1.val ≠ p.2.val := by
  obtain ⟨i, h1, h2⟩ := (mem_highCnotPairs p).mp hp
  have h3 : p.1.val ≠ p.2.val := by
    intro hh
    omega
  exact ⟨by omega, by omega, h3⟩

/-- A lower coordinate `k` and the wire with value `m + k` form a pair in `highCnotPairs m`. -/
lemma mem_highCnotPairs_agreement {m : ℕ} (hm : 1 ≤ m) {k : ℕ} (hk : k < m - 1)
    (t : Fin (m + m)) (ht : t.val = m + k) :
    (⟨k, by omega⟩, t) ∈ highCnotPairs m := by
  refine (mem_highCnotPairs _).2 ⟨⟨k, by omega⟩, rfl, ?_⟩
  rw [ht]

/-- The only listed pair targeting wire `m + k` is the pair controlled by wire `k`. -/
lemma highCnotPairs_target_unique {m : ℕ} (hm : 1 ≤ m) {k : ℕ} (hk : k < m - 1)
    (t : Fin (m + m)) (ht : t.val = m + k)
    {q : Fin (m + m) × Fin (m + m)} (hq : q ∈ highCnotPairs m) (hqt : q.2 = t) :
    q = (⟨k, by omega⟩, t) := by
  obtain ⟨i, hq1, hq2⟩ := (mem_highCnotPairs q).mp hq
  have hkval : (⟨k, by omega⟩ : Fin m).val = k := rfl
  have hi : i.val = k := by
    have hval : q.2.val = t.val := congrArg Fin.val hqt
    omega
  have e1 : q.1 = ⟨k, by omega⟩ := by
    refine Fin.ext ?_
    omega
  have e2 : q.2 = t := hqt
  exact Prod.ext e1 e2

/-- A lower first-register coordinate cannot be a target of a listed CNOT pair. -/
lemma highCnotPairs_no_small_target {m : ℕ} (hm : 1 ≤ m) {k : ℕ} (hk : k < m - 1)
    {q : Fin (m + m) × Fin (m + m)} (hq : q ∈ highCnotPairs m) :
    ⟨k, by omega⟩ ≠ q.2 := by
  obtain ⟨i, hq1, hq2⟩ := (mem_highCnotPairs q).mp hq
  have hkval : (⟨k, by omega⟩ : Fin m).val = k := rfl
  intro hh
  have hval : q.2.val = k := congrArg Fin.val hh.symm
  omega

/-- The lower-bit CNOT block leaves the first register and final workspace bit unchanged and
XORs each other second-register bit with its corresponding first-register bit. -/
lemma cnotFold_highCnotPairs_apply {m : ℕ} (hm : 1 ≤ m) (r : Reg (m + m)) (j : Fin (m + m)) :
    cnotFold (highCnotPairs m) r j =
      if j.val < m then r j
      else if j.val = m + m - 1 then r j
      else r j ^^ r ⟨j.val - m, by omega⟩ := by
  by_cases h1 : j.val < m
  · rw [if_pos h1]
    refine cnotFold_other (highCnotPairs m) r j ?_
    intro p hp
    obtain ⟨i, hp1, hp2⟩ := (mem_highCnotPairs p).mp hp
    intro hh
    exact absurd (congrArg Fin.val hh) (by omega)
  · rw [if_neg h1]
    by_cases h2 : j.val = m + m - 1
    · rw [if_pos h2]
      refine cnotFold_other (highCnotPairs m) r j ?_
      intro p hp
      obtain ⟨i, hp1, hp2⟩ := (mem_highCnotPairs p).mp hp
      intro hh
      exact absurd (congrArg Fin.val hh) (by omega)
    · rw [if_neg h2]
      have hk : j.val - m < m - 1 := by omega
      have ht : (⟨j.val, by omega⟩ : Fin (m + m)).val = m + (j.val - m) := by
        have hv : (⟨j.val, by omega⟩ : Fin (m + m)).val = j.val := rfl
        omega
      have hmem : (⟨j.val - m, by omega⟩, ⟨j.val, by omega⟩) ∈ highCnotPairs m :=
        mem_highCnotPairs_agreement hm hk _ ht
      refine cnotFold_target_val (highCnotPairs m) r
        (c := ⟨j.val - m, by omega⟩) (t := ⟨j.val, by omega⟩) hmem
        (highCnotPairs_targets_nodup m) ?_ ?_
      · intro q hq hh
        refine highCnotPairs_target_unique hm hk (⟨j.val, by omega⟩) ht hq hh
      · intro q hq
        exact highCnotPairs_no_small_target hm hk hq

/-- The first-register coordinates of a lazy row record equal the original vertex bits. -/
lemma lazyRowRecord_apply_vertex {m : ℕ} (x : Reg m) (j : Fin (m + m)) (h : j.val < m) :
    lazyRowRecord m x j = x ⟨j.val, h⟩ := by
  rw [lazyRowRecord]
  rw [cnotFold_highCnotPairs_apply (m := m) (by omega : 1 ≤ m) _ j]
  rw [if_pos h]
  exact regPad_apply x j h

/-- The final workspace bit of a lazy row record is false. -/
lemma lazyRowRecord_apply_top {m : ℕ} (hm : 1 ≤ m) (x : Reg m) (j : Fin (m + m))
    (h : j.val = m + m - 1) :
    lazyRowRecord m x j = false := by
  rw [lazyRowRecord]
  rw [cnotFold_highCnotPairs_apply (m := m) hm _ j]
  rw [if_neg (by omega : ¬ j.val < m), if_pos h]
  rw [regPad_apply']
  rw [dif_neg (by omega : ¬ j.val < m)]

/-- Every second-register coordinate below the final bit of a lazy row record equals the
corresponding vertex bit. -/
lemma lazyRowRecord_apply_agreement {m : ℕ} (hm : 1 ≤ m) (x : Reg m) (j : Fin (m + m))
    (h : m ≤ j.val) (h2 : j.val ≠ m + m - 1) :
    lazyRowRecord m x j = x ⟨j.val - m, by omega⟩ := by
  rw [lazyRowRecord]
  rw [cnotFold_highCnotPairs_apply (m := m) hm _ j]
  rw [if_neg (by omega : ¬ j.val < m), if_neg h2]
  have h1 : (regPad (m + m) m x) j = false := by
    rw [regPad_apply']
    rw [dif_neg (by omega : ¬ j.val < m)]
  have h3 : (regPad (m + m) m x) ⟨j.val - m, by omega⟩ = x ⟨j.val - m, by omega⟩ := by
    rw [regPad_apply']
    rw [dif_pos (by omega : j.val - m < m)]
  rw [h1, h3]
  simp only [Bool.false_xor]

/-- At a coordinate whose value is the top index, `lazyRowBasis x b` equals `b`. -/
lemma lazyRowBasis_of_val {m : ℕ} (x : Reg m) (b : Bool) (i : Fin m) (h : i.val + 1 = m) :
    lazyRowBasis x b i = b := by
  simp only [lazyRowBasis]
  rw [if_pos h]

/-- At the top coordinate, the base index register has bit equal to the parity of `j`. -/
lemma lazyMatchingIndexNat_distinguished {m : ℕ} (j : ℕ) (w : Fin m) (hw : w.val + 1 = m) :
    lazyMatchingIndexNat j w = decide (j % 2 = 1) := by
  simp [lazyMatchingIndexNat, hw]

/-- At any coordinate below the top bit, the base index register is false. -/
lemma lazyMatchingIndexNat_agreement {m : ℕ} (j : ℕ) (w : Fin m) (hw : w.val + 1 ≠ m) :
    lazyMatchingIndexNat j w = false := by
  simp [lazyMatchingIndexNat, hw]

/-- At the top coordinate, the neighbor register has bit equal to the parity of `j`. -/
lemma lazyMatchingNeighbourNat_distinguished {m : ℕ} (j : ℕ) (x : Reg m) (w : Fin m)
    (hw : w.val + 1 = m) : lazyMatchingNeighbourNat x j w = decide (j % 2 = 1) := by
  simp [lazyMatchingNeighbourNat, hw]

/-- At any coordinate below the top bit, the neighbor register preserves the bit of `x`. -/
lemma lazyMatchingNeighbourNat_agreement {m : ℕ} (j : ℕ) (x : Reg m) (w : Fin m)
    (hw : w.val + 1 ≠ m) : lazyMatchingNeighbourNat x j w = x w := by
  simp [lazyMatchingNeighbourNat, hw]

/-- The base index and neighbor registers have the same bit at the top coordinate. -/
lemma lazyMatchingIndexNat_eq_neighbour {m : ℕ} (j : ℕ) (x : Reg m) (w : Fin m)
    (hw : w.val + 1 = m) : lazyMatchingIndexNat j w = lazyMatchingNeighbourNat x j w := by
  simp [lazyMatchingIndexNat, lazyMatchingNeighbourNat, hw]

/-- For positive register width, the lazy matching support of every vertex has exactly two
elements. -/
lemma lazySupport_card {m : ℕ} (hm : 1 ≤ m) (x : Reg m) : (lazySupport x).card = 2 := by
  have hne : lazyMatchingNeighbourNat x 0 ≠ lazyMatchingNeighbourNat x 1 := by
    intro h
    have h1 := congrFun h (lazyTopIndex m hm)
    rw [lazyMatchingNeighbourNat_distinguished 0 x _ (by rw [lazyTopIndex_val]; omega),
      lazyMatchingNeighbourNat_distinguished 1 x _ (by rw [lazyTopIndex_val]; omega)] at h1
    norm_num at h1
  simp [lazySupport, hne]

/-- Applying the lower-bit CNOT block to a vertex concatenated with a base index produces that
vertex concatenated with its corresponding neighbor. -/
lemma cnotFold_baseRecord {m : ℕ} (hm : 1 ≤ m) (x : Reg m) (j : ℕ) :
    cnotFold (highCnotPairs m) (regCat x (lazyMatchingIndexNat j)) =
      regCat x (lazyMatchingNeighbourNat x j) := by
  funext w
  rw [cnotFold_highCnotPairs_apply (m := m) hm _ w]
  by_cases h1 : w.val < m
  · rw [if_pos h1]
    rw [regCat_apply_left x (lazyMatchingIndexNat j) w h1,
      regCat_apply_left x (lazyMatchingNeighbourNat x j) w h1]
  · by_cases h2 : w.val = m + m - 1
    · rw [if_neg h1, if_pos h2]
      have hwm : m ≤ w.val := by omega
      rw [regCat_apply_right x (lazyMatchingIndexNat j) w hwm,
        regCat_apply_right x (lazyMatchingNeighbourNat x j) w hwm]
      exact lazyMatchingIndexNat_eq_neighbour j x _ (by
        have hv : ((⟨w.val - m, by omega⟩ : Fin m)).val = w.val - m := rfl
        omega)
    · rw [if_neg h1, if_neg h2]
      have hwm : m ≤ w.val := by omega
      have hlt : w.val - m < m := by omega
      have hne : (w.val - m) + 1 ≠ m := by omega
      have hA : regCat x (lazyMatchingIndexNat j) w = false := by
        rw [regCat_apply_right x (lazyMatchingIndexNat j) w hwm]
        exact lazyMatchingIndexNat_agreement j _ hne
      have hB : regCat x (lazyMatchingIndexNat j) (⟨w.val - m, by omega⟩ : Fin (m + m)) =
          x ⟨w.val - m, by omega⟩ := by
        rw [regCat_apply_left x (lazyMatchingIndexNat j) ⟨w.val - m, by omega⟩ hlt]
      have hC : regCat x (lazyMatchingNeighbourNat x j) w = x ⟨w.val - m, by omega⟩ := by
        rw [regCat_apply_right x (lazyMatchingNeighbourNat x j) w hwm]
        exact lazyMatchingNeighbourNat_agreement j x _ hne
      rw [hA, hB, hC]
      simp only [Bool.false_xor]
end Qatlib.Concepts.WalkSearch.FrameSpectral
