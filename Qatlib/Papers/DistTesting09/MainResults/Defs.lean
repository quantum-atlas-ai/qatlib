/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
set_option warningAsError false

namespace Qatlib.Papers.DistTesting09.MainResults.Defs

abbrev Dist (N : ℕ) := FinDist (Fin N)

variable {N : ℕ}

def l1 (p q : Dist N) : ℝ := ∑ i, |p.prob i - q.prob i|

def inner (p q : Dist N) : ℝ := ∑ i, p.prob i * q.prob i

def uniform (N : ℕ) [NeZero N] : Dist N where
  prob _ := (N : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N))

def nonuniform [NeZero N] (ε : ℝ) (p : Dist N) : Prop := ε ≤ l1 p (uniform N)

@[simp] theorem uniform_prob [NeZero N] (i : Fin N) : (uniform N).prob i = (N : ℝ)⁻¹ := rfl

theorem l1_nonneg (p q : Dist N) : 0 ≤ l1 p q :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem inner_nonneg (p q : Dist N) : 0 ≤ inner p q :=
  Finset.sum_nonneg fun i _ => mul_nonneg (p.nonneg i) (q.nonneg i)

theorem inner_self_nonneg (p : Dist N) : 0 ≤ inner p p :=
  inner_nonneg p p

theorem l1_self (p : Dist N) : l1 p p = 0 := by
  simp [l1]

theorem l1_comm (p q : Dist N) : l1 p q = l1 q p := by
  unfold l1
  exact Finset.sum_congr rfl fun i _ => abs_sub_comm _ _

theorem l1_triangle (p q r : Dist N) : l1 p r ≤ l1 p q + l1 q r := by
  unfold l1
  calc ∑ i, |p.prob i - r.prob i|
      = ∑ i, |(p.prob i - q.prob i) + (q.prob i - r.prob i)| := by
        exact Finset.sum_congr rfl fun i _ => by ring_nf
    _ ≤ ∑ i, (|p.prob i - q.prob i| + |q.prob i - r.prob i|) :=
        Finset.sum_le_sum fun i _ => abs_add_le _ _
    _ = (∑ i, |p.prob i - q.prob i|) + ∑ i, |q.prob i - r.prob i| :=
        Finset.sum_add_distrib

theorem sum_abs_sq_le_card_mul_sum_sq (d : Fin N → ℝ) :
    (∑ i, |d i|) ^ 2 ≤ (N : ℝ) * ∑ i, (d i) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun _ => (1 : ℝ)) (fun x => |d x|)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    one_mul, one_pow, mul_assoc, sq_abs] using! h

theorem sum_sq_sub_uniform [NeZero N] (p : Dist N) :
    ∑ i, (p.prob i - (N : ℝ)⁻¹) ^ 2 = inner p p - (N : ℝ)⁻¹ := by
  set c : ℝ := (N : ℝ)⁻¹ with hc
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hsum : ∑ i, p.prob i = 1 := p.sum_one
  have hexp : ∑ i, (p.prob i - c) ^ 2
      = ∑ i, (p.prob i * p.prob i - 2 * c * p.prob i + c ^ 2) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hA : (∑ i, p.prob i * p.prob i) = inner p p := rfl
  have hB : (∑ i, 2 * c * p.prob i) = 2 * c * (∑ i, p.prob i) := by
    rw [Finset.mul_sum]
  have hC : (∑ i : Fin N, c ^ 2) = (N : ℝ) * c ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  rw [hA, hB, hC, hsum, hc]
  field_simp
  ring

theorem prop2_inner_lower [NeZero N] (ε : ℝ) (p : Dist N) (hε : 0 ≤ ε)
    (hnu : nonuniform ε p) :
    (1 + ε ^ 2) / (N : ℝ) ≤ inner p p := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hnu' : ε ≤ l1 p (uniform N) := hnu
  have hcs := sum_abs_sq_le_card_mul_sum_sq (fun i : Fin N => p.prob i - (uniform N).prob i)
  have hd : ∑ i, (p.prob i - (N : ℝ)⁻¹) ^ 2 = inner p p - (N : ℝ)⁻¹ :=
    sum_sq_sub_uniform p
  have hl1nn : 0 ≤ l1 p (uniform N) := l1_nonneg p (uniform N)
  have hsq : l1 p (uniform N) ^ 2 ≤ (N : ℝ) * ∑ i, (p.prob i - (N : ℝ)⁻¹) ^ 2 := by
    calc l1 p (uniform N) ^ 2
        = (∑ i, |p.prob i - (uniform N).prob i|) ^ 2 := rfl
      _ ≤ (N : ℝ) * ∑ i, (p.prob i - (N : ℝ)⁻¹) ^ 2 := hcs
  have hε2 : ε ^ 2 ≤ (N : ℝ) * ∑ i, (p.prob i - (N : ℝ)⁻¹) ^ 2 := by
    nlinarith [hε, hnu', hl1nn, hsq]
  rw [hd] at hε2
  have hNm : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN
  rw [div_le_iff₀ hNpos]
  linarith

variable {M : ℕ}

def sampleSum (p : Dist N) (S : Fin M → Fin N) : ℝ := ∑ a, p.prob (S a)

def supportOf (S : Fin M → Fin N) : Finset (Fin N) := Finset.univ.image S

def collisionProb (q : Dist N) (A : Finset (Fin N)) : ℝ := ∑ i ∈ A, q.prob i

def bigSet (p : Dist N) (M : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i => (1 : ℝ) / (2 * (M : ℝ) ^ 2) < p.prob i

def wBig (p : Dist N) (M : ℕ) : ℝ := ∑ i ∈ bigSet p M, p.prob i

def noBigElements (p : Dist N) (M : ℕ) : Prop :=
  ∀ i, p.prob i ≤ (1 : ℝ) / (2 * (M : ℝ) ^ 2)

def probSampleSumGe (p : Dist N) (M : ℕ) (threshold : ℝ) : ℝ :=
  p.probEvent (L := M) fun S => threshold ≤ sampleSum p S

theorem eventMass_independent_const (p : Dist N) (F : (Fin M → Fin N) → Prop)
    [DecidablePred F] :
    eventMass (independent (fun _ : Fin M => p)) F = p.probEvent (L := M) F := rfl

theorem probEvent_compl (p : Dist N) (E : (Fin M → Fin N) → Prop) [DecidablePred E] :
    p.probEvent (L := M) (fun S => ¬ E S) = 1 - p.probEvent (L := M) E := by
  have hsplit : (∑ S ∈ Finset.univ.filter E, p.probOf S)
      + (∑ S ∈ Finset.univ.filter (fun S => ¬ E S), p.probOf S) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := E)]
    exact FinDist.sum_probOf p M
  simp only [FinDist.probEvent]
  linarith

theorem probEvent_le_one (p : Dist N) (E : (Fin M → Fin N) → Prop) [DecidablePred E] :
    p.probEvent (L := M) E ≤ 1 := by
  have h := probEvent_compl (M := M) p E
  have hnn : 0 ≤ p.probEvent (L := M) (fun S => ¬ E S) :=
    Finset.sum_nonneg fun S _ => Finset.prod_nonneg fun i _ => p.nonneg _
  linarith

theorem probEvent_mono (p : Dist N) (E F : (Fin M → Fin N) → Prop)
    [DecidablePred E] [DecidablePred F] (h : ∀ S, E S → F S) :
    p.probEvent (L := M) E ≤ p.probEvent (L := M) F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS
    simp only [Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, h S hS.2⟩
  · intro S _ _; exact Finset.prod_nonneg fun i _ => p.nonneg _

theorem inner_self_le_max (p : Dist N) (C : ℝ) (h : ∀ i, p.prob i ≤ C) :
    inner p p ≤ C := by
  have hterm : ∀ i : Fin N, p.prob i * p.prob i ≤ C * p.prob i := by
    intro i
    exact mul_le_mul_of_nonneg_right (h i) (p.nonneg i)
  calc inner p p = ∑ i, p.prob i * p.prob i := rfl
    _ ≤ ∑ i, C * p.prob i := Finset.sum_le_sum fun i _ => hterm i
    _ = C * ∑ i, p.prob i := (Finset.mul_sum _ _ _).symm
    _ = C := by rw [p.sum_one, mul_one]

theorem inner_self_le_of_noBig (p : Dist N) (M : ℕ) (hnb : noBigElements p M) :
    inner p p ≤ (1 : ℝ) / (2 * (M : ℝ) ^ 2) :=
  inner_self_le_max p _ hnb

def massOf (p : Dist N) (B : Finset (Fin N)) : ℝ := ∑ i ∈ B, p.prob i

def renormalizeOff (p : Dist N) (B : Finset (Fin N)) (h : massOf p B < 1) : Dist N where
  prob i := if i ∈ B then 0 else p.prob i / (1 - massOf p B)
  nonneg i := by
    by_cases hi : i ∈ B
    · simp [hi]
    · simp only [hi, if_false]
      exact div_nonneg (p.nonneg i) (by linarith [h])
  sum_one := by
    have hw : massOf p B < 1 := h
    have hcompl : (∑ i ∈ Finset.univ.filter (fun i => i ∉ B), p.prob i)
        = 1 - massOf p B := by
      have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin N)))
        (p := fun i => i ∈ B) (f := fun i => p.prob i)
      have hwB : (∑ i ∈ Finset.univ.filter (fun i => i ∈ B), p.prob i) = massOf p B := by
        simp only [massOf, Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [hwB, p.sum_one] at hsplit
      linarith
    have hpt : ∀ i : Fin N, (if i ∈ B then (0 : ℝ) else p.prob i / (1 - massOf p B))
        = (1 - massOf p B)⁻¹ * (if i ∈ B then (0 : ℝ) else p.prob i) := by
      intro i
      by_cases hi : i ∈ B <;> simp [hi, div_eq_mul_inv, mul_comm]
    rw [Finset.sum_congr rfl fun i _ => hpt i, ← Finset.mul_sum]
    have hfilter : (∑ i, if i ∈ B then (0 : ℝ) else p.prob i)
        = ∑ i ∈ Finset.univ.filter (fun i => i ∉ B), p.prob i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ B <;> simp [hi]
    rw [hfilter, hcompl]
    exact inv_mul_cancel₀ (by linarith : (1 - massOf p B) ≠ 0)

theorem l1_renormalizeOff_le (p : Dist N) (B : Finset (Fin N)) (h : massOf p B < 1) :
    l1 p (renormalizeOff p B h) ≤ 2 * massOf p B := by
  suffices hmain : l1 p (renormalizeOff p B h) = 2 * massOf p B by rw [hmain]
  have hw1 : 0 < 1 - massOf p B := by linarith [h]
  have hcompl : (∑ i ∈ Finset.univ.filter (fun i => i ∉ B), p.prob i)
      = 1 - massOf p B := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin N)))
      (p := fun i => i ∈ B) (f := fun i => p.prob i)
    have hwB : (∑ i ∈ Finset.univ.filter (fun i => i ∈ B), p.prob i) = massOf p B := by
      simp only [massOf, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hwB, p.sum_one] at hsplit
    linarith
  have hsumB : (∑ i ∈ Finset.univ.filter (fun i => i ∈ B), p.prob i) = massOf p B := by
    simp only [massOf, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hterm : ∀ i : Fin N, |p.prob i - (renormalizeOff p B h).prob i| =
      if i ∈ B then p.prob i else p.prob i * massOf p B / (1 - massOf p B) := by
    intro i
    by_cases hi : i ∈ B
    · have hz : (renormalizeOff p B h).prob i = 0 := by simp [renormalizeOff, hi]
      rw [hz, sub_zero, abs_of_nonneg (p.nonneg i)]
      simp [hi]
    · simp only [renormalizeOff, hi, if_false]
      have hm0 : 0 ≤ massOf p B := Finset.sum_nonneg fun j _ => p.nonneg j
      have hge : p.prob i ≤ p.prob i / (1 - massOf p B) := by
        rw [le_div_iff₀ hw1]
        nlinarith [p.nonneg i, hm0, mul_nonneg (p.nonneg i) hm0, hw1.le]
      have hneg : p.prob i - p.prob i / (1 - massOf p B) ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      field_simp
      ring
  calc l1 p (renormalizeOff p B h)
      = ∑ i, |p.prob i - (renormalizeOff p B h).prob i| := rfl
    _ = ∑ i, (if i ∈ B then p.prob i
          else p.prob i * massOf p B / (1 - massOf p B)) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = (∑ i ∈ Finset.univ.filter (fun i => i ∈ B), p.prob i)
          + ∑ i ∈ Finset.univ.filter (fun i => i ∉ B),
              p.prob i * massOf p B / (1 - massOf p B) := by
        rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin N)))
          (p := fun i => i ∈ B)
          (f := fun i => if i ∈ B then p.prob i
            else p.prob i * massOf p B / (1 - massOf p B))]
        congr 1
        · exact Finset.sum_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
        · exact Finset.sum_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
    _ = massOf p B + massOf p B := by
        rw [hsumB]
        have hscale : (∑ i ∈ Finset.univ.filter (fun i => i ∉ B),
              p.prob i * massOf p B / (1 - massOf p B))
            = (∑ i ∈ Finset.univ.filter (fun i => i ∉ B), p.prob i)
                * (massOf p B / (1 - massOf p B)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hscale, hcompl]
        field_simp
    _ = 2 * massOf p B := by ring

theorem expect_indicator (p : Dist N) (B : Finset (Fin N)) :
    p.expect (fun x => if x ∈ B then (1 : ℝ) else 0) = ∑ x ∈ B, p.prob x := by
  simp only [FinDist.expect]
  rw [show (∑ x, p.prob x * (if x ∈ B then (1 : ℝ) else 0))
      = ∑ x, (if x ∈ B then p.prob x else 0) from
    Finset.sum_congr rfl fun x _ => by by_cases h : x ∈ B <;> simp [h]]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

def hitCount {M : ℕ} (B : Finset (Fin N)) (ω : Fin M → Fin N) : ℝ :=
  ∑ a, if ω a ∈ B then (1 : ℝ) else 0

theorem indicator_variance_le (p : Dist N) (B : Finset (Fin N)) :
    p.variance (fun x => if x ∈ B then (1 : ℝ) else 0) ≤ ∑ x ∈ B, p.prob x := by
  have hw0 : 0 ≤ ∑ x ∈ B, p.prob x := Finset.sum_nonneg fun x _ => p.nonneg x
  rw [FinDist.variance_eq_expect_sq_sub]
  have hsq : p.expect (fun x => (if x ∈ B then (1 : ℝ) else 0) ^ 2)
      = p.expect (fun x => if x ∈ B then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : x ∈ B <;> simp [FinDist.expect, h]
  rw [hsq, expect_indicator]
  nlinarith [sq_nonneg (∑ x ∈ B, p.prob x), hw0]

theorem variance_id_le (p : Dist N) (C : ℝ) (hC : ∀ i, p.prob i ≤ C) :
    p.variance p.prob ≤ C * inner p p := by
  rw [FinDist.variance_eq_expect_sq_sub]
  have hsq : p.expect (fun x => (p.prob x) ^ 2) = ∑ i, p.prob i ^ 3 := by
    simp only [FinDist.expect]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmean : p.expect p.prob = inner p p := by
    simp only [FinDist.expect, inner]
  rw [hsq, hmean]
  have hcube : (∑ i, p.prob i ^ 3) ≤ C * ∑ i, p.prob i ^ 2 := by
    calc (∑ i, p.prob i ^ 3) = ∑ i, p.prob i ^ 2 * p.prob i :=
          Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, p.prob i ^ 2 * C :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hC i) (sq_nonneg _)
      _ = C * ∑ i, p.prob i ^ 2 := by rw [← Finset.sum_mul, mul_comm]
  have hin : inner p p = ∑ i, p.prob i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hin] at *
  nlinarith [Finset.sum_nonneg (s := Finset.univ)
    (f := fun i : Fin N => p.prob i ^ 2) fun i _ => sq_nonneg (p.prob i), hcube]

end Qatlib.Papers.DistTesting09.MainResults.Defs
