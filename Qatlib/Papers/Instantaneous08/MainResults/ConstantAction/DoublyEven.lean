/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.DirectionalDeriv
import Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox.YDistribution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Doubly even codes and deterministic classical bias

This module develops restricted weights `wtOn`, overlap counts `ovOn`, and binary dot products
`dotOn`. It shows that unit X-program bias at π/8 forces the induced code weights to be
divisible by four and then forces unit bias for the classical approximation, establishing the
implication of Theorem 2 in [ShepherdBremner2009].

## Main statements

* `codeWeight_dvd_four`: deduces doubly even weights from unit quantum bias.
* `Qs_eq_zero_of_doublyEven`: deduces vanishing of the classical binary matrix.
* `yBias_eq_one_of_xBias_eq_one`: transfers unit bias from the X-program to the classical
  sample.

## References

* [Shepherd and Bremner, 2009][ShepherdBremner2009]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Instantaneous08.MainResults.ConstantAction

open Qatlib.Papers.Instantaneous08.MainResults.XProgram

attribute [local instance] Classical.propDecidable

/-- The number of coordinates equal to `1` in the binary word `c`, restricted to `t`. -/
def wtOn {k : ℕ} (t : Finset (Fin k)) (c : Fin k → ZMod 2) : ℕ :=
  (t.filter (fun i => c i = 1)).card

/-- The number of coordinates in `t` where both binary words equal `1`. -/
def ovOn {k : ℕ} (t : Finset (Fin k)) (c1 c2 : Fin k → ZMod 2) : ℕ :=
  (t.filter (fun i => c1 i = 1 ∧ c2 i = 1)).card

/-- The binary dot product of two words restricted to the coordinates in `t`. -/
def dotOn {k : ℕ} (t : Finset (Fin k)) (c1 c2 : Fin k → ZMod 2) : ZMod 2 :=
  ∑ i ∈ t, c1 i * c2 i

/-- The cardinality of a filtered finite set equals the sum of its natural-valued predicate
indicators. -/
theorem card_filter_eq_sum {ι : Type} (s : Finset ι) (q : ι → Prop)
    [DecidablePred q] : (s.filter q).card = ∑ i ∈ s, if q i then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The integer weight of a sum of binary words equals the sum of their weights minus twice
their overlap count. -/
theorem wtOn_add_cast {k : ℕ} (t : Finset (Fin k)) (c1 c2 : Fin k → ZMod 2) :
    (wtOn t (c1 + c2) : ℤ) = (wtOn t c1 : ℤ) + (wtOn t c2 : ℤ) -
      2 * (ovOn t c1 c2 : ℤ) := by
  unfold wtOn ovOn
  simp only [Pi.add_apply]
  rw [card_filter_eq_sum t (fun i => c1 i + c2 i = 1),
    card_filter_eq_sum t (fun i => c1 i = 1),
    card_filter_eq_sum t (fun i => c2 i = 1),
    card_filter_eq_sum t (fun i => c1 i = 1 ∧ c2 i = 1)]
  push_cast
  have hpt : ∀ i : Fin k,
      (if c1 i + c2 i = 1 then (1 : ℤ) else 0) =
        (if c1 i = 1 then (1 : ℤ) else 0) + (if c2 i = 1 then (1 : ℤ) else 0) -
          2 * (if c1 i = 1 ∧ c2 i = 1 then (1 : ℤ) else 0) := by
    intro i
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases ClassicalApprox.zmod2_eq_zero_or_one (c1 i) with h1 | h1 <;>
      rcases ClassicalApprox.zmod2_eq_zero_or_one (c2 i) with h2 | h2 <;>
      rw [h1, h2] <;> decide
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- The restricted binary dot product is the overlap count reduced modulo two. -/
theorem dotOn_eq_ovOn {k : ℕ} (t : Finset (Fin k)) (c1 c2 : Fin k → ZMod 2) :
    dotOn t c1 c2 = (ovOn t c1 c2 : ZMod 2) := by
  unfold dotOn ovOn
  have hcast : ((t.filter (fun i => c1 i = 1 ∧ c2 i = 1)).card : ZMod 2) =
      ∑ i ∈ t, (if c1 i = 1 ∧ c2 i = 1 then (1 : ZMod 2) else 0) := by
    rw [card_filter_eq_sum]
    push_cast
    simp
  rw [hcast]
  apply Finset.sum_congr rfl
  intro i _
  rcases ClassicalApprox.zmod2_eq_zero_or_one (c1 i) with h1 | h1 <;>
    rcases ClassicalApprox.zmod2_eq_zero_or_one (c2 i) with h2 | h2 <;>
    rw [h1, h2] <;> decide

/-- If the restricted weights of two words and their sum are divisible by four, their restricted
dot product vanishes. -/
theorem dotOn_eq_zero_of_weights {k : ℕ} (t : Finset (Fin k)) (c1 c2 : Fin k → ZMod 2)
    (h1 : ∃ a : ℤ, (wtOn t c1 : ℤ) = 4 * a)
    (h2 : ∃ a : ℤ, (wtOn t c2 : ℤ) = 4 * a)
    (h12 : ∃ a : ℤ, (wtOn t (c1 + c2) : ℤ) = 4 * a) : dotOn t c1 c2 = 0 := by
  rw [dotOn_eq_ovOn]
  obtain ⟨a1, ha1⟩ := h1
  obtain ⟨a2, ha2⟩ := h2
  obtain ⟨a12, ha12⟩ := h12

  have hcast := wtOn_add_cast t c1 c2
  have hov : (ovOn t c1 c2 : ℤ) = 2 * (a1 + a2 - a12) := by
    rw [ha1, ha2, ha12] at hcast
    linarith
  have hzero : ((ovOn t c1 c2 : ℕ) : ZMod 2) = 0 := by
    rw [← Int.cast_natCast (ovOn t c1 c2), hov]
    have h2z : (2 : ZMod 2) = 0 := by decide
    push_cast
    rw [h2z]
    ring
  exact hzero

/-- The restricted weight of the row-dot-product word on `subRowSet p s` equals `codeWeight p s
a`. -/
theorem wtOn_subRowSet {n k : ℕ} (p : Fin k → F2Vec n) (s a : F2Vec n) :
    wtOn (subRowSet p s) (fun i => dot (p i) a) = codeWeight p s a := by
  rfl

/-- If `cos (π * M / 8) ^ 2` equals one for an integer `M`, then eight divides `M`. -/
theorem eight_dvd_of_cos_sq_eq_one {M : ℤ}
    (h : Real.cos (Real.pi / 8 * (M : ℝ)) ^ 2 = 1) : (8 : ℤ) ∣ M := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpm : Real.cos (Real.pi / 8 * (M : ℝ)) = 1 ∨
      Real.cos (Real.pi / 8 * (M : ℝ)) = -1 := by
    rcases sq_eq_one_iff.mp h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  rcases hpm with h1 | h1
  · rw [Real.cos_eq_one_iff] at h1
    obtain ⟨k, hk⟩ := h1
    have hEq : (M : ℝ) = 16 * (k : ℝ) := by
      field_simp at hk
      linarith
    have : (M : ℤ) = 16 * k := by exact_mod_cast hEq
    exact ⟨2 * k, by rw [this]; ring⟩
  · rw [Real.cos_eq_neg_one_iff] at h1
    obtain ⟨k, hk⟩ := h1
    have hEq : (M : ℝ) = 8 * (2 * (k : ℝ) + 1) := by
      field_simp at hk
      linarith
    have : (M : ℤ) = 8 * (2 * k + 1) := by exact_mod_cast hEq
    exact ⟨2 * k + 1, by rw [this]⟩

/-- Unit X-program bias at π/8 forces every induced codeword weight to be divisible by four. See
[ShepherdBremner2009]. -/
theorem codeWeight_dvd_four {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n)
    (h : (∑ x : F2Vec n,
        (if dot x s = 0 then prob p (fun _ => Real.pi / 8) x else 0)) = 1) :
    ∀ a : F2Vec n, (4 : ℤ) ∣ (codeWeight p s a : ℤ) := by
  have hcos := (bias_eq_one_iff p s).mp h

  have hcosM : ∀ a : F2Vec n,
      Real.cos (Real.pi / 8 * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ))) ^ 2 = 1 := by
    intro a
    have harg : Real.pi / 16 * fdiff p s a =
        Real.pi / 8 * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ)) := by
      rw [fdiff_eq]; ring
    simpa only [harg] using hcos a
  have hdiv : ∀ a : F2Vec n,
      (8 : ℤ) ∣ (nSub p s : ℤ) - 2 * (codeWeight p s a : ℤ) := by
    intro a
    have hMcast : ((((nSub p s : ℤ) - 2 * (codeWeight p s a : ℤ)) : ℤ) : ℝ) =
        (nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ) := by push_cast; ring
    refine eight_dvd_of_cos_sq_eq_one (M := (nSub p s : ℤ) - 2 * (codeWeight p s a : ℤ)) ?_
    rw [hMcast]
    exact hcosM a

  have hzero : codeWeight p s 0 = 0 := by
    unfold codeWeight
    simp [dot]
  have hnSub : (8 : ℤ) ∣ (nSub p s : ℤ) := by
    have := hdiv 0
    rw [hzero] at this
    simpa using this
  obtain ⟨t0, ht0⟩ := hnSub
  intro a
  obtain ⟨k, hk⟩ := hdiv a
  have : (codeWeight p s a : ℤ) = 4 * (t0 - k) := by omega
  exact ⟨t0 - k, this⟩

/-- If all induced codeword weights are divisible by four, every pair of induced words has zero
restricted dot product. See [ShepherdBremner2009]. -/
theorem dotOn_eq_zero_of_doublyEven {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n)
    (hwt : ∀ a : F2Vec n, (4 : ℤ) ∣ (codeWeight p s a : ℤ))
    (a1 a2 : F2Vec n) :
    dotOn (subRowSet p s) (fun i => dot (p i) a1) (fun i => dot (p i) a2) = 0 := by
  have hcw : ∀ a : F2Vec n, ∃ m : ℤ, (wtOn (subRowSet p s)
      (fun i => dot (p i) a) : ℤ) = 4 * m := by
    intro a
    obtain ⟨m, hm⟩ := hwt a
    exact ⟨m, by rw [wtOn_subRowSet]; exact hm⟩
  have hsum : (fun i => dot (p i) (a1 + a2)) =
      ((fun i => dot (p i) a1) + (fun i => dot (p i) a2) : Fin k → ZMod 2) := by
    funext i
    change dot (p i) (a1 + a2) = dot (p i) a1 + dot (p i) a2
    rw [dot]
    change (p i) ⬝ᵥ (a1 + a2) = (p i) ⬝ᵥ a1 + (p i) ⬝ᵥ a2
    exact dotProduct_add _ _ _
  refine dotOn_eq_zero_of_weights (subRowSet p s)
    (fun i => dot (p i) a1) (fun i => dot (p i) a2)
    (hcw a1) (hcw a2) ?_
  rw [← hsum]
  exact hcw (a1 + a2)

/-- If all induced codeword weights are divisible by four, the classical approximation matrix
`Qs p s` vanishes. See [ShepherdBremner2009]. -/
theorem Qs_eq_zero_of_doublyEven {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n)
    (hwt : ∀ a : F2Vec n, (4 : ℤ) ∣ (codeWeight p s a : ℤ)) :
    ClassicalApprox.Qs p s = 0 := by
  have hself : ∀ a1 a2 : F2Vec n,
      dotOn (subRowSet p s) (fun i => dot (p i) a1) (fun i => dot (p i) a2) = 0 :=
    dotOn_eq_zero_of_doublyEven p s hwt
  ext i j
  rw [Matrix.zero_apply]
  simp only [ClassicalApprox.Qs, Matrix.mul_apply, Matrix.transpose_apply,
    ClassicalApprox.Ps]
  rw [show (∑ x : ClassicalApprox.rowsInS p s, p (x.1) i * p (x.1) j) =
      ∑ r ∈ subRowSet p s, p r i * p r j from
    (Finset.sum_subtype (s := subRowSet p s) (fun x => by simp [subRowSet]; exact Iff.rfl)
      (fun r => p r i * p r j)).symm]
  have := hself (Pi.single i (1 : ZMod 2)) (Pi.single j (1 : ZMod 2))
  unfold dotOn at this
  simpa [dot, dotProduct_single_one] using this

/-- Unit X-program bias at π/8 implies unit bias for the classical sample, as in [Shepherd and
Bremner, Theorem 2][ShepherdBremner2009]. -/
theorem yBias_eq_one_of_xBias_eq_one {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n)
    (h : (∑ x : F2Vec n,
        (if dot x s = 0 then prob p (fun _ => Real.pi / 8) x else 0)) = 1) :
    ClassicalApprox.pairProb
      (fun d e => ClassicalApprox.dot (ClassicalApprox.ySample p d e) s = 0) = 1 := by
  have hwt := codeWeight_dvd_four p s h
  have hQs := Qs_eq_zero_of_doublyEven p s hwt
  rw [ClassicalApprox.yBias_eq_rank]
  rw [hQs, Matrix.rank_zero]
  norm_num

end Qatlib.Papers.Instantaneous08.MainResults.ConstantAction
