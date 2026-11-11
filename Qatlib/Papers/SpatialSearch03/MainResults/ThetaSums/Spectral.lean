/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Lattice dispersion and the secular function

This module defines the centered wave vectors, dispersion, secular function, and first two
inverse-dispersion lattice sums for the periodic lattice model of [ChildsGoldstone2004]. It
establishes quadratic dispersion comparisons and analytic properties of the secular function at
negative energies.

## Main statements

* `dispersion_le_sum_sq` and `dispersion_ge_sum_sq`: quadratic comparisons for the dispersion.
* `secular_strictMonoOn` and `hasDerivAt_secular`: monotonicity and differentiation below zero.
* `existsUnique_secular_eq_one`: existence and uniqueness of a negative solution of the secular
  equation.

## References

* [Childs and Goldstone, 2004][ChildsGoldstone2004]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums

open Finset

variable {d : ℕ}

/-- The periodic lattice dispersion `2 * ∑ j, (1 - Real.cos (k j))`. -/
def dispersion (k : Fin d → ℝ) : ℝ := 2 * ∑ j, (1 - Real.cos (k j))

/-- The wave vector obtained by multiplying each centered integer representative of a lattice
index by `2 * Real.pi / n`. -/
def waveVector (n : ℕ) (m : Fin d → ZMod n) : Fin d → ℝ :=
  fun j => 2 * Real.pi * ((m j).valMinAbs : ℝ) / n

/-- The wave vector of the zero lattice index is zero. -/
@[simp] theorem waveVector_zero (n : ℕ) :
    waveVector (d := d) n (0 : Fin d → ZMod n) = 0 := by
  funext j
  simp [waveVector]

/-- The dispersion vanishes at the zero wave vector. -/
@[simp] theorem dispersion_zero : dispersion (d := d) (0 : Fin d → ℝ) = 0 := by
  simp [dispersion]

/-- The periodic lattice dispersion is nonnegative for every real wave vector. -/
theorem dispersion_nonneg (k : Fin d → ℝ) : 0 ≤ dispersion k := by
  unfold dispersion
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg ?_)
  intro j _
  linarith [Real.cos_le_one (k j)]

/-- The dispersion is at most the sum of the squared wave-vector coordinates. -/
theorem dispersion_le_sum_sq (k : Fin d → ℝ) :
    dispersion k ≤ ∑ j, (k j) ^ 2 := by
  unfold dispersion
  have h : ∀ j ∈ (Finset.univ : Finset (Fin d)), 2 * (1 - Real.cos (k j)) ≤ (k j) ^ 2 := by
    intro j _
    linarith [Real.one_sub_sq_div_two_le_cos (x := k j)]
  calc 2 * ∑ j, (1 - Real.cos (k j))
      = ∑ j, 2 * (1 - Real.cos (k j)) := by rw [Finset.mul_sum]
    _ ≤ ∑ j, (k j) ^ 2 := Finset.sum_le_sum h

/-- If every coordinate has absolute value at most `Real.pi`, the dispersion is at least `4 /
Real.pi ^ 2` times the sum of squared coordinates. -/
theorem dispersion_ge_sum_sq (k : Fin d → ℝ) (hk : ∀ j, |k j| ≤ Real.pi) :
    (4 / Real.pi ^ 2) * ∑ j, (k j) ^ 2 ≤ dispersion k := by
  unfold dispersion
  have h : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      (4 / Real.pi ^ 2) * (k j) ^ 2 ≤ 2 * (1 - Real.cos (k j)) := by
    intro j _
    have hb := Real.cos_le_one_sub_mul_cos_sq (hk j)
    have hkey : (4 / Real.pi ^ 2) * (k j) ^ 2 = 2 * (2 / Real.pi ^ 2 * (k j) ^ 2) := by ring
    rw [hkey]
    linarith
  calc (4 / Real.pi ^ 2) * ∑ j, (k j) ^ 2
      = ∑ j, (4 / Real.pi ^ 2) * (k j) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ j, 2 * (1 - Real.cos (k j)) := Finset.sum_le_sum h
    _ = 2 * ∑ j, (1 - Real.cos (k j)) := (Finset.mul_sum ..).symm

/-- The dispersion vanishes exactly when the cosine of every coordinate is one. -/
theorem dispersion_eq_zero_iff (k : Fin d → ℝ) :
    dispersion k = 0 ↔ ∀ j, Real.cos (k j) = 1 := by
  unfold dispersion
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · norm_num at h
    · rw [Finset.sum_eq_zero_iff_of_nonneg] at h
      · intro j
        have := h j (Finset.mem_univ j)
        linarith [Real.cos_le_one (k j)]
      · intro j _
        linarith [Real.cos_le_one (k j)]
  · intro h
    right
    refine Finset.sum_eq_zero ?_
    intro j _
    rw [h j]; ring

/-- For positive side length, every centered wave-vector coordinate has absolute value at most
`Real.pi`. -/
theorem abs_waveVector_le_pi {n : ℕ} (hn : 0 < n) (m : Fin d → ZMod n) (j : Fin d) :
    |waveVector n m j| ≤ Real.pi := by
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  have hmem := (m j).valMinAbs_mem_Ioc
  have h2 : ((m j).valMinAbs : ℝ) * 2 ≤ (n : ℝ) := by exact_mod_cast hmem.2
  have h1 : -((n : ℝ)) ≤ ((m j).valMinAbs : ℝ) * 2 := by
    have h' : ((-(n : ℤ) : ℤ) : ℤ) ≤ (m j).valMinAbs * 2 := le_of_lt hmem.1
    exact_mod_cast h'
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hc : |((m j).valMinAbs : ℝ)| * 2 ≤ (n : ℝ) := by
    have habs : |((m j).valMinAbs : ℝ) * 2| ≤ (n : ℝ) := abs_le.2 ⟨by linarith, by linarith⟩
    rwa [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at habs
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  calc |waveVector n m j|
      = 2 * Real.pi * |((m j).valMinAbs : ℝ)| / n := by
        unfold waveVector
        rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2),
          abs_of_pos hpi, abs_of_pos hnR]
    _ ≤ 2 * Real.pi * ((n : ℝ) / 2) / n := by
        gcongr
        linarith
    _ = Real.pi := by
        field_simp

/-- The integer vector of centered representatives of a periodic lattice index. -/
def centredVec (n : ℕ) (m : Fin d → ZMod n) : Fin d → ℤ := fun j => (m j).valMinAbs

/-- The map from a periodic lattice index to its vector of centered integer representatives is
injective. -/
theorem centredVec_injective (n : ℕ) : Function.Injective (centredVec (d := d) n) := by
  intro m₁ m₂ h
  funext j
  have hj : (m₁ j).valMinAbs = (m₂ j).valMinAbs := by
    have := congrFun h j
    simpa [centredVec] using this
  exact ZMod.valMinAbs_inj.mp hj

/-- The lattice-volume-normalized sum of reciprocal shifted energies `γ * dispersion (waveVector
n m) - E` over all periodic lattice indices. -/
def secular (γ : ℝ) (n d : ℕ) [NeZero n] (E : ℝ) : ℝ :=
  ((n : ℝ) ^ d)⁻¹ * ∑ m : Fin d → ZMod n, (γ * dispersion (waveVector n m) - E)⁻¹

/-- The lattice-volume-normalized sum of inverse dispersions over the nonzero periodic lattice
indices. -/
def latSum1 (n d : ℕ) [NeZero n] : ℝ :=
  ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
    (dispersion (waveVector n m))⁻¹

/-- The lattice-volume-normalized sum of squared inverse dispersions over the nonzero periodic
lattice indices. -/
def latSum2 (n d : ℕ) [NeZero n] : ℝ :=
  ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
    (dispersion (waveVector n m))⁻¹ ^ 2

/-- For positive coupling and negative energy, each reciprocal shifted lattice energy is at most
the reciprocal of the absolute energy. -/
theorem inv_resolvent_le {γ E : ℝ} {n : ℕ} (hγ : 0 < γ) (hE : E < 0)
    (m : Fin d → ZMod n) :
    (γ * dispersion (waveVector n m) - E)⁻¹ ≤ |E|⁻¹ := by
  have hd := dispersion_nonneg (waveVector n m)
  have ha : 0 ≤ γ * dispersion (waveVector n m) := mul_nonneg hγ.le hd
  have hEpos : (0:ℝ) < |E| := abs_pos.2 (ne_of_lt hE)
  have hle : |E| ≤ γ * dispersion (waveVector n m) - E := by
    rw [abs_of_neg hE]; linarith
  exact inv_anti₀ hEpos hle

/-- For positive coupling and side length and negative energy, the secular function is at most
`|E|⁻¹`. -/
theorem secular_le_inv {γ : ℝ} {E : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 0 < n)
    (hE : E < 0) : secular γ n d E ≤ |E|⁻¹ := by
  have hnpos : (0:ℝ) < (n : ℝ) ^ d := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    positivity
  have hinv_nn : 0 ≤ ((n : ℝ) ^ d)⁻¹ := by positivity
  have hsum : ∑ m : Fin d → ZMod n, (γ * dispersion (waveVector n m) - E)⁻¹
      ≤ ∑ _m : Fin d → ZMod n, |E|⁻¹ := by
    refine Finset.sum_le_sum ?_
    intro m _
    exact inv_resolvent_le hγ hE m
  have hcard : (Finset.univ : Finset (Fin d → ZMod n)).card = n ^ d := by
    simp
  calc secular γ n d E
      = ((n : ℝ) ^ d)⁻¹ * ∑ m : Fin d → ZMod n, (γ * dispersion (waveVector n m) - E)⁻¹ :=
        rfl
    _ ≤ ((n : ℝ) ^ d)⁻¹ * ∑ _m : Fin d → ZMod n, |E|⁻¹ :=
        mul_le_mul_of_nonneg_left hsum hinv_nn
    _ = ((n : ℝ) ^ d)⁻¹ * ((n : ℝ) ^ d * |E|⁻¹) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring_nf
    _ = |E|⁻¹ := by field_simp

/-- For positive coupling and side length and negative energy, the zero-mode contribution `|E|⁻¹
/ n ^ d` is at most the secular function. -/
theorem le_secular {γ : ℝ} {E : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 0 < n)
    (hE : E < 0) : |E|⁻¹ / (n : ℝ) ^ d ≤ secular γ n d E := by
  have hmem : (0 : Fin d → ZMod n) ∈ (Finset.univ : Finset (Fin d → ZMod n)) :=
    Finset.mem_univ _
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin d → ZMod n)),
      0 ≤ (γ * dispersion (waveVector n i) - E)⁻¹ := by
    intro i _
    have hd := dispersion_nonneg (waveVector n i)
    have ha : 0 ≤ γ * dispersion (waveVector n i) := mul_nonneg hγ.le hd
    have hpos : γ * dispersion (waveVector n i) - E = γ * dispersion (waveVector n i) + |E| := by
      rw [abs_of_neg hE]; ring
    rw [hpos]
    exact inv_nonneg.2 (by linarith)
  have hsingle : (γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E)⁻¹
      ≤ ∑ m : Fin d → ZMod n, (γ * dispersion (waveVector n m) - E)⁻¹ :=
    Finset.single_le_sum (f := fun m : Fin d → ZMod n =>
      (γ * dispersion (waveVector n m) - E)⁻¹) hnonneg hmem
  have hzero : (γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E)⁻¹ = |E|⁻¹ := by
    have h1 : γ * dispersion (waveVector n (0 : Fin d → ZMod n)) = 0 := by
      rw [waveVector_zero, dispersion_zero, mul_zero]
    rw [h1, zero_sub, ← abs_of_neg hE]
  rw [hzero] at hsingle
  unfold secular
  calc |E|⁻¹ / (n : ℝ) ^ d = ((n : ℝ) ^ d)⁻¹ * |E|⁻¹ := by field_simp
    _ ≤ ((n : ℝ) ^ d)⁻¹ * ∑ m : Fin d → ZMod n,
          (γ * dispersion (waveVector n m) - E)⁻¹ := by
        refine mul_le_mul_of_nonneg_left hsingle (by positivity)

/-- For positive coupling and side length, the secular function is strictly increasing on the
negative real energies. -/
theorem secular_strictMonoOn {γ : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 0 < n) :
    StrictMonoOn (secular γ n d) (Set.Iio 0) := by
  intro E₁ h₁ E₂ h₂ hlt
  have hE₁ : E₁ < 0 := h₁
  have hE₂ : E₂ < 0 := h₂
  have hsum : ∑ m : Fin d → ZMod n, (γ * dispersion (waveVector n m) - E₁)⁻¹
      < ∑ m : Fin d → ZMod n, (γ * dispersion (waveVector n m) - E₂)⁻¹ := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro m _
      have hd := dispersion_nonneg (waveVector n m)
      have ha : 0 ≤ γ * dispersion (waveVector n m) := mul_nonneg hγ.le hd
      have hpos : (0:ℝ) < γ * dispersion (waveVector n m) - E₂ := by linarith
      have hlt' : γ * dispersion (waveVector n m) - E₂ < γ * dispersion (waveVector n m) - E₁ := by
        linarith
      exact (inv_strictAnti₀ hpos hlt').le
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      have hd := dispersion_nonneg (waveVector n (0 : Fin d → ZMod n))
      have ha : 0 ≤ γ * dispersion (waveVector n (0 : Fin d → ZMod n)) :=
        mul_nonneg hγ.le hd
      have hpos : (0:ℝ) < γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E₂ := by
        linarith
      have hlt' : γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E₂
          < γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E₁ := by linarith
      exact inv_strictAnti₀ hpos hlt'
  unfold secular
  exact mul_lt_mul_of_pos_left hsum (by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    positivity)

/-- For positive coupling and negative energy, the derivative of the secular function is the
lattice-volume-normalized sum of squared reciprocal shifted energies [ChildsGoldstone2004]. -/
theorem hasDerivAt_secular {γ : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ) {E : ℝ} (hE : E < 0) :
    HasDerivAt (secular γ n d)
      (((n : ℝ) ^ d)⁻¹ * ∑ m : Fin d → ZMod n,
        (γ * dispersion (waveVector n m) - E)⁻¹ ^ 2) E := by
  have hterm : ∀ m ∈ (Finset.univ : Finset (Fin d → ZMod n)),
      HasDerivAt (fun y : ℝ => (γ * dispersion (waveVector n m) - y)⁻¹)
        ((γ * dispersion (waveVector n m) - E)⁻¹ ^ 2) E := by
    intro m _
    have hg : HasDerivAt (fun y : ℝ => γ * dispersion (waveVector n m) - y) (-1) E := by
      have h1 : HasDerivAt (fun y : ℝ => γ * dispersion (waveVector n m) - y) (0 - 1) E :=
        (hasDerivAt_const (x := E) (c := γ * dispersion (waveVector n m))).sub
          (hasDerivAt_id E)
      simpa using h1
    have hd := dispersion_nonneg (waveVector n m)
    have ha : 0 ≤ γ * dispersion (waveVector n m) := mul_nonneg hγ.le hd
    have hne : γ * dispersion (waveVector n m) - E ≠ 0 := by linarith
    have h := hg.inv hne
    have hval : - -1 / (γ * dispersion (waveVector n m) - E) ^ 2
        = (γ * dispersion (waveVector n m) - E)⁻¹ ^ 2 := by
      rw [neg_neg, div_eq_mul_inv, one_mul, inv_pow]
    rw [hval] at h
    exact h
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin d → ZMod n))) hterm
  exact hsum.const_mul _

/-- For positive side length and negative energy, the zero-mode term `1 / (n ^ d * E ^ 2)`
bounds the normalized squared-resolvent sum from below [ChildsGoldstone2004]. -/
theorem secular_deriv_ge {γ : ℝ} {n : ℕ} [NeZero n] (hn : 0 < n) {E : ℝ} (_hE : E < 0) :
    1 / ((n : ℝ) ^ d * E ^ 2)
      ≤ ((n : ℝ) ^ d)⁻¹ * ∑ m : Fin d → ZMod n,
          (γ * dispersion (waveVector n m) - E)⁻¹ ^ 2 := by
  have hmem : (0 : Fin d → ZMod n) ∈ (Finset.univ : Finset (Fin d → ZMod n)) :=
    Finset.mem_univ _
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin d → ZMod n)),
      0 ≤ (γ * dispersion (waveVector n i) - E)⁻¹ ^ 2 := by
    intro i _
    positivity
  have hsingle : (γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E)⁻¹ ^ 2
      ≤ ∑ m : Fin d → ZMod n, (γ * dispersion (waveVector n m) - E)⁻¹ ^ 2 :=
    Finset.single_le_sum (f := fun m : Fin d → ZMod n =>
      (γ * dispersion (waveVector n m) - E)⁻¹ ^ 2) hnonneg hmem
  have hzero : (γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E)⁻¹ ^ 2 = E⁻¹ ^ 2 := by
    have h1 : γ * dispersion (waveVector n (0 : Fin d → ZMod n)) = 0 := by
      rw [waveVector_zero, dispersion_zero, mul_zero]
    rw [h1, zero_sub, ← neg_inv, neg_sq]
  rw [hzero] at hsingle
  have hinv_pos : (0:ℝ) < ((n : ℝ) ^ d)⁻¹ := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    positivity
  calc 1 / ((n : ℝ) ^ d * E ^ 2) = ((n : ℝ) ^ d)⁻¹ * E⁻¹ ^ 2 := by
        rw [one_div, mul_inv, inv_pow]
    _ ≤ ((n : ℝ) ^ d)⁻¹ * ∑ m : Fin d → ZMod n,
          (γ * dispersion (waveVector n m) - E)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_left hsingle hinv_pos.le

/-- For positive coupling, the secular function is continuous on any set consisting entirely of
negative energies. -/
theorem continuousOn_secular {γ : ℝ} (hγ : 0 < γ) {n : ℕ} [NeZero n] {s : Set ℝ}
    (hs : ∀ E ∈ s, E < 0) : ContinuousOn (secular γ n d) s := by
  unfold secular
  refine ContinuousOn.const_mul ?_ _
  refine continuousOn_finsetSum _ ?_
  intro m _
  refine ContinuousOn.inv₀ ?_ ?_
  · exact (continuous_const.sub continuous_id).continuousOn
  · intro E hE
    have hd := dispersion_nonneg (waveVector n m)
    have ha : 0 ≤ γ * dispersion (waveVector n m) := mul_nonneg hγ.le hd
    have := hs E hE
    linarith

/-- For positive coupling and side length, there is a negative energy at which the secular
function equals one. -/
theorem exists_secular_eq_one {γ : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 0 < n) :
    ∃ E : ℝ, E < 0 ∧ secular γ n d E = 1 := by
  have hnpos : (0:ℝ) < (n : ℝ) ^ d := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    positivity
  have hN1 : (1:ℝ) ≤ (n : ℝ) ^ d := by
    have hnR : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc (1:ℝ) = 1 ^ d := by simp
      _ ≤ (n : ℝ) ^ d := by gcongr
  set N : ℝ := (n : ℝ) ^ d with hN
  have hNpos : (0:ℝ) < N := by simpa [hN] using hnpos
  set b : ℝ := -(1 / (2 * N)) with hb
  have hbneg : b < 0 := by
    have : 0 < 1 / (2 * N) := by positivity
    simp only [hb]; linarith
  have hab : (-2 : ℝ) ≤ b := by
    have h2N : (0:ℝ) < 2 * N := by positivity
    have hN1' : (1:ℝ) ≤ N := by simpa [hN] using hN1
    have : 1 / (2 * N) ≤ 2 := by
      rw [div_le_iff₀ h2N]
      nlinarith
    simp only [hb]; linarith
  have hcont : ContinuousOn (secular γ n d) (Set.Icc (-2 : ℝ) b) :=
    continuousOn_secular hγ (fun E hE => by
      have : E ≤ b := hE.2
      linarith)
  have hleft : secular γ n d (-2 : ℝ) ≤ (1:ℝ) / 2 := by
    have h := secular_le_inv (d := d) hγ hn (E := (-2:ℝ)) (by norm_num)
    rw [abs_of_neg (by norm_num : (-2:ℝ) < 0)] at h
    norm_num at h ⊢
    exact h
  have hright : 2 ≤ secular γ n d b := by
    have h := le_secular (d := d) hγ hn (E := b) hbneg
    rw [abs_of_neg hbneg] at h
    have habs : (-b)⁻¹ = 2 * N := by
      rw [hb, neg_neg]
      field_simp
    rw [habs] at h
    have hsplit : 2 * N / (n : ℝ) ^ d = 2 := by
      rw [hN, mul_div_assoc, div_self (by positivity), mul_one]
    rw [hsplit] at h
    exact h
  have hmem : (1:ℝ) ∈ Set.Icc (secular γ n d (-2)) (secular γ n d b) := by
    constructor <;> linarith
  obtain ⟨E, hE, hFE⟩ := intermediate_value_Icc hab hcont hmem
  exact ⟨E, by have := hE.2; linarith, hFE⟩

/-- For positive coupling and side length, there is exactly one negative energy at which the
secular function equals one. -/
theorem existsUnique_secular_eq_one {γ : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 0 < n) :
    ∃! E : ℝ, E < 0 ∧ secular γ n d E = 1 := by
  obtain ⟨E₀, hE₀⟩ := exists_secular_eq_one (d := d) hγ hn
  refine ⟨E₀, hE₀, ?_⟩
  intro E hE
  obtain ⟨hEneg, hFE⟩ := hE
  obtain ⟨hE₀neg, hFE₀⟩ := hE₀
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := secular_strictMonoOn (d := d) hγ hn hEneg hE₀neg hlt
    rw [hFE, hFE₀] at this
    exact lt_irrefl _ this
  · have := secular_strictMonoOn (d := d) hγ hn hE₀neg hEneg hlt
    rw [hFE, hFE₀] at this
    exact lt_irrefl _ this

end Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums
