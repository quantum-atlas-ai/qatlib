/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Qatlib.Papers.CommuteTest05.WalkDetect.CosineAverage

@[expose] public section

/-!
# The averaged rotation deviation of Claim 13

[Itakura2005], Claim 13 decomposes a normalized walk state into orthogonal rotation planes of
angles `2 * θ j` and bounds the time average of `‖W ^ t φ - φ‖ ^ 2`. This module gives an
explicit real Euclidean model of the walk on the two coordinates of each plane:

* `planeRotationFun` is the block-diagonal rotation whose block at `j` is the matrix
  `[[cos (2θ j), -sin (2θ j)], [sin (2θ j), cos (2θ j)]]`;
* `rotationState ν` is `∑ j, ν j • z j` on the `false` coordinates.

The deviation norm is proved to be exactly
`∑ j, 2 * ν j ^ 2 * (1 - cos (2 * θ j * t))`, so averaging over `t` and invoking the cosine
estimate of `cosine_average_bound` yields the paper's average lower bound `48 / 25` whenever
`T ≥ 100 * ∑ j, ν j ^ 2 / θ j`. Multiplication by the Hadamard-test factor `1 / 4` gives
the normalized probability bound `12 / 25`. Scaling the state by `√(1 - ε)` gives the
factor `1 - ε` in the probability bound of [Itakura2005], Theorem 15.

The rotation-plane action is assumed as the source's Definition 11 contract: this module does
not reconstruct `W` from the two row reflections, and it does not prove the spectral derivation
of the angle decomposition.

## Main statements

* `planeRotationFun_isometry`: the plane rotation preserves the Euclidean norm.
* `rotation_deviation_norm_sq`: the exact deviation identity for a single time.
* `averaged_rotation_deviation_ge`: the averaged deviation is at least `48 / 25`.
* `exists_uniform_rotation_deviation_constant`: the constant `48 / 25` is uniform outside all
  instance data.
* `averaged_rotation_deviation_scale`: scaling the coefficients by `√(1 - ε)` multiplies the
  averaged deviation by `1 - ε`.
* `averaged_detection_probability_ge`: the normalized averaged Hadamard-test flag probability
  is at least `12 / 25`.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.CommuteTest05.WalkDetect

variable {κ : Type*}

/-- The block-diagonal rotation of a family of invariant planes. The `false` coordinate of an
index `j` carries the first basis vector and the `true` coordinate carries the second; the block
at `j` rotates by the angle `2 * θ j`. -/
def planeRotationFun (θ : κ → ℝ) (x : EuclideanSpace ℝ (κ × Bool)) :
    EuclideanSpace ℝ (κ × Bool) :=
  WithLp.toLp 2 fun p : κ × Bool =>
    if p.2 then
      Real.sin (2 * θ p.1) * x (p.1, false) + Real.cos (2 * θ p.1) * x (p.1, true)
    else
      Real.cos (2 * θ p.1) * x (p.1, false) - Real.sin (2 * θ p.1) * x (p.1, true)

/-- The normalized walk state `∑ j, ν j • z j`, with `z j` the first basis vector of the `j`-th
rotation plane. Normalization is expressed separately as `∑ j, ν j ^ 2 = 1`. -/
def rotationState (ν : κ → ℝ) : EuclideanSpace ℝ (κ × Bool) :=
  WithLp.toLp 2 fun p : κ × Bool => if p.2 then 0 else ν p.1

/-- Coordinate formula for the block-diagonal plane rotation. -/
@[simp]
theorem planeRotationFun_apply (θ : κ → ℝ) (x : EuclideanSpace ℝ (κ × Bool))
    (p : κ × Bool) :
    planeRotationFun θ x p =
      if p.2 then
        Real.sin (2 * θ p.1) * x (p.1, false) + Real.cos (2 * θ p.1) * x (p.1, true)
      else
        Real.cos (2 * θ p.1) * x (p.1, false) - Real.sin (2 * θ p.1) * x (p.1, true) :=
  rfl

/-- Coordinate formula for the initial walk state: only the `false` coordinates are nonzero. -/
@[simp]
theorem rotationState_apply (ν : κ → ℝ) (p : κ × Bool) :
    rotationState ν p = if p.2 then 0 else ν p.1 :=
  rfl

/-- A single plane rotation preserves the Euclidean norm: the two coordinates of each index are
transformed by an orthogonal `2 × 2` matrix. -/
theorem planeRotationFun_isometry [Fintype κ] (θ : κ → ℝ)
    (x : EuclideanSpace ℝ (κ × Bool)) :
    ‖planeRotationFun θ x‖ = ‖x‖ := by
  have hsq : ‖planeRotationFun θ x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.univ_bool, Finset.sum_pair (by decide : true ≠ false),
      Finset.sum_pair (by decide : true ≠ false)]
    simp only [planeRotationFun_apply, Bool.false_eq_true, ite_false, ite_true]
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ j)]
  have hnonneg : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith [norm_nonneg (planeRotationFun θ x)]

/-- The `t`-th iterate of the plane rotation sends the first basis vector of plane `j` to
`cos (2 θ j t) z j + sin (2 θ j t) w j`: both coordinates are recorded together because the
induction step mixes them. -/
theorem planeRotationFun_iterate_pair (θ : κ → ℝ) (ν : κ → ℝ) (t : ℕ) (j : κ) :
    ((planeRotationFun θ)^[t] (rotationState ν)) (j, false) =
        ν j * Real.cos (2 * θ j * (t : ℝ)) ∧
      ((planeRotationFun θ)^[t] (rotationState ν)) (j, true) =
        ν j * Real.sin (2 * θ j * (t : ℝ)) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      have hangle : 2 * θ j * ((t : ℝ) + 1) = 2 * θ j * (t : ℝ) + 2 * θ j := by ring
      constructor
      · rw [planeRotationFun_apply]
        simp only [ite_false, Bool.false_eq_true, ih.1, ih.2]
        rw [show ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 by push_cast; ring, hangle,
          Real.cos_add]
        ring
      · rw [planeRotationFun_apply]
        simp only [ite_true, ih.1, ih.2]
        rw [show ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 by push_cast; ring, hangle,
          Real.sin_add]
        ring

/-- The first coordinate of the `t`-th rotated state. -/
theorem planeRotationFun_iterate_false (θ : κ → ℝ) (ν : κ → ℝ) (t : ℕ) (j : κ) :
    ((planeRotationFun θ)^[t] (rotationState ν)) (j, false) =
      ν j * Real.cos (2 * θ j * (t : ℝ)) :=
  (planeRotationFun_iterate_pair θ ν t j).1

/-- The second coordinate of the `t`-th rotated state. -/
theorem planeRotationFun_iterate_true (θ : κ → ℝ) (ν : κ → ℝ) (t : ℕ) (j : κ) :
    ((planeRotationFun θ)^[t] (rotationState ν)) (j, true) =
      ν j * Real.sin (2 * θ j * (t : ℝ)) :=
  (planeRotationFun_iterate_pair θ ν t j).2

/-- The exact deviation identity of [Itakura2005], Claim 13: the squared distance of the `t`-th
rotated state from the initial state is the sum over planes of `2 ν j ^ 2 (1 - cos (2 θ j t))`. -/
theorem rotation_deviation_norm_sq [Fintype κ] (θ : κ → ℝ) (ν : κ → ℝ) (t : ℕ) :
    ‖(planeRotationFun θ)^[t] (rotationState ν) - rotationState ν‖ ^ 2 =
      ∑ j, 2 * ν j ^ 2 * (1 - Real.cos (2 * θ j * (t : ℝ))) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.univ_bool, Finset.sum_pair (by decide : true ≠ false)]
  have hfalse : (((planeRotationFun θ)^[t] (rotationState ν) - rotationState ν) (j, false)) =
      ν j * (Real.cos (2 * θ j * (t : ℝ)) - 1) := by
    simp only [PiLp.sub_apply, planeRotationFun_iterate_false, rotationState_apply,
      Bool.false_eq_true, ite_false]
    ring
  have htrue : (((planeRotationFun θ)^[t] (rotationState ν) - rotationState ν) (j, true)) =
      ν j * Real.sin (2 * θ j * (t : ℝ)) := by
    simp only [PiLp.sub_apply, planeRotationFun_iterate_true, rotationState_apply, ite_true,
      sub_zero]
  rw [hfalse, htrue]
  nlinarith [Real.sin_sq_add_cos_sq (2 * θ j * (t : ℝ))]

/-- The averaged version of `rotation_deviation_norm_sq`, separating the average cosine. -/
private theorem averaged_rotation_deviation_eq [Fintype κ] (θ : κ → ℝ) (ν : κ → ℝ) (T : ℕ) :
    (1 / (((T + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (T + 1),
          ‖(planeRotationFun θ)^[t] (rotationState ν) - rotationState ν‖ ^ 2) =
      ∑ j, 2 * ν j ^ 2 *
        (1 - (1 / (((T + 1 : ℕ) : ℝ))) *
          (∑ t ∈ Finset.range (T + 1), Real.cos (2 * θ j * (t : ℝ)))) := by
  have hN : ((0 : ℝ) < ((T + 1 : ℕ) : ℝ)) := by positivity
  rw [Finset.sum_congr rfl fun t _ => rotation_deviation_norm_sq θ ν t]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (1 / (((T + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (T + 1),
          2 * ν j ^ 2 * (1 - Real.cos (2 * θ j * (t : ℝ)))) =
      ∑ t ∈ Finset.range (T + 1),
        2 * ν j ^ 2 * ((1 / (((T + 1 : ℕ) : ℝ))) *
          (1 - Real.cos (2 * θ j * (t : ℝ)))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [h1, ← Finset.mul_sum]
  have hcos : (∑ t ∈ Finset.range (T + 1),
        (1 / (((T + 1 : ℕ) : ℝ))) * (1 - Real.cos (2 * θ j * (t : ℝ)))) =
      1 - (1 / (((T + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (T + 1), Real.cos (2 * θ j * (t : ℝ))) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [hcos]

/-- The sum of the squared coefficients is one in the normalized case, and the squared
coefficients are nonnegative. -/
private theorem weighted_inverse_bound [Fintype κ] (ν θ : κ → ℝ) (T : ℕ)
    (hθ0 : ∀ j, 0 < θ j) (hν : ∑ j, ν j ^ 2 = 1)
    (hT : 100 * (∑ j, ν j ^ 2 / θ j) ≤ (T : ℝ)) :
    (8 : ℝ) * (∑ j, ν j ^ 2 / θ j) / (((T + 1 : ℕ) : ℝ)) ≤ 2 / 25 := by
  have hSpos : 0 < ∑ j, ν j ^ 2 / θ j := by
    have hsumpos : (0 : ℝ) < ∑ j, ν j ^ 2 := by rw [hν]; norm_num
    have hex : ∃ j ∈ Finset.univ, 0 < ν j ^ 2 := by
      by_contra h
      have h0 : ∀ j, ν j ^ 2 = 0 := by
        intro j
        refine le_antisymm ?_ (sq_nonneg _)
        by_contra hlt
        exact h ⟨j, Finset.mem_univ j, lt_of_not_ge hlt⟩
      have hzero : ∑ j, ν j ^ 2 = 0 := Finset.sum_eq_zero fun j _ => h0 j
      rw [hν] at hzero
      norm_num at hzero
    obtain ⟨j, hjmem, hjpos⟩ := hex
    refine Finset.sum_pos' (fun i _ => ?_) ⟨j, hjmem, ?_⟩
    · exact div_nonneg (sq_nonneg _) (le_of_lt (hθ0 i))
    · exact div_pos hjpos (hθ0 j)
  have hN : ((0 : ℝ) < ((T + 1 : ℕ) : ℝ)) := by positivity
  have hT' : 100 * (∑ j, ν j ^ 2 / θ j) ≤ ((T + 1 : ℕ) : ℝ) := by
    have : (T : ℝ) ≤ ((T + 1 : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hnum : (0 : ℝ) ≤ 8 * (∑ j, ν j ^ 2 / θ j) :=
    mul_nonneg (by norm_num) hSpos.le
  have hden : 100 * (∑ j, ν j ^ 2 / θ j) ≤ ((T + 1 : ℕ) : ℝ) := hT'
  have hstep : (8 * (∑ j, ν j ^ 2 / θ j)) / (((T + 1 : ℕ) : ℝ)) ≤
      (8 * (∑ j, ν j ^ 2 / θ j)) / (100 * (∑ j, ν j ^ 2 / θ j)) := by
    exact div_le_div_of_nonneg_left hnum (mul_pos (by norm_num) hSpos) hden
  have hcancel : (8 * (∑ j, ν j ^ 2 / θ j)) / (100 * (∑ j, ν j ^ 2 / θ j)) =
      (8 : ℝ) / 100 := by
    field_simp [hSpos.ne']
  rw [hcancel] at hstep
  have hfin : (8 : ℝ) / 100 = 2 / 25 := by norm_num
  rwa [hfin] at hstep

/-- [Itakura2005], Claim 13: for `0 < θ j ≤ π / 2` and normalized coefficients, every
`T ≥ 100 * ∑ j, ν j ^ 2 / θ j` satisfies the averaged deviation lower bound `48 / 25`. -/
theorem averaged_rotation_deviation_ge [Fintype κ] [Nonempty κ] (ν θ : κ → ℝ) (T : ℕ)
    (hθ0 : ∀ j, 0 < θ j) (hθπ : ∀ j, θ j ≤ Real.pi / 2)
    (hν : ∑ j, ν j ^ 2 = 1)
    (hT : 100 * (∑ j, ν j ^ 2 / θ j) ≤ (T : ℝ)) :
    (48 : ℝ) / 25 ≤
      (1 / (((T + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (T + 1),
          ‖(planeRotationFun θ)^[t] (rotationState ν) - rotationState ν‖ ^ 2) := by
  rw [averaged_rotation_deviation_eq]
  have hN : ((0 : ℝ) < ((T + 1 : ℕ) : ℝ)) := by positivity
  have hcos : ∀ j, (1 / (((T + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (T + 1), Real.cos (2 * θ j * (t : ℝ))) ≤
      4 / (((T + 1 : ℕ) : ℝ) * θ j) := by
    intro j
    exact cosine_average_bound (θ j) (hθ0 j) (hθπ j) T
  have hterm : ∀ j, 2 * ν j ^ 2 *
        (1 - (1 / (((T + 1 : ℕ) : ℝ))) *
          (∑ t ∈ Finset.range (T + 1), Real.cos (2 * θ j * (t : ℝ)))) ≥
      2 * ν j ^ 2 - 8 * ν j ^ 2 / (((T + 1 : ℕ) : ℝ) * θ j) := by
    intro j
    have hsq : (0 : ℝ) ≤ ν j ^ 2 := sq_nonneg _
    have h := mul_le_mul_of_nonneg_left (hcos j) (by positivity : (0 : ℝ) ≤ 2 * ν j ^ 2)
    have heq : 2 * ν j ^ 2 * (4 / (((T + 1 : ℕ) : ℝ) * θ j)) =
        8 * ν j ^ 2 / (((T + 1 : ℕ) : ℝ) * θ j) := by
      ring
    nlinarith
  have hsum : (∑ j, 2 * ν j ^ 2 *
        (1 - (1 / (((T + 1 : ℕ) : ℝ))) *
          (∑ t ∈ Finset.range (T + 1), Real.cos (2 * θ j * (t : ℝ))))) ≥
      ∑ j, (2 * ν j ^ 2 - 8 * ν j ^ 2 / (((T + 1 : ℕ) : ℝ) * θ j)) :=
    Finset.sum_le_sum fun j _ => hterm j
  have hId : (∑ j, (2 * ν j ^ 2 - 8 * ν j ^ 2 / (((T + 1 : ℕ) : ℝ) * θ j))) =
      2 * (∑ j, ν j ^ 2) - 8 * (∑ j, ν j ^ 2 / θ j) / (((T + 1 : ℕ) : ℝ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hsecond : (∑ j, 8 * ν j ^ 2 / (((T + 1 : ℕ) : ℝ) * θ j)) =
        8 * (∑ j, ν j ^ 2 / θ j) / (((T + 1 : ℕ) : ℝ)) := by
      calc (∑ j, 8 * ν j ^ 2 / (((T + 1 : ℕ) : ℝ) * θ j))
          = ∑ j, (8 / ((T + 1 : ℕ) : ℝ)) * (ν j ^ 2 / θ j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = (8 / ((T + 1 : ℕ) : ℝ)) * (∑ j, ν j ^ 2 / θ j) := by
            rw [Finset.mul_sum]
        _ = 8 * (∑ j, ν j ^ 2 / θ j) / ((T + 1 : ℕ) : ℝ) := by
            ring
    rw [hsecond]
  rw [hId, hν] at hsum
  have hw := weighted_inverse_bound ν θ T hθ0 hν hT
  linarith

/-- The uniform form of `averaged_rotation_deviation_ge`: a single positive constant
`48 / 25` works for every nonempty finite family of planes and every admissible time horizon,
with the constant outside all quantifiers. -/
theorem exists_uniform_rotation_deviation_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (κ : Type) [Fintype κ] [Nonempty κ] (ν θ : κ → ℝ) (T : ℕ),
        (∀ j, 0 < θ j) → (∀ j, θ j ≤ Real.pi / 2) →
        (∑ j, ν j ^ 2 = 1) → 100 * (∑ j, ν j ^ 2 / θ j) ≤ (T : ℝ) →
        C ≤ (1 / (((T + 1 : ℕ) : ℝ))) *
          (∑ t ∈ Finset.range (T + 1),
            ‖(planeRotationFun θ)^[t] (rotationState ν) - rotationState ν‖ ^ 2) := by
  refine ⟨48 / 25, by norm_num, ?_⟩
  intro κ _ _ ν θ T hθ0 hθπ hν hT
  exact averaged_rotation_deviation_ge ν θ T hθ0 hθπ hν hT

/-- [Itakura2005], Claim 13, scaling sentence: replacing `ν` by `√(1 - ε) • ν` multiplies the
averaged deviation by `1 - ε`. -/
theorem averaged_rotation_deviation_scale [Fintype κ] (ν θ : κ → ℝ) (T : ℕ) {ε : ℝ}
    (_hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 / (((T + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (T + 1),
          ‖(planeRotationFun θ)^[t] (rotationState (Real.sqrt (1 - ε) • ν)) -
            rotationState (Real.sqrt (1 - ε) • ν)‖ ^ 2) =
      (1 - ε) * ((1 / (((T + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (T + 1),
          ‖(planeRotationFun θ)^[t] (rotationState ν) - rotationState ν‖ ^ 2)) := by
  rw [averaged_rotation_deviation_eq, averaged_rotation_deviation_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hnonneg : 0 ≤ 1 - ε := by linarith
  have hsqrt : Real.sqrt (1 - ε) ^ 2 = 1 - ε := Real.sq_sqrt hnonneg
  have hcoef : (Real.sqrt (1 - ε) • ν) j = Real.sqrt (1 - ε) * ν j := rfl
  rw [hcoef]
  have hsq : (Real.sqrt (1 - ε) * ν j) ^ 2 = (1 - ε) * ν j ^ 2 := by
    rw [mul_pow, hsqrt]
  rw [hsq]
  ring

/-- In the normalized rotation-plane model of [Itakura2005], Theorem 15, the average
Hadamard-test flag probability over `t < T + 1` is at least `12 / 25` above the Claim 13
threshold. The separate scaling identity supplies the factor `1 - ε` for the paper's state. -/
theorem averaged_detection_probability_ge [Fintype κ] [Nonempty κ] (ν θ : κ → ℝ) (T : ℕ)
    (hθ0 : ∀ j, 0 < θ j) (hθπ : ∀ j, θ j ≤ Real.pi / 2)
    (hν : ∑ j, ν j ^ 2 = 1)
    (hT : 100 * (∑ j, ν j ^ 2 / θ j) ≤ (T : ℝ)) :
    (12 : ℝ) / 25 ≤
      (1 / (((T + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (T + 1),
          (1 / 4) *
            ‖(planeRotationFun θ)^[t] (rotationState ν) - rotationState ν‖ ^ 2) := by
  have hmain := averaged_rotation_deviation_ge ν θ T hθ0 hθπ hν hT
  have hN : ((0 : ℝ) < ((T + 1 : ℕ) : ℝ)) := by positivity
  rw [← Finset.mul_sum]
  have hfactor : (1 / (((T + 1 : ℕ) : ℝ))) *
        ((1 / 4) *
          (∑ t ∈ Finset.range (T + 1),
            ‖(planeRotationFun θ)^[t] (rotationState ν) - rotationState ν‖ ^ 2)) =
      (1 / 4) * ((1 / (((T + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (T + 1),
          ‖(planeRotationFun θ)^[t] (rotationState ν) - rotationState ν‖ ^ 2)) := by
    ring
  rw [hfactor]
  nlinarith

end Qatlib.Papers.CommuteTest05.WalkDetect
