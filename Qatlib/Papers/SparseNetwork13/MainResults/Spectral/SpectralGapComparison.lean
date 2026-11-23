/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseNetwork13.MainResults.Spectral.LaplacianEnergy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Variational spectral gaps of electrical networks

We prove [Wang2017Networks], Lemmas 1 and 7, using the Rayleigh domains of the
combinatorial, normalized, and augmented normalized Laplacians. Subtracting a weighted
mean transfers the test potential to the original normalized domain. The augmentation
changes the degree measure from degree to degree plus the augmentation weight and adds
a nonnegative rank-one term. The bounds concern the variational gaps of the real matrices.

Source: [arXiv:1311.1851v10](https://arxiv.org/abs/1311.1851v10).
-/

public section

noncomputable section

open Matrix

namespace Qatlib.Papers.SparseNetwork13.MainResults.Spectral

open Qatlib.Papers.SparseNetwork13.MainResults.Model

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A weighted orthogonal Rayleigh domain on at least two vertices contains a nonzero vector. -/
private theorem rayleighRange_nonempty [Nontrivial V] (A : Matrix V V ℝ)
    (w : V → ℝ) (hw : ∀ v, 0 < w v) :
    (rayleighRange A {x | ∑ v, w v * x v = 0}).Nonempty := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne V
  let x : V → ℝ := Pi.single a (w b) - Pi.single b (w a)
  have hx : x ≠ 0 := by
    intro heq
    have h := congrFun heq a
    simp [x, hab, (hw b).ne'] at h
  refine ⟨_, x, ⟨?_, hx⟩, rfl⟩
  change ∑ v, w v * x v = 0
  simp only [x, Pi.sub_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

omit [DecidableEq V] in
/-- Division by the square roots of both degree factors transfers the quadratic form. -/
private theorem normalized_quadratic (A N : Matrix V V ℝ) (d : V → ℝ)
    (hd : ∀ v, 0 < d v) (hN : ∀ u v, N u v = A u v / Real.sqrt (d u * d v))
    (x : V → ℝ) :
    x ⬝ᵥ (N *ᵥ x) =
      (fun v => x v / Real.sqrt (d v)) ⬝ᵥ (A *ᵥ (fun v => x v / Real.sqrt (d v))) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [hN, Real.sqrt_mul (hd u).le]
  field_simp [(Real.sqrt_pos.2 (hd u)).ne', (Real.sqrt_pos.2 (hd v)).ne']

/-- The original normalized Laplacian acts by the degree-scaled quadratic form. -/
private theorem normalized_laplacian_quadratic (G : ElecNetwork V E)
    (hd : ∀ v, 0 < weightedDegree G v) (x : V → ℝ) :
    x ⬝ᵥ (normalizedLaplacian G *ᵥ x) =
      (fun v => x v / Real.sqrt (weightedDegree G v)) ⬝ᵥ
        (laplacian G *ᵥ (fun v => x v / Real.sqrt (weightedDegree G v))) := by
  apply normalized_quadratic (hd := hd)
  intro u v
  simp [normalizedLaplacian, hd]

omit [DecidableEq V] in
/-- The squared coordinate dot product is the squared Euclidean norm. -/
private theorem dotProduct_self_eq_norm_sq (x : V → ℝ) :
    x ⬝ᵥ x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ V)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, pow_two]

omit [DecidableEq V] in
/-- The Euclidean Rayleigh denominator is strictly positive for every nonzero vector. -/
private theorem dotProduct_self_pos {x : V → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  rw [dotProduct_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr (by simpa using hx)) _

/-- All original normalized Laplacian Rayleigh quotients are nonnegative. -/
private theorem normalized_rayleigh_nonneg (G : ElecNetwork V E)
    (hd : ∀ v, 0 < weightedDegree G v) (x : V → ℝ) :
    0 ≤ rayleigh (normalizedLaplacian G) x := by
  unfold rayleigh
  rw [normalized_laplacian_quadratic G hd, laplacian_quadratic_eq,
    dotProduct_self_eq_norm_sq]
  exact div_nonneg (Finset.sum_nonneg fun e _ =>
    mul_nonneg (G.w_pos e).le (sq_nonneg _)) (sq_nonneg _)

/-- The original normalized gap bounds the quadratic form on degree-centered potentials. -/
private theorem normalized_gap_mul_weighted_sq_le (G : ElecNetwork V E)
    (hd : ∀ v, 0 < weightedDegree G v) (x : V → ℝ)
    (hx : ∑ v, weightedDegree G v * x v = 0) :
    lambda2Normalized G * (∑ v, weightedDegree G v * x v ^ 2) ≤
      x ⬝ᵥ (laplacian G *ᵥ x) := by
  by_cases hz : x = 0
  · simp [hz]
  let y : V → ℝ := fun v => Real.sqrt (weightedDegree G v) * x v
  have hy : y ≠ 0 := by
    intro hy
    apply hz
    funext v
    have hv := congrFun hy v
    exact (mul_eq_zero.mp hv).resolve_left (Real.sqrt_pos.2 (hd v)).ne'
  have horth : y ∈ degreeOrthogonal G := by
    change ∑ v, Real.sqrt (weightedDegree G v) * y v = 0
    simpa only [y, ← mul_assoc, ← pow_two, Real.sq_sqrt (hd _).le] using hx
  have hbound : BddBelow (rayleighRange (normalizedLaplacian G) (degreeOrthogonal G)) :=
    ⟨0, by rintro _ ⟨z, _, rfl⟩; exact normalized_rayleigh_nonneg G hd z⟩
  have hgap := csInf_le hbound (show rayleigh (normalizedLaplacian G) y ∈
      rayleighRange (normalizedLaplacian G) (degreeOrthogonal G) from
    ⟨y, ⟨horth, hy⟩, rfl⟩)
  change lambda2Normalized G ≤ rayleigh (normalizedLaplacian G) y at hgap
  unfold rayleigh at hgap
  rw [le_div_iff₀ (dotProduct_self_pos hy), normalized_laplacian_quadratic G hd] at hgap
  have hscale : (fun v => y v / Real.sqrt (weightedDegree G v)) = x := by
    funext v
    dsimp [y]
    rw [mul_comm, mul_div_cancel_right₀ _ (Real.sqrt_pos.2 (hd v)).ne']
  have hden : y ⬝ᵥ y = ∑ v, weightedDegree G v * x v ^ 2 := by
    apply Finset.sum_congr rfl
    intro v _
    change (Real.sqrt (weightedDegree G v) * x v) *
        (Real.sqrt (weightedDegree G v) * x v) = _
    rw [← pow_two, mul_pow, Real.sq_sqrt (hd v).le]
  rwa [hscale, hden] at hgap

/-- Changing from degree to a dominated positive vertex measure preserves a scaled gap. -/
private theorem gap_mul_weighted_sq_le [Nonempty V] (G : ElecNetwork V E)
    (hd : ∀ v, 0 < weightedDegree G v) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    {K g : ℝ} (hK : 0 < K) (hg : 0 ≤ g) (hgap : g ≤ lambda2Normalized G)
    (hdom : ∀ v, w v ≤ K * weightedDegree G v) (x : V → ℝ)
    (hx : ∑ v, w v * x v = 0) :
    (g / K) * (∑ v, w v * x v ^ 2) ≤ x ⬝ᵥ (laplacian G *ᵥ x) := by
  let mass : ℝ := ∑ v, weightedDegree G v
  have hm : 0 < mass := Finset.sum_pos (fun v _ => hd v) Finset.univ_nonempty
  let c : ℝ := (∑ v, weightedDegree G v * x v) / mass
  let y : V → ℝ := fun v => x v - c
  have hcenter : ∑ v, weightedDegree G v * y v = 0 := by
    simp only [y, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← show
      mass = ∑ v, weightedDegree G v from rfl, c]
    rw [mul_comm mass, div_mul_cancel₀ _ hm.ne', sub_self]
  have hvar : (∑ v, w v * x v ^ 2) ≤ ∑ v, w v * y v ^ 2 := by
    have hidentity : (∑ v, w v * y v ^ 2) =
        (∑ v, w v * x v ^ 2) - 2 * c * (∑ v, w v * x v) +
          c ^ 2 * (∑ v, w v) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => by dsimp [y]; ring
    rw [hidentity, hx, mul_zero, sub_zero]
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun v _ => (hw v).le))
  have hdom' : (∑ v, w v * y v ^ 2) ≤ K * ∑ v, weightedDegree G v * y v ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hdom v) (sq_nonneg _)
  calc
    _ ≤ (g / K) * (K * ∑ v, weightedDegree G v * y v ^ 2) :=
      mul_le_mul_of_nonneg_left (hvar.trans hdom') (div_nonneg hg hK.le)
    _ = g * (∑ v, weightedDegree G v * y v ^ 2) := by field_simp
    _ ≤ lambda2Normalized G * (∑ v, weightedDegree G v * y v ^ 2) :=
      mul_le_mul_of_nonneg_right hgap (Finset.sum_nonneg fun v _ =>
        mul_nonneg (hd v).le (sq_nonneg _))
    _ ≤ y ⬝ᵥ (laplacian G *ᵥ y) := normalized_gap_mul_weighted_sq_le G hd y hcenter
    _ = _ := laplacian_quadratic_sub_const G x c

/-- With all weighted degrees at least one, the normalized gap is no larger than the
combinatorial gap, as in [Wang2017Networks], Lemma 1. -/
theorem normalized_gap_le_combinatorial_gap [Nontrivial V] (G : ElecNetwork V E)
    (hdeg : ∀ v, 1 ≤ weightedDegree G v) : lambda2Normalized G ≤ lambda2 G := by
  have hd : ∀ v, 0 < weightedDegree G v := fun v => zero_lt_one.trans_le (hdeg v)
  have hgap : 0 ≤ lambda2Normalized G := by
    apply le_csInf (rayleighRange_nonempty _ _ fun v => Real.sqrt_pos.2 (hd v))
    rintro _ ⟨x, _, rfl⟩
    exact normalized_rayleigh_nonneg G hd x
  apply le_csInf (by simpa [constantOrthogonal] using
    rayleighRange_nonempty (laplacian G) (fun _ => 1) (fun _ => zero_lt_one))
  rintro _ ⟨x, ⟨hx, hne⟩, rfl⟩
  have hx' : ∑ v, x v = 0 := hx
  have hne' : x ≠ 0 := hne
  rw [rayleigh, le_div_iff₀ (dotProduct_self_pos hne')]
  simpa [dotProduct, pow_two] using gap_mul_weighted_sq_le G hd (fun _ => 1)
    (fun _ => zero_lt_one) (K := 1) zero_lt_one hgap le_rfl
    (fun v => by simpa using hdeg v) x (by simpa using hx')

omit [DecidableEq E] in
/-- The weighted degree counts each squared potential once for each incident edge. -/
private theorem sum_degree_mul_sq (G : ElecNetwork V E) (x : V → ℝ) :
    ∑ v, weightedDegree G v * x v ^ 2 =
      ∑ e, G.w e * (x (G.tail e) ^ 2 + x (G.head e) ^ 2) := by
  simp only [weightedDegree, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hsplit (v : V) :
      (if v = G.tail e ∨ v = G.head e then G.w e else 0) =
        (if v = G.tail e then G.w e else 0) + (if v = G.head e then G.w e else 0) := by
    by_cases ht : v = G.tail e
    · subst v
      simp [(G.nonloop e).symm]
    · simp [ht]
  simp only [hsplit, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, mul_add]

/-- The normalized Laplacian gap is at most two, as in [Wang2017Networks], Equation (13).
Each squared edge difference is bounded by twice the sum of the endpoint squares. -/
theorem normalized_gap_le_two [Nontrivial V] (G : ElecNetwork V E)
    (hd : ∀ v, 0 < weightedDegree G v) : lambda2Normalized G ≤ 2 := by
  obtain ⟨_, x, ⟨_, hx⟩, rfl⟩ :=
    rayleighRange_nonempty (normalizedLaplacian G) _ (fun v => Real.sqrt_pos.2 (hd v))
  have hbdd : BddBelow (rayleighRange (normalizedLaplacian G) (degreeOrthogonal G)) :=
    ⟨0, by rintro _ ⟨y, _, rfl⟩; exact normalized_rayleigh_nonneg G hd y⟩
  refine (csInf_le hbdd ⟨x, ⟨?_, hx⟩, rfl⟩).trans ?_
  · assumption
  · have hne : x ≠ 0 := hx
    rw [rayleigh, div_le_iff₀ (dotProduct_self_pos hne), normalized_laplacian_quadratic G hd,
      laplacian_quadratic_eq]
    let y : V → ℝ := fun v => x v / Real.sqrt (weightedDegree G v)
    have hden : x ⬝ᵥ x = ∑ v, weightedDegree G v * y v ^ 2 := by
      apply Finset.sum_congr rfl
      intro v _
      change x v * x v = weightedDegree G v * (x v / Real.sqrt (weightedDegree G v)) ^ 2
      rw [← pow_two, div_pow, Real.sq_sqrt (hd v).le, mul_comm, div_mul_cancel₀ _ (hd v).ne']
    rw [hden, sum_degree_mul_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (y (G.tail e) + y (G.head e))])
      (G.w_pos e).le

/-- With weighted degrees at least one, the augmented normalized gap is at least
`lam / (1 + lam)` whenever `lam > 0` is a lower bound on the original normalized gap. -/
theorem augmented_normalized_gap_bound [Nontrivial V] (G : ElecNetwork V E)
    (hdeg : ∀ v, 1 ≤ weightedDegree G v) {lam : ℝ} (hlam : 0 < lam)
    (hgap : lam ≤ lambda2Normalized G) (current : EuclideanSpace ℝ V) :
    lam / (1 + lam) ≤ lambda2NormalizedMod G lam current.ofLp := by
  have hd : ∀ v, 0 < weightedDegree G v := fun v => zero_lt_one.trans_le (hdeg v)
  let w : V → ℝ := weightedDegreeMod G lam
  have hw : ∀ v, 0 < w v := fun v => add_pos (hd v) hlam
  apply le_csInf (rayleighRange_nonempty _ _ fun v => Real.sqrt_pos.2 (hw v))
  rintro _ ⟨z, ⟨hz, hne⟩, rfl⟩
  have hne' : z ≠ 0 := hne
  rw [rayleigh, le_div_iff₀ (dotProduct_self_pos hne')]
  let x : V → ℝ := fun v => z v / Real.sqrt (w v)
  have horth : ∑ v, w v * x v = 0 := by
    have hz' : ∑ v, Real.sqrt (w v) * z v = 0 := hz
    rw [← hz']
    refine Finset.sum_congr rfl fun v _ => ?_
    calc
      w v * x v = (Real.sqrt (w v)) ^ 2 * (z v / Real.sqrt (w v)) := by
        rw [Real.sq_sqrt (hw v).le]
      _ = Real.sqrt (w v) * z v := by
        field_simp [(Real.sqrt_pos.2 (hw v)).ne']
  have hden : z ⬝ᵥ z = ∑ v, w v * x v ^ 2 := by
    apply Finset.sum_congr rfl
    intro v _
    change z v * z v = w v * (z v / Real.sqrt (w v)) ^ 2
    rw [← pow_two, div_pow, Real.sq_sqrt (hw v).le, mul_comm, div_mul_cancel₀ _ (hw v).ne']
  have hquad : z ⬝ᵥ (normalizedModifiedLaplacian G lam current.ofLp *ᵥ z) =
      x ⬝ᵥ (modifiedLaplacian G lam current.ofLp *ᵥ x) := by
    apply normalized_quadratic (hd := hw)
    intro u v
    simp [normalizedModifiedLaplacian, w, show ∀ v, 0 < weightedDegreeMod G lam v from hw]
  have hdom (v : V) : w v ≤ (1 + lam) * weightedDegree G v := by
    change weightedDegree G v + lam ≤ (1 + lam) * weightedDegree G v
    linarith [mul_le_mul_of_nonneg_left (hdeg v) hlam.le]
  rw [hden, hquad, modified_laplacian_quadratic_eq]
  exact (gap_mul_weighted_sq_le G hd w hw (add_pos zero_lt_one hlam) hlam.le hgap hdom x horth).trans
    (le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _)))

/-- The augmented normalized gap is at least one third of the promised original gap,
as in [Wang2017Networks], Lemma 7. The constant is uniform in the size of the network and
in the external current. -/
theorem augmented_normalized_gap_ge_third [Nontrivial V] (G : ElecNetwork V E)
    (hdeg : ∀ v, 1 ≤ weightedDegree G v) {lam : ℝ} (hlam : 0 < lam)
    (hgap : lam ≤ lambda2Normalized G) (current : EuclideanSpace ℝ V) :
    lam / 3 ≤ lambda2NormalizedMod G lam current.ofLp := by
  have htwo := hgap.trans (normalized_gap_le_two G fun v => zero_lt_one.trans_le (hdeg v))
  exact (div_le_div_of_nonneg_left hlam.le (add_pos zero_lt_one hlam)
    (by linarith)).trans (augmented_normalized_gap_bound G hdeg hlam hgap current)

/-- The square-root augmented degree vector is a nonzero null vector for balanced external
current, as in [Wang2017Networks], Equation (92). -/
theorem augmented_normalized_degree_null [Nonempty V] (G : ElecNetwork V E) (lam : ℝ)
    (hw : ∀ v, 0 < weightedDegreeMod G lam v) (current : EuclideanSpace ℝ V)
    (hbalance : ∑ v, current v = 0) :
    let q : V → ℝ := fun v => Real.sqrt (weightedDegreeMod G lam v)
    q ≠ 0 ∧ normalizedModifiedLaplacian G lam current.ofLp *ᵥ q = 0 := by
  dsimp
  constructor
  · intro h
    obtain ⟨v⟩ := ‹Nonempty V›
    exact (Real.sqrt_pos.2 (hw v)).ne' (congrFun h v)
  · funext u
    have hzero := modified_laplacian_mulVec_one G lam current.ofLp hbalance
    calc
      _ = (modifiedLaplacian G lam current.ofLp *ᵥ (fun _ => 1)) u /
          Real.sqrt (weightedDegreeMod G lam u) := by
        simp only [mulVec, dotProduct, normalizedModifiedLaplacian, hw, and_self, ite_true, mul_one,
          Finset.sum_div]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Real.sqrt_mul (hw u).le]
        field_simp [(Real.sqrt_pos.2 (hw u)).ne', (Real.sqrt_pos.2 (hw v)).ne']
      _ = 0 := by simp [hzero]

end Qatlib.Papers.SparseNetwork13.MainResults.Spectral
