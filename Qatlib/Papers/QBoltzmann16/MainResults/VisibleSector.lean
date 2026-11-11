/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QBoltzmann16.MainResults.BoundBasedQBM

/-!
# Visible sectors of a finite Gibbs model

The matrix `visibleInclusion` embeds the hidden space into a fixed visible-basis sector. This
module computes the compressed entries and visible projectors, proves that these projectors
resolve the identity, and normalizes their finite Gibbs probabilities in the model of
[AminEtAl2018].

The theorem `source_visible_training_bound` combines normalization with compressed-partition
probability lower bounds and the resulting weighted negative-log loss bound.

## Main statements

* `visible_projectors_sum`: the visible projectors sum to the identity.
* `visible_probability_sum`: the visible Gibbs probabilities sum to one.
* `source_visible_training_bound`: normalization and the bound-based training inequality.

## References

* [Amin et al., 2018][AminEtAl2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator
namespace Qatlib.Papers.QBoltzmann16.MainResults

/-- The basis embedding of the hidden register into the full product register with visible
coordinate fixed to `v`. -/
def visibleInclusion {M H : ℕ} (v : Fin M) : Matrix (Fin (M*H)) (Fin H) ℂ :=
  fun i j=>if i=finProdFinEquiv (v,j) then 1 else 0

/-- The visible-sector embedding is isometric: its conjugate transpose multiplied by itself is
the identity [AminEtAl2018]. -/
theorem visibleInclusion_gram {M H : ℕ} (v : Fin M) :
    (visibleInclusion (H := H) v)ᴴ*visibleInclusion (H := H) v=1 := by
  classical
  ext i j
  simp [visibleInclusion,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,eq_comm]

/-- Compressing to visible sector `v` selects the entries of the full operator whose row and
column both have visible coordinate `v` [AminEtAl2018]. -/
theorem visible_clamp_entry {M H : ℕ} (v : Fin M) (A : Operator (M*H)) (i j : Fin H) :
    clampHamiltonian (visibleInclusion (H := H) v) A i j =
      A (finProdFinEquiv (v,i)) (finProdFinEquiv (v,j)) := by
  classical
  simp [clampHamiltonian,visibleInclusion,Matrix.mul_apply,Matrix.conjTranspose_apply,ite_mul,mul_ite]

/-- The visible-sector projector has entry one exactly on diagonal positions with visible
coordinate `v`, and zero elsewhere [AminEtAl2018]. -/
theorem visible_projector_entry {M H : ℕ} (v : Fin M) (r s : Fin (M*H)) :
    (visibleInclusion (H := H) v*(visibleInclusion (H := H) v)ᴴ) r s =
      if (finProdFinEquiv.symm r).1=v ∧ r=s then 1 else 0 := by
  classical
  obtain ⟨⟨rv,rh⟩,rfl⟩ := finProdFinEquiv.surjective r
  obtain ⟨⟨sv,sh⟩,rfl⟩ := finProdFinEquiv.surjective s
  by_cases hrv : rv=v
  · subst rv
    by_cases hsv : sv=v
    · subst sv
      by_cases hh : rh=sh
      · subst sh
        simp [visibleInclusion,Matrix.mul_apply,Matrix.conjTranspose_apply]
      · simp [visibleInclusion,Matrix.mul_apply,Matrix.conjTranspose_apply,hh]
    · simp [visibleInclusion,Matrix.mul_apply,Matrix.conjTranspose_apply,hsv,Ne.symm hsv]
  · simp [visibleInclusion,Matrix.mul_apply,Matrix.conjTranspose_apply,mul_ite,hrv]

/-- The projectors onto all visible sectors sum to the full identity operator. -/
theorem visible_projectors_sum {M H : ℕ} :
    (∑v : Fin M,visibleInclusion (H := H) v*(visibleInclusion (H := H) v)ᴴ)=1 := by
  classical
  ext r s
  by_cases h : r=s
  · subst s
    simp [Matrix.sum_apply,visible_projector_entry]
  · simp [Matrix.sum_apply,visible_projector_entry,h]

/-- For a Hermitian Hamiltonian in positive full dimension, the finite Gibbs probabilities of
all visible sectors sum to one [AminEtAl2018]. -/
theorem visible_probability_sum {M H : ℕ} (A : Operator (M*H))
    (hD : 0 < M*H) (hA : A.IsHermitian) :
    (∑v : Fin M,marginalizedProbability (M*H) A (visibleInclusion (H := H) v*(visibleInclusion (H := H) v)ᴴ))=1 := by
  have hs : (∑v : Fin M,Matrix.trace ((visibleInclusion (H := H) v*(visibleInclusion (H := H) v)ᴴ)*NormedSpace.exp (-A)))=
      Matrix.trace (NormedSpace.exp (-A)) := by
    rw [← Matrix.trace_sum,← Matrix.sum_mul,visible_projectors_sum,Matrix.one_mul]
  have hr := congrArg Complex.re hs
  rw [Complex.re_sum] at hr
  unfold marginalizedProbability
  rw [← Finset.sum_div,hr]
  exact div_self (gibbsPartition_pos (M*H) A hD hA).ne'

/-- For a Hermitian Hamiltonian in positive full and hidden dimensions and nonnegative visible
data weights, the visible probabilities sum to one, each compressed partition ratio bounds
its probability from below, and these ratios give an upper bound on the weighted
negative-log loss [AminEtAl2018]. -/
theorem source_visible_training_bound {M H : ℕ} (A : Operator (M*H))
    (hD : 0 < M*H) (hH : 0 < H) (hA : A.IsHermitian)
    (data : Fin M → ℝ) (hd : ∀v,0 ≤ data v) :
    ((∑v : Fin M,marginalizedProbability (M*H) A
      (visibleInclusion (H := H) v*(visibleInclusion (H := H) v)ᴴ))=1) ∧
    ((∀v : Fin M,gibbsPartition H (clampHamiltonian (visibleInclusion (H := H) v) A)/gibbsPartition (M*H) A ≤
      marginalizedProbability (M*H) A (visibleInclusion (H := H) v*(visibleInclusion (H := H) v)ᴴ)) ∧
    -(∑v : Fin M,data v*Real.log (marginalizedProbability (M*H) A
      (visibleInclusion (H := H) v*(visibleInclusion (H := H) v)ᴴ))) ≤
      -(∑v : Fin M,data v*Real.log
        (gibbsPartition H (clampHamiltonian (visibleInclusion (H := H) v) A)/gibbsPartition (M*H) A))) :=
  ⟨visible_probability_sum A hD hA,
    source_bound_based_qbm_main hD hH A hA (visibleInclusion (H := H)) visibleInclusion_gram data hd⟩
end Qatlib.Papers.QBoltzmann16.MainResults
