/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.ProjectorOrderStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.Phase


open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QlsReadoutSpec.Amplification

namespace Qatlib.Concepts.QlsReadoutSpec.Amplification

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators ComplexOrder

private theorem star_mul_self_coe (z : ℂ) :
    star z * z = (((‖z‖ ^ 2 : ℝ) : ℂ)) := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  have h : Complex.normSq z = ‖z‖ ^ 2 :=
    (Complex.norm_mul_self_eq_normSq z).symm.trans (pow_two ‖z‖).symm
  rw [h]

private theorem normVec_sq {H : Type} [Fintype H] (v : H → ℂ) :
    normVec v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  show ‖toEuclidean_fromVec v‖ ^ 2 = _
  exact norm_toEuclidean_fromVec_sq v

private theorem star_dotProduct_self {H : Type} [Fintype H] (u : H → ℂ) :
    star u ⬝ᵥ u = (((normVec u) ^ 2 : ℝ) : ℂ) := by
  have hpt : ∀ i : H, star (u i) * (u i) = (((‖u i‖ ^ 2 : ℝ) : ℂ)) := fun i =>
    star_mul_self_coe (u i)
  rw [show star u ⬝ᵥ u = ∑ i, (star u) i * u i from rfl]
  simp only [Pi.star_apply]
  rw [Finset.sum_congr rfl fun i _ => hpt i, ← Complex.ofReal_sum, normVec_sq]

private theorem quad_symm {H : Type} [Fintype H] {R : Matrix H H ℂ} (hR : Rᴴ = R)
    (a b : H → ℂ) : star a ⬝ᵥ (R *ᵥ b) = star (R *ᵥ a) ⬝ᵥ b := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, hR]

private theorem quad_proj {H : Type} [Fintype H] {R : Matrix H H ℂ}
    (hR : IsStarProjection R) (x : H → ℂ) :
    star x ⬝ᵥ (R *ᵥ x) = (((normVec (R *ᵥ x)) ^ 2 : ℝ) : ℂ) := by
  have hRs : Rᴴ = R := hR.2
  have hRi : R * R = R := hR.1
  have h1s : (1 - R)ᴴ = (1 - R : Matrix H H ℂ) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hRs]
  have hsplit : x = R *ᵥ x + (1 - R) *ᵥ x := by
    rw [← Matrix.add_mulVec]
    have : (R + (1 - R) : Matrix H H ℂ) = 1 := by abel
    rw [this, Matrix.one_mulVec]
  have hzero : ((1 - R : Matrix H H ℂ) * R) = 0 := by
    rw [sub_mul, one_mul, hRi, sub_self]
  calc star x ⬝ᵥ (R *ᵥ x)
      = star (R *ᵥ x) ⬝ᵥ x := quad_symm hRs _ _
    _ = star (R *ᵥ x) ⬝ᵥ (R *ᵥ x + (1 - R) *ᵥ x) := by rw [← hsplit]
    _ = star (R *ᵥ x) ⬝ᵥ (R *ᵥ x) + star (R *ᵥ x) ⬝ᵥ ((1 - R) *ᵥ x) := by
        rw [dotProduct_add]
    _ = star (R *ᵥ x) ⬝ᵥ (R *ᵥ x) + star ((1 - R) *ᵥ (R *ᵥ x)) ⬝ᵥ x := by
        rw [quad_symm h1s]
    _ = star (R *ᵥ x) ⬝ᵥ (R *ᵥ x) + star (((1 - R) * R) *ᵥ x) ⬝ᵥ x := by
        rw [Matrix.mulVec_mulVec]
    _ = star (R *ᵥ x) ⬝ᵥ (R *ᵥ x) + star (((0 : Matrix H H ℂ) *ᵥ x)) ⬝ᵥ x := by
        rw [hzero]
    _ = star (R *ᵥ x) ⬝ᵥ (R *ᵥ x) + 0 := by simp [Matrix.zero_mulVec]
    _ = star (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := by rw [add_zero]
    _ = (((normVec (R *ᵥ x)) ^ 2 : ℝ) : ℂ) := star_dotProduct_self _

private theorem pythagorean {H : Type} [Fintype H] [DecidableEq H] {R : Matrix H H ℂ}
    (hR : IsStarProjection R) (y : H → ℂ) :
    normVec y ^ 2 = normVec (R *ᵥ y) ^ 2 + normVec ((1 - R) *ᵥ y) ^ 2 := by
  have hsplit : y = R *ᵥ y + (1 - R) *ᵥ y := by
    rw [← Matrix.add_mulVec]
    have : (R + (1 - R) : Matrix H H ℂ) = 1 := by abel
    rw [this, Matrix.one_mulVec]
  have hmain : star y ⬝ᵥ y = star y ⬝ᵥ (R *ᵥ y) + star y ⬝ᵥ ((1 - R) *ᵥ y) := by
    rw [← dotProduct_add, ← hsplit]
  rw [star_dotProduct_self y, quad_proj hR y, quad_proj hR.one_sub y,
    ← Complex.ofReal_add] at hmain
  exact Complex.ofReal_inj.mp hmain

private theorem normVec_mulVec_le {H : Type} [Fintype H] [DecidableEq H] {R : Matrix H H ℂ}
    (hR : IsStarProjection R) (x : H → ℂ) : normVec (R *ᵥ x) ≤ normVec x := by
  have hp := pythagorean hR x
  have hnn : 0 ≤ normVec ((1 - R) *ᵥ x) ^ 2 := sq_nonneg _
  have hle : normVec (R *ᵥ x) ^ 2 ≤ normVec x ^ 2 := by linarith
  exact le_of_sq_le_sq hle (norm_nonneg (toEuclidean_fromVec x))

private theorem normVec_sq_eq_zero {H : Type} [Fintype H] {v : H → ℂ}
    (h : normVec v ^ 2 = 0) : v = 0 := by
  have h2 : ∑ i, ‖v i‖ ^ 2 = 0 := by rwa [normVec_sq v] at h
  have h3 : ∀ i : H, ‖v i‖ = 0 := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      fun (i : H) (_ : i ∈ Finset.univ) => sq_nonneg (‖v i‖)).mp h2
    intro i
    exact sq_eq_zero_iff.mp (hs i (Finset.mem_univ i))
  funext i
  exact norm_eq_zero.mp (h3 i)

private theorem eq_of_mulVec_eq {H : Type} [Fintype H] [DecidableEq H] {A B : Matrix H H ℂ}
    (h : ∀ x : H → ℂ, A *ᵥ x = B *ᵥ x) : A = B :=
  Matrix.ext_of_mulVec_single (fun i => h (Pi.single i 1))

theorem Clause2ProjectorOrder_answer : Clause2ProjectorOrder := by
  intro H _ _ P Q hP hQ
  have hPi : P * P = P := hP.1
  have hQi : Q * Q = Q := hQ.1
  have hPstar : star P = P := hP.2
  have hQstar : star Q = Q := hQ.2
  have hPs : Pᴴ = P := hP.2
  have hQs : Qᴴ = Q := hQ.2
  have toPQ : Q * P = P → P * Q = P := by
    intro hQP
    have := congrArg star hQP
    rwa [star_mul, hPstar, hQstar] at this
  have toQP : P * Q = P → Q * P = P := by
    intro hPQ
    have := congrArg star hPQ
    rwa [star_mul, hPstar, hQstar] at this
  have to_norm : Q * P = P → ∀ x : H → ℂ, normVec (P *ᵥ x) ≤ normVec (Q *ᵥ x) := by
    intro hQP x
    have hPQ := toPQ hQP
    have key : P *ᵥ x = P *ᵥ (Q *ᵥ x) := by
      have h : P *ᵥ x = (P * Q) *ᵥ x := by rw [hPQ]
      rwa [← Matrix.mulVec_mulVec] at h
    rw [key]
    exact normVec_mulVec_le hP (Q *ᵥ x)
  have to_quad : Q * P = P → ∀ x : H → ℂ, 0 ≤ star x ⬝ᵥ ((Q - P) *ᵥ x) := by
    intro hQP x
    have hnorm := to_norm hQP x
    have hsub : star x ⬝ᵥ ((Q - P) *ᵥ x) = star x ⬝ᵥ (Q *ᵥ x) - star x ⬝ᵥ (P *ᵥ x) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
    have h2 : normVec (P *ᵥ x) ^ 2 ≤ normVec (Q *ᵥ x) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg _)
    rw [hsub, quad_proj hQ x, quad_proj hP x, ← Complex.ofReal_sub, Complex.zero_le_real]
    linarith
  have to_psd : Q * P = P → (Q - P).PosSemidef := by
    intro hQP
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (to_quad hQP)
    show (Q - P)ᴴ = Q - P
    rw [Matrix.conjTranspose_sub, hQs, hPs]
  have of_quad : (∀ x : H → ℂ, 0 ≤ star x ⬝ᵥ ((Q - P) *ᵥ x)) → Q * P = P := by
    intro hq
    have hnorm : ∀ x : H → ℂ, normVec (P *ᵥ x) ≤ normVec (Q *ᵥ x) := by
      intro x
      have := hq x
      have hsub : star x ⬝ᵥ ((Q - P) *ᵥ x) = star x ⬝ᵥ (Q *ᵥ x) - star x ⬝ᵥ (P *ᵥ x) := by
        rw [Matrix.sub_mulVec, dotProduct_sub]
      rw [hsub, quad_proj hQ x, quad_proj hP x, ← Complex.ofReal_sub, Complex.zero_le_real] at this
      have h2 : normVec (P *ᵥ x) ^ 2 ≤ normVec (Q *ᵥ x) ^ 2 := by linarith
      exact le_of_sq_le_sq h2 (norm_nonneg _)
    apply eq_of_mulVec_eq
    intro φ
    have hPφ : P *ᵥ (P *ᵥ φ) = P *ᵥ φ := by rw [Matrix.mulVec_mulVec, hPi]
    have hle1 := hnorm (P *ᵥ φ)
    rw [hPφ] at hle1
    have hle2 := normVec_mulVec_le hQ (P *ᵥ φ)
    have hQeq : normVec (Q *ᵥ (P *ᵥ φ)) = normVec (P *ᵥ φ) := le_antisymm hle2 hle1
    have hp := pythagorean hQ (P *ᵥ φ)
    rw [hQeq] at hp
    have hzero : normVec ((1 - Q) *ᵥ (P *ᵥ φ)) ^ 2 = 0 := by
      have h1 : normVec (P *ᵥ φ) ^ 2 + normVec ((1 - Q) *ᵥ (P *ᵥ φ)) ^ 2
          = normVec (P *ᵥ φ) ^ 2 + (0 : ℝ) := by
        rw [add_zero]
        exact hp.symm
      exact add_left_cancel h1
    have hv : (1 - Q) *ᵥ (P *ᵥ φ) = 0 := normVec_sq_eq_zero hzero
    have hsplit : P *ᵥ φ = Q *ᵥ (P *ᵥ φ) + (1 - Q) *ᵥ (P *ᵥ φ) := by
      rw [← Matrix.add_mulVec]
      have : (Q + (1 - Q) : Matrix H H ℂ) = 1 := by abel
      rw [this, Matrix.one_mulVec]
    rw [hv, add_zero] at hsplit
    rw [← Matrix.mulVec_mulVec]
    exact hsplit.symm
  have of_norm : (∀ x : H → ℂ, normVec (P *ᵥ x) ≤ normVec (Q *ᵥ x)) → Q * P = P := by
    intro hn
    apply of_quad
    intro x
    have hnorm := hn x
    have h2 : normVec (P *ᵥ x) ^ 2 ≤ normVec (Q *ᵥ x) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg _)
    have hsub : star x ⬝ᵥ ((Q - P) *ᵥ x) = star x ⬝ᵥ (Q *ᵥ x) - star x ⬝ᵥ (P *ᵥ x) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
    rw [hsub, quad_proj hQ x, quad_proj hP x, ← Complex.ofReal_sub, Complex.zero_le_real]
    linarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hfix
    apply eq_of_mulVec_eq
    intro φ
    have hPφ : P *ᵥ (P *ᵥ φ) = P *ᵥ φ := by rw [Matrix.mulVec_mulVec, hPi]
    have hfix' := hfix (P *ᵥ φ) hPφ
    rw [← Matrix.mulVec_mulVec]
    exact hfix'
  · intro hQP ψ hfix
    rw [← hfix, Matrix.mulVec_mulVec, hQP]
  · intro hker
    have hPQ : P * Q = P := by
      apply eq_of_mulVec_eq
      intro φ
      have hQφ : Q *ᵥ (Q *ᵥ φ) = Q *ᵥ φ := by rw [Matrix.mulVec_mulVec, hQi]
      have hQη : Q *ᵥ (φ - Q *ᵥ φ) = 0 := by rw [Matrix.mulVec_sub, hQφ, sub_self]
      have hPη : P *ᵥ (φ - Q *ᵥ φ) = 0 := hker (φ - Q *ᵥ φ) hQη
      rw [Matrix.mulVec_sub, sub_eq_zero] at hPη
      rw [← Matrix.mulVec_mulVec]
      exact hPη.symm
    exact toQP hPQ
  · intro hQP ψ hQ0
    have hPQ := toPQ hQP
    have h1 : P *ᵥ ψ = (P * Q) *ᵥ ψ := by rw [hPQ]
    rw [← Matrix.mulVec_mulVec] at h1
    rw [h1, hQ0, Matrix.mulVec_zero]
  · exact toPQ
  · exact toQP
  · exact fun hQP => IsStarProjection.sub_of_mul_eq_right hP hQ hQP
  · intro hproj
    apply of_quad
    intro x
    rw [quad_proj hproj x, Complex.zero_le_real]
    exact sq_nonneg _
  · intro hQP
    have h : P * Q * P = P * (Q * P) := Matrix.mul_assoc _ _ _
    rw [h, hQP, hPi]
  · intro hPQP
    have e1 : (P * Q) * (Q * P) = P := by
      have a : (P * Q) * (Q * P) = P * (Q * (Q * P)) := Matrix.mul_assoc _ _ _
      have b : Q * (Q * P) = Q * P := by rw [← Matrix.mul_assoc, hQi]
      have c : P * (Q * P) = P := by rwa [← Matrix.mul_assoc]
      rw [a, b, c]
    have e2 : (P * Q) * P = P := hPQP
    have e3 : P * (Q * P) = P := by rwa [← Matrix.mul_assoc]
    have hSH : (Q * P - P)ᴴ = P * Q - P := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hPs, hQs]
    have hSHS : (Q * P - P)ᴴ * (Q * P - P) = 0 := by
      rw [hSH]
      simp only [sub_mul, mul_sub]
      rw [e1, e2, e3, hPi]
      abel
    have hS0 : Q * P - P = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hSHS
    rwa [sub_eq_zero] at hS0
  · exact to_psd
  · intro hpsd
    apply of_quad
    exact PosSemidef.dotProduct_mulVec_nonneg hpsd
  · exact to_norm
  · exact of_norm

end Qatlib.Concepts.QlsReadoutSpec.Amplification
