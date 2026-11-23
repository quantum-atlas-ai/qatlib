/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma4RestrictedQuan
public import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2QuadraticSpeedupRestrictedQuan
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

@[expose] public section

/-!
# Euclidean isometry and the two-phase relation of the rank-one Grover iterate

In [BrassardHoyerTapp1998Counting], the sign-phase iterate `Q = -A S_0 A^{-1} S_χ` acts on the
span of the good and bad parts of the prepared state `A |0⟩` as a planar rotation. This module
turns that algebraic picture into quantitative Euclidean statements on genuine
`EuclideanSpace` / `Matrix.Norms.L2Operator` norms:

* `signIterate_mem_unitaryGroup`: `Q` is a unitary matrix whenever `A * A.conjTranspose = 1`.
* `signIterate_euclidean_norm`: `Q` preserves the complex Euclidean norm of every state vector.
* `signIterate_plane_isometry_uniform`: the isometry constant `C = 1` may be chosen uniformly,
  before quantifying over preparations and over the invariant plane.
* `signIterate_l2_opNorm`: the `Matrix.Norms.L2Operator` operator norm of `Q` is exactly one in
  non-empty dimension.
* `signIterate_plane_two_phase_quadratic` and `signIterate_plane_eigenphase_relation`: on the
  invariant plane, `Q` satisfies the quadratic `Q² - 2 cos(2θ) Q + 1 = 0` with `sin²θ = a`,
  derived from the planar action in [BrassardHoyerTapp1998Counting], Lemma 4.
* `quadratic_two_phase_roots`: the factorization of that quadratic over `ℂ`.
* `signIterate_rotation_euclidean_exact` and `signIterate_rotation_euclidean_error_uniform`: the
  Theorem 1 rotation formula holds with exactly zero Euclidean error, uniformly in the iteration
  count.

## References

* [Brassard et al., 1998, §2](https://arxiv.org/abs/quant-ph/9805082v1)
* [BrassardHoyerTapp1998Counting]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QCounting98.MainResults.PlaneIsometryEuclidean

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace
open Qatlib.Foundations.PureStateMath.BornBridge

/-- The sign-phase iterate `Q = -A S_0 A⁻¹ S_χ` is a unitary matrix whenever `A` is unitary:
the total-zero reflection `S_0` and the marked-phase reflection `S_χ` are diagonal with entries of
unit modulus, conjugation by `A` preserves unitarity, and the leading minus sign is the scalar
`-1` of unit modulus. See [BrassardHoyerTapp1998Counting]. -/
theorem signIterate_mem_unitaryGroup {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : Fin (n + 1) → Bool) (hA : A * A.conjTranspose = 1) :
    iterate A g (-1) (-1) ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  have hA' : A ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact hA
  have hA'' : A.conjTranspose ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hA'
    exact hA'
  have hdiag : ∀ d : Fin (n + 1) → ℂ, (∀ i, ‖d i‖ = 1) →
      Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
    intro d hd
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    funext i j
    rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      show d i * star (d i) = 1
      have hmul : d i * star (d i) = ‖d i‖ ^ 2 := Complex.mul_conj' _
      rw [hmul, hd i]
      norm_num
    · simp only [hij, ite_false]
  have hzero : ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
      ((-1 : ℂ) - 1) • Matrix.single (0 : Fin (n + 1)) (0 : Fin (n + 1)) (1 : ℂ)) =
      Matrix.diagonal (fun i : Fin (n + 1) => if i = 0 then (-1 : ℂ) else 1) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.single_apply,
      Matrix.diagonal_apply]
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · subst hi; subst hj
        simp only [true_and, ite_true, smul_eq_mul]
        ring
      · have h0j : ¬(0 : Fin (n + 1)) = j := fun h => hj h.symm
        subst hi
        simp only [true_and, h0j, ite_false, smul_eq_mul, mul_zero, add_zero]
    · by_cases hij : i = j
      · have h0i : ¬(0 : Fin (n + 1)) = i := fun h => hi h.symm
        subst hij
        simp only [ite_true, hi, h0i, false_and, ite_false, smul_eq_mul, mul_zero,
          add_zero]
      · have h0i : ¬(0 : Fin (n + 1)) = i := fun h => hi h.symm
        simp only [hij, h0i, false_and, ite_false, smul_eq_mul, mul_zero, add_zero]
  have hS0 : ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
      ((-1 : ℂ) - 1) • Matrix.single (0 : Fin (n + 1)) (0 : Fin (n + 1)) (1 : ℂ)) ∈
      Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
    rw [hzero]
    apply hdiag
    intro i
    by_cases hi : i = 0 <;> simp [hi]
  have hD : Matrix.diagonal (fun i : Fin (n + 1) => if g i then (-1 : ℂ) else 1) ∈
      Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
    apply hdiag
    intro i
    cases g i <;> simp
  have h1 : A * ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
      ((-1 : ℂ) - 1) • Matrix.single (0 : Fin (n + 1)) (0 : Fin (n + 1)) (1 : ℂ)) *
      A.conjTranspose ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ hA' hS0) hA''
  have hP : A * ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
      ((-1 : ℂ) - 1) • Matrix.single (0 : Fin (n + 1)) (0 : Fin (n + 1)) (1 : ℂ)) *
      A.conjTranspose * Matrix.diagonal (fun i : Fin (n + 1) => if g i then (-1 : ℂ) else 1) ∈
      Matrix.unitaryGroup (Fin (n + 1)) ℂ :=
    Submonoid.mul_mem _ h1 hD
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hP
  show -(A * ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
      ((-1 : ℂ) - 1) • Matrix.single (0 : Fin (n + 1)) (0 : Fin (n + 1)) (1 : ℂ)) *
      A.conjTranspose * Matrix.diagonal (fun i : Fin (n + 1) => if g i then (-1 : ℂ) else 1)) ∈
      Matrix.unitaryGroup (Fin (n + 1)) ℂ
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_neg,
    neg_mul_neg]
  exact hP

/-- The sign-phase iterate preserves the complex Euclidean norm of every state vector. See
[BrassardHoyerTapp1998Counting]. -/
theorem signIterate_euclidean_norm {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : Fin (n + 1) → Bool) (hA : A * A.conjTranspose = 1) (v : Fin (n + 1) → ℂ) :
    ‖toEuclidean_fromVec ((iterate A g (-1) (-1)).mulVec v)‖ = ‖toEuclidean_fromVec v‖ := by
  have hQ := signIterate_mem_unitaryGroup A g hA
  have h1 := norm_toEuclideanCLM_of_mem_unitaryGroup hQ (toEuclidean_fromVec v)
  rw [toEuclideanCLM_applyGate] at h1
  exact h1

/-- A uniform isometry constant for the invariant good/bad plane can be chosen before quantifying
over the preparation: `C = 1` works for every unitary preparation and every vector in the span
of the good and bad parts of the prepared column. See [BrassardHoyerTapp1998Counting]. -/
theorem signIterate_plane_isometry_uniform :
    ∃ C > 0, ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool),
      A * A.conjTranspose = 1 → ∀ w ∈ Submodule.span ℂ
        ({goodPart g (fun i => A i 0), badPart g (fun i => A i 0)} : Set (Fin (n + 1) → ℂ)),
        ‖toEuclidean_fromVec ((iterate A g (-1) (-1)).mulVec w)‖ =
          C * ‖toEuclidean_fromVec w‖ := by
  refine ⟨1, by norm_num, fun n A g hA w _hw => ?_⟩
  rw [one_mul]
  exact signIterate_euclidean_norm A g hA w

open scoped Matrix.Norms.L2Operator in

/-- In non-empty dimension, the `Matrix.Norms.L2Operator` operator norm of the sign-phase
iterate is exactly one. See [BrassardHoyerTapp1998Counting]. -/
theorem signIterate_l2_opNorm {n : ℕ} [Nonempty (Fin (n + 1))]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1) :
    ‖(iterate A g (-1) (-1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)‖ = 1 := by
  have hQ := signIterate_mem_unitaryGroup A g hA
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  set T := (Matrix.toEuclideanCLM (𝕜 := ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (n + 1))))
    (iterate A g (-1) (-1)) with hT
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound T zero_le_one fun x => ?_
    rw [one_mul]
    exact (norm_toEuclideanCLM_of_mem_unitaryGroup hQ x).le
  · have hne : Nonempty (Fin (n + 1)) := ⟨⟨0, Nat.succ_pos n⟩⟩
    obtain ⟨i⟩ := hne
    let x : EuclideanSpace ℂ (Fin (n + 1)) :=
      PiLp.single (β := fun _ : Fin (n + 1) => ℂ) 2 i (1 : ℂ)
    have hx : ‖x‖ = 1 := by
      rw [PiLp.norm_single]
      norm_num
    have hTx : ‖T x‖ = 1 := by
      rw [← hx]
      exact norm_toEuclideanCLM_of_mem_unitaryGroup hQ x
    have hle := T.le_opNorm x
    rw [hTx, hx, mul_one] at hle
    exact hle

/-- On the invariant good/bad plane, the sign-phase iterate satisfies the quadratic relation
`Q² - 2(1 - 2a) Q + 1 = 0`, where `a` is the squared mass of the good part of the prepared
column. With `a = sin²θ`, this is `Q² - 2 cos(2θ) Q + 1 = 0`, as follows from the planar
action in [BrassardHoyerTapp1998Counting], Lemma 4. -/
theorem signIterate_plane_two_phase_quadratic {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1) :
    ∀ w ∈ Submodule.span ℂ
        ({goodPart g (fun i => A i 0), badPart g (fun i => A i 0)} : Set (Fin (n + 1) → ℂ)),
      ((iterate A g (-1) (-1)) ^ 2 -
        (2 * (1 - 2 * (∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))) : ℂ) •
          iterate A g (-1) (-1) + 1).mulVec w = 0 := by
  intro w hw
  obtain ⟨hQa, hQb, hb⟩ := zoo_counting_two_dimensional_sign_action n A g hA
  have hQa' : (iterate A g (-1) (-1)).mulVec (goodPart g (fun i => A i 0)) =
      (1 - 2 * ((∑ i, Complex.normSq (goodPart g (fun i => A i 0) i) : ℝ) : ℂ)) •
        goodPart g (fun i => A i 0) -
      (2 * ((∑ i, Complex.normSq (goodPart g (fun i => A i 0) i) : ℝ) : ℂ)) •
        badPart g (fun i => A i 0) := hQa
  have hbC : ((∑ j, Complex.normSq (badPart g (fun k => A k 0) j) : ℝ) : ℂ) =
      1 - ((∑ i, Complex.normSq (goodPart g (fun i => A i 0) i) : ℝ) : ℂ) := by
    rw [hb]; push_cast; ring
  have hQb' : (iterate A g (-1) (-1)).mulVec (badPart g (fun i => A i 0)) =
      (1 - 2 * ((∑ i, Complex.normSq (goodPart g (fun i => A i 0) i) : ℝ) : ℂ)) •
        badPart g (fun i => A i 0) +
      (2 * (1 - ((∑ i, Complex.normSq (goodPart g (fun i => A i 0) i) : ℝ) : ℂ))) •
        goodPart g (fun i => A i 0) := by
    rw [hbC] at hQb
    exact hQb
  induction hw using Submodule.span_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · have h2 : ((iterate A g (-1) (-1)) ^ 2).mulVec (goodPart g (fun i => A i 0)) =
            (2 * (1 - 2 * ((∑ i, Complex.normSq (goodPart g (fun i => A i 0) i) : ℝ) : ℂ))) •
              (iterate A g (-1) (-1)).mulVec (goodPart g (fun i => A i 0)) -
              goodPart g (fun i => A i 0) := by
          rw [pow_two, ← Matrix.mulVec_mulVec, hQa', Matrix.mulVec_sub, Matrix.mulVec_smul,
            Matrix.mulVec_smul, hQa', hQb']
          ext i
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          push_cast
          ring
        rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h2]
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
        ring
      · have h2 : ((iterate A g (-1) (-1)) ^ 2).mulVec (badPart g (fun i => A i 0)) =
            (2 * (1 - 2 * ((∑ i, Complex.normSq (goodPart g (fun i => A i 0) i) : ℝ) : ℂ))) •
              (iterate A g (-1) (-1)).mulVec (badPart g (fun i => A i 0)) -
              badPart g (fun i => A i 0) := by
          rw [pow_two, ← Matrix.mulVec_mulVec, hQb', Matrix.mulVec_add, Matrix.mulVec_smul,
            Matrix.mulVec_smul, hQb', hQa']
          ext i
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          push_cast
          ring
        rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h2]
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
        ring
  | zero => rw [Matrix.mulVec_zero]
  | add x y _ _ ihx ihy => rw [Matrix.mulVec_add, ihx, ihy, add_zero]
  | smul r x _ ih => rw [Matrix.mulVec_smul, ih, smul_zero]

/-- On the invariant good/bad plane, the sign-phase iterate satisfies the quadratic
`Q² - 2 cos(2θ) Q + 1 = 0` with `sin²θ = a`. This is the polynomial identity
associated with the planar action in [BrassardHoyerTapp1998Counting], Lemma 4. -/
theorem signIterate_plane_eigenphase_relation {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1) (θ : ℝ)
    (hsin2 : Real.sin θ ^ 2 = ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))
    (_hθ0 : 0 ≤ θ) (_hθπ : θ ≤ Real.pi / 2)
    (_ha0 : 0 < ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))
    (_ha1 : ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i) < 1) :
    ∀ w ∈ Submodule.span ℂ
        ({goodPart g (fun i => A i 0), badPart g (fun i => A i 0)} : Set (Fin (n + 1) → ℂ)),
      ((iterate A g (-1) (-1)) ^ 2 -
        (2 * Real.cos (2 * θ) : ℂ) • iterate A g (-1) (-1) + 1).mulVec w = 0 := by
  have hcc : (2 * Real.cos (2 * θ) : ℂ) =
      (2 * (1 - 2 * (∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))) : ℂ) := by
    have hc : Real.cos (2 * θ) =
        1 - 2 * (∑ i, Complex.normSq (goodPart g (fun i => A i 0) i)) := by
      rw [Real.cos_two_mul_eq_one_sub, hsin2]
    rw [hc]
    push_cast
    ring
  rw [hcc]
  exact signIterate_plane_two_phase_quadratic A g hA

/-- The scalar quadratic associated with the planar action in [BrassardHoyerTapp1998Counting],
Lemma 4, factors over `ℂ` with roots `Complex.exp (2θ I)` and `Complex.exp (-2θ I)`. -/
theorem quadratic_two_phase_roots (θ : ℝ) (z : ℂ) :
    z ^ 2 - (2 * Real.cos (2 * θ) : ℂ) * z + 1 =
      (z - Complex.exp (2 * θ * Complex.I)) * (z - Complex.exp (-(2 * θ * Complex.I))) := by
  have hsum : Complex.exp (2 * θ * Complex.I) + Complex.exp (-(2 * θ * Complex.I)) =
      (2 * Real.cos (2 * θ) : ℂ) := by
    have e1 : Complex.exp (2 * θ * Complex.I) =
        (Real.cos (2 * θ) : ℂ) + (Real.sin (2 * θ) : ℂ) * Complex.I := by
      rw [show (2 * θ * Complex.I) = ((2 * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.exp_ofReal_mul_I _
    have e2 : Complex.exp (-(2 * θ * Complex.I)) =
        (Real.cos (2 * θ) : ℂ) - (Real.sin (2 * θ) : ℂ) * Complex.I := by
      rw [show (-(2 * θ * Complex.I)) = ((-(2 * θ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
      ring
    rw [e1, e2]
    ring
  have hprod : Complex.exp (2 * θ * Complex.I) * Complex.exp (-(2 * θ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, show 2 * θ * Complex.I + -(2 * θ * Complex.I) = 0 by ring,
      Complex.exp_zero]
  rw [← hsum, ← hprod]
  ring

/-- The Theorem 1 rotation formula of [BrassardHoyerTapp1998Counting] holds with exactly zero
Euclidean error: after `j` iterates the prepared state equals its two-dimensional rotation
formula in complex Euclidean norm. -/
theorem signIterate_rotation_euclidean_exact {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi / 2)
    (hsin2a : Real.sin θ ^ 2 = ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))
    (ha0 : 0 < ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))
    (ha1 : ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i) < 1) (j : ℕ) :
    ‖toEuclidean_fromVec (((iterate A g (-1) (-1)) ^ j).mulVec (fun i => A i 0)) -
      toEuclidean_fromVec
        ((((Real.sin ((2 * (j : ℝ) + 1) * θ) /
            Real.sqrt (∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))) : ℝ) : ℂ) •
          goodPart g (fun i => A i 0) +
        (((Real.cos ((2 * (j : ℝ) + 1) * θ) /
            Real.sqrt (1 - ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))) : ℝ) : ℂ) •
          badPart g (fun i => A i 0))‖ = 0 := by
  rw [zoo_counting_rankone_known_success_amplification_rotation A g hA θ hθ0 hθπ hsin2a ha0 ha1 j,
    sub_self, norm_zero]

/-- The Euclidean error of the Theorem 1 rotation formula is uniformly bounded by a constant
chosen before quantifying over the iteration count; here the constant `1` works since the error
is exactly zero. See [BrassardHoyerTapp1998Counting]. -/
theorem signIterate_rotation_euclidean_error_uniform {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi / 2)
    (hsin2a : Real.sin θ ^ 2 = ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))
    (ha0 : 0 < ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))
    (ha1 : ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i) < 1) :
    ∃ C > 0, ∀ j : ℕ,
      ‖toEuclidean_fromVec (((iterate A g (-1) (-1)) ^ j).mulVec (fun i => A i 0)) -
        toEuclidean_fromVec
          ((((Real.sin ((2 * (j : ℝ) + 1) * θ) /
              Real.sqrt (∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))) : ℝ) : ℂ) •
            goodPart g (fun i => A i 0) +
          (((Real.cos ((2 * (j : ℝ) + 1) * θ) /
              Real.sqrt (1 - ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))) : ℝ) : ℂ) •
            badPart g (fun i => A i 0))‖ ≤ C := by
  refine ⟨1, by norm_num, fun j => ?_⟩
  rw [signIterate_rotation_euclidean_exact A g hA θ hθ0 hθπ hsin2a ha0 ha1 j]
  norm_num

end Qatlib.Papers.QCounting98.MainResults.PlaneIsometryEuclidean
