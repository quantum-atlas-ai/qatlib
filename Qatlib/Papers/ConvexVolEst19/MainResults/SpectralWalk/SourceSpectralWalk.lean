/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.AmplitudeCore.InvFreePhase.Qubitization

set_option backward.isDefEq.respectTransparency false

/-!
# ConvexVolEst19 §3 — continuous-space quantum walk spectrum

Fixed source: arXiv:1908.03903v3 (1 Nov 2021), Chakrabarti--Childs--Hung--Li--Wang--Wu,
*Quantum algorithm for estimating volumes of convex bodies*, §3, printed pp.18--21.

This file formalizes the finite-dimensional linear algebra underlying the paper's
continuous-space walk.  The paper defines the walk `W := S(2Π - I)` with `Π = T T†`
(the orthogonal projector onto the range of the embedding `T|x⟩ = |φ_x⟩`), the swap `S`,
and the discriminant `D := T† S T`, whose entry is `√(p_{x→y} p_{y→x})` (Eq. (3.11)).
The finite model is exactly the frozen Szegedy model (`SzegedyIsometry`, `SwapGate`,
`SzegedyDiscriminant`, `szegedy_gram_eq_discriminant`), with the paper's one-reflection
walk `S R` rather than the frozen two-reflection walk `S R S R`.

Claim coverage:
* `source_lemma_3_1` — Lemma 3.1, p.19: every eigenvalue `λ` of `D` satisfies `|λ| ≤ 1`.
* `source_theorem_3_1` — Theorem 3.1, p.19: the walk eigenvalues `λ ± i√(1-λ²)` occur on
  the explicit eigenvectors `(1 - μS)T|λ⟩`; the complement contributes the `±1` branch.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

namespace Qatlib.Papers.ConvexVolEst19.MainResults.SpectralWalk

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The paper's continuous-space walk operator `W = S(2Π - I)` of Eq. (3.10), with
`Π = T Tᴴ` the projector onto the embedding and `S` the register swap.  It is the
frozen reflection `SzegedyReflection` (which is `2Π - 1`) followed by the swap. -/
noncomputable def paperWalk (P : I → I → ℝ) : Matrix (I × I) (I × I) ℂ :=
  SwapGate * SzegedyReflection P

/-- Vector action of a reflection: `(2P - 1)y = 2·(Py) - y`. -/
theorem reflectionAbout_mulVec_local (X : Matrix (I × I) (I × I) ℂ)
    (y : QState (I × I)) :
    ReflectionAbout X *ᵥ y = (2 : ℂ) • (X *ᵥ y) - y := by
  simp [ReflectionAbout, Matrix.sub_mulVec, Matrix.smul_mulVec]

/-- The Gram bridge in the exact form used below: `Tᴴ (S T)` is the complexified
discriminant matrix. -/
theorem gram_eq_discriminant_map (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    (SzegedyIsometry P)ᴴ * (SwapGate * SzegedyIsometry P)
      = (SzegedyDiscriminant P).map Complex.ofReal := by
  have h := szegedy_gram_eq_discriminant P hP
  rwa [SzegedyIsometryB] at h

/-- A real discriminant eigenvector, complexified, is a complex eigenvector of the
complexified discriminant. -/
theorem discriminant_mulVec_complex (P : I → I → ℝ) (v : I → ℝ) (lam : ℝ)
    (hvD : SzegedyDiscriminant P *ᵥ v = lam • v) :
    ((SzegedyDiscriminant P).map Complex.ofReal) *ᵥ (fun i => ((v i : ℂ)))
      = ((lam : ℂ)) • (fun i => ((v i : ℂ))) := by
  funext x
  have hsum : (((SzegedyDiscriminant P).map Complex.ofReal) *ᵥ (fun y => ((v y : ℂ)))) x
      = ((∑ y, SzegedyDiscriminant P x y * v y : ℝ) : ℂ) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [Finset.sum_congr rfl fun y _ => (Complex.ofReal_mul _ _).symm,
      ← Complex.ofReal_sum]
  rw [hsum, show (∑ y, SzegedyDiscriminant P x y * v y)
      = (SzegedyDiscriminant P *ᵥ v) x from rfl, hvD]
  simp [Pi.smul_apply, smul_eq_mul]

/-- The projector `T Tᴴ` fixes the embedded state `T|ψ⟩`. -/
theorem proj_fixes_emb (P : I → I → ℝ) (hP : IsTransitionMatrix P) (w : QState I) :
    (SzegedyIsometry P * (SzegedyIsometry P)ᴴ) *ᵥ (SzegedyIsometry P *ᵥ w)
      = SzegedyIsometry P *ᵥ w := by
  have hTT : (SzegedyIsometry P)ᴴ * SzegedyIsometry P = 1 :=
    szegedyIsometry_conjTranspose_mul P hP
  calc (SzegedyIsometry P * (SzegedyIsometry P)ᴴ) *ᵥ (SzegedyIsometry P *ᵥ w)
      = SzegedyIsometry P
          *ᵥ ((SzegedyIsometry P)ᴴ *ᵥ (SzegedyIsometry P *ᵥ w)) := by
        rw [← Matrix.mulVec_mulVec]
    _ = SzegedyIsometry P
          *ᵥ (((SzegedyIsometry P)ᴴ * SzegedyIsometry P) *ᵥ w) := by
        exact congrArg (fun z => SzegedyIsometry P *ᵥ z)
          (Matrix.mulVec_mulVec w (SzegedyIsometry P)ᴴ (SzegedyIsometry P))
    _ = SzegedyIsometry P *ᵥ w := by rw [hTT, Matrix.one_mulVec]

/-- The walk fixes the embedded state: `W T|ψ⟩ = S T|ψ⟩` (paper Eq. (3.30)). -/
theorem paperWalk_mulVec_emb (P : I → I → ℝ) (hP : IsTransitionMatrix P)
    (w : QState I) :
    paperWalk P *ᵥ (SzegedyIsometry P *ᵥ w)
      = SwapGate *ᵥ (SzegedyIsometry P *ᵥ w) := by
  have hproj := proj_fixes_emb P hP w
  calc paperWalk P *ᵥ (SzegedyIsometry P *ᵥ w)
      = SwapGate *ᵥ (SzegedyReflection P *ᵥ (SzegedyIsometry P *ᵥ w)) := by
        rw [paperWalk, ← Matrix.mulVec_mulVec]
    _ = SwapGate *ᵥ ((2 : ℂ) • ((SzegedyIsometry P * (SzegedyIsometry P)ᴴ)
          *ᵥ (SzegedyIsometry P *ᵥ w)) - (SzegedyIsometry P *ᵥ w)) := by
        rw [SzegedyReflection, reflectionAbout_mulVec_local]
    _ = SwapGate *ᵥ (SzegedyIsometry P *ᵥ w) := by
        rw [hproj]
        congr 1
        module

/-- The walk acts on the swapped embedding as `W S T|λ⟩ = 2λ S T|λ⟩ - T|λ⟩`
(paper Eq. (3.31)). -/
theorem paperWalk_mulVec_swap_emb (P : I → I → ℝ) (hP : IsTransitionMatrix P)
    (w : QState I) (lam : ℝ)
    (hDw : ((SzegedyDiscriminant P).map Complex.ofReal) *ᵥ w = ((lam : ℂ)) • w) :
    paperWalk P *ᵥ (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))
      = (2 * (lam : ℂ)) • (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))
        - (SzegedyIsometry P *ᵥ w) := by
  have hstep : (SzegedyIsometry P)ᴴ
        *ᵥ (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))
      = ((SzegedyIsometry P)ᴴ * (SwapGate * SzegedyIsometry P)) *ᵥ w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hproj : (SzegedyIsometry P * (SzegedyIsometry P)ᴴ)
      *ᵥ (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))
      = ((lam : ℂ)) • (SzegedyIsometry P *ᵥ w) := by
    calc (SzegedyIsometry P * (SzegedyIsometry P)ᴴ)
          *ᵥ (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))
        = SzegedyIsometry P *ᵥ ((SzegedyIsometry P)ᴴ
            *ᵥ (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))) := by
          rw [← Matrix.mulVec_mulVec]
      _ = SzegedyIsometry P *ᵥ
            (((SzegedyIsometry P)ᴴ * (SwapGate * SzegedyIsometry P)) *ᵥ w) := by
          rw [hstep]
      _ = SzegedyIsometry P *ᵥ
            (((SzegedyDiscriminant P).map Complex.ofReal) *ᵥ w) := by
          rw [gram_eq_discriminant_map P hP]
      _ = SzegedyIsometry P *ᵥ (((lam : ℂ)) • w) := by rw [hDw]
      _ = ((lam : ℂ)) • (SzegedyIsometry P *ᵥ w) := by rw [Matrix.mulVec_smul]
  calc paperWalk P *ᵥ (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))
      = SwapGate *ᵥ (SzegedyReflection P
          *ᵥ (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))) := by
        rw [paperWalk, ← Matrix.mulVec_mulVec]
    _ = SwapGate *ᵥ ((2 : ℂ) • ((SzegedyIsometry P * (SzegedyIsometry P)ᴴ)
          *ᵥ (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w)))
          - (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))) := by
        rw [SzegedyReflection, reflectionAbout_mulVec_local]
    _ = SwapGate *ᵥ ((2 : ℂ) • (((lam : ℂ)) • (SzegedyIsometry P *ᵥ w))
          - (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))) := by rw [hproj]
    _ = (2 * (lam : ℂ)) • (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))
          - (SzegedyIsometry P *ᵥ w) := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.mulVec_mulVec (SzegedyIsometry P *ᵥ w) SwapGate SwapGate,
          swapGate_mul_self, Matrix.one_mulVec, smul_smul]

/-- The quadratic identity behind the walk eigenvalues:
`μ² = 2λμ - 1` for `μ = λ ± i√(1-λ²)`. -/
theorem walkMu_sq (lam : ℝ) (hlam : lam ^ 2 ≤ 1) (sgn : Bool) :
    let μ : ℂ := (lam : ℂ)
      + (if sgn then Complex.I else -Complex.I) * ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)
    μ * μ = 2 * (lam : ℂ) * μ - 1 := by
  intro μ
  have hs2 : ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) ^ 2 = 1 - (lam : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
    push_cast
    ring
  have hs2' : ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)
        * ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) = 1 - (lam : ℂ) ^ 2 := by
    rw [← pow_two]; exact hs2
  cases sgn
  · simp only [Bool.false_eq_true, if_false, μ]
    have hcc : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
      rw [neg_mul_neg]; exact Complex.I_mul_I
    linear_combination (norm := ring_nf)
      (((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)) * hcc
      - hs2'
  · simp only [if_true, μ]
    have hcc : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
    linear_combination (norm := ring_nf)
      (((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)) * hcc
      - hs2'

/-- The paper's Theorem 3.1 eigenvalue relation: for a real discriminant eigenvector
`D v = λ v` with `λ² ≤ 1`, the vector `(1 - μ S) T|v⟩` satisfies
`W (1 - μ S) T|v⟩ = μ (1 - μ S) T|v⟩` for both `μ = λ ± i√(1-λ²)`. -/
theorem paperWalk_eigenvector (P : I → I → ℝ) (hP : IsTransitionMatrix P)
    (v : I → ℝ) (lam : ℝ) (hlam : lam ^ 2 ≤ 1)
    (hvD : SzegedyDiscriminant P *ᵥ v = lam • v) (sgn : Bool) :
    let μ : ℂ := (lam : ℂ)
      + (if sgn then Complex.I else -Complex.I) * ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)
    let w : QState I := fun i => ((v i : ℂ))
    paperWalk P *ᵥ (((1 : Matrix (I × I) (I × I) ℂ) - μ • SwapGate)
        *ᵥ (SzegedyIsometry P *ᵥ w))
      = μ • (((1 : Matrix (I × I) (I × I) ℂ) - μ • SwapGate)
        *ᵥ (SzegedyIsometry P *ᵥ w)) := by
  intro μ w
  have hDw := discriminant_mulVec_complex P v lam hvD
  have hT := paperWalk_mulVec_emb P hP w
  have hST := paperWalk_mulVec_swap_emb P hP w lam hDw
  have hμ := walkMu_sq lam hlam sgn
  have hstep : ((1 : Matrix (I × I) (I × I) ℂ) - μ • SwapGate)
        *ᵥ (SzegedyIsometry P *ᵥ w)
      = (SzegedyIsometry P *ᵥ w) - μ • (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w)) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  rw [hstep, Matrix.mulVec_sub, Matrix.mulVec_smul, hT, hST]
  rw [smul_sub, smul_sub]
  simp only [smul_smul]
  rw [hμ]
  module

/-- The `-1`/`+1` branch of Theorem 3.1: a nonzero vector orthogonal to the embedding
range on which the swap acts by `u ↦ u` is a walk eigenvector with eigenvalue `-1`. -/
theorem paperWalk_complement_eigenvector (P : I → I → ℝ)
    (u : QState (I × I)) (hker : (SzegedyIsometry P)ᴴ *ᵥ u = 0)
    (hS : SwapGate *ᵥ u = u) :
    paperWalk P *ᵥ u = -u := by
  have hproj : (SzegedyIsometry P * (SzegedyIsometry P)ᴴ) *ᵥ u = 0 := by
    rw [← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]
  calc paperWalk P *ᵥ u
      = SwapGate *ᵥ (SzegedyReflection P *ᵥ u) := by
        rw [paperWalk, ← Matrix.mulVec_mulVec]
    _ = SwapGate *ᵥ ((2 : ℂ) • ((SzegedyIsometry P * (SzegedyIsometry P)ᴴ) *ᵥ u)
          - u) := by
        rw [SzegedyReflection, reflectionAbout_mulVec_local]
    _ = SwapGate *ᵥ (-u) := by
        rw [hproj]
        congr 1
        module
    _ = -(SwapGate *ᵥ u) := by rw [Matrix.mulVec_neg u SwapGate]
    _ = -u := by rw [hS]

/-- The paper's walk `S(2Π - I)` is unitary. -/
theorem paperWalk_unitary (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    paperWalk P ∈ Matrix.unitaryGroup (I × I) ℂ :=
  Submonoid.mul_mem _ swapGate_unitary (szegedyReflection_unitary P hP)

/-- **Lemma 3.1 (arXiv:1908.03903v3, p.19).**  For any real eigenvector `v` of the
discriminant operator `D` with eigenvalue `λ`, `|λ| ≤ 1`.

Proof (paper pp.19--20): `λ⟨v,v⟩ = ⟨v,Dv⟩ = ⟨Tv, STv⟩`, and Cauchy--Schwarz with
`‖Tv‖ = ‖v‖`, `‖STv‖ = ‖v‖` gives `|λ| ≤ 1`. -/
theorem source_lemma_3_1 (P : I → I → ℝ) (hP : IsTransitionMatrix P)
    (v : I → ℝ) (hv : ∑ i, (v i) ^ 2 = 1) (lam : ℝ)
    (hvD : SzegedyDiscriminant P *ᵥ v = lam • v) : |lam| ≤ 1 := by
  let w : QState I := fun i => ((v i : ℂ))
  have hw : Normalized w := by
    unfold Normalized
    calc ∑ i, ‖w i‖ ^ 2 = ∑ i, (v i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show ‖w i‖ ^ 2 = (v i) ^ 2 by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring]
      _ = 1 := hv
  have hww : Inner w w = 1 := (normalized_iff_inner_self w).mp hw
  have hDw := discriminant_mulVec_complex P v lam hvD
  have hD_eq := gram_eq_discriminant_map P hP
  have hmain : Inner (SzegedyIsometry P *ᵥ w)
      (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w)) = (lam : ℂ) := by
    rw [show Inner (SzegedyIsometry P *ᵥ w)
          (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))
        = Inner w ((SzegedyIsometry P)ᴴ
            *ᵥ (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))) from
        inner_mulVec_left_rect (SzegedyIsometry P) w
          (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hD_eq, hDw]
    rw [Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
      hww, mul_one]
  have hTinner : Inner (SzegedyIsometry P *ᵥ w) (SzegedyIsometry P *ᵥ w) = 1 := by
    rw [show Inner (SzegedyIsometry P *ᵥ w) (SzegedyIsometry P *ᵥ w)
        = Inner w ((SzegedyIsometry P)ᴴ *ᵥ (SzegedyIsometry P *ᵥ w)) from
        inner_mulVec_left_rect (SzegedyIsometry P) w
          (SzegedyIsometry P *ᵥ w)]
    rw [Matrix.mulVec_mulVec, szegedyIsometry_conjTranspose_mul P hP,
      Matrix.one_mulVec, hww]
  have hTnorm : ‖toEuclidean_fromVec (SzegedyIsometry P *ᵥ w)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp
      ((normalized_iff_inner_self _).mpr hTinner)
  have hSinner : Inner (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))
      (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w)) = 1 := by
    have h := inner_applyGate swapGate_unitary
      (SzegedyIsometry P *ᵥ w) (SzegedyIsometry P *ᵥ w)
    rw [hTinner] at h
    simpa [ApplyGate] using h
  have hSnorm : ‖toEuclidean_fromVec (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp
      ((normalized_iff_inner_self _).mpr hSinner)
  have hcs : ‖Inner (SzegedyIsometry P *ᵥ w)
      (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w))‖ ≤ 1 := by
    rw [← inner_euclidean_fromVec]
    have := norm_inner_le_norm (𝕜 := ℂ)
      (toEuclidean_fromVec (SzegedyIsometry P *ᵥ w) : EuclideanSpace ℂ (I × I))
      (toEuclidean_fromVec (SwapGate *ᵥ (SzegedyIsometry P *ᵥ w)) : EuclideanSpace ℂ (I × I))
    rw [hTnorm, hSnorm, mul_one] at this
    exact this
  rw [hmain] at hcs
  simpa [Complex.norm_real, Real.norm_eq_abs] using hcs

/-- **Theorem 3.1 (arXiv:1908.03903v3, p.19).**  Let `D` be the discriminant operator
(Eq. (3.11)) and `W = S(2Π - I)` the walk (Eq. (3.10)).  For each real eigenvalue `λ`
of `D` with eigenvector `v`, the walk has the eigenvalues `λ ± i√(1-λ²)` on the explicit
vectors `(1 - μS)T|v⟩`; on the orthogonal complement of the embedding range the swap
eigen-directions contribute the `±1` eigenvalues.  Together with `paperWalk_unitary`,
this is the eigenvector-level content of the printed spectral statement.

Note: the paper writes `T` for the isometry `|x⟩ ↦ |φ_x⟩` of Eq. (3.19); the frozen
`SzegedyIsometry` is that map.  The complementary `±1` branch is realized by
`paperWalk_complement_eigenvector` (`W u = -u` for swap-symmetric kernel vectors, hence
`+u` for swap-antisymmetric ones). -/
theorem source_theorem_3_1 (P : I → I → ℝ) (hP : IsTransitionMatrix P)
    (v : I → ℝ) (hv : ∑ i, (v i) ^ 2 = 1) (lam : ℝ)
    (hvD : SzegedyDiscriminant P *ᵥ v = lam • v) :
    paperWalk P ∈ Matrix.unitaryGroup (I × I) ℂ ∧
    (∀ sgn : Bool,
      let μ : ℂ := (lam : ℂ)
        + (if sgn then Complex.I else -Complex.I) * ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)
      let w : QState I := fun i => ((v i : ℂ))
      paperWalk P *ᵥ (((1 : Matrix (I × I) (I × I) ℂ) - μ • SwapGate)
          *ᵥ (SzegedyIsometry P *ᵥ w))
        = μ • (((1 : Matrix (I × I) (I × I) ℂ) - μ • SwapGate)
          *ᵥ (SzegedyIsometry P *ᵥ w))) ∧
    (∀ u : QState (I × I), (SzegedyIsometry P)ᴴ *ᵥ u = 0 →
      SwapGate *ᵥ u = u → paperWalk P *ᵥ u = -u) := by
  have hlam : lam ^ 2 ≤ 1 := by
    have h := source_lemma_3_1 P hP v hv lam hvD
    nlinarith [abs_nonneg lam, sq_abs lam, le_abs_self lam, neg_le_abs lam]
  refine ⟨paperWalk_unitary P hP, fun sgn => ?_, fun u hker hS =>
    paperWalk_complement_eigenvector P u hker hS⟩
  exact paperWalk_eigenvector P hP v lam hlam hvD sgn

end Qatlib.Papers.ConvexVolEst19.MainResults.SpectralWalk
