/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma1Stat

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore

theorem bhmt_amplitude_amplification_lemma1_conjugation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H ≃ₗᵢ[ℂ] H) (ket0 v : H) :
    A (A.symm v - (2 * inner ℂ ket0 (A.symm v)) • ket0)
      = v - (2 * inner ℂ (A ket0) v) • (A ket0) := by
  rw [map_sub, map_smul, LinearIsometryEquiv.apply_symm_apply, ← A.inner_map_eq_flip]

theorem bhmt_amplitude_amplification_lemma1 :
    ∀ (X : Set ℤ) (hzero : (0 : ℤ) ∈ X)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis X ℂ H) (χ : ℤ → Bool) (A : H ≃ₗᵢ[ℂ] H),
  let ket0 : H := basis ⟨0, hzero⟩;
  let G : Submodule ℂ H :=
    (Submodule.span ℂ
      (Set.image (fun i : X => basis i) {i : X | χ (i : ℤ) = true})).topologicalClosure;
  let P : H →L[ℂ] H := G.starProjection;
  let ψ : H := A ket0;
  let ψ₁ : H := P ψ;
  let ψ₀ : H := ψ - ψ₁;
  let a : ℝ := (inner ℂ ψ₁ ψ₁).re;
  let S₀ : H → H := fun v => v - (2 * inner ℂ ket0 v) • ket0;
  let Sχ : H → H := fun v => v - (2 : ℂ) • P v;
  let Q : H → H := fun v => -(A (S₀ (A.symm (Sχ v))));
  Q ψ₁ = (1 - 2 * (a : ℂ)) • ψ₁ - (2 * (a : ℂ)) • ψ₀ ∧
  Q ψ₀ = (2 * (1 - (a : ℂ))) • ψ₁ + (1 - 2 * (a : ℂ)) • ψ₀ := by
  intro X hzero H _ _ _ basis χ A ket0 G P ψ ψ₁ ψ₀ a S₀ Sχ Q

  have hψ₁G : ψ₁ ∈ G := Submodule.starProjection_apply_mem G ψ
  have hψ₀orth : ψ₀ ∈ Gᗮ := Submodule.sub_starProjection_mem_orthogonal ψ
  have hPψ₁ : P ψ₁ = ψ₁ := Submodule.starProjection_eq_self_iff.mpr hψ₁G
  have hPψ₀ : P ψ₀ = 0 :=
    Submodule.eq_starProjection_of_mem_orthogonal' G.zero_mem hψ₀orth (zero_add ψ₀).symm
  have hinner₀₁ : inner ℂ ψ₀ ψ₁ = 0 :=
    (Submodule.mem_orthogonal' G ψ₀).1 hψ₀orth ψ₁ hψ₁G
  have hinner₁₀ : inner ℂ ψ₁ ψ₀ = 0 :=
    (Submodule.mem_orthogonal G ψ₀).1 hψ₀orth ψ₁ hψ₁G
  have hsum : ψ = ψ₁ + ψ₀ := (add_sub_cancel ψ₁ ψ).symm

  have hket0norm : ‖ket0‖ = 1 := basis.orthonormal.norm_eq_one ⟨0, hzero⟩
  have hψnorm : ‖ψ‖ = 1 := by
    rw [show (ψ : H) = A ket0 from rfl, LinearIsometryEquiv.norm_map, hket0norm]

  have hare : Complex.re (inner ℂ ψ₁ ψ₁) = a := rfl
  have hexp : inner ℂ ψ ψ = inner ℂ ψ₁ ψ₁ + inner ℂ ψ₀ ψ₀ := by
    rw [hsum, inner_add_add_self, hinner₁₀, hinner₀₁]; ring
  have h1 : Complex.re (inner ℂ ψ ψ) = 1 := by
    have h2 := norm_sq_eq_re_inner (𝕜 := ℂ) ψ
    rw [hψnorm, one_pow] at h2
    exact h2.symm
  have hresum : Complex.re (inner ℂ ψ₁ ψ₁) + Complex.re (inner ℂ ψ₀ ψ₀) = 1 := by
    rw [← Complex.add_re, ← hexp, h1]
  have hn₀ : Complex.re (inner ℂ ψ₀ ψ₀) = 1 - a := by linarith
  have hself₀ : inner ℂ ψ₀ ψ₀ = 1 - (a : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← hn₀]
    exact (inner_self_ofReal_re ψ₀).symm
  have hov₁ : inner ℂ ψ ψ₁ = (a : ℂ) := by
    rw [hsum, inner_add_left, hinner₀₁, add_zero, ← hare]
    exact (inner_self_ofReal_re ψ₁).symm
  have hov₀ : inner ℂ ψ ψ₀ = 1 - (a : ℂ) := by
    rw [hsum, inner_add_left, hinner₁₀, zero_add]
    exact hself₀

  have hSχψ₁ : Sχ ψ₁ = -ψ₁ := by
    rw [show Sχ ψ₁ = ψ₁ - (2 : ℂ) • P ψ₁ from rfl, hPψ₁]
    module
  have hSχψ₀ : Sχ ψ₀ = ψ₀ := by
    rw [show Sχ ψ₀ = ψ₀ - (2 : ℂ) • P ψ₀ from rfl, hPψ₀, smul_zero, sub_zero]

  have hQψ₁ : Q ψ₁ = -(Sχ ψ₁ - (2 * inner ℂ ψ (Sχ ψ₁)) • ψ) := by
    rw [show Q ψ₁ = -(A (S₀ (A.symm (Sχ ψ₁)))) from rfl,
      show S₀ (A.symm (Sχ ψ₁))
          = A.symm (Sχ ψ₁) - (2 * inner ℂ ket0 (A.symm (Sχ ψ₁))) • ket0 from rfl,
      show (ψ : H) = A ket0 from rfl]
    exact congrArg (fun w => -w) (bhmt_amplitude_amplification_lemma1_conjugation A ket0 (Sχ ψ₁))
  have hQψ₀ : Q ψ₀ = -(Sχ ψ₀ - (2 * inner ℂ ψ (Sχ ψ₀)) • ψ) := by
    rw [show Q ψ₀ = -(A (S₀ (A.symm (Sχ ψ₀)))) from rfl,
      show S₀ (A.symm (Sχ ψ₀))
          = A.symm (Sχ ψ₀) - (2 * inner ℂ ket0 (A.symm (Sχ ψ₀))) • ket0 from rfl,
      show (ψ : H) = A ket0 from rfl]
    exact congrArg (fun w => -w) (bhmt_amplitude_amplification_lemma1_conjugation A ket0 (Sχ ψ₀))

  refine ⟨?_, ?_⟩
  · rw [hQψ₁, hSχψ₁, inner_neg_right, hov₁, hsum]
    module
  · rw [hQψ₀, hSχψ₀, hov₀, hsum]
    module

end Qatlib.Concepts.AmplitudeCore.AmplifyCore
