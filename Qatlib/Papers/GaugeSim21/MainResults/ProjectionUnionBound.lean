/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaugeSim21.MainResults.TruncationModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

set_option backward.isDefEq.respectTransparency false

/-!
# Union Bound for Complementary Commuting Projections

This module formalizes Lemma 8 of Tong, Albert, McClean, Preskill, and Su on the
operator-norm union bound for complementary commuting orthogonal projections:
given commuting Hermitian idempotents `P_1, ..., P_N` and an operator `A`,
`‖(1 - ∏_μ (1 - P_μ)) A‖^2 ≤ ∑_μ ‖P_μ A‖^2`.

## Main statements

* `productProj`: ordered product `∏_μ P_μ` of per-mode operators.
* `allComplement`: complementary projection `1 - ∏_μ (1 - P_μ)`.
* `lemma8_unionBound`: Lemma 8, `‖allComplement Pc * A‖ ^ 2 ≤ ∑ μ, ‖Pc μ * A‖ ^ 2`.

## References

* [Tong et al., 2022][TongEtAl2022], Lemma 8, Eqs. (72)--(74), p. 26.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.GaugeSim21.MainResults.ProjectionUnionBound

variable {I : Type} [Fintype I] [DecidableEq I]

local notation "𝒯" => Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)

/-- The product of the per-mode projections `∏_ν Π^{(ν)}_S`. -/
def productProj {N : ℕ} (P : Fin N → Matrix I I ℂ) : Matrix I I ℂ :=
  (List.finRange N).foldr (fun μ acc => P μ * acc) 1

/-- `Π̄^all_S = I − ∏_ν (I − P_ν)` where `P_ν = Π̄^{(ν)}_S`. -/
def allComplement {N : ℕ} (Pc : Fin N → Matrix I I ℂ) : Matrix I I ℂ :=
  1 - (List.finRange N).foldr (fun μ acc => (1 - Pc μ) * acc) 1

private def complementProduct (Ps : List (Matrix I I ℂ)) : Matrix I I ℂ :=
  Ps.foldr (fun Q acc => (1 - Q) * acc) 1

private lemma commute_complementProduct (Ps : List (Matrix I I ℂ)) (R : Matrix I I ℂ)
    (h : ∀ Q ∈ Ps, Commute R Q) : Commute R (complementProduct Ps) := by
  induction Ps with
  | nil => exact Commute.one_right R
  | cons Q Ps ih =>
    exact ((Commute.one_right R).sub_right (h Q (by simp))).mul_right
      (ih fun S hS => h S (by simp [hS]))

private lemma complementProduct_projection (Ps : List (Matrix I I ℂ))
    (hp : ∀ Q ∈ Ps, Q * Q = Q) (hh : ∀ Q ∈ Ps, Qᴴ = Q)
    (hc : ∀ Q ∈ Ps, ∀ R ∈ Ps, Commute Q R) :
    complementProduct Ps * complementProduct Ps = complementProduct Ps ∧
      (complementProduct Ps)ᴴ = complementProduct Ps := by
  induction Ps with
  | nil => simp [complementProduct]
  | cons Q Ps ih =>
    obtain ⟨hpid, hph⟩ := ih (fun R hR => hp R (by simp [hR]))
      (fun R hR => hh R (by simp [hR]))
      (fun R hR S hS => hc R (by simp [hR]) S (by simp [hS]))
    have hQ := hp Q (by simp)
    have hQh := hh Q (by simp)
    have hQP := commute_complementProduct Ps Q (fun R hR => hc Q (by simp) R (by simp [hR]))
    have hCP := (Commute.one_left (complementProduct Ps)).sub_left hQP
    change ((1 - Q) * complementProduct Ps) * ((1 - Q) * complementProduct Ps) =
      (1 - Q) * complementProduct Ps ∧ _
    constructor
    · calc
        _ = ((1 - Q) * (1 - Q)) * (complementProduct Ps * complementProduct Ps) :=
          hCP.symm.mul_mul_mul_comm _ _
        _ = (1 - Q) * complementProduct Ps := by
          rw [hpid, show (1 - Q) * (1 - Q) = 1 - Q by noncomm_ring [hQ]]
    · change ((1 - Q) * complementProduct Ps)ᴴ = (1 - Q) * complementProduct Ps
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        hph, hQh, hCP.eq]

private lemma inner_eq_zero_of_mul_eq_zero (B D : Matrix I I ℂ)
    (h : Bᴴ * D = 0) (x y : EuclideanSpace ℂ I) :
    inner ℂ (𝒯 B x) (𝒯 D y) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hBD : (𝒯 B).adjoint * 𝒯 D = 0 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← map_mul,
      Matrix.star_eq_conjTranspose, h, map_zero]
  change inner ℂ x (((𝒯 B).adjoint * 𝒯 D) y) = 0
  rw [hBD, _root_.zero_apply, inner_zero_right]

private lemma projection_apply_sq_le (P : Matrix I I ℂ) (hp : P * P = P)
    (hh : Pᴴ = P) (y : EuclideanSpace ℂ I) :
    ‖𝒯 P y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  have ho := inner_eq_zero_of_mul_eq_zero P (1 - P)
    (by rw [hh, mul_sub, mul_one, hp, sub_self]) y y
  have hs : 𝒯 P y + 𝒯 (1 - P) y = y := by
    rw [← _root_.add_apply, ← map_add, add_sub_cancel,
      map_one, one_apply_eq_self]
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
  rw [hs] at hn
  nlinarith [sq_nonneg ‖𝒯 (1 - P) y‖]

private lemma complementProduct_apply_sq_le (Ps : List (Matrix I I ℂ))
    (hp : ∀ Q ∈ Ps, Q * Q = Q) (hh : ∀ Q ∈ Ps, Qᴴ = Q)
    (hc : ∀ Q ∈ Ps, ∀ R ∈ Ps, Commute Q R) (A : Matrix I I ℂ)
    (x : EuclideanSpace ℂ I) :
    ‖𝒯 ((1 - complementProduct Ps) * A) x‖ ^ 2 ≤
      (Ps.map (fun Q => ‖Q * A‖ ^ 2)).sum * ‖x‖ ^ 2 := by
  induction Ps with
  | nil => simp [complementProduct]
  | cons Q Ps ih =>
    have hp' := fun R hR => hp R (List.mem_cons_of_mem Q hR)
    have hh' := fun R hR => hh R (List.mem_cons_of_mem Q hR)
    have hc' := fun R hR S hS => hc R (List.mem_cons_of_mem Q hR)
      S (List.mem_cons_of_mem Q hS)
    obtain ⟨hpid, hph⟩ := complementProduct_projection Ps hp' hh' hc'
    have hQP := commute_complementProduct Ps Q
      (fun R hR => hc Q (by simp) R (by simp [hR]))
    have ho := inner_eq_zero_of_mul_eq_zero (1 - complementProduct Ps)
      (Q * complementProduct Ps) (by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hph,
          hQP.eq, ← mul_assoc, sub_mul, one_mul, hpid, sub_self, zero_mul])
      (𝒯 A x) (𝒯 A x)
    have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
    have hv : ‖𝒯 (Q * complementProduct Ps)
        (𝒯 A x)‖ ^ 2 ≤ ‖Q * A‖ ^ 2 * ‖x‖ ^ 2 := by
      calc
        _ = ‖𝒯 (complementProduct Ps) (𝒯 (Q * A) x)‖ ^ 2 := by
          rw [hQP.eq, map_mul, mul_apply_eq_comp, map_mul, mul_apply_eq_comp]
        _ ≤ ‖𝒯 (Q * A) x‖ ^ 2 :=
          projection_apply_sq_le _ hpid hph _
        _ ≤ (‖Q * A‖ * ‖x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) ((𝒯 (Q * A)).le_opNorm x) 2
        _ = _ := mul_pow _ _ _
    have hsplit : 1 - complementProduct (Q :: Ps) =
        (1 - complementProduct Ps) + Q * complementProduct Ps := by
      simp only [complementProduct, List.foldr_cons]
      noncomm_ring
    rw [hsplit, add_mul, map_add, _root_.add_apply]
    simp only [map_mul, mul_apply_eq_comp] at hn ⊢
    simp only [List.map_cons, List.sum_cons, add_mul]
    have hi := ih hp' hh' hc'
    simp only [map_mul, mul_apply_eq_comp] at hi hv
    nlinarith

/-- Lemma 8 (Eq. (72)): union bound for complementary commuting projections. -/
theorem lemma8_unionBound {N : ℕ} (Pc : Fin N → Matrix I I ℂ) (A : Matrix I I ℂ)
    (hproj : ∀ μ, Pc μ * Pc μ = Pc μ)
    (hherm : ∀ μ, (Pc μ)ᴴ = Pc μ)
    (hcomm : ∀ μ ν, Pc μ * Pc ν = Pc ν * Pc μ) :
    ‖allComplement Pc * A‖ ^ 2 ≤ ∑ μ : Fin N, ‖Pc μ * A‖ ^ 2 := by
  let Ps := (List.finRange N).map Pc
  have hp : ∀ Q ∈ Ps, Q * Q = Q := by
    intro Q hQ
    obtain ⟨μ, _, rfl⟩ := List.mem_map.mp hQ
    exact hproj μ
  have hh : ∀ Q ∈ Ps, Qᴴ = Q := by
    intro Q hQ
    obtain ⟨μ, _, rfl⟩ := List.mem_map.mp hQ
    exact hherm μ
  have hc : ∀ Q ∈ Ps, ∀ R ∈ Ps, Commute Q R := by
    intro Q hQ R hR
    obtain ⟨μ, _, rfl⟩ := List.mem_map.mp hQ
    obtain ⟨ν, _, rfl⟩ := List.mem_map.mp hR
    exact hcomm μ ν
  have hs : 0 ≤ (Ps.map (fun Q => ‖Q * A‖ ^ 2)).sum := by
    exact List.sum_nonneg (fun r hr => by
      obtain ⟨Q, _, rfl⟩ := List.mem_map.mp hr
      positivity)
  have hb : ‖(1 - complementProduct Ps) * A‖ ≤
      Real.sqrt (Ps.map (fun Q => ‖Q * A‖ ^ 2)).sum := by
    rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hs]
    exact complementProduct_apply_sq_le Ps hp hh hc A x
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [Real.sq_sqrt hs] at hb2
  simpa [allComplement, complementProduct, Ps, List.foldr_map, List.map_map,
    Function.comp_def, Fin.sum_univ_def] using hb2

end Qatlib.Papers.GaugeSim21.MainResults.ProjectionUnionBound
