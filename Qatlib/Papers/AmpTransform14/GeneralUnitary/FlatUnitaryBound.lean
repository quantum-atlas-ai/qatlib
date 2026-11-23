/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Qatlib.Foundations.OperatorErrors.OperatorError

@[expose] public section

/-!
# Flat general unitaries and marked-mass bounds

Section 2.14 of [Cornwell2014] bounds the point mass after a general unitary whose entries all
have modulus `N ^ -1/2`. This Euclidean version allows arbitrary complex phases: split a normalized
input state into a marked and an unmarked orthogonal part, apply Cauchy-Schwarz to each part, and
combine the two row estimates.  The dimension-free constant is outside every universal
quantifier, and all vector estimates use the `EuclideanSpace ℂ (Fin N)` norm.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Qatlib.Papers.AmpTransform14.GeneralUnitary

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Cauchy-Schwarz for a finite partial row-input pairing, expressed with Euclidean norms. -/
theorem abs_finset_sum_mul_le (a v : I → ℂ) (S : Finset I) :
    ‖∑ i ∈ S, a i * v i‖ ≤
      ‖(WithLp.toLp 2 fun i => if i ∈ S then v i else 0 : EuclideanSpace ℂ I)‖ *
        ‖(WithLp.toLp 2 fun i => if i ∈ S then starRingEnd ℂ (a i) else 0 :
            EuclideanSpace ℂ I)‖ := by
  have hin : ⟪(WithLp.toLp 2 fun i => if i ∈ S then v i else 0 : EuclideanSpace ℂ I),
      (WithLp.toLp 2 fun i => if i ∈ S then starRingEnd ℂ (a i) else 0 :
          EuclideanSpace ℂ I)⟫_ℂ =
      starRingEnd ℂ (∑ i ∈ S, a i * v i) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply]
    have hfun : ∀ x : I,
        (if x ∈ S then starRingEnd ℂ (a x) else 0) *
            starRingEnd ℂ (if x ∈ S then v x else 0) =
          if x ∈ S then starRingEnd ℂ (a x) * starRingEnd ℂ (v x) else 0 := by
      intro x
      by_cases hx : x ∈ S <;> simp [hx]
    rw [Finset.sum_congr (M := ℂ) (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
        (fun x _ => hfun x), Finset.sum_ite_mem_eq]
    rw [map_sum (starRingEnd ℂ)]
    exact Finset.sum_congr (M := ℂ) (s₁ := S) (s₂ := S) rfl fun i _ => by
      rw [map_mul (starRingEnd ℂ)]
  have hnorm : ‖∑ i ∈ S, a i * v i‖ =
      ‖⟪(WithLp.toLp 2 fun i => if i ∈ S then v i else 0 : EuclideanSpace ℂ I),
        (WithLp.toLp 2 fun i => if i ∈ S then starRingEnd ℂ (a i) else 0 :
            EuclideanSpace ℂ I)⟫_ℂ‖ := by
    calc
      ‖∑ i ∈ S, a i * v i‖ =
          ‖starRingEnd ℂ (∑ i ∈ S, a i * v i)‖ := (Complex.norm_conj _).symm
      _ = ‖⟪(WithLp.toLp 2 fun i => if i ∈ S then v i else 0 : EuclideanSpace ℂ I),
            (WithLp.toLp 2 fun i => if i ∈ S then starRingEnd ℂ (a i) else 0 :
              EuclideanSpace ℂ I)⟫_ℂ‖ := by rw [hin]
  rw [hnorm]
  exact norm_inner_le_norm _ _

/-- The Euclidean norm of a coordinate restriction is the square root of its squared mass. -/
theorem euclidean_norm_restrict (v : I → ℂ) (S : Finset I) :
    ‖(WithLp.toLp 2 fun i => if i ∈ S then v i else 0 : EuclideanSpace ℂ I)‖ =
      Real.sqrt (∑ i ∈ S, ‖v i‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  calc
    ∑ i, ‖if i ∈ S then v i else 0‖ ^ 2 = ∑ i, if i ∈ S then ‖v i‖ ^ 2 else 0 := by
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    _ = ∑ i ∈ S, ‖v i‖ ^ 2 := Finset.sum_ite_mem_eq S fun i => ‖v i‖ ^ 2

/-- For a normalized state and a flat-modulus unitary, each output Born mass is bounded by the
squared sum of the marked and unmarked Cauchy–Schwarz estimates. The uniform constant is one.
When all input mass is marked, the upper bound specializes to the marked fraction. -/
theorem generalUnitaryFlatBound :
    ∃ C > 0, C = 1 ∧ ∀ (N : ℕ) (_hN : 0 < N),
      ∀ U : Matrix (Fin N) (Fin N) ℂ,
        U ∈ Matrix.unitaryGroup (Fin N) ℂ →
        (∀ i j, ‖U i j‖ = (Real.sqrt (N : ℝ))⁻¹) →
        ∀ (A : Finset (Fin N)) (ψ : EuclideanSpace ℂ (Fin N)) (y : Fin N),
          ‖ψ‖ = 1 →
          ‖U‖ ≤ 1 ∧
            ‖∑ j, U y j * ψ j‖ ^ 2 ≤
              C * ((Real.sqrt (∑ j ∈ A, ‖ψ j‖ ^ 2) *
                    Real.sqrt ((A.card : ℝ) / N)) +
                (Real.sqrt (1 - ∑ j ∈ A, ‖ψ j‖ ^ 2) *
                  Real.sqrt (((N : ℝ) - A.card) / N))) ^ 2 := by
  refine ⟨1, by norm_num, rfl, ?_⟩
  intro N _hN U hU hflat A ψ y hψ
  have hentry (j : Fin N) : ‖U y j‖ ^ 2 = 1 / (N : ℝ) := by
    rw [hflat y j]
    field_simp
    rw [sq]
    exact_mod_cast (Real.mul_self_sqrt (Nat.cast_nonneg N)).symm
  have hflatMass (S : Finset (Fin N)) :
      ∑ j ∈ S, ‖U y j‖ ^ 2 = (S.card : ℝ) / N := by
    simp_rw [hentry]
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hcompCard : ((Aᶜ.card : ℕ) : ℝ) = (N : ℝ) - A.card := by
    have hle : A.card ≤ N := by
      simpa [Fintype.card_fin] using Finset.card_le_univ A
    rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub hle]
  have hmass : ∑ j ∈ Aᶜ, ‖ψ j‖ ^ 2 = 1 - ∑ j ∈ A, ‖ψ j‖ ^ 2 := by
    have htotal : (∑ j ∈ A, ‖ψ j‖ ^ 2) + ∑ j ∈ Aᶜ, ‖ψ j‖ ^ 2 = 1 := by
      rw [Finset.sum_add_sum_compl A (fun j => ‖ψ j‖ ^ 2),
        ← EuclideanSpace.norm_sq_eq ψ, hψ]
      norm_num
    linarith
  have hA : ‖∑ j ∈ A, U y j * ψ j‖ ≤
      Real.sqrt (∑ j ∈ A, ‖ψ j‖ ^ 2) * Real.sqrt ((A.card : ℝ) / N) := by
    calc
      ‖∑ j ∈ A, U y j * ψ j‖ ≤
          ‖(WithLp.toLp 2 fun j => if j ∈ A then ψ j else 0 :
              EuclideanSpace ℂ (Fin N))‖ *
            ‖(WithLp.toLp 2 fun j => if j ∈ A then starRingEnd ℂ (U y j) else 0 :
                EuclideanSpace ℂ (Fin N))‖ :=
        abs_finset_sum_mul_le (fun j => U y j) (fun j => ψ j) A
      _ = Real.sqrt (∑ j ∈ A, ‖ψ j‖ ^ 2) *
            Real.sqrt (∑ j ∈ A, ‖U y j‖ ^ 2) := by
        rw [euclidean_norm_restrict, euclidean_norm_restrict]
        congr 1
        exact congrArg Real.sqrt <| Finset.sum_congr (M := ℝ) (s₁ := A) (s₂ := A) rfl
          fun j _ => by rw [Complex.norm_conj]
      _ = Real.sqrt (∑ j ∈ A, ‖ψ j‖ ^ 2) *
            Real.sqrt ((A.card : ℝ) / N) := by
        rw [hflatMass]
  have hB : ‖∑ j ∈ Aᶜ, U y j * ψ j‖ ≤
      Real.sqrt (∑ j ∈ Aᶜ, ‖ψ j‖ ^ 2) *
        Real.sqrt (((N : ℝ) - A.card) / N) := by
    calc
      ‖∑ j ∈ Aᶜ, U y j * ψ j‖ ≤
          ‖(WithLp.toLp 2 fun j => if j ∈ Aᶜ then ψ j else 0 :
              EuclideanSpace ℂ (Fin N))‖ *
            ‖(WithLp.toLp 2 fun j => if j ∈ Aᶜ then starRingEnd ℂ (U y j) else 0 :
                EuclideanSpace ℂ (Fin N))‖ :=
        abs_finset_sum_mul_le (fun j => U y j) (fun j => ψ j) Aᶜ
      _ = Real.sqrt (∑ j ∈ Aᶜ, ‖ψ j‖ ^ 2) *
            Real.sqrt (∑ j ∈ Aᶜ, ‖U y j‖ ^ 2) := by
        rw [euclidean_norm_restrict, euclidean_norm_restrict]
        congr 1
        exact congrArg Real.sqrt <| Finset.sum_congr (M := ℝ) (s₁ := Aᶜ) (s₂ := Aᶜ) rfl
          fun j _ => by rw [Complex.norm_conj]
      _ = Real.sqrt (∑ j ∈ Aᶜ, ‖ψ j‖ ^ 2) *
            Real.sqrt (((N : ℝ) - A.card) / N) := by
        rw [hflatMass, hcompCard]
  have hsumSplit : ∑ j, U y j * ψ j =
      (∑ j ∈ A, U y j * ψ j) + ∑ j ∈ Aᶜ, U y j * ψ j := by
    rw [← Finset.sum_add_sum_compl A]
  have htri : ‖∑ j, U y j * ψ j‖ ≤
      (Real.sqrt (∑ j ∈ A, ‖ψ j‖ ^ 2) * Real.sqrt ((A.card : ℝ) / N)) +
        (Real.sqrt (1 - ∑ j ∈ A, ‖ψ j‖ ^ 2) *
          Real.sqrt (((N : ℝ) - A.card) / N)) := by
    rw [hmass] at hB
    rw [hsumSplit]
    exact (norm_add_le _ _).trans (add_le_add hA hB)
  refine ⟨Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one hU, ?_⟩
  calc
    ‖∑ j, U y j * ψ j‖ ^ 2 ≤
        ((Real.sqrt (∑ j ∈ A, ‖ψ j‖ ^ 2) * Real.sqrt ((A.card : ℝ) / N)) +
          (Real.sqrt (1 - ∑ j ∈ A, ‖ψ j‖ ^ 2) *
            Real.sqrt (((N : ℝ) - A.card) / N))) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ = 1 * ((Real.sqrt (∑ j ∈ A, ‖ψ j‖ ^ 2) * Real.sqrt ((A.card : ℝ) / N)) +
          (Real.sqrt (1 - ∑ j ∈ A, ‖ψ j‖ ^ 2) *
            Real.sqrt (((N : ℝ) - A.card) / N))) ^ 2 := by ring

end Qatlib.Papers.AmpTransform14.GeneralUnitary
