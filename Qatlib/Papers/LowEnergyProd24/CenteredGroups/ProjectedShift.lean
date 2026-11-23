/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.MatrixGeometry.AffineCenter
public import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.Projectors
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Centered groups and the projected leading term

This module gives a restricted bridge for the non-PSD centered-group discussion in
[HejaziZiniArrazola2024].  Scalar shifts of Hermitian group operators leave every nonempty
nested commutator unchanged.  For a fixed spectral cutoff it also defines the shifted compressed
scale as the largest, over groups, of the minimal operator norm of a compressed shifted group.
The main result chooses centers at this scale and bounds the time-integral of a projected nested
commutator of the already-compressed shifted groups by
`(2 ^ p / (p + 1)) * shiftedScale ^ (p + 1) * s ^ (p + 1)` for positive order `p`.

The final bound is intentionally labeled as restricted rather than as the source's full non-PSD
step-error theorem: the norm estimate is applied after compressing every factor.  The source's
nested commutator compresses only the final operator, so its cross-energy leakage terms are not
included here. Matrix norms are induced by continuous linear maps on Euclidean space.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.LowEnergyProd24.CenteredGroups

open Qatlib.Foundations.MatrixGeometry.AffineCenter
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff

variable {I : Type*} [Fintype I] [DecidableEq I] {M : ℕ}

/-- The commutator `A * B - B * A`. -/
def bracket (A B : Matrix I I ℂ) : Matrix I I ℂ := A*B-B*A

/-- A nested commutator with seed operator `X`, taking outer brackets in list order. -/
def nestedFrom (X : Matrix I I ℂ) : List (Matrix I I ℂ) → Matrix I I ℂ :=
  fun xs => xs.foldl (fun Y A => bracket A Y) X

/-- The nested commutator with the group `seed` as its innermost factor. -/
def nestedCommutator (A : Fin M → Matrix I I ℂ) (seed : Fin M)
    (xs : List (Fin M)) : Matrix I I ℂ := nestedFrom (A seed) (xs.map A)

/-- Adding scalar identity shifts to a family of operators leaves every nonempty nested
commutator unchanged. -/
theorem nestedCommutator_shift (A : Fin M → Matrix I I ℂ) (c : Fin M → ℝ)
    (seed : Fin M) (xs : List (Fin M)) (hxs : xs ≠ []) :
    nestedCommutator (fun m => A m+(c m : ℂ) • 1) seed xs =
      nestedCommutator A seed xs := by
  have key (B X : Matrix I I ℂ) (r : ℝ) :
      bracket (B+(r : ℂ) • 1) X = bracket B X := by
    unfold bracket
    noncomm_ring
  have keyRight (B X : Matrix I I ℂ) (r : ℝ) :
      bracket B (X+(r : ℂ) • 1) = bracket B X := by
    unfold bracket
    noncomm_ring
  induction xs generalizing seed with
  | nil => exact (hxs rfl).elim
  | cons m ys ih =>
    clear hxs ih
    have hfold (X Y : Matrix I I ℂ) (hXY : X=Y) :
        List.foldl (fun Z B => bracket B Z) X
            (ys.map (fun n => A n+(c n : ℂ) • 1)) =
          List.foldl (fun Z B => bracket B Z) Y (ys.map A) := by
      subst hXY
      induction ys generalizing X with
      | nil => rfl
      | cons n zs ihfold =>
        simp only [List.map_cons, List.foldl_cons, key]
        exact ihfold _
    simp only [nestedCommutator, nestedFrom, List.map_cons, List.foldl_cons]
    rw [key]
    exact hfold _ _ (keyRight (A m) (A seed) (c seed))

/-- The compression of a shifted Hermitian group at a spectral cutoff of `H`. -/
def shiftedCompression (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ)
    (A : Matrix I I ℂ) (c : ℝ) : Matrix I I ℂ :=
  low H hH Δ*(A+(c : ℂ) • 1)*low H hH Δ

/-- The infimum, over real shifts, of the L2-operator norm of a compressed shifted group. -/
def shiftedRadius (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ)
    (A : Matrix I I ℂ) : ℝ :=
  sInf (Set.range fun c : ℝ => ‖shiftedCompression H hH Δ A c‖)

/-- The non-PSD shifted compressed scale: the largest shifted radius in a finite group family. -/
def shiftedScale [Nonempty (Fin M)] (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ)
    (A : Fin M → Matrix I I ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun m => shiftedRadius H hH Δ (A m)

/-- Every shifted compressed radius is nonnegative because it is an infimum of operator norms. -/
theorem shiftedRadius_nonneg (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ)
    (A : Matrix I I ℂ) : 0 ≤ shiftedRadius H hH Δ A := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨c, rfl⟩
  exact norm_nonneg _

/-- The finite supremum of nonnegative shifted radii is itself nonnegative. -/
theorem shiftedScale_nonneg [Nonempty (Fin M)] (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ)
    (A : Fin M → Matrix I I ℂ) : 0 ≤ shiftedScale H hH Δ A := by
  show 0 ≤ Finset.univ.sup' Finset.univ_nonempty
    fun m => shiftedRadius H hH Δ (A m)
  obtain ⟨m⟩ := ‹Nonempty (Fin M)›
  exact (shiftedRadius_nonneg H hH Δ (A m)).trans
    (Finset.le_sup' (f := fun m => shiftedRadius H hH Δ (A m))
      (Finset.mem_univ m))

/-- The shifted compressed operator is the affine line `P A P + c • P`. -/
theorem shiftedCompression_eq (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ)
    (A : Matrix I I ℂ) (c : ℝ) :
    shiftedCompression H hH Δ A c =
      low H hH Δ*A*low H hH Δ+(c : ℂ) • low H hH Δ := by
  unfold shiftedCompression
  have hpp : low H hH Δ*low H hH Δ=low H hH Δ := low_square H hH Δ
  noncomm_ring [hpp]

/-- A nonzero spectral projector has L2-operator norm one. -/
theorem low_norm_eq_one (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ)
    (hP : low H hH Δ ≠ 0) : ‖low H hH Δ‖ = 1 := by
  have hsquare := Matrix.l2_opNorm_conjTranspose_mul_self (low H hH Δ)
  rw [low_hermitian, low_square] at hsquare
  have hnn : 0 ≤ ‖low H hH Δ‖ := norm_nonneg _
  rcases eq_zero_or_one_of_sq_eq_self (by simpa [sq] using hsquare.symm) with h0 | h1
  · exact absurd (norm_eq_zero.mp h0) hP
  · exact h1

/-- Some real shift attains the shifted compressed radius of one group. -/
theorem exists_shiftedCompression_eq_radius (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ)
    (A : Matrix I I ℂ) :
    ∃ c : ℝ, ‖shiftedCompression H hH Δ A c‖ = shiftedRadius H hH Δ A := by
  by_cases hP : low H hH Δ = 0
  · refine ⟨0, ?_⟩
    have hzero (r : ℝ) : shiftedCompression H hH Δ A r = 0 := by
      unfold shiftedCompression
      rw [hP]
      simp
    have hbdd : BddBelow (Set.range fun r : ℝ =>
        ‖shiftedCompression H hH Δ A r‖) :=
      ⟨0, by
        rintro _ ⟨r, rfl⟩
        exact norm_nonneg _⟩
    refine le_antisymm ?_ ?_
    · apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨r, rfl⟩
      rw [hzero]
      simp
    · exact csInf_le hbdd (Set.mem_range_self 0)
  · have hnorm := low_norm_eq_one H hH Δ hP
    obtain ⟨c, hc⟩ := exists_affine_center
      (low H hH Δ*A*low H hH Δ) (low H hH Δ) hnorm
    refine ⟨c, ?_⟩
    have he (r : ℝ) : shiftedCompression H hH Δ A r =
        (low H hH Δ*A*low H hH Δ)+(r : ℝ) • low H hH Δ := by
      rw [shiftedCompression_eq]
      simp
    rw [he]
    have hx : ‖low H hH Δ*A*low H hH Δ+(c : ℝ) • low H hH Δ‖ =
        shiftedRadius H hH Δ A := by
      unfold shiftedRadius shiftedCompression
      have hbdd : BddBelow (Set.range fun r : ℝ =>
          ‖shiftedCompression H hH Δ A r‖) :=
        ⟨0, by
          rintro _ ⟨r, rfl⟩
          exact norm_nonneg _⟩
      refine le_antisymm ?_ ?_
      · apply le_csInf (Set.range_nonempty _)
        rintro _ ⟨r, rfl⟩
        show ‖low H hH Δ*A*low H hH Δ+(c : ℝ) • low H hH Δ‖ ≤
          ‖low H hH Δ*(A+(r : ℂ) • 1)*low H hH Δ‖
        have hrr : ‖low H hH Δ*(A+(r : ℂ) • 1)*low H hH Δ‖ =
            ‖low H hH Δ*A*low H hH Δ+(r : ℝ) • low H hH Δ‖ :=
          congrArg norm (shiftedCompression_eq H hH Δ A r)
        rw [hrr]
        exact hc r
      · exact csInf_le hbdd
          (Set.mem_range.mpr ⟨c, by
            have hcc : ‖low H hH Δ*(A+(c : ℂ) • 1)*low H hH Δ‖ =
                ‖low H hH Δ*A*low H hH Δ+(c : ℝ) • low H hH Δ‖ :=
              congrArg norm (shiftedCompression_eq H hH Δ A c)
            exact hcc⟩)
    exact hx

/-- A real center can be chosen for every group to attain its shifted compressed radius. -/
theorem exists_shifted_centers (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ)
    (A : Fin M → Matrix I I ℂ) :
    ∃ c : Fin M → ℝ, ∀ m, ‖shiftedCompression H hH Δ (A m) (c m)‖ =
      shiftedRadius H hH Δ (A m) := by
  choose c hc using fun m => exists_shiftedCompression_eq_radius H hH Δ (A m)
  exact ⟨c, hc⟩

/-- A nested commutator of operators is bounded by two factors per bracket times the product of
the factor norms. -/
theorem nestedFrom_norm_le (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) :
    ‖nestedFrom X xs‖ ≤
      2^xs.length*‖X‖*((xs.map norm).prod) := by
  induction xs generalizing X with
  | nil => simp [nestedFrom]
  | cons A ys ih =>
    rw [nestedFrom, List.foldl_cons, List.map_cons, List.prod_cons, List.length_cons]
    have hstep : ‖bracket A X‖ ≤ 2*‖A‖*‖X‖ := by
      calc
        ‖bracket A X‖ ≤ ‖A*X‖+‖X*A‖ := by
          unfold bracket
          exact norm_sub_le _ _
        _ ≤ ‖A‖*‖X‖+‖X‖*‖A‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ = 2*‖A‖*‖X‖ := by ring
    calc
      ‖nestedFrom (bracket A X) ys‖ ≤
          2^ys.length*‖bracket A X‖*((ys.map norm).prod) := ih _
      _ ≤ 2^ys.length*(2*‖A‖*‖X‖)*((ys.map norm).prod) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hstep (by positivity))
            (List.prod_nonneg fun x hx => by
              obtain ⟨Y, _, rfl⟩ := List.mem_map.mp hx
              exact norm_nonneg Y)
      _ = _ := by ring

/-- The product of finitely many matrix L2-operator norms is nonnegative. -/
theorem matrix_norm_list_prod_nonneg (xs : List (Matrix I I ℂ)) :
    0 ≤ (xs.map norm).prod := by
  induction xs with
  | nil => simp
  | cons A ys ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_nonneg (norm_nonneg A) ih

/-- The product of shifted compressed group norms is nonnegative. -/
theorem shifted_norm_prod_nonneg (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ)
    (A : Fin M → Matrix I I ℂ) (c : Fin M → ℝ) (xs : List (Fin M)) :
    0 ≤ ((xs.map fun x =>
      ‖shiftedCompression H hH Δ (A x) (c x)‖).prod) := by
  induction xs with
  | nil => simp
  | cons x ys ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_nonneg (norm_nonneg _) ih

/-- The exact scalar power integral used by the projected leading term. -/
theorem leading_power_integral_eq (p : ℕ) (s : ℝ) (X : Matrix I I ℂ) :
    ∫ σ in (0 : ℝ)..s, (σ^p : ℝ) • X =
      (s^(p+1)/(p+1 : ℕ)) • X := by
  rw [intervalIntegral.integral_smul_const, integral_pow]
  simp

/-- L2-operator bound for the positive-order leading integral of an already-compressed
nested commutator. The coefficient `2 ^ p / (p + 1)` depends only on the order. -/
theorem projected_shifted_leading_bound [Nonempty I] [Nonempty (Fin M)]
    (H : Matrix I I ℂ)
    (hH : H.IsHermitian) (A : Fin M → Matrix I I ℂ) (Δ : ℝ) (c : Fin M → ℝ)
    (hc : ∀ m, ‖shiftedCompression H hH Δ (A m) (c m)‖ ≤ shiftedScale H hH Δ A)
    (p : ℕ) (_hp : 0 < p) (s : ℝ) (hs : 0 ≤ s)
    (seed : Fin M) (xs : List (Fin M)) (hlen : xs.length = p) :
    ‖∫ σ in (0 : ℝ)..s, (σ^p : ℝ) •
        nestedCommutator (fun m => shiftedCompression H hH Δ (A m) (c m)) seed xs‖ ≤
      (2^p / (p+1 : ℕ) : ℝ) * (shiftedScale H hH Δ A)^(p+1) * s^(p+1) := by
  have hscale : 0 ≤ shiftedScale H hH Δ A := shiftedScale_nonneg H hH Δ A
  have hnested : ‖nestedCommutator (fun m =>
        shiftedCompression H hH Δ (A m) (c m)) seed xs‖ ≤
      2^p*(shiftedScale H hH Δ A)^(p+1) := by
    rw [nestedCommutator]
    have hseed : ‖shiftedCompression H hH Δ (A seed) (c seed)‖ ≤
        shiftedScale H hH Δ A := hc seed
    have hprod : ((xs.map fun m =>
        ‖shiftedCompression H hH Δ (A m) (c m)‖).prod) ≤
        (shiftedScale H hH Δ A)^xs.length := by
      clear hlen
      induction xs with
      | nil => simp
      | cons x ys ih =>
        simp only [List.map_cons, List.prod_cons]
        have hys : 0 ≤ ((ys.map fun m =>
            ‖shiftedCompression H hH Δ (A m) (c m)‖).prod) :=
          by
            have h := matrix_norm_list_prod_nonneg
              (ys.map fun m => shiftedCompression H hH Δ (A m) (c m))
            simp only [List.map_map] at h
            exact h
        calc
          ‖shiftedCompression H hH Δ (A x) (c x)‖*
              ((ys.map fun m =>
                ‖shiftedCompression H hH Δ (A m) (c m)‖).prod) ≤
              shiftedScale H hH Δ A*
                ((ys.map fun m =>
                  ‖shiftedCompression H hH Δ (A m) (c m)‖).prod) :=
            mul_le_mul_of_nonneg_right (hc x) hys
          _ ≤ shiftedScale H hH Δ A*(shiftedScale H hH Δ A)^ys.length :=
            mul_le_mul_of_nonneg_left ih hscale
          _ = shiftedScale H hH Δ A^(x :: ys).length := by
              simp [pow_succ, mul_comm]
    have hnorm := nestedFrom_norm_le
      (shiftedCompression H hH Δ (A seed) (c seed))
      (xs.map fun m => shiftedCompression H hH Δ (A m) (c m))
    simp only [List.length_map] at hnorm
    rw [hlen] at hnorm
    rw [hlen] at hprod
    simp only [List.map_map, Function.comp_def] at hnorm
    have htwo : (0 : ℝ) < 2^p := by positivity
    have hprodx : ((xs.map fun x =>
        ‖shiftedCompression H hH Δ (A x) (c x)‖).prod) ≤
        (shiftedScale H hH Δ A)^p := hprod
    have hprodnonneg : 0 ≤ ((xs.map fun x =>
        ‖shiftedCompression H hH Δ (A x) (c x)‖).prod) :=
      shifted_norm_prod_nonneg H hH Δ A c xs
    have hcombined : ‖shiftedCompression H hH Δ (A seed) (c seed)‖*
        ((xs.map fun x =>
          ‖shiftedCompression H hH Δ (A x) (c x)‖).prod) ≤
        (shiftedScale H hH Δ A)^(p+1) := by
      calc
        ‖shiftedCompression H hH Δ (A seed) (c seed)‖*
            ((xs.map fun x =>
              ‖shiftedCompression H hH Δ (A x) (c x)‖).prod) ≤
            shiftedScale H hH Δ A*
              ((xs.map fun x =>
                ‖shiftedCompression H hH Δ (A x) (c x)‖).prod) :=
          mul_le_mul_of_nonneg_right hseed hprodnonneg
        _ ≤ shiftedScale H hH Δ A*(shiftedScale H hH Δ A)^p :=
          mul_le_mul_of_nonneg_left hprodx hscale
        _ = shiftedScale H hH Δ A^(p+1) := by ring
    rw [mul_assoc] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_left hcombined htwo.le)
  rw [leading_power_integral_eq]
  have hcoef : 0 ≤ s^(p+1)/(p+1 : ℕ) :=
    div_nonneg (pow_nonneg hs _) (Nat.cast_nonneg _)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]
  calc
    _ ≤ (s^(p+1)/(p+1 : ℕ))*(2^p*(shiftedScale H hH Δ A)^(p+1)) :=
      mul_le_mul_of_nonneg_left hnested hcoef
    _ = _ := by simp only [div_eq_mul_inv]; ring

/-- Choose centers attaining each group's shifted compressed radius. A positive constant
depending only on the order bounds all leading integrals of the already-compressed groups,
with explicit dependence on the shifted compressed scale and time. -/
theorem exists_centers_uniform_projected_shifted_leading_bound [Nonempty I] [Nonempty (Fin M)]
    (H : Matrix I I ℂ)
    (hH : H.IsHermitian) (A : Fin M → Matrix I I ℂ) (_hA : ∀ m, (A m).IsHermitian)
    (Δ : ℝ) (p : ℕ) (hp : 0 < p) :
    ∃ c : Fin M → ℝ,
      (∀ m, ‖shiftedCompression H hH Δ (A m) (c m)‖ = shiftedRadius H hH Δ (A m)) ∧
      ∃ C : ℝ, C = 2^p / (p+1 : ℕ) ∧ 0 < C ∧
        ∀ s : ℝ, 0 ≤ s → ∀ (seed : Fin M) (xs : List (Fin M)),
          xs.length = p →
            ‖∫ σ in (0 : ℝ)..s, (σ^p : ℝ) •
                nestedCommutator (fun m => shiftedCompression H hH Δ (A m) (c m)) seed xs‖ ≤
              C * (shiftedScale H hH Δ A)^(p+1) * s^(p+1) := by
  obtain ⟨c, hc⟩ := exists_shifted_centers H hH Δ A
  have hbound (m : Fin M) : ‖shiftedCompression H hH Δ (A m) (c m)‖ ≤
      shiftedScale H hH Δ A := by
    rw [hc m]
    exact Finset.le_sup' (f := fun m => shiftedRadius H hH Δ (A m)) (Finset.mem_univ m)
  exact ⟨c, hc, 2^p / (p+1 : ℕ), rfl, by positivity,
    projected_shifted_leading_bound H hH A Δ c hbound p hp⟩

end Qatlib.Papers.LowEnergyProd24.CenteredGroups
