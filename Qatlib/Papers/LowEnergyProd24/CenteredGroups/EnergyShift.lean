/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.Projectors
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import QuantumInfo.ForMathlib.Matrix

/-!
# PSD group shifts and absolute energy cutoffs

This module formalizes the spectral shift discussed in [HejaziZiniArrazola2024],
supplement p. 11, below Eq. (50). A real scalar multiple of the identity leaves the
eigenvectors of a Hermitian matrix unchanged and shifts every eigenvalue by that scalar.
Consequently the spectral low-energy projector at threshold `Δ + C` for `H + C·1` is exactly
the projector at threshold `Δ` for `H`.

For a nonempty family of Hermitian groups, adding each group's L2-operator norm as a scalar
identity shift makes every shifted group positive semidefinite.  The sum `C` of these shifts
is a positive cutoff penalty whenever at least one group is nonzero, and it is fixed outside
the quantifier over cutoffs. The proof identifies the shift for this construction as the
sum of the group norms. System-size scaling requires additional estimates on those norms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Qatlib.Papers.LowEnergyProd24.CenteredGroups

open Qatlib.Foundations.MatrixGeometry.SpectralCutoff

variable {I : Type*} [Fintype I] [DecidableEq I] {M : ℕ}

/-- The Hermitian matrix obtained by adding the real scalar `C` times the identity to `H`. -/
def scalarShift (H : Matrix I I ℂ) (C : ℝ) : Matrix I I ℂ := H+(C : ℂ) • 1

omit [Fintype I] in
/-- A real scalar identity shift preserves Hermiticity. -/
theorem scalarShift_hermitian (H : Matrix I I ℂ) (hH : H.IsHermitian) (C : ℝ) :
    (scalarShift H C).IsHermitian :=
  hH.add (Matrix.isHermitian_one.smul (R := ℂ) (k := (C : ℂ)) (by simp [IsSelfAdjoint]))

/-- The spectral cutoff projector is the indicator function in Hermitian functional calculus. -/
theorem low_eq_cfc_indicator (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    low H hH Δ = hH.cfc (fun x => if x ≤ Δ then 1 else 0) := by
  rw [low, Matrix.IsHermitian.cfc]
  congr 1
  apply congrArg Matrix.diagonal
  funext i
  by_cases h : hH.eigenvalues i ≤ Δ <;> simp [h]

/-- A common real scalar shift by `C` translates the absolute spectral cutoff by exactly `C`;
the resulting low-energy projector is unchanged. -/
theorem low_scalarShift (H : Matrix I I ℂ) (hH : H.IsHermitian) (C Δ : ℝ) :
    low (scalarShift H C) (scalarShift_hermitian H hH C) (Δ+C) = low H hH Δ := by
  have hrep : scalarShift H C = cfc (fun x : ℝ => x+C) H := by
    show H+(C : ℂ) • 1 = cfc (fun x : ℝ => id x+C) H
    have hshift : cfc (fun x : ℝ => id x+C) H =
        cfc id H+algebraMap ℝ (Matrix I I ℂ) C :=
      @cfc_add_const ℝ (Matrix I I ℂ) IsSelfAdjoint _ _ _ _ _ _ _ _ _ _ C id H
        continuousOn_id hH
    have hident : cfc id H = H := cfc_id ℝ H hH
    rw [hshift, hident]
    simp [Algebra.algebraMap_eq_smul_one]
  have hfinite : ((fun x : ℝ => x+C) '' spectrum ℝ H).Finite :=
    Set.Finite.image (f := fun x : ℝ => x+C) (finite_real_spectrum (A := H))
  rw [low_eq_cfc_indicator, low_eq_cfc_indicator]
  rw [← Matrix.IsHermitian.cfc_eq, ← Matrix.IsHermitian.cfc_eq]
  have hcomp : cfc (fun x : ℝ =>
      (fun x : ℝ => if x ≤ Δ+C then 1 else 0) ((fun x : ℝ => x+C) x)) H =
      cfc (fun x : ℝ => if x ≤ Δ+C then 1 else 0)
        (cfc (fun x : ℝ => x+C) H) :=
    cfc_comp' (fun x : ℝ => if x ≤ Δ+C then 1 else 0)
      (fun x : ℝ => x+C) H (hfinite.continuousOn _) (by fun_prop) hH
  rw [hrep, ← hcomp]
  apply cfc_congr
  intro x _
  by_cases h : x+C ≤ Δ+C
  · have hx : x ≤ Δ := by linarith
    simp [h, hx]
  · have hx : ¬ x ≤ Δ := by linarith
    simp [h, hx]

/-- Adding the L2-operator norm as a scalar identity shift makes a Hermitian matrix positive
semidefinite. -/
theorem norm_shift_posSemidef (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    (A+‖A‖ • (1 : Matrix I I ℂ)).PosSemidef := by
  have hn : (-A).IsHermitian := hA.neg
  have hDnorm : ‖Matrix.diagonal
      ((RCLike.ofReal : ℝ → ℂ) ∘ hn.eigenvalues)‖ = ‖-A‖ := by
    conv_rhs => rw [hn.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
  have hle : -A ≤ ‖A‖ • (1 : Matrix I I ℂ) := by
    refine (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hn ‖A‖).mp fun i => ?_
    calc hn.eigenvalues i ≤ |hn.eigenvalues i| := le_abs_self _
      _ = ‖((RCLike.ofReal : ℝ → ℂ) ∘ hn.eigenvalues) i‖ := by
          simp [Function.comp_apply, Complex.norm_real]
      _ ≤ ‖(RCLike.ofReal : ℝ → ℂ) ∘ hn.eigenvalues‖ := norm_le_pi_norm _ i
      _ = ‖Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hn.eigenvalues)‖ :=
          (Matrix.l2_opNorm_diagonal _).symm
      _ = ‖-A‖ := hDnorm
      _ = ‖A‖ := norm_neg A
  have hpsd : (‖A‖ • (1 : Matrix I I ℂ)-(-A)).PosSemidef := Matrix.le_iff.mp hle
  convert hpsd using 1
  abel

/-- The construction uses the nonnegative L2-operator norms to shift the Hermitian groups to
positive semidefinite matrices. Their positive sum `C` translates every absolute spectral
cutoff by exactly `C`, with the same `C` for every cutoff. -/
theorem exists_psd_shifts_with_cutoff_penalty [Nonempty I] [Nonempty (Fin M)]
    (A : Fin M → Matrix I I ℂ) (hA : ∀ m, (A m).IsHermitian)
    (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (hsum : ∑ m, A m = H) (hpos : 0 < ∑ m, ‖A m‖) :
    ∃ C : ℝ, 0 < C ∧
      ∃ c : Fin M → ℝ,
        (∀ m, (A m+(c m : ℂ) • 1).PosSemidef) ∧
        (∑ m, c m = C) ∧
        (∑ m, (A m+(c m : ℂ) • 1) = scalarShift H C) ∧
        ∀ Δ : ℝ, low (scalarShift H C)
            (scalarShift_hermitian H hH C) (Δ+C) = low H hH Δ := by
  refine ⟨∑ m, ‖A m‖, hpos, fun m => ‖A m‖, fun m => norm_shift_posSemidef _ (hA m), rfl, ?_,
    fun Δ => low_scalarShift H hH _ Δ⟩
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, hsum]
  unfold scalarShift
  congr 1
  simp

end Qatlib.Papers.LowEnergyProd24.CenteredGroups
