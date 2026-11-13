/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.MeasurementPatterns

/-!
# Extending identity recovery to reference systems

A complex linear map that fixes every density operator fixes every positive semidefinite
operator and hence every operator. `density_identity_on_reference` then shows that applying this
map to one factor fixes every joint operator with a finite reference.

These linear extension results support the reference preserving recovery arguments used for
teleportation in [BennettEtAl1993Teleportation].

## Main statements

* `density_identity_on_psd` extends density operator recovery to positive semidefinite inputs.
* `density_identity_on_all_operators` extends recovery to the full operator space.
* `density_identity_on_reference` extends recovery to a finite reference system.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound
open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QuditTeleport.ResourceIff
open Qatlib.Concepts.AdaptiveCP.BranchTrace

/-- A complex linear map that fixes every density operator also fixes every positive
semidefinite operator. -/
theorem density_identity_on_psd {n : ℕ} (G : Operator n →ₗ[ℂ] Operator n)
    (hfix : ∀ ρ, IsDensityOperator ρ → G ρ = ρ)
    (A : Operator n) (hA : A.PosSemidef) : G A = A := by
  by_cases ht : Matrix.trace A = 0
  · have hz : A = 0 := (PosSemidef.trace_eq_zero_iff hA).mp ht
    simp [hz]
  · have hnn := hA.trace_nonneg
    have him : (Matrix.trace A).im = 0 := (Complex.nonneg_iff.mp hnn).2.symm
    have hre : 0 < (Matrix.trace A).re := by
      by_contra hlt
      have hre0 : (Matrix.trace A).re = 0 := by
        have h1 := (Complex.nonneg_iff.mp hnn).1
        linarith
      apply ht
      exact Complex.ext hre0 him
    let t : ℝ := (Matrix.trace A).re
    have htpos : 0 < t := hre
    have htrace : Matrix.trace A = (t : ℂ) := by
      apply Complex.ext <;> simp [t, him]
    have hρ : IsDensityOperator (((1 / t : ℝ) : ℂ) • A) := by
      refine ⟨hA.smul ?_, ?_⟩
      · have hnonneg : (0 : ℝ) ≤ 1 / t := by positivity
        exact Complex.nonneg_iff.mpr ⟨by simpa using hnonneg, by simp⟩
      · rw [trace_smul, smul_eq_mul, htrace, ← Complex.ofReal_mul,
          div_mul_cancel₀ _ (ne_of_gt htpos), Complex.ofReal_one]
    have he := hfix _ hρ
    rw [map_smul] at he
    have hc : (t : ℂ) * ((1 / t : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_comm, div_mul_cancel₀ _ (ne_of_gt htpos),
        Complex.ofReal_one]
    have hscaled := congrArg (fun B : Operator n => (t : ℂ) • B) he
    simpa only [smul_smul, hc, one_smul] using hscaled

/-- A complex linear map that fixes every density operator is the identity on the entire
operator space. -/
theorem density_identity_on_all_operators {n : ℕ}
    (G : Operator n →ₗ[ℂ] Operator n)
    (hfix : ∀ ρ, IsDensityOperator ρ → G ρ = ρ) : ∀ A, G A = A := by
  apply eq_of_outerProduct_fixed (fun A => G A)
  · exact fun A B => G.map_add A B
  · intro c A
    simp
  · intro v
    exact density_identity_on_psd G hfix _ (outerProduct_posSemidef v)

/-- A complex linear map fixing every density operator also fixes every joint operator when
applied to one factor with a finite reference, supporting reference recovery in
[BennettEtAl1993Teleportation]. -/
theorem density_identity_on_reference {n R : ℕ}
    (G : Operator n →ₗ[ℂ] Operator n)
    (hfix : ∀ ρ, IsDensityOperator ρ → G ρ = ρ)
    (X : Matrix (Fin n × Fin R) (Fin n × Fin R) ℂ) :
    tensorLeft G X = X := by
  ext ⟨i,r⟩ ⟨j,s⟩
  change G (fun a b => X (a,r) (b,s)) i j = X (i,r) (j,s)
  rw [density_identity_on_all_operators G hfix]

end Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound
