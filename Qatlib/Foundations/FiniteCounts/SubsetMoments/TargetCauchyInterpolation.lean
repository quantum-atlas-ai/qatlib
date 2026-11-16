/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.FiniteCounts.SubsetMoments.GlobalSourceMoments

@[expose] public section


/-! # Exact finite interpolation of target Cauchy weights

For points satisfying `z^N = 1`, a Cauchy weight can be expanded using all
`N` finite power moments.  This is an exact algebraic identity, not a claim
that a non-Fourier target data structure is impossible.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteCounts.SubsetMoments
open scoped BigOperators Classical

/-- The weighted sum of the Cauchy denominators at a finite set of complex points. -/
def finiteCauchyWeight {ι : Type*} [Fintype ι]
    (z g : ι → ℂ) (c : ℂ) : ℂ :=
  ∑ i, g i / (z i - c)

/-- The finite geometric kernel factors the difference of two natural powers. -/
theorem finiteGeometricKernel_mul (z c : ℂ) : ∀ N : ℕ,
    (z - c) * (∑ r ∈ Finset.range N, z ^ (N - 1 - r) * c ^ r) =
      z ^ N - c ^ N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hsum : (∑ r ∈ Finset.range N, z ^ (N - r) * c ^ r) =
        z * (∑ r ∈ Finset.range N, z ^ (N - 1 - r) * c ^ r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hlt : r < N := Finset.mem_range.mp hr
      have hpow : N - r = (N - 1 - r) + 1 := by omega
      rw [hpow, pow_succ]
      ring
    simp only [Nat.add_sub_cancel]
    rw [hsum]
    simp only [Nat.sub_self, pow_zero, one_mul]
    calc
      (z - c) *
          (z * (∑ r ∈ Finset.range N, z ^ (N - 1 - r) * c ^ r) + c ^ N) =
          z * ((z - c) * (∑ r ∈ Finset.range N, z ^ (N - 1 - r) * c ^ r)) +
            (z - c) * c ^ N := by ring
      _ = z * (z ^ N - c ^ N) + (z - c) * c ^ N := by rw [ih]
      _ = z ^ (N + 1) - c ^ (N + 1) := by ring

/-- At roots of unity away from the evaluation pole, a finite Cauchy sum equals its complete power-moment expansion. -/
theorem finiteCauchyWeight_interpolate {ι : Type*} [Fintype ι]
    (z g : ι → ℂ) (N : ℕ) (c : ℂ)
    (hpow : ∀ i, z i ^ N = 1) (hc : 1 - c ^ N ≠ 0) :
    finiteCauchyWeight z g c =
      (1 - c ^ N)⁻¹ * ∑ r ∈ Finset.range N, c ^ r *
        ∑ i, g i * z i ^ (N - 1 - r) := by
  have hzc (i : ι) : z i - c ≠ 0 := by
    intro hz
    have hzi : z i = c := sub_eq_zero.mp hz
    apply hc
    rw [← hpow i, hzi]
    ring
  unfold finiteCauchyWeight
  calc
    (∑ i, g i / (z i - c)) =
        ∑ i, (1 - c ^ N)⁻¹ *
          ∑ r ∈ Finset.range N, g i * (z i ^ (N - 1 - r) * c ^ r) := by
      apply Fintype.sum_congr
      intro i
      have hgeom := finiteGeometricKernel_mul (z i) c N
      rw [hpow i] at hgeom
      field_simp [hzc i, hc]
      rw [← hgeom]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      ring
    _ = (1 - c ^ N)⁻¹ * ∑ r ∈ Finset.range N, c ^ r *
        ∑ i, g i * z i ^ (N - 1 - r) := by
      have hfactor :
          (∑ i, (1 - c ^ N)⁻¹ *
            ∑ r ∈ Finset.range N,
              g i * (z i ^ (N - 1 - r) * c ^ r)) =
            (1 - c ^ N)⁻¹ * ∑ i,
              ∑ r ∈ Finset.range N,
                g i * (z i ^ (N - 1 - r) * c ^ r) := by
        rw [← Finset.mul_sum]
      rw [hfactor]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      calc
        (∑ i, g i * (z i ^ (N - 1 - r) * c ^ r)) =
            ∑ i, c ^ r * (g i * z i ^ (N - 1 - r)) := by
              apply Fintype.sum_congr
              intro i
              ring
        _ = c ^ r * ∑ i, g i * z i ^ (N - 1 - r) := by
              rw [Finset.mul_sum]

end Qatlib.Foundations.FiniteCounts.SubsetMoments
