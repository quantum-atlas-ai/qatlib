/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.RetainedError.PhysicalSpectral

/-!
# Leakage bounds for physical commutator products

For the original physical Hamiltonian, `productEll` adds a scalar center contribution to the
commutator majorant precisely at order zero. Weighted bounds and leakage estimates extend to
products, and `original_positive_product_leakage` removes this correction when every factor has
positive commutator order. See [HejaziZiniArrazola2024].

## Main statements

* `original_weighted_product`: For positive `J`, `k`, and `d` and at most `L` labels per group,
  the weighted norm of a physical commutator product is at most the product of its `productEll`
  majorants.
* `original_product_leakage`: For positive `J`, `k`, and `d` and at most `L` labels per group,
  the physical product transition norm from energies at most `Δ` to energies above `Λ` is
  bounded by the product of its `productEll` majorants times `exp(-(Λ - Δ) / (2 * J * k * d))`.
* `original_positive_product_leakage`: If every factor has a nonempty outer list, positive `J`,
  `k`, and `d` and at most `L` labels per group give a physical product leakage bound using only
  the product of `sourceEll` majorants and `exp(-(Λ - Δ) / (2 * J * k * d))`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.Physical
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.CenterTransport
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

/-- The `sourceEll` majorant for a factor, augmented by the absolute group center when its outer
commutator list is empty. -/
def productEll (h : PhysicalHamiltonian N R M k d J) (L : ℕ) (factor : Fin M × List (Fin M)) : ℝ :=
  sourceEll L k d J factor.2.length + if factor.2=[] then |h.groupCenter factor.1| else 0

/-- The physical product-factor majorant is nonnegative for nonnegative `J`. -/
theorem productEll_nonneg (h : PhysicalHamiltonian N R M k d J) (L : ℕ) (hJ : 0 ≤ J)
    (factor : Fin M × List (Fin M)) : 0 ≤ productEll h L factor := by
  have hb := sourceEll_nonneg L k d factor.2.length J hJ
  unfold productEll
  split_ifs
  · exact add_nonneg hb (abs_nonneg _)
  · simpa only [add_zero] using hb

/-- For positive `J`, `k`, and `d` and at most `L` seed labels, the weighted physical nested
commutator has norm at most its `productEll` majorant. -/
theorem original_weighted_nested (h : PhysicalHamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ) (seed : Fin M)
    (hL : (h.labels seed).card ≤ L) (xs : List (Fin M)) :
    ‖weighted h.total (RetainedError.Physical.nested h seed xs) (1/(2*J*k*d))‖ ≤ productEll h L (seed,xs) := by
  have hb := actual_weighted_source_ell h.normalized hJ hk hd L seed hL xs
  have hweightone : weighted h.total 1 (1/(2*J*k*d))=1 := by
    simpa only [evolve, neg_zero, Complex.ofReal_zero, zero_mul, zero_smul, NormedSpace.exp_zero] using
      physical_weighted_exact h (1/(2*J*k*d)) 0
  by_cases hx : xs=[]
  · subst xs
    rw [RetainedError.Physical.nested_centered]
    simp only [if_true]
    have he : weighted h.total
        (RetainedError.nested h.normalized seed []+(h.groupCenter seed : ℂ) • 1) (1/(2*J*k*d)) =
        weighted h.normalized.total (RetainedError.nested h.normalized seed []) (1/(2*J*k*d))+
          (h.groupCenter seed : ℂ) • 1 := by
      calc
        _ = weighted h.total (RetainedError.nested h.normalized seed []) (1/(2*J*k*d))+
            (h.groupCenter seed : ℂ) • weighted h.total 1 (1/(2*J*k*d)) := by
          simp only [weighted, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
        _ = _ := by rw [physical_weight_centered, hweightone]
    rw [he]
    change _ ≤ sourceEll L k d J 0+|h.groupCenter seed|
    exact (norm_add_le _ _).trans
        (add_le_add hb (by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one]))
  · rw [RetainedError.Physical.nested_centered, if_neg hx, add_zero, physical_weight_centered]
    simpa only [productEll, if_neg hx, add_zero] using hb

/-- The ordered product of the physical nested commutators indexed by `factors`. -/
def nestedProduct (h : PhysicalHamiltonian N R M k d J) (factors : List (Fin M × List (Fin M))) :=
  (factors.map (fun factor => RetainedError.Physical.nested h factor.1 factor.2)).prod

/-- For positive `J`, `k`, and `d` and at most `L` labels per group, the weighted norm of a
physical commutator product is at most the product of its `productEll` majorants. -/
theorem original_weighted_product (h : PhysicalHamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (factors : List (Fin M × List (Fin M))) :
    ‖weighted h.total (nestedProduct h factors) (1/(2*J*k*d))‖ ≤ (factors.map (productEll h L)).prod := by
  induction factors with
  | nil =>
    have he : weighted h.total 1 (1/(2*J*k*d))=1 := by
      simpa only [evolve, neg_zero, Complex.ofReal_zero, zero_mul, zero_smul, NormedSpace.exp_zero] using
        physical_weighted_exact h (1/(2*J*k*d)) 0
    simpa only [nestedProduct, List.map_nil, List.prod_nil, he, norm_one] using (le_refl (1 : ℝ))
  | cons factor factors ih =>
    change ‖weighted h.total (RetainedError.Physical.nested h factor.1 factor.2*nestedProduct h factors) (1/(2*J*k*d))‖ ≤
      productEll h L factor*(factors.map (productEll h L)).prod
    rw [weighted_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul
      (original_weighted_nested h hJ hk hd L factor.1 (hL factor.1) factor.2) ih
      (norm_nonneg _) (productEll_nonneg h L hJ.le factor))

/-- For positive `J`, `k`, and `d` and at most `L` labels per group, the physical product
transition norm from energies at most `Δ` to energies above `Λ` is bounded by the product of
its `productEll` majorants times `exp(-(Λ - Δ) / (2 * J * k * d))`. See
[HejaziZiniArrazola2024]. -/
theorem original_product_leakage (h : PhysicalHamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (factors : List (Fin M × List (Fin M))) (Δ Λ : ℝ) :
    ‖high h.total h.total_hermitian Λ*nestedProduct h factors*low h.total h.total_hermitian Δ‖ ≤
      Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*(factors.map (productEll h L)).prod :=
  (weighted_leakage h.total (nestedProduct h factors) h.total_hermitian Δ Λ
    (1/(2*J*k*d)) (by positivity)).trans
    (mul_le_mul_of_nonneg_left (original_weighted_product h hJ hk hd L hL factors) (Real.exp_pos _).le)

/-- If every factor has a nonempty outer list, positive `J`, `k`, and `d` and at most `L` labels
per group give a physical product leakage bound using only the product of `sourceEll`
majorants and `exp(-(Λ - Δ) / (2 * J * k * d))`. See [HejaziZiniArrazola2024]. -/
theorem original_positive_product_leakage (h : PhysicalHamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (factors : List (Fin M × List (Fin M)))
    (hpositive : ∀ factor ∈ factors, factor.2 ≠ []) (Δ Λ : ℝ) :
    ‖high h.total h.total_hermitian Λ*nestedProduct h factors*low h.total h.total_hermitian Δ‖ ≤
      Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*(factors.map (fun factor => sourceEll L k d J factor.2.length)).prod := by
  have he : factors.map (productEll h L)=factors.map (fun factor => sourceEll L k d J factor.2.length) := by
    apply List.map_congr_left
    intro factor hf
    simp only [productEll, if_neg (hpositive factor hf), add_zero]
  simpa only [he] using original_product_leakage h hJ hk hd L hL factors Δ Λ
end Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.Physical
