/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDirectProd11.MainResults.Classical.ProductMoment

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 3.13 of arXiv:1104.4468: the product moment bound

Fixed source: arXiv:1104.4468 (2011), Corollary 3.13 (p.12).

The corollary combines Lemma 3.11 (proved in `ProductMoment.lean`) with Claim 3.12
(also proved there) applied to the *product* random variable `Π_l A_l` and the
product distribution `p^k`.  The two ingredients are:

* the `k`-fold product of a distribution is a distribution
  (`sum_prod_piFinset`);
* `E_{p^k}[(Π_l A_l)^{-1}] = (E_p[A^{-1}])^k`, so the pointwise bound of Claim 3.12
  raises to the `k`-th power.

The proof below is complete and follows the paper's derivation (p.12) literally.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QDirectProd11.MainResults.Classical

open scoped BigOperators

/-- The `k`-fold product distribution `p^k`. -/
def prodDist {ι : Type} (p : ι → ℝ) (k : ℕ) : (Fin k → ι) → ℝ :=
  fun t => ∏ l, p (t l)

/-- **The expectation identity behind Corollary 3.13** (p.12): for the product
distribution, `E_{p^k}[(Π_l A_l)^{-1}] = (E_p[A^{-1}])^k`.

This is the `k`-fold multiplicativity of the inverse moment, proved by
`Finset.sum_prod_piFinset` together with `Finset.prod_inv_distrib`. -/
theorem prod_inv_moment {ι : Type} [Fintype ι]
    (p A : ι → ℝ) (k : ℕ) :
    (∑ t : Fin k → ι, (∏ l, p (t l)) * (∏ l, A (t l))⁻¹)
      = (∑ i, p i * (A i)⁻¹) ^ k := by
  classical
  have hpt : ∀ t : Fin k → ι,
      (∏ l, p (t l)) * (∏ l, A (t l))⁻¹ = ∏ l, p (t l) * (A (t l))⁻¹ := by
    intro t
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  calc (∑ t : Fin k → ι, (∏ l, p (t l)) * (∏ l, A (t l))⁻¹)
      = ∑ t : Fin k → ι, ∏ l, p (t l) * (A (t l))⁻¹ :=
        Finset.sum_congr rfl (fun t _ => hpt t)
    _ = (∑ i, p i * (A i)⁻¹) ^ k := by
        rw [← Fintype.piFinset_univ (α := Fin k) (β := fun _ => ι)]
        rw [Finset.sum_prod_piFinset (s := Finset.univ)
          (g := fun _ j => p j * (A j)⁻¹)]
        simp

/-- **Corollary 3.13** (p.12).  Let `a₁ ≥ a₀ > 0`, let `p` be a distribution for a
random variable `A` with values in `[a₀,a₁]` and mean `ā`, and let `q` be a
distribution over `(R⁺₀)^k` such that the fidelity `F(p^k, q)` is at least
`√(δ^k)`.  Then the `q`-expectation of the product `Π_l A_l` is at least
`(δ a₀ a₁ / (a₀+a₁-ā))^k`.

Proof (paper, p.12): apply Lemma 3.11 to the product random variable `Π_l A_l`
and the product distribution `p^k`, bound `E_{p^k}[(Π_l A_l)^{-1}]` by
`(E_p[A^{-1}])^k`, and use Claim 3.12 for the single-coordinate inverse moment. -/
theorem corollary_3_13 {ι : Type} [Fintype ι]
    (p A : ι → ℝ) (a0 a1 ā δ : ℝ) (k : ℕ)
    (hk : 0 < k)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (ha0 : 0 < a0) (h01 : a0 ≤ a1) (hā : ā ≤ a1)
    (hA : ∀ i, a0 ≤ A i ∧ A i ≤ a1)
    (hmean : ∑ i, p i * A i = ā)
    (q : (Fin k → ι) → ℝ)
    (hq0 : ∀ t, 0 ≤ q t) (hq1 : ∑ t, q t = 1)
    (hδ0 : 0 ≤ δ)
    (hF : Real.sqrt (δ ^ k) ≤ ∑ t : Fin k → ι, Real.sqrt ((∏ l, p (t l)) * q t)) :
    (δ * a0 * a1 / (a0 + a1 - ā)) ^ k
      ≤ ∑ t : Fin k → ι, q t * ∏ l, A (t l) := by
  classical
  have ha1pos : 0 < a1 := lt_of_lt_of_le ha0 h01
  have hPpos : 0 < a0 * a1 := mul_pos ha0 ha1pos
  have hDpos : 0 < a0 + a1 - ā := by linarith
  have hApos : ∀ i, 0 < A i := fun i => lt_of_lt_of_le ha0 (hA i).1
  have hp'0 : ∀ t : Fin k → ι, 0 ≤ ∏ l, p (t l) :=
    fun t => Finset.prod_nonneg (fun l _ => hp0 (t l))
  have hB0 : ∀ t : Fin k → ι, 0 ≤ ∏ l, A (t l) :=
    fun t => Finset.prod_nonneg (fun l _ => (hApos (t l)).le)
  have hBpos : ∀ t : Fin k → ι, 0 < ∏ l, A (t l) :=
    fun t => Finset.prod_pos (fun l _ => hApos (t l))
  have hsum_p' : (∑ t : Fin k → ι, ∏ l, p (t l)) = 1 := by
    rw [← Fintype.piFinset_univ (α := Fin k) (β := fun _ => ι)]
    rw [Finset.sum_prod_piFinset (s := Finset.univ) (g := fun _ j => p j)]
    simp [hp1]
  have hmain := lemma_3_11 (fun t : Fin k → ι => ∏ l, p (t l)) q
    (fun t : Fin k → ι => ∏ l, A (t l)) (δ ^ k)
    hp'0 hq0 hsum_p' hq1 hB0 (fun t _ => hBpos t) (pow_nonneg hδ0 k) hF
  have hS0 : 0 ≤ ∑ i, p i * (A i)⁻¹ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp0 i) (inv_nonneg.mpr (hApos i).le))
  have hS_le : ∑ i, p i * (A i)⁻¹ ≤ (a0 + a1 - ā) / (a0 * a1) :=
    claim_3_12 p A a0 a1 ā hp0 hp1 ha0 h01 hA hmean
  have hE_le : (∑ i, p i * (A i)⁻¹) ^ k ≤ ((a0 + a1 - ā) / (a0 * a1)) ^ k :=
    pow_le_pow_left₀ hS0 hS_le k
  have hSpos : 0 < ∑ i, p i * (A i)⁻¹ := by
    have hineq : (a1)⁻¹ ≤ ∑ i, p i * (A i)⁻¹ := by
      calc (a1)⁻¹ = ∑ i, p i * (a1)⁻¹ := by rw [← Finset.sum_mul, hp1, one_mul]
        _ ≤ ∑ i, p i * (A i)⁻¹ :=
            Finset.sum_le_sum (fun i _ =>
              mul_le_mul_of_nonneg_left (inv_anti₀ (hApos i) (hA i).2) (hp0 i))
    have h1 : 0 < (a1)⁻¹ := inv_pos.mpr ha1pos
    linarith
  have hEpos : 0 < (∑ i, p i * (A i)⁻¹) ^ k := pow_pos hSpos k
  have hEinv : (((a0 + a1 - ā) / (a0 * a1)) ^ k)⁻¹
      ≤ ((∑ i, p i * (A i)⁻¹) ^ k)⁻¹ := inv_anti₀ hEpos hE_le
  have hratio : δ * a0 * a1 / (a0 + a1 - ā)
      = δ / ((a0 + a1 - ā) / (a0 * a1)) := by
    rw [div_div_eq_mul_div]
    ring
  have hpow_eq : (δ * a0 * a1 / (a0 + a1 - ā)) ^ k
      = δ ^ k * (((a0 + a1 - ā) / (a0 * a1)) ^ k)⁻¹ := by
    rw [hratio, div_pow, div_eq_mul_inv]
  calc (δ * a0 * a1 / (a0 + a1 - ā)) ^ k
      = δ ^ k * (((a0 + a1 - ā) / (a0 * a1)) ^ k)⁻¹ := hpow_eq
    _ ≤ δ ^ k * ((∑ i, p i * (A i)⁻¹) ^ k)⁻¹ :=
        mul_le_mul_of_nonneg_left hEinv (pow_nonneg hδ0 k)
    _ = δ ^ k * (∑ t : Fin k → ι, (∏ l, p (t l)) * (∏ l, A (t l))⁻¹)⁻¹ := by
        rw [prod_inv_moment]
    _ ≤ ∑ t : Fin k → ι, q t * ∏ l, A (t l) := hmain

end Qatlib.Papers.QDirectProd11.MainResults.Classical
