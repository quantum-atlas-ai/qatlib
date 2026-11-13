/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option backward.isDefEq.respectTransparency false

/-!
# Energy Stability of Positive-Definite Detail Schur Complements

This module formalizes Proposition 5.4, Eq. (5.20), establishing two-sided quadratic
form norm equivalence `c₀ ‖z‖² ≤ Re(zᴴ Σ z) ≤ C₀ ‖z‖²` with `0 < c₀ ≤ C₀` for a
Hermitian positive-definite detail Schur complement matrix `Σ`.

## Main statements

* `source_energy_stability`: existence of constants `0 < c0 ≤ C0` bounding
  `(∑ i, star (z i) * (Sig *ᵥ z) i).re` above and below by multiples of `‖z‖ ^ 2`.

## References

* [Li, 2026][Li2026EllipticPDE], Section 5.3, Proposition 5.4, Eq. (5.20), p. 16.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix BigOperators ComplexOrder

namespace Qatlib.Papers.EllipticPDELi26.MainResults.AnalyticScaling

/-- **Proposition 5.4, Eq. (5.20)**: for a Hermitian positive-definite detail Schur
complement `Sig`, there exist constants `0 < c0 ≤ C0` such that
`c0 * ‖z‖ ^ 2 ≤ (∑ i, star (z i) * (Sig *ᵥ z) i).re ≤ C0 * ‖z‖ ^ 2` for all `z`. -/
theorem source_energy_stability {n : ℕ}
    (Sig : Matrix (Fin n) (Fin n) ℂ) (hSig : Sig.IsHermitian)
    (hpos : ∀ z : Fin n → ℂ, z ≠ 0 → 0 < (∑ i, star (z i) * (Sig *ᵥ z) i).re) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 ≤ C0 ∧
      ∀ z : Fin n → ℂ,
        c0 * ‖z‖ ^ 2 ≤ (∑ i, star (z i) * (Sig *ᵥ z) i).re ∧
        (∑ i, star (z i) * (Sig *ᵥ z) i).re ≤ C0 * ‖z‖ ^ 2 := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨1, 1, zero_lt_one, le_rfl, ?_⟩
    intro z
    have hz : z = 0 := Subsingleton.elim _ _
    simp [hz]
  · obtain ⟨i0⟩ := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i0, Finset.mem_univ _⟩
    let ev : Fin n → ℝ := hSig.eigenvalues
    have hev : ∀ k, 0 < ev k := by
      intro k
      rw [show ev k = _ from hSig.eigenvalues_eq k]
      exact hpos _ ((WithLp.ofLp_eq_zero 2).ne.2
        (hSig.eigenvectorBasis.orthonormal.ne_zero k))
    let lo : ℝ := Finset.univ.inf' huniv ev
    let hi : ℝ := Finset.univ.sup' huniv ev
    have hlo : 0 < lo := (Finset.lt_inf'_iff huniv).2 fun k _ => hev k
    have hloe : ∀ k, lo ≤ ev k := fun k => Finset.inf'_le ev (Finset.mem_univ k)
    have hehi : ∀ k, ev k ≤ hi := fun k => Finset.le_sup' ev (Finset.mem_univ k)
    have hhi : 0 < hi := (hev i0).trans_le (hehi i0)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    refine ⟨lo, (n : ℝ) * hi, hlo, ?_, ?_⟩
    · exact (hloe i0).trans ((hehi i0).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn1 hhi.le))
    · intro z
      let U : Matrix (Fin n) (Fin n) ℂ := hSig.eigenvectorUnitary
      let w : Fin n → ℂ := Uᴴ *ᵥ z
      have hUU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hSig.eigenvectorUnitary
      have hdiag : Sig = U * diagonal (fun k => (ev k : ℂ)) * Uᴴ := by
        simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
          RCLike.ofReal_eq_complex_ofReal, Function.comp_def, U, ev] using hSig.spectral_theorem
      have hstar : star z ᵥ* U = star w := by
        dsimp [w]
        rw [star_mulVec, conjTranspose_conjTranspose]
      have hnorm (x : Fin n → ℂ) :
          (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
        simp [dotProduct, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow]
      -- The unitary change of coordinates preserves the sum of squared coordinate norms.
      have hsum : ∑ k, ‖w k‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
        rw [← hnorm w, ← hnorm z]
        congr 1
        calc
          star w ⬝ᵥ w = star z ⬝ᵥ (U *ᵥ w) := by
            rw [dotProduct_mulVec (star z) U w, hstar]
          _ = star z ⬝ᵥ z := by
            dsimp [w]
            rw [mulVec_mulVec, hUU, one_mulVec]
      have henergy : (∑ i, star (z i) * (Sig *ᵥ z) i).re =
          ∑ k, ev k * ‖w k‖ ^ 2 := by
        change (star z ⬝ᵥ (Sig *ᵥ z)).re = _
        rw [hdiag, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hstar]
        change (star w ⬝ᵥ (diagonal (fun k => (ev k : ℂ)) *ᵥ w)).re = _
        simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_left_comm, RCLike.star_def, Complex.conj_mul']
        simp [← Complex.ofReal_pow]
      have hlower : lo * (∑ i, ‖z i‖ ^ 2) ≤
          (∑ i, star (z i) * (Sig *ᵥ z) i).re := by
        rw [henergy, ← hsum, Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hloe k) (sq_nonneg _)
      have hupper : (∑ i, star (z i) * (Sig *ᵥ z) i).re ≤
          hi * (∑ i, ‖z i‖ ^ 2) := by
        rw [henergy, ← hsum, Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hehi k) (sq_nonneg _)
      -- The function space carries the sup norm, so the upper comparison costs a factor of n.
      have hnorm_lower : ‖z‖ ^ 2 ≤ ∑ i, ‖z i‖ ^ 2 := by
        obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' huniv (fun i => ‖z i‖)
        have hmax : ‖z‖ = ‖z j‖ := by
          apply le_antisymm
          · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
            intro i
            rw [← hj]
            exact Finset.le_sup' (fun i : Fin n => ‖z i‖) (Finset.mem_univ i)
          · exact norm_le_pi_norm z j
        rw [hmax]
        exact Finset.single_le_sum (fun i _ => sq_nonneg ‖z i‖) (Finset.mem_univ j)
      have hnorm_upper : (∑ i, ‖z i‖ ^ 2) ≤ (n : ℝ) * ‖z‖ ^ 2 := by
        calc
          (∑ i, ‖z i‖ ^ 2) ≤ ∑ _ : Fin n, ‖z‖ ^ 2 :=
            Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z i) 2
          _ = (n : ℝ) * ‖z‖ ^ 2 := by simp
      constructor
      · exact (mul_le_mul_of_nonneg_left hnorm_lower hlo.le).trans hlower
      · calc
          (∑ i, star (z i) * (Sig *ᵥ z) i).re ≤ hi * ((n : ℝ) * ‖z‖ ^ 2) :=
            hupper.trans (mul_le_mul_of_nonneg_left hnorm_upper hhi.le)
          _ = (n : ℝ) * hi * ‖z‖ ^ 2 := by rw [← mul_assoc, mul_comm hi]

end Qatlib.Papers.EllipticPDELi26.MainResults.AnalyticScaling
