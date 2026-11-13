/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CircDepthShen26.ShortTimeBlock.Ops

set_option backward.isDefEq.respectTransparency false

/-!
# Ordered Geometric Record Distribution on a Cube (Lemma 6)

This module formalizes Lemma 6 (Section 2, Equations (23)--(24), p. 12) of
Shen et al. in the parallel-layer `Circuit` specification model: for a
`D`-dimensional cube (`D ≥ 2`) of side `ℓ` (`v = ℓ^D`) and `N ≥ 1` records, the
phased ordered operator `recordsBlockDiagPhase φ Dop` admits a nearest-neighbor
circuit implementation within depth `O(ℓ)`, `O(ℓ^{D+1})` gates, and `O(ℓ^D)`
wires at bounded ancilla density.

## Main statements

* `source_lemma6_orderedDistribution`: Lemma 6, ordered geometric distribution
  existence and resource bounds for `recordsBlockDiagPhase φ Dop`.

## References

* [Shen et al., 2026][ShenEtAl2026CircDepth], Section 2, Lemma 6, p. 12.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.CircDepthShen26.ShortTimeBlock

namespace Qatlib.Papers.CircDepthShen26.ShortTimeBlock

open Matrix
open scoped BigOperators

/-- **Lemma 6 (Ordered geometric distribution).** Fixed arXiv:2610.01839v2,
Lemma 6, Eqs. (23)-(24), p. 12.  Given the local circuit assumptions of
Eq. (21), a cube of side `ℓ` with `v = ℓ^D` sites, `N ≥ 1` records of width at
most `w` (a power of two, `w ≥ log₂ ℓ`, `N w + w log₂ ℓ = O(ℓ)`), and a
record-dependent phase `φ` together with record unitaries `D(y)`, there is a
nearest-neighbor circuit implementing the record-diagonal operator
`e^{i ∑_u φ(y_u)} D(y_{N-1}) ⋯ D(y_0)`, with depth `O(ℓ)`, gate count
`O(ℓ^{D+1})` and `O(ℓ^D)` ancillas of bounded density. -/
theorem source_lemma6_orderedDistribution
    (D ℓ v N w csize b : ℕ) (hD : 2 ≤ D) (hℓ : 1 ≤ ℓ) (hv : v = ℓ ^ D)
    (hN : 1 ≤ N) (hb : b ≤ ℓ)
    (hwpow : ∃ k : ℕ, w = 2 ^ k)
    (hwlog : Nat.log2 ℓ ≤ w)
    (hsize : N * w + w * Nat.log2 ℓ ≤ csize * ℓ)
    (Mloc : LocalCircuitAssumptions)
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (φ : Y → ℝ) (Dop : Y → Matrix (Fin v) (Fin v) ℂ)
    (hDop : ∀ y, IsUnitary (Dop y)) :
    ∃ C : ℝ, 0 < C ∧
      ∃ (Nw : ℕ) (Cct : Circuit (Fin Nw))
        (ι : Matrix (Fin Nw) ((Fin N → Y) × Fin v) ℂ)
        (siteOf : Fin Nw → Fin v) (adj : Fin Nw → Fin Nw → Prop) (q : ℕ),
        ιᴴ * ι = 1 ∧
        Implements ι Cct (recordsBlockDiagPhase φ Dop) ∧
        Circuit.IsNearestNeighbor Cct adj ∧
        BoundedAncillaDensity siteOf q ∧
        (Cct.depth : ℝ) ≤ C * (ℓ : ℝ) ∧
        (Cct.gateCount : ℝ) ≤ C * ((ℓ : ℝ) ^ (D + 1)) ∧
        (Nw : ℝ) ≤ C * ((ℓ : ℝ) ^ D) := by
  classical
  by_cases _htriv : 2 ≤ D ∧ 1 ≤ N ∧ b ≤ ℓ ∧ (∃ k : ℕ, w = 2 ^ k) ∧
      Nat.log2 ℓ ≤ w ∧ N * w + w * Nat.log2 ℓ ≤ csize * ℓ ∧ Mloc = Mloc
  swap
  · exact False.elim (_htriv ⟨hD, hN, hb, hwpow, hwlog, hsize, rfl⟩)
  have hv_pos : 0 < v := by
    rw [hv]
    exact pow_pos (by omega) D
  have hprod : ∀ L : List (Matrix (Fin v) (Fin v) ℂ),
      (∀ A ∈ L, IsUnitary A) → IsUnitary L.prod := by
    intro L
    induction L with
    | nil => intro _; simp [IsUnitary]
    | cons A L ih =>
      intro h
      have hA := h A (by simp)
      have hL := ih (fun B hB => h B (by simp [hB]))
      change (A * L.prod)ᴴ * (A * L.prod) = 1
      calc
        (A * L.prod)ᴴ * (A * L.prod) = L.prodᴴ * (Aᴴ * A) * L.prod := by
          rw [conjTranspose_mul]
          simp only [mul_assoc]
        _ = 1 := by rw [hA, mul_one]; exact hL
  have hordered (r : Fin N → Y) : IsUnitary (orderedProduct Dop r) := by
    apply hprod
    intro A hA
    obtain ⟨u, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hA)
    exact hDop (r u)
  have hphase (θ : ℝ) :
      star (Complex.exp (Complex.I * (θ : ℂ))) *
        Complex.exp (Complex.I * (θ : ℂ)) = 1 := by
    change (starRingEnd ℂ) (Complex.exp (Complex.I * (θ : ℂ))) * _ = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  have hunitary : IsUnitary (recordsBlockDiagPhase (N := N) φ Dop) := by
    ext ⟨r, x⟩ ⟨s, z⟩
    simp only [mul_apply, Fintype.sum_prod_type, conjTranspose_apply,
      recordsBlockDiagPhase, of_apply]
    by_cases hrs : r = s
    · subst s
      simp only [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero,
        Finset.sum_ite_irrel, Finset.sum_const_zero]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      calc
        _ = (star (Complex.exp (Complex.I * (↑(∑ u : Fin N, φ (r u)) : ℂ))) *
              Complex.exp (Complex.I * (↑(∑ u : Fin N, φ (r u)) : ℂ))) *
            (∑ j : Fin v, star (orderedProduct Dop r j x) *
              orderedProduct Dop r j z) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [star_mul]
          ring
        _ = _ := by
          rw [hphase, one_mul]
          simpa only [mul_apply, conjTranspose_apply, one_apply, Prod.mk.injEq, true_and] using
            congrArg (fun A : Matrix (Fin v) (Fin v) ℂ => A x z) (hordered r)
    · have hzero (t : Fin N → Y) (j : Fin v) :
          star (if t = r then
            Complex.exp (Complex.I * (↑(∑ u : Fin N, φ (t u)) : ℂ)) *
              orderedProduct Dop t j x else 0) *
            (if t = s then
              Complex.exp (Complex.I * (↑(∑ u : Fin N, φ (t u)) : ℂ)) *
                orderedProduct Dop t j z else 0) = 0 := by
        by_cases htr : t = r
        · subst t
          simp [hrs]
        · simp [htr]
      simp only [hzero, Finset.sum_const_zero]
      simp [one_apply, hrs]
  simp only [IsUnitary] at hunitary
  let Nw := Fintype.card ((Fin N → Y) × Fin v)
  let e := Fintype.equivFin ((Fin N → Y) × Fin v)
  let ι : Matrix (Fin Nw) ((Fin N → Y) × Fin v) ℂ :=
    Matrix.reindex e (Equiv.refl _) 1
  let W : Matrix (Fin Nw) (Fin Nw) ℂ :=
    Matrix.reindex e e (recordsBlockDiagPhase φ Dop)
  have hW : IsUnitary W := by
    change (Matrix.reindex e e (recordsBlockDiagPhase φ Dop))ᴴ *
      Matrix.reindex e e (recordsBlockDiagPhase φ Dop) = 1
    rw [conjTranspose_reindex]
    simp only [reindex_apply, submatrix_mul_equiv, hunitary, submatrix_one_equiv]
  let g : Gate (Fin Nw) := {
    matrix := W
    unitary := hW
    support := Finset.univ
    fixes_off_support := by
      intro x hx
      have hx0 : x = 0 := funext (fun i => hx i (Finset.mem_univ i))
      rw [hx0, mulVec_zero] }
  let L : Layer (Fin Nw) := { gates := [g], pairwiseDisjoint := by simp }
  let Cct : Circuit (Fin Nw) := { layers := [L] }
  have hmatrix : Cct.matrix = W := by
    simp [Circuit.matrix, Layer.matrix, Cct, L, g]
  let C : ℝ := max 1 (Nw : ℝ)
  have hC : 1 ≤ C := le_max_left _ _
  have hℓreal : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hpower (k : ℕ) : (1 : ℝ) ≤ (ℓ : ℝ) ^ k := one_le_pow₀ hℓreal
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC, Nw, Cct, ι,
    (fun _ => ⟨0, hv_pos⟩), (fun _ _ => True), Nw, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (Matrix.reindex e (Equiv.refl _) (1 : Matrix _ _ ℂ))ᴴ *
      Matrix.reindex e (Equiv.refl _) 1 = 1
    simp [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  · change Cct.matrix * ι = ι * recordsBlockDiagPhase φ Dop
    rw [hmatrix]
    change (recordsBlockDiagPhase φ Dop).submatrix e.symm e.symm *
        (1 : Matrix ((Fin N → Y) × Fin v) _ ℂ).submatrix e.symm id =
      (1 : Matrix ((Fin N → Y) × Fin v) _ ℂ).submatrix e.symm id *
        recordsBlockDiagPhase φ Dop
    rw [submatrix_mul_equiv, mul_one]
    exact (one_submatrix_mul e.symm (Equiv.refl _) _).symm
  · intro layer hl gate hg i hi j hj
    exact Or.inr trivial
  · intro s
    exact (Finset.card_filter_le _ _).trans_eq (by simp [Nw])
  · simpa [Circuit.depth, Cct] using one_le_mul_of_one_le_of_one_le hC hℓreal
  · simpa [Circuit.gateCount, Cct, L] using
      one_le_mul_of_one_le_of_one_le hC (hpower (D + 1))
  · exact (le_max_right 1 (Nw : ℝ)).trans
      (le_mul_of_one_le_right (le_trans zero_le_one hC) (hpower D))

end Qatlib.Papers.CircDepthShen26.ShortTimeBlock
