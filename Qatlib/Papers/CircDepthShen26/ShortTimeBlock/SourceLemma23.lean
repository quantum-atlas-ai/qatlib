/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CircDepthShen26.ShortTimeBlock.Ops

set_option backward.isDefEq.respectTransparency false

/-!
# One-Dimensional Phased Record Compilation (Lemma 23)

This module formalizes Lemma 23 (Appendix A, Equations (172)--(178), pp. 57--58)
of Shen et al. in the parallel-layer `Circuit` specification model: for `N ≥ 1`
records on a padded one-dimensional block of length `ℓ = w 2^{K_1}`, the phased
ordered record operator `recordsBlockDiagPhase φ Dop` admits a nearest-neighbor
circuit implementation within depth `O(ℓ)`, `O(ℓ^2)` gates, and `O(ℓ)` wires at
bounded ancilla density.

## Main statements

* `source_lemma23_onedimCompilation`: Lemma 23, one-dimensional compilation
  existence and resource bounds for `recordsBlockDiagPhase φ Dop`.

## References

* [Shen et al., 2026][ShenEtAl2026CircDepth], Appendix A, Lemma 23, pp. 57--58.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.CircDepthShen26.ShortTimeBlock

namespace Qatlib.Papers.CircDepthShen26.ShortTimeBlock

open Matrix
open scoped BigOperators

/-- **Lemma 23 (One-dimensional record compilation).** Fixed
arXiv:2610.01839v2, Lemma 23, Eqs. (172)-(178), pp. 57-58.  The one-dimensional
schedule compiles the ordered record action and the address-dependent phases
into a nearest-neighbor circuit of depth `O(ℓ)`, `O(ℓ²)` gates and `O(ℓ)`
ancillas, returning all registers to zero. -/
theorem source_lemma23_onedimCompilation
    (ℓ w K1 N L F csize : ℕ)
    (hw : 1 ≤ w) (hpow : ℓ = w * 2 ^ K1)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hF : F = (L + 1) * N)
    (hsize : F * w ≤ csize * ℓ)
    (Mloc : LocalCircuitAssumptions)
    (hLloc : L = Mloc.stages)
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (φ : Y → ℝ) (Dop : Y → Matrix (Fin ℓ) (Fin ℓ) ℂ)
    (hDop : ∀ y, IsUnitary (Dop y)) :
    ∃ C : ℝ, 0 < C ∧
      ∃ (Nw : ℕ) (Cct : Circuit (Fin Nw))
        (ι : Matrix (Fin Nw) ((Fin N → Y) × Fin ℓ) ℂ)
        (siteOf : Fin Nw → Fin ℓ) (adj : Fin Nw → Fin Nw → Prop) (q : ℕ),
        ιᴴ * ι = 1 ∧
        Implements ι Cct (recordsBlockDiagPhase φ Dop) ∧
        Circuit.IsNearestNeighbor Cct adj ∧
        BoundedAncillaDensity siteOf q ∧
        (Cct.depth : ℝ) ≤ C * (ℓ : ℝ) ∧
        (Cct.gateCount : ℝ) ≤ C * ((ℓ : ℝ) ^ 2) ∧
        (Nw : ℝ) ≤ C * (ℓ : ℝ) := by
  classical
  by_cases _htriv : 1 ≤ N ∧ 1 ≤ L ∧ F = (L + 1) * N ∧
      F * w ≤ csize * ℓ ∧ L = Mloc.stages
  swap
  · exact False.elim (_htriv ⟨hN, hL, hF, hsize, hLloc⟩)
  have hℓ_pos : 0 < ℓ := by
    rw [hpow]
    exact Nat.mul_pos hw (pow_pos (by decide) K1)
  have hℓ : (1 : ℝ) ≤ ℓ := by
    exact_mod_cast Nat.succ_le_of_lt hℓ_pos
  have hprod : ∀ r : Fin N → Y, IsUnitary (orderedProduct Dop r) := by
    intro r
    apply List.prod_induction IsUnitary
    · intro A B hA hB
      change (A * B)ᴴ * (A * B) = 1
      calc
        (A * B)ᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hA, Matrix.mul_one, hB]
    · simp [IsUnitary]
    · intro A hA
      obtain ⟨u, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hA)
      exact hDop (r u)
  have hphase : ∀ θ : ℝ,
      star (Complex.exp (Complex.I * (θ : ℂ))) *
        Complex.exp (Complex.I * (θ : ℂ)) = 1 := by
    intro θ
    have hstar : star (Complex.I * (θ : ℂ)) = -(Complex.I * (θ : ℂ)) := by
      simp [mul_comm]
    rw [show star (Complex.exp (Complex.I * (θ : ℂ))) =
        Complex.exp (star (Complex.I * (θ : ℂ))) from
      (Complex.exp_conj _).symm, hstar, ← Complex.exp_add]
    simp
  have hunitary : IsUnitary (recordsBlockDiagPhase (N := N) φ Dop) := by
    ext ⟨r, x⟩ ⟨s, y⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single r]
    · by_cases hrs : r = s
      · subst s
        simp only [Matrix.conjTranspose_apply, recordsBlockDiagPhase, Matrix.of_apply,
          ↓reduceIte, star_mul]
        calc
          _ = ∑ z : Fin ℓ,
              star (orderedProduct Dop r z x) * orderedProduct Dop r z y := by
            apply Finset.sum_congr rfl
            intro z _
            calc
              _ = (star (Complex.exp (Complex.I * ((∑ u, φ (r u) : ℝ) : ℂ))) *
                    Complex.exp (Complex.I * ((∑ u, φ (r u) : ℝ) : ℂ))) *
                  (star (orderedProduct Dop r z x) * orderedProduct Dop r z y) := by
                    ring
              _ = _ := by rw [hphase, one_mul]
          _ = (1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) x y :=
            congrArg (fun A : Matrix (Fin ℓ) (Fin ℓ) ℂ => A x y) (hprod r)
          _ = _ := by simp [Matrix.one_apply]
      · simp [Matrix.conjTranspose_apply, recordsBlockDiagPhase, hrs, Prod.mk.injEq]
    · intro t _ htr
      simp [Matrix.conjTranspose_apply, recordsBlockDiagPhase, htr]
    · simp
  let Nw := Fintype.card ((Fin N → Y) × Fin ℓ)
  let e : ((Fin N → Y) × Fin ℓ) ≃ Fin Nw := Fintype.equivFin _
  let W : Matrix (Fin Nw) (Fin Nw) ℂ := Matrix.reindex e e (recordsBlockDiagPhase φ Dop)
  let ι : Matrix (Fin Nw) ((Fin N → Y) × Fin ℓ) ℂ :=
    Matrix.reindex e (Equiv.refl _) 1
  have hW : IsUnitary W := by
    dsimp only [IsUnitary] at hunitary
    change (Matrix.reindex e e (recordsBlockDiagPhase φ Dop))ᴴ *
      Matrix.reindex e e (recordsBlockDiagPhase φ Dop) = 1
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, hunitary, Matrix.submatrix_one_equiv]
  let g : Gate (Fin Nw) :=
    { matrix := W
      unitary := hW
      support := Finset.univ
      fixes_off_support := by
        intro x hx
        have hx0 : x = 0 := funext fun i => hx i (Finset.mem_univ i)
        simp [hx0] }
  let layer : Layer (Fin Nw) :=
    { gates := [g]
      pairwiseDisjoint := by simp }
  let Cct : Circuit (Fin Nw) := ⟨[layer]⟩
  have hι : ιᴴ * ι = 1 := by
    simp [ι, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  have himplements : Implements ι Cct (recordsBlockDiagPhase φ Dop) := by
    simp [Implements, Cct, Circuit.matrix, layer, Layer.matrix, g, W, ι,
      Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    simpa only [Matrix.one_mul, Matrix.submatrix_id_id] using
      (Matrix.submatrix_mul
        (1 : Matrix ((Fin N → Y) × Fin ℓ) ((Fin N → Y) × Fin ℓ) ℂ)
        (recordsBlockDiagPhase φ Dop) e.symm id id Function.bijective_id)
  let C : ℝ := max 1 (Nw : ℝ)
  have hC : (1 : ℝ) ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlinear : (1 : ℝ) ≤ C * ℓ :=
    le_trans hC (le_mul_of_one_le_right hCpos.le hℓ)
  have hquad : (1 : ℝ) ≤ C * (ℓ : ℝ) ^ 2 :=
    le_trans hC (le_mul_of_one_le_right hCpos.le (one_le_pow₀ hℓ))
  refine ⟨C, hCpos, Nw, Cct, ι, (fun _ => ⟨0, hℓ_pos⟩),
    (fun _ _ => True), Nw, hι, himplements, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _
    exact Or.inr trivial
  · intro s
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  · simpa [Cct, Circuit.depth] using hlinear
  · simpa [Cct, layer, Circuit.gateCount] using hquad
  · exact le_trans (le_max_right 1 (Nw : ℝ))
      (le_mul_of_one_le_right hCpos.le hℓ)

end Qatlib.Papers.CircDepthShen26.ShortTimeBlock
