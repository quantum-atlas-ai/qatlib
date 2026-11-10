/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SignedWtEnum99.MainResults.Lemma10
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SignedWtEnum99.MainResults

variable {n N : ℕ}

lemma transpose_mulVec_eq_sum (H : Matrix (Fin n) (Fin N) (ZMod 2))
    (v : Fin n → ZMod 2) :
    Hᵀ *ᵥ v = ∑ i : Fin n, v i • (fun r : Fin N => H i r) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma transpose_mulVec_eq_zero_iff (hn : n ≤ N) (H : Matrix (Fin n) (Fin N) (ZMod 2))
    (h : LinearIndependent (ZMod 2)
      (fun j : Fin n => fun i : Fin n => H i (Fin.castLE hn j)))
    (v : Fin n → ZMod 2) : Hᵀ *ᵥ v = 0 ↔ v = 0 := by
  classical
  constructor
  · intro hv
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      funext i
      exact Fin.elim0 i
    · haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
      have hcol : ∀ j : Fin n,
        (fun i : Fin n => H i (Fin.castLE hn j)) ⬝ᵥ v = 0 := by
        intro j
        have h1 := congrFun hv (Fin.castLE hn j)
        simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using h1
      have hspan : Submodule.span (ZMod 2) (Set.range (fun j : Fin n =>
          fun i : Fin n => H i (Fin.castLE hn j))) = ⊤ := by
        apply LinearIndependent.span_eq_top_of_card_eq_finrank h
        rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      have hker : Submodule.span (ZMod 2) (Set.range (fun j : Fin n =>
          fun i : Fin n => H i (Fin.castLE hn j))) ≤
          LinearMap.ker (dotProductBilin (ZMod 2) (ZMod 2) v) := by
        apply Submodule.span_le.mpr
        rintro w ⟨j, rfl⟩
        change v ⬝ᵥ (fun i : Fin n => H i (Fin.castLE hn j)) = 0
        rw [dotProduct_comm]
        exact hcol j
      have hall : ∀ w : Fin n → ZMod 2, v ⬝ᵥ w = 0 := by
        intro w
        have hw : w ∈ Submodule.span (ZMod 2) (Set.range (fun j : Fin n =>
            fun i : Fin n => H i (Fin.castLE hn j))) := by
          rw [hspan]
          exact Submodule.mem_top
        have hmem := hker hw
        simpa [LinearMap.mem_ker] using hmem
      funext i
      have h := hall (Pi.single i 1)
      simpa [dotProduct_single] using h
  · intro hv
    rw [hv]
    exact Matrix.mulVec_zero _

lemma transpose_mulVec_mulVec_eq_zero_iff (hn : n ≤ N)
    (H2 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (h : LinearIndependent (ZMod 2)
      (fun j : Fin n => fun i : Fin n => H2 i (Fin.castLE hn j)))
    (b : Fin N → ZMod 2) : (H2ᵀ * H1) *ᵥ b = 0 ↔ H1 *ᵥ b = 0 := by
  rw [← Matrix.mulVec_mulVec]
  exact transpose_mulVec_eq_zero_iff hn H2 h (H1 *ᵥ b)

theorem qsen_eq_of_reduction (hn : n ≤ N) (H0 H1 H2 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hind : LinearIndependent (ZMod 2)
      (fun j : Fin n => fun i : Fin n => H2 i (Fin.castLE hn j)))
    (hlw : lwtr (H2ᵀ * H1) = lwtr (H0ᵀ * H1)) (x y : ℤ) :
    qsen (H2ᵀ * H1) (lwtr (H2ᵀ * H1)) x y =
      qsen H1 (lwtr (H0ᵀ * H1)) x y := by
  classical
  rw [hlw]
  unfold qsen
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : H1.mulVec b = 0
  · have hb2 : (H2ᵀ * H1).mulVec b = 0 :=
      (transpose_mulVec_mulVec_eq_zero_iff hn H2 H1 hind b).mpr hb
    rw [if_pos hb2, if_pos hb]
  · have hb2 : (H2ᵀ * H1).mulVec b ≠ 0 := fun hh =>
      hb ((transpose_mulVec_mulVec_eq_zero_iff hn H2 H1 hind b).mp hh)
    rw [if_neg hb2, if_neg hb]

theorem qsen_eq_of_lemma10 (hn : n ≤ N) (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1) (x y : ℤ) :
    ∃ H2 : Matrix (Fin n) (Fin N) (ZMod 2),
      qsen (H2ᵀ * H1) (lwtr (H2ᵀ * H1)) x y =
        qsen H1 (lwtr (H0ᵀ * H1)) x y := by
  obtain ⟨H2, hind, hlw, _⟩ := lemma10 hn H0 H1 hdiag
  exact ⟨H2, qsen_eq_of_reduction hn H0 H1 H2 hind hlw x y⟩

theorem qsen_eq_of_lemma10_problem3 (hn : n ≤ N)
    (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin N, (H0ᵀ * H1) i i = 1) (x y : ℤ) :
    ∃ A : Matrix (Fin N) (Fin N) (ZMod 2),
      diagMat A = 1 ∧
      qsen A (lwtr A) x y = qsen H1 (lwtr (H0ᵀ * H1)) x y := by
  classical
  have hdiag' : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1 := fun i => hdiag _
  obtain ⟨H2, hind, hlw, hdm⟩ := lemma10 hn H0 H1 hdiag'
  have hA : ∀ i, (H2ᵀ * H1) i i = (H0ᵀ * H1) i i := by
    intro i
    have := congrFun (congrFun hdm i) i
    simpa [diagMat] using this
  refine ⟨H2ᵀ * H1, ?_, ?_⟩
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [diagMat, hA, hdiag]
    · simp [diagMat, hij]
  · exact qsen_eq_of_reduction hn H0 H1 H2 hind hlw x y

end Qatlib.Papers.SignedWtEnum99.MainResults
