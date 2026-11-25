/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DQIOptim24.MainResults.IdealAlgebra
public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

/-!
# Norm of the binary ideal DQI state

Binary vectors on one Hamming shell are indexed by their support sets.
The distance condition makes the basis states at the selected syndromes
orthogonal. The support count then cancels each shell's normalizing factor.
-/

set_option autoImplicit false

open scoped BigOperators Classical
open Qatlib.Papers.DQIOptim24.MainResults.Source
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.DQIOptim24.MainResults

/-- A weight-`k` binary shell has one vector for each support of size `k`. -/
private theorem binary_shell_card (m k : ℕ) : (shell (ZMod 2) m k).card = m.choose k := by
  let supp (y : Fin m → ZMod 2) := Finset.univ.filter (fun i => y i ≠ 0)
  calc
    _ = ((Finset.univ : Finset (Fin m)).powersetCard k).card := by
      refine Finset.card_bij (fun y _ => supp y) ?_ ?_ ?_
      · intro y hy
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hy).2⟩
      · intro a _ b _ h
        funext i
        have hmem : i ∈ supp a ↔ i ∈ supp b := by rw [h]
        have he : a i ≠ 0 ↔ b i ≠ 0 := by simpa [supp] using hmem
        rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (a i) with ha | ha <;>
          rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (b i) with hb | hb <;>
          simp_all
      · intro s hs
        let y : Fin m → ZMod 2 := fun i => if i ∈ s then 1 else 0
        have he : supp y = s := by
          ext i
          by_cases hi : i ∈ s <;> simp [supp, y, hi]
        have hc := (Finset.mem_powersetCard.mp hs).2
        refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
        change (supp y).card = k
        exact he ▸ hc
    _ = _ := by rw [Finset.card_powersetCard]; simp

/-- The binary case of Lemma 9.1: with distance greater than twice the retained
weight, the squared norm of the ideal syndrome state is the sum of squared weights. -/
theorem idealState_normSq {m n L : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (g : (Fin m → ZMod 2) → ℂ) (d : ℕ) (hd : IsMinDistance B d) (hL : 2 * L < d)
    (hg : ∀ y, Complex.normSq (g y) = 1) (w : Fin (L + 1) → ℝ) :
    normSqFn (idealState B g w) = ∑ k : Fin (L + 1), w k ^ 2 := by
  classical
  let S := (Finset.univ : Finset (Fin (L + 1))).sigma
    (fun k => shell (ZMod 2) m k.val)
  let c (a : Σ _ : Fin (L + 1), Fin m → ZMod 2) : ℂ :=
    ((w a.1 / Real.sqrt (m.choose a.1.val : ℝ) : ℝ) : ℂ) * g a.2
  have hweight (a : S) : weight a.val.2 = a.val.1.val :=
    (Finset.mem_filter.mp (Finset.mem_sigma.mp a.property).2).2
  have hi : Function.Injective (fun a : S => syndrome B a.val.2) := by
    intro a b hab
    have hlow := Qatlib.Concepts.CodingDecoding.DecoderCapacity.lowWeight_injective
      (ZMod 2) (Fin m) (Fin n) (syndromeLin B) L (Qatlib.Papers.DQIOptim24.MainResults.kernelSeparated_of_minDistance B d L hd hL)
    have hae : a.val.2 = b.val.2 := hlow
      (by change weight a.val.2 ≤ L; rw [hweight a]; omega)
      (by change weight b.val.2 ≤ L; rw [hweight b]; omega) hab
    have he : a.val.1 = b.val.1 := by
      apply Fin.ext
      rw [← hweight a, ← hweight b, hae]
    apply Subtype.ext
    exact Sigma.ext he (heq_of_eq hae)
  let v (a : S) := Ket (syndrome B a.val.2)
  have hv (a b : S) : Inner (v a) (v b) = @ite ℂ (a = b) (Classical.propDecidable (a = b)) 1 0 := by
    change Inner (Ket _) (Ket _) = _
    rw [inner_ket_ket]
    by_cases h : a = b
    · subst b; simp
    · have he : syndrome B a.val.2 ≠ syndrome B b.val.2 := fun h' => h (hi h')
      simp [he, h]
  have hstate : idealState B g w = ∑ a : S, c a.val • v a := by
    unfold idealState
    change (∑ k : Fin (L + 1), ∑ y ∈ shell (ZMod 2) m k.val, c ⟨k,y⟩ • Ket (syndrome B y)) =
      ∑ a : S, c a.val • Ket (syndrome B a.val.2)
    rw [Finset.sum_sigma' (Finset.univ : Finset (Fin (L + 1)))
      (fun k => shell (ZMod 2) m k.val) (fun k y => c ⟨k,y⟩ • Ket (syndrome B y))]
    exact (Finset.sum_attach S (fun a => c a • Ket (syndrome B a.2))).symm
  have hnorm (f : (Fin n → ZMod 2) → ℂ) : normSqFn f = ∑ z, ‖f z‖ ^ 2 := by
    simp only [normSqFn, Qatlib.Papers.DQIOptim24.MainResults.Source.inner, Complex.re_sum, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hm : L ≤ m := by
    obtain ⟨y, _, _, hy⟩ := hd.2
    have hh : weight y ≤ m := by
      simpa [weight] using (hammingNorm_le_card_fintype (x := y))
    omega
  rw [hnorm, hstate, sum_norm_sq_orthonormal v (fun a : S => c a.val) hv]
  change (∑ a ∈ S.attach, ‖c a.val‖ ^ 2) = _
  rw [Finset.sum_attach S (fun a => ‖c a‖ ^ 2)]
  dsimp only [S]
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  have hchoose : 0 < (m.choose k.val : ℝ) := by
    exact_mod_cast Nat.choose_pos (show k.val ≤ m by omega)
  have hc (y : Fin m → ZMod 2) :
      ‖c ⟨k, y⟩‖ ^ 2 = w k ^ 2 / (m.choose k.val : ℝ) := by
    have hgy : ‖g y‖ ^ 2 = 1 := (Complex.normSq_eq_norm_sq (g y)) ▸ hg y
    dsimp [c]
    rw [norm_mul, mul_pow, hgy, mul_one, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, div_pow, Real.sq_sqrt hchoose.le]
  simp_rw [hc, Finset.sum_const, nsmul_eq_mul, binary_shell_card]
  field_simp

end Qatlib.Papers.DQIOptim24.MainResults
