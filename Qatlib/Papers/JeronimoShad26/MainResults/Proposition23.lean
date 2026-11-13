/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JeronimoShad26.MainResults.SourceModel.Basic
import Mathlib.Analysis.Matrix.PosDef

set_option backward.isDefEq.respectTransparency false

/-!
# Finite-Ensemble Personick Minimum-MSE Estimator

This module formalizes Proposition 2.3 of Jeronimo and Shad: for any finite
quantum state ensemble `{(q_x, ρ_x)}` with real labels `z_x`, the symmetric
logarithmic derivative operator `L` solving `ρ̄ L + L ρ̄ = 2 ∑_x q_x z_x ρ_x` on
the support of `ρ̄ = ∑_x q_x ρ_x` exists and is unique, every finite-outcome
scalar POVM strategy has mean-square risk at least `∑_x q_x z_x² - Tr(L A)`, and
the spectral PVM of `L` attains this minimum risk.

## Main statements

* `proposition_2_3`: existence, uniqueness, Personick lower bound, and attainment
  of the minimum-MSE scalar quantum estimator.

## References

* [Jeronimo and Shad, 2026][JeronimoShad2026Shadow], Section 2, Proposition 2.3,
  Eqs. (8)--(9), p. 9.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Papers.JeronimoShad26.MainResults.Proposition23

open Matrix
open Qatlib.Papers.JeronimoShad26.MainResults.SourceModel
open scoped BigOperators
open scoped ComplexOrder MatrixOrder

private lemma psd_column_zero {d : ℕ} {B : Op d} (hB : B.PosSemidef)
    (a : Fin d) (ha : (B a a).re = 0) (b : Fin d) : B b a = 0 := by
  have hd : B a a = 0 := by
    have h := Complex.nonneg_iff.mp (hB.diag_nonneg (i := a))
    exact Complex.ext ha h.2.symm
  have hq : star (Pi.single a (1 : ℂ)) ⬝ᵥ (B *ᵥ Pi.single a 1) = 0 := by
    simpa using hd
  have hv := hB.dotProduct_mulVec_zero_iff.mp hq
  simpa using congrFun hv b

private lemma trace_product_nonneg {d : ℕ} {B C : Op d}
    (hB : B.PosSemidef) (hC : C.PosSemidef) : 0 ≤ (trace (B * C)).re := by
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  have h := Complex.nonneg_iff.mp (hC.mul_mul_conjTranspose_same S).trace_nonneg
  have ht : trace (B * C) = trace (S * C * Sᴴ) := by
    rw [hS]
    exact (trace_mul_cycle S C Sᴴ).symm
  rw [ht]
  exact h.1

private lemma diagonal_solution {d : ℕ} (e : Fin d → ℝ) (he : ∀ a, 0 ≤ e a)
    (B : Op d) (hB : B.IsHermitian)
    (hker : ∀ a b, e a = 0 ∨ e b = 0 → B a b = 0) :
    ∃ (P K : Op d), SupportedOn (diagonal (fun a => (e a : ℂ))) P ∧
      K.IsHermitian ∧ P * K * P = K ∧
      diagonal (fun a => (e a : ℂ)) * K + K * diagonal (fun a => (e a : ℂ)) =
        (2 : ℂ) • B ∧
      (∀ J : Op d, P * J * P = J →
        diagonal (fun a => (e a : ℂ)) * J + J * diagonal (fun a => (e a : ℂ)) =
          (2 : ℂ) • B → J = K) := by
  classical
  let p : Fin d → ℂ := fun a => if 0 < e a then 1 else 0
  let P : Op d := diagonal p
  let K : Op d := of fun a b =>
    if 0 < e a ∧ 0 < e b then 2 * B a b / ((e a + e b : ℝ) : ℂ) else 0
  have hp (a : Fin d) : star (p a) = p a := by simp [p]
  have hP : SupportedOn (diagonal (fun a => (e a : ℂ))) P := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact isHermitian_diagonal_iff.mpr hp
    · ext a b
      by_cases hab : a = b <;> by_cases ha : 0 < e a <;>
        simp [P, hab, p]
    · ext a b
      by_cases hab : a = b
      · subst b
        by_cases ha : 0 < e a
        · simp [P, p, ha]
        · have hz : e a = 0 := le_antisymm (le_of_not_gt ha) (he a)
          simp [P, p, hz]
      · simp [P, hab]
  have hK : K.IsHermitian := by
    ext a b
    have hb : star (B b a) = B a b := congrFun (congrFun hB a) b
    by_cases ha : 0 < e a <;> by_cases hc : 0 < e b <;>
      simp [K, conjTranspose_apply, ha, hc, hb, add_comm]
  have hPK : P * K * P = K := by
    ext a b
    by_cases ha : 0 < e a <;> by_cases hb : 0 < e b <;>
      simp [P, p, K, diagonal_mul, mul_diagonal, ha, hb]
  have hsolve : diagonal (fun a => (e a : ℂ)) * K +
      K * diagonal (fun a => (e a : ℂ)) = (2 : ℂ) • B := by
    ext a b
    simp only [Matrix.add_apply, diagonal_mul, mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    by_cases hab : 0 < e a ∧ 0 < e b
    · have hn : ((e a + e b : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (add_pos hab.1 hab.2)
      simp only [K, of_apply, hab.1, hab.2, and_self, ite_true]
      rw [mul_comm (e a : ℂ), ← mul_add, ← Complex.ofReal_add]
      exact div_mul_cancel₀ _ hn
    · have hz : e a = 0 ∨ e b = 0 := by
        by_cases ha : 0 < e a
        · exact Or.inr (le_antisymm (le_of_not_gt (fun hb => hab ⟨ha, hb⟩)) (he b))
        · exact Or.inl (le_antisymm (le_of_not_gt ha) (he a))
      simp [K, hab, hker a b hz]
  refine ⟨P, K, hP, hK, hPK, hsolve, ?_⟩
  intro J hJ hJE
  ext a b
  have hj := congrFun (congrFun hJ a) b
  have hs := congrFun (congrFun hJE a) b
  have hk := congrFun (congrFun hsolve a) b
  simp only [P, diagonal_mul, mul_diagonal] at hj
  simp only [Matrix.add_apply, diagonal_mul, mul_diagonal, Matrix.smul_apply,
    smul_eq_mul] at hs hk
  by_cases hab : 0 < e a ∧ 0 < e b
  · have hn : (e a : ℂ) + (e b : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (add_pos hab.1 hab.2)
    apply (mul_left_cancel₀ hn)
    linear_combination hs - hk
  · have hj0 : J a b = 0 := by
      by_cases ha : 0 < e a <;> by_cases hb : 0 < e b <;>
        simp_all [p]
    simp [hj0, K, hab]

private lemma support_solution {ι d : ℕ} (F : Ensemble ι d) (z : Fin ι → ℝ) :
    ∃ (P L : Op d), SupportedOn (avgOn F.weight F.state) P ∧
      L.IsHermitian ∧ P * L * P = L ∧
      avgOn F.weight F.state * L + L * avgOn F.weight F.state =
        (2 : ℂ) • avgOn F.weight (fun x => z x • F.state x) ∧
      (∀ J : Op d, P * J * P = J →
        avgOn F.weight F.state * J + J * avgOn F.weight F.state =
          (2 : ℂ) • avgOn F.weight (fun x => z x • F.state x) → J = L) := by
  classical
  let ρ : Op d := avgOn F.weight F.state
  let A : Op d := avgOn F.weight (fun x => z x • F.state x)
  have hρ : ρ.PosSemidef := posSemidef_sum _ fun x _ =>
    (F.state_density x).1.smul (F.weight_nonneg x)
  have hA : A.IsHermitian := isSelfAdjoint_sum _ fun x _ =>
    ((F.state_density x).1.1.smul (IsSelfAdjoint.all (z x))).smul
      (IsSelfAdjoint.all (F.weight x))
  let C := Unitary.conjStarAlgAut ℂ (Op d) hρ.1.eigenvectorUnitary
  let e := hρ.1.eigenvalues
  let D : Op d := diagonal (fun a => (e a : ℂ))
  have hρC : C D = ρ := hρ.1.spectral_theorem.symm
  have hdiag : C.symm ρ = D := by
    rw [← hρC]
    exact C.symm_apply_apply D
  let B : Op d := C.symm A
  have hB : B.IsHermitian := hA.isSelfAdjoint.map C.symm
  let T : Fin ι → Op d := fun x => C.symm (F.weight x • F.state x)
  have hT (x : Fin ι) : (T x).PosSemidef := by
    exact ((F.state_density x).1.smul (F.weight_nonneg x)).conjTranspose_mul_mul_same
      (hρ.1.eigenvectorUnitary : Op d)
  have hsumT : ∑ x, T x = D := by
    rw [← hdiag]
    exact (map_sum C.symm _ _).symm
  have hsumB : B = ∑ x, z x • T x := by
    simp only [B, A, avgOn, map_sum, T]
    congr 1
    funext x
    rw [smul_comm]
    simp [C]
  have hcol (a : Fin d) (ha : e a = 0) (b : Fin d) : B b a = 0 := by
    have hsum : ∑ x, ((T x) a a).re = 0 := by
      have hh := congrArg (fun M : Op d => (M a a).re) hsumT
      simpa [D, ha, Matrix.sum_apply] using hh
    have hz (x : Fin ι) : ((T x) a a).re = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun y _ =>
        (Complex.nonneg_iff.mp ((hT y).diag_nonneg (i := a))).1)).mp hsum x
        (Finset.mem_univ x)
    rw [hsumB]
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    exact Finset.sum_eq_zero fun x _ => by rw [psd_column_zero (hT x) a (hz x) b, smul_zero]
  have hker (a b : Fin d) (hab : e a = 0 ∨ e b = 0) : B a b = 0 := by
    rcases hab with ha | hb
    · have hh := congrFun (congrFun hB a) b
      simpa [conjTranspose_apply, hcol a ha b] using hh.symm
    · exact hcol b hb a
  obtain ⟨P, K, hP, hK, hPK, hsolve, huniq⟩ :=
    diagonal_solution e hρ.eigenvalues_nonneg B hB hker
  change SupportedOn D P at hP
  change D * K + K * D = (2 : ℂ) • B at hsolve
  change ∀ J : Op d, P * J * P = J → D * J + J * D = (2 : ℂ) • B → J = K at huniq
  have hAC : C B = A := C.apply_symm_apply A
  refine ⟨C P, C K, ⟨⟨hP.1.1.isSelfAdjoint.map C, ?_⟩, ?_⟩,
    hK.isSelfAdjoint.map C, ?_, ?_, ?_⟩
  · simpa only [map_mul] using congrArg C hP.1.2
  · simpa only [map_mul, hρC] using congrArg C hP.2
  · simpa only [map_mul] using congrArg C hPK
  · simpa only [map_add, map_mul, map_smul, hρC, hAC] using congrArg C hsolve
  · intro J hJP hJE
    have hh : C.symm J = K := by
      apply huniq
      · simpa only [map_mul, C.symm_apply_apply] using congrArg C.symm hJP
      · change ρ * J + J * ρ = (2 : ℂ) • A at hJE
        simpa only [map_add, map_mul, map_smul, hdiag] using congrArg C.symm hJE
    simpa only [C.apply_symm_apply] using congrArg C hh

private lemma born_avg {ι d : ℕ} (q : Fin ι → ℝ) (S : Fin ι → Op d) (E : Op d) :
    bornOn E (avgOn q S) = ∑ x, q x * bornOn E (S x) := by
  simp [bornOn, avgOn, Finset.mul_sum, trace_smul]

private lemma born_real_smul {d : ℕ} (E S : Op d) (r : ℝ) :
    bornOn E (r • S) = r * bornOn E S := by
  simp [bornOn, trace_smul]

private lemma risk_expansion {ι d m : ℕ} (F : Ensemble ι d) (z : Fin ι → ℝ)
    (N : Povm (Fin m) (Fin d)) (t : Fin m → ℝ) :
    scalarRisk F z N t = (∑ x, F.weight x * (z x) ^ 2) +
      (∑ w, (t w) ^ 2 * bornOn (N.effect w) (avgOn F.weight F.state)) -
      2 * ∑ w, t w * bornOn (N.effect w) (avgOn F.weight (fun x => z x • F.state x)) := by
  have hnorm (x : Fin ι) : ∑ w, bornOn (N.effect w) (F.state x) = 1 := by
    simp only [bornOn, ← Complex.re_sum, ← trace_sum, ← Finset.sum_mul, N.effect_total,
      one_mul, (F.state_density x).2, Complex.one_re]
  have hconst : ∑ w, ∑ x, F.weight x * (z x) ^ 2 *
      bornOn (N.effect w) (F.state x) = ∑ x, F.weight x * (z x) ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hnorm, mul_one]
  simp only [born_avg, born_real_smul]
  simp_rw [Finset.mul_sum]
  rw [← hconst]
  unfold scalarRisk
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro x _
  ring1

private lemma trace_balance {d : ℕ} (ρ A L : Op d)
    (hsolve : ρ * L + L * ρ = (2 : ℂ) • A) :
    (trace (L * A)).re = (trace (L * ρ * L)).re := by
  have h := congrArg (fun M : Op d => (trace (L * M)).re) hsolve
  have hc : trace (L * L * ρ) = trace (L * ρ * L) := (trace_mul_cycle L ρ L).symm
  simp only [mul_add, trace_add, Complex.add_re, hc, mul_smul_comm, trace_smul,
    smul_eq_mul, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, ← Matrix.mul_assoc] at h
  linear_combination -h / 2

private lemma square_expansion {d : ℕ} (ρ A L : Op d)
    (hsolve : ρ * L + L * ρ = (2 : ℂ) • A) (t : ℝ) :
    ((t : ℂ) • 1 - L) * ρ * ((t : ℂ) • 1 - L) =
      ((t : ℂ) ^ 2) • ρ - ((2 * t : ℝ) : ℂ) • A + L * ρ * L := by
  calc
    _ = ((t : ℂ) ^ 2) • ρ - (t : ℂ) • (ρ * L + L * ρ) + L * ρ * L := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
        smul_sub, smul_add, smul_smul, pow_two]
      abel
    _ = _ := by rw [hsolve, smul_smul]; congr 2; push_cast; ring_nf

private lemma risk_square_identity {ι d m : ℕ} (F : Ensemble ι d) (z : Fin ι → ℝ)
    (L : Op d)
    (hsolve : avgOn F.weight F.state * L + L * avgOn F.weight F.state =
      (2 : ℂ) • avgOn F.weight (fun x => z x • F.state x))
    (N : Povm (Fin m) (Fin d)) (t : Fin m → ℝ) :
    scalarRisk F z N t - ((∑ x, F.weight x * (z x) ^ 2) -
      (trace (L * avgOn F.weight (fun x => z x • F.state x))).re) =
    ∑ w, (trace (N.effect w *
      (((t w : ℂ) • 1 - L) * avgOn F.weight F.state * ((t w : ℂ) • 1 - L)))).re := by
  have htotal (B : Op d) : ∑ w, (trace (N.effect w * B)).re = (trace B).re := by
    rw [← Complex.re_sum, ← trace_sum, ← Finset.sum_mul, N.effect_total, one_mul]
  simp_rw [square_expansion _ _ _ hsolve, mul_add, mul_sub, mul_smul_comm,
    trace_add, trace_sub, trace_smul, Complex.add_re, Complex.sub_re]
  simp only [← Complex.ofReal_pow, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, htotal]
  rw [risk_expansion, trace_balance _ _ _ hsolve]
  simp only [bornOn]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring_nf

private lemma spectral_measurement {d : ℕ} (L : Op d) (hL : L.IsHermitian) :
    ∃ (N : Povm (Fin d) (Fin d)) (t : Fin d → ℝ),
      ∀ w, N.effect w * ((t w : ℂ) • 1 - L) = 0 := by
  classical
  let C := Unitary.conjStarAlgAut ℂ (Op d) hL.eigenvectorUnitary
  let t := hL.eigenvalues
  let D : Op d := diagonal (fun a => (t a : ℂ))
  let T : Fin d → Op d := fun w => diagonal (Pi.single w 1)
  let E : Fin d → Op d := fun w => C (T w)
  have hLD : L = C D := hL.spectral_theorem
  have hT (w : Fin d) : (T w).PosSemidef := by
    apply PosSemidef.diagonal
    intro a
    by_cases ha : a = w <;> simp [ha]
  have hE (w : Fin d) : (E w).PosSemidef :=
    (hT w).mul_mul_conjTranspose_same (hL.eigenvectorUnitary : Op d)
  have hsumT : ∑ w, T w = 1 := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp [T, Matrix.sum_apply, Pi.single_apply]
    · simp [T, Matrix.sum_apply, hab]
  have hsumE : ∑ w, E w = 1 := by
    rw [← map_sum C, hsumT, map_one]
  let N : Povm (Fin d) (Fin d) := ⟨E, hE, hsumE⟩
  refine ⟨N, t, ?_⟩
  intro w
  have hTD : T w * D = (t w : ℂ) • T w := by
    ext a b
    by_cases hab : a = b
    · subst b
      by_cases haw : a = w <;> simp [T, D, haw]
    · simp [T, D, mul_diagonal, hab]
  have hEL : E w * L = (t w : ℂ) • E w := by
    rw [hLD, ← map_mul, hTD, map_smul]
  change E w * ((t w : ℂ) • 1 - L) = 0
  rw [mul_sub, mul_smul_comm, mul_one, hEL, sub_self]

/-- **Proposition 2.3**: existence and uniqueness of the support-compressed
Personick operator `L` solving `ρ̄ L + L ρ̄ = 2 A`, universal MSE lower bound, and
attainment by a finite-outcome POVM strategy. -/
theorem proposition_2_3 (ι d : ℕ) (F : Ensemble ι d) (z : Fin ι → ℝ) :
    ∃ (P L : Op d),
      SupportedOn (avgOn F.weight F.state) P ∧
      L.IsHermitian ∧
      P * L * P = L ∧
      avgOn F.weight F.state * L + L * avgOn F.weight F.state =
        (2 : ℂ) • avgOn F.weight (fun x => z x • F.state x) ∧
      (∀ (L' : Op d), L'.IsHermitian → P * L' * P = L' →
        avgOn F.weight F.state * L' + L' * avgOn F.weight F.state =
          (2 : ℂ) • avgOn F.weight (fun x => z x • F.state x) → L' = L) ∧
      (∀ (m : ℕ) (N : Povm (Fin m) (Fin d)) (zhat : Fin m → ℝ),
        (∑ x, F.weight x * (z x) ^ 2) -
            (Matrix.trace (L * avgOn F.weight (fun x => z x • F.state x))).re
          ≤ scalarRisk F z N zhat) ∧
      (∃ (m : ℕ) (N : Povm (Fin m) (Fin d)) (zhat : Fin m → ℝ),
        scalarRisk F z N zhat =
          (∑ x, F.weight x * (z x) ^ 2) -
            (Matrix.trace (L * avgOn F.weight (fun x => z x • F.state x))).re) := by
  obtain ⟨P, L, hP, hL, hPL, hsolve, huniq⟩ := support_solution F z
  have hρ : (avgOn F.weight F.state).PosSemidef :=
    posSemidef_sum _ fun x _ => (F.state_density x).1.smul (F.weight_nonneg x)
  refine ⟨P, L, hP, hL, hPL, hsolve, ?_, ?_, ?_⟩
  · intro J _ hJP hJE
    exact huniq J hJP hJE
  · intro m N t
    have hnonneg : 0 ≤ ∑ w, (trace (N.effect w *
        (((t w : ℂ) • 1 - L) * avgOn F.weight F.state * ((t w : ℂ) • 1 - L)))).re := by
      apply Finset.sum_nonneg
      intro w _
      have hΔ : ((t w : ℂ) • (1 : Op d) - L).IsHermitian :=
        (isHermitian_one.smul (by simp [IsSelfAdjoint])).sub hL
      apply trace_product_nonneg (N.effect_pos w)
      simpa only [hΔ.eq] using
        hρ.conjTranspose_mul_mul_same ((t w : ℂ) • (1 : Op d) - L)
    rw [← risk_square_identity F z L hsolve N t] at hnonneg
    linarith
  · obtain ⟨N, t, hNt⟩ := spectral_measurement L hL
    refine ⟨d, N, t, ?_⟩
    have hid := risk_square_identity F z L hsolve N t
    have hz : ∑ w, (trace (N.effect w *
        (((t w : ℂ) • 1 - L) * avgOn F.weight F.state * ((t w : ℂ) • 1 - L)))).re = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      simp only [← Matrix.mul_assoc, hNt w, zero_mul, trace_zero, Complex.zero_re]
    rw [hz] at hid
    linarith

end Qatlib.Papers.JeronimoShad26.MainResults.Proposition23
