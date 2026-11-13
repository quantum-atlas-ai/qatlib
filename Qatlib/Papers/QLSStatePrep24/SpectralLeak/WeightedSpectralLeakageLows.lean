/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLSStatePrep24.SpectralLeak.WeightedSpectralLeakageStat

/-!
# Bounds for weighted spectral leakage

This module proves `Clause30WeightedSpectralLeakage` from normalization, terminal stopping, and
row error bounds. Telescoping continuation masses establishes total stopping mass one, while
tail product estimates bound both weighted and unweighted leakage. See [LowSu2026] for the paper
context.

## Main statements

* `stopMass_telescope`: For a positive number of normalized rows with a deterministic terminal
  stop, the squared norms of the stopping coefficients sum to one.
* `Clause30WeightedSpectralLeakage_answer`: Legal band rows have total stopping mass one and
  satisfy the weighted and unweighted leakage bounds specified by
  `Clause30WeightedSpectralLeakage`.

## References

* [Low and Su, 2026][LowSu2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace Qatlib.Papers.QLSStatePrep24.SpectralLeak

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators

/-- The squared norms of the two components of a normalized state sum to one. -/
private theorem normalized_two_eq {ψ : QState (Fin 2)} (h : Normalized ψ) :
    ‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2 = 1 := by
  have h2 : ∑ i : Fin 2, ‖ψ i‖ ^ 2 = 1 := h
  rwa [Fin.sum_univ_two] at h2

/-- Each component of a normalized two-component state has squared norm at most one. -/
private theorem normalized_two_le {ψ : QState (Fin 2)} (h : Normalized ψ) (b : Fin 2) :
    ‖ψ b‖ ^ 2 ≤ 1 := by
  have hs := normalized_two_eq h
  have h0 : ‖ψ 0‖ ^ 2 ≤ 1 := by linarith [sq_nonneg (‖ψ 1‖)]
  have h1 : ‖ψ 1‖ ^ 2 ≤ 1 := by linarith [sq_nonneg (‖ψ 0‖)]
  fin_cases b
  · exact h0
  · exact h1

/-- The product of squared continuation amplitudes through the first `t` steps for label `u`. -/
private def contMass {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I) (t : ℕ) : ℝ :=
  ∏ l : Fin t, ‖ξ (l.val + 1) u 1‖ ^ 2

/-- The continuation mass before any steps is one. -/
private theorem contMass_zero {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I) :
    contMass ξ u 0 = 1 := by
  show (∏ l : Fin 0, ‖ξ (l.val + 1) u 1‖ ^ 2) = 1
  simp

/-- The continuation mass equals the product over `i < t` of the squared continuation amplitude
at step `i + 1`. -/
private theorem contMass_eq_prod_range {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I) (t : ℕ) :
    contMass ξ u t = ∏ i ∈ Finset.range t, ‖ξ (i + 1) u 1‖ ^ 2 :=
  Fin.prod_univ_eq_prod_range (fun k : ℕ => ‖ξ (k + 1) u 1‖ ^ 2) t

/-- The continuation mass through step `t + 1` is the previous mass times the squared
continuation amplitude at that step. -/
private theorem contMass_succ {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I) (t : ℕ) :
    contMass ξ u (t + 1) = contMass ξ u t * ‖ξ (t + 1) u 1‖ ^ 2 := by
  rw [contMass_eq_prod_range ξ u (t + 1), contMass_eq_prod_range ξ u t,
    Finset.prod_range_succ]

/-- The continuation mass is nonnegative. -/
private theorem contMass_nonneg {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I) (t : ℕ) :
    0 ≤ contMass ξ u t := by
  apply Finset.prod_nonneg
  intro i _
  exact sq_nonneg _

/-- If the first `n` rows are normalized and `t ≤ n`, the continuation mass through `t` steps is
at most one. -/
private theorem contMass_le_one {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I)
    {n t : ℕ} (ht : t ≤ n) (hnorm : ∀ j : ℕ, j < n → Normalized (ξ (j + 1) u)) :
    contMass ξ u t ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i _
    exact sq_nonneg _
  · intro i _
    exact normalized_two_le (hnorm i.val (by omega)) 1

/-- At a positive step `j`, the squared stopping amplitude is the squared stop component times
the continuation mass through `j - 1` steps. -/
private theorem stopCoefficient_sq {I : Type} {ξ : ℕ → I → QState (Fin 2)}
    (u : I) {j : ℕ} (hj : 0 < j) :
    ‖stopCoefficient ξ j u‖ ^ 2 = ‖ξ j u 0‖ ^ 2 * contMass ξ u (j - 1) := by
  have hj0 : j ≠ 0 := Nat.pos_iff_ne_zero.mp hj
  have hsc : stopCoefficient ξ j u = ξ j u 0 * ∏ l : Fin (j - 1), ξ (l.val + 1) u 1 := by
    simp [stopCoefficient, hj0]
  rw [hsc, norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
  rfl

/-- Reindexing the sum of `f(i + 1)` over `i < n` gives the sum of `f` over the integers from
one to `n`. -/
private theorem sum_range_add_one {α : Type} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    (∑ i ∈ Finset.range n, f (i + 1)) = ∑ l ∈ Finset.Icc 1 n, f l := by
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro i₁ _ i₂ _ h
    exact Nat.succ.inj h
  · intro l hl
    simp only [Finset.mem_Icc] at hl
    refine ⟨l - 1, by simp only [Finset.mem_range]; omega, Nat.sub_add_cancel (by omega)⟩
  · intro i hi
    rfl

/-- The sum of `f(j + 1)` over `Fin m` equals the sum of `f` over the natural interval from one
to `m`. -/
private theorem sum_fin_add_one {α : Type} [AddCommMonoid α] (m : ℕ) (f : ℕ → α) :
    (∑ j : Fin m, f (j.val + 1)) = ∑ l ∈ Finset.Icc 1 m, f l :=
  (Fin.sum_univ_eq_sum_range (fun k : ℕ => f (k + 1)) m).trans (sum_range_add_one m f)

/-- Shifting the indices in the squared error product over `[n, b)` gives the product over `[n +
1, b + 1)`. -/
private theorem prod_Ico_shift (δ : ℕ → ℝ) (n b : ℕ) :
    (∏ i ∈ Finset.Ico n b, δ (i + 1) ^ 2)
      = ∏ l ∈ Finset.Ico (n + 1) (b + 1), δ l ^ 2 := by
  refine Finset.prod_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_Ico] at hi ⊢
    omega
  · intro i₁ _ i₂ _ h
    exact Nat.succ.inj h
  · intro l hl
    simp only [Finset.mem_Ico] at hl
    refine ⟨l - 1, by simp only [Finset.mem_Ico]; omega, Nat.sub_add_cancel (by omega)⟩
  · intro i hi
    rfl

/-- If the tail errors lie in `[0, 1/3]` and `n + 1 ≤ b`, their squared product is at most `δ
b²`. -/
private theorem tail_prod_le (δ : ℕ → ℝ) (n b : ℕ)
    (hδ : ∀ l, n + 1 ≤ l → l ≤ b → 0 ≤ δ l ∧ δ l ≤ 1 / 3) (hge : n + 1 ≤ b) :
    (∏ l ∈ Finset.Ico (n + 1) (b + 1), δ l ^ 2) ≤ δ b ^ 2 := by
  rw [Finset.prod_Ico_succ_top hge]
  have hle : (∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i _
      exact sq_nonneg _
    · intro i hi
      have hi' : n + 1 ≤ i ∧ i < b := Finset.mem_Ico.mp hi
      have hd := hδ i hi'.1 (by omega)
      nlinarith [hd.1, hd.2]
  have hd : 0 ≤ δ b ^ 2 := sq_nonneg _
  nlinarith

/-- For a nonempty tail of errors in `[0, 1/3]`, multiplying their squared product by `9^(b +
1)` is bounded by `9^(n + 2) * δ b²`. -/
private theorem tail_prod_weighted_le (δ : ℕ → ℝ) (n b : ℕ)
    (hδ : ∀ l, n + 1 ≤ l → l ≤ b → 0 ≤ δ l ∧ δ l ≤ 1 / 3) (hge : n + 1 ≤ b) :
    (∏ l ∈ Finset.Ico (n + 1) (b + 1), δ l ^ 2) * (9 : ℝ) ^ (b + 1)
      ≤ (9 : ℝ) ^ (n + 2) * δ b ^ 2 := by
  have hsp : (∏ l ∈ Finset.Ico (n + 1) (b + 1), δ l ^ 2)
      = δ b ^ 2 * ∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2 := by
    rw [Finset.prod_Ico_succ_top hge]
    ring
  have hle9 : (∏ l ∈ Finset.Ico (n + 1) b, (9 : ℝ) * δ l ^ 2) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i _
      exact mul_nonneg (by norm_num) (sq_nonneg _)
    · intro i hi
      have hi' : n + 1 ≤ i ∧ i < b := Finset.mem_Ico.mp hi
      have hd := hδ i hi'.1 (by omega)
      nlinarith [hd.1, hd.2]
  have hkey : (9 : ℝ) ^ (b - (n + 1)) * ∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2 ≤ 1 := by
    have h1 : (∏ l ∈ Finset.Ico (n + 1) b, (9 : ℝ) * δ l ^ 2)
        = (9 : ℝ) ^ (b - (n + 1)) * ∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2 := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
    rw [← h1]
    exact hle9
  have hexp : (9 : ℝ) ^ (b + 1)
      = (9 : ℝ) ^ (n + 2) * (9 : ℝ) ^ (b - (n + 1)) := by
    have : b + 1 = n + 2 + (b - (n + 1)) := by omega
    rw [this, pow_add]
  calc (∏ l ∈ Finset.Ico (n + 1) (b + 1), δ l ^ 2) * (9 : ℝ) ^ (b + 1)
      = (δ b ^ 2 * ∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2) * (9 : ℝ) ^ (b + 1) := by rw [hsp]
    _ = δ b ^ 2 * ((9 : ℝ) ^ (b + 1) * ∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2) := by ring
    _ = δ b ^ 2 *
        ((9 : ℝ) ^ (n + 2) * ((9 : ℝ) ^ (b - (n + 1)) * ∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2)) := by
        rw [hexp]
        ring
    _ ≤ δ b ^ 2 * ((9 : ℝ) ^ (n + 2) * 1) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_left hkey (pow_nonneg (by norm_num) _)
    _ = (9 : ℝ) ^ (n + 2) * δ b ^ 2 := by ring

/-- For a positive number of normalized rows with a deterministic terminal stop, the squared
norms of the stopping coefficients sum to one. -/
private theorem stopMass_telescope {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I) (m : ℕ)
    (hm : 0 < m) (hnorm : ∀ j : ℕ, j < m → Normalized (ξ (j + 1) u))
    (hstop : ξ m u = (fun b => if b = 0 then 1 else 0)) :
    (∑ j : Fin m, ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2) = 1 := by
  have hz : ∀ j : Fin m, ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2
      = contMass ξ u j.val - contMass ξ u (j.val + 1) := by
    intro j
    have hj : 0 < j.val + 1 := Nat.succ_pos _
    rw [stopCoefficient_sq u hj, Nat.add_sub_cancel]
    have h01 := normalized_two_eq (hnorm j.val j.is_lt)
    have hc := contMass_succ ξ u j.val
    have hre : ‖ξ (j.val + 1) u 0‖ ^ 2 = 1 - ‖ξ (j.val + 1) u 1‖ ^ 2 := by linarith
    rw [hre, hc]
    ring
  have h2 : (∑ j : Fin m, ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2)
      = ∑ i ∈ Finset.range m, (contMass ξ u i - contMass ξ u (i + 1)) :=
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖stopCoefficient ξ (i + 1) u‖ ^ 2) m).trans
      (Finset.sum_congr rfl (fun i hi => hz ⟨i, Finset.mem_range.mp hi⟩))
  rw [h2, Finset.sum_range_sub', contMass_zero]
  have hm0 : contMass ξ u m = 0 := by
    rw [contMass_eq_prod_range]
    refine Finset.prod_eq_zero (f := fun i : ℕ => ‖ξ (i + 1) u 1‖ ^ 2) (i := m - 1) ?_ ?_
    · exact Finset.mem_range.mpr (by omega)
    · have hsu : ξ m u 1 = 0 := by
        rw [hstop]
        simp
      have hidx : m - 1 + 1 = m := by omega
      show ‖ξ (m - 1 + 1) u 1‖ ^ 2 = 0
      rw [hidx, hsu]
      simp
  rw [hm0]
  ring

/-- Legal band rows have total stopping mass one and satisfy the weighted and unweighted leakage
bounds specified by `Clause30WeightedSpectralLeakage`. See [LowSu2026]. -/
theorem Clause30WeightedSpectralLeakage_answer : Clause30WeightedSpectralLeakage := by
  intro I _ m k γ ξ δ hleg
  obtain ⟨hm, hk, hδ, hstop, hnorm, hbefore, hafter⟩ := hleg
  have hδ' : ∀ j : ℕ, j < m → 0 ≤ δ (j + 1) ∧ δ (j + 1) ≤ 1 / 3 := fun j hj => hδ ⟨j, hj⟩
  have hnorm' : ∀ j : ℕ, j < m → ∀ v : I, Normalized (ξ (j + 1) v) :=
    fun j hj v => hnorm ⟨j, hj⟩ v
  have hbefore' : ∀ j : ℕ, j < m → ∀ v : I, j + 1 < k v → ‖ξ (j + 1) v 0‖ ≤ δ (j + 1) :=
    fun j hj v h => hbefore ⟨j, hj⟩ v h
  have hafter' : ∀ j : ℕ, j < m → ∀ v : I, k v + 1 ≤ j + 1 → ‖ξ (j + 1) v 1‖ ≤ δ (j + 1) :=
    fun j hj v h => hafter ⟨j, hj⟩ v h
  have hstop' : ∀ v : I, ξ m v = (fun b => if b = 0 then 1 else 0) := hstop
  have hδ'' : ∀ r : ℕ, 1 ≤ r → r < m → 0 ≤ δ r ∧ δ r ≤ 1 / 3 := by
    intro r hr1 hr2
    have := hδ' (r - 1) (by omega)
    rwa [Nat.sub_add_cancel hr1] at this
  have hnorm'' : ∀ r : ℕ, 1 ≤ r → r < m → ∀ v : I, Normalized (ξ r v) := by
    intro r hr1 hr v
    have := hnorm' (r - 1) (by omega) v
    rwa [Nat.sub_add_cancel hr1] at this
  have hbefore'' : ∀ r : ℕ, 1 ≤ r → r < m → ∀ v : I, r < k v → ‖ξ r v 0‖ ≤ δ r := by
    intro r hr1 hr v h
    have := hbefore' (r - 1) (by omega) v (by omega)
    rwa [Nat.sub_add_cancel hr1] at this
  have hafter'' : ∀ r : ℕ, 1 ≤ r → r < m → ∀ v : I, k v + 1 ≤ r → ‖ξ r v 1‖ ≤ δ r := by
    intro r hr1 hr v h
    have := hafter' (r - 1) (by omega) v (by omega)
    rwa [Nat.sub_add_cancel hr1] at this
  show (∀ u, (∑ j : Fin m, ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2) = 1) ∧
      bandLeakage m k γ (stopCoefficient ξ) true ≤
        9 * singleBandProbability m k γ * (∑ j : Fin m, δ (j.val + 1)) ^ 2 ∧
      bandLeakage m k γ (stopCoefficient ξ) false ≤
        singleBandProbability m k γ / 9 * (∑ j : Fin m, δ (j.val + 1)) ^ 2
  have hnormMain : ∀ u : I, (∑ j : Fin m, ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2) = 1 :=
    fun u => stopMass_telescope ξ u m hm (fun j hj => hnorm' j hj u) (hstop' u)

  have hsplit : ∀ (n : ℕ) (f : Fin m → ℝ),
      (∑ j : Fin m, (if j.val + 1 ≠ n ∧ j.val + 1 ≠ n + 1 then f j else 0))
        = (∑ j : Fin m, (if j.val + 1 < n then f j else 0))
          + (∑ j : Fin m, (if n + 1 < j.val + 1 then f j else 0)) := by
    intro n f
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> first | (exfalso; omega) | ring

  have hbefore_le : ∀ (u : I) (j : Fin m), j.val + 1 < k u →
      ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 ≤ δ (j.val + 1) ^ 2 := by
    intro u j hj
    have hj' : 0 < j.val + 1 := Nat.succ_pos _
    rw [stopCoefficient_sq u hj', Nat.add_sub_cancel]
    have hb := hbefore' j.val j.is_lt u hj
    have hc := contMass_le_one ξ u j.is_lt.le (fun l hl => hnorm' l (by omega) u)
    have hd0 : 0 ≤ δ (j.val + 1) := (hδ' j.val j.is_lt).1
    have hp2 : ‖ξ (j.val + 1) u 0‖ ^ 2 ≤ δ (j.val + 1) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (norm_nonneg _) hb
    have hstep : ‖ξ (j.val + 1) u 0‖ ^ 2 * contMass ξ u j.val
        ≤ ‖ξ (j.val + 1) u 0‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    linarith
  have hafter_le : ∀ (u : I) (j : Fin m), k u + 1 < j.val + 1 →
      ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 ≤ δ j.val ^ 2 := by
    intro u j hj
    have hj' : 0 < j.val + 1 := Nat.succ_pos _
    have hn : k u < m := hk u
    have hge : k u + 1 ≤ j.val := by omega
    rw [stopCoefficient_sq u hj', Nat.add_sub_cancel]
    have hle : (∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2)
        ≤ ∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), δ l ^ 2 := by
      have h1 : (∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2)
          = ∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), ‖ξ l u 1‖ ^ 2 := prod_Ico_shift (fun l : ℕ => ‖ξ l u 1‖) (k u) (j.val)
      rw [h1]
      apply Finset.prod_le_prod₀
      · intro i _
        exact sq_nonneg _
      · intro i hi
        have hi' : k u + 1 ≤ i ∧ i < j.val + 1 := Finset.mem_Ico.mp hi
        have hlt : i < m := by omega
        have ha := hafter'' i (by omega) hlt u (by omega)
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (norm_nonneg _) ha
    have hle2 : (∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), δ l ^ 2) ≤ δ j.val ^ 2 :=
      tail_prod_le δ (k u) j.val (fun l hl hl' => hδ'' l (by omega) (by omega)) hge
    have hc : contMass ξ u j.val ≤ δ j.val ^ 2 := by
      have hsplitP : contMass ξ u j.val
          = contMass ξ u (k u) * ∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2 := by
        rw [contMass_eq_prod_range ξ u j.val, contMass_eq_prod_range ξ u (k u),
          ← Finset.prod_range_mul_prod_Ico _ (by omega : k u ≤ j.val)]
      rw [hsplitP]
      have hn1 : contMass ξ u (k u) ≤ 1 :=
        contMass_le_one ξ u (Nat.le_refl _) (fun l hl => hnorm' l (by omega) u)
      have hstep1 : contMass ξ u (k u) * ∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2
          ≤ 1 * ∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), δ l ^ 2 := by
        apply mul_le_mul hn1 hle
        · exact Finset.prod_nonneg fun i _ => sq_nonneg _
        · exact zero_le_one
      have hstep2 : (1 : ℝ) * ∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), δ l ^ 2 ≤ δ j.val ^ 2 := by
        rw [one_mul]
        exact hle2
      exact hstep1.trans hstep2
    have hnorm0 : ‖ξ (j.val + 1) u 0‖ ^ 2 ≤ 1 :=
      normalized_two_le (hnorm' j.val j.is_lt u) 0
    have hstep : ‖ξ (j.val + 1) u 0‖ ^ 2 * contMass ξ u j.val ≤ 1 * contMass ξ u j.val :=
      mul_le_mul_of_nonneg_right hnorm0 (contMass_nonneg ξ u j.val)
    linarith
  have hbefore_w : ∀ (u : I) (j : Fin m), j.val + 1 < k u →
      ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1)
        ≤ (9 : ℝ) ^ (k u + 2) * δ (j.val + 1) ^ 2 := by
    intro u j hj
    have h1 := hbefore_le u j hj
    have h2 : (9 : ℝ) ^ (j.val + 1) ≤ (9 : ℝ) ^ (k u + 2) := by
      apply pow_le_pow_right₀
      · norm_num
      · omega
    have hd : 0 ≤ δ (j.val + 1) ^ 2 := sq_nonneg _
    have hp : 0 ≤ (9 : ℝ) ^ (j.val + 1) := pow_nonneg (by norm_num) _
    have h3 : ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1)
        ≤ δ (j.val + 1) ^ 2 * (9 : ℝ) ^ (j.val + 1) :=
      mul_le_mul_of_nonneg_right h1 hp
    have h4 : δ (j.val + 1) ^ 2 * (9 : ℝ) ^ (j.val + 1)
        ≤ δ (j.val + 1) ^ 2 * (9 : ℝ) ^ (k u + 2) :=
      mul_le_mul_of_nonneg_left h2 hd
    have h4' : δ (j.val + 1) ^ 2 * (9 : ℝ) ^ (k u + 2)
        = (9 : ℝ) ^ (k u + 2) * δ (j.val + 1) ^ 2 := by ring
    rw [h4'] at h4
    exact h3.trans h4
  have hafter_w : ∀ (u : I) (j : Fin m), k u + 1 < j.val + 1 →
      ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1)
        ≤ (9 : ℝ) ^ (k u + 2) * δ j.val ^ 2 := by
    intro u j hj
    have hj' : 0 < j.val + 1 := Nat.succ_pos _
    have hn : k u < m := hk u
    have hge : k u + 1 ≤ j.val := by omega
    rw [stopCoefficient_sq u hj', Nat.add_sub_cancel]
    have hle : (∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2)
        ≤ ∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), δ l ^ 2 := by
      have h1 : (∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2)
          = ∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), ‖ξ l u 1‖ ^ 2 := prod_Ico_shift (fun l : ℕ => ‖ξ l u 1‖) (k u) (j.val)
      rw [h1]
      apply Finset.prod_le_prod₀
      · intro i _
        exact sq_nonneg _
      · intro i hi
        have hi' : k u + 1 ≤ i ∧ i < j.val + 1 := Finset.mem_Ico.mp hi
        have hlt : i < m := by omega
        have ha := hafter'' i (by omega) hlt u (by omega)
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (norm_nonneg _) ha
    have hbound' : (∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), δ l ^ 2) * (9 : ℝ) ^ (j.val + 1)
        ≤ (9 : ℝ) ^ (k u + 2) * δ j.val ^ 2 :=
      tail_prod_weighted_le δ (k u) j.val (fun l hl hl' => hδ'' l (by omega) (by omega)) hge
    have hpow : 0 ≤ (9 : ℝ) ^ (j.val + 1) := pow_nonneg (by norm_num) _
    have hc : ‖ξ (j.val + 1) u 0‖ ^ 2 * contMass ξ u j.val * (9 : ℝ) ^ (j.val + 1)
        ≤ (9 : ℝ) ^ (k u + 2) * δ j.val ^ 2 := by
      have hsplitP : contMass ξ u j.val
          = contMass ξ u (k u) * ∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2 := by
        rw [contMass_eq_prod_range ξ u j.val, contMass_eq_prod_range ξ u (k u),
          ← Finset.prod_range_mul_prod_Ico _ (by omega : k u ≤ j.val)]
      rw [hsplitP]
      have hn1 : contMass ξ u (k u) ≤ 1 :=
        contMass_le_one ξ u (Nat.le_refl _) (fun l hl => hnorm' l (by omega) u)
      have hnorm0 : ‖ξ (j.val + 1) u 0‖ ^ 2 ≤ 1 :=
        normalized_two_le (hnorm' j.val j.is_lt u) 0
      have hp : 0 ≤ ∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2 :=
        Finset.prod_nonneg fun i _ => sq_nonneg _
      calc ‖ξ (j.val + 1) u 0‖ ^ 2
          * (contMass ξ u (k u) * ∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2)
          * (9 : ℝ) ^ (j.val + 1)
          ≤ 1 * (contMass ξ u (k u) * ∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2)
            * (9 : ℝ) ^ (j.val + 1) := by
              apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) _)
              exact mul_le_mul_of_nonneg_right hnorm0
                (mul_nonneg (contMass_nonneg ξ u (k u)) hp)
        _ = (contMass ξ u (k u) * ∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2)
            * (9 : ℝ) ^ (j.val + 1) := by ring
        _ ≤ (∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), δ l ^ 2) * (9 : ℝ) ^ (j.val + 1) := by
              apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) _)
              have h := mul_le_mul hn1 hle
                (Finset.prod_nonneg fun i _ => sq_nonneg _) zero_le_one
              rwa [one_mul] at h
        _ ≤ (9 : ℝ) ^ (k u + 2) * δ j.val ^ 2 := hbound'
    exact hc

  have hsum_split : ∀ (n : ℕ), n < m →
      (∑ j : Fin m, (if j.val + 1 < n then δ (j.val + 1) ^ 2 else 0))
        + (∑ j : Fin m, (if n + 1 < j.val + 1 then δ j.val ^ 2 else 0))
        ≤ (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by
    intro n hn
    have hA : (∑ j : Fin m, (if j.val + 1 < n then δ (j.val + 1) ^ 2 else 0))
        = ∑ l ∈ Finset.Icc 1 (n - 1), δ l ^ 2 := by
      have h2 : (∑ j : Fin m, (if j.val + 1 < n then δ (j.val + 1) ^ 2 else 0))
          = ∑ i ∈ Finset.range m, (if i + 1 < n then δ (i + 1) ^ 2 else 0) :=
        Fin.sum_univ_eq_sum_range (fun k : ℕ => if k + 1 < n then δ (k + 1) ^ 2 else 0) m
      have h3 : (∑ i ∈ Finset.range m, (if i + 1 < n then δ (i + 1) ^ 2 else 0))
          = ∑ l ∈ Finset.Icc 1 m, (if l < n then δ l ^ 2 else 0) :=
        sum_range_add_one m (fun l => if l < n then δ l ^ 2 else 0)
      have h4 : (∑ l ∈ Finset.Icc 1 m, (if l < n then δ l ^ 2 else 0))
          = ∑ l ∈ Finset.Icc 1 (n - 1), δ l ^ 2 := by
        rw [← Finset.sum_filter]
        congr 1
        ext l
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, by omega⟩
        · intro ⟨h1, h2⟩
          exact ⟨⟨h1, by omega⟩, by omega⟩
      exact h2.trans (h3.trans h4)
    have hB : (∑ j : Fin m, (if n + 1 < j.val + 1 then δ j.val ^ 2 else 0))
        = ∑ l ∈ Finset.Icc (n + 1) (m - 1), δ l ^ 2 := by
      have h2 : (∑ j : Fin m, (if n + 1 < j.val + 1 then δ j.val ^ 2 else 0))
          = ∑ i ∈ Finset.range m, (if n + 1 < i + 1 then δ i ^ 2 else 0) :=
        Fin.sum_univ_eq_sum_range (fun k : ℕ => if n + 1 < k + 1 then δ k ^ 2 else 0) m
      have h3 : (∑ i ∈ Finset.range m, (if n + 1 < i + 1 then δ i ^ 2 else 0))
          = ∑ i ∈ Finset.range m, (if n + 1 ≤ i then δ i ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : n + 1 < i + 1 <;> by_cases h' : n + 1 ≤ i <;> simp [h, h'] <;> omega
      have h4 : (∑ i ∈ Finset.range m, (if n + 1 ≤ i then δ i ^ 2 else 0))
          = ∑ l ∈ Finset.Icc (n + 1) (m - 1), δ l ^ 2 := by
        rw [← Finset.sum_filter]
        congr 1
        ext l
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        constructor
        · intro ⟨h1, h2⟩
          exact ⟨h2, by omega⟩
        · intro ⟨h1, h2⟩
          exact ⟨by omega, h1⟩
      exact h2.trans (h3.trans h4)
    have hdisj : Disjoint (Finset.Icc 1 (n - 1)) (Finset.Icc (n + 1) (m - 1)) := by
      apply Finset.disjoint_left.mpr
      intro l hl1 hl2
      simp only [Finset.mem_Icc] at hl1 hl2
      omega
    have hsub : Finset.Icc 1 (n - 1) ∪ Finset.Icc (n + 1) (m - 1) ⊆ Finset.Icc 1 m := by
      intro l hl
      simp only [Finset.mem_union, Finset.mem_Icc] at hl ⊢
      omega
    have hle : (∑ l ∈ Finset.Icc 1 (n - 1), δ l ^ 2)
        + (∑ l ∈ Finset.Icc (n + 1) (m - 1), δ l ^ 2)
        ≤ ∑ l ∈ Finset.Icc 1 m, δ l ^ 2 := by
      rw [← Finset.sum_union hdisj]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => sq_nonneg _)
    have hfinal : (∑ l ∈ Finset.Icc 1 m, δ l ^ 2) ≤ (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by
      have h := Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset (Fin m))) (f := fun j => δ (j.val + 1))
        (fun j _ => (hδ' j.val j.is_lt).1)
      have h2 : (∑ l ∈ Finset.Icc 1 m, δ l ^ 2) = ∑ j : Fin m, δ (j.val + 1) ^ 2 :=
        (sum_fin_add_one m (fun l => δ l ^ 2)).symm
      rw [h2]
      exact h
    rw [hA, hB]
    exact hle.trans hfinal

  have key_uw : ∀ u : I,
      (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
        ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 else 0))
        ≤ (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by
    intro u
    have hn : k u < m := hk u
    rw [hsplit (k u) (fun j => ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2)]
    have h1 : (∑ j : Fin m, (if j.val + 1 < k u then
        ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 else 0))
        ≤ ∑ j : Fin m, (if j.val + 1 < k u then δ (j.val + 1) ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : j.val + 1 < k u
      · simp [h]
        exact hbefore_le u j h
      · simp [h]
    have h2 : (∑ j : Fin m, (if k u + 1 < j.val + 1 then
        ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 else 0))
        ≤ ∑ j : Fin m, (if k u + 1 < j.val + 1 then δ j.val ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : k u + 1 < j.val + 1
      · simp [h]
        exact hafter_le u j h
      · simp [h]
    exact (add_le_add h1 h2).trans (hsum_split (k u) hn)
  have key_w : ∀ u : I,
      (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
        ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1) else 0))
        ≤ (9 : ℝ) ^ (k u + 2) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by
    intro u
    have hn : k u < m := hk u
    rw [hsplit (k u) (fun j => ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1))]
    have h1 : (∑ j : Fin m, (if j.val + 1 < k u then
        ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1) else 0))
        ≤ (9 : ℝ) ^ (k u + 2) * ∑ j : Fin m, (if j.val + 1 < k u then δ (j.val + 1) ^ 2 else 0) := by
      have h1a : (∑ j : Fin m, (if j.val + 1 < k u then
          ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1) else 0))
          ≤ ∑ j : Fin m, (if j.val + 1 < k u then
            (9 : ℝ) ^ (k u + 2) * δ (j.val + 1) ^ 2 else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : j.val + 1 < k u
        · simp [h]
          exact hbefore_w u j h
        · simp [h]
      have h1b : (∑ j : Fin m, (if j.val + 1 < k u then
          (9 : ℝ) ^ (k u + 2) * δ (j.val + 1) ^ 2 else 0))
          = (9 : ℝ) ^ (k u + 2) * ∑ j : Fin m, (if j.val + 1 < k u then δ (j.val + 1) ^ 2 else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by
          by_cases h : j.val + 1 < k u <;> simp [h])
      exact h1a.trans (le_of_eq h1b)
    have h2 : (∑ j : Fin m, (if k u + 1 < j.val + 1 then
        ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1) else 0))
        ≤ (9 : ℝ) ^ (k u + 2) * ∑ j : Fin m, (if k u + 1 < j.val + 1 then δ j.val ^ 2 else 0) := by
      have h2a : (∑ j : Fin m, (if k u + 1 < j.val + 1 then
          ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1) else 0))
          ≤ ∑ j : Fin m, (if k u + 1 < j.val + 1 then
            (9 : ℝ) ^ (k u + 2) * δ j.val ^ 2 else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : k u + 1 < j.val + 1
        · simp [h]
          exact hafter_w u j h
        · simp [h]
      have h2b : (∑ j : Fin m, (if k u + 1 < j.val + 1 then
          (9 : ℝ) ^ (k u + 2) * δ j.val ^ 2 else 0))
          = (9 : ℝ) ^ (k u + 2) * ∑ j : Fin m, (if k u + 1 < j.val + 1 then δ j.val ^ 2 else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by
          by_cases h : k u + 1 < j.val + 1 <;> simp [h])
      exact h2a.trans (le_of_eq h2b)
    have h3 := add_le_add h1 h2
    have h4 : (9 : ℝ) ^ (k u + 2) * ∑ j : Fin m, (if j.val + 1 < k u then δ (j.val + 1) ^ 2 else 0)
        + (9 : ℝ) ^ (k u + 2) * ∑ j : Fin m, (if k u + 1 < j.val + 1 then δ j.val ^ 2 else 0)
        = (9 : ℝ) ^ (k u + 2) *
          ((∑ j : Fin m, (if j.val + 1 < k u then δ (j.val + 1) ^ 2 else 0))
            + ∑ j : Fin m, (if k u + 1 < j.val + 1 then δ j.val ^ 2 else 0)) := by
      ring
    rw [h4] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left (hsum_split (k u) hn)
      (pow_nonneg (by norm_num) _))

  refine ⟨hnormMain, ?_, ?_⟩
  · simp only [bandLeakage, singleBandProbability, if_true]
    have hpow9 : ∀ u : I, (9 : ℝ) * (9 : ℝ) ^ (k u + 1) = (9 : ℝ) ^ (k u + 2) := by
      intro u
      have h := pow_succ (a := (9:ℝ)) (n := k u + 1)
      have h2 : (k u + 2 : ℕ) = k u + 1 + 1 := by omega
      rw [h2, h]
      ring
    have hform : (9 : ℝ) * (∑ u, ‖γ u‖ ^ 2 * (9 : ℝ) ^ (k u + 1) / (9 : ℝ) ^ m)
          * (∑ j : Fin m, δ (j.val + 1)) ^ 2
        = ∑ u, ‖γ u‖ ^ 2 *
            ((9 : ℝ) ^ (k u + 2) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 / (9 : ℝ) ^ m) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      have h9 := hpow9 u
      field_simp
      ring
    rw [hform]
    apply Finset.sum_le_sum
    intro u _
    have hkey := key_w u
    have hinner : (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
        ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1) / (9 : ℝ) ^ m else 0))
        = (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
          ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1) else 0)) / (9 : ℝ) ^ m := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs <;> simp
    rw [hinner]
    have hpow : (0 : ℝ) < (9 : ℝ) ^ m := pow_pos (by norm_num) _
    have hg : 0 ≤ ‖γ u‖ ^ 2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_left
      ((div_le_div_iff_of_pos_right hpow).mpr hkey) hg
  · simp only [bandLeakage, singleBandProbability, Bool.false_eq_true, if_false]
    have h9 : ∀ u : I, (9 : ℝ) ^ (k u + 1) / 9 = (9 : ℝ) ^ (k u) := by
      intro u
      rw [pow_succ (a := (9:ℝ)) (n := k u)]
      field_simp
      try ring
    have hform : (∑ u, ‖γ u‖ ^ 2 * (9 : ℝ) ^ (k u + 1) / (9 : ℝ) ^ m) / 9
          * (∑ j : Fin m, δ (j.val + 1)) ^ 2
        = ∑ u, ‖γ u‖ ^ 2 *
            ((9 : ℝ) ^ (k u) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 / (9 : ℝ) ^ m) := by
      rw [div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      have h9u := h9 u
      field_simp
      ring
    rw [hform]
    apply Finset.sum_le_sum
    intro u _
    have hkey := key_uw u
    have hinner : (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
        ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (k u) / (9 : ℝ) ^ m else 0))
        = (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
          ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 else 0)) * (9 : ℝ) ^ (k u) / (9 : ℝ) ^ m := by
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs <;> simp
    rw [hinner]
    have hpow : (0 : ℝ) < (9 : ℝ) ^ m := pow_pos (by norm_num) _
    have hg : 0 ≤ ‖γ u‖ ^ 2 := sq_nonneg _
    have hkn : 0 ≤ (9 : ℝ) ^ (k u) := pow_nonneg (by norm_num) _
    have hprod : (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
        ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2 else 0)) * (9 : ℝ) ^ (k u)
        ≤ (9 : ℝ) ^ (k u) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hkey hkn
      have heq : (∑ j : Fin m, δ (j.val + 1)) ^ 2 * (9 : ℝ) ^ (k u)
          = (9 : ℝ) ^ (k u) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by ring
      rw [heq] at h
      exact h
    exact mul_le_mul_of_nonneg_left
      ((div_le_div_iff_of_pos_right hpow).mpr hprod) hg

end Qatlib.Papers.QLSStatePrep24.SpectralLeak
