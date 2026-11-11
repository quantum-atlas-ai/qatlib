/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Approximation.Causalean.Mathlib.Analysis.Approximation.Chebyshev.BasicBernsteinSzegoTrig
import Qatlib.Foundations.CbmdAnalysis.Approximation.Causalean.Mathlib.Analysis.Approximation.Chebyshev.TrigPoly
import Qatlib.Foundations.CbmdAnalysis.Approximation.Causalean.Mathlib.Analysis.Approximation.Chebyshev.Interp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Algebra.Polynomial.CancelLeads
import Mathlib.Topology.Algebra.Polynomial

/-!
# Bernstein–Szegő bound for cosine compositions

This module places cosine compositions and Szegő interpolants in bounded-degree trigonometric
polynomial spaces and develops the extremum-point identities needed for comparison. The theorem
`szego_deriv_sq_bound` bounds the squared derivative together with the degree-weighted squared
value, supporting the approximation analysis associated with [WangEtAl2026].

## Main statements

* `cosComp_isTrigPolyLE`: Transfer a polynomial degree bound to a cosine composition.
* `szego_deriv_sq_bound`: Prove the combined derivative-and-value bound.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Approximation

section

open Real Polynomial

namespace Causalean.Mathlib.Analysis.BernsteinSzegoTrig

/-- The Szegő interpolant is a trigonometric polynomial of degree at most `β`. -/
theorem szegoInterp_isTrigPolyLE (β : ℕ) (Q₀ Q₁ t₀ : ℝ) :
    IsTrigPolyLE β (szegoInterp β Q₀ Q₁ t₀) := by
  let A : ℝ :=
    Q₀ * Real.cos ((β : ℝ) * t₀) - (Q₁ / (β : ℝ)) * Real.sin ((β : ℝ) * t₀)
  let B : ℝ :=
    Q₀ * Real.sin ((β : ℝ) * t₀) + (Q₁ / (β : ℝ)) * Real.cos ((β : ℝ) * t₀)
  refine ⟨fun k => if k = β then A else 0, fun k => if k = β then B else 0, ?_⟩
  intro t
  rw [Finset.sum_eq_single β]
  · simp only [szegoInterp, A, B, ↓reduceIte]
    have harg : (β : ℝ) * (t - t₀) = (β : ℝ) * t - (β : ℝ) * t₀ := by
      ring
    rw [harg, Real.cos_sub, Real.sin_sub]
    ring
  · intro k _ hne
    simp only [hne, ↓reduceIte, zero_mul, zero_add]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_self β)))

/-- The sum of two trigonometric polynomials of degree at most `n` has degree at most `n`. -/
theorem IsTrigPolyLE.add {n : ℕ} {f g : ℝ → ℝ} (hf : IsTrigPolyLE n f)
    (hg : IsTrigPolyLE n g) : IsTrigPolyLE n (fun t => f t + g t) := by
  rcases hf with ⟨a, b, ha⟩
  rcases hg with ⟨c, d, hg⟩
  refine ⟨fun k => a k + c k, fun k => b k + d k, ?_⟩
  intro t
  change f t + g t =
    ∑ k ∈ Finset.range (n + 1),
      ((a k + c k) * Real.cos ((k : ℝ) * t) + (b k + d k) * Real.sin ((k : ℝ) * t))
  rw [ha t, hg t, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  ring

/-- Multiplying a trigonometric polynomial by a real constant preserves its degree bound. -/
theorem IsTrigPolyLE.const_mul {n : ℕ} {f : ℝ → ℝ} (c : ℝ)
    (hf : IsTrigPolyLE n f) : IsTrigPolyLE n (fun t => c * f t) := by
  rcases hf with ⟨a, b, ha⟩
  refine ⟨fun k => c * a k, fun k => c * b k, ?_⟩
  intro t
  change c * f t =
    ∑ k ∈ Finset.range (n + 1),
      (c * a k * Real.cos ((k : ℝ) * t) + c * b k * Real.sin ((k : ℝ) * t))
  rw [ha t, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  ring

/-- A function pointwise equal to a trigonometric polynomial satisfies the same degree bound. -/
theorem IsTrigPolyLE.congr {n : ℕ} {f g : ℝ → ℝ} (hf : IsTrigPolyLE n f)
    (hfg : ∀ t, g t = f t) : IsTrigPolyLE n g := by
  rcases hf with ⟨a, b, ha⟩
  exact ⟨a, b, fun t => by rw [hfg t, ha t]⟩

/-- The cosine harmonic of natural frequency `n` is a trigonometric polynomial of degree at most
`n`. -/
theorem cos_nat_mul_isTrigPolyLE (n : ℕ) :
    IsTrigPolyLE n (fun t => Real.cos ((n : ℝ) * t)) := by
  classical
  refine ⟨fun k => if k = n then 1 else 0, fun _ => 0, ?_⟩
  intro t
  rw [Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    simp [hkn]
  · intro hn
    exact (hn (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim

/-- Evaluating a polynomial of degree at most `β` at cosine gives a trigonometric polynomial of
degree at most `β`. -/
theorem cosComp_isTrigPolyLE (R : Polynomial ℝ) (β : ℕ) (hβ : R.natDegree ≤ β) :
    IsTrigPolyLE β (fun t => R.eval (Real.cos t)) := by
  classical
  revert R
  induction β with
  | zero =>
      intro R hR
      obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp (Nat.le_zero.mp hR)
      simpa using isTrigPolyLE_const 0 c
  | succ β ih =>
      intro R hRβ
      by_cases hR : R.natDegree ≤ β
      · exact (ih R hR).mono (Nat.le_succ β)
      · have hRdeg : R.natDegree = β + 1 := by
          exact le_antisymm hRβ (Nat.succ_le_of_lt (Nat.lt_of_not_ge hR))
        let T : Polynomial ℝ := Polynomial.Chebyshev.T ℝ (((β + 1 : ℕ) : ℤ))
        let P : Polynomial ℝ := T.cancelLeads R
        have hTdeg : T.natDegree = β + 1 := by
          dsimp [T]
          rw [Polynomial.Chebyshev.natDegree_T]
          apply Nat.cast_injective (R := ℤ)
          rw [Int.natCast_natAbs]
          have hnonneg : 0 ≤ ((β : ℤ) + 1) := by omega
          rw [abs_of_nonneg hnonneg]
          norm_num
        have hPdeg : P.natDegree ≤ β := by
          have hlt : P.natDegree < R.natDegree := by
            exact Polynomial.natDegree_cancelLeads_lt_of_natDegree_le_natDegree
              (by simp [hTdeg, hRdeg]) (by simp [hRdeg])
          omega
        have hPtrig : IsTrigPolyLE (β + 1) (fun t => P.eval (Real.cos t)) :=
          (ih P hPdeg).mono (Nat.le_succ β)
        have hcostrig : IsTrigPolyLE (β + 1)
            (fun t => R.leadingCoeff * Real.cos (((β + 1 : ℕ) : ℝ) * t)) :=
          IsTrigPolyLE.const_mul R.leadingCoeff (cos_nat_mul_isTrigPolyLE (β + 1))
        have hsum : IsTrigPolyLE (β + 1)
            (fun t => P.eval (Real.cos t)
              + R.leadingCoeff * Real.cos (((β + 1 : ℕ) : ℝ) * t)) :=
          hPtrig.add hcostrig
        have hTlc_ne : T.leadingCoeff ≠ 0 := by
          simp [T]
        have hscaled : IsTrigPolyLE (β + 1)
            (fun t => (T.leadingCoeff)⁻¹
              * (P.eval (Real.cos t)
                + R.leadingCoeff * Real.cos (((β + 1 : ℕ) : ℝ) * t))) :=
          IsTrigPolyLE.const_mul (T.leadingCoeff)⁻¹ hsum
        refine hscaled.congr ?_
        intro t
        have hTeval : T.eval (Real.cos t) =
            Real.cos (((β + 1 : ℕ) : ℝ) * t) := by
          simp [T]
        have hPeval : P.eval (Real.cos t) =
            T.leadingCoeff * R.eval (Real.cos t) - R.leadingCoeff * T.eval (Real.cos t) := by
          simp [P, Polynomial.cancelLeads, hTdeg, hRdeg]
        rw [hPeval, hTeval]
        field_simp [hTlc_ne]
        ring

/-- The Szegő interpolant is continuous for every natural frequency. -/
@[fun_prop]
theorem szegoInterp_continuous (β : ℕ) (Q₀ Q₁ t₀ : ℝ) :
    Continuous (szegoInterp β Q₀ Q₁ t₀) := by
  unfold szegoInterp
  fun_prop

/-- At the `k`th equally spaced extremum point, the shifted phase argument equals `k * π` when
`β` is nonzero. -/
private lemma szegoExtrema_arg {β : ℕ} (hβ : (β : ℝ) ≠ 0) (t₀ φ : ℝ) (k : ℤ) :
    (β : ℝ) *
        ((t₀ + φ / (β : ℝ) + (k : ℝ) * (Real.pi / (β : ℝ))) - t₀) - φ =
      (k : ℝ) * Real.pi := by
  field_simp [hβ]
  ring

/-- For positive frequency, the integer-indexed extremum points are strictly increasing. -/
private lemma szegoExtrema_strictMono {β : ℕ} (hβpos : 0 < (β : ℝ)) (t₀ φ : ℝ) :
    StrictMono (fun k : ℤ => t₀ + φ / (β : ℝ) + (k : ℝ) * (Real.pi / (β : ℝ))) := by
  intro k l hkl
  have hcast : (k : ℝ) < (l : ℝ) := by exact_mod_cast hkl
  have hcoef : 0 < Real.pi / (β : ℝ) := div_pos Real.pi_pos hβpos
  have hmul := mul_lt_mul_of_pos_right hcast hcoef
  linarith

/-- Advancing the extremum index by `2 * β` translates the corresponding point by `2 * π` when
`β` is nonzero. -/
private lemma szegoExtrema_period {β : ℕ} (hβ : (β : ℝ) ≠ 0) (t₀ φ : ℝ)
    (m : ℤ) :
    t₀ + φ / (β : ℝ) + ((m + (2 * β : ℤ) : ℤ) : ℝ) * (Real.pi / (β : ℝ)) =
      (t₀ + φ / (β : ℝ) + (m : ℝ) * (Real.pi / (β : ℝ))) + 2 * Real.pi := by
  field_simp [hβ]
  norm_num
  ring

/-- For positive frequency, `t₀` lies between the extremum points with indices `⌊-φ / π⌋` and
`⌊-φ / π⌋ + 1`, including the left endpoint and excluding the right. -/
private lemma szegoExtrema_floor_mem {β : ℕ} (hβpos : 0 < (β : ℝ)) (t₀ φ : ℝ) :
    let u : ℤ → ℝ := fun k => t₀ + φ / (β : ℝ) + (k : ℝ) * (Real.pi / (β : ℝ))
    let m : ℤ := ⌊(-φ) / Real.pi⌋
    t₀ ∈ Set.Ico (u m) (u (m + 1)) := by
  intro u m
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcoef : 0 < Real.pi / (β : ℝ) := div_pos hpi hβpos
  constructor
  · have hm : (m : ℝ) ≤ (-φ) / Real.pi := Int.floor_le _
    have hmul := mul_le_mul_of_nonneg_right hm hcoef.le
    field_simp [ne_of_gt hβpos] at hmul ⊢
    dsimp only [u]
    field_simp [ne_of_gt hβpos]
    nlinarith [hpi]
  · have hm : (-φ) / Real.pi < (m : ℝ) + 1 := Int.lt_floor_add_one _
    have hmul := mul_lt_mul_of_pos_right hm hcoef
    field_simp [ne_of_gt hβpos] at hmul ⊢
    dsimp only [u]
    field_simp [ne_of_gt hβpos]
    norm_num at hmul ⊢
    nlinarith [hpi]

/-- If a polynomial has degree at most `β` and its cosine composition is bounded in absolute
value by `M`, then the squared derivative plus `β ^ 2` times the squared value is at most `β
^ 2 * M ^ 2`. -/
theorem szego_deriv_sq_bound (R : Polynomial ℝ) (β : ℕ) (hβ : R.natDegree ≤ β)
    (M : ℝ) (hM : ∀ t, |R.eval (Real.cos t)| ≤ M) :
    ∀ t, (deriv (fun s => R.eval (Real.cos s)) t) ^ 2
        + (β : ℝ) ^ 2 * (R.eval (Real.cos t)) ^ 2 ≤ (β : ℝ) ^ 2 * M ^ 2 := by
  intro t₀
  by_cases hβ0 : β = 0
  · subst β
    obtain ⟨c, hRc⟩ := Polynomial.natDegree_eq_zero.mp (Nat.le_zero.mp hβ)
    subst R
    have hderiv0 : deriv (fun s => Polynomial.eval (Real.cos s) (Polynomial.C c)) t₀ = 0 := by
      rw [deriv_cosComp]
      simp
    rw [hderiv0]
    simp
  · have hβ1 : 1 ≤ β := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hβ0)
    let Q : ℝ → ℝ := fun t => R.eval (Real.cos t)
    let Q₀ : ℝ := Q t₀
    let Q₁ : ℝ := deriv Q t₀
    let A : ℝ := Real.sqrt (Q₀ ^ 2 + (Q₁ / (β : ℝ)) ^ 2)
    have hM_nonneg : 0 ≤ M := by
      exact (abs_nonneg (Q t₀)).trans (hM t₀)
    have hβR_ne : (β : ℝ) ≠ 0 := by exact_mod_cast hβ0
    have hA_nonneg : 0 ≤ A := Real.sqrt_nonneg _
    have hrad_nonneg : 0 ≤ Q₀ ^ 2 + (Q₁ / (β : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg Q₀, sq_nonneg (Q₁ / (β : ℝ))]
    have hamp_sq :
        A ^ 2 = Q₀ ^ 2 + (Q₁ / (β : ℝ)) ^ 2 := by
      dsimp [A]
      rw [Real.sq_sqrt hrad_nonneg]
    have hAmpBound : A ^ 2 ≤ M ^ 2 := by
      by_contra hnot
      have hgt : M ^ 2 < A ^ 2 := lt_of_not_ge hnot
      have hA_gt_M : M < A := by
        nlinarith [sq_lt_sq.mp hgt, hA_nonneg, hM_nonneg]
      let Sfun : ℝ → ℝ := szegoInterp β Q₀ Q₁ t₀
      let g : ℝ → ℝ := fun t => Q t - Sfun t
      have hg_trig : IsTrigPolyLE β g := by
        exact (cosComp_isTrigPolyLE R β hβ).sub (szegoInterp_isTrigPolyLE β Q₀ Q₁ t₀)
      have hg_t₀ : g t₀ = 0 := by
        dsimp [g, Sfun, Q₀, Q]
        rw [szegoInterp_self]
        ring
      have hQ_hasDeriv : HasDerivAt Q Q₁ t₀ := by
        dsimp [Q₁, Q]
        simpa [deriv_cosComp] using (hasDerivAt_cosComp R t₀)
      have hS_hasDeriv : HasDerivAt Sfun Q₁ t₀ := by
        dsimp [Sfun]
        exact szegoInterp_hasDerivAt β hβ1 Q₀ Q₁ t₀
      have hg_deriv : HasDerivAt g 0 t₀ := by
        have h := hQ_hasDeriv.fun_sub hS_hasDeriv
        rw [sub_self] at h
        exact h
      have hg_nonzero : ∃ t, g t ≠ 0 := by
        obtain ⟨φ, hφ⟩ := szegoInterp_amplitude β Q₀ Q₁ t₀
        let u : ℝ := t₀ + φ / (β : ℝ)
        refine ⟨u, ?_⟩
        have hS_u : Sfun u = A := by
          dsimp [Sfun]
          rw [hφ u]
          have harg : (β : ℝ) * (u - t₀) - φ = 0 := by
            dsimp [u]
            field_simp [hβR_ne]
            ring
          rw [harg, Real.cos_zero, mul_one]
        have hQ_le : |Q u| ≤ M := hM u
        intro hg0
        have hQu_eq : Q u = A := by
          have := congrArg (fun x => x + Sfun u) hg0
          simpa [g, hS_u] using this
        have : A ≤ M := by
          rw [← hQu_eq]
          exact le_trans (le_abs_self _) hQ_le
        linarith

      have hcount : (2 * β - 1) + 2 ≤ 2 * β := by
        classical
        obtain ⟨φ, hφ⟩ := szegoInterp_amplitude β Q₀ Q₁ t₀
        have hβR_pos : 0 < (β : ℝ) := by exact_mod_cast hβ1
        let u : ℤ → ℝ :=
          fun k => t₀ + φ / (β : ℝ) + (k : ℝ) * (Real.pi / (β : ℝ))
        let m : ℤ := ⌊(-φ) / Real.pi⌋
        have hu_mono : StrictMono u := by
          simpa [u] using szegoExtrema_strictMono hβR_pos t₀ φ
        have hgap_pos : ∀ k : ℤ, u k < u (k + 1) := fun k => hu_mono (by omega)
        have hS_ext : ∀ k : ℤ, Sfun (u k) = A * ((-1 : ℝ) ^ k) := by
          intro k
          dsimp [Sfun]
          rw [hφ (u k)]
          rw [szegoExtrema_arg hβR_ne t₀ φ k]
          rw [Real.cos_int_mul_pi]
        have hg_cont : Continuous g := by
          have hQ_cont : Continuous Q := by
            dsimp [Q]
            fun_prop
          have hS_cont : Continuous Sfun := by
            dsimp [Sfun]
            exact szegoInterp_continuous β Q₀ Q₁ t₀
          dsimp [g]
          exact hQ_cont.sub hS_cont
        have hsign : ∀ k : ℤ, g (u k) * ((-1 : ℝ) ^ k) < 0 := by
          intro k
          let s : ℝ := (-1 : ℝ) ^ k
          have hs_abs : |s| = 1 := by
            simp [s]
          have hs_sq : s * s = 1 := by
            have hs_sq_abs : |s| ^ 2 = 1 := by
              rw [hs_abs]
              norm_num
            rw [sq_abs] at hs_sq_abs
            nlinarith [hs_sq_abs]
          have hQs_le : Q (u k) * s ≤ M := by
            calc
              Q (u k) * s ≤ |Q (u k) * s| := le_abs_self _
              _ = |Q (u k)| * |s| := by rw [abs_mul]
              _ = |Q (u k)| := by rw [hs_abs, mul_one]
              _ ≤ M := hM (u k)
          have hS := hS_ext k
          calc
            g (u k) * s = (Q (u k) - A * s) * s := by
              dsimp [g]
              rw [hS]
            _ = Q (u k) * s - A := by
              rw [show (Q (u k) - A * s) * s = Q (u k) * s - A * (s * s) by ring]
              rw [hs_sq, mul_one]
            _ < 0 := by linarith
        have hzero_exists :
            ∀ k : ℤ, ∃ x, x ∈ Set.Ioo (u k) (u (k + 1)) ∧ g x = 0 := by
          intro k
          let s : ℝ := (-1 : ℝ) ^ k
          let F : ℝ → ℝ := fun x => g x * s
          have hs_ne : s ≠ 0 := by
            have hs_abs : |s| = 1 := by
              simp [s]
            intro hs0
            rw [hs0, abs_zero] at hs_abs
            norm_num at hs_abs
          have hleft : F (u k) < 0 := by
            simpa [F, s] using hsign k
          have hright : 0 < F (u (k + 1)) := by
            have hnext := hsign (k + 1)
            have hs_next : ((-1 : ℝ) ^ (k + 1) : ℝ) = -s := by
              rw [zpow_add₀]
              · norm_num [s]
              · norm_num
            rw [hs_next] at hnext
            dsimp [F]
            nlinarith
          have hF_cont : ContinuousOn F (Set.Icc (u k) (u (k + 1))) := by
            exact (hg_cont.mul continuous_const).continuousOn
          have hzero_mem : (0 : ℝ) ∈ Set.Ioo (F (u k)) (F (u (k + 1))) :=
            ⟨hleft, hright⟩
          rcases intermediate_value_Ioo (le_of_lt (hgap_pos k)) hF_cont hzero_mem with
            ⟨x, hx, hFx⟩
          refine ⟨x, hx, ?_⟩
          have hgxs : g x * s = 0 := by
            simpa [F] using hFx
          exact (mul_eq_zero.mp hgxs).resolve_right hs_ne
        let v : ℤ → ℝ := fun k => Classical.choose (hzero_exists k)
        have hv_mem : ∀ k : ℤ, v k ∈ Set.Ioo (u k) (u (k + 1)) := by
          intro k
          exact (Classical.choose_spec (hzero_exists k)).1
        have hv_zero : ∀ k : ℤ, g (v k) = 0 := by
          intro k
          exact (Classical.choose_spec (hzero_exists k)).2
        have hv_mono : StrictMono v := by
          intro k l hkl
          have hk1le : k + 1 ≤ l := by omega
          exact (lt_of_lt_of_le (hv_mem k).2 (hu_mono.monotone hk1le)).trans (hv_mem l).1
        let N : ℕ := 2 * β - 1
        let w : Fin N → ℝ := fun j => v (m + 1 + (j : ℤ))
        let S : Finset ℝ :=
          (Finset.univ : Finset (Fin N)).image w
        have hS_zero : ∀ x ∈ S, g x = 0 := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨j, _hj, hjx⟩
          rw [← hjx]
          dsimp [w]
          exact hv_zero (m + 1 + (j : ℤ))
        have hS_sub : ↑S ⊆ Set.Ico (u m) (u m + 2 * Real.pi) := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨j, _hj, hjx⟩
          rw [← hjx]
          dsimp [w]
          constructor
          · have hm_lt : m < m + 1 + (j : ℤ) := by omega
            exact ((hu_mono hm_lt).trans (hv_mem (m + 1 + (j : ℤ))).1).le
          · have hidx : m + 1 + (j : ℤ) + 1 ≤ m + (2 * β : ℤ) := by
              have hjlt : (j : ℕ) < N := j.isLt
              dsimp [N] at hjlt
              omega
            have hu_le : u (m + 1 + (j : ℤ) + 1) ≤ u (m + (2 * β : ℤ)) :=
              hu_mono.monotone hidx
            have hper : u (m + (2 * β : ℤ)) = u m + 2 * Real.pi := by
              simpa [u] using szegoExtrema_period hβR_ne t₀ φ m
            exact (hv_mem (m + 1 + (j : ℤ))).2.trans_le (hu_le.trans (le_of_eq hper))
        have ht₀_gap : t₀ ∈ Set.Ico (u m) (u (m + 1)) := by
          simpa [u, m] using szegoExtrema_floor_mem hβR_pos t₀ φ
        have ht₀_mem : t₀ ∈ Set.Ico (u m) (u m + 2 * Real.pi) := by
          constructor
          · exact ht₀_gap.1
          · have hidx : m + 1 < m + (2 * β : ℤ) := by omega
            have hper : u (m + (2 * β : ℤ)) = u m + 2 * Real.pi := by
              simpa [u] using szegoExtrema_period hβR_ne t₀ φ m
            exact ht₀_gap.2.trans (by simpa [hper] using hu_mono hidx)
        have ht₀_not_mem : t₀ ∉ S := by
          intro ht₀S
          rcases Finset.mem_image.mp ht₀S with ⟨j, _hj, hj⟩
          have hidx : m + 1 ≤ m + 1 + (j : ℤ) := by omega
          have hut : u (m + 1) ≤ u (m + 1 + (j : ℤ)) := hu_mono.monotone hidx
          have ht_lt : t₀ < w j := by
            dsimp [w]
            exact ht₀_gap.2.trans_le
              (hut.trans (le_of_lt (hv_mem (m + 1 + (j : ℤ))).1))
          exact (ne_of_gt ht_lt) hj
        have hS_card : S.card = 2 * β - 1 := by
          have hinj : Set.InjOn w ((Finset.univ : Finset (Fin N)) : Set (Fin N)) := by
            intro i _hi j _hj hij
            apply Fin.ext
            dsimp [w] at hij
            have hidx_eq : m + 1 + (i : ℤ) = m + 1 + (j : ℤ) :=
              hv_mono.injective hij
            have hcast_eq : (i : ℤ) = (j : ℤ) := by omega
            exact_mod_cast hcast_eq
          dsimp [S]
          rw [Finset.card_image_of_injOn hinj]
          simp [N]
        have hraw := IsTrigPolyLE.card_simple_add_double_le
          (n := β) (f := g) hg_trig hg_nonzero (c := u m) (S := S)
          hS_sub hS_zero ht₀_mem ht₀_not_mem hg_t₀ hg_deriv
        rw [hS_card] at hraw
        exact hraw
      omega
    have hgoal_alg :
        Q₁ ^ 2 + (β : ℝ) ^ 2 * Q₀ ^ 2 ≤ (β : ℝ) ^ 2 * M ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hAmpBound (sq_nonneg (β : ℝ))
      rw [hamp_sq] at hmul
      calc
        Q₁ ^ 2 + (β : ℝ) ^ 2 * Q₀ ^ 2
            = (β : ℝ) ^ 2 * (Q₀ ^ 2 + (Q₁ / (β : ℝ)) ^ 2) := by
              field_simp [hβR_ne]
              ring
        _ ≤ (β : ℝ) ^ 2 * M ^ 2 := hmul
    simpa [Q, Q₀, Q₁] using hgoal_alg

end Causalean.Mathlib.Analysis.BernsteinSzegoTrig

end
end Qatlib.Foundations.CbmdAnalysis.Approximation
