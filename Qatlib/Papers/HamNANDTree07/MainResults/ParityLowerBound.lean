/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open scoped BigOperators Classical
open Set

namespace Qatlib.Papers.HamNANDTree07.MainResults.ParityLowerBound

abbrev ParityInstance (K : ℕ) := Set (Fin K)

def Adjacent {K : ℕ} (S S' : ParityInstance K) : Prop :=
  ∃ j : Fin K,
    (∀ i : Fin K, i ≠ j → (i ∈ S ↔ i ∈ S')) ∧ (j ∈ S ↔ j ∉ S')

def toggle {K : ℕ} (j : Fin K) (S : ParityInstance K) : ParityInstance K :=
  if j ∈ S then S \ {j} else insert j S

lemma mem_toggle {K : ℕ} (j i : Fin K) (S : ParityInstance K) :
    i ∈ toggle j S ↔ if i = j then j ∉ S else i ∈ S := by
  by_cases hj : j ∈ S <;> by_cases hij : i = j <;> simp [toggle, hj, hij]

lemma toggle_toggle {K : ℕ} (j : Fin K) (S : ParityInstance K) :
    toggle j (toggle j S) = S := by
  ext i
  simp only [mem_toggle]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij]

lemma adjacent_toggle_fst {K : ℕ} (j : Fin K) (S : ParityInstance K) :
    ∀ i : Fin K, i ≠ j → (i ∈ S ↔ i ∈ toggle j S) := by
  intro i hij
  by_cases hj : j ∈ S <;> simp [toggle, hj, hij]

lemma adjacent_toggle_snd {K : ℕ} (j : Fin K) (S : ParityInstance K) :
    j ∈ S ↔ j ∉ toggle j S := by
  by_cases hj : j ∈ S <;> simp [toggle, hj]

lemma adjacent_toggle {K : ℕ} (j : Fin K) (S : ParityInstance K) :
    Adjacent S (toggle j S) :=
  ⟨j, adjacent_toggle_fst j S, adjacent_toggle_snd j S⟩

lemma adjacent_unique {K : ℕ} {S S' : ParityInstance K} {i j : Fin K}
    (hi : ∀ k : Fin K, k ≠ i → (k ∈ S ↔ k ∈ S')) (hii : i ∈ S ↔ i ∉ S')
    (hj : ∀ k : Fin K, k ≠ j → (k ∈ S ↔ k ∈ S')) (hjj : j ∈ S ↔ j ∉ S') :
    i = j := by
  by_contra hne
  have hiff : j ∈ S' ↔ j ∉ S' := ((hi j (Ne.symm hne)).symm).trans hjj
  by_cases h : j ∈ S'
  · exact (hiff.mp h) h
  · exact h (hiff.mpr h)

def pairIndex (K : ℕ) : Type :=
  {p : ParityInstance K × ParityInstance K // Adjacent p.1 p.2}

def adjacentEquiv (K : ℕ) :
    (Fin K × ParityInstance K) ≃ pairIndex K where
  toFun x := ⟨(x.2, toggle x.1 x.2), adjacent_toggle x.1 x.2⟩
  invFun p := (Classical.choose p.2, p.1.1)
  left_inv x := by
    obtain ⟨j, S⟩ := x
    have hchoose : Classical.choose (adjacent_toggle j S) = j :=
      adjacent_unique
        (Classical.choose_spec (adjacent_toggle j S)).1
        (Classical.choose_spec (adjacent_toggle j S)).2
        (adjacent_toggle_fst j S) (adjacent_toggle_snd j S)
    exact Prod.ext hchoose rfl
  right_inv p := by
    obtain ⟨⟨S, S'⟩, hadj⟩ := p
    obtain ⟨j, hfst, hsnd⟩ := hadj
    have hk : Classical.choose
        (show Adjacent (S, S').1 (S, S').2 from ⟨j, hfst, hsnd⟩) = j :=
      adjacent_unique
        (Classical.choose_spec
          (show Adjacent (S, S').1 (S, S').2 from ⟨j, hfst, hsnd⟩)).1
        (Classical.choose_spec
          (show Adjacent (S, S').1 (S, S').2 from ⟨j, hfst, hsnd⟩)).2
        hfst hsnd
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change toggle
          (Classical.choose (show Adjacent (S, S').1 (S, S').2 from ⟨j, hfst, hsnd⟩))
          (S, S').1 = (S, S').2
      rw [hk]
      ext i
      rw [mem_toggle]
      by_cases hij : i = j
      · subst hij
        simp only [if_true]
        have hsnd' : i ∈ S ↔ i ∉ S' := hsnd
        simp [hsnd']
      · simp only [if_false, hij]
        exact hfst i hij

instance pairIndexFintype (K : ℕ) : Fintype (pairIndex K) :=
  Fintype.ofEquiv (Fin K × ParityInstance K) (adjacentEquiv K)

def numPairs (K : ℕ) : ℕ := Fintype.card (pairIndex K)

theorem numPairs_eq (K : ℕ) : numPairs K = K * 2 ^ K := by
  unfold numPairs
  change @Fintype.card (pairIndex K)
    (Fintype.ofEquiv (Fin K × ParityInstance K) (adjacentEquiv K)) = K * 2 ^ K
  rw [Fintype.ofEquiv_card (f := adjacentEquiv K)]
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_set, Fintype.card_fin]

def distanceSum {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {K : ℕ} (ψ : ParityInstance K → ℝ → V) (t : ℝ) : ℝ :=
  ∑ p : pairIndex K, ‖ψ p.1.1 t - ψ p.1.2 t‖ ^ 2

theorem distanceSum_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {K : ℕ} (ψ : ParityInstance K → ℝ → V) (ψ0 : V)
    (h : ∀ S : ParityInstance K, ψ S 0 = ψ0) :
    distanceSum ψ 0 = 0 := by
  unfold distanceSum
  apply Finset.sum_eq_zero
  intro p _
  rw [h p.1.1, h p.1.2]
  simp

theorem pairSum_ge_card_mul {K : ℕ} (d : pairIndex K → ℝ) (δ : ℝ)
    (h : ∀ p : pairIndex K, δ ≤ d p) :
    (numPairs K : ℝ) * δ ≤ ∑ p : pairIndex K, d p := by
  have hsum : (∑ _p : pairIndex K, δ) ≤ ∑ p : pairIndex K, d p :=
    Finset.sum_le_sum (fun p _ => h p)
  rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum

theorem le_mul_of_hasDerivAt_le {F g : ℝ → ℝ} {C T : ℝ} (hT : 0 ≤ T)
    (hF0 : F 0 = 0) (hcont : ContinuousOn F (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt F (g t) t)
    (hbound : ∀ t ∈ Ioo 0 T, g t ≤ C) :
    F T ≤ C * T := by
  have hD : Convex ℝ (Icc (0 : ℝ) T) := convex_Icc 0 T
  have hcont' : ContinuousOn (fun t : ℝ => C * t - F t) (Icc 0 T) :=
    (continuous_const.mul continuous_id).continuousOn.sub hcont
  have hmono : MonotoneOn (fun t : ℝ => C * t - F t) (Icc 0 T) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => C - g t) hD hcont' ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      have h1 : HasDerivAt (fun t : ℝ => C * t) C x := by
        simpa using (hasDerivAt_id x).const_mul C
      have h2 : HasDerivAt F (g x) x := hderiv x hx
      simpa using! (h1.sub h2).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have := hbound x hx
      linarith
  have hmem0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT
  have hmemT : T ∈ Icc 0 T := right_mem_Icc.mpr hT
  have h := hmono hmem0 hmemT hT
  have h' : 0 ≤ C * T - F T := by simpa [hF0] using h
  linarith

theorem parity_lower_bound_core (K : ℕ) (hK : 0 < K) (δ T : ℝ)
    (hδ : 0 < δ) (hT : 0 ≤ T) (F g : ℝ → ℝ)
    (hF0 : F 0 = 0) (hcont : ContinuousOn F (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt F (g t) t)
    (hbound : ∀ t ∈ Ioo 0 T, g t ≤ 4 * (2 : ℝ) ^ K)
    (hsuccess : (2 : ℝ) ^ K * (K : ℝ) * δ ≤ F T) :
    T ≥ (K : ℝ) * δ / 4 := by
  have hgrowth : F T ≤ 4 * (2 : ℝ) ^ K * T :=
    le_mul_of_hasDerivAt_le hT hF0 hcont hderiv hbound
  have hA : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hchain : (2 : ℝ) ^ K * ((K : ℝ) * δ) ≤ (2 : ℝ) ^ K * (4 * T) := by
    calc (2 : ℝ) ^ K * ((K : ℝ) * δ) = (2 : ℝ) ^ K * (K : ℝ) * δ := by ring
      _ ≤ F T := hsuccess
      _ ≤ 4 * (2 : ℝ) ^ K * T := hgrowth
      _ = (2 : ℝ) ^ K * (4 * T) := by ring
  have hdiv : (K : ℝ) * δ ≤ 4 * T := le_of_mul_le_mul_left hchain hA
  linarith

structure ParitySetup (K : ℕ) (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] where

  Hj : Fin K → Bool → V → V

  P : Fin K → V → V

  g : ℝ → ℝ

  HA : ℝ → V → V

  H : ParityInstance K → ℝ → V → V

  H_eq : ∀ (S : ParityInstance K) (t : ℝ) (x : V),
    H S t x = g t • (∑ j : Fin K, Hj j (decide (j ∈ S)) x) + HA t x

  g_bound : ∀ t : ℝ, |g t| ≤ 1

  H_herm : ∀ (S : ParityInstance K) (t : ℝ) (x y : V),
    inner ℂ (H S t x) y = inner ℂ x (H S t y)

  Hj_herm : ∀ (j : Fin K) (b : Bool) (x y : V),
    inner ℂ (Hj j b x) y = inner ℂ x (Hj j b y)

  P_idem : ∀ (j : Fin K) (x : V), P j (P j x) = P j x

  P_orth : ∀ (i j : Fin K), i ≠ j → ∀ (x y : V), inner ℂ (P i x) (P j y) = 0

  Hj_mem : ∀ (j : Fin K) (b : Bool) (x : V), Hj j b x = P j (Hj j b x)

  Hj_norm : ∀ (j : Fin K) (b : Bool) (x : V), ‖Hj j b x‖ ≤ ‖x‖

  P_self : ∀ (j : Fin K) (x y : V), inner ℂ (P j x) y = inner ℂ x (P j y)

  Hj_le_P : ∀ (j : Fin K) (b : Bool) (x : V), ‖Hj j b x‖ ≤ ‖P j x‖

  P_sum_le : ∀ x : V, ∑ j : Fin K, ‖P j x‖ ^ 2 ≤ ‖x‖ ^ 2

set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace

section DerivBound

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

lemma im_inner_herm_self {T : V → V}
    (hT : ∀ x y : V, inner ℂ (T x) y = inner ℂ x (T y)) (x : V) :
    (inner ℂ x (T x)).im = 0 := by
  have h : starRingEnd ℂ (inner ℂ x (T x)) = inner ℂ x (T x) := by
    calc starRingEnd ℂ (inner ℂ x (T x))
        = starRingEnd ℂ (inner ℂ (T x) x) := by rw [← hT x x]
      _ = inner ℂ x (T x) := inner_conj_symm x (T x)
  exact Complex.conj_eq_iff_im.mp h

lemma im_inner_sub_herm {T T' : V → V}
    (hT : ∀ x y : V, inner ℂ (T x) y = inner ℂ x (T y))
    (hT' : ∀ x y : V, inner ℂ (T' x) y = inner ℂ x (T' y)) (u w : V) :
    (inner ℂ (u - w) (T u - T' w)).im = (inner ℂ u (T w - T' w)).im := by
  have h1 : (inner ℂ u (T u)).im = 0 := im_inner_herm_self hT u
  have h2 : (inner ℂ w (T' w)).im = 0 := im_inner_herm_self hT' w
  have h3 : (inner ℂ w (T u)).im = - (inner ℂ u (T w)).im := by
    have hc : inner ℂ w (T u) = starRingEnd ℂ (inner ℂ (T u) w) :=
      (inner_conj_symm w (T u)).symm
    rw [hc, Complex.conj_im, hT u w]
  simp only [inner_sub_left, inner_sub_right, Complex.sub_im]
  rw [h1, h2, h3]
  ring

def pairDeriv {K : ℕ} (M : ParitySetup K V) (ψ : ParityInstance K → ℝ → V)
    (S S' : ParityInstance K) (t : ℝ) : ℝ :=
  2 * Complex.re (inner ℂ (ψ S t - ψ S' t)
    ((-Complex.I) • (M.H S t (ψ S t) - M.H S' t (ψ S' t))))

lemma hasDerivAt_pair {K : ℕ} (M : ParitySetup K V) (ψ : ParityInstance K → ℝ → V)
    (hschr : ∀ (S : ParityInstance K) (t : ℝ),
      HasDerivAt (ψ S) ((-Complex.I) • M.H S t (ψ S t)) t)
    (S S' : ParityInstance K) (t : ℝ) :
    HasDerivAt (fun s => ‖ψ S s - ψ S' s‖ ^ 2) (pairDeriv M ψ S S' t) t := by
  letI : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  have h1 : HasDerivAt (fun s => ψ S s - ψ S' s)
      ((-Complex.I) • M.H S t (ψ S t) - (-Complex.I) • M.H S' t (ψ S' t)) t :=
    (hschr S t).sub (hschr S' t)
  have h2 := h1.norm_sq
  have hre : inner ℝ (ψ S t - ψ S' t)
      ((-Complex.I) • M.H S t (ψ S t) - (-Complex.I) • M.H S' t (ψ S' t))
      = Complex.re (inner ℂ (ψ S t - ψ S' t)
        ((-Complex.I) • M.H S t (ψ S t) - (-Complex.I) • M.H S' t (ψ S' t))) :=
    real_inner_eq_re_inner (𝕜 := ℂ) _ _
  rw [hre] at h2
  simpa only [pairDeriv, smul_sub] using h2

lemma H_sub_eq {K : ℕ} (M : ParitySetup K V) (j : Fin K) (S : ParityInstance K)
    (t : ℝ) (x : V) :
    M.H S t x - M.H (toggle j S) t x
      = M.g t • (M.Hj j (decide (j ∈ S)) x
          - M.Hj j (decide (j ∈ toggle j S)) x) := by
  have hsum : (∑ i : Fin K, M.Hj i (decide (i ∈ S)) x)
      - (∑ i : Fin K, M.Hj i (decide (i ∈ toggle j S)) x)
      = M.Hj j (decide (j ∈ S)) x
          - M.Hj j (decide (j ∈ toggle j S)) x := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_eq_single j ?_ ?_
    · intro i _ hij
      have hib : (i ∈ S) ↔ (i ∈ toggle j S) := adjacent_toggle_fst j S i hij
      have hdec : decide (i ∈ S) = decide (i ∈ toggle j S) := by
        by_cases h : i ∈ S
        · have h' : i ∈ toggle j S := hib.mp h
          simp [h, h']
        · have h' : i ∉ toggle j S := fun hh => h (hib.mpr hh)
          simp [h, h']
      rw [hdec]
      simp
    · intro hmem
      exact absurd (Finset.mem_univ j) hmem
  rw [M.H_eq S t x, M.H_eq (toggle j S) t x]
  have hcancel : M.g t • (∑ i : Fin K, M.Hj i (decide (i ∈ S)) x) + M.HA t x
      - (M.g t • (∑ i : Fin K, M.Hj i (decide (i ∈ toggle j S)) x) + M.HA t x)
      = M.g t • ((∑ i : Fin K, M.Hj i (decide (i ∈ S)) x)
          - (∑ i : Fin K, M.Hj i (decide (i ∈ toggle j S)) x)) := by
    rw [smul_sub]
    abel
  rw [hcancel, hsum]

lemma pair_deriv_bound {K : ℕ} (M : ParitySetup K V) (ψ : ParityInstance K → ℝ → V)
    (j : Fin K) (S : ParityInstance K) (t : ℝ) :
    pairDeriv M ψ S (toggle j S) t
      ≤ 2 * (‖M.P j (ψ S t)‖ ^ 2 + ‖M.P j (ψ (toggle j S) t)‖ ^ 2) := by
  set S' := toggle j S with hS'
  unfold pairDeriv
  set v := ψ S t with hv
  set w := ψ S' t with hw
  have hHS : ∀ x y : V, inner ℂ (M.H S t x) y = inner ℂ x (M.H S t y) := M.H_herm S t
  have hHS' : ∀ x y : V, inner ℂ (M.H S' t x) y = inner ℂ x (M.H S' t y) := M.H_herm S' t
  have hA : 2 * Complex.re (inner ℂ (v - w) ((-Complex.I) • (M.H S t v - M.H S' t w)))
      = 2 * (inner ℂ (v - w) (M.H S t v - M.H S' t w)).im := by
    rw [inner_smul_right]
    congr 1
    simp [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im]
  have hB : (inner ℂ (v - w) (M.H S t v - M.H S' t w)).im
      = (inner ℂ v (M.H S t w - M.H S' t w)).im :=
    im_inner_sub_herm hHS hHS' v w
  have hC : (inner ℂ v (M.H S t w - M.H S' t w)).im
      = (inner ℂ v (M.g t • (M.Hj j (decide (j ∈ S)) w
          - M.Hj j (decide (j ∈ S')) w))).im := by
    rw [hS', H_sub_eq M j S t w]
  have hD : (inner ℂ v (M.g t • (M.Hj j (decide (j ∈ S)) w
        - M.Hj j (decide (j ∈ S')) w))).im
      = M.g t * (inner ℂ v (M.Hj j (decide (j ∈ S)) w
          - M.Hj j (decide (j ∈ S')) w)).im := by
    have hcoe : M.g t • (M.Hj j (decide (j ∈ S)) w
          - M.Hj j (decide (j ∈ S')) w)
        = ((M.g t : ℂ) • (M.Hj j (decide (j ∈ S)) w
          - M.Hj j (decide (j ∈ S')) w)) :=
      RCLike.real_smul_eq_coe_smul (K := ℂ) (M.g t) _
    rw [hcoe, inner_smul_right]
    simp [Complex.mul_im]
  have hE : (inner ℂ v (M.Hj j (decide (j ∈ S)) w
        - M.Hj j (decide (j ∈ S')) w)).im
      = (inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w)).im
        - (inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w)).im := by
    have hA1 : inner ℂ v (M.Hj j (decide (j ∈ S)) w)
        = inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w) := by
      rw [M.P_self j v (M.Hj j (decide (j ∈ S)) w),
        ← M.Hj_mem j (decide (j ∈ S)) w]
    have hB1 : inner ℂ v (M.Hj j (decide (j ∈ S')) w)
        = inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w) := by
      rw [M.P_self j v (M.Hj j (decide (j ∈ S')) w),
        ← M.Hj_mem j (decide (j ∈ S')) w]
    rw [inner_sub_right, Complex.sub_im, hA1, hB1]
  have hle1 : |(inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w)).im|
      ≤ ‖M.P j v‖ * ‖M.P j w‖ := by
    refine le_trans (Complex.abs_im_le_norm _) (le_trans (norm_inner_le_norm _ _) ?_)
    gcongr
    exact M.Hj_le_P j (decide (j ∈ S)) w
  have hle2 : |(inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w)).im|
      ≤ ‖M.P j v‖ * ‖M.P j w‖ := by
    refine le_trans (Complex.abs_im_le_norm _) (le_trans (norm_inner_le_norm _ _) ?_)
    gcongr
    exact M.Hj_le_P j (decide (j ∈ S')) w
  have hz : |(inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w)).im
        - (inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w)).im|
      ≤ ‖M.P j v‖ * ‖M.P j w‖ + ‖M.P j v‖ * ‖M.P j w‖ := by
    have htri : |(inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w)).im
          - (inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w)).im|
        ≤ |(inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w)).im|
          + |(inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w)).im| := by
      have := abs_add_le ((inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w)).im)
        (-(inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w)).im)
      simpa [sub_eq_add_neg] using this
    exact le_trans htri (add_le_add hle1 hle2)
  have hbound : 2 * (M.g t * ((inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w)).im
        - (inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w)).im))
      ≤ 2 * (‖M.P j v‖ ^ 2 + ‖M.P j w‖ ^ 2) := by
    have hg : |M.g t| ≤ 1 := M.g_bound t
    have habs : |2 * (M.g t * ((inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w)).im
          - (inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w)).im))|
        = 2 * |M.g t| * |(inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w)).im
          - (inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w)).im| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    calc 2 * (M.g t * ((inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w)).im
            - (inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w)).im))
        ≤ |2 * (M.g t * ((inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w)).im
            - (inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w)).im))| := le_abs_self _
      _ = 2 * |M.g t| * |(inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S)) w)).im
            - (inner ℂ (M.P j v) (M.Hj j (decide (j ∈ S')) w)).im| := habs
      _ ≤ 2 * 1 * (‖M.P j v‖ * ‖M.P j w‖ + ‖M.P j v‖ * ‖M.P j w‖) := by
          apply mul_le_mul
          · nlinarith [abs_nonneg (M.g t)]
          · exact hz
          · positivity
          · norm_num
      _ ≤ 2 * (‖M.P j v‖ ^ 2 + ‖M.P j w‖ ^ 2) := by
          nlinarith [sq_nonneg (‖M.P j v‖ - ‖M.P j w‖),
            norm_nonneg (M.P j v), norm_nonneg (M.P j w)]
  rw [hA, hB, hC, hD, hE]
  exact hbound

end DerivBound

theorem distance_sum_growth_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (K : ℕ) (M : ParitySetup K V) (T : ℝ)
    (ψ : ParityInstance K → ℝ → V)
    (hunit : ∀ (S : ParityInstance K) (t : ℝ), ‖ψ S t‖ ≤ 1)
    (hschr : ∀ (S : ParityInstance K) (t : ℝ),
      HasDerivAt (ψ S) ((-Complex.I) • M.H S t (ψ S t)) t) :
    ∃ g' : ℝ → ℝ,
      ContinuousOn (fun t => distanceSum ψ t) (Icc 0 T) ∧
      (∀ t ∈ Ioo 0 T, HasDerivAt (fun t => distanceSum ψ t) (g' t) t) ∧
      ∀ t ∈ Ioo 0 T, g' t ≤ 4 * (2 : ℝ) ^ K := by
  refine ⟨fun t => ∑ p : pairIndex K, pairDeriv M ψ p.1.1 p.1.2 t, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun t => distanceSum ψ t) := by
      unfold distanceSum
      refine continuous_finsetSum _ (fun p _ => ?_)
      have h1 : Continuous (fun t => ψ p.1.1 t) :=
        continuous_iff_continuousAt.mpr (fun t => (hschr p.1.1 t).continuousAt)
      have h2 : Continuous (fun t => ψ p.1.2 t) :=
        continuous_iff_continuousAt.mpr (fun t => (hschr p.1.2 t).continuousAt)
      exact (h1.sub h2).norm.pow 2
    exact hcont.continuousOn
  · intro t _
    have h := HasDerivAt.sum (u := (Finset.univ : Finset (pairIndex K)))
      (A := fun p s => ‖ψ p.1.1 s - ψ p.1.2 s‖ ^ 2)
      (A' := fun p => pairDeriv M ψ p.1.1 p.1.2 t)
      (fun p _ => hasDerivAt_pair M ψ hschr p.1.1 p.1.2 t)
    have hfun : (fun t => distanceSum ψ t)
        = ∑ p : pairIndex K, fun s => ‖ψ p.1.1 s - ψ p.1.2 s‖ ^ 2 := by
      rw [Finset.sum_fn]
      rfl
    rw [hfun]
    exact h
  · intro t _
    have hcard : Fintype.card (ParityInstance K) = 2 ^ K := by
      rw [Fintype.card_set, Fintype.card_fin]
    have hreindex : (∑ p : pairIndex K, pairDeriv M ψ p.1.1 p.1.2 t)
        = ∑ x : Fin K × ParityInstance K,
            pairDeriv M ψ x.2 (toggle x.1 x.2) t := by
      rw [← Equiv.sum_comp (adjacentEquiv K)
        (fun p => pairDeriv M ψ p.1.1 p.1.2 t)]
      rfl
    have hstep : (∑ x : Fin K × ParityInstance K,
          pairDeriv M ψ x.2 (toggle x.1 x.2) t)
        ≤ ∑ x : Fin K × ParityInstance K,
            2 * (‖M.P x.1 (ψ x.2 t)‖ ^ 2
              + ‖M.P x.1 (ψ (toggle x.1 x.2) t)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro x _
      exact pair_deriv_bound M ψ x.1 x.2 t
    have hfirst : (∑ x : Fin K × ParityInstance K,
          ‖M.P x.1 (ψ x.2 t)‖ ^ 2) ≤ (2 : ℝ) ^ K := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      calc ∑ S : ParityInstance K, ∑ j : Fin K, ‖M.P j (ψ S t)‖ ^ 2
          ≤ ∑ S : ParityInstance K, ‖ψ S t‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro S _
            exact M.P_sum_le (ψ S t)
        _ ≤ ∑ _S : ParityInstance K, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro S _
            have h1 : ‖ψ S t‖ ≤ 1 := hunit S t
            nlinarith [norm_nonneg (ψ S t)]
        _ = (2 : ℝ) ^ K := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
            push_cast
            ring
    have hsecond : (∑ x : Fin K × ParityInstance K,
          ‖M.P x.1 (ψ (toggle x.1 x.2) t)‖ ^ 2) ≤ (2 : ℝ) ^ K := by
      rw [Fintype.sum_prod_type]
      have hper : ∀ j : Fin K,
          ∑ S : ParityInstance K, ‖M.P j (ψ (toggle j S) t)‖ ^ 2
            = ∑ S' : ParityInstance K, ‖M.P j (ψ S' t)‖ ^ 2 := by
        intro j
        let e : ParityInstance K ≃ ParityInstance K :=
          { toFun := toggle j, invFun := toggle j,
            left_inv := fun S => toggle_toggle j S,
            right_inv := fun S => toggle_toggle j S }
        have hcomp := Equiv.sum_comp e (fun S' => ‖M.P j (ψ S' t)‖ ^ 2)
        simpa [e] using hcomp
      calc ∑ j : Fin K, ∑ S : ParityInstance K, ‖M.P j (ψ (toggle j S) t)‖ ^ 2
          = ∑ j : Fin K, ∑ S' : ParityInstance K, ‖M.P j (ψ S' t)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            exact hper j
        _ ≤ (2 : ℝ) ^ K := by
            rw [Finset.sum_comm]
            calc ∑ S' : ParityInstance K, ∑ j : Fin K, ‖M.P j (ψ S' t)‖ ^ 2
                ≤ ∑ S' : ParityInstance K, ‖ψ S' t‖ ^ 2 := by
                  apply Finset.sum_le_sum
                  intro S' _
                  exact M.P_sum_le (ψ S' t)
              _ ≤ ∑ _S' : ParityInstance K, (1 : ℝ) := by
                  apply Finset.sum_le_sum
                  intro S' _
                  have h1 : ‖ψ S' t‖ ≤ 1 := hunit S' t
                  nlinarith [norm_nonneg (ψ S' t)]
              _ = (2 : ℝ) ^ K := by
                  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
                  push_cast
                  ring
    have hsplit : (∑ x : Fin K × ParityInstance K,
          2 * (‖M.P x.1 (ψ x.2 t)‖ ^ 2
            + ‖M.P x.1 (ψ (toggle x.1 x.2) t)‖ ^ 2))
        = 2 * ((∑ x : Fin K × ParityInstance K, ‖M.P x.1 (ψ x.2 t)‖ ^ 2)
            + (∑ x : Fin K × ParityInstance K,
                ‖M.P x.1 (ψ (toggle x.1 x.2) t)‖ ^ 2)) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    calc ∑ p : pairIndex K, pairDeriv M ψ p.1.1 p.1.2 t
        = ∑ x : Fin K × ParityInstance K, pairDeriv M ψ x.2 (toggle x.1 x.2) t :=
          hreindex
      _ ≤ ∑ x : Fin K × ParityInstance K,
            2 * (‖M.P x.1 (ψ x.2 t)‖ ^ 2
              + ‖M.P x.1 (ψ (toggle x.1 x.2) t)‖ ^ 2) := hstep
      _ = 2 * ((∑ x : Fin K × ParityInstance K, ‖M.P x.1 (ψ x.2 t)‖ ^ 2)
            + (∑ x : Fin K × ParityInstance K,
                ‖M.P x.1 (ψ (toggle x.1 x.2) t)‖ ^ 2)) := hsplit
      _ ≤ 2 * ((2 : ℝ) ^ K + (2 : ℝ) ^ K) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith [hfirst, hsecond]
      _ = 4 * (2 : ℝ) ^ K := by ring

theorem hamiltonian_parity_lower_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (K : ℕ) (hK : 0 < K) (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T)
    (M : ParitySetup K V)
    (ψ : ParityInstance K → ℝ → V)
    (hunit : ∀ (S : ParityInstance K) (t : ℝ), ‖ψ S t‖ ≤ 1)
    (hinit : ∃ ψ0 : V, ∀ S : ParityInstance K, ψ S 0 = ψ0)
    (hschr : ∀ (S : ParityInstance K) (t : ℝ),
      HasDerivAt (ψ S) ((-Complex.I) • M.H S t (ψ S t)) t)
    (hsep : ∀ p : pairIndex K, δ ≤ ‖ψ p.1.1 T - ψ p.1.2 T‖ ^ 2) :
    T ≥ (K : ℝ) * δ / 4 := by
  obtain ⟨ψ0, hψ0⟩ := hinit
  obtain ⟨g', hcont, hderiv, hbound⟩ :=
    distance_sum_growth_bound K M T ψ hunit hschr
  have hF0 : distanceSum ψ 0 = 0 := distanceSum_zero ψ ψ0 hψ0
  have hsuccess : (2 : ℝ) ^ K * (K : ℝ) * δ ≤ distanceSum ψ T := by
    have hsum := pairSum_ge_card_mul
      (fun p : pairIndex K => ‖ψ p.1.1 T - ψ p.1.2 T‖ ^ 2) δ hsep
    rw [numPairs_eq K] at hsum
    have hcast : ((K * 2 ^ K : ℕ) : ℝ) = (K : ℝ) * (2 : ℝ) ^ K := by
      push_cast
      ring
    rw [hcast] at hsum
    calc (2 : ℝ) ^ K * (K : ℝ) * δ = (K : ℝ) * (2 : ℝ) ^ K * δ := by ring
      _ ≤ distanceSum ψ T := hsum
  exact parity_lower_bound_core K hK δ T hδ hT (distanceSum ψ) g' hF0 hcont
    hderiv hbound hsuccess

theorem hamiltonian_parity_lower_bound_of_norm_sep
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (K : ℕ) (hK : 0 < K) (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T)
    (M : ParitySetup K V)
    (ψ : ParityInstance K → ℝ → V)
    (hunit : ∀ (S : ParityInstance K) (t : ℝ), ‖ψ S t‖ ≤ 1)
    (hinit : ∃ ψ0 : V, ∀ S : ParityInstance K, ψ S 0 = ψ0)
    (hschr : ∀ (S : ParityInstance K) (t : ℝ),
      HasDerivAt (ψ S) ((-Complex.I) • M.H S t (ψ S t)) t)
    (hsep : ∀ p : pairIndex K, δ ≤ ‖ψ p.1.1 T - ψ p.1.2 T‖) :
    T ≥ (K : ℝ) * δ ^ 2 / 4 := by
  refine hamiltonian_parity_lower_bound K hK (δ ^ 2) T (by positivity) hT M ψ
    hunit hinit hschr ?_
  intro p
  exact pow_le_pow_left₀ hδ.le (hsep p) 2

end Qatlib.Papers.HamNANDTree07.MainResults.ParityLowerBound
