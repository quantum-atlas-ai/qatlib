/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Qatlib.Papers.PolyMethod01.SymDegree.SymmetricDegreeLower
import Mathlib.Data.Nat.Dist

/-!
# Layer changes and the symmetric jump parameter

The parameter `Gamma` is the infimum of distances `Nat.dist (2 * k + 1) n` over changing weight
layers. For nonconstant symmetric functions this distance is attained, and layer values remain
constant across bands with smaller distance; polynomial approximation also gives a root between
each pair of changing layers. These constructions support the symmetric-function analysis of
[BealsEtAl2001].

## Main statements

* `gamma_mem`: For a nonconstant symmetric Boolean function, the jump parameter belongs to its
  changing-layer distance set.
* `layerVal_const_on_band`: For a symmetric function, the layer values at `a ≤ b ≤ n` are equal
  if every intervening layer distance is strictly below `Gamma f`.
* `jump_root`: If `p` approximates a symmetric Boolean function within one third, each changing
  layer `k < n` yields a root of `avgPoly p - 1 / 2` strictly between `k` and `k + 1`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.PolyMethod01.SymDegree

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open scoped Classical BigOperators

variable {n : ℕ}

/-- The existence of words of weights `k` and `k + 1` on which `f` takes different values. -/
def LayerChange (f : (Fin n → Bool) → Bool) (k : ℕ) : Prop :=
  ∃ x y : Fin n → Bool, boolWeight x = k ∧ boolWeight y = k + 1 ∧ f x ≠ f y

/-- The set of distances `Nat.dist (2 * k + 1) n` for changing layers with `k < n`. -/
def jumpDist (f : (Fin n → Bool) → Bool) : Set ℕ :=
  {d | ∃ k, k < n ∧ LayerChange f k ∧ d = Nat.dist (2 * k + 1) n}

/-- The natural-number infimum of the changing-layer distance set `jumpDist f`. -/
def Gamma (f : (Fin n → Bool) → Bool) : ℕ := sInf (jumpDist f)

/-- The jump parameter is at most the distance associated with any changing layer `k < n`. -/
theorem gamma_le_of_layerChange {f : (Fin n → Bool) → Bool} {k : ℕ}
    (hk : k < n) (hc : LayerChange f k) :
    Gamma f ≤ Nat.dist (2 * k + 1) n :=
  Nat.sInf_le ⟨k, hk, hc, rfl⟩

/-- A layer `k < n` whose distance is strictly smaller than `Gamma f` cannot be a changing
layer. See [Beals et al., 2001][BealsEtAl2001]. -/
theorem gamma_band_no_change {f : (Fin n → Bool) → Bool} {k : ℕ} (hk : k < n)
    (h : Nat.dist (2 * k + 1) n < Gamma f) : ¬ LayerChange f k := by
  intro hc
  have hle := gamma_le_of_layerChange (f := f) hk hc
  omega

/-- The value of `f` on a chosen word of weight `k` when `k ≤ n`, and false for larger `k`. -/
def layerVal (f : (Fin n → Bool) → Bool) (k : ℕ) : Bool :=
  if h : k ≤ n then f (Classical.choose (exists_word_weight (n := n) h)) else false

/-- For a symmetric function, its value on a word of weight `k` equals `layerVal f k`. -/
theorem layerVal_eq {f : (Fin n → Bool) → Bool} (hsym : Symmetric f) {k : ℕ}
    (w : Fin n → Bool) (hw : boolWeight w = k) : f w = layerVal f k := by
  have hk : k ≤ n := by
    have h := Finset.card_le_univ (boolSupp w)
    rw [← hw]
    simpa [boolWeight] using! h
  unfold layerVal
  rw [dif_pos hk]
  exact hsym w _ (hw.trans (Classical.choose_spec (exists_word_weight (n := n) hk)).symm)

/-- A layer change of a symmetric function forces distinct values on the two adjacent weight
layers. -/
theorem layerVal_ne_of_layerChange {f : (Fin n → Bool) → Bool} (hsym : Symmetric f)
    {k : ℕ} (hc : LayerChange f k) : layerVal f k ≠ layerVal f (k + 1) := by
  intro heq
  obtain ⟨x, y, hx, hy, hxy⟩ := hc
  have hx' : f x = layerVal f k := layerVal_eq hsym x hx
  have hy' : f y = layerVal f (k + 1) := layerVal_eq hsym y hy
  exact hxy (hx'.trans (heq.trans hy'.symm))

/-- For a symmetric function and `k < n`, unequal adjacent layer values imply a layer change. -/
theorem layerChange_of_layerVal_ne {f : (Fin n → Bool) → Bool} (hsym : Symmetric f)
    {k : ℕ} (hk : k < n) (h : layerVal f k ≠ layerVal f (k + 1)) :
    LayerChange f k := by
  obtain ⟨x, hx⟩ := exists_word_weight (n := n) (k := k) (by omega)
  obtain ⟨y, hy⟩ := exists_word_weight (n := n) (k := k + 1) (by omega)
  refine ⟨x, y, hx, hy, ?_⟩
  rw [layerVal_eq hsym x hx, layerVal_eq hsym y hy]
  exact h

/-- For a symmetric function and `k < n`, a layer change is equivalent to unequal adjacent layer
values. -/
theorem layerChange_iff {f : (Fin n → Bool) → Bool} (hsym : Symmetric f) {k : ℕ}
    (hk : k < n) : LayerChange f k ↔ layerVal f k ≠ layerVal f (k + 1) :=
  ⟨layerVal_ne_of_layerChange hsym, layerChange_of_layerVal_ne hsym hk⟩

/-- For a symmetric function, the layer values at `a ≤ b ≤ n` are equal if no layer changes
occur between them. -/
theorem layerVal_const_of_no_change {f : (Fin n → Bool) → Bool} (hsym : Symmetric f)
    {a b : ℕ} (hab : a ≤ b) (hn : b ≤ n)
    (h : ∀ k, a ≤ k → k < b → ¬ LayerChange f k) : layerVal f a = layerVal f b := by
  have key : ∀ m, a ≤ m → m ≤ b → layerVal f a = layerVal f m := by
    intro m ham
    refine Nat.le_induction (P := fun m _ => m ≤ b → layerVal f a = layerVal f m)
      ?_ ?_ m ham
    · intro _; rfl
    · intro p hap ih hpb
      have hpb' : p < b := by omega
      have hnc := h p hap hpb'
      have heq : layerVal f p = layerVal f (p + 1) := by
        by_contra hne
        exact hnc (layerChange_of_layerVal_ne hsym (by omega) hne)
      exact (ih (by omega)).trans heq
  exact key b hab (le_refl b)

/-- For a symmetric function, the layer values at `a ≤ b ≤ n` are equal if every intervening
layer distance is strictly below `Gamma f`. See [Beals et al., 2001][BealsEtAl2001]. -/
theorem layerVal_const_on_band {f : (Fin n → Bool) → Bool} (hsym : Symmetric f)
    {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n)
    (hband : ∀ k, a ≤ k → k < b → Nat.dist (2 * k + 1) n < Gamma f) :
    layerVal f a = layerVal f b :=
  layerVal_const_of_no_change hsym hab hbn
    (fun k ha hk => gamma_band_no_change (by omega) (hband k ha hk))

/-- A nonconstant symmetric Boolean function has a changing layer `k < n`. -/
theorem exists_layerChange_of_symmetric_nonconstant {f : (Fin n → Bool) → Bool}
    (hsym : Symmetric f) (hnc : Nonconstant f) : ∃ k, k < n ∧ LayerChange f k := by
  classical
  obtain ⟨x, y, hxy⟩ := hnc
  have hxn : boolWeight x ≤ n := by
    have h := Finset.card_le_univ (boolSupp x)
    simpa [boolWeight] using! h
  have hyn : boolWeight y ≤ n := by
    have h := Finset.card_le_univ (boolSupp y)
    simpa [boolWeight] using! h
  have hxval : f x = layerVal f (boolWeight x) := layerVal_eq hsym x rfl
  have hyval : f y = layerVal f (boolWeight y) := layerVal_eq hsym y rfl
  have hne : layerVal f (boolWeight x) ≠ layerVal f (boolWeight y) := by
    intro h
    exact hxy (hxval.trans (h.trans hyval.symm))
  rcases lt_trichotomy (boolWeight x) (boolWeight y) with hlt | heq | hgt
  · by_contra hcon
    have hno : ∀ k, boolWeight x ≤ k → k < boolWeight y → ¬ LayerChange f k := by
      intro k _ hkb hc
      exact hcon ⟨k, by omega, hc⟩
    exact hne (layerVal_const_of_no_change hsym (le_of_lt hlt) hyn hno)
  · exact absurd (by rw [heq]) hne
  · by_contra hcon
    have hno : ∀ k, boolWeight y ≤ k → k < boolWeight x → ¬ LayerChange f k := by
      intro k _ hkb hc
      exact hcon ⟨k, by omega, hc⟩
    exact hne (layerVal_const_of_no_change hsym (le_of_lt hgt) hxn hno).symm

/-- The changing-layer distance set of a nonconstant symmetric Boolean function is nonempty. -/
theorem jumpDist_nonempty {f : (Fin n → Bool) → Bool} (hsym : Symmetric f)
    (hnc : Nonconstant f) : (jumpDist f).Nonempty := by
  obtain ⟨k, hk, hc⟩ := exists_layerChange_of_symmetric_nonconstant hsym hnc
  exact ⟨Nat.dist (2 * k + 1) n, k, hk, hc, rfl⟩

/-- For a nonconstant symmetric Boolean function, the jump parameter belongs to its
changing-layer distance set. See [Beals et al., 2001][BealsEtAl2001]. -/
theorem gamma_mem {f : (Fin n → Bool) → Bool} (hsym : Symmetric f)
    (hnc : Nonconstant f) : Gamma f ∈ jumpDist f :=
  Nat.sInf_mem (jumpDist_nonempty hsym hnc)

/-- For a nonconstant symmetric Boolean function on `n` bits, the jump parameter is at most `n -
1`. -/
theorem gamma_le_pred {f : (Fin n → Bool) → Bool} (hsym : Symmetric f)
    (hnc : Nonconstant f) : Gamma f ≤ n - 1 := by
  obtain ⟨k, hk, hc, hd⟩ := gamma_mem hsym hnc
  rw [hd]
  by_cases h : 2 * k + 1 ≤ n
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_eq_sub_of_le_right (le_of_lt (Nat.lt_of_not_le h))]
    omega

/-- A nonconstant symmetric Boolean function in even dimension has positive jump parameter. -/
theorem gamma_pos_of_even {f : (Fin n → Bool) → Bool} (hsym : Symmetric f)
    (hnc : Nonconstant f) (heven : Even n) : 0 < Gamma f := by
  obtain ⟨k, hk, hc, hd⟩ := gamma_mem hsym hnc
  rw [hd]
  have hpos : Nat.dist (2 * k + 1) n ≠ 0 := by
    intro h0
    have heq := Nat.eq_of_dist_eq_zero h0
    obtain ⟨m, hm⟩ := heven
    omega
  exact Nat.pos_of_ne_zero hpos

/-- If `p` approximates a symmetric Boolean function within one third on the cube, its layer
average approximates every valid layer value within one third. See [Beals et al.,
2001][BealsEtAl2001]. -/
theorem layerAverage_close_symmetric {f : (Fin n → Bool) → Bool} (hsym : Symmetric f)
    {p : MvPolynomial (Fin n) ℝ}
    (hyp : ∀ g : Fin n → Bool,
      |p.eval (boolPoint g) - (if f g then (1 : ℝ) else 0)| ≤ 1 / 3)
    {k : ℕ} (hk : k ≤ n) :
    |layerAverage p k - (if layerVal f k then (1 : ℝ) else 0)| ≤ 1 / 3 := by
  classical
  set c : ℝ := if layerVal f k then (1 : ℝ) else 0 with hcdef
  have hck : (Nat.choose n k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hk)
  have hckpos : (0 : ℝ) < (Nat.choose n k : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  have hA : layerAverage p k - c
      = (Nat.choose n k : ℝ)⁻¹ *
        (∑ g : {g : Fin n → Bool // boolWeight g = k}, (p.eval (boolPoint g.1) - c)) := by
    have key : (∑ g : {g : Fin n → Bool // boolWeight g = k},
        (p.eval (boolPoint g.1) - c))
        = (∑ g : {g : Fin n → Bool // boolWeight g = k}, p.eval (boolPoint g.1))
          - (Nat.choose n k : ℝ) * c := by
      show (∑ g ∈ (Finset.univ : Finset {g : Fin n → Bool // boolWeight g = k}),
          (p.eval (boolPoint g.1) - c)) = _
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        card_level_real (I := Fin n) k]
      simp
    rw [layerAverage, layerSum, key]
    simp only [Fintype.card_fin]
    field_simp [hck]
  have hterm : ∀ g : {g : Fin n → Bool // boolWeight g = k},
      |p.eval (boolPoint g.1) - c| ≤ 1 / 3 := by
    intro g
    have hval : f g.1 = layerVal f k := layerVal_eq hsym g.1 g.2
    have hg := hyp g.1
    rw [hval] at hg
    simpa [hcdef] using! hg
  rw [hA]
  calc |(Nat.choose n k : ℝ)⁻¹ *
        (∑ g : {g : Fin n → Bool // boolWeight g = k}, (p.eval (boolPoint g.1) - c))|
      = |(Nat.choose n k : ℝ)⁻¹| *
        |∑ g : {g : Fin n → Bool // boolWeight g = k},
          (p.eval (boolPoint g.1) - c)| := abs_mul _ _
    _ ≤ |(Nat.choose n k : ℝ)⁻¹| *
        ∑ g : {g : Fin n → Bool // boolWeight g = k},
          |p.eval (boolPoint g.1) - c| := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      show |∑ g ∈ (Finset.univ : Finset {g : Fin n → Bool // boolWeight g = k}),
        (p.eval (boolPoint g.1) - c)| ≤ _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = (Nat.choose n k : ℝ)⁻¹ *
        ∑ g : {g : Fin n → Bool // boolWeight g = k},
          |p.eval (boolPoint g.1) - c| := by
      rw [abs_of_pos (inv_pos.mpr hckpos)]
    _ ≤ (Nat.choose n k : ℝ)⁻¹ *
        ∑ _g : {g : Fin n → Bool // boolWeight g = k}, (1 / 3 : ℝ) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hckpos))
      show (∑ g ∈ (Finset.univ : Finset {g : Fin n → Bool // boolWeight g = k}),
        |p.eval (boolPoint g.1) - c|) ≤ _
      exact Finset.sum_le_sum fun g _ => hterm g
    _ = (Nat.choose n k : ℝ)⁻¹ *
        ((Fintype.card {g : Fin n → Bool // boolWeight g = k} : ℝ) * (1 / 3 : ℝ)) := by
      congr 1
      show (∑ _g ∈ (Finset.univ : Finset {g : Fin n → Bool // boolWeight g = k}),
        (1 / 3 : ℝ)) = _
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 1 / 3 := by
      rw [card_level_real (I := Fin n) k]
      simp only [Fintype.card_fin]
      field_simp [hck]

/-- If `p` approximates a symmetric Boolean function within one third, each changing layer `k <
n` yields a root of `avgPoly p - 1 / 2` strictly between `k` and `k + 1`. See [Beals et al.,
2001][BealsEtAl2001]. -/
theorem jump_root {f : (Fin n → Bool) → Bool} (hsym : Symmetric f)
    {p : MvPolynomial (Fin n) ℝ}
    (hyp : ∀ g : Fin n → Bool,
      |p.eval (boolPoint g) - (if f g then (1 : ℝ) else 0)| ≤ 1 / 3)
    {k : ℕ} (hk : k < n) (hc : LayerChange f k) :
    ∃ c : ℝ, c ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ) ∧
      (avgPoly p - Polynomial.C ((1 : ℝ) / 2)).eval c = 0 := by
  classical
  have hk' : k ≤ n := le_of_lt hk
  have hk1 : k + 1 ≤ n := by omega
  have hne : layerVal f k ≠ layerVal f (k + 1) := layerVal_ne_of_layerChange hsym hc
  have hbk := layerAverage_close_symmetric hsym hyp hk'
  have hbk1 := layerAverage_close_symmetric hsym hyp hk1
  rw [layerAverage_eq_avgPoly p k (by simpa using! hk')] at hbk
  rw [layerAverage_eq_avgPoly p (k + 1) (by simpa using! hk1)] at hbk1
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by rw [Nat.cast_succ]; linarith
  have hsign : (1 / 2 < (avgPoly p).eval (k : ℝ) ∧
        (avgPoly p).eval ((k + 1 : ℕ) : ℝ) < 1 / 2) ∨
      ((avgPoly p).eval (k : ℝ) < 1 / 2 ∧
        1 / 2 < (avgPoly p).eval ((k + 1 : ℕ) : ℝ)) := by
    cases hk0 : layerVal f k <;> cases hk1v : layerVal f (k + 1)
    · exact absurd (hk0.trans hk1v.symm) hne
    · have h0 : |(avgPoly p).eval (k : ℝ)| ≤ 1 / 3 := by
        simpa [hk0] using! hbk
      have h1 : |(avgPoly p).eval ((k + 1 : ℕ) : ℝ) - 1| ≤ 1 / 3 := by
        simpa [hk1v] using! hbk1
      refine Or.inr ⟨?_, ?_⟩
      · have := le_abs_self ((avgPoly p).eval (k : ℝ)); linarith
      · have := neg_le_abs ((avgPoly p).eval ((k + 1 : ℕ) : ℝ) - 1); linarith
    · have h0 : |(avgPoly p).eval (k : ℝ) - 1| ≤ 1 / 3 := by
        simpa [hk0] using! hbk
      have h1 : |(avgPoly p).eval ((k + 1 : ℕ) : ℝ)| ≤ 1 / 3 := by
        simpa [hk1v] using! hbk1
      refine Or.inl ⟨?_, ?_⟩
      · have := neg_le_abs ((avgPoly p).eval (k : ℝ) - 1); linarith
      · have := le_abs_self ((avgPoly p).eval ((k + 1 : ℕ) : ℝ)); linarith
    · exact absurd (hk0.trans hk1v.symm) hne
  have hcont : ContinuousOn (fun t : ℝ => (avgPoly p).eval t)
      (Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := (Polynomial.continuous _).continuousOn
  have himg : (1 / 2 : ℝ) ∈ (fun t : ℝ => (avgPoly p).eval t) ''
      Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    rcases hsign with ⟨hfk, hfk1⟩ | ⟨hfk, hfk1⟩
    · exact (intermediate_value_Icc' hle hcont) (show (1 / 2 : ℝ) ∈
        Set.Icc ((avgPoly p).eval ((k + 1 : ℕ) : ℝ)) ((avgPoly p).eval (k : ℝ)) from
          Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
    · exact (intermediate_value_Icc hle hcont) (show (1 / 2 : ℝ) ∈
        Set.Icc ((avgPoly p).eval (k : ℝ)) ((avgPoly p).eval ((k + 1 : ℕ) : ℝ)) from
          Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨c, hc', hcv⟩ := himg
  (try dsimp only at hcv)
  rcases hsign with ⟨hfk, hfk1⟩ | ⟨hfk, hfk1⟩
  · refine ⟨c, ?_, ?_⟩
    · rw [Set.mem_Ioo]
      have hne1 : c ≠ (k : ℝ) := by intro h; rw [h] at hcv; linarith
      have hne2 : c ≠ ((k + 1 : ℕ) : ℝ) := by intro h; rw [h] at hcv; linarith
      exact ⟨lt_of_le_of_ne hc'.1 (Ne.symm hne1), lt_of_le_of_ne hc'.2 hne2⟩
    · simp [Polynomial.eval_sub, hcv]
  · refine ⟨c, ?_, ?_⟩
    · rw [Set.mem_Ioo]
      have hne1 : c ≠ (k : ℝ) := by intro h; rw [h] at hcv; linarith
      have hne2 : c ≠ ((k + 1 : ℕ) : ℝ) := by intro h; rw [h] at hcv; linarith
      exact ⟨lt_of_le_of_ne hc'.1 (Ne.symm hne1), lt_of_le_of_ne hc'.2 hne2⟩
    · simp [Polynomial.eval_sub, hcv]

end Qatlib.Papers.PolyMethod01.SymDegree
