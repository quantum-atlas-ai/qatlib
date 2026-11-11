/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DihedralSub16.MainResults.DifferenceSetInfluence
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Random-translation injectivization of hidden difference-set instances

Source: Martin Roetteler, *Quantum algorithms for abelian difference sets and
applications to dihedral hidden subgroups*, fixed arXiv:1608.02005v1 (5 Aug 2016),
§3.2 pp. 10–12, eq. (5), Lemma 1 (p. 11) and Theorem 3 (p. 11).

For a hiding function `f : A → S` and `V = {v₁, …, v_m} ⊆ A` the paper defines
`f_V(x) := (f(x + v₁), …, f(x + v_m))`.  Gharibi's bound (eq. (5)) gives

  `Pr_V(f_V not injective) ≤ |A|² (1 - γ_min)^m`,  `γ_min = min_{v≠0} γ_v(f)`.

For the characteristic function of a `(v,k,λ)`-difference set, Lemma 1 gives
`γ_v(f) = 2(k-λ)/v` for every `v ≠ 0`.  Theorem 3 concludes that
`m = O(log |A|)` copies suffice to obtain an injective `f_V` with probability
greater than `1 - 1/64`.

This file formalises the counting content exactly:

* `card_badTranslations_le` — the union bound over the `|A|²` ordered pairs:
  the number of non-injective translation tuples of length `m` is at most
  `|A|² (|A| - 2(k-λ))^m`;
* `theorem3_probability_le` — the same divided by the number `|A|^m` of tuples,
  i.e. bound (5) specialised to difference sets, with `1 - 2(k-λ)/|A|` in place
  of `1 - γ_min`;
* `rpow_probability_le` and `theorem3_probability_lt` — the real-arithmetic
  core: for `m ≥ ⌈(6 + 2 log₂|A|)/γ_min⌉` the failure probability is at most
  `1/64`.  In the paper's applications `γ_min = Θ(1)` (Paley, Hadamard and
  Singer difference sets), so this threshold is `O(log |A|)`, which is the
  content of Theorem 3; for a general difference set the threshold is
  `O(log(|A|)/γ_min)`.
-/

namespace Qatlib.Papers.DihedralSub16.MainResults

open Finset

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

noncomputable section

open Classical

/-- The `m`-fold translation injectivization `f_V(x) = (f(x + v₁), …, f(x + v_m))`
of the characteristic function of `D` (arXiv:1608.02005v1, §3.2, p. 10). -/
def injectivized (D : Finset A) (m : ℕ) (V : Fin m → A) (x : A) : Fin m → Bool :=
  fun i => charFun D (x + V i)

/-- The set of shifts `a` at which the characteristic function of `D` is invariant
under the translation `a ↦ a + w`. -/
def stableShifts (D : Finset A) (w : A) : Finset A :=
  Finset.univ.filter (fun a => charFun D a = charFun D (a + w))

/-- For a pair `(x, y)` of inputs, the set of shifts `a` that make the two
evaluations `f(x + a)` and `f(y + a)` agree (written as a set of shifts). -/
def pairStable (D : Finset A) (x y : A) : Finset A :=
  Finset.univ.filter (fun a => charFun D (x + a) = charFun D (y + a))

/-- The set of length-`m` translation tuples all of whose coordinates lie in
`pairStable D x y`: these are precisely the tuples `V` for which `f_V(x) = f_V(y)`. -/
def pairBad (D : Finset A) (m : ℕ) (x y : A) : Finset (Fin m → A) :=
  Fintype.piFinset (fun _ : Fin m => pairStable D x y)

/-- The set of length-`m` translation tuples for which the injectivized function
`f_V` fails to be injective. -/
def badTranslations (D : Finset A) (m : ℕ) : Finset (Fin m → A) :=
  Finset.univ.filter (fun V => ¬ Function.Injective (injectivized D m V))

/-- For a difference set, the number of shifts stabilizing the characteristic
function is `|A| - 2(k - λ)` (the complement of the `2(k - λ)` shifts that change it,
Lemma 1). -/
theorem card_stableShifts (D : Finset A) (lam : ℕ) (hD : IsDifferenceSet D lam)
    (w : A) (hw : w ≠ 0) :
    (stableShifts D w).card = Fintype.card A - 2 * (D.card - lam) := by
  have hI : (D.filter (fun d => d + w ∈ D)).card = lam := by
    have h := hD (-w) (neg_ne_zero.mpr hw)
    simpa [sub_eq_add_neg] using h
  have hle : lam ≤ D.card := by
    rw [← hI]
    exact Finset.card_filter_le _ _
  have hcount := card_filter_charFun_ne_add D w
  rw [hI] at hcount
  have hchange : (Finset.univ.filter (fun x => charFun D x ≠ charFun D (x + w))).card
      = 2 * (D.card - lam) := by omega
  have hcompl : stableShifts D w
      = Finset.univ.filter (fun x => ¬ (charFun D x ≠ charFun D (x + w))) := by
    ext x
    simp [stableShifts]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset A))
    (p := fun x => charFun D x ≠ charFun D (x + w))
  simp only [Finset.card_univ] at hsplit
  rw [hcompl]
  omega

/-- `pairStable D x y` is the translate of `stableShifts D (y - x)` by `-x`. -/
theorem pairStable_eq_image (D : Finset A) (x y : A) :
    pairStable D x y = (stableShifts D (y - x)).image (fun z => z - x) := by
  ext a
  rw [Finset.mem_image]
  simp only [pairStable, stableShifts, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    refine ⟨x + a, ?_, by abel⟩
    rw [show x + a + (y - x) = y + a by abel]
    exact h
  · rintro ⟨z, hz, rfl⟩
    rw [show x + (z - x) = z by abel, show y + (z - x) = z + (y - x) by abel]
    exact hz

/-- Cardinality of `pairStable` for distinct inputs, via Lemma 1. -/
theorem card_pairStable (D : Finset A) (lam : ℕ) (hD : IsDifferenceSet D lam)
    (x y : A) (hxy : x ≠ y) :
    (pairStable D x y).card = Fintype.card A - 2 * (D.card - lam) := by
  rw [pairStable_eq_image]
  rw [Finset.card_image_of_injective _ (fun a b h => by
    have := congrArg (fun z => z + x) h
    simpa using this)]
  have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  exact card_stableShifts D lam hD (y - x) hne

/-- Membership in `pairBad D m x y` means that `f_V` agrees at `x` and `y`. -/
theorem mem_pairBad {D : Finset A} {m : ℕ} {x y : A} {V : Fin m → A} :
    V ∈ pairBad D m x y ↔ ∀ i, charFun D (x + V i) = charFun D (y + V i) := by
  simp only [pairBad, Fintype.mem_piFinset, pairStable, mem_filter, mem_univ, true_and]

/-- Cardinality of `pairBad D m x y` for distinct `x ≠ y`. -/
theorem card_pairBad (D : Finset A) (lam : ℕ) (hD : IsDifferenceSet D lam)
    (m : ℕ) (x y : A) (hxy : x ≠ y) :
    (pairBad D m x y).card = (Fintype.card A - 2 * (D.card - lam)) ^ m := by
  simp only [pairBad, Fintype.card_piFinset_const, card_pairStable D lam hD x y hxy]

/-- Membership in `badTranslations`: `f_V` is not injective. -/
theorem mem_badTranslations {D : Finset A} {m : ℕ} {V : Fin m → A} :
    V ∈ badTranslations D m ↔
      ∃ x y : A, x ≠ y ∧ ∀ i, charFun D (x + V i) = charFun D (y + V i) := by
  simp only [badTranslations, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    by_contra hc
    apply h
    intro x y hxy
    by_contra hne
    have hstep : ∃ i, charFun D (x + V i) ≠ charFun D (y + V i) := by
      by_contra hc2
      exact hc ⟨x, y, hne, fun i => by
        by_contra hi
        exact hc2 ⟨i, hi⟩⟩
    obtain ⟨i, hi⟩ := hstep
    exact hi (congrFun hxy i)
  · rintro ⟨x, y, hne, h⟩ hinj
    exact hne (hinj (funext fun i => h i))

/-- Union bound for the injectivization failure set: at most `|A|²` ordered pairs,
each contributing `(|A| - 2(k - λ))^m` translation tuples.  This is bound (5) of
arXiv:1608.02005v1 (p. 11) for the characteristic function of a difference set,
in exact counting form. -/
theorem card_badTranslations_le (D : Finset A) (lam m : ℕ) (hD : IsDifferenceSet D lam) :
    (badTranslations D m).card
      ≤ (Fintype.card A) ^ 2 * (Fintype.card A - 2 * (D.card - lam)) ^ m := by
  classical
  set P : Finset (A × A) := Finset.univ.filter (fun p : A × A => p.1 ≠ p.2) with hP
  have hsub : badTranslations D m ⊆ P.biUnion (fun p => pairBad D m p.1 p.2) := by
    intro V hV
    rw [mem_badTranslations] at hV
    obtain ⟨x, y, hne, hmem⟩ := hV
    refine Finset.mem_biUnion.mpr ⟨(x, y), ?_, ?_⟩
    · rw [hP]
      simpa using hne
    · exact mem_pairBad.mpr hmem
  calc (badTranslations D m).card
      ≤ (P.biUnion (fun p => pairBad D m p.1 p.2)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P, (pairBad D m p.1 p.2).card := Finset.card_biUnion_le
    _ = ∑ _p ∈ P, (Fintype.card A - 2 * (D.card - lam)) ^ m := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [hP, mem_filter] at hp
        exact card_pairBad D lam hD m p.1 p.2 hp.2
    _ = P.card * (Fintype.card A - 2 * (D.card - lam)) ^ m := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (Fintype.card A) ^ 2 * (Fintype.card A - 2 * (D.card - lam)) ^ m := by
        refine Nat.mul_le_mul_right _ ?_
        calc P.card ≤ (Finset.univ : Finset (A × A)).card := Finset.card_filter_le _ _
          _ = Fintype.card (A × A) := Finset.card_univ
          _ = Fintype.card A * Fintype.card A := Fintype.card_prod _ _
          _ = (Fintype.card A) ^ 2 := (pow_two _).symm

/-- Bound (5) of arXiv:1608.02005v1 (p. 11) in probability form, specialised to
the characteristic function of a `(v,k,λ)`-difference set:
`Pr_V(f_V not injective) ≤ |A|² (1 - 2(k-λ)/|A|)^m`. -/
theorem theorem3_probability_le (D : Finset A) (lam m : ℕ) (hD : IsDifferenceSet D lam)
    (hcard : 0 < Fintype.card A) :
    ((badTranslations D m).card : ℝ) / (Fintype.card A : ℝ) ^ m
      ≤ (Fintype.card A : ℝ) ^ 2 *
          (((Fintype.card A - 2 * (D.card - lam) : ℕ) : ℝ) / (Fintype.card A : ℝ)) ^ m := by
  classical
  have hv : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast hcard
  have hvm : (0 : ℝ) < (Fintype.card A : ℝ) ^ m := pow_pos hv m
  have hcount := card_badTranslations_le D lam m hD
  have hc : ((badTranslations D m).card : ℝ)
      ≤ (Fintype.card A : ℝ) ^ 2 *
          (((Fintype.card A - 2 * (D.card - lam) : ℕ) : ℝ)) ^ m := by
    exact_mod_cast hcount
  rw [div_le_iff₀ hvm]
  calc ((badTranslations D m).card : ℝ)
      ≤ (Fintype.card A : ℝ) ^ 2 *
          (((Fintype.card A - 2 * (D.card - lam) : ℕ) : ℝ)) ^ m := hc
    _ = (Fintype.card A : ℝ) ^ 2 *
          ((((Fintype.card A - 2 * (D.card - lam) : ℕ) : ℝ) / (Fintype.card A : ℝ)) ^ m)
          * (Fintype.card A : ℝ) ^ m := by
        rw [div_pow]
        field_simp

/-- `(v - c)^m / v^m = (1 - c/v)^m`, the rewrite that puts the injectivization bound
in the form `|A|² (1 - γ)^m` of the paper. -/
theorem nat_sub_div_pow {v c : ℕ} (hc : c ≤ v) (hv : 0 < v) (m : ℕ) :
    (((v - c : ℕ) : ℝ) / (v : ℝ)) ^ m
      = (1 - (c : ℝ) / (v : ℝ)) ^ m := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hv)
  congr 1
  rw [Nat.cast_sub hc]
  field_simp

/-- Theorem 3 of arXiv:1608.02005v1 (p. 11), probability form with the paper's
`γ_min = 2(k-λ)/|A|`: when `2(k-λ) ≤ |A|`, the failure probability of the
`m`-fold random-translation injectivization is at most
`|A|² (1 - 2(k-λ)/|A|)^m`. -/
theorem theorem3_probability_gamma (D : Finset A) (lam m : ℕ) (hD : IsDifferenceSet D lam)
    (hcard : 2 ≤ Fintype.card A) (hkv : 2 * (D.card - lam) ≤ Fintype.card A) :
    ((badTranslations D m).card : ℝ) / (Fintype.card A : ℝ) ^ m
      ≤ (Fintype.card A : ℝ) ^ 2 *
          (1 - 2 * ((D.card : ℝ) - (lam : ℝ)) / (Fintype.card A : ℝ)) ^ m := by
  have hcard0 : 0 < Fintype.card A := by omega
  have hle : lam ≤ D.card := by
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card A)
    have hv : a - b ≠ 0 := sub_ne_zero.mpr hab
    have h := hD (a - b) hv
    rw [← h]
    exact Finset.card_filter_le _ _
  calc ((badTranslations D m).card : ℝ) / (Fintype.card A : ℝ) ^ m
      ≤ (Fintype.card A : ℝ) ^ 2 *
          (((Fintype.card A - 2 * (D.card - lam) : ℕ) : ℝ) / (Fintype.card A : ℝ)) ^ m :=
        theorem3_probability_le D lam m hD hcard0
    _ = (Fintype.card A : ℝ) ^ 2 *
          (1 - (2 * (D.card - lam) : ℕ) / (Fintype.card A : ℝ)) ^ m := by
        rw [nat_sub_div_pow hkv hcard0 m]
    _ = (Fintype.card A : ℝ) ^ 2 *
          (1 - 2 * ((D.card : ℝ) - (lam : ℝ)) / (Fintype.card A : ℝ)) ^ m := by
        rw [Nat.cast_mul, Nat.cast_sub hle]
        norm_num

/-- Real-arithmetic core of Theorem 3: if `2 ≤ v`, `0 < γ < 1` and
`m ≥ (6 + 2 log₂ v)/γ`, then `v² (1 - γ)^m ≤ 1/64`.  This is the step
"`m ≥ 2 log₂|A| + 6`" of the proof of Theorem 3 (arXiv:1608.02005v1, p. 11,
eqs. (9)–(10)), with `γ = γ_min = 2(k-λ)/|A|`; for the paper's three families of
difference sets `γ_min = Θ(1)`, hence `m = O(log |A|)`. -/
theorem rpow_probability_le (v : ℕ) (γ : ℝ) (hv : 2 ≤ v) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (m : ℕ) (hm : (6 + 2 * Real.logb 2 (v : ℝ)) / γ ≤ (m : ℝ)) :
    (v : ℝ) ^ 2 * (1 - γ) ^ m ≤ 1 / 64 := by
  have hv0 : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (by omega : 0 < v)
  have hv1 : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast (by omega : 1 ≤ v)
  have h1γ : (0 : ℝ) < 1 - γ := by linarith
  -- `log(1-γ) ≤ -γ`
  have hlog_le : Real.log (1 - γ) ≤ -γ := by
    have h := Real.log_le_sub_one_of_pos h1γ
    linarith
  -- `log 2 ≤ 1`
  have hlog2_le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogv_nonneg : (0 : ℝ) ≤ Real.log (v : ℝ) := Real.log_nonneg hv1
  -- `m γ ≥ 6 + 2 log₂ v`
  have hmγ : 6 + 2 * Real.logb 2 (v : ℝ) ≤ (m : ℝ) * γ := by
    have h := hm
    rw [div_le_iff₀ hγ0] at h
    linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- `log v ≤ log v / log 2`, since `0 < log 2 ≤ 1` and `0 ≤ log v`
  have hdiv : Real.log (v : ℝ) ≤ Real.log (v : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos]
    nlinarith [hlogv_nonneg, hlog2_le]
  -- `m γ ≥ 6 log 2 + 2 log v`
  have hmγ' : 6 * Real.log 2 + 2 * Real.log (v : ℝ) ≤ (m : ℝ) * γ := by
    rw [Real.logb] at hmγ
    nlinarith [hmγ, hdiv, hlog2_le, hlogv_nonneg]
  -- main exponent inequality
  have hmain : (m : ℝ) * Real.log (1 - γ) ≤ -6 * Real.log 2 - 2 * Real.log (v : ℝ) := by
    have h1 : (m : ℝ) * Real.log (1 - γ) ≤ (m : ℝ) * (-γ) :=
      mul_le_mul_of_nonneg_left hlog_le hm0
    nlinarith [h1, hmγ']
  -- exponential form
  have hexp1 : (v : ℝ) ^ 2 = Real.exp (2 * Real.log (v : ℝ)) := by
    rw [show (2 : ℝ) * Real.log (v : ℝ) = ((2 : ℕ) : ℝ) * Real.log (v : ℝ) by norm_num]
    rw [Real.exp_nat_mul, Real.exp_log hv0]
  have hexp2 : (1 - γ) ^ m = Real.exp ((m : ℝ) * Real.log (1 - γ)) := by
    rw [Real.exp_nat_mul, Real.exp_log h1γ]
  rw [hexp1, hexp2, ← Real.exp_add]
  calc Real.exp (2 * Real.log (v : ℝ) + (m : ℝ) * Real.log (1 - γ))
      ≤ Real.exp (-6 * Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / 64 := by
        rw [show (-6 * Real.log 2 : ℝ) = -(((6 : ℕ) : ℝ) * Real.log 2) by norm_num,
          Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num

/-- Theorem 3 of arXiv:1608.02005v1 (p. 11), final form: for a nontrivial
`(v,k,λ)`-difference set (`k > λ`, `2(k-λ) < |A|`) and
`m ≥ (6 + 2 log₂|A|)/γ_min` with `γ_min = 2(k-λ)/|A|`, the random-translation
injectivization of the hiding function is non-injective with probability at most
`1/64`, i.e. it is injective with probability greater than `1 - 1/64`. -/
theorem theorem3_injectivization_probability (D : Finset A) (lam m : ℕ)
    (hD : IsDifferenceSet D lam) (hcard : 2 ≤ Fintype.card A)
    (hk : lam < D.card) (hkv : 2 * (D.card - lam) < Fintype.card A)
    (hm : (6 + 2 * Real.logb 2 (Fintype.card A : ℝ)) /
            (2 * ((D.card : ℝ) - (lam : ℝ)) / (Fintype.card A : ℝ)) ≤ (m : ℝ)) :
    ((badTranslations D m).card : ℝ) / (Fintype.card A : ℝ) ^ m ≤ 1 / 64 := by
  have hcard0 : 0 < Fintype.card A := by omega
  have hle : lam ≤ D.card := le_of_lt hk
  have hγ0 : 0 < 2 * ((D.card : ℝ) - (lam : ℝ)) / (Fintype.card A : ℝ) := by
    have : (0 : ℝ) < (D.card : ℝ) - (lam : ℝ) := by
      have : (lam : ℝ) < (D.card : ℝ) := by exact_mod_cast hk
      linarith
    positivity
  have hγ1 : 2 * ((D.card : ℝ) - (lam : ℝ)) / (Fintype.card A : ℝ) < 1 := by
    have hc : ((2 * (D.card - lam) : ℕ) : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast hkv
    rw [Nat.cast_mul, Nat.cast_sub hle] at hc
    rw [div_lt_one (by positivity)]
    exact hc
  calc ((badTranslations D m).card : ℝ) / (Fintype.card A : ℝ) ^ m
      ≤ (Fintype.card A : ℝ) ^ 2 *
          (1 - 2 * ((D.card : ℝ) - (lam : ℝ)) / (Fintype.card A : ℝ)) ^ m :=
        theorem3_probability_gamma D lam m hD hcard (le_of_lt hkv)
    _ ≤ 1 / 64 :=
        rpow_probability_le (Fintype.card A)
          (2 * ((D.card : ℝ) - (lam : ℝ)) / (Fintype.card A : ℝ))
          hcard hγ0 hγ1 m hm

end

end Qatlib.Papers.DihedralSub16.MainResults
