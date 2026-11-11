/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreqMoments15.MainResults.FrequencyMomentModel
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4: moments of the `k`-wise collision count

Paper: Ashley Montanaro, *The quantum complexity of approximating the frequency moments*
(arXiv:1505.00113v3, 4 Aug 2016), Lemma 4, §2.2 p. 6, with its proof in Appendix A,
pp. 18–19.

The quoted statement (Appendix A, p. 18) reads:

> Fix `ℓ` such that `1 ≤ ℓ ≤ n`. Let `s_1, …, s_ℓ ∈ [n]` be picked uniformly at random and
> define
>   `C_k(s_1, …, s_ℓ) := |{T ∈ ([ℓ] choose k) : a_{s_i} = a_{s_j} for all i, j ∈ T}|`.
> Then
>   `E_{s_1,…,s_ℓ}[C_k(s_1,…,s_ℓ)] = (ℓ choose k) F_k / n^k`
> and
>   `Var(C_k) ≤ ∑_{q=k}^{2k-1} (ℓ F_k^{1/k} / n)^q`.

The values `a_i` live in the alphabet `[m]` (represented here by `ZMod m`); the paper's
Lemma 4 uses the special case `m = n`, but the expectation/variance computation is
independent of the alphabet size, so we state it for the general universe `ZMod m`.
The degenerate case `k = 0` (where the paper's `F_0` is the *distinct count*, not
`∑_j n_j^0 = m`) is excluded; the lemma is used in the paper only for `k ≥ 2`.

The expectation identity is proved completely below (Section "Expectation").  The
variance bound is registered as a `Prop`-valued definition, with the paper's proof route
recorded next to it; its second-moment proof is not formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FreqMoments15.MainResults

open scoped BigOperators

variable {n m : ℕ} [NeZero m]

/-- A uniformly random sample of `ℓ` positions of a stream of length `n`. -/
abbrev Sample (ℓ n : ℕ) := Fin ℓ → Fin n

/-- `C_k(s)`: the number of `k`-subsets `T` of the sampled positions whose values
`a_{s_i}` all coincide (paper §2.2 p. 6, Lemma 4). -/
def collCount {ℓ : ℕ} (a : Stream n m) (k : ℕ) (s : Sample ℓ n) : ℕ :=
  (((Finset.univ : Finset (Fin ℓ)).powersetCard k).filter
      (fun T => ∀ i ∈ T, ∀ j ∈ T, a (s i) = a (s j))).card

/-- Expectation over the uniform distribution on `Sample ℓ n` (all `n^ℓ` samples equally
likely), i.e. `E_{s_1,…,s_ℓ}[f]`. -/
def sampleExp {ℓ : ℕ} (f : Sample ℓ n → ℝ) : ℝ :=
  (∑ s : Sample ℓ n, f s) / (n : ℝ) ^ ℓ

/-- Variance over the uniform distribution on `Sample ℓ n`, i.e.
`Var(f) = E[(f − E[f])²]`. -/
def sampleVar {ℓ : ℕ} (f : Sample ℓ n → ℝ) : ℝ :=
  sampleExp (fun s => (f s - sampleExp f) ^ 2)

/-! ## Counting lemmas -/

/-- Cardinality of a subtype is invariant under a pointwise equivalence of predicates. -/
theorem card_subtype_congr {α : Type*} [Fintype α] {p q : α → Prop}
    [DecidablePred p] [DecidablePred q] (h : ∀ x, p x ↔ q x) :
    Fintype.card {x // p x} = Fintype.card {x // q x} :=
  Fintype.card_congr (Equiv.subtypeEquivRight h)

/-- The number of samples whose values on `T` are all equal to a fixed value `v` is
`(freq v)^{|T|} · n^{ℓ−|T|}`: on `T` the entry is forced to `v` (`freq v` choices), off
`T` it is free (`n` choices).  This is the combinatorial content of (2) in Appendix A. -/
theorem card_fiber {ℓ : ℕ} (a : Stream n m) (v : ZMod m) (T : Finset (Fin ℓ)) :
    Fintype.card {s : Sample ℓ n // ∀ i ∈ T, a (s i) = v}
      = freq a v ^ T.card * n ^ (ℓ - T.card) := by
  classical
  have hcard : Fintype.card {s : Sample ℓ n // ∀ i ∈ T, a (s i) = v}
      = Fintype.card (∀ i : Fin ℓ, {x : Fin n // (i ∈ T → a x = v)}) :=
    Fintype.card_congr (Equiv.subtypePiEquivPi (β := fun _ : Fin ℓ => Fin n)
      (p := fun i (x : Fin n) => (i ∈ T → a x = v)))
  rw [hcard, Fintype.card_pi]
  have hfib : ∀ i : Fin ℓ,
      Fintype.card {x : Fin n // (i ∈ T → a x = v)} = if i ∈ T then freq a v else n := by
    intro i
    by_cases hi : i ∈ T
    · rw [if_pos hi]
      rw [card_subtype_congr (q := fun x => a x = v) (fun x => by simp [hi])]
      rw [Fintype.card_subtype]
      simp [freq]
    · rw [if_neg hi]
      rw [card_subtype_congr (q := fun _ => True) (fun x => by simp [hi])]
      simp
  rw [Finset.prod_congr rfl (fun i _ => hfib i)]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hcompl : Finset.univ.filter (fun i : Fin ℓ => i ∉ T) = Tᶜ := by
    ext i
    simp
  rw [show Finset.univ.filter (fun i : Fin ℓ => i ∈ T) = T by ext i; simp]
  rw [hcompl, Finset.card_compl]
  simp

/-- For a fixed `k`-set `T` of positions, the total number of samples for which all `T`-values
agree equals `F_k · n^{ℓ−k}`. -/
theorem sum_indicator_const {ℓ k : ℕ} (a : Stream n m) {T : Finset (Fin ℓ)}
    (hTcard : T.card = k) (hne : T.Nonempty) :
    (∑ s : Sample ℓ n,
        (if (∀ i ∈ T, ∀ j ∈ T, a (s i) = a (s j)) then (1 : ℝ) else 0))
      = (Fk a k : ℝ) * (n : ℝ) ^ (ℓ - k) := by
  classical
  have hpoint : ∀ s : Sample ℓ n,
      (if (∀ i ∈ T, ∀ j ∈ T, a (s i) = a (s j)) then (1 : ℝ) else 0)
        = ∑ v : ZMod m, (if ∀ i ∈ T, a (s i) = v then (1 : ℝ) else 0) := by
    intro s
    by_cases h : ∀ i ∈ T, ∀ j ∈ T, a (s i) = a (s j)
    · rw [if_pos h]
      have hw : ∀ i ∈ T, a (s i) = a (s hne.choose) :=
        fun i hi => h i hi _ hne.choose_spec
      have hsingle :
          (∑ v : ZMod m, (if ∀ i ∈ T, a (s i) = v then (1 : ℝ) else 0))
            = (if ∀ i ∈ T, a (s i) = a (s hne.choose) then
                (1 : ℝ) else 0) := by
        refine Finset.sum_eq_single (a (s hne.choose)) ?_ ?_
        · intro v _ hv
          rw [if_neg]
          intro hp
          exact hv ((hp _ hne.choose_spec).symm.trans (hw _ hne.choose_spec))
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
      rw [hsingle, if_pos (fun i hi => hw i hi)]
    · rw [if_neg h]
      rw [Finset.sum_eq_zero]
      intro v _
      rw [if_neg]
      exact fun hp => h (fun i hi j hj => (hp i hi).trans (hp j hj).symm)
  rw [Finset.sum_congr rfl (fun s _ => hpoint s)]
  rw [Finset.sum_comm]
  have hinner : ∀ v : ZMod m,
      (∑ s : Sample ℓ n, (if ∀ i ∈ T, a (s i) = v then (1 : ℝ) else 0))
        = (freq a v : ℝ) ^ T.card * (n : ℝ) ^ (ℓ - T.card) := by
    intro v
    have hsumb : (∑ s : Sample ℓ n, (if ∀ i ∈ T, a (s i) = v then (1 : ℝ) else 0))
        = (Fintype.card {s : Sample ℓ n // ∀ i ∈ T, a (s i) = v} : ℝ) := by
      have huniv : (∑ s : Sample ℓ n, (if ∀ i ∈ T, a (s i) = v then (1 : ℝ) else 0))
          = (∑ s ∈ (Finset.univ : Finset (Sample ℓ n)),
              (if ∀ i ∈ T, a (s i) = v then (1 : ℝ) else 0)) := rfl
      rw [huniv, Finset.sum_boole, ← Fintype.card_subtype]
    rw [hsumb, card_fiber a v T, hTcard]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun v _ => hinner v)]
  rw [← Finset.sum_mul]
  rw [hTcard]
  congr 1
  rw [Fk, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun v _ => (Nat.cast_pow _ _).symm)

/-! ## Expectation -/

/-- **Lemma 4, expectation part** (paper §2.2 p. 6 and Appendix A p. 18):
the expected number of `k`-wise collisions in a uniformly random sample of `ℓ` positions is
`C(ℓ,k) · F_k / n^k`.  Hypothesis `1 ≤ ℓ ≤ n` and `1 ≤ k` are the paper's side conditions. -/
theorem lemma4_expectation {ℓ k : ℕ} (a : Stream n m) (hk : 0 < k) (hkl : k ≤ ℓ)
    (hℓn : ℓ ≤ n) :
    sampleExp (fun s : Sample ℓ n => (collCount a k s : ℝ))
      = (Nat.choose ℓ k : ℝ) * (Fk a k : ℝ) / (n : ℝ) ^ k := by
  classical
  unfold sampleExp
  have hcs : ∀ s : Sample ℓ n, (collCount a k s : ℝ)
      = ∑ T ∈ (Finset.univ : Finset (Fin ℓ)).powersetCard k,
          (if (∀ i ∈ T, ∀ j ∈ T, a (s i) = a (s j)) then (1 : ℝ) else 0) := by
    intro s
    unfold collCount
    exact (Finset.sum_boole
      (fun T : Finset (Fin ℓ) => ∀ i ∈ T, ∀ j ∈ T, a (s i) = a (s j))
      ((Finset.univ : Finset (Fin ℓ)).powersetCard k)).symm
  rw [Finset.sum_congr rfl (fun s _ => hcs s)]
  rw [Finset.sum_comm]
  have hT : ∀ T ∈ (Finset.univ : Finset (Fin ℓ)).powersetCard k,
      (∑ s : Sample ℓ n,
          (if (∀ i ∈ T, ∀ j ∈ T, a (s i) = a (s j)) then (1 : ℝ) else 0))
        = (Fk a k : ℝ) * (n : ℝ) ^ (ℓ - k) := by
    intro T hTmem
    have hcard : T.card = k := (Finset.mem_powersetCard.mp hTmem).2
    have hne : T.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hk)
    exact sum_indicator_const a hcard hne
  rw [Finset.sum_congr rfl hT]
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have hn0 : 0 < n := lt_of_lt_of_le hk (le_trans hkl hℓn)
    exact_mod_cast hn0
  have hpow : (n : ℝ) ^ (ℓ - k) * (n : ℝ) ^ k = (n : ℝ) ^ ℓ := by
    rw [← pow_add, Nat.sub_add_cancel hkl]
  field_simp
  rw [← hpow]
  simp only [Fintype.card_fin]
  ring

/-! ## Variance

The variance bound is the second-moment computation of Appendix A p. 18–19.  The paper
derives
`E[C_k²] = ∑_{T,U} Pr[T-values and U-values all agree]`, splits the sum by whether
`T ∩ U ≠ ∅`, uses `Pr[T and U agree] = Pr[T ∪ U agree]` when `T ∩ U ≠ ∅` and independence
when `T ∩ U = ∅`, and concludes
`E[C_k²] ≤ ∑_{q=k}^{2k-1} (ℓ F_k^{1/k}/n)^q + (ℓ choose k)((ℓ-k) choose k)² F_k²/n^{2k}`,
hence `Var(C_k) ≤ ∑_{q=k}^{2k-1} (ℓ F_k^{1/k}/n)^q`.

Formal gap: this needs (i) the pair-counting bound
`|{T,U ∈ ([ℓ] choose k) : |T∪U| = q}| ≤ ℓ^q`, (ii) the ℓ^p-norm monotonicity
`F_q^{1/q} ≤ F_k^{1/k}` for `q ≥ k` (from `∑ n_j^q ≤ (∑ n_j^k)^{q/k}`), and (iii) the
algebraic rearrangement.  These are all standard but amount to a substantial second-moment
development; the honest expectation part above is complete.
Suggested takeover: prove (i) via `Finset.card_le` on the injection that records
`T ∩ U` and the two disjoint differences, then (ii) via `Real.rpow_le_rpow` applied to
`∑ n_j^q ≤ (∑ n_j^k)^(q/k)` (Hölder/power-mean for finite families). -/

/-- **Lemma 4, variance part — statement registration** (paper §2.2 p. 6 and Appendix A
pp. 18–19).  The variance of the collision count is at most
`∑_{q=k}^{2k−1} (ℓ · F_k^{1/k} / n)^q`.

**Status.** The statement is registered as a `Prop`-valued definition; the second-moment
argument of Appendix A (pair counting, power-mean monotonicity and algebraic
rearrangement) is not formalised here. -/
def lemma4_variance_statement {ℓ k : ℕ} (a : Stream n m) (hk : 0 < k) (hkl : k ≤ ℓ)
    (hℓn : ℓ ≤ n) : Prop :=
  sampleVar (fun s : Sample ℓ n => (collCount a k s : ℝ))
    ≤ ∑ q ∈ Finset.Icc k (2 * k - 1),
        ((ℓ : ℝ) * Real.rpow (Fk a k : ℝ) (1 / (k : ℝ)) / (n : ℝ)) ^ q

/-- **Lemma 4 — statement registration**: expectation (proved in `lemma4_expectation`) and
the variance bound (registered in `lemma4_variance_statement`). -/
def lemma4_statement {ℓ k : ℕ} (a : Stream n m) (hk : 0 < k) (hkl : k ≤ ℓ) (hℓn : ℓ ≤ n) : Prop :=
  sampleExp (fun s : Sample ℓ n => (collCount a k s : ℝ))
      = (Nat.choose ℓ k : ℝ) * (Fk a k : ℝ) / (n : ℝ) ^ k ∧
    lemma4_variance_statement a hk hkl hℓn

end Qatlib.Papers.FreqMoments15.MainResults
