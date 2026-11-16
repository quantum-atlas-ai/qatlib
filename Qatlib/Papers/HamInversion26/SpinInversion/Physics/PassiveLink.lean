/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section


set_option autoImplicit false

/-!
# Passive linear-optical links and circulant/bright-mode certificates
# (Corollary 3, Propositions S22–S23)

Fixed arXiv:2607.29382v2, Letter page 4 and Supplement pages S22–S25.

* **Proposition S22** (Supplement, page S22, Eqs. (S108)–(S110)): for `n` modes and at
  most `N` photons, the sector dimensions are `C(n + r − 1, r)`. The sector sum is bounded
  by `N [quniv(n) + 1]`, assuming the stated bound on each sector's query cost and zero
  cost for the vacuum sector.
* **Corollary 3** (Letter, page 4): the numerical inequality
  `N (n² + 1) ≤ N (n + 1)²` bounds the resulting polynomial expression.
* **Proposition S23** (Supplement, page S24, Eqs. (S115)–(S119)): for the circulant
  Hermitian family the exact query number is `q_circ = n`; for the bright-mode family
  `X = x₀ I + x₁ |b⟩⟨b|` with `n ≥ 2` the exact query number on `H^{≤2}` is `q_bright = 2`
  (with `c = (4, 2)`), and on the exactly-two-excitation sector it is `1`.

The physical model (bosonic Fock space, symmetric powers and the Fourier diagonalisation of
circulant matrices) is not formalised; the statements below are made through the sumset
criterion of `SpectralSumset.Basic` (`kappa`), where the character sets `Λ_circ`, `Λ_bright`,
`Λ₂` of Eqs. (S117)–(S119) are supplied by their membership characterisations.
-/

open scoped BigOperators

namespace Qatlib.Papers.HamInversion26.SpinInversion.Physics

noncomputable section

open Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset

attribute [local instance] Classical.propDecidable

/-- The dimension of the `r`-photon symmetric sector of an `n`-mode passive link
(`Sym^r ℂ^n`), Eq. (S108) region, page S22: `C(n + r − 1, r)`. -/
def symDim (n r : ℕ) : ℕ := Nat.choose (n + r - 1) r

/-- **Proposition S22** (Supplement, page S22, Eqs. (S108)–(S110)), sector bookkeeping:
assuming each symmetric sector has query cost at most `quniv n` and the vacuum has zero
cost, the completion expression over the `N + 1` sectors is at most `N * (quniv n + 1)`.
Here `n` counts modes and `N` bounds the photon number. -/
theorem propositionS22_passive_sector_bound (N n : ℕ) (hn : 1 ≤ n) (quniv : ℕ → ℕ)
    (hvac : quniv 1 = 0)
    (hmono : ∀ r ∈ Finset.range (N + 1), quniv (symDim n r) ≤ quniv n) :
    (∑ r ∈ Finset.range (N + 1), (quniv (symDim n r) + 1)) - 1 ≤ N * (quniv n + 1) := by
  have hzero : symDim n 0 = 1 := by
    cases n with
    | zero => omega
    | succ n => simp [symDim]
  rw [Finset.sum_range_succ', hzero, hvac]
  simp only [Nat.zero_add, Nat.add_sub_cancel]
  calc
    (∑ r ∈ Finset.range N, (quniv (symDim n (r + 1)) + 1)) ≤
        ∑ _r ∈ Finset.range N, (quniv n + 1) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Nat.add_le_add_right
      exact hmono (r + 1) (by simp only [Finset.mem_range] at hr ⊢; omega)
    _ = N * (quniv n + 1) := by simp

/-- **Corollary 3** (Letter, page 4), numerical bound: the expression `N * (n² + 1)`
is bounded by `N * (n + 1)²` for a positive number of modes. -/
theorem corollary3_passive_link_query (N n : ℕ) (hn : 1 ≤ n) :
    N * (n * n + 1) ≤ N * ((n + 1) * (n + 1)) := by
  refine Nat.mul_le_mul_left N ?_
  nlinarith [hn]

/-- The character set `Λ₂ = {(2,0), (2,1), (2,2)}` of the exactly-two-excitation sector,
Eq. (S119), page S24. -/
def twoExcitationSet : Finset (ℤ × ℤ) := {(2, 0), (2, 1), (2, 2)}

/-- A vector belongs to `Σ_1(Λ₂)` exactly when it lies in `Λ₂`
(Eq. (S118) with `q = 1`). -/
theorem sumOf_one_twoExcitationSet {s : ℤ × ℤ} :
    SumOf 1 twoExcitationSet s ↔ s ∈ twoExcitationSet := by
  constructor
  · rintro ⟨m, hm, hmem, hs⟩
    obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hm
    simp only [Multiset.mem_singleton] at hmem
    rw [← hs]
    simp [hmem]
  · intro hs
    exact ⟨{s}, rfl, by simpa using hs, by simp⟩

/-- **Proposition S23, exactly-two-excitation sector** (Supplement, page S24, Eq. (S119)):
on `Λ₂ = {(2,0), (2,1), (2,2)}` a single query suffices (the choice `c = (4,2)` satisfies
`c − Λ₂ = Λ₂`), while zero queries cannot distinguish three distinct characters; hence the
exact query number is `κ(Λ₂) = 1`. -/
theorem propositionS23_two_excitation :
    Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset.kappa
        twoExcitationSet = 1 := by
  have hne : twoExcitationSet.Nonempty := ⟨(2, 0), by decide⟩
  have hcard : twoExcitationSet.card = 3 := by decide
  refine le_antisymm ?_ ?_
  · refine kappa_le (q := 1) ?_
    refine ⟨(4, 2), ?_⟩
    intro a ha
    rw [sumOf_one_twoExcitationSet]
    simp only [twoExcitationSet, Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    rcases ha with rfl | rfl | rfl <;> decide
  · by_contra hlt
    have h0 : Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset.kappa
        twoExcitationSet = 0 := by omega
    rw [kappa_eq_zero_iff hne, hcard] at h0
    omega

/-- **Proposition S23, bright-mode family** (Supplement, pages S24–S25, Eq. (S115)–(S119)):
for `n ≥ 2` and `X = x₀ I + x₁ |b⟩⟨b|`, the character pairs on `H^{≤2}` are
`Λ_bright = {(0,0), (1,0), (1,1), (2,0), (2,1), (2,2)}` (Eq. (S119)); the choice `c = (4,2)`
gives two queries and one query is impossible, so the exact query number is `κ = 2`. -/
theorem propositionS23_bright (Λ : Finset (ℤ × ℤ))
    (hΛ : ∀ m : ℤ × ℤ, m ∈ Λ ↔
      m = (0, 0) ∨ m = (1, 0) ∨ m = (1, 1) ∨
        m = (2, 0) ∨ m = (2, 1) ∨ m = (2, 2)) :
    Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset.kappa Λ = 2 := by
  have h00 : (0, 0) ∈ Λ := (hΛ _).mpr (by simp)
  have h10 : (1, 0) ∈ Λ := (hΛ _).mpr (by simp)
  have h20 : (2, 0) ∈ Λ := (hΛ _).mpr (by simp)
  have h21 : (2, 1) ∈ Λ := (hΛ _).mpr (by simp)
  have h22 : (2, 2) ∈ Λ := (hΛ _).mpr (by simp)
  have hadd (a b : ℤ × ℤ) (ha : a ∈ Λ) (hb : b ∈ Λ) : SumOf 2 Λ (a + b) :=
    sumOf_succ b hb ⟨{a}, rfl, by simpa using ha, by simp⟩
  have hone {s : ℤ × ℤ} : SumOf 1 Λ s → s ∈ Λ := by
    rintro ⟨m, hm, hmem, hs⟩
    obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hm
    have hsa : a = s := by simpa using hs
    exact hsa ▸ hmem a (by simp)
  refine le_antisymm (kappa_le (q := 2) ⟨(4, 2), ?_⟩) ?_
  · intro a ha
    rcases (hΛ a).mp ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hadd (2, 0) (2, 2) h20 h22
    · exact hadd (1, 0) (2, 2) h10 h22
    · exact hadd (1, 0) (2, 1) h10 h21
    · exact hadd (0, 0) (2, 2) h00 h22
    · exact hadd (0, 0) (2, 1) h00 h21
    · exact hadd (0, 0) (2, 0) h00 h20
  · obtain ⟨c, hc⟩ := kappa_spec (Λ := Λ)
    by_contra hlt
    have hq : kappa Λ = 0 ∨ kappa Λ = 1 := by omega
    rcases hq with hq | hq
    · have hz := sumOf_zero_iff.mp (hq ▸ hc _ h00)
      have ht := sumOf_zero_iff.mp (hq ▸ hc _ h20)
      have hz' := congrArg Prod.fst hz
      have ht' := congrArg Prod.fst ht
      change c.1 - 0 = 0 at hz'
      change c.1 - 2 = 0 at ht'
      omega
    · have hz := (hΛ _).mp (hone (hq ▸ hc _ h00))
      have ht := (hΛ _).mp (hone (hq ▸ hc _ h22))
      have hu := (hΛ _).mp (hone (hq ▸ hc _ h20))
      simp only [Prod.ext_iff] at hz ht hu
      dsimp at hz ht hu
      omega

/-- A sum of `q` nonnegative occupation vectors of total occupation at most two has
nonnegative coordinates and total occupation at most `2q`. -/
private theorem sumOf_bounds (n : ℕ) (Λ : Finset (Fin n → ℤ))
    (hΛ : ∀ m : Fin n → ℤ, m ∈ Λ ↔ (∀ i, 0 ≤ m i) ∧ ∑ i, m i ≤ 2)
    {q : ℕ} {s : Fin n → ℤ} (hs : SumOf q Λ s) :
    (∀ i, 0 ≤ s i) ∧ ∑ i, s i ≤ 2 * (q : ℤ) := by
  obtain ⟨m, hm, hmem, rfl⟩ := hs
  subst q
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
    have ha := (hΛ a).mp (hmem a (by simp))
    have ht := ih (fun x hx => hmem x (Multiset.mem_cons_of_mem hx))
    constructor
    · intro i
      simpa using add_nonneg (ha.1 i) (ht.1 i)
    · simpa only [Multiset.sum_cons, Pi.add_apply, Finset.sum_add_distrib,
        Multiset.card_cons, Nat.cast_add, Nat.cast_one] using
        (by linarith [ha.2, ht.2] : (∑ i, a i) + ∑ i, m.sum i ≤
          2 * ((m.card : ℤ) + 1))

/-- **Proposition S23, circulant family** (Supplement, page S24, Eqs. (S115)–(S118)): for a
Hermitian circulant matrix the fixed occupation basis diagonalises the family, with character
set `Λ_circ = {m ∈ ℤ^n : m_i ≥ 0, ‖m‖₁ ≤ 2}` (Eq. (S117)); the exact query number is
`κ(Λ_circ) = n`. -/
theorem propositionS23_circulant (n : ℕ) (hn : 1 ≤ n) (Λ : Finset (Fin n → ℤ))
    (hΛ : ∀ m : Fin n → ℤ, m ∈ Λ ↔ (∀ i, 0 ≤ m i) ∧ ∑ i, m i ≤ 2) :
    Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset.kappa Λ = n := by
  rcases Nat.eq_zero_or_pos n with hzero | _
  · omega
  have hsingle (i : Fin n) (z : ℤ) (hz : 0 ≤ z) (hz2 : z ≤ 2) :
      Pi.single i z ∈ Λ := by
    apply (hΛ _).mpr
    constructor
    · intro j
      by_cases hij : i = j
      · subst j; simpa using hz
      · simp [Pi.single_eq_of_ne (Ne.symm hij)]
    · simpa using hz2
  refine le_antisymm (kappa_le (q := n) ⟨fun _ => 2, ?_⟩) ?_
  · intro a ha
    obtain ⟨ha0, ha2⟩ := (hΛ a).mp ha
    have hai (i : Fin n) : a i ≤ 2 :=
      le_trans (Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ i)) ha2
    refine ⟨Finset.univ.val.map (fun i : Fin n => Pi.single i (2 - a i)), ?_, ?_, ?_⟩
    · simp
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
      exact hsingle i (2 - a i) (by linarith [hai i]) (by linarith [ha0 i])
    · rw [Finset.sum_map_val]
      funext i
      simp [Finset.sum_apply, Finset.sum_pi_single]
  · obtain ⟨c, hc⟩ := kappa_spec (Λ := Λ)
    have hzero : (0 : Fin n → ℤ) ∈ Λ := (hΛ _).mpr (by simp)
    have htotal := (sumOf_bounds n Λ hΛ (hc 0 hzero)).2
    have hci (i : Fin n) : (2 : ℤ) ≤ c i := by
      have hnonneg := (sumOf_bounds n Λ hΛ (hc _ (hsingle i 2 (by decide)
        (by decide)))).1 i
      simpa using hnonneg
    have hsum : 2 * (n : ℤ) ≤ ∑ i, c i := by
      simpa [mul_comm] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hci i)
    have hbound : (n : ℤ) ≤ kappa Λ := by
      simp only [sub_zero] at htotal
      linarith
    exact_mod_cast hbound

end

end Qatlib.Papers.HamInversion26.SpinInversion.Physics
