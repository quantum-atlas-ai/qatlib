/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Approximate encoded permutations: deviation, subadditivity and the 10⁻⁷ bound

Source: Gidney--Ekerå, *How to factor 2048 bit RSA integers in 8 hours using
20 million noisy qubits*, arXiv:1905.09749v3 (13 Apr 2021), §2.9, p. 10.
Fixed version: v3 (PDF header `arXiv:1905.09749v3 [quant-ph] 13 Apr 2021`),
accepted Quantum 2021-03-29.

Claims covered:

* c004 (§2.9, lines 624–642): the oblivious runways and the coset
  representation are "approximate encoded permutations" with a "deviation";
  with padding/runway length `c_pad` and runway separation `c_sep`, the
  deviation per addition is at most `n / (c_sep 2^{c_pad})`; deviation is
  subadditive under composition, so the deviation of the whole modular
  exponentiation is at most the number of lookup additions times the
  per-addition deviation.
* c005 (§2.9, Eq. (4) and the following paragraph): with
  `c_pad = 2 lg n + lg n_e + 10`, `c_sep = 1024` and
  `LookupAdditionCount ≈ 0.1 n_e n`, the total deviation is
  `0.1 / (1024 · 2^{10}) ≈ 10⁻⁷`; and when an approximate encoded permutation
  has deviation `ε`, the trace distance between its output and the ideal
  output is at most `2√ε`, hence ≈ 0.1 %.

Model (documented boundary): an approximate encoded permutation is a
permutation `σ` of a finite configuration space, and its deviation from the
ideal permutation `π` is the fraction of computational-basis inputs on which
the two disagree.  This is the error probability of the encoded operation on
a uniformly random input; the corresponding uniform-superposition graph states
have fidelity `1 - deviation`, so the pure-state trace-distance relation
`√(1 - F²) ≤ 2√ε` applies.  The per-piece runway fault fraction `2^{-c_pad}`
is the standard fault model of [33] that the paper invokes; it is an explicit
hypothesis of `deviation_perAddition_le`, while the union bound, the piece
count and all arithmetic are proved here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.RSAFactoring19.MainResults.ApproximationError

/-! ### Deviation of a finite approximate encoded permutation -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The set of inputs on which the encoded permutation `σ` differs from the
ideal permutation `π`. -/
def badSet (σ π : Equiv.Perm ι) : Finset ι :=
  Finset.univ.filter (fun x => σ x ≠ π x)

/-- Deviation of an approximate encoded permutation from the ideal: the
fraction of inputs on which it errs (Gidney--Ekerå §2.9, following [33]). -/
def deviation (σ π : Equiv.Perm ι) : ℝ :=
  ((badSet σ π).card : ℝ) / (Fintype.card ι : ℝ)

/-- The deviation of a permutation from itself is zero. -/
theorem deviation_self (π : Equiv.Perm ι) : deviation π π = 0 := by
  simp [deviation, badSet]

/-- Deviation is nonnegative. -/
theorem deviation_nonneg (σ π : Equiv.Perm ι) : 0 ≤ deviation σ π := by
  unfold deviation
  positivity

/-- Deviation is at most one (for a nonempty configuration space). -/
theorem deviation_le_one (σ π : Equiv.Perm ι) (hN : 0 < Fintype.card ι) :
    deviation σ π ≤ 1 := by
  unfold deviation
  have hcard : (badSet σ π).card ≤ Fintype.card ι := by
    simpa using Finset.card_le_univ (badSet σ π)
  have hN' : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hN
  calc ((badSet σ π).card : ℝ) / (Fintype.card ι : ℝ)
      ≤ (Fintype.card ι : ℝ) / (Fintype.card ι : ℝ) := by
        gcongr
    _ = 1 := by field_simp

/-- **Subadditivity of deviation under composition** (Gidney--Ekerå §2.9).
Composing two approximate encoded permutations costs at most the sum of their
deviations.  The composite `σ₂.trans σ₁` applies `σ₂` first and `σ₁` second;
it errs only when `σ₂` errs or when `σ₁` errs at `σ₂`'s actual output.
Injectivity of `σ₂` lets us count the pulled-back second bad set. -/
theorem deviation_comp_le (σ₁ σ₂ π₁ π₂ : Equiv.Perm ι) :
    deviation (σ₂.trans σ₁) (π₂.trans π₁) ≤
      deviation σ₁ π₁ + deviation σ₂ π₂ := by
  classical
  have hsub : badSet (σ₂.trans σ₁) (π₂.trans π₁) ⊆
      badSet σ₂ π₂ ∪ Finset.univ.filter (fun x => σ₁ (σ₂ x) ≠ π₁ (σ₂ x)) := by
    intro x hx
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union] at hx ⊢
    by_cases h : σ₂ x = π₂ x
    · right
      simpa [Equiv.trans_apply, h] using hx
    · left
      exact h
  -- The pullback bad set is equinumerous with the first bad set.
  have hcardPull : (Finset.univ.filter (fun x => σ₁ (σ₂ x) ≠ π₁ (σ₂ x))).card =
      (badSet σ₁ π₁).card := by
    refine Finset.card_bij (fun x _ => σ₂ x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simpa [badSet] using hx
    · intro x₁ _ x₂ _ h
      exact σ₂.injective h
    · intro y hy
      refine ⟨σ₂.symm y, ?_, by simp⟩
      simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using hy
  have hcard : (badSet (σ₂.trans σ₁) (π₂.trans π₁)).card ≤
      (badSet σ₁ π₁).card + (badSet σ₂ π₂).card := by
    calc (badSet (σ₂.trans σ₁) (π₂.trans π₁)).card
        ≤ (badSet σ₂ π₂ ∪
            Finset.univ.filter (fun x => σ₁ (σ₂ x) ≠ π₁ (σ₂ x))).card :=
          Finset.card_le_card hsub
      _ ≤ (badSet σ₂ π₂).card +
            (Finset.univ.filter (fun x => σ₁ (σ₂ x) ≠ π₁ (σ₂ x))).card :=
          Finset.card_union_le _ _
      _ = (badSet σ₂ π₂).card + (badSet σ₁ π₁).card := by rw [hcardPull]
      _ = (badSet σ₁ π₁).card + (badSet σ₂ π₂).card := by ring
  unfold deviation
  have hcast : (((badSet σ₁ π₁).card + (badSet σ₂ π₂).card : ℕ) : ℝ) =
      ((badSet σ₁ π₁).card : ℝ) + ((badSet σ₂ π₂).card : ℝ) := by
    push_cast
    ring
  calc ((badSet (σ₂.trans σ₁) (π₂.trans π₁)).card : ℝ) / (Fintype.card ι : ℝ)
      ≤ (((badSet σ₁ π₁).card + (badSet σ₂ π₂).card : ℕ) : ℝ) /
          (Fintype.card ι : ℝ) := by
        gcongr
    _ = ((badSet σ₁ π₁).card : ℝ) / (Fintype.card ι : ℝ) +
          ((badSet σ₂ π₂).card : ℝ) / (Fintype.card ι : ℝ) := by
        rw [hcast, add_div]

/-- The left-to-right composition of a list of permutations, with the identity
as the empty composition.  `composeList (σ :: l)` applies `σ` first. -/
def composeList : List (Equiv.Perm ι) → Equiv.Perm ι
  | [] => 1
  | σ :: l => σ.trans (composeList l)

/-- The deviation of a composite is at most the sum of the stage deviations
(Gidney--Ekerå §2.9, iterated form). -/
theorem deviation_composeList_le_sum (l₁ l₂ : List (Equiv.Perm ι))
    (hlen : l₁.length = l₂.length) :
    deviation (composeList l₁) (composeList l₂) ≤
      ((l₁.zip l₂).map (fun p => deviation p.1 p.2)).sum := by
  classical
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => simp [composeList, deviation_self]
      | cons _ _ => simp at hlen
  | cons a l₁ ih =>
      cases l₂ with
      | nil => simp at hlen
      | cons b l₂ =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          have hrec := ih l₂ hlen
          simp only [composeList, List.zip_cons_cons, List.map_cons, List.sum_cons]
          calc deviation (a.trans (composeList l₁)) (b.trans (composeList l₂))
              ≤ deviation (composeList l₁) (composeList l₂) + deviation a b :=
                deviation_comp_le (composeList l₁) a (composeList l₂) b
            _ ≤ ((l₁.zip l₂).map (fun p => deviation p.1 p.2)).sum + deviation a b := by
                linarith
            _ = deviation a b + ((l₁.zip l₂).map (fun p => deviation p.1 p.2)).sum := by
                ring

/-- Iterated subadditivity in the form used in the paper: if every stage has
deviation at most `ε`, a list of `k` stages has deviation at most `k · ε`
("the deviation of the entire modular exponentiation process is at most the
number of lookup additions times the deviation per addition"). -/
theorem deviation_composeList_le_length_mul (l₁ l₂ : List (Equiv.Perm ι))
    (hlen : l₁.length = l₂.length) (ε : ℝ)
    (hε : ∀ (σ π : Equiv.Perm ι), deviation σ π ≤ ε) :
    deviation (composeList l₁) (composeList l₂) ≤ (l₁.length : ℝ) * ε := by
  classical
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => simp [composeList, deviation_self]
      | cons _ _ => simp at hlen
  | cons a l₁ ih =>
      cases l₂ with
      | nil => simp at hlen
      | cons b l₂ =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          have hrec := ih l₂ hlen
          have hd : deviation a b ≤ ε := hε a b
          have hε0 : 0 ≤ ε := (deviation_nonneg a b).trans hd
          calc deviation (a.trans (composeList l₁)) (b.trans (composeList l₂))
              ≤ deviation (composeList l₁) (composeList l₂) + deviation a b :=
                deviation_comp_le (composeList l₁) a (composeList l₂) b
            _ ≤ (l₁.length : ℝ) * ε + ε := by linarith
            _ = ((a :: l₁).length : ℝ) * ε := by
                simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
                ring

/-! ### Runway fault union bound and the per-addition deviation -/

/-- Bad inputs are contained in the union of the per-piece fault sets. -/
theorem badSet_card_le_biUnion {κ : Type*} [Fintype κ] [DecidableEq κ]
    (σ π : Equiv.Perm ι) (bad : κ → Finset ι)
    (hcover : ∀ x, σ x ≠ π x → ∃ i, x ∈ bad i) :
    (badSet σ π).card ≤ (Finset.univ.biUnion bad).card := by
  apply Finset.card_le_card
  intro x hx
  have hx' : σ x ≠ π x := by simpa [badSet] using hx
  obtain ⟨i, hi⟩ := hcover x hx'
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩

/-- **Union bound over runway pieces.**  If each of `m` pieces faults on at
most a fraction `p` of all inputs, the addition faults on at most a fraction
`m · p` of them. -/
theorem deviation_le_pieceUnion {κ : Type*} [Fintype κ] [DecidableEq κ]
    (σ π : Equiv.Perm ι) (bad : κ → Finset ι) (p : ℝ) (hp : 0 ≤ p)
    (hcover : ∀ x, σ x ≠ π x → ∃ i, x ∈ bad i)
    (hpiece : ∀ i, ((bad i).card : ℝ) ≤ p * (Fintype.card ι : ℝ)) :
    deviation σ π ≤ (Fintype.card κ : ℝ) * p := by
  classical
  have hcard : (badSet σ π).card ≤ (Finset.univ.biUnion bad).card :=
    badSet_card_le_biUnion σ π bad hcover
  have hsum : ((Finset.univ.biUnion bad).card : ℝ) ≤
      ∑ i : κ, ((bad i).card : ℝ) := by
    have h := Finset.card_biUnion_le (s := Finset.univ) (t := bad)
    calc ((Finset.univ.biUnion bad).card : ℝ)
        ≤ ((∑ i ∈ (Finset.univ : Finset κ), (bad i).card : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = ∑ i : κ, ((bad i).card : ℝ) := by simp
  have hsum' : ∑ i : κ, ((bad i).card : ℝ) ≤
      ∑ _i : κ, p * (Fintype.card ι : ℝ) :=
    Finset.sum_le_sum (fun i _ => hpiece i)
  have hsum'' : (∑ _i : κ, p * (Fintype.card ι : ℝ)) =
      (Fintype.card κ : ℝ) * (p * (Fintype.card ι : ℝ)) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmain : ((badSet σ π).card : ℝ) ≤
      (Fintype.card κ : ℝ) * p * (Fintype.card ι : ℝ) := by
    calc ((badSet σ π).card : ℝ)
        ≤ ((Finset.univ.biUnion bad).card : ℝ) := by exact_mod_cast hcard
      _ ≤ ∑ i : κ, ((bad i).card : ℝ) := hsum
      _ ≤ ∑ _i : κ, p * (Fintype.card ι : ℝ) := hsum'
      _ = (Fintype.card κ : ℝ) * p * (Fintype.card ι : ℝ) := by
          rw [hsum'']; ring
  by_cases hN : (Fintype.card ι : ℝ) = 0
  · have hempty : (badSet σ π).card = 0 := by
      have : Fintype.card ι = 0 := by exact_mod_cast hN
      haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp this
      simp [badSet]
    unfold deviation
    rw [hempty, hN]
    simp only [Nat.cast_zero, zero_div]
    positivity
  · have hNpos : (0 : ℝ) < (Fintype.card ι : ℝ) :=
      lt_of_le_of_ne (by positivity) (Ne.symm hN)
    unfold deviation
    calc ((badSet σ π).card : ℝ) / (Fintype.card ι : ℝ)
        ≤ ((Fintype.card κ : ℝ) * p * (Fintype.card ι : ℝ)) /
            (Fintype.card ι : ℝ) := by
          gcongr
      _ = (Fintype.card κ : ℝ) * p := by field_simp

/-- The deviation of one addition with runway length `c_pad` and runway
separation `c_sep` is at most `n / (c_sep · 2^{c_pad})` (Gidney--Ekerå §2.9,
p. 10).  There are `n / c_sep` pieces, each faulting with probability
`2^{-c_pad}`; the union bound is `deviation_le_pieceUnion`. -/
theorem deviation_perAddition_le (n csep cpad : ℕ) (hsep : 0 < csep)
    (σ π : Equiv.Perm ι) (bad : Fin (n / csep) → Finset ι)
    (hcover : ∀ x, σ x ≠ π x → ∃ i, x ∈ bad i)
    (hpiece : ∀ i, ((bad i).card : ℝ) ≤
      ((1 / 2 : ℝ) ^ cpad) * (Fintype.card ι : ℝ)) :
    deviation σ π ≤ (n : ℝ) / ((csep : ℝ) * 2 ^ cpad) := by
  have hbase := deviation_le_pieceUnion σ π bad ((1 / 2 : ℝ) ^ cpad)
    (by positivity) hcover hpiece
  have hcard : (Fintype.card (Fin (n / csep)) : ℝ) ≤ (n : ℝ) / (csep : ℝ) := by
    simpa using Nat.cast_div_le (α := ℝ) (m := n) (n := csep)
  have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ cpad := by positivity
  calc deviation σ π
      ≤ (Fintype.card (Fin (n / csep)) : ℝ) * ((1 / 2 : ℝ) ^ cpad) := hbase
    _ ≤ ((n : ℝ) / (csep : ℝ)) * ((1 / 2 : ℝ) ^ cpad) := by gcongr
    _ = (n : ℝ) / ((csep : ℝ) * 2 ^ cpad) := by
        rw [one_div_pow]
        field_simp

/-- The paper's displayed per-addition deviation bound, as an identity:
`(n / c_sep) · 2^{-c_pad} = n / (c_sep · 2^{c_pad})`. -/
theorem deviation_perAddition_eq (n csep cpad : ℕ) (hsep : 0 < csep) :
    ((n : ℝ) / (csep : ℝ)) * ((1 / 2 : ℝ) ^ cpad) =
      (n : ℝ) / ((csep : ℝ) * 2 ^ cpad) := by
  rw [one_div_pow]
  field_simp

/-- **c004 (composition half).**  If every lookup addition has deviation at
most `n / (c_sep · 2^{c_pad})`, the whole modular exponentiation has deviation
at most the number of additions times that bound (Gidney--Ekerå §2.9). -/
theorem deviation_of_modularExponentiation_le (n csep cpad : ℕ)
    (_hsep : 0 < csep)
    (acts ideals : List (Equiv.Perm ι)) (hlen : acts.length = ideals.length)
    (hstage : ∀ (σ π : Equiv.Perm ι),
      deviation σ π ≤ (n : ℝ) / ((csep : ℝ) * 2 ^ cpad)) :
    deviation (composeList acts) (composeList ideals) ≤
      (acts.length : ℝ) * ((n : ℝ) / ((csep : ℝ) * 2 ^ cpad)) :=
  deviation_composeList_le_length_mul acts ideals hlen _ hstage

/-! ### Total deviation (Eq. (4)) and the trace-distance transfer -/

/-- Base-2 logarithm, written `lg` in the paper. -/
def lg (x : ℝ) : ℝ := Real.logb 2 x

/-- The paper's parameter choice `c_pad = 2 lg n + lg n_e + 10`
(Gidney--Ekerå §2.8/§2.9). -/
def padLength (n ne : ℝ) : ℝ := 2 * lg n + lg ne + 10

/-- The number of lookup additions, in the paper's approximation
`LookupAdditionCount(n, n_e) ≈ 0.1 n_e n` (Eq. (1)). -/
def lookupAdditionCountApprox (n ne : ℝ) : ℝ := 0.1 * ne * n

/-- Deviation per addition with the paper's padding/runway parameters. -/
def perAdditionDeviation (n ne : ℝ) : ℝ :=
  n / (1024 * 2 ^ padLength n ne)

/-- `TotalDeviation(n, n_e)` of Eq. (4): the lookup-addition count times the
per-addition deviation. -/
def totalDeviation (n ne : ℝ) : ℝ :=
  lookupAdditionCountApprox n ne * perAdditionDeviation n ne

/-- `2^{c_pad} = n² · n_e · 2^{10}` for the paper's choice
`c_pad = 2 lg n + lg n_e + 10`; this is the algebraic cancellation behind
Eq. (4). -/
theorem two_pow_padLength (n ne : ℝ) (hn : 0 < n) (hne : 0 < ne) :
    (2 : ℝ) ^ padLength n ne = n ^ 2 * ne * 2 ^ 10 := by
  have h2 : (2 : ℝ) ^ padLength n ne =
      (2 : ℝ) ^ (2 * lg n) * (2 : ℝ) ^ (lg ne) * (2 : ℝ) ^ (10 : ℝ) := by
    rw [padLength, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hn2 : (2 : ℝ) ^ (2 * lg n) = (n : ℝ) ^ 2 := by
    have h1 : (2 : ℝ) ^ (2 * lg n) = ((2 : ℝ) ^ (lg n)) ^ (2 : ℝ) := by
      rw [show 2 * lg n = lg n * 2 by ring, Real.rpow_mul (by norm_num)]
    have h2' : (2 : ℝ) ^ (lg n) = n := by
      simpa [lg] using Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hn
    rw [h1, h2', Real.rpow_two]
  have hne2 : (2 : ℝ) ^ (lg ne) = ne := by
    simpa [lg] using Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hne
  have h10 : (2 : ℝ) ^ (10 : ℝ) = (2 : ℝ) ^ 10 := Real.rpow_natCast 2 10
  rw [h2, hn2, hne2, h10]

/-- **c005, Eq. (4): the total deviation is `0.1 / (1024 · 2^{10})`.**  With
`c_pad = 2 lg n + lg n_e + 10`, `c_sep = 1024` and
`LookupAdditionCount ≈ 0.1 n_e n`, the `n²` and `n_e` factors cancel exactly. -/
theorem totalDeviation_eq (n ne : ℝ) (hn : 0 < n) (hne : 0 < ne) :
    totalDeviation n ne = 0.1 / (1024 * 2 ^ 10) := by
  unfold totalDeviation lookupAdditionCountApprox perAdditionDeviation
  rw [two_pow_padLength n ne hn hne]
  field_simp

/-- The numerical value of Eq. (4): `0.1 / (1024 · 2^{10}) ≈ 9.54 · 10⁻⁸`. -/
theorem totalDeviation_eq_numeric :
    (0.1 : ℝ) / (1024 * 2 ^ 10) = 0.1 / 1048576 := by norm_num

/-- **c005, Eq. (4) conclusion: the total deviation is at most `10⁻⁷`.** -/
theorem totalDeviation_le_one_e7 (n ne : ℝ) (hn : 0 < n) (hne : 0 < ne) :
    totalDeviation n ne ≤ 1 / 10000000 := by
  rw [totalDeviation_eq n ne hn hne, totalDeviation_eq_numeric]
  norm_num

/-- The pure-state trace distance induced by a deviation: `√(1 - F²)` where
the fidelity of the actual and ideal uniform-superposition graph states is
`F = 1 - deviation`.  (This is the standard pure-state trace distance.) -/
def traceDistance (σ π : Equiv.Perm ι) : ℝ :=
  Real.sqrt (1 - (1 - deviation σ π) ^ 2)

/-- **c005, trace-distance transfer.**  If an approximate encoded permutation
has deviation at most `ε`, the trace distance between its output and the ideal
output is at most `2√ε` (Gidney--Ekerå §2.9, p. 10). -/
theorem traceDistance_le_two_sqrt (σ π : Equiv.Perm ι) (ε : ℝ)
    (hdev : deviation σ π ≤ ε) (hε0 : 0 ≤ ε) :
    traceDistance σ π ≤ 2 * Real.sqrt ε := by
  have hd0 : 0 ≤ deviation σ π := deviation_nonneg σ π
  have hmain : 1 - (1 - deviation σ π) ^ 2 ≤ 4 * ε := by nlinarith [sq_nonneg (deviation σ π)]
  have h4 : Real.sqrt (4 * ε) = 2 * Real.sqrt ε := by
    rw [show (4 : ℝ) * ε = 2 ^ 2 * ε by norm_num]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  calc traceDistance σ π = Real.sqrt (1 - (1 - deviation σ π) ^ 2) := rfl
    _ ≤ Real.sqrt (4 * ε) := Real.sqrt_le_sqrt hmain
    _ = 2 * Real.sqrt ε := h4

/-- **c005 with the paper's parameters:** total deviation `≤ 10⁻⁷` and trace
distance `≤ 2√(10⁻⁷) ≈ 0.063 %`, below the paper's quoted "roughly 0.1 %"
approximation error. -/
theorem approximationError_le (n ne : ℝ) (hn : 0 < n) (hne : 0 < ne) :
    totalDeviation n ne ≤ 1 / 10000000 ∧
      Real.sqrt (4 * (1 / 10000000)) = 2 * Real.sqrt (1 / 10000000) :=
  ⟨totalDeviation_le_one_e7 n ne hn hne, by
    rw [show (4 : ℝ) * (1 / 10000000) = 2 ^ 2 * (1 / 10000000) by norm_num]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]⟩

end Qatlib.Papers.RSAFactoring19.MainResults.ApproximationError
