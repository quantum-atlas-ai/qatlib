/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemGates95.BorrowedAnd.Section7.BorrowedNetworks

/-!
# Explicit four-block controlled NOT construction

This module instantiates the four-block composition of Lemma 7.3 in [BarencoEtAl1995] with
actual legal elementary-gate lists. `noWorkPrefixAnd_add` and `noWorkPrefixAnd_head` split the
control conjunction so that the two programs supplied to `lemma7_3_composition` have the
required predicates.

For `n >= 5` and `2 <= m <= n - 3`, `lemma7_3_actual` constructs programs with `m` and `n - m -
1` controls in an ambient register satisfying the stated distinctness assumptions. Their
four-block concatenation toggles the target by all `n - 2` listed controls, restores the
borrowed wire, and comes with explicit elementary-gate bounds and query-count information.

## Main statements

* `noWorkPrefixAnd_add` separates a conjunction into consecutive segments.
* `noWorkPrefixAnd_head` separates a distinguished first control.
* `lemma7_3_actual` constructs the two legal programs and proves the semantics and accounting of
  their four-block concatenation.

## References

* [Barenco et al., 1995][BarencoEtAl1995], Section 7, Lemma 7.3.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Papers.ElemGates95.BorrowedAnd.Section7

/-- The conjunction of the first `m + k` Boolean values is the conjunction of the first `m`
values and the following `k` values. -/
theorem noWorkPrefixAnd_add (c : ℕ → Bool) (m k : ℕ) :
    noWorkPrefixAnd c (m + k) =
      (noWorkPrefixAnd c m && noWorkPrefixAnd (fun i => c (m + i)) k) := by
  induction k with
  | zero => simp [noWorkPrefixAnd]
  | succ k ih =>
    have h1 : noWorkPrefixAnd c (m + (k + 1)) =
        (noWorkPrefixAnd c (m + k) && c (m + k)) := by
      rw [show m + (k + 1) = (m + k) + 1 by omega, noWorkPrefixAnd_succ]
    have h2 : noWorkPrefixAnd (fun i => c (m + i)) (k + 1) =
        (noWorkPrefixAnd (fun i => c (m + i)) k && c (m + k)) := by
      simpa using! noWorkPrefixAnd_succ (fun i => c (m + i)) k
    rw [h1, ih, h2]
    exact Bool.and_assoc _ _ _

/-- The conjunction of a distinguished head wire followed by `k` control wires equals the head
value conjoined with the conjunction of those `k` controls. -/
theorem noWorkPrefixAnd_head {N : ℕ} (h : Fin N) (c : ℕ → Fin N) (x : Reg N) (k : ℕ) :
    noWorkPrefixAnd (fun i => x (if i = 0 then h else c (i - 1))) (k + 1) =
      (x h && noWorkPrefixAnd (fun i => x (c i)) k) := by
  induction k with
  | zero => simp [noWorkPrefixAnd]
  | succ k ih =>
    have h1 : noWorkPrefixAnd (fun i => x (if i = 0 then h else c (i - 1)))
        ((k + 1) + 1) =
        (noWorkPrefixAnd (fun i => x (if i = 0 then h else c (i - 1))) (k + 1) &&
          x (c k)) := by
      rw [noWorkPrefixAnd_succ]
      simp
    rw [show (k + 1) + 1 = k + 1 + 1 by omega, h1, ih]
    rw [noWorkPrefixAnd_succ]
    exact Bool.and_assoc _ _ _

/-- For `n >= 5`, `2 <= m <= n - 3`, and the stated distinct wire layout, constructs legal
programs with `m` and `n - m - 1` controls whose four-block concatenation toggles the target
by all `n - 2` controls and restores every other wire. This concrete form of Lemma 7.3 in
[BarencoEtAl1995] includes the displayed bounds for the two program lengths, zero queries,
and equality of compiled gate count with list length. -/
theorem lemma7_3_actual {N n m : ℕ} (c : ℕ → Fin N) (s t : Fin N)
    (hn : 5 ≤ n) (hm2 : 2 ≤ m) (hm : m ≤ n - 3)
    (hc : Set.InjOn c (Set.Iio (n - 2)))
    (hcs : ∀ i < n - 2, c i ≠ s) (hct : ∀ i < n - 2, c i ≠ t)
    (hst : s ≠ t) :
    ∃ as bs : List (ReflectionGate N),
      reflectionLegal as ∧ reflectionLegal bs ∧
      as.length ≤ 120 * (m + 1) + 4 ∧
      bs.length ≤ 120 * ((n - m - 1) + 1) + 4 ∧
      reflectionLegal (as ++ bs ++ as ++ bs) ∧
      (as ++ bs ++ as ++ bs).length = 2 * as.length + 2 * bs.length ∧
      QueryCount (reflectionCompile (as ++ bs ++ as ++ bs)) = 0 ∧
      GateCount (reflectionCompile (as ++ bs ++ as ++ bs)) = (as ++ bs ++ as ++ bs).length ∧
      ∀ x : Reg N, Run (1 : Matrix (Reg N) (Reg N) ℂ)
        (reflectionCompile (as ++ bs ++ as ++ bs))
        (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket
          (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) (n - 2))) := by

  have hcA : Set.InjOn c (Set.Iio m) := by
    intro i hi j hj he
    exact hc (show i < n - 2 from by change i < m at hi; omega)
      (show j < n - 2 from by change j < m at hj; omega) he
  have hctA : ∀ i < m, c i ≠ t := fun i hi => hct i (by omega)
  have hcsA : ∀ i < m, c i ≠ s := fun i hi => hcs i (by omega)
  obtain ⟨as, has, haslen, hasrun⟩ :=
    noWork_single_dirty_and_table c t s m hcA hctA hcsA hst.symm

  let cb : ℕ → Fin N := fun i => if i = 0 then s else c (m + (i - 1))
  have hcb_inj : Set.InjOn cb (Set.Iio (n - m - 1)) := by
    intro i hi j hj he
    change i < n - m - 1 at hi
    change j < n - m - 1 at hj
    by_cases hi0 : i = 0
    · subst hi0
      have hc0 : cb 0 = s := by simp [cb]
      rw [hc0] at he
      by_cases hj0 : j = 0
      · exact hj0.symm
      · have hval : cb j = c (m + (j - 1)) := by simp [cb, hj0]
        rw [hval] at he
        exact absurd he.symm (hcs (m + (j - 1)) (by omega))
    · by_cases hj0 : j = 0
      · subst hj0
        have hc0 : cb 0 = s := by simp [cb]
        rw [hc0] at he
        have hval : cb i = c (m + (i - 1)) := by simp [cb, hi0]
        rw [hval] at he
        exact absurd he (hcs (m + (i - 1)) (by omega))
      · have hvi : cb i = c (m + (i - 1)) := by simp [cb, hi0]
        have hvj : cb j = c (m + (j - 1)) := by simp [cb, hj0]
        rw [hvi, hvj] at he
        have hii : m + (i - 1) < n - 2 := by omega
        have hjj : m + (j - 1) < n - 2 := by omega
        have := hc hii hjj he
        omega
  have hcb_t : ∀ i < n - m - 1, cb i ≠ t := by
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0; simp [cb]; exact hst
    · have hval : cb i = c (m + (i - 1)) := by simp [cb, hi0]
      rw [hval]
      exact hct (m + (i - 1)) (by omega)
  have hborrow_s : c 0 ≠ s := hcs 0 (by omega)
  have hborrow : ∀ i < n - m - 1, cb i ≠ c 0 := by
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      simpa [cb] using! hborrow_s.symm
    · have hval : cb i = c (m + (i - 1)) := by simp [cb, hi0]
      rw [hval]
      intro he
      have hidx := hc (show m + (i - 1) < n - 2 by omega)
        (show 0 < n - 2 by omega) he
      omega
  obtain ⟨bs, hbs, hbslen, hbsrun⟩ :=
    noWork_single_dirty_and_table cb (c 0) t (n - m - 1) hcb_inj hborrow hcb_t
      (hct 0 (by omega))

  let A : Reg N → Bool := fun x => noWorkPrefixAnd (fun i => x (c i)) m
  let B : Reg N → Bool := fun x => noWorkPrefixAnd (fun i => x (c (m + i))) (n - 2 - m)
  have hA : ∀ (x : Reg N) (v : Bool), A (Function.update x s v) = A x ∧
      A (Function.update x t v) = A x := by
    intro x v
    constructor
    · apply Bool.eq_iff_iff.mpr
      simp only [A, noWorkPrefixAnd, List.all_eq_true, List.mem_range]
      exact ⟨fun hh i hi => by simpa [Function.update_of_ne (hcs i (by omega))] using! hh i hi,
        fun hh i hi => by simpa [Function.update_of_ne (hcs i (by omega))] using! hh i hi⟩
    · apply Bool.eq_iff_iff.mpr
      simp only [A, noWorkPrefixAnd, List.all_eq_true, List.mem_range]
      exact ⟨fun hh i hi => by simpa [Function.update_of_ne (hct i (by omega))] using! hh i hi,
        fun hh i hi => by simpa [Function.update_of_ne (hct i (by omega))] using! hh i hi⟩
  have hB : ∀ (x : Reg N) (v : Bool), B (Function.update x s v) = B x ∧
      B (Function.update x t v) = B x := by
    intro x v
    constructor
    · apply Bool.eq_iff_iff.mpr
      simp only [B, noWorkPrefixAnd, List.all_eq_true, List.mem_range]
      exact ⟨fun hh i hi => by simpa [Function.update_of_ne (hcs (m + i) (by omega))] using! hh i hi,
        fun hh i hi => by simpa [Function.update_of_ne (hcs (m + i) (by omega))] using! hh i hi⟩
    · apply Bool.eq_iff_iff.mpr
      simp only [B, noWorkPrefixAnd, List.all_eq_true, List.mem_range]
      exact ⟨fun hh i hi => by simpa [Function.update_of_ne (hct (m + i) (by omega))] using! hh i hi,
        fun hh i hi => by simpa [Function.update_of_ne (hct (m + i) (by omega))] using! hh i hi⟩

  have hBs : ∀ x : Reg N,
      noWorkPrefixAnd (fun i => x (cb i)) (n - m - 1) = (B x && x s) := by
    intro x
    have hshape : n - m - 1 = (n - 2 - m) + 1 := by omega
    rw [hshape, noWorkPrefixAnd_head s (fun i => c (m + i)) x (n - 2 - m)]
    exact Bool.and_comm _ _
  have hbsrun' : ∀ x : Reg N, Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile bs) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket
        (Function.update x t (x t ^^ (B x && x s))) := by
    intro x
    rw [hbsrun x, hBs x]
  obtain ⟨hlegal, hlen, hsem⟩ :=
    lemma7_3_composition s t hst A B hA hB as bs has hbs hasrun hbsrun'
  refine ⟨as, bs, has, hbs, haslen, hbslen, hlegal, hlen,
    queryCount_reflectionCompile _, gateCount_reflectionCompile _, ?_⟩
  intro x
  rw [hsem x]
  have hsplit : noWorkPrefixAnd (fun i => x (c i)) (n - 2) = (A x && B x) := by
    have h := noWorkPrefixAnd_add (fun i => x (c i)) m (n - 2 - m)
    rw [show m + (n - 2 - m) = n - 2 by omega] at h
    rw [h]
  rw [hsplit]

end Qatlib.Papers.ElemGates95.BorrowedAnd.Section7
