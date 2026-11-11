/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KhovanovHom25.MainResults.Model
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 19: the Laplacian of `TU_n` in bidegree `(0, 3 - n)`

Source: arXiv:2501.12378v2, Proposition 19, p. 38, eq. (6.10).

In homological degree zero the chain space of the twisted unknot `TU_n` is
`V^{⊗(n+1)}`, and the `q`-degree `3 - n` subspace is spanned by the states with
exactly two `1`s, indexed by pairs `{a, b}` with `1 ≤ a < b ≤ n + 1`.  The paper
computes the Laplacian on this basis:

`Δ(0,3-n) {a,b} = (4 - δ_{a,1} - δ_{b,n+1} - δ_{b,a+1}){a,b}
                  + {a-1,b} + {a+1,b} + {a,b-1} + {a,b+1}`     (6.10)

with the convention `{a,b} = 0` if `a < 1`, `b > n+1` or `a = b`.

The operator is formalized on the index set `PairIdx n` of *valid* pairs, so the
paper's "`{a,b} = 0` outside the range" convention is implemented by dropping the
out-of-range neighbouring term.  `proposition19` below is exactly (6.10) read as
an identity of functions on this basis; the companion counting lemma records the
dimension `C(n+1, 2)` asserted in the proposition.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults

/-- The pair basis of Prop. 19: the pairs `{a, b}` with `1 ≤ a < b ≤ n + 1`,
i.e. the tensor states with `1` in positions `a`, `b` and `X` everywhere else. -/
abbrev PairIdx (n : ℕ) := {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ n + 1}

/-- The diagonal coefficient `4 - δ_{a,1} - δ_{b,n+1} - δ_{b,a+1}` of eq. (6.10). -/
def prop19DiagCoeff (n a b : ℕ) : ℂ :=
  (4 : ℂ) - (if a = 1 then 1 else 0) - (if b = n + 1 then 1 else 0) -
    (if b = a + 1 then 1 else 0)

/-- The neighbour `{a-1, b}` of `{a, b}`, available when `2 ≤ a`. -/
def prop19DownA {n : ℕ} (p : PairIdx n) (h : 2 ≤ p.1.1) : PairIdx n :=
  ⟨(p.1.1 - 1, p.1.2), by
    obtain ⟨h1, h2, h3⟩ := p.2
    omega⟩

/-- The neighbour `{a+1, b}` of `{a, b}`, available when `a + 1 < b`. -/
def prop19UpA {n : ℕ} (p : PairIdx n) (h : p.1.1 + 1 < p.1.2) : PairIdx n :=
  ⟨(p.1.1 + 1, p.1.2), by
    obtain ⟨h1, h2, h3⟩ := p.2
    omega⟩

/-- The neighbour `{a, b-1}` of `{a, b}`, available when `1 ≤ a < b-1`. -/
def prop19DownB {n : ℕ} (p : PairIdx n) (h : p.1.1 + 1 < p.1.2) : PairIdx n :=
  ⟨(p.1.1, p.1.2 - 1), by
    obtain ⟨h1, h2, h3⟩ := p.2
    omega⟩

/-- The neighbour `{a, b+1}` of `{a, b}`, available when `b + 1 ≤ n + 1`. -/
def prop19UpB {n : ℕ} (p : PairIdx n) (h : p.1.2 + 1 ≤ n + 1) : PairIdx n :=
  ⟨(p.1.1, p.1.2 + 1), by
    obtain ⟨h1, h2, h3⟩ := p.2
    omega⟩

/-- The Laplacian of `TU_n` in bidegree `(0, 3 - n)`, eq. (6.10), acting on the
coordinate space of the pair basis: row `{a,b}` reads the diagonal coefficient
and the four neighbours `{a±1,b}`, `{a,b±1}`, with a neighbour dropped when it
falls outside `1 ≤ a < b ≤ n + 1` (the paper's `{a,b} = 0` convention). -/
def prop19Lap (n : ℕ) : (PairIdx n → ℂ) →ₗ[ℂ] (PairIdx n → ℂ) :=
  LinearMap.pi fun q : PairIdx n =>
    prop19DiagCoeff n q.1.1 q.1.2 • (LinearMap.proj q : (PairIdx n → ℂ) →ₗ[ℂ] ℂ) +
      (if h : 2 ≤ q.1.1 then
        (LinearMap.proj (prop19DownA q h) : (PairIdx n → ℂ) →ₗ[ℂ] ℂ) else 0) +
      (if h : q.1.1 + 1 < q.1.2 then
        (LinearMap.proj (prop19UpA q h) : (PairIdx n → ℂ) →ₗ[ℂ] ℂ) else 0) +
      (if h : q.1.1 + 1 < q.1.2 then
        (LinearMap.proj (prop19DownB q h) : (PairIdx n → ℂ) →ₗ[ℂ] ℂ) else 0) +
      (if h : q.1.2 + 1 ≤ n + 1 then
        (LinearMap.proj (prop19UpB q h) : (PairIdx n → ℂ) →ₗ[ℂ] ℂ) else 0)

/-- Pointwise form of `prop19Lap`: the row `{a,b}` of eq. (6.10). -/
theorem prop19Lap_apply (n : ℕ) (x : PairIdx n → ℂ) (q : PairIdx n) :
    prop19Lap n x q = prop19DiagCoeff n q.1.1 q.1.2 * x q +
      (if h : 2 ≤ q.1.1 then x (prop19DownA q h) else 0) +
      (if h : q.1.1 + 1 < q.1.2 then x (prop19UpA q h) else 0) +
      (if h : q.1.1 + 1 < q.1.2 then x (prop19DownB q h) else 0) +
      (if h : q.1.2 + 1 ≤ n + 1 then x (prop19UpB q h) else 0) := by
  simp only [prop19Lap, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, LinearMap.zero_apply, smul_eq_mul]
  split_ifs <;> simp [LinearMap.proj_apply]

/-- Value-level equality of pair indices: from `q = p` extract coordinate
equalities. -/
private theorem pair_val_eq {n : ℕ} {q p : PairIdx n} (h : q = p) :
    q.1.1 = p.1.1 ∧ q.1.2 = p.1.2 := by
  have hv : q.1 = p.1 := Subtype.ext_iff.mp h
  exact ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩

/-- Value-level equality of pair indices, converse. -/
private theorem pair_eq_of_val {n : ℕ} {q p : PairIdx n}
    (h : q.1.1 = p.1.1 ∧ q.1.2 = p.1.2) : q = p :=
  Subtype.ext_iff.mpr (Prod.ext_iff.mpr ⟨h.1, h.2⟩)

/-- **Proposition 19, row/neighbour duality for the `{a-1, b}` slot.**  Reading
the basis vector `{a,b}` in the `{a-1,b}` row equals reading the `{a+1,b}`
neighbour of `{a,b}` in the `q` row, because the two shifts are mutually
inverse on the valid range. -/
private theorem row_downA_eq {n : ℕ} (q : PairIdx n) (a b : ℕ)
    (hh : 1 ≤ a ∧ a < b ∧ b ≤ n + 1) :
    (if hq : 2 ≤ q.1.1 then
      (if prop19DownA q hq = (⟨(a, b), hh⟩ : PairIdx n) then (1 : ℂ) else 0)
      else 0) =
      (if h : a + 1 < b then
      (if q = prop19UpA (⟨(a, b), hh⟩ : PairIdx n) h then (1 : ℂ) else 0)
      else 0) := by
  obtain ⟨q1, q2, q3⟩ := q.2
  by_cases hq : q.1.1 = a + 1 ∧ q.1.2 = b
  · obtain ⟨hq1, hq2⟩ := hq
    have hguard : 2 ≤ q.1.1 := by omega
    have hguardP : a + 1 < b := by omega
    have hDA : prop19DownA q hguard = (⟨(a, b), hh⟩ : PairIdx n) := by
      apply pair_eq_of_val
      show q.1.1 - 1 = a ∧ q.1.2 = b
      omega
    have hUA : prop19UpA (⟨(a, b), hh⟩ : PairIdx n) hguardP = q := by
      apply pair_eq_of_val
      show a + 1 = q.1.1 ∧ b = q.1.2
      omega
    rw [dif_pos hguard, dif_pos hguardP, hDA, hUA]
    simp
  · have hL : (if hq2 : 2 ≤ q.1.1 then
        (if prop19DownA q hq2 = (⟨(a, b), hh⟩ : PairIdx n) then (1 : ℂ) else 0)
        else 0) = 0 := by
      split
      · rename_i hq2
        rw [if_neg]
        intro hne
        apply hq
        have hval : q.1.1 - 1 = a ∧ q.1.2 = b := pair_val_eq hne
        omega
      · rfl
    have hR : (if h : a + 1 < b then
        (if q = prop19UpA (⟨(a, b), hh⟩ : PairIdx n) h then (1 : ℂ) else 0)
        else 0) = 0 := by
      split
      · rename_i h
        rw [if_neg]
        intro hne
        apply hq
        have hval : q.1.1 = a + 1 ∧ q.1.2 = b := pair_val_eq hne
        omega
      · rfl
    rw [hL, hR]

/-- **Proposition 19, row/neighbour duality for the `{a+1, b}` slot.** -/
private theorem row_upA_eq {n : ℕ} (q : PairIdx n) (a b : ℕ)
    (hh : 1 ≤ a ∧ a < b ∧ b ≤ n + 1) :
    (if hq : q.1.1 + 1 < q.1.2 then
      (if prop19UpA q hq = (⟨(a, b), hh⟩ : PairIdx n) then (1 : ℂ) else 0)
      else 0) =
      (if h : 2 ≤ a then
      (if q = prop19DownA (⟨(a, b), hh⟩ : PairIdx n) h then (1 : ℂ) else 0)
      else 0) := by
  obtain ⟨q1, q2, q3⟩ := q.2
  have hh1 : 1 ≤ a := hh.1
  have hh2 : a < b := hh.2.1
  have hh3 : b ≤ n + 1 := hh.2.2
  by_cases hq : q.1.1 = a - 1 ∧ q.1.2 = b
  · obtain ⟨hq1, hq2⟩ := hq
    have hguard : q.1.1 + 1 < q.1.2 := by omega
    have hguardP : 2 ≤ a := by omega
    have hUA : prop19UpA q hguard = (⟨(a, b), hh⟩ : PairIdx n) := by
      apply pair_eq_of_val
      show q.1.1 + 1 = a ∧ q.1.2 = b
      omega
    have hDA : prop19DownA (⟨(a, b), hh⟩ : PairIdx n) hguardP = q := by
      apply pair_eq_of_val
      show a - 1 = q.1.1 ∧ b = q.1.2
      omega
    rw [dif_pos hguard, dif_pos hguardP, hUA, hDA]
    simp
  · have hL : (if hq2 : q.1.1 + 1 < q.1.2 then
        (if prop19UpA q hq2 = (⟨(a, b), hh⟩ : PairIdx n) then (1 : ℂ) else 0)
        else 0) = 0 := by
      split
      · rename_i hq2
        rw [if_neg]
        intro hne
        apply hq
        have hval : q.1.1 + 1 = a ∧ q.1.2 = b := pair_val_eq hne
        omega
      · rfl
    have hR : (if h : 2 ≤ a then
        (if q = prop19DownA (⟨(a, b), hh⟩ : PairIdx n) h then (1 : ℂ) else 0)
        else 0) = 0 := by
      split
      · rename_i h
        rw [if_neg]
        intro hne
        apply hq
        have hval : q.1.1 = a - 1 ∧ q.1.2 = b := pair_val_eq hne
        omega
      · rfl
    rw [hL, hR]

/-- **Proposition 19, row/neighbour duality for the `{a, b-1}` slot.** -/
private theorem row_downB_eq {n : ℕ} (q : PairIdx n) (a b : ℕ)
    (hh : 1 ≤ a ∧ a < b ∧ b ≤ n + 1) :
    (if hq : q.1.1 + 1 < q.1.2 then
      (if prop19DownB q hq = (⟨(a, b), hh⟩ : PairIdx n) then (1 : ℂ) else 0)
      else 0) =
      (if h : b + 1 ≤ n + 1 then
      (if q = prop19UpB (⟨(a, b), hh⟩ : PairIdx n) h then (1 : ℂ) else 0)
      else 0) := by
  obtain ⟨q1, q2, q3⟩ := q.2
  have hh1 : 1 ≤ a := hh.1
  have hh2 : a < b := hh.2.1
  have hh3 : b ≤ n + 1 := hh.2.2
  by_cases hq : q.1.1 = a ∧ q.1.2 = b + 1
  · obtain ⟨hq1, hq2⟩ := hq
    have hguard : q.1.1 + 1 < q.1.2 := by omega
    have hguardP : b + 1 ≤ n + 1 := by omega
    have hDB : prop19DownB q hguard = (⟨(a, b), hh⟩ : PairIdx n) := by
      apply pair_eq_of_val
      show q.1.1 = a ∧ q.1.2 - 1 = b
      omega
    have hUB : prop19UpB (⟨(a, b), hh⟩ : PairIdx n) hguardP = q := by
      apply pair_eq_of_val
      show a = q.1.1 ∧ b + 1 = q.1.2
      omega
    rw [dif_pos hguard, dif_pos hguardP, hDB, hUB]
    simp
  · have hL : (if hq2 : q.1.1 + 1 < q.1.2 then
        (if prop19DownB q hq2 = (⟨(a, b), hh⟩ : PairIdx n) then (1 : ℂ) else 0)
        else 0) = 0 := by
      split
      · rename_i hq2
        rw [if_neg]
        intro hne
        apply hq
        have hval : q.1.1 = a ∧ q.1.2 - 1 = b := pair_val_eq hne
        omega
      · rfl
    have hR : (if h : b + 1 ≤ n + 1 then
        (if q = prop19UpB (⟨(a, b), hh⟩ : PairIdx n) h then (1 : ℂ) else 0)
        else 0) = 0 := by
      split
      · rename_i h
        rw [if_neg]
        intro hne
        apply hq
        have hval : q.1.1 = a ∧ q.1.2 = b + 1 := pair_val_eq hne
        omega
      · rfl
    rw [hL, hR]

/-- **Proposition 19, row/neighbour duality for the `{a, b+1}` slot.** -/
private theorem row_upB_eq {n : ℕ} (q : PairIdx n) (a b : ℕ)
    (hh : 1 ≤ a ∧ a < b ∧ b ≤ n + 1) :
    (if hq : q.1.2 + 1 ≤ n + 1 then
      (if prop19UpB q hq = (⟨(a, b), hh⟩ : PairIdx n) then (1 : ℂ) else 0)
      else 0) =
      (if h : a + 1 < b then
      (if q = prop19DownB (⟨(a, b), hh⟩ : PairIdx n) h then (1 : ℂ) else 0)
      else 0) := by
  obtain ⟨q1, q2, q3⟩ := q.2
  have hh1 : 1 ≤ a := hh.1
  have hh2 : a < b := hh.2.1
  have hh3 : b ≤ n + 1 := hh.2.2
  by_cases hq : q.1.1 = a ∧ q.1.2 = b - 1
  · obtain ⟨hq1, hq2⟩ := hq
    have hguard : q.1.2 + 1 ≤ n + 1 := by omega
    have hguardP : a + 1 < b := by omega
    have hUB : prop19UpB q hguard = (⟨(a, b), hh⟩ : PairIdx n) := by
      apply pair_eq_of_val
      show q.1.1 = a ∧ q.1.2 + 1 = b
      omega
    have hDB : prop19DownB (⟨(a, b), hh⟩ : PairIdx n) hguardP = q := by
      apply pair_eq_of_val
      show a = q.1.1 ∧ b - 1 = q.1.2
      omega
    rw [dif_pos hguard, dif_pos hguardP, hUB, hDB]
    simp
  · have hL : (if hq2 : q.1.2 + 1 ≤ n + 1 then
        (if prop19UpB q hq2 = (⟨(a, b), hh⟩ : PairIdx n) then (1 : ℂ) else 0)
        else 0) = 0 := by
      split
      · rename_i hq2
        rw [if_neg]
        intro hne
        apply hq
        have hval : q.1.1 = a ∧ q.1.2 + 1 = b := pair_val_eq hne
        omega
      · rfl
    have hR : (if h : a + 1 < b then
        (if q = prop19DownB (⟨(a, b), hh⟩ : PairIdx n) h then (1 : ℂ) else 0)
        else 0) = 0 := by
      split
      · rename_i h
        rw [if_neg]
        intro hne
        apply hq
        have hval : q.1.1 = a ∧ q.1.2 = b - 1 := pair_val_eq hne
        omega
      · rfl
    rw [hL, hR]

/-- **Proposition 19** (arXiv:2501.12378v2, p. 38, eq. (6.10)).  On the pair
basis `{a, b}` the Laplacian of `TU_n` in bidegree `(0, 3 - n)` acts by the
diagonal coefficient plus the four neighbouring pair basis vectors, with a
neighbour dropped exactly when it falls outside `1 ≤ a < b ≤ n + 1` (the
paper's `{a,b} = 0` convention).  Proved by the four row/neighbour duality
lemmas and a pointwise case split on `q = {a,b}`. -/
theorem proposition19 (n a b : ℕ) (h : 1 ≤ a ∧ a < b ∧ b ≤ n + 1) :
    prop19Lap n (Pi.single (⟨(a, b), h⟩ : PairIdx n) 1) =
      prop19DiagCoeff n a b • Pi.single (⟨(a, b), h⟩ : PairIdx n) (1 : ℂ) +
        (if h2 : 2 ≤ a then
          Pi.single (prop19DownA (⟨(a, b), h⟩ : PairIdx n) h2) (1 : ℂ) else 0) +
        (if h2 : a + 1 < b then
          Pi.single (prop19UpA (⟨(a, b), h⟩ : PairIdx n) h2) (1 : ℂ) else 0) +
        (if h2 : a + 1 < b then
          Pi.single (prop19DownB (⟨(a, b), h⟩ : PairIdx n) h2) (1 : ℂ) else 0) +
        (if h2 : b + 1 ≤ n + 1 then
          Pi.single (prop19UpB (⟨(a, b), h⟩ : PairIdx n) h2) (1 : ℂ) else 0) := by
  have hh1 : 1 ≤ a := h.1
  have hh2 : a < b := h.2.1
  have hh3 : b ≤ n + 1 := h.2.2
  funext q
  rw [prop19Lap_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Pi.zero_apply, dite_apply]
  rw [row_downA_eq q a b h, row_upA_eq q a b h,
      row_downB_eq q a b h, row_upB_eq q a b h]
  by_cases hq : q = (⟨(a, b), h⟩ : PairIdx n)
  · subst hq
    have hneDA : ∀ hg : 2 ≤ (⟨(a, b), h⟩ : PairIdx n).1.1,
        prop19DownA (⟨(a, b), h⟩ : PairIdx n) hg ≠
          (⟨(a, b), h⟩ : PairIdx n) := by
      intro hg hne
      have hval : (⟨(a, b), h⟩ : PairIdx n).1.1 - 1 = a ∧
        (⟨(a, b), h⟩ : PairIdx n).1.2 = b := pair_val_eq hne
      simp only [show ((⟨(a, b), h⟩ : PairIdx n).val).1 = a from rfl,
        show ((⟨(a, b), h⟩ : PairIdx n).val).2 = b from rfl] at hval
      omega
    have hneUA : ∀ hg : (⟨(a, b), h⟩ : PairIdx n).1.1 + 1 <
        (⟨(a, b), h⟩ : PairIdx n).1.2,
        prop19UpA (⟨(a, b), h⟩ : PairIdx n) hg ≠
          (⟨(a, b), h⟩ : PairIdx n) := by
      intro hg hne
      have hval : (⟨(a, b), h⟩ : PairIdx n).1.1 + 1 = a ∧
        (⟨(a, b), h⟩ : PairIdx n).1.2 = b := pair_val_eq hne
      simp only [show ((⟨(a, b), h⟩ : PairIdx n).val).1 = a from rfl,
        show ((⟨(a, b), h⟩ : PairIdx n).val).2 = b from rfl] at hval
      omega
    have hneDB : ∀ hg : (⟨(a, b), h⟩ : PairIdx n).1.1 + 1 <
        (⟨(a, b), h⟩ : PairIdx n).1.2,
        prop19DownB (⟨(a, b), h⟩ : PairIdx n) hg ≠
          (⟨(a, b), h⟩ : PairIdx n) := by
      intro hg hne
      have hval : (⟨(a, b), h⟩ : PairIdx n).1.1 = a ∧
        (⟨(a, b), h⟩ : PairIdx n).1.2 - 1 = b := pair_val_eq hne
      simp only [show ((⟨(a, b), h⟩ : PairIdx n).val).1 = a from rfl,
        show ((⟨(a, b), h⟩ : PairIdx n).val).2 = b from rfl] at hval
      omega
    have hneUB : ∀ hg : (⟨(a, b), h⟩ : PairIdx n).1.2 + 1 ≤ n + 1,
        prop19UpB (⟨(a, b), h⟩ : PairIdx n) hg ≠
          (⟨(a, b), h⟩ : PairIdx n) := by
      intro hg hne
      have hval : (⟨(a, b), h⟩ : PairIdx n).1.1 = a ∧
        (⟨(a, b), h⟩ : PairIdx n).1.2 + 1 = b := pair_val_eq hne
      simp only [show ((⟨(a, b), h⟩ : PairIdx n).val).1 = a from rfl,
        show ((⟨(a, b), h⟩ : PairIdx n).val).2 = b from rfl] at hval
      omega
    rw [if_pos rfl]
    have hneDA : ∀ hg : 2 ≤ a, (⟨(a, b), h⟩ : PairIdx n) ≠
        prop19DownA (⟨(a, b), h⟩ : PairIdx n) hg := by
      intro hg hne
      have hval := pair_val_eq hne
      simp only [prop19DownA, show ((⟨(a, b), h⟩ : PairIdx n).val).1 = a from rfl,
        show ((⟨(a, b), h⟩ : PairIdx n).val).2 = b from rfl] at hval
      omega
    have hneUA : ∀ hg : a + 1 < b, (⟨(a, b), h⟩ : PairIdx n) ≠
        prop19UpA (⟨(a, b), h⟩ : PairIdx n) hg := by
      intro hg hne
      have hval := pair_val_eq hne
      simp only [prop19UpA, show ((⟨(a, b), h⟩ : PairIdx n).val).1 = a from rfl,
        show ((⟨(a, b), h⟩ : PairIdx n).val).2 = b from rfl] at hval
      omega
    have hneDB : ∀ hg : a + 1 < b, (⟨(a, b), h⟩ : PairIdx n) ≠
        prop19DownB (⟨(a, b), h⟩ : PairIdx n) hg := by
      intro hg hne
      have hval := pair_val_eq hne
      simp only [prop19DownB, show ((⟨(a, b), h⟩ : PairIdx n).val).1 = a from rfl,
        show ((⟨(a, b), h⟩ : PairIdx n).val).2 = b from rfl] at hval
      omega
    have hneUB : ∀ hg : b + 1 ≤ n + 1, (⟨(a, b), h⟩ : PairIdx n) ≠
        prop19UpB (⟨(a, b), h⟩ : PairIdx n) hg := by
      intro hg hne
      have hval := pair_val_eq hne
      simp only [prop19UpB, show ((⟨(a, b), h⟩ : PairIdx n).val).1 = a from rfl,
        show ((⟨(a, b), h⟩ : PairIdx n).val).2 = b from rfl] at hval
      omega
    have z1 : (if h2 : a + 1 < b then
        (if (⟨(a, b), h⟩ : PairIdx n) = prop19UpA (⟨(a, b), h⟩ : PairIdx n) h2
          then (1 : ℂ) else 0) else 0) = 0 := by
      split
      · rename_i h2
        rw [if_neg (hneUA h2)]
      · rfl
    have z2 : (if h2 : 2 ≤ a then
        (if (⟨(a, b), h⟩ : PairIdx n) = prop19DownA (⟨(a, b), h⟩ : PairIdx n) h2
          then (1 : ℂ) else 0) else 0) = 0 := by
      split
      · rename_i h2
        rw [if_neg (hneDA h2)]
      · rfl
    have z3 : (if h2 : b + 1 ≤ n + 1 then
        (if (⟨(a, b), h⟩ : PairIdx n) = prop19UpB (⟨(a, b), h⟩ : PairIdx n) h2
          then (1 : ℂ) else 0) else 0) = 0 := by
      split
      · rename_i h2
        rw [if_neg (hneUB h2)]
      · rfl
    have z4 : (if h2 : a + 1 < b then
        (if (⟨(a, b), h⟩ : PairIdx n) = prop19DownB (⟨(a, b), h⟩ : PairIdx n) h2
          then (1 : ℂ) else 0) else 0) = 0 := by
      split
      · rename_i h2
        rw [if_neg (hneDB h2)]
      · rfl
    rw [z1, z2, z3, z4]
  · rw [if_neg hq, mul_zero, mul_zero]
    ring

/-- **Proposition 19, dimension count.**  The number of pairs `{a, b}` with
`1 ≤ a < b ≤ n + 1` is `C(n+1, 2)`, so the bidegree `(0, 3-n)` chain space of
`TU_n` is `C(n+1, 2)`-dimensional (p. 37-38). -/
theorem proposition19_dim (n : ℕ) :
    ((Finset.univ : Finset (Fin (n + 1))).powersetCard 2).card = Nat.choose (n + 1) 2 := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end Qatlib.Papers.KhovanovHom25.MainResults
