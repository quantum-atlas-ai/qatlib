/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemigroupLog13.MainResults.SemigroupTasks.SourceSemigroupTasks
import Mathlib.Data.Fintype.Perm

set_option backward.isDefEq.respectTransparency false

/-!
# The hard-instance family of Theorem 2

Fixed paper: Childs--Ivanyos, *Quantum computation of discrete logarithms in
semigroups*, arXiv:1310.6238v2 (1 Nov 2013).

Section 5 constructs, for every `n` and `k`, the finite commutative semigroup

`S = {g_0^{a_0} ⋯ g_{k-1}^{a_{k-1}} : 1 ≤ a_0 + ⋯ + a_{k-1} ≤ n} ∪ {0}`

with `0` absorbing and products exceeding total degree `n` sent to `0`.  Its
elements are exactly the positive exponent vectors of total length at most `n`,
plus `0`.

The hardness comes from a hidden encoding: elements of total degree `n` are
encoded by a hidden permutation `π` of the top layer, so constructive membership
for the encoded target recovers `π⁻¹`.  In this file the underlying set is
`Semi n k = Option (Boundary n k)`, the multiplication is `shiftMul`, and the
hidden encoding is the relabelling `relabel π`; the multiplication seen by the
algorithm is the conjugated `mulRelabel π`.  This makes the hard instance an
instance of the same program type used by every other claim: the program is
fixed, while both the multiplication table and the encoded input state depend on
`π`.

The semigroup laws (commutativity, associativity, absorption at `0`) hold by
case analysis on total degree.  They are not needed for the query statement and
are therefore not recorded as typeclass instances; the multiplication used in
the statement is the explicit function `mulRelabel`.
-/

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace Qatlib.Papers.SemigroupLog13.MainResults

/-! ## §1. Bounded exponent vectors -/

/-- Sum of a bounded exponent vector, as a natural number. -/
def vecSum {n k : ℕ} (v : Fin k → Fin (n + 1)) : ℕ := ∑ i, (v i : ℕ)

/-- Positive exponent vectors of total length at most `n` (the non-zero elements
of the paper's semigroup). -/
abbrev Boundary (n k : ℕ) : Type :=
  {v : Fin k → Fin (n + 1) // 0 < vecSum v ∧ vecSum v ≤ n}

/-- The top layer: exponent vectors of total length exactly `n` (the layer whose
encoding hides the permutation `π`). -/
abbrev TopVec (n k : ℕ) : Type := {v : Boundary n k // vecSum v.1 = n}

/-- The paper's semigroup: bounded exponent vectors together with the absorbing
zero, represented as `none`. -/
abbrev Semi (n k : ℕ) : Type := Option (Boundary n k)

noncomputable instance boundaryFintype (n k : ℕ) : Fintype (Boundary n k) := by
  classical exact inferInstance

noncomputable instance boundaryDecEq (n k : ℕ) : DecidableEq (Boundary n k) := by
  classical exact inferInstance

noncomputable instance topVecFintype (n k : ℕ) : Fintype (TopVec n k) := by
  classical exact inferInstance

noncomputable instance topVecDecEq (n k : ℕ) : DecidableEq (TopVec n k) := by
  classical exact inferInstance

noncomputable instance permTopFintype (n k : ℕ) : Fintype (Equiv.Perm (TopVec n k)) := by
  classical exact inferInstance

noncomputable instance permTopDecEq (n k : ℕ) : DecidableEq (Equiv.Perm (TopVec n k)) := by
  classical exact inferInstance

/-- Coordinatewise sum of two bounded vectors whose total degrees fit in `n`. -/
def addVec {n k : ℕ} (a b : Fin k → Fin (n + 1))
    (h : vecSum a + vecSum b ≤ n) : Fin k → Fin (n + 1) :=
  fun i => ⟨(a i : ℕ) + (b i : ℕ), by
    have ha : (a i : ℕ) ≤ vecSum a := by
      simpa only [vecSum] using Finset.single_le_sum (s := Finset.univ) (f := fun j => (a j : ℕ))
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hb : (b i : ℕ) ≤ vecSum b := by
      simpa only [vecSum] using Finset.single_le_sum (s := Finset.univ) (f := fun j => (b j : ℕ))
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega⟩

/-- Total degree adds under `addVec`. -/
theorem vecSum_addVec {n k : ℕ} (a b : Fin k → Fin (n + 1))
    (h : vecSum a + vecSum b ≤ n) :
    vecSum (addVec a b h) = vecSum a + vecSum b := by
  simp only [vecSum, addVec]
  rw [← Finset.sum_add_distrib]

/-- The paper's multiplication before relabelling: add total degrees when they
fit in `n`, and send the result to `0` otherwise. -/
def shiftMul (n k : ℕ) (u v : Semi n k) : Semi n k :=
  match u, v with
  | some a, some b =>
      if h : vecSum a.1 + vecSum b.1 ≤ n then
        some ⟨addVec a.1 b.1 h, by
          rw [vecSum_addVec]
          exact ⟨by have ha := a.2.1; have hb := b.2.1; omega, h⟩⟩
      else none
  | _, _ => none

/-- Relabelling by a permutation of the top layer: top-layer elements are sent
through `π`, every other element is fixed. -/
def relabel (n k : ℕ) (π : Equiv.Perm (TopVec n k)) (u : Semi n k) : Semi n k := by
  classical
  exact match u with
  | none => none
  | some a =>
      if h : vecSum a.1 = n then some (π ⟨a, h⟩).1 else some a

/-- The multiplication seen by the algorithm when the top layer is encoded by
the hidden permutation `π` (conjugation of `shiftMul` by the relabelling). -/
def mulRelabel (n k : ℕ) (π : Equiv.Perm (TopVec n k)) (u v : Semi n k) : Semi n k :=
  relabel n k π.symm (shiftMul n k (relabel n k π u) (relabel n k π v))

/-! ## §2. Generators and the hidden target -/

/-- The exponent vector with a single `1` in coordinate `i`. -/
def unitVec {n k : ℕ} (hn : 1 ≤ n) (i : Fin k) : Fin k → Fin (n + 1) :=
  fun j => if j = i then ⟨1, by omega⟩ else ⟨0, by omega⟩

/-- The unit vector has total degree one. -/
theorem vecSum_unitVec {n k : ℕ} (hn : 1 ≤ n) (i : Fin k) :
    vecSum (unitVec hn i) = 1 := by
  classical
  rw [vecSum, Finset.sum_eq_single i]
  · simp [unitVec]
  · intro j _ hji
    simp [unitVec, hji]
  · intro hnot
    exact absurd (Finset.mem_univ i) hnot

/-- The generator `g_i` of the paper's semigroup. -/
def gen (n k : ℕ) (hn : 1 ≤ n) (i : Fin k) : Boundary n k :=
  ⟨unitVec hn i, by rw [vecSum_unitVec hn]; exact ⟨by omega, by omega⟩⟩

/-- The fixed target vector `(n, 0, …, 0)` of the paper's reduction. -/
def topSigma (n k : ℕ) (hn : 1 ≤ n) (i0 : Fin k) : TopVec n k :=
  let v : Fin k → Fin (n + 1) := fun j => if j = i0 then ⟨n, by omega⟩ else ⟨0, by omega⟩
  have hsum : vecSum v = n := by
    classical
    rw [vecSum, Finset.sum_eq_single i0]
    · simp [v]
    · intro j _ hji
      simp [v, hji]
    · intro hnot
      exact absurd (Finset.mem_univ i0) hnot
  ⟨⟨v, by rw [hsum]; exact ⟨by omega, le_rfl⟩⟩, hsum⟩

/-- The encoded target seen by the algorithm: the relabelled top-layer vector. -/
def target (n k : ℕ) (hn : 1 ≤ n) (i0 : Fin k)
    (π : Equiv.Perm (TopVec n k)) : Semi n k :=
  relabel n k π (some (topSigma n k hn i0).1)

/-! ## §3. Explicit products and the membership target -/

/-- Powers for an explicit multiplication (no monoid structure assumed). -/
def powMul {S : Type} (mul : S → S → S) (g : S) : ℕ → S
  | 0 => g
  | j + 1 => mul (powMul mul g j) g

/-- Product of a nonempty list for an explicit multiplication. -/
def mulList {S : Type} (mul : S → S → S) (l : List S) : Option S :=
  l.foldr (fun x acc => some (match acc with | none => x | some y => mul x y)) none

/-- The paper's product `g_0^{a_0} ⋯ g_{k-1}^{a_{k-1}}` with zero exponents
contributing no factor, evaluated under an explicit multiplication. -/
def tupleProdMul {S : Type} (mul : S → S → S) {k : ℕ} (g : Fin k → S)
    (a : Fin k → ℕ) : Option S :=
  mulList mul
    ((Finset.univ.filter (fun i => 0 < a i)).toList.map (fun i => powMul mul (g i) (a i)))

/-- Membership target on the `π`-relabelled hard instance: `a` is a nonzero
exponent tuple whose product is the hidden target. -/
def membershipOk (n k : ℕ) (hn : 1 ≤ n) (i0 : Fin k)
    (π : Equiv.Perm (TopVec n k)) (a : Fin k → ℕ) : Prop :=
  (∃ i, 0 < a i) ∧
    tupleProdMul (mulRelabel n k π) (fun i => some (gen n k hn i)) a =
      some (target n k hn i0 π)

end Qatlib.Papers.SemigroupLog13.MainResults
