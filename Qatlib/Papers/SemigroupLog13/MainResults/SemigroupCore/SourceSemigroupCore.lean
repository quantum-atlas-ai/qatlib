/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log

set_option backward.isDefEq.respectTransparency false

/-!
# Semigroup core: powers, index, period and the pigeonhole product bound

Fixed paper: Childs--Ivanyos, *Quantum computation of discrete logarithms in
semigroups*, arXiv:1310.6238v2 (1 Nov 2013).

This file owns the purely algebraic vocabulary that every result of the paper
uses:

* `spow g j` is the paper's `g^j` for `j ≥ 1`, evaluated inside the
  identity-adjoined monoid `WithOne S`.  The paper does not assume an identity;
  the adjoined identity only lets us write the empty product faithfully as `1`
  (see the note on Lemma 3 below).  For positive exponents the value lies in the
  `S` layer.
* `indexOf g` and `periodOf g` are the paper's index `t` and period `r`
  (Section 2, page 2), together with their defining universal properties,
  existence (finite semigroup) and eventual periodicity.
* `gamma` is the paper's `γ(g^j) = 1 iff g^{j+r} = g^j` predicate (page 3).
* `tupleProd`, `LexLt` and `lemma3_core` are the combinatorial content of
  Lemma 3 (page 6): the lexicographically first exponent tuple of a product has
  `∏ (aᵢ+1) ≤ |M|` in a finite commutative monoid.

The statement of Lemma 3 in the paper is phrased for a semigroup without an
identity and uses `|S|`.  The pigeonhole map actually lands in `S ∪ {1}` (the
empty exponent tuple is the adjoined identity), so the sharp statement for a
plain commutative semigroup is `∏(aᵢ+1) ≤ |S| + 1`; when an identity is present
the paper's `|S|` is recovered.  Both forms are proved here; see the docstrings
of `lemma3_semigroup` and `lemma3_monoid`.
-/

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace Qatlib.Papers.SemigroupLog13.MainResults

/-! ## §1. Semigroup powers in the identity-adjoined monoid -/

section Powers

variable {S : Type*} [Semigroup S]

/-- The paper's `g^j` (`j ≥ 1`) evaluated in the identity-adjoined monoid
`WithOne S` (Section 2, page 2).  For positive `j` the value is the coercion of
an element of `S`. -/
def spow (g : S) (j : ℕ) : WithOne S := (g : WithOne S) ^ j

/-- For `j ≥ 1`, `spow g j` is the coercion of an element of the semigroup. -/
theorem withOne_pow_coe (g : S) : ∀ j : ℕ, 0 < j → ∃ s : S, spow g j = (s : WithOne S)
  | 1, _ => ⟨g, by simp [spow]⟩
  | j + 2, _ => by
      obtain ⟨s, hs⟩ := withOne_pow_coe g (j + 1) (by omega)
      refine ⟨s * g, ?_⟩
      rw [spow, pow_succ]
      have hpow : (g : WithOne S) ^ (j + 1) = (s : WithOne S) := hs
      rw [hpow]
      exact (WithOne.coe_mul s g).symm

/-- Powers add: `g^{i+j} = g^i · g^j` (in the adjoined monoid). -/
theorem spow_add (g : S) (i j : ℕ) : spow g (i + j) = spow g i * spow g j := by
  simp [spow, pow_add]

/-- A positive power of a semigroup element is never the adjoined identity. -/
theorem spow_ne_one (g : S) (j : ℕ) (hj : 0 < j) : spow g j ≠ 1 := by
  obtain ⟨s, hs⟩ := withOne_pow_coe g j hj
  rw [hs]
  exact WithOne.coe_ne_one

/-- Pigeonhole on the `|S|+1` positive powers `g^1, …, g^{|S|+1}`: two of them
coincide, producing the paper's first periodic pair. -/
theorem exists_periodic_pair [Fintype S] (g : S) :
    ∃ j k : ℕ, 0 < j ∧ j < k ∧ spow g j = spow g k := by
  classical
  have hexp : ∀ m : Fin (Fintype.card S + 1), ∃ s : S, spow g (m.val + 1) = (s : WithOne S) :=
    fun m => withOne_pow_coe g (m.val + 1) (by omega)
  let f : Fin (Fintype.card S + 1) → S := fun m => Classical.choose (hexp m)
  have hf : ∀ m, spow g (m.val + 1) = (f m : WithOne S) := fun m =>
    Classical.choose_spec (hexp m)
  have hcard : Fintype.card S < Fintype.card (Fin (Fintype.card S + 1)) := by simp
  obtain ⟨m₁, m₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hv : m₁.val ≠ m₂.val := by
    intro h
    exact hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hlt
  · exact ⟨m₁.val + 1, m₂.val + 1, by omega, by omega, by rw [hf m₁, hf m₂, heq]⟩
  · exact ⟨m₂.val + 1, m₁.val + 1, by omega, by omega, by rw [hf m₁, hf m₂, heq]⟩

/-- The paper's index `t = min {j ∈ ℕ : g^j = g^k for some k ∈ j + ℕ}`
(Section 2, page 2) exists for every finite semigroup. -/
theorem index_exists [Fintype S] (g : S) :
    ∃ t : ℕ, 0 < t ∧ ∃ k : ℕ, t < k ∧ spow g t = spow g k := by
  obtain ⟨j, k, hj, hjk, he⟩ := exists_periodic_pair g
  exact ⟨j, hj, k, hjk, he⟩

/-- The index of `g` (paper's `t`, Section 2). -/
def indexOf [Fintype S] (g : S) : ℕ := by
  classical exact Nat.find (index_exists g)

/-- The index is positive. -/
theorem indexOf_pos [Fintype S] (g : S) : 0 < indexOf g :=
  (Nat.find_spec (index_exists g)).1

/-- Defining property of the index: some later power coincides with `g^t`. -/
theorem indexOf_spec [Fintype S] (g : S) :
    ∃ k : ℕ, indexOf g < k ∧ spow g (indexOf g) = spow g k :=
  (Nat.find_spec (index_exists g)).2

/-- Minimality of the index: any positive exponent with a later repeat is at
least `indexOf g`. -/
theorem indexOf_le [Fintype S] (g : S) {j : ℕ}
    (h : 0 < j ∧ ∃ k : ℕ, j < k ∧ spow g j = spow g k) : indexOf g ≤ j :=
  Nat.find_min' (index_exists g) h

/-- The paper's period `r = min {j ∈ ℕ : g^t = g^{t+j}}` (Section 2, page 2)
exists. -/
theorem period_exists [Fintype S] (g : S) :
    ∃ r : ℕ, 0 < r ∧ spow g (indexOf g + r) = spow g (indexOf g) := by
  obtain ⟨k, hk, he⟩ := indexOf_spec g
  refine ⟨k - indexOf g, by omega, ?_⟩
  rw [Nat.add_sub_of_le (le_of_lt hk)]
  exact he.symm

/-- The period of `g` (paper's `r`, Section 2). -/
def periodOf [Fintype S] (g : S) : ℕ := by
  classical exact Nat.find (period_exists g)

/-- The period is positive. -/
theorem periodOf_pos [Fintype S] (g : S) : 0 < periodOf g :=
  (Nat.find_spec (period_exists g)).1

/-- Defining property of the period: `g^{t+r} = g^t`. -/
theorem periodOf_spec [Fintype S] (g : S) :
    spow g (indexOf g + periodOf g) = spow g (indexOf g) :=
  (Nat.find_spec (period_exists g)).2

/-- Once past the index, the sequence `g^j` is `periodOf g`-periodic. -/
theorem eventually_periodic [Fintype S] (g : S) (j : ℕ) (hj : indexOf g ≤ j) :
    spow g (j + periodOf g) = spow g j := by
  have hper := periodOf_spec g
  have hadd : j + periodOf g = (indexOf g + periodOf g) + (j - indexOf g) := by omega
  rw [hadd, spow_add, hper]
  conv_rhs => rw [← Nat.add_sub_of_le hj]
  rw [spow_add]

/-- The paper's cycle predicate `γ(g^j) = 1` (page 3): whether `g^j` is in the
cycle of `g`, detected by `g^{j+r} = g^j`. -/
def gamma [Fintype S] (g : S) (j : ℕ) : Prop := spow g (j + periodOf g) = spow g j

/-- For positive `j`, `γ(g^j) = 1` exactly when `j` is at least the index. -/
theorem gamma_iff [Fintype S] (g : S) (j : ℕ) (hj : 0 < j) :
    gamma g j ↔ indexOf g ≤ j := by
  constructor
  · intro h
    have hr := periodOf_pos g
    exact indexOf_le g ⟨hj, j + periodOf g, by omega, h.symm⟩
  · intro h
    exact eventually_periodic g j h

/-- `γ` is monotone: once an element is in the cycle, all later powers are. -/
theorem gamma_monotone [Fintype S] (g : S) {j j' : ℕ} (hj : 0 < j) (hjj : j ≤ j')
    (h : gamma g j) : gamma g j' := by
  have hj' : 0 < j' := lt_of_lt_of_le hj hjj
  exact (gamma_iff g j' hj').2 (le_trans ((gamma_iff g j hj).1 h) hjj)

/-- The index is the first `1` in the list `γ(g^1), γ(g^2), …` (page 3). -/
theorem index_is_first_gamma [Fintype S] (g : S) :
    0 < indexOf g ∧ gamma g (indexOf g) ∧
      ∀ j : ℕ, 0 < j → gamma g j → indexOf g ≤ j := by
  refine ⟨indexOf_pos g, ?_, ?_⟩
  · exact (gamma_iff g (indexOf g) (indexOf_pos g)).2 le_rfl
  · intro j hj h
    exact (gamma_iff g j hj).1 h

end Powers

/-! ## §2. The lexicographically first exponent tuple (Lemma 3) -/

section Tuple

variable {M : Type*} [CommMonoid M] {k : ℕ}

/-- The product `g_0^{a_0} ⋯ g_{k-1}^{a_{k-1}}` of the paper, with the
convention `g_i^0 = 1` in the monoid `M`. -/
def tupleProd (g : Fin k → M) (a : Fin k → ℕ) : M := ∏ i, g i ^ a i

/-- Multiplicativity of the tuple product in the exponent. -/
theorem tupleProd_add (g : Fin k → M) (c d : Fin k → ℕ) :
    tupleProd g (c + d) = tupleProd g c * tupleProd g d := by
  simp only [tupleProd, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

/-- Factorisation of the tuple product along a coordinatewise inequality. -/
theorem tupleProd_decomp (g : Fin k → M) {a f : Fin k → ℕ} (h : ∀ i, f i ≤ a i) :
    tupleProd g a = tupleProd g f * tupleProd g (a - f) := by
  have ha : a = f + (a - f) := by
    funext i
    exact (Nat.add_sub_of_le (h i)).symm
  conv_lhs => rw [ha]
  rw [tupleProd_add]

/-- Lexicographic strict order on exponent tuples: the first differing
coordinate is smaller. -/
def LexLt (b a : Fin k → ℕ) : Prop :=
  ∃ i : Fin k, (∀ j : Fin k, j < i → b j = a j) ∧ b i < a i

/-- The box `{c : c_i ≤ a_i}` of exponent tuples below `a` (the pigeonhole
domain of Lemma 3). -/
def box (a : Fin k → ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (a i + 1))

/-- Membership in the box. -/
theorem mem_box {a c : Fin k → ℕ} : c ∈ box a ↔ ∀ i, c i ≤ a i := by
  rw [box, Fintype.mem_piFinset]
  simp [Nat.lt_succ_iff]

/-- The box has `∏ (a_i + 1)` elements. -/
theorem card_box (a : Fin k → ℕ) : (box a).card = ∏ i, (a i + 1) := by
  rw [box, Fintype.card_piFinset]
  simp

/-- **Lemma 3 core (pigeonhole form).**  In a finite commutative monoid `M`, if
`a` is the lexicographically first exponent tuple representing `x`, then
`∏ (aᵢ + 1) ≤ |M|`.

This is the paper's pigeonhole argument (arXiv:1310.6238v2, Lemma 3, page 6):
the box `{c : cᵢ ≤ aᵢ}` has `∏(aᵢ+1)` elements; if it exceeded `|M|` two
distinct tuples `e ≠ f` would have equal products; putting `bᵢ = aᵢ + eᵢ - fᵢ`
and orienting `e, f` at their first differing coordinate gives a solution `b`
that is lexicographically smaller than `a`, a contradiction.  No cancellation is
used: we compare `tupleProd a = tupleProd f * tupleProd (a - f)` with
`tupleProd b = tupleProd e * tupleProd (a - f)`. -/
theorem lemma3_core [Fintype M] (g : Fin k → M) (x : M) (a : Fin k → ℕ)
    (hfirst : tupleProd g a = x)
    (hmin : ∀ b : Fin k → ℕ, tupleProd g b = x → ¬ LexLt b a) :
    (∏ i, (a i + 1)) ≤ Fintype.card M := by
  classical
  by_contra hle
  have hlt : Fintype.card M < ∏ i, (a i + 1) := Nat.lt_of_not_le hle
  have hcard : Fintype.card M < Fintype.card ↥(box a) := by
    rw [Fintype.card_coe, card_box]
    exact hlt
  let Φ : ↥(box a) → M := fun c => tupleProd g c.1
  obtain ⟨e, f, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt Φ hcard
  have hboxe : ∀ i, e.1 i ≤ a i := mem_box.mp e.2
  have hboxf : ∀ i, f.1 i ≤ a i := mem_box.mp f.2
  -- Locate the first coordinate at which `e` and `f` differ.
  have hexists : ∃ i : Fin k, e.1 i ≠ f.1 i := by
    by_contra h
    apply hne
    rw [Subtype.ext_iff]
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  let D : Finset (Fin k) := Finset.univ.filter (fun i => e.1 i ≠ f.1 i)
  have hD : D.Nonempty :=
    ⟨Classical.choose hexists,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Classical.choose_spec hexists⟩⟩
  let i₀ : Fin k := D.min' hD
  have hi₀_mem : i₀ ∈ D := Finset.min'_mem D hD
  have hi₀_diff : e.1 i₀ ≠ f.1 i₀ := (Finset.mem_filter.mp hi₀_mem).2
  have hi₀_first : ∀ j : Fin k, j < i₀ → e.1 j = f.1 j := by
    intro j hj
    by_contra hne'
    have hjD : j ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne'⟩
    have hle : D.min' hD ≤ j := (Finset.isLeast_min' D hD).2 hjD
    omega
  -- Both tuples are solutions; comparing at `i₀` makes one lexicographically smaller.
  have key : ∀ (lo hi : Fin k → ℕ), (∀ i, lo i ≤ a i) → (∀ i, hi i ≤ a i) →
      tupleProd g lo = tupleProd g hi →
      (∀ j : Fin k, j < i₀ → lo j = hi j) → lo i₀ < hi i₀ → False := by
    intro lo hi hlo hhi heqlohi hbef hlti
    -- The competitor tuple `b = a + lo - hi`.
    let b : Fin k → ℕ := fun i => a i + lo i - hi i
    have hb_add : b = lo + (a - hi) := by
      funext i
      simp only [b, Pi.add_apply, Pi.sub_apply]
      have h1 : hi i ≤ a i := hhi i
      omega
    have ha_add : a = hi + (a - hi) := by
      funext i
      exact (Nat.add_sub_of_le (hhi i)).symm
    have hb_sol : tupleProd g b = x := by
      calc tupleProd g b = tupleProd g (lo + (a - hi)) := by rw [hb_add]
        _ = tupleProd g lo * tupleProd g (a - hi) := tupleProd_add g lo (a - hi)
        _ = tupleProd g hi * tupleProd g (a - hi) := by rw [heqlohi]
        _ = tupleProd g (hi + (a - hi)) := (tupleProd_add g hi (a - hi)).symm
        _ = tupleProd g a := by conv_rhs => rw [ha_add]
        _ = x := hfirst
    have hb_lex : LexLt b a := by
      refine ⟨i₀, ?_, ?_⟩
      · intro j hj
        simp only [b]
        rw [hbef j hj]
        exact Nat.add_sub_cancel _ _
      · have h1 : hi i₀ ≤ a i₀ := hhi i₀
        have h2 : lo i₀ < hi i₀ := hlti
        simp only [b]
        omega
    exact hmin b hb_sol hb_lex
  rcases lt_or_gt_of_ne hi₀_diff with hcase | hcase
  · exact key e.1 f.1 hboxe hboxf heq hi₀_first hcase
  · exact key f.1 e.1 hboxf hboxe heq.symm (fun j hj => (hi₀_first j hj).symm) hcase

/-- **Lemma 3 for a finite commutative monoid.**  When `M` has an identity, the
paper's `|S|` bound holds verbatim. -/
theorem lemma3_monoid {S : Type*} [CommMonoid S] [Fintype S] (g : Fin k → S) (x : S)
    (a : Fin k → ℕ) (hfirst : tupleProd g a = x)
    (hmin : ∀ b : Fin k → ℕ, tupleProd g b = x → ¬ LexLt b a) :
    (∏ i, (a i + 1)) ≤ Fintype.card S :=
  lemma3_core g x a hfirst hmin

/-- **Lemma 3 for a finite commutative semigroup** (paper's setting: no identity
assumed).  The empty exponent tuple contributes the adjoined identity, so the
sharp bound is `|S| + 1`; the paper writes `|S|`, which is correct under the
identity reading and is delivered by `lemma3_monoid`.

A literal `|S|` statement for a semigroup without identity is false: on the
three-element commutative semigroup with `a·a = a`, `b·b = b`, `a·b = c` and
`c` absorbing, the element `x = c = a·b` has lexicographically first exponent
tuple `(1,1)` with `(1+1)(1+1) = 4 > 3 = |S|` (the empty tuple is the extra
point `1`). -/
theorem lemma3_semigroup {S : Type*} [CommSemigroup S] [Fintype S] (g : Fin k → S)
    (x : S) (a : Fin k → ℕ)
    (hfirst : tupleProd (fun i => (g i : WithOne S)) a = (x : WithOne S))
    (hmin : ∀ b : Fin k → ℕ, tupleProd (fun i => (g i : WithOne S)) b = (x : WithOne S) →
      ¬ LexLt b a) :
    (∏ i, (a i + 1)) ≤ Fintype.card S + 1 := by
  haveI : Fintype (WithOne S) := inferInstanceAs (Fintype (Option S))
  have hcore := lemma3_core (fun i => (g i : WithOne S)) (x : WithOne S) a hfirst hmin
  have hcard : Fintype.card (WithOne S) = Fintype.card S + 1 := by
    have h1 : Fintype.card (WithOne S) = Fintype.card (Option S) :=
      Fintype.card_congr (Equiv.refl (WithOne S))
    rw [h1]
    exact Fintype.card_option
  rwa [hcard] at hcore

end Tuple

end Qatlib.Papers.SemigroupLog13.MainResults
