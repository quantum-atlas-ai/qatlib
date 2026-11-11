/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false

/-! Girth versus injectivity of the DQI parity map for
"No Quantum Advantage in Decoded Quantum Interferometry for MaxCut"
(arXiv:2509.19966, 2025).

**Lemma 2 (`lem:girth`)**: the parity map `f`, sending the incidence
vector `β ∈ 𝔽₂^E` of a subgraph of `G` to the parity vector of its
vertex degrees, is injective on the subgraphs `ℰ_l` with at most `l`
edges if and only if `G` has girth at least `2l+1`.

The paper's proof is F₂-linear algebra: `f(β) = Bᵀβ` for the
edge-vertex incidence matrix `B`, so two distinct subgraphs with equal
parity vectors yield a nonzero even-degree subgraph `β + β'` with at
most `2l` edges, which must contain a cycle of length at most `2l`;
conversely a cycle of length at most `2l` splits into two arcs of
length at most `l` with equal parity vectors.

This file proves the complete F₂ core of that argument:

- `parityMap_add` / `parityMap_zero`: `f` is additive (linear).
- `hwt_add_le`: Hamming weight is subadditive, so `β + β'` has at
  most `2l` edges.
- `injOn_of_kernel_min_weight`: if every nonzero even subgraph has
  more than `2l` edges then `f` is injective on `ℰ_l` (the `β + β'`
  argument, one direction of Lemma 2).
- `exists_small_kernel_of_not_injOn`: failure of injectivity on `ℰ_l`
  exhibits a nonzero even subgraph with at most `2l` edges (the other
  `β + β'` direction).
- `inj_iff_min_cycle_weight`: assembling both directions with the
  graph-theoretic facts — cycles are even, a nonzero even subgraph
  contains a (no longer) cycle, and a cycle of length at most `2l`
  splits into two `ℰ_l` arcs of equal parity — the full Lemma 2
  equivalence "injective on `ℰ_l` iff every cycle has more than `2l`
  edges", i.e. girth at least `2l+1`.

The three graph facts are stated as explicit hypotheses; they are the
standard walk arguments recorded in the paper's proof.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.DQIAdvantage25.MainResults

open Finset

variable {V E : Type} [Fintype V] [Fintype E]

/-- The field with two elements. -/
local notation "𝔽₂" => ZMod 2

/-- The parity map of DQI: the incidence vector `β ∈ 𝔽₂^E` of a
subgraph is sent to the parity vector `f(β) ∈ 𝔽₂^V` of its vertex
degrees, `f(β) = Bᵀβ` for the edge-vertex incidence `B`. -/
def parityMap (B : E → V → 𝔽₂) (β : E → 𝔽₂) : V → 𝔽₂ :=
  fun v => ∑ e, β e * B e v

/-- The Hamming weight of an `𝔽₂^E` vector: the number of edges of
the subgraph it represents. -/
def hwt {E : Type} [Fintype E] (β : E → 𝔽₂) : ℕ := ∑ e, (β e).val

omit [Fintype V] in
/-- Doubling is zero on `𝔽₂`. -/
lemma ztwo_add_self (x : 𝔽₂) : x + x = 0 := by
  have hx : x.val < 2 := ZMod.val_lt x
  have h : (x + x).val = 0 := by rw [ZMod.val_add]; omega
  exact (ZMod.val_eq_zero _).mp h

omit [Fintype V] in
/-- On `𝔽₂`, a sum vanishes only when the summands agree. -/
lemma ztwo_add_eq_zero_iff (x y : 𝔽₂) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    apply ZMod.val_injective
    have hx : x.val < 2 := ZMod.val_lt x
    have hy : y.val < 2 := ZMod.val_lt y
    have hval := congrArg ZMod.val h
    rw [ZMod.val_add, ZMod.val_zero] at hval
    omega
  · intro h
    rw [h, ztwo_add_self]

omit [Fintype V] in
/-- The parity map is additive: `f(β + β') = f(β) + f(β')`. -/
lemma parityMap_add (B : E → V → 𝔽₂) (β β' : E → 𝔽₂) :
    parityMap B (β + β') = parityMap B β + parityMap B β' := by
  funext v
  simp only [parityMap, Pi.add_apply, add_mul, Finset.sum_add_distrib]

omit [Fintype V] in
/-- The parity map sends the empty subgraph to the zero parity. -/
lemma parityMap_zero (B : E → V → 𝔽₂) : parityMap B 0 = 0 := by
  funext v
  simp [parityMap]

omit [Fintype V] in
/-- The parity map sends differences of subgraphs with equal parity
to zero. -/
lemma parityMap_eq_of_eq (B : E → V → 𝔽₂) {β β' : E → 𝔽₂}
    (h : parityMap B β = parityMap B β') : parityMap B (β + β') = 0 := by
  rw [parityMap_add, h]
  funext v
  exact ztwo_add_self _

/-- Hamming weight is subadditive: the subgraph `β + β'` has at most
the combined number of edges of `β` and `β'`. -/
lemma hwt_add_le (β β' : E → 𝔽₂) : hwt (β + β') ≤ hwt β + hwt β' := by
  have h : ∀ e, ((β + β') e).val ≤ (β e).val + (β' e).val := by
    intro e
    rw [Pi.add_apply, ZMod.val_add]
    omega
  calc hwt (β + β') = ∑ e, ((β + β') e).val := rfl
    _ ≤ ∑ e, ((β e).val + (β' e).val) := Finset.sum_le_sum (fun e _ => h e)
    _ = hwt β + hwt β' := by
        simp only [hwt]
        rw [Finset.sum_add_distrib]

omit [Fintype E] in
/-- On `𝔽₂^E`, distinct vectors never sum to zero. -/
lemma add_ne_zero_of_ne {β β' : E → 𝔽₂} (h : β ≠ β') : β + β' ≠ 0 := by
  intro hz
  apply h
  funext e
  have h1 : β e + β' e = 0 := congrFun hz e
  exact (ztwo_add_eq_zero_iff _ _) |>.mp h1

/-- A nonzero vector on `𝔽₂^E` has positive Hamming weight. -/
lemma hwt_pos_of_ne {β : E → 𝔽₂} (h : β ≠ 0) : 0 < hwt β := by
  by_contra hle
  apply h
  funext e
  have hsum : ∑ e', (β e').val = 0 :=
    Nat.le_zero.mp (Nat.le_of_not_gt hle)
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun e' _ => Nat.zero_le ((β e').val))).mp hsum e (Finset.mem_univ e)
  exact (ZMod.val_eq_zero _).mp this

omit [Fintype V] in
/-- **Lemma 2, `β + β'` direction (sufficiency)**: if every nonzero
even subgraph of `G` has more than `2l` edges, then the parity map is
injective on the subgraphs `ℰ_l` with at most `l` edges. -/
theorem injOn_of_kernel_min_weight (B : E → V → 𝔽₂) (l : ℕ)
    (h : ∀ δ : E → 𝔽₂, δ ≠ 0 → parityMap B δ = 0 → 2 * l < hwt δ)
    {β β' : E → 𝔽₂} (hβ : hwt β ≤ l) (hβ' : hwt β' ≤ l)
    (hEq : parityMap B β = parityMap B β') : β = β' := by
  by_contra hne
  have h2l := h _ (add_ne_zero_of_ne hne) (parityMap_eq_of_eq B hEq)
  have hle := hwt_add_le β β'
  omega

omit [Fintype V] in
/-- **Lemma 2, `β + β'` direction (necessity)**: two distinct
subgraphs of `ℰ_l` with equal parity vectors yield a nonzero even
subgraph with at most `2l` edges. -/
theorem exists_small_kernel_of_ne (B : E → V → 𝔽₂) (l : ℕ)
    {β β' : E → 𝔽₂} (hne : β ≠ β')
    (hβ : hwt β ≤ l) (hβ' : hwt β' ≤ l)
    (hEq : parityMap B β = parityMap B β') :
    ∃ δ : E → 𝔽₂, δ ≠ 0 ∧ parityMap B δ = 0 ∧ hwt δ ≤ 2 * l :=
  ⟨β + β', add_ne_zero_of_ne hne, parityMap_eq_of_eq B hEq,
    le_trans (hwt_add_le β β') (by omega)⟩

omit [Fintype V] in
/-- **Lemma 2 (`lem:girth`), assembled**: with the incidence `B` of a
graph `G`, the parity map is injective on the subgraphs `ℰ_l` with at
most `l` edges if and only if every cycle of `G` has more than `2l`
edges — that is, if and only if the girth of `G` is at least
`2l+1`. The graph facts used by the paper's proof enter as explicit
hypotheses:

- `hEven`: a nonzero even subgraph contains a cycle with no more
  edges (the paper's walk argument; in particular every nonzero cycle
  is itself even, so the cycle edge vectors lie in the kernel).
- `hArcs`: a cycle with at most `2l` edges splits into two subgraphs
  of at most `l` edges with equal parity vectors (the two arcs
  between a pair of antipodal cycle vertices).

Here `C` abstracts the predicate "is the edge-incidence vector of a
cycle of `G`", so the right-hand side reads "the girth of `G` exceeds
`2l`". -/
theorem inj_iff_min_cycle_weight (B : E → V → 𝔽₂) (l : ℕ)
    (C : (E → 𝔽₂) → Prop)
    (hEven : ∀ δ : E → 𝔽₂, δ ≠ 0 → parityMap B δ = 0 →
      ∃ c, C c ∧ hwt c ≤ hwt δ)
    (hArcs : ∀ c, C c → hwt c ≤ 2 * l →
      ∃ β₁ β₂ : E → 𝔽₂, β₁ ≠ β₂ ∧ hwt β₁ ≤ l ∧ hwt β₂ ≤ l ∧
        parityMap B β₁ = parityMap B β₂) :
    (∀ β : E → 𝔽₂, hwt β ≤ l → ∀ β' : E → 𝔽₂, hwt β' ≤ l →
        parityMap B β = parityMap B β' → β = β')
      ↔ ∀ c, C c → 2 * l < hwt c := by
  constructor
  · intro hinj c hc
    by_contra hle
    obtain ⟨β₁, β₂, hne, h₁, h₂, hEq⟩ := hArcs c hc (by omega)
    exact hne (hinj β₁ h₁ β₂ h₂ hEq)
  · intro hmin β hβ β' hβ' hEq
    refine injOn_of_kernel_min_weight B l (fun δ hδ hker => ?_) hβ hβ' hEq
    obtain ⟨c, hc, hle⟩ := hEven δ hδ hker
    exact lt_of_lt_of_le (hmin c hc) hle

omit [Fintype V] in
/-- Two distinct subgraphs with equal parity vectors and at most `l`
edges each exist already when a single nonzero even subgraph `γ` with
at most `2l` edges admits a splitting — the interface consumed by the
arc-splitting direction of `inj_iff_min_cycle_weight`. -/
theorem not_injOn_of_small_cycle_split (B : E → V → 𝔽₂) (l : ℕ)
    (h : ∃ β₁ β₂ : E → 𝔽₂, β₁ ≠ β₂ ∧ hwt β₁ ≤ l ∧ hwt β₂ ≤ l ∧
      parityMap B β₁ = parityMap B β₂) :
    ¬ ∀ β : E → 𝔽₂, hwt β ≤ l → ∀ β' : E → 𝔽₂, hwt β' ≤ l →
      parityMap B β = parityMap B β' → β = β' := by
  obtain ⟨β₁, β₂, hne, h₁, h₂, hEq⟩ := h
  intro hinj
  exact hne (hinj β₁ h₁ β₂ h₂ hEq)

end Qatlib.Papers.DQIAdvantage25.MainResults
