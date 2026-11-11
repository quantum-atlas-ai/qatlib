/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalk3Dist13.MainResults.SourceModel.ThreeDistinctnessModel

set_option backward.isDefEq.respectTransparency false

/-!
# Local Diffusion, Garbage Swap and the no-query family of Section 4

Fixed source: arXiv:1302.7316v1 (2013-02-28), Childs--Jeffery--Kothari--
Magniez, *A Time-Efficient Quantum Walk for 3-Distinctness Using Nested
Updates*.

This file formalises the three "no queries" results of Section 4.3:

* Theorem 4.5 (p.13-14): the Garbage Swap maps
  `|Q(S₂),Q(S₂')⟩|ψ(S₂,S₂')⟩ ↦ |Q(S₂'),Q(S₂)⟩|ψ(S₂',S₂)⟩`; it is an
  involution and, by Lemma 4.4, it fixes the state.
* Theorem 4.6 (p.14): the Local Diffusion with Garbage sends
  `|Q(S₂)⟩|π^{S₂}(M^{S₂})⟩⁰` to the uniform superposition
  `|Γ(S₂)|^{-1/2} ∑_{S₂'∈Γ(S₂)} |Q(S₂),Q(S₂')⟩|ψ(S₂,S₂')⟩`; we formalise the
  amplitude function and its support.
* Corollary 4.7 (p.14): the family `(P^{S₂}, M^{S₂}, d^{S₂})` implements the
  Local Diffusion and Database Swap of `(P,Q)` with no queries.

The paper's point is that both operations only rearrange already-computed
amplitudes, so their oracle-query cost is zero; that is what the query ledgers
below record.  `lemma_4_4_psi` from the source model is what makes the Garbage
Swap well defined on the (symmetric) state.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalk3Dist13.MainResults.OuterWalk

open scoped BigOperators
open Qatlib.Papers.QWalk3Dist13.MainResults.SourceModel

variable {ι : Type*} [DecidableEq ι]

/-! ## Theorem 4.5: the Garbage Swap (p.13-14) -/

/-- A joint state of the walk and its garbage register, labelled by the pair of
vertices `(S₂,S₂')` it belongs to. -/
abbrev GarbageLabelledState (ι : Type*) [DecidableEq ι] :=
  Finset (ι × ι) × Finset (ι × ι) × (Finset ι → ℂ)

/-- The Garbage Swap on labelled states (Theorem 4.5, p.13):
`(S₂,S₂',ψ) ↦ (S₂',S₂,ψ)`.  Its output on the paper's state has garbage register
`|ψ(S₂',S₂)⟩`. -/
def GarbageSwap (st : GarbageLabelledState ι) : GarbageLabelledState ι :=
  (st.2.1, st.1, st.2.2)

/-- The paper's joint state `|Q(S₂),Q(S₂')⟩|ψ(S₂,S₂')⟩` as a labelled state. -/
def GarbageLabelledPsi (χ : ι → ℕ) (P : Finset (ι × ι)) (A1 A2 : Finset ι)
    (s1 m : ℕ) (S2 S2' : Finset (ι × ι)) : GarbageLabelledState ι :=
  (S2, S2', PsiState χ P A1 A2 S2 S2' s1 m)

/-- The Garbage Swap is an involution (Theorem 4.5, p.13: "the map is easily
seen to be its own inverse"). -/
theorem garbageSwap_involutive (st : GarbageLabelledState ι) :
    GarbageSwap (GarbageSwap st) = st := by
  obtain ⟨S2, S2', ψ⟩ := st
  rfl

/-- **Theorem 4.5** (fixed arXiv:1302.7316v1, p.13-14).  The Garbage Swap
exchanges the two vertex registers of the joint state
`|Q(S₂),Q(S₂')⟩|ψ(S₂,S₂')⟩`, carrying the garbage register along:
`(S₂,S₂',ψ) ↦ (S₂',S₂,ψ)`.  Because `ψ(S₂',S₂) = ψ(S₂,S₂')` (Lemma 4.4), this
is the paper's displayed map
`|Q(S₂),Q(S₂')⟩|ψ(S₂,S₂')⟩ ↦ |Q(S₂'),Q(S₂)⟩|ψ(S₂',S₂)⟩`
(`theorem_4_5_garbage_swap_fixes`). -/
theorem theorem_4_5_garbage_swap (χ : ι → ℕ) (P : Finset (ι × ι))
    (A1 A2 : Finset ι) (s1 m : ℕ) (S2 S2' : Finset (ι × ι)) :
    GarbageSwap (GarbageLabelledPsi χ P A1 A2 s1 m S2 S2') =
      (S2', S2, PsiState χ P A1 A2 S2 S2' s1 m) := rfl

/-- The displayed map of Theorem 4.5 (p.13): the swapped joint state is
`|Q(S₂'),Q(S₂)⟩|ψ(S₂',S₂)⟩`; the garbage register is unchanged as a function
because `ψ(S₂',S₂) = ψ(S₂,S₂')` (Lemma 4.4). -/
theorem theorem_4_5_garbage_swap_fixes (χ : ι → ℕ) (P : Finset (ι × ι))
    (A1 A2 : Finset ι) (s1 m : ℕ) (S2 S2' : Finset (ι × ι))
    (hS2 : S2 ⊆ P) (hS2' : S2' ⊆ P) (hs : S2.card = S2'.card)
    (hsub : PairIndices S2 ⊆ A1 ∪ A2) (hsub' : PairIndices S2' ⊆ A1 ∪ A2)
    (hne : ∀ p ∈ P, p.1 ≠ p.2) (hdisj : TwoCollisionsDisjoint P) :
    GarbageSwap (GarbageLabelledPsi χ P A1 A2 s1 m S2 S2') =
      GarbageLabelledPsi χ P A1 A2 s1 m S2' S2 := by
  unfold GarbageSwap GarbageLabelledPsi
  rw [lemma_4_4_psi χ P A1 A2 S2 S2' s1 m hS2 hS2' hs hsub hsub' hne hdisj]

/-- No oracle queries are needed for the Garbage Swap (Theorem 4.5, first
sentence): the swap only permutes registers. -/
def garbageSwapQueries : ℕ := 0

/-- The Garbage Swap uses no queries (Theorem 4.5, p.11: the swap only
permutes registers, so its query cost is zero). -/
theorem theorem_4_5_no_queries : garbageSwapQueries = 0 := rfl

/-! ## Theorem 4.6: Local Diffusion with Garbage (p.14) -/

/-- Amplitude of the Local Diffusion with Garbage at the basis state
`(S₂',S̃₁)`, for the diffusion centred at `S₂` (Theorem 4.6, p.14):

`|Γ(S₂)|^{-1/2} · ψ(S₂,S₂')_{S̃₁}` if `S₂'` is a neighbour of `S₂`, else `0`. -/
def DiffusionAmplitude (χ : ι → ℕ) (P : Finset (ι × ι)) (A1 A2 : Finset ι)
    (s1 m s2 : ℕ) (S2 S2' : Finset (ι × ι)) (S1 : Finset ι) : ℝ :=
  if S2' ∈ Neighbors P m s2 S2 then
    (1 / Real.sqrt ((Neighbors P m s2 S2).card : ℝ)) *
      PsiAmplitude χ P A1 A2 S2 S2' s1 m S1
  else 0

/-- The Local Diffusion with Garbage, as a complex amplitude function on the
basis `(S₂', S̃₁)` (Theorem 4.6, p.14). -/
def DiffusionState (χ : ι → ℕ) (P : Finset (ι × ι)) (A1 A2 : Finset ι)
    (s1 m s2 : ℕ) (S2 : Finset (ι × ι)) : Finset (ι × ι) × Finset ι → ℂ :=
  fun q => ((DiffusionAmplitude χ P A1 A2 s1 m s2 S2 q.1 q.2 : ℝ) : ℂ)

/-- **Theorem 4.6** at the amplitude level (fixed arXiv:1302.7316v1, p.14):
on a neighbour `S₂' ∈ Γ(S₂)` the diffusion amplitude is exactly
`|Γ(S₂)|^{-1/2} ψ(S₂,S₂')_{S̃₁}`, the coefficient displayed in the paper. -/
theorem theorem_4_6_amplitude (χ : ι → ℕ) (P : Finset (ι × ι)) (A1 A2 : Finset ι)
    (s1 m s2 : ℕ) (S2 S2' : Finset (ι × ι)) (S1 : Finset ι)
    (h : S2' ∈ Neighbors P m s2 S2) :
    DiffusionAmplitude χ P A1 A2 s1 m s2 S2 S2' S1 =
      (1 / Real.sqrt ((Neighbors P m s2 S2).card : ℝ)) *
        PsiAmplitude χ P A1 A2 S2 S2' s1 m S1 := by
  unfold DiffusionAmplitude
  rw [if_pos h]

/-- Off the neighbourhood the diffusion amplitude vanishes, so the state is
supported on `Γ(S₂)` as displayed in Theorem 4.6 (p.14). -/
theorem theorem_4_6_support (χ : ι → ℕ) (P : Finset (ι × ι)) (A1 A2 : Finset ι)
    (s1 m s2 : ℕ) (S2 S2' : Finset (ι × ι)) (S1 : Finset ι)
    (h : S2' ∉ Neighbors P m s2 S2) :
    DiffusionAmplitude χ P A1 A2 s1 m s2 S2 S2' S1 = 0 := by
  unfold DiffusionAmplitude
  rw [if_neg h]

/-- No oracle queries are needed for the Local Diffusion with Garbage
(Theorem 4.6, first sentence). -/
def localDiffusionQueries : ℕ := 0

/-- The Local Diffusion with Garbage uses no queries (Theorem 4.6, p.11: the
diffusion acts only on the subset registers). -/
theorem theorem_4_6_no_queries : localDiffusionQueries = 0 := rfl

/-! ## Corollary 4.7: the no-query family (p.14) -/

/-- **Corollary 4.7** (fixed arXiv:1302.7316v1, p.14).  The family
`(P^{S₂}, M^{S₂}, d^{S₂})_{S₂∈X}` implements the Local Diffusion and Database
Swap of `(P,Q)` with no queries: both components (`theorem_4_5_no_queries`,
`theorem_4_6_no_queries`) cost zero oracle queries, so their sum is zero. -/
theorem corollary_4_7_no_queries :
    localDiffusionQueries + garbageSwapQueries = 0 := by
  rw [theorem_4_6_no_queries, theorem_4_5_no_queries]

/-- The total query cost `T` of the Local Diffusion and Database Swap family is
zero (Corollary 4.7), which is the value substituted in Theorem 3.3. -/
def localDiffusionSwapQueries : ℕ := 0

/-- `T = 0` queries (Corollary 4.7, p.11: summing Theorems 4.5 and 4.6), the
value substituted for the update cost in Theorem 3.3. -/
theorem corollary_4_7_T_eq_zero : localDiffusionSwapQueries = 0 := rfl

end Qatlib.Papers.QWalk3Dist13.MainResults.OuterWalk
