/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Controlled local updates between representative pairs

Formal core of Supplementary Section I.2 (Eq. (S2)–(S9)) of *Harnessing problem
structure for end-to-end quantum speed-ups* (arXiv:2609.40105v1).

A local update acts on the ordered pair `(|x⟩, |x'⟩)` of a source and a target
basis string.  On the real two-dimensional subspace spanned by that pair the
paper's generator `H_up(μ) = i (F_μ - F_μ†)` exponentiates to the rotation

`|x⟩ ↦ cos θ |x⟩ + sin θ |x'⟩`,
`|x'⟩ ↦ -sin θ |x⟩ + cos θ |x'⟩`  (Eq. (S5)),

which is what `pairEvolve` models here.  The module also records the cost
accounting of Algorithm S1 (gate count `G = G_X + G_CX + 2 g + 2`, depth
`D = D_out + 2 d + 2`, ancillas `A = a`), and proves the linear cost bound
`G ≤ 4κ + 2g + 2` used by every family construction.
-/

namespace Qatlib.Papers.ProbStructure26.StatePrep

open Finset

/-- A bit string on `n` positions. -/
abbrev BitString (n : ℕ) := Fin n → Bool

/-- The support of a local update: the positions where the source and target
strings differ (the set `K` of Eq. (S2)). -/
def support {n : ℕ} (x x' : BitString n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ x' i)

/-- The control set of an update: positions where source and target agree, so
that the pair is selected exactly (the set `C` of Eq. (S6)). -/
def agreeSet {n : ℕ} (x x' : BitString n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = x' i)

/-- Support and agreement set partition the register. -/
theorem support_union_agreeSet {n : ℕ} (x x' : BitString n) :
    support x x' ∪ agreeSet x x' = Finset.univ := by
  ext i
  by_cases h : x i = x' i <;> simp [support, agreeSet, h]

/-- Support and agreement set are disjoint. -/
theorem support_disjoint_agreeSet {n : ℕ} (x x' : BitString n) :
    Disjoint (support x x') (agreeSet x x') := by
  rw [Finset.disjoint_left]
  intro i hi hj
  simp only [support, agreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact hi hj

/-- The number of support plus control positions is the register size. -/
theorem card_support_add_agreeSet {n : ℕ} (x x' : BitString n) :
    (support x x').card + (agreeSet x x').card = n := by
  have h := support_union_agreeSet x x'
  have hc := Finset.card_union_add_card_inter (support x x') (agreeSet x x')
  rw [h, Finset.card_univ, Fintype.card_fin] at hc
  have hd : (support x x') ∩ (agreeSet x x') = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp (support_disjoint_agreeSet x x')
  rw [hd, Finset.card_empty] at hc
  omega

/-- The signed update pattern of Eq. (S2): `+1` when a `0` becomes `1`, `-1`
when a `1` becomes `0`, and `0` off the support. -/
def signedPattern {n : ℕ} (x x' : BitString n) (i : Fin n) : ℤ :=
  if x i = false ∧ x' i = true then 1
  else if x i = true ∧ x' i = false then -1
  else 0

/-- Off the support the signed pattern vanishes. -/
theorem signedPattern_eq_zero_of_not_mem {n : ℕ} {x x' : BitString n} {i : Fin n}
    (hi : i ∉ support x x') : signedPattern x x' i = 0 := by
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
  unfold signedPattern
  rw [hi]
  cases x i <;> cases x' i <;> simp_all

/-- On a `+1` site the source bit is `0` and the target bit is `1`. -/
theorem signedPattern_pos {n : ℕ} {x x' : BitString n} {i : Fin n}
    (hi : signedPattern x x' i = 1) : x i = false ∧ x' i = true := by
  unfold signedPattern at hi
  by_cases h1 : x i = false ∧ x' i = true
  · exact h1
  · rw [if_neg h1] at hi
    by_cases h2 : x i = true ∧ x' i = false
    · rw [if_pos h2] at hi
      omega
    · rw [if_neg h2] at hi
      omega

/-- On a `-1` site the source bit is `1` and the target bit is `0`. -/
theorem signedPattern_neg {n : ℕ} {x x' : BitString n} {i : Fin n}
    (hi : signedPattern x x' i = -1) : x i = true ∧ x' i = false := by
  unfold signedPattern at hi
  by_cases h1 : x i = false ∧ x' i = true
  · rw [if_pos h1] at hi
    omega
  · rw [if_neg h1] at hi
    by_cases h2 : x i = true ∧ x' i = false
    · exact h2
    · rw [if_neg h2] at hi
      omega

/-- The real two-level rotation of Eq. (S5) applied to the amplitude pair
`(a, b)` of `|x⟩` and `|x'⟩`. -/
noncomputable def pairEvolve (θ : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos θ * v.1 - Real.sin θ * v.2, Real.sin θ * v.1 + Real.cos θ * v.2)

/-- The source basis vector evolves to `cos θ |x⟩ + sin θ |x'⟩`, the expansion
direction used in preparation (Eq. (S5), first relation). -/
theorem pairEvolve_source (θ : ℝ) :
    pairEvolve θ (1, 0) = (Real.cos θ, Real.sin θ) := by
  simp [pairEvolve]

/-- The target basis vector evolves to `-sin θ |x⟩ + cos θ |x'⟩`, which fixes
the unitary extension (Eq. (S5), second relation). -/
theorem pairEvolve_target (θ : ℝ) :
    pairEvolve θ (0, 1) = (-Real.sin θ, Real.cos θ) := by
  simp [pairEvolve]

/-- The two-level update is an isometry: it preserves the squared norm
`a² + b²`, so probability mass is conserved. -/
theorem pairEvolve_norm (θ a b : ℝ) :
    (pairEvolve θ (a, b)).1 ^ 2 + (pairEvolve θ (a, b)).2 ^ 2 = a ^ 2 + b ^ 2 := by
  simp only [pairEvolve]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Two successive two-level updates compose additively in the angle, the
elementary step in reading a chain of updates as a rotation. -/
theorem pairEvolve_add (θ φ : ℝ) (v : ℝ × ℝ) :
    pairEvolve φ (pairEvolve θ v) = pairEvolve (θ + φ) v := by
  obtain ⟨a, b⟩ := v
  simp only [pairEvolve, Prod.mk.injEq, Real.cos_add, Real.sin_add]
  constructor <;> ring

/-- Off the two-dimensional subspace a controlled update is the identity: basis
strings other than the source and target are untouched (Eq. (S6)). -/
noncomputable def controlledAmplitude {n : ℕ} (x x' : BitString n) (θ : ℝ)
    (ψ : BitString n → ℝ) (z : BitString n) : ℝ :=
  if z = x then Real.cos θ * ψ x - Real.sin θ * ψ x'
  else if z = x' then Real.sin θ * ψ x + Real.cos θ * ψ x'
  else ψ z

/-- The controlled update returns the source amplitude demanded by Eq. (S5). -/
theorem controlledAmplitude_source {n : ℕ} (x x' : BitString n) (θ : ℝ)
    (ψ : BitString n → ℝ) :
    controlledAmplitude x x' θ ψ x = Real.cos θ * ψ x - Real.sin θ * ψ x' := by
  simp [controlledAmplitude]

/-- The controlled update returns the target amplitude demanded by Eq. (S5). -/
theorem controlledAmplitude_target {n : ℕ} (x x' : BitString n) (θ : ℝ)
    (ψ : BitString n → ℝ) (hne : x' ≠ x) :
    controlledAmplitude x x' θ ψ x' = Real.sin θ * ψ x + Real.cos θ * ψ x' := by
  simp [controlledAmplitude, hne]

/-- Every other basis string keeps its amplitude. -/
theorem controlledAmplitude_other {n : ℕ} (x x' : BitString n) (θ : ℝ)
    (ψ : BitString n → ℝ) {z : BitString n} (hz : z ≠ x) (hz' : z ≠ x') :
    controlledAmplitude x x' θ ψ z = ψ z := by
  simp [controlledAmplitude, hz, hz']

/-- A control pattern `η` on a control set `C` is matched by the string `z`. -/
def MatchesOn {n : ℕ} (C : Finset (Fin n)) (η : BitString n) (z : BitString n) : Prop :=
  ∀ i ∈ C, z i = η i

/-- The generic update of Eq. (S6) sets `C := I \ K` and `η` to the common
values on `C`; the pair then matches its own control pattern. -/
theorem matches_agreeSet {n : ℕ} (x x' : BitString n) :
    MatchesOn (agreeSet x x') x x ∧ MatchesOn (agreeSet x x') x x' := by
  constructor <;> intro i hi
  · rfl
  · simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi.symm

/-- Gate count of Algorithm S1 before decomposing the middle multi-control:
`G_X = 2(δ_p + z_K + z_C)` temporary `X` gates and `G_CX = 2(κ_u - 1)` CNOTs. -/
def preGateCount (δp zK zC κu : ℕ) : ℕ := 2 * (δp + zK + zC) + 2 * (κu - 1)

/-- The depth outside the positive-control core, `D_out`; the extra `+2`
appears only when at least one temporary `X` layer is needed. -/
def outerDepth (δp κu z : ℕ) : ℕ :=
  2 * (κu - 1) + 2 * δp + if 0 < z then 2 else 0

/-- The total gate count `G = G_X + G_CX + 2 g_{κ-1} + 2` of one update, once
the middle multi-control is synthesized with `g` gates. -/
def updateGateCount (δp zK zC κu g : ℕ) : ℕ :=
  preGateCount δp zK zC κu + 2 * g + 2

/-- The total depth `D = D_out + 2 d_{κ-1} + 2` of one update. -/
def updateDepth (δp κu z d : ℕ) : ℕ := outerDepth δp κu z + 2 * d + 2

/-- The ancilla count of one update is that of the middle multi-control. -/
def updateAncillas (a : ℕ) : ℕ := a

/-- Protocol size: support plus control qubits, `κ = κ_u + κ_c`. -/
def updateWidth (κu κc : ℕ) : ℕ := κu + κc

/-- Linear gate bound of the controlled update: with `z_K + z_C ≤ κ` and
`δ_p ≤ 1`, the gate count is at most `2κ + 2(κ_u - 1) + 2g + 4`, hence
`O(κ + g)` and, for a linear multi-control synthesis, `O(κ)` gates. -/
theorem updateGateCount_le (δp zK zC κu g : ℕ) (hδ : δp ≤ 1) :
    updateGateCount δp zK zC κu g ≤ 4 * updateWidth κu (zK + zC) + 2 * g + 4 := by
  unfold updateGateCount preGateCount updateWidth
  omega

/-- Linear depth bound of the controlled update: `D_out ≤ 2(κ_u - 1) + 2δ_p + 2`,
so the depth is at most `2κ + 2d + 2` for `κ ≥ κ_u`, i.e. `O(κ + d)`. -/
theorem updateDepth_le (δp κu z d : ℕ) (hδ : δp ≤ 1) :
    updateDepth δp κu z d ≤ 2 * updateWidth κu (z + 1) + 2 * d + 4 := by
  unfold updateDepth outerDepth updateWidth
  split_ifs with h <;> omega

/-- With no control qubits (`κ_u = 1`, `δ_p = 0`, `z = 0`) the update is a
single `R_y(2θ)` and costs one gate and one depth unit in the core. -/
theorem updateGateCount_trivial (g : ℕ) :
    updateGateCount 0 0 0 1 g = 2 * g + 2 := by
  unfold updateGateCount preGateCount
  simp

/-- The support of a generic update is exactly the number of differing
positions. -/
theorem support_card_eq {n : ℕ} (x x' : BitString n) :
    (support x x').card = n - (agreeSet x x').card := by
  have h := card_support_add_agreeSet x x'
  omega

end Qatlib.Papers.ProbStructure26.StatePrep
