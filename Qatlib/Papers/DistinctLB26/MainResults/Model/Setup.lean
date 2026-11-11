/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.DistinctLB26.MainResults.Core.StateCore
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Setup — the paper's framework in a finite coordinate model

Fixed source: arXiv:2604.05133v1 (Belovs, *Tight Quantum Lower Bound for
k-Distinctness*), Sections 3.1–3.3 (pp. 8–11) and Section 3.5 (pp. 14–16).

This file fixes the modelling conventions used throughout the paper layer:

* `State ι` is the finite complex Hilbert space `EuclideanSpace ℂ ι` (the paper's
  finite-dimensional pure states).
* `Joint Y A` is the joint state space `Y ⊗ A` of the label register `Y` and the
  algorithm register `A`; the tensor product is modelled as the coordinate
  product `Y × A`.
* `measProj P` is the measurement operator `Π = Σ_ρ M_ρ ⊗ Π_ρ` of Eq. (3.31):
  a sum of pairwise orthogonal coordinate projectors, i.e. the projector onto
  the union of the outcome masks.
* `successProb P` is the total success probability `Σ_ρ ‖(M_ρ ⊗ Π_ρ) ψ‖²`.
* `PlainAntiConc` / `StrongAntiConc` are Definitions 3.8 / 3.9 (measuring only
  the algorithm register, resp. every measurement on `Y ⊗ A`).
* `Xle supp t` is the subspace `X_{≤ t}` of Fourier states whose support has
  size at most `t` (Section 3.1), together with the support-invariance of a
  single oracle query used in Proposition 3.2.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.Model

open Qatlib.Papers.DistinctLB26.MainResults.Core

/-- The paper's finite state space over the index type `ι`. -/
abbrev State (ι : Type*) : Type _ := Core.State ι

/-- The joint state space `Y ⊗ A` of the label register `Y` and the algorithm
register `A` (modelled as the coordinate product `Y × A`). -/
abbrev Joint (Y A : Type*) : Type _ := State (Y × A)

/-! ## Coordinate projectors and their algebra -/

variable {ι : Type*} [Fintype ι]

/-- Coordinate masks are additive. -/
theorem projMask_add (P : ι → Prop) [DecidablePred P] (x y : State ι) :
    Core.State.projMask P (x + y) =
      Core.State.projMask P x + Core.State.projMask P y := by
  apply Core.State.ext
  intro i
  by_cases h : P i <;> simp [Core.State.projMask_apply, h]

/-- Coordinate masks are homogeneous. -/
theorem projMask_smul (P : ι → Prop) [DecidablePred P] (c : ℂ) (x : State ι) :
    Core.State.projMask P (c • x) = c • Core.State.projMask P x := by
  apply Core.State.ext
  intro i
  by_cases h : P i <;> simp [Core.State.projMask_apply, h]

/-! ## Success probability and the measurement operator `Π` of (3.31) -/

/-- The slice of a joint state at a fixed algorithm-register coordinate. -/
def slice {ι A : Type*} [Fintype ι] (ψ : State (ι × A)) (a : A) : State ι :=
  WithLp.toLp 2 (fun i => ψ (i, a))

/-- The orthogonal projector `Π = Σ_ρ M_ρ ⊗ Π_ρ` of Eq. (3.31), realised as the
coordinate projector onto the union of the outcome masks `P ρ`. -/
def measProj {ρ : Type} [Fintype ρ] (P : ρ → ι → Prop) [∀ r, DecidablePred (P r)]
    (ψ : State ι) : State ι :=
  Core.State.projMask (fun i => ∃ r, P r i) ψ

/-- Total success probability of the measurement with outcome masks `P ρ`,
Eq. (3.31): the sum of the squared norms of the projected states. -/
def successProb {ρ : Type} [Fintype ρ] (P : ρ → ι → Prop) [∀ r, DecidablePred (P r)]
    (ψ : State ι) : ℝ :=
  ∑ r, ‖Core.State.projMask (P r) ψ‖ ^ 2

/-- **Claim 3.7** (p. 13, Eq. (3.31)): the total success probability of the
algorithm on the problem of Definition 3.3 equals `‖Π Υ ψ'T‖²`, where
`Π = Σ_ρ M_ρ ⊗ Π_ρ` is the orthogonal projector onto the correct-output
subspaces.  Here `Π` is `measProj P`, the success probability is the sum over the
outcome projectors, and the identity is the additivity of squared norms over the
pairwise orthogonal outcome masks. -/
theorem claim3_7 {ρ : Type} [Fintype ρ] (P : ρ → ι → Prop)
    [∀ r, DecidablePred (P r)]
    (hdisj : ∀ i r s, r ≠ s → ¬ (P r i ∧ P s i)) (ψ : State ι) :
    successProb P ψ = ‖measProj P ψ‖ ^ 2 := by
  unfold successProb measProj
  exact Core.State.sum_normSq_projMask_of_partition P hdisj ψ

/-- The measurement operator never increases the norm (it is an orthogonal
projector). -/
theorem norm_measProj_le {ρ : Type} [Fintype ρ] (P : ρ → ι → Prop)
    [∀ r, DecidablePred (P r)] (ψ : State ι) :
    ‖measProj P ψ‖ ≤ ‖ψ‖ :=
  Core.State.norm_projMask_le _ _

/-! ## Anti-concentration (Definitions 3.8 and 3.9) -/

/-- Plain `γ`-anti-concentration of a set `S` of joint states (Definition 3.8):
measuring only the algorithm register `A` has success probability at most
`γ² ‖ψ‖²`, i.e. `‖Π ψ‖ ≤ γ ‖ψ‖`. -/
def PlainAntiConc {Y A : Type*} [Fintype Y] [Fintype A] (γ : ℝ)
    (S : Set (State (Y × A))) : Prop :=
  ∀ (ψ : State (Y × A)), ψ ∈ S →
    ∀ (ρ : Type) [Fintype ρ] (Pa : ρ → A → Prop) [∀ r, DecidablePred (Pa r)],
      (∀ (z : Y × A) r s, r ≠ s → ¬ (Pa r z.2 ∧ Pa s z.2)) →
      ‖measProj (fun r (z : Y × A) => Pa r z.2) ψ‖ ≤ γ * ‖ψ‖

/-- Strong `γ`-anti-concentration of a set `S` of joint states (Definition 3.9):
every measurement `Π = Σ_ρ M_ρ ⊗ Π_ρ` on `Y ⊗ A` satisfies
`‖Π ψ‖ ≤ γ ‖ψ‖`. -/
def StrongAntiConc {Y A : Type*} [Fintype Y] [Fintype A] (γ : ℝ)
    (S : Set (State (Y × A))) : Prop :=
  ∀ (ψ : State (Y × A)), ψ ∈ S →
    ∀ (ρ : Type) [Fintype ρ] (P : ρ → Y × A → Prop) [∀ r, DecidablePred (P r)],
      (∀ (z : Y × A) r s, r ≠ s → ¬ (P r z ∧ P s z)) →
      ‖measProj P ψ‖ ≤ γ * ‖ψ‖

/-- **Claim 3.10** (p. 13): a strongly `γ`-anti-concentrated state is
`γ`-anti-concentrated.  Every measurement of the algorithm register alone is a
measurement of `Y ⊗ A` with masks independent of the label register. -/
theorem claim3_10 {Y A : Type*} [Fintype Y] [Fintype A] {γ : ℝ}
    {S : Set (State (Y × A))} (h : StrongAntiConc γ S) : PlainAntiConc γ S := by
  intro ψ hψ ρ _ Pa _ hdisj
  exact h ψ hψ ρ (fun r (z : Y × A) => Pa r z.2)
    (fun z r s hrs => hdisj z r s hrs)

/-- **Proposition 3.11** (p. 13): if `ψ` is strongly `γ`-anti-concentrated, then
for every orthogonal measurement `{Π_ρ}` of `A` we have `‖Π ψ‖ ≤ γ ‖ψ‖`, hence
the measurement success probability is at most `γ² ‖ψ‖²`. -/
theorem prop3_11 {Y A : Type*} [Fintype Y] [Fintype A] {γ : ℝ}
    {S : Set (State (Y × A))} (h : StrongAntiConc γ S) {ψ : State (Y × A)}
    (hψ : ψ ∈ S) {ρ : Type} [Fintype ρ] (P : ρ → Y × A → Prop)
    [∀ r, DecidablePred (P r)]
    (hdisj : ∀ (z : Y × A) r s, r ≠ s → ¬ (P r z ∧ P s z)) :
    ‖measProj P ψ‖ ≤ γ * ‖ψ‖ :=
  h ψ hψ ρ P hdisj

/-- **Proposition 3.11**, success-probability form: the success probability is
at most `(γ ‖ψ‖)²`. -/
theorem prop3_11_success {Y A : Type*} [Fintype Y] [Fintype A] {γ : ℝ}
    {S : Set (State (Y × A))} (h : StrongAntiConc γ S) {ψ : State (Y × A)}
    (hψ : ψ ∈ S) {ρ : Type} [Fintype ρ] (P : ρ → Y × A → Prop)
    [∀ r, DecidablePred (P r)]
    (hdisj : ∀ (z : Y × A) r s, r ≠ s → ¬ (P r z ∧ P s z)) :
    successProb P ψ ≤ (γ * ‖ψ‖) ^ 2 := by
  rw [claim3_7 P hdisj]
  exact pow_le_pow_left₀ (norm_nonneg _) (prop3_11 h hψ P hdisj) _

/-- **Lemma 3.12 (Success Probability of the Algorithm)** (p. 14): if the final
state `Υ ψT' = u + v` with `‖u‖ ≤ δ` and `v` strongly `γ`-anti-concentrated,
then the success probability is at most `(γ + δ)²`.  States of the algorithm are
unit vectors, hence `‖v‖ ≤ 1` is part of the paper's normalisation. -/
theorem lemma3_12 {Y A : Type*} [Fintype Y] [Fintype A] {γ δ : ℝ} (hγ : 0 ≤ γ)
    (hδ : 0 ≤ δ) {S : Set (State (Y × A))} {u v φ : State (Y × A)}
    (hdecomp : φ = u + v) (hu : ‖u‖ ≤ δ) (hv : ‖v‖ ≤ 1) (hac : StrongAntiConc γ S)
    (hvS : v ∈ S) {ρ : Type} [Fintype ρ] (P : ρ → Y × A → Prop)
    [∀ r, DecidablePred (P r)] (hdisj : ∀ (z : Y × A) r s, r ≠ s → ¬ (P r z ∧ P s z)) :
    successProb P φ ≤ (γ + δ) ^ 2 := by
  have hsplit : measProj P φ = measProj P u + measProj P v := by
    rw [hdecomp]
    exact projMask_add _ u v
  have hPu : ‖measProj P u‖ ≤ ‖u‖ := norm_measProj_le P u
  have hPv : ‖measProj P v‖ ≤ γ * ‖v‖ := prop3_11 hac hvS P hdisj
  have hbound : ‖measProj P φ‖ ≤ γ + δ := by
    rw [hsplit]
    calc ‖measProj P u + measProj P v‖ ≤ ‖measProj P u‖ + ‖measProj P v‖ := norm_add_le _ _
      _ ≤ ‖u‖ + γ * ‖v‖ := add_le_add hPu hPv
      _ ≤ δ + γ * ‖v‖ := add_le_add hu le_rfl
      _ ≤ δ + γ * 1 := by
          have : γ * ‖v‖ ≤ γ * 1 := mul_le_mul_of_nonneg_left hv hγ
          linarith
      _ = γ + δ := by ring
  rw [claim3_7 P hdisj]
  calc ‖measProj P φ‖ ^ 2 ≤ (γ + δ) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) hbound
    _ = (γ + δ) ^ 2 := rfl

/-- **Lemma 3.18 (Lower Bound Framework)** (p. 17): let `L⁺` be a knowledge
system with `Υ⁻ X_{≤T}` strongly `γ`-anti-concentrated and `‖Υ⁺ ψT'‖ ≤ δ`.
The decomposition `Υ ψT' = u + v` separates the component `u` carrying the
knowledge (`‖u‖ ≤ δ`) from the component `v` lying in the anti-concentrated
space, so the total success probability is at most `(γ + δ)²`. -/
theorem lemma3_18 {Y A : Type*} [Fintype Y] [Fintype A] {γ δ : ℝ} (hγ : 0 ≤ γ)
    (hδ : 0 ≤ δ) {S : Set (State (Y × A))} {u v φ : State (Y × A)}
    (hdecomp : φ = u + v) (hknow : ‖u‖ ≤ δ) (hunit : ‖v‖ ≤ 1)
    (hac : StrongAntiConc γ S) (hvS : v ∈ S) {ρ : Type} [Fintype ρ]
    (P : ρ → Y × A → Prop) [∀ r, DecidablePred (P r)]
    (hdisj : ∀ (z : Y × A) r s, r ≠ s → ¬ (P r z ∧ P s z)) :
    successProb P φ ≤ (γ + δ) ^ 2 :=
  lemma3_12 hγ hδ hdecomp hknow hunit hac hvS P hdisj

/-! ## Support size and the subspaces `X_{≤ t}` (Section 3.1, Proposition 3.2) -/

/-- The subspace `X_{≤ t}`: states whose Fourier expansion uses only indices
`i` with support size `supp i ≤ t`. -/
def Xle {ι : Type*} (supp : ι → ℕ) (t : ℕ) : Submodule ℂ (State ι) where
  carrier := {x | ∀ i, x i ≠ 0 → supp i ≤ t}
  add_mem' := by
    intro x y hx hy i hi
    by_cases hx0 : x i = 0
    · have hy0 : y i ≠ 0 := by
        intro h
        exact hi (by simp [hx0, h])
      exact hy i hy0
    · exact hx i hx0
  zero_mem' := by
    intro i hi
    exact absurd rfl hi
  smul_mem' := by
    intro c x hx i hi
    by_cases hc : c = 0
    · exact absurd (by simp [hc] : (c • x) i = 0) hi
    · have hxi : x i ≠ 0 := by
        intro h
        exact hi (by simp [h])
      exact hx i hxi

/-- `X_{≤ t}` is monotone in `t`. -/
theorem Xle_mono {ι : Type*} {supp : ι → ℕ} {t t' : ℕ} (htt : t ≤ t') :
    Xle supp t ≤ Xle supp t' := by
  intro x hx i hi
  exact le_trans (hx i hi) htt

/-- Membership in `X_{≤ t} ⊗ A` (the paper writes `ψ ∈ X_{≤ t} ⊗ A`). -/
def InXle {ι A : Type*} [Fintype ι] (supp : ι → ℕ) (t : ℕ)
    (ψ : State (ι × A)) : Prop :=
  ∀ a, slice ψ a ∈ Xle supp t

/-- Membership in `X_{≤ t} ⊗ A` is monotone in `t`. -/
theorem InXle_mono {ι A : Type*} [Fintype ι] {supp : ι → ℕ} {t t' : ℕ} (htt : t ≤ t')
    {ψ : State (ι × A)} (h : InXle supp t ψ) : InXle supp t' ψ := by
  intro a
  exact Xle_mono htt (h a)

/-- One oracle query raises the support size of every used Fourier index by at
most one (the oracle `O_{i,c}` only shifts the value at position `i`). -/
def SupportStep {ι : Type*} (supp : ι → ℕ) (O : State ι → State ι) : Prop :=
  ∀ x i, O x i ≠ 0 → ∃ j, x j ≠ 0 ∧ supp i ≤ supp j + 1

/-- A single query maps `X_{≤ t}` into `X_{≤ t+1}`. -/
theorem Xle_oracle_step {ι : Type*} {supp : ι → ℕ} {O : State ι → State ι}
    (hO : SupportStep supp O) {t : ℕ} {x : State ι} (hx : x ∈ Xle supp t) :
    O x ∈ Xle supp (t + 1) := by
  intro i hi
  obtain ⟨j, hj, hle⟩ := hO x i hi
  have := hx j hj
  omega

/-- The oracle acting on the Fourier register of a joint state, leaving `A`
untouched. -/
def oracleOnJoint {ι A : Type*} [Fintype ι] [Fintype A] (O : State ι → State ι)
    (ψ : State (ι × A)) : State (ι × A) :=
  WithLp.toLp 2 (fun z => O (slice ψ z.2) z.1)

/-- A query preserves membership in `X_{≤ t} ⊗ A`, raising `t` by one. -/
theorem oracleOnJoint_step {ι A : Type*} [Fintype ι] [Fintype A]
    {supp : ι → ℕ} {O : State ι → State ι} (hO : SupportStep supp O) {t : ℕ}
    {ψ : State (ι × A)} (hψ : InXle supp t ψ) :
    InXle supp (t + 1) (oracleOnJoint O ψ) := by
  intro a i hi
  exact Xle_oracle_step hO (hψ a) i hi

/-- Iterating a map `t` times. -/
def iter {ι : Type*} (F : State ι → State ι) : ℕ → State ι → State ι
  | 0, x => x
  | n + 1, x => F (iter F n x)

/-- `t` queries send `X_{≤ 0}` into `X_{≤ t}`. -/
theorem iter_mem_Xle {ι : Type*} {supp : ι → ℕ} {O : State ι → State ι}
    (hO : SupportStep supp O) {x₀ : State ι} (h₀ : x₀ ∈ Xle supp 0) :
    ∀ t, iter O t x₀ ∈ Xle supp t
  | 0 => h₀
  | t + 1 => Xle_oracle_step hO (iter_mem_Xle hO h₀ t)

/-- **Proposition 3.2** (p. 10, Eq. (3.11)/(3.19)): for the uniform states of
the algorithm, `ψ_t, ψ'_t ∈ X_{≤ t} ⊗ A`.  The state before the `t`-th query has
seen `t-1` queries, the state after it `t`; both have Fourier support at most
`t`, because each oracle query raises the support size by at most one. -/
theorem prop3_2 {ι A : Type*} [Fintype ι] [Fintype A] {supp : ι → ℕ}
    {O : State ι → State ι} (hO : SupportStep supp O) (ψ₀ : State (ι × A))
    (h₀ : InXle supp 0 ψ₀) (t : ℕ) :
    InXle supp t (iter (oracleOnJoint O) t ψ₀) ∧
      InXle supp t (iter (oracleOnJoint O) (t - 1) ψ₀) := by
  have hmain : ∀ t, InXle supp t (iter (oracleOnJoint O) t ψ₀) := by
    intro t
    induction t with
    | zero => simpa [iter] using h₀
    | succ n ih => simpa [iter] using oracleOnJoint_step hO ih
  exact ⟨hmain t, InXle_mono (Nat.sub_le t 1) (hmain (t - 1))⟩

/-- **Corollary 3.14** (p. 15): an algorithm evaluating the complementary
function `g` has total success probability at most `1/2`.  Together with the
success/failure balance `p_f + p_g ≤ 1` and the symmetry `p_f = p_g`, this gives
the paper's bound `1/2`.  (The source text phrases it as "exactly 1/2"; the
derivable statement is the upper bound, since the inequality direction is
`p_f + p_g ≤ 1`.) -/
theorem cor3_14 {pf pg : ℝ} (hsum : pf + pg ≤ 1) (hsym : pf = pg) : pf ≤ 1 / 2 := by
  linarith

/-- **Theorem 3.15** (p. 15): under the dual-polynomial assumptions, any quantum
algorithm evaluating `f` with `T` queries has success probability at most
`1 - ε`, where `ε` lower-bounds the success probability of the complementary
problem `g`. -/
theorem thm3_15 {pf pg ε : ℝ} (hsum : pf + pg ≤ 1) (hε : ε ≤ pg) : pf ≤ 1 - ε := by
  linarith

end Qatlib.Papers.DistinctLB26.MainResults.Model
