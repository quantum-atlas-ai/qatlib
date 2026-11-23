/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Executable Fourier-register query model

Fixed source: arXiv:2604.05133v1, Section 3.2--3.3, Eqs. (3.2)--(3.19).
The work register contains the actual query index, Fourier query symbol, and
workspace. Input-independent gates act on that register alone. A query adds
the query symbol to the selected coordinate of the input Fourier label.

The output state and query count below are recursive functions of the same
instruction list. In particular the support bound covers arbitrary unitary
interleavings, rather than iterating an unconstrained support-preserving map.
This module does not assert the later orbit/knowledge success bound.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.Execution

/-- An input Fourier label, including its explicit zero coordinates. -/
abbrev Label (n q : ℕ) := Fin n → ZMod q

/-- The index, query-symbol, and arbitrary workspace registers. -/
abbrev Work (n q : ℕ) (W : Type*) := Fin n × ZMod q × W

/-- The joint Fourier input and work-register Hilbert space. -/
abbrev Joint (n q : ℕ) (W : Type*) := EuclideanSpace ℂ (Label n q × Work n q W)

/-- The work-register Hilbert space accessible to input-independent gates. -/
abbrev Local (n q : ℕ) (W : Type*) := EuclideanSpace ℂ (Work n q W)

variable {n q : ℕ} [NeZero q] {W : Type*} [Fintype W]

/-- Translation of precisely the queried Fourier coordinate. -/
def translate (i : Fin n) (c : ZMod q) : Label n q ≃ Label n q where
  toFun σ := Function.update σ i (σ i + c)
  invFun σ := Function.update σ i (σ i - c)
  left_inv σ := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Function.update_of_ne h]
  right_inv σ := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Function.update_of_ne h]

/-- The controlled Fourier query is an explicit permutation of the joint basis. -/
def queryPerm : (Label n q × Work n q W) ≃ (Label n q × Work n q W) where
  toFun z := (translate z.2.1 z.2.2.1 z.1, z.2)
  invFun z := ((translate z.2.1 z.2.2.1).symm z.1, z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- One oracle query, acting by the inverse permutation on amplitudes. -/
def query (ψ : Joint n q W) : Joint n q W :=
  WithLp.toLp 2 (fun z => ψ (queryPerm.symm z))

/-- The work-register slice at a fixed input Fourier label. -/
def fiber (ψ : Joint n q W) (σ : Label n q) : Local n q W :=
  WithLp.toLp 2 (fun a => ψ (σ, a))

/-- An input-independent unitary acts on each work-register slice with the same gate. -/
def localGate (U : Local n q W ≃ₗᵢ[ℂ] Local n q W) (ψ : Joint n q W) : Joint n q W :=
  WithLp.toLp 2 (fun z => U (fiber ψ z.1) z.2)

/-- The instructions of an actual oracle program. -/
inductive Instr (n q : ℕ) (W : Type*) [NeZero q] [Fintype W] where
  | gate (U : Local n q W ≃ₗᵢ[ℂ] Local n q W)
  | oracle

/-- Count the query constructors in the same list that is executed. -/
def queryCount : List (Instr n q W) → ℕ
  | [] => 0
  | .gate _ :: rest => queryCount rest
  | .oracle :: rest => queryCount rest + 1

/-- Execute a finite oracle program from left to right. -/
def execute : List (Instr n q W) → Joint n q W → Joint n q W
  | [], ψ => ψ
  | .gate U :: rest, ψ => execute rest (localGate U ψ)
  | .oracle :: rest, ψ => execute rest (query ψ)

/-- A controlled basis permutation preserves the actual Hilbert norm. -/
theorem query_norm (ψ : Joint n q W) : ‖query ψ‖ = ‖ψ‖ := by
  have hsq : ‖query ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    exact Fintype.sum_equiv queryPerm.symm _ _ (fun _ => rfl)
  nlinarith [norm_nonneg (query ψ), norm_nonneg ψ]

/-- Input-independent unitary gates preserve the norm of the full joint state. -/
theorem local_norm (U : Local n q W ≃ₗᵢ[ℂ] Local n q W) (ψ : Joint n q W) :
    ‖localGate U ψ‖ = ‖ψ‖ := by
  have hs (σ : Label n q) :
      (∑ a, ‖U (fiber ψ σ) a‖ ^ 2) = ∑ a, ‖ψ (σ, a)‖ ^ 2 := by
    rw [← EuclideanSpace.norm_sq_eq, U.norm_map, EuclideanSpace.norm_sq_eq]
    rfl
  have hsq : ‖localGate U ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun σ _ => hs σ
  nlinarith [norm_nonneg (localGate U ψ), norm_nonneg ψ]

/-- Every program preserves normalization, including arbitrary unitary interleavings. -/
theorem execute_norm (prog : List (Instr n q W)) (ψ : Joint n q W) :
    ‖execute prog ψ‖ = ‖ψ‖ := by
  induction prog generalizing ψ with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | gate U => exact (ih _).trans (local_norm U ψ)
    | oracle => exact (ih _).trans (query_norm ψ)

/-- The positions carrying nonzero Fourier symbols. -/
def support (σ : Label n q) : Finset (Fin n) :=
  Finset.univ.filter (fun i => σ i ≠ 0)

omit [NeZero q] in
/-- A query changes at most one position of the Fourier support. -/
theorem translate_card (i : Fin n) (c : ZMod q) (σ : Label n q) :
    (support (translate i c σ)).card ≤ (support σ).card + 1 := by
  have hs : support (translate i c σ) ⊆ insert i (support σ) := by
    intro j hj
    by_cases h : j = i
    · exact Finset.mem_insert.mpr (Or.inl h)
    · apply Finset.mem_insert.mpr
      right
      have hnz := (Finset.mem_filter.mp hj).2
      change Function.update σ i (σ i + c) j ≠ 0 at hnz
      rw [Function.update_of_ne h] at hnz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

/-- A state is supported on Fourier labels of degree at most `t`. -/
def Supported (t : ℕ) (ψ : Joint n q W) : Prop :=
  ∀ (σ : Label n q) (a : Work n q W), ψ (σ, a) ≠ 0 → (support σ).card ≤ t

/-- An input-independent unitary cannot change the input Fourier support. -/
theorem local_support {t : ℕ} {ψ : Joint n q W} (hψ : Supported t ψ)
    (U : Local n q W ≃ₗᵢ[ℂ] Local n q W) : Supported t (localGate U ψ) := by
  intro σ a hnonzero
  by_contra hlarge
  have hf : fiber ψ σ = 0 := by
    ext b
    by_contra hb
    exact hlarge (hψ σ b hb)
  apply hnonzero
  change U (fiber ψ σ) a = 0
  rw [hf, map_zero]
  rfl

omit [NeZero q] [Fintype W] in
/-- The actual controlled query increases Fourier degree by at most one. -/
theorem query_support {t : ℕ} {ψ : Joint n q W} (hψ : Supported t ψ) :
    Supported (t + 1) (query ψ) := by
  intro σ a hnonzero
  have hold : ψ ((translate a.1 a.2.1).symm σ, a) ≠ 0 := hnonzero
  have hdeg := hψ _ a hold
  have hstep := translate_card a.1 a.2.1 ((translate a.1 a.2.1).symm σ)
  rw [Equiv.apply_symm_apply] at hstep
  exact hstep.trans (Nat.add_le_add_right hdeg 1)

/-- The degree bound is determined by the executed query constructors, not an independent field. -/
theorem execute_support (prog : List (Instr n q W)) {t : ℕ} {ψ : Joint n q W}
    (hψ : Supported t ψ) : Supported (t + queryCount prog) (execute prog ψ) := by
  induction prog generalizing t ψ with
  | nil => simpa [execute, queryCount] using hψ
  | cons step rest ih =>
    cases step with
    | gate U => exact ih (local_support hψ U)
    | oracle =>
      simpa [execute, queryCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (query_support hψ)

variable [DecidableEq W]

/-- The uniform-input initial state, expressed in the Fourier basis as the zero label. -/
def initial (a₀ : Work n q W) : Joint n q W :=
  WithLp.toLp 2 (fun z => if z = (0, a₀) then 1 else 0)

/-- The actual initial state is normalized. -/
theorem initial_norm (a₀ : Work n q W) : ‖initial a₀‖ = 1 := by
  have hs : ‖initial a₀‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ z, ‖(if z = (0, a₀) then 1 else 0 : ℂ)‖ ^ 2) = 1
    calc
      (∑ z : Label n q × Work n q W, ‖(if z = (0, a₀) then 1 else 0 : ℂ)‖ ^ 2) =
          ∑ z : Label n q × Work n q W, if z = (0, a₀) then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        split_ifs <;> norm_num
      _ = 1 := by simp
  nlinarith [norm_nonneg (initial a₀)]

omit [NeZero q] [Fintype W] in
/-- The uniform-input initial state has degree zero. -/
theorem initial_support (a₀ : Work n q W) : Supported 0 (initial a₀) := by
  intro σ a hnonzero
  have hz : (σ, a) = (0, a₀) := by
    by_contra hz
    exact hnonzero (by simp [initial, hz])
  have hσ := congrArg Prod.fst hz
  change σ = 0 at hσ
  rw [hσ]
  simp [support]

/-- Proposition 3.2 for an arbitrary executed quantum query word with real unitary gates. -/
theorem uniform_degree (prog : List (Instr n q W)) (a₀ : Work n q W) :
    Supported (queryCount prog) (execute prog (initial a₀)) ∧
      ‖execute prog (initial a₀)‖ = 1 := by
  exact ⟨by simpa using execute_support prog (initial_support a₀),
    (execute_norm prog _).trans (initial_norm a₀)⟩

/-- Born probability of an actual work-register output event after execution. -/
def outputProb (prog : List (Instr n q W)) (a₀ : Work n q W)
    (event : Work n q W → Prop) [DecidablePred event] : ℝ :=
  ∑ z : Label n q × Work n q W,
    if event z.2 then ‖execute prog (initial a₀) z‖ ^ 2 else 0

/-- Output probabilities of the executed normalized program lie in the unit interval. -/
theorem output_bounds (prog : List (Instr n q W)) (a₀ : Work n q W)
    (event : Work n q W → Prop) [DecidablePred event] :
    0 ≤ outputProb prog a₀ event ∧ outputProb prog a₀ event ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun z _ => by split_ifs <;> positivity
  · have h := (uniform_degree prog a₀).2
    calc
      outputProb prog a₀ event ≤ ∑ z, ‖execute prog (initial a₀) z‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro z _
        split_ifs <;> simp
      _ = 1 := by rw [← EuclideanSpace.norm_sq_eq, h]; norm_num

end Qatlib.Papers.DistinctLB26.MainResults.Execution
