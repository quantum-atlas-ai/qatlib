/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.DistinctLB26.MainResults.Execution.FourierRun
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The standard phase oracle and the Fourier-register execution

Fixed source: arXiv:2604.05133v1, Section 3.2, Eqs. (3.2)--(3.4).
The character is the canonical exponential character of `ZMod q`. The same
instruction list executes either with the standard input phase oracle or with
the controlled Fourier-label translation. Their exact intertwining below
links the degree bound to a genuine input-query execution.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.Execution

variable {n q : ℕ} [NeZero q] {W : Type*} [Fintype W]

/-- The canonical character indexed by a computational input. -/
def inputChar (x : Label n q) : AddChar (Label n q) ℂ where
  toFun σ := ∏ i, AddChar.zmodAddEquiv (x i) (σ i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' σ τ := by
    simp only [Pi.add_apply, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

/-- The canonical input character is the product of its coordinate characters. -/
theorem inputChar_apply (x σ : Label n q) :
    inputChar x σ = ∏ i : Fin n, AddChar.zmodAddEquiv (x i) (σ i) := rfl

/-- Evaluating a single-coordinate label gives exactly the queried input symbol. -/
theorem inputChar_single (x : Label n q) (i : Fin n) (c : ZMod q) :
    inputChar x (Pi.single i c) = AddChar.zmodAddEquiv (x i) c := by
  classical
  rw [inputChar_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- Distinct computational inputs have distinct canonical characters. -/
theorem inputChar_injective : Function.Injective (inputChar (n := n) (q := q)) := by
  intro x y h
  funext i
  apply AddChar.zmodAddEquiv.injective
  ext c
  simpa only [inputChar_single] using congrArg (fun χ : AddChar (Label n q) ℂ =>
    χ (Pi.single i c)) h

omit [NeZero q] in
/-- The inverse Fourier query subtracts its queried coordinate label. -/
theorem translate_inv (i : Fin n) (c : ZMod q) (σ : Label n q) :
    (translate i c).symm σ = σ - Pi.single i c := by
  ext j
  by_cases h : j = i
  · subst j
    simp [translate]
  · simp [translate, Function.update_of_ne h, Pi.single_eq_of_ne h]

/-- The normalized Fourier plane wave for one fixed computational input. -/
def plane (x : Label n q) (φ : Local n q W) : Joint n q W :=
  WithLp.toLp 2 (fun z =>
    (inputChar x (-z.1) / (Real.sqrt (Fintype.card (Label n q)) : ℂ)) * φ z.2)

/-- The physical phase query on the index and query-symbol registers. -/
def phaseQuery (x : Label n q) (φ : Local n q W) : Local n q W :=
  WithLp.toLp 2 (fun a => AddChar.zmodAddEquiv (x a.1) a.2.1 * φ a)

omit [Fintype W] in
/-- A Fourier-register query is exactly the standard phase query on a plane wave. -/
theorem query_plane (x : Label n q) (φ : Local n q W) :
    query (plane x φ) = plane x (phaseQuery x φ) := by
  ext z
  change (inputChar x (-((translate z.2.1 z.2.2.1).symm z.1)) /
    (Real.sqrt (Fintype.card (Label n q)) : ℂ)) * φ z.2 = _
  rw [translate_inv, neg_sub]
  rw [show (Pi.single z.2.1 z.2.2.1 - z.1 : Label n q) =
    -z.1 + Pi.single z.2.1 z.2.2.1 by abel]
  rw [AddChar.map_add_eq_mul, inputChar_single]
  change (_ * _ / _) * _ = (_ / _) * (_ * _)
  ring

omit [Fintype W] in
/-- A plane-wave fiber is a scalar multiple of the same physical work state. -/
theorem fiber_plane (x : Label n q) (φ : Local n q W) (σ : Label n q) :
    fiber (plane x φ) σ =
      (inputChar x (-σ) / (Real.sqrt (Fintype.card (Label n q)) : ℂ)) • φ := by
  ext a
  rfl

/-- Input-independent work gates intertwine with the same physical work gate. -/
theorem local_plane (x : Label n q) (φ : Local n q W)
    (U : Local n q W ≃ₗᵢ[ℂ] Local n q W) :
    localGate U (plane x φ) = plane x (U φ) := by
  ext z
  change U (fiber (plane x φ) z.1) z.2 = _
  rw [fiber_plane, U.map_smul]
  rfl

/-- Execute the same program using its standard input phase oracle. -/
def inputRun (x : Label n q) : List (Instr n q W) → Local n q W → Local n q W
  | [], φ => φ
  | .gate U :: rest, φ => inputRun x rest (U φ)
  | .oracle :: rest, φ => inputRun x rest (phaseQuery x φ)

/-- The entire physical execution is intertwined by the Fourier plane-wave embedding. -/
theorem execute_plane (x : Label n q) (prog : List (Instr n q W)) (φ : Local n q W) :
    execute prog (plane x φ) = plane x (inputRun x prog φ) := by
  induction prog generalizing φ with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | gate U => simpa only [execute, inputRun, local_plane] using ih (U φ)
    | oracle => simpa only [execute, inputRun, query_plane] using ih (phaseQuery x φ)

/-- The actual phase oracle is norm preserving on the physical work space. -/
theorem phaseQuery_norm (x : Label n q) (φ : Local n q W) :
    ‖phaseQuery x φ‖ = ‖φ‖ := by
  have hs : ‖phaseQuery x φ‖ ^ 2 = ‖φ‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro a _
    change ‖AddChar.zmodAddEquiv (x a.1) a.2.1 * φ a‖ ^ 2 = ‖φ a‖ ^ 2
    rw [norm_mul, AddChar.norm_apply, one_mul]
  nlinarith [norm_nonneg (phaseQuery x φ), norm_nonneg φ]

/-- Arbitrary physical input-query executions preserve normalization. -/
theorem inputRun_norm (x : Label n q) (prog : List (Instr n q W)) (φ : Local n q W) :
    ‖inputRun x prog φ‖ = ‖φ‖ := by
  induction prog generalizing φ with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | gate U => exact (ih (U φ)).trans (U.norm_map φ)
    | oracle => exact (ih _).trans (phaseQuery_norm x φ)

/-- The Fourier plane-wave embedding preserves the physical state norm. -/
theorem plane_norm (x : Label n q) (φ : Local n q W) : ‖plane x φ‖ = ‖φ‖ := by
  let d : ℝ := Fintype.card (Label n q)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos (α := Label n q)
  have hc (σ : Label n q) :
      ‖inputChar x (-σ) / (Real.sqrt d : ℂ)‖ ^ 2 = 1 / d := by
    rw [norm_div, AddChar.norm_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg d), div_pow, one_pow, Real.sq_sqrt hd.le]
  have hs : ‖plane x φ‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    change (∑ σ : Label n q, ∑ a : Work n q W,
      ‖inputChar x (-σ) / (Real.sqrt d : ℂ) * φ a‖ ^ 2) = ‖φ‖ ^ 2
    simp_rw [norm_mul, mul_pow, hc]
    simp only [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    change 1 / d * (d * ‖φ‖ ^ 2) = ‖φ‖ ^ 2
    field_simp
  nlinarith [norm_nonneg (plane x φ), norm_nonneg φ]

end Qatlib.Papers.DistinctLB26.MainResults.Execution
