/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# HidShiftQuad09 — source model (Definitions)

Rötteler, *Quantum algorithms to solve the hidden shift problem for quadratics
and for functions of large Gowers norm*, fixed arXiv:0911.4724v1 (24 Nov 2009).

This module fixes the objects that the paper's Theorem 2, Theorem 5 and the
abstract main result quantify over:

* `Cube n` — the Boolean cube `Z_2^n`, with `Z_2 = ZMod 2`.
* `agreeChar f g x` — the `±1` character `(-1)^{f(x)+g(x)}` written as
  agreement/disagreement of the two Boolean values (`= +1` iff `f x = g x`).
* `corr f g` — the correlation `⟨f, g⟩ = 2^{-n} Σ_x (-1)^{f(x)+g(x)}` of the
  paper (§2, eq. (2) with `w = 0`), and `disagreeFrac f g = Pr_x[f x ≠ g x]`.
* `fourierCoeff f w` — the Walsh–Hadamard coefficient `\hat F(w)` of eq. (2).
* `QuadPoly n` — a Boolean quadratic polynomial `x Q xᵀ + L xᵀ` over `Z_2`
  (§2, "Review of Boolean quadratic functions"), with `QuadPoly.eval`.
* `HiddenShift f g s` — the hidden-shift promise `g(x) = f(x + s)` (§3).
* `gowersU3 f` — the Gowers `U₃` norm of the `±1` phase of `f` (§4).
* `bent f` — flat Walsh spectrum `|\hat F(w)| = 2^{-n/2}` (§2).

Nothing here asserts an algorithm; the algorithmic statements live in the
sibling claim files, where the papers' robustness arguments are formalised.

The character identity `(-1)^{f+g}` is implemented through agreement rather
than through `sign (f x + g x)` so that no `ZMod 2` sign arithmetic is needed:
over `Z_2`, `f x + g x = 0 ↔ f x = g x` and otherwise it is `1`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HidShiftQuad09.MainResults.SourceModel

open scoped BigOperators
open Finset

/-- The Boolean cube `Z_2^n`. -/
abbrev Cube (n : ℕ) := Fin n → ZMod 2

/-- The `±1` character of a pair of Boolean values at `x`: `+1` iff they agree,
`-1` iff they differ.  This is `(-1)^{f(x)+g(x)}` over `Z_2`. -/
def agreeChar {n : ℕ} (f g : Cube n → ZMod 2) (x : Cube n) : ℝ :=
  if f x = g x then 1 else -1

/-- The fraction of inputs on which `f` and `g` disagree. -/
def disagreeFrac {n : ℕ} (f g : Cube n → ZMod 2) : ℝ :=
  (∑ x : Cube n, if f x = g x then (0 : ℝ) else 1) / (Fintype.card (Cube n) : ℝ)

/-- The correlation `⟨f, g⟩ = 2^{-n} Σ_x (-1)^{f(x)+g(x)}` (paper eq. (2)). -/
def corr {n : ℕ} (f g : Cube n → ZMod 2) : ℝ :=
  (∑ x : Cube n, agreeChar f g x) / (Fintype.card (Cube n) : ℝ)

/-- The Walsh–Hadamard coefficient at frequency `w` (paper eq. (2)):
`\hat F(w) = 2^{-n} Σ_x (-1)^{f(x) + w·x}`. -/
def fourierCoeff {n : ℕ} (f : Cube n → ZMod 2) (w : Cube n) : ℝ :=
  (∑ x : Cube n, agreeChar f (fun y => ∑ i, w i * y i) x) / (Fintype.card (Cube n) : ℝ)

/-- A Boolean quadratic polynomial `x Q xᵀ + L xᵀ` over `Z_2`; `Q` need not be
symmetric or zero-diagonal, matching the all-pairs sum `Σ_{i,j} q_{ij} x_i x_j`
of the paper's Theorem 2. -/
structure QuadPoly (n : ℕ) where
  /-- the quadratic coefficient matrix `q_{i,j}` -/
  Q : Fin n → Fin n → ZMod 2
  /-- the linear coefficient vector `\ell_i` -/
  L : Fin n → ZMod 2

namespace QuadPoly

/-- Evaluation `x ↦ Σ_{i,j} q_{ij} x_i x_j + Σ_i \ell_i x_i` over `Z_2`. -/
def eval {n : ℕ} (p : QuadPoly n) (x : Cube n) : ZMod 2 :=
  (∑ i, ∑ j, p.Q i j * x i * x j) + ∑ i, p.L i * x i

/-- The purely quadratic part (constant/linear parts dropped), used for the
"quadratic form" recovered by Find-Close-Quadratic. -/
def form {n : ℕ} (p : QuadPoly n) : Fin n → Fin n → ZMod 2 := p.Q

/-- Two quadratics define the same quadratic *form* when their `Q` matrices
agree (the linear parts are recovered afterwards by Fourier sampling). -/
def SameForm {n : ℕ} (p q : QuadPoly n) : Prop := p.Q = q.Q

end QuadPoly

/-- `f` is a Boolean quadratic polynomial. -/
def IsQuadratic {n : ℕ} (f : Cube n → ZMod 2) : Prop :=
  ∃ p : QuadPoly n, f = p.eval

/-- `f` has no nonzero period: `f(x + a) = f(x)` for all `x` forces `a = 0`. -/
def HasNoPeriod {n : ℕ} (f : Cube n → ZMod 2) : Prop :=
  ∀ a : Cube n, (∀ x, f (x + a) = f x) → a = 0

/-- The hidden-shift promise: `g(x) = f(x + s)` for all `x` (paper §3). -/
def HiddenShift {n : ℕ} (f g : Cube n → ZMod 2) (s : Cube n) : Prop :=
  ∀ x, g x = f (x + s)

/-- The `±1` phase `F(x) = (-1)^{f(x)}` of a Boolean function. -/
def phase {n : ℕ} (f : Cube n → ZMod 2) (x : Cube n) : ℝ :=
  if f x = 0 then 1 else -1

/-- The Gowers `U₃` norm of the `±1` phase of `f` (paper §4):
`‖f‖_{U₃} = |E_{x,h₁,h₂,h₃} ∏_{S ⊆ {1,2,3}} F(x + Σ_{i∈S} h_i)|^{1/8}`. -/
def gowersU3 {n : ℕ} (f : Cube n → ZMod 2) : ℝ :=
  |(∑ x : Cube n, ∑ h : Fin 3 → Cube n,
      ∏ S : Finset (Fin 3), phase f (x + ∑ i ∈ S, h i)) /
    ((Fintype.card (Cube n) : ℝ) * (Fintype.card (Fin 3 → Cube n) : ℝ))| ^ (1 / 8 : ℝ)

/-- A Boolean function is *bent* when its Walsh spectrum is flat:
`|\hat F(w)| = 2^{-n/2}` for all `w` (§2). -/
def bent {n : ℕ} (f : Cube n → ZMod 2) : Prop :=
  ∀ w : Cube n, |fourierCoeff f w| = (2 : ℝ) ^ (-(n : ℝ) / 2)

/-! ## Basic correlation identities -/

/-- The character is `+1` on agreement and `-1` on disagreement. -/
theorem agreeChar_eq {n : ℕ} (f g : Cube n → ZMod 2) (x : Cube n) :
    agreeChar f g x = 1 - 2 * (if f x = g x then (0 : ℝ) else 1) := by
  unfold agreeChar
  by_cases h : f x = g x <;> simp [h] <;> norm_num

/-- The cube has `2^n` points. -/
theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]

/-- The cube is nonempty, so its cardinality is a nonzero real. -/
theorem card_cube_ne_zero (n : ℕ) : (Fintype.card (Cube n) : ℝ) ≠ 0 := by
  rw [card_cube]
  positivity

/-- Correlation and disagreement fraction are related by `⟨f,g⟩ = 1 - 2 Pr[f≠g]`. -/
theorem corr_eq_one_sub_two_disagree {n : ℕ} (f g : Cube n → ZMod 2) :
    corr f g = 1 - 2 * disagreeFrac f g := by
  unfold corr disagreeFrac
  have hchar : ∀ x : Cube n, agreeChar f g x = 1 - 2 * (if f x = g x then (0 : ℝ) else 1) :=
    fun x => agreeChar_eq f g x
  have hsum : (∑ x : Cube n, agreeChar f g x)
      = (Fintype.card (Cube n) : ℝ) - 2 * ∑ x : Cube n, (if f x = g x then (0 : ℝ) else 1) := by
    calc (∑ x : Cube n, agreeChar f g x)
        = ∑ x : Cube n, (1 - 2 * (if f x = g x then (0 : ℝ) else 1)) := by
          exact Finset.sum_congr rfl (fun x _ => hchar x)
      _ = (∑ x : Cube n, (1 : ℝ))
            - ∑ x : Cube n, 2 * (if f x = g x then (0 : ℝ) else 1) := by
          rw [Finset.sum_sub_distrib]
      _ = (Fintype.card (Cube n) : ℝ)
            - 2 * ∑ x : Cube n, (if f x = g x then (0 : ℝ) else 1) := by
          rw [← Finset.mul_sum]
          simp
  rw [hsum]
  have hc : (Fintype.card (Cube n) : ℝ) ≠ 0 := card_cube_ne_zero n
  field_simp [hc]

/-- The disagreement fraction is a probability. -/
theorem disagreeFrac_bounds {n : ℕ} (f g : Cube n → ZMod 2) :
    0 ≤ disagreeFrac f g ∧ disagreeFrac f g ≤ 1 := by
  constructor
  · unfold disagreeFrac
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x _
      split_ifs <;> norm_num
    · positivity
  · unfold disagreeFrac
    rw [div_le_one (by positivity)]
    calc (∑ x : Cube n, if f x = g x then (0 : ℝ) else 1)
        ≤ ∑ _x : Cube n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          split_ifs <;> norm_num
      _ = (Fintype.card (Cube n) : ℝ) := by simp

/-- Correlations lie in `[-1, 1]`. -/
theorem abs_corr_le_one {n : ℕ} (f g : Cube n → ZMod 2) : |corr f g| ≤ 1 := by
  rw [corr_eq_one_sub_two_disagree]
  have h := disagreeFrac_bounds f g
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Correlation is nonnegative when `f` and `g` agree on at least half the cube. -/
theorem corr_nonneg_of_half_agree {n : ℕ} (f g : Cube n → ZMod 2)
    (h : disagreeFrac f g ≤ 1 / 2) : 0 ≤ corr f g := by
  rw [corr_eq_one_sub_two_disagree]
  linarith

/-! ## The Bernoulli power bound used in the tensor-copy argument -/

/-- Bernoulli's inequality in the form used by the paper: for `0 ≤ ε ≤ 1` and
`k ≥ 1`, `(1 - ε)^k ≥ 1 - k ε`. -/
theorem bernstein_pow (k : ℕ) (ε : ℝ) (hε : ε ≤ 1) :
    1 - (k : ℝ) * ε ≤ (1 - ε) ^ k := by
  have h := one_add_mul_le_pow (a := -ε) (by linarith) k
  simpa [sub_eq_add_neg] using h

/-- Monotonicity of powers on `[0,1]`, used to pass from `1-ε` to `|⟨f,g⟩|`. -/
theorem pow_le_pow_of_le_one {r : ℝ} (k : ℕ) (_hr0 : 0 ≤ r) (_hr1 : r ≤ 1)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ r) : a ^ k ≤ r ^ k := by
  exact pow_le_pow_left₀ ha0 ha k

end Qatlib.Papers.HidShiftQuad09.MainResults.SourceModel
