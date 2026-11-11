/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GateEffSim12.MainResults.CompressedEncoding
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# ErrorFreeMeasurement — Theorem 5.3 of arXiv:1211.4637v2

Fixed paper version: arXiv:1211.4637v2 (5 April 2013), PDF SHA-256
`aef583fed3675ee75a251ed7438ab99cb4c16b34697dd8f4293f3d39d07d471d`.
Theorem 5.3 and Eqs. (32)–(39) are on pp. 17–19; Alg. 5.2 is on p. 16.

The theorem is the error-free part of §5: assume the uncompressed and
compressed states before the final measurement have matching amplitudes on
low-Hamming-weight strings, Eqs. (32)–(33), and that the measurement is exact
(`U_n` implemented exactly).  Then the recursive measurement Alg. 5.2 exactly
simulates the uncompressed `R^{⊗m}` measurement: every measurement result has
the same probability, and the post-measurement target state agrees.

Formal model: a state is an amplitude function `α → T → ℂ`, where `α` indexes
the computational basis of the control block(s) and `T` the target basis.
`compress enc` is the isometry induced by the encoding `x ↦ enc x` of
Eqs. (32)–(33); `applyStep sel` is the post-measurement (partial) state of a
zero/non-zero block measurement with zero-set `sel`; `runSteps` iterates the
recursive measurement to depth `K`.

The core one-step transport `compress_applyStep` is proved: the compressed and
uncompressed block measurements commute with the encoding isometry, which is
the induction step of the paper's proof (Eqs. (35)–(39)).  `runSteps_compress`
iterates it over all recursion levels.  Theorem 5.3 is then the pair
"post-selected states agree" and "outcome probabilities agree"; both parts are
proved.  The second uses `prob_compress`, the squared-norm isometry for an
injective encoding.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GateEffSim12.MainResults.ErrorFreeMeasurement

variable {X B T : Type} [Fintype X] [Fintype B] [Fintype T]

/-- The compressed amplitude function induced by an encoding `enc`: the
coefficient of `|enc x>|w_x>` is the coefficient of `|x>|w_x>`.  This is the
state-level content of Eqs. (32)–(33). -/
def compress [DecidableEq B] (enc : X → B) (ψ : X → T → ℂ) : B → T → ℂ :=
  fun b t => ∑ x, if enc x = b then ψ x t else 0

/-- Post-measurement state of a block measurement whose "zero" set is `sel`:
outcomes outside `sel` are kept. -/
def applyStep (sel : X → Bool) (ψ : X → T → ℂ) : X → T → ℂ :=
  fun x t => if sel x then ψ x t else 0

/-- Iterate `K` levels of a recursive measurement with zero-sets `sel i`. -/
def runSteps (sel : ℕ → X → Bool) (K : ℕ) (ψ : X → T → ℂ) : X → T → ℂ :=
  (List.range K).foldl (fun ψ i => applyStep (sel i) ψ) ψ

/-- Outcome probability (squared norm) of an amplitude function. -/
def prob (ψ : X → T → ℂ) : ℝ := ∑ x, ∑ t, ‖ψ x t‖ ^ 2

/-- **One-step transport of a block measurement** (the induction step of
Theorem 5.3, Eqs. (35)–(39) of arXiv:1211.4637v2, pp. 18–19): if the
compressed zero-set `selB` agrees with the uncompressed zero-set `selX` under
the encoding, then the compressed block measurement commutes with
compression. -/
theorem compress_applyStep [DecidableEq B]
    (enc : X → B) (selX : X → Bool) (selB : B → Bool)
    (hcompat : ∀ x, selB (enc x) = selX x) (ψ : X → T → ℂ) :
    compress enc (applyStep selX ψ) = applyStep selB (compress enc ψ) := by
  funext b t
  cases hsb : selB b with
  | true =>
      simp only [compress, applyStep, hsb, if_true]
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases hx : enc x = b
      · have hsel : selX x = true := by
          have h := hcompat x
          rw [hx, hsb] at h
          exact h.symm
        simp [hx, hsel]
      · simp [hx]
  | false =>
      simp only [compress, applyStep, hsb, if_false]
      refine Finset.sum_eq_zero ?_
      intro x _
      by_cases hx : enc x = b
      · have hsel : selX x = false := by
          have h := hcompat x
          rw [hx, hsb] at h
          exact h.symm
        simp [hx, hsel]
      · simp [hx]

/-- One unfolding step of `runSteps`. -/
theorem runSteps_succ (sel : ℕ → X → Bool) (K : ℕ) (ψ : X → T → ℂ) :
    runSteps sel (K + 1) ψ = applyStep (sel K) (runSteps sel K ψ) := by
  simp [runSteps, List.range_succ, List.foldl_append]

/-- **Iterated transport** of the recursive measurement: if the compressed
zero-set of every recursion level agrees with the uncompressed one, then the
whole depth-`K` run commutes with compression.  This is the induction behind
Theorem 5.3. -/
theorem runSteps_compress [DecidableEq B]
    (enc : X → B) (selX : ℕ → X → Bool) (selB : ℕ → B → Bool)
    (hcompat : ∀ i x, selB i (enc x) = selX i x) (K : ℕ) (ψ : X → T → ℂ) :
    compress enc (runSteps selX K ψ) = runSteps selB K (compress enc ψ) := by
  induction K with
  | zero => simp [runSteps]
  | succ K ih =>
      rw [runSteps_succ, runSteps_succ,
        compress_applyStep enc (selX K) (selB K) (hcompat K) (runSteps selX K ψ), ih]

/-- Squared norm of a sum over a finset with at most one element. -/
lemma norm_sum_sq_of_card_le_one {s : Finset X} (hs : s.card ≤ 1) (f : X → ℂ) :
    ‖∑ x ∈ s, f x‖ ^ 2 = ∑ x ∈ s, ‖f x‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [Finset.card_eq_zero.1 h0]
    simp
  · have h1 : s.card = 1 := Nat.le_antisymm hs hpos
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h1
    simp

/-- An injective encoding preserves the outcome probability (squared norm). -/
theorem prob_compress [DecidableEq B] (enc : X → B) (hinj : Function.Injective enc)
    (ψ : X → T → ℂ) : prob (compress enc ψ) = prob ψ := by
  simp only [prob, compress]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro t _
  have h₁ : ∀ b : B, ‖∑ x, (if enc x = b then ψ x t else 0)‖ ^ 2
      = ∑ x ∈ Finset.univ.filter (fun x => enc x = b), ‖ψ x t‖ ^ 2 := by
    intro b
    rw [← Finset.sum_filter]
    refine norm_sum_sq_of_card_le_one ?_ (fun x => ψ x t)
    rw [Finset.card_le_one]
    intro a ha c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hc
    exact hinj (ha.trans hc.symm)
  calc
    ∑ b : B, ‖∑ x, (if enc x = b then ψ x t else 0)‖ ^ 2
        = ∑ b : B, ∑ x ∈ Finset.univ.filter (fun x => enc x = b), ‖ψ x t‖ ^ 2 :=
          Finset.sum_congr rfl (fun b _ => h₁ b)
    _ = ∑ x : X, ‖ψ x t‖ ^ 2 := by
          simpa using
            (Finset.sum_fiberwise (Finset.univ : Finset X) enc (fun x => ‖ψ x t‖ ^ 2))

/-- **Theorem 5.3 (error-free simulation), arXiv:1211.4637v2, p. 18.**
Assume the uncompressed state `ψ` and the compressed state `φ` are related by
the encoding isometry (`hinit`, Eqs. (32)–(33)), that the encoding is
injective, and that at every level `i` of the recursion the compressed
zero-set `selB i` matches the uncompressed zero-set `selX i` under the
encoding (`hcompat`, Eqs. (35)–(39)).  Then, after running the recursive
measurement to depth `K`:

1. the post-measurement amplitude functions agree under compression (so the
   target-register states match), and
2. the outcome probabilities agree.

Part 1 is `runSteps_compress`.  Part 2 is `prob_compress`, the squared-norm
isometry `prob (compress enc ψ) = prob ψ` for injective `enc`; its proof uses
that the fibres of `enc` are singletons and sums them by `Finset.sum_fiberwise`.
This follows the paper's induction on the recursion level (pp. 18–19), where
the compressed and uncompressed measurement operators act on states with the
same amplitude weights `γ_x` (Eqs. (35)–(39)). -/
theorem theorem_5_3 [DecidableEq B]
    (enc : X → B) (hini : Function.Injective enc)
    (ψ : X → T → ℂ) (φ : B → T → ℂ) (hinit : compress enc ψ = φ)
    (K : ℕ) (selX : ℕ → X → Bool) (selB : ℕ → B → Bool)
    (hcompat : ∀ i x, selB i (enc x) = selX i x) :
    (compress enc (runSteps selX K ψ) = runSteps selB K φ) ∧
      (prob (runSteps selB K φ) = prob (runSteps selX K ψ)) := by
  constructor
  · rw [← hinit]
    exact runSteps_compress enc selX selB hcompat K ψ
  · rw [← hinit, ← runSteps_compress enc selX selB hcompat K ψ]
    exact prob_compress enc hini (runSteps selX K ψ)

end Qatlib.Papers.GateEffSim12.MainResults.ErrorFreeMeasurement
