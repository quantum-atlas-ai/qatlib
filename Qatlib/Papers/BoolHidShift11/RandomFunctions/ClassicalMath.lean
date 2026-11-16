/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier.SourceInfluenceFourier
public import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery

@[expose] public section


/-! # Preserved complete legacy mathematical components

These definitions and conditional estimates retain their complete original
mathematics. Free success/query fields are not an oracle algorithm; scalar
amplification estimates are not a repetition or termination proof.
-/
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel
open Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier
open scoped BigOperators ENNReal
open Qatlib.Concepts.QueryComplexity.DegreeMethod
namespace Qatlib.Papers.BoolHidShift11.RandomFunctions.ClassicalMath

def pairwiseDiff {n k : ℕ} (X : Fin k → Reg n) : Finset (Reg n) :=
  (Finset.univ : Finset (Fin k × Fin k)).image (fun p => regXor (X p.1) (X p.2))

/-- `|S_k| ≤ k²`: there are only `k²` ordered pairs of indices. This is the
denominator estimate underlying equation (3) of Lemma 2. -/
theorem differenceCount {n k : ℕ} (X : Fin k → Reg n) :
    (pairwiseDiff X).card ≤ k ^ 2 := by
  calc
    (pairwiseDiff X).card ≤ (Finset.univ : Finset (Fin k × Fin k)).card :=
      Finset.card_image_le
    _ = k ^ 2 := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      ring

/-! ### The arithmetic core of the lower bound -/

/-- If the success probability bound `(t² + 1)/(2^n - t²)` of Lemma 2 is at
least `1/2`, then `2^n ≤ 3t² + 2`; equivalently `t ≥ sqrt((2^n - 2)/3)`, i.e.
`t ∈ Ω(2^{n/2})`. -/
theorem queryArithmetic {n t : ℕ}
    (hden : (t : ℝ) ^ 2 < (2 : ℝ) ^ n)
    (hsucc : (1 / 2 : ℝ) ≤
      ((t : ℝ) ^ 2 + 1) / ((2 : ℝ) ^ n - (t : ℝ) ^ 2)) :
    (2 : ℝ) ^ n ≤ 3 * (t : ℝ) ^ 2 + 2 := by
  have hden_pos : (0 : ℝ) < (2 : ℝ) ^ n - (t : ℝ) ^ 2 := by linarith
  have h1 : (1 / 2 : ℝ) * ((2 : ℝ) ^ n - (t : ℝ) ^ 2)
      ≤ (t : ℝ) ^ 2 + 1 := by
    exact (le_div_iff₀ hden_pos).mp hsucc
  linarith

/-! ### The classical query model -/

/-- The oracle induced by a pair of functions `g(x) = f(x+s)`: the Boolean
first component selects `f` (`false`) or `g` (`true`). -/
def oracleOf {n : ℕ} (f : Reg n → Bool) (s : Reg n) : Bool × Reg n → Bool :=
  fun q => if q.1 then f (regXor q.2 s) else f q.2

/-- The average success probability of a randomized classical query tree over
the uniform distribution on `(f, s)` (functions `Reg n → Bool` times shifts
`Reg n`), matching the "uniformly random instance" of Lemma 2. -/
noncomputable def avgSuccess {n : ℕ}
    (prog : PMF (BoolQueryTree (Bool × Reg n) (Reg n))) : ℝ :=
  (∑ f : Reg n → Bool, ∑ s : Reg n,
      (BoolQueryTree.SuccessProb prog (oracleOf f s) (fun out => out = s)).toReal)
    / ((Fintype.card (Reg n → Bool) : ℝ) * (Fintype.card (Reg n) : ℝ))


end Qatlib.Papers.BoolHidShift11.RandomFunctions.ClassicalMath
