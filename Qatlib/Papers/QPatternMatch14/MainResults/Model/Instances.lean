/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPatternMatch14.MainResults.Model.PatternStrings
import Qatlib.Papers.QPatternMatch14.MainResults.Model.QueryModel

/-!
# Concrete input instances and promise predicates

This file packages the input distributions and promises of Montanaro, *Quantum
pattern matching fast on average* (arXiv:1408.1816v3): the pattern-matching input
of Theorem 2 / Proposition 8 (p. 3, p. 9), the hidden-shift input of Theorem 4
(p. 6), the unique-match input of Theorem 5 (p. 8), and the pattern-detection
input of Lemma 10, Lemma 11, Theorem 12 and Proposition 13 (Section 4, p. 10).
-/

/-!
# Instances

Paper-layer definitions and source results for QPatternMatch14.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.QPatternMatch14.MainResults.Model

/-- A pattern-matching instance: a text `T : [n]^d → A` and pattern `P : [m]^d → A`. -/
structure PatternInput (d n m : ℕ) (A : Type*) where
  /-- The text. -/
  T : DStr d n A
  /-- The pattern. -/
  P : DStr d m A

/-- The promise of Theorem 2 (arXiv:1408.1816v3, p. 3): both strings have
injectivity length at most `ν ≤ m/2`, and every non-matching offset disagrees on
at least a `γ` fraction of positions. -/
def theorem2Promise {d n m : ℕ} {A : Type*} [DecidableEq A] (hmn : m ≤ n)
    (ν : ℕ) (hνT : ν ≤ n) (hνP : ν ≤ m) (γ : ℝ) (inp : PatternInput d n m A) : Prop :=
  injectivityLengthAtMost inp.T ν hνT ∧ injectivityLengthAtMost inp.P ν hνP ∧
    ν ≤ m / 2 ∧
    ∀ s, ¬ matchesAt hmn inp.T inp.P s → γ ≤ mismatchFraction hmn inp.T inp.P s

/-- The output specification of Theorem 2: output a matching offset if one
exists, and `none` otherwise. -/
def patternSpec {d n m : ℕ} {A : Type*} (hmn : m ≤ n) (inp : PatternInput d n m A) :
    Option (Coord d (n - m + 1)) → Prop
  | some s => matchesAt hmn inp.T inp.P s
  | none => ∀ s, ¬ matchesAt hmn inp.T inp.P s

/-- The promise of Theorem 5 (arXiv:1408.1816v3, p. 8): the pattern matches the
text at some (necessarily unique) offset, and both injectivity lengths are at
most `ν ≤ m/2`. -/
def theorem5Promise {d n m : ℕ} {A : Type*} [DecidableEq A] (hmn : m ≤ n)
    (ν : ℕ) (hνT : ν ≤ n) (hνP : ν ≤ m) (inp : PatternInput d n m A) : Prop :=
  injectivityLengthAtMost inp.T ν hνT ∧ injectivityLengthAtMost inp.P ν hνP ∧
    ν ≤ m / 2 ∧ ∃ i, matchesAt hmn inp.T inp.P i

/-- Good random instances of Proposition 8 (arXiv:1408.1816v3, p. 9): the text
has injectivity length at most `ν`, and every non-matching offset disagrees on at
least a `1/4` fraction (obtained from Lemma 7 with the parameters of p. 9). -/
def proposition8Good {d n m : ℕ} {A : Type*} [DecidableEq A] (hmn : m ≤ n)
    (ν : ℕ) (hνT : ν ≤ n) (inp : PatternInput d n m A) : Prop :=
  injectivityLengthAtMost inp.T ν hνT ∧
    ∀ s, ¬ matchesAt hmn inp.T inp.P s →
      (1 / 4 : ℝ) ≤ mismatchFraction hmn inp.T inp.P s

/-- The "good" random instances of Theorem 1 (arXiv:1408.1816v3, p. 2, derived
on p. 9): the text has some injectivity length at most `ν`, and every
non-matching offset disagrees on at least a `1/4` fraction of positions. -/
def theorem1Good {d n m : ℕ} {A : Type*} [DecidableEq A] (hmn : m ≤ n)
    (inp : PatternInput d n m A) : Prop :=
  ∃ (ν : ℕ) (hν : ν ≤ n), injectivityLengthAtMost inp.T ν hν ∧
    ∀ s, ¬ matchesAt hmn inp.T inp.P s →
      (1 / 4 : ℝ) ≤ mismatchFraction hmn inp.T inp.P s

/-- The pattern-detection specification (arXiv:1408.1816v3, p. 10): decide
whether the pattern matches somewhere. -/
def patternDetectionSpec {d n m : ℕ} {A : Type*} (hmn : m ≤ n) (inp : PatternInput d n m A) :
    Bool → Prop
  | true => ∃ s, matchesAt hmn inp.T inp.P s
  | false => ∀ s, ¬ matchesAt hmn inp.T inp.P s

/-- Cyclic addition in `Z_{2^k}` applied coordinatewise (Theorem 4, arXiv:1408.1816v3, p. 6). -/
def addCoord {d : ℕ} (k : ℕ) (s x : Coord d (2 ^ k)) : Coord d (2 ^ k) :=
  fun i => ⟨((s i).val + (x i).val) % 2 ^ k,
    Nat.mod_lt _ (pow_pos (by norm_num : 0 < 2) k)⟩

/-- A hidden-shift instance over `Z_{2^k}^d`: injective functions `f`, `g` and a
hidden shift `s` with `g(x) = f(x+s)` for almost every `x` (Theorem 4, p. 6). -/
structure HiddenShiftInput (d k : ℕ) (A : Type*) where
  /-- The first function `f : Z_{2^k}^d → A`. -/
  f : Coord d (2 ^ k) → A
  /-- The second function `g : Z_{2^k}^d → A`. -/
  g : Coord d (2 ^ k) → A
  /-- The hidden shift `s`. -/
  s : Coord d (2 ^ k)

/-- The fraction of positions where `g` and the shift of `f` disagree (Theorem 4, arXiv:1408.1816v3, p. 6). -/
noncomputable def hiddenShiftMismatchFraction {d k : ℕ} {A : Type*} [DecidableEq A]
    (inp : HiddenShiftInput d k A) : ℝ :=
  (Fintype.card { x : Coord d (2 ^ k) // inp.g x ≠ inp.f (addCoord k inp.s x) } : ℝ) /
    ((2 ^ k) ^ d : ℕ)

/-- The promise of Theorem 4 (arXiv:1408.1816v3, p. 6): both functions are
injective and the mismatch fraction is `O(n^{-2} 2^{-√((2 log₂ 3) dn)})`. -/
def theorem4Promise {d k : ℕ} {A : Type*} [DecidableEq A]
    (inp : HiddenShiftInput d k A) : Prop :=
  Function.Injective inp.f ∧ Function.Injective inp.g ∧
    ∃ C : ℝ, 0 < C ∧
      hiddenShiftMismatchFraction inp ≤
        C * ((k : ℝ) ^ (-2 : ℤ)) * (expLogTerm (d : ℝ) (k : ℝ))⁻¹

end Qatlib.Papers.QPatternMatch14.MainResults.Model
