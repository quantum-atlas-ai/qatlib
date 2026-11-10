/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Classical
attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.QLattice03.MainResults

abbrev DCPRegister (N : ℕ) := ℤ × ℤ

def SolvesDCP (A : ∀ N : ℕ, DCPRegister N → ℤ) : Prop :=
  ∀ (N : ℕ) (r : DCPRegister N), A N r = r.2 - r.1

structure TwoPointRegister (n M : ℕ) where
  a : Fin n → Fin M
  a' : Fin n → Fin M

def TwoPointRegister.delta {n M : ℕ} (r : TwoPointRegister n M) : Fin n → ℤ :=
  fun i => (r.a' i : ℤ) - (r.a i : ℤ)

def SolvesTwoPoint (A : ∀ n M : ℕ, TwoPointRegister n M → (Fin n → ℤ)) : Prop :=
  ∀ (n M : ℕ) (r : TwoPointRegister n M), A n M r = r.delta

abbrev LatticeBasis (n : ℕ) := Fin n → Fin n → ℤ

def IsLatticeVector {n : ℕ} (b : LatticeBasis n) (v : Fin n → ℤ) : Prop :=
  ∃ c : Fin n → ℤ, ∀ j : Fin n, v j = ∑ i : Fin n, c i * b i j

def normsq {n : ℕ} (v : Fin n → ℤ) : ℝ := ∑ i : Fin n, (v i : ℝ) ^ 2

noncomputable def norm {n : ℕ} (v : Fin n → ℤ) : ℝ := Real.sqrt (normsq v)

def IsUniqueShortest {n : ℕ} (γ : ℕ → ℝ) (b : LatticeBasis n) (u : Fin n → ℤ) : Prop :=
  IsLatticeVector b u ∧ u ≠ 0 ∧
    ∀ v : Fin n → ℤ, IsLatticeVector b v → v ≠ 0 →
      (¬ ∃ k : ℤ, ∀ j, v j = k * u j) → γ n * norm u ≤ norm v

def SolvesUniqueSVP (γ : ℕ → ℝ)
    (A : ∀ n : ℕ, LatticeBasis n → (Fin n → ℤ)) : Prop :=
  ∀ (n : ℕ) (b : LatticeBasis n) (u : Fin n → ℤ), IsUniqueShortest γ b u → A n b = u

def HidesSlope (N : ℕ) (f : ZMod N × Bool → Bool) (s : ZMod N) : Prop :=
  ∀ p q : ZMod N × Bool, f p = f q ↔ q = p ∨ q = (p.1 + s, !p.2)

def SolvesDihedralHSP (A : ∀ N : ℕ, (ZMod N × Bool → Bool) → ZMod N) : Prop :=
  ∀ (N : ℕ) (f : ZMod N × Bool → Bool) (s : ZMod N), HidesSlope N f s → A N f = s

def SubsetSumLegal (N r : ℕ) (a : Fin r → ZMod N) (t : ZMod N) : Prop :=
  ∃ B : Finset (Fin r), ∑ i ∈ B, a i = t

abbrev SubsetSumRoutine := ∀ (N r : ℕ), (Fin r → ZMod N) → ZMod N → Option (Finset (Fin r))

noncomputable def legalCard (N r : ℕ) [NeZero N] : ℕ :=
  Fintype.card {p : (Fin r → ZMod N) × ZMod N // SubsetSumLegal N r p.1 p.2}

noncomputable def solvedCard (S : SubsetSumRoutine) (N r : ℕ) [NeZero N] : ℕ :=
  Fintype.card {p : (Fin r → ZMod N) × ZMod N //
    SubsetSumLegal N r p.1 p.2 ∧ (S N r p.1 p.2).isSome}

def SolvesSubsetSum (S : SubsetSumRoutine) : Prop :=
  ∃ (r : ℕ → ℕ) (frac : ℕ → ℝ), (∀ N, 0 < frac N) ∧
    ∀ N : ℕ, ∀ (hN : 0 < N),
      frac N * (@legalCard N (r N) ⟨Nat.pos_iff_ne_zero.mp hN⟩ : ℝ) ≤
        (@solvedCard S N (r N) ⟨Nat.pos_iff_ne_zero.mp hN⟩ : ℝ)

end Qatlib.Papers.QLattice03.MainResults
