/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

open Matrix

abbrev F1024 := GaloisField 2 10

noncomputable instance : Fintype F1024 := Fintype.ofFinite F1024

noncomputable instance : DecidableEq F1024 := Classical.decEq _

/-- Computes the cardinality of `F1024` as two to the tenth power. -/
theorem card_F1024 : Fintype.card F1024 = 2 ^ 10 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card (p := 2) (n := 10) (by norm_num)

noncomputable def f1024Trace : F1024 → ZMod 2 := Algebra.trace (ZMod 2) F1024

def qPhase : ZMod 2 → ℂ := fun b => if b = 0 then 1 else -1

/-- Shows that the binary phase at zero equals one. -/
theorem qPhase_zero : qPhase 0 = 1 := by simp [qPhase]

/-- Shows that the binary phase at one equals minus one. -/
theorem qPhase_one : qPhase 1 = -1 := by simp [qPhase]

noncomputable def quditX : F1024 → Matrix F1024 F1024 ℂ := fun β =>
  Matrix.of fun i j => if i = j + β then 1 else 0

noncomputable def quditZ : F1024 → Matrix F1024 F1024 ℂ := fun γ =>
  Matrix.diagonal fun η => qPhase (f1024Trace (γ * η))

noncomputable def quditDiagGate : F1024 → ℕ → Matrix F1024 F1024 ℂ := fun β r =>
  Matrix.diagonal fun γ =>
    Complex.exp (Complex.I * Real.pi * ((f1024Trace (β * γ ^ r)).val : ℝ))

noncomputable def u1SeventhPhase : F1024 → ℂ := fun γ =>
  Complex.exp (Complex.I * Real.pi * ((f1024Trace (γ ^ 7)).val : ℝ))

noncomputable def u1Seventh : Matrix F1024 F1024 ℂ := Matrix.diagonal u1SeventhPhase

def IsQuditPauli (M : Matrix F1024 F1024 ℂ) : Prop :=
  ∃ (a : ℕ) (β γ : F1024), M = ((Complex.I : ℂ) ^ a) • (quditX β * quditZ γ)

def IsQuditClifford (U : Matrix F1024 F1024 ℂ) : Prop :=
  ∀ P, IsQuditPauli P → IsQuditPauli (U * P * Uᴴ)

def InQuditThirdLevel (U : Matrix F1024 F1024 ℂ) : Prop :=
  ∀ P, IsQuditPauli P → IsQuditClifford (U * P * Uᴴ)

noncomputable def quditXVec {n : ℕ} (v : Fin n → F1024) :
    Matrix (Fin n → F1024) (Fin n → F1024) ℂ :=
  Matrix.of fun w w' => if w = w' + v then 1 else 0

noncomputable def quditZVec {n : ℕ} (w : Fin n → F1024) :
    Matrix (Fin n → F1024) (Fin n → F1024) ℂ :=
  Matrix.diagonal fun u => qPhase (∑ i, f1024Trace (w i * u i))

noncomputable def tensorDiagGate {n : ℕ} (f : F1024 → ℂ) :
    Matrix (Fin n → F1024) (Fin n → F1024) ℂ :=
  Matrix.diagonal fun u => ∏ j, f (u j)

end Qatlib.Papers.MagicDistill24.Triorthogonal
