/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiagPowerBQP06.MainResults.Defs

open Matrix

structure DiagEntryInstance where

  N : ℕ

  A : Matrix (Fin N) (Fin N) ℝ

  hA : A.IsHermitian

  b : ℝ

  hb : 0 ≤ b

  m : ℕ

  j : Fin N

  g : ℝ

  ε : ℝ

  hε : 0 < ε

def DiagEntryYes (I : DiagEntryInstance) : Prop :=
  I.g + I.ε * I.b ^ I.m ≤ (I.A ^ I.m) I.j I.j

def DiagEntryNo (I : DiagEntryInstance) : Prop :=
  (I.A ^ I.m) I.j I.j ≤ I.g - I.ε * I.b ^ I.m

def DiagEntryPromise (I : DiagEntryInstance) : Prop :=
  DiagEntryYes I ∨ DiagEntryNo I

def PolynomialGrowth (f : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n, f n ≤ (n + 1) ^ c + c

def InstanceSize (I : DiagEntryInstance) : ℕ := I.N + I.m

def DiagonalEntryEstimationInBQP : Prop :=
  ∃ (decide : DiagEntryInstance → Bool) (cost : DiagEntryInstance → ℕ),
    (∃ c : ℕ, ∀ I, cost I ≤ (InstanceSize I + 1) ^ c + c) ∧
      ∀ I, DiagEntryPromise I → (decide I = true ↔ DiagEntryYes I)

def DiagonalEntryEstimationBQPHard : Prop :=
  ∀ (L : List Bool → Prop) (accept : List Bool → ℝ),
    (∀ x, L x → 2 / 3 ≤ accept x) →
      (∀ x, ¬ L x → accept x ≤ 1 / 3) →
        ∃ (enc : List Bool → DiagEntryInstance) (c : ℕ),
          (∀ x, (enc x).N ≤ (x.length + 1) ^ c + c ∧
            (enc x).m ≤ (x.length + 1) ^ c + c) ∧
            (∀ x, L x → DiagEntryNo (enc x)) ∧
              (∀ x, ¬ L x → DiagEntryYes (enc x))

def DiagonalEntryEstimationBQPHardZeroOne : Prop :=
  ∀ (L : List Bool → Prop) (accept : List Bool → ℝ),
    (∀ x, L x → 2 / 3 ≤ accept x) →
      (∀ x, ¬ L x → accept x ≤ 1 / 3) →
        ∃ (enc : List Bool → DiagEntryInstance) (c : ℕ),
          (∀ x, (enc x).N ≤ (x.length + 1) ^ c + c ∧
            (enc x).m ≤ (x.length + 1) ^ c + c) ∧
            (∀ x, ∀ i k, (enc x).A i k = -1 ∨ (enc x).A i k = 0 ∨
              (enc x).A i k = 1) ∧
              (∀ x, L x → DiagEntryNo (enc x)) ∧
                (∀ x, ¬ L x → DiagEntryYes (enc x))

end Qatlib.Papers.DiagPowerBQP06.MainResults.Defs
