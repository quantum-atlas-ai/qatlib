/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPoly05.MainResults.CircuitCompilation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.JonesPoly05.MainResults.PathDefs

open Qatlib.Papers.JonesPoly05.MainResults.Kauffman
open Qatlib.Papers.JonesPoly05.MainResults.CircuitCompilation

theorem lemma31_trace_closure
    {n : ℕ} {A d : ℂ} (hd : d ≠ 0) (B : BraidWord n) (T : ℂ)
    (hT : T = markovTrace A d B) :
    jonesTrace A d B = (-A) ^ (3 * writhe B : ℤ) * d ^ ((n : ℤ) - 1) * T := by
  rw [jonesTrace_eq_markovTrace hd B, hT]

theorem lemma31_matrix_trace
    (φ : ∀ n : ℕ, Fin (n - 1) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    {n : ℕ} {A d : ℂ} (hd : d ≠ 0) (B : BraidWord n)
    (hmarkov : Matrix.trace (braidOperator φ B) = markovTrace A d B) :
    jonesTrace A d B = (-A) ^ (3 * writhe B : ℤ) * d ^ ((n : ℤ) - 1) *
      Matrix.trace (braidOperator φ B) := by
  rw [jonesTrace_eq_markovTrace hd B, ← hmarkov]

theorem lemma31_trace_closure_of_matrix
    (φ : ∀ n : ℕ, Fin (n - 1) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    {n : ℕ} {A d : ℂ} (hd : d ≠ 0) (B : BraidWord n)
    (hmarkov : Matrix.trace (braidOperator φ B) = markovTrace A d B) :
    jonesTrace A d B = (-A) ^ (3 * writhe B : ℤ) * d ^ ((n : ℤ) - 1) *
      Matrix.trace (braidOperator φ B) :=
  lemma31_trace_closure hd B (Matrix.trace (braidOperator φ B)) hmarkov

end Qatlib.Papers.JonesPoly05.MainResults.PathDefs
