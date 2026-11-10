/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPolyShor07.MainResults.Definitions.ElementaryUnitaries
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Synthesis

open Definitions Matrix
open scoped BigOperators

def diag2 (u v : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then (if i.val = 0 then u else v) else 0

theorem Mn_eq_blockDiag5 :
    Mn = blockDiag5 bFib aFib (fun i j =>
      match i.val, j.val with
      | 0, 0 => eFib
      | 0, 1 => dFib
      | 1, 0 => dFib
      | 1, 1 => cFib
      | _, _ => 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mn, blockDiag5]

theorem Mdiag_eq_blockDiag5 (α : ℝ) :
    Mdiag α = blockDiag5 (Complex.exp ((α / 2) * Complex.I))
      (Complex.exp ((α / 2) * Complex.I))
      (diag2 (Complex.exp ((α / 2) * Complex.I)) (Complex.exp (-(α / 2) * Complex.I))) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mdiag, blockDiag5, diag2]

theorem lemma3_diagBlock (α : ℝ) :
    ∃ (r : ℕ) (P : Matrix (Fin 5) (Fin 5) ℂ) (φ1 φ2 : ℂ),
      (∃ l : List (Matrix (Fin 5) (Fin 5) ℂ),
        l.length ≤ r ∧
          (∀ M ∈ l, (∃ α' : ℝ, M = Mdiag α') ∨ M = Mn) ∧
            P = l.prod) ∧
        P = blockDiag5 φ1 φ2
          (diag2 (Complex.exp ((α / 2) * Complex.I)) (Complex.exp (-(α / 2) * Complex.I))) := by
  refine ⟨1, Mdiag α, Complex.exp ((α / 2) * Complex.I), Complex.exp ((α / 2) * Complex.I),
    ⟨[Mdiag α], by simp, ?_, by simp⟩, Mdiag_eq_blockDiag5 α⟩
  intro M hM
  rw [List.mem_singleton] at hM
  subst hM
  exact Or.inl ⟨α, rfl⟩

end Qatlib.Papers.JonesPolyShor07.MainResults.Synthesis
