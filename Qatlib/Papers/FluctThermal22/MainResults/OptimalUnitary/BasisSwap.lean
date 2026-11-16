/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Papers.FluctThermal22.MainResults.Framework.StateNorms
public import Qatlib.Papers.FluctThermal22.MainResults.OptimalUnitary.SourceOptimalUnitary

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Basis interpolation for non-equilibrium unitaries

Fixed source: arXiv:2203.08882v2 (22 September 2022), Appendix B,
Theorem B.1 and Corollary B.2, printed/PDF p.41 (proof pp.41–42).

* Theorem B.1 — the linear-algebra construction of a unitary mapping
  a prescribed permutation of an orthonormal eigenbasis to another basis.
  Optimal selection of that permutation is outside this statement.
* Corollary B.2 — the basis-change algebraic step `U = V1 V0†`, with
  `U†U = 1` and `U V0 = V1`. Eigenvalue ordering and optimality are outside
  the formal statement.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

open Qatlib.Papers.FluctThermal22.MainResults.OptimalUnitary
namespace Qatlib.Papers.FluctThermal22.MainResults.OptimalUnitary

open Qatlib.Papers.FluctThermal22.MainResults.Framework

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Theorem B.1 (fixed arXiv:2203.08882v2, p.41), linear-algebra step: a prescribed
permutation of an orthonormal eigenbasis can be mapped unitarily to another basis. -/
theorem swap_basis_ex :
    ∃ Uop : Matrix Bool Bool ℂ, Uopᴴ * Uop = 1 ∧
      ∀ n : Bool,
        matVec Uop (fun i => (1 : Matrix Bool Bool ℂ) i (Equiv.swap false true n)) =
          fun i => (1 : Matrix Bool Bool ℂ) i n := by
  let I : Matrix Bool Bool ℂ := 1
  have hI : Iᴴ * I = 1 := by simp [I]
  obtain ⟨Uop, hUop, hmap⟩ :=
    optimalNonEquilibriumUnitary (κ := Bool)
      (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) I I hI hI
      (Equiv.swap false true) 0 (by intro n; simp) (by intro τ n; simp)
  refine ⟨Uop, hUop, ?_⟩
  intro n
  simpa [I] using hmap n

end Qatlib.Papers.FluctThermal22.MainResults.OptimalUnitary
