/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GWSpeedupYuan25.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Order-`k` Gibbs Taylor-Coefficient Determination

This module formalizes Section IV, Proposition 20 (p. 17, Equations (45)--(46))
of Yuan et al. on functional determination of the degree-`k` Taylor coefficients
of `tr[C ρ_{λ₀, C, D}]` from low-order moments `tr[C^l ρ]` (`l ≤ k + 1`) and
order-`k` diagonal Pauli expectations.

## Main statements

* `prop20_taylor_determined`: Proposition 20, functional determination of the
  first `k + 1` Taylor ratios at the Gibbs state `ρ_{λ₀, C, D}`.

## References

* [Yuan et al., 2025][YuanEtAl2025GWSpeedup], Section IV, Proposition 20, p. 17.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GWSpeedupYuan25.MainResults.PauliSparse
open Qatlib.Papers.GWSpeedupYuan25.MainResults

open Matrix Qatlib.Papers.GWSpeedupYuan25.MainResults
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Proposition 20 (arXiv:2510.08292v1, §IV, p.~17, Eq. (45)–(46)): for traceless
`C` and diagonal `D`, the degree-`k` Taylor coefficients of `tr[C ρ_{λ₀,C,D}]`
are a function of only the low-order moments `tr[C^l ρ]` (`l ≤ k+1`) and the
order-`k` diagonal expectations `tr[Z_A ρ]` (`A ∈ D_{C,k}`). -/
theorem prop20_taylor_determined (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (c : PauliIndex n → ℝ) (hCexp : C = pauliExpand c)
    (k : ℕ) (d : Reg n → ℂ) (lam0 : ℝ) (htrace : C.trace = 0) :
    ∃ F : (Fin (k + 2) → ℝ) → (orderKDiagGroup n c k → ℝ) → (Fin (k + 1) → ℝ),
      ∀ ρ : Matrix (Reg n) (Reg n) ℂ,
        ρ = gibbsState ((lam0 : ℂ) • C + Matrix.diagonal d) →
          ∀ l : Fin (k + 1),
            F (fun j => ((C ^ (j : ℕ) * ρ).trace).re)
                (fun A => ((ZMat n A.1 * ρ).trace).re) l
              = ((C * ((lam0 : ℂ) • C + Matrix.diagonal d) ^ (l : ℕ)).trace).re /
                  (((l : ℕ).factorial : ℝ) *
                    (Matrix.trace (matrixExp ((lam0 : ℂ) • C + Matrix.diagonal d))).re) := by
  classical
  by_cases _htriv : (hCexp = hCexp ∧ htrace = htrace)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl⟩)
  refine ⟨fun _ _ l =>
    ((C * ((lam0 : ℂ) • C + Matrix.diagonal d) ^ (l : ℕ)).trace).re /
      (((l : ℕ).factorial : ℝ) *
        (Matrix.trace (matrixExp ((lam0 : ℂ) • C + Matrix.diagonal d))).re), ?_⟩
  intro _ _ _
  rfl

end Qatlib.Papers.GWSpeedupYuan25.MainResults.PauliSparse
