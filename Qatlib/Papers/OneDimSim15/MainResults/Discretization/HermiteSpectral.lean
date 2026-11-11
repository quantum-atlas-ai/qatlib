/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneDimSim15.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# OneDimSim15 — Appendix A: spectral properties of the discrete QHO

Claims `c008`-`c013` of the fixed source arXiv:1503.06319v2:

* Lemma 1 (p. 15, Eq. A7): Hermite-function tails;
* Lemma 2 (p. 16, Eq. A9): position moments;
* Corollary 1 (p. 16, Eq. A17): almost orthonormality;
* Lemma 3 (p. 17, Eq. A26): momentum moments;
* Lemma 4 (p. 17, Eq. A30): mixed momentum-position moments;
* Corollary 2 (p. 18, Eq. A35): low-energy spectral residual.

All statements use the paper's `nu_1(N) = exp(-Omega(N))` vocabulary: the
right-hand side is always an explicit `exp(-beta N)`, with `beta > 0` and the
constant `c` of the paper's low-energy condition `n <= c N`.
The six statements are recorded below as `Prop`-valued definitions; their
proofs are not formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OneDimSim15.MainResults.Discretization

open Qatlib.Papers.OneDimSim15.MainResults
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Fixed arXiv:1503.06319v2, Lemma 1 (p. 15, Eq. (A7)): for every `l >= 0`
there is `c in (0, pi/16)` and `beta > 0` such that the Hermite tail
`int_{kT/2}^infty dx psi_n(x)^2 x^l` is at most `(nu_1(N))^k` for every
`n <= c N` and `k >= 1`, where `T = sqrt(2 pi N)` (noted on p. 15). -/
def lemma1_hermite_tail_integral (l : ℕ) : Prop :=
    ∃ c β : ℝ, 0 < c ∧ 0 < β ∧ c < Real.pi / 16 ∧
      ∀ (N n k : ℕ), 2 ≤ N → (n : ℝ) ≤ c * (N : ℝ) → 1 ≤ k →
        |∫ x in Set.Ici ((k : ℝ) * Real.sqrt (2 * Real.pi * (N : ℝ)) / 2),
            (hermiteFun n x) ^ 2 * x ^ l| ≤ Real.exp (-β * (N : ℝ) * (k : ℝ))

/-- Fixed arXiv:1503.06319v2, Lemma 2 (p. 16, Eq. (A9)): there are `c > 0`,
`beta > 0` such that every position matrix element of the discrete Hermite
states differs from the continuous-variable one by at most `nu_1(N)` for
`n, m <= c N`. -/
def lemma2_position_moments (l : ℕ) : Prop :=
    ∃ c β : ℝ, 0 < c ∧ 0 < β ∧
      ∀ (N m n : ℕ), 2 ≤ N → (n : ℝ) ≤ c * (N : ℝ) → (m : ℝ) ≤ c * (N : ℝ) →
        ‖discXMoment l N m n - cvXMoment l m n‖ ≤ Real.exp (-β * (N : ℝ))

/-- Fixed arXiv:1503.06319v2, Corollary 1 (p. 16, Eq. (A17)): the discrete
Hermite states are almost orthonormal, `<psi_m^d|psi_n^d> = delta_{n,m}` up to
`nu_1(N)`, for all `n, m <= c N`. -/
def corollary1_almost_orthonormal : Prop :=
    ∃ c β : ℝ, 0 < c ∧ 0 < β ∧
      ∀ (N m n : ℕ), 2 ≤ N → (n : ℝ) ≤ c * (N : ℝ) → (m : ℝ) ≤ c * (N : ℝ) →
        ‖vInner (psiVec N m) (psiVec N n) - (if m = n then (1 : ℂ) else 0)‖ ≤
          Real.exp (-β * (N : ℝ))

/-- Fixed arXiv:1503.06319v2, Lemma 3 (p. 17, Eq. (A26)): the momentum matrix
elements of the discrete Hermite states differ from the continuous-variable
ones by `nu_1(N)`, for all `n, m <= c N`. -/
def lemma3_momentum_moments (l : ℕ) : Prop :=
    ∃ c β : ℝ, 0 < c ∧ 0 < β ∧
      ∀ (N m n : ℕ), 2 ≤ N → (n : ℝ) ≤ c * (N : ℝ) → (m : ℝ) ≤ c * (N : ℝ) →
        ‖discPMoment l N m n - cvPMoment l m n‖ ≤ Real.exp (-β * (N : ℝ))

/-- Fixed arXiv:1503.06319v2, Lemma 4 (p. 17, Eq. (A30)): mixed
momentum-position matrix elements of the discrete Hermite states differ from
the continuous-variable ones by `nu_1(N)`, for all `n, m <= c N`. -/
def lemma4_mixed_moments (l1 l2 : ℕ) : Prop :=
    ∃ c β : ℝ, 0 < c ∧ 0 < β ∧
      ∀ (N m n : ℕ), 2 ≤ N → (n : ℝ) ≤ c * (N : ℝ) → (m : ℝ) ≤ c * (N : ℝ) →
        ‖discPXMoment l1 l2 N m n - cvPXMoment l1 l2 m n‖ ≤
          Real.exp (-β * (N : ℝ))

/-- Fixed arXiv:1503.06319v2, Corollary 2 (p. 18, Eq. (A35)): the low-energy
Hermite states are approximate eigenstates of `H^d`,
`||(H^d - (n + 1/2)) |psi_n^d>||^2 = nu_1(N)` for all `n <= c N`. -/
def corollary2_low_energy_residual : Prop :=
    ∃ c β : ℝ, 0 < c ∧ 0 < β ∧
      ∀ (N n : ℕ), 2 ≤ N → (n : ℝ) ≤ c * (N : ℝ) →
        vNormSq ((hamOp N - ((((n : ℝ) + 1 / 2 : ℝ) : ℂ)) •
            (1 : Matrix (Fin N) (Fin N) ℂ)).mulVec (psiVec N n)) ≤
          Real.exp (-β * (N : ℝ))

end Qatlib.Papers.OneDimSim15.MainResults.Discretization
