/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ViscositySol25.MainResults.PrecisionEstimation

@[expose] public section

/-!
# Digital soft-minimum error on the `Nx ^ d` grid

*Quantum algorithms for viscosity solutions to nonlinear Hamilton-Jacobi equations based on an
entropy penalisation method*, arXiv:2512.07919v2, §IV.C.2, Eq. (69) and Lemma 18. See
<https://arxiv.org/abs/2512.07919>.

The digital protocol reads the minimum `Smin` of a grid function `S` off the normalisation
constant of `|u(t)⟩_{DV}` with entropy weight `ν = 1 / Nx ^ 4`. The grid has `Nx ^ d` points, one
for each of the `d` coordinates discretised on `Nx` levels, so the finite LogSumExp sandwich of
Lemma 18 specialises to

`|ν * log (∑_j exp (-(S j / ν))) + m| ≤ ν * d * log Nx`

for any lower bound `m` of `S` that is attained on the grid. This is the paper's digital
soft-minimum error scale `εmin = d / Nx ^ 2 + d * log Nx / Nx ^ 4` at leading order: the weight
`ν = 1 / Nx ^ 4` multiplies the number of grid points counted logarithmically.

The finite-index cardinality bookkeeping is the only content beyond the published bound
`Qatlib.Papers.ViscositySol25.MainResults.PrecisionEstimation.lemma18_logsumexp_bound`, which is
applied at `s = Finset.univ`.

## Boundary

Only the grid instance of the finite LogSumExp estimate is proved. The analog Laplace asymptotic
estimate, the attainment of the minimum by the actual interpolated solution `S` (as opposed to the
grid samples assumed here), the preparation of `|u(t)⟩_{DV}` and the identity
`εmin = d / Nx ^ 2 + d * log Nx / Nx ^ 4` are outside this file.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ViscositySol25.MainResults

open Qatlib.Papers.ViscositySol25.MainResults.PrecisionEstimation

/-- **Lemma 18, Eq. (69), p.21: the `Nx ^ d` grid instance.**

For a grid function `S : Fin (Nx ^ d) → ℝ`, a lower bound `m` attained at some grid point, and
`ν = 1 / Nx ^ 4` with `Nx > 0`, the digital soft minimum deviates from `m` by at most
`(1 / Nx ^ 4) * d * log Nx`.

The proof applies the published finite LogSumExp bound at the full grid, where the cardinality
`Nx ^ d` contributes `d * log Nx` after taking logarithms; this is the exact error scale the paper
quotes for `ln Nx` qubits per coordinate. -/
theorem digital_softmin_deviation_le
    (Nx d : ℕ) (S : Fin (Nx ^ d) → ℝ) (m : ℝ) (hNx : 0 < Nx)
    (hmin : ∀ j, m ≤ S j) (hach : ∃ j, S j = m) :
    |(1 / (Nx : ℝ) ^ 4) * Real.log (∑ j, Real.exp (-(S j / (1 / (Nx : ℝ) ^ 4)))) + m|
      ≤ (1 / (Nx : ℝ) ^ 4) * (d : ℝ) * Real.log (Nx : ℝ) := by
  have hNxpos : 0 < (Nx : ℝ) := by exact_mod_cast hNx
  have hν : 0 < 1 / (Nx : ℝ) ^ 4 := by positivity
  have hgridpos : 0 < Nx ^ d := pow_pos hNx d
  obtain ⟨j₀, hj₀⟩ := hach
  have hne : (Finset.univ : Finset (Fin (Nx ^ d))).Nonempty :=
    ⟨⟨0, hgridpos⟩, Finset.mem_univ _⟩
  have hcard : (((Finset.univ : Finset (Fin (Nx ^ d))).card : ℝ)) = (Nx : ℝ) ^ d := by
    simp [Nat.cast_pow]
  have hlog : Real.log ((Finset.univ : Finset (Fin (Nx ^ d))).card : ℝ)
      = (d : ℝ) * Real.log (Nx : ℝ) := by
    rw [hcard, Real.log_pow]
  have hbound := lemma18_logsumexp_bound (Finset.univ : Finset (Fin (Nx ^ d))) S
    (1 / (Nx : ℝ) ^ 4) m hν hne (fun j _ => hmin j)
    ⟨j₀, Finset.mem_univ j₀, hj₀⟩
  rw [hlog] at hbound
  calc |(1 / (Nx : ℝ) ^ 4) * Real.log (∑ j, Real.exp (-(S j / (1 / (Nx : ℝ) ^ 4)))) + m|
      ≤ (1 / (Nx : ℝ) ^ 4) * ((d : ℝ) * Real.log (Nx : ℝ)) := hbound
    _ = (1 / (Nx : ℝ) ^ 4) * (d : ℝ) * Real.log (Nx : ℝ) := by ring

end Qatlib.Papers.ViscositySol25.MainResults
