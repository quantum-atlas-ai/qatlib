/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QImagTime19.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# The QLanczos variational bound (arXiv:1901.07653, main text p. 5)

Paper: M. Motta et al., "Determining eigenstates and thermal states on a quantum
computer using quantum imaginary time evolution", arXiv:1901.07653 (2019).
Fixed source: `assets/1901.07653.pdf`, main text p. 5 ("Quantum Lanczos"): after
the QITE trajectory `|Φ_0⟩, …, |Φ_n⟩`, the QLanczos matrix `H_L` is the
compression of the Hamiltonian to the Krylov subspace spanned by these vectors;
diagonalising it yields energy estimates that are minima of the Rayleigh
quotient of `H` over that subspace.

The paper states (main text p. 5):

> Diagonalization of the QLanczos Hamiltonian matrix is guaranteed to give a
> ground-state energy lower than that of the last imaginary time vector `Φ_n`
> (while higher roots approximate excited states).

This is the variational principle: every eigenvalue of a Hermitian operator
`H` is a stationary value of the Rayleigh quotient `⟨ψ|H|ψ⟩ / ‖ψ‖²`, and the
smallest one is its infimum over the allowed subspace.  Hence the smallest root
of `H_L` — the infimum of the Rayleigh quotient over the Krylov subspace —
cannot exceed the Rayleigh quotient of any vector in that subspace, in
particular that of the last imaginary-time vector `Φ_n`; likewise the higher
roots, being the infima over the subspaces orthogonal to the lower roots, are
upper-bounded by the Rayleigh quotient of any vector in those subspaces, e.g. an
excited eigenvector.

The statements below formalise exactly these inequalities.  The Rayleigh
quotient of `H` at `ψ` is Mathlib's `ContinuousLinearMap.rayleighQuotient`,
`re ⟨H ψ, ψ⟩ / ‖ψ‖²`, i.e. the energy expectation `⟨ψ|Ĥ|ψ⟩` of the normalised
state `ψ/‖ψ‖`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QImagTime19.MainResults

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hamiltonian `H` as a continuous linear operator on the state space,
used to form Rayleigh quotients. -/
def hamCLM (H : Matrix ι ι ℂ) : State ι →L[ℂ] State ι :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H

/-- The QLanczos ground-state energy estimate: the infimum of the Rayleigh
quotient of the operator `T` over the nonzero vectors of the subspace `S`
(playing the role of the Krylov subspace spanned by the QITE vectors).  When `S`
is finite dimensional this is the smallest root of the compressed Hamiltonian
matrix `H_L`. -/
def subspaceGroundEnergy (T : State ι →L[ℂ] State ι) (S : Submodule ℂ (State ι)) : ℝ :=
  ⨅ x : {x : State ι // x ∈ S ∧ x ≠ 0}, T.rayleighQuotient (x : State ι)

/-- The Rayleigh quotient over any set of nonzero vectors is bounded below by
`-‖T‖`, since `|⟨T x, x⟩| / ‖x‖² ≤ ‖T‖` for every `x`. -/
theorem bddBelow_subspace_rayleigh (T : State ι →L[ℂ] State ι)
    (S : Submodule ℂ (State ι)) :
    BddBelow (Set.range fun x : {x : State ι // x ∈ S ∧ x ≠ 0} =>
      T.rayleighQuotient (x : State ι)) := by
  refine ⟨-‖T‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (neg_le_neg (T.rayleighQuotient_le_norm (x : State ι))).trans (neg_abs_le _)

/-- **Variational principle on a subspace.**  The infimum of the Rayleigh
quotient over the nonzero vectors of a subspace `S` is at most the Rayleigh
quotient of any nonzero vector of `S`. -/
theorem subspaceGroundEnergy_le_rayleigh (T : State ι →L[ℂ] State ι)
    (S : Submodule ℂ (State ι)) {ψ : State ι} (hψS : ψ ∈ S) (hψ : ψ ≠ 0) :
    subspaceGroundEnergy T S ≤ T.rayleighQuotient ψ := by
  unfold subspaceGroundEnergy
  exact ciInf_le (bddBelow_subspace_rayleigh T S) ⟨ψ, hψS, hψ⟩

/-- **Ground-state bound of the QLanczos method (main text p. 5).**

Diagonalising the QLanczos Hamiltonian matrix — i.e. taking the infimum of the
energy functional `⟨ψ|Ĥ|ψ⟩/‖ψ‖²` over the Krylov subspace `S` spanned by the
imaginary-time vectors — is guaranteed to give an energy no larger than that of
the last imaginary-time vector `Φ` (which lies in `S`).  Here `H` is the
Hamiltonian and `Φ` an arbitrary nonzero state of the subspace, e.g.
`Φ = qiteSeq U ψ0 (n*m)`. -/
theorem qlanczos_ground_energy_le_last_vector (H : Matrix ι ι ℂ)
    (S : Submodule ℂ (State ι)) {Φ : State ι} (hΦS : Φ ∈ S) (hΦ : Φ ≠ 0) :
    subspaceGroundEnergy (hamCLM H) S ≤ (hamCLM H).rayleighQuotient Φ :=
  subspaceGroundEnergy_le_rayleigh _ S hΦS hΦ

/-- **Ground-state bound for the QITE trajectory of Theorem 1.**  The smallest
root of the QLanczos matrix built from the QITE trajectory
`|Φ_0⟩, …, |Φ_{n m}⟩` is at most the Rayleigh quotient (energy expectation) of
the last imaginary-time vector `|Φ_{n m}⟩`. -/
theorem qlanczos_ground_energy_le_imaginary_time_vector
    {m : ℕ} [NeZero m] (H : Matrix ι ι ℂ) (U : ℕ → Matrix ι ι ℂ) (n : ℕ)
    (S : Submodule ℂ (State ι)) (ψ0 : State ι)
    (hΦS : qiteSeq U ψ0 (n * m) ∈ S) (hΦ : qiteSeq U ψ0 (n * m) ≠ 0) :
    subspaceGroundEnergy (hamCLM H) S ≤ (hamCLM H).rayleighQuotient (qiteSeq U ψ0 (n * m)) :=
  qlanczos_ground_energy_le_last_vector H S hΦS hΦ

/-- **Higher roots approximate excited states (main text p. 5).**  The `k`-th
root of the QLanczos matrix is the infimum of the energy functional over the
subspace `S'` orthogonal to the lower roots.  Therefore, whenever an
approximate excited state `Φ` lies in that subspace, the corresponding
QLanczos energy is no larger than the energy expectation of `Φ`. -/
theorem qlanczos_excited_energy_le_of_subspace (H : Matrix ι ι ℂ)
    (S S' : Submodule ℂ (State ι)) (_hSS' : S' ≤ S) {Φ : State ι}
    (hΦS' : Φ ∈ S') (hΦ : Φ ≠ 0) :
    subspaceGroundEnergy (hamCLM H) S' ≤ (hamCLM H).rayleighQuotient Φ :=
  subspaceGroundEnergy_le_rayleigh _ S' hΦS' hΦ

end Qatlib.Papers.QImagTime19.MainResults
