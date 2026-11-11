/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussBosonic24.MomentPropagate.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Supplemental Proposition 2 (particle-preserving generators)

Paper: *Gate-based quantum simulation of Gaussian bosonic circuits on
exponentially many modes*, fixed arXiv:2407.06290 (2024), Supplemental
Information Appendix A.3, Supplemental Proposition 2, Eqs. (A35)–(A37).

The paper's statement (SI p. 11): for a gate generator

`Ĥ = Σ_{m,m'} h_{mm'} â†_m â_{m'} + (Tr h / 2) 1_{2M}`   (A35)

with `h` Hermitian, one has `[Ω, K] = 0`, and the propagator `e^{tΩK}` is the
real-time evolution under the effective Hamiltonian `i Ω K` (main text, p. 2:
"the propagator e^{tΩK} is the real-time evolution of the Hermitian iΩK";
the SI line prints `−iΩK`, which differs only by the sign convention of the
definition of `Ω` versus the propagator; we state the main-text form).

Route followed (Eqs. (A36)–(A37)): expanding `â_m = (q̂_m + i p̂_m)/√2`,
`â†_m = (q̂_m − i p̂_m)/√2` and using the canonical commutation relations
(Eq. (A5)) shows that the real symmetric matrix `K` has the block structure

`K = [[Re h, -Im h], [Im h, Re h]]`

on the phase-space split `(q_1, …, q_M, p_1, …, p_M)`.  The two conclusions are
then block-matrix identities: `Ω K = K Ω`, and `Ω K` is skew-Hermitian, so the
propagator `exp(t Ω K)` is unitary and equals `e^{-i t (i Ω K)}`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.GaussBosonic24.MomentPropagate

variable {M : ℕ}

/-- **Supplemental Proposition 2, commutation half.**  For a Hermitian
coefficient matrix `h`, the phase-space generator `K(h)` of Eq. (A37) commutes
with the symplectic form: `[Ω, K] = 0`. -/
theorem particleK_commutes_omega {h : Matrix (Fin M) (Fin M) ℂ} (_hh : h.IsHermitian) :
    omega M * particleK h = particleK h * omega M := by
  rw [omega, particleK, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- The generator `Ω K(h)` of a particle-preserving gate is skew-Hermitian. -/
theorem particle_omegaK_skewHermitian {h : Matrix (Fin M) (Fin M) ℂ} (hh : h.IsHermitian) :
    (omega M * particleK h)ᴴ = -(omega M * particleK h) := by
  have hre : (rePart h)ᴴ = rePart h := rePart_isHermitian hh
  have him := imPart_skewHermitian hh
  rw [omega, particleK, fromBlocks_multiply]
  -- the product is `fromBlocks (Im h) (Re h) (-Re h) (Im h)`
  simp only [Matrix.zero_mul, Matrix.one_mul,
    Matrix.neg_mul, Matrix.mul_neg, zero_add, add_zero, neg_neg]
  simp only [fromBlocks_conjTranspose, Matrix.conjTranspose_neg, him, hre, neg_neg,
    fromBlocks_neg, neg_zero, zero_add]

/-- **Supplemental Proposition 2, propagator half.**  For a Hermitian `h` and real
time `t`, the phase-space propagator `e^{tΩK}` is the real-time evolution under
the Hermitian effective Hamiltonian `i Ω K`: `e^{tΩK} = e^{-i t (iΩK)}`. -/
theorem particle_propagator_eq_hamiltonianEvolution {h : Matrix (Fin M) (Fin M) ℂ}
    (_hh : h.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (omega M * particleK h)) =
      HamiltonianEvolution (Complex.I • (omega M * particleK h)) t := by
  unfold HamiltonianEvolution
  have harg : (-Complex.I * (t : ℂ)) • (Complex.I • (omega M * particleK h))
      = (t : ℂ) • (omega M * particleK h) := by
    rw [smul_smul]
    congr 1
    calc (-Complex.I * (t : ℂ)) * Complex.I
        = -(Complex.I * Complex.I) * (t : ℂ) := by ring
      _ = (t : ℂ) := by rw [Complex.I_mul_I]; ring
  rw [harg]

/-- **Supplemental Proposition 2, unitarity.**  For a Hermitian `h` and real `t`,
the propagator `e^{tΩK}` is unitary: this is the paper's conclusion that
particle-preserving generators give real-time (unitary) phase-space dynamics. -/
theorem particle_propagator_unitary {h : Matrix (Fin M) (Fin M) ℂ} (hh : h.IsHermitian)
    (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (omega M * particleK h)) ∈
      Matrix.unitaryGroup (Fin M ⊕ Fin M) ℂ := by
  apply exp_unitary_of_skewHermitian
  rw [Matrix.conjTranspose_smul, particle_omegaK_skewHermitian hh]
  simp

end Qatlib.Papers.GaussBosonic24.MomentPropagate
