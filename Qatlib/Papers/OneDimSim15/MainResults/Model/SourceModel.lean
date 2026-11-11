/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# OneDimSim15 source model: the discrete one-dimensional quantum system

Rolando D. Somma, "Quantum simulations of one dimensional quantum systems",
fixed arXiv:1503.06319v2 (LA-UR-15-20573), PDF SHA-256
`a4b1d1e0c37ee0d8f0b0f1e5f8d49c0b2bbf16f5b0eccdd4a04a4e0eaa7bd0f5`.

This file fixes the paper-level objects shared by all claims of the paper:

* the centered grid `x_j = j sqrt(2 pi / N)`, `j = k - N/2` (Eq. 11);
* the discrete position operator `x^d` (Eq. 11) and the centered discrete
  Fourier transform `F_c^d` (Eq. 13) with the discrete momentum operator
  `p^d = (F_c^d)^{-1} x^d F_c^d` (Eq. 12);
* the discrete QHO Hamiltonian `H^d = ((x^d)^2 + (p^d)^2)/2` (Eq. 10) and the
  evolution `U^d(t) = exp(-i H^d t)`;
* the physicist's Hermite functions and the discrete Hermite states
  `|psi_n^d> = (2 pi/N)^{1/4} sum_j psi_n(x_j)|j>` (Eq. 15);
* the symmetric high-order Trotter-Suzuki words `U_p^d(s)` (Eq. 29);
* the discrete Jaynes-Cummings Hamiltonian `H_JC^d` (Eq. 38) and the
  asymmetric word `W(s)` (Eq. D7);
* the paper's `nu_1(N) = exp(-Omega(N))` notation (p. 15).

Boundary. The continuous-variable (CV) QHO is represented only through the
explicit integrals of Hermite functions that the paper writes down (Eqs. 5, 6,
A9, A26, A30); the unbounded CV operators `x-hat`, `p-hat` themselves are not
modelled as Lean operators. Paper-layer results that name `U_p(s)` of the CV
QHO (`Lemma 5`, `Lemma 7`) are transcribed with the paper's own discrete
replacement `x-hat -> x^d`, `p-hat -> p^d`, which is the form Appendix B
consumes in Lemmas 6-8 and Theorem 2; this boundary is repeated at the
corresponding theorems. Circuit implementation is likewise a separate layer:
`PaperCircuit`/`CompiledUnitary` record the claimed two-qubit gate count of a
realized unitary, while the paper's gate-synthesis statements are the claims
under study, not premises used here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OneDimSim15.MainResults

open Matrix MeasureTheory
open scoped BigOperators Matrix Kronecker Matrix.Norms.L2Operator ComplexOrder

/-! ## Grid, position, momentum, Hamiltonian -/

/-- The centered integer label `j = k - N/2` of a grid point (Eq. 11, with
`j` running from `-N/2` to `N/2 - 1` for even `N`). -/
def centIdx (N : ℕ) (k : Fin N) : ℤ := (k : ℤ) - (N / 2 : ℕ)

/-- The grid coordinate `x_j = j sqrt(2 pi / N)` (Eq. 11). -/
def gridCoord (N : ℕ) (k : Fin N) : ℝ :=
  (centIdx N k : ℝ) * Real.sqrt (2 * Real.pi / N)

/-- The discrete position operator `x^d = diag(x_j)` (Eq. 11). -/
def posOp (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun k => (gridCoord N k : ℂ))

/-- The centered discrete Fourier transform, matrix entries
`(F_c^d)_{j,k} = N^{-1/2} exp(i 2 pi j k / N)` (Eq. 13). -/
def cDft (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k =>
    ((Real.sqrt N : ℂ)⁻¹) *
      Complex.exp (Complex.I * ((2 * Real.pi * (centIdx N j : ℝ) *
        (centIdx N k : ℝ) / N : ℝ) : ℂ))

/-- The discrete momentum operator `p^d = (F_c^d)^{-1} x^d F_c^d` (Eq. 12).
`F_c^d` is unitary, so its inverse is its conjugate transpose. -/
def momOp (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  (cDft N)ᴴ * posOp N * cDft N

/-- The discrete QHO Hamiltonian `H^d = ((x^d)^2 + (p^d)^2)/2` (Eq. 10). -/
def hamOp (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  (2 : ℂ)⁻¹ • (posOp N ^ 2 + momOp N ^ 2)

/-- The discrete QHO evolution operator `U^d(t) = exp(-i H^d t)`. -/
def evolveOp (N : ℕ) (t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • hamOp N)

/-! ## Hermite functions and discrete Hermite states -/

/-- The physicists' Hermite polynomial `H_n(x) = (-1)^n e^{x^2} (d/dx)^n e^{-x^2}`
(Eq. A2). -/
def hermitePoly (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * Real.exp (x ^ 2) * iteratedDeriv n (fun y : ℝ => Real.exp (-(y ^ 2))) x

/-- The `n`-th Hermite function
`psi_n(x) = (n! 2^n sqrt(pi))^{-1/2} e^{-x^2/2} H_n(x)` (Eq. A1). -/
def hermiteFun (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt ((n.factorial : ℝ) * (2 : ℝ) ^ n * Real.sqrt Real.pi))⁻¹ *
    Real.exp (-(x ^ 2) / 2) * hermitePoly n x

/-- The `l`-th derivative of the `n`-th Hermite function, the kernel of
`p-hat^l = (-i d/dx)^l` (Eq. 6). -/
def hermiteDeriv (n l : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv l (fun y : ℝ => hermiteFun n y) x

/-- The discrete Hermite state `|psi_n^d> = (2 pi/N)^{1/4} sum_j psi_n(x_j)|j>`
(Eq. 15), stored as its amplitude vector. -/
def psiVec (N n : ℕ) : Fin N → ℂ :=
  fun k => ((Real.sqrt (Real.sqrt (2 * Real.pi / N)) *
    hermiteFun n (gridCoord N k) : ℝ) : ℂ)

/-- The state is real, so its conjugate is itself. -/
@[simp] theorem star_psiVec (N n : ℕ) (k : Fin N) :
    star (psiVec N n k) = psiVec N n k := by
  simp [psiVec]

/-! ## Finite vector operations -/

/-- The Hermitian inner product `sum_k conj(u_k) v_k`. -/
def vInner {N : ℕ} (u v : Fin N → ℂ) : ℂ := ∑ k, star (u k) * v k

/-- The squared Euclidean norm `sum_k |v_k|^2`. -/
def vNormSq {N : ℕ} (v : Fin N → ℂ) : ℝ := ∑ k, Complex.normSq (v k)

/-- The Euclidean norm. -/
def vNorm {N : ℕ} (v : Fin N → ℂ) : ℝ := Real.sqrt (vNormSq v)

/-- The normalization of a nonzero vector (junk `0` at the zero vector). -/
def normalize {N : ℕ} (v : Fin N → ℂ) : Fin N → ℂ := (vNorm v)⁻¹ • v

/-- The computational basis vector `|k>`. -/
def basisVec {N : ℕ} (k : Fin N) : Fin N → ℂ := fun j => if j = k then 1 else 0

/-- The state `sum_{n=0}^{N'} c_n |psi_n^d>` (unnormalized; the paper's `|phi^d>`
is proportional to this). -/
def coeffVec (N' N : ℕ) (c : ℕ → ℂ) : Fin N → ℂ :=
  Finset.sum (Finset.range (N' + 1)) (fun n => c n • psiVec N n)

/-- The continuous-variable overlap `sum_{n=0}^{N'} conj(c'_n) c_n e^{-i(n+1/2)t}`
(Eq. 8). -/
def cvOverlap (N' : ℕ) (c c' : ℕ → ℂ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (N' + 1))
    (fun n => star (c' n) * c n * Complex.exp (-Complex.I * ((n : ℝ) + 1 / 2) * (t : ℂ)))

/-- The discretized overlap `<phi'^d|U^d(t)|phi^d>` of Theorem 1. -/
def discOverlap (N N' : ℕ) (c c' : ℕ → ℂ) (t : ℝ) : ℂ :=
  vInner (normalize (coeffVec N' N c'))
    ((evolveOp N t).mulVec (normalize (coeffVec N' N c)))

/-- The position-eigenstate overlap `(2 pi/N)^{1/4} <x_j|U(t)|phi>` of Eq. (27). -/
def cvPositionOverlap (N N' : ℕ) (c : ℕ → ℂ) (t : ℝ) (j : Fin N) : ℂ :=
  ((Real.sqrt (Real.sqrt (2 * Real.pi / N)) : ℝ) : ℂ) *
    Finset.sum (Finset.range (N' + 1))
      (fun n => c n * Complex.exp (-Complex.I * ((n : ℝ) + 1 / 2) * (t : ℂ)) *
        (hermiteFun n (gridCoord N j) : ℂ))

/-! ## Moments: discrete versus continuous (Appendix A) -/

/-- `<psi_m^d|(x^d)^l|psi_n^d>` (Eq. A9, left side). -/
def discXMoment (l N m n : ℕ) : ℂ :=
  ∑ k : Fin N, star (psiVec N m k) * (gridCoord N k : ℂ) ^ l * psiVec N n k

/-- `<psi_m|x-hat^l|psi_n> = int psi_m(x) x^l psi_n(x) dx` (Eq. 5). -/
def cvXMoment (l m n : ℕ) : ℂ :=
  ∫ x : ℝ, (hermiteFun m x : ℂ) * (x : ℂ) ^ l * (hermiteFun n x : ℂ)

/-- `<psi_m|p-hat^l|psi_n> = int psi_m(x) (-i d/dx)^l psi_n(x) dx` (Eq. 6). -/
def cvPMoment (l m n : ℕ) : ℂ :=
  ∫ x : ℝ, (hermiteFun m x : ℂ) * (-Complex.I) ^ l * (hermiteDeriv n l x : ℂ)

/-- `<psi_m^d|(p^d)^l|psi_n^d>` (Eq. A26, left side). -/
def discPMoment (l N m n : ℕ) : ℂ :=
  vInner (psiVec N m) ((momOp N ^ l).mulVec (psiVec N n))

/-- `<psi_m|p-hat^{l1} x-hat^{l2}|psi_n> = int psi_m (-i d/dx)^{l1}(x^{l2} psi_n) dx`. -/
def cvPXMoment (l1 l2 m n : ℕ) : ℂ :=
  ∫ x : ℝ, (hermiteFun m x : ℂ) * (-Complex.I) ^ l1 *
    ((x : ℂ) ^ l2 * (hermiteDeriv n l1 x : ℂ))

/-- `<psi_m^d|(p^d)^{l1} (x^d)^{l2}|psi_n^d>` (Eq. A30, left side). -/
def discPXMoment (l1 l2 N m n : ℕ) : ℂ :=
  vInner (psiVec N m) (((momOp N ^ l1) * (posOp N ^ l2)).mulVec (psiVec N n))

/-! ## The `nu_1(N) = exp(-Omega(N))` vocabulary (p. 15) -/

/-- `f = nu_1` in the paper's sense: `f(N) = exp(-Omega(N))`, i.e. some `beta > 0`
bounds `|f(N)|` by `exp(-beta N)` for all sufficiently large `N`. -/
def IsExpSmall (f : ℕ → ℝ) : Prop :=
  ∃ β : ℝ, 0 < β ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → |f N| ≤ Real.exp (-β * N)

/-! ## Trotter-Suzuki words (Eqs. 29, B4) -/

/-- The symmetric base word `U_1^d(s) = e^{-is(x^d)^2/4} e^{-is(p^d)^2/2}
e^{-is(x^d)^2/4}` (Eq. B3, with `x-hat -> x^d`, `p-hat -> p^d`). -/
def trotterBase (N : ℕ) (s : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  NormedSpace.exp ((-Complex.I * (s : ℂ) / 4) • (posOp N ^ 2)) *
    NormedSpace.exp ((-Complex.I * (s : ℂ) / 2) • (momOp N ^ 2)) *
      NormedSpace.exp ((-Complex.I * (s : ℂ) / 4) • (posOp N ^ 2))

/-- The Suzuki time step `s_p = s/(4 - 4^{1/(2p+1)})` (Eq. 29). -/
def suzukiStep (p : ℕ) (s : ℝ) : ℝ :=
  s / (4 - 4 ^ ((1 : ℝ) / (2 * (p : ℝ) + 1)))

/-- The `p`-th order symmetric Trotter-Suzuki word `U_p^d(s)` (Eq. 29, Eq. B4):
`U_{p+1}(s) = (U_p(s_p))^2 U_p(s - 4 s_p) (U_p(s_p))^2`, with `U_1` the base
word above.  (`p = 0` is the identity and is never used.) -/
def trotterWord : (p : ℕ) → (N : ℕ) → ℝ → Matrix (Fin N) (Fin N) ℂ
  | 0, _, _ => 1
  | 1, N, s => trotterBase N s
  | (p + 2), N, s =>
      let sp := suzukiStep (p + 2) s
      let U := trotterWord (p + 1) N
      U sp * U sp * U (s - 4 * sp) * U sp * U sp

/-- The number of exponentials of `(x^d)^2` and `(p^d)^2` in `U_p^d(s)`:
`U_1` has three, and the recursion multiplies the count by five (Eq. 29). -/
def trotterCount : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | (p + 2) => 5 * trotterCount (p + 1)

/-- The Trotter error operator `epsilon_p(s) = U_p(s) U(s)^{-1} - 1` (Eqs. B5, B6). -/
def trotterEps (N p : ℕ) (s : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  trotterWord p N s * (evolveOp N s)⁻¹ - 1

/-- The paper's exponential count `3 * 5^{p-1}` for the order-`p` word. -/
theorem trotterCount_eq (p : ℕ) (hp : 1 ≤ p) :
    trotterCount p = 3 * 5 ^ (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  induction q with
  | zero => simp [trotterCount]
  | succ q ih =>
      have hstep : trotterCount (q + 1 + 1) = 5 * trotterCount (q + 1) := rfl
      rw [hstep, ih (by omega)]
      have hexp : q + 1 + 1 - 1 = (q + 1 - 1) + 1 := by omega
      rw [hexp, pow_succ]
      ring

/-! ## Jaynes-Cummings model (Appendix D) -/

/-- The Pauli `sigma_x`. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `sigma_y`. -/
def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The discrete Jaynes-Cummings Hamiltonian
`H_JC^d = (x^d ⊗ sigma_x - p^d ⊗ sigma_y)/sqrt 2` (Eq. 38). -/
def jcHam (N : ℕ) : Matrix (Fin N × Fin 2) (Fin N × Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (Matrix.kroneckerMap (· * ·) (posOp N) sigmaX -
      Matrix.kroneckerMap (· * ·) (momOp N) sigmaY)

/-- The JC evolution `e^{-i H_JC^d s}`. -/
def jcEvolve (N : ℕ) (s : ℝ) : Matrix (Fin N × Fin 2) (Fin N × Fin 2) ℂ :=
  NormedSpace.exp ((-Complex.I * (s : ℂ)) • jcHam N)

/-- The asymmetric first-order word
`W(s) = e^{-i(x^d ⊗ sigma_x) s/sqrt 2} e^{i(p^d ⊗ sigma_y) s/sqrt 2}` (Eq. D7). -/
def jcWord (N : ℕ) (s : ℝ) : Matrix (Fin N × Fin 2) (Fin N × Fin 2) ℂ :=
  NormedSpace.exp ((-Complex.I * (s : ℂ) / (Real.sqrt 2 : ℂ)) •
      Matrix.kroneckerMap (· * ·) (posOp N) sigmaX) *
    NormedSpace.exp ((Complex.I * (s : ℂ) / (Real.sqrt 2 : ℂ)) •
      Matrix.kroneckerMap (· * ·) (momOp N) sigmaY)

/-- Tensor product of an `N`-vector with a qubit vector. -/
def tensorVec {N : ℕ} (u : Fin N → ℂ) (b : Fin 2 → ℂ) : Fin N × Fin 2 → ℂ :=
  fun ki => u ki.1 * b ki.2

/-- The qubit state `|0>`. -/
def qubit0 : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0

/-- The qubit state `|1>`. -/
def qubit1 : Fin 2 → ℂ := fun i => if i = 1 then 1 else 0

/-- The normalized JC states `|gamma_{n,pm}^d> = (1/sqrt 2)(|phi_n^d>|0> ±
|phi_{n+1}^d>|1>)` (Eq. 39), parametrized by the sign `sigma = ±1`. -/
def gammaVec {N : ℕ} (phin phin1 : Fin N → ℂ) (σ : ℂ) : Fin N × Fin 2 → ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (tensorVec phin qubit0 + σ • tensorVec phin1 qubit1)

/-- The unnormalized Gaussian initial state of Eq. (C1),
`sum_j exp(-j^2/(2 delta))|j>`. -/
def gaussVec (N : ℕ) (δ : ℝ) : Fin N → ℂ :=
  fun k => ((Real.exp (-((centIdx N k : ℝ) ^ 2) / (2 * δ)) : ℝ) : ℂ)

/-- `|phi_n^d>` is an eigenstate of `H^d` with eigenvalue within `nu` of `n + 1/2`:
the exact eigenvector may be degenerate/unknown, so all statements that consume
it carry this certificate instead of naming an eigenvector. -/
structure ApproxEigenstate (N n : ℕ) (φ : Fin N → ℂ) (ν : ℝ) : Prop where
  normed : vNorm φ = 1
  eigen : ∃ E : ℝ, |E - ((n : ℝ) + 1 / 2)| ≤ ν ∧
    vNorm ((hamOp N).mulVec φ - (E : ℂ) • φ) ≤ ν

/-! ## Paper-level circuit and compiled-unitary contracts -/

/-- The gate-count/amplitude contract of a paper-level circuit: a realized
two-qubit gate count and the measured amplitude of the circuit on the source's
prepared input.  Gate synthesis and ancilla management are the object of the
claims, not premises. -/
structure PaperCircuit where
  gateCount : ℝ
  amplitude : ℂ

/-- A compiled unitary matrix together with its two-qubit gate count. -/
structure CompiledUnitary (N : ℕ) where
  mat : Matrix (Fin N) (Fin N) ℂ
  unitary : matᴴ * mat = 1
  gateCount : ℝ

end Qatlib.Papers.OneDimSim15.MainResults
