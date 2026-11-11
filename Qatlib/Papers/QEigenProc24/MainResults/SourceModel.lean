/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QEigenProc24 — fixed source model

Low & Su, *Quantum eigenvalue processing*, fixed arXiv:2401.06240**v3** (26 Mar 2026).
PDF SHA reference: `prove/assets/2401.06240.pdf`.

This module owns the paper-level vocabulary of the `MainResults` block:

* the Euclidean state space and square operators the paper's algorithms act on;
* the centered modulus `CMod_q` (Eq. (164), p. 44) and the two Chebyshev families
  `T_j`, `U_j`, the rescaled `T̃_j` (Eqs. (52)–(60), pp. 19–20), and their matrix
  realisations `T_j(A)`, `U_j(A)`;
* the paper's numerical range `W(C)` and Hermitian part `ℜ(C)` (Appendix B.2, p. 101);
* the Faber-region and Jordan-form *interfaces* used in Sections 8–9 and Appendix A;
* an explicit, documented `MachineModel` interface for the algorithm-existence and
  query-count claims (Theorems 1–12): programs, the state a program prepares, its
  success probability and its query ledger.

Boundary.  The model records what the paper's theorems *assert*; it does not claim
efficient circuit synthesis, and the `MachineModel` interface is stated explicitly so
that the algorithm-existence statements are not silently weakened.  Every theorem
file names the FQN of a reusable Frozen/Mathlib result where one exists.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Matrix Matrix.Norms.L2Operator BigOperators ComplexOrder InnerProductSpace

namespace Qatlib.Papers.QEigenProc24.MainResults

/-! ## §1. States, operators and real spectra -/

/-- The paper's state space: `d` complex amplitudes with the Euclidean (ℓ²) norm. -/
abbrev Vec (d : ℕ) : Type := EuclideanSpace ℂ (Fin d)

/-- A square operator acting on `Vec d`. -/
abbrev Op (d : ℕ) : Type := Matrix (Fin d) (Fin d) ℂ

/-- The action of an operator on a state, `A|x⟩`, as a state again. -/
def applyOp {d : ℕ} (A : Op d) (x : Vec d) : Vec d :=
  WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)

/-- "A square matrix with only real eigenvalues" (Theorems 1, 3, 4, 5, 7, 8):
every eigenpair `μ, x` with `x ≠ 0` has real eigenvalue. -/
def OnlyRealEigenvalues {d : ℕ} (A : Op d) : Prop :=
  ∀ (μ : ℂ) (x : Vec d), x ≠ 0 → applyOp A x = μ • x → μ.im = 0

/-- The Hermitian part `ℜ(C) = (C + C†)/2` (Proposition 34, Eq. (472)). -/
def hermitianPart {d : ℕ} (C : Op d) : Op d := (1 / 2 : ℂ) • (C + Cᴴ)

/-- The numerical range `W(C) = { ⟪x, C x⟫ | ‖x‖ = 1 }` (Appendix B.2). -/
def numericalRange {d : ℕ} (C : Op d) : Set ℂ :=
  {z | ∃ x : Vec d, ‖x‖ = 1 ∧ z = ⟪x, applyOp C x⟫_ℂ}

/-- The real part of the numerical range, `ℜ(W(C))` (left side of Eq. (472)). -/
def realPartNumericalRange {d : ℕ} (C : Op d) : Set ℝ :=
  {t | ∃ z ∈ numericalRange C, z.re = t}

/-! ## §2. Centered modulus and Chebyshev families -/

/-- The centered modulus `CMod_q(x) = x - q ⌊(x + q/2)/q⌋ ∈ [-q/2, q/2)` (Eq. (164), p. 44). -/
def cmod (q x : ℝ) : ℝ := x - q * ((⌊(x + q / 2) / q⌋ : ℤ) : ℝ)

/-- Chebyshev polynomial of the first kind `T_j(x) = cos(j arccos x)` (Eq. (52), p. 19). -/
def chebT (j : ℕ) (x : ℝ) : ℝ := Real.cos ((j : ℝ) * Real.arccos x)

/-- Rescaled Chebyshev polynomial `T̃_j` with `T̃_0 = T_0/2` and `T̃_j = T_j` for `j ≥ 1`
(Eq. (54), p. 20). -/
def chebTilde (j : ℕ) (x : ℝ) : ℝ := if j = 0 then 1 / 2 else chebT j x

/-- Chebyshev polynomial of the second kind `U_j` (Eq. (56)), through Mathlib's
`Polynomial.Chebyshev.U`. -/
def chebU (j : ℕ) (x : ℝ) : ℝ := (Polynomial.Chebyshev.U ℝ (j : ℤ)).eval x

/-- Matrix Chebyshev polynomial of the first kind, by the recurrence
`T_0(A) = 1`, `T_1(A) = A`, `T_{j+2}(A) = 2 A T_{j+1}(A) - T_j(A)`. -/
def chebTMat {d : ℕ} (A : Op d) : ℕ → Op d
  | 0 => 1
  | 1 => A
  | (j + 2) => 2 • (A * chebTMat A (j + 1)) - chebTMat A j

/-- Matrix Chebyshev polynomial of the second kind, same recurrence with `U_1 = 2A`. -/
def chebUMat {d : ℕ} (A : Op d) : ℕ → Op d
  | 0 => 1
  | 1 => 2 • A
  | (j + 2) => 2 • (A * chebUMat A (j + 1)) - chebUMat A j

/-- Rescaled matrix Chebyshev polynomial `T̃_j(A)`, Eq. (54). -/
def chebTildeMat {d : ℕ} (A : Op d) (j : ℕ) : Op d :=
  if j = 0 then (1 / 2 : ℝ) • (1 : Op d) else chebTMat A j

/-- A Chebyshev partial sum `Σ_{k< n} β_k T_k(A)` (used by Theorems 1, 4, 5). -/
def chebSum {d : ℕ} (A : Op d) (n : ℕ) (β : ℕ → ℝ) : Op d :=
  ∑ k ∈ Finset.range n, (β k : ℝ) • chebTMat A k

/-- A rescaled Chebyshev partial sum `Σ_{k< n} β̃_k T̃_k(A)` (Eqs. (6), (222)). -/
def chebTildeSum {d : ℕ} (A : Op d) (n : ℕ) (β : ℕ → ℝ) : Op d :=
  ∑ k ∈ Finset.range n, (β k : ℝ) • chebTildeMat A k

/-! ## §3. Numerical-range, Jordan and Faber interfaces -/

/-- Jordan-block data: block sizes `dims l`, eigenvalues `lam l`, and the assembled
block-diagonal Jordan matrix `J` on `Σ l, Fin (dims l)`.  Used by Propositions 28 and 34's
neighbours and by Theorem 12. -/
structure JordanBlockData where
  k : ℕ
  dims : Fin k → ℕ
  lam : Fin k → ℂ

/-- The Jordan block `J(λ, d)`: `λ` on the diagonal and `1` on the superdiagonal. -/
def jordanBlock (lam : ℂ) (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i = j then lam else if (i : ℕ) + 1 = (j : ℕ) then 1 else 0

/-- The block-diagonal Jordan matrix associated with `JordanBlockData`. -/
def jordanMatrix (B : JordanBlockData) : Matrix (Σ l : Fin B.k, Fin (B.dims l))
    (Σ l : Fin B.k, Fin (B.dims l)) ℂ :=
  fun i j => if h : i.1 = j.1 then
      jordanBlock (B.lam i.1) (B.dims i.1) i.2 (h ▸ j.2)
    else 0

/-- A Jordan decomposition `C = S J S⁻¹` with Jordan condition number bound `κS ≥ ‖S‖‖S⁻¹‖`
(Section 2.1, p. 29), together with the block data of `J`. -/
structure JordanForm {d : ℕ} (C : Op d) where
  blocks : JordanBlockData
  S : Matrix (Fin d) (Σ l : Fin blocks.k, Fin (blocks.dims l)) ℂ
  T : Matrix (Σ l : Fin blocks.k, Fin (blocks.dims l)) (Fin d) ℂ
  left_inv : T * S = 1
  right_inv : S * T = 1
  decomp : C = S * jordanMatrix blocks * T
  kappaS : ℝ
  kappaS_nonneg : 0 ≤ kappaS
  kappaS_bound : ‖S‖ * ‖T‖ ≤ kappaS

/-- A Faber region `E` with conformal maps `Φ : Eᶜ → Dᶜ`, `Ψ : Dᶜ → Eᶜ` and Faber
polynomials `F_n` (Section 8.1).  The geometric hypotheses (convexity, real-axis symmetry,
lying in the left half-plane) are the ones used by Lemma 27 / Theorem 11. -/
structure FaberRegion where
  E : Set ℂ
  Phi : ℂ → ℂ
  Psi : ℂ → ℂ
  Fpoly : ℕ → Polynomial ℂ
  F_zero : Fpoly 0 = 1
  Psi_left_inv : ∀ z, Psi (Phi z) = z
  convex : Convex ℝ E
  conjugate_symm : ∀ z ∈ E, star z ∈ E
  leftHalf : ∀ z ∈ E, z.re ≤ 0

/-- The value of the `j`-th Faber polynomial of a Faber region. -/
def faberPoly (R : FaberRegion) (j : ℕ) (z : ℂ) : ℂ := (R.Fpoly j).eval z

/-- The matrix Faber polynomial `F_j(A/α_A)`. -/
def faberMat {d : ℕ} (A : Op d) (alphaA : ℝ) (R : FaberRegion) (j : ℕ) : Op d :=
  Polynomial.aeval (alphaA⁻¹ • A) (R.Fpoly j)

/-- The `F'`-normalisation bound `α_{F'} ≥ max_{j=1..n} ‖F'_j(A/α_A)/j‖` (Theorem 9, p. 84),
spelled as `‖dF_j‖ ≤ α · j` for the derivative matrices `dF_j = F'_j(A/α_A)`. -/
def IsFaberDerivativeBound {d : ℕ} (dF : ℕ → Op d) (n : ℕ) (alpha : ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 n, ‖dF j‖ ≤ alpha * (j : ℝ)

/-! ## §4. Algorithm-existence interface -/

/-- A state on an arbitrary index type, e.g. the register space
`Fin (η+1) × Fin n × Fin d` of the history-state algorithms. -/
abbrev VecI (ι : Type) : Type := EuclideanSpace ℂ ι

/-- Build a state from its amplitudes. -/
def ofFun {ι : Type} (f : ι → ℂ) : VecI ι := WithLp.toLp 2 f

/-- The amplitudes of a state. -/
def amp {ι : Type} (v : VecI ι) : ι → ℂ := WithLp.ofLp v

/-- Query ledger of one run of the paper's eigenvalue-processing algorithms.
`ctrlOA`, `ctrlOPsi`, `ctrlOBeta` count queries to the controlled block-encoding oracle,
the state-preparation oracle and the coefficient-shift oracle respectively. -/
structure QueryLedger where
  ctrlOA : ℕ
  ctrlOPsi : ℕ
  ctrlOBeta : ℕ
  gates : ℕ
  deriving Repr

/-- The paper's algorithm model on an output register space `ι`.  A `Program` is one algorithm
of the model; `outState P` is the (unnormalised) state it produces, `successProb P` is the
probability that the run returns the paper's target, and `ledger P` is the query ledger of
that run. -/
structure MachineModel (ι : Type) where
  Program : Type
  outState : Program → VecI ι
  successProb : Program → ℝ
  ledger : Program → QueryLedger

/-- The paper's accuracy convention: the prepared state is within Euclidean distance `ε` of
the (normalised) target state. -/
def Approximates {ι : Type} [Fintype ι] (prepared target : VecI ι) (ε : ℝ) : Prop :=
  ‖prepared - target‖ ≤ ε

/-- Normalisation of a vector, `|v⟩ / ‖|v⟩‖`. -/
def normalize {ι : Type} [Fintype ι] (v : VecI ι) : VecI ι := (‖v‖ : ℂ)⁻¹ • v

/-- The paper's `O(·)` at the fixed set of parameters of a theorem: a positive constant*independent* of the quantities named in the theorem bounds (n, ε, p_fail, α_A, …).  Using an
existential constant keeps the statements free of an asymptotic variable; the accompanying
comment of each theorem records the exact bound displayed in the paper. -/
def BigO (f g : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ f ≤ C * g

end Qatlib.Papers.QEigenProc24.MainResults
