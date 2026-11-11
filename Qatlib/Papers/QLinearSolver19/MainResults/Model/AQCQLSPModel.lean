/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

/-!
# Paper model for An–Lin, *Quantum linear system solver based on time-optimal
adiabatic quantum computing and quantum approximate optimization algorithm*
(arXiv:1909.05500v3; ACM TQC 3(2), Article 5, 2022).

This module fixes the objects that all claims of the paper are stated about:

* the positive-definite Hamiltonian pair `H₀ = σ_x ⊗ Q_b`, `H₁ = σ₊ ⊗ (A Q_b) + σ₋ ⊗ (Q_b A)`
  of §2 (Appendix A, Eq. (15)),
* the indefinite Hermitian construction of §7 on the `4N`-dimensional space,
* the schedules of Eq. (5)/(6) (AQC(p)) and Eq. (8) (AQC(exp)),
* the Schrödinger evolution Eq. (2) as the Frozen Dyson propagator `orderedEvolution`
  (`QuantumAlgorithm.Papers.QLinearODE17.TaylorAnalysis`,
  Frozen FQN `QuantumAlgorithm.Papers.QLinearODE17.TaylorAnalysis.orderedEvolution`),
* the density-matrix error `‖|ψ_T(s)⟩⟨ψ_T(s)| - |x̃⟩⟨x̃|‖₂` of §2.

The paper is normalized as `‖A‖₂ = 1` and `N = 2ⁿ`; here `N : ℕ` is arbitrary and
`‖A‖ = 1` is an explicit hypothesis of the statement files.
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder InnerProductSpace
open MeasureTheory
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Papers.QLinearSolver19.MainResults

set_option autoImplicit false

/-! ## Registers and kets -/

/-- The `N`-amplitude register `ℂ^N`. -/
abbrev Vec (N : ℕ) := EuclideanSpace ℂ (Fin N)

/-- The doubled register `ℂ^N ⊕ ℂ^N` of the positive-definite reduction (§2). -/
abbrev Block (N : ℕ) := EuclideanSpace ℂ (Fin N ⊕ Fin N)

/-- `|0⟩ ⊗ v`: `v` placed in the first block. -/
noncomputable def ketLeft {ι : Type*} (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (ι ⊕ ι) :=
  WithLp.toLp 2 (fun p : ι ⊕ ι => match p with
    | Sum.inl i => WithLp.ofLp v i
    | Sum.inr _ => 0)

/-- `|1⟩ ⊗ v`: `v` placed in the second block (the paper's `|b̄⟩ = |1,b⟩`). -/
noncomputable def ketRight {ι : Type*} (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (ι ⊕ ι) :=
  WithLp.toLp 2 (fun p : ι ⊕ ι => match p with
    | Sum.inl _ => 0
    | Sum.inr i => WithLp.ofLp v i)

/-- The paper's `|b̄⟩ = |1,b⟩`. -/
noncomputable def ketB {N : ℕ} (b : Vec N) : Block N := ketRight b

/-- The paper's `|0,x⟩`. -/
noncomputable def ketX {N : ℕ} (x : Vec N) : Block N := ketLeft x

/-- `|+⟩ = (|0⟩ + |1⟩)/√2` tensored with `v`, inside the doubled register. -/
noncomputable def ketPlus {N : ℕ} (v : Vec N) : Block N :=
  (Real.sqrt 2 : ℂ)⁻¹ • (ketLeft v + ketRight v)

/-- `|-⟩ = (|0⟩ - |1⟩)/√2` tensored with `v`, inside the doubled register. -/
noncomputable def ketMinus {N : ℕ} (v : Vec N) : Block N :=
  (Real.sqrt 2 : ℂ)⁻¹ • (ketLeft v - ketRight v)

/-! ## The positive-definite Hamiltonian pair of §2 -/

/-- The matrix `Q_b = I_N - |b⟩⟨b|`. -/
noncomputable def qbMat {N : ℕ} (b : Vec N) : Matrix (Fin N) (Fin N) ℂ :=
  1 - vecMulVec (WithLp.ofLp b) (star (WithLp.ofLp b))

/-- `H₀ = σ_x ⊗ Q_b = [[0, Q_b], [Q_b, 0]]` on `ℂ^N ⊕ ℂ^N`. -/
noncomputable def h0PD {N : ℕ} (b : Vec N) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  fromBlocks 0 (qbMat b) (qbMat b) 0

/-- `H₁ = σ₊ ⊗ (A Q_b) + σ₋ ⊗ (Q_b A) = [[0, A Q_b], [Q_b A, 0]]`. -/
noncomputable def h1PD {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (b : Vec N) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  fromBlocks 0 (A * qbMat b) (qbMat b * A) 0

/-- The affine Hamiltonian path `H(f) = (1 - f) H₀ + f H₁` of §2. -/
noncomputable def hPath {ι : Type} (H0 H1 : Matrix ι ι ℂ) (f : ℝ) : Matrix ι ι ℂ :=
  (1 - f) • H0 + f • H1

/-! ## The indefinite Hermitian construction of §7 -/

/-- `σ_z ⊗ I_N` on the doubled register `ℂ^N ⊕ ℂ^N`. -/
noncomputable def sigmaZBlock {N : ℕ} : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  fromBlocks 1 0 0 (-1)

/-- `σ_x ⊗ A` on the doubled register `ℂ^N ⊕ ℂ^N`. -/
noncomputable def sigmaXABlock {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  fromBlocks 0 A A 0

/-- `Q_{+,b} = I - |+,b⟩⟨+,b|`. -/
noncomputable def qPlusMat {N : ℕ} (b : Vec N) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  1 - vecMulVec (WithLp.ofLp (ketPlus b)) (star (WithLp.ofLp (ketPlus b)))

/-- §7's `H₀ = σ₊ ⊗ (σ_z ⊗ I)Q_{+,b} + σ₋ ⊗ Q_{+,b}(σ_z ⊗ I)`,
as the Hermitian block completion `[[0, M], [M', 0]]` with `M = (σ_z⊗I)Q_{+,b}`,
`M' = Q_{+,b}(σ_z⊗I)` (the paper's displayed sum). -/
noncomputable def h0Gen {N : ℕ} (b : Vec N) :
    Matrix ((Fin N ⊕ Fin N) ⊕ (Fin N ⊕ Fin N))
      ((Fin N ⊕ Fin N) ⊕ (Fin N ⊕ Fin N)) ℂ :=
  fromBlocks 0 (sigmaZBlock * qPlusMat b) (qPlusMat b * sigmaZBlock) 0

/-- §7's `H₁ = σ₊ ⊗ (σ_x ⊗ A)Q_{+,b} + σ₋ ⊗ Q_{+,b}(σ_x ⊗ A)`. -/
noncomputable def h1Gen {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (b : Vec N) :
    Matrix ((Fin N ⊕ Fin N) ⊕ (Fin N ⊕ Fin N))
      ((Fin N ⊕ Fin N) ⊕ (Fin N ⊕ Fin N)) ℂ :=
  fromBlocks 0 (sigmaXABlock A * qPlusMat b) (qPlusMat b * sigmaXABlock A) 0

/-! ## Schedules -/

/-- AQC(p) schedule, Eq. (5)/(6): `f(s) = κ/(κ-1) (1 - (1 + s(κ^{p-1}-1))^{1/(1-p)})`. -/
noncomputable def schedP (κ p s : ℝ) : ℝ :=
  κ / (κ - 1) *
    (1 - Real.rpow (1 + s * (Real.rpow κ (p - 1) - 1)) (1 / (1 - p)))

/-- The integrand `exp(-1/(t(1-t)))` of the AQC(exp) schedule, Eq. (8), extended by `0` outside
the open interval `(0,1)`.  This is the flat extension used in the paper around Lemma 8: all
derivatives vanish at `t = 0` and `t = 1`. -/
noncomputable def flatWeight (t : ℝ) : ℝ :=
  if t ∈ Set.Ioo (0 : ℝ) 1 then Real.exp (-(1 / (t * (1 - t)))) else 0

/-- The normalization constant `c_e = ∫₀¹ exp(-1/(t(1-t))) dt`. -/
noncomputable def expNorm : ℝ := ∫ t in (0 : ℝ)..1, flatWeight t

/-- AQC(exp) schedule, Eq. (8): `f(s) = c_e⁻¹ ∫₀^s exp(-1/(t(1-t))) dt`. -/
noncomputable def schedExp (s : ℝ) : ℝ := expNorm⁻¹ * ∫ t in (0 : ℝ)..s, flatWeight t

/-- The continuous-linear-map form of a square matrix, used to state spectral-gap conditions. -/
noncomputable def matCLM {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) H

/-- Positive-definite gap lower bound of Eq. (1) / Appendix A: `Δ*(f) = 1 - f + f/κ`. -/
noncomputable def gapStarPD (κ f : ℝ) : ℝ := 1 - f + f / κ

/-- Uniform gap lower bound of §7 / Appendix D–E: `Δ*(f) = (1 - f + f/κ)/√2`. -/
noncomputable def gapStar (κ f : ℝ) : ℝ := ((1 - f) + f / κ) / Real.sqrt 2

/-! ## Schrödinger evolution and the density-matrix error -/

/-- The generator `-i H` scaled by the runtime: Eq. (2) reads `∂_s ψ = -i T H ψ`. -/
noncomputable def aqcGenerator {ι : Type} (H : ℝ → Matrix ι ι ℂ) (T : ℝ) :
    ℝ → Matrix ι ι ℂ :=
  fun s => (Complex.I * (T : ℂ)) • H s

/-- The time-ordered propagator of Eq. (2), built from the Frozen Dyson series. -/
noncomputable def aqcPropagator {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : ℝ → Matrix ι ι ℂ) (T s : ℝ) : Matrix ι ι ℂ :=
  orderedEvolution (aqcGenerator H T) 0 s

/-- The evolved state `|ψ_T(s)⟩ = U_T(s) |ψ_T(0)⟩`. -/
noncomputable def aqcState {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : ℝ → Matrix ι ι ℂ) (T : ℝ) (ψ0 : EuclideanSpace ℂ ι) (s : ℝ) :
    EuclideanSpace ℂ ι :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (aqcPropagator H T s)) ψ0

/-- The rank-one density matrix `|v⟩⟨v|`. -/
noncomputable def density {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  InnerProductSpace.rankOne ℂ v v

/-- The ground-space projector `P₀ = |x̃⟩⟨x̃| + |b̄⟩⟨b̄|` of the positive-definite reduction
(paper page 5:15, proof of Lemma 5). -/
noncomputable def pdGroundProj {N : ℕ} (b x : Vec N) :
    Block N →L[ℂ] Block N :=
  density (ketX x) + density (ketB b)

/-- The paper's adiabatic infidelity `|1 - ⟨ψ_T(1)|P₀(1)|ψ_T(1)⟩|` for the positive-definite
AQC(exp) evolution (Theorem 6). -/
noncomputable def pdInfidelity {N : ℕ} (b x : Vec N)
    (H : ℝ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ) (T : ℝ) : ℝ :=
  ‖(1 : ℂ) - ⟪ketB b, pdGroundProj b x (aqcState H T (ketB b) 1)⟫_ℂ‖

/-- The spectral projector onto the kernel of a square matrix (the ground projector `P₀` when the
ground energy is normalized to `0`), realised as an orthogonal projection in finite dimension. -/
noncomputable def kerProj {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  let K : Submodule ℂ (EuclideanSpace ℂ ι) :=
    LinearMap.ker (matCLM H).toLinearMap
  letI : FiniteDimensional ℂ K := inferInstance
  letI : CompleteSpace K := FiniteDimensional.complete ℂ K
  K.starProjection

/-- The matrix of `kerProj`, used to state derivative estimates of the ground projector. -/
noncomputable def kerProjMat {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).symm (kerProj H)

/-- The resolvent `R(z,s) = (H(s) - z)⁻¹` of the paper (page 5:20, before Lemma 14). -/
noncomputable def resolventMat {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  (H - z • 1)⁻¹

/-- The paper's density-matrix error `‖|ψ_T(1)⟩⟨ψ_T(1)| - |x̃⟩⟨x̃|‖₂`. -/
noncomputable def aqcError {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : ℝ → Matrix ι ι ℂ) (T : ℝ) (ψ0 xt : EuclideanSpace ℂ ι) : ℝ :=
  ‖density (aqcState H T ψ0 1) - density xt‖

/-- The AQC(p) Hamiltonian path of Theorem 1/3 with the schedule Eq. (6). -/
noncomputable def hPathP {ι : Type} (H0 H1 : Matrix ι ι ℂ) (κ p : ℝ) : ℝ → Matrix ι ι ℂ :=
  fun s => hPath H0 H1 (schedP κ p s)

/-- The AQC(exp) Hamiltonian path of Theorem 2/4 with the schedule Eq. (8). -/
noncomputable def hPathExp {ι : Type} (H0 H1 : Matrix ι ι ℂ) : ℝ → Matrix ι ι ℂ :=
  fun s => hPath H0 H1 (schedExp s)

/-- Theorem 1/2 error: AQC on the positive-definite pair, starting at `|b̄⟩`, target `|0,x⟩`. -/
noncomputable def pdError {N : ℕ} (b x : Vec N)
    (H : ℝ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ) (T : ℝ) : ℝ :=
  aqcError H T (ketB b) (ketX x)

/-- Theorem 3/4 error: AQC on the §7 pair, starting at `|0,-,b⟩`, target `|0,+,x⟩`. -/
noncomputable def genError {N : ℕ} (b x : Vec N)
    (H : ℝ → Matrix ((Fin N ⊕ Fin N) ⊕ (Fin N ⊕ Fin N))
      ((Fin N ⊕ Fin N) ⊕ (Fin N ⊕ Fin N)) ℂ) (T : ℝ) : ℝ :=
  aqcError H T (ketLeft (ketMinus b)) (ketLeft (ketPlus x))

end Qatlib.Papers.QLinearSolver19.MainResults
