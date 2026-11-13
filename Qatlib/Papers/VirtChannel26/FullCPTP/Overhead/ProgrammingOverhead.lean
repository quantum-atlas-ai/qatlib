/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import QuantumInfo.Channels.CPTP
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Programming overhead for exact virtual channel programming

Fixed source: arXiv:2609.01419v1, "Exact Virtual Channel Programming with
Vanishing Excess Overhead" (Jing, Guo, Yao, Wang).  Supplemental Material,
Appendix A, Definition S1, Eq. (S2)--(S4).

This file fixes the operational objects used by every paper-layer contract of
`QuantumAlgorithmDev.Papers.VirtChannel26.FullCPTP`.

* A channel is a linear map `MatrixMap A B ℂ := Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ`
  (input system `A`, output system `B`).
* The normalized Choi program of `E` is `π_E := J_E / d_A` (Definition S1).  We
  use the output-first Choi convention of Physlib (`MatrixMap.choi_matrix`, on
  `B × A`); it agrees with the paper's input-first `J_E = (I ⊗ E)(Ω)` after the
  canonical tensor-factor swap, which changes neither the program state as an
  operator nor any of the overhead values.
* The exact `k`-copy overhead `ν_k(S)` is the infimum of `‖P‖_◇` over the
  HPTP maps `P` that reproduce every `E ∈ S` on the product memory `π_E^{⊗k}`
  (Eq. (S3)).
* The diamond norm is the finite-reference cb trace norm of Appendix A
  (`‖T‖_◇ = sup_{r, ‖X‖_1 ≤ 1} ‖(I_r ⊗ T)(X)‖_1`), specialized to general finite
  index types.  For `Fin d` indices it is definitionally the Frozen
  `Qatlib.Papers.RandCompiler19.ChannelBudget.finiteDiamondNorm`.

The paper works at `d_A = d_B = d` in the closed-form statements; the general
definitions below keep `A` and `B` separate because Appendix A also covers
`d_A ≠ d_B`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

namespace Qatlib.Papers.VirtChannel26.FullCPTP

/-- The tensor product of two operators under the canonical `A × P` ordering.
This is the identification used for the source/reference/program registers. -/
def kronOp {A P : Type*} (X : Matrix A A ℂ) (Y : Matrix P P ℂ) :
    Matrix (A × P) (A × P) ℂ :=
  fun (a, p) (a', p') => X a a' * Y p p'

/-- The `k`-fold Kronecker power on the tuple index `Fin k → ι`.  For `k = 0`
this is the `1 × 1` unit. -/
def tensorPow {ι : Type*} (M : Matrix ι ι ℂ) (k : ℕ) :
    Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  fun x y => ∏ i : Fin k, M (x i) (y i)

/-- One-sided amplification `I_r ⊗ T` on the doubled index `A × R`, written out
on entries so that it applies to arbitrary finite index types.  This is the
reference-amplification appearing in Definition S1 and Lemma S1. -/
def tensorLeftGen {A B R : Type*} (T : MatrixMap A B ℂ)
    (X : Matrix (A × R) (A × R) ℂ) : Matrix (B × R) (B × R) ℂ :=
  fun (b, r) (b', r') => T (fun a a' => X (a, r) (a', r')) b b'

/-- The finite-reference completely bounded trace norm (diamond norm),
`sup_{r, ‖X‖_1 ≤ 1} ‖(I_r ⊗ T)(X)‖_1`.  This is the general-index form of
Frozen's `finiteDiamondNorm`; for `Fin D`/`Fin E` it coincides with it. -/
def diamondNorm {A B : Type*} [Fintype A] [Fintype B] (T : MatrixMap A B ℂ) : ℝ≥0∞ :=
  ⨆ r : ℕ, ⨆ X : Matrix (A × Fin r) (A × Fin r) ℂ,
    if Matrix.traceNorm X ≤ 1 then ENNReal.ofReal (Matrix.traceNorm (tensorLeftGen T X)) else 0

/-- Normalized Choi program state `π_E = J_E / d_A` (Definition S1), using the
Physlib output-first Choi matrix on `B × A`. -/
def choiProgram {A B : Type*} [Fintype A] (E : MatrixMap A B ℂ) :
    Matrix (B × A) (B × A) ℂ :=
  ((Fintype.card A : ℂ)⁻¹) • E.choi_matrix

/-- `P` is an exact `k`-copy retriever for the channel family `S` (Eq. (S3)):
it is independent of `E` and reproduces `E` on every input operator from the
product program memory `π_E^{⊗k}`. -/
def IsExactRetriever {A B : Type*} [Fintype A] (k : ℕ)
    (S : Set (MatrixMap A B ℂ))
    (P : MatrixMap (A × (Fin k → (B × A))) B ℂ) : Prop :=
  ∀ E ∈ S, ∀ ρ : Matrix A A ℂ,
    P (kronOp ρ (tensorPow (choiProgram E) k)) = E ρ

/-- The exact `k`-copy programming overhead `ν_k(S)` of Definition S1 / Eq. (S3):
the infimum of `‖P‖_◇` over all exact retrievers.  Values are in `ℝ≥0∞`, so an
empty feasible set correctly records `+∞`. -/
def overhead {A B : Type*} [Fintype A] [Fintype B] (k : ℕ)
    (S : Set (MatrixMap A B ℂ)) : ℝ≥0∞ :=
  sInf {x : ℝ≥0∞ | ∃ P : MatrixMap (A × (Fin k → (B × A))) B ℂ,
    IsExactRetriever k S P ∧ x = diamondNorm P}

/-- The family `CPTP_d` of all quantum channels on a `d`-dimensional system. -/
def cptpFamily (d : ℕ) : Set (MatrixMap (Fin d) (Fin d) ℂ) :=
  {E | E.IsCompletelyPositive ∧ E.IsTracePreserving}

/-- Channels realized by conjugation with a unitary matrix (`Ad_U`). -/
def unitaryFamily (d : ℕ) : Set (MatrixMap (Fin d) (Fin d) ℂ) :=
  {E | ∃ U : Matrix (Fin d) (Fin d) ℂ,
      U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ ∀ X, E X = U * X * star U}

/-- Unitary channels whose implementing unitary has determinant one, i.e. the
adjoint action of `SU(d)` (`Ad_SU(d)`). -/
def suFamily (d : ℕ) : Set (MatrixMap (Fin d) (Fin d) ℂ) :=
  {E | ∃ U : Matrix (Fin d) (Fin d) ℂ,
      U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ U.det = 1 ∧ ∀ X, E X = U * X * star U}

/-- The real-channel family `L_R`: channels whose Choi matrix is real in the
fixed computational basis (Appendix E). -/
def realFamily (d : ℕ) : Set (MatrixMap (Fin d) (Fin d) ℂ) :=
  {E | E.IsCompletelyPositive ∧ E.IsTracePreserving ∧
      ∀ i j, (E.choi_matrix i j).im = 0}

/-- The unital-channel family `T(d)`: quantum channels with `E(I) = I`. -/
def unitalFamily (d : ℕ) : Set (MatrixMap (Fin d) (Fin d) ℂ) :=
  {E | E.IsCompletelyPositive ∧ E.IsTracePreserving ∧ E 1 = 1}

/-- The all-channel `k`-copy overhead `ν_k(CPTP_d)`. -/
def nuCPTP (d k : ℕ) : ℝ≥0∞ := overhead k (cptpFamily d)

/-- The normalized maximally entangled operator `Φ_d = Ω_d / d` on the doubled
index `Fin d × Fin d` (Appendix A). -/
def phi (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ((d : ℂ)⁻¹) • fun (a, b) (a', b') => if a = b ∧ a' = b' then 1 else 0

/-- The unnormalized maximally entangled operator `Ω_d = |I_d⟩⟩⟨⟨I_d|`. -/
def omega (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun (a, b) (a', b') => if a = b ∧ a' = b' then 1 else 0

/-- `Ω` on an arbitrary index type, the unnormalized maximally entangled
operator `|I⟩⟩⟨⟨I|`. -/
def omegaOn (A : Type*) : Matrix (A × A) (A × A) ℂ :=
  fun (a, b) (a', b') => if a = b ∧ a' = b' then 1 else 0

/-- The normalized maximally entangled operator `Φ = Ω / dim` on an arbitrary
finite index type. -/
def phiOn (A : Type*) [Fintype A] : Matrix (A × A) (A × A) ℂ :=
  ((Fintype.card A : ℂ)⁻¹) • omegaOn A

/-- Hermiticity preservation of a linear map on operators. -/
def IsHermiticityPreserving {A B : Type*} (E : MatrixMap A B ℂ) : Prop :=
  ∀ X : Matrix A A ℂ, X.IsHermitian → (E X).IsHermitian

/-- Joint covariance `V_g† ∘ E ∘ U_g = E` of Lemma S1, written on operator
arguments: `E (U_g X U_g†) = V_g (E X) V_g†`. -/
def IsJointlyCovariant {G A B : Type*} [Fintype A] [Fintype B]
    (E : MatrixMap A B ℂ) (U : G → Matrix A A ℂ) (V : G → Matrix B B ℂ) : Prop :=
  ∀ g (X : Matrix A A ℂ),
    E (U g * X * star (U g)) = V g * E X * star (V g)

/-- The one-design condition of Lemma S1: the group average of `U_g X U_g†` is
the maximally mixed operator `(Tr X / dim) I`. -/
def IsOneDesign {G A : Type*} [Fintype G] [Fintype A] (U : G → Matrix A A ℂ) : Prop :=
  ∀ X : Matrix A A ℂ,
    ((Fintype.card G : ℂ)⁻¹) • (∑ g : G, U g * X * star (U g)) =
      ((Matrix.trace X / (Fintype.card A : ℂ))) • (1 : Matrix A A ℂ)

/-- Self-conjugacy of a pair of representations (Definition S2): for every `g`
there is `h` with `U_h = U_gᵀ` and `V_h = V_gᵀ` up to the phases absorbed by the
adjoint action.  Encoded at the level of the representation matrices. -/
def IsSelfConjugate {G A B : Type*} (U : G → Matrix A A ℂ) (V : G → Matrix B B ℂ) : Prop :=
  ∀ g, ∃ h, U h = (U g).transpose ∧ V h = (V g).transpose

/-- Post-composition family `F ∘ S := {F ∘ E : E ∈ S}` (Appendix G). -/
def postComposeFamily {A B : Type*} [Fintype A] [Fintype B]
    (F : MatrixMap B B ℂ) (S : Set (MatrixMap A B ℂ)) : Set (MatrixMap A B ℂ) :=
  {G | ∃ E ∈ S, ∀ X : Matrix A A ℂ, G X = F (E X)}

/-- Pre-composition family `S ∘ V := {E ∘ V : E ∈ S}` (Appendix G). -/
def preComposeFamily {A B : Type*} [Fintype A] [Fintype B]
    (S : Set (MatrixMap A B ℂ)) (V : MatrixMap A A ℂ) : Set (MatrixMap A B ℂ) :=
  {G | ∃ E ∈ S, ∀ X : Matrix A A ℂ, G X = E (V X)}

/-- The tensor-product channel set `S₁ ⊗ S₂` of Definition S5, using the
Physlib tensor product `MatrixMap.kron` on product index types. -/
def tensorFamily {A1 B1 A2 B2 : Type*} [Fintype A1] [Fintype B1] [Fintype A2] [Fintype B2]
    (S1 : Set (MatrixMap A1 B1 ℂ)) (S2 : Set (MatrixMap A2 B2 ℂ)) :
    Set (MatrixMap (A1 × A2) (B1 × B2) ℂ) :=
  {G | ∃ E1 ∈ S1, ∃ E2 ∈ S2, G = MatrixMap.kron E1 E2}

/-- A set `S` is `(G, U, V)`-covariant when output-conjugating by `V_g` and
input-conjugating by `U_g†` maps each member back into `S` (Definition S2). -/
def IsCovariant {G A B : Type*} [Fintype A] [Fintype B]
    (S : Set (MatrixMap A B ℂ))
    (U : G → Matrix A A ℂ) (V : G → Matrix B B ℂ) : Prop :=
  ∀ g (E : MatrixMap A B ℂ), E ∈ S →
    ∃ E' ∈ S, ∀ X : Matrix A A ℂ,
      E' X = V g * E (star (U g) * X * U g) * star (V g)

/-- Representation-theoretic commutant of the `k`-copy action on the total
program space (Definition S2, Eq. (S6) and its `k`-fold version Eq. (S79)). -/
def commutantOf {H G : Type*} [Fintype H] (ρ : G → Matrix H H ℂ) :
    Set (Matrix H H ℂ) :=
  {X | ∀ g, ρ g * X = X * ρ g}

end Qatlib.Papers.VirtChannel26.FullCPTP
