/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumEntropy.EntropyCalculus

set_option backward.isDefEq.respectTransparency false

/-!
# Source model for arXiv:1106.1445v8 (Wilde, *From Classical to Quantum Shannon Theory*)

Fixed paper version: **arXiv:1106.1445v8** (v8, 2019-07-14).

This file fixes the finite-dimensional vocabulary used by every paper-layer
statement in this directory.  The state/entropy/relative-entropy layer reuses
the `Qatlib.Concepts.QuantumEntropy.EntropyCalculus`
interface (`Density`, `entropy`, `relative`, `MState.traceLeft/traceRight`);
fidelity, trace distance, effects, POVMs, Kraus representations and the
composite entropies are defined here from those primitives.

Conventions
* `Op I` is the complex matrix algebra on a finite index type `I`.
* `Dens I` is the `Density I` subtype: PSD and trace one.
* A bipartite state `ρ : Dens (A × B)` has marginals `marginR` (on `A`) and
  `marginL` (on `B`); `H_A`/`H_B` denote `H(A)`/`H(B)`.
* A tripartite state is written `Dens (A × C × B)` with the *conditioning*
  system `C` in the middle, matching the library's strong-subadditivity order.
-/

namespace Qatlib.Papers.QShannonWilde11.MainResults.Model

open Matrix
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open scoped BigOperators ComplexOrder ENNReal MatrixOrder

noncomputable section

/-! ## Operators, states, pure vectors -/

/-- Operators on a finite index type. -/
abbrev Op (I : Type) : Type _ := Matrix I I ℂ

/-- Density operators: the PSD trace-one subtype. -/
abbrev Dens (I : Type) [Fintype I] [DecidableEq I] : Type _ := Density I

/-- A unit vector. -/
def IsUnitVec {I : Type} [Fintype I] (ψ : I → ℂ) : Prop :=
  (∑ i, ‖ψ i‖ ^ 2) = 1

/-- The rank-one operator `|ψ⟩⟨ψ|`. -/
def outerProduct {I : Type} [Fintype I] [DecidableEq I] (ψ : I → ℂ) : Op I :=
  fun i j => ψ i * star (ψ j)

/-- A PSD operator of trace at most one (the paper's `σ` with `Tr σ ≤ 1`). -/
def IsSubDensity {I : Type} [Fintype I] [DecidableEq I] (σ : Op I) : Prop :=
  σ.PosSemidef ∧ (Matrix.trace σ).re ≤ 1

/-- A measurement operator (effect): `0 ≤ Λ ≤ I`. -/
def IsEffect {I : Type} [Fintype I] [DecidableEq I] (Λ : Op I) : Prop :=
  Λ.PosSemidef ∧ (1 - Λ).PosSemidef

/-- A POVM indexed by `ι`. -/
def IsPOVM {I ι : Type} [Fintype I] [DecidableEq I] [Fintype ι] (M : ι → Op I) : Prop :=
  (∀ j, (M j).PosSemidef) ∧ (∑ j, M j) = 1

/-! ## Fidelity and trace distance -/

/-- Root fidelity `‖√ρ √σ‖₁` (the paper's `√F(ρ,σ)`). -/
def rootFidelity {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Op I) : ℝ :=
  Matrix.traceNorm (CFC.sqrt ρ * CFC.sqrt σ)

/-- Uhlmann fidelity `F(ρ,σ) = ‖√ρ √σ‖₁²`. -/
def fidelity {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Op I) : ℝ :=
  (rootFidelity ρ σ) ^ 2

/-- The (unnormalised) trace distance `‖ρ−σ‖₁`. -/
def traceNormDiff {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Op I) : ℝ :=
  Matrix.traceNorm (ρ - σ)

/-- The paper's normalised trace distance `½‖ρ−σ‖₁`. -/
def traceDist {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Op I) : ℝ :=
  (1 / 2) * Matrix.traceNorm (ρ - σ)

/-- The sum of singular values `Σ_i σ_i(M)`, computed as `Tr √(M†M)` (Prop. 9.1.1). -/
def singularValueSum {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (Matrix.trace (CFC.sqrt (Mᴴ * M))).re

/-- The operator `√Λ ρ √Λ` (post-measurement operator, §9.4). -/
def sandwich {d : ℕ} (Λ ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  CFC.sqrt Λ * ρ * CFC.sqrt Λ

/-- Entanglement fidelity `F_e(ρ, N) = Σ_m |Tr(ρ K_m)|²` (Thm 9.5.1). -/
def entanglementFidelity {d : ℕ} {ι : Type} [Fintype ι]
    (K : ι → Matrix (Fin d) (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ m, ‖Matrix.trace (ρ * K m)‖ ^ 2

/-! ## Entropic quantities -/

/-- Von Neumann entropy `H(ρ)`. -/
def vnH {I : Type} [Fintype I] [DecidableEq I] (ρ : Dens I) : ℝ := entropy ρ

/-- Marginal on the first factor of a bipartite state. -/
def marginR {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Dens (A × B)) : Dens A := localState (state ρ).traceRight

/-- Marginal on the second factor of a bipartite state. -/
def marginL {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Dens (A × B)) : Dens B := localState (state ρ).traceLeft

/-- `H(A)` of a bipartite state. -/
def H_A {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Dens (A × B)) : ℝ := entropy (marginR ρ)

/-- `H(B)` of a bipartite state. -/
def H_B {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Dens (A × B)) : ℝ := entropy (marginL ρ)

/-- Conditional entropy `H(A|B) = H(AB) − H(B)`. -/
def Hcond {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Dens (A × B)) : ℝ := entropy ρ - entropy (marginL ρ)

/-- Quantum mutual information `I(A;B) = H(A)+H(B)−H(AB)`. -/
def mutualInfo {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Dens (A × B)) : ℝ := entropy (marginR ρ) + entropy (marginL ρ) - entropy ρ

/-- Coherent information `I(A⟩B) = H(B) − H(AB)`. -/
def cohInfo {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Dens (A × B)) : ℝ := entropy (marginL ρ) - entropy ρ

/-- Coherent information `I(B⟩A) = H(A) − H(AB)`. -/
def cohInfoBA {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Dens (A × B)) : ℝ := entropy (marginR ρ) - entropy ρ

/-- Conditional quantum mutual information, with the conditioning system in the
middle: for `ρ : Dens (A × C × B)`,
`I(A;B|C) = H(AC)+H(BC)−H(ABC)−H(C)`. -/
def cmi {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (ρ : Dens (A × C × B)) : ℝ :=
  entropy (localState (state ρ).assoc'.traceRight)
    + entropy (localState (state ρ).traceLeft)
    - entropy ρ
    - entropy (localState (state ρ).traceLeft.traceRight)

/-- Quantum relative entropy `D(ρ‖σ)` as an extended nonnegative real. -/
def relEnt {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Dens I) : ℝ≥0∞ := relative ρ σ

/-- The finite real value of `D(ρ‖σ)` (zero if infinite). -/
def relEntR {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Dens I) : ℝ := (relative ρ σ).toReal

/-! ## Channels and Kraus representations -/

/-- Finite quantum channels (linear, completely positive, trace preserving). -/
abbrev QChannel (a b : ℕ) : Type _ :=
  Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel a b

/-- A Kraus representation of a finite linear map `N` (paper Theorem 4.4.1 /
Eq. (4.1) conventions). -/
def IsKraus {a b : ℕ} (N : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ)
    {ι : Type} [Fintype ι] (K : ι → Matrix (Fin b) (Fin a) ℂ) : Prop :=
  (∀ X : Matrix (Fin a) (Fin a) ℂ, N X = ∑ j, K j * X * (K j)ᴴ) ∧
  (∑ j, (K j)ᴴ * K j) = 1

/-- Partial trace over the second factor of a bipartite operator. -/
def ptraceSecond {X Y : Type} [Fintype Y] (M : Matrix (X × Y) (X × Y) ℂ) :
    Matrix X X ℂ :=
  fun i k => ∑ j, M (i, j) (k, j)

/-- Projector onto the register value `j` in a bipartite index `X × ι`. -/
def regProj {X ι : Type} [DecidableEq X] [DecidableEq ι] (j : ι) :
    Matrix (X × ι) (X × ι) ℂ :=
  fun x y => if x.2 = j ∧ y.2 = j ∧ x.1 = y.1 then 1 else 0

/-- The isometric extension `U = Σ_j K_j ⊗ |j⟩_E` of a Kraus family
(paper Eqs. (5.35)–(5.36)). -/
def isometricExtension {a b : ℕ} {ι : Type} (K : ι → Matrix (Fin b) (Fin a) ℂ) :
    Matrix (Fin b × ι) (Fin a) ℂ :=
  fun (bo, j) ai => K j bo ai

/-- The coherent-instrument unitary `U = Σ_j Σ_l K^j_l ⊗ |j⟩_J ⊗ |j⟩_{E_J}`
(paper Eqs. (5.81)–(5.85)); the output index is
`Fin b × (κ × (ι × ι))` with `κ` the environment `E`, the first `ι` the register
`J`, and the second `ι` the register `E_J`. -/
def coherentInstrument {a b : ℕ} {ι κ : Type} [DecidableEq ι]
    (K : ι → κ → Matrix (Fin b) (Fin a) ℂ) :
    Matrix (Fin b × (κ × (ι × ι))) (Fin a) ℂ :=
  fun p ai => if p.2.2.1 = p.2.2.2 then K p.2.2.1 p.2.1 p.1 ai else 0

/-- The coherent-measurement isometry `U = Σ_j M_j ⊗ |j⟩_{S'}` (Eqs. (5.88)–(5.91)). -/
def coherentMeasurement {d : ℕ} {ι : Type} (M : ι → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × ι) (Fin d) ℂ :=
  fun p ai => M p.2 p.1 ai

/-- A channel is unital when it preserves the identity. -/
def IsUnital {a b : ℕ} (N : QChannel a b) : Prop :=
  N.map 1 = 1

/-- `M` is the Hilbert–Schmidt adjoint of the linear map `N`. -/
def IsAdjoint {a b : ℕ}
    (N : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ)
    (M : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ) : Prop :=
  ∀ X Y, Matrix.trace ((N X)ᴴ * Y) = Matrix.trace (Xᴴ * (M Y))

/-- An entanglement-breaking map has a rank-one Kraus (measure-and-prepare)
decomposition, `N(ρ) = Σ_j ⟨φ_j|ρ|φ_j⟩ |ψ_j⟩⟨ψ_j|` (Thm 4.6.1). -/
def IsEntanglementBreaking {a b : ℕ} (N : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ]
    Matrix (Fin b) (Fin b) ℂ) {ι : Type} [Fintype ι]
    (φ : ι → (Fin a → ℂ)) (ψ : ι → (Fin b → ℂ)) : Prop :=
  ∀ X, N X = ∑ j, (∑ i, ∑ k, (φ j) i * X i k * star ((φ j) k)) •
    Matrix.of (fun u v => (ψ j) u * star ((ψ j) v))

/-- `φ` purifies `ρ` on a reference system `R` (paper §5.1): the partial trace
of `|φ⟩⟨φ|` over `R` is `ρ`. -/
def IsPurification {A R : Type} [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    (φ : A × R → ℂ) (ρ : Dens A) : Prop :=
  IsUnitVec φ ∧ ptraceSecond (outerProduct φ) = (state ρ).m

/-! ## Classical ensembles and Holevo information -/

/-- A classical-quantum ensemble: probabilities `p` over an index `X` and states
`ρs`. -/
structure Ensemble (X : Type) [Fintype X] (A : Type) [Fintype A] [DecidableEq A] where
  p : X → ℝ
  p_nonneg : ∀ x, 0 ≤ p x
  p_sum : (∑ x, p x) = 1
  ρs : X → Dens A

/-- The average state of an ensemble, stated as a predicate on a supplied state. -/
def IsAverage {X A : Type} [Fintype X] [Fintype A] [DecidableEq A]
    (E : Ensemble X A) (σ : Dens A) : Prop :=
  (state σ).m = ∑ x, E.p x • (state (E.ρs x)).m

/-- The Holevo information `χ = H(σ) − Σ_x p(x) H(ρ_x)` of an ensemble, given
its average state `σ` (constrained by `IsAverage`). -/
def holevo {X A : Type} [Fintype X] [Fintype A] [DecidableEq A]
    (E : Ensemble X A) (σ : Dens A) : ℝ :=
  entropy σ - ∑ x, E.p x * entropy (E.ρs x)

/-! ## Channel action and diamond distance -/

/-- Apply a channel to the second factor: `(id_r ⊗ N)(ρ)`. -/
def applyRight {r a b : ℕ} (N : QChannel a b)
    (ρ : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    Matrix (Fin r × Fin b) (Fin r × Fin b) ℂ :=
  fun (i, x) (j, y) => N.map (fun u v => ρ (i, u) (j, v)) x y

/-- Diamond-norm distance with the reference dimension left free (Thm 9.1.1). -/
def diamondDist {a b : ℕ} (N M : QChannel a b) : ℝ :=
  sSup { t : ℝ | ∃ (r : ℕ) (ρ : Dens (Fin r × Fin a)),
    t = traceDist (applyRight N (state ρ).m) (applyRight M (state ρ).m) }

end

end Qatlib.Papers.QShannonWilde11.MainResults.Model
