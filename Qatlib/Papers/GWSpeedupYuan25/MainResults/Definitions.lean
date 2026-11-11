/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Defs

set_option backward.isDefEq.respectTransparency false

/-!
# GWSpeedupYuan25 — paper-level model for Goemans–Williamson with Pauli sparsity

Yuan, Stilck França, Luchnikov, Tiunov, Haug, Aolita.
Fixed arXiv:2510.08292v1 (9 Oct 2025). PDF SHA-256 as recorded in
`metadata/papers/GWSpeedupYuan25.json` extraction block.

This file fixes the elementary mathematical objects that the paper uses
throughout §II (Notation and Basic Concepts):

* `Reg n = Fin n → Bool` — the computational-basis register of an `n`-qubit
  system; the dimension is `2^n`.
* `ZMat n A` — the Pauli Z-string `Z_A` of §II D (Eq. (9)) written as a
  diagonal `±1` matrix, for a subset `A : Finset (Fin n)`.
* `PauliIndex n = Reg n × Reg n` — the `(x,z) ∈ {0,1}^{2n}` label of a Pauli
  string; `PauliIndex n → ℝ` is the coefficient function of a Pauli expansion
  (Eqs. (10)–(12)).
* `pauliL1` — the Pauli `ℓ1` norm `‖C‖_{P,ℓ1}` (Definition 3 / Definition 31).
* `GwFeasible` / `gwValue` — the relaxed Goemans–Williamson program of
  Definition 4 / Definition 11 (Eq. (17) and Eq. (27)).
* `ugwValue` — the unnormalised GW program of Eq. (2).
* `quboValue` — the QUBO value of Eq. (1).
* `lambdaMax` — the largest eigenvalue via the Rayleigh quotient
  (variational characterisation used in Corollary 6 / Corollary 16).
* `pauliSpan` / `diagGroup` — the diagonal group `D_C` of Definition 1 in its
  classical GF(2) symplectic-vector representation (§II D).
* `gwHamiltonian` / `gibbsState` — the HU Gibbs state `σ(λ)` of Eq. (7) /
  Eq. (21) and the Hamiltonian `H(λ,C,S)` of Lemma 13, Eq. (29).

Boundary: this is the paper's own model layer. It does not import or claim any
prerequisite unit; it reuses only Mathlib's generic matrix/measure API.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GWSpeedupYuan25.MainResults

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- The computational-basis register of an `n`-qubit system, `Reg n = Fin n → Bool`,
of cardinality `2^n`. -/
abbrev Reg (n : ℕ) := Fin n → Bool

/-! ## §1 Pauli Z-strings (paper §II D, Eq. (9)) -/

/-- The `Z_A` character in `±1` form evaluated at a bit string:
`∏ i ∈ A, (-1)^{x_i}`. This is the diagonal entry of the Pauli Z-string `Z_A`. -/
def zSign (n : ℕ) (A : Finset (Fin n)) (x : Reg n) : ℂ :=
  ∏ i ∈ A, if x i then (-1 : ℂ) else 1

/-- The Pauli Z-string `Z_A` (`A ⊆ [n]`) as a diagonal `±1` matrix. For `A = ∅`
this is the identity. This is the diagonal matrix `P_(0,z_A)` of §II D, Eq. (9). -/
def ZMat (n : ℕ) (A : Finset (Fin n)) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (zSign n A)

/-! ## §2 Pauli expansions, support and ℓ1 norm (Definition 3 / Definition 31) -/

/-- A Pauli label `(x,z) ∈ {0,1}^{2n}`: the X-part and the Z-part. -/
abbrev PauliIndex (n : ℕ) := Reg n × Reg n

/-- The Pauli `ℓ1` norm of a coefficient function, `∑ |c_p|` (Definition 3,
Eq. (16); repeated as Definition 31, Eq. (B2)). Stated for a general finite
index so that it applies to a single-system Pauli index `PauliIndex n` as well
as to a product (Kronecker) index. -/
def pauliL1 {ι : Type*} [Fintype ι] (c : ι → ℝ) : ℝ :=
  ∑ p, |c p|

/-- The Pauli support `P_supp(C) = {(x,z) | c_(x,z) ≠ 0}`. -/
def pauliSupport {n : ℕ} (c : PauliIndex n → ℝ) : Set (PauliIndex n) :=
  {p | c p ≠ 0}

/-- `C` is Pauli-sparse in the sense of Definition 2: its support has at most
polynomially (in `n`) many nonzero Pauli coefficients. -/
def PauliSparse {n : ℕ} (c : PauliIndex n → ℝ) : Prop :=
  ∃ k : ℕ, (pauliSupport c).ncard ≤ (n + 1) ^ k

/-- The weight `w(P_(x,z))` of a Pauli string: the number of sites where the
Pauli is not the identity (i.e. the X- or Z-part is nonzero). -/
def pauliWeight {n : ℕ} (p : PauliIndex n) : ℕ :=
  (Finset.univ.filter (fun i => p.1 i = true ∨ p.2 i = true)).card

/-- `C` has Pauli weight at most `k` (Definition 2, Eq. (14)). -/
def WeightAtMost {n : ℕ} (c : PauliIndex n → ℝ) (k : ℕ) : Prop :=
  ∀ p, c p ≠ 0 → pauliWeight p ≤ k

/-! ## §3 The relaxed Goemans–Williamson program (Definition 4 / Definition 11) -/

/-- A density matrix on `n` qubits: positive semidefinite with unit trace. -/
def IsDensity {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

/-- Feasibility for `GW(C,S,ε)` (Eq. (17) / Eq. (27)): `ρ` is a density matrix
and `|tr[Z_A ρ]| ≤ ε` for every `A ∈ S`. -/
def GwFeasible (n : ℕ) (S : Set (Finset (Fin n))) (ε : ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) : Prop :=
  IsDensity ρ ∧ ∀ A ∈ S, ‖(ZMat n A * ρ).trace‖ ≤ ε

/-- The normalised GW objective `tr[(C/‖C‖) ρ]`. -/
def gwObjective {n : ℕ} (C : Matrix (Reg n) (Reg n) ℂ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) : ℝ :=
  ((C * ρ).trace).re / ‖C‖

/-- The set of objective values attained by feasible points of `GW(C,S,ε)`. -/
def gwObjSet (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (S : Set (Finset (Fin n))) (ε : ℝ) : Set ℝ :=
  {v : ℝ | ∃ ρ : Matrix (Reg n) (Reg n) ℂ, GwFeasible n S ε ρ ∧ v = gwObjective C ρ}

/-- `GW(C,S,ε)`: the value of the relaxed GW program, Eq. (17) / Eq. (27). -/
def gwValue (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (S : Set (Finset (Fin n))) (ε : ℝ) : ℝ :=
  sSup (gwObjSet n C S ε)

/-- The full constraint set `2^[n] \ {∅}` used by the original GW program. -/
def fullConstraints (n : ℕ) : Set (Finset (Fin n)) := {A | A ≠ ∅}

/-- The unnormalised GW program `uGW(C)`, Eq. (2): `max tr[CY]` over
positive semidefinite `Y` with unit diagonal. -/
def ugwValue (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ) : ℝ :=
  sSup {v : ℝ | ∃ Y : Matrix (Reg n) (Reg n) ℂ,
    Y.PosSemidef ∧ (∀ i, Y i i = 1) ∧ v = ((C * Y).trace).re}

/-- The `±1` lift of a Boolean bit. -/
def bitSign : Bool → ℝ
  | true => 1
  | false => -1

/-- A `±1`-valued vector on the register (`{±1}^D`, `D = 2^n`). -/
def IsPlusMinus {n : ℕ} (x : Reg n → ℝ) : Prop := ∀ i, x i = 1 ∨ x i = -1

/-- The QUBO value `QUBO(C) = max_{x ∈ {±1}^D} ⟨x, C x⟩`, Eq. (1). -/
def quboValue (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ) : ℝ :=
  sSup {v : ℝ | ∃ x : Reg n → ℝ, IsPlusMinus x ∧
    v = ∑ i, ∑ j, x i * (C i j).re * x j}

/-- Rayleigh quotient `⟨v, C v⟩ / ⟨v, v⟩` for a complex vector. -/
def rayleigh {n : ℕ} (C : Matrix (Reg n) (Reg n) ℂ) (v : Reg n → ℂ) : ℝ :=
  ((∑ i, ∑ j, (star (v i)) * C i j * v j)).re / ((∑ i, (star (v i)) * v i).re)

/-- The largest eigenvalue `λ_max(C)` via the Rayleigh-quotient variational
characterisation (used in Corollary 6 / Corollary 16, Eq. (20) / Eq. (33)). -/
def lambdaMax (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ v : Reg n → ℂ, v ≠ 0 ∧ r = rayleigh C v}

/-! ## §4 Diagonal group of `C` in symplectic GF(2) form (Definition 1) -/

/-- The GF(2) characteristic vector of a subset `A ⊆ [n]`. -/
def vectorOfFinset {n : ℕ} (A : Finset (Fin n)) : Fin n → ZMod 2 :=
  fun i => if i ∈ A then 1 else 0

/-- The symplectic vector `(x,z) ∈ GF(2)^{2n}` of a Pauli label. -/
def sympVec {n : ℕ} (p : PauliIndex n) : (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  (fun i => if p.1 i = true then 1 else 0, fun i => if p.2 i = true then 1 else 0)

/-- The GF(2)-span of the Pauli labels in the support of `C` — the group `G_C`
of Definition 1 in its symplectic-vector representation. -/
def pauliSpan {n : ℕ} (support : Set (PauliIndex n)) :
    Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
  Submodule.span (ZMod 2) (sympVec '' support)

/-- The traceless diagonal group `Ḋ_C = D_C \ {I}` of `C`, presented as the set of
nonempty subsets `A` whose diagonal Pauli `(0, z_A)` lies in the GF(2)-span of
the support (Definition 1). -/
def diagGroup {n : ℕ} (support : Set (PauliIndex n)) : Set (Finset (Fin n)) :=
  {A | ((0 : Fin n → ZMod 2), vectorOfFinset A) ∈ pauliSpan support ∧ A ≠ ∅}

/-! ## §5 Gibbs states and the HU Hamiltonian (Eq. (7), Eq. (21), Eq. (29)) -/

/-- The matrix exponential `exp H` (Mathlib `NormedSpace.exp` under the scoped
`L2Operator` matrix normalisation, which is the matrix exponential). -/
def matrixExp {n : ℕ} (H : Matrix (Reg n) (Reg n) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  NormedSpace.exp H

/-- The Gibbs state `σ(H) ∝ exp(H)` normalised to unit trace. -/
def gibbsState {n : ℕ} (H : Matrix (Reg n) (Reg n) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  ((Matrix.trace (matrixExp H))⁻¹) • matrixExp H

/-- The HU Hamiltonian `H(λ,C,S) = -λ_C (C/‖C‖) - ∑_{A∈S} λ_A Z_A` of Lemma 13,
Eq. (29). The parameters are given as a real `λ_C` and a real-valued function on
the finite constraint set. -/
def gwHamiltonian (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (S : Finset (Finset (Fin n))) (lamC : ℝ) (lam : Finset (Fin n) → ℝ) :
    Matrix (Reg n) (Reg n) ℂ :=
  (-(lamC : ℂ)) • ((‖C‖)⁻¹ • C) - ∑ A ∈ S, (lam A : ℂ) • ZMat n A

/-- The parameter `ℓ1` mass `|λ_C| + ∑_{A∈S} |λ_A|` appearing in Eq. (7) and
Lemma 13. -/
def lambdaL1 {n : ℕ} (S : Finset (Finset (Fin n))) (lamC : ℝ)
    (lam : Finset (Fin n) → ℝ) : ℝ :=
  |lamC| + ∑ A ∈ S, |lam A|

/-- The HU Gibbs family `σ(λ) ∝ exp(λ_0 C/‖C‖ + ∑ λ_i Z_{A_i})` of Eq. (21)
(here written with the Hamiltonian sign convention of `gwHamiltonian`). -/
def huGibbs (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (S : Finset (Finset (Fin n))) (lamC : ℝ) (lam : Finset (Fin n) → ℝ) :
    Matrix (Reg n) (Reg n) ℂ :=
  gibbsState (gwHamiltonian n C S lamC lam)

/-! ## §6 Diagonal constraints of order `k` (Definition 19, Eq. (44)) -/

/-- The set of diagonal Paulis obtainable as products of at most `k` Paulis of
the support (Definition 19). Modelled at the level of subsets: `A ∈ DC,k` when
`z_A` has GF(2)-weight-`≤ k` representation, which we expose through the concrete
finite predicate below. -/
def orderKDiagGroup (n : ℕ) (c : PauliIndex n → ℝ) (k : ℕ) : Set (Finset (Fin n)) :=
  {A | A ≠ ∅ ∧ ∃ T : Finset (PauliIndex n),
      (T : Set (PauliIndex n)) ⊆ pauliSupport c ∧ T.card ≤ k ∧
        ((0 : Fin n → ZMod 2), vectorOfFinset A) ∈
          Submodule.span (ZMod 2) (sympVec '' (T : Set (PauliIndex n)))}

/-! ## §7 Concrete single-qubit and register Pauli matrices

The paper's Pauli expansion `C = ∑_(x,z) c_(x,z) P_(x,z)` (§II D, Eqs. (10)–(12))
is used verbatim in the sparsification (Proposition 8 / Theorem 32) and in the
graph-theoretic structure results (Propositions 22–24), so we give the concrete
matrix model of a Pauli string on the register `Reg n`. -/

/-- The single-qubit Pauli matrix `P_(x,z) = i^{xz} X^x Z^z` in the `(x,z)` label
of §II D, over the Boolean index `Bool` (`false = 0`, `true = 1`). This matches
`P_(0,0)=I`, `P_(1,0)=X`, `P_(0,1)=Z`, `P_(1,1)=Y`. -/
def pauli1Mat (x z : Bool) : Matrix Bool Bool ℂ :=
  fun a b =>
    match x, z, a, b with
    | false, false, a, b => if a = b then 1 else 0
    | true, false, false, true => 1
    | true, false, true, false => 1
    | true, false, _, _ => 0
    | false, true, false, false => 1
    | false, true, true, true => -1
    | false, true, _, _ => 0
    | true, true, false, true => -Complex.I
    | true, true, true, false => Complex.I
    | true, true, _, _ => 0

/-- The `n`-qubit Pauli string `P_(x,z) = ⊗_{i} P_(x_i,z_i)` as a matrix on the
register `Reg n` (the Pauli expansion basis of §II D, Eq. (10)). -/
def pauliOp (n : ℕ) (p : PauliIndex n) : Matrix (Reg n) (Reg n) ℂ :=
  fun i j => ∏ k, pauli1Mat (p.1 k) (p.2 k) (i k) (j k)

/-- The Pauli expansion `∑_(x,z) c_(x,z) P_(x,z)` of a coefficient function,
§II D, Eq. (10). -/
def pauliExpand {n : ℕ} (c : PauliIndex n → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ p, (c p : ℂ) • pauliOp n p

/-- The GF(2)-span of the diagonal vectors `z_A` for `A` ranging over a finite
family `G`; used to state that `G` generates the diagonal group (Proposition 15). -/
def spanOfFinsets {n : ℕ} (G : Finset (Finset (Fin n))) :
    Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
  Submodule.span (ZMod 2)
    ((G.image (fun A => ((0 : Fin n → ZMod 2), vectorOfFinset A)) : Finset _) : Set _)

/-- Hamming distance between two computational-basis strings. -/
def hammingDist {n : ℕ} (x y : Reg n) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

/-- The string obtained from `x` by flipping exactly the bits indexed by `A`. -/
def flipBits {n : ℕ} (A : Finset (Fin n)) (x : Reg n) : Reg n :=
  fun i => if i ∈ A then Bool.not (x i) else x i

/-- The normalised QUBO energy `2^{-n} ⟨x, C x⟩` of a `±1` string `x` that the
Monte Carlo rounding estimator targets (Proposition 9 / Eq. (23)). -/
def energyDensity {n : ℕ} (C : Matrix (Reg n) (Reg n) ℂ) (x : Reg n → ℝ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ i, ∑ j, x i * (C i j).re * x j

/-- The `Ξ(S,ε)` feasible coefficient set of Corollary 35 / Eq. (F11): real weights
`ξ_A` such that `∑_{A∈S} ξ_A Z_A ⪰ -GW(C,S,ε) · I`, read through the Pauli
`ℓ1` mass `∑ |ξ_A|`. -/
def xiValueSet (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (S : Finset (Finset (Fin n))) (ε : ℝ) : Set ℝ :=
  {r : ℝ | ∃ ξ : Finset (Fin n) → ℝ,
    r = ∑ A ∈ S, |ξ A| ∧
    ((gwValue n C (S : Set (Finset (Fin n))) ε) • (1 : Matrix (Reg n) (Reg n) ℂ) +
        ∑ A ∈ S, (ξ A : ℂ) • ZMat n A).PosSemidef}

end Qatlib.Papers.GWSpeedupYuan25.MainResults
