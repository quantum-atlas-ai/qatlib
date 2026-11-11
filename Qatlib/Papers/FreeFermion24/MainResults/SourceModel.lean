/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceModel — shared objects for *Solving Free Fermion Problems on a Quantum Computer*

Fixed arXiv:2409.04550 (prefetched PDF `assets/2409.04550.pdf`, text `assets/2409.04550.txt`).

This file records the paper's objects in the notation of the quantum-algorithm library:

* `SparseHermitian` — Definition 2 / Proposition 5 data: an `s`-sparse Hermitian matrix
  with entries bounded by one in modulus;
* `fBeta`, `gDeltaBetaOmega` — the scalar functions of Eq. (16) and Eq. (17)/(F1);
* `hermFun` — Hermitian functional calculus (spectral decomposition `Uᴴ diag U`);
* `thermalM`, `thermalMQuarter`, `greenG`, `expIht`, `timeEvolvedM`, `timeEvolvedM2` —
  the matrices of Eq. (3), (7), (4) and (5);
* `pathJ` — the clock Hamiltonian `J = ∑_{l=1}^{L}(|l+1⟩⟨l| + |l⟩⟨l+1|)` of Eq. (H5);
* `ControlledBlockEncoding` / `ResourceLedger` — a controlled approximate block
  encoding (reusing the frozen `BlockCorner` corner convention) together with the
  resource ledger used in the paper's cost statements;
* cost predicates encoding `poly(n)/ε`, `O(n)+n_a+log^{5/2}(poly(n)/ε⁴)`, `Θ(...)`
  and classical `poly(n/ε, log(1/ε))` bounds;
* `RandomisedEstimator` — finite-sample entry estimator used in Lemma 12;
* `QuantumDecider`, `PolyTimeReduces`, `BQPComplete` — the complexity interface for
  Theorem 13.

Boundary: this is a paper layer.  It does not claim that the block encodings are
synthesised into elementary gates; the resource ledger is a faithful *accounting*
of the paper's counts attached to an actual block-encoding unitary.  No statement
here is used to enlarge the shared `Foundations`/`Concepts` layer.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Concepts.BlockEncoding.StateBlockEncoding (BlockCorner)

namespace Qatlib.Papers.FreeFermion24.MainResults.Model

/-! ## Sparse Hermitian matrices and the scalar functions -/

/-- Number of nonzero entries in row `i` of `A`. -/
def rowSupport {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℕ :=
  (Finset.univ.filter (fun j => A i j ≠ 0)).card

/-- Definition 2 / Proposition 5 data: an `s`-sparse Hermitian `N × N` matrix whose
entries have modulus at most one. -/
structure SparseHermitian (N s : ℕ) where
  A : Matrix (Fin N) (Fin N) ℂ
  hermitian : A.IsHermitian
  rowSupport_le : ∀ i, rowSupport A i ≤ s
  entry_norm_le_one : ∀ i j, ‖A i j‖ ≤ 1

/-- Eq. (16): `f^(β)(x) = (1/4) · 1/(1 + exp(β s x))`. -/
def fBeta (s β x : ℝ) : ℝ := (1 / 4) * (1 / (1 + Real.exp (β * s * x)))

/-- Eq. (17)/(F1): `g^(δ,β,ω)(x)`, the complex scalar function whose real and
imaginary parts are block-encoded. -/
def gDeltaBetaOmega (s δ β ω x : ℝ) : ℂ :=
  ((δ / 8 : ℝ) : ℂ) *
    ((((1 - 1 / (1 + Real.exp (β * s * x)) : ℝ) : ℂ) *
        (Complex.I * (δ : ℂ) - ((s * x + ω : ℝ) : ℂ))⁻¹) +
      (((1 / (1 + Real.exp (β * s * x)) : ℝ) : ℂ) *
        (Complex.I * (δ : ℂ) + ((s * x + ω : ℝ) : ℂ))⁻¹))

/-! ## Hermitian functional calculus and the paper's matrices -/

/-- Hermitian functional calculus: `f(h) = Uᴴ diag(f ∘ λ) U` for the orthonormal
eigenbasis `U` of `h`.  For continuous `f` this is the usual `cfc`; the explicit
eigenbasis form keeps the definition elementary. -/
def hermFun {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (hh : h.IsHermitian)
    (f : ℝ → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ((hh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ))ᴴ *
    Matrix.diagonal (fun i => f (hh.eigenvalues i)) *
      ((hh.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ))

/-- Eq. (3): the thermal correlation matrix `M^(β) = I/(I + exp(β h))`. -/
def thermalM {N s : ℕ} (h : SparseHermitian N s) (β : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  hermFun h.A h.hermitian (fun y => ((1 / (1 + Real.exp (β * y)) : ℝ) : ℂ))

/-- Eq. (3), scaled as in Theorems 9/16: `(1/4) M^(β)`. -/
def thermalMQuarter {N s : ℕ} (h : SparseHermitian N s) (β : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (1 / 4 : ℝ) • thermalM h β

/-- Eq. (7): the thermal Green's function `G^(δ,β,ω)(h)`. -/
def greenG {N s : ℕ} (h : SparseHermitian N s) (δ β ω : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  hermFun h.A h.hermitian (fun y =>
    ((δ / 2 : ℝ) : ℂ) *
      ((((1 - 1 / (1 + Real.exp (β * y)) : ℝ) : ℂ) *
          (Complex.I * (δ : ℂ) - ((y + ω : ℝ) : ℂ))⁻¹) +
        (((1 / (1 + Real.exp (β * y)) : ℝ) : ℂ) *
          (Complex.I * (δ : ℂ) + ((y + ω : ℝ) : ℂ))⁻¹)))

/-- Eq. (7), scaled as in the statements of Theorems 10/19: `(1/4) G^(δ,β,ω)(h)`. -/
def greenGQuarter {N s : ℕ} (h : SparseHermitian N s) (δ β ω : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (1 / 4 : ℝ) • greenG h δ β ω

/-- The time-evolution unitary `exp(i h t)` of a Hermitian matrix `h`. -/
def expIht {N s : ℕ} (h : SparseHermitian N s) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  hermFun h.A h.hermitian (fun y => Complex.exp (Complex.I * (y : ℂ) * (t : ℂ)))

/-- Eq. (4): `M(t) = e^{iht} M e^{-iht}`. -/
def timeEvolvedM {N s : ℕ} (h : SparseHermitian N s)
    (M : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  expIht h t * M * expIht h (-t)

/-- Eq. (5): `M(t₁,t₂) = e^{iht₁} M e^{-iht₂}`. -/
def timeEvolvedM2 {N s : ℕ} (h : SparseHermitian N s)
    (M : Matrix (Fin N) (Fin N) ℂ) (t₁ t₂ : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  expIht h t₁ * M * expIht h (-t₂)

/-! ## The clock Hamiltonian of Lemma 20 -/

/-- Eq. (H5): the path Hamiltonian `J = ∑_{l=1}^{L}(|l+1⟩⟨l| + |l⟩⟨l+1|)` on the
`(L+1)`-dimensional clock space, indexed by `Fin (L+1)` with `0` playing the role of
`|1⟩` and `Fin.last L` the role of `|L+1⟩`. -/
def pathJ (L : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℂ :=
  Matrix.of fun i j =>
    if ((j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) then 1 else 0

/-- The transition matrix element `⟨L+1| e^{-iJt} |1⟩` of Lemma 20, with the
`Fin (L+1)` indexing of `pathJ`. -/
def pathAmplitude (L : ℕ) (t : ℝ) : ℂ :=
  (NormedSpace.exp (-(Complex.I) • ((t : ℝ) • pathJ L))) (Fin.last L) 0

/-! ## Resource ledger and controlled block encodings -/

/-- Resource ledger of an implementation: number of oracle calls, extra ancillary
qubits, elementary gates, and classical computing time.  Real-valued so that the
paper's `poly(n)/ε` bounds are stated directly. -/
structure ResourceLedger where
  oracleCalls : ℝ
  ancillaryQubits : ℝ
  gates : ℝ
  classicalTime : ℝ
  /-- Number of uses of the input block-encoding `U_M` (Theorems 11/17 use exactly one). -/
  usesOfUM : ℝ

/-- A controlled approximate `(α, ε)`-block-encoding of `A` on `N` data dimensions,
with a resource ledger.  `U` acts on `m` ancilla qubits (dimension `2^m`) tensored
with the data register, is unitary, and its `j₀`-corner encodes `A` up to spectral
error `ε` (normalisation `α`).  This reuses the frozen `BlockCorner` convention. -/
structure ControlledBlockEncoding (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (α ε : ℝ) where
  m : ℕ
  j₀ : Fin (2 ^ m)
  U : Matrix (Fin (2 ^ m) × Fin N) (Fin (2 ^ m) × Fin N) ℂ
  unitary : U ∈ Matrix.unitaryGroup (Fin (2 ^ m) × Fin N) ℂ
  error_nonneg : 0 ≤ ε
  error_le : ‖A - α • BlockCorner U j₀‖ ≤ ε
  cost : ResourceLedger

/-! ## Cost predicates mirroring the paper's asymptotic notation -/

/-- A real polynomial that is nonnegative on all natural-number inputs; used to
express `poly(n)` without committing to a degree. -/
def IsNatNonnegPoly (P : Polynomial ℝ) : Prop := ∀ k : ℕ, 0 ≤ P.eval (k : ℝ)

/-- `v ≤ poly(n)/ε` for some nonnegative polynomial `poly`. -/
def PolyOverEps (v : ℝ) (n : ℕ) (ε : ℝ) : Prop :=
  ∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ v ≤ P.eval (n : ℝ) / ε

/-- The logarithmic factor `log^{5/2}(poly(n)/ε⁴)` appearing in Theorems 9/10/11. -/
def logPolyEps (P : Polynomial ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  Real.rpow (Real.log (max (P.eval (n : ℝ) / ε ^ 4) 1)) (5 / 2 : ℝ)

/-- `v ≤ O(n) + n_a + log^{5/2}(poly(n)/ε⁴)`. -/
def AncillaShape (v : ℝ) (n na : ℕ) (ε : ℝ) : Prop :=
  ∃ (C : ℝ) (P : Polynomial ℝ), 0 ≤ C ∧ IsNatNonnegPoly P ∧
    v ≤ C * (n : ℝ) + (na : ℝ) + logPolyEps P n ε

/-- `v ≤ O(n) + poly(n)/ε + log^{5/2}(poly(n)/ε⁴)`. -/
def GateShape (v : ℝ) (n : ℕ) (ε : ℝ) : Prop :=
  ∃ (C : ℝ) (P : Polynomial ℝ), 0 ≤ C ∧ IsNatNonnegPoly P ∧
    v ≤ C * (n : ℝ) + P.eval (n : ℝ) / ε + logPolyEps P n ε

/-- `v ≤ poly(n/ε, log(1/ε))` classical time. -/
def ClassicalShape (v : ℝ) (n : ℕ) (ε : ℝ) : Prop :=
  ∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧
    v ≤ P.eval ((n : ℝ) / ε + Real.log (1 / ε))

/-- A two-sided `Θ` bound with witness constants. -/
def ThetaBound (v low high : ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₁ * low ≤ v ∧ v ≤ c₂ * high

/-- `v = O(bound)`: a single constant witness. -/
def BigO (v bound : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ v ≤ C * bound

/-- `v ≤ poly(x)` for a nonnegative-on-naturals polynomial. -/
def PolyBound (v x : ℝ) : Prop :=
  ∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ v ≤ P.eval x

/-- A real polynomial nonnegative on the nonnegative reals (used for the `poly(βs)` and
`poly(s/δ)` error bounds of Lemmas 7/8). -/
def NonnegOnNonneg (P : Polynomial ℝ) : Prop := ∀ x : ℝ, 0 ≤ x → 0 ≤ P.eval x

/-- `v ≤ poly(K) · poly(n)`, the classical-effort shape of Lemma 14. -/
def PolyKPolyN (v : ℝ) (K n : ℕ) : Prop :=
  ∃ P Q : Polynomial ℝ, IsNatNonnegPoly P ∧ IsNatNonnegPoly Q ∧
    v ≤ P.eval (K : ℝ) * Q.eval (n : ℝ)

/-- `v ≤ poly(a) · poly(b)`, the two-parameter classical-time shape
`poly(β^4 s^4/ε_PA, log(1/δ))` of Theorems 16/19. -/
def PolyTwo (v a b : ℝ) : Prop :=
  ∃ P Q : Polynomial ℝ, NonnegOnNonneg P ∧ NonnegOnNonneg Q ∧
    v ≤ P.eval a * Q.eval b

/-! ## Lemma 12: finite-sample entry estimation -/

/-- A randomised estimator of matrix entries that uses `k` random bits. -/
structure RandomisedEstimator (N : ℕ) where
  k : ℕ
  estimate : Fin (2 ^ k) → Fin N → Fin N → ℂ
  calls : ℕ

/-- Fraction of the `2^k` random strings on which the estimator is within `tol`
of the entry `A i j`. -/
def successProb {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (E : RandomisedEstimator N) (i j : Fin N) (tol : ℝ) : ℝ :=
  ((Finset.univ.filter (fun r : Fin (2 ^ E.k) =>
      ‖E.estimate r i j - A i j‖ ≤ tol)).card : ℝ) / (2 : ℝ) ^ E.k

/-! ## Theorem 13: the complexity interface -/

/-- A promise problem. -/
structure PromiseProblem where
  Instance : Type
  yes : Set Instance
  no : Set Instance

/-- A uniform polynomial-size quantum decider for a promise problem, acting on the
all-zero input of a per-instance number of qubits and accepting with probability
`‖U 0 0‖²`.  This is the paper's BQP machine model in interface form. -/
structure QuantumDecider (P : PromiseProblem) where
  qubits : P.Instance → ℕ
  U : (x : P.Instance) → Matrix (Fin (2 ^ qubits x)) (Fin (2 ^ qubits x)) ℂ
  unitary : ∀ x, U x ∈ Matrix.unitaryGroup (Fin (2 ^ qubits x)) ℂ
  size : P.Instance → ℕ
  size_poly : ∃ Q : Polynomial ℝ, IsNatNonnegPoly Q ∧ ∀ x, (size x : ℝ) ≤ Q.eval (qubits x : ℝ)
  accept_yes : ∀ x, x ∈ P.yes → (2 : ℝ) / 3 ≤ ‖U x 0 0‖ ^ 2
  accept_no : ∀ x, x ∈ P.no → ‖U x 0 0‖ ^ 2 ≤ (1 : ℝ) / 3

/-- `P` is in BQP. -/
def InBQP (P : PromiseProblem) : Prop := Nonempty (QuantumDecider P)

/-- A polynomial-time many-one reduction from `Q` to `P`. -/
structure PolyTimeReduces (Q P : PromiseProblem) where
  f : Q.Instance → P.Instance
  runtime : Q.Instance → ℕ
  runtime_poly : ∃ R : Polynomial ℝ, IsNatNonnegPoly R ∧ ∀ x, (runtime x : ℝ) ≤ R.eval (7 : ℝ)
  maps_yes : ∀ x, x ∈ Q.yes → f x ∈ P.yes
  maps_no : ∀ x, x ∈ Q.no → f x ∈ P.no

/-- `P` is BQP-complete. -/
def BQPComplete (P : PromiseProblem) : Prop :=
  InBQP P ∧ ∀ Q : PromiseProblem, InBQP Q → Nonempty (PolyTimeReduces Q P)

/-! ## The concrete promise problem of Theorem 13 -/

/-- Instance of the free-fermion dynamics decision problem: a sparse Hermitian
single-particle matrix `h` on `2^n` modes, a sparse initial correlation matrix `M₀`,
an evolution time `t` with `t = poly(n)`, and a mode `j`.  (The paper additionally
assumes `H` is the quadratic Hamiltonian with single-particle matrix `h`, that the
initial state `ρ₀` is fermionic, and that the oracle tuples `O_h`, `O_{M₀}` are
`poly(n)`-sized circuits; these computational hypotheses are not representable in the
matrix model and are recorded in the docstring of `theorem13_fermionDynamics_BQPComplete`.) -/
structure DynamicsInstance where
  n : ℕ
  s : ℕ
  h : SparseHermitian (2 ^ n) s
  sM : ℕ
  M₀ : SparseHermitian (2 ^ n) sM
  t : ℝ
  j : Fin (2 ^ n)
  t_poly : ∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ t ≤ P.eval (n : ℝ)

/-- The occupation `n_j(t) = Tr(a_j† a_j e^{-iHt} ρ₀ e^{iHt})`, identified with the
`(j,j)` entry of the time-evolved correlation matrix Eq. (4). -/
def DynamicsInstance.nj (x : DynamicsInstance) : ℝ :=
  (timeEvolvedM x.h x.M₀.A x.t) x.j x.j |>.re

/-- YES instances: `n_j(t) ≥ 1/p(√n)` for some polynomial `p`. -/
def dynamicsYes : Set DynamicsInstance :=
  {x | ∃ p : Polynomial ℝ, IsNatNonnegPoly p ∧ p.eval (Real.sqrt (x.n : ℝ)) ≠ 0 ∧
      1 / p.eval (Real.sqrt (x.n : ℝ)) ≤ x.nj}

/-- NO instances: `n_j(t) ≤ exp(-√n)`. -/
def dynamicsNo : Set DynamicsInstance :=
  {x | x ∉ dynamicsYes ∧ x.nj ≤ Real.exp (-(Real.sqrt (x.n : ℝ)))}

/-- The promise problem of Theorem 13. -/
def fermionDynamicsProblem : PromiseProblem where
  Instance := DynamicsInstance
  yes := dynamicsYes
  no := dynamicsNo

end Qatlib.Papers.FreeFermion24.MainResults.Model
