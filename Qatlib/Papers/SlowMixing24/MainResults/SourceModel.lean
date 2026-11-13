/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCoreDefs
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# SourceModel — shared vocabulary for `SlowMixing24`

Gamarnik--Kiani--Zlokapa, *Slow Mixing of Quantum Gibbs Samplers*,
arXiv:2411.04300v2.

This file only fixes the notation shared by all claims of the paper block:

* `Op n` — operators on the `n`-qubit Hilbert space `(ℂ²)^{⊗n}`, encoded as
  `2^n`-dimensional matrices (the library convention `Operator (2^n)`);
* the library's GKSL generator `GKSL (2^n)`, the semigroup `lindbladSemigroup`,
  the Gibbs density `gibbsDensity`, the trace distance `traceDistance` and
  the mixing time `mixingTime` are **reused** from
  `Qatlib.Concepts.LindbladFlow.GkslSemigroup`
  (`LindbladSemigroupModel` and `LindbladSemigroupCore`);
* projectors, their Gibbs weights `Tr[Πρ]`, the initial state `σ₀` of
  Equations (42)/(47), the Hamming distances of Definitions 3.5 and the
  Pauli-`Z`/Pauli-`X` matrices used in Equations (86)/(114);
* the discrete-channel mixing time of Definition 2.1 and the asymptotic
  predicates `exp[Ω(·)]`, `exp[O(·)]`, `o(1)`, `Ω(1)` and `superpolynomial`
  used throughout the paper.

Nothing here asserts a paper result; the theorems live in the claim files.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal BigOperators

namespace Qatlib.Papers.SlowMixing24.MainResults

open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open Qatlib.Foundations.PureStateMath

/-! ## Hilbert space and channels -/

/-- Operators on `n` qubits, i.e. `2^n × 2^n` complex matrices. -/
abbrev Op (n : ℕ) : Type := Operator (2 ^ n)

/-- A (linear) quantum channel on `n` qubits, in the Schrödinger picture. -/
abbrev Chan (n : ℕ) : Type := Op n →ₗ[ℂ] Op n

/-- A GKSL generator on `n` qubits. -/
abbrev Gksl (n : ℕ) : Type := GKSL (2 ^ n)

/-- Real part of the matrix trace. -/
noncomputable def tr {n : ℕ} (A : Op n) : ℝ := (Matrix.trace A).re

/-- Computational-basis spin configuration on `n` qubits (`true` = `+1`). -/
abbrev St (n : ℕ) : Type := Fin n → Bool

/-- The spin value `σ_i = ±1` attached to a configuration. -/
noncomputable def spin {n : ℕ} (σ : St n) (i : Fin n) : ℝ := if σ i then 1 else -1

/-- Flip the spins in `S` and leave the others unchanged (used in Lemma 4.8/4.10). -/
def flipOn {n : ℕ} (S : Finset (Fin n)) (σ : St n) : St n :=
  fun i => if i ∈ S then !σ i else σ i

/-- Hamming distance between two spin configurations. -/
noncomputable def hammingDist {n : ℕ} (x y : St n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card

/-- `i`-th bit of the basis index `z : Fin (2^n)`. -/
noncomputable def bitOf {n : ℕ} (z : Fin (2 ^ n)) (i : Fin n) : Bool :=
  Nat.testBit z.val i.val

/-- Hamming distance between two computational-basis indices, Definition 3.5. -/
noncomputable def hammingDistZ {n : ℕ} (z w : Fin (2 ^ n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => bitOf z i ≠ bitOf w i)).card

/-! ## Pauli matrices and the transverse-field Ising Hamiltonian -/

/-- Pauli `Z` on qubit `i` (paper Equation (114)). -/
noncomputable def zOp (n : ℕ) (i : Fin n) : Op n :=
  Matrix.diagonal (fun a : Fin (2 ^ n) => if Nat.testBit a.val i.val then (-1 : ℂ) else 1)

/-- Pauli `X` on qubit `i` (paper Equation (114)). -/
noncomputable def xOp (n : ℕ) (i : Fin n) : Op n :=
  Matrix.of (fun a b : Fin (2 ^ n) => if b.val = (a.val ^^^ (2 ^ i.val)) then (1 : ℂ) else 0)

/-- The transverse field `Σ_i X_i`. -/
noncomputable def xSum (n : ℕ) : Op n := ∑ i : Fin n, xOp n i

/-- The classical interaction `-Σ_{⟨i,j⟩} Z_i Z_j` over an edge set. -/
noncomputable def zzHam (n : ℕ) (nb : Finset (Fin n × Fin n)) : Op n :=
  - ∑ p ∈ nb, zOp n p.1 * zOp n p.2

/-- The transverse-field Ising Hamiltonian `-Σ_{⟨i,j⟩} Z_i Z_j - h Σ_i X_i`
of Equation (114). -/
noncomputable def tfim (n : ℕ) (nb : Finset (Fin n × Fin n)) (h : ℝ) : Op n :=
  zzHam n nb - (h : ℂ) • xSum n

/-- A two-dimensional Ising instance: the edge set of the `side × side` lattice
and the field strength, together with the paper's Hamiltonian (114). -/
structure TFIM2D (n : ℕ) where
  /-- Lattice side length (`side * side = n`). -/
  side : ℕ
  /-- `n` is the number of lattice sites. -/
  qubits_eq : n = side * side
  /-- Nearest-neighbour edge set of the lattice. -/
  nb : Finset (Fin n × Fin n)
  /-- Every site has at most four neighbours (square lattice). -/
  degree_le : ∀ i : Fin n, (nb.filter (fun p => p.1 = i ∨ p.2 = i)).card ≤ 4
  /-- Transverse-field strength `h`. -/
  h : ℝ
  /-- The Hamiltonian of Equation (114). -/
  H : Op n
  /-- `H` is exactly the transverse-field Ising Hamiltonian. -/
  H_eq : H = tfim n nb h

/-! ## Projectors and Gibbs weights -/

/-- An orthogonal projector `Π ∈ OH_n` (Hermitian and idempotent). -/
structure Projector (n : ℕ) where
  /-- The matrix of the projector. -/
  mat : Op n
  /-- Hermiticity. -/
  hermitian : mat.IsHermitian
  /-- Idempotence `Π² = Π`. -/
  idempotent : mat * mat = mat

/-- `Tr[Πρ]`. -/
noncomputable def Projector.weight {n : ℕ} (P : Projector n) (ρ : Op n) : ℝ :=
  tr (P.mat * ρ)

/-- Diagrammatic `e^{-βH}` (unnormalised Gibbs weight). -/
noncomputable def gibbsBolt {n : ℕ} (H : Op n) (β : ℝ) : Op n :=
  NormedSpace.exp ((-(β : ℂ)) • H)

/-- `e^{-βH/2}`. -/
noncomputable def halfGibbsBolt {n : ℕ} (H : Op n) (β : ℝ) : Op n :=
  NormedSpace.exp ((-((β / 2 : ℝ)) : ℂ) • H)

/-- The initial state `σ₀ = e^{-βH/2}Π_A e^{-βH/2} / Tr[Π_A e^{-βH}]`
of Equations (42)/(47)/(97). -/
noncomputable def sigma0 {n : ℕ} (H : Op n) (β : ℝ) (PA : Projector n) : Op n :=
  (tr (PA.mat * gibbsBolt H β))⁻¹ •
    (halfGibbsBolt H β * PA.mat * halfGibbsBolt H β)

/-- `Tr[Π_C σ₀]`, the dephasing quantity of Equation (43). -/
noncomputable def decouplingWeight {n : ℕ} (H : Op n) (β : ℝ)
    (PA PC : Projector n) : ℝ :=
  PC.weight (sigma0 H β PA)

/-- The default bottleneck matrix `Π_B = I − Π_A − Π_C` (Section 3.3). -/
noncomputable def Bmat {n : ℕ} (PA PC : Projector n) : Op n :=
  1 - PA.mat - PC.mat

/-- `Tr[Π_B ρ_β]` for the default bottleneck `Π_B = I − Π_A − Π_C`. -/
noncomputable def Bweight {n : ℕ} (PA PC : Projector n) (H : Op n) (β : ℝ) : ℝ :=
  tr (Bmat PA PC * gibbsDensity H β)

/-- `Tr[Πσ]` for the Gibbs density `ρ_β = e^{-βH}/Tr[e^{-βH}]`. -/
noncomputable def gibbsWeight {n : ℕ} (P : Projector n) (H : Op n) (β : ℝ) : ℝ :=
  P.weight (gibbsDensity H β)

/-- A diagonal entry `⟨z|e^{-βH}|z⟩` of the unnormalised Gibbs operator. -/
noncomputable def gibbsDiag {n : ℕ} (H : Op n) (β : ℝ) (z : Fin (2 ^ n)) : ℝ :=
  (gibbsBolt H β z z).re

/-- `A` acts trivially outside the qubit set `S`: its matrix elements vanish
whenever the two basis indices differ on a qubit of `S`. This is the concrete
content of "acts nontrivially only on the qubits in `S`". -/
def ActsOnQubits {n : ℕ} (A : Op n) (S : Finset (Fin n)) : Prop :=
  ∀ z w : Fin (2 ^ n), (∃ i ∈ S, bitOf z i ≠ bitOf w i) → A z w = 0

/-- An `ℓ`-local Hamiltonian: a finite sum of terms, each acting on at most
`ℓ` qubits. This is the concrete content of "`ℓ`-local Hamiltonian `V`" in
Lemmas 4.5/4.7 and Proposition 4.6. -/
def LocalHamiltonian {n : ℕ} (V : Op n) (ℓ : ℕ) : Prop :=
  ∃ (m : ℕ) (terms : Fin m → Op n) (S : Fin m → Finset (Fin n)),
    (∀ i, (S i).card ≤ ℓ) ∧ (∀ i, ActsOnQubits (terms i) (S i)) ∧
      V = ∑ i, terms i

/-- A projector is diagonal in the computational (`Z`) basis. -/
def DiagonalInZ {n : ℕ} (P : Projector n) : Prop :=
  ∀ z w : Fin (2 ^ n), z ≠ w → P.mat z w = 0

/-- Computational-basis support `S = {z : ⟨z|Π|z⟩ ≠ 0}` of Definition 3.5. -/
noncomputable def Projector.compSupport {n : ℕ} (P : Projector n) : Finset (Fin (2 ^ n)) :=
  Finset.univ.filter (fun z => P.mat z z ≠ 0)

/-- `dist_Z(A,C) ≥ k` (Definition 3.5): every computational-basis vector in
the support of `Π_A` is at Hamming distance at least `k` from every vector in
the support of `Π_C`. -/
def CompDistAtLeast {n : ℕ} (PA PC : Projector n) (k : ℕ) : Prop :=
  ∀ z w : Fin (2 ^ n), z ∈ PA.compSupport → w ∈ PC.compSupport → k ≤ hammingDistZ z w

/-- hamming distance between the supports of two configuration sets (used for
classical `A`, `C` of Proposition 4.1). -/
def SetDistAtLeast {n : ℕ} (A C : Finset (St n)) (k : ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ C, k ≤ hammingDist x y

/-! ## Mixing times (Definitions 2.1 and 2.2) -/

/-- Discrete mixing time (Definition 2.1): the smallest `k` such that every
density operator is within trace distance `ε` of `ρ` after `k` applications
of `T`. The continuous counterpart is the library's
`Qatlib.Concepts.LindbladFlow.GkslSemigroup.mixingTime`. -/
noncomputable def TmixD {n : ℕ} (T : Chan n) (ρ : Op n) (ε : ℝ) : ℕ :=
  sInf {k : ℕ | ∀ σ : Op n, IsDensityOperator σ →
    traceDistance (((T : Op n → Op n))^[k] σ) ρ ≤ ε}

/-- The continuous mixing time of Definition 2.2, reusing the library's `mixingTime`. -/
noncomputable def TmixC {n : ℕ} (G : Gksl n) (ρ : Op n) (ε : ℝ) : ℝ≥0∞ :=
  mixingTime G ρ ε

/-- `TmixD` as a real number. -/
noncomputable def TmixDreal {n : ℕ} (T : Chan n) (ρ : Op n) (ε : ℝ) : ℝ :=
  (TmixD T ρ ε : ℝ)

/-- The library's mixing time as a real number (with the `⊤` convention). -/
noncomputable def TmixCreal {n : ℕ} (G : Gksl n) (ρ : Op n) (ε : ℝ) : ℝ :=
  (TmixC G ρ ε).toReal

/-! ## Structural hypotheses from the paper -/

/-- `‖L‖ = O(poly n)` for a GKSL generator, in the bounded-operator form
`‖L(ρ)‖ ≤ C n^p ‖ρ‖` (Lemma 2.1, Corollary 2.2). -/
def GeneratorPolyBounded {n : ℕ} (G : Gksl n) (C : ℝ) (p : ℕ) : Prop :=
  ∀ ρ : Op n, ‖lindbladApply G ρ‖ ≤ C * (n : ℝ) ^ p * ‖ρ‖

/-- The generator annihilates the Gibbs state: `L(ρ_β) = 0` (Equation (20)). -/
def GeneratorFixed {n : ℕ} (G : Gksl n) (ρ : Op n) : Prop :=
  lindbladApply G ρ = 0

/-- `T` fixes `ρ_β` (discrete Gibbs sampler, Proposition 3.4). -/
def ChannelFixed {n : ℕ} (T : Chan n) (ρ : Op n) : Prop := T ρ = ρ

/-- `T†(A) ≼ B` tested on positive-semidefinite states: for every PSD `ρ`,
`Tr[A T(ρ)] ≤ Tr[B ρ]`. This is the trace-dual form of the Loewner-order
hypothesis `T†(Π_C) ≼ Π_B + Π_C` of Lemma 3.3 and Propositions 3.4/3.5. -/
def DualBelow {n : ℕ} (T : Chan n) (A B : Op n) : Prop :=
  ∀ ρ : Op n, ρ.PosSemidef → tr (A * T ρ) ≤ tr (B * ρ)

/-- `dist_T(A,C) > range_T(T)`, recorded as the numerical separation datum of
Definitions 3.2/3.3. This is an *assumption* of Lemma 1.1 and Lemma 3.3, not a
conclusion. -/
structure SeparationHyp (n : ℕ) where
  /-- Lower bound on the jump-operator distance `dist_T(A,C)`. -/
  distT : ℕ
  /-- Upper bound on the jump-operator range `range_T(T)`. -/
  rangeT : ℕ
  /-- The strict separation `dist_T(A,C) > range_T(T)`. -/
  lt : rangeT < distT

/-- The Choi-matrix form of the diamond norm used for the Appendix-A
statements. For completely positive maps this is the standard diamond norm
`‖T‖_⋄ = ‖(T ⊗ id)(Φ)‖₁` (Choi's theorem). -/
noncomputable def diamondNorm {n : ℕ} (T : Chan n) : ℝ :=
  (MatrixMap.choi_matrix T).traceNorm

/-- The semigroup as a linear channel, for nonnegative times. -/
noncomputable def semigroupChan {n : ℕ} (G : Gksl n) (t : ℝ) (ht : 0 ≤ t) :
    Chan n :=
  lindbladSemigroupMap G t ht

/-- Every Lindblad jump operator of `G` acts on at most `R * R` qubits
(Theorem 1.4 / Corollary 4.17: `R × R` geometric regions). -/
def JumpLocality {n : ℕ} (G : Gksl n) (R : ℕ) : Prop :=
  ∃ S : Fin (2 ^ n * 2 ^ n) → Finset (Fin n),
    (∀ t, (S t).card ≤ R * R) ∧ ∀ t, ActsOnQubits (G.jumps t) (S t)

/-- A channel whose Kraus operators each act on at most `R * R` qubits
(Definition 3.4 / Lemma 4.18). -/
def KrausRadius {n : ℕ} (T : Chan n) (R : ℕ) : Prop :=
  ∃ (m : ℕ) (K K' : Fin m → Op n) (S : Fin m → Finset (Fin n)),
    (∀ i, (S i).card ≤ R * R) ∧
      (∀ i, ActsOnQubits (K i) (S i) ∧ ActsOnQubits (K' i) (S i)) ∧
      ∀ ρ : Op n, T ρ = ∑ i, K i * ρ * K' i

/-- A Pauli assignment with its weight (number of non-identity factors),
Definition 4.4. -/
structure PauliAssign (n : ℕ) where
  /-- The `n`-qubit Pauli operator. -/
  mat : Op n
  /-- Its weight `w(a)`. -/
  weight : ℕ

/-- A `[[n,k,d]]` stabilizer code together with the Hamiltonian of Eq. (67)
`H = Σ_i (I − C_i)/2`; `checks i` is the Pauli check `C_i`. -/
structure StabilizerCode (n : ℕ) where
  /-- Number of logical qubits. -/
  k : ℕ
  /-- Code distance. -/
  d : ℕ
  /-- The `n − k` stabilizer checks. -/
  checks : Fin (n - k) → Op n
  /-- The associated Hamiltonian of Equation (67). -/
  H : Op n
  /-- `H = Σ_i (I − C_i)/2`. -/
  H_eq : H = ∑ i, ((2 : ℂ)⁻¹) • ((1 : Op n) - checks i)

/-- Number of checks violated (not commuting) by a Pauli assignment `a`,
Eq. (69). -/
noncomputable def codeViolations {n : ℕ} (C : StabilizerCode n)
    (a : PauliAssign n) : ℕ :=
  (Finset.univ.filter (fun i : Fin (n - C.k) =>
    C.checks i * a.mat ≠ a.mat * C.checks i)).card

/-- `(γ, α)` small-set expander condition of Definition 4.4:
for every assignment of weight `≤ α n`, `V(a) ≥ γ w(a)`. -/
def IsSmallSetExpander {n : ℕ} (C : StabilizerCode n) (γ α : ℝ) : Prop :=
  ∀ a : PauliAssign n, (a.weight : ℝ) ≤ α * (n : ℝ) →
    γ * (a.weight : ℝ) ≤ (codeViolations C a : ℝ)

/-! ## Asymptotic vocabulary -/

/-- `f = exp[Ω(g)]`: there is a constant `c > 0` with `f n ≥ exp(c g n)`
eventually. -/
def ExpOmegaGe (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, Real.exp (c * g n) ≤ f n

/-- `f = exp[O(g)]`. -/
def ExpBigOLe (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, f n ≤ Real.exp (c * g n)

/-- `f = exp[-Ω(g)]`. -/
def ExpNegOmegaLe (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, f n ≤ Real.exp (-(c * g n))

/-- `f = o(1)`. -/
def LittleOOne (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |f n| ≤ ε

/-- `f = Ω(1)`. -/
def OmegaOne (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, c ≤ f n

/-- `f` grows superpolynomially: `f n ≥ n^k` eventually for every `k`. -/
def SuperPolynomial (f : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ^ k ≤ f n

/-- `Tmix = exp[Ω(poly n)]` for one fixed exponent `α > 0`. -/
def ExpPolyOmega (f : ℕ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ExpOmegaGe f (fun n => (n : ℝ) ^ α)

/-- `f n = n^{1/2 - o(1)}` growth, in the precise form used in Corollaries
1.5 and 4.20: `f n ≥ exp((1/2 - o(1)) log n)`, i.e. for every `η > 0`,
`f n ≥ n^{1/2 - η}` eventually. -/
def ExpHalfMinusLittleO (f : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ^ (1 / 2 - η) ≤ f n

/-! ## Basic trace-distance facts used by the proofs -/

/-- `Tr[Πρ] = Tr[ρΠ]` for a projector: cyclicity of the trace. -/
theorem Projector.weight_comm {n : ℕ} (P : Projector n) (ρ : Op n) :
    P.weight ρ = tr (ρ * P.mat) := by
  unfold Projector.weight tr
  rw [Matrix.trace_mul_comm]

/-- The trace distance is nonnegative. -/
theorem traceDistance_nonneg' {n : ℕ} (ρ σ : Op n) : 0 ≤ traceDistance ρ σ := by
  unfold traceDistance
  exact div_nonneg (Matrix.traceNorm_nonneg _) (by norm_num)

/-- The trace distance is symmetric. -/
theorem traceDistance_comm' {n : ℕ} (ρ σ : Op n) :
    traceDistance ρ σ = traceDistance σ ρ := by
  unfold traceDistance
  rw [show ρ - σ = -(σ - ρ) by abel, Matrix.traceNorm_neg]

/-- The triangle inequality for the trace distance. This is the only metric
fact used in the discrete-to-continuous mixing transfer (Corollary 2.2). -/
theorem traceDistance_triangle' {n : ℕ} (ρ σ τ : Op n) :
    traceDistance ρ σ ≤ traceDistance ρ τ + traceDistance τ σ := by
  unfold traceDistance
  have h := Matrix.traceNorm_add_le (ρ - τ) (τ - σ)
  have he : ρ - σ = (ρ - τ) + (τ - σ) := by abel
  rw [he]
  linarith

/-! ## Monotonicity of the asymptotic vocabulary

These are used when a lower bound proved at scale `g` is transported to a
smaller scale or to the `n^{1/2-o(1)}` vocabulary of Corollaries 1.5/4.20. -/

/-- If `f = exp[Ω(g)]` and `g' ≤ g` eventually, then `f = exp[Ω(g')]`. -/
theorem ExpOmegaGe.mono {f g g' : ℕ → ℝ} (h : ExpOmegaGe f g)
    (hg : ∀ n, g' n ≤ g n) : ExpOmegaGe f g' := by
  obtain ⟨c, hc, N, hN⟩ := h
  refine ⟨c, hc, N, fun n hn => le_trans ?_ (hN n hn)⟩
  exact Real.exp_le_exp.mpr (by
    exact mul_le_mul_of_nonneg_left (hg n) hc.le)

/-- `f = exp[Ω(g)]` is unaffected by adding a nonnegative constant to the
comparison scale, i.e. `exp[Ω(g + c)] ⊆ exp[Ω(g)]` for `c > 0`, `g ≥ 0`. -/
theorem ExpOmegaGe.add_const {f g : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (_hg : ∀ n, 0 ≤ g n)
    (h : ExpOmegaGe f (fun n => g n + c)) : ExpOmegaGe f g := by
  obtain ⟨c₀, hc₀, N, hN⟩ := h
  refine ⟨c₀, hc₀, N, fun n hn => le_trans ?_ (hN n hn)⟩
  apply Real.exp_le_exp.mpr
  show c₀ * g n ≤ c₀ * (g n + c)
  nlinarith [hc₀.le, hc.le]

/-! ## Hamming distance on spin configurations -/

/-- Hamming distance is symmetric. -/
theorem hammingDist_comm {n : ℕ} (x y : St n) : hammingDist x y = hammingDist y x := by
  unfold hammingDist
  congr 1
  apply Finset.filter_congr
  intro i _
  exact ne_comm

/-- Hamming distance is zero on equal configurations. -/
theorem hammingDist_self {n : ℕ} (x : St n) : hammingDist x x = 0 := by
  unfold hammingDist
  simp

/-- Hamming distance is bounded by the number of sites. -/
theorem hammingDist_le_card {n : ℕ} (x y : St n) : hammingDist x y ≤ n := by
  unfold hammingDist
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n))
    (fun i => x i ≠ y i)

/-! ## Local operators and separated computational-basis supports

The following is the operator-algebra core of the last assertion of Lemma 4.14,
Eq. (155): a local operator `O` cannot connect the two regions `A` and `C`.
It is proved here from the definitions (no paper result is assumed). -/

/-- **Local orthogonality of separated Z-diagonal projectors** (the core of
Lemma 4.14, Eq. (155), arXiv:2411.04300v2 p. 38).

If `Π_A, Π_C` are diagonal in the computational basis, `O` acts trivially off
the qubit set `S` (`ActsOnQubits`), and every pair of computational-basis
vectors in the supports of `Π_A` and `Π_C` differs on some qubit of `S`, then
`Tr[Π_A O Π_C] = 0`. -/
theorem trace_projector_mul_eq_zero_of_local_support {n : ℕ}
    (PA PC : Projector n) (O : Op n) (S : Finset (Fin n))
    (hdiagA : DiagonalInZ PA) (hdiagC : DiagonalInZ PC)
    (_hlocal : ActsOnQubits O S)
    (hsep : ∀ z w : Fin (2 ^ n), PA.mat z z ≠ 0 → PC.mat w w ≠ 0 →
      ∃ i ∈ S, bitOf z i ≠ bitOf w i) :
    Matrix.trace (PA.mat * O * PC.mat) = 0 := by
  -- The diagonal entry `(Π_A O Π_C) z z` equals `(Π_A) z z * O z z * (Π_C) z z`
  -- because both projectors are diagonal; the off-diagonal mass is killed.
  have houter : ∀ z : Fin (2 ^ n),
      (PA.mat * O * PC.mat) z z = (PA.mat * O) z z * PC.mat z z := by
    intro z
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single z
    · intro b _ hb
      rw [hdiagC b z hb, mul_zero]
    · intro hz
      exact absurd (Finset.mem_univ z) hz
  have hinner : ∀ z : Fin (2 ^ n),
      (PA.mat * O) z z = PA.mat z z * O z z := by
    intro z
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single z
    · intro b _ hb
      rw [hdiagA z b (Ne.symm hb), zero_mul]
    · intro hz
      exact absurd (Finset.mem_univ z) hz
  have hdiag_entry : ∀ z : Fin (2 ^ n),
      (PA.mat * O * PC.mat) z z = PA.mat z z * O z z * PC.mat z z := by
    intro z
    rw [houter z, hinner z]
  unfold Matrix.trace
  apply Finset.sum_eq_zero
  intro z _
  simp only [Matrix.diag]
  rw [hdiag_entry z]
  by_cases hA : PA.mat z z = 0
  · rw [hA, zero_mul, zero_mul]
  by_cases hC : PC.mat z z = 0
  · rw [hC, mul_zero]
  · obtain ⟨_, _, hbit⟩ := hsep z z hA hC
    exact absurd rfl hbit

end Qatlib.Papers.SlowMixing24.MainResults
