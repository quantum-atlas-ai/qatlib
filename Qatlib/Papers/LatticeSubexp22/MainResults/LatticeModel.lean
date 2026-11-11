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

set_option backward.isDefEq.respectTransparency false

/-!
# LatticeSubexp22 — paper-layer model

Eldar--Hallgren, *An efficient quantum algorithm for lattice problems achieving
subexponential approximation factor*, fixed arXiv:2201.13450v1 (2022-01-31).

This file holds the shared objects of the paper layer:

* integer and residue vectors, `q`-periodic lattices, finite-group decompositions
  `(G, q, r)` and the modular norm `‖·‖_q` of Section 2.1 (p. 6);
* the shortest-vector length `λ₁(G)` and the distance `dist_q(t, G)`;
* cube states and phased cube states of Definition 13 (p. 11), together with the
  shift operator `U_x`;
* approximate eigenvectors of Definition 9 (p. 9) and the finite phase-state
  norm used to state Lemma 11 (p. 9);
* an abstract algorithm interface (`BDDRandomAlgorithm`, `CVPAlgorithm`,
  `BasisReductionAlgorithm`) carrying a running-time function and an output law,
  so that the algorithmic claims of the paper can be stated non-vacuously.

The statements themselves live in the sibling files; this file records only the
source objects and their elementary API.  Nothing here asserts any of the
paper's results.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.LatticeSubexp22.MainResults

open scoped BigOperators ENNReal
open Finset

/-! ## Vectors -/

/-- Integer lattice coordinates in dimension `n`. -/
abbrev ZVec (n : ℕ) := Fin n → ℤ

/-- Residue vectors `Z_q^n` (paper's `Z_q^n`, p. 5). -/
abbrev QVec (n q : ℕ) := Fin n → ZMod q

/-- Real vectors of length `n`. -/
abbrev RVec (n : ℕ) := Fin n → ℝ

/-- The pointwise reduction of an integer vector modulo `q`. -/
def zvecToQ {n q : ℕ} (a : ZVec n) : QVec n q := fun i => (a i : ZMod q)

/-- Unfolding lemma: `zvecToQ` is pointwise reduction modulo `q`. -/
@[simp] theorem zvecToQ_apply {n q : ℕ} (a : ZVec n) (i : Fin n) :
    zvecToQ a i = (a i : ZMod q) := rfl

/-- The Euclidean norm of an integer vector, written via its real embedding. -/
noncomputable def zvecNorm {n : ℕ} (a : ZVec n) : ℝ :=
  Real.sqrt (∑ i : Fin n, ((a i : ℝ)) ^ 2)

/-- The defining equation of `zvecNorm`: `‖a‖² = ∑ᵢ aᵢ²` (used to convert the
squared norm bounds of Section 2.1, p. 6, into norm bounds). -/
theorem zvecNorm_sq {n : ℕ} (a : ZVec n) :
    zvecNorm a ^ 2 = ∑ i : Fin n, ((a i : ℝ)) ^ 2 := by
  unfold zvecNorm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- The Euclidean norm of an integer vector is nonnegative, the lower bound
needed for the infimum defining `modNorm` (Section 2.1, p. 6). -/
theorem zvecNorm_nonneg {n : ℕ} (a : ZVec n) : 0 ≤ zvecNorm a :=
  Real.sqrt_nonneg _

/-- Pointwise embedding of an integer vector into the reals. -/
noncomputable def zvecToReal {n : ℕ} (a : ZVec n) : RVec n :=
  fun i => (a i : ℝ)

/-- Unfolding lemma: `zvecToReal` is pointwise coercion to `ℝ`. -/
@[simp] theorem zvecToReal_apply {n : ℕ} (a : ZVec n) (i : Fin n) :
    zvecToReal a i = (a i : ℝ) := rfl

/-- Euclidean bound for integer vectors with coordinatewise bound `σ`:
`‖a‖ ≤ √n · σ`. -/
theorem zvecNorm_le_of_coord_le {n : ℕ} {a : ZVec n} {σ : ℕ}
    (h : ∀ i, |(a i : ℝ)| ≤ (σ : ℝ)) : zvecNorm a ≤ Real.sqrt (n : ℝ) * (σ : ℝ) := by
  have hs : ∑ i : Fin n, ((a i : ℝ)) ^ 2 ≤ (n : ℝ) * (σ : ℝ) ^ 2 := by
    calc ∑ i : Fin n, ((a i : ℝ)) ^ 2 ≤ ∑ _i : Fin n, (σ : ℝ) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro i _
          have h0 : (0 : ℝ) ≤ |(a i : ℝ)| := abs_nonneg _
          nlinarith [h i, abs_nonneg (a i : ℝ), sq_abs (a i : ℝ)]
      _ = (n : ℝ) * (σ : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc zvecNorm a = Real.sqrt (∑ i : Fin n, ((a i : ℝ)) ^ 2) := rfl
    _ ≤ Real.sqrt ((n : ℝ) * (σ : ℝ) ^ 2) := Real.sqrt_le_sqrt hs
    _ = Real.sqrt (n : ℝ) * (σ : ℝ) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (Nat.cast_nonneg σ)]

/-! ## The modular norm `‖·‖_q` -/

/-- The set of integer lifts of a residue vector. -/
def LiftSet {n q : ℕ} (y : QVec n q) : Set (ZVec n) :=
  {a | ∀ i, ((a i : ℤ) : ZMod q) = y i}

/-- The paper's modular norm `‖y‖_q = min_{a ≡ y (mod q)} ‖a‖` on `Z_q^n`
(Section 2.1, p. 6), as the infimum of the Euclidean norms of integer lifts. -/
noncomputable def modNorm {n q : ℕ} [NeZero q] (y : QVec n q) : ℝ :=
  ⨅ (a : {a : ZVec n // a ∈ LiftSet y}), zvecNorm a.1

/-- The digit lift of a residue vector: the `ZMod.val` coordinates. -/
def digitLift {n q : ℕ} [NeZero q] (y : QVec n q) : ZVec n := fun i => ((y i).val : ℤ)

/-- The digit lift is an integer lift of `y`: `digitLift y ≡ y (mod q)`.  This
supplies the nonempty index type of the infimum in `modNorm` (Section 2.1,
p. 6, where `‖y‖_q` ranges over all integer lifts). -/
theorem digitLift_mem_liftSet {n q : ℕ} [NeZero q] (y : QVec n q) :
    digitLift y ∈ LiftSet y := by
  intro i
  unfold digitLift
  have h := ZMod.natCast_zmod_val (y i)
  simpa using h

instance liftSet_nonempty {n q : ℕ} [NeZero q] (y : QVec n q) :
    Nonempty {a : ZVec n // a ∈ LiftSet y} :=
  ⟨⟨digitLift y, digitLift_mem_liftSet y⟩⟩

/-- The range of `zvecNorm` is bounded below by zero. -/
theorem bddBelow_range_zvecNorm {n : ℕ} :
    BddBelow (Set.range (fun a : ZVec n => zvecNorm a)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact zvecNorm_nonneg a

/-- Any integer lift bounds the modular norm: `‖y‖_q ≤ ‖a‖`. -/
theorem modNorm_le_lift {n q : ℕ} [NeZero q] {y : QVec n q} (a : ZVec n)
    (ha : a ∈ LiftSet y) : modNorm y ≤ zvecNorm a := by
  unfold modNorm
  refine ciInf_le (show BddBelow (Set.range
    (fun b : {a : ZVec n // a ∈ LiftSet y} => zvecNorm b.1)) from ?_) ⟨a, ha⟩
  refine ⟨0, ?_⟩
  rintro _ ⟨b, rfl⟩
  exact zvecNorm_nonneg b.1

/-- The modular norm is nonnegative. -/
theorem modNorm_nonneg {n q : ℕ} [NeZero q] (y : QVec n q) : 0 ≤ modNorm y := by
  unfold modNorm
  exact le_ciInf (fun a => zvecNorm_nonneg a.1)

/-- The modular norm is at most the digit lift: `‖y‖_q ≤ √(∑ yᵢ²)` for `yᵢ` the
`ZMod.val` digits. -/
theorem modNorm_le_digitLift {n q : ℕ} [NeZero q] (y : QVec n q) :
    modNorm y ≤ zvecNorm (digitLift y) :=
  modNorm_le_lift _ (digitLift_mem_liftSet y)

/-- Modular distance `dist_q(y, z) = ‖y - z‖_q`. -/
noncomputable def modDist {n q : ℕ} [NeZero q] (y z : QVec n q) : ℝ :=
  modNorm (y - z)

/-- The modular norm of a single residue `s ∈ Z_q`, viewed as the length-one vector
`(s)`.  This is the scalar `|s|_q` used in the sampling lemmas (p. 15). -/
noncomputable def residueNorm {q : ℕ} [NeZero q] (s : ZMod q) : ℝ :=
  modNorm (fun _ : Fin 1 => s)

/-- The modular distance `|s - t|_q` between two residues. -/
noncomputable def residueDist {q : ℕ} [NeZero q] (s t : ZMod q) : ℝ :=
  residueNorm (s - t)

/-- The inner product `s · a = ∑ᵢ sᵢ aᵢ ∈ Z_q` of two coefficient vectors. -/
def dotCoeff {r q : ℕ} (s a : Fin r → ZMod q) : ZMod q :=
  ∑ i : Fin r, s i * a i

/-! ## Subgroups of `Z_q^n`: shortest vector length and distance -/

/-- The paper's shortest nonzero group-element length `λ₁(G)` (Section 2.1, p. 7). -/
noncomputable def lambda1 {n q : ℕ} [NeZero q] (G : AddSubgroup (QVec n q)) : ℝ :=
  ⨅ (v : {v : QVec n q // v ∈ G ∧ v ≠ 0}), modNorm v.1

/-- `dist_q(y, G) = min_{v ∈ G} ‖y - v‖_q` (Section 2.1, p. 7). -/
noncomputable def subgroupDist {n q : ℕ} [NeZero q] (y : QVec n q)
    (G : AddSubgroup (QVec n q)) : ℝ :=
  ⨅ (v : {v : QVec n q // v ∈ G}), modNorm (y - v.1)

/-- A closest group element of `y` in `G`. -/
def IsClosestGroupElement {n q : ℕ} [NeZero q] (y : QVec n q)
    (G : AddSubgroup (QVec n q)) (s : QVec n q) : Prop :=
  s ∈ G ∧ ∀ v ∈ G, modNorm (y - s) ≤ modNorm (y - v)

/-- A finite abelian group decomposition `(G, q, r)` of a subgroup of `Z_q^n`
(Section 2.1, p. 6): the columns `gens` span `G`, and `orders i` is the order of
the `i`-th generator. -/
structure DecomposedSubgroup (n q : ℕ) where
  /-- the finite group rank `r` -/
  r : ℕ
  /-- generator columns `G ∈ Z_q^{n×r}` -/
  gens : Fin r → QVec n q
  /-- orders `q₁, …, q_r` of the columns -/
  orders : Fin r → ℕ
  /-- the periodicity is positive -/
  hq : 0 < q
  /-- each order is positive -/
  orders_pos : ∀ i, 0 < orders i
  /-- each generator is killed by its order -/
  gen_order : ∀ i, orders i • gens i = 0

namespace DecomposedSubgroup

variable {n q : ℕ} (D : DecomposedSubgroup n q)

/-- The subgroup `G` spanned by the decomposition's generators. -/
def group : AddSubgroup (QVec n q) :=
  AddSubgroup.closure (Set.range D.gens)

/-- The shortest nonzero element length of the decomposed group. -/
noncomputable def lambda1 : ℝ :=
  haveI : NeZero q := ⟨D.hq.ne'⟩
  LatticeSubexp22.MainResults.lambda1 D.group

/-- The distance from a residue vector to the decomposed group. -/
noncomputable def dist (t : QVec n q) : ℝ :=
  haveI : NeZero q := ⟨D.hq.ne'⟩
  LatticeSubexp22.MainResults.subgroupDist t D.group

/-- Each generator lies in the decomposed group `G = ⟨g₁, …, g_r⟩` (Definition 13.2,
p. 11). -/
theorem gens_mem_group (i : Fin D.r) : D.gens i ∈ D.group :=
  AddSubgroup.subset_closure ⟨i, rfl⟩

end DecomposedSubgroup

/-! ## Cube states (Definition 13, p. 11) -/

/-- The paper's centred cube `[±σ]^n = {-σ, …, σ-1}^n ⊆ Z^n` (p. 11): the residue
set `{q-σ+1, …, σ} ⊆ Z_q` of size `2σ`, lifted to the centred representatives. -/
noncomputable def signedBox (n σ : ℕ) : Finset (ZVec n) :=
  Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(σ : ℤ)) ((σ : ℤ) - 1))

/-- Membership in the centred cube: `z ∈ [±σ]^n` iff every coordinate satisfies
`-σ ≤ zᵢ ≤ σ-1` (Definition 13.1, p. 11). -/
theorem mem_signedBox {n σ : ℕ} {z : ZVec n} :
    z ∈ signedBox n σ ↔ ∀ i, -(σ : ℤ) ≤ z i ∧ z i ≤ (σ : ℤ) - 1 := by
  unfold signedBox
  rw [Fintype.mem_piFinset]
  constructor
  · intro h i
    exact Finset.mem_Icc.mp (h i)
  · intro h i
    exact Finset.mem_Icc.mpr (h i)

/-- The translation of the cube supported at `y` by an integer vector `z`. -/
def cubePoint {n q : ℕ} (y : QVec n q) (z : ZVec n) : QVec n q := y + zvecToQ z

/-- The normalization `(2σ)^{-n/2}` of a cube state (Definition 13.1, p. 11). -/
noncomputable def cubeNormSq (n σ : ℕ) : ℝ := (Real.sqrt (2 * (σ : ℝ))) ^ n

/-- The amplitude function of the cube state: the coefficient of `|x⟩` in
`(2σ)^{-n/2} ∑_{z ∈ [±σ]^n} |y + z⟩` is `(2σ)^{-n/2}` times the number of
`z ∈ [±σ]^n` with `y + z = x` (equal to one when the cube is embedded). -/
noncomputable def cubeFun {n q : ℕ} [NeZero q] (σ : ℕ) (y : QVec n q) :
    QVec n q → ℂ :=
  fun x => ((cubeNormSq n σ)⁻¹ : ℂ) *
    ((signedBox n σ).sum (fun z => if cubePoint y z = x then (1 : ℂ) else 0))

/-- The cube state `|C(y)⟩ = (2σ)^{-n/2} ∑_{z ∈ [±σ]^n} |y + z⟩`
(Definition 13.1, p. 11). -/
noncomputable def cubeState {n q : ℕ} [NeZero q] (σ : ℕ) (y : QVec n q) :
    EuclideanSpace ℂ (QVec n q) :=
  WithLp.toLp 2 (cubeFun (n := n) (q := q) σ y)

/-- Unfolding lemma: `cubeState` evaluates to `cubeFun`. -/
@[simp] theorem cubeState_apply {n q : ℕ} [NeZero q] (σ : ℕ) (y x : QVec n q) :
    cubeState (n := n) (q := q) σ y x = cubeFun σ y x := rfl

/-- The additive translation equivalence `y ↦ y + x`. -/
def addRightEquiv {n q : ℕ} (x : QVec n q) : QVec n q ≃ QVec n q where
  toFun y := y + x
  invFun y := y - x
  left_inv y := by simp
  right_inv y := by simp

/-- The shift operator `U_x |y⟩ = |x + y⟩` on `Z_q^n`, as the linear isometry
reindexing the computational basis (Definition 13.2, p. 11). -/
noncomputable def shiftOp {n q : ℕ} [NeZero q] (x : QVec n q) :
    EuclideanSpace ℂ (QVec n q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (QVec n q) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (addRightEquiv x)

/-- Unfolding lemma: `shiftOp x` sends `f` to `y ↦ f (y - x)`. -/
@[simp] theorem shiftOp_apply {n q : ℕ} [NeZero q] (x : QVec n q)
    (f : EuclideanSpace ℂ (QVec n q)) (y : QVec n q) :
    shiftOp x f y = f (y - x) := by
  unfold shiftOp addRightEquiv
  simp [LinearIsometryEquiv.piLpCongrLeft_apply]

/-- The residue character `ω_q^s = exp(2πi s/q)` of the paper (p. 10). -/
noncomputable def qRoot (q : ℕ) [NeZero q] (s : ZMod q) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((s.val : ℝ) / (q : ℝ)))

/-- The group element `Gc = ∑ᵢ cᵢ gᵢ ∈ Z_q^n` attached to the coefficient vector
`c ∈ C̃ = Z_q^r` (Definition 13, p. 11). -/
def pcsPoint {n q : ℕ} (D : DecomposedSubgroup n q) (c : Fin D.r → ZMod q) :
    QVec n q :=
  ∑ i : Fin D.r, ((c i).val : ℕ) • D.gens i

/-- The phase character `χ_a(c) = ∏ᵢ ω_q^{aᵢ cᵢ}` of the phased cube state
(Definition 13.2, p. 11). -/
noncomputable def pcsChar {q : ℕ} [NeZero q] {r : ℕ}
    (a c : Fin r → ZMod q) : ℂ :=
  ∏ i : Fin r, qRoot q (a i * c i)

/-- The phase character of the phased cube state, as an abstract multiplicative
character on the coefficient box. -/
structure PCSPhase (r : ℕ) where
  /-- the character `χ_a(c)`, with `a` the label index -/
  phase : (Fin r → ℕ) → ℂ
  /-- characters have unit modulus -/
  phase_unit : ∀ c, ‖phase c‖ = 1
  /-- multiplicativity over coefficient addition -/
  phase_mul : ∀ c d, phase (c + d) = phase c * phase d

/-! ## Approximate eigenvectors (Definition 9, p. 9) -/

/-- Definition 9 (p. 9): `ψ` is an `ε`-approximate eigenvector of `U` with
eigenvalue `λ` if `‖Uψ - λψ‖ ≤ ε`.  The operator is taken as a plain function so
that both `LinearIsometry`s and `LinearIsometryEquiv`s (the shift operators
`U_x`) can be passed. -/
def IsApproximateEigenvector {E : Type*} [NormedAddCommGroup E] [Module ℂ E]
    (U : E → E) (ψ : E) (lam : ℂ) (ε : ℝ) : Prop :=
  ‖U ψ - lam • ψ‖ ≤ ε

/-- The norm of the phase-state `T^{-1/2} ∑_{k<T} |k⟩ ⊗ v_k`, modelled on the
orthonormal family `|k⟩`: `‖∑_k |k⟩⊗v_k‖ = √(∑_k ‖v_k‖²)`. -/
noncomputable def phaseStateNorm {E : Type*} [NormedAddCommGroup E] (T : ℕ)
    (v : Fin T → E) : ℝ :=
  Real.sqrt (∑ k : Fin T, ‖v k‖ ^ 2)

/-! ## Integer lattices and BDD -/

/-- The lattice generated by the columns of an integer basis matrix. -/
def basisLattice {n : ℕ} (B : Fin n → Fin n → ℤ) : AddSubgroup (ZVec n) :=
  AddSubgroup.closure (Set.range (fun j : Fin n => fun i => B i j))

/-- The mod-`q` image of the lattice generated by `B`. -/
def modBasisLattice {n q : ℕ} (B : Fin n → Fin n → ℤ) : AddSubgroup (QVec n q) :=
  AddSubgroup.closure (Set.range (fun j : Fin n => fun i => (B i j : ZMod q)))

/-- `L(B)` is `q`-periodic: `q Z^n ⊆ L(B)` (Section 2.1, p. 5). -/
def IsQPeriodic {n : ℕ} (B : Fin n → Fin n → ℤ) (q : ℕ) : Prop :=
  ∀ i : Fin n, (fun j => if j = i then (q : ℤ) else 0) ∈ basisLattice B

/-- `L(B)` has finite group rank `r`: a decomposition of `L mod q` with `r`
generators. -/
def HasFiniteGroupRank {n q : ℕ} (B : Fin n → Fin n → ℤ) (r : ℕ) : Prop :=
  ∃ D : DecomposedSubgroup n q, D.r = r ∧ D.group = modBasisLattice B

/-- Euclidean distance between integer vectors. -/
noncomputable def intDist {n : ℕ} (t u : ZVec n) : ℝ := zvecNorm (t - u)

/-- The shortest nonzero vector length of the integer lattice `L(B)`. -/
noncomputable def latticeLambda1 {n : ℕ} (B : Fin n → Fin n → ℤ) : ℝ :=
  ⨅ (v : {v : ZVec n // v ∈ basisLattice B ∧ v ≠ 0}), zvecNorm v.1

/-- The BDD promise of Definition 3 (p. 7): there is a lattice vector within
`ε₁ λ₁(L)`. -/
def BDDPromise {n : ℕ} (B : Fin n → Fin n → ℤ) (t : ZVec n) (ε1 : ℝ) : Prop :=
  ∃ v : ZVec n, v ∈ basisLattice B ∧ intDist t v < ε1 * latticeLambda1 B

/-- `v` is a closest vector of `L(B)` to `t`. -/
def IsClosestVector {n : ℕ} (B : Fin n → Fin n → ℤ) (t v : ZVec n) : Prop :=
  v ∈ basisLattice B ∧ ∀ u ∈ basisLattice B, intDist t v ≤ intDist t u

/-- A coarse polynomial bound in `n` and `log q`, used to phrase the paper's
`poly(n, log q)` running times for algorithms whose time is a single real number. -/
def PolyBound (f : ℝ) (n q : ℕ) : Prop :=
  ∃ k : ℕ, f ≤ ((n : ℝ) + 1) ^ k * (Real.log (q : ℝ) + 1) ^ k

/-- A randomized algorithm for BDD in dimension `n`: an output law and a running
time, both as functions of the (basis, target) instance and the periodicity. -/
structure BDDRandomAlgorithm (n : ℕ) where
  /-- the output distribution on input `(B, t)` -/
  run : (Fin n → Fin n → ℤ) → ZVec n → PMF (ZVec n)
  /-- the running time on input `(B, t)` with periodicity `q` -/
  time : (Fin n → Fin n → ℤ) → ℕ → ℝ

/-- The probability mass a PMF assigns to a set. -/
noncomputable def pmfProb {α : Type*} (p : PMF α) (s : Set α) : ℝ≥0∞ := by
  classical
  exact ∑' x, if x ∈ s then (p x : ℝ≥0∞) else 0

/-- A deterministic algorithm for approximate CVP in dimension `m`. -/
structure CVPAlgorithm (m : ℕ) where
  run : (Fin m → Fin m → ℤ) → ZVec m → ZVec m
  time : (Fin m → Fin m → ℤ) → ℝ

/-- A deterministic basis-reduction algorithm in dimension `n`. -/
structure BasisReductionAlgorithm (n : ℕ) where
  run : (Fin n → Fin n → ℤ) → (Fin n → Fin n → ℤ)
  time : (Fin n → Fin n → ℤ) → ℝ

/-- The columns of `B` are linearly independent over `ℚ` (so `B` is a basis). -/
def IsBasisMatrix {n : ℕ} (B : Fin n → Fin n → ℤ) : Prop :=
  LinearIndependent ℚ (fun j : Fin n => fun i => (B i j : ℚ))

/-- The maximal length of the basis vectors of `B` (the paper's `B` in the
running-time bound of Theorem 5). -/
noncomputable def basisMaxLength {n : ℕ} (B : Fin n → Fin n → ℤ) : ℝ :=
  ⨆ j : Fin n, zvecNorm (fun i => B i j)

end Qatlib.Papers.LatticeSubexp22.MainResults
