/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dimension.Finrank
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

set_option backward.isDefEq.respectTransparency false

/-!
# HamDecodedQI25: source model

Hamiltonian Decoded Quantum Interferometry, fixed arXiv:2510.07913 (v1, 2025-10).
This module fixes the paper-local objects shared by the claim modules:

* sign-free `n`-qubit Pauli strings and their symplectic vectors (Definition 8–9);
* commuting Pauli Hamiltonians with coefficients `v_i ∈ {±1}` and the
  symplectic code `Symp(H)` together with its logical dimension and distance
  (Definition 9);
* the anticommutation graph of formal variables (Definition 17), the
  antisymmetry character `α_G` and the `β`-function (Definitions 18–20);
* elementary symmetric polynomials `e_a(V)` (Eqn. (285));
* a minimal gate-list model of a state-preparation procedure, used only to
  phrase the "efficiently prepares" conclusions.  The model records an actual
  unitary acting on `n` qubits plus an ancilla register, together with a
  declared gate count; gate locality is *not* imposed (see the module note in
  `StatePreparation.lean`).

Boundary: this block models the paper's mathematical objects.  It does not
model a uniform circuit compiler, oracle input tapes or classical preprocessing
machines; those aspects of the algorithmic claims are recorded in the docstring
of the corresponding theorem and are not folded into the statements.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexOrder
open Matrix

namespace Qatlib.Papers.HamDecodedQI25.MainResults

/-! ## Pauli strings and symplectic vectors -/

/-- The four sign-free single-qubit Pauli letters. -/
inductive PauliLetter where
  | I : PauliLetter
  | X : PauliLetter
  | Y : PauliLetter
  | Z : PauliLetter
deriving DecidableEq, Repr, Fintype

/-- A sign-free `n`-qubit Pauli string, `P ∈ {I,X,Y,Z}^{⊗ n}`. -/
abbrev PauliString (n : ℕ) := Fin n → PauliLetter

namespace PauliString

variable {n : ℕ}

/-- Support of a Pauli string (Definition 5 of the paper). -/
def supp (P : PauliString n) : Finset (Fin n) :=
  Finset.univ.filter fun i => P i ≠ PauliLetter.I

/-- Hamming weight of a Pauli string. -/
def weight (P : PauliString n) : ℕ := (supp P).card

/-- `X`-part of the symplectic vector (Definition 8). -/
def xPart (P : PauliString n) : Fin n → ZMod 2 :=
  fun i => if P i = PauliLetter.X ∨ P i = PauliLetter.Y then 1 else 0

/-- `Z`-part of the symplectic vector (Definition 8). -/
def zPart (P : PauliString n) : Fin n → ZMod 2 :=
  fun i => if P i = PauliLetter.Z ∨ P i = PauliLetter.Y then 1 else 0

/-- Symplectic representation `symp(P) ∈ F₂^{2n}` (Definition 8). -/
def symp (P : PauliString n) : (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  (xPart P, zPart P)

/-- Weight of a symplectic vector: number of qubits on which it acts. -/
def vecWeight (v : (Fin n → ZMod 2) × (Fin n → ZMod 2)) : ℕ :=
  (Finset.univ.filter fun i => v.1 i ≠ 0 ∨ v.2 i ≠ 0).card

end PauliString

/-- Symplectic inner product over `F₂` (Eqn. (98) of the paper). -/
def symplecticInner {n : ℕ}
    (u v : (Fin n → ZMod 2) × (Fin n → ZMod 2)) : ZMod 2 :=
  ∑ i, (u.1 i * v.2 i + u.2 i * v.1 i)

/-- Two Pauli strings commute iff their symplectic inner product vanishes. -/
def PauliCommutes {n : ℕ} (P Q : PauliString n) : Prop :=
  symplecticInner (PauliString.symp P) (PauliString.symp Q) = 0

/-- The symplectic inner product is symmetric. -/
theorem symplecticInner_comm {n : ℕ}
    (u v : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
    symplecticInner u v = symplecticInner v u := by
  unfold symplecticInner
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The symplectic inner product of a vector with itself vanishes in characteristic two. -/
theorem symplecticInner_self {n : ℕ}
    (u : (Fin n → ZMod 2) × (Fin n → ZMod 2)) : symplecticInner u u = 0 := by
  unfold symplecticInner
  refine Finset.sum_eq_zero fun i _ => ?_
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc u.1 i * u.2 i + u.2 i * u.1 i = 2 * (u.1 i * u.2 i) := by ring
    _ = 0 := by rw [h2, zero_mul]

/-! ## Pauli Hamiltonians and the symplectic code -/

/-- A Pauli Hamiltonian `H = ∑_{i=1}^m v_i P_i` with `v_i ∈ {±1}`. -/
structure PauliHamiltonian (n m : ℕ) where
  /-- Coefficients `v_i`. -/
  coef : Fin m → ℝ
  /-- Pauli strings `P_i`. -/
  op : Fin m → PauliString n
  /-- Every coefficient is `+1` or `-1`. -/
  coef_unit : ∀ i, coef i = 1 ∨ coef i = -1

namespace PauliHamiltonian

variable {n m : ℕ}

/-- The Hamiltonian is commuting (Definition 6). -/
def IsCommuting (H : PauliHamiltonian n m) : Prop :=
  ∀ i j, PauliCommutes (H.op i) (H.op j)

variable (H : PauliHamiltonian n m)

/-- The symplectic code `Symp(H) ⊆ F₂^{2n}` (Definition 9). -/
def symplecticCode : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
  Submodule.span (ZMod 2) (Set.range fun i => PauliString.symp (H.op i))

/-- Number of logical bits `k = dim Symp(H)`. -/
def logicalDim : ℕ := Module.finrank (ZMod 2) (symplecticCode H)

/-- `Symp(H)` has minimum distance at least `d` (used for `d^⊥`). -/
def HasDistanceAtLeast (d : ℕ) : Prop :=
  ∀ v ∈ symplecticCode H, v ≠ 0 → d ≤ PauliString.vecWeight v

end PauliHamiltonian

/-- Every term of the Hamiltonian has Pauli weight exactly `w` (the `b`-regular
Z-part of Theorem 5 / Eqn. (30)). -/
def AllTermsWeight {n m : ℕ} (H : PauliHamiltonian n m) (w : ℕ) : Prop :=
  ∀ i, PauliString.weight (H.op i) = w

/-- At most `K` pairwise overlapping support (`|supp P_i ∩ supp P_j| ≤ K` for
`i ≠ j`), the hypothesis in Theorem 38. -/
def PairwiseOverlapAtMost {n m : ℕ} (H : PauliHamiltonian n m) (K : ℕ) : Prop :=
  ∀ i j, i ≠ j →
    ((PauliString.supp (H.op i)) ∩ (PauliString.supp (H.op j))).card ≤ K

/-! ## Anticommutation graphs and characters (Definitions 17–20) -/

/-- An anticommutation graph on `m` formal variables, encoded by its adjacency
function over `F₂` (Definition 17, Eqn. (99)). -/
structure AnticommGraph (m : ℕ) where
  /-- Adjacency matrix `A_{ij}`. -/
  adj : Fin m → Fin m → ZMod 2

/-- Number of inversions of the relation `z_i z_j = (1 - 2 A_{ij}) z_j z_i`. -/
def AnticommGraph.anticommutes {m : ℕ} (G : AnticommGraph m) (i j : Fin m) : Prop :=
  G.adj i j = 1

/-! ## Elementary symmetric polynomials (Eqn. (285)) -/

/-- The degree-`a` elementary symmetric polynomial in the variables `z : V → R`,
`e_a(V) = ∑_{S ⊆ V, |S| = a} ∏_{i ∈ S} z_i` (Eqn. (285)). -/
def elemSymm {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]
    (z : ι → R) (V : Finset ι) (a : ℕ) : R :=
  ∑ S ∈ V.powersetCard a, ∏ i ∈ S, z i

/-- Structural recursion for `elemSymm` under adjoining one variable. -/
theorem elemSymm_insert {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]
    (z : ι → R) (V : Finset ι) (i : ι) (hi : i ∉ V) (a : ℕ) :
    elemSymm z (insert i V) (a + 1) =
      elemSymm z V (a + 1) + z i * elemSymm z V a := by
  classical
  have hinj : ∀ x ∈ V.powersetCard a, ∀ y ∈ V.powersetCard a, insert i x = insert i y → x = y := by
    intro x hx y hy hxy
    have hxV : i ∉ x := fun h => hi ((Finset.mem_powersetCard.mp hx).1 h)
    have hyV : i ∉ y := fun h => hi ((Finset.mem_powersetCard.mp hy).1 h)
    have h := congrArg (fun s => s.erase i) hxy
    simpa [Finset.erase_insert hxV, Finset.erase_insert hyV] using h
  have hdisj : Disjoint (V.powersetCard (a + 1))
      ((V.powersetCard a).image (insert i)) := by
    apply Finset.disjoint_left.mpr
    intro S hS hS'
    obtain ⟨T, _hT, rfl⟩ := Finset.mem_image.mp hS'
    exact hi ((Finset.mem_powersetCard.mp hS).1 (Finset.mem_insert_self i T))
  unfold elemSymm
  have himg : (∑ x ∈ (V.powersetCard a).image (insert i), ∏ j ∈ x, z j) =
      ∑ S ∈ V.powersetCard a, z i * ∏ j ∈ S, z j := by
    rw [Finset.sum_image (fun x hx y hy hxy => hinj x hx y hy hxy)]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.prod_insert]
    intro hiS
    exact hi ((Finset.mem_powersetCard.mp hS).1 hiS)
  rw [Finset.powersetCard_succ_insert hi a, Finset.sum_union hdisj, Finset.mul_sum, himg]

/-- `elemSymm` at degree zero is one, including on the empty index set. -/
@[simp] theorem elemSymm_zero {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]
    (z : ι → R) (V : Finset ι) : elemSymm z V 0 = 1 := by
  classical
  unfold elemSymm
  rw [Finset.powersetCard_zero]
  simp

/-- `elemSymm` vanishes strictly beyond the cardinality of `V`. -/
theorem elemSymm_eq_zero_of_card_lt {R : Type*} [CommSemiring R] {ι : Type*}
    [DecidableEq ι] (z : ι → R) (V : Finset ι) (a : ℕ) (h : V.card < a) :
    elemSymm z V a = 0 := by
  classical
  unfold elemSymm
  rw [Finset.powersetCard_eq_empty.mpr h, Finset.sum_empty]

end Qatlib.Papers.HamDecodedQI25.MainResults
