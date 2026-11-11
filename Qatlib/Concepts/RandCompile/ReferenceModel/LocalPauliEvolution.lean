/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Foundations.OperatorErrors.OperatorError
import Mathlib.Data.List.FinRange
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError

/-!
# Local Pauli evolution circuits

This module constructs Pauli strings and explicit circuits that diagonalize them using local
basis changes and parity gates. `localPauliExactSteps` realizes Pauli evolution up to a global
phase, while `localPauliRationalSteps` replaces the central phase by a counted rational Cayley
approximation. The Pauli circuit construction follows the standard framework of
[NielsenChuang2010].

## Main statements

* `local_pauli_actual_diagonalization`: correctness and legality of the diagonalizing circuit.
* `local_pauli_exact_and_finite_phase_gate_tables`: exact semantics and finite circuit costs.
* `local_pauli_rational_actual_reference_error`: a trace norm error bound with an arbitrary
  finite reference.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.PauliClifford.ExactRank

set_option maxHeartbeats 1000000

namespace Qatlib.Concepts.RandCompile.ReferenceModel
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The single-qubit operator indexed by `0`, `1`, `2`, or `3`, corresponding to the identity,
Pauli X, Pauli Y, or Pauli Z. -/
def localPauliMatrix (a : Fin 4) : Operator 2 := ![1,pauliX,pauliY,pauliZ] a

/-- The tensor product of the single-qubit Pauli operators specified by `v`, indexed on a
register of dimension `2^q`. -/
noncomputable def pauliStringMatrix (q : ℕ) (v : Fin q → Fin 4) : Operator (2^q) :=
  tensorPauliProduct q (fun i => localPauliMatrix (v i))

/-- The set of wires on which the Pauli label is nonzero. -/
def pauliStringSupport (q : ℕ) (v : Fin q → Fin 4) : Finset (Fin q) :=
  Finset.univ.filter (fun i => v i ≠ 0)

/-- The least wire in the Pauli string support, or `none` when the support is empty. -/
def pauliStringTarget (q : ℕ) (v : Fin q → Fin 4) : Option (Fin q) :=
  ((pauliStringSupport q v).sort (· ≤ ·)).head?

/-- Each indexed local Pauli operator equals its conjugate transpose. -/
private theorem localPauliMatrix_hermitian (a : Fin 4) :
    (localPauliMatrix a)ᴴ = localPauliMatrix a := by
  fin_cases a
  · simp [localPauliMatrix]
  · exact pauliMatrix_conjTranspose 0
  · exact pauliMatrix_conjTranspose 1
  · exact pauliMatrix_conjTranspose 2

/-- Each indexed local Pauli operator squares to the identity. -/
private theorem localPauliMatrix_square (a : Fin 4) :
    localPauliMatrix a * localPauliMatrix a = 1 := by
  fin_cases a
  · simp [localPauliMatrix]
  · exact pauliMatrix_mul_self 0
  · exact pauliMatrix_mul_self 1
  · exact pauliMatrix_mul_self 2

/-- Every Pauli string is Hermitian and unitary with operator norm one, and its support consists
exactly of the nonzero labels. -/
theorem local_pauli_string_contract_and_support :
    ∀ (q : ℕ) (v : Fin q → Fin 4),
      (pauliStringMatrix q v).IsHermitian ∧
      pauliStringMatrix q v ∈ Matrix.unitaryGroup (Fin (2^q)) ℂ ∧
      ‖pauliStringMatrix q v‖ = 1 ∧
      (∀ i : Fin q, i ∈ pauliStringSupport q v ↔ v i ≠ 0) := by
  intro q v
  have hh : (pauliStringMatrix q v)ᴴ = pauliStringMatrix q v := by
    simp only [pauliStringMatrix, tensorPauliProduct_conjTranspose, localPauliMatrix_hermitian]
  have hs : pauliStringMatrix q v * pauliStringMatrix q v = 1 := by
    simp only [pauliStringMatrix, tensorPauliProduct_mul, localPauliMatrix_square,
      tensorPauliProduct_one]
  have hu : pauliStringMatrix q v ∈ Matrix.unitaryGroup (Fin (2^q)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hh, hs]
  refine ⟨hh,hu,?_,fun i => by simp [pauliStringSupport]⟩
  exact CStarRing.norm_of_mem_unitary hu

/-- The local basis-change gates that send the Pauli label on wire `w` to the Z basis, with no
gates for identity or Z labels. -/
noncomputable def pauliBasisSteps (q : ℕ) (v : Fin q → Fin 4) (w : Fin q) :
    List (ReflectionGate q) :=
  if v w = 1 then [Sum.inl (w,Hadamard)]
  else if v w = 2 then [Sum.inl (w,Rz (-Real.pi/2)),Sum.inl (w,Hadamard)]
  else []

/-- The ordered CNOT gates from all supported wires other than `target` into `target`. -/
def pauliParitySteps (q : ℕ) (v : Fin q → Fin 4) (target : Fin q) :
    List (ReflectionGate q) :=
  (((pauliStringSupport q v).sort (· ≤ ·)).filter (fun w => w ≠ target)).map
    (fun w => Sum.inr (w,target))

/-- The circuit consisting of local Pauli basis changes followed by parity accumulation into the
selected support wire. -/
noncomputable def pauliDiagonalizeSteps (q : ℕ) (v : Fin q → Fin 4) :
    List (ReflectionGate q) :=
  (List.ofFn id).flatMap (pauliBasisSteps q v) ++
    match pauliStringTarget q v with
    | none => []
    | some w => pauliParitySteps q v w

/-- The diagonalize, exact phase, and inverse-diagonalize circuit for Pauli evolution, with an
empty circuit for the identity string. -/
noncomputable def localPauliExactSteps (q : ℕ) (v : Fin q → Fin 4) (u : ℚ) :
    List (ReflectionGate q) :=
  match pauliStringTarget q v with
  | none => []
  | some w => pauliDiagonalizeSteps q v ++ [Sum.inl (w,Rz (2*(u:ℝ)))] ++
    reflectionAdjoint (pauliDiagonalizeSteps q v)

/-- The rational Cayley phase approximation at angle `2*u`, together with its four arithmetic
operation counts. -/
def localPauliPhaseData (u : ℚ) (k : ℕ) : GaussianRat × ℕ × ℕ × ℕ × ℕ :=
  let init := countedCayleyInit (2*u) k
  let phase := squareLoop init.1 k
  (phase.1, init.2.1, init.2.2.1 + phase.2.1,
    init.2.2.2.1 + phase.2.2, init.2.2.2.2)

/-- The Pauli evolution circuit using the counted rational phase approximation at precision `k`. -/
noncomputable def localPauliRationalSteps (q : ℕ) (v : Fin q → Fin 4) (u : ℚ) (k : ℕ) :
    List (ReflectionGate q) :=
  match pauliStringTarget q v with
  | none => []
  | some w =>
    let phase := localPauliPhaseData u k
    pauliDiagonalizeSteps q v ++ [Sum.inl (w,rationalPhaseGate phase.1)] ++
      reflectionAdjoint (pauliDiagonalizeSteps q v)

/-- The gate cost `2*cX + 4*cY + 2*(w-1) + 1` for a nonempty support of size `w`, and zero for
empty support. -/
def localPauliGateCost (q : ℕ) (v : Fin q → Fin 4) : ℕ :=
  let w := (pauliStringSupport q v).card
  let cX := (Finset.univ.filter (fun i => v i = 1)).card
  let cY := (Finset.univ.filter (fun i => v i = 2)).card
  if w = 0 then 0 else 2*cX + 4*cY + 2*(w-1) + 1

/-- The computed phase equals `countedCayleyPhase (2*u) k`, and its operation counts are `(k,
4*k+3, 2*k+2, 3)`. -/
theorem localPauliPhaseData_value_counts (u : ℚ) (k : ℕ) :
    (localPauliPhaseData u k).1 = (countedCayleyPhase (2*u) k).1 ∧
    (localPauliPhaseData u k).2 = (k,4*k+3,2*k+2,3) := by
  constructor
  · rfl
  · unfold localPauliPhaseData
    rw [countedCayleyInit_value_and_cost]
    have hm := (squareLoop_value_and_counts (cayleyRat (2*u/(2*2^k))) k).2.1
    have ha := (squareLoop_value_and_counts (cayleyRat (2*u/(2*2^k))) k).2.2
    simp only [hm,ha]
    simp only [Nat.add_comm]

/-- A wire selected by `pauliStringTarget` belongs to the Pauli string support. -/
theorem pauliStringTarget_mem (q : ℕ) (v : Fin q → Fin 4) (w : Fin q)
    (h : pauliStringTarget q v = some w) : w ∈ pauliStringSupport q v := by
  exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_head? h)

/-- When no target wire is selected, the Pauli string is the identity and its support has
cardinality zero. -/
theorem pauliStringTarget_none (q : ℕ) (v : Fin q → Fin 4)
    (h : pauliStringTarget q v = none) :
    pauliStringMatrix q v = 1 ∧ (pauliStringSupport q v).card = 0 := by
  have hs : pauliStringSupport q v = ∅ := by
    have hl : ((pauliStringSupport q v).sort (· ≤ ·)) = [] := List.head?_eq_none_iff.mp h
    exact by
      ext i
      simpa using (show i ∉ (pauliStringSupport q v).sort (· ≤ ·) by rw [hl]; simp)
  have hv : ∀ i, v i = 0 := by
    intro i
    have hi : i ∉ pauliStringSupport q v := by rw [hs]; simp
    simpa [pauliStringSupport] using hi
  constructor
  · simp only [pauliStringMatrix,hv,localPauliMatrix,Matrix.cons_val_zero,tensorPauliProduct_one]
  · simp [hs]

/-- The local Pauli basis-change circuit satisfies `reflectionLegal`. -/
private theorem pauliBasisSteps_legal (q : ℕ) (v : Fin q → Fin 4) (w : Fin q) :
    reflectionLegal (pauliBasisSteps q v w) := by
  unfold pauliBasisSteps reflectionLegal
  split_ifs <;> simp only [List.mem_cons, List.not_mem_nil, or_false]
  · intro g hg
    subst g
    exact hadamard_unitary
  · intro g hg
    rcases hg with rfl | rfl
    · exact rz_unitary _
    · exact hadamard_unitary
  · intro g hg
    cases hg

/-- The full Pauli diagonalization circuit satisfies `reflectionLegal`. -/
theorem pauliDiagonalizeSteps_legal (q : ℕ) (v : Fin q → Fin 4) :
    reflectionLegal (pauliDiagonalizeSteps q v) := by
  intro g hg
  unfold pauliDiagonalizeSteps at hg
  rcases List.mem_append.mp hg with hbase | hpar
  · obtain ⟨w,_,hw⟩ := List.mem_flatMap.mp hbase
    exact pauliBasisSteps_legal q v w g hw
  · cases ht : pauliStringTarget q v with
    | none => simp [ht] at hpar
    | some w =>
      simp only [ht,pauliParitySteps,List.mem_map,List.mem_filter] at hpar
      obtain ⟨c,⟨_,hc⟩,rfl⟩ := hpar
      change c ≠ w
      exact of_decide_eq_true hc

/-- Both the exact and rational Pauli evolution circuits satisfy `reflectionLegal`. -/
theorem localPauliSteps_legal (q : ℕ) (v : Fin q → Fin 4) (u : ℚ) (k : ℕ) :
    reflectionLegal (localPauliExactSteps q v u) ∧
      reflectionLegal (localPauliRationalSteps q v u k) := by
  have hd := pauliDiagonalizeSteps_legal q v
  have ha := reflectionAdjoint_legal _ hd
  constructor
  · cases ht : pauliStringTarget q v with
    | none => simp [localPauliExactSteps,ht,reflectionLegal]
    | some w =>
      intro g hg
      simp only [localPauliExactSteps,ht,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with (hg | rfl) | hg
      · exact hd g hg
      · exact rz_unitary _
      · exact ha g hg
  · cases ht : pauliStringTarget q v with
    | none => simp [localPauliRationalSteps,ht,reflectionLegal]
    | some w =>
      intro g hg
      simp only [localPauliRationalSteps,ht,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with (hg | rfl) | hg
      · exact hd g hg
      · rw [(localPauliPhaseData_value_counts u k).1]
        exact (rational_cayley_gate_unitarity_and_target_error (2*u) k).1
      · exact ha g hg

/-- The single-qubit change-of-basis matrix for each of the four Pauli labels. -/
private noncomputable def localPauliBasis (a : Fin 4) : Operator 2 :=
  ![1,pauliBasisMatrix 0,pauliBasisMatrix 1,1] a

/-- Relabeling the Boolean-indexed Hadamard matrix gives the basis-change matrix for Pauli X. -/
private theorem hadamard_pauliBasis : relabelGate boolEquivFin2 Hadamard = pauliBasisMatrix 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [relabelGate, boolEquivFin2, Hadamard, pauliBasisMatrix]

/-- The phase gate `Rz (-Real.pi/2)` is diagonal with entries `1` and `-Complex.I`. -/
private theorem rz_neg_half_pi : Rz (-Real.pi/2) =
    Matrix.diagonal (fun b : Bool => if b then -Complex.I else 1) := by
  ext i j
  simp only [Rz]
  congr 1
  funext b
  cases b
  · rfl
  · simp only [if_true]
    rw [show ((-Real.pi/2 : ℝ) : ℂ) * Complex.I = -(Real.pi/2*Complex.I) by push_cast; ring]
    rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I]
    exact Complex.inv_I

/-- Relabeling Hadamard after `Rz (-Real.pi/2)` gives the basis-change matrix for Pauli Y. -/
private theorem y_pauliBasis :
    relabelGate boolEquivFin2 (Hadamard * Rz (-Real.pi/2)) = pauliBasisMatrix 1 := by
  rw [rz_neg_half_pi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [relabelGate, boolEquivFin2, Hadamard, pauliBasisMatrix, Matrix.mul_diagonal]

/-- A gate on one wire equals the tensor product with its relabeled matrix on that wire and
identities elsewhere. -/
private theorem wireGate_density (q : ℕ) (w : Fin q) (U : Matrix Bool Bool ℂ) :
    wireGate q w U = pauliProductDensity (fun i => if i = w then relabelGate boolEquivFin2 U else 1) := by
  ext x y
  simp [wireGate, tensorPauliWireGate, tensorPauliProduct, relabelGate]

/-- The local basis-change program has the tensor product matrix with `localPauliBasis (v w)` on
wire `w`. -/
private theorem pauliBasisSteps_matrix (q : ℕ) (v : Fin q → Fin 4) (w : Fin q) :
    reflectionProgramMatrix (pauliBasisSteps q v w) =
      pauliProductDensity (fun i => if i = w then localPauliBasis (v w) else 1) := by
  generalize hv : v w = a
  fin_cases a
  · simp only [pauliBasisSteps,hv,localPauliBasis]
    simp [reflectionProgramMatrix,pauliProductDensity_one]
  · simp [pauliBasisSteps,hv,localPauliBasis,reflectionProgramMatrix,reflectionGateMatrix]
    rw [wireGate_density,hadamard_pauliBasis]
    simp [pauliBasisMatrix]
  · simp [pauliBasisSteps,hv,localPauliBasis,reflectionProgramMatrix,reflectionGateMatrix]
    rw [wireGate_mul,wireGate_density,y_pauliBasis]
    simp [pauliBasisMatrix]
  · simp only [pauliBasisSteps,hv,localPauliBasis]
    simp [reflectionProgramMatrix,pauliProductDensity_one]

/-- Basis changes on a list of distinct wires have the tensor product matrix of the selected
local bases. -/
private theorem pauliBasisLayers_matrix (q : ℕ) (v : Fin q → Fin 4) (ws : List (Fin q))
    (hws : ws.Nodup) :
    reflectionProgramMatrix (ws.flatMap (pauliBasisSteps q v)) =
      pauliProductDensity (fun i => if i ∈ ws then localPauliBasis (v i) else 1) := by
  induction ws with
  | nil => simp [reflectionProgramMatrix,pauliProductDensity_one]
  | cons w ws ih =>
    rw [List.nodup_cons] at hws
    rw [List.flatMap_cons,reflectionProgramMatrix_append,ih hws.2,pauliBasisSteps_matrix,
      pauliProductDensity_mul]
    congr 1
    funext i
    by_cases hi : i = w
    · subst i
      simp [hws.1]
    · simp [hi]

/-- Conjugation by the Pauli basis-change matrix sends the corresponding nonidentity Pauli
matrix to Pauli Z. -/
private theorem pauliBasisMatrix_push (a : Fin 3) :
    pauliBasisMatrix a * pauliMatrix a * (pauliBasisMatrix a)ᴴ = pauliZ := by
  have hu : pauliBasisMatrix a * (pauliBasisMatrix a)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp (pauliBasisMatrix_unitary a)
  rw [← pauliBasisMatrix_conj_z a]
  calc _ = (pauliBasisMatrix a * (pauliBasisMatrix a)ᴴ) * pauliZ *
      (pauliBasisMatrix a * (pauliBasisMatrix a)ᴴ) := by noncomm_ring
    _ = pauliZ := by rw [hu]; simp

/-- The local basis change sends a nonzero Pauli label to Z by conjugation and leaves the
identity label equal to the identity. -/
private theorem localPauliBasis_push (a : Fin 4) :
    localPauliBasis a * localPauliMatrix a * (localPauliBasis a)ᴴ =
      if a = 0 then 1 else pauliZ := by
  fin_cases a
  · simp [localPauliBasis,localPauliMatrix]
  · exact pauliBasisMatrix_push 0
  · exact pauliBasisMatrix_push 1
  · simp [localPauliBasis,localPauliMatrix]

/-- Applying all local basis-change programs gives the tensor product of their local basis
matrices. -/
private theorem pauliBasisFull_matrix (q : ℕ) (v : Fin q → Fin 4) :
    reflectionProgramMatrix ((List.ofFn id).flatMap (pauliBasisSteps q v)) =
      pauliProductDensity (fun i => localPauliBasis (v i)) := by
  simpa using pauliBasisLayers_matrix q v (List.ofFn id) (List.nodup_ofFn.mpr Function.injective_id)

/-- Relabeling a Pauli string onto Boolean registers gives the product of its local Pauli
matrices. -/
private theorem pauliStringMatrix_pull (q : ℕ) (v : Fin q → Fin 4) :
    relabelGate (bitVecEquiv q).symm (pauliStringMatrix q v) =
      pauliProductDensity (fun i => localPauliMatrix (v i)) := by
  ext x y
  simp [pauliStringMatrix,tensorPauliProduct,relabelGate]

/-- Conjugating a Pauli string by all local basis changes yields Z on every supported wire and
identity elsewhere. -/
private theorem pauliBasisFull_push (q : ℕ) (v : Fin q → Fin 4) :
    reflectionProgramMatrix ((List.ofFn id).flatMap (pauliBasisSteps q v)) *
      relabelGate (bitVecEquiv q).symm (pauliStringMatrix q v) *
      (reflectionProgramMatrix ((List.ofFn id).flatMap (pauliBasisSteps q v)))ᴴ =
      pauliProductDensity (fun i => if v i = 0 then 1 else pauliZ) := by
  rw [pauliBasisFull_matrix,pauliStringMatrix_pull,pauliProductDensity_conjTranspose,
    pauliProductDensity_mul,pauliProductDensity_mul]
  simp only [localPauliBasis_push]

/-- The complex sign `-1` for a true bit and `1` for a false bit. -/
private def pauliBitSign (b : Bool) : ℂ := if b then -1 else 1
/-- The product of the bit signs over the specified support. -/
private def pauliSupportSign {q : ℕ} (s : Finset (Fin q)) (x : Reg q) : ℂ :=
  ∏ i ∈ s, pauliBitSign (x i)
/-- The diagonal register operator whose entries are the parity signs on the specified support. -/
private def pauliSupportZ {q : ℕ} (s : Finset (Fin q)) : Matrix (Reg q) (Reg q) ℂ :=
  Matrix.diagonal (pauliSupportSign s)

/-- The sign of the exclusive-or of two bits is the product of their signs. -/
private theorem pauliBitSign_xor (a b : Bool) :
    pauliBitSign (a ^^ b) = pauliBitSign a * pauliBitSign b := by
  cases a <;> cases b <;> simp [pauliBitSign]

/-- A tensor product of diagonal single-qubit matrices is diagonal with entries given by the
products of local entries. -/
private theorem density_diagonal {q : ℕ} (d : Fin q → Fin 2 → ℂ) :
    pauliProductDensity (fun i => Matrix.diagonal (d i)) =
      Matrix.diagonal (fun x => ∏ i, d i (boolEquivFin2 (x i))) := by
  have h := tensorPauliProduct_diagonal q d
  have hx := congrArg (relabelGate (bitVecEquiv q).symm) h
  ext x y
  have he := congrFun (congrFun hx x) y
  simpa [tensorPauliProduct,relabelGate,Matrix.diagonal_apply] using he

/-- The tensor product of Z on a support and identities elsewhere equals `pauliSupportZ`. -/
private theorem density_supportZ (q : ℕ) (s : Finset (Fin q)) :
    pauliProductDensity (fun i => if i ∈ s then pauliZ else 1) = pauliSupportZ s := by
  have hf : (fun i => if i ∈ s then pauliZ else (1 : Operator 2)) =
      (fun i => Matrix.diagonal (fun b : Fin 2 =>
        if i ∈ s then pauliBitSign (boolEquivFin2.symm b) else 1)) := by
    funext i
    by_cases hi : i ∈ s
    · simp only [if_pos hi]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [pauliZ,pauliBitSign,boolEquivFin2]
    · simp [hi]
  rw [hf,density_diagonal]
  congr 1
  funext x
  simp [pauliSupportSign,Finset.prod_ite_mem]

/-- A Z gate on wire `w` equals the support-Z operator for the singleton `{w}`. -/
private theorem wireGate_pauliZ (q : ℕ) (w : Fin q) :
    wireGate q w PauliZ = pauliSupportZ {w} := by
  rw [wireGate_density]
  have hz : relabelGate boolEquivFin2 PauliZ = pauliZ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [relabelGate,boolEquivFin2,PauliZ,pauliZ]
  rw [hz]
  simpa using density_supportZ q {w}

/-- Conjugating a diagonal matrix by an involutive permutation matrix composes its diagonal
function with that permutation. -/
private theorem perm_conj_diagonal {I : Type} [Fintype I] [DecidableEq I]
    (σ : I → I) (hσ : Function.Involutive σ) (d : I → ℂ) :
    permMatrix σ * Matrix.diagonal d * (permMatrix σ)ᴴ =
      Matrix.diagonal (fun x => d (σ x)) := by
  classical
  rw [permMatrix_conjTranspose hσ]
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,permMatrix,Matrix.of_apply]
  rw [Finset.sum_eq_single (σ y)]
  · by_cases h : x = y
    · subst y
      simp [hσ x]
    · simp [h,hσ y]
  · intro z _ hz
    simp [hz]
  · simp

/-- Updating a supported target bit by an unsupported control bit multiplies the support parity
by the control sign. -/
private theorem supportSign_cnot {q : ℕ} (s : Finset (Fin q)) (c t : Fin q)
    (ht : t ∈ s) (hc : c ∉ s) (x : Reg q) :
    pauliSupportSign s (Function.update x t (x t ^^ x c)) =
      pauliSupportSign (insert c s) x := by
  classical
  have hct : c ≠ t := fun h => hc (h ▸ ht)
  have he : ∏ i ∈ s.erase t, pauliBitSign (Function.update x t (x t ^^ x c) i) =
      ∏ i ∈ s.erase t, pauliBitSign (x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  unfold pauliSupportSign
  rw [← Finset.mul_prod_erase _ _ ht,Function.update_self,pauliBitSign_xor,he,
    Finset.prod_insert hc,← Finset.mul_prod_erase _ _ ht]
  ring

/-- Conjugating a support-Z operator by a CNOT adds the unsupported control to the support when
the target is supported. -/
private theorem cnot_pull_support {q : ℕ} (s : Finset (Fin q)) (c t : Fin q)
    (ht : t ∈ s) (hc : c ∉ s) :
    (cnotGate q c t)ᴴ * pauliSupportZ s * cnotGate q c t =
      pauliSupportZ (insert c s) := by
  have hct : c ≠ t := fun h => hc (h ▸ ht)
  have hh := permMatrix_conjTranspose (cnotUpdate_involutive q c t hct)
  have hp := perm_conj_diagonal (fun x : Reg q => Function.update x t (x t ^^ x c))
    (cnotUpdate_involutive q c t hct) (pauliSupportSign s)
  simp only [hh] at hp
  change cnotGate q c t * Matrix.diagonal (pauliSupportSign s) * cnotGate q c t = _ at hp
  rw [show (cnotGate q c t)ᴴ = cnotGate q c t from hh]
  rw [pauliSupportZ,hp]
  congr 1
  funext x
  exact supportSign_cnot s c t ht hc x

/-- Pulling a target Z through CNOTs from distinct other wires gives Z parity on the target
together with those controls. -/
private theorem pauliParityList_pull (q : ℕ) (t : Fin q) (ws : List (Fin q))
    (hws : ws.Nodup) (ht : t ∉ ws) :
    (reflectionProgramMatrix (ws.map (fun c => Sum.inr (c,t))))ᴴ * wireGate q t PauliZ *
      reflectionProgramMatrix (ws.map (fun c => Sum.inr (c,t))) =
      pauliSupportZ (insert t ws.toFinset) := by
  induction ws with
  | nil => simp [reflectionProgramMatrix,wireGate_pauliZ]
  | cons c ws ih =>
    have hnd := List.nodup_cons.mp hws
    have htc : t ≠ c ∧ t ∉ ws := by
      simpa only [List.mem_cons,not_or] using ht
    have hc : c ∉ insert t ws.toFinset := by
      simp [hnd.1,Ne.symm htc.1]
    simp only [List.map_cons,reflectionProgramMatrix,reflectionGateMatrix,Matrix.conjTranspose_mul]
    calc
      _ = (cnotGate q c t)ᴴ *
          ((reflectionProgramMatrix (ws.map (fun c => Sum.inr (c,t))))ᴴ * wireGate q t PauliZ *
            reflectionProgramMatrix (ws.map (fun c => Sum.inr (c,t)))) * cnotGate q c t := by
        noncomm_ring
      _ = (cnotGate q c t)ᴴ * pauliSupportZ (insert t ws.toFinset) * cnotGate q c t := by
        rw [ih hnd.2 htc.2]
      _ = pauliSupportZ (insert c (insert t ws.toFinset)) :=
        cnot_pull_support _ _ _ (Finset.mem_insert_self _ _) hc
      _ = _ := by simp [Finset.insert_comm]

/-- Pulling target Z through the Pauli parity program gives Z parity on the full Pauli string
support. -/
private theorem pauliParitySteps_pull (q : ℕ) (v : Fin q → Fin 4) (w : Fin q)
    (hw : w ∈ pauliStringSupport q v) :
    (reflectionProgramMatrix (pauliParitySteps q v w))ᴴ * wireGate q w PauliZ *
      reflectionProgramMatrix (pauliParitySteps q v w) = pauliSupportZ (pauliStringSupport q v) := by
  let ws := ((pauliStringSupport q v).sort (· ≤ ·)).filter (fun c => c ≠ w)
  have hn : ws.Nodup := (Finset.sort_nodup _ _).filter _
  have ht : w ∉ ws := by simp [ws]
  have he : insert w ws.toFinset = pauliStringSupport q v := by
    ext i
    simp only [Finset.mem_insert, List.mem_toFinset, ws, List.mem_filter,Finset.mem_sort]
    by_cases hi : i = w
    · subst i
      simp [hw]
    · simp [hi]
  exact (pauliParityList_pull q w ws hn ht).trans (congrArg pauliSupportZ he)

/-- The Pauli parity accumulation program satisfies `reflectionLegal`. -/
private theorem pauliParitySteps_legal (q : ℕ) (v : Fin q → Fin 4) (w : Fin q) :
    reflectionLegal (pauliParitySteps q v w) := by
  intro g hg
  simp only [pauliParitySteps,List.mem_map,List.mem_filter] at hg
  obtain ⟨c,⟨_,hc⟩,rfl⟩ := hg
  change c ≠ w
  exact of_decide_eq_true hc

/-- The diagonalization program is legal and sends a nonidentity Pauli string to target-wire Z
by conjugation. When no target exists, the string is the identity with empty support. -/
theorem local_pauli_actual_diagonalization :
    ∀ (q : ℕ) (v : Fin q → Fin 4),
      reflectionLegal (pauliDiagonalizeSteps q v) ∧
      match pauliStringTarget q v with
      | none => pauliStringMatrix q v = 1 ∧ (pauliStringSupport q v).card = 0
      | some w => w ∈ pauliStringSupport q v ∧
        reflectionProgramMatrix (pauliDiagonalizeSteps q v) *
          relabelGate (bitVecEquiv q).symm (pauliStringMatrix q v) *
          (reflectionProgramMatrix (pauliDiagonalizeSteps q v))ᴴ = wireGate q w PauliZ := by
  intro q v
  refine ⟨pauliDiagonalizeSteps_legal q v,?_⟩
  cases ht : pauliStringTarget q v with
  | none => exact pauliStringTarget_none q v ht
  | some w =>
    have hw := pauliStringTarget_mem q v w ht
    refine ⟨hw,?_⟩
    have hbase : reflectionProgramMatrix ((List.ofFn id).flatMap (pauliBasisSteps q v)) *
        relabelGate (bitVecEquiv q).symm (pauliStringMatrix q v) *
        (reflectionProgramMatrix ((List.ofFn id).flatMap (pauliBasisSteps q v)))ᴴ =
        pauliSupportZ (pauliStringSupport q v) := by
      rw [pauliBasisFull_push,← density_supportZ]
      congr 1
      funext i
      by_cases hi : v i = 0 <;> simp [pauliStringSupport,hi]
    let C := reflectionProgramMatrix (pauliParitySteps q v w)
    have hu : C * Cᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp
        (reflectionProgramMatrix_unitary _ (pauliParitySteps_legal q v w))
    have hp := pauliParitySteps_pull q v w hw
    unfold pauliDiagonalizeSteps
    rw [ht,reflectionProgramMatrix_append,Matrix.conjTranspose_mul]
    calc
      _ = C * (reflectionProgramMatrix ((List.ofFn id).flatMap (pauliBasisSteps q v)) *
          relabelGate (bitVecEquiv q).symm (pauliStringMatrix q v) *
          (reflectionProgramMatrix ((List.ofFn id).flatMap (pauliBasisSteps q v)))ᴴ) * Cᴴ := by
        dsimp [C]
        noncomm_ring
      _ = C * pauliSupportZ (pauliStringSupport q v) * Cᴴ := by rw [hbase]
      _ = C * (Cᴴ * wireGate q w PauliZ * C) * Cᴴ := by rw [hp]
      _ = (C * Cᴴ) * wireGate q w PauliZ * (C * Cᴴ) := by noncomm_ring
      _ = wireGate q w PauliZ := by rw [hu]; simp

/-- The full basis-change program uses one gate per X label and two gates per Y label. -/
private theorem pauliBasisFull_length (q : ℕ) (v : Fin q → Fin 4) :
    ((List.ofFn id).flatMap (pauliBasisSteps q v)).length =
      (Finset.univ.filter (fun i => v i = 1)).card +
        2*(Finset.univ.filter (fun i => v i = 2)).card := by
  classical
  have hl : ∀ i : Fin q, (pauliBasisSteps q v i).length =
      (if v i = 1 then 1 else 0) + 2*(if v i = 2 then 1 else 0) := by
    intro i
    unfold pauliBasisSteps
    by_cases h1 : v i = 1
    · have h2 : v i ≠ 2 := by rw [h1]; decide
      simp [h1]
    · by_cases h2 : v i = 2 <;> simp [h1,h2]
  rw [List.length_flatMap,List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply,id_eq,hl]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  congr 1
  · exact (Finset.card_filter _ _).symm
  · congr 1
    exact (Finset.card_filter _ _).symm

/-- For a supported target, the parity program length is the support cardinality minus one. -/
private theorem pauliParitySteps_length (q : ℕ) (v : Fin q → Fin 4) (w : Fin q)
    (hw : w ∈ pauliStringSupport q v) :
    (pauliParitySteps q v w).length = (pauliStringSupport q v).card - 1 := by
  classical
  let ws := ((pauliStringSupport q v).sort (· ≤ ·)).filter (fun c => c ≠ w)
  have hn : ws.Nodup := (Finset.sort_nodup _ _).filter _
  have he : ws.toFinset = (pauliStringSupport q v).erase w := by
    ext i
    simp [ws,and_comm]
  simp only [pauliParitySteps,List.length_map]
  change ws.length = _
  rw [← List.toFinset_card_of_nodup hn,he,Finset.card_erase_of_mem hw]

/-- The compiled rational Pauli evolution circuit has exactly `localPauliGateCost q v` gates. -/
theorem localPauliSteps_gateCount (q : ℕ) (v : Fin q → Fin 4) (u : ℚ) (k : ℕ) :
    GateCount (reflectionCompile (localPauliRationalSteps q v u k)) = localPauliGateCost q v := by
  rw [gateCount_reflectionCompile]
  cases ht : pauliStringTarget q v with
  | none => simp [localPauliRationalSteps,ht,localPauliGateCost,(pauliStringTarget_none q v ht).2]
  | some w =>
    have hw := pauliStringTarget_mem q v w ht
    have hn : (pauliStringSupport q v).card ≠ 0 := Finset.card_ne_zero.mpr ⟨w,hw⟩
    simp only [localPauliRationalSteps,List.length_append,List.length_cons,List.length_nil,
      reflectionAdjoint_length,pauliDiagonalizeSteps,ht,List.length_append]
    rw [pauliBasisFull_length,pauliParitySteps_length q v w hw]
    unfold localPauliGateCost
    rw [if_neg hn]
    omega

/-- The Pauli evolution gate cost is at most `6*q+1`. -/
private theorem localPauliGateCost_le (q : ℕ) (v : Fin q → Fin 4) :
    localPauliGateCost q v ≤ 6*q+1 := by
  classical
  have hxy : (Finset.univ.filter (fun i => v i = 1)).card +
      (Finset.univ.filter (fun i => v i = 2)).card ≤ q := by
    have hd : Disjoint (Finset.univ.filter (fun i => v i = 1))
        (Finset.univ.filter (fun i => v i = 2)) := by
      rw [Finset.disjoint_left]
      intro i hi hj
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
      have : (1 : Fin 4) = 2 := hi.symm.trans hj
      contradiction
    rw [← Finset.card_union_of_disjoint hd]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin q)
  have hs : (pauliStringSupport q v).card ≤ q :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin q)
  unfold localPauliGateCost
  (try dsimp only)
  split_ifs <;> omega

/-- Embedding a diagonal single-qubit gate on wire `w` gives a diagonal register matrix
determined by the bit on `w`. -/
private theorem wireGate_diagonal (q : ℕ) (w : Fin q) (d : Bool → ℂ) :
    wireGate q w (Matrix.diagonal d) = Matrix.diagonal (fun x => d (x w)) := by
  classical
  ext x y
  rw [wireGate_apply]
  by_cases hxy : x = y
  · subst y
    simp
  · rw [Matrix.diagonal_apply_ne _ hxy]
    by_cases ho : ∀ i : Fin q, i ≠ w → x i = y i
    · have hw : x w ≠ y w := fun he => hxy (funext (fun i => by
        by_cases hi : i = w
        · subst i; exact he
        · exact ho i hi))
      simp [Matrix.diagonal_apply_ne _ hw]
    · simp [ho]

/-- The wire phase gate at angle `2*u` equals evolution under wire Z for time `u`, multiplied by
`exp (I*u)`. -/
private theorem wireGate_phase_evolution (q : ℕ) (w : Fin q) (u : ℝ) :
    wireGate q w (Rz (2*u)) =
      Complex.exp (Complex.I*(u:ℂ)) • HamiltonianEvolution (wireGate q w PauliZ) u := by
  rw [Rz,wireGate_diagonal,wireGate_pauliZ]
  unfold HamiltonianEvolution pauliSupportZ
  rw [← Matrix.diagonal_smul,Matrix.exp_diagonal,← Matrix.diagonal_smul]
  congr 1
  funext x
  simp only [Pi.smul_apply]
  rw [Pi.coe_exp,← Complex.exp_eq_exp_ℂ]
  simp only [Pi.smul_apply,pauliSupportSign,Finset.prod_singleton,pauliBitSign,smul_eq_mul]
  rw [← Complex.exp_add]
  cases x w <;> simp
  congr 1
  ring

/-- Matrix exponentiation commutes with relabeling by an equivalence of finite index types. -/
private theorem local_relabel_exp {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℂ) :
    NormedSpace.exp (relabelGate e A) = relabelGate e (NormedSpace.exp A) := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e)
    (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap.continuous_of_finiteDimensional A).symm

/-- Hamiltonian evolution commutes with conjugation by a unitary change of basis. -/
private theorem local_evolution_conjugate {I : Type} [Fintype I] [DecidableEq I]
    (D Z : Matrix I I ℂ) (hD : D ∈ Matrix.unitaryGroup I ℂ) (u : ℝ) :
    HamiltonianEvolution (Dᴴ * Z * D) u = Dᴴ * HamiltonianEvolution Z u * D := by
  have hl : D * Dᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hD
  have hr : Dᴴ * D = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hD
  let U : (Matrix I I ℂ)ˣ := ⟨D,Dᴴ,hl,hr⟩
  unfold HamiltonianEvolution
  rw [show (-Complex.I*(u:ℂ)) • (Dᴴ*Z*D) =
      Dᴴ*((-Complex.I*(u:ℂ)) • Z)*D by simp]
  exact Matrix.exp_units_conj' U _

/-- Evolution under the identity Hamiltonian becomes the identity after multiplication by the
scalar phase `exp (I*u)`. -/
private theorem local_identity_phase {I : Type} [Fintype I] [DecidableEq I] (u : ℝ) :
    (1 : Matrix I I ℂ) = Complex.exp (Complex.I*(u:ℂ)) • HamiltonianEvolution 1 u := by
  unfold HamiltonianEvolution
  rw [← Matrix.diagonal_one,← Matrix.diagonal_smul,Matrix.exp_diagonal,← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [Pi.coe_exp,← Complex.exp_eq_exp_ℂ,← Complex.exp_add]
  simp

/-- The relabeled exact Pauli circuit equals evolution under the Pauli string for time `u`,
multiplied by the global phase `exp (I*u)`. -/
theorem localPauliExactSteps_evolution (q : ℕ) (v : Fin q → Fin 4) (u : ℚ) :
    relabelGate (bitVecEquiv q) (reflectionProgramMatrix (localPauliExactSteps q v u)) =
      Complex.exp (Complex.I*(u:ℂ)) • HamiltonianEvolution (pauliStringMatrix q v) (u:ℝ) := by
  cases ht : pauliStringTarget q v with
  | none =>
    rw [localPauliExactSteps,ht,reflectionProgramMatrix,(pauliStringTarget_none q v ht).1]
    have he : relabelGate (bitVecEquiv q) (1 : Matrix (Reg q) (Reg q) ℂ) = 1 := by
      ext x y
      simp [relabelGate,Matrix.one_apply]
    rw [he]
    exact local_identity_phase _
  | some w =>
    let D := reflectionProgramMatrix (pauliDiagonalizeSteps q v)
    let P := relabelGate (bitVecEquiv q).symm (pauliStringMatrix q v)
    have hd := pauliDiagonalizeSteps_legal q v
    have hu := reflectionProgramMatrix_unitary _ hd
    have hdu : Dᴴ * D = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
    have hdiag : D * P * Dᴴ = wireGate q w PauliZ := by
      have h := (local_pauli_actual_diagonalization q v).2
      rw [ht] at h
      exact h.2
    have hp : Dᴴ * wireGate q w PauliZ * D = P := by
      rw [← hdiag]
      calc _ = (Dᴴ*D)*P*(Dᴴ*D) := by noncomm_ring
        _ = P := by rw [hdu]; simp
    have he : reflectionProgramMatrix (localPauliExactSteps q v u) =
        Complex.exp (Complex.I*(u:ℂ)) • HamiltonianEvolution P (u:ℝ) := by
      rw [localPauliExactSteps,ht,reflectionProgramMatrix_append,reflectionAdjoint_matrix _ hd,
        reflectionProgramMatrix_append]
      simp only [reflectionProgramMatrix,reflectionGateMatrix,one_mul]
      rw [wireGate_phase_evolution,Matrix.smul_mul,Matrix.mul_smul]
      simp only [Complex.ofReal_ratCast]
      congr 1
      rw [← mul_assoc,← local_evolution_conjugate D (wireGate q w PauliZ) hu,hp]
    rw [he]
    unfold HamiltonianEvolution
    have hm : relabelGate (bitVecEquiv q)
        (NormedSpace.exp ((-Complex.I*((u:ℝ):ℂ)) • P)) =
        NormedSpace.exp ((-Complex.I*((u:ℝ):ℂ)) • pauliStringMatrix q v) := by
      rw [← local_relabel_exp]
      congr 1
      ext x y
      simp [P,relabelGate]
    change Complex.exp (Complex.I*(u:ℂ)) • relabelGate (bitVecEquiv q)
      (NormedSpace.exp ((-Complex.I*((u:ℝ):ℂ)) • P)) = _
    rw [hm]

/-- The exact and rational Pauli circuits are legal, with the stated exact semantics and zero
queries for the rational circuit. The rational circuit and its adjoint have the same
explicit gate cost, bounded by `6*q+1`. -/
theorem local_pauli_exact_and_finite_phase_gate_tables :
    ∀ (q : ℕ) (v : Fin q → Fin 4) (u : ℚ) (k : ℕ),
      reflectionLegal (localPauliExactSteps q v u) ∧
      reflectionLegal (localPauliRationalSteps q v u k) ∧
      GateCount (reflectionCompile (localPauliRationalSteps q v u k)) = localPauliGateCost q v ∧
      QueryCount (reflectionCompile (localPauliRationalSteps q v u k)) = 0 ∧
      localPauliGateCost q v ≤ 6*q+1 ∧
      GateCount (reflectionCompile (reflectionAdjoint (localPauliRationalSteps q v u k))) =
        localPauliGateCost q v ∧
      relabelGate (bitVecEquiv q) (reflectionProgramMatrix (localPauliExactSteps q v u)) =
        Complex.exp (Complex.I*(u:ℂ)) • HamiltonianEvolution (pauliStringMatrix q v) (u:ℝ) := by
  intro q v u k
  exact ⟨(localPauliSteps_legal q v u k).1,(localPauliSteps_legal q v u k).2,
    localPauliSteps_gateCount q v u k,queryCount_reflectionCompile _,localPauliGateCost_le q v,
    by rw [gateCount_reflectionCompile,reflectionAdjoint_length,← gateCount_reflectionCompile];
       exact localPauliSteps_gateCount q v u k,
    localPauliExactSteps_evolution q v u⟩

/-- Embedding two diagonal single-qubit gates on a wire does not increase the operator norm of
their difference. -/
private theorem wireGate_diagonal_error (q : ℕ) (w : Fin q) (d e : Bool → ℂ) :
    ‖wireGate q w (Matrix.diagonal d) - wireGate q w (Matrix.diagonal e)‖ ≤
      ‖Matrix.diagonal d - Matrix.diagonal e‖ := by
  rw [wireGate_diagonal,wireGate_diagonal,Matrix.diagonal_sub,Matrix.diagonal_sub,
    Matrix.l2_opNorm_diagonal,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro x
  exact norm_le_pi_norm (d-e) (x w)

/-- Conjugating a matrix by a unitary does not increase its operator norm. -/
private theorem local_norm_sandwich {I : Type} [Fintype I] [DecidableEq I]
    (D E : Matrix I I ℂ) (hD : D ∈ Matrix.unitaryGroup I ℂ) :
    ‖Dᴴ * E * D‖ ≤ ‖E‖ := by
  have h := l2_norm_unitary_le_one hD
  have hh : ‖Dᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact h
  calc
    _ ≤ ‖Dᴴ * E‖ * ‖D‖ := norm_mul_le _ _
    _ ≤ (‖Dᴴ‖ * ‖E‖) * ‖D‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖E‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hh (norm_nonneg _)) h (norm_nonneg _)
      (by positivity)
    _ = ‖E‖ := by ring

/-- For `|2*u| ≤ 1`, the rational and exact Pauli program matrices differ in operator norm by at
most `(1/2)^k`. -/
private theorem localPauliProgram_error (q : ℕ) (v : Fin q → Fin 4) (u : ℚ) (k : ℕ)
    (h : |(2*u : ℚ)| ≤ 1) :
    ‖reflectionProgramMatrix (localPauliRationalSteps q v u k) -
      reflectionProgramMatrix (localPauliExactSteps q v u)‖ ≤ (1/2 : ℝ)^k := by
  cases ht : pauliStringTarget q v with
  | none => simp [localPauliRationalSteps,localPauliExactSteps,ht]
  | some w =>
    let D := reflectionProgramMatrix (pauliDiagonalizeSteps q v)
    have hd := pauliDiagonalizeSteps_legal q v
    have hu := reflectionProgramMatrix_unitary _ hd
    have ha : |((2*u : ℚ) : ℝ)| ≤ 1 := by exact_mod_cast h
    have hc := (rational_cayley_gate_unitarity_and_target_error (2*u) k).2 ha
    have he : ‖wireGate q w (rationalPhaseGate (localPauliPhaseData u k).1) -
        wireGate q w (Rz (2*(u:ℝ)))‖ ≤ (1/2 : ℝ)^k := by
      rw [(localPauliPhaseData_value_counts u k).1]
      have hz : (((2*u:ℚ):ℝ)) = 2*(u:ℝ) := by push_cast; ring
      rw [hz] at hc
      exact (wireGate_diagonal_error q w _ _).trans (by simpa only [one_div] using! hc)
    rw [localPauliRationalSteps,localPauliExactSteps,ht,
      reflectionProgramMatrix_append,reflectionProgramMatrix_append,
      reflectionAdjoint_matrix _ hd]
    simp only [reflectionProgramMatrix_append,reflectionProgramMatrix,reflectionGateMatrix,one_mul,
      reflectionAdjoint_matrix _ hd]
    have hs : Dᴴ * (wireGate q w (rationalPhaseGate (localPauliPhaseData u k).1) * D) -
        Dᴴ * (wireGate q w (Rz (2*(u:ℝ))) * D) =
        Dᴴ * (wireGate q w (rationalPhaseGate (localPauliPhaseData u k).1) -
          wireGate q w (Rz (2*(u:ℝ)))) * D := by noncomm_ring
    rw [hs]
    exact (local_norm_sandwich D _ hu).trans he

/-- Relabeling a unitary matrix by an equivalence of finite index types preserves unitarity. -/
private theorem local_relabel_unitary {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) : relabelGate e U ∈ Matrix.unitaryGroup J ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose] at hU ⊢
  simp only [relabelGate,Matrix.reindex_apply,Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv,hU,Matrix.submatrix_one_equiv]

/-- A scalar phase satisfying `z * star z = 1` cancels in conjugation after tensoring with an
identity reference. -/
private theorem local_phase_reference_cancel {D r : ℕ} (V : Operator D) (z : ℂ)
    (hz : z * star z = 1) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    TensorGate (z • V) (1 : Operator r) * X * (TensorGate (z • V) (1 : Operator r))ᴴ =
      TensorGate V (1 : Operator r) * X * (TensorGate V (1 : Operator r))ᴴ := by
  have hzz : star z * z = 1 := by rw [mul_comm,hz]
  simp only [TensorGate,Matrix.smul_kronecker,Matrix.conjTranspose_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,hzz,one_smul]

/-- For `|2*u| ≤ 1`, rational Pauli circuit conjugation differs from exact Pauli evolution by at
most `2*(1/2)^k*Matrix.traceNorm X`, for every finite reference and matrix input. -/
theorem local_pauli_rational_actual_reference_error :
    ∀ (q : ℕ) (v : Fin q → Fin 4) (u : ℚ) (k r : ℕ)
      (X : Matrix (Fin (2^q) × Fin r) (Fin (2^q) × Fin r) ℂ),
      |(2*u : ℚ)| ≤ 1 →
      let U :=
          relabelGate (bitVecEquiv q) (reflectionProgramMatrix (localPauliRationalSteps q v u k))
      let V := HamiltonianEvolution (pauliStringMatrix q v) (u:ℝ)
      Matrix.traceNorm (TensorGate U (1 : Operator r)*X*(TensorGate U (1 : Operator r))ᴴ -
        TensorGate V (1 : Operator r)*X*(TensorGate V (1 : Operator r))ᴴ) ≤
          2*(1/2 : ℝ)^k*Matrix.traceNorm X := by
  intro q v u k r X h
  (try dsimp only)
  let U := relabelGate (bitVecEquiv q) (reflectionProgramMatrix (localPauliRationalSteps q v u k))
  let E := relabelGate (bitVecEquiv q) (reflectionProgramMatrix (localPauliExactSteps q v u))
  have hU := local_relabel_unitary (bitVecEquiv q) _
    (reflectionProgramMatrix_unitary _ (localPauliSteps_legal q v u k).2)
  have hE := local_relabel_unitary (bitVecEquiv q) _
    (reflectionProgramMatrix_unitary _ (localPauliSteps_legal q v u k).1)
  have hn : ‖U-E‖ ≤ (1/2 : ℝ)^k := by
    rw [l2_norm_relabelGate_sub]
    exact localPauliProgram_error q v u k h
  have hz : Complex.exp (Complex.I*(u:ℂ)) * star (Complex.exp (Complex.I*(u:ℂ))) = 1 := by
    rw [RCLike.star_def,← Complex.exp_conj,← Complex.exp_add]
    simp
  have hc := local_phase_reference_cancel (HamiltonianEvolution (pauliStringMatrix q v) (u:ℝ))
    _ hz X
  have he : E = Complex.exp (Complex.I*(u:ℂ)) •
      HamiltonianEvolution (pauliStringMatrix q v) (u:ℝ) := localPauliExactSteps_evolution q v u
  have hb := finite_reference_conjugation_error U E r X hU hE
  have hb' := hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 2)) (Matrix.traceNorm_nonneg X))
  rw [he,hc] at hb'
  exact hb'

end Qatlib.Concepts.RandCompile.ReferenceModel
