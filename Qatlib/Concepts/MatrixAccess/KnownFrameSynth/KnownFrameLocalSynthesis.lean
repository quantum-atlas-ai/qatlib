/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.MultiControlConsumers
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

/-!
# Exact local synthesis of known unitaries

`TwoLevelInstruction` describes a qubit block on two basis coordinates or a phase on one
coordinate. Finite vector elimination gives exact unitary factorizations of length at most `d *
(d + 1) / 2` in dimension `d`. The synthesis framework follows the use of elementary local gates
in [BarencoEtAl1995].

Wire embeddings, address permutations, and multicontrolled known gates turn these factors into
legal local gate lists with arbitrary known single-qubit matrices. `knownFrameEmbed` appends `n
+ 1` zero workspace qubits, which are restored after each construction; the final `n`-qubit
unitary implementation has at most `128 * (n + 1)² * 4ⁿ` gates and zero oracle queries.

## Main statements

* `known_unitary_two_level_factorization`: bounded exact factorization into legal two-level
  instructions.
* `known_two_level_gray_local_implementation`: bounded local implementation of one legal
  instruction.
* `known_unitary_actual_clean_local_synthesis`: exact local synthesis with restored workspace
  and explicit gate and query counts.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false

/-- An instruction acting by a qubit matrix on two chosen basis coordinates or by a scalar phase
on one coordinate. -/
inductive TwoLevelInstruction (I : Type) where
  | pair : I → I → Matrix Bool Bool ℂ → TwoLevelInstruction I
  | phase : I → ℂ → TwoLevelInstruction I

/-- Requires distinct coordinates and a unitary qubit block for a pair instruction, or a
unit-modulus scalar for a phase instruction. -/
def twoLevelLegal {I : Type} : TwoLevelInstruction I → Prop
  | .pair x y B => x ≠ y ∧ B ∈ unitaryGroup Bool ℂ
  | .phase _ z => star z*z = 1

/-- The matrix acting by the specified block or phase on the selected coordinates and by the
identity elsewhere. -/
noncomputable def twoLevelMatrix {I : Type} [DecidableEq I] :
    TwoLevelInstruction I → Matrix I I ℂ
  | .pair x y B => fun u v =>
      if u = x then if v = x then B false false else if v = y then B false true else 0
      else if u = y then if v = x then B true false else if v = y then B true true else 0
      else if u = v then 1 else 0
  | .phase x z => fun u v => if u = v then if u = x then z else 1 else 0

/-- The matrix obtained by executing a list of two-level instructions in list order. -/
noncomputable def twoLevelProgram {I : Type} [Fintype I] [DecidableEq I]
    (ts : List (TwoLevelInstruction I)) : Matrix I I ℂ :=
  ts.foldl (fun acc g => twoLevelMatrix g * acc) 1

/-- Embeds an `n`-qubit state by appending `n + 1` qubits in the all-false basis state. -/
noncomputable def knownFrameEmbed (n : ℕ) (ψ : QState (Reg n)) : QState (Reg (n+(n+1))) :=
  relabelState (regAppendEquiv n (n+1)).symm
    (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin (n+1) => false)))

/-- Folding two-level instructions by left multiplication starting at `A` gives the program
matrix multiplied by `A`. -/
private theorem twoLevel_foldl {I : Type} [Fintype I] [DecidableEq I]
    (ts : List (TwoLevelInstruction I)) (A : Matrix I I ℂ) :
    ts.foldl (fun acc g => twoLevelMatrix g * acc) A = twoLevelProgram ts * A := by
  induction ts generalizing A with
  | nil => simp [twoLevelProgram]
  | cons g ts ih =>
    simp only [List.foldl_cons, twoLevelProgram]
    rw [ih, ih]
    simp only [mul_one, mul_assoc]

/-- Prepending an instruction multiplies its matrix on the right of the tail program matrix. -/
theorem twoLevelProgram_cons {I : Type} [Fintype I] [DecidableEq I]
    (g : TwoLevelInstruction I) (ts : List (TwoLevelInstruction I)) :
    twoLevelProgram (g :: ts) = twoLevelProgram ts * twoLevelMatrix g := by
  simp only [twoLevelProgram, List.foldl_cons, mul_one]
  exact twoLevel_foldl ts _

/-- Appending two two-level programs multiplies their matrices with the later program on the
left. -/
theorem twoLevelProgram_append {I : Type} [Fintype I] [DecidableEq I]
    (ts us : List (TwoLevelInstruction I)) :
    twoLevelProgram (ts ++ us) = twoLevelProgram us * twoLevelProgram ts := by
  simp only [twoLevelProgram, List.foldl_append]
  exact twoLevel_foldl us _

/-- A phase instruction multiplies the amplitude at its selected coordinate by the phase and
leaves all other amplitudes unchanged. -/
theorem twoLevel_phase_mulVec {I : Type} [Fintype I] [DecidableEq I]
    (x : I) (z : ℂ) (ψ : QState I) (u : I) :
    (twoLevelMatrix (.phase x z) *ᵥ ψ) u = if u = x then z * ψ u else ψ u := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single u]
  · simp [twoLevelMatrix]
  · intro v _ hv
    simp [twoLevelMatrix, Ne.symm hv]
  · simp

/-- A pair instruction with distinct coordinates applies its qubit block to their two amplitudes
and fixes every other amplitude. -/
theorem twoLevel_pair_mulVec {I : Type} [Fintype I] [DecidableEq I]
    (x y : I) (B : Matrix Bool Bool ℂ) (hxy : x ≠ y) (ψ : QState I) (u : I) :
    (twoLevelMatrix (.pair x y B) *ᵥ ψ) u =
      if u = x then B false false * ψ x + B false true * ψ y
      else if u = y then B true false * ψ x + B true true * ψ y else ψ u := by
  rw [Matrix.mulVec, dotProduct]
  by_cases hx : u = x
  · subst u
    calc
      _ = ∑ v : I, ((if v = x then B false false * ψ x else 0) +
          (if v = y then B false true * ψ y else 0)) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hvx : v = x <;> by_cases hvy : v = y <;>
          simp_all [twoLevelMatrix]
      _ = _ := by simp [Finset.sum_add_distrib]
  · by_cases hy : u = y
    · subst u
      calc
        _ = ∑ v : I, ((if v = x then B true false * ψ x else 0) +
            (if v = y then B true true * ψ y else 0)) := by
          apply Finset.sum_congr rfl
          intro v _
          by_cases hvx : v = x <;> by_cases hvy : v = y <;>
            simp_all [twoLevelMatrix]
        _ = _ := by simp [Finset.sum_add_distrib, Ne.symm hxy]
    · rw [Finset.sum_eq_single u]
      · simp [twoLevelMatrix, hx, hy]
      · intro v _ hv
        simp [twoLevelMatrix, hx, hy, Ne.symm hv]
      · simp

/-- A single-coordinate phase matrix is unitary when its scalar has unit modulus. -/
theorem twoLevel_phase_unitary {I : Type} [Fintype I] [DecidableEq I]
    (x : I) (z : ℂ) (hz : star z * z = 1) :
    twoLevelMatrix (.phase x z) ∈ unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext u v
  change (twoLevelMatrix (.phase x z) *ᵥ
    (fun t => star (twoLevelMatrix (.phase x z) v t))) u = _
  rw [twoLevel_phase_mulVec]
  by_cases huv : u = v <;> by_cases hux : u = x <;>
    simp_all [twoLevelMatrix, Matrix.one_apply, mul_comm, eq_comm]

/-- Multiplying pair matrices on the same distinct coordinates multiplies their qubit blocks. -/
theorem twoLevel_pair_mul {I : Type} [Fintype I] [DecidableEq I]
    (x y : I) (B C : Matrix Bool Bool ℂ) (hxy : x ≠ y) :
    twoLevelMatrix (.pair x y B) * twoLevelMatrix (.pair x y C) =
      twoLevelMatrix (.pair x y (B*C)) := by
  ext u v
  change (twoLevelMatrix (.pair x y B) *ᵥ
    (fun t => twoLevelMatrix (.pair x y C) t v)) u = _
  rw [twoLevel_pair_mulVec x y B hxy]
  by_cases hux : u = x <;> by_cases huy : u = y <;>
    by_cases hvx : v = x <;> by_cases hvy : v = y <;>
    simp_all [twoLevelMatrix, Matrix.mul_apply, Ne.symm hxy, add_comm]

/-- The pair matrix with identity block on distinct coordinates is the identity. -/
theorem twoLevel_pair_one {I : Type} [DecidableEq I]
    (x y : I) (hxy : x ≠ y) :
    twoLevelMatrix (.pair x y (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext u v
  by_cases hux : u = x <;> by_cases huy : u = y <;>
    by_cases hvx : v = x <;> by_cases hvy : v = y <;>
    simp_all [twoLevelMatrix, Matrix.one_apply, eq_comm]

/-- The adjoint of a pair matrix on distinct coordinates is obtained by taking the adjoint of
its block. -/
theorem twoLevel_pair_conjTranspose {I : Type} [DecidableEq I]
    (x y : I) (B : Matrix Bool Bool ℂ) (hxy : x ≠ y) :
    (twoLevelMatrix (.pair x y B))ᴴ = twoLevelMatrix (.pair x y Bᴴ) := by
  ext u v
  by_cases hux : u = x <;> by_cases huy : u = y <;>
    by_cases hvx : v = x <;> by_cases hvy : v = y <;>
    simp_all [twoLevelMatrix, Matrix.conjTranspose_apply, eq_comm]

/-- Embedding a unitary qubit block on two distinct coordinates gives a unitary matrix. -/
theorem twoLevel_pair_unitary {I : Type} [Fintype I] [DecidableEq I]
    (x y : I) (B : Matrix Bool Bool ℂ) (hxy : x ≠ y)
    (hB : B ∈ unitaryGroup Bool ℂ) :
    twoLevelMatrix (.pair x y B) ∈ unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hB ⊢
  rw [twoLevel_pair_conjTranspose x y B hxy, twoLevel_pair_mul x y B Bᴴ hxy,
    hB, twoLevel_pair_one x y hxy]

/-- Every legal two-level instruction has a unitary matrix. -/
theorem twoLevelMatrix_unitary {I : Type} [Fintype I] [DecidableEq I]
    (g : TwoLevelInstruction I) (hg : twoLevelLegal g) :
    twoLevelMatrix g ∈ unitaryGroup I ℂ := by
  cases g with
  | pair x y B => exact twoLevel_pair_unitary x y B hg.1 hg.2
  | phase x z => exact twoLevel_phase_unitary x z hg

/-- A program of legal two-level instructions has a unitary matrix. -/
theorem twoLevelProgram_unitary {I : Type} [Fintype I] [DecidableEq I]
    (ts : List (TwoLevelInstruction I)) (hts : ∀ g ∈ ts, twoLevelLegal g) :
    twoLevelProgram ts ∈ unitaryGroup I ℂ := by
  induction ts with
  | nil => simp [twoLevelProgram]
  | cons g ts ih =>
    rw [twoLevelProgram_cons]
    exact (unitaryGroup I ℂ).mul_mem
      (ih (fun t ht => hts t (List.mem_cons_of_mem g ht)))
      (twoLevelMatrix_unitary g (hts g List.mem_cons_self))

/-- Every unitary on a singleton index type has an exact legal two-level factorization of length
at most `d * (d + 1) / 2`, where `d` is the cardinality. -/
theorem known_unitary_two_level_factorization_singleton
    (I : Type) [Fintype I] [DecidableEq I] [Unique I] (U : Matrix I I ℂ)
    (hU : U ∈ unitaryGroup I ℂ) :
    ∃ ts : List (TwoLevelInstruction I), (∀ g ∈ ts, twoLevelLegal g) ∧
      ts.length ≤ Fintype.card I * (Fintype.card I+1)/2 ∧ twoLevelProgram ts = U := by
  have hz : star (U default default) * U default default = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    simpa [Matrix.star_eq_conjTranspose, Matrix.mul_apply] using!
      congrArg (fun M : Matrix I I ℂ => M default default) h
  refine ⟨[.phase default (U default default)], ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g = .phase default (U default default) := List.mem_singleton.mp hg
    subst g
    exact hz
  · simp [Fintype.card_unique]
  · rw [twoLevelProgram_cons]
    ext u v
    have hu : u = default := Subsingleton.elim _ _
    have hv : v = default := Subsingleton.elim _ _
    subst u; subst v
    simp [twoLevelProgram, twoLevelMatrix]

/-- Every qubit unitary has an exact legal two-level factorization with at most three
instructions. -/
theorem known_unitary_two_level_factorization_bool (U : Matrix Bool Bool ℂ)
    (hU : U ∈ unitaryGroup Bool ℂ) :
    ∃ ts : List (TwoLevelInstruction Bool), (∀ g ∈ ts, twoLevelLegal g) ∧
      ts.length ≤ Fintype.card Bool * (Fintype.card Bool+1)/2 ∧ twoLevelProgram ts = U := by
  refine ⟨[.pair false true U], ?_, by simp, ?_⟩
  · intro g hg
    have hg' : g = .pair false true U := List.mem_singleton.mp hg
    subst g
    exact ⟨Bool.false_ne_true, hU⟩
  · rw [twoLevelProgram_cons]
    ext a b
    cases a <;> cases b <;> simp [twoLevelProgram, twoLevelMatrix]

/-- An embedded state's amplitude equals the original data amplitude when all appended workspace
bits are false and is zero otherwise. -/
theorem knownFrameEmbed_apply (n : ℕ) (ψ : QState (Reg n)) (x : Reg (n+(n+1))) :
    knownFrameEmbed n ψ x = ψ ((regAppendEquiv n (n+1) x).1) *
      (if (regAppendEquiv n (n+1) x).2 = (fun _ => false) then 1 else 0) := rfl

/-- Appending zero workspace commutes with complex scalar multiplication. -/
theorem knownFrameEmbed_smul (n : ℕ) (z : ℂ) (ψ : QState (Reg n)) :
    knownFrameEmbed n (z • ψ) = z • knownFrameEmbed n ψ := by
  funext x
  simp only [knownFrameEmbed_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Embedding a zero-qubit state gives its unique scalar amplitude times the false one-qubit
basis state. -/
theorem knownFrameEmbed_zero (ψ : QState (Reg 0)) :
    knownFrameEmbed 0 ψ = ψ (fun _ => false) • Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin 1 => false) := by
  funext x
  rw [knownFrameEmbed_apply]
  have hfirst : (regAppendEquiv 0 1 x).1 = (fun _ => false) := Subsingleton.elim _ _
  have hsnd : (regAppendEquiv 0 1 x).2 = x := by
    funext i
    rw [regAppendEquiv_apply_snd]
    congr 1
    exact Fin.ext (by simp)
  simp [hfirst, hsnd, Qatlib.Foundations.PureStateMath.Ket, Pi.smul_apply, smul_eq_mul]

/-- A one-gate program applying the scalar `z` to the false basis component of a single
workspace qubit. -/
noncomputable def knownScalarPhaseSteps (z : ℂ) : List (ReflectionGate 1) :=
  [Sum.inl (0, twoLevelMatrix (.phase false z))]

/-- The scalar phase program is legal when `z` has unit modulus. -/
theorem knownScalarPhaseSteps_legal (z : ℂ) (hz : star z * z = 1) :
    reflectionLegal (knownScalarPhaseSteps z) := by
  intro g hg
  have hg' : g = Sum.inl (0, twoLevelMatrix (.phase false z)) := List.mem_singleton.mp hg
  subst g
  exact twoLevel_phase_unitary false z hz

/-- The scalar phase program multiplies an embedded zero-qubit state by `z` and returns the
workspace to false. -/
theorem knownScalarPhaseSteps_run (z : ℂ) (ψ : QState (Reg 0)) :
    Run 1 (reflectionCompile (knownScalarPhaseSteps z)) (knownFrameEmbed 0 ψ) =
      knownFrameEmbed 0 (z • ψ) := by
  rw [knownFrameEmbed_smul, knownFrameEmbed_zero, run_reflectionCompile]
  simp only [knownScalarPhaseSteps, reflectionProgramMatrix, reflectionGateMatrix, one_mul]
  change wireGate 1 0 (twoLevelMatrix (.phase false z)) *ᵥ
    (ψ (fun _ => false) • Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) =
    z • (ψ (fun _ => false) • Qatlib.Foundations.PureStateMath.Ket (fun _ => false))
  rw [Matrix.mulVec_smul]
  have hk := applyGate_wireGate_ket 1 0 (twoLevelMatrix (.phase false z)) (fun _ => false)
  change wireGate 1 0
      (twoLevelMatrix (.phase false z)) *ᵥ Qatlib.Foundations.PureStateMath.Ket
      (fun _ => false) = _ at hk
  rw [hk]
  simp [twoLevelMatrix, smul_smul, mul_comm]

/-- Every legal two-level instruction on the zero-qubit register has a legal implementation
using at most 128 gates and one restored workspace qubit. -/
theorem known_two_level_local_implementation_zero
    (g : TwoLevelInstruction (Reg 0)) (hg : twoLevelLegal g) :
    ∃ gs : List (ReflectionGate 1), reflectionLegal gs ∧ gs.length ≤ 128 ∧
      ∀ ψ : QState (Reg 0),
      Run 1 (reflectionCompile gs) (knownFrameEmbed 0 ψ) =
        knownFrameEmbed 0 (twoLevelMatrix g *ᵥ ψ) := by
  cases g with
  | pair x y B => exact (hg.1 (Subsingleton.elim x y)).elim
  | phase x z =>
    refine ⟨knownScalarPhaseSteps z, knownScalarPhaseSteps_legal z hg,
      by simp [knownScalarPhaseSteps], ?_⟩
    intro ψ
    rw [knownScalarPhaseSteps_run]
    congr 1
    funext u
    rw [twoLevel_phase_mulVec, if_pos (Subsingleton.elim u x)]
    rfl

/-- The qubit block with rows `(conj(a), conj(b)) / r` and `(-b, a) / r` used to eliminate a
vector coordinate. -/
noncomputable def knownGivensBlock (a b : ℂ) (r : ℝ) : Matrix Bool Bool ℂ :=
  fun u v => match u, v with
    | false, false => star a / r
    | false, true => star b / r
    | true, false => -b / r
    | true, true => a / r

/-- The Givens block is unitary when `r` is nonzero and the squared moduli of `a` and `b` sum to
`r²`. -/
theorem knownGivensBlock_unitary (a b : ℂ) (r : ℝ) (hr : r ≠ 0)
    (h : star a*a + star b*b = (r : ℂ)^2) :
    knownGivensBlock a b r ∈ unitaryGroup Bool ℂ := by
  change (starRingEnd ℂ) a*a + (starRingEnd ℂ) b*b = (r : ℂ)^2 at h
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext u v
  cases u <;> cases v <;>
    simp [knownGivensBlock, Matrix.mul_apply, Matrix.conjTranspose_apply,
      map_div₀, map_neg] <;>
    field_simp <;> first | (solve | linear_combination h) | (solve | linear_combination -h) | ring

/-- Under the nonzero normalization condition, the Givens block sends the vector `(a, b)` to
`(r, 0)`. -/
theorem knownGivensBlock_eliminate (a b : ℂ) (r : ℝ) (hr : r ≠ 0)
    (h : star a*a + star b*b = (r : ℂ)^2) :
    knownGivensBlock a b r *ᵥ (fun t => if t then b else a) =
      (fun t => if t then 0 else (r : ℂ)) := by
  change (starRingEnd ℂ) a*a + (starRingEnd ℂ) b*b = (r : ℂ)^2 at h
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  funext t
  cases t <;>
    simp [knownGivensBlock, Matrix.mulVec, dotProduct] <;>
    field_simp <;> first | (solve | linear_combination h) | (solve | linear_combination -h) | ring

/-- For two distinct coordinates of a finite vector, a unitary qubit block can eliminate the
second coordinate. -/
theorem known_two_coordinate_elimination {I : Type} [Fintype I] [DecidableEq I]
    (x y : I) (hxy : x ≠ y) (ψ : QState I) :
    ∃ B : Matrix Bool Bool ℂ, B ∈ unitaryGroup Bool ℂ ∧
      (twoLevelMatrix (.pair x y B) *ᵥ ψ) y = 0 := by
  by_cases hz : ψ x = 0 ∧ ψ y = 0
  · refine ⟨1, (unitaryGroup Bool ℂ).one_mem, ?_⟩
    rw [twoLevel_pair_one x y hxy, Matrix.one_mulVec]
    exact hz.2
  · let r : ℝ := Real.sqrt (‖ψ x‖^2 + ‖ψ y‖^2)
    have hr : r ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      have hnorm : ‖ψ x‖ ≠ 0 ∨ ‖ψ y‖ ≠ 0 := by
        by_cases ha : ψ x = 0
        · exact Or.inr (fun h => hz ⟨ha, norm_eq_zero.mp h⟩)
        · exact Or.inl (fun h => ha (norm_eq_zero.mp h))
      rcases hnorm with hx | hy
      · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg ‖ψ y‖]
      · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg ‖ψ x‖]
    have hh : star (ψ x)*ψ x + star (ψ y)*ψ y = (r : ℂ)^2 := by
      change (starRingEnd ℂ) (ψ x)*ψ x + (starRingEnd ℂ) (ψ y)*ψ y = (r : ℂ)^2
      rw [Complex.conj_mul', Complex.conj_mul']
      have hsq : r^2 = ‖ψ x‖^2 + ‖ψ y‖^2 := Real.sq_sqrt (by positivity)
      exact_mod_cast hsq.symm
    refine ⟨knownGivensBlock (ψ x) (ψ y) r,
      knownGivensBlock_unitary (ψ x) (ψ y) r hr hh, ?_⟩
    rw [twoLevel_pair_mulVec x y _ hxy, if_neg (Ne.symm hxy), if_pos rfl]
    have he := congrFun (knownGivensBlock_eliminate (ψ x) (ψ y) r hr hh) true
    simpa [Matrix.mulVec, dotProduct, add_comm] using! he

/-- A pair instruction leaves every vector coordinate outside its chosen pair unchanged. -/
theorem twoLevel_pair_outside {I : Type} [Fintype I] [DecidableEq I]
    (x y : I) (B : Matrix Bool Bool ℂ) (hxy : x ≠ y) (ψ : QState I)
    (u : I) (hux : u ≠ x) (huy : u ≠ y) :
    (twoLevelMatrix (.pair x y B) *ᵥ ψ) u = ψ u := by
  rw [twoLevel_pair_mulVec x y B hxy, if_neg hux, if_neg huy]

/-- At most one legal two-level instruction per coordinate in `s` eliminates those coordinates
while preserving coordinates outside `s` and the chosen pivot. -/
theorem known_finite_vector_elimination {I : Type} [Fintype I] [DecidableEq I]
    (x : I) (s : Finset I) (hx : x ∉ s) (ψ : QState I) :
    ∃ ts : List (TwoLevelInstruction I), (∀ g ∈ ts, twoLevelLegal g) ∧
      ts.length ≤ s.card ∧
      (∀ y ∈ s, (twoLevelProgram ts *ᵥ ψ) y = 0) ∧
      (∀ y, y ≠ x → y ∉ s → (twoLevelProgram ts *ᵥ ψ) y = ψ y) := by
  induction s using Finset.induction_on generalizing ψ with
  | empty =>
    refine ⟨[], by simp, by simp, by simp, ?_⟩
    intro y _ _
    simp [twoLevelProgram]
  | @insert y s hy ih =>
    simp only [Finset.mem_insert, not_or] at hx
    have hxy : x ≠ y := hx.1
    have hxs : x ∉ s := hx.2
    obtain ⟨B,hB,hzero⟩ := known_two_coordinate_elimination x y hxy ψ
    obtain ⟨ts,hts,hlen,hs,hout⟩ := ih hxs (twoLevelMatrix (.pair x y B) *ᵥ ψ)
    refine ⟨.pair x y B :: ts, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with hg | hg
      · subst g; exact ⟨hxy,hB⟩
      · exact hts g hg
    · simp only [List.length_cons, Finset.card_insert_of_notMem hy]
      omega
    · intro u hu
      rw [twoLevelProgram_cons, ← Matrix.mulVec_mulVec]
      rcases Finset.mem_insert.mp hu with hu | hu
      · subst u
        rw [hout y (Ne.symm hxy) hy]
        exact hzero
      · exact hs u hu
    · intro u hux hu
      have huy : u ≠ y := fun h => hu (h ▸ Finset.mem_insert_self y s)
      have hus : u ∉ s := fun h => hu (Finset.mem_insert_of_mem h)
      rw [twoLevelProgram_cons, ← Matrix.mulVec_mulVec, hout u hux hus,
        twoLevel_pair_outside x y B hxy ψ u hux huy]

/-- Appending zero workspace to a computational basis state gives the basis state of the
appended configuration. -/
theorem knownFrameEmbed_ket (n : ℕ) (x : Reg n) :
    knownFrameEmbed n (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket ((regAppendEquiv n (n+1)).symm (x, fun _ => false)) := by
  unfold knownFrameEmbed
  rw [tensorState_ket_ket]
  funext y
  simp only [relabelState, Function.comp_apply, Equiv.symm_symm, Qatlib.Foundations.PureStateMath.Ket,
    Equiv.apply_eq_iff_eq_symm_apply]

/-- Appending zero workspace to the all-false basis state gives the all-false basis state on the
larger register. -/
theorem knownFrameEmbed_zero_ket (n : ℕ) :
    knownFrameEmbed n (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) = Qatlib.Foundations.PureStateMath.Ket (fun _ => false) := by
  rw [knownFrameEmbed_ket]
  congr 1
  apply (regAppendEquiv n (n+1)).injective
  rw [Equiv.apply_symm_apply]
  rfl

/-- Takes the adjoint qubit block of a pair instruction or conjugates the scalar of a phase
instruction. -/
noncomputable def twoLevelAdjoint {I : Type} : TwoLevelInstruction I → TwoLevelInstruction I
  | .pair x y B => .pair x y Bᴴ
  | .phase x z => .phase x (star z)

/-- The adjoint of a legal two-level instruction is legal and has the conjugate-transpose
matrix. -/
theorem twoLevelAdjoint_spec {I : Type} [Fintype I] [DecidableEq I]
    (g : TwoLevelInstruction I) (hg : twoLevelLegal g) :
    twoLevelLegal (twoLevelAdjoint g) ∧
      twoLevelMatrix (twoLevelAdjoint g) = (twoLevelMatrix g)ᴴ := by
  cases g with
  | pair x y B =>
    exact ⟨⟨hg.1, by simpa only [Matrix.star_eq_conjTranspose] using! Unitary.star_mem hg.2⟩,
      (twoLevel_pair_conjTranspose x y B hg.1).symm⟩
  | phase x z =>
    refine ⟨by simpa [twoLevelAdjoint, twoLevelLegal, mul_comm] using! hg, ?_⟩
    ext u v
    by_cases huv : u = v <;> by_cases hux : u = x <;>
      simp_all [twoLevelAdjoint, twoLevelMatrix, Matrix.conjTranspose_apply, eq_comm]

/-- Reversing a legal two-level program and taking each instruction adjoint gives a legal
program for its conjugate-transpose matrix. -/
theorem twoLevelProgram_adjoint {I : Type} [Fintype I] [DecidableEq I]
    (ts : List (TwoLevelInstruction I)) (hts : ∀ g ∈ ts, twoLevelLegal g) :
    (∀ g ∈ ts.reverse.map twoLevelAdjoint, twoLevelLegal g) ∧
      twoLevelProgram (ts.reverse.map twoLevelAdjoint) = (twoLevelProgram ts)ᴴ := by
  constructor
  · intro g hg
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
    exact (twoLevelAdjoint_spec t (hts t (List.mem_reverse.mp ht))).1
  · induction ts with
    | nil => simp [twoLevelProgram]
    | cons g ts ih =>
      have htail : ∀ t ∈ ts, twoLevelLegal t := fun t ht => hts t (List.mem_cons_of_mem g ht)
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      rw [twoLevelProgram_append, twoLevelProgram_cons, twoLevelProgram_cons,
        ih htail, (twoLevelAdjoint_spec g (hts g List.mem_cons_self)).2]
      simp [twoLevelProgram, Matrix.conjTranspose_mul]

/-- A pair instruction fixes every computational basis state outside its two selected
coordinates. -/
private theorem twoLevel_pair_fixed_ket {I : Type} [Fintype I] [DecidableEq I]
    (x y : I) (B : Matrix Bool Bool ℂ) (hxy : x ≠ y)
    (u : I) (hux : u ≠ x) (huy : u ≠ y) :
    twoLevelMatrix (.pair x y B) *ᵥ Qatlib.Foundations.PureStateMath.Ket u = Qatlib.Foundations.PureStateMath.Ket u := by
  funext v
  rw [twoLevel_pair_mulVec x y B hxy]
  by_cases hvx : v = x <;> by_cases hvy : v = y <;>
    simp_all [Qatlib.Foundations.PureStateMath.Ket, eq_comm]

/-- A finite set of vector coordinates can be eliminated within its cardinality bound while also
fixing every basis state outside that set and the pivot. -/
theorem known_finite_vector_elimination_fixed {I : Type} [Fintype I] [DecidableEq I]
    (x : I) (s : Finset I) (hx : x ∉ s) (ψ : QState I) :
    ∃ ts : List (TwoLevelInstruction I), (∀ g ∈ ts, twoLevelLegal g) ∧
      ts.length ≤ s.card ∧
      (∀ y ∈ s, (twoLevelProgram ts *ᵥ ψ) y = 0) ∧
      (∀ y, y ≠ x → y ∉ s → (twoLevelProgram ts *ᵥ ψ) y = ψ y) ∧
      (∀ y, y ≠ x → y ∉ s → twoLevelProgram ts *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket y) := by
  induction s using Finset.induction_on generalizing ψ with
  | empty =>
    refine ⟨[], by simp, by simp, by simp, ?_, ?_⟩ <;>
      intro y _ _ <;> simp [twoLevelProgram]
  | @insert y s hy ih =>
    simp only [Finset.mem_insert, not_or] at hx
    have hxy : x ≠ y := hx.1
    obtain ⟨B,hB,hzero⟩ := known_two_coordinate_elimination x y hxy ψ
    obtain ⟨ts,hts,hlen,hs,hout,hfixed⟩ := ih hx.2 (twoLevelMatrix (.pair x y B) *ᵥ ψ)
    refine ⟨.pair x y B :: ts, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with hg | hg
      · subst g; exact ⟨hxy,hB⟩
      · exact hts g hg
    · simp only [List.length_cons, Finset.card_insert_of_notMem hy]; omega
    · intro u hu
      rw [twoLevelProgram_cons, ← Matrix.mulVec_mulVec]
      rcases Finset.mem_insert.mp hu with hu | hu
      · subst u; rw [hout y (Ne.symm hxy) hy]; exact hzero
      · exact hs u hu
    · intro u hux hu
      have huy : u ≠ y := fun h => hu (h ▸ Finset.mem_insert_self y s)
      have hus : u ∉ s := fun h => hu (Finset.mem_insert_of_mem h)
      rw [twoLevelProgram_cons, ← Matrix.mulVec_mulVec, hout u hux hus,
        twoLevel_pair_outside x y B hxy ψ u hux huy]
    · intro u hux hu
      have huy : u ≠ y := fun h => hu (h ▸ Finset.mem_insert_self y s)
      have hus : u ∉ s := fun h => hu (Finset.mem_insert_of_mem h)
      rw [twoLevelProgram_cons, ← Matrix.mulVec_mulVec,
        twoLevel_pair_fixed_ket x y B hxy u hux huy, hfixed u hux hus]

/-- Multiplying a matrix by a basis state extracts the corresponding matrix column. -/
private theorem known_mulVec_ket_apply {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (x y : I) : (U *ᵥ Qatlib.Foundations.PureStateMath.Ket x) y = U y x := by
  simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]

/-- If a unitary fixes a basis state, its corresponding row is the identity row. -/
private theorem known_unitary_fixed_row {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ unitaryGroup I ℂ) (x : I)
    (hx : U *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket x) (y : I) : U x y = if x = y then 1 else 0 := by
  have h := congrArg (fun v => Uᴴ *ᵥ v) hx
  (try dsimp only at h)
  rw [Matrix.mulVec_mulVec, show Uᴴ * U = 1 from hU.1, Matrix.one_mulVec] at h
  have hh := congrFun h y
  rw [known_mulVec_ket_apply, Matrix.conjTranspose_apply] at hh
  have hs := congrArg star hh
  simpa [Qatlib.Foundations.PureStateMath.Ket, eq_comm] using! hs.symm

/-- A phase instruction fixes every computational basis state at a different coordinate. -/
private theorem twoLevel_phase_fixed_ket {I : Type} [Fintype I] [DecidableEq I]
    (x y : I) (z : ℂ) (hy : y ≠ x) :
    twoLevelMatrix (.phase x z) *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket y := by
  funext u
  rw [twoLevel_phase_mulVec]
  by_cases hu : u = x <;> simp_all [Qatlib.Foundations.PureStateMath.Ket, eq_comm]

/-- A unitary fixing all basis states outside `s` has a legal two-level factorization of length
at most `s.card * (s.card + 1) / 2`. -/
private theorem known_factorization_supported {I : Type} [Fintype I] [DecidableEq I]
    (s : Finset I) (U : Matrix I I ℂ) (hU : U ∈ unitaryGroup I ℂ)
    (hfix : ∀ y, y ∉ s → U *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket y) :
    ∃ ts : List (TwoLevelInstruction I), (∀ g ∈ ts, twoLevelLegal g) ∧
      ts.length ≤ s.card * (s.card+1)/2 ∧ twoLevelProgram ts = U := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty =>
    refine ⟨[], by simp, by simp, ?_⟩
    have he : U = 1 := by
      ext x y
      have h := congrFun (hfix y (by simp)) x
      simpa [known_mulVec_ket_apply, Qatlib.Foundations.PureStateMath.Ket,
          Matrix.one_apply] using! h
    simp [twoLevelProgram, he]
  | @insert x s hx ih =>
    obtain ⟨es,hes,hlen,hzero,hout,hfixed⟩ :=
      known_finite_vector_elimination_fixed x s hx (U *ᵥ Qatlib.Foundations.PureStateMath.Ket x)
    let E := twoLevelProgram es
    let W := E * U
    have hE : E ∈ unitaryGroup I ℂ := twoLevelProgram_unitary es hes
    have hW : W ∈ unitaryGroup I ℂ := (unitaryGroup I ℂ).mul_mem hE hU
    have hwfix : ∀ y, y ∉ insert x s → W *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket y := by
      intro y hy
      have hys : y ∉ s := fun h => hy (Finset.mem_insert_of_mem h)
      have hyx : y ≠ x := fun h => hy (h ▸ Finset.mem_insert_self x s)
      rw [show W = E*U from rfl, ← Matrix.mulVec_mulVec, hfix y hy]
      exact hfixed y hyx hys
    have hwcol : ∀ y, y ≠ x → W y x = 0 := by
      intro y hyx
      by_cases hy : y ∈ s
      · have h := hzero y hy
        simpa [E, W, Matrix.mulVec_mulVec, known_mulVec_ket_apply] using! h
      · have hy' : y ∉ insert x s := by simp [hyx, hy]
        simpa [hyx] using! known_unitary_fixed_row W hW y (hwfix y hy') x
    let z : ℂ := W x x
    have hz : star z*z = 1 := by
      have hh := congrArg (fun M : Matrix I I ℂ => M x x) hW.1
      simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.one_apply, if_true] at hh
      rw [Finset.sum_eq_single x] at hh
      · exact hh
      · intro y _ hy; simp [hwcol y hy]
      · simp
    let P := twoLevelMatrix (TwoLevelInstruction.phase x (star z))
    have hP : P ∈ unitaryGroup I ℂ := twoLevel_phase_unitary x (star z)
      (by simpa [mul_comm] using! hz)
    let V := P * W
    have hV : V ∈ unitaryGroup I ℂ := (unitaryGroup I ℂ).mul_mem hP hW
    have hvfix : ∀ y, y ∉ s → V *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket y := by
      intro y hy
      rw [show V = P * W from rfl, ← Matrix.mulVec_mulVec]
      by_cases hyx : y = x
      · subst y
        funext u
        rw [show P = twoLevelMatrix (.phase x (star z)) from rfl,
          twoLevel_phase_mulVec, known_mulVec_ket_apply]
        by_cases hux : u = x
        · subst u; simpa [Qatlib.Foundations.PureStateMath.Ket, z] using! hz
        · simp [hux, hwcol u hux, Qatlib.Foundations.PureStateMath.Ket]
      · have hy' : y ∉ insert x s := by simp [hy, hyx]
        rw [hwfix y hy']
        exact twoLevel_phase_fixed_ket x y (star z) hyx
    obtain ⟨ts,hts,htlen,ht⟩ := ih V hV hvfix
    obtain ⟨hes',heq⟩ := twoLevelProgram_adjoint es hes
    refine ⟨ts ++ [.phase x z] ++ es.reverse.map twoLevelAdjoint, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · rcases List.mem_append.mp hg with hg | hg
        · exact hts g hg
        · have h := List.mem_singleton.mp hg; subst g; exact hz
      · exact hes' g hg
    · simp only [List.length_append, List.length_map, List.length_reverse,
        List.length_singleton, Finset.card_insert_of_notMem hx]
      have htri : (s.card+1)*(s.card+1+1)/2 = s.card*(s.card+1)/2 + (s.card+1) := by
        have heq : (s.card+1)*(s.card+1+1) = s.card*(s.card+1) + 2*(s.card+1) := by ring
        rw [heq, Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
      rw [htri]; omega
    · rw [twoLevelProgram_append, twoLevelProgram_append, heq, ht,
        twoLevelProgram_cons]
      simp only [twoLevelProgram, List.foldl_nil, one_mul]
      have hphase : twoLevelMatrix (TwoLevelInstruction.phase x z) = Pᴴ := by
        have hh := (twoLevelAdjoint_spec (.phase x (star z))
          (by simpa [twoLevelLegal, mul_comm] using! hz)).2
        simpa [twoLevelAdjoint, P] using! hh
      rw [hphase]
      change Eᴴ * (Pᴴ * (P * (E * U))) = U
      rw [← mul_assoc Pᴴ P, show Pᴴ * P = 1 from hP.1, one_mul,
        ← mul_assoc, show Eᴴ * E = 1 from hE.1, one_mul]

/-- Every finite-dimensional unitary has an exact legal two-level factorization with at most `d
* (d + 1) / 2` instructions. This is the matrix factorization underlying local synthesis in
[BarencoEtAl1995]. -/
theorem known_unitary_two_level_factorization
    (I : Type) [Fintype I] [DecidableEq I] (U : Matrix I I ℂ)
    (hU : U ∈ unitaryGroup I ℂ) :
    ∃ ts : List (TwoLevelInstruction I), (∀ g ∈ ts, twoLevelLegal g) ∧
      ts.length ≤ Fintype.card I * (Fintype.card I+1)/2 ∧ twoLevelProgram ts = U := by
  simpa using! known_factorization_supported Finset.univ U hU (by simp)

/-- Extends a Boolean register along an injective wire map and assigns false to every unused
wire. -/
noncomputable def knownWireExtend {a b : ℕ} (e : Fin a ↪ Fin b) (x : Reg a) : Reg b :=
  Function.extend e x (fun _ => false)

/-- The extended register agrees with the original register on every mapped wire. -/
@[simp] theorem knownWireExtend_at {a b : ℕ} (e : Fin a ↪ Fin b) (x : Reg a) (i : Fin a) :
    knownWireExtend e x (e i) = x i := e.injective.extend_apply _ _ _

/-- Updating a mapped wire of an extended register equals extending the corresponding update of
the original register. -/
theorem knownWireExtend_update {a b : ℕ} (e : Fin a ↪ Fin b) (x : Reg a)
    (t : Fin a) (v : Bool) :
    Function.update (knownWireExtend e x) (e t) v = knownWireExtend e (Function.update x t v) := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i,rfl⟩ := hj
    by_cases hi : i = t
    · subst i; simp
    · rw [Function.update_of_ne (fun h => hi (e.injective h)),
        knownWireExtend_at, knownWireExtend_at, Function.update_of_ne hi]
  · have hne : j ≠ e t := fun h => hj ⟨t,h.symm⟩
    rw [Function.update_of_ne hne]
    simp only [knownWireExtend, Function.extend_apply' _ _ j hj]

/-- Linearly embeds a state along an injective wire map, fixing every unused wire to false. -/
noncomputable def knownWireEmbed {a b : ℕ} (e : Fin a ↪ Fin b) (ψ : QState (Reg a)) :
    QState (Reg b) := ∑ x, ψ x • Qatlib.Foundations.PureStateMath.Ket (knownWireExtend e x)

/-- Embedding a computational basis state gives the basis state of the extended register. -/
theorem knownWireEmbed_ket {a b : ℕ} (e : Fin a ↪ Fin b) (x : Reg a) :
    knownWireEmbed e (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (knownWireExtend e x) := by
  simp [knownWireEmbed, Qatlib.Foundations.PureStateMath.Ket]

/-- Embedding along an injective wire map commutes with complex scalar multiplication. -/
theorem knownWireEmbed_smul {a b : ℕ} (e : Fin a ↪ Fin b) (z : ℂ) (ψ : QState (Reg a)) :
    knownWireEmbed e (z • ψ) = z • knownWireEmbed e ψ := by
  simp [knownWireEmbed, Finset.smul_sum, smul_smul]

/-- Embedding along an injective wire map commutes with finite sums of states. -/
theorem knownWireEmbed_sum {a b : ℕ} {J : Type} [Fintype J] (e : Fin a ↪ Fin b)
    (ψ : J → QState (Reg a)) : knownWireEmbed e (∑ j, ψ j) = ∑ j, knownWireEmbed e (ψ j) := by
  simp only [knownWireEmbed, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- Relabels the wires of a single-qubit gate or CNOT along an injective wire map. -/
noncomputable def knownWireGateMap {a b : ℕ} (e : Fin a ↪ Fin b) :
    ReflectionGate a → ReflectionGate b
  | .inl (t,U) => .inl (e t,U)
  | .inr (c,t) => .inr (e c,e t)

/-- Injective wire relabeling preserves legality of a local gate. -/
theorem knownWireGateMap_legal {a b : ℕ} (e : Fin a ↪ Fin b) (g : ReflectionGate a)
    (hg : reflectionGateLegal g) : reflectionGateLegal (knownWireGateMap e g) := by
  rcases g with ⟨t,U⟩ | ⟨c,t⟩
  · exact hg
  · exact fun h => hg (e.injective h)

/-- A relabeled legal gate acts on an extended basis configuration as the embedding of the
original gate action. -/
theorem knownWireGateMap_ket {a b : ℕ} (e : Fin a ↪ Fin b) (g : ReflectionGate a)
    (hg : reflectionGateLegal g) (x : Reg a) :
    ApplyGate (reflectionGateMatrix (knownWireGateMap e g)) (Qatlib.Foundations.PureStateMath.Ket (knownWireExtend e x)) =
      knownWireEmbed e (ApplyGate (reflectionGateMatrix g) (Qatlib.Foundations.PureStateMath.Ket x)) := by
  rcases g with ⟨t,U⟩ | ⟨c,t⟩
  · simp only [knownWireGateMap, reflectionGateMatrix, applyGate_wireGate_ket,
      knownWireExtend_at, knownWireExtend_update]
    rw [show knownWireEmbed e
      (U false (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t false) +
        U true (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t true)) =
      knownWireEmbed e (U false (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t false)) +
        knownWireEmbed e (U true (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t true)) from by
          simp [knownWireEmbed, add_smul, Finset.sum_add_distrib]]
    simp only [knownWireEmbed_smul, knownWireEmbed_ket]
  · simp only [knownWireGateMap, reflectionGateMatrix]
    rw [applyGate_cnotGate_ket b (e c) (e t) (fun h => hg (e.injective h)),
      applyGate_cnotGate_ket a c t hg, knownWireEmbed_ket,
      knownWireExtend_at, knownWireExtend_update]
    simp only [knownWireExtend_at]

/-- A relabeled legal gate commutes with embedding a state along its injective wire map. -/
theorem knownWireGateMap_embed {a b : ℕ} (e : Fin a ↪ Fin b) (g : ReflectionGate a)
    (hg : reflectionGateLegal g) (ψ : QState (Reg a)) :
    ApplyGate (reflectionGateMatrix (knownWireGateMap e g)) (knownWireEmbed e ψ) =
      knownWireEmbed e (ApplyGate (reflectionGateMatrix g) ψ) := by
  conv_rhs => arg 2; arg 2; rw [state_ket_expansion ψ]
  simp only [ApplyGate, Matrix.mulVec_sum, Matrix.mulVec_smul, knownWireEmbed_sum,
    knownWireEmbed_smul]
  change (reflectionGateMatrix (knownWireGateMap e g)) *ᵥ
    (∑ x, ψ x • Qatlib.Foundations.PureStateMath.Ket (knownWireExtend e x)) = _
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro x _
  rw [show reflectionGateMatrix (knownWireGateMap e g) *ᵥ Qatlib.Foundations.PureStateMath.Ket (knownWireExtend e x) =
    knownWireEmbed e (reflectionGateMatrix g *ᵥ Qatlib.Foundations.PureStateMath.Ket x) from knownWireGateMap_ket e g hg x]

/-- Relabeling every gate of a legal program preserves execution on embedded states. -/
theorem knownWireProgram_embed {a b : ℕ} (e : Fin a ↪ Fin b) (gs : List (ReflectionGate a))
    (hgs : reflectionLegal gs) (ψ : QState (Reg a)) :
    Run 1 (reflectionCompile (gs.map (knownWireGateMap e))) (knownWireEmbed e ψ) =
      knownWireEmbed e (Run 1 (reflectionCompile gs) ψ) := by
  induction gs generalizing ψ with
  | nil => simp [reflectionCompile]
  | cons g gs ih =>
    simp only [List.map_cons, reflectionCompile, List.map_cons, run_gate]
    rw [knownWireGateMap_embed e g (hgs g List.mem_cons_self)]
    exact ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg)) _

/-- The embedding of the first `a` wire indices into a register of width `a + b`. -/
noncomputable def knownPrefixWires (a b : ℕ) : Fin a ↪ Fin (a+b) :=
  ⟨Fin.castAdd b, Fin.castAdd_injective a b⟩

/-- Extending along the prefix wire embedding appends an all-false register. -/
theorem knownWireExtend_prefix (a b : ℕ) (x : Reg a) :
    knownWireExtend (knownPrefixWires a b) x = (regAppendEquiv a b).symm (x,fun _ => false) := by
  funext i
  by_cases hi : i.val < a
  · let j : Fin a := ⟨i.val,hi⟩
    have he : i = (knownPrefixWires a b) j := Fin.ext rfl
    rw [he, knownWireExtend_at]
    exact (congrArg (fun p => p.1 j) ((regAppendEquiv a b).apply_symm_apply (x,fun _=>false))).symm
  · let j : Fin b := ⟨i.val-a,by omega⟩
    have he : i = Fin.natAdd a j := Fin.ext (by dsimp [j]; omega)
    have hn : ¬∃ k, (knownPrefixWires a b) k = i := by
      rintro ⟨k,hk⟩
      have hh := congrArg Fin.val hk
      change k.val = i.val at hh
      omega
    rw [knownWireExtend, Function.extend_apply' _ _ i hn, he]
    exact (congrArg (fun p => p.2 j) ((regAppendEquiv a b).apply_symm_apply (x,fun _=>false))).symm

/-- The state embedding along the prefix of width `n` agrees with `knownFrameEmbed n`. -/
theorem knownWireEmbed_frame (n : ℕ) (ψ : QState (Reg n)) :
    knownWireEmbed (knownPrefixWires n (n+1)) ψ = knownFrameEmbed n ψ := by
  conv_rhs => arg 2; rw [state_ket_expansion ψ]
  have hsum {J : Type} [Fintype J] (φ : J → QState (Reg n)) :
      knownFrameEmbed n (∑ j,φ j) = ∑ j,knownFrameEmbed n (φ j) := by
    funext x
    simp [knownFrameEmbed, relabelState, TensorState, Finset.sum_mul]
  rw [hsum]
  simp only [knownFrameEmbed_smul, knownFrameEmbed_ket, knownWireEmbed,
    knownWireExtend_prefix]

/-- Relabeling every gate of a legal program along an injective wire map preserves program
legality. -/
theorem knownWireMapList_legal {a b : ℕ} (e : Fin a ↪ Fin b)
    (gs : List (ReflectionGate a)) (hgs : reflectionLegal gs) :
    reflectionLegal (gs.map (knownWireGateMap e)) := by
  intro g hg
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
  exact knownWireGateMap_legal e t (hgs t ht)

/-- Lifting a legal program to the data prefix implements its program matrix on states with
appended zero workspace. -/
theorem knownFrame_lift_program (n : ℕ) (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) (ψ : QState (Reg n)) :
    Run 1 (reflectionCompile (gs.map (knownWireGateMap (knownPrefixWires n (n+1)))))
      (knownFrameEmbed n ψ) = knownFrameEmbed n (reflectionProgramMatrix gs *ᵥ ψ) := by
  rw [← knownWireEmbed_frame, knownWireProgram_embed _ gs hgs, knownWireEmbed_frame,
    run_reflectionCompile]
  rfl

/-- The amplitude of a matrix applied to a basis state is the corresponding matrix entry. -/
private theorem local_ket_mul {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (x y : I) : (A *ᵥ Qatlib.Foundations.PureStateMath.Ket x) y = A y x := by
  simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]

/-- The action of a pair instruction is the original state plus explicit corrections at its two
selected basis coordinates. -/
theorem known_two_level_pair_update {I : Type} [Fintype I] [DecidableEq I]
    (x y : I) (B : Matrix Bool Bool ℂ) (hxy : x ≠ y) (ψ : QState I) :
    twoLevelMatrix (.pair x y B) *ᵥ ψ = ψ +
      ((B false false - 1)*ψ x + B false true*ψ y) • Qatlib.Foundations.PureStateMath.Ket x +
      (B true false*ψ x + (B true true - 1)*ψ y) • Qatlib.Foundations.PureStateMath.Ket y := by
  funext u
  rw [twoLevel_pair_mulVec x y B hxy]
  by_cases hux : u = x <;> by_cases huy : u = y <;>
    simp_all [Qatlib.Foundations.PureStateMath.Ket, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- If a unitary sends basis state `x` to basis state `p`, its adjoint sends `p` back to `x`,
and every transformed vector has amplitude `ψ x` at `p`. -/
theorem known_unitary_mapped_ket {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ unitaryGroup I ℂ) (x p : I)
    (hx : A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket p) :
    Aᴴ *ᵥ Qatlib.Foundations.PureStateMath.Ket p = Qatlib.Foundations.PureStateMath.Ket x ∧ ∀ ψ : QState I, (A *ᵥ ψ) p = ψ x := by
  have hi : Aᴴ *ᵥ Qatlib.Foundations.PureStateMath.Ket p = Qatlib.Foundations.PureStateMath.Ket x := by
    rw [← hx, Matrix.mulVec_mulVec, show Aᴴ*A=1 from hA.1, Matrix.one_mulVec]
  refine ⟨hi, ?_⟩
  have hrow : ∀ u, A p u = if u = x then 1 else 0 := by
    intro u
    have h := congrFun hi u
    rw [local_ket_mul, Matrix.conjTranspose_apply] at h
    have hh := congrArg star h
    simpa [Qatlib.Foundations.PureStateMath.Ket] using! hh
  intro ψ
  simp [Matrix.mulVec, dotProduct, hrow]

/-- Conjugating a pair instruction by a unitary that sends its source basis states to the
selected target pair transports the instruction back to the source pair. -/
theorem known_two_level_unitary_conjugate {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ unitaryGroup I ℂ)
    (x y p q : I) (hxy : x ≠ y) (hpq : p ≠ q)
    (hx : A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket p) (hy : A *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket q)
    (B : Matrix Bool Bool ℂ) (ψ : QState I) :
    Aᴴ *ᵥ (twoLevelMatrix (.pair p q B) *ᵥ (A *ᵥ ψ)) =
      twoLevelMatrix (.pair x y B) *ᵥ ψ := by
  obtain ⟨hix,hcx⟩ := known_unitary_mapped_ket A hA x p hx
  obtain ⟨hiy,hcy⟩ := known_unitary_mapped_ket A hA y q hy
  rw [known_two_level_pair_update p q B hpq, known_two_level_pair_update x y B hxy,
    Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    hix, hiy, hcx, hcy, Matrix.mulVec_mulVec, show Aᴴ*A=1 from hA.1, Matrix.one_mulVec]

/-- A Pauli X gate on one wire flips that bit of a computational basis state. -/
private theorem known_X_ket (n : ℕ) (w : Fin n) (x : Reg n) :
    ApplyGate (wireGate n w PauliX) (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x w (!(x w))) := by
  rw [applyGate_wireGate_ket]
  cases hx : x w <;> simp [PauliX, permMatrix]

/-- The list of Pauli X instructions on the supplied wire indices. -/
noncomputable def knownFlipSteps {n : ℕ} (is : List (Fin n)) : List (ReflectionGate n) :=
  is.map (fun i => .inl (i,PauliX))

/-- A list of single-wire Pauli X instructions is legal. -/
theorem knownFlipSteps_legal {n : ℕ} (is : List (Fin n)) : reflectionLegal (knownFlipSteps is) := by
  intro g hg
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
  exact pauliX_unitary

/-- For a list without duplicate wires, executing its Pauli X instructions flips exactly the
listed bits of a basis configuration. -/
theorem knownFlipSteps_action {n : ℕ} (is : List (Fin n)) (hi : is.Nodup) (x : Reg n) :
    Run 1 (reflectionCompile (knownFlipSteps is)) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (fun k => if k ∈ is then !(x k) else x k) := by
  induction is generalizing x with
  | nil => simp [knownFlipSteps, reflectionCompile]
  | cons i is ih =>
    simp only [knownFlipSteps, List.map_cons, reflectionCompile, List.map_cons, run_gate,
      reflectionGateMatrix]
    rw [known_X_ket]
    change Run 1 (reflectionCompile (knownFlipSteps is))
      (Qatlib.Foundations.PureStateMath.Ket (Function.update x i (!(x i)))) = _
    rw [ih hi.tail]
    congr 1
    funext k
    by_cases hki : k = i
    · subst k
      simp [(List.nodup_cons.mp hi).1]
    · simp [hki]

/-- The list of CNOT instructions from a fixed control wire to the supplied target wires. -/
noncomputable def knownFanoutSteps {n : ℕ} (t : Fin n) (is : List (Fin n)) :
    List (ReflectionGate n) := is.map (fun i => .inr (t,i))

/-- A CNOT fanout list is legal when its control wire is absent from the target list. -/
theorem knownFanoutSteps_legal {n : ℕ} (t : Fin n) (is : List (Fin n))
    (ht : t ∉ is) : reflectionLegal (knownFanoutSteps t is) := by
  intro g hg
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hg
  exact fun h => ht (h ▸ hi)

/-- For distinct targets excluding the control, the fanout list XORs the control bit into
exactly those target bits. -/
theorem knownFanoutSteps_action {n : ℕ} (t : Fin n) (is : List (Fin n))
    (hi : is.Nodup) (ht : t ∉ is) (x : Reg n) :
    Run 1 (reflectionCompile (knownFanoutSteps t is)) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (fun k => if k ∈ is then x k ^^ x t else x k) := by
  induction is generalizing x with
  | nil => simp [knownFanoutSteps, reflectionCompile]
  | cons i is ih =>
    have hti : t ≠ i := fun h => ht (List.mem_cons.mpr (Or.inl h))
    have hts : t ∉ is := fun h => ht (List.mem_cons_of_mem i h)
    simp only [knownFanoutSteps, List.map_cons, reflectionCompile, List.map_cons, run_gate,
      reflectionGateMatrix]
    rw [applyGate_cnotGate_ket n t i hti]
    change Run 1 (reflectionCompile (knownFanoutSteps t is))
      (Qatlib.Foundations.PureStateMath.Ket (Function.update x i (x i ^^ x t))) = _
    rw [ih hi.tail hts]
    congr 1
    funext k
    by_cases hki : k = i
    · subst k; simp [(List.nodup_cons.mp hi).1]
    · simp [hki, Function.update_of_ne hti]

/-- The empty program for equal wires, or the three-CNOT program swapping two different wires. -/
noncomputable def knownSwapSteps {n : ℕ} (t w : Fin n) : List (ReflectionGate n) :=
  if t = w then [] else [.inr (t,w),.inr (w,t),.inr (t,w)]

/-- The wire-swap program is legal, uses at most three gates, and exchanges the chosen bits of
every basis state. -/
theorem knownSwapSteps_spec {n : ℕ} (t w : Fin n) :
    reflectionLegal (knownSwapSteps t w) ∧ (knownSwapSteps t w).length ≤ 3 ∧
      ∀ x : Reg n, Run 1 (reflectionCompile (knownSwapSteps t w)) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (x ∘ Equiv.swap t w) := by
  by_cases htw : t = w
  · subst w; simp [knownSwapSteps, reflectionLegal, reflectionCompile]
  · refine ⟨?_, by simp [knownSwapSteps, htw], ?_⟩
    · intro g hg
      simp only [knownSwapSteps, if_neg htw, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      exact htw
      exact Ne.symm htw
      exact htw
    · intro x
      simp only [knownSwapSteps, if_neg htw, reflectionCompile, List.map_cons, List.map_nil,
        run_gate, run_nil, reflectionGateMatrix]
      rw [applyGate_cnotGate_ket n t w htw,
        applyGate_cnotGate_ket n w t (Ne.symm htw), applyGate_cnotGate_ket n t w htw]
      congr 1
      funext k
      by_cases hkt : k = t
      · subst k
        simp only [Function.comp_apply, Equiv.swap_apply_left,
          Function.update_of_ne htw, Function.update_self]
        cases x t <;> cases x w <;> rfl
      · by_cases hkw : k = w
        · subst k
          simp [Function.comp_apply, Function.update_of_ne (Ne.symm htw),
            Function.update_of_ne htw, Bool.xor_left_comm]
        · simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hkt hkw, hkt, hkw]

/-- The equivalence appending a Boolean target bit after a `k`-bit control register. -/
def knownDataEquiv (k : ℕ) : (Reg k × Bool) ≃ Reg (k+1) where
  toFun p := Fin.lastCases p.2 p.1
  invFun x := (fun i => x i.castSucc, x (Fin.last k))
  left_inv p := by ext i <;> simp
  right_inv x := by funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- Appending a target bit preserves every control-register coordinate. -/
@[simp] theorem knownDataEquiv_control (k : ℕ) (x : Reg k) (b : Bool) (i : Fin k) :
    knownDataEquiv k (x,b) i.castSucc = x i := by
  change Fin.lastCases b x i.castSucc = x i
  simp

/-- The last coordinate of the appended register is the supplied target bit. -/
@[simp] theorem knownDataEquiv_target (k : ℕ) (x : Reg k) (b : Bool) :
    knownDataEquiv k (x,b) (Fin.last k) = b := by
  change Fin.lastCases b x (Fin.last k) = b
  simp

/-- The embedding of the first `a` wires into a register of width `b`, given `a ≤ b`. -/
noncomputable def knownInitialWires (a b : ℕ) (h : a ≤ b) : Fin a ↪ Fin b :=
  ⟨fun i => ⟨i.val,lt_of_lt_of_le i.isLt h⟩, fun _ _ hij => Fin.ext (congrArg (fun r : Fin b => r.val) hij)⟩

/-- Extending the multicontrol basis layout into the larger workspace agrees with appending zero
workspace to its data-and-target register. -/
theorem knownMultiEmbed_basis (k : ℕ) (x : Reg k) (b : Bool) :
    knownWireExtend (knownInitialWires (k+1+(k-1)) ((k+1)+(k+2)) (by omega))
      ((multiKnownSplit k).symm ((x,b),fun _ => false)) =
    (regAppendEquiv (k+1) (k+2)).symm (knownDataEquiv k (x,b),fun _=>false) := by
  let e := knownInitialWires (k+1+(k-1)) ((k+1)+(k+2)) (by omega)
  let q := (multiKnownSplit k).symm ((x,b),fun _=>false)
  apply (regAppendEquiv (k+1) (k+2)).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [knownDataEquiv_target]
      change knownWireExtend e q ⟨k,by omega⟩ = b
      have he : (⟨k,by omega⟩ : Fin ((k+1)+(k+2))) = e (multiKnownTargetWire k) := rfl
      rw [he, knownWireExtend_at]
      dsimp only [q]
      rw [multiKnownJoin_target]
    · simp only [knownDataEquiv_control]
      change knownWireExtend e q ⟨j.val,by omega⟩ = x j
      have he : (⟨j.val,by omega⟩ : Fin ((k+1)+(k+2))) = e (multiKnownControlWire k j) := rfl
      rw [he, knownWireExtend_at]
      dsimp only [q]
      rw [multiKnownJoin_control]
  · funext i
    change knownWireExtend e q ⟨k+1+i.val,by omega⟩ = false
    by_cases hi : i.val < k-1
    · let j : Fin (k-1) := ⟨i.val,hi⟩
      have he : (⟨k+1+i.val,by omega⟩ : Fin ((k+1)+(k+2))) = e (multiKnownWorkWire k j) := rfl
      rw [he, knownWireExtend_at]
      dsimp only [q]
      rw [multiKnownJoin_work]
    · have hn : ¬∃ j, e j = (⟨k+1+i.val,by omega⟩ : Fin ((k+1)+(k+2))) := by
        rintro ⟨j,hj⟩
        have h := congrArg Fin.val hj
        change j.val = k+1+i.val at h
        omega
      exact Function.extend_apply' _ _ _ hn

/-- Appending zero workspace commutes with finite sums of states. -/
theorem knownFrameEmbed_sum {n : ℕ} {J : Type} [Fintype J] (φ : J → QState (Reg n)) :
    knownFrameEmbed n (∑ j,φ j) = ∑ j,knownFrameEmbed n (φ j) := by
  funext x
  simp [knownFrameEmbed, relabelState, TensorState, Finset.sum_mul]

/-- Embedding the multicontrol workspace layout into the larger register agrees with
`knownFrameEmbed` after relabeling the data and target. -/
theorem knownMultiEmbed_frame (k : ℕ) (φ : QState (Reg k × Bool)) :
    knownWireEmbed (knownInitialWires (k+1+(k-1)) ((k+1)+(k+2)) (by omega))
      (multiKnownEmbed k φ) = knownFrameEmbed (k+1) (relabelState (knownDataEquiv k) φ) := by
  conv_lhs => arg 2; arg 2; rw [state_ket_expansion φ]
  rw [multiKnownEmbed_sum, knownWireEmbed_sum]
  simp only [multiKnownEmbed_smul, multiKnownEmbed_ket, knownWireEmbed_smul, knownWireEmbed_ket]
  conv_rhs => arg 2; arg 2; rw [state_ket_expansion φ]
  have hsum : relabelState (knownDataEquiv k) (∑ x,φ x • Qatlib.Foundations.PureStateMath.Ket x) =
      ∑ x,φ x • Qatlib.Foundations.PureStateMath.Ket (knownDataEquiv k x) := by
    funext y
    simp only [relabelState, Function.comp_apply, Finset.sum_apply, Pi.smul_apply,
        Qatlib.Foundations.PureStateMath.Ket, smul_eq_mul]
    simp [Equiv.symm_apply_eq]
  rw [hsum, knownFrameEmbed_sum]
  simp only [knownFrameEmbed_smul, knownFrameEmbed_ket]
  apply Finset.sum_congr rfl
  intro ⟨x,b⟩ _
  rw [knownMultiEmbed_basis]

/-- A known qubit unitary controlled on `k` bits has a legal implementation of exactly
`multiKnownCost k` gates on the enlarged register, returning the workspace to zero. -/
theorem knownCanonicalControl_synthesis (k : ℕ) (B : Matrix Bool Bool ℂ)
    (hB : B ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate ((k+1)+(k+2))), reflectionLegal gs ∧
      gs.length = multiKnownCost k ∧
      ∀ φ : QState (Reg k × Bool),
      Run 1 (reflectionCompile gs)
        (knownFrameEmbed (k+1) (relabelState (knownDataEquiv k) φ)) =
      knownFrameEmbed (k+1) (relabelState (knownDataEquiv k) (multiKnownGate k B *ᵥ φ)) := by
  let e := knownInitialWires (k+1+(k-1)) ((k+1)+(k+2)) (by omega)
  let p := knownQubitAnglesOfUnitary B
  have hp : knownQubitUnitary p = B := (knownQubitEuler_explicit_angles_cover_unitaries B hB).1
  refine ⟨(multiKnownSteps k p).map (knownWireGateMap e),
    knownWireMapList_legal e _ (multiKnownSteps_legal k p), ?_, ?_⟩
  · rw [List.length_map, multiKnownSteps_length]
  · intro φ
    rw [← knownMultiEmbed_frame, knownWireProgram_embed e _ (multiKnownSteps_legal k p),
      (multi_known_control_actual_local_table_and_cost k p).2.2.2.2, hp, knownMultiEmbed_frame]

/-- The Pauli X program flipping exactly the coordinates where configurations `x` and `a`
differ. -/
noncomputable def knownAddressFlips {n : ℕ} (x a : Reg n) : List (ReflectionGate n) :=
  knownFlipSteps ((Finset.univ.filter (fun i => x i ≠ a i)).toList)

/-- The address-flip program is legal, has at most `n` gates, and sends basis state `x` to basis
state `a`. -/
theorem knownAddressFlips_spec {n : ℕ} (x a : Reg n) :
    reflectionLegal (knownAddressFlips x a) ∧ (knownAddressFlips x a).length ≤ n ∧
    Run 1 (reflectionCompile (knownAddressFlips x a)) (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket a := by
  refine ⟨knownFlipSteps_legal _, ?_, ?_⟩
  · simp only [knownAddressFlips, knownFlipSteps, List.length_map, Finset.length_toList]
    calc
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n := by simp
  · rw [knownAddressFlips, knownFlipSteps_action _ (Finset.nodup_toList _)]
    congr 1
    funext i
    simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
    cases x i <;> cases a i <;> simp

/-- The canonical address with every control bit true and last target bit equal to `b`. -/
def knownControlAddress (k : ℕ) (b : Bool) : Reg (k+1) :=
  fun i => if i = Fin.last k then b else true

/-- Two addresses differing at a selected wire can be mapped to the canonical false and true
target addresses by a legal program of at most `2 * (k + 1) + 3` gates. -/
theorem knownPairAddress_program (k : ℕ) (x y : Reg (k+1))
    (t : Fin (k+1)) (ht : x t ≠ y t) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧ gs.length ≤ 2*(k+1)+3 ∧
      Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (knownControlAddress k false) ∧
      Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket y) = Qatlib.Foundations.PureStateMath.Ket (knownControlAddress k true) := by
  let w := Fin.last k
  let x' : Reg (k+1) := x ∘ Equiv.swap t w
  let y' : Reg (k+1) := y ∘ Equiv.swap t w
  let a := knownControlAddress k false
  let r := Finset.univ.filter (fun i => x' i ≠ a i)
  let d := Finset.univ.filter (fun i => i ≠ w ∧ x' i ≠ y' i)
  let fs := knownFlipSteps r.toList
  let cs := knownFanoutSteps w d.toList
  have hcs : w ∉ d.toList := by simp [d]
  have hrlen : fs.length ≤ k+1 := by
    simpa only [fs, r, knownAddressFlips] using! (knownAddressFlips_spec x' a).2.1
  have hdlen : cs.length ≤ k+1 := by
    simp only [cs, knownFanoutSteps, List.length_map, Finset.length_toList]
    calc
      _ ≤ (Finset.univ : Finset (Fin (k+1))).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = k+1 := by simp
  have hax : Run 1 (reflectionCompile fs) (Qatlib.Foundations.PureStateMath.Ket x') = Qatlib.Foundations.PureStateMath.Ket a :=
    (knownAddressFlips_spec x' a).2.2
  have hat : a w = false := by simp [a, knownControlAddress, w]
  have hdx : Run 1 (reflectionCompile cs) (Qatlib.Foundations.PureStateMath.Ket a) = Qatlib.Foundations.PureStateMath.Ket a := by
    rw [knownFanoutSteps_action w d.toList (Finset.nodup_toList _) hcs]
    congr 1
    funext i
    simp [hat]
  have hdiff : x' w ≠ y' w := by simpa [x',y',w] using! ht
  have hdy : Run 1 (reflectionCompile (fs ++ cs)) (Qatlib.Foundations.PureStateMath.Ket y') =
      Qatlib.Foundations.PureStateMath.Ket (knownControlAddress k true) := by
    rw [reflectionCompile_append, run_append,
      knownFlipSteps_action r.toList (Finset.nodup_toList _),
      knownFanoutSteps_action w d.toList (Finset.nodup_toList _) hcs]
    congr 1
    funext i
    have hb : (if w ∈ r.toList then !(y' w) else y' w) = true := by
      simp only [r, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, hat]
      cases hx : x' w <;> cases hy : y' w <;> simp_all
    rw [hb]
    by_cases hi : i = w
    · subst i
      simpa [knownControlAddress, w, d] using! hb
    · simp only [r, d, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
        knownControlAddress]
      have hai : a i = true := by simp [a, knownControlAddress, hi, w]
      rw [hai]
      cases x' i <;> cases y' i <;> simp [hi]
  obtain ⟨hswap,hslen,hsx⟩ := knownSwapSteps_spec t w
  refine ⟨knownSwapSteps t w ++ fs ++ cs, ?_, ?_, ?_, ?_⟩
  · rw [reflectionLegal_append, reflectionLegal_append]
    exact ⟨⟨hswap, knownFlipSteps_legal _⟩, knownFanoutSteps_legal _ _ hcs⟩
  · simp only [List.length_append]; omega
  · rw [reflectionCompile_append, reflectionCompile_append, run_append, run_append,
      hsx, hax, hdx]
  · rw [show knownSwapSteps t w ++ fs ++ cs = knownSwapSteps t w ++ (fs ++ cs) from
      List.append_assoc _ _ _, reflectionCompile_append, run_append, hsx]
    exact hdy

/-- The canonical control address is the data-target encoding of all-true controls and target
bit `b`. -/
theorem knownControlAddress_data (k : ℕ) (b : Bool) :
    knownControlAddress k b = knownDataEquiv k ((fun _=>true),b) := by
  funext i
  refine Fin.lastCases ?_ (fun j=>?_) i <;>
    simp [knownControlAddress, knownDataEquiv]

/-- The multicontrolled gate applies its qubit block to the target amplitudes when all controls
are true and fixes all other amplitudes. -/
theorem multiKnownGate_mulVec_apply (k : ℕ) (B : Matrix Bool Bool ℂ)
    (φ : QState (Reg k × Bool)) (x : Reg k) (b : Bool) :
    (multiKnownGate k B *ᵥ φ) (x,b) =
      if allControlTrue k x then B b false*φ (x,false) + B b true*φ (x,true) else φ (x,b) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x]
  · cases hx : allControlTrue k x <;> cases b <;>
      simp [multiKnownGate,hx,Matrix.one_apply,add_comm]
  · intro y _ hy; simp [multiKnownGate,Ne.symm hy]
  · simp

/-- Relabeling the multicontrolled gate gives the two-level matrix on the canonical false and
true target addresses. -/
theorem knownCanonicalPair_action (k : ℕ) (B : Matrix Bool Bool ℂ)
    (φ : QState (Reg k × Bool)) :
    relabelState (knownDataEquiv k) (multiKnownGate k B *ᵥ φ) =
      twoLevelMatrix (.pair (knownControlAddress k false) (knownControlAddress k true) B) *ᵥ
        relabelState (knownDataEquiv k) φ := by
  have hpq : knownControlAddress k false ≠ knownControlAddress k true := by
    intro h
    have hh := congrFun h (Fin.last k)
    simp [knownControlAddress] at hh
  funext u
  obtain ⟨⟨x,b⟩,rfl⟩ := (knownDataEquiv k).surjective u
  rw [show relabelState (knownDataEquiv k) (multiKnownGate k B *ᵥ φ)
    (knownDataEquiv k (x,b)) = (multiKnownGate k B *ᵥ φ) (x,b) from by simp [relabelState]]
  rw [multiKnownGate_mulVec_apply, twoLevel_pair_mulVec _ _ B hpq]
  have hall : allControlTrue k x = true ↔ x = fun _=>true := by
    rw [allControlTrue_eq_decide, decide_eq_true_eq]
    exact ⟨fun h=>funext h, fun h=>by simp [h]⟩
  by_cases hx : x = fun _=>true
  · have ha := hall.mpr hx
    subst x
    cases b <;> simp [ha,knownControlAddress_data,relabelState]
  · have hnot : allControlTrue k x = false := Bool.eq_false_iff.mpr (fun h=>hx (hall.mp h))
    simp [hnot,knownControlAddress_data,relabelState,(knownDataEquiv k).injective.eq_iff,
      Prod.mk.injEq,hx]

/-- The two-level gate on the canonical address pair has a legal implementation of exactly
`multiKnownCost k` gates with restored zero workspace. -/
theorem knownCanonicalPair_synthesis (k : ℕ) (B : Matrix Bool Bool ℂ)
    (hB : B ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate ((k+1)+(k+2))), reflectionLegal gs ∧
      gs.length = multiKnownCost k ∧
      ∀ ψ : QState (Reg (k+1)),
      Run 1 (reflectionCompile gs) (knownFrameEmbed (k+1) ψ) =
        knownFrameEmbed (k+1)
          (twoLevelMatrix (.pair (knownControlAddress k false) (knownControlAddress k true) B) *ᵥ ψ) := by
  obtain ⟨gs,hgs,hlen,hrun⟩ := knownCanonicalControl_synthesis k B hB
  refine ⟨gs,hgs,hlen,?_⟩
  intro ψ
  let φ := relabelState (knownDataEquiv k).symm ψ
  have hφ : relabelState (knownDataEquiv k) φ = ψ := by
    funext u; simp [φ,relabelState]
  rw [← hφ, hrun, knownCanonicalPair_action]

/-- The multicontrol layout for data and a false target embeds as the data register followed by
zero workspace. -/
theorem knownPhaseEmbed_basis (n : ℕ) (x : Reg n) :
    knownWireExtend (knownInitialWires (n+1+(n-1)) (n+(n+1)) (by omega))
      ((multiKnownSplit n).symm ((x,false),fun _=>false)) =
      (regAppendEquiv n (n+1)).symm (x,fun _=>false) := by
  let e := knownInitialWires (n+1+(n-1)) (n+(n+1)) (by omega)
  let q := (multiKnownSplit n).symm ((x,false),fun _=>false)
  apply (regAppendEquiv n (n+1)).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · funext i
    change knownWireExtend e q ⟨i.val,by omega⟩ = x i
    have he : (⟨i.val,by omega⟩ : Fin (n+(n+1))) = e (multiKnownControlWire n i) := rfl
    rw [he,knownWireExtend_at]
    exact multiKnownJoin_control n x false (fun _=>false) i
  · funext i
    change knownWireExtend e q ⟨n+i.val,by omega⟩ = false
    by_cases hz : i.val = 0
    · have he : (⟨n+i.val,by omega⟩ : Fin (n+(n+1))) = e (multiKnownTargetWire n) := Fin.ext (by simp [hz,e,knownInitialWires])
      rw [he,knownWireExtend_at]
      exact multiKnownJoin_target n x false (fun _=>false)
    · by_cases hi : i.val-1 < n-1
      · let j : Fin (n-1) := ⟨i.val-1,hi⟩
        have he : (⟨n+i.val,by omega⟩ : Fin (n+(n+1))) = e (multiKnownWorkWire n j) :=
            Fin.ext (by dsimp [e,knownInitialWires,j];omega)
        rw [he,knownWireExtend_at]
        exact multiKnownJoin_work n x false (fun _=>false) j
      · have hn : ¬∃ j, e j = (⟨n+i.val,by omega⟩ : Fin (n+(n+1))) := by
          rintro ⟨j,hj⟩
          have h := congrArg Fin.val hj
          change j.val = n+i.val at h
          omega
        exact Function.extend_apply' _ _ _ hn

/-- A unit-modulus phase on the all-true basis coordinate has a legal implementation of exactly
`multiKnownCost n` gates with restored zero workspace. -/
theorem knownCanonicalPhase_synthesis (n : ℕ) (z : ℂ) (hz : star z*z=1) :
    ∃ gs : List (ReflectionGate (n+(n+1))), reflectionLegal gs ∧
      gs.length = multiKnownCost n ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) (knownFrameEmbed n ψ) =
        knownFrameEmbed n (twoLevelMatrix (.phase (fun _=>true) z) *ᵥ ψ) := by
  let B := Matrix.diagonal (fun b : Bool=>if b then 1 else z)
  have hB : B ∈ unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
    change (starRingEnd ℂ) z*z=1 at hz
    ext a b
    cases a <;> cases b <;> simp [B,Matrix.mul_apply,hz]
  let p := knownQubitAnglesOfUnitary B
  have hp : knownQubitUnitary p = B := (knownQubitEuler_explicit_angles_cover_unitaries B hB).1
  let e := knownInitialWires (n+1+(n-1)) (n+(n+1)) (by omega)
  let gs := (multiKnownSteps n p).map (knownWireGateMap e)
  have hgs : reflectionLegal gs := knownWireMapList_legal e _ (multiKnownSteps_legal n p)
  have hb (x : Reg n) :
      Run 1 (reflectionCompile gs) (knownFrameEmbed n (Qatlib.Foundations.PureStateMath.Ket x)) =
        (if allControlTrue n x then z else 1) • knownFrameEmbed n (Qatlib.Foundations.PureStateMath.Ket x) := by
    rw [knownFrameEmbed_ket, ← knownPhaseEmbed_basis]
    rw [← knownWireEmbed_ket, knownWireProgram_embed e _ (multiKnownSteps_legal n p),
      multiKnown_basis_action, hp, knownWireEmbed_sum]
    simp only [Fintype.sum_bool,knownWireEmbed_smul,knownWireEmbed_ket]
    cases allControlTrue n x <;>
      simp [e,B,knownPhaseEmbed_basis]
  refine ⟨gs,hgs,by simp [gs,multiKnownSteps_length],?_⟩
  intro ψ
  conv_lhs => arg 3; arg 2; rw [state_ket_expansion ψ]
  rw [knownFrameEmbed_sum,run_reflectionCompile_sum]
  conv_rhs => arg 2; arg 2; rw [state_ket_expansion ψ]
  rw [Matrix.mulVec_sum,knownFrameEmbed_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [knownFrameEmbed_smul,run_reflectionCompile_smul,hb,Matrix.mulVec_smul,
    knownFrameEmbed_smul]
  congr 1
  have he : twoLevelMatrix (.phase (fun _=>true) z) *ᵥ Qatlib.Foundations.PureStateMath.Ket x =
      (if allControlTrue n x then z else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
    have hall : allControlTrue n x = true ↔ x = fun _=>true := by
      rw [allControlTrue_eq_decide,decide_eq_true_eq]
      exact ⟨fun h=>funext h,fun h=>by simp [h]⟩
    funext u
    rw [twoLevel_phase_mulVec]
    by_cases hux : u=x
    · subst u
      cases hx :
          allControlTrue n x <;> simp_all
          [Qatlib.Foundations.PureStateMath.Ket,Pi.smul_apply,smul_eq_mul]
    · simp [hux,Qatlib.Foundations.PureStateMath.Ket,Pi.smul_apply,smul_eq_mul]
  rw [he,knownFrameEmbed_smul]

/-- A unitary block on any two distinct `(k + 1)`-qubit basis coordinates has a legal local
implementation using at most `128 * (k + 2)²` gates and restored zero workspace. -/
theorem knownPair_actual_synthesis (k : ℕ) (x y : Reg (k+1))
    (hxy : x ≠ y) (B : Matrix Bool Bool ℂ) (hB : B ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate ((k+1)+(k+2))), reflectionLegal gs ∧
      gs.length ≤ 128*(k+2)^2 ∧
      ∀ ψ : QState (Reg (k+1)), Run 1 (reflectionCompile gs) (knownFrameEmbed (k+1) ψ) =
        knownFrameEmbed (k+1) (twoLevelMatrix (.pair x y B) *ᵥ ψ) := by
  obtain ⟨t,ht⟩ : ∃ t, x t ≠ y t := by
    by_contra h; push Not at h; exact hxy (funext h)
  obtain ⟨as,has,halen,hax,hay⟩ := knownPairAddress_program k x y t ht
  obtain ⟨bs,hbs,hblen,hb⟩ := knownCanonicalPair_synthesis k B hB
  let e := knownPrefixWires (k+1) (k+2)
  let fs := as.map (knownWireGateMap e)
  have hfs : reflectionLegal fs := knownWireMapList_legal e as has
  let ds := reflectionAdjoint as
  have hds : reflectionLegal ds := reflectionAdjoint_legal as has
  let rs := ds.map (knownWireGateMap e)
  have hrs : reflectionLegal rs := knownWireMapList_legal e ds hds
  let A := reflectionProgramMatrix as
  have hA : A ∈ unitaryGroup (Reg (k+1)) ℂ := reflectionProgramMatrix_unitary as has
  have hpq : knownControlAddress k false ≠ knownControlAddress k true := by
    intro h; have hh := congrFun h (Fin.last k); simp [knownControlAddress] at hh
  have hx : A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket (knownControlAddress k false) := by
    simpa only [run_reflectionCompile, ApplyGate] using! hax
  have hy : A *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket (knownControlAddress k true) := by
    simpa only [run_reflectionCompile, ApplyGate] using! hay
  refine ⟨fs ++ bs ++ rs, ?_, ?_, ?_⟩
  · rw [reflectionLegal_append,reflectionLegal_append]; exact ⟨⟨hfs,hbs⟩,hrs⟩
  · have hfl : fs.length = as.length := List.length_map _
    have hrl : rs.length = as.length := by simp [rs,ds,reflectionAdjoint_length]
    simp only [List.length_append,hfl,hrl,hblen]
    have hcost : multiKnownCost k ≤ 30*k+6 := by
      unfold multiKnownCost; split <;> omega
    nlinarith
  · intro ψ
    rw [reflectionCompile_append,reflectionCompile_append,run_append,run_append,
      knownFrame_lift_program (k+1) as has, hb,
      knownFrame_lift_program (k+1) ds hds, reflectionAdjoint_matrix as has]
    congr 1
    exact known_two_level_unitary_conjugate A hA x y _ _ hxy hpq hx hy B ψ

/-- A single-coordinate phase acts by adding the correction `(z - 1) * ψ x` at the selected
basis state. -/
theorem known_two_level_phase_update {I : Type} [Fintype I] [DecidableEq I]
    (x : I) (z : ℂ) (ψ : QState I) :
    twoLevelMatrix (.phase x z) *ᵥ ψ = ψ + ((z-1)*ψ x) • Qatlib.Foundations.PureStateMath.Ket x := by
  funext u
  rw [twoLevel_phase_mulVec]
  by_cases hux : u=x <;> simp_all [Qatlib.Foundations.PureStateMath.Ket,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring

/-- Conjugating a phase instruction by a unitary that maps basis state `x` to `p` moves that
phase from `p` back to `x`. -/
theorem known_two_level_phase_conjugate {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ unitaryGroup I ℂ) (x p : I)
    (hx : A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket p) (z : ℂ) (ψ : QState I) :
    Aᴴ *ᵥ (twoLevelMatrix (.phase p z) *ᵥ (A *ᵥ ψ)) =
      twoLevelMatrix (.phase x z) *ᵥ ψ := by
  obtain ⟨hix,hcx⟩ := known_unitary_mapped_ket A hA x p hx
  rw [known_two_level_phase_update,known_two_level_phase_update,
    Matrix.mulVec_add,Matrix.mulVec_smul,hix,hcx,Matrix.mulVec_mulVec,
    show Aᴴ*A=1 from hA.1,Matrix.one_mulVec]

/-- A unit-modulus phase on any `n`-qubit basis coordinate has a legal local implementation
using at most `128 * (n + 1)²` gates and restored zero workspace. -/
theorem knownPhase_actual_synthesis (n : ℕ) (x : Reg n) (z : ℂ) (hz : star z*z=1) :
    ∃ gs : List (ReflectionGate (n+(n+1))), reflectionLegal gs ∧
      gs.length ≤ 128*(n+1)^2 ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) (knownFrameEmbed n ψ) =
        knownFrameEmbed n (twoLevelMatrix (.phase x z) *ᵥ ψ) := by
  let as := knownAddressFlips x (fun _=>true)
  obtain ⟨has,halen,hax⟩ := knownAddressFlips_spec x (fun _=>true)
  obtain ⟨bs,hbs,hblen,hb⟩ := knownCanonicalPhase_synthesis n z hz
  let e := knownPrefixWires n (n+1)
  let fs := as.map (knownWireGateMap e)
  have hfs : reflectionLegal fs := knownWireMapList_legal e as has
  let ds := reflectionAdjoint as
  have hds : reflectionLegal ds := reflectionAdjoint_legal as has
  let rs := ds.map (knownWireGateMap e)
  have hrs : reflectionLegal rs := knownWireMapList_legal e ds hds
  let A := reflectionProgramMatrix as
  have hA : A ∈ unitaryGroup (Reg n) ℂ := reflectionProgramMatrix_unitary as has
  have hx : A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket (fun _=>true) := by
    simpa only [run_reflectionCompile,ApplyGate] using! hax
  refine ⟨fs ++ bs ++ rs, ?_, ?_, ?_⟩
  · rw [reflectionLegal_append,reflectionLegal_append]; exact ⟨⟨hfs,hbs⟩,hrs⟩
  · have hfl : fs.length = as.length := List.length_map _
    have hrl : rs.length = as.length := by simp [rs,ds,reflectionAdjoint_length]
    simp only [List.length_append,hfl,hrl,hblen]
    have hcost : multiKnownCost n ≤ 30*n+6 := by
      unfold multiKnownCost; split <;> omega
    nlinarith
  · intro ψ
    rw [reflectionCompile_append,reflectionCompile_append,run_append,run_append,
      knownFrame_lift_program n as has,hb,
      knownFrame_lift_program n ds hds,reflectionAdjoint_matrix as has]
    congr 1
    exact known_two_level_phase_conjugate A hA x _ hx z ψ

/-- Every legal `n`-qubit two-level instruction has an exact legal local implementation using at
most `128 * (n + 1)²` gates with `n + 1` workspace qubits returned to zero. -/
theorem known_two_level_gray_local_implementation
    (n : ℕ) (g : TwoLevelInstruction (Reg n)) (hg : twoLevelLegal g) :
    ∃ gs : List (ReflectionGate (n+(n+1))), reflectionLegal gs ∧
      gs.length ≤ 128*(n+1)^2 ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) (knownFrameEmbed n ψ) =
        knownFrameEmbed n (twoLevelMatrix g *ᵥ ψ) := by
  cases g with
  | phase x z => exact knownPhase_actual_synthesis n x z hg
  | pair x y B =>
    cases n with
    | zero => exact (hg.1 (Subsingleton.elim _ _)).elim
    | succ k => exact knownPair_actual_synthesis k x y hg.1 B hg.2

/-- If each legal instruction has an implementation of at most `C` gates under a fixed state
embedding, a legal two-level program has an implementation of at most `C * ts.length` gates. -/
theorem twoLevel_program_table_of_instruction_tables (n N C : ℕ)
    (embed : QState (Reg n) → QState (Reg N))
    (ts : List (TwoLevelInstruction (Reg n)))
    (hts : ∀ g ∈ ts, twoLevelLegal g)
    (hlocal : ∀ g ∈ ts, twoLevelLegal g →
      ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧ gs.length ≤ C ∧
        ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) (embed ψ) =
          embed (twoLevelMatrix g *ᵥ ψ)) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧ gs.length ≤ C*ts.length ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) (embed ψ) =
        embed (twoLevelProgram ts *ᵥ ψ) := by
  induction ts with
  | nil =>
    refine ⟨[],by simp [reflectionLegal],by simp,?_⟩
    intro ψ
    simp [reflectionCompile,twoLevelProgram]
  | cons g ts ih =>
    obtain ⟨fs,hfs,hflen,hf⟩ := hlocal g List.mem_cons_self (hts g List.mem_cons_self)
    obtain ⟨gs,hgs,hlen,hg⟩ := ih (fun t ht => hts t (List.mem_cons_of_mem g ht))
      (fun t ht => hlocal t (List.mem_cons_of_mem g ht))
    refine ⟨fs ++ gs,(reflectionLegal_append fs gs).mpr ⟨hfs,hgs⟩,?_,?_⟩
    · simp only [List.length_append,List.length_cons]
      nlinarith
    · intro ψ
      rw [reflectionCompile_append,run_append,hf,hg,twoLevelProgram_cons,
        ← Matrix.mulVec_mulVec]

/-- Local implementations bounded by `C` for each two-level instruction yield an exact
implementation of every `n`-qubit unitary using at most `C * 4ⁿ` gates and zero queries. -/
theorem known_unitary_table_of_instruction_tables (n N C : ℕ)
    (embed : QState (Reg n) → QState (Reg N))
    (hlocal : ∀ (g : TwoLevelInstruction (Reg n)), twoLevelLegal g →
      ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧ gs.length ≤ C ∧
        ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) (embed ψ) =
          embed (twoLevelMatrix g *ᵥ ψ))
    (U : Matrix (Reg n) (Reg n) ℂ) (hU : U ∈ unitaryGroup (Reg n) ℂ) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧ gs.length ≤ C*4^n ∧
      QueryCount (reflectionCompile gs) = 0 ∧ GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) (embed ψ) = embed (U *ᵥ ψ) := by
  obtain ⟨ts,hts,htlen,ht⟩ := known_unitary_two_level_factorization (Reg n) U hU
  obtain ⟨gs,hgs,hlen,hg⟩ := twoLevel_program_table_of_instruction_tables n N C
    embed ts hts (fun g _ => hlocal g)
  have hcard : Fintype.card (Reg n) = 2^n := by simp [Reg]
  rw [hcard] at htlen
  have htri : 2^n*(2^n+1)/2 ≤ 2^n*2^n := Nat.div_le_of_le_mul (by
    have hpos := Nat.pow_pos (n := n) (by decide : 0 < 2)
    nlinarith)
  have hp : (2:ℕ)^n*2^n = 4^n := by rw [← mul_pow]; rfl
  have htslen : ts.length ≤ 4^n := by rw [← hp]; exact htlen.trans htri
  refine ⟨gs,hgs,hlen.trans (Nat.mul_le_mul_left _ htslen),
    queryCount_reflectionCompile gs,gateCount_reflectionCompile gs,?_⟩
  intro ψ
  rw [hg,ht]

/-- A legal two-level program has an exact local implementation using at most `128 * (n + 1)² *
ts.length` gates and restored zero workspace. -/
theorem known_two_level_program_actual_synthesis (n : ℕ)
    (ts : List (TwoLevelInstruction (Reg n))) (hts : ∀ g ∈ ts, twoLevelLegal g) :
    ∃ gs : List (ReflectionGate (n+(n+1))), reflectionLegal gs ∧
      gs.length ≤ 128*(n+1)^2*ts.length ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) (knownFrameEmbed n ψ) =
        knownFrameEmbed n (twoLevelProgram ts *ᵥ ψ) := by
  exact twoLevel_program_table_of_instruction_tables n (n+(n+1)) (128*(n+1)^2)
    (knownFrameEmbed n) ts hts
    (fun g _ hg => known_two_level_gray_local_implementation n g hg)

/-- Every known `n`-qubit unitary has an exact legal local implementation using at most `128 *
(n + 1)² * 4ⁿ` gates, zero queries, and `n + 1` workspace qubits returned to zero. See
[BarencoEtAl1995] for the synthesis framework. -/
theorem known_unitary_actual_clean_local_synthesis
    (n : ℕ) (U : Matrix (Reg n) (Reg n) ℂ) (hU : U ∈ unitaryGroup (Reg n) ℂ) :
    ∃ gs : List (ReflectionGate (n+(n+1))), reflectionLegal gs ∧
      gs.length ≤ 128*(n+1)^2*4^n ∧
      QueryCount (reflectionCompile gs) = 0 ∧ GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) (knownFrameEmbed n ψ) =
        knownFrameEmbed n (U *ᵥ ψ) := by
  exact known_unitary_table_of_instruction_tables n (n+(n+1)) (128*(n+1)^2)
    (knownFrameEmbed n) (known_two_level_gray_local_implementation n) U hU

end Qatlib.Concepts.MatrixAccess.KnownFrameSynth
