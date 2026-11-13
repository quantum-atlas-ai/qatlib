/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Foundations.PureStateMath.Reflection

set_option backward.isDefEq.respectTransparency false

/-!
# Definitions 1–2 and Eqs. (4)–(7) — standard form, quantum signal processor, eigenphase

Low–Chuang, *Hamiltonian Simulation by Qubitization*, fixed arXiv:1610.06546v3.

* Definition 1 (PDF p.4): a Hermitian signal operator `H` with `‖H‖ ≤ 1` is
  encoded in **standard form** by a unitary oracle `U` on ancilla ⊗ system and
  a state-preparation oracle `G |0⟩ = |G⟩` with
  `(⟨G|_a ⊗ I_s) U (|G⟩_a ⊗ I_s) = H`.
* Definition 2 (PDF p.5): a **quantum signal processor** maps a standard-form
  encoding of `H` (`‖H‖ ≤ 1`) and a function `f` on the unit disc into a
  standard-form encoding of `f[H] = ∑_λ f(λ)|λ⟩⟨λ|`.
* Eqs. (4)–(7) (PDF p.6): Gram–Schmidt defines `|G⊥_λ⟩ = (Ŵ − λ)|G_λ⟩/√(1−λ²)`
  (Eq. (4)); the iterate acts on `span{|G_λ⟩, |G⊥_λ⟩}` as the rotation matrix
  `[[λ, −√(1−λ²)], [√(1−λ²), λ]]` (Eq. (5)), i.e. `Ŵ = e^{−iŶ_λ θ_λ}` (Eq. (6))
  with the eigenphase `θ_λ = cos⁻¹(λ)` (Eq. (7)).

This file defines the two problem specifications and proves the eigenphase
identities of Eqs. (4)–(7) (`cos θ_λ = λ`, `sin θ_λ = √(1−λ²)`) and the entrywise
form of the Eq. (5) rotation, including its unitarity. The matrix-level standard
form is the frozen `IsBlockEncoding U j₀ H 1` (corner form), which is equivalent
to Definition 1 by `standardFormEncoding_iff_isBlockEncoding`; the frozen
FiberBridge/BlockEncoding calculus is the substrate for the rest of the block.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.Qubitization19.MainResults

/-- Fixed arXiv:1610.06546v3, Definition 1 (PDF p.4): the signal operator `H`
(with `‖H‖ ≤ 1`) is encoded in standard form by the unitary workspace oracle
`U` on `J × I` and the ancilla signal state at fiber index `j₀`: the `j₀`-corner
of `U` is `H` and `U` is unitary. -/
def StandardFormEncoding {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (U : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (H : Matrix I I ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (J × I) ℂ ∧ ‖H‖ ≤ 1 ∧ BlockCorner U j₀ = H

/-- Fixed arXiv:1610.06546v3, Definition 1 (PDF p.4), compared with the frozen
block-encoding calculus: standard form at unit scale is exactly the corner form
`IsBlockEncoding U j₀ H 1` together with the spectral bound `‖H‖ ≤ 1` that the
paper requires for post-selected signal operators. -/
theorem standardFormEncoding_iff_isBlockEncoding {J I : Type*} [Fintype J]
    [DecidableEq J] [Fintype I] [DecidableEq I] (U : Matrix (J × I) (J × I) ℂ)
    (j₀ : J) (H : Matrix I I ℂ) :
    StandardFormEncoding U j₀ H ↔ IsBlockEncoding U j₀ H 1 ∧ ‖H‖ ≤ 1 := by
  unfold StandardFormEncoding IsBlockEncoding
  constructor
  · rintro ⟨hU, hnorm, hcorner⟩
    exact ⟨⟨hU, one_pos, by simpa using hcorner⟩, hnorm⟩
  · rintro ⟨⟨hU, -, hcorner⟩, hnorm⟩
    exact ⟨hU, hnorm, by simpa using hcorner⟩

/-- Fixed arXiv:1610.06546v3, Definition 2 (PDF p.5): `f` maps the unit interval
into the complex unit disc, `∀ x ∈ [−1,1], |f(x)| ≤ 1`. -/
def IsUnitDiscValued (f : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, -1 ≤ x → x ≤ 1 → ‖f x‖ ≤ 1

/-- Fixed arXiv:1610.06546v3, Eq. after Definition 2 (PDF p.4): the operator
`f[H] = ∑_λ f(λ)|λ⟩⟨λ|` applied by the spectral calculus. -/
def SpectrumAction {I : Type*} [Fintype I] [DecidableEq I] (f : ℝ → ℂ)
    (H fH : Matrix I I ℂ) : Prop :=
  ∀ (v : I → ℂ) (lam : ℝ), H *ᵥ v = ((lam : ℝ) : ℂ) • v → fH *ᵥ v = f lam • v

universe u

/-- A standard-form encoding witness for `H`: a finite ancilla carrier `J`, a
fiber index `j₀`, and the unitary oracle. -/
structure StandardFormWitness (I : Type u) [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) where
  /-- Ancilla carrier. -/
  J : Type u
  [instFintype : Fintype J]
  [instDecidableEq : DecidableEq J]
  j₀ : J
  U : Matrix (J × I) (J × I) ℂ
  encoding : StandardFormEncoding U j₀ H

/-- `H` has a standard-form encoding. -/
def EncodableInStandardForm {I : Type u} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) : Prop :=
  Nonempty (StandardFormWitness I H)

/-- **Statement only — not proved in Qatlib.** Fixed arXiv:1610.06546v3, Definition 2 (PDF p.5): the quantum signal
processor problem. Given a Hermitian `H` with `‖H‖ ≤ 1` and a standard-form
encoding of `H`, and given a unit-disc function `f` on `[−1,1]`, produce a
standard-form encoding of the operator `f[H]`. The resources listed in the
paper (queries to the standard-form oracles, constant ancillas, and
`O(Q log dim H_a)` gates for a degree-`Q` processor) are not quantified in this
problem statement; they are supplied by the concrete processors of Theorems 3–4. -/
def QuantumSignalProcessorSpec : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H : Matrix I I ℂ),
    H.IsHermitian → ‖H‖ ≤ 1 → EncodableInStandardForm H →
    ∀ f : ℝ → ℂ, IsUnitDiscValued f →
      ∃ fH : Matrix I I ℂ,
        SpectrumAction f H fH ∧ EncodableInStandardForm fH

/-- Fixed arXiv:1610.06546v3, Eq. (7) (PDF p.6): the eigenphase of the iterate
on the eigenbranch of eigenvalue `λ` is `θ_λ = cos⁻¹(λ)`. -/
def eigenphase (lam : ℝ) : ℝ := Real.arccos lam

/-- Fixed arXiv:1610.06546v3, Eq. (7) (PDF p.6): the first half of the defining
equality `λ − i√(1−λ²) = cos θ_λ − i sin θ_λ`, namely `cos θ_λ = λ`. -/
theorem eigenphase_cos (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    Real.cos (eigenphase lam) = lam :=
  Real.cos_arccos h1 h2

/-- Fixed arXiv:1610.06546v3, Eq. (7) (PDF p.6): the second half of the defining
equality, `sin θ_λ = √(1−λ²)`. -/
theorem eigenphase_sin (lam : ℝ) :
    Real.sin (eigenphase lam) = Real.sqrt (1 - lam ^ 2) :=
  Real.sin_arccos lam

/-- Fixed arXiv:1610.06546v3, Eq. (5) (PDF p.6): the rotation realized by the
iterate on `span{|G_λ⟩, |G⊥_λ⟩}`, with entries `λ` and `±√(1−λ²)`. -/
def eq5Rotation (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(lam : ℂ), -((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ);
     ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ), (lam : ℂ)]

/-- Fixed arXiv:1610.06546v3, Eqs. (4)–(5) (PDF p.6): the first column of the
iterate on the eigenbranch. With `|G_λ⟩` the first basis vector and `|G⊥_λ⟩` the
second, Eq. (4)'s Gram–Schmidt state is exactly the second component
`√(1−λ²)`, so `Ŵ|G_λ⟩ = λ|G_λ⟩ + √(1−λ²)|G⊥_λ⟩` is the statement that the
first column of `eq5Rotation lam` is `(lam, √(1−lam²))`. -/
theorem eq5Rotation_col_zero (lam : ℝ) :
    (eq5Rotation lam).col (0 : Fin 2)
      = fun i : Fin 2 =>
          if i = 0 then (lam : ℂ) else ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) := by
  ext i
  fin_cases i <;> simp [eq5Rotation, Matrix.col]

/-- Fixed arXiv:1610.06546v3, Eqs. (4)–(5) (PDF p.6): the action of the iterate
on the eigenvector `|G_λ⟩ = |0⟩` of the two-dimensional eigenbranch, in the
form `Ŵ|G_λ⟩ = λ|G_λ⟩ + √(1−λ²)|G⊥_λ⟩` with the Gram–Schmidt state
`|G⊥_λ⟩ = |1⟩` of Eq. (4). -/
theorem eq5Rotation_mulVec_basis (lam : ℝ) :
    eq5Rotation lam *ᵥ (Pi.single (0 : Fin 2) (1 : ℂ))
      = fun i : Fin 2 =>
          if i = 0 then (lam : ℂ) else ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) := by
  rw [Matrix.mulVec_single_one]
  exact eq5Rotation_col_zero lam

/-- Fixed arXiv:1610.06546v3, Eqs. (5)–(6) (PDF p.6): the `(0,0)` and `(1,1)`
entries of the iterate are `cos θ_λ` for the eigenphase `θ_λ = cos⁻¹(λ)`. -/
theorem eq5Rotation_diagonal_cos (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    eq5Rotation lam 0 0 = ((Real.cos (eigenphase lam) : ℝ) : ℂ) ∧
      eq5Rotation lam 1 1 = ((Real.cos (eigenphase lam) : ℝ) : ℂ) := by
  constructor <;> simp [eq5Rotation, eigenphase, Real.cos_arccos h1 h2]

/-- Fixed arXiv:1610.06546v3, Eqs. (5)–(6) (PDF p.6): the off-diagonal entries
of the iterate are `∓ sin θ_λ` for the eigenphase `θ_λ = cos⁻¹(λ)`. -/
theorem eq5Rotation_offdiagonal_sin (lam : ℝ) (_h1 : -1 ≤ lam) (_h2 : lam ≤ 1) :
    eq5Rotation lam 0 1 = ((-Real.sin (eigenphase lam) : ℝ) : ℂ) ∧
      eq5Rotation lam 1 0 = ((Real.sin (eigenphase lam) : ℝ) : ℂ) := by
  constructor <;> simp [eq5Rotation, eigenphase, Real.sin_arccos]

/-- Fixed arXiv:1610.06546v3, Eq. (5) (PDF p.6): the rotation matrix of the
iterate is unitary (indeed a real orthogonal rotation), as required of a walk
step. -/
theorem eq5Rotation_mem_unitaryGroup (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    eq5Rotation lam ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hs : ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)
      = 1 - ((lam : ℝ) : ℂ) * ((lam : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by nlinarith)]
    push_cast
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eq5Rotation, Matrix.mul_apply, Fin.sum_univ_two, Complex.conj_ofReal]
  all_goals first | (rw [hs]; ring) | ring

end Qatlib.Papers.Qubitization19.MainResults
