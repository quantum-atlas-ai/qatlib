/-
Copyright (c) 2026 qatlas-lean-lib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Concepts.GateVocabulary.LocalReflectionGates

@[expose] public section


set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Papers.GaussBosonic24.GateUniversal

/-- The single-qubit **`Y` Pauli matrix** on the `Bool` basis. -/
def PauliY : Matrix Bool Bool ℂ :=
  fun a b => if a then (if b then 0 else -Complex.I) else (if b then Complex.I else 0)

/-- The standard single-qubit rotation about the `y` axis,
`Ry(θ) = [[cos(θ/2), −sin(θ/2)], [sin(θ/2), cos(θ/2)]]`, with rows/columns
indexed by `Bool` (the paper's convention, Lemma 2 / Eq. (D3)). -/
def Ry (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    match a, b with
    | false, false => (Real.cos (θ / 2) : ℂ)
    | false, true => -(Real.sin (θ / 2) : ℂ)
    | true, false => (Real.sin (θ / 2) : ℂ)
    | true, true => (Real.cos (θ / 2) : ℂ)

/-- `Ry(0)` is the identity. -/
@[simp] theorem Ry_zero : Ry 0 = 1 := by
  ext a b
  cases a <;> cases b <;> simp [Ry]

/-- `Ry(θ)` is real, so its conjugate transpose is its transpose. -/
theorem ry_conjTranspose_eq_transpose (θ : ℝ) : (Ry θ)ᴴ = (Ry θ)ᵀ := by
  ext a b
  cases a <;> cases b <;>
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Ry, Matrix.of_apply]
  · rw [Complex.star_def]; simp only [Complex.conj_ofReal]
  · rw [Complex.star_def]; simp only [Complex.conj_ofReal]
  · rw [Complex.star_def]
    simp only [← Complex.ofReal_neg, Complex.conj_ofReal]
  · rw [Complex.star_def]; simp only [Complex.conj_ofReal]

/-- **`Ry(θ)` is unitary.** -/
theorem ry_unitary (θ : ℝ) : Ry θ ∈ Matrix.unitaryGroup Bool ℂ := by
  have hc : (↑(Real.sin (θ / 2)) * ↑(Real.sin (θ / 2)) +
      ↑(Real.cos (θ / 2)) * ↑(Real.cos (θ / 2)) : ℂ) = 1 := by
    have h : Real.sin (θ / 2) * Real.sin (θ / 2) +
        Real.cos (θ / 2) * Real.cos (θ / 2) = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, h]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    ry_conjTranspose_eq_transpose]
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  cases a <;> cases b <;>
    simp only [Ry, Matrix.of_apply, Matrix.transpose_apply, Fintype.sum_bool,
      ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false]
  all_goals
    first
      | linear_combination hc
      | ring

/-- The two-qubit **controlled-`Ry`** gate, controlled on the first (control)
qubit in the `true` state: `CRy(θ) = 1 ⊕ Ry(θ)` in the control block.  The
index type is `Bool ⊕ Bool`, canonically identified with the pair type
`Bool × Bool` (`control, target`). -/
def cryTwo (θ : ℝ) : Matrix (Bool ⊕ Bool) (Bool ⊕ Bool) ℂ :=
  fromBlocks 1 0 0 (Ry θ)

/-- `CRy(0)` is the identity. -/
@[simp] theorem cryTwo_zero : cryTwo 0 = 1 := by
  rw [cryTwo, Ry_zero, fromBlocks_one]

/-- **`CRy(θ)` is unitary.** -/
theorem cryTwo_unitary (θ : ℝ) : cryTwo θ ∈ Matrix.unitaryGroup (Bool ⊕ Bool) ℂ := by
  have h : (Ry θ)ᴴ * Ry θ = 1 := by
    have hh := (Matrix.mem_unitaryGroup_iff'.mp (ry_unitary θ))
    rwa [Matrix.star_eq_conjTranspose] at hh
  rw [cryTwo, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    fromBlocks_conjTranspose, fromBlocks_multiply]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add, h, fromBlocks_one]

/-- Controlled-`Ry(θ)` placed on wires `c` (control, active on the `true`
branch) and `t` (target) of an `n`-qubit register; all other wires are
spectators.  This is the paper's `CRy` gate (Lemma 2). -/
def cryOnWires {n : ℕ} (c t : Fin n) (θ : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y =>
    if x c = y c then
      (if x c then (wireGate n t (Ry θ)) x y else (if x = y then 1 else 0))
    else 0

/-- A single gate instruction of the paper's universal set on `n` qubits. -/
inductive L2Gate (n : ℕ) where
  | rz (w : Fin n) (θ : ℝ)
  | ry (w : Fin n) (θ : ℝ)
  | cry (c t : Fin n) (hct : c ≠ t) (θ : ℝ)

/-- Matrix semantics of a single instruction.  (The side condition `c ≠ t` of
`CRy` is syntactic; the interpreted matrix is `cryOnWires`.) -/
def l2GateMatrix {n : ℕ} : L2Gate n → Matrix (Reg n) (Reg n) ℂ
  | .rz w θ => wireGate n w (Rz θ)
  | .ry w θ => wireGate n w (Ry θ)
  | .cry c t _ θ => cryOnWires c t θ

/-- Matrix semantics of a word (leftmost gate applied first). -/
def l2WordMatrix {n : ℕ} : List (L2Gate n) → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | g :: gs => l2WordMatrix gs * l2GateMatrix g

/-- **Lemma 2, universality contract.**  Every `n`-qubit unitary is exactly the
matrix of some word over `{Rz, Ry, CRy}`. -/
def Lemma2Universal : Prop :=
  ∀ (n : ℕ) (U : Matrix (Reg n) (Reg n) ℂ),
    U ∈ Matrix.unitaryGroup (Reg n) ℂ → ∃ gs : List (L2Gate n), l2WordMatrix gs = U

/-- Every `Rz`/`Ry` instruction denotes a unitary matrix (the controlled-`Ry`
instruction is unitary on the two-qubit block `cryTwo`; its wire placement
`cryOnWires` inherits that unitarity and is the paper's `CRy`). -/
theorem l2GateMatrix_unitary_rz_ry {n : ℕ} (w : Fin n) (θ : ℝ) :
    l2GateMatrix (.rz w θ) ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
      l2GateMatrix (.ry w θ) ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  ⟨by simpa [l2GateMatrix] using wireGate_unitary n w (Rz θ) (rz_unitary θ),
    by simpa [l2GateMatrix] using wireGate_unitary n w (Ry θ) (ry_unitary θ)⟩

/-- A zero-qubit register admits only the empty gate word, whose matrix is the identity. -/
theorem zero_register_word (gs : List (L2Gate 0)) : l2WordMatrix gs = 1 := by
  cases gs with
  | nil => rfl
  | cons g gs =>
    cases g with
    | rz w _ => exact Fin.elim0 w
    | ry w _ => exact Fin.elim0 w
    | cry c _ _ _ => exact Fin.elim0 c

/-- The unrestricted exact-universality contract fails on a zero-qubit global phase. -/
theorem universality_zero_false : ¬ Lemma2Universal := by
  intro h
  have hu : (-1 : Matrix (Reg 0) (Reg 0) ℂ) ∈ Matrix.unitaryGroup (Reg 0) ℂ := by
    simp [Matrix.mem_unitaryGroup_iff']
  obtain ⟨gs, hgs⟩ := h 0 (-1) hu
  have heq : (1 : Matrix (Reg 0) (Reg 0) ℂ) = -1 :=
    (zero_register_word gs).symm.trans hgs
  let z : Reg 0 := fun i => Fin.elim0 i
  have hz := congrFun (congrFun heq z) z
  norm_num at hz

end Qatlib.Papers.GaussBosonic24.GateUniversal
