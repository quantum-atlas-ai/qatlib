/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorNetwork.GaugeInvariance
import Qatlib.Concepts.TensorNetwork.CanonicalMPS

/-!
# Sequential matrix product amplitude classes

`seqAmplitude` contracts site tensors with initial and final ancillary vectors. `InMpsClass`
records such representations, `InDetSequentialClass` additionally requires each step to be
isometric, and `InProbSequentialClass` is defined to equal `InMpsClass`.

Computational basis states provide explicit examples with bond dimension one through
`basisStep`. See [SchoenEtAl2007] for the sequential generation setting.

## Main statements

* `det_subset_mps`: forgets the step isometry conditions.
* `prob_iff_mps`: unfolds the probabilistic class definition.
* `basisState_det`: deterministic sequential representation of a basis state.

## References

* [Schoen et al., 2007][SchoenEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.MatProductCav06.MainResults

variable {n d D : ℕ}

/-- The sequential amplitude obtained by summing over ancillary index paths, with an initial
vector and the conjugate of a final vector. -/
def seqAmplitude (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (φI φF : Fin D → ℂ) (x : Fin n → Fin d) : ℂ :=
  ∑ α : Fin (n + 1) → Fin D,
    conj (φF (α (Fin.last n))) * φI (α ⟨0, Nat.succ_pos n⟩) *
      ∏ i : Fin n, A i (x i) (α (Fin.succ i)) (α (Fin.castSucc i))

/-- The step isometry condition `∑ x, (V x)ᴴ * V x = 1` on a family of ancillary matrices. -/
def IsStepIsometry {d D : ℕ} (V : Fin d → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∑ x : Fin d, (V x)ᴴ * (V x) = 1

/-- The predicate that an amplitude function has a sequential matrix product representation with
bond dimension `D` and two boundary vectors. -/
def InMpsClass (n d D : ℕ) (ψ : (Fin n → Fin d) → ℂ) : Prop :=
  ∃ (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (φI φF : Fin D → ℂ),
    ∀ x, ψ x = seqAmplitude A φI φF x

/-- The predicate that an amplitude function has a sequential representation whose site tensors
satisfy `IsStepIsometry`. -/
def InDetSequentialClass (n d D : ℕ) (ψ : (Fin n → Fin d) → ℂ) : Prop :=
  ∃ (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (φI φF : Fin D → ℂ),
    (∀ i, IsStepIsometry (A i)) ∧ ∀ x, ψ x = seqAmplitude A φI φF x

/-- The probabilistic sequential class, defined here as the matrix product class. -/
def InProbSequentialClass (n d D : ℕ) (ψ : (Fin n → Fin d) → ℂ) : Prop :=
  InMpsClass n d D ψ

/-- Deterministic sequential membership implies matrix product membership after forgetting the
step isometry conditions. -/
theorem det_subset_mps {n d D : ℕ} {ψ : (Fin n → Fin d) → ℂ}
    (h : InDetSequentialClass n d D ψ) : InMpsClass n d D ψ := by
  rcases h with ⟨A, φI, φF, _, hψ⟩
  exact ⟨A, φI, φF, hψ⟩

/-- The probabilistic sequential predicate is equivalent to the matrix product predicate. See
[SchoenEtAl2007]. -/
theorem prob_iff_mps {n d D : ℕ} {ψ : (Fin n → Fin d) → ℂ} :
    InProbSequentialClass n d D ψ ↔ InMpsClass n d D ψ :=
  Iff.rfl

/-- The amplitude function of the computational basis configuration `w`. -/
def basisState {n d : ℕ} (w : Fin n → Fin d) : (Fin n → Fin d) → ℂ :=
  fun x => if x = w then 1 else 0

/-- The bond dimension one tensor selecting the physical basis value `w`. -/
def basisStep {d : ℕ} (w : Fin d) : Fin d → Matrix (Fin 1) (Fin 1) ℂ :=
  fun x _ _ => if x = w then 1 else 0

/-- Contracting the tensors selecting `w` with unit boundary vectors gives the basis state
amplitude at `x`. -/
theorem basisState_amplitude {n d : ℕ} (w : Fin n → Fin d) (x : Fin n → Fin d) :
    seqAmplitude (D := 1) (fun i (x : Fin d) => basisStep (w i) x)
      (fun _ => 1) (fun _ => 1) x = basisState w x := by
  classical
  haveI : Unique (Fin (n + 1) → Fin 1) := uniqueOfSubsingleton (fun _ => 0)
  rw [seqAmplitude, Fintype.sum_unique]
  simp only [basisStep, map_one, one_mul]
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, forall_true_left, basisState]
  simp [funext_iff]

/-- The bond dimension one basis tensor satisfies the step isometry condition. -/
theorem basisStep_isStepIsometry {d : ℕ} (w : Fin d) :
    IsStepIsometry (d := d) (D := 1) (basisStep w) := by
  classical
  unfold IsStepIsometry
  ext a b
  have hab : a = b := Subsingleton.elim a b
  subst hab
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, if_true, basisStep]
  rw [Finset.sum_eq_single w]
  · simp
  · intro x _ hx
    simp [hx]
  · intro hmem
    exact absurd (Finset.mem_univ w) hmem

/-- A computational basis state belongs to the matrix product class with bond dimension one. -/
theorem basisState_mps {n d : ℕ} (w : Fin n → Fin d) :
    InMpsClass n d 1 (basisState w) :=
  ⟨fun i x => basisStep (w i) x, fun _ => 1, fun _ => 1,
    fun x => (basisState_amplitude w x).symm⟩

/-- A computational basis state belongs to the deterministic sequential class with bond
dimension one. See [SchoenEtAl2007]. -/
theorem basisState_det {n d : ℕ} (w : Fin n → Fin d) :
    InDetSequentialClass n d 1 (basisState w) :=
  ⟨fun i x => basisStep (w i) x, fun _ => 1, fun _ => 1,
    fun i => basisStep_isStepIsometry (w i),
    fun x => (basisState_amplitude w x).symm⟩

end Qatlib.Papers.MatProductCav06.MainResults
