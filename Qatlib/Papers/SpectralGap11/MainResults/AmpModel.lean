/-
Copyright (c) 2026 qatlas contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Tensor
public import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
public import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation

@[expose] public section


/-!
# SpectralGap11 reviewed AmpModel

Closed legacy definitions and lemmas, with separately named contract diagnostics.
Coverage and unproved source bridges are recorded in the batch source review.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.SpectralGap11.MainResults

variable {N L : ℕ}

/-- `Υ_k = |k⟩⟨k|`, the rank-one projector on the ancilla register (Eq. (2)). -/
noncomputable def ancProj (k : Fin L) : Matrix (Fin L) (Fin L) ℂ :=
  outerProduct (Ket k)

/-- `X = Σ_{k=1}^L Π_k ⊗ |k⟩⟨k|` (Theorem 1, Eq. (2)). -/
noncomputable def ampX (Proj : Fin L → Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N × Fin L) (Fin N × Fin L) ℂ :=
  ∑ k, TensorGate (Proj k) (ancProj k)

/-- `U = 1l - 2X`, written additively as `1 - X - X` (Theorem 1, Eq. (3)). -/
noncomputable def ampU (Proj : Fin L → Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N × Fin L) (Fin N × Fin L) ℂ :=
  1 - ampX Proj - ampX Proj

/-- `P = 1l_N ⊗ |0⟩⟨0|`, with `|0⟩` the uniform ancilla state (Theorem 1, p. 4). -/
noncomputable def ampP : Matrix (Fin N × Fin L) (Fin N × Fin L) ℂ :=
  TensorGate (1 : Matrix (Fin N) (Fin N) ℂ) (outerProduct (Uniform (Fin L)))

/-- `G = U P U - P` (Theorem 1, Eq. (4)). -/
noncomputable def ampG (Proj : Fin L → Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N × Fin L) (Fin N × Fin L) ℂ :=
  ampU Proj * ampP * ampU Proj - ampP

/-- `H' = L·G + δ(1l - P)`, the amplified Hamiltonian (Theorem 1, Eq. (7)). -/
noncomputable def ampH' (Proj : Fin L → Matrix (Fin N) (Fin N) ℂ) (δ : ℂ) :
    Matrix (Fin N × Fin L) (Fin N × Fin L) ℂ :=
  (L : ℂ) • ampG Proj + δ • (1 - ampP)

/-- The last ordered index of a finite spectrum (position of the smallest
eigenvalue under Mathlib's antitone `eigenvalues₀`). -/
def ordLast {I : Type} [Fintype I] (h : 0 < Fintype.card I) : Fin (Fintype.card I) :=
  Fin.rev ⟨0, h⟩

/-- The second-smallest ordered index of a finite spectrum. -/
def ordPrev {I : Type} [Fintype I] (h : 2 ≤ Fintype.card I) : Fin (Fintype.card I) :=
  Fin.rev ⟨1, by omega⟩

/-- A finite type with at least two elements has positive cardinality. -/
lemma card_pos_of_two_le {I : Type} [Fintype I] (h2 : 2 ≤ Fintype.card I) :
    0 < Fintype.card I :=
  Nat.pos_of_ne_zero (by omega)

/-- Spectral gap between the two smallest eigenvalues of a Hermitian matrix. -/
noncomputable def spectralGap {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (h2 : 2 ≤ Fintype.card I) : ℝ :=
  orderedHermitianValues hA (ordPrev (I := I) h2)
    - orderedHermitianValues hA (ordLast (I := I) (card_pos_of_two_le (I := I) h2))

/-- Dimension of the kernel (null space) of a matrix. -/
noncomputable def nullDim {I : Type} [Fintype I]
    (A : Matrix I I ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.ker A.mulVecLin)


/-- The amplified matrix is Hermitian for Hermitian inputs and a real penalty. -/
theorem ampH'_isHermitian (Proj : Fin L → Matrix (Fin N) (Fin N) ℂ)
    (hHerm : ∀ k, (Proj k).IsHermitian) (δ : ℂ) (hδ : star δ = δ) :
    (ampH' (N := N) (L := L) Proj δ).IsHermitian := by
  have hX : (ampX Proj).IsHermitian := by
    unfold ampX
    apply isSelfAdjoint_sum
    intro k _
    change (TensorGate (Proj k) (ancProj k))ᴴ = TensorGate (Proj k) (ancProj k)
    unfold TensorGate ancProj
    rw [Matrix.conjTranspose_kronecker, (hHerm k).eq]
    have hk : (outerProduct (Ket k)).IsHermitian :=
      (isOrthogonalProjector_outerProduct (normalized_ket k)).isSelfAdjoint
    rw [hk.eq]
  have hU : (ampU Proj).IsHermitian := (Matrix.isHermitian_one.sub hX).sub hX
  have hP : (ampP (N := N) (L := L)).IsHermitian := by
    unfold ampP TensorGate
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply, outerProduct, mul_comm]
  have hG : (ampG Proj).IsHermitian := by
    unfold ampG
    have h := Matrix.isHermitian_mul_mul_conjTranspose (ampU Proj) hP
    rw [hU.eq] at h
    exact h.sub hP
  exact (hG.smul (IsSelfAdjoint.natCast L)).add
    ((Matrix.isHermitian_one.sub hP).smul hδ)

end Qatlib.Papers.SpectralGap11.MainResults
