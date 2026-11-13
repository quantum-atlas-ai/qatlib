/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.LcuFrame.Normalization

/-!
# Controlled unitaries on coherent branches

`controlled` is the finite block-diagonal matrix applying a selected system matrix on each
control coordinate. `coherent` combines control amplitudes with conditional system vectors, and
the module proves the branchwise action, unitarity, and normalization identities.

`truncated` replaces branches whose supplied query count exceeds a cutoff by the identity,
preserving controlled unitarity. These constructions express coherent branch operations in the
setting of [JefferyKothariMagniez2013].

## Main statements

* `controlled_apply`: controlled multiplication acts independently on each control slice.
* `coherent_normalized`: normalized control amplitudes and branch states give a normalized
  coherent state.
* `truncated_controlled_unitary`: cutoff replacement preserves unitarity.

## References

* [Jeffery et al., 2013][JefferyKothariMagniez2013]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace Qatlib.Foundations.MatrixGeometry.BranchUnitary
open Qatlib.Foundations.MatrixGeometry.LcuFrame
variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

/-- The block-diagonal matrix applying `U c` on the system register for control value `c`. -/
def controlled (U : C → Matrix S S ℂ) : Matrix (S × C) (S × C) ℂ :=
  Matrix.blockDiagonal U

omit [DecidableEq S] in

/-- The action of the controlled matrix on a fixed control slice is exactly the matrix-vector
action of that branch. This realizes the coherent branch action used in
[JefferyKothariMagniez2013]. -/
theorem controlled_apply (U : C → Matrix S S ℂ) (ψ : State (S × C)) (s : S) (c : C) :
    (controlled U *ᵥ ψ) (s,c) = (U c *ᵥ (fun t => ψ (t,c))) s := by
  simp [controlled, Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type]

/-- If every branch matrix is unitary, their controlled block-diagonal matrix is unitary, as in
the branch construction of [JefferyKothariMagniez2013]. -/
theorem controlled_unitary (U : C → Matrix S S ℂ)
    (hU : ∀ c, U c ∈ Matrix.unitaryGroup S ℂ) :
    controlled U ∈ Matrix.unitaryGroup (S × C) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  unfold controlled
  change (Matrix.blockDiagonal U)ᴴ * Matrix.blockDiagonal U = 1
  rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  have h : (fun c => (U c)ᴴ * U c) = (fun _ : C => (1 : Matrix S S ℂ)) := by
    funext c
    exact Matrix.mem_unitaryGroup_iff'.mp (hU c)
  simpa only [h] using! (Matrix.blockDiagonal_one (o := C) (m := S) (α := ℂ))

/-- A unitary matrix preserves the coordinate complex inner product. -/
theorem unitary_inner (U : Matrix S S ℂ) (hU : U ∈ Matrix.unitaryGroup S ℂ)
    (u v : State S) : Inner (U *ᵥ u) (U *ᵥ v) = Inner u v := by
  have hu : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]

/-- A unitary matrix maps a normalized coordinate state to a normalized state. -/
theorem unitary_normalized (U : Matrix S S ℂ) (hU : U ∈ Matrix.unitaryGroup S ℂ)
    (v : State S) (hv : Normalized v) : Normalized (U *ᵥ v) := by
  apply (normalized_iff_inner _).2
  rw [unitary_inner U hU, (normalized_iff_inner v).1 hv]

/-- The system-control state whose amplitude at `(s, c)` is `α c * φ c s`. -/
def coherent (α : C → ℂ) (φ : C → State S) : State (S × C) :=
  fun x => α x.2 * φ x.2 x.1

omit [DecidableEq C] [DecidableEq S] in

/-- Normalized control amplitudes and normalized conditional states give a normalized coherent
state, as used in [JefferyKothariMagniez2013]. -/
theorem coherent_normalized (α : C → ℂ) (φ : C → State S)
    (hα : ∑ c, ‖α c‖ ^ 2 = 1) (hφ : ∀ c, Normalized (φ c)) :
    Normalized (coherent α φ) := by
  unfold Normalized coherent
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [norm_mul, mul_pow]
  simp_rw [← Finset.mul_sum, show ∀ c, (∑ s, ‖φ c s‖ ^ 2) = 1 from hφ, mul_one]
  exact hα

omit [DecidableEq S] in

/-- Applying a controlled matrix to a coherent state applies the corresponding matrix to each
conditional state while retaining its control amplitude. -/
theorem controlled_coherent (U : C → Matrix S S ℂ) (α : C → ℂ) (φ : C → State S) :
    controlled U *ᵥ coherent α φ = coherent α (fun c => U c *ᵥ φ c) := by
  ext ⟨s,c⟩
  rw [controlled_apply]
  change (U c *ᵥ (α c • φ c)) s = α c * (U c *ᵥ φ c) s
  rw [Matrix.mulVec_smul]
  rfl

/-- The branch family obtained by retaining `U c` when `q c ≤ cutoff` and replacing it by the
identity otherwise. -/
def truncated (U : C → Matrix S S ℂ) (q : C → ℕ) (cutoff : ℕ) : C → Matrix S S ℂ :=
  fun c => if q c ≤ cutoff then U c else 1

/-- Replacing branches above the query cutoff by the identity preserves unitarity of the
controlled matrix for every cutoff. This is the cutoff construction used in
[JefferyKothariMagniez2013]. -/
theorem truncated_controlled_unitary (U : C → Matrix S S ℂ)
    (hU : ∀ c, U c ∈ Matrix.unitaryGroup S ℂ) (q : C → ℕ) (cutoff : ℕ) :
    controlled (truncated U q cutoff) ∈ Matrix.unitaryGroup (S × C) ℂ := by
  apply controlled_unitary
  intro c
  unfold truncated
  split_ifs
  · exact hU c
  · exact (Matrix.unitaryGroup S ℂ).one_mem

end Qatlib.Foundations.MatrixGeometry.BranchUnitary
