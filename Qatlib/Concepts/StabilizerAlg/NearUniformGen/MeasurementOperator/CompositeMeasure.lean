/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Composite measurement operators

`measOp` applies a branch-dependent matrix to a data register while preserving the branch
register. Its block decomposition and action on `initState` yield the branch-mixture formula
`composite_probability`; multiplication and conjugate transpose act independently on each
branch. For background, see [Kitaev1995].

## Main statements

* `composite_probability`: expresses coarse-grained Born weights as a mixture of conditional
  branch weights.
* `measOp_mul`: identifies multiplication with branchwise matrix multiplication.
* `measOp_unitary`: proves the right-unitarity identity from the corresponding branch
  identities.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath

set_option linter.unusedSectionVars false

namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen.MeasurementOperator

variable {A D Ω Y : Type*} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
  [Fintype Ω] [DecidableEq Ω] [Fintype Y] [DecidableEq Y]

/-- The block-diagonal matrix applying `U (branch a)` to the data register at each preserved
branch-register value `a`. -/
def measOp (branch : A → Ω) (U : Ω → Matrix D D ℂ) : Matrix (A × D) (A × D) ℂ :=
  Matrix.of fun (a, d) (a', d') => if a = a' then U (branch a) d d' else 0

/-- The matrix equal to `Uv` on the data blocks whose branch label is `V` and zero on all other
blocks. -/
def blockOp (branch : A → Ω) (V : Ω) (Uv : Matrix D D ℂ) :
    Matrix (A × D) (A × D) ℂ :=
  Matrix.of fun (a, d) (a', d') => if a = a' ∧ branch a = V then Uv d d' else 0

/-- The diagonal projector onto branch-register basis values with label `V`. -/
def branchProj (branch : A → Ω) (V : Ω) : Matrix A A ℂ :=
  Matrix.diagonal fun a => if branch a = V then 1 else 0

/-- The product of the branch-register amplitude function `ψ` and the data-register basis state
at `d0`. -/
def initState (ψ : QState A) (d0 : D) : QState (A × D) :=
  fun p => if p.2 = d0 then ψ p.1 else 0

/-- The coarse-grained Born weight for output `y` after applying branch matrix `U V` to the
basis state at `d0`. -/
def condProb (U : Ω → Matrix D D ℂ) (C : D → Y) (d0 : D) (V : Ω) (y : Y) : ℝ :=
  ∑ d, if C d = y then BornProb (ApplyGate (U V) (Ket d0)) d else 0

/-- The sum of the Born weights of branch-register values whose label is `V`. -/
def branchProb (branch : A → Ω) (ψ : QState A) (V : Ω) : ℝ :=
  ∑ a, if branch a = V then BornProb ψ a else 0

/-- Applying a matrix to a basis ket gives the corresponding matrix column. -/
theorem applyGate_ket_apply (U : Matrix D D ℂ) (d0 d : D) :
    ApplyGate U (Ket d0) d = U d d0 := by
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single d0]
  · simp [Ket]
  · intro d' _ hd'; simp [Ket, hd']
  · intro h; exact absurd (Finset.mem_univ d0) h

/-- The composite measurement operator is the sum of its branch-restricted blocks. -/
theorem measOp_eq_sum_block (branch : A → Ω) (U : Ω → Matrix D D ℂ) :
    measOp branch U = ∑ V, blockOp branch V (U V) := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  simp only [measOp, blockOp, Matrix.of_apply, Matrix.sum_apply]
  by_cases ha : a = a'
  · subst ha
    rw [Finset.sum_eq_single (branch a)]
    · simp
    · intro V _ hV; simp [Ne.symm hV]
    · intro h; exact absurd (Finset.mem_univ (branch a)) h
  · simp [ha]

/-- The composite operator sends the initialized amplitude at `(a, d)` to `ψ a * U (branch a) d
d0`. -/
theorem measOp_apply (branch : A → Ω) (U : Ω → Matrix D D ℂ) (ψ : QState A) (d0 : D)
    (a : A) (d : D) :
    ApplyGate (measOp branch U) (initState ψ d0) (a, d) = ψ a * U (branch a) d d0 := by
  simp only [ApplyGate, Matrix.mulVec, dotProduct, measOp, initState, Matrix.of_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single d0]
    · simp [mul_comm]
    · intro d' _ hd'; simp [hd']
    · intro h; exact absurd (Finset.mem_univ d0) h
  · intro a' _ ha'; simp [Ne.symm ha']
  · intro h; exact absurd (Finset.mem_univ a) h

/-- The Born weight after composite measurement factors into the branch-register weight and the
corresponding branch data-register weight. -/
theorem bornProb_measOp (branch : A → Ω) (U : Ω → Matrix D D ℂ) (ψ : QState A) (d0 : D)
    (a : A) (d : D) :
    BornProb (ApplyGate (measOp branch U) (initState ψ d0)) (a, d)
      = BornProb ψ a * BornProb (ApplyGate (U (branch a)) (Ket d0)) d := by
  simp only [BornProb]
  rw [measOp_apply, applyGate_ket_apply, norm_mul, mul_pow]

/-- The coarse-grained Born weight of the composite operator is the sum of the branch weights
times their conditional output weights, giving the mixture identity of [Kitaev, Lemma
8][Kitaev1995]. -/
theorem composite_probability (branch : A → Ω) (U : Ω → Matrix D D ℂ)
    (ψ : QState A) (d0 : D) (C : D → Y) (y : Y) :
    (∑ a, ∑ d, if C d = y then
        BornProb (ApplyGate (measOp branch U) (initState ψ d0)) (a, d) else 0)
      = ∑ V, branchProb branch ψ V * condProb U C d0 V y := by
  have hL : ∀ a d, BornProb (ApplyGate (measOp branch U) (initState ψ d0)) (a, d)
      = BornProb ψ a * BornProb (ApplyGate (U (branch a)) (Ket d0)) d :=
    fun a d => bornProb_measOp branch U ψ d0 a d
  simp only [hL, branchProb, condProb]
  have key : ∀ (f : A → ℝ) (g : Ω → D → ℝ),
      (∑ V, (∑ a, if branch a = V then f a else 0) *
              (∑ d, if C d = y then g V d else 0))
        = ∑ a, ∑ d, if C d = y then f a * g (branch a) d else 0 := by
    intro f g
    simp_rw [Fintype.sum_mul_sum]
    simp only [ite_mul, zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_eq_single (branch a)]
    · simp
    · intro V _ hV; simp [Ne.symm hV]
    · intro h; exact absurd (Finset.mem_univ (branch a)) h
  rw [key]

/-- Multiplying composite measurement operators multiplies their data matrices branchwise, as
used in [Kitaev, Lemma 8][Kitaev1995]. -/
theorem measOp_mul (branch : A → Ω) (U U' : Ω → Matrix D D ℂ) :
    measOp branch U * measOp branch U' = measOp branch (fun V => U V * U' V) := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  simp only [measOp, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
  by_cases ha : a = a'
  · subst ha
    simp only [if_true]
    rw [Finset.sum_eq_single a]
    · simp
    · intro a'' _ ha''
      simp [Ne.symm ha'']
    · intro h; exact absurd (Finset.mem_univ a) h
  · simp [ha]

omit [Fintype A] [Fintype D] [DecidableEq D] [Fintype Ω] [DecidableEq Ω] in

/-- The conjugate transpose of a composite measurement operator is obtained by
conjugate-transposing every branch matrix, as used in [Kitaev, Lemma 8][Kitaev1995]. -/
theorem measOp_conjTranspose (branch : A → Ω) (U : Ω → Matrix D D ℂ) :
    (measOp branch U)ᴴ = measOp branch (fun V => (U V)ᴴ) := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  simp only [measOp, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases ha : a = a'
  · subst ha; simp
  · have h0 : ¬ (a' = a) := fun h => ha h.symm
    simp [ha, h0]

/-- If every branch matrix satisfies `U V * (U V)ᴴ = 1`, the composite measurement operator
satisfies the same identity. This supplies the branchwise unitarity calculation associated
with [Kitaev, Lemma 8][Kitaev1995]. -/
theorem measOp_unitary (branch : A → Ω) (U : Ω → Matrix D D ℂ)
    (hU : ∀ V, U V * (U V)ᴴ = 1) :
    measOp branch U * (measOp branch U)ᴴ = 1 := by
  rw [measOp_conjTranspose, measOp_mul]
  have hone : (fun V => U V * (U V)ᴴ) = fun _ => (1 : Matrix D D ℂ) := funext hU
  rw [hone]
  ext ⟨a, d⟩ ⟨a', d'⟩
  simp only [measOp, Matrix.of_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases ha : a = a'
  · subst ha; simp
  · simp [ha]

end Qatlib.Concepts.StabilizerAlg.NearUniformGen.MeasurementOperator
