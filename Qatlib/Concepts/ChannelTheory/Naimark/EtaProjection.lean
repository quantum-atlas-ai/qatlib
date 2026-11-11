/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

/-!
# Conserved positive-label weight under Hamiltonian evolution

`hamiltonian` is block diagonal in a finite auxiliary label, with block `A₁ + η e * A₂`. The
positive-label projector `positive` commutes with this matrix and its exponential `evolution`.
Hermitian system matrices give unitary evolution and conservation of the projected trace weight.

The mathematical background is described in [JinLiu2024].

## Main statements

* `hamiltonian_hermitian`: Hermitian blocks give a Hermitian joint Hamiltonian.
* `evolution_unitary`: real-time exponential evolution is unitary.
* `positive_weight_constant`: positive-label trace weight is conserved.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped Classical Matrix.Norms.Operator
namespace Qatlib.Concepts.ChannelTheory.Naimark.EtaProjection
variable {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

/-- The auxiliary-label block diagonal matrix whose block at label `e` is `A₁ + η e * A₂`. -/
def hamiltonian (A₁ A₂ : Matrix I I ℂ) (η : E→ℝ) : Matrix (I×E) (I×E) ℂ :=
  fun p q=>if p.2=q.2 then A₁ p.1 q.1+(η p.2:ℂ)*A₂ p.1 q.1 else 0

/-- The diagonal projector retaining auxiliary labels for which `η` is strictly positive. -/
def positive (η : E→ℝ) : Matrix (I×E) (I×E) ℂ :=diagonal (fun p=>if 0<η p.2 then 1 else 0)

/-- The positive-label projector commutes with the auxiliary-label block Hamiltonian. -/
theorem positive_commutes (A₁ A₂ : Matrix I I ℂ) (η : E→ℝ) :
    Commute (positive (I:=I) η) (hamiltonian A₁ A₂ η) := by
  apply Matrix.ext
  intro p q
  simp only [positive,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases h : p.2=q.2
  · simp [hamiltonian,h,mul_comm]
  · simp [hamiltonian,h]
omit [Fintype I] [Fintype E] [DecidableEq I] in

/-- If `A₁` and `A₂` are Hermitian, their real auxiliary-label block Hamiltonian is Hermitian.
See [JinLiu2024]. -/
theorem hamiltonian_hermitian (A₁ A₂ : Matrix I I ℂ) (h₁ : A₁.IsHermitian) (h₂ : A₂.IsHermitian) (η : E→ℝ) :
    (hamiltonian A₁ A₂ η).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  have h₁' := congrArg (fun M : Matrix I I ℂ=>M p.1 q.1) h₁.eq
  have h₂' := congrArg (fun M : Matrix I I ℂ=>M p.1 q.1) h₂.eq
  simp only [Matrix.conjTranspose_apply] at h₁' h₂'
  by_cases h : p.2=q.2
  · simp [hamiltonian,h,star_add,star_mul,h₁',h₂',mul_comm]
  · simp [hamiltonian,h,Ne.symm h]

/-- The matrix exponential `exp (-I * t • hamiltonian A₁ A₂ η)` describing real-time evolution. -/
def evolution (A₁ A₂ : Matrix I I ℂ) (η : E→ℝ) (t : ℝ) : Matrix (I×E) (I×E) ℂ :=
  NormedSpace.exp ((-Complex.I*(t:ℂ)) •hamiltonian A₁ A₂ η)

/-- The positive-label projector commutes with the exponential evolution of the block
Hamiltonian. -/
theorem evolution_commutes (A₁ A₂ : Matrix I I ℂ) (η : E→ℝ) (t : ℝ) :
    Commute (positive (I:=I) η) (evolution A₁ A₂ η t) :=
  ((positive_commutes A₁ A₂ η).smul_right _).exp_right

/-- The exponential evolution is unitary for Hermitian `A₁` and `A₂` and real time. -/
theorem evolution_unitary (A₁ A₂ : Matrix I I ℂ) (h₁ : A₁.IsHermitian) (h₂ : A₂.IsHermitian) (η : E→ℝ) (t : ℝ) :
    evolution A₁ A₂ η t∈Matrix.unitaryGroup (I×E) ℂ := by
  let G := (-Complex.I*(t:ℂ)) •hamiltonian A₁ A₂ η
  have hg : Gᴴ= -G := by
    simp [G,hamiltonian_hermitian A₁ A₂ h₁ h₂ η,Matrix.IsHermitian.eq]
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  change (NormedSpace.exp G)ᴴ*NormedSpace.exp G=1
  rw [← Matrix.exp_conjTranspose,hg,← Matrix.exp_add_of_commute _ _ (Commute.refl G).neg_left]
  simp

/-- For Hermitian `A₁` and `A₂`, conjugation by the evolution preserves the trace pairing of
every input matrix with the positive-label projector. -/
theorem positive_weight_constant (A₁ A₂ : Matrix I I ℂ) (h₁ : A₁.IsHermitian) (h₂ : A₂.IsHermitian)
    (η : E→ℝ) (ρ : Matrix (I×E) (I×E) ℂ) (t : ℝ) :
    ((positive (I:=I) η)*(evolution A₁ A₂ η t*ρ*(evolution A₁ A₂ η t)ᴴ)).trace=
      ((positive (I:=I) η)*ρ).trace := by
  let P:=positive (I:=I) η
  let U:=evolution A₁ A₂ η t
  have hc : P*U=U*P := (evolution_commutes A₁ A₂ η t).eq
  have hu : Uᴴ*U=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff'.mp (evolution_unitary A₁ A₂ h₁ h₂ η t)
  change (P*(U*ρ*Uᴴ)).trace=(P*ρ).trace
  calc
    (P*(U*ρ*Uᴴ)).trace=((P*U)*ρ*Uᴴ).trace := by simp only [Matrix.mul_assoc]
    _=((U*P)*ρ*Uᴴ).trace := by rw [hc]
    _=(Uᴴ*((U*P)*ρ)).trace := Matrix.trace_mul_comm _ _
    _=(P*ρ).trace := by simp only [← Matrix.mul_assoc,hu,Matrix.one_mul]
end Qatlib.Concepts.ChannelTheory.Naimark.EtaProjection
