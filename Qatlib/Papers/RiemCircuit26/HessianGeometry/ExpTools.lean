/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.UniformSpace.Real
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Matrix
open scoped Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.RiemCircuit26.HessianGeometry

abbrev Mat (p : ℕ) := Matrix (Fin p) (Fin p) ℂ

def comm {p : ℕ} (A B : Mat p) : Mat p := A * B - B * A

@[simp]
theorem comm_self {p : ℕ} (A : Mat p) : comm A A = 0 := by
  simp [comm]

theorem comm_add_left {p : ℕ} (A B C : Mat p) : comm (A + B) C = comm A C + comm B C := by
  simp only [comm, add_mul, mul_add]
  abel

theorem comm_add_right {p : ℕ} (A B C : Mat p) : comm A (B + C) = comm A B + comm A C := by
  simp only [comm, add_mul, mul_add]
  abel

theorem comm_neg_left {p : ℕ} (A B : Mat p) : comm (-A) B = -comm A B := by
  simp only [comm, neg_mul, mul_neg]
  abel

theorem comm_neg_right {p : ℕ} (A B : Mat p) : comm A (-B) = -comm A B := by
  simp only [comm, neg_mul, mul_neg]
  abel

theorem comm_smul_left {p : ℕ} (c : ℂ) (A B : Mat p) : comm (c • A) B = c • comm A B := by
  simp only [comm, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

theorem comm_smul_right {p : ℕ} (c : ℂ) (A B : Mat p) : comm A (c • B) = c • comm A B := by
  simp only [comm, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

theorem comm_neg_swap {p : ℕ} (A B : Mat p) : comm A B = -comm B A := by
  simp only [comm]
  abel

theorem comm_star {p : ℕ} (A B : Mat p) : (comm A B)ᴴ = -comm Aᴴ Bᴴ := by
  have h : (comm A B)ᴴ = (A * B)ᴴ - (B * A)ᴴ := by
    rw [comm, Matrix.conjTranspose_sub]
  rw [h, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, comm, neg_sub]

theorem comm_hermitian_skew {p : ℕ} (A B : Mat p) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (comm A B)ᴴ = -comm A B := by
  rw [comm_star, hA, hB]

theorem comm_skew_skew {p : ℕ} (A B : Mat p) (hA : Aᴴ = -A) (hB : Bᴴ = -B) :
    (comm A B)ᴴ = -comm A B := by
  rw [comm_star, hA, hB]
  congr 1
  simp only [comm, neg_mul_neg]

theorem trace_commutator_mul {p : ℕ} (A B C : Mat p) :
    (comm A B * C).trace = (A * comm B C).trace := by
  have hL : (comm A B * C).trace = (A * (B * C)).trace - (B * (A * C)).trace := by
    simp only [comm, sub_mul, Matrix.mul_assoc, Matrix.trace_sub]
  have hR : (A * comm B C).trace = (A * (B * C)).trace - (A * (C * B)).trace := by
    simp only [comm, mul_sub, Matrix.trace_sub]
  have hcyc : (B * (A * C)).trace = (A * (C * B)).trace := by
    rw [Matrix.trace_mul_cycle' B A C, Matrix.trace_mul_cycle' C B A]
  rw [hL, hR, hcyc]

theorem trace_commutator_cycle {p : ℕ} (A B C : Mat p) :
    (comm A B * C).trace = (comm B C * A).trace := by
  have hL : (comm A B * C).trace = (A * (B * C)).trace - (A * (C * B)).trace := by
    rw [trace_commutator_mul]
    simp only [comm, mul_sub, Matrix.trace_sub]
  have hR : (comm B C * A).trace = (B * (C * A)).trace - (B * (A * C)).trace := by
    rw [trace_commutator_mul]
    simp only [comm, mul_sub, Matrix.trace_sub]
  have h1 : (A * (B * C)).trace = (B * (C * A)).trace := by
    rw [Matrix.trace_mul_cycle' A B C, Matrix.trace_mul_cycle' C A B]
  have h2 : (A * (C * B)).trace = (B * (A * C)).trace := by
    rw [Matrix.trace_mul_cycle' A C B]
  rw [hL, hR, h1, h2]

theorem trace_commutator_self {p : ℕ} (A B : Mat p) : (comm A B).trace = 0 := by
  rw [comm, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

theorem trace_mul_commutator {p : ℕ} (A B C : Mat p) :
    (A * comm B C).trace = (C * comm A B).trace := by
  have hL : (A * comm B C).trace = (A * (B * C)).trace - (A * (C * B)).trace := by
    simp only [comm, mul_sub, Matrix.trace_sub]
  have hR : (C * comm A B).trace = (C * (A * B)).trace - (C * (B * A)).trace := by
    simp only [comm, mul_sub, Matrix.trace_sub]
  have h1 : (A * (B * C)).trace = (C * (A * B)).trace := by
    rw [Matrix.trace_mul_cycle' A B C]
  have h2 : (A * (C * B)).trace = (C * (B * A)).trace := by
    rw [Matrix.trace_mul_cycle' A C B, Matrix.trace_mul_cycle' B A C]
  rw [hL, hR, h1, h2]

noncomputable def pauliHom {p : ℕ} (P : Mat p) (hP : P * P = 1) : ℂ →ₐ[ℝ] Mat p :=
  Complex.liftAux (Complex.I • P) (by
    rw [smul_mul_smul, hP, Complex.I_mul_I]
    simp)

@[simp]
theorem pauliHom_apply {p : ℕ} (P : Mat p) (hP : P * P = 1) (z : ℂ) :
    pauliHom P hP z = algebraMap ℝ (Mat p) z.re + z.im • (Complex.I • P) :=
  Complex.liftAux_apply _ _ z

theorem exp_euler {p : ℕ} (P : Mat p) (hP : P * P = 1) (θ : ℝ) :
    NormedSpace.exp (θ • (Complex.I • P)) =
      (Real.cos θ) • (1 : Mat p) + (Real.sin θ) • (Complex.I • P) := by
  letI : Algebra ℚ (Mat p) := Algebra.restrictScalars ℚ ℝ (Mat p)
  have hcont : Continuous (pauliHom P hP) := by
    have hfun : (⇑(pauliHom P hP) : ℂ → Mat p)
        = fun z => algebraMap ℝ (Mat p) z.re + z.im • (Complex.I • P) :=
      funext (pauliHom_apply P hP)
    rw [hfun]
    exact ((continuous_algebraMap ℝ (Mat p)).comp Complex.continuous_re).add
      (Complex.continuous_im.smul continuous_const)
  have hz : NormedSpace.exp ((θ : ℂ) * Complex.I) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [← Complex.exp_eq_exp_ℂ, Complex.exp_mul_I θ, Complex.ofReal_cos,
      Complex.ofReal_sin]
  have hmap := NormedSpace.map_exp (pauliHom P hP) hcont ((θ : ℂ) * Complex.I)
  rw [hz] at hmap
  have hB : pauliHom P hP ((θ : ℂ) * Complex.I) = θ • (Complex.I • P) := by
    rw [pauliHom_apply]
    simp
  have hC : pauliHom P hP ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) =
      (Real.cos θ) • (1 : Mat p) + (Real.sin θ) • (Complex.I • P) := by
    rw [pauliHom_apply]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Algebra.algebraMap_eq_smul_one]
  rw [hB, hC] at hmap
  exact hmap.symm

theorem exp_half_euler {p : ℕ} (P : Mat p) (hP : P * P = 1) (θ : ℝ) :
    NormedSpace.exp ((θ / 2) • (Complex.I • P)) =
      (Real.cos (θ / 2)) • (1 : Mat p) + (Real.sin (θ / 2)) • (Complex.I • P) :=
  exp_euler P hP (θ / 2)

def halfI {p : ℕ} (P : Mat p) : Mat p := (1 / 2 : ℝ) • (Complex.I • P)

theorem halfI_star {p : ℕ} (P : Mat p) (hP : Pᴴ = P) : (halfI P)ᴴ = -halfI P := by
  simp [halfI, hP, Complex.conj_I]

noncomputable def evol {p : ℕ} (Ω : Mat p) (t : ℝ) : Mat p :=
  NormedSpace.exp (t • Ω)

@[simp]
theorem evol_zero {p : ℕ} (Ω : Mat p) : evol Ω 0 = 1 := by
  simp [evol]

theorem evol_hasDerivAt {p : ℕ} (Ω : Mat p) (t : ℝ) :
    HasDerivAt (evol Ω) (evol Ω t * Ω) t := by
  simpa [evol] using! hasDerivAt_exp_smul_const Ω t

theorem evol_star_hasDerivAt {p : ℕ} (Ω : Mat p) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evol Ω s)ᴴ) ((evol Ω t * Ω)ᴴ) t :=
  (evol_hasDerivAt Ω t).star

theorem evol_star_eq {p : ℕ} (Ω : Mat p) (t : ℝ) : (evol Ω t)ᴴ = evol Ωᴴ t := by
  simp only [evol]
  rw [← Matrix.star_eq_conjTranspose, NormedSpace.star_exp]
  congr 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul]
  simp

theorem evol_commute {p : ℕ} (Ω : Mat p) (t : ℝ) : Commute (evol Ω t) Ω := by
  have h : Commute (t • Ω) Ω := (Commute.refl Ω).smul_left t
  simpa [evol] using Commute.exp_left h

theorem evol_mul_comm {p : ℕ} (Ω : Mat p) (t : ℝ) : evol Ω t * Ω = Ω * evol Ω t :=
  (evol_commute Ω t).eq

noncomputable def conjEvol {p : ℕ} (Ω M : Mat p) (t : ℝ) : Mat p :=
  evol Ω t * M * (evol Ω t)ᴴ

@[simp]
theorem conjEvol_zero {p : ℕ} (Ω M : Mat p) : conjEvol Ω M 0 = M := by
  simp [conjEvol]

theorem hasDerivAt_conjEvol {p : ℕ} (Ω M : Mat p) (hΩ : Ωᴴ = -Ω) (t : ℝ) :
    HasDerivAt (conjEvol Ω M) (conjEvol Ω (comm Ω M) t) t := by
  have hU : HasDerivAt (evol Ω) (evol Ω t * Ω) t := evol_hasDerivAt Ω t
  have hUs : HasDerivAt (fun s : ℝ => (evol Ω s)ᴴ) ((evol Ω t * Ω)ᴴ) t := hU.star
  have h1 : HasDerivAt (fun s : ℝ => evol Ω s * M) (evol Ω t * Ω * M) t := hU.mul_const M
  have h2 := h1.mul hUs
  have h2' : HasDerivAt (fun s : ℝ => (evol Ω s * M) * (evol Ω s)ᴴ)
      ((evol Ω t * Ω * M) * (evol Ω t)ᴴ + (evol Ω t * M) * (evol Ω t * Ω)ᴴ) t := h2
  have hder : (evol Ω t * Ω * M) * (evol Ω t)ᴴ + (evol Ω t * M) * (evol Ω t * Ω)ᴴ
      = conjEvol Ω (comm Ω M) t := by
    rw [Matrix.conjTranspose_mul, hΩ, neg_mul]
    simp only [conjEvol, comm]
    noncomm_ring
  rw [hder] at h2'
  exact h2'

noncomputable def traceCLM (p : ℕ) : Mat p →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin p) ℝ ℂ)

theorem hasDerivAt_trace {p : ℕ} {F : ℝ → Mat p} {F' : Mat p} {t : ℝ}
    (h : HasDerivAt F F' t) : HasDerivAt (fun s => (F s).trace) F'.trace t := by
  have hc := (traceCLM p).hasFDerivAt.comp_hasDerivAt t h
  simpa [traceCLM] using! hc

theorem hasDerivAt_trace_conjEvol {p : ℕ} (Ω O M : Mat p) (hΩ : Ωᴴ = -Ω) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (O * conjEvol Ω M s).trace)
      ((O * conjEvol Ω (comm Ω M) t).trace) t :=
  hasDerivAt_trace ((hasDerivAt_conjEvol Ω M hΩ t).const_mul O)

theorem hasDerivAt_trace_conjEvol_zero {p : ℕ} (Ω O M : Mat p) (hΩ : Ωᴴ = -Ω) :
    HasDerivAt (fun s : ℝ => (O * conjEvol Ω M s).trace) ((O * comm Ω M).trace) 0 := by
  simpa using hasDerivAt_trace_conjEvol Ω O M hΩ 0

theorem hasDerivAt_trace_conjEvol_second {p : ℕ} (Ω O M : Mat p) (hΩ : Ωᴴ = -Ω) :
    HasDerivAt (fun t : ℝ => (O * conjEvol Ω (comm Ω M) t).trace)
      ((O * comm Ω (comm Ω M)).trace) 0 := by
  simpa using hasDerivAt_trace_conjEvol Ω O (comm Ω M) hΩ 0

end Qatlib.Papers.RiemCircuit26.HessianGeometry
