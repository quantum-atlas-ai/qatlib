/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Fin.Tuple
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Group.ContinuousDiv
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Basic
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.UniformSpace.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Topology Kronecker
open scoped Matrix.Norms.Elementwise
open Filter

namespace Qatlib.Papers.QWalkConnect06.MainResults

open Qatlib.Concepts.ChannelTheory.Stinespring (pauliX pauliY pauliZ)

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℂ

lemma pauliX_sq : pauliX * pauliX = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

lemma pauliY_sq : pauliY * pauliY = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Complex.I_sq]

lemma pauliZ_sq : pauliZ * pauliZ = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

def phase (k : ℝ) : ℂ := Complex.exp ((k : ℂ) * Complex.I)

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]

lemma phase_cos_sin (k : ℝ) : phase k = Complex.cos ((k : ℂ)) + Complex.sin ((k : ℂ)) * Complex.I := by
  unfold phase
  rw [Complex.exp_ofReal_mul_I]
  simp [Complex.ofReal_cos, Complex.ofReal_sin]

lemma phase_neg_eq (k : ℝ) :
    phase (-k) = Complex.cos ((k : ℂ)) - Complex.sin ((k : ℂ)) * Complex.I := by
  rw [phase_cos_sin]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

lemma phase_neg (k : ℝ) : phase (-k) = (phase k)⁻¹ := by
  unfold phase
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg]

lemma phase_ne_zero (k : ℝ) : phase k ≠ 0 := by
  unfold phase
  exact Complex.exp_ne_zero _

lemma phase_mul_neg (k : ℝ) : phase k * phase (-k) = 1 := by
  rw [phase_neg, mul_inv_cancel₀ (phase_ne_zero k)]

lemma phase_neg_mul (k : ℝ) : phase (-k) * phase k = 1 := by
  rw [mul_comm, phase_mul_neg]

lemma phase_two_mul (k : ℝ) : phase (2 * k) = phase k * phase k := by
  rw [show 2 * k = k + k by ring, phase_add]

lemma phase_two_mul_neg (k : ℝ) : phase (-(2 * k)) = phase (-k) * phase (-k) := by
  rw [show -(2 * k) = -k + -k by ring, phase_add]

lemma phase_two_mul' (k : ℝ) : phase (k * 2) = phase k * phase k := by
  rw [show k * 2 = k + k by ring, phase_add]

lemma phase_two_mul_neg' (k : ℝ) : phase (-(k * 2)) = phase (-k) * phase (-k) := by
  rw [show -(k * 2) = -k + -k by ring, phase_add]

lemma phase_cancel (k : ℝ) (a x : ℂ) : a * phase k * x * phase (-k) = a * x := by
  calc a * phase k * x * phase (-k) = a * x * (phase k * phase (-k)) := by ring
    _ = a * x := by rw [phase_mul_neg, mul_one]

lemma phase_cancel_neg (k : ℝ) (a x : ℂ) : a * phase (-k) * x * phase k = a * x := by
  calc a * phase (-k) * x * phase k = a * x * (phase (-k) * phase k) := by ring
    _ = a * x := by rw [phase_neg_mul, mul_one]

lemma phase_add_neg (k : ℝ) : phase k + phase (-k) = 2 * (Real.cos k : ℂ) := by
  have h1 := phase_cos_sin k
  have h2 := phase_neg_eq k
  rw [h1, h2, Complex.ofReal_cos]
  ring

def rotX (θ : ℝ) : M2 :=
  Complex.cos ((θ : ℂ)) • (1 : M2) - ((Complex.sin ((θ : ℂ)) * Complex.I) • pauliX)

def diagZ (k : ℝ) : M2 :=
  Complex.cos ((k : ℂ)) • (1 : M2) - ((Complex.sin ((k : ℂ)) * Complex.I) • pauliZ)

def Ustep (k θ : ℝ) : M2 := diagZ k * rotX θ

lemma rotX_apply (θ : ℝ) :
    rotX θ = !![Complex.cos ((θ : ℂ)), -(Complex.sin ((θ : ℂ)) * Complex.I);
                  -(Complex.sin ((θ : ℂ)) * Complex.I), Complex.cos ((θ : ℂ))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotX, pauliX, Matrix.one_apply] <;> ring

lemma diagZ_apply (k : ℝ) : diagZ k = !![phase (-k), 0; 0, phase k] := by
  have h1 := phase_cos_sin k
  have h2 := phase_neg_eq k
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, pauliZ, Matrix.one_apply, h1, h2] <;> ring

theorem Ustep_entry (k θ : ℝ) :
    Ustep k θ = !![phase (-k) * Complex.cos ((θ : ℂ)),
                   -(Complex.I) * phase (-k) * Complex.sin ((θ : ℂ));
                   -(Complex.I) * phase k * Complex.sin ((θ : ℂ)),
                   phase k * Complex.cos ((θ : ℂ))] := by
  unfold Ustep
  rw [diagZ_apply, rotX_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma cos_pi_div_two_sub_complex (δ : ℝ) :
    Complex.cos (((Real.pi / 2 - δ : ℝ)) : ℂ) = (Real.sin δ : ℂ) := by
  rw [← Complex.ofReal_cos, Real.cos_pi_div_two_sub]

lemma sin_pi_div_two_sub_complex (δ : ℝ) :
    Complex.sin (((Real.pi / 2 - δ : ℝ)) : ℂ) = (Real.cos δ : ℂ) := by
  rw [← Complex.ofReal_sin, Real.sin_pi_div_two_sub]

lemma cos_pi_div_two_sub_cast (δ : ℝ) :
    Complex.cos ((Real.pi : ℂ) * (1 / 2) - (δ : ℂ)) = (Real.sin δ : ℂ) := by
  rw [show (Real.pi : ℂ) * (1 / 2) - (δ : ℂ) = ((Real.pi / 2 - δ : ℝ) : ℂ) by
    push_cast
    ring]
  exact cos_pi_div_two_sub_complex δ

lemma sin_pi_div_two_sub_cast (δ : ℝ) :
    Complex.sin ((Real.pi : ℂ) * (1 / 2) - (δ : ℂ)) = (Real.cos δ : ℂ) := by
  rw [show (Real.pi : ℂ) * (1 / 2) - (δ : ℂ) = ((Real.pi / 2 - δ : ℝ) : ℂ) by
    push_cast
    ring]
  exact sin_pi_div_two_sub_complex δ

lemma cos_neg_complex (δ : ℝ) : Complex.cos (((-δ : ℝ)) : ℂ) = (Real.cos δ : ℂ) := by
  rw [← Complex.ofReal_cos, Real.cos_neg]

lemma sin_neg_complex (δ : ℝ) : Complex.sin (((-δ : ℝ)) : ℂ) = -(Real.sin δ : ℂ) := by
  rw [← Complex.ofReal_sin, Real.sin_neg]
  simp

def rotA (k : ℝ) : M2 := !![0, phase (-2 * k); phase (2 * k), 0]

def rotC (k δ : ℝ) : M2 :=
  Complex.cos ((δ : ℂ)) • (1 : M2) + ((Complex.sin ((δ : ℂ)) * Complex.I) • rotA k)

lemma rotC_apply (k δ : ℝ) :
    rotC k δ = !![Complex.cos ((δ : ℂ)),
                   Complex.I * Complex.sin ((δ : ℂ)) * phase (-2 * k);
                   Complex.I * Complex.sin ((δ : ℂ)) * phase (2 * k),
                   Complex.cos ((δ : ℂ))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotC, rotA, phase_ne_zero] <;> ring

def dblLead (k δ : ℝ) : M2 := rotC k δ * rotX (-δ)

theorem Ustep_sq_eq (k δ : ℝ) :
    Ustep k (Real.pi / 2 - δ) * Ustep k (Real.pi / 2 - δ)
      = (-1 : ℂ) • dblLead k δ := by
  simp only [Ustep_entry, dblLead, rotC_apply, rotX_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
      cos_neg_complex, sin_neg_complex, phase_two_mul, phase_two_mul_neg,
      phase_ne_zero, Complex.ofReal_cos, Complex.ofReal_sin]
  all_goals ring_nf
  all_goals try simp only [cos_pi_div_two_sub_cast, sin_pi_div_two_sub_cast,
    Complex.ofReal_cos, Complex.ofReal_sin, Complex.I_sq]
  all_goals
    try rw [phase_neg]
    try field_simp [phase_ne_zero k]
    ring

lemma dblLead_expand (k δ : ℝ) :
    dblLead k δ
      = (Complex.cos ((δ : ℂ)) ^ 2) • (1 : M2)
        + (-(Complex.sin ((δ : ℂ)) ^ 2)) • !![phase (-2 * k), 0; 0, phase (2 * k)]
        + (Complex.I * (Complex.sin ((δ : ℂ)) * Complex.cos ((δ : ℂ)))) •
            !![0, 1 + phase (-2 * k); 1 + phase (2 * k), 0] := by
  simp only [dblLead, rotC_apply, rotX_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply, smul_eq_mul, cos_neg_complex, sin_neg_complex,
      Complex.ofReal_cos, Complex.ofReal_sin]
  all_goals ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals ring

lemma one_add_phase_two_mul (k : ℝ) :
    (1 : ℂ) + phase (2 * k) = 2 * (Real.cos k : ℂ) * phase k := by
  have h2 : phase (2 * k) = phase k * phase k := phase_two_mul k
  have h1 : (1 : ℂ) = phase k * phase (-k) := (phase_mul_neg k).symm
  rw [h2, h1, ← mul_add, add_comm (phase (-k)), phase_add_neg]
  ring

lemma one_add_phase_neg_two_mul (k : ℝ) :
    (1 : ℂ) + phase (-(2 * k)) = 2 * (Real.cos k : ℂ) * phase (-k) := by
  have h2 : phase (-(2 * k)) = phase (-k) * phase (-k) := phase_two_mul_neg k
  have h1 : (1 : ℂ) = phase (-k) * phase k := by rw [mul_comm, phase_mul_neg]
  rw [h2, h1, ← mul_add, phase_add_neg]
  ring

def Bsym (k : ℝ) : M2 := !![0, phase (-k); phase k, 0]

lemma Bsym_eq (k : ℝ) :
    Bsym k = Complex.cos ((k : ℂ)) • pauliX + Complex.sin ((k : ℂ)) • pauliY := by
  have h1 := phase_cos_sin k
  have h2 := phase_neg_eq k
  unfold Bsym
  rw [h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] <;> ring

lemma offdiag_eq (k : ℝ) :
    (!![0, 1 + phase (-2 * k); 1 + phase (2 * k), 0] : M2)
      = (2 * (Real.cos k : ℂ)) • Bsym k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bsym, Matrix.smul_apply, smul_eq_mul, one_add_phase_two_mul,
      one_add_phase_neg_two_mul] <;> ring

def Hmat (k γ : ℝ) : M2 := ((-2 * γ * Real.cos k : ℝ) : ℂ) • Bsym k

theorem eq10_Hamiltonian (k γ : ℝ) :
    Hmat k γ = ((-2 * γ * Real.cos k : ℝ) : ℂ) •
      (Complex.cos ((k : ℂ)) • pauliX + Complex.sin ((k : ℂ)) • pauliY) := by
  unfold Hmat
  rw [Bsym_eq]

lemma dblLead_deriv_eq (k : ℝ) :
    (!![0, Complex.I * (1 + phase (-(2 * k)));
          Complex.I * (1 + phase (2 * k)), 0] : M2)
      = Complex.I • ((2 * (Real.cos k : ℂ)) • Bsym k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bsym, Matrix.smul_apply, smul_eq_mul, one_add_phase_two_mul,
      one_add_phase_neg_two_mul] <;> ring

theorem dblLead_hasDerivAt (k : ℝ) :
    HasDerivAt (fun δ : ℝ => dblLead k δ)
      (Complex.I • ((2 * (Real.cos k : ℂ)) • Bsym k)) 0 := by
  have hcos : HasDerivAt (fun δ : ℝ => Complex.cos ((δ : ℂ))) (-Complex.sin (0 : ℂ)) 0 :=
    (Complex.hasDerivAt_cos (0 : ℂ)).comp_ofReal
  have hsin : HasDerivAt (fun δ : ℝ => Complex.sin ((δ : ℂ))) (Complex.cos (0 : ℂ)) 0 :=
    (Complex.hasDerivAt_sin (0 : ℂ)).comp_ofReal
  have h1 : HasDerivAt (fun δ : ℝ => Complex.cos ((δ : ℂ)) ^ 2 • (1 : M2)) _ 0 :=
    (hcos.pow 2).smul_const (1 : M2)
  have h2 : HasDerivAt
      (fun δ : ℝ => (-(Complex.sin ((δ : ℂ)) ^ 2)) •
        (!![phase (-2 * k), 0; 0, phase (2 * k)] : M2)) _ 0 :=
    (hsin.pow 2).neg.smul_const _
  have h3 : HasDerivAt
      (fun δ : ℝ => (Complex.I * (Complex.sin ((δ : ℂ)) * Complex.cos ((δ : ℂ))) ) •
        (!![0, 1 + phase (-2 * k); 1 + phase (2 * k), 0] : M2)) _ 0 :=
    ((hsin.mul hcos).const_mul Complex.I).smul_const _
  have hf : HasDerivAt
      (((fun δ : ℝ => (Complex.cos ((δ : ℂ)) ^ 2) • (1 : M2))
          + (fun δ : ℝ => (-(Complex.sin ((δ : ℂ)) ^ 2)) •
              (!![phase (-2 * k), 0; 0, phase (2 * k)] : M2)))
        + (fun δ : ℝ => (Complex.I * (Complex.sin ((δ : ℂ)) * Complex.cos ((δ : ℂ)))) •
            (!![0, 1 + phase (-2 * k); 1 + phase (2 * k), 0] : M2)))
      (!![0, Complex.I * (1 + phase (-(2 * k)));
            Complex.I * (1 + phase (2 * k)), 0] : M2) 0 := by
    have h := (h1.add h2).add h3
    simpa [Complex.cos_zero, Complex.sin_zero] using! h
  have hfun : (((fun δ : ℝ => (Complex.cos ((δ : ℂ)) ^ 2) • (1 : M2))
          + (fun δ : ℝ => (-(Complex.sin ((δ : ℂ)) ^ 2)) •
              (!![phase (-2 * k), 0; 0, phase (2 * k)] : M2)))
        + (fun δ : ℝ => (Complex.I * (Complex.sin ((δ : ℂ)) * Complex.cos ((δ : ℂ)))) •
            (!![0, 1 + phase (-2 * k); 1 + phase (2 * k), 0] : M2)))
      = (fun δ : ℝ => dblLead k δ) := by
    funext δ
    simp only [Pi.add_apply]
    rw [dblLead_expand]
  rw [hfun] at hf
  simpa [dblLead_deriv_eq] using hf

theorem eq8_generator_relation (k γ : ℝ) :
    (γ : ℂ) • (Complex.I • ((2 * (Real.cos k : ℂ)) • Bsym k))
      = (-Complex.I) • Hmat k γ := by
  unfold Hmat
  rw [smul_smul, smul_smul, smul_smul]
  congr 1
  push_cast
  ring

def expIB (k φ : ℝ) : M2 :=
  Complex.cos ((φ : ℂ)) • (1 : M2) + ((Complex.sin ((φ : ℂ)) * Complex.I) • Bsym k)

lemma Bsym_sq (k : ℝ) : Bsym k * Bsym k = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bsym, Matrix.mul_apply, Fin.sum_univ_two, phase_mul_neg, phase_neg_mul]

lemma expIB_add (k φ ψ : ℝ) : expIB k φ * expIB k ψ = expIB k (φ + ψ) := by
  have hcos : Complex.cos (((φ + ψ : ℝ)) : ℂ)
      = Complex.cos ((φ : ℂ)) * Complex.cos ((ψ : ℂ))
        - Complex.sin ((φ : ℂ)) * Complex.sin ((ψ : ℂ)) := by
    rw [show ((φ + ψ : ℝ) : ℂ) = (φ : ℂ) + (ψ : ℂ) by push_cast; ring, Complex.cos_add]
  have hsin : Complex.sin (((φ + ψ : ℝ)) : ℂ)
      = Complex.sin ((φ : ℂ)) * Complex.cos ((ψ : ℂ))
        + Complex.cos ((φ : ℂ)) * Complex.sin ((ψ : ℂ)) := by
    rw [show ((φ + ψ : ℝ) : ℂ) = (φ : ℂ) + (ψ : ℂ) by push_cast; ring, Complex.sin_add]
  rw [expIB, expIB, expIB, hcos, hsin]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bsym, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
  all_goals ring_nf
  all_goals try simp only [Complex.I_sq]
  all_goals try rw [phase_neg]
  all_goals try field_simp [phase_ne_zero k]
  all_goals try ring

lemma expIB_zero (k : ℝ) : expIB k 0 = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [expIB, Bsym, Complex.cos_zero, Complex.sin_zero]

lemma expIB_pow (k φ : ℝ) (n : ℕ) : expIB k φ ^ n = expIB k ((n : ℝ) * φ) := by
  induction n with
  | zero =>
      simp [expIB_zero]
  | succ n ih =>
      rw [pow_succ, ih, expIB_add]
      congr 1
      push_cast
      ring

lemma neg_one_pow_eq_exp (n : ℕ) :
    (-1 : ℂ) ^ n = Complex.exp ((n : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  induction n with
  | zero => simp [Complex.exp_zero]
  | succ n ih =>
      rw [pow_succ, ih, ← Complex.exp_pi_mul_I, ← Complex.exp_add]
      congr 1
      push_cast
      ring

def expNegIH (k γ t : ℝ) : M2 := expIB k (2 * Real.cos k * (γ * t))

theorem expNegIH_eq (k γ t δ : ℝ) (n : ℕ) (h : (n : ℝ) * δ = γ * t) :
    ((-1 : ℂ) ^ n) • expIB k (2 * Real.cos k * ((n : ℝ) * δ))
      = ((-1 : ℂ) ^ n • (1 : M2)) * expNegIH k γ t := by
  rw [h]
  unfold expNegIH
  rw [Matrix.smul_mul, Matrix.one_mul]

theorem eq11_offdiag (k : ℝ) :
    (1 : ℂ) + phase (2 * k) = 2 * (Real.cos k : ℂ) * phase k :=
  one_add_phase_two_mul k

theorem eq11_symbol (k γ : ℝ) :
    ((-γ : ℝ) : ℂ) • (!![0, 1 + phase (-2 * k); 1 + phase (2 * k), 0] : M2)
      = Hmat k γ := by
  unfold Hmat
  rw [offdiag_eq, smul_smul]
  congr 1
  push_cast
  ring

def StepR (α β : ℝ) (pR pL : ℤ → ℝ) (n : ℤ) : ℝ :=
  α * pR (n - 1) + β * pL (n - 1)

def StepL (α β : ℝ) (pR pL : ℤ → ℝ) (n : ℤ) : ℝ :=
  α * pL (n + 1) + β * pR (n + 1)

theorem eq20_two_step (α β : ℝ) (pR pL : ℤ → ℕ → ℝ)
    (hR : ∀ n τ, pR n (τ + 1) = α * pR (n - 1) τ + β * pL (n - 1) τ)
    (hL : ∀ n τ, pL n (τ + 1) = α * pL (n + 1) τ + β * pR (n + 1) τ) :
    (∀ n τ, pR n (τ + 2) = α ^ 2 * pR (n - 2) τ
        + α * β * (pL (n - 2) τ + pL n τ) + β ^ 2 * pR n τ) ∧
      (∀ n τ, pL n (τ + 2) = α ^ 2 * pL (n + 2) τ
        + α * β * (pR (n + 2) τ + pR n τ) + β ^ 2 * pL n τ) := by
  constructor
  · intro n τ
    rw [show τ + 2 = (τ + 1) + 1 by ring, hR n (τ + 1), hR (n - 1) τ, hL (n - 1) τ]
    have h1 : n - 1 - 1 = n - 2 := by ring
    have h2 : n - 1 + 1 = n := by ring
    rw [h1, h2]
    ring
  · intro n τ
    rw [show τ + 2 = (τ + 1) + 1 by ring, hL n (τ + 1), hL (n + 1) τ, hR (n + 1) τ]
    have h1 : n + 1 + 1 = n + 2 := by ring
    have h2 : n + 1 - 1 = n := by ring
    rw [h1, h2]
    ring

theorem eq21_continuum (γ : ℝ) (pR pL : ℤ → ℝ) (n : ℤ) :
    Tendsto (fun Δt : ℝ =>
        ((2 * γ * Δt) ^ 2 * pR (n - 2)
          + (2 * γ * Δt) * (1 - 2 * γ * Δt) * (pL (n - 2) + pL n)
          + ((1 - 2 * γ * Δt) ^ 2 - 1) * pR n) / (2 * Δt))
      (𝓝[>] (0 : ℝ))
      (𝓝 (γ * (pL (n - 2) + pL n) + (-2) * γ * pR n)) := by
  have hFG : (fun Δt : ℝ =>
        ((2 * γ * Δt) ^ 2 * pR (n - 2)
          + (2 * γ * Δt) * (1 - 2 * γ * Δt) * (pL (n - 2) + pL n)
          + ((1 - 2 * γ * Δt) ^ 2 - 1) * pR n) / (2 * Δt))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun Δt : ℝ =>
        2 * γ ^ 2 * Δt * pR (n - 2)
          + γ * (1 - 2 * γ * Δt) * (pL (n - 2) + pL n)
          + (-2 * γ + 2 * γ ^ 2 * Δt) * pR n) := by
    filter_upwards [self_mem_nhdsWithin] with Δt hΔt
    have hne : Δt ≠ 0 := ne_of_gt hΔt
    field_simp [hne]
    ring
  have hlim : Tendsto (fun Δt : ℝ =>
        2 * γ ^ 2 * Δt * pR (n - 2)
          + γ * (1 - 2 * γ * Δt) * (pL (n - 2) + pL n)
          + (-2 * γ + 2 * γ ^ 2 * Δt) * pR n)
      (𝓝[>] (0 : ℝ))
      (𝓝 (γ * (pL (n - 2) + pL n) + (-2) * γ * pR n)) := by
    have hcont : Continuous (fun Δt : ℝ =>
        2 * γ ^ 2 * Δt * pR (n - 2)
          + γ * (1 - 2 * γ * Δt) * (pL (n - 2) + pL n)
          + (-2 * γ + 2 * γ ^ 2 * Δt) * pR n) := by continuity
    have hle : 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) ≤ 𝓝 (0 : ℝ) := nhdsWithin_le_nhds
    have h := (hcont.tendsto 0).mono_left hle
    have hval : (2 * γ ^ 2 * 0 * pR (n - 2)
          + γ * (1 - 2 * γ * 0) * (pL (n - 2) + pL n)
          + (-2 * γ + 2 * γ ^ 2 * 0) * pR n)
        = γ * (pL (n - 2) + pL n) + (-2) * γ * pR n := by ring
    simpa [hval] using h
  exact Tendsto.congr' hFG.symm hlim

def Pwalk (pR pL : ℤ → ℝ) (n : ℤ) : ℝ := pR n + pL (n - 1)

theorem eq22_diffusion (γ : ℝ) (pR pL : ℤ → ℝ) (n : ℤ) :
    (-2 * γ * pR n + γ * (pL (n - 2) + pL n))
        + (-2 * γ * pL (n - 1) + γ * (pR (n - 1) + pR (n + 1)))
      = γ * (Pwalk pR pL (n + 1) - 2 * Pwalk pR pL n + Pwalk pR pL (n - 1)) := by
  have h1 : n + 1 - 1 = n := by ring
  have h2 : n - 1 - 1 = n - 2 := by ring
  simp only [Pwalk, h1, h2]
  ring

theorem eq22_diffusion_expanded (γ : ℝ) (pR pL : ℤ → ℝ) (n : ℤ) :
    (-2 * γ * pR n + γ * (pL (n - 2) + pL n))
        + (-2 * γ * pL (n - 1) + γ * (pR (n - 1) + pR (n + 1)))
      = γ * ((pR (n + 1) + pL n) - 2 * (pR n + pL (n - 1))
          + (pR (n - 1) + pL (n - 2))) := by
  ring

abbrev M4 : Type := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

def kZX : M4 := pauliZ ⊗ₖ pauliX

def kZY : M4 := pauliZ ⊗ₖ pauliY

def kZZ : M4 := pauliZ ⊗ₖ pauliZ

def kXI : M4 := pauliX ⊗ₖ (1 : M2)

theorem kZX_sq : kZX * kZX = (1 : M4) := by
  unfold kZX
  rw [← Matrix.mul_kronecker_mul, pauliZ_sq, pauliX_sq, Matrix.one_kronecker_one]

theorem kZY_sq : kZY * kZY = (1 : M4) := by
  unfold kZY
  rw [← Matrix.mul_kronecker_mul, pauliZ_sq, pauliY_sq, Matrix.one_kronecker_one]

theorem kZZ_sq : kZZ * kZZ = (1 : M4) := by
  unfold kZZ
  rw [← Matrix.mul_kronecker_mul, pauliZ_sq, Matrix.one_kronecker_one]

theorem kXI_sq : kXI * kXI = (1 : M4) := by
  unfold kXI
  rw [← Matrix.mul_kronecker_mul, pauliX_sq, Matrix.one_mul, Matrix.one_kronecker_one]

def rotT4 (A : M4) (φ : ℝ) : M4 :=
  Complex.cos ((φ : ℂ)) • (1 : M4) - ((Complex.sin ((φ : ℂ)) * Complex.I) • A)

def U3 (kx ky kz θ : ℝ) : M4 :=
  rotT4 kZX (kx / 2) * rotT4 kZY (ky / 2) * rotT4 kZZ kz *
    rotT4 kZY (ky / 2) * rotT4 kZX (kx / 2) * rotT4 kXI θ

def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma sum_phase_sgn (k : ℝ) :
    (∑ b : Bool, phase (sgn b * k)) = 2 * (Real.cos k : ℂ) := by
  rw [show (Finset.univ : Finset Bool) = {false, true} from by decide,
    Finset.sum_pair (by decide)]
  simp only [sgn, Bool.false_eq_true, if_false, if_true, neg_one_mul, one_mul]
  rw [add_comm]
  exact phase_add_neg k

theorem eq25_symbol (kx ky kz : ℝ) :
    (∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
        phase (sgn a * kx + sgn b * ky + sgn c * kz))
      = ((8 : ℝ) : ℂ) * ((Real.cos kx * Real.cos ky * Real.cos kz : ℝ) : ℂ) := by
  have hsplit : ∀ a b c : Bool, phase (sgn a * kx + sgn b * ky + sgn c * kz)
      = phase (sgn a * kx) * phase (sgn b * ky) * phase (sgn c * kz) := by
    intro a b c
    rw [phase_add, phase_add]
  have hprod : ((8 : ℝ) : ℂ) * ((Real.cos kx * Real.cos ky * Real.cos kz : ℝ) : ℂ)
      = (2 * (Real.cos kx : ℂ)) * (2 * (Real.cos ky : ℂ)) * (2 * (Real.cos kz : ℂ)) := by
    push_cast
    ring
  rw [hprod, ← sum_phase_sgn kx, ← sum_phase_sgn ky, ← sum_phase_sgn kz]
  simp only [hsplit]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem eq25_symbol_scaled (γ kx ky kz : ℝ) :
    ((-γ / 4 : ℝ) : ℂ) * (∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
        phase (sgn a * kx + sgn b * ky + sgn c * kz))
      = ((-2 * γ * (Real.cos kx * Real.cos ky * Real.cos kz) : ℝ) : ℂ) := by
  rw [eq25_symbol]
  push_cast
  ring

lemma pauliX_mul_pauliY : pauliX * pauliY = Complex.I • pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul] <;> ring

lemma pauliY_mul_pauliX : pauliY * pauliX = -Complex.I • pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul] <;> ring

lemma pauliY_mul_pauliZ : pauliY * pauliZ = Complex.I • pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul] <;> ring

lemma pauliZ_mul_pauliY : pauliZ * pauliY = -Complex.I • pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul] <;> ring

lemma pauliZ_mul_pauliX : pauliZ * pauliX = Complex.I • pauliY := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul] <;> ring

lemma pauliX_mul_pauliZ : pauliX * pauliZ = -Complex.I • pauliY := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul] <;> ring

theorem kZX_anticomm_kZY : kZX * kZY + kZY * kZX = 0 := by
  unfold kZX kZY
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [pauliZ_sq, pauliX_mul_pauliY, pauliY_mul_pauliX]
  rw [Matrix.kronecker_smul, Matrix.kronecker_smul]
  rw [← add_smul]
  simp

theorem kZX_anticomm_kZZ : kZX * kZZ + kZZ * kZX = 0 := by
  unfold kZX kZZ
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [pauliZ_sq, pauliX_mul_pauliZ, pauliZ_mul_pauliX]
  rw [Matrix.kronecker_smul, Matrix.kronecker_smul]
  rw [← add_smul]
  simp

theorem kZY_anticomm_kZZ : kZY * kZZ + kZZ * kZY = 0 := by
  unfold kZY kZZ
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [pauliZ_sq, pauliY_mul_pauliZ, pauliZ_mul_pauliY]
  rw [Matrix.kronecker_smul, Matrix.kronecker_smul]
  rw [← add_smul]
  simp

theorem kZX_anticomm_kXI : kZX * kXI + kXI * kZX = 0 := by
  unfold kZX kXI
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [pauliZ_mul_pauliX, pauliX_mul_pauliZ, Matrix.mul_one, Matrix.one_mul]
  rw [Matrix.smul_kronecker, Matrix.smul_kronecker]
  rw [← add_smul]
  simp

theorem kZY_anticomm_kXI : kZY * kXI + kXI * kZY = 0 := by
  unfold kZY kXI
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [pauliZ_mul_pauliX, pauliX_mul_pauliZ, Matrix.mul_one, Matrix.one_mul]
  rw [Matrix.smul_kronecker, Matrix.smul_kronecker]
  rw [← add_smul]
  simp

theorem kZZ_anticomm_kXI : kZZ * kXI + kXI * kZZ = 0 := by
  unfold kZZ kXI
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [pauliZ_mul_pauliX, pauliX_mul_pauliZ, Matrix.mul_one, Matrix.one_mul]
  rw [Matrix.smul_kronecker, Matrix.smul_kronecker]
  rw [← add_smul]
  simp

def U3disp (kx ky kz : ℝ) : M4 :=
  rotT4 kZX (kx / 2) * rotT4 kZY (ky / 2) * rotT4 kZZ kz *
    rotT4 kZY (ky / 2) * rotT4 kZX (kx / 2)

def genE (kx ky kz : ℝ) : M4 :=
  U3disp kx ky kz * kXI * U3disp (-kx) (-ky) (-kz)

def eDel (δ : ℝ) : M4 :=
  Complex.cos ((δ : ℂ)) • (1 : M4) + ((Complex.sin ((δ : ℂ)) * Complex.I) • kXI)

lemma rotT4_zero (A : M4) : rotT4 A 0 = (1 : M4) := by
  unfold rotT4; simp [Complex.cos_zero, Complex.sin_zero]

lemma rotT4_add (A : M4) (hA : A * A = (1 : M4)) (φ ψ : ℝ) :
    rotT4 A φ * rotT4 A ψ = rotT4 A (φ + ψ) := by
  have hcos : Complex.cos (((φ + ψ : ℝ)) : ℂ)
      = Complex.cos ((φ : ℂ)) * Complex.cos ((ψ : ℂ))
        - Complex.sin ((φ : ℂ)) * Complex.sin ((ψ : ℂ)) := by
    rw [show ((φ + ψ : ℝ) : ℂ) = (φ : ℂ) + (ψ : ℂ) by push_cast; ring, Complex.cos_add]
  have hsin : Complex.sin (((φ + ψ : ℝ)) : ℂ)
      = Complex.sin ((φ : ℂ)) * Complex.cos ((ψ : ℂ))
        + Complex.cos ((φ : ℂ)) * Complex.sin ((ψ : ℂ)) := by
    rw [show ((φ + ψ : ℝ) : ℂ) = (φ : ℂ) + (ψ : ℂ) by push_cast; ring, Complex.sin_add]
  unfold rotT4
  rw [hcos, hsin, sub_mul, mul_sub, mul_sub]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hA, smul_smul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma palindrome_inv {M : Type*} [Monoid M] (a b c a' b' c' : M)
    (ha : a * a' = 1) (hb : b * b' = 1) (hc : c * c' = 1) :
    (a * b * c * b * a) * (a' * b' * c' * b' * a') = 1 := by
  grind

lemma U3disp_mul_neg (kx ky kz : ℝ) :
    U3disp kx ky kz * U3disp (-kx) (-ky) (-kz) = (1 : M4) := by
  unfold U3disp
  have ha : rotT4 kZX (kx / 2) * rotT4 kZX (-kx / 2) = (1 : M4) := by
    rw [rotT4_add kZX kZX_sq, show kx / 2 + -kx / 2 = 0 by ring, rotT4_zero]
  have hb : rotT4 kZY (ky / 2) * rotT4 kZY (-ky / 2) = (1 : M4) := by
    rw [rotT4_add kZY kZY_sq, show ky / 2 + -ky / 2 = 0 by ring, rotT4_zero]
  have hc : rotT4 kZZ kz * rotT4 kZZ (-kz) = (1 : M4) := by
    rw [rotT4_add kZZ kZZ_sq, show kz + -kz = 0 by ring, rotT4_zero]
  exact palindrome_inv _ _ _ _ _ _ ha hb hc

lemma eDel_eq_rotT4 (δ : ℝ) : eDel δ = rotT4 kXI (-δ) := by
  unfold eDel rotT4
  simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, neg_mul]
  simp

private lemma conj_five {M : Type*} [Monoid M] (d x1 x2 x3 x4 x5 : M) (hd : d * d = 1) :
    d * (x1 * x2 * x3 * x4 * x5) * d
      = (d * x1 * d) * (d * x2 * d) * (d * x3 * d) * (d * x4 * d) * (d * x5 * d) := by
  grind

lemma kXI_conj_rotT4 (A : M4) (hAD : A * kXI + kXI * A = 0) (φ : ℝ) :
    kXI * rotT4 A φ * kXI = rotT4 A (-φ) := by
  have hDA : kXI * A = -(A * kXI) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hAD
  have hDAD : kXI * A * kXI = -A := by
    calc kXI * A * kXI = (-(A * kXI)) * kXI := by rw [hDA]
      _ = -(A * kXI * kXI) := by rw [Matrix.neg_mul]
      _ = -(A * (kXI * kXI)) := by rw [Matrix.mul_assoc]
      _ = -(A * 1) := by rw [kXI_sq]
      _ = -A := by rw [Matrix.mul_one]
  unfold rotT4
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, hDAD, kXI_sq, smul_neg]
  simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, neg_mul]
  simp

lemma kXI_conj_U3disp (kx ky kz : ℝ) :
    kXI * U3disp kx ky kz * kXI = U3disp (-kx) (-ky) (-kz) := by
  unfold U3disp
  rw [conj_five kXI _ _ _ _ _ kXI_sq,
    kXI_conj_rotT4 kZX kZX_anticomm_kXI (kx / 2),
    kXI_conj_rotT4 kZY kZY_anticomm_kXI (ky / 2),
    kXI_conj_rotT4 kZZ kZZ_anticomm_kXI kz]
  simp only [neg_div]

lemma rotT4_pi_div_two (A : M4) :
    rotT4 A (Real.pi / 2) = (-Complex.I) • A := by
  unfold rotT4
  rw [show ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) / 2 by push_cast; ring,
    Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  simp

lemma eDel_zero : eDel 0 = (1 : M4) := by
  unfold eDel
  simp [Complex.cos_zero, Complex.sin_zero]

lemma rotT4_shift (δ : ℝ) :
    rotT4 kXI (Real.pi / 2 - δ) = (-Complex.I) • (kXI * eDel δ) := by
  have harg : Real.pi / 2 - δ = Real.pi / 2 + (-δ) := by ring
  rw [harg, ← rotT4_add kXI kXI_sq (Real.pi / 2) (-δ), rotT4_pi_div_two,
    ← eDel_eq_rotT4, Matrix.smul_mul]

lemma U3_eq_shift (kx ky kz δ : ℝ) :
    U3 kx ky kz (Real.pi / 2 - δ) = (-Complex.I) • (U3disp kx ky kz * kXI * eDel δ) := by
  unfold U3
  rw [rotT4_shift, Matrix.mul_smul]
  unfold U3disp
  simp only [Matrix.mul_assoc]

lemma P_e_Pneg (kx ky kz δ : ℝ) :
    U3disp kx ky kz * eDel δ * U3disp (-kx) (-ky) (-kz)
      = Complex.cos ((δ : ℂ)) • (1 : M4) +
          ((Complex.sin ((δ : ℂ)) * Complex.I) • genE kx ky kz) := by
  unfold eDel genE
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.add_mul, Matrix.smul_mul,
    U3disp_mul_neg]

lemma kXI_comm_eDel (δ : ℝ) : kXI * eDel δ = eDel δ * kXI := by
  rw [eDel_eq_rotT4]
  unfold rotT4
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, kXI_sq]

theorem U3_sq_pi_div_two (kx ky kz : ℝ) :
    U3 kx ky kz (Real.pi / 2) * U3 kx ky kz (Real.pi / 2) = -1 := by
  have h := U3_eq_shift kx ky kz 0
  rw [show Real.pi / 2 - 0 = Real.pi / 2 by ring] at h
  rw [h, eDel_zero, Matrix.mul_one]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (-Complex.I) * (-Complex.I) = (Complex.I) * Complex.I by ring, Complex.I_mul_I]
  have hPD : (U3disp kx ky kz * kXI) * (U3disp kx ky kz * kXI) = (1 : M4) := by
    calc (U3disp kx ky kz * kXI) * (U3disp kx ky kz * kXI)
        = U3disp kx ky kz * (kXI * U3disp kx ky kz * kXI) := by
          simp only [Matrix.mul_assoc]
      _ = U3disp kx ky kz * U3disp (-kx) (-ky) (-kz) := by rw [kXI_conj_U3disp]
      _ = 1 := U3disp_mul_neg kx ky kz
  rw [hPD]
  simp

theorem U3_sq_shift_expand (kx ky kz δ : ℝ) :
    U3 kx ky kz (Real.pi / 2 - δ) * U3 kx ky kz (Real.pi / 2 - δ)
      = (-1 : ℂ) •
          ((Complex.cos ((δ : ℂ)) • (1 : M4) +
              ((Complex.sin ((δ : ℂ)) * Complex.I) • genE kx ky kz)) *
           (Complex.cos ((δ : ℂ)) • (1 : M4) +
              ((Complex.sin ((δ : ℂ)) * Complex.I) • kXI))) := by
  simp only [U3_eq_shift]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (-Complex.I) * (-Complex.I) = (Complex.I) * Complex.I by ring, Complex.I_mul_I]
  congr 1
  calc (U3disp kx ky kz * kXI * eDel δ) * (U3disp kx ky kz * kXI * eDel δ)
      = U3disp kx ky kz * (kXI * eDel δ) * (U3disp kx ky kz * kXI * eDel δ) := by
        simp only [Matrix.mul_assoc]
    _ = U3disp kx ky kz * (eDel δ * kXI) * (U3disp kx ky kz * kXI * eDel δ) := by
        rw [kXI_comm_eDel]
    _ = U3disp kx ky kz * eDel δ * (kXI * U3disp kx ky kz * kXI) * eDel δ := by
        simp only [Matrix.mul_assoc]
    _ = U3disp kx ky kz * eDel δ * U3disp (-kx) (-ky) (-kz) * eDel δ := by
        rw [kXI_conj_U3disp]
    _ = (Complex.cos ((δ : ℂ)) • (1 : M4) +
          ((Complex.sin ((δ : ℂ)) * Complex.I) • genE kx ky kz)) * eDel δ := by
        rw [P_e_Pneg]
    _ = (Complex.cos ((δ : ℂ)) • (1 : M4) +
          ((Complex.sin ((δ : ℂ)) * Complex.I) • genE kx ky kz)) *
        (Complex.cos ((δ : ℂ)) • (1 : M4) +
          ((Complex.sin ((δ : ℂ)) * Complex.I) • kXI)) := by
        rfl

end Qatlib.Papers.QWalkConnect06.MainResults
