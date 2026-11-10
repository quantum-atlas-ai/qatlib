/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Basic.Unique
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

namespace Qatlib.Papers.StateTransfer03.MainResults.Defs

open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

noncomputable section

def pathAdj (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

def complexify {m n : Type*} (A : Matrix m n ℝ) : Matrix m n ℂ :=
  A.map Complex.ofReal

def propagator {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  NormedSpace.exp (-(Complex.I * (t : ℂ)) • A)

def amplitude {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (a b : n) (t : ℝ) : ℂ :=
  propagator A t b a

def PerfectTransfer {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (a b : n) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ‖amplitude A a b t‖ = 1

def chainFirst (N : ℕ) (hN : 0 < N) : Fin N := ⟨0, hN⟩

def chainLast (N : ℕ) (hN : 0 < N) : Fin N :=
  ⟨N - 1, Nat.sub_lt hN (by decide : (0 : ℕ) < 1)⟩

def phase (E t : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (t : ℂ) * (E : ℂ)))

def pathEigenvalue (N : ℕ) (k : Fin N) : ℝ :=
  2 * Real.cos (((k.val : ℝ) + 1) * Real.pi / ((N : ℝ) + 1))

def pathWeight (N : ℕ) (k : Fin N) : ℝ :=
  (2 / ((N : ℝ) + 1)) *
    Real.sin (((k.val : ℝ) + 1) * Real.pi / ((N : ℝ) + 1)) *
      Real.sin (((k.val : ℝ) + 1) * (N : ℝ) * Real.pi / ((N : ℝ) + 1))

def spectralAmplitude {ι : Type*} [Fintype ι] (E : ι → ℝ) (u : ι → ℂ)
    (t : ℝ) : ℂ :=
  ∑ k, u k * phase (E k) t

def SpectralPerfectTransfer {ι : Type*} [Fintype ι] (E : ι → ℝ) (u : ι → ℂ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ‖spectralAmplitude E u t‖ = 1

def pathSpectralAmplitude (N : ℕ) (t : ℝ) : ℂ :=
  spectralAmplitude (pathEigenvalue N) (fun k => (pathWeight N k : ℂ)) t

def productEigenvalue {ι κ : Type*} (E : ι → ℝ) (F : κ → ℝ) (p : ι × κ) : ℝ :=
  E p.1 + F p.2

def productWeight {ι κ : Type*} (u : ι → ℂ) (v : κ → ℂ) (p : ι × κ) : ℂ :=
  u p.1 * v p.2

def powerEigenvalue {ι : Type*} (E : ι → ℝ) : ∀ d : ℕ, (Fin d → ι) → ℝ
  | 0, _ => 0
  | _ + 1, p => E (p 0) + powerEigenvalue E _ (fun i => p i.succ)

def powerWeight {ι : Type*} (u : ι → ℂ) : ∀ d : ℕ, (Fin d → ι) → ℂ
  | 0, _ => 1
  | _ + 1, p => u (p 0) * powerWeight u _ (fun i => p i.succ)

theorem spectralAmplitude_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → ℝ) (u : ι → ℂ) (F : κ → ℝ) (v : κ → ℂ) (t : ℝ) :
    spectralAmplitude (productEigenvalue E F) (productWeight u v) t =
      spectralAmplitude E u t * spectralAmplitude F v t := by
  simp only [spectralAmplitude, productEigenvalue, productWeight, phase,
    Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  have harg :
      -(Complex.I * (t : ℂ) * ((E k + F l : ℝ) : ℂ)) =
        -(Complex.I * (t : ℂ) * ((E k : ℝ) : ℂ)) +
          -(Complex.I * (t : ℂ) * ((F l : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]
  ring

theorem powerAmplitude_succ {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (u : ι → ℂ) (d : ℕ) (t : ℝ) :
    spectralAmplitude (powerEigenvalue E (d + 1)) (powerWeight u (d + 1)) t =
      spectralAmplitude (productEigenvalue E (powerEigenvalue E d))
        (productWeight u (powerWeight u d)) t := by
  have hL : (∑ p : Fin (d + 1) → ι,
      powerWeight u (d + 1) p * phase (powerEigenvalue E (d + 1) p) t)
      = ∑ x : ι, ∑ y : Fin d → ι,
          (u x * powerWeight u d (fun i => y i)) *
            phase (E x + powerEigenvalue E d (fun i => y i)) t := by
    rw [← (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => ι))
      (fun p : Fin (d + 1) → ι =>
        powerWeight u (d + 1) p * phase (powerEigenvalue E (d + 1) p) t))]
    rw [Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, powerEigenvalue, powerWeight,
      Fin.cons_zero, Fin.cons_succ]
  rw [spectralAmplitude, hL]
  rw [spectralAmplitude_prod (E := E) (u := u)
    (F := powerEigenvalue E d) (v := powerWeight u d)]
  change (∑ x : ι, ∑ y : Fin d → ι,
      (u x * powerWeight u d (fun i => y i)) *
        phase (E x + powerEigenvalue E d (fun i => y i)) t)
    = (∑ k, u k * phase (E k) t) *
        (∑ p, powerWeight u d p * phase (powerEigenvalue E d p) t)
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  refine Finset.sum_congr rfl ?_
  intro y _
  have harg :
      -(Complex.I * (t : ℂ) * (((E x + powerEigenvalue E d y : ℝ)) : ℂ)) =
        -(Complex.I * (t : ℂ) * ((E x : ℝ) : ℂ)) +
          -(Complex.I * (t : ℂ) * ((powerEigenvalue E d y : ℝ) : ℂ)) := by
    push_cast
    ring
  simp only [phase, harg, Complex.exp_add]
  ring

theorem spectralAmplitude_pow {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (u : ι → ℂ) (d : ℕ) (t : ℝ) :
    spectralAmplitude (powerEigenvalue E d) (powerWeight u d) t =
      spectralAmplitude E u t ^ d := by
  induction d with
  | zero =>
      rw [spectralAmplitude]
      rw [Fintype.sum_eq_single (fun i : Fin 0 => Fin.elim0 i)]
      · simp [powerWeight, powerEigenvalue, phase]
      · intro x hx
        exact (hx (Subsingleton.elim x (fun i : Fin 0 => Fin.elim0 i))).elim
  | succ d ih =>
      rw [powerAmplitude_succ E u d t]
      rw [spectralAmplitude_prod (E := E) (u := u)
        (F := powerEigenvalue E d) (v := powerWeight u d)]
      rw [ih]
      ring

end

end Qatlib.Papers.StateTransfer03.MainResults.Defs
