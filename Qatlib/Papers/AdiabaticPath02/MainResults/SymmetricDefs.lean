/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticPath02.MainResults.PathDefs
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticPath02.MainResults.SymmetricDefs

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AdiabaticPath02.MainResults.PathDefs
open scoped BigOperators Matrix

def Jz (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun k => (n : ℝ) / 2 - (k.val : ℝ))

def Jplus (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of (fun k l =>
    if k.val + 1 = l.val then Real.sqrt ((l.val : ℝ) * ((n : ℝ) - (l.val : ℝ) + 1))
    else 0)

def Jx (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (1 / 2 : ℝ) • (Jplus n + (Jplus n)ᵀ)

theorem Jx_isSymm (n : ℕ) : (Jx n).IsSymm := by
  unfold Jx
  exact (Matrix.isSymm_add_transpose_self (Jplus n)).smul _

theorem Jz_isSymm (n : ℕ) : (Jz n).IsSymm := by
  unfold Jz
  exact Matrix.isSymm_diagonal _

def symHP (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun k => hpEnergy (n : ℝ) (k.val : ℝ))

def symHB (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  ((Nat.choose (n - 1) 2 : ℝ)) • (((n : ℝ) / 2) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - Jx n)

def symHE (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (-2 * (n : ℝ)) • ((Jx n * Jz n) + (Jx n * Jz n)ᵀ)

theorem symHP_isSymm (n : ℕ) : (symHP n).IsSymm := by
  unfold symHP
  exact Matrix.isSymm_diagonal _

theorem symHB_isSymm (n : ℕ) : (symHB n).IsSymm := by
  unfold symHB
  exact ((Matrix.isSymm_one.smul _).sub (Jx_isSymm n)).smul _

theorem symHE_isSymm (n : ℕ) : (symHE n).IsSymm := by
  unfold symHE
  exact (Matrix.isSymm_add_transpose_self (Jx n * Jz n)).smul _

def symH (n : ℕ) (s : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (1 - s) • symHB n + s • symHP n + (s * (1 - s)) • symHE n

@[simp] theorem symH_zero (n : ℕ) : symH n 0 = symHB n := by
  simp [symH]

@[simp] theorem symH_one (n : ℕ) : symH n 1 = symHP n := by
  simp [symH]

theorem symH_isSymm (n : ℕ) (s : ℝ) : (symH n s).IsSymm := by
  unfold symH
  have h1 : ((1 - s) • symHB n).IsSymm := (symHB_isSymm n).smul _
  have h2 : (s • symHP n).IsSymm := (symHP_isSymm n).smul _
  have h3 : ((s * (1 - s)) • symHE n).IsSymm := (symHE_isSymm n).smul _
  exact (h1.add h2).add h3

def toOperator {D : ℕ} (A : Matrix (Fin D) (Fin D) ℝ) : Operator D :=
  A.map Complex.ofReal

theorem toOperator_isHermitian {D : ℕ} {A : Matrix (Fin D) (Fin D) ℝ}
    (hA : A.IsSymm) : (toOperator A).IsHermitian := by
  ext i j
  simp [toOperator, Matrix.conjTranspose_apply, Matrix.map_apply, hA.apply i j,
    Complex.conj_ofReal]

def p2H (n : ℕ) (s : ℝ) : Operator (n + 1) :=
  toOperator (symH n s)

theorem p2H_isHermitian (n : ℕ) (s : ℝ) : (p2H n s).IsHermitian :=
  toOperator_isHermitian (symH_isSymm n s)

theorem p2H_continuous (n : ℕ) : Continuous (fun s : ℝ => p2H n s) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h : (fun s : ℝ => p2H n s i j) =
      fun s =>
        (((1 - s) * (symHB n) i j + s * (symHP n) i j +
          (s * (1 - s)) * (symHE n) i j : ℝ) : ℂ) := by
    funext s
    simp [p2H, symH, toOperator, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [h]
  fun_prop

def overlap {D : ℕ} (φ ψ : Fin D → ℂ) : ℂ := ∑ i, star (φ i) * ψ i

def fidelity {D : ℕ} (φ ψ : Fin D → ℂ) : ℝ := Complex.normSq (overlap φ ψ)

def hpGroundVec (n : ℕ) : Fin (n + 1) → ℂ :=
  fun k => if k.val = 0 then 1 else 0

def plusXVec (n : ℕ) : Fin (n + 1) → ℂ :=
  fun k => ((Real.sqrt (Nat.choose n k.val : ℝ) / (Real.sqrt 2) ^ n : ℝ) : ℂ)

def evolutionOperator {D : ℕ} (H : ℝ → Operator D) (T : ℝ) : Operator D :=
  Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
    (fun t => Complex.I • H t) 0 T

def p2Scheduled (n : ℕ) (T : ℝ) : ℝ → Operator (n + 1) :=
  fun t => p2H n (t / T)

def p2Fidelity (n : ℕ) (T : ℕ) : ℝ :=
  fidelity (hpGroundVec n)
    (evolutionOperator (p2Scheduled n (T : ℝ)) (T : ℝ) *ᵥ plusXVec n)

def straightH (n : ℕ) (s : ℝ) : Operator (n + 1) :=
  toOperator ((1 - s) • symHB n + s • symHP n)

def straightFidelity (n : ℕ) (T : ℕ) : ℝ :=
  fidelity (hpGroundVec n)
    (evolutionOperator (fun t => straightH n (t / (T : ℝ))) (T : ℝ) *ᵥ plusXVec n)

theorem p2Scheduled_continuous (n : ℕ) (T : ℝ) : Continuous (p2Scheduled n T) := by
  unfold p2Scheduled
  exact (p2H_continuous n).comp (by fun_prop : Continuous fun t : ℝ => t / T)

theorem p2Scheduled_isHermitian (n : ℕ) (T : ℝ) (t : ℝ) :
    (p2Scheduled n T t).IsHermitian := by
  unfold p2Scheduled
  exact p2H_isHermitian n (t/T)

theorem evolutionOperator_unitary (n : ℕ) (T : ℝ) :
    evolutionOperator (p2Scheduled n T) T ∈ unitaryGroup (Fin (n+1)) ℂ := by
  unfold evolutionOperator
  exact Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.ordered_evolution_hermitian_unitary
    (Fin (n+1)) (p2Scheduled n T) (p2Scheduled_continuous n T)
    (p2Scheduled_isHermitian n T) 0 T

def IsPolynomialBound (T : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, 0 < C ∧ ∀ n : ℕ, T n ≤ C * (n + 1) ^ d

theorem isPolynomialBound_zero : IsPolynomialBound (fun _ => 0) :=
  ⟨1, 0, by norm_num, fun n => by simp⟩

end Qatlib.Papers.AdiabaticPath02.MainResults.SymmetricDefs
