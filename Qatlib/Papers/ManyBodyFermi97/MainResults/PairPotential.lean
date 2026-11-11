/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.TensorAction

/-!
# Permutation-invariant pair-potential evolution

`pairEnergy` sums a potential over all ordered particle pairs, including equal indices. Its
permutation invariance implies that `groupEvolution` preserves antisymmetric states. Lists of
these diagonal groups define unitary circuits and schedules that retain antisymmetry after every
complete group.

The mathematical setting is that of [AbramsLloyd1997].

## Main statements

* `pairEnergy_perm`: Relabeling all particles by a permutation leaves the ordered-pair energy
  unchanged.
* `groupEvolution_antisym`: The complete pair-potential group evolution preserves antisymmetric
  states.
* `groupSchedule_antisym`: Any finite schedule of complete pair-potential groups preserves
  antisymmetric states.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.PairPotential
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

open TensorAction

/-- The total potential energy summed over all ordered pairs of particle indices, including the
diagonal pairs. -/
def pairEnergy {n m : ℕ} (v : Fin m → Fin m → ℝ) (x : Fin n → Fin m) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, v (x i) (x j)

/-- Relabeling all particles by a permutation leaves the ordered-pair energy unchanged.
[AbramsLloyd1997] -/
theorem pairEnergy_perm {n m : ℕ} (v : Fin m → Fin m → ℝ)
    (τ : Equiv.Perm (Fin n)) (x : Fin n → Fin m) :
    pairEnergy v (permCfg x τ) = pairEnergy v x := by
  simp only [pairEnergy, permCfg]
  refine Fintype.sum_equiv τ _ _ (fun i => ?_)
  exact Fintype.sum_equiv τ (fun j => v (x (τ i)) (x (τ j)))
    (fun j => v (x (τ i)) (x j)) (fun j => rfl)

/-- The diagonal evolution phases `exp(-i * t * f x)` for a real-valued energy function. -/
def phaseDiag {I : Type*} (f : I → ℝ) (t : ℝ) : I → ℂ :=
  fun x => Complex.exp (((-(t * f x) : ℝ) : ℂ) * Complex.I)

/-- Each diagonal evolution phase has norm one. -/
theorem phaseDiag_norm {I : Type*} (f : I → ℝ) (t : ℝ) (x : I) :
    ‖phaseDiag f t x‖ = 1 := by
  unfold phaseDiag
  simpa using Complex.norm_exp_ofReal_mul_I (-(t * f x))

/-- Multiplies each state amplitude pointwise by the corresponding diagonal coefficient. -/
def diagApply {I : Type*} (d : I → ℂ) (ψ : QState I) : QState I :=
  fun x => d x * ψ x

/-- Pointwise multiplication by `d` agrees with applying the diagonal matrix with entries `d`. -/
theorem diagApply_eq_applyGate {I : Type*} [Fintype I] [DecidableEq I]
    (d : I → ℂ) (ψ : QState I) :
    diagApply d ψ = ApplyGate (Matrix.diagonal d) ψ := by
  funext x
  simp only [diagApply, ApplyGate, Matrix.mulVec, Matrix.diagonal, Matrix.of_apply]
  rw [dotProduct, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

/-- A permutation-invariant diagonal multiplier commutes with the particle permutation action on
states. -/
theorem diagApply_permState {n m : ℕ} (d : (Fin n → Fin m) → ℂ)
    (hd : ∀ (τ : Equiv.Perm (Fin n)) (x : Fin n → Fin m),
      d (permCfg x τ) = d x) (τ : Equiv.Perm (Fin n))
    (ψ : QState (Fin n → Fin m)) :
    diagApply d (permState τ ψ) = permState τ (diagApply d ψ) := by
  funext x
  simp only [diagApply, permState, permCfg]
  rw [hd τ x]

/-- A permutation-invariant diagonal multiplier preserves antisymmetry of states. -/
theorem diagApply_antisym {n m : ℕ} (d : (Fin n → Fin m) → ℂ)
    (hd : ∀ (τ : Equiv.Perm (Fin n)) (x : Fin n → Fin m),
      d (permCfg x τ) = d x)
    {ψ : QState (Fin n → Fin m)} (hψ : IsAntisym ψ) :
    IsAntisym (diagApply d ψ) := by
  intro τ x
  simp only [diagApply]
  rw [hd τ x, hψ τ x]
  ring

/-- Any two diagonal multipliers commute on states. -/
theorem diagApply_commute {I : Type*} (d e : I → ℂ) (ψ : QState I) :
    diagApply d (diagApply e ψ) = diagApply e (diagApply d ψ) := by
  funext x
  simp only [diagApply]
  ring

/-- Applies the diagonal phase associated with the total ordered-pair energy. -/
def groupEvolution {n m : ℕ} (v : Fin m → Fin m → ℝ) (t : ℝ)
    (ψ : QState (Fin n → Fin m)) : QState (Fin n → Fin m) :=
  diagApply (phaseDiag (pairEnergy v) t) ψ

/-- The complete pair-potential group evolution preserves antisymmetric states.
[AbramsLloyd1997] -/
theorem groupEvolution_antisym {n m : ℕ} (v : Fin m → Fin m → ℝ) (t : ℝ)
    {ψ : QState (Fin n → Fin m)} (hψ : IsAntisym ψ) :
    IsAntisym (groupEvolution v t ψ) :=
  diagApply_antisym (phaseDiag (pairEnergy v) t)
    (fun τ x => by simp only [phaseDiag, pairEnergy_perm v τ x]) hψ

/-- The diagonal gate for the complete pair-potential group is unitary. [AbramsLloyd1997] -/
theorem groupGate_unitary {n m : ℕ} (v : Fin m → Fin m → ℝ) (t : ℝ) :
    Matrix.diagonal (fun x : Fin n → Fin m => phaseDiag (pairEnergy v) t x) ∈
      Matrix.unitaryGroup (Fin n → Fin m) ℂ :=
  diagonal_mem_unitaryGroup _ (fun x => phaseDiag_norm _ _ x)

/-- The single-gate circuit for a complete pair-potential group in the configuration basis. -/
def groupWord {n m : ℕ} (v : Fin m → Fin m → ℝ) (t : ℝ) :
    Circuit (Fin n → Fin m) := [.gate (Matrix.diagonal (fun x : Fin n → Fin m => phaseDiag (pairEnergy v) t x))]

/-- The pair-potential group circuit is unitary, has no queries, and contains one gate.
[AbramsLloyd1997] -/
theorem groupWord_correct {n m : ℕ} (v : Fin m → Fin m → ℝ) (t : ℝ) :
    IsUnitaryCircuit (groupWord (n := n) (m := m) v t) ∧
      QueryCount (groupWord (n := n) (m := m) v t) = 0 ∧
      GateCount (groupWord (n := n) (m := m) v t) = 1 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [groupWord, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
  exact groupGate_unitary v t

/-- Applies a list of pair-potential group evolutions successively using a left fold. -/
def groupSchedule {n m : ℕ} (groups : List (Fin m → Fin m → ℝ)) (t : ℝ)
    (ψ : QState (Fin n → Fin m)) : QState (Fin n → Fin m) :=
  groups.foldl (fun ψ v => groupEvolution v t ψ) ψ

/-- The circuit containing one diagonal gate for each pair-potential group in the list. -/
def groupWordList {n m : ℕ} (groups : List (Fin m → Fin m → ℝ)) (t : ℝ) :
    Circuit (Fin n → Fin m) :=
  groups.map (fun v => .gate (Matrix.diagonal (fun x : Fin n → Fin m => phaseDiag (pairEnergy v) t x)))

/-- The group circuit is unitary, has no queries, and has as many gates as the list has groups.
[AbramsLloyd1997] -/
theorem groupWordList_correct {n m : ℕ} (groups : List (Fin m → Fin m → ℝ))
    (t : ℝ) :
    IsUnitaryCircuit (groupWordList (n := n) (m := m) groups t) ∧
      QueryCount (groupWordList (n := n) (m := m) groups t) = 0 ∧
      GateCount (groupWordList (n := n) (m := m) groups t) = groups.length := by
  induction groups with
  | nil => simp [groupWordList]
  | cons v rest ih =>
    change (IsUnitaryCircuit (Step.gate (Matrix.diagonal
        (fun x : Fin n → Fin m => phaseDiag (pairEnergy v) t x)) ::
        groupWordList (n := n) (m := m) rest t) ∧
      QueryCount (Step.gate (Matrix.diagonal
        (fun x : Fin n → Fin m => phaseDiag (pairEnergy v) t x)) ::
        groupWordList (n := n) (m := m) rest t) = 0 ∧
      GateCount (Step.gate (Matrix.diagonal
        (fun x : Fin n → Fin m => phaseDiag (pairEnergy v) t x)) ::
        groupWordList (n := n) (m := m) rest t) = (v :: rest).length)
    refine ⟨?_, ?_, ?_⟩
    · simp only [isUnitaryCircuit_gate]
      exact ⟨groupGate_unitary v t, ih.1⟩
    · simp [ih.2.1]
    · simp [ih.2.2]

/-- Running the group circuit agrees with the successive group evolutions in `groupSchedule`.
[AbramsLloyd1997] -/
theorem groupSchedule_eq_fold {n m : ℕ} (groups : List (Fin m → Fin m → ℝ))
    (t : ℝ) (ψ : QState (Fin n → Fin m)) :
    Run 1 (groupWordList (n := n) (m := m) groups t) ψ =
      groupSchedule (n := n) (m := m) groups t ψ := by
  induction groups generalizing ψ with
  | nil => simp [groupWordList, groupSchedule]
  | cons v rest ih =>
    change Run 1 (Step.gate (Matrix.diagonal
        (fun x : Fin n → Fin m => phaseDiag (pairEnergy v) t x)) ::
        groupWordList (n := n) (m := m) rest t) ψ
      = groupSchedule (n := n) (m := m) (v :: rest) t ψ
    rw [show groupSchedule (n := n) (m := m) (v :: rest) t ψ
        = groupSchedule (n := n) (m := m) rest t (groupEvolution v t ψ) from rfl]
    simp only [Run]
    rw [ih]
    congr 1
    simp [ApplyGate, diagApply_eq_applyGate, groupEvolution]

/-- Any finite schedule of complete pair-potential groups preserves antisymmetric states.
[AbramsLloyd1997] -/
theorem groupSchedule_antisym {n m : ℕ} (groups : List (Fin m → Fin m → ℝ))
    (t : ℝ) {ψ : QState (Fin n → Fin m)} (hψ : IsAntisym ψ) :
    IsAntisym (groupSchedule groups t ψ) := by
  induction groups generalizing ψ with
  | nil => exact hψ
  | cons v rest ih => exact ih (groupEvolution_antisym v t hψ)

end Qatlib.Papers.ManyBodyFermi97.MainResults.PairPotential
