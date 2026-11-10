/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

namespace Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

open Matrix
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

variable {n : ℕ}

inductive LocalQFTGate (n : ℕ) where
  | h : Fin n → LocalQFTGate n
  | cp : Fin n → Fin n → ℕ → Bool → LocalQFTGate n
  | swap : Fin n → Fin n → LocalQFTGate n
  deriving DecidableEq, Repr

noncomputable def dyadicPhaseAngle (k : ℕ) (neg : Bool) : ℝ :=
  if neg then -(2 * Real.pi / (2 ^ k : ℝ)) else 2 * Real.pi / (2 ^ k : ℝ)

noncomputable def localGateMatrix {n : ℕ} : LocalQFTGate n → Matrix (Reg n) (Reg n) ℂ
  | .h a => Matrix.of fun x y =>
      if ∀ k : Fin n, k ≠ a → x k = y k then Hadamard (x a) (y a) else 0
  | .cp a c k neg => Matrix.diagonal fun x =>
      if x a && x c then Complex.exp (dyadicPhaseAngle k neg * Complex.I) else 1
  | .swap a c => permMatrix (fun w => fun i => w (Equiv.swap a c i))

theorem hadamard_entry_star (p q : Bool) : (starRingEnd ℂ) (Hadamard p q) = Hadamard p q := by
  simp only [Hadamard, Matrix.of_apply, map_mul, map_inv₀, Complex.conj_ofReal]
  split_ifs <;> simp

theorem hadamard_entry_symm (p q : Bool) : Hadamard p q = Hadamard q p := by
  simp only [Hadamard, Matrix.of_apply, Bool.and_comm]

@[simp] theorem localGateMatrix_h (n : ℕ) (a : Fin n) (x y : Reg n) :
    localGateMatrix (.h a) x y =
      if ∀ k : Fin n, k ≠ a → x k = y k then Hadamard (x a) (y a) else 0 := rfl

@[simp] theorem localGateMatrix_cp (n : ℕ) (a c : Fin n) (k : ℕ) (neg : Bool) (x y : Reg n) :
    localGateMatrix (.cp a c k neg) x y = if x = y then
      (if x a && x c then Complex.exp (dyadicPhaseAngle k neg * Complex.I) else 1) else 0 := by
  simp only [localGateMatrix, Matrix.diagonal_apply]

@[simp] theorem localGateMatrix_swap (n : ℕ) (a c : Fin n) (x y : Reg n) :
    localGateMatrix (.swap a c) x y =
      if x = (fun k => y (Equiv.swap a c k)) then 1 else 0 := rfl

theorem localGateMatrix_h_star (n : ℕ) (a : Fin n) :
    (localGateMatrix (.h a))ᴴ = localGateMatrix (.h a) := by
  ext x y
  show (starRingEnd ℂ) (localGateMatrix (.h a) y x) = localGateMatrix (.h a) x y
  by_cases hP : ∀ k : Fin n, k ≠ a → y k = x k
  · rw [localGateMatrix_h, if_pos hP, localGateMatrix_h, if_pos (fun k hk => (hP k hk).symm),
      hadamard_entry_star (y a) (x a), hadamard_entry_symm (y a) (x a)]
  · rw [localGateMatrix_h, if_neg hP, localGateMatrix_h,
      if_neg (fun hQ => hP (fun k hk => (hQ k hk).symm))]
    simp

private theorem star_exp_mul_I (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) = Complex.exp ((-θ) * Complex.I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  ring

theorem dyadicPhaseAngle_neg (k : ℕ) (neg : Bool) :
    dyadicPhaseAngle k (!neg) = -dyadicPhaseAngle k neg := by
  cases neg <;> simp [dyadicPhaseAngle]

private theorem star_dyadicPhaseAngle (k : ℕ) (neg : Bool) :
    (starRingEnd ℂ) (Complex.exp (dyadicPhaseAngle k neg * Complex.I))
      = Complex.exp (dyadicPhaseAngle k (!neg) * Complex.I) := by
  rw [star_exp_mul_I, dyadicPhaseAngle_neg]
  congr 1
  push_cast
  ring

theorem localGateMatrix_cp_star (n : ℕ) (a c : Fin n) (k : ℕ) (neg : Bool) :
    (localGateMatrix (.cp a c k neg))ᴴ = localGateMatrix (.cp a c k (!neg)) := by
  have hpoint : ∀ x : Reg n, (starRingEnd ℂ)
      (if x a && x c then Complex.exp (dyadicPhaseAngle k neg * Complex.I) else 1)
      = if x a && x c then Complex.exp (dyadicPhaseAngle k (!neg) * Complex.I) else 1 := by
    intro x
    by_cases hc : x a && x c
    · rw [if_pos hc, if_pos hc, star_dyadicPhaseAngle]
    · rw [if_neg hc, if_neg hc, map_one]
  unfold localGateMatrix
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  exact funext hpoint

theorem localGateMatrix_swap_involutive (n : ℕ) (a c : Fin n) :
    Function.Involutive (fun w : Reg n => fun i => w (Equiv.swap a c i)) := by
  intro w
  funext i
  simp [Equiv.swap, Equiv.swapCore_swapCore]

theorem localGateMatrix_swap_unitary (n : ℕ) (a c : Fin n) :
    localGateMatrix (.swap a c) ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  permMatrix_unitary (localGateMatrix_swap_involutive n a c)

private theorem star_h_entry (n : ℕ) (a : Fin n) (z x : Reg n) :
    (starRingEnd ℂ) (localGateMatrix (.h a) z x)
      = if ∀ k : Fin n, k ≠ a → z k = x k then Hadamard (x a) (z a) else 0 := by
  rw [localGateMatrix_h]
  by_cases h : ∀ k : Fin n, k ≠ a → z k = x k
  · rw [if_pos h, if_pos h, hadamard_entry_star (z a) (x a), hadamard_entry_symm (z a) (x a)]
  · rw [if_neg h, if_neg h, map_zero]

private theorem two_hadamard_terms (n : ℕ) (x y : Reg n) (a : Fin n) :
    Hadamard (x a) (x a) * Hadamard (x a) (y a)
      + Hadamard (x a) (!x a) * Hadamard (!x a) (y a)
      = (Hadamard * Hadamard) (x a) (y a) := by
  rw [Matrix.mul_apply]
  cases x a <;> simp [add_comm]

private def hFlip (n : ℕ) (a : Fin n) (x : Reg n) : Reg n := fun k => if k = a then !x k else x k

private theorem hFlip_apply_self (n : ℕ) (a : Fin n) (x : Reg n) :
    hFlip n a x a = !x a := by
  show (if a = a then !x a else x a) = !x a
  rw [if_pos rfl]

private theorem hFlip_apply_of_ne (n : ℕ) (a : Fin n) (x : Reg n) (k : Fin n) (h : k ≠ a) :
    hFlip n a x k = x k := by
  show (if k = a then !x k else x k) = x k
  rw [if_neg h]

private theorem h_support_iff (n : ℕ) (a : Fin n) (x : Reg n) (z : Reg n) :
    (∀ k : Fin n, k ≠ a → z k = x k) ↔ z = x ∨ z = hFlip n a x := by
  constructor
  · intro h
    cases zk : z a <;> cases xk : x a
    · left
      funext k
      by_cases hka : k = a
      · simp [hka, zk, xk]
      · simp [h k hka]
    · right
      funext k
      by_cases hka : k = a
      · simp [hFlip, hka, zk, xk]
      · simp [hFlip, hka, h k hka]
    · right
      funext k
      by_cases hka : k = a
      · simp [hFlip, hka, zk, xk]
      · simp [hFlip, hka, h k hka]
    · left
      funext k
      by_cases hka : k = a
      · simp [hka, zk, xk]
      · simp [h k hka]
  · intro h
    rcases h with h | h
    · subst h; intro k _; rfl
    · subst h; intro k hk
      show hFlip n a x k = x k
      exact hFlip_apply_of_ne n a x k hk

private theorem h_support_sum (n : ℕ) (a : Fin n) (x y : Reg n) :
    (∑ z : Reg n, if ∀ k : Fin n, k ≠ a → z k = x k then
        Hadamard (x a) (z a) * Hadamard (z a) (y a) else 0)
      = (Hadamard * Hadamard) (x a) (y a) := by
  have hSeq : (Finset.univ.filter (fun z : Reg n => ∀ k : Fin n, k ≠ a → z k = x k)
      : Finset (Reg n)) = {x, hFlip n a x} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact (h_support_iff n a x z)
  have hne : x ≠ hFlip n a x := by
    intro h
    have h1 : x a = !x a := by
      have h2 : x a = hFlip n a x a := congrFun h a
      rw [hFlip_apply_self] at h2
      exact h2
    cases hx : x a <;> simp at h1
  calc (∑ z : Reg n, if ∀ k : Fin n, k ≠ a → z k = x k then
        Hadamard (x a) (z a) * Hadamard (z a) (y a) else 0)
      = ∑ z ∈ (Finset.univ.filter (fun z : Reg n => ∀ k : Fin n, k ≠ a → z k = x k)
          : Finset (Reg n)), Hadamard (x a) (z a) * Hadamard (z a) (y a) :=
        (Finset.sum_filter (fun z : Reg n => ∀ k : Fin n, k ≠ a → z k = x k)
          (fun z : Reg n => Hadamard (x a) (z a) * Hadamard (z a) (y a))).symm
    _ = ∑ z ∈ ({x, hFlip n a x} : Finset (Reg n)),
        Hadamard (x a) (z a) * Hadamard (z a) (y a) := by rw [hSeq]
    _ = Hadamard (x a) (x a) * Hadamard (x a) (y a)
        + Hadamard (x a) (!x a) * Hadamard (!x a) (y a) := by
      calc (∑ z ∈ ({x, hFlip n a x} : Finset (Reg n)),
            Hadamard (x a) (z a) * Hadamard (z a) (y a))
          = Hadamard (x a) (x a) * Hadamard (x a) (y a)
              + Hadamard (x a) (hFlip n a x a) * Hadamard (hFlip n a x a) (y a) :=
            Finset.sum_pair hne
        _ = _ := by rw [hFlip_apply_self]
    _ = (Hadamard * Hadamard) (x a) (y a) := two_hadamard_terms n x y a

theorem localGateMatrix_h_unitary (n : ℕ) (a : Fin n) :
    localGateMatrix (.h a) ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Matrix.one_apply]
  by_cases hgood : ∀ k : Fin n, k ≠ a → x k = y k
  · have hxy : (x a = y a) ↔ x = y := by
      constructor
      · intro h
        funext k
        by_cases hka : k = a
        · simpa [hka] using h
        · exact hgood k hka
      · intro h
        have := congrFun h a
        simpa using this
    have key : ∀ z : Reg n,
        (starRingEnd ℂ) (localGateMatrix (.h a) z x) * localGateMatrix (.h a) z y
          = if ∀ k : Fin n, k ≠ a → z k = x k then
              Hadamard (x a) (z a) * Hadamard (z a) (y a) else 0 := by
      intro z
      rw [star_h_entry, localGateMatrix_h]
      by_cases hz : ∀ k : Fin n, k ≠ a → z k = x k
      · rw [if_pos hz, if_pos (fun k hk => by rw [hz k hk, hgood k hk]), if_pos hz]
      · rw [if_neg hz, if_neg (fun hzy => hz (fun k hk => (hzy k hk).trans (hgood k hk).symm)),
          if_neg hz]
        simp
    rw [Finset.sum_congr rfl (fun z _ => key z), h_support_sum, hadamard_mul_self,
      Matrix.one_apply]
    by_cases hxy' : x = y
    · simp [hxy']
    · have hne : ¬(x a = y a) := fun h => hxy' (funext fun k => by
        by_cases hka : k = a
        · simpa [hka] using h
        · exact hgood k hka)
      rw [if_neg hne, if_neg hxy']
  · have hne : x ≠ y := fun hxy => hgood (fun k hk => by rw [hxy])
    have hzero : (∑ z : Reg n, (starRingEnd ℂ) (localGateMatrix (.h a) z x)
        * localGateMatrix (.h a) z y) = 0 := by
      refine Finset.sum_eq_zero (s := (Finset.univ : Finset (Reg n))) (fun z _ => ?_)
      by_cases hz : ∀ k : Fin n, k ≠ a → z k = x k
      · have hz' : ¬(∀ k : Fin n, k ≠ a → z k = y k) := by
          intro hzy
          obtain ⟨k, hka, hk⟩ : ∃ k, k ≠ a ∧ ¬(x k = y k) := by
            by_contra hc
            refine hgood ?_
            intro k hka
            by_contra hn
            exact hc ⟨k, hka, hn⟩
          have h1 := hzy k hka
          have h2 := hz k hka
          exact hk (h2.symm.trans h1)
        rw [star_h_entry, if_pos hz, localGateMatrix_h, if_neg hz']
        simp
      · rw [star_h_entry, if_neg hz, zero_mul]
    rw [hzero, if_neg hne]

theorem localGateMatrix_cp_unitary (n : ℕ) (a c : Fin n) (k : ℕ) (neg : Bool) :
    localGateMatrix (.cp a c k neg) ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, localGateMatrix_cp_star]
  simp only [localGateMatrix]
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  show (if x a && x c then Complex.exp (dyadicPhaseAngle k (!neg) * Complex.I) else 1)
    * (if x a && x c then Complex.exp (dyadicPhaseAngle k neg * Complex.I) else 1) = 1
  by_cases h : x a && x c
  · rw [if_pos h, if_pos h, ← star_dyadicPhaseAngle k neg,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  · rw [if_neg h, if_neg h, mul_one]

theorem localGateMatrix_unitary {n : ℕ} (g : LocalQFTGate n) :
    localGateMatrix g ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  cases g with
  | h a => exact localGateMatrix_h_unitary n a
  | cp a c k neg => exact localGateMatrix_cp_unitary n a c k neg
  | swap a c => exact localGateMatrix_swap_unitary n a c

theorem localDyadicGate_semantics_and_unitary (n : ℕ) :
    (∀ (a : Fin n) (x y : Reg n), localGateMatrix (.h a) x y =
      if ∀ k : Fin n, k ≠ a → x k = y k then Hadamard (x a) (y a) else 0) ∧
    (∀ (a c : Fin n) (k : ℕ) (neg : Bool) (x y : Reg n),
      localGateMatrix (.cp a c k neg) x y = if x = y then
        (if x a && x c then Complex.exp
          (((if neg then -(2 * Real.pi / (2 ^ k : ℝ)) else 2 * Real.pi / (2 ^ k : ℝ)) : ℝ)
            * Complex.I)
        else 1) else 0) ∧
    (∀ (a c : Fin n) (x y : Reg n), localGateMatrix (.swap a c) x y =
      if x = (fun k => y (Equiv.swap a c k)) then 1 else 0) ∧
    (∀ g : LocalQFTGate n, localGateMatrix g ∈ Matrix.unitaryGroup (Reg n) ℂ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a x y
    exact localGateMatrix_h n a x y
  · intro a c k neg x y
    show localGateMatrix (.cp a c k neg) x y = if x = y then
      (if x a && x c then Complex.exp (dyadicPhaseAngle k neg * Complex.I) else 1) else 0
    exact localGateMatrix_cp n a c k neg x y
  · intro a c x y
    exact localGateMatrix_swap n a c x y
  · intro g
    exact localGateMatrix_unitary g

def localGateAdjoint : {n : ℕ} → LocalQFTGate n → LocalQFTGate n
  | _, .h a => .h a
  | _, .cp a c k neg => .cp a c k (!neg)
  | _, .swap a c => .swap a c

@[simp] theorem localGateAdjoint_h (a : Fin n) : localGateAdjoint (.h a) = .h a := rfl

@[simp] theorem localGateAdjoint_cp (a c : Fin n) (k : ℕ) (neg : Bool) :
    localGateAdjoint (.cp a c k neg) = .cp a c k (!neg) := rfl

@[simp] theorem localGateAdjoint_swap (a c : Fin n) : localGateAdjoint (.swap a c) = .swap a c := rfl

@[simp] theorem localGateAdjoint_involutive {n : ℕ} (g : LocalQFTGate n) :
    localGateAdjoint (localGateAdjoint g) = g := by
  cases g <;> simp

theorem localGateMatrix_localGateAdjoint {n : ℕ} (g : LocalQFTGate n) :
    localGateMatrix (localGateAdjoint g) = (localGateMatrix g)ᴴ := by
  cases g with
  | h a => rw [localGateAdjoint, localGateMatrix_h_star]
  | cp a c k neg => rw [localGateAdjoint, localGateMatrix_cp_star n a c k neg]
  | swap a c =>
    rw [localGateAdjoint, localGateMatrix,
      permMatrix_conjTranspose (localGateMatrix_swap_involutive n a c)]

def localProgramAdjoint {n : ℕ} (gs : List (LocalQFTGate n)) : List (LocalQFTGate n) :=
  gs.reverse.map localGateAdjoint

@[simp] theorem localProgramAdjoint_nil (n : ℕ) :
    localProgramAdjoint ([] : List (LocalQFTGate n)) = [] := rfl

theorem localProgramAdjoint_cons {n : ℕ} (g : LocalQFTGate n) (gs : List (LocalQFTGate n)) :
    localProgramAdjoint (g :: gs) = localProgramAdjoint gs ++ [localGateAdjoint g] := by
  simp [localProgramAdjoint]

@[simp] theorem localProgramAdjoint_involutive {n : ℕ} (gs : List (LocalQFTGate n)) :
    localProgramAdjoint (localProgramAdjoint gs) = gs := by
  simp [localProgramAdjoint, Function.comp_def]

noncomputable def localProgramCircuit {n : ℕ} (gs : List (LocalQFTGate n)) : Circuit (Reg n) :=
  gs.map (fun g => Step.gate (localGateMatrix g))

@[simp] theorem localProgramCircuit_nil (n : ℕ) :
    localProgramCircuit ([] : List (LocalQFTGate n)) = [] := rfl

@[simp] theorem localProgramCircuit_cons {n : ℕ} (g : LocalQFTGate n) (gs : List (LocalQFTGate n)) :
    localProgramCircuit (g :: gs) = Step.gate (localGateMatrix g) :: localProgramCircuit gs := rfl

theorem localProgramCircuit_append {n : ℕ} (gs ds : List (LocalQFTGate n)) :
    localProgramCircuit (gs ++ ds) = localProgramCircuit gs ++ localProgramCircuit ds := by
  show (gs ++ ds).map (fun g => Step.gate (localGateMatrix g))
      = (gs.map (fun g => Step.gate (localGateMatrix g)))
        ++ (ds.map (fun g => Step.gate (localGateMatrix g)))
  exact List.map_append

noncomputable def localProgramMatrix {n : ℕ} : List (LocalQFTGate n) → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | g :: gs => localProgramMatrix gs * localGateMatrix g

@[simp] theorem localProgramMatrix_nil (n : ℕ) :
    localProgramMatrix ([] : List (LocalQFTGate n)) = 1 := rfl

@[simp] theorem localProgramMatrix_cons {n : ℕ} (g : LocalQFTGate n) (gs : List (LocalQFTGate n)) :
    localProgramMatrix (g :: gs) = localProgramMatrix gs * localGateMatrix g := rfl

theorem localProgramMatrix_eq_reverse_prod {n : ℕ} (gs : List (LocalQFTGate n)) :
    localProgramMatrix gs = (gs.reverse.map localGateMatrix).prod := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [localProgramMatrix_cons, ih, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one]

theorem localProgramMatrix_append {n : ℕ} (gs ds : List (LocalQFTGate n)) :
    localProgramMatrix (gs ++ ds) = localProgramMatrix ds * localProgramMatrix gs := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp [localProgramMatrix, ih, mul_assoc]

theorem localDyadicProgram_run_adjoint_cost (n : ℕ) (gs : List (LocalQFTGate n))
    (ψ : QState (Reg n)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (localProgramCircuit gs) ψ =
      ApplyGate (localProgramMatrix gs) ψ ∧
    localProgramMatrix (localProgramAdjoint gs) = (localProgramMatrix gs)ᴴ ∧
    localProgramAdjoint (localProgramAdjoint gs) = gs ∧
    IsUnitaryCircuit (localProgramCircuit gs) ∧
    localProgramMatrix gs ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
    QueryCount (localProgramCircuit gs) = 0 ∧
    GateCount (localProgramCircuit gs) = gs.length ∧
    GateCount (localProgramCircuit (localProgramAdjoint gs)) = gs.length ∧
    (∀ g : LocalQFTGate n, localGateMatrix (localGateAdjoint g) = (localGateMatrix g)ᴴ) := by
  have run : ∀ (gs : List (LocalQFTGate n)) (ψ : QState (Reg n)),
      Run (1 : Matrix (Reg n) (Reg n) ℂ) (localProgramCircuit gs) ψ =
        ApplyGate (localProgramMatrix gs) ψ := by
    intro gs
    induction gs with
    | nil =>
      intro _
      simp [localProgramCircuit, localProgramMatrix]
    | cons g gs ih =>
      intro ψ
      rw [localProgramCircuit_cons, run_gate, ih, localProgramMatrix_cons, applyGate_mul]
  have adj : ∀ (gs : List (LocalQFTGate n)),
      localProgramMatrix (localProgramAdjoint gs) = (localProgramMatrix gs)ᴴ := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      rw [localProgramAdjoint_cons, localProgramMatrix_append, localProgramMatrix_cons,
        localProgramMatrix_nil, Matrix.one_mul, ih, localProgramMatrix_cons,
        Matrix.conjTranspose_mul]
      exact congrArg (fun M => M * (localProgramMatrix gs)ᴴ) (localGateMatrix_localGateAdjoint g)
  have unitary : ∀ (gs : List (LocalQFTGate n)),
      localProgramMatrix gs ∈ Matrix.unitaryGroup (Reg n) ℂ := by
    intro gs
    induction gs with
    | nil => exact (Matrix.unitaryGroup (Reg n) ℂ).one_mem
    | cons g gs ih =>
      rw [localProgramMatrix_cons]
      exact Submonoid.mul_mem (Matrix.unitaryGroup (Reg n) ℂ) ih (localGateMatrix_unitary g)
  have wellFormed : ∀ (gs : List (LocalQFTGate n)),
      IsUnitaryCircuit (localProgramCircuit gs) := by
    intro gs
    induction gs with
    | nil => exact isUnitaryCircuit_nil
    | cons g gs ih =>
      rw [localProgramCircuit_cons, isUnitaryCircuit_gate]
      exact ⟨localGateMatrix_unitary g, ih⟩
  have queryCount : ∀ (gs : List (LocalQFTGate n)),
      QueryCount (localProgramCircuit gs) = 0 := by
    intro gs
    induction gs with
    | nil => rfl
    | cons g gs ih => exact ih
  have gateCount : ∀ (gs : List (LocalQFTGate n)),
      GateCount (localProgramCircuit gs) = gs.length := by
    intro gs
    induction gs with
    | nil => rfl
    | cons g gs ih => simp [ih]
  have gateCountAdj : ∀ (gs : List (LocalQFTGate n)),
      GateCount (localProgramCircuit (localProgramAdjoint gs)) = gs.length := by
    intro gs
    have hlen : (localProgramAdjoint gs).length = gs.length := by
      simp [localProgramAdjoint]
    have hgc := gateCount (localProgramAdjoint gs)
    rw [hlen] at hgc
    exact hgc
  exact ⟨run gs ψ, adj gs, localProgramAdjoint_involutive gs, wellFormed gs, unitary gs,
    queryCount gs, gateCount gs, gateCountAdj gs, fun g => localGateMatrix_localGateAdjoint g⟩

end Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
