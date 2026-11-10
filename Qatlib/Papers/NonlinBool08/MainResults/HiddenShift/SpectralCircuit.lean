/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinBool08.MainResults.QuantumDefs
import Qatlib.Papers.NonlinBool08.MainResults.HiddenShift.Theorems
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.HiddenShift

open Qatlib.Papers.NonlinBool08.MainResults.BentCore
open Qatlib.Papers.NonlinBool08.MainResults.QuantumDefs

lemma pow_half_mul_c {n : ℕ} (hn : Even n) :
    (2 : ℂ) ^ (n / 2) * (2 : ℂ) ^ (n / 2) = (2 : ℂ) ^ n :=
  QuantumDefs.pow_half_mul_c hn

lemma hnorm_cube_mul {n : ℕ} (hn : Even n) :
    hnorm n * hnorm n * hnorm n * (2 : ℂ) ^ (n / 2) * (2 : ℂ) ^ n = 1 := by
  have h2 : (2 : ℂ) ^ (n / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsq : (2 : ℂ) ^ n = (2 : ℂ) ^ (n / 2) * (2 : ℂ) ^ (n / 2) :=
    (pow_half_mul_c hn).symm
  unfold hnorm
  rw [hsq]
  rw [show ((2 : ℂ) ^ (n / 2))⁻¹ * ((2 : ℂ) ^ (n / 2))⁻¹ * ((2 : ℂ) ^ (n / 2))⁻¹
        * (2 : ℂ) ^ (n / 2) * ((2 : ℂ) ^ (n / 2) * (2 : ℂ) ^ (n / 2))
      = (((2 : ℂ) ^ (n / 2))⁻¹ * (2 : ℂ) ^ (n / 2))
        * (((2 : ℂ) ^ (n / 2))⁻¹ * (2 : ℂ) ^ (n / 2))
        * (((2 : ℂ) ^ (n / 2))⁻¹ * (2 : ℂ) ^ (n / 2)) from by ring]
  rw [inv_mul_cancel₀ h2]
  norm_num

theorem hadamard_phaseOracle_const {n : ℕ} (f : BVec n → ZMod 2) (c : ℂ) :
    hadamard (phaseOracle f (fun _ => c))
      = fun y => hnorm n * c * (walsh f y : ℂ) := by
  funext y
  simp only [hadamard, phaseOracle]
  rw [show (∑ x : BVec n, (eps (dot y x) : ℂ) * ((eps (f x) : ℂ) * c))
      = c * ∑ x : BVec n, (eps (dot y x) : ℂ) * (eps (f x) : ℂ) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)]
  rw [← walsh_cast]
  ring

theorem phaseOracle_phaseVec {n : ℕ} (ft g : BVec n → ZMod 2) (c : ℂ) :
    phaseOracle ft (fun y => c * (walsh g y : ℂ))
      = fun y => c * ((phaseVec ft g y : ℤ) : ℂ) := by
  funext y
  simp only [phaseOracle, phaseVec]
  rw [Int.cast_mul]
  ring

theorem hadamard_phaseVec {n : ℕ} (ft g : BVec n → ZMod 2) (c : ℂ) :
    hadamard (fun y => c * ((phaseVec ft g y : ℤ) : ℂ))
      = fun z => hnorm n * c * (finalAmp ft g z : ℂ) := by
  funext z
  simp only [hadamard]
  have hfin : ((finalAmp ft g z : ℤ) : ℂ)
      = ∑ y : BVec n, (eps (dot z y) : ℂ) * ((phaseVec ft g y : ℤ) : ℂ) := by
    rw [finalAmp, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [Int.cast_mul, dot_comm]
  rw [hfin]
  rw [show (∑ y : BVec n, (eps (dot z y) : ℂ) * (c * ((phaseVec ft g y : ℤ) : ℂ)))
      = c * ∑ y : BVec n, (eps (dot z y) : ℂ) * ((phaseVec ft g y : ℤ) : ℂ) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => by ring)]
  ring

def progA1 {n : ℕ} (g ft : BVec n → ZMod 2) : Program n :=
  [Gate.had, Gate.orcl g, Gate.had, Gate.orcl ft, Gate.had]

theorem progA1_oracleCount {n : ℕ} (g ft : BVec n → ZMod 2) :
    (progA1 g ft).oracleCount = 2 := by
  simp [Program.oracleCount, progA1, Gate.isOracle]

theorem progA1_eval_eq {n : ℕ} (g ft : BVec n → ZMod 2) :
    (progA1 g ft).eval (initState n)
      = fun z => hnorm n * (hnorm n * hnorm n) * (finalAmp ft g z : ℂ) := by
  simp only [Program.eval, progA1, List.foldl_cons, List.foldl_nil, Gate.eval]
  rw [hadamard_init]
  rw [hadamard_phaseOracle_const g (hnorm n)]
  rw [show (fun y => hnorm n * hnorm n * (walsh g y : ℂ))
      = fun y => (hnorm n * hnorm n) * (walsh g y : ℂ) from rfl]
  rw [phaseOracle_phaseVec ft g (hnorm n * hnorm n)]
  rw [hadamard_phaseVec ft g (hnorm n * hnorm n)]

theorem progA1_correct {n : ℕ} (hn : Even n) {f g ft : BVec n → ZMod 2} {s : BVec n}
    (hd : IsDual f ft) (hg : HidesShiftOn f g s) :
    (progA1 g ft).eval (initState n) = basisState (n := n) s := by
  rw [progA1_eval_eq]
  funext z
  rw [finalAmp_eq hd hg hn z]
  simp only [basisState]
  by_cases hz : z = s
  · rw [if_pos hz, if_pos hz]
    push_cast
    rw [show hnorm n * (hnorm n * hnorm n)
          * (((2 : ℂ) ^ (n / 2)) * (2 : ℂ) ^ n)
        = hnorm n * hnorm n * hnorm n * (2 : ℂ) ^ (n / 2) * (2 : ℂ) ^ n from by ring,
      hnorm_cube_mul hn]
  · rw [if_neg hz, if_neg hz]
    simp

theorem progA1_born {n : ℕ} (hn : Even n) {f g ft : BVec n → ZMod 2} {s : BVec n}
    (hd : IsDual f ft) (hg : HidesShiftOn f g s) :
    prob ((progA1 g ft).eval (initState n)) s = 1 ∧
      ∀ z : BVec n, z ≠ s → prob ((progA1 g ft).eval (initState n)) z = 0 := by
  rw [progA1_correct hn hd hg]
  constructor
  · simp [prob, basisState]
  · intro z hz
    simp [prob, basisState, hz]

theorem theorem6_twoQuery_zeroError (n : ℕ) (hn : Even n) :
    ∃ prog : (BVec n → ZMod 2) → (BVec n → ZMod 2) → Program n,
      (∀ g ft, (prog g ft).oracleCount = 2) ∧
      (∀ (f g ft : BVec n → ZMod 2) (s : BVec n), IsDual f ft →
        HidesShiftOn f g s →
        (prog g ft).eval (initState n) = basisState (n := n) s ∧
          prob ((prog g ft).eval (initState n)) s = 1) := by
  refine ⟨progA1, progA1_oracleCount, ?_⟩
  intro f g ft s hd hg
  exact ⟨progA1_correct hn hd hg, (progA1_born hn hd hg).1⟩

end Qatlib.Papers.NonlinBool08.MainResults.HiddenShift
