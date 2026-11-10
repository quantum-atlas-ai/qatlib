/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonFullSpectrumStat
import Qatlib.Concepts.WalkFind.WalkSpectrum.NormalSpectralPerturbationQuan
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonSpectrumPhase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.GroverInterp

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.WalkSpectrum
open Matrix Polynomial Qatlib.Concepts.WalkFind.UniqueCollision
open scoped Classical BigOperators

def johnsonFalling (n : ℕ) (x : ℂ) : ℂ := (descPochhammer ℂ n).eval x

theorem johnsonFalling_succ (n : ℕ) (x : ℂ) :
    johnsonFalling (n+1) x = johnsonFalling n x*(x-n) :=
  descPochhammer_succ_eval n x

theorem johnsonFalling_shift (n : ℕ) (x : ℂ) :
    johnsonFalling (n+1) x = x*johnsonFalling n (x-1) := by
  simp [johnsonFalling, descPochhammer_succ_left, Polynomial.eval_comp]

theorem johnsonFalling_backward (n : ℕ) (x : ℂ) :
    johnsonFalling (n+1) (x-1) = johnsonFalling (n+1) x-(n+1)*johnsonFalling n (x-1) := by
  have h := congrArg (Polynomial.eval x) (descPochhammer_succ_comp_X_sub_one ℂ n)
  simpa [johnsonFalling, Polynomial.eval_comp, smul_eq_mul] using! h

theorem johnsonFalling_forward (n : ℕ) (x : ℂ) :
    johnsonFalling (n+1) (x+1)-johnsonFalling (n+1) x = (n+1)*johnsonFalling n x := by
  have h := johnsonFalling_backward n (x+1)
  simp only [add_sub_cancel_right] at h
  linear_combination -h

theorem johnsonFalling_birthDeath (n : ℕ) (x N k r : ℂ) :
    (k-x)*(r-x)*(johnsonFalling (n+1) x-johnsonFalling (n+1) (x+1))+
      x*(N-k-r+x)*(johnsonFalling (n+1) x-johnsonFalling (n+1) (x-1)) =
    (n+1)*(N-n)*johnsonFalling (n+1) x-
      (n+1)*(k-n)*(r-n)*johnsonFalling n x := by
  have hf := johnsonFalling_forward n x
  have hb := johnsonFalling_backward n x
  have hs := johnsonFalling_shift n x
  have hr := johnsonFalling_succ n x
  linear_combination -(k-x)*(r-x)*hf-x*(N-k-r+x)*hb-
    (n+1)*(N-k-r+x)*hs+(n+1)*(x+n-k-r)*hr

def johnsonBirthRate (k r i : ℕ) : ℂ := ((k : ℂ)-i)*((r : ℂ)-i)
def johnsonDeathRate (k N r i : ℕ) : ℂ := (i : ℂ)*((N : ℂ)-k-r+i)
def johnsonLaplacianValue (j N : ℕ) : ℂ := (j : ℂ)*((N : ℂ)+1-j)

def johnsonBirthDeath (k N r : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
  fun i j => (if i = j then johnsonBirthRate k r i.val+johnsonDeathRate k N r i.val else 0)-
    (if j.val = i.val+1 then johnsonBirthRate k r i.val else 0)-
    (if j.val+1 = i.val then johnsonDeathRate k N r i.val else 0)

def johnsonFallingMatrix (k : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
  fun i j => johnsonFalling j.val i.val

def johnsonFallingTriangular (k N r : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
  fun i j => (if i = j then johnsonLaplacianValue j.val N else 0)-
    (if i.val+1 = j.val then (j.val : ℂ)*((k : ℂ)+1-j.val)*((r : ℂ)+1-j.val) else 0)

theorem johnsonBirthDeath_mulVec (k N r : ℕ) (f : ℂ → ℂ) (i : Fin (k+1)) :
    (johnsonBirthDeath k N r *ᵥ (fun j => f j.val)) i =
      johnsonBirthRate k r i.val*(f i.val-f ((i.val : ℂ)+1))+
      johnsonDeathRate k N r i.val*(f i.val-f ((i.val : ℂ)-1)) := by
  simp only [johnsonBirthDeath, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hup : (∑ j : Fin (k+1), if j.val = i.val+1 then johnsonBirthRate k r i.val*f j.val else 0) =
      johnsonBirthRate k r i.val*f ((i.val : ℂ)+1) := by
    by_cases hi : i.val < k
    · let u : Fin (k+1) := ⟨i.val+1, by omega⟩
      have heq (j : Fin (k+1)) : j.val = i.val+1 ↔ j = u := by rw [Fin.ext_iff]
      simp [heq, u]
    · have hik : i.val = k := by omega
      simp [johnsonBirthRate, hik]
  have hdown : (∑ j : Fin (k+1), if j.val+1 = i.val then johnsonDeathRate k N r i.val*f j.val else 0) =
      johnsonDeathRate k N r i.val*f ((i.val : ℂ)-1) := by
    by_cases hi : i.val = 0
    · simp [hi, johnsonDeathRate]
    · let u : Fin (k+1) := ⟨i.val-1, by omega⟩
      have heq (j : Fin (k+1)) : j.val+1 = i.val ↔ j = u := by rw [Fin.ext_iff]; dsimp [u]; omega
      simp [heq, u, Nat.cast_sub (show 1 ≤ i.val by omega)]
  rw [hup, hdown]
  ring

theorem johnsonBirthDeath_falling (k N r n : ℕ) (i : Fin (k+1)) :
    (johnsonBirthDeath k N r *ᵥ (fun j => johnsonFalling n j.val)) i =
      johnsonLaplacianValue n N*johnsonFalling n i.val-
      (n : ℂ)*((k : ℂ)+1-n)*((r : ℂ)+1-n)*johnsonFalling (n-1) i.val := by
  rw [johnsonBirthDeath_mulVec]
  cases n with
  | zero => simp [johnsonFalling, johnsonLaplacianValue]
  | succ n =>
    have h := johnsonFalling_birthDeath n (i.val : ℂ) (N : ℂ) (k : ℂ) (r : ℂ)
    simpa [johnsonBirthRate, johnsonDeathRate, johnsonLaplacianValue] using! h

theorem johnsonBirthDeath_falling_similarity (k N r : ℕ) :
    johnsonBirthDeath k N r*johnsonFallingMatrix k =
      johnsonFallingMatrix k*johnsonFallingTriangular k N r := by
  ext i j
  have hL := johnsonBirthDeath_falling k N r j.val i
  change (johnsonBirthDeath k N r *ᵥ (fun u => johnsonFalling j.val u.val)) i = _
  rw [hL]
  let A : ℂ := (j.val : ℂ)*((k : ℂ)+1-j.val)*((r : ℂ)+1-j.val)
  change johnsonLaplacianValue j.val N*johnsonFalling j.val i.val-A*johnsonFalling (j.val-1) i.val =
    ∑ u : Fin (k+1), johnsonFalling u.val i.val *
      ((if u = j then johnsonLaplacianValue j.val N else 0)-(if u.val+1 = j.val then A else 0))
  have hterm (u : Fin (k+1)) : johnsonFalling u.val i.val *
      ((if u = j then johnsonLaplacianValue j.val N else 0)-(if u.val+1 = j.val then A else 0)) =
      (if u = j then johnsonFalling u.val i.val*johnsonLaplacianValue j.val N else 0)-
      (if u.val+1 = j.val then johnsonFalling u.val i.val*A else 0) := by
    split_ifs <;> ring
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hdown : (∑ u : Fin (k+1), if u.val+1 = j.val then
      johnsonFalling u.val i.val*((j.val : ℂ)*((k : ℂ)+1-j.val)*((r : ℂ)+1-j.val)) else 0) =
      (j.val : ℂ)*((k : ℂ)+1-j.val)*((r : ℂ)+1-j.val)*johnsonFalling (j.val-1) i.val := by
    by_cases hj : j.val = 0
    · simp [hj]
    · let u : Fin (k+1) := ⟨j.val-1, by omega⟩
      have heq (v : Fin (k+1)) : v.val+1 = j.val ↔ v = u := by rw [Fin.ext_iff]; dsimp [u]; omega
      simp [heq, u, mul_comm]
  change _ = _ - ∑ u : Fin (k+1), if u.val+1 = j.val then
    johnsonFalling u.val i.val*((j.val : ℂ)*((k : ℂ)+1-j.val)*((r : ℂ)+1-j.val)) else 0
  rw [hdown]
  dsimp [A]
  ring

theorem johnsonFallingMatrix_det_ne_zero (k : ℕ) : (johnsonFallingMatrix k).det ≠ 0 := by
  have htri : (johnsonFallingMatrix k).BlockTriangular OrderDual.toDual := by
    intro i j hij
    change johnsonFalling j.val i.val = 0
    rw [johnsonFalling, descPochhammer_eval_eq_descFactorial]
    exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.mpr hij
  rw [Matrix.det_of_lowerTriangular _ htri]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simp [johnsonFallingMatrix, johnsonFalling, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_self, Nat.factorial_ne_zero]

theorem johnsonBirthDeath_charpoly (k N r : ℕ) :
    (johnsonBirthDeath k N r).charpoly =
      ∏ j : Fin (k+1), (Polynomial.X-Polynomial.C (johnsonLaplacianValue j.val N)) := by
  let F := johnsonFallingMatrix k
  have hF : F.det ≠ 0 := johnsonFallingMatrix_det_ne_zero k
  have hFu : IsUnit F.det := isUnit_iff_ne_zero.mpr hF
  have hsim := johnsonBirthDeath_falling_similarity k N r
  change johnsonBirthDeath k N r*F = F*johnsonFallingTriangular k N r at hsim
  have hrepr : johnsonBirthDeath k N r = F*johnsonFallingTriangular k N r*F⁻¹ := by
    have h := congrArg (fun A => A*F⁻¹) hsim
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv F hFu, Matrix.mul_one] using! h
  rw [hrepr, Matrix.charpoly_mul_comm]
  have hinv : F⁻¹*(F*johnsonFallingTriangular k N r) = johnsonFallingTriangular k N r := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul F hFu, Matrix.one_mul]
  rw [hinv]
  have htri : (johnsonFallingTriangular k N r).BlockTriangular id := by
    intro i j hij
    change j.val < i.val at hij
    simp [johnsonFallingTriangular, show i ≠ j by omega, show ¬i.val+1 = j.val by omega]
  rw [Matrix.charpoly_of_upperTriangular _ htri]
  apply Finset.prod_congr rfl
  intro j _
  simp [johnsonFallingTriangular]

def johnsonPlusFrame (k : ℕ) (d : ℝ) : Matrix (Fin (2*k+1)) (Fin (k+1)) ℂ :=
  fun i j => if i.val/2 = j.val then
    if i.val%2 = 0 then (Real.sqrt (1-((k : ℝ)-j.val)/d) : ℂ)
    else (Real.sqrt (((k : ℝ)-j.val)/d) : ℂ) else 0

private theorem johnsonPlusFrame_pair (k : ℕ) (d : ℝ) (a : Bool) (j : Fin k) (p : Fin (k+1)) :
    johnsonPlusFrame k d (jwPairIndex k a j) p =
      if j.val = p.val then
        (if a then (Real.sqrt (((k : ℝ)-p.val)/d) : ℂ) else (Real.sqrt (1-((k : ℝ)-p.val)/d) : ℂ)) else 0 := by
  cases a with
  | false => simp [johnsonPlusFrame, jwPairIndex]
  | true =>
    have he : (2*j.val+1)/2 = j.val := by omega
    simp [johnsonPlusFrame, jwPairIndex, he]

private theorem johnsonPlusFrame_last (k : ℕ) (d : ℝ) (p : Fin (k+1)) :
    johnsonPlusFrame k d (Fin.last (2*k)) p = if p.val = k then 1 else 0 := by
  by_cases hp : p.val = k
  · simp [johnsonPlusFrame, hp]
  · simp [johnsonPlusFrame, hp, Ne.symm hp]

theorem johnsonPlusFrame_isometry (k : ℕ) (d : ℝ) (hd : (k : ℝ) < d) :
    (johnsonPlusFrame k d)ᴴ * johnsonPlusFrame k d = 1 := by
  have hd0 : 0 < d := lt_of_le_of_lt (by positivity) hd
  ext p q
  by_cases hpq : p = q
  · subst q
    have hp : (p.val : ℝ) ≤ k := by exact_mod_cast (show p.val ≤ k by omega)
    have hε0 : 0 ≤ ((k : ℝ)-p.val)/d := div_nonneg (by linarith) hd0.le
    have hp0 : (0 : ℝ) ≤ p.val := by positivity
    have hε1 : ((k : ℝ)-p.val)/d ≤ 1 := (div_le_one hd0).mpr (by linarith)
    have hs (x : ℝ) (hx : 0 ≤ x) :
        (starRingEnd ℂ) (Real.sqrt x : ℂ)*(Real.sqrt x : ℂ) = (x : ℂ) := by
      change star (Real.sqrt x : ℂ)*(Real.sqrt x : ℂ) = _
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1
      nlinarith [Real.sq_sqrt hx]
    have hnorm : (starRingEnd ℂ) (Real.sqrt (1-((k : ℝ)-p.val)/d) : ℂ)*
        (Real.sqrt (1-((k : ℝ)-p.val)/d) : ℂ)+
      (starRingEnd ℂ) (Real.sqrt (((k : ℝ)-p.val)/d) : ℂ)*
        (Real.sqrt (((k : ℝ)-p.val)/d) : ℂ) = 1 := by
      rw [hs _ (by linarith : 0 ≤ 1-((k : ℝ)-p.val)/d), hs _ hε0]
      push_cast
      ring
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq]
    rw [jwSumPairs]
    simp only [johnsonPlusFrame_pair, johnsonPlusFrame_last]
    by_cases hpk : p.val < k
    · let j : Fin k := ⟨p.val,hpk⟩
      have hpm : p.val ≠ k := by omega
      rw [Finset.sum_eq_single j]
      · simpa [j, hpm] using! hnorm
      · intro u _ hu
        have huv : u.val ≠ p.val := fun h => hu (Fin.ext h)
        simp [huv]
      · simp
    · have hpk' : p.val = k := by omega
      have hu (u : Fin k) : u.val ≠ k := Nat.ne_of_lt u.isLt
      simp [hpk', hu]
  · have hvpq : p.val ≠ q.val := fun h => hpq (Fin.ext h)
    rw [Matrix.one_apply, if_neg hpq]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hip : i.val/2 = p.val
    · simp [johnsonPlusFrame, hip, hvpq]
    · simp [johnsonPlusFrame, hip]

theorem johnsonPlusFrame_projection_entry (k : ℕ) (d : ℝ) (i j : Fin (2*k+1)) :
    (johnsonPlusFrame k d*(johnsonPlusFrame k d)ᴴ) i j =
      if i.val/2 = j.val/2 then
        (if i.val%2 = 0 then (Real.sqrt (1-((k : ℝ)-(i.val/2 : ℕ))/d) : ℂ)
          else (Real.sqrt (((k : ℝ)-(i.val/2 : ℕ))/d) : ℂ))*
        (if j.val%2 = 0 then (Real.sqrt (1-((k : ℝ)-(i.val/2 : ℕ))/d) : ℂ)
          else (Real.sqrt (((k : ℝ)-(i.val/2 : ℕ))/d) : ℂ)) else 0 := by
  let u : Fin (k+1) := ⟨i.val/2, by have := i.isLt; omega⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single u]
  · by_cases h : i.val/2 = j.val/2
    · by_cases hj : j.val%2 = 0
      · simp [johnsonPlusFrame, u, h, hj]
      · simp [johnsonPlusFrame, u, h, hj]
    · have h' : j.val/2 ≠ i.val/2 := Ne.symm h
      simp [johnsonPlusFrame, u, h, h']
  · intro v _ hv
    have hv' : i.val/2 ≠ v.val := fun h => hv (Fin.ext h.symm)
    simp [johnsonPlusFrame, hv']
  · simp

def johnsonPairedReflection (k : ℕ) (d : ℝ) : Matrix (Fin (2*k+1)) (Fin (2*k+1)) ℂ :=
  fun i j => if i.val/2 = j.val/2 then
    jwD2 (((k : ℝ)-(j.val/2 : ℕ))/d) (decide (i.val%2 = 1)) (decide (j.val%2 = 1)) else 0

theorem johnsonPairedReflection_frame (k : ℕ) (d : ℝ) (hd : (k : ℝ) < d) :
    johnsonPairedReflection k d = ReflectionAbout (johnsonPlusFrame k d*(johnsonPlusFrame k d)ᴴ) := by
  ext i j
  have hd0 : 0 < d := lt_of_le_of_lt (by positivity) hd
  simp only [ReflectionAbout, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    johnsonPlusFrame_projection_entry, Matrix.one_apply]
  by_cases hij : i.val/2 = j.val/2
  · have hjk : ((j.val/2 : ℕ) : ℝ) ≤ k := by exact_mod_cast (show j.val/2 ≤ k by have := j.isLt; omega)
    have hj0 : (0 : ℝ) ≤ (j.val/2 : ℕ) := by positivity
    let ε := ((k : ℝ)-(j.val/2 : ℕ))/d
    have hε0 : 0 ≤ ε := div_nonneg (by linarith) hd0.le
    have hε1 : ε ≤ 1 := (div_le_one hd0).mpr (by linarith)
    have hsq0 : (Real.sqrt (1-ε) : ℂ)^2 = ((1-ε : ℝ) : ℂ) := by
      exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-ε)
    have hsq1 : (Real.sqrt ε : ℂ)^2 = (ε : ℂ) := by exact_mod_cast Real.sq_sqrt hε0
    have hcross : (Real.sqrt (1-ε) : ℂ)*(Real.sqrt ε : ℂ) = (Real.sqrt (ε-ε*ε) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by linarith : 0 ≤ 1-ε)]
      congr 2
      ring
    have heq : i = j ↔ i.val%2 = j.val%2 := by
      constructor
      · intro h; rw [h]
      · intro h; apply Fin.ext; omega
    have heven : ((1-2*ε : ℝ) : ℂ) = 2*((Real.sqrt (1-ε) : ℂ)*(Real.sqrt (1-ε) : ℂ))-1 := by
      rw [← pow_two, hsq0]
      push_cast
      ring
    have hodd : ((-1+2*ε : ℝ) : ℂ) = 2*((Real.sqrt ε : ℂ)*(Real.sqrt ε : ℂ))-1 := by
      rw [← pow_two, hsq1]
      push_cast
      ring
    have hcross' : ((2*Real.sqrt (ε-ε*ε) : ℝ) : ℂ) =
        2*((Real.sqrt (1-ε) : ℂ)*(Real.sqrt ε : ℂ)) := by
      rw [hcross]
      push_cast
      ring
    have hcross'' : ((2*Real.sqrt (ε-ε*ε) : ℝ) : ℂ) =
        2*((Real.sqrt ε : ℂ)*(Real.sqrt (1-ε) : ℂ)) := by
      rw [mul_comm (Real.sqrt ε : ℂ)]
      exact hcross'
    by_cases hi : i.val%2 = 0 <;> by_cases hj : j.val%2 = 0
    · have he : i = j := heq.mpr (hi.trans hj.symm)
      simpa [johnsonPairedReflection, jwD2, he, hj, ε] using! heven
    · have hj' : j.val%2 = 1 := by omega
      have hne : i ≠ j := fun h => by subst j; exact hj hi
      simpa [johnsonPairedReflection, jwD2, hij, hi, hj', hne, ε] using! hcross'
    · have hi' : i.val%2 = 1 := by omega
      have hne : i ≠ j := fun h => by subst j; exact hi hj
      simpa [johnsonPairedReflection, jwD2, hij, hi', hj, hne, ε] using! hcross''
    · have hi' : i.val%2 = 1 := by omega
      have hj' : j.val%2 = 1 := by omega
      have he : i = j := heq.mpr (hi'.trans hj'.symm)
      simpa [johnsonPairedReflection, jwD2, he, hj', ε] using! hodd
  · have hne : i ≠ j := fun h => hij (by rw [h])
    simp [johnsonPairedReflection, hij, hne]

theorem johnsonStep1_paired (k N r : ℕ) : jwStep1 k N r = johnsonPairedReflection k ((N : ℝ)-r) := by
  ext i j
  have hi := Nat.mod_lt i.val (by decide : 0 < 2)
  have hj := Nat.mod_lt j.val (by decide : 0 < 2)
  by_cases hi0 : i.val%2 = 0 <;> by_cases hj0 : j.val%2 = 0
  · have hdiv : (i.val+1)/2 = i.val/2 := by omega
    simp [jwStep1, jwPhiCoord, jwPsiCoord, johnsonPairedReflection, hi0, hj0, hdiv]
  · have hj1 : j.val%2 = 1 := by omega
    have hdiv : (i.val+1)/2 = i.val/2 := by omega
    simp [jwStep1, jwPhiCoord, jwPsiCoord, johnsonPairedReflection, hi0, hj1, hdiv]
  · have hi1 : i.val%2 = 1 := by omega
    have hdiv : (i.val+1)/2 = i.val/2+1 := by omega
    simp [jwStep1, jwPhiCoord, jwPsiCoord, johnsonPairedReflection, hi1, hj0, hdiv]
  · have hi1 : i.val%2 = 1 := by omega
    have hj1 : j.val%2 = 1 := by omega
    have hdiv : (i.val+1)/2 = i.val/2+1 := by omega
    simp [jwStep1, jwPhiCoord, jwPsiCoord, johnsonPairedReflection, hi1, hj1, hdiv]

theorem johnsonStep2_paired (k r : ℕ) :
    jwStep2 k r = (johnsonPairedReflection k ((r : ℝ)+1)).submatrix Fin.rev Fin.rev := by
  ext i j
  simp only [Matrix.submatrix_apply]
  have hi := i.isLt
  have hj := j.isLt
  have hir : i.rev.val = 2*k-i.val := by simp [Fin.val_rev]
  have hjr : j.rev.val = 2*k-j.val := by simp [Fin.val_rev]
  have hdivi : i.rev.val/2 = k-(i.val+1)/2 := by rw [hir]; omega
  have hdivj : j.rev.val/2 = k-(j.val+1)/2 := by rw [hjr]; omega
  have hmodi : i.rev.val%2 = i.val%2 := by rw [hir]; omega
  have hmodj : j.rev.val%2 = j.val%2 := by rw [hjr]; omega
  have hboundi : (i.val+1)/2 ≤ k := by omega
  have hboundj : (j.val+1)/2 ≤ k := by omega
  have heq : k-(i.val+1)/2 = k-(j.val+1)/2 ↔ (i.val+1)/2 = (j.val+1)/2 := by omega
  have hcastj : ((k-(j.val+1)/2 : ℕ) : ℝ) = k-((j.val+1)/2 : ℕ) := Nat.cast_sub hboundj
  have hε : (k : ℝ)-(k-(j.val+1)/2 : ℕ) = ((j.val+1)/2 : ℕ) := by rw [hcastj]; ring
  simp only [johnsonPairedReflection, hdivi, hdivj, hmodi, hmodj, heq, hε]
  by_cases hip : i.val%2 = 0 <;> by_cases hjp : j.val%2 = 0
  · have hdi : (i.val+1)/2 = i.val/2 := by omega
    simp [jwStep2, jwPhiCoord, jwPsiCoord, hip, hjp, hdi]
  · have hj1 : j.val%2 = 1 := by omega
    have hdi : (i.val+1)/2 = i.val/2 := by omega
    simp [jwStep2, jwPhiCoord, jwPsiCoord, jwD2, hip, hj1, hdi]
  · have hi1 : i.val%2 = 1 := by omega
    have hdi : (i.val+1)/2 = i.val/2+1 := by omega
    simp [jwStep2, jwPhiCoord, jwPsiCoord, hi1, hjp, hdi]
  · have hi1 : i.val%2 = 1 := by omega
    have hj1 : j.val%2 = 1 := by omega
    have hdi : (i.val+1)/2 = i.val/2+1 := by omega
    simp [jwStep2, jwPhiCoord, jwPsiCoord, hi1, hj1, hdi]

def johnsonReverseFrame (k : ℕ) (d : ℝ) : Matrix (Fin (2*k+1)) (Fin (k+1)) ℂ :=
  (johnsonPlusFrame k d).submatrix Fin.rev Fin.rev

theorem johnsonReverseFrame_isometry (k : ℕ) (d : ℝ) (hkd : (k : ℝ) < d) :
    (johnsonReverseFrame k d)ᴴ * johnsonReverseFrame k d = 1 := by
  unfold johnsonReverseFrame
  rw [Matrix.conjTranspose_submatrix]
  change (johnsonPlusFrame k d)ᴴ.submatrix Fin.revPerm Fin.revPerm *
    (johnsonPlusFrame k d).submatrix Fin.revPerm Fin.revPerm = _
  rw [Matrix.submatrix_mul_equiv, johnsonPlusFrame_isometry k d hkd,
    Matrix.submatrix_one_equiv]

theorem johnsonHalfSteps_frames (k N r : ℕ) (hkr : k ≤ r) (hkN : k < N-r) :
    jwStep1 k N r = ReflectionAbout (johnsonPlusFrame k ((N : ℝ)-r) *
      (johnsonPlusFrame k ((N : ℝ)-r))ᴴ) ∧
    jwStep2 k r = ReflectionAbout (johnsonReverseFrame k ((r : ℝ)+1) *
      (johnsonReverseFrame k ((r : ℝ)+1))ᴴ) := by
  have hN : (k : ℝ) < (N : ℝ)-r := by
    have hh : (k : ℝ)+(r : ℝ) < N := by exact_mod_cast (show k+r < N by omega)
    linarith
  have hr : (k : ℝ) < (r : ℝ)+1 := by exact_mod_cast (show k < r+1 by omega)
  refine ⟨(johnsonStep1_paired k N r).trans (johnsonPairedReflection_frame k _ hN), ?_⟩
  rw [johnsonStep2_paired, johnsonPairedReflection_frame k _ hr]
  unfold johnsonReverseFrame ReflectionAbout
  rw [Matrix.conjTranspose_submatrix]
  change _ = 2 • ((johnsonPlusFrame k ((r : ℝ)+1)).submatrix Fin.revPerm Fin.revPerm *
    (johnsonPlusFrame k ((r : ℝ)+1))ᴴ.submatrix Fin.revPerm Fin.revPerm) - 1
  rw [Matrix.submatrix_mul_equiv]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply, Fin.rev_inj]

theorem johnsonPhase_cosine_bounds (k N r j : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r)
    (hkN : k < N-r) (hj : 1 ≤ j) (hjk : j ≤ k) :
    -1 < 1-2*(j : ℝ)*(N+1-j)/((r+1)*(N-r)) ∧
    1-2*(j : ℝ)*(N+1-j)/((r+1)*(N-r)) < 1 := by
  have hNr : r < N := by omega
  have htwo : 2*k < N := by omega
  have hr0 : 0 < (r : ℝ)+1 := by positivity
  have hNr0 : 0 < (N : ℝ)-(r : ℝ) := by
    have hh : (r : ℝ) < N := by exact_mod_cast hNr
    linarith
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast hj
  have hjr : (j : ℝ) ≤ r := by exact_mod_cast (show j ≤ r by omega)
  have hjN : (j : ℝ) < (N : ℝ)-(r : ℝ) := by
    have hh : (j : ℝ)+(r : ℝ) < N := by exact_mod_cast (show j+r < N by omega)
    linarith
  have hpos : 0 < (j : ℝ)*((N : ℝ)+1-j) := mul_pos hj0 (by linarith)
  have hrem : 0 < ((r : ℝ)+1-j)*((N : ℝ)-r-j) := mul_pos (by linarith) (by linarith)
  have hden : 0 < ((r : ℝ)+1)*((N : ℝ)-r) := mul_pos hr0 hNr0
  have htop : (j : ℝ)*((N : ℝ)+1-j) < ((r : ℝ)+1)*((N : ℝ)-r) := by nlinarith
  constructor
  · have hh : 2*(j : ℝ)*(N+1-j)/((r+1)*(N-r)) < 2 := by
      apply (div_lt_iff₀ hden).mpr
      nlinarith
    linarith
  · have hh : 0 < 2*(j : ℝ)*(N+1-j) := by nlinarith
    exact sub_lt_self _ (div_pos hh hden)

theorem johnsonPhase_strict_bounds (k N r j : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r)
    (hkN : k < N-r) (hj : 1 ≤ j) (hjk : j ≤ k) :
    0 < johnsonPhase j N r ∧ johnsonPhase j N r < Real.pi := by
  obtain ⟨hlo,hhi⟩ := johnsonPhase_cosine_bounds k N r j hk hkr hkN hj hjk
  exact ⟨Real.arccos_pos.mpr hhi, Real.arccos_lt_pi.mpr hlo⟩

theorem johnsonPhase_strictMono (k N r : ℕ) (hkr : k ≤ r) (hkN : k < N-r) :
    StrictMono (fun j : Fin k => johnsonPhase (j.val+1) N r) := by
  intro i j hij
  have hik : i.val+1 ≤ k := by omega
  have hjk : j.val+1 ≤ k := by omega
  have hk : 1 ≤ k := by omega
  have h2k : 2*k < N := by omega
  have hri : (i.val : ℝ) < j.val := by exact_mod_cast hij
  have hjN : 2*((j.val : ℝ)+1) < (N : ℝ)+1 := by exact_mod_cast (show 2*(j.val+1) < N+1 by omega)
  have hden : 0 < ((r : ℝ)+1)*((N : ℝ)-r) := mul_pos (by positivity) (by
    have hh : (r : ℝ) < N := by exact_mod_cast (show r < N by omega)
    linarith)
  have hprod : ((i.val : ℝ)+1)*((N : ℝ)-i.val) < ((j.val : ℝ)+1)*((N : ℝ)-j.val) := by nlinarith
  obtain ⟨hlo,_⟩ := johnsonPhase_cosine_bounds k N r (j.val+1) hk hkr hkN (by omega) hjk
  obtain ⟨_,hhi⟩ := johnsonPhase_cosine_bounds k N r (i.val+1) hk hkr hkN (by omega) hik
  apply Real.arccos_lt_arccos hlo.le _ hhi.le
  apply sub_lt_sub_left
  apply (div_lt_div_iff_of_pos_right hden).mpr
  push_cast
  nlinarith

private theorem johnsonReverseFrame_pair (k : ℕ) (d : ℝ) (a : Bool) (j : Fin k) (p : Fin (k+1)) :
    johnsonReverseFrame k d (jwPairIndex k a j) p =
      if a then (if j.val+1 = p.val then (Real.sqrt ((p : ℝ)/d) : ℂ) else 0)
      else (if j.val = p.val then (Real.sqrt (1-(p : ℝ)/d) : ℂ) else 0) := by
  have hj := j.isLt
  have hp := p.isLt
  have hrevp : p.rev.val = k-p.val := by simp [Fin.val_rev]
  have hcastp : ((k-p.val : ℕ) : ℝ) = (k : ℝ)-p.val := Nat.cast_sub (by omega)
  cases a with
  | false =>
    have hv : (jwPairIndex k false j).rev.val = 2*(k-j.val) := by
      simp [Fin.val_rev,jwPairIndex]; omega
    have heq : k-j.val = k-p.val ↔ j.val = p.val := by omega
    have hsub : (k : ℝ)-(k-p.val : ℕ) = (p : ℝ) := by rw [hcastp]; ring
    simp only [johnsonReverseFrame,Matrix.submatrix_apply,johnsonPlusFrame,hv,hrevp]
    simp [heq,hsub]
  | true =>
    have hv : (jwPairIndex k true j).rev.val = 2*(k-(j.val+1))+1 := by
      simp [Fin.val_rev,jwPairIndex]; omega
    have heq : k-(j.val+1) = k-p.val ↔ j.val+1 = p.val := by omega
    have hsub : (k : ℝ)-(k-p.val : ℕ) = (p : ℝ) := by rw [hcastp]; ring
    simp only [johnsonReverseFrame,Matrix.submatrix_apply,johnsonPlusFrame,hv,hrevp]
    have hd : (2*(k-(j.val+1))+1)/2 = k-(j.val+1) := by omega
    simp [hd,heq,hsub]

private theorem johnsonReverseFrame_last (k : ℕ) (d : ℝ) (p : Fin (k+1)) :
    johnsonReverseFrame k d (Fin.last (2*k)) p =
      if p.val = k then (Real.sqrt (1-(k : ℝ)/d) : ℂ) else 0 := by
  have hp := p.isLt
  have hr : (Fin.last (2*k)).rev.val = 0 := by simp
  have hpr : p.rev.val = k-p.val := by simp [Fin.val_rev]
  have heq : 0 = k-p.val ↔ p.val = k := by omega
  by_cases hp' : p.val = k
  · have hz : k-p.val = 0 := by omega
    simp only [johnsonReverseFrame,Matrix.submatrix_apply,johnsonPlusFrame,hr,hpr,hz]
    simp [hp']
  · simp only [johnsonReverseFrame,Matrix.submatrix_apply,johnsonPlusFrame,hr,hpr]
    simp [heq,hp']

theorem johnsonOverlap_bidiagonal (k : ℕ) (d e : ℝ) (i j : Fin (k+1)) :
    ((johnsonPlusFrame k d)ᴴ*johnsonReverseFrame k e) i j =
      (if i = j then (Real.sqrt (1-((k : ℝ)-i.val)/d) : ℂ)*
        (Real.sqrt (1-(i : ℝ)/e) : ℂ) else 0)+
      (if j.val = i.val+1 then (Real.sqrt (((k : ℝ)-i.val)/d) : ℂ)*
        (Real.sqrt (((i : ℝ)+1)/e) : ℂ) else 0) := by
  rw [Matrix.mul_apply,jwSumPairs]
  simp only [Matrix.conjTranspose_apply,johnsonPlusFrame_pair,johnsonReverseFrame_pair,
    Bool.false_eq_true,if_false,if_true]
  have hlast := johnsonPlusFrame_last k d i
  rw [hlast,johnsonReverseFrame_last,Finset.sum_add_distrib]
  have hstars (x : ℝ) : star (x : ℂ) = x := Complex.conj_ofReal x
  simp only [apply_ite star,star_zero,star_one,hstars]
  by_cases hi : i.val < k
  · let ii : Fin k := ⟨i.val,hi⟩
    have heq (a : Fin k) : a.val = i.val ↔ a = ii := by simp [Fin.ext_iff,ii]
    have hne : i.val ≠ k := by omega
    simp only [heq,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,hne,if_false,zero_mul,add_zero]
    have heqij : i.val = j.val ↔ i = j := Fin.ext_iff.symm
    simp only [ii,heqij,show i.val+1 = j.val ↔ j.val = i.val+1 from eq_comm]
    congr 1
    · split_ifs with h
      · subst j; rfl
      · simp
    · split_ifs with h
      · have hc : (j : ℝ) = (i : ℝ)+1 := by exact_mod_cast h
        rw [hc]
      · simp
  · have hik : i.val = k := by omega
    have hne (a : Fin k) : a.val ≠ i.val := by have ha := a.isLt; omega
    have heqij : i = j ↔ j.val = k := by rw [Fin.ext_iff,hik]; omega
    simp only [hne,if_false,zero_mul,Finset.sum_const_zero]
    simp [hik,heqij]

def johnsonOverlapDiagonal (k i : ℕ) (d e : ℝ) : ℂ :=
  (Real.sqrt (1-((k : ℝ)-i)/d) : ℂ)*(Real.sqrt (1-(i : ℝ)/e) : ℂ)
def johnsonOverlapUpper (k i : ℕ) (d e : ℝ) : ℂ :=
  (Real.sqrt (((k : ℝ)-i)/d) : ℂ)*(Real.sqrt (((i : ℝ)+1)/e) : ℂ)

theorem johnsonOverlap_squares (k i : ℕ) (d e : ℝ) (hi : i ≤ k)
    (hd : (k : ℝ) < d) (he : (k : ℝ) < e) :
    johnsonOverlapDiagonal k i d e ^ 2 =
      (((d-k+i)*(e-i)/(d*e) : ℝ) : ℂ) ∧
    johnsonOverlapUpper k i d e ^ 2 =
      ((((k : ℝ)-i)*(i+1)/(d*e) : ℝ) : ℂ) := by
  have hiR : (i : ℝ) ≤ k := by exact_mod_cast hi
  have hd0 : 0 < d := lt_of_le_of_lt (Nat.cast_nonneg k) hd
  have he0 : 0 < e := lt_of_le_of_lt (Nat.cast_nonneg k) he
  have hδ : 0 ≤ 1-((k : ℝ)-i)/d := by
    rw [sub_nonneg,div_le_one hd0]
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hη : 0 ≤ 1-(i : ℝ)/e := by
    rw [sub_nonneg,div_le_one he0]
    linarith
  have hβ : 0 ≤ ((k : ℝ)-i)/d := div_nonneg (by linarith) hd0.le
  have hγ : 0 ≤ ((i : ℝ)+1)/e := by positivity
  have hs (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ)^2 = x := by exact_mod_cast Real.sq_sqrt hx
  constructor
  · rw [johnsonOverlapDiagonal,mul_pow,hs _ hδ,hs _ hη,← Complex.ofReal_mul]
    congr 1
    field_simp
    ring
  · rw [johnsonOverlapUpper,mul_pow,hs _ hβ,hs _ hγ,← Complex.ofReal_mul]
    congr 1
    field_simp

theorem johnsonOverlap_laplacian_diagonal (k N r i : ℕ) (hi : i ≤ k)
    (hkr : k ≤ r) (hkN : k < N-r) :
    (((N : ℝ)-r)*((r : ℝ)+1) : ℂ)*
      (1-johnsonOverlapDiagonal k i ((N : ℝ)-r) ((r : ℝ)+1)^2-
        johnsonOverlapUpper k i ((N : ℝ)-r) ((r : ℝ)+1)^2) =
      johnsonBirthRate k r i+johnsonDeathRate k N r i := by
  have hd : (k : ℝ) < (N : ℝ)-r := by
    have hh : (k : ℝ)+(r : ℝ) < N := by exact_mod_cast (show k+r < N by omega)
    linarith
  have he : (k : ℝ) < (r : ℝ)+1 := by exact_mod_cast (show k < r+1 by omega)
  obtain ⟨hδ,hβ⟩ := johnsonOverlap_squares k i _ _ hi hd he
  rw [hδ,hβ]
  unfold johnsonBirthRate johnsonDeathRate
  push_cast
  have hd0 : (N : ℂ)-(r : ℂ) ≠ 0 := by
    exact_mod_cast (show (N : ℝ)-(r : ℝ) ≠ 0 by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have he0 : (r : ℂ)+1 ≠ 0 := by exact_mod_cast (show (r : ℝ)+1 ≠ 0 by positivity)
  field_simp
  ring

theorem johnsonOverlap_laplacian_offsquare (k N r i : ℕ) (hi : i < k)
    (hkr : k ≤ r) (hkN : k < N-r) :
    (((N : ℝ)-r)*((r : ℝ)+1) : ℂ)^2*
      (johnsonOverlapUpper k i ((N : ℝ)-r) ((r : ℝ)+1)*
        johnsonOverlapDiagonal k (i+1) ((N : ℝ)-r) ((r : ℝ)+1))^2 =
      johnsonBirthRate k r i*johnsonDeathRate k N r (i+1) := by
  have hd : (k : ℝ) < (N : ℝ)-r := by
    have hh : (k : ℝ)+(r : ℝ) < N := by exact_mod_cast (show k+r < N by omega)
    linarith
  have he : (k : ℝ) < (r : ℝ)+1 := by exact_mod_cast (show k < r+1 by omega)
  have hβ := (johnsonOverlap_squares k i _ _ hi.le hd he).2
  have hδ := (johnsonOverlap_squares k (i+1) _ _ (by omega) hd he).1
  simp only [mul_pow]
  rw [hβ,hδ]
  unfold johnsonBirthRate johnsonDeathRate
  push_cast
  have hd0 : (N : ℂ)-(r : ℂ) ≠ 0 := by
    exact_mod_cast (show (N : ℝ)-(r : ℝ) ≠ 0 by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have he0 : (r : ℂ)+1 ≠ 0 := by exact_mod_cast (show (r : ℝ)+1 ≠ 0 by positivity)
  field_simp
  ring

def johnsonOffRate (k N r i : ℕ) : ℂ :=
  (((N : ℝ)-r)*((r : ℝ)+1) : ℂ)*johnsonOverlapUpper k i ((N : ℝ)-r) ((r : ℝ)+1)*
    johnsonOverlapDiagonal k (i+1) ((N : ℝ)-r) ((r : ℝ)+1)

def johnsonJacobi (k N r : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
  fun i j => (if i = j then johnsonBirthRate k r i.val+johnsonDeathRate k N r i.val else 0)-
    (if j.val = i.val+1 then johnsonOffRate k N r i.val else 0)-
    (if j.val+1 = i.val then johnsonOffRate k N r j.val else 0)

def johnsonScale (k N r i : ℕ) : ℂ :=
  ∏ j ∈ Finset.range i, johnsonOffRate k N r j/johnsonBirthRate k r j

theorem johnsonScale_succ (k N r i : ℕ) :
    johnsonScale k N r (i+1) = johnsonScale k N r i*(johnsonOffRate k N r i/johnsonBirthRate k r i) :=
  Finset.prod_range_succ _ i

theorem johnsonBirthRate_ne_zero (k r i : ℕ) (hkr : k ≤ r) (hi : i < k) :
    johnsonBirthRate k r i ≠ 0 := by
  have hik : (i : ℝ) < k := by exact_mod_cast hi
  have hir : (i : ℝ) < r := by exact_mod_cast (show i < r by omega)
  have h : ((k : ℝ)-i)*((r : ℝ)-i) ≠ 0 := (mul_pos (by linarith) (by linarith)).ne'
  unfold johnsonBirthRate
  exact_mod_cast h

theorem johnsonDeathRate_succ_ne_zero (k N r i : ℕ) (hkN : k < N-r) :
    johnsonDeathRate k N r (i+1) ≠ 0 := by
  have hN : (k : ℝ)+(r : ℝ) < N := by exact_mod_cast (show k+r < N by omega)
  have h : ((i : ℝ)+1)*((N : ℝ)-k-r+(i+1)) ≠ 0 :=
    (mul_pos (by positivity) (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])).ne'
  simpa [johnsonDeathRate] using!
      (show ((i+1 : ℕ) : ℂ)*((N : ℂ)-k-r+(i+1 : ℕ)) ≠ 0 by exact_mod_cast h)

theorem johnsonOffRate_sq (k N r i : ℕ) (hi : i < k) (hkr : k ≤ r) (hkN : k < N-r) :
    johnsonOffRate k N r i^2 = johnsonBirthRate k r i*johnsonDeathRate k N r (i+1) := by
  simpa only [johnsonOffRate,mul_pow,mul_assoc] using!
    johnsonOverlap_laplacian_offsquare k N r i hi hkr hkN

theorem johnsonOffRate_ne_zero (k N r i : ℕ) (hi : i < k) (hkr : k ≤ r) (hkN : k < N-r) :
    johnsonOffRate k N r i ≠ 0 := by
  intro hz
  have hs := johnsonOffRate_sq k N r i hi hkr hkN
  rw [hz,zero_pow (by decide : 2 ≠ 0)] at hs
  exact (mul_ne_zero (johnsonBirthRate_ne_zero k r i hkr hi)
    (johnsonDeathRate_succ_ne_zero k N r i hkN)) hs.symm

theorem johnsonScale_ne_zero (k N r i : ℕ) (hi : i ≤ k) (hkr : k ≤ r) (hkN : k < N-r) :
    johnsonScale k N r i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hjk : j < k := lt_of_lt_of_le (Finset.mem_range.mp hj) hi
  exact div_ne_zero (johnsonOffRate_ne_zero k N r j hjk hkr hkN)
    (johnsonBirthRate_ne_zero k r j hkr hjk)

theorem johnsonBirthDeath_Jacobi_similarity (k N r : ℕ) (hkr : k ≤ r) (hkN : k < N-r) :
    johnsonBirthDeath k N r * Matrix.diagonal (fun i : Fin (k+1) => johnsonScale k N r i.val) =
      Matrix.diagonal (fun i : Fin (k+1) => johnsonScale k N r i.val)*johnsonJacobi k N r := by
  ext i j
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j
    simp [johnsonBirthDeath,johnsonJacobi,mul_comm]
  · by_cases hup : j.val = i.val+1
    · have hi : i.val < k := by have hj := j.isLt; omega
      have hd : johnsonBirthRate k r i.val ≠ 0 := johnsonBirthRate_ne_zero k r i.val hkr hi
      simp only [johnsonBirthDeath,johnsonJacobi,hij,if_false,hup,if_true,zero_sub]
      simp only [show ¬i.val+1+1 = i.val by omega,if_false,sub_zero]
      rw [johnsonScale_succ]
      field_simp
    · by_cases hdown : j.val+1 = i.val
      · have hj : j.val < k := by have hi := i.isLt; omega
        have hd := johnsonBirthRate_ne_zero k r j.val hkr hj
        have hs := johnsonOffRate_sq k N r j.val hj hkr hkN
        simp only [johnsonBirthDeath,johnsonJacobi,hij,if_false,hup,hdown,if_true,sub_zero,zero_sub]
        rw [← hdown,johnsonScale_succ]
        field_simp
        linear_combination johnsonScale k N r j.val*hs
      · simp [johnsonBirthDeath,johnsonJacobi,hij,hup,hdown]

theorem johnsonJacobi_charpoly (k N r : ℕ) (hkr : k ≤ r) (hkN : k < N-r) :
    (johnsonJacobi k N r).charpoly =
      ∏ j : Fin (k+1), (Polynomial.X-Polynomial.C (johnsonLaplacianValue j.val N)) := by
  let S := Matrix.diagonal (fun i : Fin (k+1) => johnsonScale k N r i.val)
  have hs : IsUnit S.det := isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact johnsonScale_ne_zero k N r i.val (by have hi := i.isLt; omega) hkr hkN)
  have hsim := johnsonBirthDeath_Jacobi_similarity k N r hkr hkN
  change johnsonBirthDeath k N r*S = S*johnsonJacobi k N r at hsim
  have hrepr : johnsonJacobi k N r = S⁻¹*johnsonBirthDeath k N r*S := by
    have hh := congrArg (fun A => S⁻¹*A) hsim
    simpa only [← Matrix.mul_assoc,Matrix.nonsing_inv_mul S hs,Matrix.one_mul] using! hh.symm
  rw [hrepr,Matrix.charpoly_mul_comm]
  rw [← Matrix.mul_assoc,Matrix.mul_nonsing_inv S hs,Matrix.one_mul]
  exact johnsonBirthDeath_charpoly k N r

def johnsonUpperStep (k : ℕ) (B : Fin (k+1) → ℂ) : Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
  fun i j => if j.val = i.val+1 then B i else 0

theorem johnsonUpperStep_gram (k : ℕ) (B : Fin (k+1) → ℂ) (hB : B (Fin.last k) = 0) :
    johnsonUpperStep k B*(johnsonUpperStep k B)ᴴ = Matrix.diagonal (fun i => B i*star (B i)) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val < k
  · let u : Fin (k+1) := ⟨i.val+1,by omega⟩
    rw [Finset.sum_eq_single u]
    · by_cases hij : i = j
      · subst j
        simp [johnsonUpperStep,Matrix.conjTranspose_apply,u]
      · have hne : u.val ≠ j.val+1 := by dsimp [u]; intro hh; apply hij; apply Fin.ext; omega
        have hneq : i.val ≠ j.val := fun h => hij (Fin.ext h)
        simp [johnsonUpperStep,Matrix.conjTranspose_apply,u,hneq,hij]
    · intro v _ hv
      have hvi : ¬v.val = i.val+1 := by intro hh; exact hv (Fin.ext hh)
      simp [johnsonUpperStep,hvi]
    · simp
  · have hik : i = Fin.last k := by apply Fin.ext; have hi' := i.isLt; simp; omega
    have hz : B i = 0 := hik ▸ hB
    simp [johnsonUpperStep,hz,Matrix.diagonal_apply]

theorem johnsonBidiagonal_gram (k : ℕ) (A B : Fin (k+1) → ℂ) (hB : B (Fin.last k) = 0)
    (i j : Fin (k+1)) :
    ((Matrix.diagonal A+johnsonUpperStep k B)*(Matrix.diagonal A+johnsonUpperStep k B)ᴴ) i j =
      (if i = j then A i*star (A i)+B i*star (B i) else 0)+
      (if j.val = i.val+1 then B i*star (A j) else 0)+
      (if i.val = j.val+1 then A i*star (B j) else 0) := by
  rw [Matrix.conjTranspose_add,Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,
    Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,johnsonUpperStep_gram k B hB]
  simp only [Matrix.add_apply,Matrix.diagonal_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,
    Matrix.conjTranspose_apply,johnsonUpperStep,Pi.star_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp only [hij,if_false]
    split_ifs <;> simp only [star_zero,mul_zero,zero_mul,add_zero,zero_add]
    all_goals ring

def johnsonOverlapMatrix (k : ℕ) (d e : ℝ) : Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
  (johnsonPlusFrame k d)ᴴ*johnsonReverseFrame k e

theorem johnsonOverlapMatrix_bidiagonal (k : ℕ) (d e : ℝ) :
    johnsonOverlapMatrix k d e =
      Matrix.diagonal (fun i => johnsonOverlapDiagonal k i.val d e)+
        johnsonUpperStep k (fun i => johnsonOverlapUpper k i.val d e) := by
  ext i j
  rw [johnsonOverlapMatrix,johnsonOverlap_bidiagonal]
  simp only [Matrix.add_apply,Matrix.diagonal_apply,johnsonUpperStep,johnsonOverlapDiagonal,johnsonOverlapUpper]

theorem johnsonOverlapMatrix_compression (k N r : ℕ) (hkr : k ≤ r) (hkN : k < N-r) :
    ((((N : ℝ)-r)*((r : ℝ)+1) : ℂ) •
      (1-johnsonOverlapMatrix k ((N : ℝ)-r) ((r : ℝ)+1)*
        (johnsonOverlapMatrix k ((N : ℝ)-r) ((r : ℝ)+1))ᴴ)) = johnsonJacobi k N r := by
  let d : ℝ := (N : ℝ)-r
  let e : ℝ := (r : ℝ)+1
  let A : Fin (k+1) → ℂ := fun i => johnsonOverlapDiagonal k i.val d e
  let B : Fin (k+1) → ℂ := fun i => johnsonOverlapUpper k i.val d e
  have hB : B (Fin.last k) = 0 := by simp [B,johnsonOverlapUpper]
  have hAstar (i : Fin (k+1)) : star (A i) = A i := by simp [A,johnsonOverlapDiagonal]
  have hBstar (i : Fin (k+1)) : star (B i) = B i := by simp [B,johnsonOverlapUpper]
  ext i j
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply,Matrix.one_apply]
  rw [johnsonOverlapMatrix_bidiagonal]
  have hdc : ((N : ℝ) : ℂ)-(r : ℂ) = (d : ℂ) := by simp [d]
  have hec : ((r : ℝ) : ℂ)+1 = (e : ℂ) := by simp [e]
  rw [hdc,hec]
  change ((d : ℂ)*(e : ℂ))*((if i=j then 1 else 0)-
    ((Matrix.diagonal A+johnsonUpperStep k B)*(Matrix.diagonal A+johnsonUpperStep k B)ᴴ) i j) = _
  rw [johnsonBidiagonal_gram k A B hB i j,hAstar,hBstar,hAstar,hBstar]
  by_cases hij : i = j
  · subst j
    have hi : i.val ≤ k := by have hh := i.isLt; omega
    have hh := johnsonOverlap_laplacian_diagonal k N r i.val hi hkr hkN
    simpa [johnsonJacobi,d,e,A,B,pow_two,sub_add_eq_sub_sub] using! hh
  · by_cases hup : j.val = i.val+1
    · simp [johnsonJacobi,hij,hup]
      dsimp [A,B,d,e,johnsonOffRate]
      rw [hup]
      simp [show ¬i.val = i.val+1+1 by omega,show ¬i.val+1+1 = i.val by omega]
      ring
    · by_cases hdown : i.val = j.val+1
      · simp [johnsonJacobi,hij,hdown]
        dsimp [A,B,d,e,johnsonOffRate]
        rw [hdown]
        simp [show ¬j.val = j.val+1+1 by omega]
        ring
      · have hdown' : ¬j.val+1 = i.val := fun h => hdown h.symm
        simp [johnsonJacobi,hij,hup,hdown,hdown']

theorem johnsonOverlapMatrix_compression_charpoly (k N r : ℕ) (hkr : k ≤ r) (hkN : k < N-r) :
    (((((N : ℝ)-r)*((r : ℝ)+1) : ℂ) •
      (1-johnsonOverlapMatrix k ((N : ℝ)-r) ((r : ℝ)+1)*
        (johnsonOverlapMatrix k ((N : ℝ)-r) ((r : ℝ)+1))ᴴ))).charpoly =
      ∏ j : Fin (k+1), (Polynomial.X-Polynomial.C (johnsonLaplacianValue j.val N)) := by
  rw [johnsonOverlapMatrix_compression k N r hkr hkN]
  exact johnsonJacobi_charpoly k N r hkr hkN

def principalPairReflection {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (2 : ℂ) • (P*Pᴴ)-1

theorem principalPairReflection_sq {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℂ)
    (hP : Pᴴ*P = 1) : principalPairReflection P * principalPairReflection P = 1 := by
  have hE : (P*Pᴴ)*(P*Pᴴ) = P*Pᴴ := by
    calc
      _ = P*(Pᴴ*P)*Pᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP]; simp
  unfold principalPairReflection
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  rw [hE]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  ring

theorem principalPairReflection_fix {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℂ)
    (hP : Pᴴ*P = 1) (v : Fin m → ℂ) :
    principalPairReflection P *ᵥ (P *ᵥ v) = P *ᵥ v := by
  unfold principalPairReflection
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec,
    show P*Pᴴ*P = P from by rw [Matrix.mul_assoc,hP,Matrix.mul_one]]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem principalPair_compressed {n m : ℕ} (P Q : Matrix (Fin n) (Fin m) ℂ)
    (hP : Pᴴ*P = 1) (σ : ℂ) (v : Fin m → ℂ)
    (hv : ((Pᴴ*Q)*(Pᴴ*Q)ᴴ) *ᵥ v = σ • v) :
    Pᴴ *ᵥ (principalPairReflection Q *ᵥ (P *ᵥ v)) = (2*σ-1) • v := by
  have he : Pᴴ*(Q*Qᴴ)*P = (Pᴴ*Q)*(Pᴴ*Q)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  unfold principalPairReflection
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, he, hv,
    Matrix.mulVec_mulVec,hP,Matrix.one_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem principalPair_recurrence {n m : ℕ} (P Q : Matrix (Fin n) (Fin m) ℂ)
    (hP : Pᴴ*P = 1) (hQ : Qᴴ*Q = 1) (σ : ℂ) (v : Fin m → ℂ)
    (hv : ((Pᴴ*Q)*(Pᴴ*Q)ᴴ) *ᵥ v = σ • v) :
    let W := principalPairReflection Q * principalPairReflection P
    let x := P *ᵥ v
    let y := principalPairReflection Q *ᵥ x
    W *ᵥ x = y ∧ W *ᵥ y = (2*(2*σ-1)) • y-x := by
  (try dsimp only)
  constructor
  · rw [← Matrix.mulVec_mulVec, principalPairReflection_fix P hP]
  · rw [← Matrix.mulVec_mulVec]
    change principalPairReflection Q *ᵥ
      (((2 : ℂ) • (P*Pᴴ)-1) *ᵥ (principalPairReflection Q *ᵥ (P *ᵥ v))) = _
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      principalPair_compressed P Q hP σ v hv, Matrix.mulVec_smul, Matrix.mulVec_sub,
      Matrix.mulVec_smul]
    simp only [Matrix.mulVec_smul,smul_smul]
    have hR2 : principalPairReflection Q *ᵥ (principalPairReflection Q *ᵥ (P *ᵥ v)) = P *ᵥ v := by
      rw [Matrix.mulVec_mulVec, principalPairReflection_sq Q hQ, Matrix.one_mulVec]
    rw [hR2]

theorem principalPair_eigenvector {n m : ℕ} (P Q : Matrix (Fin n) (Fin m) ℂ)
    (hP : Pᴴ*P = 1) (hQ : Qᴴ*Q = 1) (σ μ : ℂ) (v : Fin m → ℂ)
    (hv0 : v ≠ 0) (hv : ((Pᴴ*Q)*(Pᴴ*Q)ᴴ) *ᵥ v = σ • v)
    (hμ : μ^2-2*(2*σ-1)*μ+1 = 0) (hμsq : μ^2 ≠ 1) :
    let x := P *ᵥ v
    let z := x-μ • (principalPairReflection Q *ᵥ x)
    z ≠ 0 ∧ (principalPairReflection Q * principalPairReflection P) *ᵥ z = μ • z := by
  (try dsimp only)
  let x := P *ᵥ v
  let y := principalPairReflection Q *ᵥ x
  have hx : x ≠ 0 := by
    intro hx
    apply hv0
    have h := congrArg (fun u => Pᴴ *ᵥ u) hx
    simpa only [x, Matrix.mulVec_mulVec, hP, Matrix.one_mulVec, Matrix.mulVec_zero] using! h
  obtain ⟨hwx,hwy⟩ := principalPair_recurrence P Q hP hQ σ v hv
  have hR : principalPairReflection Q *ᵥ y = x := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec,principalPairReflection_sq Q hQ,Matrix.one_mulVec]
  constructor
  · intro hz
    change x-μ • y = 0 at hz
    have heq : x = μ • y := sub_eq_zero.mp hz
    have hyx : y = μ • x := by
      have he := congrArg (fun u => principalPairReflection Q *ᵥ u) heq
      simpa only [Matrix.mulVec_smul,hR] using! he
    have hxx : x = μ^2 • x := by
      calc
        x = μ • y := heq
        _ = μ • (μ • x) := congrArg (fun u => μ • u) hyx
        _ = μ^2 • x := by rw [smul_smul,pow_two]
    have hscalar : (1-μ^2) • x = 0 := by
      rw [sub_smul,one_smul,← hxx,sub_self]
    have hnon : (1-μ^2 : ℂ) ≠ 0 := by intro h; apply hμsq; linear_combination -h
    exact hx ((smul_eq_zero.mp hscalar).resolve_left hnon)
  · rw [Matrix.mulVec_sub,Matrix.mulVec_smul,hwx,hwy]
    ext i
    have h := congrArg (fun c : ℂ => c * y i) hμ
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at h ⊢
    linear_combination h

theorem principalPair_normalize {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (z : Fin n → ℂ) (hz0 : z ≠ 0) (hz : W *ᵥ z = μ • z) :
    ∃ u : Fin n → ℂ, Normalized u ∧ W *ᵥ u = μ • u := by
  have he : toEuclidean_fromVec z ≠ 0 := by
    intro he
    apply hz0
    have h := congrArg (fun f : EuclideanSpace ℂ (Fin n) => fun i => f i) he
    simpa only [toEuclidean_fromVec, PiLp.zero_apply] using! h
  have hnorm : ‖toEuclidean_fromVec z‖ ≠ 0 := norm_ne_zero_iff.mpr he
  let a : ℂ := ((‖toEuclidean_fromVec z‖ : ℝ)⁻¹ : ℝ)
  let u := a • z
  refine ⟨u,?_,?_⟩
  · rw [normalized_iff_norm_toEuclidean_fromVec]
    change ‖a • toEuclidean_fromVec z‖ = 1
    rw [norm_smul]
    simp [a, Complex.norm_real, inv_mul_cancel₀ hnorm]
  · dsimp only [u]
    rw [Matrix.mulVec_smul,hz,smul_comm]

theorem principalPair_normalized_eigenvector {n m : ℕ} (P Q : Matrix (Fin n) (Fin m) ℂ)
    (hP : Pᴴ*P = 1) (hQ : Qᴴ*Q = 1) (σ μ : ℂ) (v : Fin m → ℂ)
    (hv0 : v ≠ 0) (hv : ((Pᴴ*Q)*(Pᴴ*Q)ᴴ) *ᵥ v = σ • v)
    (hμ : μ^2-2*(2*σ-1)*μ+1 = 0) (hμsq : μ^2 ≠ 1) :
    ∃ u : Fin n → ℂ, Normalized u ∧
      (principalPairReflection Q * principalPairReflection P) *ᵥ u = μ • u := by
  obtain ⟨hz0,hz⟩ := principalPair_eigenvector P Q hP hQ σ μ v hv0 hv hμ hμsq
  exact principalPair_normalize _ μ _ hz0 hz

def johnsonDen (N r : ℕ) : ℂ := ((N : ℂ)-r)*((r : ℂ)+1)

theorem johnsonDen_ne_zero (k N r : ℕ) (hkN : k < N-r) : johnsonDen N r ≠ 0 := by
  have hN : (r : ℝ) < N := by exact_mod_cast (show r < N by omega)
  have hh : ((N : ℝ)-r)*((r : ℝ)+1) ≠ 0 := (mul_pos (by linarith) (by positivity)).ne'
  unfold johnsonDen
  exact_mod_cast hh

theorem johnsonPhase_cos_exact (k N r j : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r)
    (hkN : k < N-r) (hj : 1 ≤ j) (hjk : j ≤ k) :
    (Real.cos (johnsonPhase j N r) : ℂ) = 1-2*johnsonLaplacianValue j N/johnsonDen N r := by
  obtain ⟨hlo,hhi⟩ := johnsonPhase_cosine_bounds k N r j hk hkr hkN hj hjk
  unfold johnsonPhase
  rw [Real.cos_arccos hlo.le hhi.le]
  unfold johnsonLaplacianValue johnsonDen
  push_cast
  ring

theorem johnsonJacobi_eigenvector_gram (k N r : ℕ) (hkr : k ≤ r) (hkN : k < N-r)
    (lam : ℂ) (v : Fin (k+1) → ℂ) (hv : johnsonJacobi k N r *ᵥ v = lam • v) :
    (johnsonOverlapMatrix k ((N : ℝ)-r) ((r : ℝ)+1)*
      (johnsonOverlapMatrix k ((N : ℝ)-r) ((r : ℝ)+1))ᴴ) *ᵥ v =
      (1-lam/johnsonDen N r) • v := by
  have he := johnsonOverlapMatrix_compression k N r hkr hkN
  have he' : johnsonDen N r • (1-johnsonOverlapMatrix k ((N : ℝ)-r) ((r : ℝ)+1)*
      (johnsonOverlapMatrix k ((N : ℝ)-r) ((r : ℝ)+1))ᴴ) = johnsonJacobi k N r := by
    simpa only [johnsonDen,Complex.ofReal_natCast] using! he
  rw [← he',Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec] at hv
  have hden := johnsonDen_ne_zero k N r hkN
  ext i
  have h := congrFun hv i
  simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul] at h ⊢
  apply mul_left_cancel₀ hden
  field_simp
  linear_combination -h

theorem johnsonWalk_principalPair (k N r : ℕ) (hkr : k ≤ r) (hkN : k < N-r) :
    jwWalk k N r = principalPairReflection (johnsonReverseFrame k ((r : ℝ)+1))*
      principalPairReflection (johnsonPlusFrame k ((N : ℝ)-r)) := by
  obtain ⟨h1,h2⟩ := johnsonHalfSteps_frames k N r hkr hkN
  rw [jwWalk,h1,h2]
  rfl

theorem principalPair_charpoly_eigenvector (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ)
    (lam : ℂ) (hroot : A.charpoly.eval lam = 0) :
    ∃ v : Fin m → ℂ, v ≠ 0 ∧ A *ᵥ v = lam • v := by
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v,hv,he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  refine ⟨v,hv,?_⟩
  rw [Matrix.sub_mulVec] at he
  have hscalar : Matrix.scalar (Fin m) lam *ᵥ v = lam • v := by
    ext i
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  rw [hscalar] at he
  exact (sub_eq_zero.mp he).symm

theorem principalPair_unit_eigenvalue (n : ℕ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (e : ℂ) (v : Fin n → ℂ)
    (hnorm : Normalized v) (heig : U *ᵥ v = e • v) : star e * e = 1 := by
  have hs := inner_applyGate hU v v
  change Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v)
      (U *ᵥ v) = Qatlib.Foundations.PureStateMath.Inner v v at hs
  rw [heig] at hs
  simp only [Qatlib.Foundations.PureStateMath.Inner, star_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul] at hs
  have hself : star v ⬝ᵥ v = 1 := (normalized_iff_inner_self v).mp hnorm
  rw [hself] at hs
  simpa only [mul_one,one_mul,mul_comm] using! hs

theorem principalPair_ordered_eigenframe (n : ℕ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (e : Fin n → ℂ)
    (hinj : Function.Injective e)
    (hex : ∀ i : Fin n, ∃ v : Fin n → ℂ, Normalized v ∧ U *ᵥ v = e i • v) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, B ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      U*B = B*Matrix.diagonal e := by
  classical
  choose v hnorm heig using hex
  have hU' : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have heunit : ∀ i, star (e i)*e i = 1 :=
    fun i => principalPair_unit_eigenvalue n U hU (e i) (v i) (hnorm i) (heig i)
  let B : Matrix (Fin n) (Fin n) ℂ := fun i j => v j i
  have hBB : Bᴴ*B = 1 := by
    ext i j
    change star (v i) ⬝ᵥ v j = if i = j then 1 else 0
    by_cases hij : i = j
    · subst j
      simpa only [if_pos rfl] using! (normalized_iff_inner_self (v i)).mp (hnorm i)
    · rw [if_neg hij]
      exact jw_unitary_distinct_eigenvectors_orthogonal n U (v i) (v j) (e i) (e j)
        hU' (heunit i) (heig i) (heig j) (fun h => hij (hinj h))
  have hB : B ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simpa only [Matrix.star_eq_conjTranspose] using! hBB
  refine ⟨B,hB,?_⟩
  ext i j
  rw [Matrix.mul_diagonal]
  change (U *ᵥ v j) i = B i j * e j
  rw [heig j]
  simp only [B, Pi.smul_apply, smul_eq_mul, mul_comm]

namespace JohnsonSpectrumPhase

end JohnsonSpectrumPhase

theorem johnsonJacobi_eigenvalue (k N r : ℕ) (hkr : k ≤ r) (hkN : k < N-r) (j : Fin (k+1)) :
    ∃ v : Fin (k+1) → ℂ, v ≠ 0 ∧ johnsonJacobi k N r *ᵥ v = johnsonLaplacianValue j.val N • v := by
  apply principalPair_charpoly_eigenvector
  rw [johnsonJacobi_charpoly k N r hkr hkN,Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp

theorem johnsonFullSpectrum_answer : JohnsonFullSpectrumContract := by
  intro k N r hk hkr hkN
  let θ : Fin k → ℝ := fun j => johnsonPhase (j.val+1) N r
  let e := Qatlib.Concepts.WalkFind.WalkSpectrum.phaseEigenvalues θ
  have hθ : ∀ j : Fin k, 0 < θ j ∧ θ j < Real.pi := by
    intro j
    exact johnsonPhase_strict_bounds k N r (j.val+1) hk hkr hkN (by omega) (by omega)
  have hmono : StrictMono θ := johnsonPhase_strictMono k N r hkr hkN
  have hinj : Function.Injective e :=
      Qatlib.Concepts.WalkFind.WalkSpectrum.phaseEigenvalues_injective θ hmono hθ
  have hu : jwWalk k N r ∈ Matrix.unitaryGroup (Fin (2*k+1)) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    exact (walkUnitary k N r hkN.le (by omega)).2.2.1
  have hex (i : Fin (2*k+1)) :
      ∃ v : Fin (2*k+1) → ℂ, Normalized v ∧ jwWalk k N r *ᵥ v = e i • v := by
    by_cases hi : i.val = 0
    · have hie : i = ⟨0,by omega⟩ := Fin.ext hi
      rw [hie,show e ⟨0,by omega⟩ = 1 from Qatlib.Concepts.WalkFind.WalkSpectrum.phaseEigenvalues_zero θ]
      have hs := jwNormalizedSearch_inputs k N r 1 hk hkr hkN
      refine ⟨_,hs.2.1,?_⟩
      simpa only [pow_one,one_smul] using! hs.2.2.2.2.1
    · let j : Fin k := Qatlib.Concepts.WalkFind.WalkSpectrum.phaseIndex i hi
      let jj : Fin (k+1) := ⟨j.val+1,by omega⟩
      let lam := johnsonLaplacianValue jj.val N
      let σ : ℂ := 1-lam/johnsonDen N r
      obtain ⟨v,hv0,hv⟩ := johnsonJacobi_eigenvalue k N r hkr hkN jj
      have hg := johnsonJacobi_eigenvector_gram k N r hkr hkN lam v hv
      have hcos : (Real.cos (θ j) : ℂ) = 2*σ-1 := by
        rw [johnsonPhase_cos_exact k N r (j.val+1) hk hkr hkN (by omega) (by omega)]
        dsimp only [σ,lam,jj]
        ring
      have hquad : (e i)^2-2*(2*σ-1)*e i+1 = 0 := by
        rw [← hcos]
        exact Qatlib.Concepts.WalkFind.WalkSpectrum.phaseEigenvalues_quadratic θ i hi
      let P := johnsonPlusFrame k ((N : ℝ)-r)
      let Q := johnsonReverseFrame k ((r : ℝ)+1)
      have hd : (k : ℝ) < (N : ℝ)-r := by
        have hh : (k : ℝ)+(r : ℝ) < N := by exact_mod_cast (show k+r < N by omega)
        linarith
      have hr : (k : ℝ) < (r : ℝ)+1 := by exact_mod_cast (show k < r+1 by omega)
      have hP : Pᴴ*P = 1 := johnsonPlusFrame_isometry k _ hd
      have hQ : Qᴴ*Q = 1 := johnsonReverseFrame_isometry k _ hr
      obtain ⟨u,hun,hue⟩ := principalPair_normalized_eigenvector P Q hP hQ σ (e i) v hv0 hg hquad
        (Qatlib.Concepts.WalkFind.WalkSpectrum.phaseEigenvalues_sq_ne_one θ hθ i hi)
      refine ⟨u,hun,?_⟩
      rw [johnsonWalk_principalPair k N r hkr hkN]
      exact hue
  obtain ⟨B,hB,hBW⟩ := principalPair_ordered_eigenframe (2*k+1) (jwWalk k N r) hu e hinj hex
  refine ⟨B,e,hB,hinj,hBW,Qatlib.Concepts.WalkFind.WalkSpectrum.phaseEigenvalues_zero θ,?_⟩
  intro j
  exact ⟨Qatlib.Concepts.WalkFind.WalkSpectrum.phaseEigenvalues_plus θ j,Qatlib.Concepts.WalkFind.WalkSpectrum.phaseEigenvalues_minus θ j⟩

end Qatlib.Concepts.WalkFind.WalkSpectrum
