/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.GeneratorSeries
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.CommutatorExp
variable {A : Type*} [NormedRing A]

def Central (z : A) : Prop := ∀ X : A,Commute z X

theorem central_sum (zs : List A) (hz : ∀ z∈zs,Central z) : Central zs.sum := by
  induction zs with
  | nil => intro X;change (0:A)*X=X*0;simp
  | cons z zs ih =>
    intro X
    change Commute (z+zs.sum) X
    exact (hz z (by simp) X).add_left (ih (fun q hq => hz q (by simp [hq])) X)

theorem ad_add_central_left (H X z : A) (hz : Central z) : ad (H+z) X=ad H X := by
  simp only [ad,add_mul,mul_add]
  rw [(hz X).eq]
  abel

theorem adIter_add (H X Y : A) (n : ℕ) : adIter H n (X+Y)=adIter H n X+adIter H n Y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [adIter,ih];unfold ad;noncomm_ring

theorem adIter_central_pos (H z : A) (hz : Central z) (n : ℕ) (hn : 0<n) : adIter H n z=0 := by
  have hc : ad H z=0 := by unfold ad;rw [(hz H).eq];exact sub_self _
  cases n with
  | zero => omega
  | succ n =>
    clear hn
    induction n with
    | zero => exact hc
    | succ n ih => rw [adIter,ih];simp [ad]

theorem adIter_add_central_left (H X z : A) (hz : Central z) (n : ℕ) :
    adIter (H+z) n X=adIter H n X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ad (H+z) (adIter (H+z) n X)=ad H (adIter H n X)
    rw [ih,ad_add_central_left H _ z hz]

theorem adIter_add_central_right (H X z : A) (hz : Central z) (n : ℕ) (hn : 0<n) :
    adIter H n (X+z)=adIter H n X := by
  rw [adIter_add,adIter_central_pos H z hz n hn,add_zero]

theorem sum_stage_shifts (ps : List (A×A)) :
    (ps.map (fun p => p.1+p.2)).sum=(ps.map Prod.fst).sum+(ps.map Prod.snd).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons,List.sum_cons,ih];abel
variable [NormedAlgebra ℝ A]

theorem generatorCoefficient_zero (ks : List A) : generatorCoefficient ks 0=ks.sum := by
  induction ks with
  | nil => rfl
  | cons K ks ih => simp [generatorCoefficient,adIter,ih]

theorem generatorCoefficient_central_shift (ps : List (A×A))
    (hz : ∀ p∈ps,Central p.2) (n : ℕ) :
    generatorCoefficient (ps.map (fun p => p.1+p.2)) n=
      generatorCoefficient (ps.map Prod.fst) n+
        if n=0 then (ps.map Prod.snd).sum else 0 := by
  induction ps generalizing n with
  | nil => simp [generatorCoefficient]
  | cons p ps ih =>
    have hhead : Central p.2 := hz p (by simp)
    have htail : ∀ q∈ps,Central q.2 := fun q hq => hz q (by simp [hq])
    by_cases hn : n=0
    · subst n
      rw [generatorCoefficient_zero,generatorCoefficient_zero]
      exact sum_stage_shifts (p::ps)
    · simp only [List.map_cons,generatorCoefficient,if_neg hn,zero_add,add_zero]
      apply Finset.sum_congr rfl
      intro ij hij
      rw [adIter_add_central_left p.1 _ p.2 hhead,ih htail ij.2]
      by_cases hj : ij.2=0
      · rw [if_pos hj]
        have hi : 0 < ij.1 := by have hs := Finset.mem_antidiagonal.mp hij;omega
        have hc : Central ((ps.map Prod.snd).sum) :=
          central_sum _ (by
            intro z hz
            obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
            exact htail q hq)
        rw [adIter_add_central_right p.1 _ _ hc ij.1 hi]
      · rw [if_neg hj,add_zero]
variable [CompleteSpace A]

theorem conjugation_add_central (H X z : A) (hz : Central z) (t : ℝ) :
    NormedSpace.exp (t • (H+z))*X*NormedSpace.exp ((-t) • (H+z))=
      NormedSpace.exp (t • H)*X*NormedSpace.exp ((-t) • H) := by
  apply (conjugation_hasSum (H+z) X t).unique
  simpa only [adIter_add_central_left H X z hz] using conjugation_hasSum H X t
end Qatlib.Foundations.MatrixAlgebra.CommutatorExp
