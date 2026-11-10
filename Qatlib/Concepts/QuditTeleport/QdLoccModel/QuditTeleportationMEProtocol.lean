/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationDefs
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.QdLoccModel.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.MessagingBounds.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundRestrictedTele
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationBranchMarginal
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError false
open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped ComplexOrder

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel
open Matrix
open scoped BigOperators ComplexOrder
open scoped BigOperators
set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
open Matrix Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
noncomputable def clause4Aux_meKraus (n : ℕ) [NeZero n] (o : Fin n × Fin n) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun u p => (if u = (0, 0) then (1 : ℂ) else 0)
    * (QFTMatrix n)ᴴ o.1 p.1 * (if p.2 = quditAdd n o.2 p.1 then (1 : ℂ) else 0)

theorem clause4Aux_quditAdd_sum_one (n : ℕ) [NeZero n] (a c : Fin n) :
    ∑ o2 : Fin n, (if a = quditAdd n o2 c then (1 : ℂ) else 0) = 1 := by
  have hcomp : (∑ o2 : Fin n, (if a = quditAdd n o2 c then (1 : ℂ) else 0))
      = ∑ x : Fin n, (if a = x then (1 : ℂ) else 0) :=
    Equiv.sum_comp (quditShiftEquiv n ((ZMod.finEquiv n) c))
      (fun x => if a = x then (1 : ℂ) else 0)
  rw [hcomp, Finset.sum_ite_eq, if_pos (Finset.mem_univ a)]

theorem clause4Aux_quditAdd_cross_sum (n : ℕ) [NeZero n] (a a' c : Fin n) :
    ∑ o2 : Fin n, (if a = quditAdd n o2 c then (1 : ℂ) else 0)
        * (if a' = quditAdd n o2 c then (1 : ℂ) else 0)
      = if a = a' then (1 : ℂ) else 0 := by
  by_cases haa' : a = a'
  · subst haa'
    rw [if_pos rfl]
    have h : ∀ o2 : Fin n, (if a = quditAdd n o2 c then (1 : ℂ) else 0)
        * (if a = quditAdd n o2 c then (1 : ℂ) else 0)
        = (if a = quditAdd n o2 c then (1 : ℂ) else 0) := by
      intro o2
      by_cases hq : a = quditAdd n o2 c <;> simp [hq]
    rw [Finset.sum_congr rfl (fun o2 _ => h o2)]
    exact clause4Aux_quditAdd_sum_one n a c
  · rw [if_neg haa']
    apply Finset.sum_eq_zero
    intro o2 _
    by_cases hq : a = quditAdd n o2 c
    · by_cases hq' : a' = quditAdd n o2 c
      · exact absurd (hq.trans hq'.symm) haa'
      · simp [hq, hq']
    · simp [hq]

theorem clause4Aux_qft_col_orth (n : ℕ) [NeZero n] (c c' : Fin n) :
    ∑ o1 : Fin n, star ((QFTMatrix n)ᴴ o1 c) * (QFTMatrix n)ᴴ o1 c'
      = if c = c' then (1 : ℂ) else 0 := by
  have h1 : (QFTMatrix n) * (QFTMatrix n)ᴴ = 1 :=
    qftMatrix_mul_conjTranspose n (Nat.pos_of_ne_zero (NeZero.ne n))
  have h2 : ((QFTMatrix n)ᴴ).conjTranspose * (QFTMatrix n)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact h1
  have h3 : (∑ o1 : Fin n, star ((QFTMatrix n)ᴴ o1 c) * (QFTMatrix n)ᴴ o1 c')
      = (((QFTMatrix n)ᴴ).conjTranspose * (QFTMatrix n)ᴴ) c c' := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h3, h2, Matrix.one_apply]

theorem clause4Aux_rowKraus_me (n : ℕ) [NeZero n] (Ψ : QState (Fin n × Fin n)) (o u : Fin n × Fin n) :
    qdRowKraus (clause4Aux_meKraus n o) Ψ u
      = (if u = (0, 0) then (1 : ℂ) else 0) • quditResourceBranchKraus n Ψ o := by
  classical
  ext i c
  set w : ℂ := if u = (0, 0) then (1 : ℂ) else 0
  set q : Fin n := quditAdd n o.2 c
  set M : ℂ := (QFTMatrix n)ᴴ o.1 c
  have hL : qdRowKraus (clause4Aux_meKraus n o) Ψ u i c
      = w * M * Ψ (q, i) := by
    have h1 : qdRowKraus (clause4Aux_meKraus n o) Ψ u i c
        = ∑ a : Fin n, Ψ (a, i) * (w * M * (if a = q then (1 : ℂ) else 0)) := by
      simp only [qdRowKraus, qdMatW, qdMatA, clause4Aux_meKraus, Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun a _ => by
        simp only [w, q, M])
    rw [h1]
    have h2 : ∀ a : Fin n, Ψ (a, i) * (w * M * (if a = q then (1 : ℂ) else 0))
        = if a = q then w * M * Ψ (a, i) else 0 := by
      intro a
      by_cases ha : a = q <;> simp [ha, mul_comm]
    rw [Finset.sum_congr rfl (fun a _ => h2 a), Finset.sum_ite_eq',
      if_pos (Finset.mem_univ q)]
  have hR : quditResourceBranchKraus n Ψ o i c = M * Ψ (q, i) := by
    rw [quditResourceBranchKraus_entry]
  rw [hL, Matrix.smul_apply, smul_eq_mul, hR]
  ring

theorem g8p_conjBranch_smul {n : ℕ} (c : ℂ) (B ρ : Operator n) :
    conjBranch (c • B) ρ = (c * star c) • conjBranch B ρ := by
  simp only [conjBranch_apply, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [mul_comm (star c) c]

theorem clause4Aux_branch_me (n : ℕ) [NeZero n] (Ψ : QState (Fin n × Fin n)) (o : Fin n × Fin n)
    (ρ : Operator n) :
    qdBranchMarginal (clause4Aux_meKraus n o) (outerProduct Ψ) ρ
      = conjBranch (quditResourceBranchKraus n Ψ o) ρ := by
  classical
  rw [qdBranchMarginal_outerProduct_kraus]
  have hkey : ∀ u : Fin n × Fin n,
      conjBranch (qdRowKraus (clause4Aux_meKraus n o) Ψ u) ρ
        = if u = (0, 0) then conjBranch (quditResourceBranchKraus n Ψ o) ρ else 0 := by
    intro u
    by_cases hu : u = (0, 0)
    · subst hu
      simp only [if_true]
      rw [clause4Aux_rowKraus_me, if_pos rfl, one_smul]
    · simp only [hu, if_false]
      rw [clause4Aux_rowKraus_me, if_neg hu, zero_smul]
      simp only [conjBranch_apply]
      simp
  rw [Finset.sum_congr rfl (fun u _ => hkey u), Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _)]

private theorem clause4Aux_meKraus_rowGram (n : ℕ) [NeZero n] (o : Fin n × Fin n)
    (p q : Fin n × Fin n) :
    (∑ u : Fin n × Fin n, star (clause4Aux_meKraus n o u p) * clause4Aux_meKraus n o u q)
      = star ((QFTMatrix n)ᴴ o.1 p.1 * (if p.2 = quditAdd n o.2 p.1 then (1 : ℂ) else 0))
          * ((QFTMatrix n)ᴴ o.1 q.1 * (if q.2 = quditAdd n o.2 q.1 then (1 : ℂ) else 0)) := by
  classical
  set Lp : ℂ := (QFTMatrix n)ᴴ o.1 p.1 * (if p.2 = quditAdd n o.2 p.1 then (1 : ℂ) else 0)
  set Lq : ℂ := (QFTMatrix n)ᴴ o.1 q.1 * (if q.2 = quditAdd n o.2 q.1 then (1 : ℂ) else 0)
  have h : ∀ u : Fin n × Fin n,
      star (clause4Aux_meKraus n o u p) * clause4Aux_meKraus n o u q
        = (if u = (0, 0) then (1 : ℂ) else 0) * (star Lp * Lq) := by
    intro u
    simp only [clause4Aux_meKraus, Lp, Lq]
    by_cases hu : u = (0, 0) <;> simp [hu]
  rw [Finset.sum_congr rfl (fun u _ => h u)]
  rw [← Finset.sum_mul]
  have hsum : (∑ u : Fin n × Fin n, (if u = (0, 0) then (1 : ℂ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [hsum, one_mul]

theorem clause4Aux_meKraus_complete (n : ℕ) [NeZero n] :
    ∑ o : Fin n × Fin n, (clause4Aux_meKraus n o)ᴴ * clause4Aux_meKraus n o = 1 := by
  classical
  ext p q
  have h1 : ((∑ o : Fin n × Fin n, (clause4Aux_meKraus n o)ᴴ * clause4Aux_meKraus n o)) p q
      = ∑ o : Fin n × Fin n, ∑ u : Fin n × Fin n,
          star (clause4Aux_meKraus n o u p) * clause4Aux_meKraus n o u q := by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h1]
  have h2 : ∀ o : Fin n × Fin n,
      (∑ u : Fin n × Fin n, star (clause4Aux_meKraus n o u p) * clause4Aux_meKraus n o u q)
        = star ((QFTMatrix n)ᴴ o.1 p.1 * (if p.2 = quditAdd n o.2 p.1 then (1 : ℂ) else 0))
            * ((QFTMatrix n)ᴴ o.1 q.1 * (if q.2 = quditAdd n o.2 q.1 then (1 : ℂ) else 0)) :=
    fun o => clause4Aux_meKraus_rowGram n o p q
  rw [Finset.sum_congr rfl (fun o _ => h2 o)]
  rw [Fintype.sum_prod_type]
  have hterm : ∀ (o1 o2 : Fin n),
      star ((QFTMatrix n)ᴴ o1 p.1 * (if p.2 = quditAdd n o2 p.1 then (1 : ℂ) else 0))
        * ((QFTMatrix n)ᴴ o1 q.1 * (if q.2 = quditAdd n o2 q.1 then (1 : ℂ) else 0))
      = (star ((QFTMatrix n)ᴴ o1 p.1) * (QFTMatrix n)ᴴ o1 q.1)
          * ((if p.2 = quditAdd n o2 p.1 then (1 : ℂ) else 0)
              * (if q.2 = quditAdd n o2 q.1 then (1 : ℂ) else 0)) := by
    intro o1 o2
    by_cases hp : p.2 = quditAdd n o2 p.1 <;>
      by_cases hq : q.2 = quditAdd n o2 q.1 <;>
      simp [hp, hq, mul_comm]
  have h3 : (∑ o1 : Fin n, ∑ o2 : Fin n,
      star ((QFTMatrix n)ᴴ o1 p.1 * (if p.2 = quditAdd n o2 p.1 then (1 : ℂ) else 0))
        * ((QFTMatrix n)ᴴ o1 q.1 * (if q.2 = quditAdd n o2 q.1 then (1 : ℂ) else 0)))
      = (∑ o1 : Fin n, star ((QFTMatrix n)ᴴ o1 p.1) * (QFTMatrix n)ᴴ o1 q.1)
          * (∑ o2 : Fin n, (if p.2 = quditAdd n o2 p.1 then (1 : ℂ) else 0)
              * (if q.2 = quditAdd n o2 q.1 then (1 : ℂ) else 0)) := by
    rw [Finset.sum_congr rfl (fun o1 _ => Finset.sum_congr rfl (fun o2 _ => hterm o1 o2))]
    have h4 : (∑ o1 : Fin n, ∑ o2 : Fin n,
        (star ((QFTMatrix n)ᴴ o1 p.1) * (QFTMatrix n)ᴴ o1 q.1)
          * ((if p.2 = quditAdd n o2 p.1 then (1 : ℂ) else 0)
              * (if q.2 = quditAdd n o2 q.1 then (1 : ℂ) else 0)))
        = (∑ o1 : Fin n, star ((QFTMatrix n)ᴴ o1 p.1) * (QFTMatrix n)ᴴ o1 q.1)
            * (∑ o2 : Fin n, (if p.2 = quditAdd n o2 p.1 then (1 : ℂ) else 0)
                * (if q.2 = quditAdd n o2 q.1 then (1 : ℂ) else 0)) := by
      rw [Finset.sum_congr rfl (fun o1 _ => by rw [← Finset.mul_sum]), Finset.sum_mul]
    rw [h4]
  rw [h3, clause4Aux_qft_col_orth n p.1 q.1, Matrix.one_apply]
  by_cases hc : p.1 = q.1
  · rw [hc, if_pos rfl, one_mul, clause4Aux_quditAdd_cross_sum n p.2 q.2 q.1]
    by_cases ha : p.2 = q.2
    · rw [if_pos ha, if_pos (show p = q by exact Prod.ext hc ha)]
    · rw [if_neg ha, if_neg (fun h => ha (congrArg Prod.snd h))]
  · rw [if_neg hc, zero_mul, if_neg (fun h => hc (congrArg Prod.fst h))]
end Qatlib.Concepts.QuditTeleport.QdLoccModel
