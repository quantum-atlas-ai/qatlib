/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.WeakPromise
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Grid Matching

The four-residue bits keep the matching side distinct from the low coordinate parity.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching
open Qatlib.Concepts.SpinorSampling.Model

/-- The four-residue bits keep the matching side distinct from the low coordinate parity. -/
def residueBits : Fin 4 ≃ Bool × Bool :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr finTwoEquiv finTwoEquiv)

/-- A quotient-free known coordinate permutation separates block, parity and matching side. -/
def coordinate (K : ℕ) : Fin (K*4) ≃ (Fin K × Bool) × Bool :=
  (finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl (Fin K)) residueBits)).trans
    { toFun := fun a => ((a.1,a.2.2),a.2.1)
      invFun := fun a => (a.1.1,(a.2,a.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The concrete physical coordinate is exactly four times the block plus parity plus twice the matching side. -/
theorem coordinate_value (K : ℕ) (u : Fin K) (p t : Bool) :
    ((coordinate K).symm ((u,p),t)).val=4*u.val+p.toNat+2*t.toNat := by
  cases p <;> cases t <;> simp [coordinate,residueBits,finProdFinEquiv,finTwoEquiv] <;> omega

/-- The complete original grid is relabeled bijectively; no address register is observed or discarded. -/
def grid (d K : ℕ) : (Fin (d+1) → Fin (K*4)) ≃ ((Fin K × Bool) × (Fin d → Fin (K*4))) × Bool :=
  ((Fin.consEquiv (fun _ : Fin (d+1) => Fin (K*4))).symm.trans
    (Equiv.prodCongr (coordinate K) (Equiv.refl (Fin d → Fin (K*4))))).trans
      { toFun := fun a => ((a.1.1,a.2),a.1.2)
        invFun := fun a => ((a.1.1,a.2),a.1.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

/-- The selected original coordinate of the full inverse relabeling is the concrete block/parity/side code. -/
theorem grid_zero (d K : ℕ) (a : ((Fin K × Bool) × (Fin d → Fin (K*4))) × Bool) :
    (grid d K).symm a 0=(coordinate K).symm (a.1.1,a.2) := rfl

/-- Every remaining original grid coordinate is retained literally. -/
theorem grid_succ (d K : ℕ) (a : ((Fin K × Bool) × (Fin d → Fin (K*4))) × Bool) (j : Fin d) :
    (grid d K).symm a j.succ=a.1.2 j := rfl

/-- The actual finite-grid ring equivalence preserves the concrete natural coordinate. -/
theorem finite_coordinate_cast (N : ℕ) [NeZero N] (x : Fin N) :
    (ZMod.finEquiv N) x=(x.val : ZMod N) := by
  have hv : ((ZMod.finEquiv N) x).val=x.val := by
    cases N with
    | zero => exact False.elim (NeZero.ne 0 rfl)
    | succ n => rfl
  calc
    _ = (((ZMod.finEquiv N) x).val : ZMod N) := (ZMod.natCast_zmod_val _).symm
    _ = _ := congrArg (fun k : ℕ => (k : ZMod N)) hv

/-- Half of the first-axis original directed double-shift edges are precisely the two vertices in each matching pair. -/
theorem original_matched_edge (d K : ℕ) [NeZero (K*4)]
    (e : (Fin K × Bool) × (Fin d → Fin (K*4))) :
    periodicDoubleShift (d+1) (K*4) 0 ((grid d K).symm (e,false))=
      (grid d K).symm (e,true) := by
  funext k
  apply (ZMod.finEquiv (K*4)).injective
  rw [periodic_double_shift_coordinates]
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [grid_zero,ite_true]
    have h0 := coordinate_value K e.1.1 e.1.2 false
    have h1 := coordinate_value K e.1.1 e.1.2 true
    rw [finite_coordinate_cast,finite_coordinate_cast]
    change (((coordinate K).symm (e.1,false)).val : ZMod (K*4))+2=
      (((coordinate K).symm (e.1,true)).val : ZMod (K*4))
    rw [h0,h1]
    cases e.1.2 <;> norm_num
  · simp [grid_succ,Fin.succ_ne_zero]

/-- The actual pairing uses exactly half of all original grid sites. -/
theorem pair_cardinality (d K : ℕ) :
    2*Fintype.card ((Fin K × Bool) × (Fin d → Fin (K*4)))=(K*4)^(d+1) := by
  have h := Fintype.card_congr (grid d K)
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_prod,Fintype.card_bool] at h ⊢
  omega

/-- A genuine original double shift has no fixed site when the physical side length exceeds two. -/
theorem original_shift_no_fixed (d N : ℕ) [NeZero N] (hN : 2<N) (j : Fin d)
    (x : Fin d → Fin N) : periodicDoubleShift d N j x≠x := by
  intro he
  have h := congrArg (fun z => (ZMod.finEquiv N) (z j)) he
  rw [periodic_double_shift_coordinates] at h
  simp only [ite_true] at h
  have hz : (2 : ZMod N)=0 := by linear_combination h
  have hd := (ZMod.natCast_eq_zero_iff 2 N).mp hz
  have hl := Nat.le_of_dvd (by decide : 0<2) hd
  omega

/-- Two genuine original double shifts have no return cycle in the physical grid range. -/
theorem original_shift_no_two_cycle (d N : ℕ) [NeZero N] (hN : 4<N) (j : Fin d)
    (x : Fin d → Fin N) : periodicDoubleShift d N j (periodicDoubleShift d N j x)≠x := by
  intro he
  have h := congrArg (fun z => (ZMod.finEquiv N) (z j)) he
  rw [periodic_double_shift_coordinates,periodic_double_shift_coordinates] at h
  simp only [ite_true] at h
  have hz : (4 : ZMod N)=0 := by linear_combination h
  have hd := (ZMod.natCast_eq_zero_iff 4 N).mp hz
  have hl := Nat.le_of_dvd (by decide : 0<4) hd
  omega

/-- The original physical double-shift graph after the one known complete basis relabeling. -/
def doubleGraph (d K : ℕ) [NeZero (K*4)] (j : Fin (d+1)) :
    Equiv.Perm (((Fin K × Bool) × (Fin d → Fin (K*4))) × Bool) :=
  ((grid d K).symm.trans (periodicDoubleShift (d+1) (K*4) j)).trans (grid d K)

/-- The known full grid relabeling preserves the exact physical graph action. -/
theorem doubleGraph_inverse (d K : ℕ) [NeZero (K*4)] (j : Fin (d+1))
    (a : ((Fin K × Bool) × (Fin d → Fin (K*4))) × Bool) :
    (grid d K).symm (doubleGraph d K j a)=
      periodicDoubleShift (d+1) (K*4) j ((grid d K).symm a) := by
  simp only [doubleGraph,Equiv.trans_apply,Equiv.symm_apply_apply]

/-- The actual graph sends the first vertex of every pair to its second vertex on the selected axis. -/
theorem doubleGraph_matched (d K : ℕ) [NeZero (K*4)]
    (e : (Fin K × Bool) × (Fin d → Fin (K*4))) :
    doubleGraph d K 0 (e,false)=(e,true) := by
  apply (grid d K).symm.injective
  rw [doubleGraph_inverse,original_matched_edge]

/-- The actual completely relabeled physical graph has no fixed vertex. -/
theorem doubleGraph_no_fixed (d K : ℕ) [NeZero (K*4)] (hK : 1<K) (j : Fin (d+1))
    (a : ((Fin K × Bool) × (Fin d → Fin (K*4))) × Bool) : doubleGraph d K j a≠a := by
  intro he
  have h := congrArg (grid d K).symm he
  rw [doubleGraph_inverse] at h
  exact original_shift_no_fixed (d+1) (K*4) (by omega) j _ h

/-- The actual completely relabeled physical graph has no two-cycle. -/
theorem doubleGraph_no_two_cycle (d K : ℕ) [NeZero (K*4)] (hK : 1<K) (j : Fin (d+1))
    (a : ((Fin K × Bool) × (Fin d → Fin (K*4))) × Bool) :
    doubleGraph d K j (doubleGraph d K j a)≠a := by
  intro he
  have h := congrArg (grid d K).symm he
  rw [doubleGraph_inverse,doubleGraph_inverse] at h
  exact original_shift_no_two_cycle (d+1) (K*4) (by omega) j _ h

/-- The other half of selected-axis directed edges connects distinct actual pair variables. -/
theorem doubleGraph_unmatched (d K : ℕ) [NeZero (K*4)] (hK : 1<K)
    (e : (Fin K × Bool) × (Fin d → Fin (K*4))) : (doubleGraph d K 0 (e,true)).1≠e := by
  intro he
  have hz : doubleGraph d K 0 (e,true)=(e,(doubleGraph d K 0 (e,true)).2) := Prod.ext he rfl
  cases hs : (doubleGraph d K 0 (e,true)).2 with
  | false =>
    rw [hs] at hz
    have hc : doubleGraph d K 0 (doubleGraph d K 0 (e,false))=(e,false) := by
      rw [doubleGraph_matched,hz]
    exact doubleGraph_no_two_cycle d K hK 0 (e,false) hc
  | true =>
    rw [hs] at hz
    exact doubleGraph_no_fixed d K hK 0 (e,true) hz

/-- Directions other than the selected matching axis change a distinct actual pair variable. -/
theorem doubleGraph_transverse (d K : ℕ) [NeZero (K*4)] (hK : 1<K) (j : Fin d)
    (a : ((Fin K × Bool) × (Fin d → Fin (K*4))) × Bool) :
    (doubleGraph d K j.succ a).1≠a.1 := by
  intro he
  have hzero : (grid d K).symm (doubleGraph d K j.succ a) 0=(grid d K).symm a 0 := by
    rw [doubleGraph_inverse]
    apply (ZMod.finEquiv (K*4)).injective
    rw [periodic_double_shift_coordinates]
    have hj : (0 : Fin (d+1))≠j.succ := Ne.symm (Fin.succ_ne_zero j)
    simp only [ite_eq_right hj,add_zero]
  rw [grid_zero,grid_zero,he] at hzero
  have hs := congrArg Prod.snd ((coordinate K).symm.injective hzero)
  have hz : doubleGraph d K j.succ a=a := Prod.ext he hs
  exact doubleGraph_no_fixed d K hK j.succ a hz

/-- Exactly the false-side first-axis edges share a pair variable; every other original directed edge uses independent pair variables. -/
theorem doubleGraph_same_pair_iff (d K : ℕ) [NeZero (K*4)] (hK : 1<K) (j : Fin (d+1))
    (a : ((Fin K × Bool) × (Fin d → Fin (K*4))) × Bool) :
    (doubleGraph d K j a).1=a.1 ↔ j=0 ∧ a.2=false := by
  refine Fin.cases ?_ (fun k => ?_) j
  · rcases a with ⟨e,t⟩
    cases t
    · simp only [doubleGraph_matched,and_self,eq_self]
    · simp only [doubleGraph_unmatched d K hK e,Bool.true_eq_false,and_false]
  · have hj : k.succ≠(0 : Fin (d+1)) := Fin.succ_ne_zero k
    simp only [doubleGraph_transverse d K hK k a,hj,false_and,iff_self]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- Every original side length divisible by four has the actual complete coordinate bijection used by the matching construction. -/
def originalGrid (d N : ℕ) (h4 : 4∣N) :
    (Fin (d+1) → Fin N) ≃ (((Fin (N/4) × Bool) × (Fin d → Fin ((N/4)*4))) × Bool) :=
  (Equiv.piCongrRight (fun _ : Fin (d+1) => finCongr (Nat.div_mul_cancel h4).symm)).trans (grid d (N/4))

/-- The actual matching has more than one block throughout the original physical parameter range. -/
theorem original_block_range (N : ℕ) (hN : 256≤N) (h4 : 4∣N) : 64≤N/4 := by
  have h := Nat.div_mul_cancel h4
  omega

/-- The actual full basis has precisely the original number of sites; no ancillary promise changes its dimension. -/
theorem original_grid_cardinality (d N : ℕ) (h4 : 4∣N) :
    Fintype.card ((((Fin (N/4) × Bool) × (Fin d → Fin ((N/4)*4))) × Bool))=N^(d+1) := by
  have h := Fintype.card_congr (originalGrid d N h4)
  simpa only [Fintype.card_fun,Fintype.card_fin] using h.symm

/-- Equality of original grid sizes transports the actual physical double shift through the complete known coordinate bijection. -/
theorem periodic_size_transport (d N M : ℕ) [NeZero N] [NeZero M] (h : N=M) (j : Fin d)
    (x : Fin d → Fin N) :
    (Equiv.piCongrRight (fun _ : Fin d => finCongr h)) (periodicDoubleShift d N j x)=
      periodicDoubleShift d M j ((Equiv.piCongrRight (fun _ : Fin d => finCongr h)) x) := by
  subst M
  rfl

/-- Every complete original supplied-copy amplitude is preserved by the same known address bijection, including its original one-over-square-root normalization. -/
theorem original_copies_address_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B)
    (ψ : B → Bool → ℂ) (Q : ℕ) (ω : B → Fin (Q+1)) (x : Fin Q → A × Bool) :
    originalSuppliedCopies (fun a => ψ (e a)) Q (fun a => ω (e a)) x=
      originalSuppliedCopies ψ Q ω (fun j => (e (x j).1,(x j).2)) := by
  simp only [originalSuppliedCopies,sharedPhaseField,suppliedSpinState,complexSpinor_parts,Fintype.card_congr e]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching


namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts

/-- On actual first-axis matching edges the literal original Bell-prior mean pays one correlation rho. -/
theorem matched_edge_mean (d K : ℕ) [NeZero (K*4)]
    (b ρ : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (hlo : -1≤ρ) (hhi : ρ≤1)
    (e : (Fin K × Bool) × (Fin d → Fin (K*4))) :
    (∑ κ,pairedSignLaw ρ κ*edgeBell b κ (e,false) (doubleGraph d K 0 (e,false)))=
      b*(1-b)*(1-ρ) := by
  rw [doubleGraph_matched,actual_edge_mean b ρ hb0 hb1 hlo hhi]
  simp only [ite_true,Bool.false_eq_true,ite_false]

/-- The other actual first-axis edges use independent original pair variables and have no correlation deficit. -/
theorem unmatched_edge_mean (d K : ℕ) [NeZero (K*4)] (hK : 1<K)
    (b ρ : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (hlo : -1≤ρ) (hhi : ρ≤1)
    (e : (Fin K × Bool) × (Fin d → Fin (K*4))) :
    (∑ κ,pairedSignLaw ρ κ*edgeBell b κ (e,true) (doubleGraph d K 0 (e,true)))=b*(1-b) := by
  rw [actual_edge_mean b ρ hb0 hb1 hlo hhi,ite_eq_right (Ne.symm (doubleGraph_unmatched d K hK e))]
  simp only [sub_zero,mul_one]

/-- Every transverse original edge uses independent pair variables in the same actual prior. -/
theorem transverse_edge_mean (d K : ℕ) [NeZero (K*4)] (hK : 1<K)
    (b ρ : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (hlo : -1≤ρ) (hhi : ρ≤1) (j : Fin d)
    (a : ((Fin K × Bool) × (Fin d → Fin (K*4))) × Bool) :
    (∑ κ,pairedSignLaw ρ κ*edgeBell b κ a (doubleGraph d K j.succ a))=b*(1-b) := by
  rw [actual_edge_mean b ρ hb0 hb1 hlo hhi,ite_eq_right (Ne.symm (doubleGraph_transverse d K hK j a))]
  simp only [sub_zero,mul_one]

/-- The actual weighted physical graph mean expands to the original literal edge means. -/
theorem spin_prior_mean_expand {E : Type} [Fintype E] [DecidableEq E]
    {d : ℕ} (b G ρ : ℝ) (τ : Fin d → Equiv.Perm (E × Bool)) :
    (∑ κ : E → Fin 4,pairedSignLaw ρ κ*spinEnergy b G τ κ)=
      (G/(Fintype.card (E × Bool) : ℝ))*(∑ j : Fin d,∑ a : E × Bool,
        ∑ κ : E → Fin 4,pairedSignLaw ρ κ*edgeBell b κ a (τ j a)) := by
  have ht (κ : E → Fin 4) : pairedSignLaw ρ κ*spinEnergy b G τ κ=
      (G/(Fintype.card (E × Bool) : ℝ))*(∑ j : Fin d,∑ a : E × Bool,
        pairedSignLaw ρ κ*edgeBell b κ a (τ j a)) := by
    simp only [spinEnergy,Finset.mul_sum]
    ring
  simp_rw [ht]
  rw [←Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

/-- The original complete periodic-grid spin prior has the source's exact mean, with only half the first-axis edges correlated. -/
theorem original_spin_prior_mean (d K : ℕ) [NeZero (K*4)] (hK : 1<K)
    (b G ρ : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (hlo : -1≤ρ) (hhi : ρ≤1) :
    (∑ κ : ((Fin K × Bool) × (Fin d → Fin (K*4))) → Fin 4,
      pairedSignLaw ρ κ*spinEnergy b G (doubleGraph d K) κ)=
        G*b*(1-b)*((d+1 : ℕ)-ρ/2) := by
  let E := (Fin K × Bool) × (Fin d → Fin (K*4))
  have hcard : (Fintype.card E : ℝ)≠0 := by
    let : NeZero K := ⟨by omega⟩
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card E≠0)
  rw [spin_prior_mean_expand,Fin.sum_univ_succ]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,matched_edge_mean d K b ρ hb0 hb1 hlo hhi,
    unmatched_edge_mean d K hK b ρ hb0 hb1 hlo hhi,
    transverse_edge_mean d K hK b ρ hb0 hb1 hlo hhi,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fin]
  rw [show (Fintype.card (E × Bool) : ℝ)=(Fintype.card E : ℝ)*2 by
    simp only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]]
  change G/((Fintype.card E : ℝ)*2)*
    ((Fintype.card E : ℝ)*(b*(1-b)+b*(1-b)*(1-ρ))+
      (d : ℝ)*((Fintype.card E : ℝ)*2*(b*(1-b))))=G*b*(1-b)*((d+1 : ℕ)-ρ/2)
  push_cast
  field_simp [hcard]
  ring

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching
