/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

namespace Qatlib.Concepts.SpectralFilter.BusySpectrum
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

private theorem bipartite_inner_add_right {K : Type} [Fintype K] (u v w : QState K) :
    Qatlib.Foundations.PureStateMath.Inner u (v+w)=Qatlib.Foundations.PureStateMath.Inner u v+Qatlib.Foundations.PureStateMath.Inner u w := by simp [Qatlib.Foundations.PureStateMath.Inner,dotProduct_add]

private theorem bipartite_inner_rev {K : Type} [Fintype K] (u v : QState K) :
    Qatlib.Foundations.PureStateMath.Inner v u=(starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Inner u v) := by
  exact star_dotProduct (v:=v) (w:=u)

theorem bipartite_endpoint_projectors {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) (hA : IsIsometry A) (hB : IsIsometry B)
    (w : QState H) :
    (bipartiteWalk A B*ᵥw=w ↔ (A*Aᴴ)*ᵥw=(B*Bᴴ)*ᵥw) ∧
    (bipartiteWalk A B*ᵥw=-w ↔ (A*Aᴴ)*ᵥw+(B*Bᴴ)*ᵥw=w) := by
  let P := A*Aᴴ
  let Q := B*Bᴴ
  have hP : IsOrthogonalProjector P := rangeProjector_isOrthogonalProjector hA
  have hQ : IsOrthogonalProjector Q := rangeProjector_isOrthogonalProjector hB
  have hr : ReflectionAbout Q*ᵥ(bipartiteWalk A B*ᵥw)=ReflectionAbout P*ᵥw := by
    rw [Matrix.mulVec_mulVec,bipartiteWalk,← Matrix.mul_assoc,reflectionAbout_mul_self hQ,Matrix.one_mul]
  have hp : bipartiteWalk A B*ᵥw=ReflectionAbout Q*ᵥ(ReflectionAbout P*ᵥw) := by
    rw [bipartiteWalk,Matrix.mulVec_mulVec]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro he
    rw [he,reflectionAbout_mulVec,reflectionAbout_mulVec] at hr
    exact smul_right_injective (QState H) (by norm_num : (2:ℂ)≠0) (sub_left_inj.mp hr.symm)
  · intro he
    have hh : ReflectionAbout P*ᵥw=ReflectionAbout Q*ᵥw := by
      rw [reflectionAbout_mulVec,reflectionAbout_mulVec,he]
    rw [hp,hh,Matrix.mulVec_mulVec,reflectionAbout_mul_self hQ,Matrix.one_mulVec]
  · intro he
    rw [he,Matrix.mulVec_neg,reflectionAbout_mulVec,reflectionAbout_mulVec] at hr
    apply smul_right_injective (QState H) (by norm_num : (2:ℂ)≠0)
    calc
      (2:ℂ)•(P*ᵥw+Q*ᵥw) = ((2:ℂ)•(P*ᵥw)-w)+((2:ℂ)•(Q*ᵥw)-w)+(2:ℂ)•w := by module
      _ = (2:ℂ)•w := by rw [← hr]; module
  · intro he
    have hh : ReflectionAbout P*ᵥw=-(ReflectionAbout Q*ᵥw) := by
      rw [reflectionAbout_mulVec,reflectionAbout_mulVec]
      have hx : P*ᵥw=w-Q*ᵥw := eq_sub_of_add_eq he
      rw [hx]
      module
    rw [hp,hh,Matrix.mulVec_neg,Matrix.mulVec_mulVec,reflectionAbout_mul_self hQ,Matrix.one_mulVec]

theorem bipartite_busy_fixed_in_both_ranges {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) (hA : IsIsometry A) (hB : IsIsometry B)
    (w : QState H) (hw : bipartiteWalk A B*ᵥw=w)
    (hv : w∈LinearMap.range (bipartiteTilde A B).toLin') :
    (A*Aᴴ)*ᵥw=w ∧ (B*Bᴴ)*ᵥw=w := by
  have hpq := (bipartite_endpoint_projectors A B hA hB w).1.mp hw
  let d := w-(A*Aᴴ)*ᵥw
  have ha : Aᴴ*ᵥd=0 := by
    rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,
      show Aᴴ*(A*Aᴴ)=Aᴴ from by rw [← Matrix.mul_assoc,show Aᴴ*A=1 from hA,Matrix.one_mul],sub_self]
  have hb : Bᴴ*ᵥd=0 := by
    change Bᴴ*ᵥ(w-(A*Aᴴ)*ᵥw)=0
    rw [hpq,Matrix.mulVec_sub,Matrix.mulVec_mulVec,
      show Bᴴ*(B*Bᴴ)=Bᴴ from by rw [← Matrix.mul_assoc,show Bᴴ*B=1 from hB,Matrix.one_mul],sub_self]
  obtain ⟨v,hv⟩ := hv
  have hdA (a : QState I) : Qatlib.Foundations.PureStateMath.Inner d (A*ᵥa)=0 := by
    rw [bipartite_inner_rev,inner_mulVec_left_rect,ha]
    simp [Qatlib.Foundations.PureStateMath.Inner]
  have hdB (b : QState J) : Qatlib.Foundations.PureStateMath.Inner d (B*ᵥb)=0 := by
    rw [bipartite_inner_rev,inner_mulVec_left_rect,hb]
    simp [Qatlib.Foundations.PureStateMath.Inner]
  have hdw : Qatlib.Foundations.PureStateMath.Inner d w=0 := by
    rw [← hv]
    change Qatlib.Foundations.PureStateMath.Inner d (bipartiteTilde A B*ᵥv)=0
    rw [bipartiteTilde,Matrix.fromCols_mulVec,bipartite_inner_add_right,hdA,hdB,add_zero]
  have hdp : Qatlib.Foundations.PureStateMath.Inner d ((A*Aᴴ)*ᵥw)=0 := by
    rw [← Matrix.mulVec_mulVec]
    exact hdA _
  have hdd : Qatlib.Foundations.PureStateMath.Inner d d=0 := by
    change Qatlib.Foundations.PureStateMath.Inner d (w-(A*Aᴴ)*ᵥw)=0
    rw [Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_right,hdw,hdp,sub_self]
  have hd : d=0 := dotProduct_star_self_eq_zero.mp hdd
  have hp : (A*Aᴴ)*ᵥw=w := (sub_eq_zero.mp hd).symm
  exact ⟨hp,hpq.symm.trans hp⟩

private theorem bipartite_busy_plus_dimension {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) (hA : IsIsometry A) (hB : IsIsometry B) :
    Module.finrank ℂ ↥(LinearMap.ker ((bipartiteWalk A B-1).toLin') ⊓
      LinearMap.range (bipartiteTilde A B).toLin')=
      Fintype.card I+Fintype.card J-Matrix.rank (bipartiteTilde A B) := by
  classical
  let T := bipartiteTilde A B
  let F := LinearMap.ker T.toLin'
  let E := LinearMap.ker ((bipartiteWalk A B-1).toLin') ⊓ LinearMap.range T.toLin'
  have he (w : E) : bipartiteWalk A B*ᵥw.val=w.val := by
    have hh := w.property.1
    change (bipartiteWalk A B-1)*ᵥw.val=0 at hh
    exact sub_eq_zero.mp (by simpa [Matrix.sub_mulVec,Matrix.one_mulVec] using! hh)
  have hp (w : E) := bipartite_busy_fixed_in_both_ranges A B hA hB w.val (he w) w.property.2
  have hc (v : F) : A*ᵥ(fun i=>v.val (.inl i))+B*ᵥ(fun j=>v.val (.inr j))=0 := by
    have hh := v.property
    change T*ᵥv.val=0 at hh
    simpa [T,bipartiteTilde,Matrix.fromCols_mulVec] using! hh
  have hf (v : F) : A*ᵥ(fun i=>v.val (.inl i))∈E := by
    have hh : A*ᵥ(fun i=>v.val (.inl i))=B*ᵥ(-(fun j=>v.val (.inr j))) := by
      rw [Matrix.mulVec_neg]
      exact eq_neg_of_add_eq_zero_left (hc v)
    have hw := (two_isometry_intersection_gram_and_fixed I J H A B
      (fun i=>v.val (.inl i)) (-(fun j=>v.val (.inr j))) hA hB).2 hh
    refine ⟨?_,⟨Sum.elim (fun i=>v.val (.inl i)) 0,?_⟩⟩
    · change (bipartiteWalk A B-1)*ᵥ(A*ᵥ(fun i=>v.val (.inl i)))=0
      rw [Matrix.sub_mulVec,Matrix.one_mulVec,show bipartiteWalk A B*ᵥ(A*ᵥ(fun i=>v.val (.inl i)))=_ from hw,sub_self]
    · change T*ᵥ(Sum.elim (fun i=>v.val (.inl i)) 0)=_
      simp [T,bipartiteTilde]
  have hg (w : E) : Sum.elim (Aᴴ*ᵥw.val) (-(Bᴴ*ᵥw.val))∈F := by
    change T*ᵥ(Sum.elim (Aᴴ*ᵥw.val) (-(Bᴴ*ᵥw.val)))=0
    dsimp only [T]
    rw [bipartiteTilde,Matrix.fromCols_mulVec_sumElim,Matrix.mulVec_neg,
      Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,(hp w).1,(hp w).2,add_neg_cancel]
  let e : F ≃ₗ[ℂ] E := {
    toFun := fun v=>⟨A*ᵥ(fun i=>v.val (.inl i)),hf v⟩
    invFun := fun w=>⟨Sum.elim (Aᴴ*ᵥw.val) (-(Bᴴ*ᵥw.val)),hg w⟩
    left_inv := by
      intro v
      apply Subtype.ext
      have hb : Bᴴ*ᵥ(A*ᵥ(fun i=>v.val (.inl i)))=-(fun j=>v.val (.inr j)) := by
        have hh := congrArg (fun w : QState H=>Bᴴ*ᵥw) (hc v)
        (try dsimp only at hh)
        simp only [Matrix.mulVec_add,Matrix.mulVec_mulVec,show Bᴴ*B=1 from hB,Matrix.one_mulVec,Matrix.mulVec_zero] at hh
        simpa only [Matrix.mulVec_mulVec] using! eq_neg_of_add_eq_zero_left hh
      ext (i | j)
      · change (Aᴴ*ᵥ(A*ᵥ(fun i=>v.val (.inl i)))) i=v.val (.inl i)
        rw [Matrix.mulVec_mulVec,show Aᴴ*A=1 from hA,Matrix.one_mulVec]
      · change -(Bᴴ*ᵥ(A*ᵥ(fun i=>v.val (.inl i)))) j=v.val (.inr j)
        rw [hb]
        simp
    right_inv := by
      intro w
      apply Subtype.ext
      exact (Matrix.mulVec_mulVec _ _ _).trans (hp w).1
    map_add' := by intro v w; apply Subtype.ext; exact Matrix.mulVec_add _ _ _
    map_smul' := by intro c v; apply Subtype.ext; exact Matrix.mulVec_smul _ _ _ }
  have hdim := LinearMap.finrank_range_add_finrank_ker T.toLin'
  change T.rank+Module.finrank ℂ F=Module.finrank ℂ (QState (I⊕J)) at hdim
  simp only [Module.finrank_pi,Fintype.card_sum] at hdim
  have hF : Module.finrank ℂ F=Fintype.card I+Fintype.card J-T.rank := by omega
  exact e.finrank_eq.symm.trans hF

private theorem bipartite_busy_minus_dimension {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) (hA : IsIsometry A) (hB : IsIsometry B) :
    Module.finrank ℂ ↥(LinearMap.ker ((bipartiteWalk A B+1).toLin') ⊓
      LinearMap.range (bipartiteTilde A B).toLin')=
      Fintype.card I+Fintype.card J-2*Matrix.rank (Aᴴ*B) := by
  classical
  let Ka := LinearMap.ker (Bᴴ*A).toLin'
  let Kb := LinearMap.ker (Aᴴ*B).toLin'
  let E :=
      LinearMap.ker ((bipartiteWalk A B+1).toLin') ⊓ LinearMap.range (bipartiteTilde A B).toLin'
  have hs (w : E) : (A*Aᴴ)*ᵥw.val+(B*Bᴴ)*ᵥw.val=w.val := by
    apply (bipartite_endpoint_projectors A B hA hB w.val).2.mp
    have hh := w.property.1
    change (bipartiteWalk A B+1)*ᵥw.val=0 at hh
    exact eq_neg_of_add_eq_zero_left (by simpa [Matrix.add_mulVec,Matrix.one_mulVec] using! hh)
  have hga (w : E) : Aᴴ*ᵥw.val∈Ka := by
    have hh := congrArg (fun x : QState H => Bᴴ*ᵥx) (hs w)
    (try dsimp only at hh)
    rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
      show Bᴴ*(B*Bᴴ)=Bᴴ from by rw [← Matrix.mul_assoc,show Bᴴ*B=1 from hB,Matrix.one_mul]] at hh
    change (Bᴴ*A)*ᵥ(Aᴴ*ᵥw.val)=0
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc]
    exact add_eq_right.mp hh
  have hgb (w : E) : Bᴴ*ᵥw.val∈Kb := by
    have hh := congrArg (fun x : QState H => Aᴴ*ᵥx) (hs w)
    (try dsimp only at hh)
    rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
      show Aᴴ*(A*Aᴴ)=Aᴴ from by rw [← Matrix.mul_assoc,show Aᴴ*A=1 from hA,Matrix.one_mul]] at hh
    change (Aᴴ*B)*ᵥ(Bᴴ*ᵥw.val)=0
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc]
    exact add_eq_left.mp hh
  have hf (v : Ka×Kb) : A*ᵥv.1.val+B*ᵥv.2.val∈E := by
    let u : QState (I⊕J) := Sum.elim v.1.val v.2.val
    have hd : bipartiteDiscriminant A B*ᵥu=0 := by
      rw [bipartiteDiscriminant,Matrix.fromBlocks_mulVec]
      have ha : (Bᴴ*A)*ᵥv.1.val=0 := v.1.property
      have hb : (Aᴴ*B)*ᵥv.2.val=0 := v.2.property
      simp [u,ha,hb]
    have hw := (bipartite_endpoint_kernel_transport H I J A B u hA hB).2.2 hd
    have ht : bipartiteTilde A B*ᵥu=A*ᵥv.1.val+B*ᵥv.2.val := Matrix.fromCols_mulVec_sumElim _ _ _ _
    rw [ht] at hw
    refine ⟨?_,⟨u,ht⟩⟩
    change (bipartiteWalk A B+1)*ᵥ(A*ᵥv.1.val+B*ᵥv.2.val)=0
    rw [Matrix.add_mulVec,Matrix.one_mulVec,hw,neg_add_cancel]
  let e : (Ka×Kb) ≃ₗ[ℂ] E := {
    toFun := fun v=>⟨A*ᵥv.1.val+B*ᵥv.2.val,hf v⟩
    invFun := fun w=>(⟨Aᴴ*ᵥw.val,hga w⟩,⟨Bᴴ*ᵥw.val,hgb w⟩)
    left_inv := by
      intro v
      apply Prod.ext <;> apply Subtype.ext
      all_goals (try dsimp only)
      · rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,show Aᴴ*A=1 from hA,Matrix.one_mulVec,
          Matrix.mulVec_mulVec,show (Aᴴ*B)*ᵥv.2.val=0 from v.2.property,add_zero]
      · rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,show (Bᴴ*A)*ᵥv.1.val=0 from v.1.property,
          Matrix.mulVec_mulVec,show Bᴴ*B=1 from hB,Matrix.one_mulVec,zero_add]
    right_inv := by
      intro w
      apply Subtype.ext
      simpa only [Matrix.mulVec_mulVec] using! hs w
    map_add' := by
      intro v w
      apply Subtype.ext
      simp only [Matrix.mulVec_add,Prod.fst_add,Prod.snd_add,Submodule.coe_add]
      module
    map_smul' := by
      intro c v
      apply Subtype.ext
      change A*ᵥ(c•v.1.val)+B*ᵥ(c•v.2.val)=c•(A*ᵥv.1.val+B*ᵥv.2.val)
      rw [Matrix.mulVec_smul,Matrix.mulVec_smul,smul_add] }
  have ha := LinearMap.finrank_range_add_finrank_ker (Bᴴ*A).toLin'
  have hb := LinearMap.finrank_range_add_finrank_ker (Aᴴ*B).toLin'
  change (Bᴴ*A).rank+Module.finrank ℂ Ka=Module.finrank ℂ (QState I) at ha
  change (Aᴴ*B).rank+Module.finrank ℂ Kb=Module.finrank ℂ (QState J) at hb
  have hr : (Bᴴ*A).rank=(Aᴴ*B).rank := by
    have hh : (Aᴴ*B)ᴴ=Bᴴ*A := by
      simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    rw [← hh,Matrix.rank_conjTranspose]
  rw [hr] at ha
  simp only [Module.finrank_pi,] at ha hb
  rw [← e.finrank_eq,Module.finrank_prod]
  omega

theorem bipartite_busy_idle_multiplicity :
    ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    IsIsometry A → IsIsometry B →
    Module.finrank ℂ ↥(LinearMap.ker ((bipartiteWalk A B-1).toLin') ⊓
      LinearMap.range (bipartiteTilde A B).toLin')=
      Fintype.card I+Fintype.card J-Matrix.rank (bipartiteTilde A B) ∧
    Module.finrank ℂ ↥(LinearMap.ker ((bipartiteWalk A B+1).toLin') ⊓
      LinearMap.range (bipartiteTilde A B).toLin')=
      Fintype.card I+Fintype.card J-2*Matrix.rank (Aᴴ*B) ∧
    Module.finrank ℂ (LinearMap.ker ((bipartiteTilde A B)ᴴ.toLin'))+
      Matrix.rank (bipartiteTilde A B)=Fintype.card H := by
  intro H I J _ _ _ _ _ _ A B hA hB
  refine ⟨bipartite_busy_plus_dimension A B hA hB,bipartite_busy_minus_dimension A B hA hB,?_⟩
  have hh := LinearMap.finrank_range_add_finrank_ker (bipartiteTilde A B)ᴴ.toLin'
  change ((bipartiteTilde A B)ᴴ).rank+Module.finrank ℂ (LinearMap.ker ((bipartiteTilde A B)ᴴ.toLin'))=
    Module.finrank ℂ (QState H) at hh
  simpa [Matrix.rank_conjTranspose,Module.finrank_pi,Nat.add_comm] using! hh

noncomputable def bipartitePrepareReflectWord {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (F : Matrix H I ℂ) (G : Matrix H J ℂ) (U V : Matrix H H ℂ) : Circuit H :=
  [.gate Uᴴ,.gate (ReflectionAbout (F*Fᴴ)),.gate U,
    .gate Vᴴ,.gate (ReflectionAbout (G*Gᴴ)),.gate V]

private theorem bipartite_prepared_reflection {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (U : Matrix H H ℂ)
    (hU : U∈unitaryGroup H ℂ) :
    U*ReflectionAbout (F*Fᴴ)*Uᴴ=ReflectionAbout ((U*F)*(U*F)ᴴ) := by
  have hUU : U*Uᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.2
  simp only [ReflectionAbout,Matrix.conjTranspose_mul,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
    hUU,Matrix.mul_assoc]

theorem bipartite_actual_prepare_reflect_word :
    ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (F : Matrix H I ℂ) (G : Matrix H J ℂ)
      (U V : Matrix H H ℂ), IsIsometry F → IsIsometry G →
    U∈Matrix.unitaryGroup H ℂ → V∈Matrix.unitaryGroup H ℂ →
    let C : Circuit H := [.gate Uᴴ,.gate (ReflectionAbout (F*Fᴴ)),.gate U,
      .gate Vᴴ,.gate (ReflectionAbout (G*Gᴴ)),.gate V]
    IsUnitaryCircuit C ∧ QueryCount C=0 ∧ GateCount C=6 ∧
    ∀ ψ : QState H,Run 1 C ψ=bipartiteWalk (U*F) (V*G)*ᵥψ := by
  intro H I J _ _ _ _ _ _ F G U V hF hG hU hV
  have hUs : Uᴴ∈unitaryGroup H ℂ := by
    constructor
    · simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using! hU.2
    · simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using! hU.1
  have hVs : Vᴴ∈unitaryGroup H ℂ := by
    constructor
    · simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using! hV.2
    · simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using! hV.1
  refine ⟨?_,rfl,rfl,?_⟩
  · simp only [isUnitaryCircuit_gate,isUnitaryCircuit_nil,and_true]
    exact ⟨hUs,reflectionAbout_unitary (rangeProjector_isOrthogonalProjector hF),hU,
      hVs,reflectionAbout_unitary (rangeProjector_isOrthogonalProjector hG),hV⟩
  · intro ψ
    simp only [Run,ApplyGate,Matrix.mulVec_mulVec]
    have hr : V*ReflectionAbout (G*Gᴴ)*Vᴴ*U*ReflectionAbout (F*Fᴴ)*Uᴴ=
        bipartiteWalk (U*F) (V*G) := by
      rw [show V*ReflectionAbout (G*Gᴴ)*Vᴴ*U*ReflectionAbout (F*Fᴴ)*Uᴴ=
          (V*ReflectionAbout (G*Gᴴ)*Vᴴ)*(U*ReflectionAbout (F*Fᴴ)*Uᴴ) by simp only [Matrix.mul_assoc],
        bipartite_prepared_reflection G V hV,bipartite_prepared_reflection F U hU]
      rfl
    simp only [Matrix.mul_assoc] at hr
    rw [hr]

theorem bipartite_actual_repeated_prepare_reflect_word {H I J : Type}
    [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (F : Matrix H I ℂ) (G : Matrix H J ℂ) (U V : Matrix H H ℂ)
    (hF : IsIsometry F) (hG : IsIsometry G) (hU : U∈unitaryGroup H ℂ)
    (hV : V∈unitaryGroup H ℂ) (k : ℕ) :
    IsUnitaryCircuit (RepeatCircuit (bipartitePrepareReflectWord F G U V) k) ∧
    QueryCount (RepeatCircuit (bipartitePrepareReflectWord F G U V) k)=0 ∧
    GateCount (RepeatCircuit (bipartitePrepareReflectWord F G U V) k)=4*k+2*k ∧
    ∀ ψ,Run 1 (RepeatCircuit (bipartitePrepareReflectWord F G U V) k) ψ=
      (bipartiteWalk (U*F) (V*G))^k*ᵥψ := by
  have hc := bipartite_actual_prepare_reflect_word H I J F G U V hF hG hU hV
  change IsUnitaryCircuit (bipartitePrepareReflectWord F G U V) ∧
    QueryCount (bipartitePrepareReflectWord F G U V)=0 ∧
    GateCount (bipartitePrepareReflectWord F G U V)=6 ∧
    (∀ ψ,Run 1 (bipartitePrepareReflectWord F G U V) ψ=bipartiteWalk (U*F) (V*G)*ᵥψ) at hc
  refine ⟨hc.1.repeatCircuit k,?_,?_,?_⟩
  · rw [queryCount_repeatCircuit,hc.2.1,Nat.mul_zero]
  · rw [gateCount_repeatCircuit,hc.2.2.1]
    omega
  · intro ψ
    induction k generalizing ψ with
    | zero => simp [RepeatCircuit]
    | succ k ih =>
        rw [RepeatCircuit,run_append,hc.2.2.2,ih,Matrix.mulVec_mulVec,pow_succ]

inductive BipartiteAccessStep where
  | prepareLeft (inverse : Bool)
  | prepareRight (inverse : Bool)
  | reflectLeft
  | reflectRight
  deriving DecidableEq

def bipartiteAccessBlock : List BipartiteAccessStep :=
  [.prepareLeft true,.reflectLeft,.prepareLeft false,
    .prepareRight true,.reflectRight,.prepareRight false]

def bipartiteAccessProgram : ℕ→List BipartiteAccessStep
  | 0 => []
  | k+1 => bipartiteAccessBlock++bipartiteAccessProgram k

def BipartiteAccessStep.isPrepare : BipartiteAccessStep→Bool
  | .prepareLeft _ | .prepareRight _ => true
  | .reflectLeft | .reflectRight => false

noncomputable def compileBipartiteAccess {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (F : Matrix H I ℂ) (G : Matrix H J ℂ) (U V : Matrix H H ℂ)
    (program : List BipartiteAccessStep) : Circuit H := program.map fun s => .gate (match s with
      | .prepareLeft inverse => if inverse then Uᴴ else U
      | .prepareRight inverse => if inverse then Vᴴ else V
      | .reflectLeft => ReflectionAbout (F*Fᴴ)
      | .reflectRight => ReflectionAbout (G*Gᴴ))

theorem bipartite_actual_access_program {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (F : Matrix H I ℂ) (G : Matrix H J ℂ) (U V : Matrix H H ℂ) (k : ℕ) :
    compileBipartiteAccess F G U V (bipartiteAccessProgram k)=
      RepeatCircuit (bipartitePrepareReflectWord F G U V) k ∧
    (bipartiteAccessProgram k).countP BipartiteAccessStep.isPrepare=4*k ∧
    (bipartiteAccessProgram k).countP (fun s=>!s.isPrepare)=2*k := by
  induction k with
  | zero => simp [bipartiteAccessProgram,compileBipartiteAccess,RepeatCircuit]
  | succ k ih =>
      refine ⟨?_,?_,?_⟩
      · simp only [bipartiteAccessProgram,compileBipartiteAccess,List.map_append,RepeatCircuit]
        change bipartitePrepareReflectWord F G U V++compileBipartiteAccess F G U V
            (bipartiteAccessProgram k)=_
        rw [ih.1]
      · simp only [bipartiteAccessProgram,List.countP_append,ih.2.1]
        norm_num [bipartiteAccessBlock,BipartiteAccessStep.isPrepare,List.countP_cons]
        omega
      · simp only [bipartiteAccessProgram,List.countP_append,ih.2.2]
        norm_num [bipartiteAccessBlock,BipartiteAccessStep.isPrepare,List.countP_cons]
        omega

theorem bipartite_actual_spectral_access_program {H I J K : Type}
    [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (F : Matrix H I ℂ) (G : Matrix H J ℂ) (U V : Matrix H H ℂ)
    (X : Matrix H K ℂ) (z : K→ℂ)
    (hF : IsIsometry F) (hG : IsIsometry G) (hU : U∈unitaryGroup H ℂ)
    (hV : V∈unitaryGroup H ℂ)
    (hWX : bipartiteWalk (U*F) (V*G)*X=X*diagonal z) (k : ℕ) :
    IsUnitaryCircuit (compileBipartiteAccess F G U V (bipartiteAccessProgram k)) ∧
    QueryCount (compileBipartiteAccess F G U V (bipartiteAccessProgram k))=0 ∧
    GateCount (compileBipartiteAccess F G U V (bipartiteAccessProgram k))=4*k+2*k ∧
    (bipartiteAccessProgram k).countP BipartiteAccessStep.isPrepare=4*k ∧
    (bipartiteAccessProgram k).countP (fun s=>!s.isPrepare)=2*k ∧
    ∀ v : QState K,
      Run 1 (compileBipartiteAccess F G U V (bipartiteAccessProgram k)) (X*ᵥv)=
        X*ᵥ((diagonal z)^k*ᵥv) := by
  have ha := bipartite_actual_access_program F G U V k
  have hr := bipartite_actual_repeated_prepare_reflect_word F G U V hF hG hU hV k
  refine ⟨?_,?_,?_,ha.2.1,ha.2.2,?_⟩
  · rw [ha.1]
    exact hr.1
  · rw [ha.1]
    exact hr.2.1
  · rw [ha.1]
    exact hr.2.2.1
  · intro v
    rw [ha.1,hr.2.2.2]
    clear ha hr
    have hp : (bipartiteWalk (U*F) (V*G))^k*X=X*(diagonal z)^k := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ',Matrix.mul_assoc,ih,← Matrix.mul_assoc,hWX,Matrix.mul_assoc,← pow_succ']
    rw [Matrix.mulVec_mulVec,hp,← Matrix.mulVec_mulVec]

theorem bipartite_prepared_complete_spectrum_consumer {H I J : Type}
    [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (F : Matrix H I ℂ) (G : Matrix H J ℂ) (U V : Matrix H H ℂ)
    (hF : IsIsometry F) (hG : IsIsometry G) (hU : U∈unitaryGroup H ℂ)
    (hV : V∈unitaryGroup H ℂ) :
    ∃ (m : ℕ) (X : Matrix H (Fin m) ℂ) (z : Fin m→ℂ),
      IsIsometry X ∧ X*Xᴴ=bipartiteTilde (U*F) (V*G)*matrixPseudoinverse (bipartiteTilde (U*F) (V*G)) ∧
      m=(bipartiteTilde (U*F) (V*G)).rank ∧
      (∀ i,z i=1 ∨ z i=-1 ∨ ∃ lam : ℝ,0<lam ∧ lam<1 ∧
        (z i=bipartitePhase lam true ∨ z i=bipartitePhase lam false)) ∧
      ∀ (k : ℕ) (v : QState (Fin m)),
        Run 1 (compileBipartiteAccess F G U V (bipartiteAccessProgram k)) (X*ᵥv)=
          X*ᵥ((diagonal z)^k*ᵥv) ∧
        (bipartiteAccessProgram k).countP BipartiteAccessStep.isPrepare=4*k ∧
        (bipartiteAccessProgram k).countP (fun s=>!s.isPrepare)=2*k := by
  have hUF : IsIsometry (U*F) := by
    change (U*F)ᴴ*(U*F)=1
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc Uᴴ U,
      show Uᴴ*U=1 from by simpa only [Matrix.star_eq_conjTranspose] using! hU.1,Matrix.one_mul]
    exact hF
  have hVG : IsIsometry (V*G) := by
    change (V*G)ᴴ*(V*G)=1
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc Vᴴ V,
      show Vᴴ*V=1 from by simpa only [Matrix.star_eq_conjTranspose] using! hV.1,Matrix.one_mul]
    exact hG
  obtain ⟨m,X,z,hX,hXX,hWX,hm,hz⟩ :=
      bipartite_complete_busy_spectral_frame H I J (U*F) (V*G) hUF hVG
  refine ⟨m,X,z,hX,hXX,hm,hz,?_⟩
  intro k v
  obtain ⟨_,_,_,hprep,hreflect,hrun⟩ :=
    bipartite_actual_spectral_access_program F G U V X z hF hG hU hV hWX k
  exact ⟨hrun v,hprep,hreflect⟩

theorem bipartite_actual_tau_power_consumer {H I J : Type}
    [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) (a : QState I) (b : QState J) (lam : ℝ)
    (hA : IsIsometry A) (hB : IsIsometry B) (hl : 0<lam) (hu : lam<1)
    (hn : Normalized (Sum.elim a b)) (hab : (Aᴴ*B)*ᵥb=(lam:ℂ)•a)
    (hba : (Bᴴ*A)*ᵥa=(lam:ℂ)•b) (s : Bool) (k : ℕ) :
    Normalized (bipartiteTau A B a b lam s) ∧
    Run 1 (compileBipartiteAccess A B 1 1 (bipartiteAccessProgram k)) (bipartiteTau A B a b lam s)=
      (bipartitePhase lam s)^k•bipartiteTau A B a b lam s := by
  have ht := bipartite_normalized_tau_pair H I J A B a b lam hA hB hl hu hn hab hba s
  refine ⟨ht.1,?_⟩
  rw [(bipartite_actual_access_program A B 1 1 k).1,
    (bipartite_actual_repeated_prepare_reflect_word A B 1 1 hA hB
      (unitaryGroup H ℂ).one_mem (unitaryGroup H ℂ).one_mem k).2.2.2]
  simp only [Matrix.one_mul]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ',← Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul,ht.2.1,smul_smul,pow_succ]

theorem bipartite_actual_negative_label_and_idle_consumer {H I J : Type}
    [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) (hA : IsIsometry A) (hB : IsIsometry B)
    (v : QState (I⊕J)) (w : QState H)
    (hd : bipartiteDiscriminant A B*ᵥv=-v) (ha : Aᴴ*ᵥw=0) (hb : Bᴴ*ᵥw=0) (k : ℕ) :
    bipartiteTilde A B*ᵥv=0 ∧
    Run 1 (compileBipartiteAccess A B 1 1 (bipartiteAccessProgram k)) (bipartiteTilde A B*ᵥv)=0 ∧
    Run 1 (compileBipartiteAccess A B 1 1 (bipartiteAccessProgram k)) w=w := by
  have hz := (bipartite_endpoint_kernel_transport H I J A B v hA hB).2.1 hd
  have hw := (two_isometry_idle_sector_fixed I J H A B w hA hB ha hb).2.2
  have hrun (ψ : QState H) :
      Run 1 (compileBipartiteAccess A B 1 1 (bipartiteAccessProgram k)) ψ=(bipartiteWalk A B)^k*ᵥψ := by
    rw [(bipartite_actual_access_program A B 1 1 k).1,
      (bipartite_actual_repeated_prepare_reflect_word A B 1 1 hA hB
        (unitaryGroup H ℂ).one_mem (unitaryGroup H ℂ).one_mem k).2.2.2]
    simp only [Matrix.one_mul]
  refine ⟨hz,by rw [hrun,hz,Matrix.mulVec_zero],?_⟩
  rw [hrun]
  clear hrun
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ',← Matrix.mulVec_mulVec,ih]; exact hw

theorem bipartite_actual_zero_discriminant_consumer {H I J : Type}
    [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) (hA : IsIsometry A) (hB : IsIsometry B)
    (v : QState (I⊕J)) (hd : bipartiteDiscriminant A B*ᵥv=0) (k : ℕ) :
    Run 1 (compileBipartiteAccess A B 1 1 (bipartiteAccessProgram k)) (bipartiteTilde A B*ᵥv)=
      (-1:ℂ)^k•(bipartiteTilde A B*ᵥv) := by
  have hw := (bipartite_endpoint_kernel_transport H I J A B v hA hB).2.2 hd
  rw [(bipartite_actual_access_program A B 1 1 k).1,
    (bipartite_actual_repeated_prepare_reflect_word A B 1 1 hA hB
      (unitaryGroup H ℂ).one_mem (unitaryGroup H ℂ).one_mem k).2.2.2]
  simp only [Matrix.one_mul]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ',← Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul,hw,pow_succ]
      module

end Qatlib.Concepts.SpectralFilter.BusySpectrum
