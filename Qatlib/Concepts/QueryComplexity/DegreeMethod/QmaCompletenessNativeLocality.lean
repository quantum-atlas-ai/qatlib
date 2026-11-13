/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeOutput

/-!
# Locality of native propagation coefficients

This module proves that gate and clock propagation coefficients are determined by their
designated sites and vanish when the outside registers differ. The predicates `AgreeOutside` and
`controlled` express the entrywise locality condition and its relation to `partitionLift`.

Masking and filling preserve the relevant clock guards and gate coefficients, yielding the local
propagation representation used in the circuit-to-Hamiltonian framework of
[KitaevShenVyalyi2002].

## Main statements

* `controlled_eq_partitionLift`: A controlled local entry rule is the lift of its local table.
* `rawCoeff_strong`: Gate coefficients satisfy the local entry formula on `gateSites`.
* `propagationCoeff_strong`: Propagation coefficients satisfy the local entry formula on
  `propSites`.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib
open Qatlib.Concepts.TensorRegisters.RegisterModel
open scoped Classical
set_option autoImplicit false

/-- Requires two Boolean registers to agree at every site outside `A`. -/
def AgreeOutside {N : ℕ} (A : Finset (Fin N)) (x y : Reg N) : Prop :=
  ∀j : Fin N,j∉A → x j=y j

/-- Uses the entry rule `f` when the registers agree outside `A`, and the default value `z`
otherwise. -/
noncomputable def controlled {N : ℕ} {T : Type} (z : T) (A : Finset (Fin N))
    (f : Reg N→Reg N→T) (x y : Reg N) : T :=
  if AgreeOutside A x y then f x y else z

/-- For registers agreeing outside `S`, agreement outside `A` is equivalent before and after
masking and filling `S`. -/
theorem active_fill_iff {N : ℕ} (A S : Finset (Fin N)) (x y : Reg N)
    (hout : outside S x=outside S y) :
    AgreeOutside A x y ↔
      AgreeOutside A (fill S (mask S x)) (fill S (mask S y)) := by
  constructor
  · intro h j hjA
    by_cases hjS : j∈S
    · rw [fill_mask_on S x j hjS,fill_mask_on S y j hjS]
      exact h j hjA
    · rw [fill_off S _ j hjS,fill_off S _ j hjS]
  · intro h j hjA
    by_cases hjS : j∈S
    · have he := h j hjA
      rw [fill_mask_on S x j hjS,fill_mask_on S y j hjS] at he
      exact he
    · exact (outside_eq_iff S x y).mp hout j hjS

/-- A controlled entry rule invariant under masking to a support containing `A` is recovered
from its local entries when outside registers agree, and equals the default value otherwise. -/
theorem controlled_entries {N : ℕ} {T : Type} (z : T)
    (A S : Finset (Fin N)) (hAS : A⊆S)
    (f : Reg N→Reg N→T)
    (hf : ∀x y,f x y=f (fill S (mask S x)) (fill S (mask S y)))
    (x y : Reg N) :
    controlled z A f x y =
      if outside S x=outside S y then
        controlled z A f (fill S (mask S x)) (fill S (mask S y)) else z := by
  by_cases hout : outside S x=outside S y
  · rw [if_pos hout]
    have ha := active_fill_iff A S x y hout
    unfold controlled
    by_cases h : AgreeOutside A x y
    · rw [if_pos h,if_pos (ha.mp h)]
      exact hf x y
    · rw [if_neg h,if_neg (fun h' => h (ha.mpr h'))]
  · have ha : ¬AgreeOutside A x y := by
      intro h
      apply hout
      apply (outside_eq_iff S x y).mpr
      intro j hjS
      exact h j (fun hjA => hjS (hAS hjA))
    rw [if_neg hout]
    simpa only [controlled] using
      (if_neg ha : (if AgreeOutside A x y then f x y else z)=z)

/-- A complex controlled entry rule invariant under masking to a support containing `A` equals
the partition lift of its local table. -/
theorem controlled_eq_partitionLift {N : ℕ}
    (A S : Finset (Fin N)) (hAS : A⊆S)
    (f : Reg N→Reg N→ℂ)
    (hf : ∀x y,f x y=f (fill S (mask S x)) (fill S (mask S y))) :
    (fun x y => controlled (0:ℂ) A f x y) =
      partitionLift (split S)
        (fun u v => controlled (0:ℂ) A f (fill S u) (fill S v)) := by
  apply eq_partitionLift_of_entries
  intro x y
  exact controlled_entries 0 A S hAS f hf x y

/-- A flattened clock site belongs to the propagation support exactly when its clock index
belongs to `clockSites`. -/
theorem castAdd_mem_propSites {m : ℕ} (n : ℕ) (i c : Fin m) (g : FiniteGateCode) :
    c.castAdd n∈propSites n i g ↔ c∈clockSites i := by
  simp only [propSites,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro (⟨j,hj,hji⟩|⟨j,_,hji⟩)
    · have he : j=c := Fin.ext (congrArg (fun k : Fin (m+n) => k.val) hji)
      simpa only [he] using hj
    · have he:=congrArg Fin.val hji
      change m+j.val=c.val at he
      have hc:=c.isLt
      omega
  · intro hc
    exact Or.inl ⟨c,hc,rfl⟩

/-- A flattened work site belongs to the propagation support exactly when its work index belongs
to `gateSites`. -/
theorem natAdd_mem_propSites {m : ℕ} (n : ℕ) (i : Fin m) (w : Fin n)
    (g : FiniteGateCode) :
    w.natAdd m∈propSites n i g ↔ w∈gateSites n g := by
  simp only [propSites,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro (⟨j,_,hji⟩|⟨j,hj,hji⟩)
    · have he:=congrArg Fin.val hji
      change j.val=m+w.val at he
      have hj:=j.isLt
      omega
    · have he : j=w := Fin.ext (by
        have hh:=congrArg Fin.val hji
        change m+j.val=m+w.val at hh
        omega)
      simpa only [he] using hj
  · intro hw
    exact Or.inr ⟨w,hw,rfl⟩

/-- Agreement outside the flattened propagation support is equivalent to agreement outside the
clock support and outside the gate support in the two components. -/
theorem prop_outside_iff {m : ℕ} (n : ℕ) (i : Fin m) (g : FiniteGateCode)
    (x y : Reg (m+n)) :
    outside (propSites n i g) x=outside (propSites n i g) y ↔
      outside (clockSites i) (flattenEquiv m n x).1=
        outside (clockSites i) (flattenEquiv m n y).1 ∧
      outside (gateSites n g) (flattenEquiv m n x).2=
        outside (gateSites n g) (flattenEquiv m n y).2 := by
  simp only [outside_eq_iff]
  constructor
  · intro h
    constructor
    · intro c hc
      exact h (c.castAdd n) (by simpa only [castAdd_mem_propSites] using hc)
    · intro w hw
      exact h (w.natAdd m) (by simpa only [natAdd_mem_propSites] using hw)
  · rintro ⟨hc,hw⟩ j
    refine Fin.addCases ?_ ?_ j
    · intro c hcs
      exact hc c (by simpa only [castAdd_mem_propSites] using hcs)
    · intro w hws
      exact hw w (by simpa only [natAdd_mem_propSites] using hws)

/-- Masking and filling the flattened propagation support has the same clock component as
masking and filling `clockSites`. -/
theorem prop_fill_clock {m : ℕ} (n : ℕ) (i : Fin m) (g : FiniteGateCode)
    (x : Reg (m+n)) :
    (flattenEquiv m n (fill (propSites n i g) (mask (propSites n i g) x))).1=
      fill (clockSites i) (mask (clockSites i) (flattenEquiv m n x).1) := by
  funext c
  change fill (propSites n i g) (mask (propSites n i g) x) (c.castAdd n)=_
  by_cases hc : c∈clockSites i
  · rw [fill_mask_on _ _ _ ((castAdd_mem_propSites n i c g).mpr hc),
      fill_mask_on _ _ _ hc]
    rfl
  · rw [fill_off _ _ _ (by simpa only [castAdd_mem_propSites] using hc),fill_off _ _ _ hc]

/-- Masking and filling the flattened propagation support has the same work component as masking
and filling `gateSites`. -/
theorem prop_fill_work {m : ℕ} (n : ℕ) (i : Fin m) (g : FiniteGateCode)
    (x : Reg (m+n)) :
    (flattenEquiv m n (fill (propSites n i g) (mask (propSites n i g) x))).2=
      fill (gateSites n g) (mask (gateSites n g) (flattenEquiv m n x).2) := by
  funext w
  change fill (propSites n i g) (mask (propSites n i g) x) (w.natAdd m)=_
  by_cases hw : w∈gateSites n g
  · rw [fill_mask_on _ _ _ ((natAdd_mem_propSites n i w g).mpr hw),
      fill_mask_on _ _ _ hw]
    rfl
  · rw [fill_off _ _ _ (by simpa only [natAdd_mem_propSites] using hw),fill_off _ _ _ hw]

/-- For registers agreeing outside `S`, equality is equivalent to equality after masking and
filling `S`. -/
theorem eq_fill_iff {N : ℕ} (S : Finset (Fin N)) (x y : Reg N)
    (hout : outside S x=outside S y) :
    x=y ↔ fill S (mask S x)=fill S (mask S y) := by
  constructor
  · rintro rfl
    rfl
  · intro h
    have hm:=congrArg (mask S) h
    simp only [mask_fill] at hm
    apply (split S).injective
    rw [split_apply,split_apply,hm,hout]

open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

/-- Boolean values are equal when their equalities to true are equivalent. -/
private theorem bool_eq_of_true_iff (a b : Bool) (h : a=true ↔ b=true) : a=b := by
  cases a <;> cases b <;> simp_all

/-- A Boolean value that is not true is false. -/
private theorem bool_false_of_not_true (a : Bool) (h : ¬a=true) : a=false := by
  cases a <;> simp_all

/-- Agreement outside the empty support is equivalent to equality of the registers. -/
theorem outside_empty_iff {n : ℕ} (x y : Reg n) :
    Qatlib.Concepts.TensorRegisters.RegisterModel.outside (∅ : Finset (Fin n)) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside ∅ y ↔ x=y := by
  rw [Qatlib.Concepts.TensorRegisters.RegisterModel.outside_eq_iff]
  constructor
  · intro h
    funext j
    exact h j (by simp)
  · intro h j _
    exact congrFun h j

/-- Identity entry tags satisfy the local entry formula on the empty support, vanishing when
outside registers differ. -/
theorem identityTag_strong {n : ℕ} (x y : Reg n) :
    identityTag x y =
      if Qatlib.Concepts.TensorRegisters.RegisterModel.outside (∅ : Finset (Fin n)) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside ∅ y then
        identityTag (Qatlib.Concepts.TensorRegisters.RegisterModel.fill ∅ (Qatlib.Concepts.TensorRegisters.RegisterModel.mask ∅ x)) (Qatlib.Concepts.TensorRegisters.RegisterModel.fill ∅ (Qatlib.Concepts.TensorRegisters.RegisterModel.mask ∅ y))
      else zeroTag := by
  have hf : Qatlib.Concepts.TensorRegisters.RegisterModel.fill (∅ : Finset (Fin n)) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask ∅ x)=
      Qatlib.Concepts.TensorRegisters.RegisterModel.fill ∅ (Qatlib.Concepts.TensorRegisters.RegisterModel.mask ∅ y) := by
    funext j
    rw [Qatlib.Concepts.TensorRegisters.RegisterModel.fill_off ∅ _ j (by simp),Qatlib.Concepts.TensorRegisters.RegisterModel.fill_off ∅ _ j (by simp)]
  have hrf : regEq (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (∅ : Finset (Fin n)) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask ∅ x))
      (Qatlib.Concepts.TensorRegisters.RegisterModel.fill ∅ (Qatlib.Concepts.TensorRegisters.RegisterModel.mask ∅ y))=true := (regEq_true_iff _ _).mpr hf
  by_cases ho : Qatlib.Concepts.TensorRegisters.RegisterModel.outside (∅ : Finset (Fin n)) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside ∅ y
  · have hr : regEq x y=true := (regEq_true_iff _ _).mpr ((outside_empty_iff x y).mp ho)
    simp [identityTag,ho,hr,hrf]
  · have hr : regEq x y=false := bool_false_of_not_true _ (by
      intro h
      exact ho ((outside_empty_iff x y).mpr ((regEq_true_iff _ _).mp h)))
    simp [identityTag,ho,hr]

/-- A valid one-wire entry tag is determined by the masked wire when outside registers agree,
and is zero otherwise. -/
theorem oneWireTag_strong {n : ℕ} (w : Fin n) (cell : Bool→Bool→Tag)
    (x y : Reg n) :
    oneWireTag n w.val cell x y =
      if Qatlib.Concepts.TensorRegisters.RegisterModel.outside ({w} : Finset (Fin n)) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside {w} y then
        oneWireTag n w.val cell (Qatlib.Concepts.TensorRegisters.RegisterModel.fill {w} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {w} x))
          (Qatlib.Concepts.TensorRegisters.RegisterModel.fill {w} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {w} y)) else zeroTag := by
  have ho : outsideEq w x y=true ↔
      Qatlib.Concepts.TensorRegisters.RegisterModel.outside ({w} : Finset (Fin n)) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside {w} y := by
    rw [outsideEq_true_iff,Qatlib.Concepts.TensorRegisters.RegisterModel.outside_eq_iff]
    simp only [Finset.mem_singleton]
  have hf : outsideEq w (Qatlib.Concepts.TensorRegisters.RegisterModel.fill {w} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {w} x))
      (Qatlib.Concepts.TensorRegisters.RegisterModel.fill {w} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {w} y))=true := by
    apply (outsideEq_true_iff _ _ _).mpr
    intro j hj
    rw [Qatlib.Concepts.TensorRegisters.RegisterModel.fill_off {w} _ j (by simpa using hj),
      Qatlib.Concepts.TensorRegisters.RegisterModel.fill_off {w} _ j (by simpa using hj)]
  have hx :=
      Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on ({w} : Finset (Fin n)) x w
      (by simp)
  have hy :=
      Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on ({w} : Finset (Fin n)) y w
      (by simp)
  by_cases h : Qatlib.Concepts.TensorRegisters.RegisterModel.outside ({w} : Finset (Fin n)) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside {w} y
  · have hr : outsideEq w x y=true := ho.mpr h
    simp [oneWireTag,w.isLt,h,hr,hf,hx,hy]
  · have hr : outsideEq w x y=false :=
      bool_false_of_not_true _ (fun ht => h (ho.mp ht))
    simp [oneWireTag,w.isLt,h,hr]

/-- For distinct control and target wires, equality to the controlled-NOT update is equivalent
to agreement elsewhere together with the control and target bit equations. -/
theorem cnot_update_eq_iff {n : ℕ} (c t : Fin n) (hct : c≠t)
    (x y : Reg n) :
    x=Function.update y t (y t ^^ y c) ↔
      (∀j : Fin n,j≠c → j≠t → x j=y j) ∧
        x c=y c ∧ x t=(y t ^^ y c) := by
  constructor
  · intro h
    subst x
    refine ⟨?_,?_,?_⟩
    · intro j _ hjt
      simp [Function.update,hjt]
    · simp [Function.update,hct]
    · simp
  · rintro ⟨hout,hc,ht⟩
    funext j
    by_cases hjt : j=t
    · subst j
      simpa using ht
    · by_cases hjc : j=c
      · subst j
        simpa [Function.update,hct] using hc
      · simpa [Function.update,hjt] using hout j hjc hjt

/-- The controlled-NOT register test is equivalent to agreement outside its two wires and the
corresponding control and target bit equations. -/
theorem cnot_regEq_iff {n : ℕ} (c t : Fin n) (hct : c≠t)
    (x y : Reg n) :
    regEq x (Function.update y t (y t ^^ y c))=true ↔
      Qatlib.Concepts.TensorRegisters.RegisterModel.outside ({c,t} : Finset (Fin n)) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside {c,t} y ∧
        x c=y c ∧ x t=(y t ^^ y c) := by
  have ho : Qatlib.Concepts.TensorRegisters.RegisterModel.outside ({c,t} : Finset (Fin n)) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside {c,t} y ↔
      ∀j : Fin n,j≠c → j≠t → x j=y j := by
    rw [Qatlib.Concepts.TensorRegisters.RegisterModel.outside_eq_iff]
    constructor
    · intro h j hjc hjt
      exact h j (by simp [hjc,hjt])
    · intro h j hj
      have hh : j≠c ∧ j≠t := by simpa using hj
      exact h j hh.1 hh.2
  rw [regEq_true_iff,cnot_update_eq_iff c t hct,← ho]

/-- For distinct control and target wires, the controlled-NOT entry tag satisfies the local
entry formula on those two wires. -/
theorem cnotTag_strong {n : ℕ} (c t : Fin n) (hct : c≠t) (x y : Reg n) :
    (if regEq x (Function.update y t (y t ^^ y c)) then oneTag else zeroTag) =
      if Qatlib.Concepts.TensorRegisters.RegisterModel.outside ({c,t} : Finset (Fin n)) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside {c,t} y then
        (if regEq (Qatlib.Concepts.TensorRegisters.RegisterModel.fill {c,t} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {c,t} x))
          (Function.update (Qatlib.Concepts.TensorRegisters.RegisterModel.fill {c,t} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {c,t} y)) t
            (Qatlib.Concepts.TensorRegisters.RegisterModel.fill {c,t} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {c,t} y) t ^^
              Qatlib.Concepts.TensorRegisters.RegisterModel.fill {c,t} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {c,t} y) c)) then oneTag else zeroTag)
      else zeroTag := by
  have hf : Qatlib.Concepts.TensorRegisters.RegisterModel.outside ({c,t} : Finset (Fin n)) (Qatlib.Concepts.TensorRegisters.RegisterModel.fill {c,t} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {c,t} x))=
      Qatlib.Concepts.TensorRegisters.RegisterModel.outside {c,t} (Qatlib.Concepts.TensorRegisters.RegisterModel.fill {c,t} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {c,t} y)) := by
    rw [Qatlib.Concepts.TensorRegisters.RegisterModel.outside_fill,Qatlib.Concepts.TensorRegisters.RegisterModel.outside_fill]
  have hxc :=
      Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on ({c,t} : Finset (Fin n)) x c
      (by simp)
  have hxt :=
      Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on ({c,t} : Finset (Fin n)) x t
      (by simp)
  have hyc :=
      Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on ({c,t} : Finset (Fin n)) y c
      (by simp)
  have hyt :=
      Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on ({c,t} : Finset (Fin n)) y t
      (by simp)
  by_cases ho : Qatlib.Concepts.TensorRegisters.RegisterModel.outside ({c,t} : Finset (Fin n)) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside {c,t} y
  · have hr : regEq x (Function.update y t (y t ^^ y c)) =
        regEq (Qatlib.Concepts.TensorRegisters.RegisterModel.fill {c,t} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {c,t} x))
          (Function.update (Qatlib.Concepts.TensorRegisters.RegisterModel.fill {c,t} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {c,t} y)) t
            (Qatlib.Concepts.TensorRegisters.RegisterModel.fill {c,t} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {c,t} y) t ^^
              Qatlib.Concepts.TensorRegisters.RegisterModel.fill {c,t} (Qatlib.Concepts.TensorRegisters.RegisterModel.mask {c,t} y) c)) := by
      apply bool_eq_of_true_iff
      rw [cnot_regEq_iff c t hct,cnot_regEq_iff c t hct]
      simp only [ho,hf,true_and,hxc,hxt,hyc,hyt]
    simp only [if_pos ho,hr]
  · have hr : regEq x (Function.update y t (y t ^^ y c))=false :=
      bool_false_of_not_true _ (fun h => ho ((cnot_regEq_iff c t hct x y).mp h).1)
    simp [ho,hr]

/-- A finite gate's entry tag is determined by its masked gate support when outside registers
agree, and is zero otherwise. -/
theorem rawTag_strong (n : ℕ) (g : FiniteGateCode) (x y : Reg n) :
    rawTag n g x y =
      if Qatlib.Concepts.TensorRegisters.RegisterModel.outside (gateSites n g) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside (gateSites n g) y then
        rawTag n g (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (gateSites n g) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (gateSites n g) x))
          (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (gateSites n g) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (gateSites n g) y)) else zeroTag := by
  cases g with
  | h w =>
    by_cases hw : w < n
    · have hs : gateSites n (.h w)={⟨w,hw⟩}:=by simp [gateSites,hw]
      rw [hs]
      exact oneWireTag_strong (⟨w,hw⟩ : Fin n) hCell x y
    · have hs : gateSites n (.h w)=∅:=by simp [gateSites,hw]
      rw [hs]
      simpa only [rawTag,oneWireTag,dif_neg hw] using identityTag_strong x y
  | x w =>
    by_cases hw : w < n
    · have hs : gateSites n (.x w)={⟨w,hw⟩}:=by simp [gateSites,hw]
      rw [hs]
      exact oneWireTag_strong (⟨w,hw⟩ : Fin n) xCell x y
    · have hs : gateSites n (.x w)=∅:=by simp [gateSites,hw]
      rw [hs]
      simpa only [rawTag,oneWireTag,dif_neg hw] using identityTag_strong x y
  | t w =>
    by_cases hw : w < n
    · have hs : gateSites n (.t w)={⟨w,hw⟩}:=by simp [gateSites,hw]
      rw [hs]
      exact oneWireTag_strong (⟨w,hw⟩ : Fin n) tCell x y
    · have hs : gateSites n (.t w)=∅:=by simp [gateSites,hw]
      rw [hs]
      simpa only [rawTag,oneWireTag,dif_neg hw] using identityTag_strong x y
  | tdg w =>
    by_cases hw : w < n
    · have hs : gateSites n (.tdg w)={⟨w,hw⟩}:=by simp [gateSites,hw]
      rw [hs]
      exact oneWireTag_strong (⟨w,hw⟩ : Fin n) tdgCell x y
    · have hs : gateSites n (.tdg w)=∅:=by simp [gateSites,hw]
      rw [hs]
      simpa only [rawTag,oneWireTag,dif_neg hw] using identityTag_strong x y
  | cx c t =>
    by_cases hw : c < n ∧ t < n ∧ c≠t
    · have hct : (⟨c,hw.1⟩ : Fin n)≠⟨t,hw.2.1⟩ := by
        intro h
        exact hw.2.2 (congrArg Fin.val h)
      have hs : gateSites n (.cx c t)={⟨c,hw.1⟩,⟨t,hw.2.1⟩}:=by simp [gateSites,hw]
      rw [hs]
      simpa only [rawTag,dif_pos hw] using
        cnotTag_strong (⟨c,hw.1⟩ : Fin n) (⟨t,hw.2.1⟩ : Fin n) hct x y
    · have hs : gateSites n (.cx c t)=∅:=by simp [gateSites,hw]
      rw [hs]
      simpa only [rawTag,dif_neg hw] using identityTag_strong x y

/-- A finite gate's integer coefficient pair is determined by its masked gate support when
outside registers agree, and is zero otherwise. -/
theorem rawCoeff_strong (n b : ℕ) (g : FiniteGateCode) (x y : Reg n) :
    rawCoeff n b g x y =
      if Qatlib.Concepts.TensorRegisters.RegisterModel.outside (gateSites n g) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside (gateSites n g) y then
        rawCoeff n b g (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (gateSites n g) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (gateSites n g) x))
          (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (gateSites n g) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (gateSites n g) y)) else (0,0) := by
  have ht := rawTag_strong n g x y
  by_cases ho : Qatlib.Concepts.TensorRegisters.RegisterModel.outside (gateSites n g) x=Qatlib.Concepts.TensorRegisters.RegisterModel.outside (gateSites n g) y
  · rw [if_pos ho] at ht ⊢
    simp only [rawCoeff,ht]
  · rw [if_neg ho] at ht ⊢
    simp [rawCoeff,ht,zeroTag,atomNumerator]

/-- The central clock index belongs to its clock support. -/
theorem clock_center_mem {m : ℕ} (i : Fin m) : i∈clockSites i := by
  simp [clockSites]

/-- Masking and filling `clockSites i` preserves the left clock bit read by `nativeBit` at
`i.val`. -/
theorem nativeBit_left_fill {m : ℕ} (i : Fin m) (c : Clock m) :
    nativeBit (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (clockSites i) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (clockSites i) c)) i.val=
      nativeBit c i.val := by
  by_cases hz : i.val=0
  · simp [nativeBit,hz]
  · have hp : 0 < i.val := by omega
    have hm : i.val ≤ m := by omega
    simp only [nativeBit,dif_neg hz,dif_pos hm]
    apply Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on
    simp [clockSites,hp]

/-- Masking and filling `clockSites i` preserves the right clock bit read by `nativeBit` at
`i.val + 2`. -/
theorem nativeBit_right_fill {m : ℕ} (i : Fin m) (c : Clock m) :
    nativeBit (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (clockSites i) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (clockSites i) c)) (i.val+2)=
      nativeBit c (i.val+2) := by
  have hz : i.val+2≠0 := by omega
  by_cases hm : i.val+2 ≤ m
  · have hr : i.val+1 < m := by omega
    simp only [nativeBit,dif_neg hz,dif_pos hm]
    apply Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on
    have he : (⟨i.val+2-1,by omega⟩ : Fin m)=⟨i.val+1,hr⟩ := by
      apply Fin.ext
      change i.val+2-1=i.val+1
      omega
    rw [he]
    simp [clockSites,hr]
  · simp [nativeBit,hm]

/-- Masking and filling `clockSites i` preserves all three bit values used by the transition
guards. -/
theorem guard_values_fill {m : ℕ} (i : Fin m) (c : Clock m) :
    nativeBit (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (clockSites i) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (clockSites i) c)) i.val=
        nativeBit c i.val ∧
      Qatlib.Concepts.TensorRegisters.RegisterModel.fill (clockSites i) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (clockSites i) c) i=c i ∧
      nativeBit (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (clockSites i) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (clockSites i) c)) (i.val+2)=
        nativeBit c (i.val+2) :=
  ⟨nativeBit_left_fill i c,Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on _ _ i (clock_center_mem i),nativeBit_right_fill i c⟩

/-- Masking and filling the clock support preserves both the pre-transition and post-transition
Boolean guards. -/
theorem pre_post_fill {m : ℕ} (i : Fin m) (c : Clock m) :
    preBool i (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (clockSites i) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (clockSites i) c))=preBool i c ∧
      postBool i (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (clockSites i) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (clockSites i) c))=postBool i c := by
  obtain ⟨hl,hc,hr⟩ := guard_values_fill i c
  constructor <;> simp only [preBool,postBool,hl,hc,hr]

/-- For registers agreeing outside `K`, the test of agreement away from one site is preserved by
masking and filling `K`. -/
theorem outsideEq_fill {n : ℕ} (K : Finset (Fin n)) (i : Fin n) (r c : Reg n)
    (ho : Qatlib.Concepts.TensorRegisters.RegisterModel.outside K r=Qatlib.Concepts.TensorRegisters.RegisterModel.outside K c) :
    outsideEq i r c=outsideEq i (Qatlib.Concepts.TensorRegisters.RegisterModel.fill K (Qatlib.Concepts.TensorRegisters.RegisterModel.mask K r)) (Qatlib.Concepts.TensorRegisters.RegisterModel.fill K (Qatlib.Concepts.TensorRegisters.RegisterModel.mask K c)) := by
  apply bool_eq_of_true_iff
  rw [outsideEq_true_iff,outsideEq_true_iff]
  constructor
  · intro h j hj
    by_cases hjK : j∈K
    · rw [Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on K r j hjK,Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on K c j hjK]
      exact h j hj
    · rw [Qatlib.Concepts.TensorRegisters.RegisterModel.fill_off K _ j hjK,Qatlib.Concepts.TensorRegisters.RegisterModel.fill_off K _ j hjK]
  · intro h j hj
    by_cases hjK : j∈K
    · have he := h j hj
      rw [Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on K r j hjK,Qatlib.Concepts.TensorRegisters.RegisterModel.fill_mask_on K c j hjK] at he
      exact he
    · exact (Qatlib.Concepts.TensorRegisters.RegisterModel.outside_eq_iff K r c).mp ho j hjK

/-- The clock-hop test is determined by the masked clock support when outside registers agree,
and is false otherwise. -/
theorem hopBool_strong {m : ℕ} (i : Fin m) (r c : Clock m) :
    hopBool i r c =
      if Qatlib.Concepts.TensorRegisters.RegisterModel.outside (clockSites i) r=Qatlib.Concepts.TensorRegisters.RegisterModel.outside (clockSites i) c then
        hopBool i (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (clockSites i) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (clockSites i) r))
          (Qatlib.Concepts.TensorRegisters.RegisterModel.fill (clockSites i) (Qatlib.Concepts.TensorRegisters.RegisterModel.mask (clockSites i) c)) else false := by
  by_cases ho : Qatlib.Concepts.TensorRegisters.RegisterModel.outside (clockSites i) r=Qatlib.Concepts.TensorRegisters.RegisterModel.outside (clockSites i) c
  · rw [if_pos ho]
    have he := outsideEq_fill (clockSites i) i r c ho
    simp only [hopBool,(pre_post_fill i r).2,(pre_post_fill i c).1,← he]
  · have hz : hopBool i r c=false := bool_false_of_not_true _ (by
      intro h
      have hh := (hopBool_iff i r c).mp h
      apply ho
      apply (Qatlib.Concepts.TensorRegisters.RegisterModel.outside_eq_iff (clockSites i) r c).mpr
      intro j hj
      have hji : j≠i := by
        intro he
        subst j
        exact hj (clock_center_mem i)
      exact hh.2.2 j hji)
    simp [ho,hz]

/-- Boolean values are equal if being true is equivalent for the two values. -/
private theorem prop_bool_eq_of_true_iff (a b : Bool) (h : a=true ↔ b=true) : a=b := by
  cases a <;> cases b <;> simp_all

/-- A Boolean value unequal to true equals false. -/
private theorem prop_bool_false_of_not_true (a : Bool) (h : ¬a=true) : a=false := by
  cases a <;> simp_all

/-- Tests equality separately on the clock and work components of a register pair. -/
def regEqPairBool {m n : ℕ} (p q : Clock m×Reg n) : Bool :=
  regEq p.1 q.1 && regEq p.2 q.2

/-- The componentwise Boolean equality test is true exactly when the clock-work pairs are equal. -/
theorem regEqPairBool_true_iff {m n : ℕ} (p q : Clock m×Reg n) :
    regEqPairBool p q=true ↔ p=q := by
  rw [regEqPairBool,Bool.and_eq_true,regEq_true_iff,regEq_true_iff]
  constructor
  · rintro ⟨hc,hw⟩
    exact Prod.ext hc hw
  · rintro rfl
    exact ⟨rfl,rfl⟩

/-- For registers agreeing outside the propagation support, masking and filling that support
preserves the componentwise equality test. -/
theorem regEqPairBool_fill {m : ℕ} (n : ℕ) (i : Fin m) (g : FiniteGateCode)
    (x y : Reg (m+n))
    (ho : outside (propSites n i g) x=outside (propSites n i g) y) :
    regEqPairBool (flattenEquiv m n x) (flattenEquiv m n y)=
      regEqPairBool
        (flattenEquiv m n (fill (propSites n i g) (mask (propSites n i g) x)))
        (flattenEquiv m n (fill (propSites n i g) (mask (propSites n i g) y))) := by
  apply prop_bool_eq_of_true_iff
  simp only [regEqPairBool_true_iff,(flattenEquiv m n).injective.eq_iff]
  exact eq_fill_iff (propSites n i g) x y ho

/-- Propagation coefficient pairs are preserved by masking and filling their support when the
outside registers agree. -/
theorem propagationCoeff_fill {m : ℕ} (n b : ℕ) (i : Fin m) (g : FiniteGateCode)
    (x y : Reg (m+n))
    (ho : outside (propSites n i g) x=outside (propSites n i g) y) :
    propagationCoeff n b i g (flattenEquiv m n x) (flattenEquiv m n y)=
      propagationCoeff n b i g
        (flattenEquiv m n (fill (propSites n i g) (mask (propSites n i g) x)))
        (flattenEquiv m n (fill (propSites n i g) (mask (propSites n i g) y))) := by
  let X : Reg (m+n) := fill (propSites n i g) (mask (propSites n i g) x)
  let Y : Reg (m+n) := fill (propSites n i g) (mask (propSites n i g) y)
  have hc := ((prop_outside_iff n i g x y).mp ho).1
  have hw := ((prop_outside_iff n i g x y).mp ho).2
  have hXc : (flattenEquiv m n X).1=
      fill (clockSites i) (mask (clockSites i) (flattenEquiv m n x).1) :=
    prop_fill_clock n i g x
  have hYc : (flattenEquiv m n Y).1=
      fill (clockSites i) (mask (clockSites i) (flattenEquiv m n y).1) :=
    prop_fill_clock n i g y
  have hXw : (flattenEquiv m n X).2=
      fill (gateSites n g) (mask (gateSites n g) (flattenEquiv m n x).2) :=
    prop_fill_work n i g x
  have hYw : (flattenEquiv m n Y).2=
      fill (gateSites n g) (mask (gateSites n g) (flattenEquiv m n y).2) :=
    prop_fill_work n i g y
  have hpost : postBool i (flattenEquiv m n X).1=postBool i (flattenEquiv m n x).1 := by
    rw [hXc]
    exact (pre_post_fill i (flattenEquiv m n x).1).2
  have hpre : preBool i (flattenEquiv m n X).1=preBool i (flattenEquiv m n x).1 := by
    rw [hXc]
    exact (pre_post_fill i (flattenEquiv m n x).1).1
  have hhop : hopBool i (flattenEquiv m n x).1 (flattenEquiv m n y).1=
      hopBool i (flattenEquiv m n X).1 (flattenEquiv m n Y).1 := by
    rw [hXc,hYc]
    simpa only [if_pos hc] using
      hopBool_strong i (flattenEquiv m n x).1 (flattenEquiv m n y).1
  have hhopRev : hopBool i (flattenEquiv m n y).1 (flattenEquiv m n x).1=
      hopBool i (flattenEquiv m n Y).1 (flattenEquiv m n X).1 := by
    rw [hYc,hXc]
    simpa only [if_pos hc.symm] using
      hopBool_strong i (flattenEquiv m n y).1 (flattenEquiv m n x).1
  have hraw : rawCoeff n b g (flattenEquiv m n x).2 (flattenEquiv m n y).2=
      rawCoeff n b g (flattenEquiv m n X).2 (flattenEquiv m n Y).2 := by
    rw [hXw,hYw]
    simpa only [if_pos hw] using
      rawCoeff_strong n b g (flattenEquiv m n x).2 (flattenEquiv m n y).2
  have hrawRev : rawCoeff n b g (flattenEquiv m n y).2 (flattenEquiv m n x).2=
      rawCoeff n b g (flattenEquiv m n Y).2 (flattenEquiv m n X).2 := by
    rw [hYw,hXw]
    simpa only [if_pos hw.symm] using
      rawCoeff_strong n b g (flattenEquiv m n y).2 (flattenEquiv m n x).2
  have hdiag :
      (regEq (flattenEquiv m n x).1 (flattenEquiv m n y).1 &&
        regEq (flattenEquiv m n x).2 (flattenEquiv m n y).2)=
      (regEq (flattenEquiv m n X).1 (flattenEquiv m n Y).1 &&
        regEq (flattenEquiv m n X).2 (flattenEquiv m n Y).2) :=
    regEqPairBool_fill n i g x y ho
  change propagationCoeff n b i g (flattenEquiv m n x) (flattenEquiv m n y)=
    propagationCoeff n b i g (flattenEquiv m n X) (flattenEquiv m n Y)
  simp only [propagationCoeff,hdiag,hpost,hpre,hhop,hhopRev,hraw,hrawRev]

/-- The forward hopping coefficient pair vanishes when the registers differ outside the
propagation support. -/
theorem forwardCoeff_zero_of_outside_ne {m : ℕ} (n b : ℕ) (i : Fin m)
    (g : FiniteGateCode) (x y : Reg (m+n))
    (ho : outside (propSites n i g) x≠outside (propSites n i g) y) :
    (if hopBool i (flattenEquiv m n x).1 (flattenEquiv m n y).1 then
      rawCoeff n b g (flattenEquiv m n x).2 (flattenEquiv m n y).2 else (0,0))=(0,0) := by
  by_cases hc : outside (clockSites i) (flattenEquiv m n x).1=
      outside (clockSites i) (flattenEquiv m n y).1
  · have hw : outside (gateSites n g) (flattenEquiv m n x).2≠
        outside (gateSites n g) (flattenEquiv m n y).2 := by
      intro hw
      exact ho ((prop_outside_iff n i g x y).mpr ⟨hc,hw⟩)
    have hr : rawCoeff n b g (flattenEquiv m n x).2 (flattenEquiv m n y).2=(0,0) := by
      simpa only [if_neg hw] using
        rawCoeff_strong n b g (flattenEquiv m n x).2 (flattenEquiv m n y).2
    simp only [hr,ite_self]
  · have hh : hopBool i (flattenEquiv m n x).1 (flattenEquiv m n y).1=false := by
      simpa only [if_neg hc] using
        hopBool_strong i (flattenEquiv m n x).1 (flattenEquiv m n y).1
    simp [hh]

/-- The propagation coefficient pair vanishes when the registers differ outside the propagation
support. -/
theorem propagationCoeff_zero_of_outside_ne {m : ℕ} (n b : ℕ) (i : Fin m)
    (g : FiniteGateCode) (x y : Reg (m+n))
    (ho : outside (propSites n i g) x≠outside (propSites n i g) y) :
    propagationCoeff n b i g (flattenEquiv m n x) (flattenEquiv m n y)=(0,0) := by
  have hd :
      (regEq (flattenEquiv m n x).1 (flattenEquiv m n y).1 &&
        regEq (flattenEquiv m n x).2 (flattenEquiv m n y).2)=false := by
    apply prop_bool_false_of_not_true
    intro h
    have hp : flattenEquiv m n x=flattenEquiv m n y :=
      (regEqPairBool_true_iff _ _).mp h
    have hxy : x=y := (flattenEquiv m n).injective hp
    apply ho
    rw [hxy]
  have hf := forwardCoeff_zero_of_outside_ne n b i g x y ho
  have hr := forwardCoeff_zero_of_outside_ne n b i g y x (fun he => ho he.symm)
  simp [propagationCoeff,hd,hf,hr]

/-- The propagation coefficient pair is recovered from the masked local registers when outside
registers agree, and is zero otherwise. -/
theorem propagationCoeff_strong {m : ℕ} (n b : ℕ) (i : Fin m) (g : FiniteGateCode)
    (x y : Reg (m+n)) :
    propagationCoeff n b i g (flattenEquiv m n x) (flattenEquiv m n y)=
      if outside (propSites n i g) x=outside (propSites n i g) y then
        propagationCoeff n b i g
          (flattenEquiv m n (fill (propSites n i g) (mask (propSites n i g) x)))
          (flattenEquiv m n (fill (propSites n i g) (mask (propSites n i g) y)))
      else (0,0) := by
  by_cases ho : outside (propSites n i g) x=outside (propSites n i g) y
  · rw [if_pos ho]
    exact propagationCoeff_fill n b i g x y ho
  · rw [if_neg ho]
    exact propagationCoeff_zero_of_outside_ne n b i g x y ho

end Qatlib.Concepts.QueryComplexity.DegreeMethod
