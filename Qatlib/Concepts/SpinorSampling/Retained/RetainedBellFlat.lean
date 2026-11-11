/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedSpinCohorts

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Retained Bell Flat

Retained Bell Flat constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Qatlib ShiftCircuit NativeBridge

/-- Complete original `native_h_update` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem native_h_update {N : ℕ} (f : QState (Reg N)) (w : Fin N) (x : Reg N) :
    ApplyGate (wireGate N w Hadamard) f x=
      (f (Function.update x w false)+(if x w then (-1 : ℂ) else 1)*
        f (Function.update x w true))/(Real.sqrt 2 : ℂ) := by
  let x0 := Function.update x w false
  let x1 := Function.update x w true
  let g : Reg N → ℂ := fun y => wireGate N w Hadamard x y*f y
  have h01 : x0≠x1 := by
    intro h
    have hh := congrFun h w
    have hf : false=true := by simpa only [x0,x1,Function.update_self] using hh
    cases hf
  have hs0 : ∀ j : Fin N,j≠w → x j=x0 j := by
    intro j hj
    simp [x0,Function.update_of_ne hj]
  have hs1 : ∀ j : Fin N,j≠w → x j=x1 j := by
    intro j hj
    simp [x1,Function.update_of_ne hj]
  have hoff (y : Reg N) (_hy : y∈(Finset.univ : Finset (Reg N)))
      (hout : y∉({x0,x1} : Finset (Reg N))) : g y=0 := by
    dsimp [g]
    rw [wireGate_apply]
    split_ifs with hs
    · have hy : y=Function.update x w (y w) := by
        funext j
        by_cases hj : j=w
        · subst j
          simp
        · rw [Function.update_of_ne hj]
          exact (hs j hj).symm
      cases hb : y w
      · have h : y=x0 := by simpa only [hb] using hy
        exact (hout (by simp [h])).elim
      · have h : y=x1 := by simpa only [hb] using hy
        exact (hout (by simp [h])).elim
    · exact zero_mul _
  change (∑ y : Reg N,g y)=_
  rw [← Finset.sum_subset (Finset.subset_univ ({x0,x1} : Finset (Reg N))) hoff]
  rw [Finset.sum_insert (by simp [h01]),Finset.sum_singleton]
  simp only [g,wireGate_apply,ite_eq_left hs0,ite_eq_left hs1]
  dsimp [x0,x1]
  cases h : x w <;> simp [Hadamard,div_eq_mul_inv] <;> ring

variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

/-- Construction for pair Site in the retained bell flat model. -/
def pairSite (e : I × Bool → Fin N) (σ : Reg N) (i : I) : Reg 2 :=
  pairReg (σ (e (i,false))) (σ (e (i,true)))

/-- Construction for paired State in the retained bell flat model. -/
def pairedState (e : I × Bool → Fin N) (f : I → QState (Reg 2))
    (u : unusedWires e → Bool → ℂ) : QState (Reg N) := fun σ =>
  (∏ i : I,f i (pairSite e σ i))*(∏ w : unusedWires e,u w (σ w.val))

/-- Construction for rest Factor in the retained bell flat model. -/
def restFactor (e : I × Bool → Fin N) (i : I) (f : I → QState (Reg 2))
    (u : unusedWires e → Bool → ℂ) (σ : Reg N) : ℂ :=
  (∏ j ∈ Finset.univ.erase i,f j (pairSite e σ j))*(∏ w : unusedWires e,u w (σ w.val))

/-- Complete original `paired_state_split` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem paired_state_split (e : I × Bool → Fin N) (i : I) (f : I → QState (Reg 2))
    (u : unusedWires e → Bool → ℂ) (σ : Reg N) :
    pairedState e f u σ=f i (pairSite e σ i)*restFactor e i f u σ := by
  dsimp [pairedState,restFactor]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (pairSite e σ j)) (Finset.mem_univ i)]
  ring

omit [Fintype I] [DecidableEq I] in
/-- Complete original `other_pair_wire_ne` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem other_pair_wire_ne (e : I × Bool → Fin N) (he : Function.Injective e)
    {i j : I} (hji : j≠i) (a b : Bool) : e (j,a)≠e (i,b) := by
  intro h
  exact hji (congrArg Prod.fst (he h))

omit [Fintype I] [DecidableEq I] in
/-- Complete original `within_pair_wire_ne` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem within_pair_wire_ne (e : I × Bool → Fin N) (he : Function.Injective e) (i : I) :
    e (i,false)≠e (i,true) := by
  intro h
  have hh := congrArg Prod.snd (he h)
  cases hh

/-- Complete original `rest_factor_update_bit` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem rest_factor_update_bit (e : I × Bool → Fin N) (he : Function.Injective e)
    (i : I) (f : I → QState (Reg 2)) (u : unusedWires e → Bool → ℂ)
    (σ : Reg N) (b value : Bool) :
    restFactor e i f u (Function.update σ (e (i,b)) value)=restFactor e i f u σ := by
  unfold restFactor
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [pairSite,Function.update_of_ne (other_pair_wire_ne e he hji false b),
      Function.update_of_ne (other_pair_wire_ne e he hji true b)]
  · apply Finset.prod_congr rfl
    intro w _
    have hw : w.val≠e (i,b) := by
      intro h
      exact w.property ⟨(i,b),h.symm⟩
    rw [Function.update_of_ne hw]

/-- Complete original `rest_factor_update_family` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem rest_factor_update_family (e : I × Bool → Fin N) (i : I)
    (f : I → QState (Reg 2)) (g : QState (Reg 2))
    (u : unusedWires e → Bool → ℂ) (σ : Reg N) :
    restFactor e i (Function.update f i g) u σ=restFactor e i f u σ := by
  unfold restFactor
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

omit [Fintype I] [DecidableEq I] in
/-- Complete original `pair_site_update_first` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem pair_site_update_first (e : I × Bool → Fin N) (he : Function.Injective e)
    (i : I) (σ : Reg N) (value : Bool) :
    pairSite e (Function.update σ (e (i,false)) value) i=pairReg value (σ (e (i,true))) := by
  simp only [pairSite,Function.update_self,
    Function.update_of_ne (within_pair_wire_ne e he i).symm]

omit [Fintype I] [DecidableEq I] in
/-- Complete original `pair_site_update_second` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem pair_site_update_second (e : I × Bool → Fin N) (he : Function.Injective e)
    (i : I) (σ : Reg N) (value : Bool) :
    pairSite e (Function.update σ (e (i,true)) value) i=pairReg (σ (e (i,false))) value := by
  simp only [pairSite,Function.update_self,Function.update_of_ne (within_pair_wire_ne e he i)]

/-- Complete original `native_cnot_paired_at` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem native_cnot_paired_at (e : I × Bool → Fin N) (he : Function.Injective e)
    (i : I) (f : I → QState (Reg 2)) (u : unusedWires e → Bool → ℂ) (σ : Reg N) :
    ApplyGate (cnotGate N (e (i,false)) (e (i,true))) (pairedState e f u) σ=
      ApplyGate (cnotGate 2 0 1) (f i) (pairSite e σ i)*restFactor e i f u σ := by
  rw [cnotGate,applyGate_permMatrix
    (cnotUpdate_involutive N (e (i,false)) (e (i,true)) (within_pair_wire_ne e he i))]
  rw [paired_state_split e i,rest_factor_update_bit e he i f u σ true,
    pair_site_update_second e he]
  dsimp only [pairSite]
  rw [native_cnot_at]

/-- Construction for pair Word in the retained bell flat model. -/
def pairWord (e : I × Bool → Fin N) (l : List I) : List (MeasurementGate N) :=
  l.flatMap fun i => [.native (.cx (e (i,false)) (e (i,true))),.native (.h (e (i,false)))]

/-- Construction for pair Program in the retained bell flat model. -/
def pairProgram (e : I × Bool → Fin N) (l : List I) : Circuit (Reg N) :=
  measurementProgram (pairWord e l)

/-- Complete original `one_pair_program_transport` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem one_pair_program_transport (e : I × Bool → Fin N) (he : Function.Injective e)
    (i : I) (f : I → QState (Reg 2)) (u : unusedWires e → Bool → ℂ) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (pairProgram e [i]) (pairedState e f u)=
      pairedState e (Function.update f i
        (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) bellProgram (f i))) u := by
  funext σ
  change ApplyGate (wireGate N (e (i,false)) Hadamard)
    (ApplyGate (cnotGate N (e (i,false)) (e (i,true))) (pairedState e f u)) σ=_
  rw [native_h_update,native_cnot_paired_at e he,native_cnot_paired_at e he]
  rw [rest_factor_update_bit e he i f u σ false,
    rest_factor_update_bit e he i f u σ false,
    pair_site_update_first e he,pair_site_update_first e he]
  rw [paired_state_split e i,rest_factor_update_family,Function.update_self]
  let localCnot := ApplyGate (cnotGate 2 0 1) (f i)
  have hlocal : Run (1 : Matrix (Reg 2) (Reg 2) ℂ) bellProgram (f i) (pairSite e σ i)=
      (localCnot (pairReg false (σ (e (i,true))))+
        (if σ (e (i,false)) then (-1 : ℂ) else 1)*
          localCnot (pairReg true (σ (e (i,true)))))/
        (Real.sqrt 2 : ℂ) := by
    change ApplyGate (wireGate 2 0 Hadamard) (ApplyGate (cnotGate 2 0 1) (f i))
      (pairReg (σ (e (i,false))) (σ (e (i,true))))=_
    exact native_h_at _ _ _
  rw [hlocal]
  ring

omit [Fintype I] [DecidableEq I] in
/-- Complete original `pair_program_cons` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem pair_program_cons (e : I × Bool → Fin N) (i : I) (l : List I) :
    pairProgram e (i::l)=pairProgram e [i]++pairProgram e l := by
  simp [pairProgram,pairWord,measurementProgram,reflectionCompile]

/-- Complete original `pair_program_transport` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem pair_program_transport (e : I × Bool → Fin N) (he : Function.Injective e)
    (l : List I) (hl : l.Nodup) (f : I → QState (Reg 2)) (u : unusedWires e → Bool → ℂ) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (pairProgram e l) (pairedState e f u)=
      pairedState e (fun i => if i∈l then
        Run (1 : Matrix (Reg 2) (Reg 2) ℂ) bellProgram (f i) else f i) u := by
  induction l generalizing f with
  | nil => simp [pairProgram,pairWord,measurementProgram,reflectionCompile]
  | cons i l ih =>
    have hi := (List.nodup_cons.mp hl).1
    have hn := (List.nodup_cons.mp hl).2
    rw [pair_program_cons,run_append,one_pair_program_transport e he,ih hn]
    congr 1
    funext j
    by_cases hji : j=i
    · subst j
      simp [hi]
    · simp [hji]

omit [Fintype I] [DecidableEq I] in
/-- Complete original `pair_word_length` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem pair_word_length (e : I × Bool → Fin N) (l : List I) : (pairWord e l).length=2*l.length := by
  induction l with
  | nil => simp [pairWord]
  | cons i l ih =>
    simp only [pairWord,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil]
    change 2+(pairWord e l).length=2*(l.length+1)
    rw [ih]
    omega

omit [Fintype I] [DecidableEq I] in
/-- Complete original `pair_program_counts` guarantee for `RetainedBellFlat`; all source hypotheses and output obligations are retained. -/
theorem pair_program_counts (e : I × Bool → Fin N) (l : List I) :
    QueryCount (pairProgram e l)=0 ∧ GateCount (pairProgram e l)=2*l.length := by
  simpa only [pairProgram,pair_word_length] using measurement_program_counts (pairWord e l)

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.native_h_update
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.one_pair_program_transport
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pair_program_transport
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pair_program_counts
