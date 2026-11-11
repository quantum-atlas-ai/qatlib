/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.Corollary74Stat
import Qatlib.Concepts.CircuitImpl.MultiControl.CountPackedCommutator

/-!
# Elementary synthesis of conjunction-controlled toggles

This module proves `corollary7_4`, the elementary-gate conjunction-toggle bound corresponding to
Corollary 7.4 of [BarencoEtAl1995]. For at least five distinct controls with separate spectator
and target wires, it constructs a legal, query-free word of length at most `48 * m - 108` and
verifies its basis-state action.

## Main statements

* `corollary7_4`: The synthesis bound with explicit wire separation and gate accounting.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.CircuitImpl.MultiControl.CountFramedBorrowed
open Qatlib.Concepts.CircuitImpl.MultiControl.CountPackedCommutator
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl.Corollary74Elem
open Matrix
open scoped Classical BigOperators

/-- Two Boolean sequences agreeing on their first `r` entries have equal prefix conjunctions. -/
private theorem and_congr (c d : ℕ → Bool) (r : ℕ) (h : ∀ i < r, c i = d i) :
    noWorkPrefixAnd c r = noWorkPrefixAnd d r := by
  apply Bool.eq_iff_iff.mpr
  simp only [noWorkPrefixAnd, List.all_eq_true, List.mem_range]
  constructor
  · intro hc i hi
    rw [← h i hi]
    exact hc i hi
  · intro hd i hi
    rw [h i hi]
    exact hd i hi

/-- Changing a wire outside the prefix control wires leaves their conjunction unchanged. -/
private theorem and_update {N : ℕ} (c : ℕ → Fin N) (r : ℕ) (s : Fin N)
    (hc : ∀ i < r, c i ≠ s) (x : Reg N) (v : Bool) :
    noWorkPrefixAnd (fun i => Function.update x s v (c i)) r = noWorkPrefixAnd (fun i => x (c i)) r :=
  and_congr _ _ _ (fun i hi => Function.update_of_ne (hc i hi) _ _)

/-- A prefix conjunction over `a + b` bits is the conjunction of its two consecutive segments. -/
private theorem and_add (c : ℕ → Bool) (a b : ℕ) :
    noWorkPrefixAnd c (a+b) = (noWorkPrefixAnd c a && noWorkPrefixAnd (fun i => c (a+i)) b) := by
  simp [noWorkPrefixAnd, List.range_add, List.all_map, Function.comp_def]

/-- A singleton word containing a unitary single-wire gate is legal. -/
private theorem singleton_legal {N : ℕ} (s : Fin N) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ unitaryGroup Bool ℂ) : reflectionLegal [.inl (s,U)] := by
  simpa [reflectionLegal, reflectionGateLegal] using! hU

/-- For `m ≥ 5` distinct controls and separate spectator and target wires, constructs a legal,
query-free conjunction toggle of length at most `48 * m - 108` [Barenco et al., Corollary
7.4][BarencoEtAl1995]. -/
theorem corollary7_4 : Corollary7_4 := by
  intro N m c s t hm hc hcs hct hst
  let a := (m+1)/2
  let b := m/2
  let ra := a-2
  let rb := b-1
  have hab : a+b=m := by dsimp [a,b]; omega
  have ha : 3 ≤ a := by dsimp [a]; omega
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hbal : b ≤ a ∧ a ≤ b+1 := by dsimp [a,b]; omega
  have hra : 1 ≤ ra := by dsimp [ra]; omega
  have hrb : 1 ≤ rb := by dsimp [rb]; omega
  have hea : ra+2=a := by dsimp [ra]; omega
  have heb : rb+2=b+1 := by dsimp [rb]; omega
  have hsum : ra+rb=m-3 := by dsimp [ra,rb]; omega
  have hne (i j : ℕ) (hi : i < m) (hj : j < m) (hij : i ≠ j) : c i ≠ c j :=
    fun he => hij (hc hi hj he)
  let ca : ℕ → Fin N := c
  let wa : ℕ → Fin N := fun j => c (a+j)
  let cb : ℕ → Fin N := fun i => if i < b then c (a+i) else s
  let wb : ℕ → Fin N := c
  have hca : Set.InjOn ca (Set.Iio a) := by
    intro i hi j hj he
    exact hc (show i < m from by change i < a at hi; omega)
      (show j < m from by change j < a at hj; omega) he
  have hwa : Set.InjOn wa (Set.Iio ra) := by
    intro i hi j hj he
    have heq : a+i=a+j := hc (show a+i < m from by change i < ra at hi; omega)
      (show a+j < m from by change j < ra at hj; omega) he
    omega
  have hcrossA : ∀ i < a, ∀ j < ra, ca i ≠ wa j := by
    intro i hi j hj
    exact hne i (a+j) (by omega) (by omega) (by omega)
  have hLA : noWorkDirtyPrefixLayout ca wa ra := by
    refine ⟨?_,hwa,?_⟩
    · intro i hi j hj he
      exact hca (show i < a from by change i < ra+1 at hi; omega)
        (show j < a from by change j < ra+1 at hj; omega) he
    · intro i hi j hj
      exact hcrossA i (by omega) j hj
  have hAcS : ∀ i < ra+2, ca i ≠ s := fun i hi => hcs i (by omega)
  have hAwS : ∀ j < ra, wa j ≠ s := fun j hj => hcs (a+j) (by omega)
  have hAlast : ∀ j < ra, ca (ra+1) ≠ wa j := fun j hj => hcrossA _ (by omega) j hj
  have hcb : Set.InjOn cb (Set.Iio (b+1)) := by
    intro i hi j hj he
    change i < b+1 at hi
    change j < b+1 at hj
    by_cases hib : i < b <;> by_cases hjb : j < b
    · simp only [cb, if_pos hib, if_pos hjb] at he
      have heq : a+i=a+j := hc (show a+i < m from by omega) (show a+j < m from by omega) he
      omega
    · simp only [cb, if_pos hib, if_neg hjb] at he
      exact (hcs (a+i) (by omega) he).elim
    · simp only [cb, if_neg hib, if_pos hjb] at he
      exact (hcs (a+j) (by omega) he.symm).elim
    · omega
  have hwb : Set.InjOn wb (Set.Iio rb) := by
    intro i hi j hj he
    exact hc (show i < m from by change i < rb at hi; omega)
        (show j < m from by change j < rb at hj; omega) he
  have hcrossB : ∀ i < b+1, ∀ j < rb, cb i ≠ wb j := by
    intro i hi j hj
    by_cases hib : i < b
    · simp only [cb, if_pos hib, wb]
      exact hne (a+i) j (by omega) (by omega) (by omega)
    · simp only [cb, if_neg hib, wb]
      exact (hcs j (by omega)).symm
  have hLB : noWorkDirtyPrefixLayout cb wb rb := by
    refine ⟨?_,hwb,?_⟩
    · intro i hi j hj he
      exact hcb (show i < b+1 from by change i < rb+1 at hi; omega)
        (show j < b+1 from by change j < rb+1 at hj; omega) he
    · intro i hi j hj
      exact hcrossB i (by omega) j hj
  have hBcT : ∀ i < rb+2, cb i ≠ t := by
    intro i hi
    by_cases hib : i < b
    · simpa only [cb, if_pos hib] using! hct (a+i) (by omega)
    · simpa only [cb, if_neg hib] using! hst
  have hBwT : ∀ j < rb, wb j ≠ t := fun j hj => hct j (by omega)
  have hBlast : ∀ j < rb, cb (rb+1) ≠ wb j := fun j hj => hcrossB _ (by omega) j hj
  have hBfirst : ∀ i < rb+1, cb (rb+1) ≠ cb i := by
    intro i hi he
    have heq : rb+1=i := hcb (show rb+1 < b+1 from by omega) (show i < b+1 from by omega) he
    omega
  have hBwire : cb (rb+1)=s := by
    have heq : rb+1=b := by omega
    rw [heq]
    simp [cb]
  let ar := sourceBorrowedRelative ca wa s ra
  let br := sourceBorrowedExact cb wb t rb
  let ac := sourceBorrowedRelativeCore ca wa s ra
  let bc := sourceBorrowedExactCore cb wb t rb
  let R := qubitEulerRotation (-Real.pi/4)
  let gs := sourcePackedCommutator s t R tGate ac bc
  have har : reflectionLegal ar := sourceBorrowedRelative_legal ca wa s ra hra hLA hAcS hAwS
  have hbr : reflectionLegal br := sourceBorrowedExact_legal cb wb t rb hrb hLB hBlast hBcT hBwT
  have hac : reflectionLegal ac := sourceBorrowedRelativeCore_legal ca wa s ra hra hLA hAcS hAwS
  have hbc : reflectionLegal bc := sourceBorrowedExactCore_legal cb wb t rb hrb hLB hBlast hBcT hBwT
  have havAr : ∀ g ∈ ar, t ∉ reflectionGateWires g :=
    sourceBorrowedRelative_avoids ca wa s t ra hra
      (fun i hi => (hct i (by omega)).symm) (fun j hj => (hct (a+j) (by omega)).symm) hst.symm
  have havAc : ∀ g ∈ ac, t ∉ reflectionGateWires g :=
    sourceBorrowedRelativeCore_avoids ca wa s t ra hra
      (fun i hi => (hct i (by omega)).symm) (fun j hj => (hct (a+j) (by omega)).symm) hst.symm
  let A : Reg N → Bool := fun x => noWorkPrefixAnd (fun i => x (c i)) a
  let B : Reg N → Bool := fun x => noWorkPrefixAnd (fun i => x (c (a+i))) b
  let z : Reg N → ℂ := sourceBorrowedSign ca wa s ra
  have hRA (x : Reg N) : Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile ar) (Qatlib.Foundations.PureStateMath.Ket x) =
      z x • Qatlib.Foundations.PureStateMath.Ket (Function.update x s (x s ^^ A x)) := by
    have hh := sourceBorrowedRelative_ket ca wa s ra hra hLA hAlast hAcS hAwS x
    simpa only [hea, ca, ar, A, z] using! hh
  have hBconj (x : Reg N) : noWorkPrefixAnd (fun i => x (cb i)) (rb+2)=(B x && x s) := by
    rw [heb, noWorkPrefixAnd_succ]
    have hp : noWorkPrefixAnd (fun i => x (cb i)) b = B x :=
      and_congr _ _ _ (fun i hi => by simp only [cb, if_pos hi])
    rw [hp, show cb b=s from by simp [cb]]
  have hRB (x : Reg N) : Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile br) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (B x && x s))) := by
    have hh := sourceBorrowedExact_ket cb wb t rb hrb hLB hBlast hBcT hBwT x
    rw [hBconj x] at hh
    exact hh
  have hBstable (x : Reg N) (v : Bool) : B (Function.update x s v)=B x ∧ B (Function.update x t v)=B x :=
    ⟨and_update (fun i => c (a+i)) b s (fun i hi => hcs (a+i) (by omega)) x v,
      and_update (fun i => c (a+i)) b t (fun i hi => hct (a+i) (by omega)) x v⟩
  have hquad (x : Reg N) : Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (ar ++ br ++ reflectionAdjoint ar ++ reflectionAdjoint br)) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) m)) := by
    have hh := source_signed_dirty_combine s t hst A B hBstable ar br har hbr havAr z
      (sourceBorrowedSign_sq ca wa s ra) hRA hRB x
    simpa only [← hab, and_add, A, B] using! hh
  let af : List (ReflectionGate N) := [.inl (s,R)] ++ ac ++ [.inl (s,Rᴴ)]
  let bf : List (ReflectionGate N) :=
      [.inl (s,tGate), .inl (t,Hadamard)] ++ bc ++ [.inl (t,Hadamard), .inl (s,tGateᴴ)]
  have hR : R ∈ unitaryGroup Bool ℂ := qubitEulerRotation_unitary _
  have haf : reflectionLegal af := by
    simp only [af, reflectionLegal_append]
    exact ⟨⟨singleton_legal s R hR,hac⟩,singleton_legal s Rᴴ (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hR)⟩
  have hbf : reflectionLegal bf := by
    have hf : reflectionLegal [.inl (s,tGate), .inl (t,Hadamard)] := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact tGate_mem_unitary
      · exact hadamard_unitary
    have ht : reflectionLegal [.inl (t,Hadamard), .inl (s,tGateᴴ)] := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hadamard_unitary
      · exact Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary tGate_mem_unitary
    simp only [bf, reflectionLegal_append]
    exact ⟨⟨hf,hbc⟩,ht⟩
  have hMA : reflectionProgramMatrix af=reflectionProgramMatrix ar :=
    sourceBorrowedRelative_frame ca wa s ra hLA (fun i hi => hAcS i (by omega)) hAwS
  have hMB : reflectionProgramMatrix bf=reflectionProgramMatrix br := by
    have hh := sourceBorrowedExact_frame cb wb t rb hrb hLB hBlast hBfirst hBcT hBwT
    simpa only [hBwire, bf, bc, br] using! hh
  have hM : reflectionProgramMatrix gs =
      reflectionProgramMatrix (ar ++ br ++ reflectionAdjoint ar ++ reflectionAdjoint br) := by
    exact (sourcePackedCommutator_matrix s t hst R tGate hR tGate_mem_unitary ac bc hac hbc havAc).trans
      (source_quad_matrix_congr af bf ar br haf hbf har hbr hMA hMB)
  refine ⟨gs, sourcePackedCommutator_legal s t R tGate hR tGate_mem_unitary ac bc hac hbc,
    ?_, queryCount_reflectionCompile gs, gateCount_reflectionCompile gs, ?_⟩
  · have hAC := (sourceBorrowedCore_lengths ca wa s t ra hra).1
    have hBC := (sourceBorrowedCore_lengths cb wb s t rb hrb).2
    change (sourcePackedCommutator s t R tGate ac bc).length ≤ 48*m-108
    rw [sourcePackedCommutator_length]
    change 2*(sourceBorrowedRelativeCore ca wa s ra).length+2*(sourceBorrowedExactCore cb wb t rb).length+7 ≤ 48*m-108
    rw [hAC,hBC]
    omega
  · intro x
    rw [run_reflectionCompile, hM, ← run_reflectionCompile]
    exact hquad x

end Qatlib.Concepts.CircuitImpl.MultiControl.Corollary74Elem
