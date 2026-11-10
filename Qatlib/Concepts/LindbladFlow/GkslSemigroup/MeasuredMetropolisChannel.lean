/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel
import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedInstrument
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError
import Qatlib.Concepts.CopyEvolution.Discriminate.PartialSwapEvolution
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.LindbladFlow.GkslSemigroup

open Matrix

open scoped ComplexOrder

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

noncomputable def thermalKrausWeight (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (i j : Fin D)
    (b : Bool) : ℝ :=
  if b then thermalAcceptance E β i j / (D : ℝ)
  else (1 - thermalAcceptance E β i j) / (D : ℝ)

def thermalKrausRow (D : ℕ) (i j : Fin D) (b : Bool) : Fin D :=
  if b then j else i

noncomputable def thermalKraus (D : ℕ) (E : Fin D → ℝ) (β : ℝ)
    (o : Fin D × Fin D × Bool) : Operator D :=
  Matrix.of fun r p : Fin D =>
    if p = o.1 ∧ r = thermalKrausRow D o.1 o.2.1 o.2.2 then
      (Real.sqrt (thermalKrausWeight D E β o.1 o.2.1 o.2.2) : ℂ) else 0

@[simp] theorem thermalKraus_apply (D : ℕ) (E : Fin D → ℝ) (β : ℝ)
    (o : Fin D × Fin D × Bool) (r p : Fin D) :
    thermalKraus D E β o r p =
      if p = o.1 ∧ r = thermalKrausRow D o.1 o.2.1 o.2.2 then
        (Real.sqrt (thermalKrausWeight D E β o.1 o.2.1 o.2.2) : ℂ) else 0 := rfl

theorem thermalKrausWeight_nonneg (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (i j : Fin D) (b : Bool) : 0 ≤ thermalKrausWeight D E β i j b := by
  by_cases hb : b
  · rw [thermalKrausWeight, if_pos hb]
    exact div_nonneg (thermalAcceptance_pos E β i j).le (by exact_mod_cast hD.le)
  · rw [thermalKrausWeight, if_neg hb]
    exact div_nonneg (by linarith [thermalAcceptance_le_one E β i j])
      (by exact_mod_cast hD.le)

private theorem thermalKraus_mul_conjTranspose_entry (D : ℕ) (hD : 0 < D)
    (E : Fin D → ℝ) (β : ℝ) (o : Fin D × Fin D × Bool) (p q : Fin D) :
    ((thermalKraus D E β o)ᴴ*thermalKraus D E β o) p q
      = if p = o.1 ∧ q = o.1 then (thermalKrausWeight D E β o.1 o.2.1 o.2.2 : ℂ) else 0 := by
  have hreal : ∀ x : ℝ, star ((x : ℂ)) = ((x : ℂ)) := fun x => by simp
  have hsq : star ((Real.sqrt (thermalKrausWeight D E β o.1 o.2.1 o.2.2 : ℝ) : ℂ))
      * (Real.sqrt (thermalKrausWeight D E β o.1 o.2.1 o.2.2 : ℝ) : ℂ)
      = (thermalKrausWeight D E β o.1 o.2.1 o.2.2 : ℂ) := by
    rw [hreal, ← Complex.ofReal_mul, ← sq,
      Real.sq_sqrt (thermalKrausWeight_nonneg D hD E β o.1 o.2.1 o.2.2)]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, thermalKraus_apply]
  by_cases hp : p = o.1
  · subst p
    by_cases hq : q = o.1
    · subst q
      refine (Fintype.sum_eq_single (thermalKrausRow D o.1 o.2.1 o.2.2) ?_).trans ?_
      · intro r hr
        simp [hr]
      · rw [if_pos ⟨rfl, rfl⟩, hsq, if_pos ⟨rfl, rfl⟩]
    · rw [Fintype.sum_eq_zero _ (fun r => by
          simp only [if_neg (fun h : q = o.1 ∧ r = _ => hq h.1), mul_zero]),
        if_neg (fun h => hq h.2)]
  · rw [Fintype.sum_eq_zero _ (fun r => by
        simp only [if_neg (fun h : p = o.1 ∧ r = _ => hp h.1), star_zero, zero_mul]),
      if_neg (fun h => hp h.1)]

theorem thermalKraus_complete (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    ∑ o : Fin D × Fin D × Bool, (thermalKraus D E β o)ᴴ*thermalKraus D E β o = 1 := by
  ext p q
  simp only [Matrix.sum_apply, thermalKraus_mul_conjTranspose_entry D hD E β]
  rw [Fintype.sum_prod_type]
  simp only [Prod.fst, Prod.snd]
  by_cases hpq : p = q
  · subst q
    have hsumb : ∀ j : Fin D, ∑ b : Bool,
        (thermalKrausWeight D E β p j b : ℂ) = ((1:ℝ)/(D:ℝ) : ℂ) := by
      intro j
      have hw : (thermalKrausWeight D E β p j true : ℂ)
          + (thermalKrausWeight D E β p j false : ℂ) = ((1:ℝ)/(D:ℝ) : ℂ) := by
        have hreal : thermalKrausWeight D E β p j true + thermalKrausWeight D E β p j false
            = (1:ℝ)/(D:ℝ) := by
          rw [show thermalKrausWeight D E β p j true = thermalAcceptance E β p j / (D : ℝ)
              from rfl,
            show thermalKrausWeight D E β p j false
              = (1 - thermalAcceptance E β p j) / (D : ℝ) from rfl,
            ← add_div]
          have hn : thermalAcceptance E β p j + (1 - thermalAcceptance E β p j) = 1 := by ring
          rw [hn]
        rw [← Complex.ofReal_add, hreal]
        push_cast
        norm_num
      rw [Fintype.sum_bool]
      exact hw
    have hsumi : ∑ j : Fin D, ((1:ℝ)/(D:ℝ) : ℂ) = 1 := by
      have h1 : ∑ j : Fin D, ((1:ℝ)/(D:ℝ) : ℂ)
          = ((D : ℕ) : ℂ) * ((1:ℝ)/(D:ℝ) : ℂ) := by
        simp [Finset.sum_const]
      rw [h1]
      have hne : ((D : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
      push_cast
      rw [one_div]
      exact mul_inv_cancel₀ hne
    have hsumy : ∑ y : Fin D × Bool, (thermalKrausWeight D E β p y.1 y.2 : ℂ) = 1 := by
      rw [Fintype.sum_prod_type]
      simp only [Prod.fst, Prod.snd]
      rw [Finset.sum_congr rfl fun j _ => hsumb j]
      exact hsumi
    have hR : (1 : Operator D) p p = 1 := by simp [Matrix.one_apply]
    refine (Fintype.sum_eq_single p ?_).trans ?_
    · intro i hi
      have hnp : ¬(p = i) := fun h => hi h.symm
      simp [hnp]
    · simp only [eq_self_iff_true, true_and, if_true]
      rw [hR]
      exact hsumy
  · have hzero : ∀ i : Fin D, (∑ y : Fin D × Bool,
        (if p = i ∧ q = i then (thermalKrausWeight D E β i y.1 y.2 : ℂ) else 0)) = 0 := by
      intro i
      have hnp : ¬(p = i ∧ q = i) := fun h => hpq (h.1.trans h.2.symm)
      simp [hnp]
    calc (∑ i : Fin D, ∑ y : Fin D × Bool,
          (if p = i ∧ q = i then (thermalKrausWeight D E β i y.1 y.2 : ℂ) else 0))
        = ∑ i : Fin D, (0 : ℂ) := Finset.sum_congr rfl fun i _ => hzero i
      _ = (0:ℂ) := by simp
      _ = (1 : Operator D) p q := by simp [Matrix.one_apply, hpq]

noncomputable def thermalInstrument (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    Instrument (Fin D × Fin D × Bool) D D :=
  Instrument.ofKraus (thermalKraus D E β) (thermalKraus_complete D hD E β)

@[simp] theorem thermalInstrument_branch (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (i j : Fin D) (b : Bool) (ρ : Operator D) :
    (thermalInstrument D hD E β).branch (i, j, b) ρ
      = thermalKraus D E β (i, j, b)*ρ*(thermalKraus D E β (i, j, b))ᴴ :=
  Instrument.ofKraus_branch _ _ _ _

variable (D : ℕ) (E : Fin D → ℝ) (β : ℝ)

def thermalDataLabel (D : ℕ) : Fin (D*2) → Fin D := fun k => (finProdFinEquiv.symm k).1

def thermalCoinLabel (D : ℕ) : Fin (D*2) → Fin 2 := fun k => (finProdFinEquiv.symm k).2

noncomputable def thermalCoinGate (D : ℕ) (a : ℝ) : Operator (D*2) :=
  (TensorGate (1 : Operator D) (MetropolisCoin a)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

noncomputable def thermalSwapGate (D : ℕ) (i j : Fin D) : Operator (D*2) :=
  (TensorGate (permMatrix (Equiv.swap i j)) (1 : Operator 2)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

noncomputable def thermalFeedbackGate (D : ℕ) (i j : Fin D) (b : Bool) : Operator (D*2) :=
  if b then thermalSwapGate D i j else 1

def thermalCoinIdx (b : Bool) : Fin 2 := if b then 1 else 0

def thermalDataSet (D : ℕ) (i : Fin D) : Finset (Fin (D*2)) :=
  Finset.univ.filter (fun k => (finProdFinEquiv.symm k).1 = i)

def thermalCoinSet (D : ℕ) (c : Fin 2) : Finset (Fin (D*2)) :=
  Finset.univ.filter (fun k => (finProdFinEquiv.symm k).2 = c)

noncomputable def thermalFeedbackStep (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j i : Fin D)
    (c : Fin 2) : ObservedCircuit (Fin (D*2)) :=
  .step (.gate (thermalFeedbackGate D i j (c = 1))) (.halt true)

noncomputable def thermalCoinMeasure (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j i : Fin D) :
    ObservedCircuit (Fin (D*2)) :=
  .measure 2 (thermalCoinLabel D) (fun c => thermalFeedbackStep D E β j i c)

noncomputable def thermalDataStep (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j i : Fin D) :
    ObservedCircuit (Fin (D*2)) :=
  .step (.gate (thermalCoinGate D (thermalAcceptance E β i j)))
    (thermalCoinMeasure D E β j i)

noncomputable def thermalProgram (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j : Fin D) :
    ObservedCircuit (Fin (D*2)) :=
  .measure D (thermalDataLabel D) (fun i => thermalDataStep D E β j i)

variable {D E β}

private theorem unitary_submatrix_equiv {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {A : Matrix I I ℂ} (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (e : I ≃ J) : (A.submatrix e.symm e.symm) ∈ Matrix.unitaryGroup J ℂ := by
  have he : Function.Bijective (e.symm : J → I) := e.symm.bijective
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have h2 : A.conjTranspose * A = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hA
    rwa [Matrix.star_eq_conjTranspose] at this
  have h1 : ((A.submatrix e.symm e.symm).conjTranspose * (A.submatrix e.symm e.symm))
      = ((A.conjTranspose * A).submatrix e.symm e.symm) := by
    rw [Matrix.conjTranspose_submatrix,
      ← Matrix.submatrix_mul _ _ e.symm e.symm e.symm he]
  have h3 : ((1 : Matrix I I ℂ).submatrix e.symm e.symm) = 1 := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.one_apply, e.symm.injective.eq_iff]
  rw [h1, h2, h3]

private theorem one_unitary (I : Type*) [Fintype I] [DecidableEq I] :
    (1 : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, conjTranspose_one, one_mul]

theorem thermalCoinGate_unitary (D : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    thermalCoinGate D a ∈ Matrix.unitaryGroup (Fin (D*2)) ℂ :=
  unitary_submatrix_equiv
    (tensorGate_unitary (one_unitary (Fin D))
      (metropolisCoin_unitary ha0 ha1)) finProdFinEquiv

theorem thermalSwapGate_unitary (D : ℕ) (i j : Fin D) :
    thermalSwapGate D i j ∈ Matrix.unitaryGroup (Fin (D*2)) ℂ :=
  unitary_submatrix_equiv
    (tensorGate_unitary (permMatrix_unitary (fun k => Equiv.swap_apply_self i j k))
      (one_unitary (Fin 2))) finProdFinEquiv

set_option maxHeartbeats 1000000 in

theorem thermalProgram_wellFormed (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j : Fin D) :
    observedWellFormed (thermalProgram D E β j) := by
  intro i
  refine ⟨thermalCoinGate_unitary D _ (thermalAcceptance_pos E β i j).le
    (thermalAcceptance_le_one E β i j), fun c => ?_⟩
  fin_cases c
  · exact ⟨one_unitary _, trivial⟩
  · exact ⟨thermalSwapGate_unitary D i j, trivial⟩

noncomputable def thermalHaltLeaf {D : ℕ} : ObservedKrausLeaf (D*2) :=
  { operator := 1, accepted := true, queries := 0, gates := 0, measurements := 0,
    outcomes := [] }

noncomputable def thermalFinalLeaf (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j i : Fin D)
    (c : Fin 2) : ObservedKrausLeaf (D*2) :=
  ObservedKrausLeaf.prepend (Projector (thermalDataSet D i)) 0 0 1 [(D, i.val)]
    (ObservedKrausLeaf.prepend (thermalCoinGate D (thermalAcceptance E β i j)) 0 1 0 []
      (ObservedKrausLeaf.prepend (Projector (thermalCoinSet D c)) 0 0 1 [(2, c.val)]
        (ObservedKrausLeaf.prepend (thermalFeedbackGate D i j (c = 1)) 0 1 0 []
          thermalHaltLeaf)))

theorem thermalProgram_leafCount (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j : Fin D) :
    observedLeafCount (thermalProgram D E β j) = D*2 := by
  unfold thermalProgram thermalDataStep thermalCoinMeasure thermalFeedbackStep
  simp only [observedLeafCount]
  simp

private theorem flatten_map_singleton {α : Type*} (l : List α) :
    List.flatten (List.map (fun a => [a]) l) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.flatten_cons, ih, List.singleton_append]

private theorem flatten_ofFn_two {α : Type*} (F : Fin 2 → α) :
    List.flatten (List.ofFn (fun c : Fin 2 => [F c])) = List.ofFn F := by
  rw [show (fun c : Fin 2 => [F c]) = (fun a => [a]) ∘ F from rfl,
    ← List.map_ofFn, flatten_map_singleton]

theorem observedKrausLeaves_thermalProgram (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j : Fin D) :
    observedKrausLeaves 1 (thermalProgram D E β j)
      = List.flatten (List.ofFn (fun i : Fin D =>
          List.ofFn (fun c : Fin 2 => thermalFinalLeaf D E β j i c))) := by
  have hinner : ∀ (o : Fin D) (c : Fin 2),
      List.map (ObservedKrausLeaf.prepend (Projector (thermalCoinSet D c)) 0 0 1 [(2, c.val)])
        (List.map (ObservedKrausLeaf.prepend (thermalFeedbackGate D o j (c = 1)) 0 1 0 [])
          [thermalHaltLeaf])
      = [ObservedKrausLeaf.prepend (Projector (thermalCoinSet D c)) 0 0 1 [(2, c.val)]
          (ObservedKrausLeaf.prepend (thermalFeedbackGate D o j (c = 1)) 0 1 0 []
            thermalHaltLeaf)] := by
    intro o c
    rfl
  have hblock : ∀ o : Fin D,
      List.map (ObservedKrausLeaf.prepend (thermalCoinGate D (thermalAcceptance E β o j))
          0 1 0 [])
        (List.flatten (List.ofFn (fun c : Fin 2 =>
          [ObservedKrausLeaf.prepend (Projector (thermalCoinSet D c)) 0 0 1 [(2, c.val)]
            (ObservedKrausLeaf.prepend (thermalFeedbackGate D o j (c = 1)) 0 1 0 []
              thermalHaltLeaf)])))
      = List.ofFn (fun c : Fin 2 =>
          ObservedKrausLeaf.prepend (thermalCoinGate D (thermalAcceptance E β o j)) 0 1 0 []
            (ObservedKrausLeaf.prepend (Projector (thermalCoinSet D c)) 0 0 1 [(2, c.val)]
              (ObservedKrausLeaf.prepend (thermalFeedbackGate D o j (c = 1)) 0 1 0 []
                thermalHaltLeaf))) := by
    intro o
    rw [flatten_ofFn_two
      (fun c : Fin 2 =>
        ObservedKrausLeaf.prepend (Projector (thermalCoinSet D c)) 0 0 1 [(2, c.val)]
          (ObservedKrausLeaf.prepend (thermalFeedbackGate D o j (c = 1)) 0 1 0 []
            thermalHaltLeaf))]
    rw [List.map_ofFn]
    rfl
  have hmapD : ∀ (U : Operator (D*2)) (q g m : ℕ) (outs : List (ℕ × ℕ))
      (F : Fin D → ObservedKrausLeaf (D*2)),
      List.map (ObservedKrausLeaf.prepend U q g m outs) (List.ofFn F)
        = List.ofFn (fun i => ObservedKrausLeaf.prepend U q g m outs (F i)) := by
    intro U q g m outs F
    rw [List.map_ofFn]
    rfl
  unfold thermalProgram thermalDataStep thermalCoinMeasure thermalFeedbackStep
  simp only [observedKrausLeaves, hinner, hblock, hmapD]
  rfl

private theorem getElem_index_eq {α : Type*} (l : List α) (k1 k2 : ℕ)
    (h1 : k1 < l.length) (h2 : k2 < l.length) (h : k1 = k2) :
    l[k1]'h1 = l[k2]'h2 := by
  subst h
  rfl

private theorem getElem_flatten_ofFn_two {α : Type*} : ∀ {D : ℕ} (g : Fin D → List α),
    ∀ hlen : (∀ i, (g i).length = 2), ∀ (i : Fin D) (c : Fin 2) (L : List α)
    (hL : L = List.flatten (List.ofFn g)) (k : ℕ)
    (hk : k < L.length) (hkval : k = 2*i.val + c.val),
    L[k]'hk = (g i)[c.val]'(by rw [hlen i]; omega) := by
  intro D
  induction D with
  | zero => intro g _ i; exact absurd i.isLt (Nat.not_lt_zero i.val)
  | succ D ih =>
    intro g hlen i c L hL k hk hkval
    revert hkval
    revert hk
    rw [hL, List.ofFn_succ, List.flatten_cons]
    intro hk hkval
    rcases Fin.eq_zero_or_eq_succ i with hi | ⟨i', hi⟩
    · subst i
      rw [Fin.val_zero] at hkval
      have hk0 : k = c.val := by omega
      subst hk0
      exact List.getElem_append_left (by rw [hlen 0]; exact c.isLt)
    · subst i
      have hsucc : 1 ≤ (i'.succ).val := by rw [Fin.val_succ]; omega
      rw [List.length_append, hlen 0] at hk
      rw [List.getElem_append_right (by rw [hlen 0]; omega)]
      subst hkval
      rw [Fin.val_succ] at hk
      refine Eq.trans ?_ (ih (fun i => g i.succ) (fun i => hlen i.succ) i' c _ rfl
        (2*i'.val + c.val) (by omega) rfl)
      exact getElem_index_eq _ _ _ _ (by omega)
        (show 2*((i'.succ : Fin (D+1)).val) + c.val - (g 0).length = 2*i'.val + c.val from by
          rw [hlen 0, Fin.val_succ]; omega)

noncomputable def thermalLeaf (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) (j i : Fin D)
    (b : Bool) : Fin (observedLeafCount (thermalProgram D E β j)) :=
  Fin.cast (thermalProgram_leafCount D E β j).symm
    (finProdFinEquiv (i, thermalCoinIdx b))

private theorem get_of_eq_list {α : Type*} {l l' : List α} (h : l = l') (i : Fin l.length) :
    l.get i = l'.get (Fin.cast (by rw [h]) i) := by
  subst h
  rfl

theorem observedLeaf_thermalLeaf (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (j i : Fin D) (b : Bool) :
    observedLeaf 1 (thermalProgram D E β j) (thermalLeaf D hD E β j i b)
      = thermalFinalLeaf D E β j i (thermalCoinIdx b) := by
  have hlen : ∀ i : Fin D,
      (List.ofFn (fun c : Fin 2 => thermalFinalLeaf D E β j i c)).length = 2 := by
    intro i
    simp
  have hlenall : (List.flatten (List.ofFn (fun i : Fin D =>
      List.ofFn (fun c : Fin 2 => thermalFinalLeaf D E β j i c)))).length = D*2 := by
    rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_apply]
    rw [Finset.sum_congr rfl (fun i _ => hlen i)]
    simp
  have key := getElem_flatten_ofFn_two (fun i : Fin D =>
    List.ofFn (fun c : Fin 2 => thermalFinalLeaf D E β j i c)) hlen i (thermalCoinIdx b)
    (List.flatten (List.ofFn (fun i : Fin D =>
      List.ofFn (fun c : Fin 2 => thermalFinalLeaf D E β j i c)))) rfl
    (2*i.val + (thermalCoinIdx b).val) (by rw [hlenall]; omega) rfl
  have hlast : (List.ofFn (fun c : Fin 2 => thermalFinalLeaf D E β j i c))[(thermalCoinIdx b).val]
      = thermalFinalLeaf D E β j i (thermalCoinIdx b) := by
    rw [List.getElem_ofFn]
  unfold observedLeaf thermalLeaf
  rw [get_of_eq_list (observedKrausLeaves_thermalProgram D E β j)]
  refine Eq.trans (congrArg (List.get _) (Fin.ext ?_)) (Eq.trans key hlast)
  show (thermalCoinIdx b).val + 2*i.val = 2*i.val + (thermalCoinIdx b).val
  omega

theorem thermalLeaf_bijective (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) (j : Fin D) :
    Function.Bijective (fun o : Fin D × Bool => thermalLeaf D hD E β j o.1 o.2) := by
  have hidx : Function.Bijective
      (fun o : Fin D × Bool => finProdFinEquiv (o.1, thermalCoinIdx o.2)) := by
    constructor
    · intro a b hab
      have hpair : (a.1, thermalCoinIdx a.2) = (b.1, thermalCoinIdx b.2) :=
        finProdFinEquiv.injective hab
      have h1 : a.1 = b.1 := by
        have := congrArg (fun p : Fin D × Fin 2 => p.1) hpair
        simpa using this
      have h2 : a.2 = b.2 := by
        have hpair2 : thermalCoinIdx a.2 = thermalCoinIdx b.2 :=
          congrArg (fun p : Fin D × Fin 2 => p.2) hpair
        revert hpair2
        unfold thermalCoinIdx
        cases a.2 <;> cases b.2 <;> simp_all
      exact Prod.ext h1 h2
    · intro k
      refine ⟨((finProdFinEquiv.symm k).1, decide ((finProdFinEquiv.symm k).2 = 1)), ?_⟩
      have hcoin : thermalCoinIdx (decide ((finProdFinEquiv.symm k).2 = 1))
          = (finProdFinEquiv.symm k).2 := by
        by_cases hc : (finProdFinEquiv.symm k).2 = 1
        · rw [hc]
          simp [thermalCoinIdx]
        · have hc0 : (finProdFinEquiv.symm k).2 = 0 := by
            have hlt : ((finProdFinEquiv.symm k).2).val < 2 :=
              (finProdFinEquiv.symm k).2.isLt
            have hne : ((finProdFinEquiv.symm k).2).val ≠ 1 := fun h => hc (Fin.ext h)
            omega
          rw [hc0]
          simp [thermalCoinIdx]
      show finProdFinEquiv ((finProdFinEquiv.symm k).1,
          thermalCoinIdx (decide ((finProdFinEquiv.symm k).2 = 1))) = k
      rw [hcoin]
      exact Equiv.apply_symm_apply finProdFinEquiv k
  have hcastbij : Function.Bijective
      (Fin.cast (thermalProgram_leafCount D E β j).symm :
        Fin (D*2) → Fin (observedLeafCount (thermalProgram D E β j))) := by
    constructor
    · intro a b hab
      exact Fin.val_injective (by simpa using congrArg Fin.val hab)
    · intro b
      exact ⟨Fin.cast (thermalProgram_leafCount D E β j) b, by simp⟩
  exact Function.Bijective.comp hcastbij hidx

noncomputable def thermalLeafOperator (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j i : Fin D)
    (b : Bool) : Operator (D*2) :=
  (thermalFinalLeaf D E β j i (thermalCoinIdx b)).operator

theorem thermalLeafOperator_eq (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j i : Fin D) (b : Bool) :
    thermalLeafOperator D E β j i b
      = thermalFeedbackGate D i j b * Projector (thermalCoinSet D (thermalCoinIdx b))
        * thermalCoinGate D (thermalAcceptance E β i j) * Projector (thermalDataSet D i) := by
  cases b <;>
    simp [thermalLeafOperator, thermalFinalLeaf, thermalHaltLeaf, ObservedKrausLeaf.prepend,
      one_mul, thermalCoinIdx, thermalFeedbackGate]

noncomputable def thermalEmbed (D : ℕ) : Operator D →ₗ[ℂ] Operator (D*2) where
  toFun ρ := (TensorGate ρ (outerProduct (Qatlib.Foundations.PureStateMath.Ket 0))).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm
  map_add' := by
    intro ρ σ
    ext k l
    rw [← Equiv.apply_symm_apply finProdFinEquiv k,
      ← Equiv.apply_symm_apply finProdFinEquiv l]
    simp [tensorGate_apply, add_mul]
  map_smul' := by
    intro c ρ
    ext k l
    rw [← Equiv.apply_symm_apply finProdFinEquiv k,
      ← Equiv.apply_symm_apply finProdFinEquiv l]
    simp [tensorGate_apply, mul_assoc]

noncomputable def thermalDiscard (D : ℕ) : Operator (D*2) →ₗ[ℂ] Operator D where
  toFun A x y := ∑ c : Fin 2, A (finProdFinEquiv (x, c)) (finProdFinEquiv (y, c))
  map_add' := by
    intro A B
    ext x y
    simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c A
    ext x y
    simp [Finset.mul_sum, RingHom.id_apply, add_mul, mul_add]

noncomputable def thermalActualBranch (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (j i : Fin D) (b : Bool) : Operator D →ₗ[ℂ] Operator D :=
  ((1/(D:ℝ) : ℂ)) • ((thermalDiscard D).comp
    ((conjBranch (thermalLeafOperator D E β j i b)).comp (thermalEmbed D)))

theorem thermalEmbed_apply (D : ℕ) (ρ : Operator D) (p q : Fin D × Fin 2) :
    thermalEmbed D ρ (finProdFinEquiv p) (finProdFinEquiv q)
      = if p.2 = 0 ∧ q.2 = 0 then ρ p.1 q.1 else 0 := by
  obtain ⟨a, c⟩ := p
  obtain ⟨b, c'⟩ := q
  simp only [thermalEmbed, LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, tensorGate_apply, outerProduct_apply]
  by_cases hp : c = 0 <;> by_cases hq : c' = 0 <;>
    simp [Qatlib.Foundations.PureStateMath.Ket, Matrix.of_apply, hp, hq, star_one, star_zero]

theorem thermalCoinGate_apply (D : ℕ) (a : ℝ) (p q : Fin D × Fin 2) :
    thermalCoinGate D a (finProdFinEquiv p) (finProdFinEquiv q)
      = if p.1 = q.1 then MetropolisCoin a p.2 q.2 else 0 := by
  obtain ⟨a₁, c⟩ := p
  obtain ⟨b₁, c'⟩ := q
  simp only [thermalCoinGate, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    tensorGate_apply]
  by_cases h : a₁ = b₁ <;>
    simp [h, Qatlib.Foundations.PureStateMath.Ket, Matrix.of_apply, mul_ite, mul_one,
        mul_zero, Matrix.one_apply]

theorem thermalDataProjector_apply (D : ℕ) (i : Fin D) (p q : Fin D × Fin 2) :
    Projector (thermalDataSet D i) (finProdFinEquiv p) (finProdFinEquiv q)
      = if p = q ∧ p.1 = i then (1:ℂ) else 0 := by
  simp only [Projector, Matrix.diagonal_apply, thermalDataSet, Finset.mem_filter,
    Finset.mem_univ]
  by_cases hpq : p = q <;> by_cases hp : p.1 = i <;>
    simp [hpq, hp, Equiv.symm_apply_apply]

theorem thermalCoinProjector_apply (D : ℕ) (c : Fin 2) (p q : Fin D × Fin 2) :
    Projector (thermalCoinSet D c) (finProdFinEquiv p) (finProdFinEquiv q)
      = if p = q ∧ p.2 = c then (1:ℂ) else 0 := by
  simp only [Projector, Matrix.diagonal_apply, thermalCoinSet, Finset.mem_filter,
    Finset.mem_univ]
  by_cases hpq : p = q <;> by_cases hp : p.2 = c <;>
    simp [hpq, hp, Equiv.symm_apply_apply]

private theorem coinGate_mul_dataProjector (D : ℕ) (a : ℝ) (i : Fin D)
    (p q : Fin D × Fin 2) :
    (thermalCoinGate D a * Projector (thermalDataSet D i)) (finProdFinEquiv p)
      (finProdFinEquiv q)
      = if p.1 = i ∧ q.1 = i then MetropolisCoin a p.2 q.2 else 0 := by
  rw [Matrix.mul_apply, ← Equiv.sum_comp finProdFinEquiv (fun k =>
    thermalCoinGate D a (finProdFinEquiv p) k
      * Projector (thermalDataSet D i) k (finProdFinEquiv q))]
  have hstep : ∀ w : Fin D × Fin 2,
      (if p.1 = w.1 then MetropolisCoin a p.2 w.2 else 0)
        * (if w = q ∧ w.1 = i then (1:ℂ) else 0)
      = if w = q ∧ p.1 = i ∧ q.1 = i then MetropolisCoin a p.2 q.2 else 0 := by
    intro w
    by_cases hw : w = q <;> by_cases hp : p.1 = i <;> by_cases hq : q.1 = i <;>
      simp [hw, hp, hq]
  simp only [thermalCoinGate_apply, thermalDataProjector_apply, hstep]
  by_cases hq : q.1 = i
  · rw [Fintype.sum_eq_single q]
    · simp [hq]
    · intro w hw
      rw [if_neg (fun h => hw h.1)]
  · have hz : ∀ w : Fin D × Fin 2,
        (if w = q ∧ p.1 = i ∧ q.1 = i then MetropolisCoin a p.2 q.2 else 0) = 0 := by
      intro w
      by_cases hw : w = q <;> simp [hw, hq]
    rw [Finset.sum_congr rfl (fun w _ => hz w)]
    simp [hq]

private theorem coinProjector_mul (D : ℕ) (c : Fin 2) (X : Operator (D*2))
    (p q : Fin D × Fin 2) :
    (Projector (thermalCoinSet D c) * X) (finProdFinEquiv p) (finProdFinEquiv q)
      = if p.2 = c then X (finProdFinEquiv p) (finProdFinEquiv q) else 0 := by
  rw [Matrix.mul_apply, ← Equiv.sum_comp finProdFinEquiv (fun k =>
    Projector (thermalCoinSet D c) (finProdFinEquiv p) k * X k (finProdFinEquiv q))]
  have hstep : ∀ w : Fin D × Fin 2,
      (if p = w ∧ p.2 = c then (1:ℂ) else 0) * X (finProdFinEquiv w) (finProdFinEquiv q)
      = if p = w ∧ p.2 = c then X (finProdFinEquiv w) (finProdFinEquiv q) else 0 := by
    intro w
    by_cases hwp : p = w
    · by_cases hp : p.2 = c <;> simp [hwp, hp]
    · rw [if_neg (fun h => hwp h.1), if_neg (fun h => hwp h.1), zero_mul]
  simp only [thermalCoinProjector_apply, hstep]
  by_cases hp : p.2 = c
  · rw [Fintype.sum_eq_single p]
    · simp [hp]
    · intro w hw
      rw [if_neg (fun h => hw h.1.symm)]
  · have hz : ∀ w : Fin D × Fin 2,
        (if p = w ∧ p.2 = c then X (finProdFinEquiv w) (finProdFinEquiv q) else 0) = 0 := by
      intro w
      rw [if_neg (fun h => hp h.2)]
    rw [Finset.sum_congr rfl (fun w _ => hz w)]
    simp [hp]

def thermalDataMap (D : ℕ) (i j : Fin D) (b : Bool) (x : Fin D) : Fin D :=
  if b then Equiv.swap i j x else x

theorem thermalDataMap_self (D : ℕ) (i j : Fin D) (b : Bool) (x : Fin D) :
    thermalDataMap D i j b (thermalDataMap D i j b x) = x := by
  by_cases hb : b <;> simp [thermalDataMap, hb, Equiv.swap_apply_self]

theorem thermalDataMap_eq_iff (D : ℕ) (i j : Fin D) (b : Bool) (x : Fin D) :
    thermalDataMap D i j b x = i ↔ x = thermalKrausRow D i j b := by
  cases b
  · simp only [thermalDataMap, thermalKrausRow, if_neg (by simp : ¬(false = true))]
  · simp only [thermalDataMap, thermalKrausRow, if_true]
    constructor
    · intro h
      rw [← Equiv.swap_apply_self i j x, h]
      exact Equiv.swap_apply_left i j
    · intro h
      rw [h]
      exact Equiv.swap_apply_right i j

private theorem feedbackGate_mul (D : ℕ) (i j : Fin D) (b : Bool) (X : Operator (D*2))
    (p q : Fin D × Fin 2) :
    (thermalFeedbackGate D i j b * X) (finProdFinEquiv p) (finProdFinEquiv q)
      = X (finProdFinEquiv (thermalDataMap D i j b p.1, p.2)) (finProdFinEquiv q) := by
  cases b
  · rw [thermalFeedbackGate, if_neg (by simp), one_mul, thermalDataMap]
    rfl
  · rw [show thermalFeedbackGate D i j true = thermalSwapGate D i j from rfl]
    rw [Matrix.mul_apply, ← Equiv.sum_comp finProdFinEquiv (fun k =>
        thermalSwapGate D i j (finProdFinEquiv p) k * X k (finProdFinEquiv q))]
    have hentry : ∀ w : Fin D × Fin 2,
        thermalSwapGate D i j (finProdFinEquiv p) (finProdFinEquiv w)
          = if p.1 = Equiv.swap i j w.1 ∧ p.2 = w.2 then (1:ℂ) else 0 := by
      intro w
      obtain ⟨u, cu⟩ := p
      obtain ⟨v, cw⟩ := w
      simp only [thermalSwapGate, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        tensorGate_apply]
      by_cases h1 : u = Equiv.swap i j v <;> by_cases h2 : cu = cw <;>
        simp [h1, h2, permMatrix, Matrix.of_apply, Matrix.one_apply]
    rw [Fintype.sum_eq_single (Equiv.swap i j p.1, p.2)]
    · simp only [hentry]
      rw [if_pos ⟨(Equiv.swap_apply_self i j p.1).symm, trivial⟩, one_mul]
      rfl
    · intro w hw
      rw [hentry w]
      by_cases h1 : p.1 = Equiv.swap i j w.1
      · by_cases h2 : p.2 = w.2
        · refine absurd ?_ hw
          refine Prod.ext ?_ h2.symm
          show w.1 = Equiv.swap i j p.1
          rw [h1]
          exact (Equiv.swap_apply_self i j w.1).symm
        · rw [if_neg (fun h => h2 h.2)]
          simp
      · rw [if_neg (fun h => h1 h.1)]
        simp

theorem thermalLeafOperator_apply (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j i : Fin D) (b : Bool)
    (p q : Fin D × Fin 2) :
    thermalLeafOperator D E β j i b (finProdFinEquiv p) (finProdFinEquiv q)
      = if p = (thermalKrausRow D i j b, thermalCoinIdx b) ∧ q.1 = i then
          MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) q.2 else 0 := by
  rw [thermalLeafOperator_eq, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [feedbackGate_mul]
  rw [coinProjector_mul]
  have hmid : (thermalCoinGate D (thermalAcceptance E β i j)
      * Projector (thermalDataSet D i)) (finProdFinEquiv (thermalDataMap D i j b p.1, p.2))
      (finProdFinEquiv q)
      = if thermalDataMap D i j b p.1 = i ∧ q.1 = i then
          MetropolisCoin (thermalAcceptance E β i j) p.2 q.2 else 0 :=
    coinGate_mul_dataProjector D _ i _ q
  rw [hmid]
  by_cases hp : p = (thermalKrausRow D i j b, thermalCoinIdx b)
  · have hp2 : p.2 = thermalCoinIdx b := by rw [hp]
    have hrow : thermalDataMap D i j b p.1 = i :=
      (thermalDataMap_eq_iff D i j b p.1).mpr (congrArg (fun r => r.1) hp)
    by_cases hi : q.1 = i
    · rw [if_pos hp2, if_pos ⟨hrow, hi⟩, if_pos ⟨hp, hi⟩, hp2]
    · rw [if_pos hp2, if_neg (fun h => hi h.2), if_neg (fun h => hi h.2)]
  · have hdm : ¬(p.2 = thermalCoinIdx b ∧ thermalDataMap D i j b p.1 = i) := by
      intro h
      exact hp (Prod.ext ((thermalDataMap_eq_iff D i j b p.1).mp h.2) h.1)
    by_cases hp2 : p.2 = thermalCoinIdx b
    · have hneg : ¬(thermalDataMap D i j b p.1 = i ∧ q.1 = i) := by
        intro h
        exact hdm ⟨hp2, h.1⟩
      rw [if_pos hp2, if_neg hneg, if_neg (fun h => hp h.1)]
    · rw [if_neg hp2, if_neg (fun h => hp h.1)]

private theorem metropolisCoin_00 (a : ℝ) :
    MetropolisCoin a 0 0 = ((Real.sqrt (1-a) : ℝ) : ℂ) := rfl

private theorem metropolisCoin_10 (a : ℝ) :
    MetropolisCoin a 1 0 = ((Real.sqrt a : ℝ) : ℂ) := rfl

private theorem metropolisCoin_sq (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (b : Bool) :
    MetropolisCoin a (thermalCoinIdx b) 0 * (starRingEnd ℂ)
      (MetropolisCoin a (thermalCoinIdx b) 0)
      = if b then (a : ℂ) else ((1 - a) : ℂ) := by
  have hconj : ∀ x : ℝ, (starRingEnd ℂ) ((Real.sqrt x : ℝ) : ℂ)
      = ((Real.sqrt x : ℝ) : ℂ) := fun x => by simp
  cases b
  · show MetropolisCoin a 0 0 * (starRingEnd ℂ) (MetropolisCoin a 0 0) = ((1 - a) : ℂ)
    rw [metropolisCoin_00, hconj, ← Complex.ofReal_mul, ← sq,
      Real.sq_sqrt (by linarith)]
    push_cast
    ring
  · show MetropolisCoin a 1 0 * (starRingEnd ℂ) (MetropolisCoin a 1 0) = (a : ℂ)
    rw [metropolisCoin_10, hconj, ← Complex.ofReal_mul, ← sq, Real.sq_sqrt ha]

private theorem leafOp_mul_embed (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j i : Fin D) (b : Bool)
    (ρ : Operator D) (u w' : Fin D × Fin 2) :
    (thermalLeafOperator D E β j i b * thermalEmbed D ρ) (finProdFinEquiv u)
      (finProdFinEquiv w')
      = if u = (thermalKrausRow D i j b, thermalCoinIdx b) ∧ w'.2 = 0 then
          MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) 0 * ρ i w'.1
        else 0 := by
  rw [Matrix.mul_apply, ← Equiv.sum_comp finProdFinEquiv (fun k =>
    thermalLeafOperator D E β j i b (finProdFinEquiv u) k
      * thermalEmbed D ρ k (finProdFinEquiv w'))]
  simp only [thermalLeafOperator_apply, thermalEmbed_apply]
  have hstep : ∀ w : Fin D × Fin 2,
      (if u = (thermalKrausRow D i j b, thermalCoinIdx b) ∧ w.1 = i then
          MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) w.2 else 0)
        * (if w.2 = 0 ∧ w'.2 = 0 then ρ w.1 w'.1 else 0)
      = if u = (thermalKrausRow D i j b, thermalCoinIdx b) ∧ w = (i, 0) ∧ w'.2 = 0 then
          MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) 0 * ρ i w'.1
        else 0 := by
    intro w
    by_cases hu : u = (thermalKrausRow D i j b, thermalCoinIdx b) <;>
      by_cases hw1 : w.1 = i <;>
        by_cases hw2 : w.2 = 0 <;>
          by_cases hw'2 : w'.2 = 0 <;>
            simp_all [show w = (i, 0) ↔ w.1 = i ∧ w.2 = 0 from Prod.ext_iff]
  simp only [hstep]
  by_cases hu : u = (thermalKrausRow D i j b, thermalCoinIdx b)
  · refine (Fintype.sum_eq_single (i, 0) ?_).trans ?_
    · intro w hw
      simp [hw]
    · by_cases hw'2 : w'.2 = 0 <;> simp [hu]
  · have hz : ∀ w : Fin D × Fin 2,
        (if u = (thermalKrausRow D i j b, thermalCoinIdx b) ∧ w = (i, 0) ∧ w'.2 = 0 then
          MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) 0 * ρ i w'.1
        else 0) = 0 := fun w => if_neg (fun h => hu h.1)
    rw [Finset.sum_congr rfl (fun w _ => hz w), if_neg (fun h => hu h.1)]
    simp

private theorem leafOp_sandwich (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (j i : Fin D) (b : Bool)
    (ρ : Operator D) (u v : Fin D × Fin 2) :
    (thermalLeafOperator D E β j i b * thermalEmbed D ρ
      * (thermalLeafOperator D E β j i b)ᴴ) (finProdFinEquiv u) (finProdFinEquiv v)
      = if u = (thermalKrausRow D i j b, thermalCoinIdx b)
            ∧ v = (thermalKrausRow D i j b, thermalCoinIdx b) then
          MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) 0
            * (starRingEnd ℂ) (MetropolisCoin (thermalAcceptance E β i j)
                (thermalCoinIdx b) 0) * ρ i i
        else 0 := by
  rw [Matrix.mul_apply, ← Equiv.sum_comp finProdFinEquiv (fun k =>
    (thermalLeafOperator D E β j i b * thermalEmbed D ρ) (finProdFinEquiv u) k
      * (thermalLeafOperator D E β j i b)ᴴ k (finProdFinEquiv v))]
  simp only [leafOp_mul_embed, Matrix.conjTranspose_apply, thermalLeafOperator_apply]
  have hstep : ∀ w' : Fin D × Fin 2,
      (if u = (thermalKrausRow D i j b, thermalCoinIdx b) ∧ w'.2 = 0 then
          MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) 0 * ρ i w'.1
        else 0)
        * star
            (if v = (thermalKrausRow D i j b, thermalCoinIdx b) ∧ w'.1 = i then
              MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) w'.2 else 0)
      = if u = (thermalKrausRow D i j b, thermalCoinIdx b)
            ∧ v = (thermalKrausRow D i j b, thermalCoinIdx b) ∧ w' = (i, 0) then
          MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) 0
            * (starRingEnd ℂ) (MetropolisCoin (thermalAcceptance E β i j)
                (thermalCoinIdx b) 0) * ρ i i
        else 0 := by
    intro w'
    by_cases hu : u = (thermalKrausRow D i j b, thermalCoinIdx b) <;>
      by_cases hv : v = (thermalKrausRow D i j b, thermalCoinIdx b) <;>
        by_cases hw'2 : w'.2 = 0 <;>
          by_cases hw'1 : w'.1 = i <;>
            (simp_all [show w' = (i, 0) ↔ w'.1 = i ∧ w'.2 = 0 from Prod.ext_iff];
              try ring)
  simp only [hstep]
  by_cases huv : u = (thermalKrausRow D i j b, thermalCoinIdx b)
      ∧ v = (thermalKrausRow D i j b, thermalCoinIdx b)
  · refine (Fintype.sum_eq_single (i, 0) ?_).trans ?_
    · intro w' hw'
      simp [hw']
    · simp [huv]
  · have hz : ∀ w' : Fin D × Fin 2,
        (if u = (thermalKrausRow D i j b, thermalCoinIdx b)
            ∧ v = (thermalKrausRow D i j b, thermalCoinIdx b) ∧ w' = (i, 0) then
          MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) 0
            * (starRingEnd ℂ) (MetropolisCoin (thermalAcceptance E β i j)
                (thermalCoinIdx b) 0) * ρ i i
        else 0) = 0 := fun w' => if_neg (fun h => huv ⟨h.1, h.2.1⟩)
    rw [Finset.sum_congr rfl (fun w' _ => hz w'), if_neg huv]
    simp

theorem thermalActualBranch_apply (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (j i : Fin D) (b : Bool) (ρ : Operator D) (x y : Fin D) :
    thermalActualBranch D hD E β j i b ρ x y
      = (thermalKrausWeight D E β i j b : ℂ) * ρ i i *
        (if x = thermalKrausRow D i j b ∧ y = thermalKrausRow D i j b then (1:ℂ) else 0) := by
  have hcoin := metropolisCoin_sq (thermalAcceptance E β i j)
    (thermalAcceptance_pos E β i j).le (thermalAcceptance_le_one E β i j) b
  show ((1/(D:ℝ) : ℂ)) * (∑ c : Fin 2,
      (thermalLeafOperator D E β j i b * thermalEmbed D ρ
        * (thermalLeafOperator D E β j i b)ᴴ) (finProdFinEquiv (x, c))
        (finProdFinEquiv (y, c))) = _
  have hentry : ∀ c : Fin 2,
      (thermalLeafOperator D E β j i b * thermalEmbed D ρ
        * (thermalLeafOperator D E β j i b)ᴴ) (finProdFinEquiv (x, c))
        (finProdFinEquiv (y, c))
      = if x = thermalKrausRow D i j b ∧ y = thermalKrausRow D i j b
            ∧ c = thermalCoinIdx b then
          MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) 0
            * (starRingEnd ℂ) (MetropolisCoin (thermalAcceptance E β i j)
                (thermalCoinIdx b) 0) * ρ i i
        else 0 := by
    intro c
    rw [leafOp_sandwich]
    by_cases hx : x = thermalKrausRow D i j b
    · by_cases hy : y = thermalKrausRow D i j b
      · by_cases hc : c = thermalCoinIdx b <;> simp [hx, hy, hc]
      · simp [hy]
    · simp [hx]
  rw [Finset.sum_congr rfl (fun c _ => hentry c)]
  by_cases hx : x = thermalKrausRow D i j b ∧ y = thermalKrausRow D i j b
  · have hsingle : ∑ c : Fin 2,
        (if x = thermalKrausRow D i j b ∧ y = thermalKrausRow D i j b
            ∧ c = thermalCoinIdx b then
          MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) 0
            * (starRingEnd ℂ) (MetropolisCoin (thermalAcceptance E β i j)
                (thermalCoinIdx b) 0) * ρ i i
          else 0)
      = MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) 0
          * (starRingEnd ℂ) (MetropolisCoin (thermalAcceptance E β i j)
              (thermalCoinIdx b) 0) * ρ i i := by
      refine (Fintype.sum_eq_single (thermalCoinIdx b) ?_).trans ?_
      · intro c hc
        simp [hc]
      · simp [hx]
    rw [hsingle, hcoin, if_pos hx]
    rw [thermalKrausWeight]
    have hDne : ((D:ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    cases b <;>
      · simp only [eq_self_iff_true, if_true, Bool.false_eq_true, if_false,
          Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]
        field_simp
        try ring
  · have hzero : ∑ c : Fin 2,
        (if x = thermalKrausRow D i j b ∧ y = thermalKrausRow D i j b
            ∧ c = thermalCoinIdx b then
          MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) 0
            * (starRingEnd ℂ) (MetropolisCoin (thermalAcceptance E β i j)
                (thermalCoinIdx b) 0) * ρ i i
          else 0) = 0 := by
      have hz : ∀ c : Fin 2,
          (if x = thermalKrausRow D i j b ∧ y = thermalKrausRow D i j b
              ∧ c = thermalCoinIdx b then
            MetropolisCoin (thermalAcceptance E β i j) (thermalCoinIdx b) 0
              * (starRingEnd ℂ) (MetropolisCoin (thermalAcceptance E β i j)
                  (thermalCoinIdx b) 0) * ρ i i
          else 0) = 0 := fun c => if_neg (fun h => hx ⟨h.1, h.2.1⟩)
      rw [Finset.sum_congr rfl (fun c _ => hz c)]
      simp
    rw [hzero, if_neg hx]
    simp

noncomputable def thermalPowerChannel (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (n : ℕ) : QuantumChannel D D :=
  match n with
  | 0 => QuantumChannel.id D
  | n + 1 => (thermalPowerChannel D hD E β n).comp (thermalInstrument D hD E β).forget

private theorem hreal' (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) (b : Bool) :
    star ((Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ))
      = ((Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ)) := by simp

private theorem hsqr' (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) (b : Bool) :
    (Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ)
      * (Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ)
      = (thermalKrausWeight D E β i j b : ℂ) := by
  rw [← Complex.ofReal_mul, ← sq,
    Real.sq_sqrt (thermalKrausWeight_nonneg D hD E β i j b)]

private theorem thermalKraus_conj_entry (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (i j : Fin D) (b : Bool) (ρ : Operator D) (x y : Fin D) :
    (thermalKraus D E β (i, j, b)*ρ*(thermalKraus D E β (i, j, b))ᴴ) x y
      = (thermalKrausWeight D E β i j b : ℂ) * ρ i i *
        (if x = thermalKrausRow D i j b ∧ y = thermalKrausRow D i j b then (1:ℂ) else 0) := by
  have hq := hsqr' D hD E β i j b
  have hr := hreal' D hD E β i j b
  have hkr : ∀ (x r : Fin D), (thermalKraus D E β (i, j, b) * ρ) x r
      = if x = thermalKrausRow D i j b then
          (Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ) * ρ i r else 0 := by
    intro x r
    simp only [Matrix.mul_apply, thermalKraus_apply]
    by_cases hx : x = thermalKrausRow D i j b
    · have hsingle : (if i = i ∧ x = thermalKrausRow D i j b then
          (Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ) else 0) * ρ i r
          = (Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ) * ρ i r := by
        rw [if_pos ⟨rfl, hx⟩]
      refine Eq.trans (Fintype.sum_eq_single i ?_) ?_
      · intro s hs
        rw [if_neg (fun h => hs h.1)]
        simp
      · rw [hsingle, if_pos hx]
    · have hz : ∀ s : Fin D, (if s = i ∧ x = thermalKrausRow D i j b then
          (Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ) else 0) * ρ s r = 0 :=
        fun s => by
          rw [show (if s = i ∧ x = thermalKrausRow D i j b then
              (Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ) else 0) = 0 from
            if_neg (fun h => hx h.2)]
          rw [zero_mul]
      rw [if_neg hx]
      rw [Finset.sum_congr rfl (fun s _ => hz s)]
      simp
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hkr, thermalKraus_apply]
  by_cases hx : x = thermalKrausRow D i j b
  · simp only [if_pos hx]
    by_cases hy : y = thermalKrausRow D i j b
    · have hterm : ∀ r : Fin D,
          ((Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ) * ρ i r)
            * star ((if r = i ∧ y = thermalKrausRow D i j b then
              (Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ) else 0))
          = if r = i then (thermalKrausWeight D E β i j b : ℂ) * ρ i i else 0 := by
        intro r
        by_cases hrn : r = i
        · rw [hrn, if_pos ⟨rfl, hy⟩, hr, if_pos rfl]
          linear_combination hq * ρ i i
        · rw [if_neg (fun h => hrn h.1), star_zero, mul_zero, if_neg hrn]
      simp only [hterm]
      refine (Fintype.sum_eq_single i ?_).trans ?_
      · intro r hrn
        rw [if_neg hrn]
      · rw [if_pos rfl, if_pos ⟨hx, hy⟩, mul_one]
    · have hterm : ∀ r : Fin D,
          ((Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ) * ρ i r)
            * star ((if r = i ∧ y = thermalKrausRow D i j b then
              (Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ) else 0)) = 0 := by
        intro r
        by_cases hrn : r = i
        · rw [if_neg (fun h => hy h.2), star_zero, mul_zero]
        · rw [if_neg (fun h => hrn h.1), star_zero, mul_zero]
      simp only [hterm]
      rw [Finset.sum_const_zero, if_neg (fun h => hy h.2), mul_zero]
  · have hterm : ∀ r : Fin D,
        ((if x = thermalKrausRow D i j b then
          (Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ) * ρ i r else 0))
          * star ((if r = i ∧ y = thermalKrausRow D i j b then
            (Real.sqrt (thermalKrausWeight D E β i j b : ℝ) : ℂ) else 0)) = 0 := by
      intro r
      simp [hx]
    simp only [hterm]
    rw [Finset.sum_const_zero, if_neg (fun h => hx h.1), mul_zero]

theorem measured_metropolis_kraus_and_actual_branch (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ)
    (β : ℝ) :
    (∑ o : Fin D × Fin D × Bool, (thermalKraus D E β o)ᴴ*thermalKraus D E β o)=1 ∧
    (∀ (i j : Fin D) (b : Bool) (ρ : Operator D),
      (thermalInstrument D hD E β).branch (i,j,b) ρ =
        thermalKraus D E β (i,j,b)*ρ*(thermalKraus D E β (i,j,b))ᴴ ∧
      thermalActualBranch D hD E β j i b ρ = (thermalInstrument D hD E β).branch (i,j,b) ρ) := by
  refine ⟨thermalKraus_complete D hD E β,
      fun i j b ρ => ⟨thermalInstrument_branch D hD E β i j b ρ, ?_⟩⟩
  ext x y
  rw [thermalActualBranch_apply D hD E β j i b ρ x y,
    thermalInstrument_branch D hD E β i j b ρ,
    thermalKraus_conj_entry D hD E β i j b ρ x y]

theorem measured_metropolis_leaf_resources (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (j : Fin D) :
    observedWellFormed (thermalProgram D E β j) ∧
    observedLeafCount (thermalProgram D E β j)=D*2 ∧
    Function.Bijective (fun o : Fin D × Bool => thermalLeaf D hD E β j o.1 o.2) ∧
    (∀ (i : Fin D) (b : Bool),
      let l := observedLeaf 1 (thermalProgram D E β j) (thermalLeaf D hD E β j i b)
      l.accepted=true ∧ l.queries=0 ∧ l.gates=2 ∧ l.measurements=2) := by
  refine ⟨thermalProgram_wellFormed D E β j, thermalProgram_leafCount D E β j,
    thermalLeaf_bijective D hD E β j, fun i b => ?_⟩
  rw [observedLeaf_thermalLeaf D hD E β j i b]
  unfold thermalFinalLeaf ObservedKrausLeaf.prepend thermalHaltLeaf
  simp

private theorem thermalAcceptance_self {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (p : Fin D) :
    thermalAcceptance E β p p = 1 := by
  simp [thermalAcceptance]

private theorem sum_one_div (D : ℕ) (hD : 0 < D) :
    ∑ j : Fin D, ((1:ℝ)/(D:ℝ) : ℂ) = 1 := by
  have h : ∑ j : Fin D, ((1:ℝ)/(D:ℝ)) = 1 := by
    have hc : ∑ j : Fin D, ((1:ℝ)/(D:ℝ)) = ((D:ℕ) : ℝ) * ((1:ℝ)/(D:ℝ)) := by
      simp [Finset.sum_const]
    rw [hc]
    field_simp
  exact_mod_cast h

private theorem sum_one_sub (D : ℕ) (hD : 0 < D) (a : Fin D → ℝ) :
    ∑ j : Fin D, ((1 - a j) / (D:ℝ) : ℂ)
      = 1 - ∑ j : Fin D, (a j / (D:ℝ) : ℂ) := by
  have hone := sum_one_div D hD
  have hsum1 : ∑ j : Fin D, ((1 - a j) / (D:ℝ) : ℂ)
      = ∑ j : Fin D, ((1:ℝ)/(D:ℝ) : ℂ) - ∑ j : Fin D, (a j / (D:ℝ) : ℂ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [sub_div]
      push_cast
      ring
  rw [hsum1, hone]

private theorem forget_diag_sum (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (ρ : Operator D) (x : Fin D) :
    (∑ i : Fin D, (thermalAcceptance E β i x / (D:ℝ) : ℂ) * ρ i i)
      + (1 - ∑ j : Fin D, (thermalAcceptance E β x j / (D:ℝ) : ℂ)) * ρ x x
    = ∑ i : Fin D, (thermalKernel D E β i x : ℂ) * ρ i i := by
  have hself := thermalAcceptance_self E β x
  have hsplit : ∀ (f : Fin D → ℂ),
      f x + ∑ i ∈ Finset.univ.erase x, f i = ∑ i : Fin D, f i := by
    intro f
    rw [show Finset.univ = insert x (Finset.univ.erase x) from
        (Finset.insert_erase (Finset.mem_univ x)).symm,
      Finset.sum_insert (Finset.notMem_erase x Finset.univ),
      Finset.erase_insert (Finset.notMem_erase x Finset.univ)]
  have hkdiag : (thermalKernel D E β x x : ℂ)
      = 1 - ∑ j' ∈ Finset.univ.erase x, (thermalAcceptance E β x j' / (D:ℝ) : ℂ) := by
    show (Complex.ofReal (if x = x then 1 - ∑ j' ∈ Finset.univ.erase x,
          thermalAcceptance E β x j' / (D:ℝ)
        else thermalAcceptance E β x x / (D:ℝ))) = _
    rw [if_pos rfl, Complex.ofReal_sub, Complex.ofReal_one]
    have hsumpush : ∀ (s : Finset (Fin D)) (g : Fin D → ℝ),
        ((∑ j' ∈ s, g j' : ℝ) : ℂ) = ∑ j' ∈ s, ((g j' : ℝ) : ℂ) := by
      intro s g
      push_cast
      rfl
    rw [hsumpush]
    refine congrArg (fun t => (1:ℂ) - t) ?_
    exact Finset.sum_congr rfl fun j' _ => by
      push_cast
      ring
  have hkoff : ∀ i ∈ Finset.univ.erase x,
      (thermalKernel D E β i x : ℂ) = thermalAcceptance E β i x / (D:ℝ) := by
    intro i hi
    show (Complex.ofReal (if i = x then 1 - ∑ j' ∈ Finset.univ.erase i,
          thermalAcceptance E β i j' / (D:ℝ)
        else thermalAcceptance E β i x / (D:ℝ))) = _
    rw [if_neg (Finset.ne_of_mem_erase hi), Complex.ofReal_div]
  have hR : ∑ i : Fin D, (thermalKernel D E β i x : ℂ) * ρ i i
      = (1 - ∑ j' ∈ Finset.univ.erase x, (thermalAcceptance E β x j' / (D:ℝ) : ℂ))
          * ρ x x
        + ∑ i ∈ Finset.univ.erase x, (thermalAcceptance E β i x / (D:ℝ) : ℂ) * ρ i i := by
    have hfull : ∑ i : Fin D, (thermalKernel D E β i x : ℂ) * ρ i i
        = (thermalKernel D E β x x : ℂ) * ρ x x
          + ∑ i ∈ Finset.univ.erase x, (thermalKernel D E β i x : ℂ) * ρ i i := by
      rw [show (Finset.univ : Finset (Fin D)) = insert x (Finset.univ.erase x) from
        (Finset.insert_erase (Finset.mem_univ x)).symm,
        Finset.sum_insert (Finset.notMem_erase x Finset.univ),
        Finset.erase_insert (Finset.notMem_erase x Finset.univ)]
    rw [hfull, hkdiag]
    refine congrArg (fun t => (1 - ∑ j' ∈ Finset.univ.erase x,
        (thermalAcceptance E β x j' / (D:ℝ) : ℂ)) * ρ x x + t) ?_
    exact Finset.sum_congr rfl (fun i hi => by rw [hkoff i hi])
  have hS : (thermalAcceptance E β x x / (D:ℝ) : ℂ)
      + ∑ j' ∈ Finset.univ.erase x, (thermalAcceptance E β x j' / (D:ℝ) : ℂ)
      = ∑ j : Fin D, (thermalAcceptance E β x j / (D:ℝ) : ℂ) :=
    hsplit (fun j => (thermalAcceptance E β x j / (D:ℝ) : ℂ))
  have hT : (thermalAcceptance E β x x / (D:ℝ) : ℂ) * ρ x x
      + ∑ i ∈ Finset.univ.erase x, (thermalAcceptance E β i x / (D:ℝ) : ℂ) * ρ i i
      = ∑ i : Fin D, (thermalAcceptance E β i x / (D:ℝ) : ℂ) * ρ i i :=
    hsplit (fun i => (thermalAcceptance E β i x / (D:ℝ) : ℂ) * ρ i i)
  rw [hR, ← hS, ← hT]
  rw [show (thermalAcceptance E β x x / (D:ℝ) : ℂ) = ((1:ℝ)/(D:ℝ) : ℂ) from by
    rw [hself]]
  ring

theorem thermalInstrument_forget_apply (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (ρ : Operator D) :
    (thermalInstrument D hD E β).forget.map ρ
      = Matrix.diagonal (fun j : Fin D => ∑ i : Fin D,
          (thermalKernel D E β i j : ℂ)*ρ i i) := by
  ext x y
  have hinner : ∀ i : Fin D, ∑ y' : Fin D × Bool,
      (((thermalInstrument D hD E β).branch (i, y')) ρ x y)
      = ∑ j : Fin D, ∑ b : Bool,
          (((thermalInstrument D hD E β).branch (i, j, b)) ρ x y) := fun i =>
    Fintype.sum_prod_type (fun p : Fin D × Bool =>
      ((thermalInstrument D hD E β).branch (i, p)) ρ x y)
  have hentry : ∀ (i j : Fin D) (b : Bool),
      ((thermalInstrument D hD E β).branch (i, j, b)) ρ x y
      = (thermalKrausWeight D E β i j b : ℂ) * ρ i i *
        (if x = thermalKrausRow D i j b ∧ y = thermalKrausRow D i j b then (1:ℂ) else 0) := by
    intro i j b
    rw [thermalInstrument_branch D hD E β i j b ρ,
      thermalKraus_conj_entry D hD E β i j b ρ x y]
  rw [Instrument.forget_apply, Matrix.sum_apply, Fintype.sum_prod_type,
    Finset.sum_congr rfl (fun i _ => hinner i),
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun b _ => hentry i j b)))]
  simp only [Fintype.sum_bool]
  by_cases hxy : x = y
  · subst y
    rw [Matrix.diagonal_apply, if_pos rfl]
    have hsumb : ∀ i j : Fin D,
        ((thermalKrausWeight D E β i j true : ℂ) * ρ i i
            * (if x = thermalKrausRow D i j true ∧ x = thermalKrausRow D i j true then
              (1:ℂ) else 0))
          + ((thermalKrausWeight D E β i j false : ℂ) * ρ i i
            * (if x = thermalKrausRow D i j false ∧ x = thermalKrausRow D i j false then
              (1:ℂ) else 0))
        = ((if x = j then (thermalAcceptance E β i j / (D:ℝ) : ℂ) * ρ i i else 0)
          + (if x = i then ((1 - thermalAcceptance E β i j) / (D:ℝ) : ℂ) * ρ i i
            else 0)) := by
      intro i j
      simp only [thermalKrausRow, thermalKrausWeight, Bool.cond_true, Bool.cond_false]
      by_cases hj : x = j <;> by_cases hi : x = i <;> simp [hj, hi]
    simp only [hsumb]

    have hrow : ∀ i : Fin D,
        (∑ j : Fin D, ((if x = j then (thermalAcceptance E β i j / (D:ℝ) : ℂ) * ρ i i
              else 0)
            + (if x = i then ((1 - thermalAcceptance E β i j) / (D:ℝ) : ℂ) * ρ i i
              else 0)))
        = (thermalAcceptance E β i x / (D:ℝ) : ℂ) * ρ i i
          + (if x = i then (1 - ∑ j : Fin D,
              (thermalAcceptance E β i j / (D:ℝ) : ℂ)) * ρ i i else 0) := by
      intro i
      rw [Finset.sum_add_distrib]
      have h1 : ∑ j : Fin D, (if x = j then
          (thermalAcceptance E β i j / (D:ℝ) : ℂ) * ρ i i else 0)
          = (thermalAcceptance E β i x / (D:ℝ) : ℂ) * ρ i i :=
        (Fintype.sum_eq_single x (fun j hj => if_neg (fun h => hj h.symm))).trans
          (if_pos rfl)
      rw [h1]
      by_cases hi : x = i
      · subst i
        rw [Finset.sum_congr rfl (fun j _ => if_pos rfl)]
        rw [show (∑ j : Fin D, ((1 - thermalAcceptance E β x j) / (D:ℝ) : ℂ)
            * ρ x x) = (∑ j : Fin D, ((1 - thermalAcceptance E β x j) / (D:ℝ) : ℂ))
            * ρ x x from (Finset.sum_mul Finset.univ
            (fun j => ((1 - thermalAcceptance E β x j) / (D:ℝ) : ℂ)) (ρ x x)).symm]
        rw [sum_one_sub D hD (fun j => thermalAcceptance E β x j)]
        rw [if_pos rfl]
      · have hz : ∀ j : Fin D,
            (if x = i then ((1 - thermalAcceptance E β i j) / (D:ℝ) : ℂ) * ρ i i
              else 0) = 0 := fun j => if_neg (fun h : x = i => hi h)
        rw [Finset.sum_congr rfl (fun j _ => hz j), if_neg hi, add_zero]
        simp
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_add_distrib]
    calc (∑ i : Fin D, (thermalAcceptance E β i x / (D:ℝ) : ℂ) * ρ i i)
            + ∑ i_1 : Fin D, (if x = i_1 then
              (1 - ∑ j : Fin D, (thermalAcceptance E β i_1 j / (D:ℝ) : ℂ)) * ρ i_1 i_1
              else 0)
        = (∑ i : Fin D, (thermalAcceptance E β i x / (D:ℝ) : ℂ) * ρ i i)
          + (1 - ∑ j : Fin D, (thermalAcceptance E β x j / (D:ℝ) : ℂ)) * ρ x x := by
          refine congrArg _ ?_
          exact (Fintype.sum_eq_single x (fun i hi => if_neg
            (fun h : x = i => hi h.symm))).trans (if_pos rfl)
      _ = ∑ i : Fin D, (thermalKernel D E β i x : ℂ) * ρ i i :=
          forget_diag_sum D hD E β ρ x
  · rw [Matrix.diagonal_apply, if_neg hxy]
    have hzero : ∀ i j : Fin D,
        ((thermalKrausWeight D E β i j true : ℂ) * ρ i i
            * (if x = thermalKrausRow D i j true ∧ y = thermalKrausRow D i j true then
              (1:ℂ) else 0))
          + ((thermalKrausWeight D E β i j false : ℂ) * ρ i i
            * (if x = thermalKrausRow D i j false ∧ y = thermalKrausRow D i j false then
              (1:ℂ) else 0)) = 0 := by
      intro i j
      rw [if_neg (fun h => hxy (h.1.trans h.2.symm)),
        if_neg (fun h => hxy (h.1.trans h.2.symm))]
      ring
    simp only [hzero]
    simp

theorem thermalPowerChannel_iterate (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (n : ℕ) (ρ : Operator D) :
    (thermalPowerChannel D hD E β n).map ρ
      = ((thermalInstrument D hD E β).forget.map)^[n] ρ := by
  induction n generalizing ρ with
  | zero => rfl
  | succ n ih =>
    show (thermalPowerChannel D hD E β n).map
      ((thermalInstrument D hD E β).forget.map ρ) = _
    rw [Function.iterate_succ, ih]
    rfl

theorem measured_metropolis_channel_stationary (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ)
    (β : ℝ) :
    (∀ ρ : Operator D, (thermalInstrument D hD E β).forget.map ρ =
      Matrix.diagonal (fun j : Fin D => ∑ i : Fin D, (thermalKernel D E β i j : ℂ)*ρ i i)) ∧
    (thermalInstrument D hD E β).forget.map (diagonalGibbsDensity D hD E β)=diagonalGibbsDensity D hD E β ∧
    (∀ (ρ : Operator D) (n : ℕ), (thermalPowerChannel D hD E β n).map ρ =
      ((thermalInstrument D hD E β).forget.map)^[n] ρ) := by
  refine ⟨thermalInstrument_forget_apply D hD E β, ?_,
    fun ρ n => thermalPowerChannel_iterate D hD E β n ρ⟩
  rw [thermalInstrument_forget_apply D hD E β]
  ext x y
  by_cases hxy : x = y
  · subst y
    rw [Matrix.diagonal_apply, if_pos rfl]
    have hπ : ∑ i : Fin D, (diagonalGibbsDist D hD E β).prob i
        * thermalKernel D E β i x = (diagonalGibbsDist D hD E β).prob x :=
      (diagonal_metropolis_transition_reversible D hD E β).2.2.1.2.2 x
    have hcast : ((diagonalGibbsDist D hD E β).prob x : ℂ)
        = ∑ i : Fin D, (thermalKernel D E β i x : ℂ)
          * ((diagonalGibbsDist D hD E β).prob i : ℂ) := by
      have hcast' : ((∑ i : Fin D, (diagonalGibbsDist D hD E β).prob i
          * thermalKernel D E β i x : ℝ) : ℂ)
          = ∑ i : Fin D, ((thermalKernel D E β i x : ℝ) : ℂ)
            * ((diagonalGibbsDist D hD E β).prob i : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring
      rw [← hπ, hcast']
    have hdens : ∀ i : Fin D, diagonalGibbsDensity D hD E β i i
        = ((diagonalGibbsDist D hD E β).prob i : ℂ) := fun i => by
      show (Matrix.diagonal (fun k => ((diagonalGibbsDist D hD E β).prob k : ℂ))) i i = _
      rw [Matrix.diagonal_apply, if_pos rfl]
    rw [hdens x, Finset.sum_congr rfl (fun i _ => by rw [hdens i]), hcast]
  · rw [Matrix.diagonal_apply, if_neg hxy]
    rw [diagonalGibbsDensity]
    rw [Matrix.diagonal_apply, if_neg hxy]

noncomputable def kernelDiagMap {D : ℕ} (w : Fin D → Fin D → ℝ) :
    Operator D →ₗ[ℂ] Operator D :=
  ∑ i : Fin D, ∑ x : Fin D, ((w i x : ℂ) • conjBranch (Matrix.single x i (1:ℂ)))

private theorem conjBranch_single_apply {D : ℕ} (i x : Fin D) (σ : Operator D) (u v : Fin D) :
    conjBranch (Matrix.single x i (1:ℂ)) σ u v = if x = u ∧ x = v then σ i i else 0 := by
  by_cases h1 : x = u
  · by_cases h2 : x = v
    · simp only [conjBranch_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
        Matrix.of_apply, h1, h2, Finset.sum_ite_eq, Finset.mem_univ, star_one]
      by_cases huv : u = v <;> simp [huv, Finset.sum_ite_eq]
    · have huv : u ≠ v := by
        intro h
        apply h2
        exact h1.trans h
      simp [h1, h2, huv, conjBranch_apply]
  · simp [h1, conjBranch_apply]

theorem kernelDiagMap_apply {D : ℕ} (w : Fin D → Fin D → ℝ) (σ : Operator D) :
    kernelDiagMap w σ = Matrix.diagonal (fun x => ∑ i, (w i x : ℂ) * σ i i) := by
  ext u v
  have h : ∀ i x : Fin D, (((w i x : ℂ)) • conjBranch (Matrix.single x i (1:ℂ))) σ u v
      = if x = u ∧ x = v then (w i x : ℂ) * σ i i else 0 := by
    intro i x
    rw [LinearMap.smul_apply, Matrix.smul_apply, conjBranch_single_apply, smul_ite,
      smul_eq_mul, smul_zero]
  simp only [kernelDiagMap, LinearMap.sum_apply, Matrix.sum_apply, h]
  by_cases huv : u = v
  · subst huv
    simp
  · have hfalse : ∀ a : Fin D, ¬(a = u ∧ a = v) := fun a hh => huv (hh.1.symm.trans hh.2)
    simp [huv, hfalse, Matrix.diagonal_apply]

theorem kernelDiagMap_cp {D : ℕ} {w : Fin D → Fin D → ℝ} (hw : ∀ i x, 0 ≤ w i x) :
    CompletelyPositive (kernelDiagMap w) := by
  refine CompletelyPositive.sum (fun i _ => CompletelyPositive.sum (fun x _ => ?_))
  intro r A hA
  have hamp : ChannelAmplification (((w i x : ℂ)) • conjBranch (Matrix.single x i (1:ℂ))) r A
      = ((w i x : ℂ)) • ChannelAmplification (conjBranch (Matrix.single x i (1:ℂ))) r A := by
    ext p q
    simp [ChannelAmplification]
  rw [hamp]
  exact Matrix.PosSemidef.smul (completelyPositive_conjBranch _ r A hA)
    (by exact_mod_cast hw i x)

theorem kernelDiagMap_tp {D : ℕ} {w : Fin D → Fin D → ℝ} (hw : ∀ i, ∑ x, w i x = 1) :
    TracePreserving (kernelDiagMap w) := by
  intro σ
  have h1 : Matrix.trace (kernelDiagMap w σ) = ∑ x : Fin D, ∑ i : Fin D, (w i x : ℂ) * σ i i := by
    rw [kernelDiagMap_apply, Matrix.trace_diagonal]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, hw i, Complex.ofReal_one, one_mul]
  rfl

private theorem tensorLeft_add' {D E R : ℕ} (S T : Operator D →ₗ[ℂ] Operator E)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (S + T) ρ = tensorLeft S ρ + tensorLeft T ρ := by
  ext x y
  simp [tensorLeft]

theorem traceSmulLeft_eq_kernelDiagMap {D : ℕ} (p : Fin D → ℝ) (σ : Operator D) :
    traceSmulLeft (Matrix.diagonal (fun x => ((p x : ℝ) : ℂ))) σ
      = kernelDiagMap (fun _ x => p x) σ := by
  rw [kernelDiagMap_apply, traceSmulLeft_apply]
  ext u v
  by_cases huv : u = v
  · subst huv
    rw [Matrix.smul_apply, Matrix.diagonal_apply, if_pos rfl, smul_eq_mul,
      Matrix.diagonal_apply, if_pos rfl, ← Finset.mul_sum]
    exact mul_comm _ _
  · simp [huv, Matrix.diagonal_apply]

noncomputable def kernelPow {D : ℕ} (k : Fin D → Fin D → ℝ) : ℕ → Fin D → Fin D → ℝ
  | 0 => fun i x => if i = x then 1 else 0
  | n + 1 => fun i x => ∑ m, k i m * kernelPow k n m x

theorem kernelPow_zero {D : ℕ} (k : Fin D → Fin D → ℝ) (i x : Fin D) :
    kernelPow k 0 i x = if i = x then (1:ℝ) else 0 := rfl

private theorem kernelDiagMap_comp_apply {D : ℕ} (w v : Fin D → Fin D → ℝ) (σ : Operator D) :
    kernelDiagMap w (kernelDiagMap v σ)
      = kernelDiagMap (fun i x => ∑ m, v i m * w m x) σ := by
  rw [kernelDiagMap_apply, kernelDiagMap_apply, kernelDiagMap_apply]
  ext u v'
  simp only [Matrix.diagonal_apply]
  by_cases huv : u = v'
  · subst huv
    rw [if_pos rfl, if_pos rfl]
    calc (∑ x : Fin D, (w x u : ℂ) * ∑ i : Fin D, (v i x : ℂ) * σ i i)
        = ∑ i : Fin D, ∑ x : Fin D, (w x u : ℂ) * ((v i x : ℂ) * σ i i) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
      _ = ∑ i : Fin D, ∑ x : Fin D, ((v i x * w x u : ℝ) : ℂ) * σ i i := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
          push_cast
          ring
      _ = ∑ i : Fin D, ((∑ m : Fin D, v i m * w m u : ℝ) : ℂ) * σ i i := by
          simp only [← Finset.sum_mul, ← Complex.ofReal_sum]
  · rw [if_neg huv, if_neg huv]

theorem thermalPowerChannel_eq_kernelDiagMap (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    ∀ m : ℕ, (thermalPowerChannel D hD E β (m+1)).map
      = kernelDiagMap (kernelPow (thermalKernel D E β) (m+1)) := by
  intro m
  induction m with
  | zero =>
    apply LinearMap.ext
    intro σ
    have h1 : (thermalPowerChannel D hD E β 1).map σ
        = (thermalInstrument D hD E β).forget.map σ := rfl
    have hkp : ∀ i x : Fin D, kernelPow (thermalKernel D E β) 1 i x = thermalKernel D E β i x := by
      intro i x
      simp [kernelPow, Finset.sum_ite_eq]
    rw [h1, thermalInstrument_forget_apply, kernelDiagMap_apply]
    ext u v
    simp only [Matrix.diagonal_apply]
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl, if_pos rfl]
      exact Finset.sum_congr rfl fun i _ => by rw [hkp i u]
    · rw [if_neg huv, if_neg huv]
  | succ m ih =>
    apply LinearMap.ext
    intro σ
    have hstep : (thermalPowerChannel D hD E β (m+2)).map σ
        = (thermalPowerChannel D hD E β (m+1)).map ((thermalInstrument D hD E β).forget.map σ) := rfl
    have hforget : (thermalInstrument D hD E β).forget.map
        = kernelDiagMap (thermalKernel D E β) := by
      apply LinearMap.ext
      intro τ
      rw [thermalInstrument_forget_apply, kernelDiagMap_apply]
    rw [hstep, ih, hforget, kernelDiagMap_comp_apply]
    congr 1

private theorem kernelPow_nonneg {D : ℕ} {k : Fin D → Fin D → ℝ} (hk : ∀ i x, 0 ≤ k i x) :
    ∀ (n : ℕ) (i x : Fin D), 0 ≤ kernelPow k n i x := by
  intro n
  induction n with
  | zero =>
    intro i x
    rw [kernelPow_zero]
    by_cases hix : i = x
    · rw [if_pos hix]; try norm_num
    · rw [if_neg hix]; try exact le_refl _
  | succ n ih =>
    intro i x
    refine Finset.sum_nonneg fun m _ => ?_
    exact mul_nonneg (hk i m) (ih m x)

private theorem kernelPow_row {D : ℕ} {k : Fin D → Fin D → ℝ} (hk : ∀ i, ∑ x, k i x = 1) :
    ∀ (n : ℕ) (i : Fin D), ∑ x, kernelPow k n i x = 1 := by
  intro n
  induction n with
  | zero =>
    intro i
    rw [Finset.sum_congr rfl (fun x _ => kernelPow_zero k i x), Finset.sum_ite_eq,
      if_pos (Finset.mem_univ i)]
  | succ n ih =>
    intro i
    calc ∑ x : Fin D, kernelPow k (n+1) i x
        = ∑ x : Fin D, ∑ m : Fin D, k i m * kernelPow k n m x := rfl
      _ = ∑ m : Fin D, k i m * ∑ x : Fin D, kernelPow k n m x := by
          rw [Finset.sum_comm]
          simp only [← Finset.mul_sum]
      _ = ∑ m : Fin D, k i m * 1 := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [ih m]
      _ = 1 := by
          rw [← Finset.sum_mul, hk i, mul_one]

private theorem kernelPow_stat {D : ℕ} {q : Fin D → Fin D → ℝ} {p : Fin D → ℝ}
    (hqrow : ∀ i, ∑ x, q i x = 1) (hpstat : ∀ x, ∑ i, p i * q i x = p x) :
    ∀ (n : ℕ) (x : Fin D), ∑ i, p i * kernelPow q n i x = p x := by
  intro n
  induction n with
  | zero =>
    intro x
    rw [Finset.sum_congr rfl (fun i _ => by rw [kernelPow_zero])]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ x)]
  | succ n ih =>
    intro x
    calc ∑ i : Fin D, p i * kernelPow q (n+1) i x
        = ∑ i : Fin D, p i * ∑ m : Fin D, q i m * kernelPow q n m x := rfl
      _ = ∑ i : Fin D, ∑ m : Fin D, p i * (q i m * kernelPow q n m x) := by
          simp only [Finset.mul_sum]
      _ = ∑ m : Fin D, ∑ i : Fin D, p i * (q i m * kernelPow q n m x) := Finset.sum_comm
      _ = ∑ m : Fin D, ∑ i : Fin D, (p i * q i m) * kernelPow q n m x := by
          simp only [mul_assoc]
      _ = ∑ m : Fin D, (∑ i : Fin D, p i * q i m) * kernelPow q n m x := by
          simp only [← Finset.sum_mul]
      _ = ∑ m : Fin D, p m * kernelPow q n m x := by
          simp only [hpstat]
      _ = p x := ih x

private theorem kernelPow_split {D : ℕ} {k q : Fin D → Fin D → ℝ} {p : Fin D → ℝ} {η c : ℝ}
    (hc : 0 < c) (hcη : c + η = 1)
    (hqmul : ∀ i x, c * q i x = k i x - η * p x)
    (hqrow : ∀ i, ∑ x, q i x = 1) (hpsum : ∑ x, p x = 1)
    (hstat : ∀ x, ∑ i, p i * k i x = p x) :
    ∀ (n : ℕ) (i x : Fin D),
      kernelPow k n i x = c ^ n * kernelPow q n i x + (1 - c ^ n) * p x := by
  intro n
  induction n with
  | zero =>
    intro i x
    simp only [pow_zero, one_mul, sub_self, zero_mul, add_zero]
    rw [kernelPow_zero, kernelPow_zero]
  | succ n ih =>
    intro i x
    have hone : ∀ i x : Fin D, k i x = c * q i x + η * p x := by
      intro i x
      rw [hqmul i x]
      ring
    have hqstat : ∀ y : Fin D, ∑ i : Fin D, p i * q i y = p y := by
      intro y
      have hqdiv : ∀ i : Fin D, q i y = (k i y - η * p y) / c := by
        intro i
        rw [eq_div_iff hc.ne', mul_comm]
        exact hqmul i y
      calc ∑ i : Fin D, p i * q i y
          = ∑ i : Fin D, p i * ((k i y - η * p y) / c) :=
            Finset.sum_congr rfl fun i _ => by rw [hqdiv i]
        _ = (∑ i : Fin D, p i * (k i y - η * p y)) / c := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun i _ => (mul_div_assoc _ _ _).symm
        _ = (∑ i : Fin D, (p i * k i y - p i * (η * p y))) / c := by
            refine congrArg (fun t => t / c) ?_
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = ((∑ i : Fin D, p i * k i y) - η * p y * (∑ i : Fin D, p i)) / c := by
            congr 1
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = (p y - η * p y * 1) / c := by rw [hstat y, hpsum]
        _ = p y := by
            have h1c : (1:ℝ) - η = c := by linarith
            have hkey : p y - η * p y * 1 = c * p y := by
              rw [mul_one, ← h1c]
              ring
            rw [hkey]
            field_simp
    have hqstatn : ∀ y : Fin D, ∑ m : Fin D, p m * kernelPow q n m y = p y :=
      fun y => kernelPow_stat hqrow hqstat n y
    calc kernelPow k (n+1) i x
        = ∑ m : Fin D, k i m * kernelPow k n m x := rfl
      _ = ∑ m : Fin D, (c * q i m + η * p m)
            * (c ^ n * kernelPow q n m x + (1 - c ^ n) * p x) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hone i m, ih m x]
      _ = (∑ m : Fin D, c * q i m * (c ^ n * kernelPow q n m x))
          + (∑ m : Fin D, c * q i m * ((1 - c ^ n) * p x))
          + (∑ m : Fin D, η * p m * (c ^ n * kernelPow q n m x))
          + (∑ m : Fin D, η * p m * ((1 - c ^ n) * p x)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
      _ = c ^ (n+1) * kernelPow q (n+1) i x + (1 - c ^ (n+1)) * p x := by
          have s1 : ∑ m : Fin D, c * q i m * (c ^ n * kernelPow q n m x)
              = c ^ (n+1) * kernelPow q (n+1) i x := by
            rw [show c ^ (n+1) = c * c ^ n from (by rw [pow_succ]; ring), kernelPow,
              Finset.mul_sum]
            exact Finset.sum_congr rfl fun m _ => by ring
          have s2 : ∑ m : Fin D, c * q i m * ((1 - c ^ n) * p x)
              = c * (1 - c ^ n) * p x := by
            calc ∑ m : Fin D, c * q i m * ((1 - c ^ n) * p x)
                = ∑ m : Fin D, c * (1 - c ^ n) * p x * q i m :=
                  Finset.sum_congr rfl fun m _ => by ring
              _ = c * (1 - c ^ n) * p x * (∑ m : Fin D, q i m) :=
                  (Finset.mul_sum Finset.univ _ _).symm
              _ = c * (1 - c ^ n) * p x * 1 := by rw [hqrow i]
              _ = c * (1 - c ^ n) * p x := by ring
          have s3 : ∑ m : Fin D, η * p m * (c ^ n * kernelPow q n m x)
              = η * c ^ n * p x := by
            have h := hqstatn x
            calc ∑ m : Fin D, η * p m * (c ^ n * kernelPow q n m x)
                = ∑ m : Fin D, η * c ^ n * (p m * kernelPow q n m x) :=
                  Finset.sum_congr rfl fun m _ => by ring
              _ = η * c ^ n * (∑ m : Fin D, p m * kernelPow q n m x) :=
                  (Finset.mul_sum Finset.univ _ _).symm
              _ = η * c ^ n * p x := by rw [h]
          have s4 : ∑ m : Fin D, η * p m * ((1 - c ^ n) * p x)
              = η * (1 - c ^ n) * p x := by
            calc ∑ m : Fin D, η * p m * ((1 - c ^ n) * p x)
                = ∑ m : Fin D, η * (1 - c ^ n) * p x * p m :=
                  Finset.sum_congr rfl fun m _ => by ring
              _ = η * (1 - c ^ n) * p x * (∑ m : Fin D, p m) :=
                  (Finset.mul_sum Finset.univ _ _).symm
              _ = η * (1 - c ^ n) * p x * 1 := by rw [hpsum]
              _ = η * (1 - c ^ n) * p x := by ring
          rw [s1, s2, s3, s4]
          rw [show c ^ (n+1) = c * c ^ n from (by rw [pow_succ]; ring)]
          have key : c * c ^ n * kernelPow q (n + 1) i x + c * (1 - c ^ n) * p x
              + η * c ^ n * p x + η * (1 - c ^ n) * p x
              = c * c ^ n * kernelPow q (n + 1) i x + (1 - c * c ^ n) * p x := by
            linear_combination hcη * p x
          exact key

private theorem kernelDiagMap_two_term {D : ℕ} (u v : Fin D → Fin D → ℝ) (t s : ℝ)
    (σ : Operator D) :
    kernelDiagMap (fun i x => t * u i x + s * v i x) σ
      = ((t : ℝ) : ℂ) • kernelDiagMap u σ + ((s : ℝ) : ℂ) • kernelDiagMap v σ := by
  rw [kernelDiagMap_apply, kernelDiagMap_apply, kernelDiagMap_apply]
  ext x y
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, if_pos rfl, if_pos rfl]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  · rw [if_neg hxy, if_neg hxy, if_neg hxy]
    simp

theorem measured_gibbs_reference_mixing (D : ℕ) (hD : 0 < D) (r : ℕ) (E : Fin D → ℝ) (β R : ℝ)
    (n : ℕ) (hβ : 0 ≤ β) (hR : 0 ≤ R) (hn : 0 < n)
    (hE : ∀ i, 0 ≤ E i ∧ E i ≤ R)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) (hρ : ρ.PosSemidef)
    (htr : Matrix.trace ρ = 1) :
    Matrix.traceNorm (tensorLeft (thermalPowerChannel D hD E β n).map ρ
      - TensorGate (diagonalGibbsDensity D hD E β) (Matrix.traceLeft ρ))
      ≤ 2 * (1 - Real.exp (-β * R)) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hηpos, hηle, hmin⟩ :=
    diagonal_metropolis_derived_minorization D hD E β R hβ hR hE
  have hG2 := diagonal_metropolis_transition_reversible D hD E β
  have hG1 := diagonal_gibbs_weight_density D hD E β
  have hpsum : ∑ x : Fin D, (diagonalGibbsDist D hD E β).prob x = 1 :=
    (diagonalGibbsDist D hD E β).sum_one
  have hstatk : ∀ x : Fin D, ∑ i : Fin D, (diagonalGibbsDist D hD E β).prob i
      * thermalKernel D E β i x = (diagonalGibbsDist D hD E β).prob x :=
    fun x => hG2.2.2.1.2.2 x
  have hdens : diagonalGibbsDensity D hD E β
      = Matrix.diagonal (fun i => ((diagonalGibbsDist D hD E β).prob i : ℂ)) := hG1.2.1
  have hπpsd : (diagonalGibbsDensity D hD E β).PosSemidef := (hG1.2.2).1
  have hπtr : Matrix.trace (diagonalGibbsDensity D hD E β) = 1 := (hG1.2.2).2
  by_cases hc0 : (1:ℝ) - Real.exp (-β * R) = 0
  · have hη1 : Real.exp (-β * R) = 1 := by linarith
    have hkπ : ∀ i x : Fin D, thermalKernel D E β i x
        = (diagonalGibbsDist D hD E β).prob x := by
      intro i x
      have hnnall : ∀ y ∈ (Finset.univ : Finset (Fin D)), 0 ≤ thermalKernel D E β i y
          - Real.exp (-β * R) * (diagonalGibbsDist D hD E β).prob y := by
        intro y _
        have := hmin i y
        linarith
      have hs : ∑ y : Fin D, (thermalKernel D E β i y - Real.exp (-β * R)
          * (diagonalGibbsDist D hD E β).prob y) = 0 := by
        rw [Finset.sum_sub_distrib, hG2.1.2 i, ← Finset.mul_sum, hpsum, hη1, mul_one,
          sub_self]
      have h0 := sub_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg hnnall).mp hs x (Finset.mem_univ x))
      rw [h0, hη1, one_mul]
    have hkdiag : (thermalInstrument D hD E β).forget.map
        = kernelDiagMap (fun _ x => (diagonalGibbsDist D hD E β).prob x) := by
      apply LinearMap.ext
      intro σ
      rw [thermalInstrument_forget_apply, kernelDiagMap_apply]
      ext u v
      simp only [Matrix.diagonal_apply]
      by_cases huv : u = v
      · subst huv
        rw [if_pos rfl, if_pos rfl, Finset.sum_congr rfl (fun i _ => by rw [hkπ i u])]
      · rw [if_neg huv, if_neg huv]
    have hSS : traceSmulLeft (diagonalGibbsDensity D hD E β)
        = kernelDiagMap (fun _ x => (diagonalGibbsDist D hD E β).prob x) := by
      rw [hdens]
      apply LinearMap.ext
      intro σ
      exact traceSmulLeft_eq_kernelDiagMap (diagonalGibbsDist D hD E β).prob σ
    have hpower : (thermalPowerChannel D hD E β (m+1)).map
        = traceSmulLeft (diagonalGibbsDensity D hD E β) := by
      induction m with
      | zero =>
        apply LinearMap.ext
        intro σ
        have h1 : (thermalPowerChannel D hD E β 1).map σ
            = (thermalInstrument D hD E β).forget.map σ := rfl
        rw [h1, hkdiag, ← hSS]
      | succ m ih =>
        apply LinearMap.ext
        intro σ
        have hstep : (thermalPowerChannel D hD E β (m+2)).map σ
            = (thermalPowerChannel D hD E β (m+1)).map
              ((thermalInstrument D hD E β).forget.map σ) := rfl
        have htp : Matrix.trace
            (kernelDiagMap (fun _ x => (diagonalGibbsDist D hD E β).prob x) σ)
            = Matrix.trace σ := kernelDiagMap_tp (fun _ => hpsum) σ
        rw [hstep, ih (by omega), hkdiag, traceSmulLeft_apply, traceSmulLeft_apply, htp]
    rw [hpower, tensorLeft_traceSmulLeft, sub_self, Matrix.traceNorm_zero, hc0]
    simp [zero_pow (by omega : (0:ℕ) + 1 ≠ 0)]
  · have hc : 0 < (1:ℝ) - Real.exp (-β * R) := by
      rcases lt_or_eq_of_le hηle with h | h
      · exact sub_pos.mpr h
      · exact absurd (sub_eq_zero_of_eq h.symm) hc0
    set q : Fin D → Fin D → ℝ := fun i x => (thermalKernel D E β i x
      - Real.exp (-β * R) * (diagonalGibbsDist D hD E β).prob x)
      / (1 - Real.exp (-β * R)) with hqdef
    have hqmul : ∀ i x, (1 - Real.exp (-β * R)) * q i x
        = thermalKernel D E β i x
          - Real.exp (-β * R) * (diagonalGibbsDist D hD E β).prob x :=
      fun i x => mul_div_cancel₀ _ hc.ne'
    have hqnonneg : ∀ i x, 0 ≤ q i x := by
      intro i x
      exact div_nonneg (by have := hmin i x; linarith) hc.le
    have hqrow : ∀ i, ∑ x, q i x = 1 := by
      intro i
      have h1 : ∑ x : Fin D, (thermalKernel D E β i x
          - Real.exp (-β * R) * (diagonalGibbsDist D hD E β).prob x)
          = 1 - Real.exp (-β * R) := by
        rw [Finset.sum_sub_distrib, hG2.1.2 i, ← Finset.mul_sum, hpsum, mul_one]
      rw [hqdef, ← Finset.sum_div, h1, div_self hc.ne']
    have hsplit := kernelPow_split (k := thermalKernel D E β) (q := q)
      (p := (diagonalGibbsDist D hD E β).prob) (η := Real.exp (-β * R))
      (c := 1 - Real.exp (-β * R)) hc (by ring) hqmul hqrow hpsum hstatk
    have hqpownn : ∀ i x, 0 ≤ kernelPow q (m+1) i x := kernelPow_nonneg hqnonneg (m+1)
    have hqpowrow : ∀ i, ∑ x, kernelPow q (m+1) i x = 1 := kernelPow_row hqrow (m+1)
    have hmix : (thermalPowerChannel D hD E β (m+1)).map
        = (((1 - Real.exp (-β * R)) ^ (m+1) : ℝ) : ℂ) • kernelDiagMap (kernelPow q (m+1))
          + (((1 - (1 - Real.exp (-β * R)) ^ (m+1) : ℝ)) : ℂ)
            • traceSmulLeft (diagonalGibbsDensity D hD E β) := by
      apply LinearMap.ext
      intro σ
      have hker : kernelPow (thermalKernel D E β) (m+1) = fun i x =>
          (1 - Real.exp (-β * R)) ^ (m+1) * kernelPow q (m+1) i x
          + (1 - (1 - Real.exp (-β * R)) ^ (m+1))
            * (diagonalGibbsDist D hD E β).prob x :=
        funext fun i => funext fun x => hsplit (m+1) i x
      rw [thermalPowerChannel_eq_kernelDiagMap D hD E β m, hker, kernelDiagMap_two_term]
      simp only [LinearMap.add_apply, LinearMap.smul_apply]
      have hS : traceSmulLeft (diagonalGibbsDensity D hD E β) σ
          = kernelDiagMap (fun _ x => (diagonalGibbsDist D hD E β).prob x) σ := by
        rw [hdens]
        exact traceSmulLeft_eq_kernelDiagMap (diagonalGibbsDist D hD E β).prob σ
      rw [hS]
    have hY : tensorLeft (traceSmulLeft (diagonalGibbsDensity D hD E β)) ρ
        = TensorGate (diagonalGibbsDensity D hD E β) (Matrix.traceLeft ρ) :=
      tensorLeft_traceSmulLeft _ _
    have hsplit2 : tensorLeft ((((1 - Real.exp (-β * R)) ^ (m+1) : ℝ) : ℂ)
          • kernelDiagMap (kernelPow q (m+1))
          + (((1 - (1 - Real.exp (-β * R)) ^ (m+1) : ℝ)) : ℂ)
            • traceSmulLeft (diagonalGibbsDensity D hD E β)) ρ
        = (((1 - Real.exp (-β * R)) ^ (m+1) : ℝ) : ℂ)
          • tensorLeft (kernelDiagMap (kernelPow q (m+1))) ρ
          + (((1 - (1 - Real.exp (-β * R)) ^ (m+1) : ℝ)) : ℂ)
            • TensorGate (diagonalGibbsDensity D hD E β) (Matrix.traceLeft ρ) := by
      rw [tensorLeft_add', tensorLeft_smul, tensorLeft_smul, hY]
    have key : ∀ (a : ℂ) (X Y : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
        a • X + (1 - a) • Y - Y = a • (X - Y) := by
      intro a X Y
      ext u v
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
      ring
    rw [hmix, hsplit2]
    rw [show (((1 - (1 - Real.exp (-β * R)) ^ (m+1) : ℝ)) : ℂ)
        = 1 - (((1 - Real.exp (-β * R)) ^ (m+1) : ℝ) : ℂ) from by push_cast; ring]
    rw [key]
    rw [Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hc.le (m+1))]
    have htri : Matrix.traceNorm (tensorLeft (kernelDiagMap (kernelPow q (m+1))) ρ
        - TensorGate (diagonalGibbsDensity D hD E β) (Matrix.traceLeft ρ))
        ≤ Matrix.traceNorm (tensorLeft (kernelDiagMap (kernelPow q (m+1))) ρ)
          + Matrix.traceNorm
            (TensorGate (diagonalGibbsDensity D hD E β) (Matrix.traceLeft ρ)) := by
      rw [sub_eq_add_neg]
      refine le_trans (Matrix.traceNorm_add_le _ _) ?_
      rw [Matrix.traceNorm_neg]
    have h1 : Matrix.traceNorm (tensorLeft (kernelDiagMap (kernelPow q (m+1))) ρ) = 1 := by
      have hpsd : (tensorLeft (kernelDiagMap (kernelPow q (m+1))) ρ).PosSemidef :=
        tensorLeft_posSemidef (kernelDiagMap_cp hqpownn) hρ
      have htrX : Matrix.trace (tensorLeft (kernelDiagMap (kernelPow q (m+1))) ρ)
          = Matrix.trace ρ :=
        tensorLeft_trace (kernelDiagMap (kernelPow q (m+1))) (kernelDiagMap_tp hqpowrow) ρ
      have h0 := Matrix.PosSemidef.traceNorm_eq_trace hpsd
      rw [htrX, htr, ← Complex.ofReal_one] at h0
      exact Complex.ofReal_injective h0
    have h2 : Matrix.traceNorm
        (TensorGate (diagonalGibbsDensity D hD E β) (Matrix.traceLeft ρ)) = 1 := by
      have hpsdL : (Matrix.traceLeft ρ).PosSemidef := hρ.traceLeft
      have hpsd : (TensorGate (diagonalGibbsDensity D hD E β) (Matrix.traceLeft ρ)).PosSemidef :=
        Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate hπpsd hpsdL
      have htrX : Matrix.trace
          (TensorGate (diagonalGibbsDensity D hD E β) (Matrix.traceLeft ρ)) = 1 := by
        rw [Qatlib.Foundations.PureStateMath.BornBridge.trace_tensorGate, hπtr, Matrix.traceLeft_trace,
            htr, mul_one]
      have h0 := Matrix.PosSemidef.traceNorm_eq_trace hpsd
      rw [htrX, ← Complex.ofReal_one] at h0
      exact Complex.ofReal_injective h0
    calc (1 - Real.exp (-β * R)) ^ (m+1) * Matrix.traceNorm
          (tensorLeft (kernelDiagMap (kernelPow q (m+1))) ρ
            - TensorGate (diagonalGibbsDensity D hD E β) (Matrix.traceLeft ρ))
        ≤ (1 - Real.exp (-β * R)) ^ (m+1) * (1 + 1) :=
          mul_le_mul_of_nonneg_left (le_trans htri (by rw [h1, h2])) (pow_nonneg hc.le (m+1))
      _ = 2 * (1 - Real.exp (-β * R)) ^ (m+1) := by ring

theorem thermalPowerChannel_eq_reset {D : ℕ} (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (hkπ : ∀ i x : Fin D, thermalKernel D E β i x = (diagonalGibbsDist D hD E β).prob x)
    (m : ℕ) :
    (thermalPowerChannel D hD E β (m+1)).map
      = traceSmulLeft (diagonalGibbsDensity D hD E β) := by
  have hG1 := diagonal_gibbs_weight_density D hD E β
  have hpsum : ∑ x : Fin D, (diagonalGibbsDist D hD E β).prob x = 1 :=
    (diagonalGibbsDist D hD E β).sum_one
  have hdens : diagonalGibbsDensity D hD E β
      = Matrix.diagonal (fun i => ((diagonalGibbsDist D hD E β).prob i : ℂ)) := hG1.2.1
  have hkdiag : (thermalInstrument D hD E β).forget.map
      = kernelDiagMap (fun _ x => (diagonalGibbsDist D hD E β).prob x) := by
    apply LinearMap.ext
    intro σ
    rw [thermalInstrument_forget_apply, kernelDiagMap_apply]
    ext u v
    simp only [Matrix.diagonal_apply]
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl, if_pos rfl, Finset.sum_congr rfl (fun i _ => by rw [hkπ i u])]
    · rw [if_neg huv, if_neg huv]
  have hSS : traceSmulLeft (diagonalGibbsDensity D hD E β)
      = kernelDiagMap (fun _ x => (diagonalGibbsDist D hD E β).prob x) := by
    rw [hdens]
    apply LinearMap.ext
    intro σ
    exact traceSmulLeft_eq_kernelDiagMap (diagonalGibbsDist D hD E β).prob σ
  induction m with
  | zero =>
    apply LinearMap.ext
    intro σ
    have h1 : (thermalPowerChannel D hD E β 1).map σ
        = (thermalInstrument D hD E β).forget.map σ := rfl
    rw [h1, hkdiag, ← hSS]
  | succ m ih =>
    apply LinearMap.ext
    intro σ
    have hstep : (thermalPowerChannel D hD E β (m+2)).map σ
        = (thermalPowerChannel D hD E β (m+1)).map
          ((thermalInstrument D hD E β).forget.map σ) := rfl
    have htp : Matrix.trace
        (kernelDiagMap (fun _ x => (diagonalGibbsDist D hD E β).prob x) σ)
        = Matrix.trace σ := kernelDiagMap_tp (fun _ => hpsum) σ
    rw [hstep, ih, hkdiag, traceSmulLeft_apply, traceSmulLeft_apply, htp]

private def consEquiv' {O : Type*} (n : ℕ) :
    O × (Fin n → O) ≃ (Fin (n + 1) → O) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, fun k => f k.succ)
  left_inv p := by
    rw [Prod.mk.injEq]
    constructor
    · exact Fin.cons_zero (α := fun _ => O) p.1 p.2
    · funext k
      exact Fin.cons_succ (α := fun _ => O) p.1 p.2 k
  right_inv f := by
    funext k
    rcases Fin.eq_zero_or_eq_succ k with h | ⟨k', h⟩
    · subst h
      exact Fin.cons_zero (α := fun _ => O) (f 0) (fun j => f j.succ)
    · subst h
      exact Fin.cons_succ (α := fun _ => O) (f 0) (fun j => f j.succ) k'

private theorem sum_cons {O : Type*} {M : Type*} [Fintype O] [AddCommMonoid M] (n : ℕ)
    (F : (Fin (n + 1) → O) → M) :
    ∑ hist : Fin (n + 1) → O, F hist
      = ∑ o : O, ∑ σ : Fin n → O, F (Fin.cons o σ) := by
  rw [← Fintype.sum_equiv (consEquiv' n) (fun p => F (Fin.cons p.1 p.2)) F
    (fun x => rfl), Fintype.sum_prod_type]

private theorem conjBranch_one (D : ℕ) :
    conjBranch ((1 : Operator D)) = LinearMap.id := by
  refine LinearMap.ext fun ρ => ?_
  simp

private theorem thermalInstrument_branch' (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (o : Fin D × Fin D × Bool) :
    (thermalInstrument D hD E β).branch o = conjBranch (thermalKraus D E β o) := by
  obtain ⟨i, j, b⟩ := o
  refine LinearMap.ext fun ρ => ?_
  rw [thermalInstrument_branch, conjBranch_apply]

noncomputable def thermalHistoryKraus (D : ℕ) (E : Fin D → ℝ) (β : ℝ) {n : ℕ}
    (hist : Fin n → Fin D × Fin D × Bool) : Operator D :=
  (List.ofFn hist).foldl (fun acc o => thermalKraus D E β o * acc) 1

private theorem thermalKraus_foldl_mul (D : ℕ) (E : Fin D → ℝ) (β : ℝ)
    (xs : List (Fin D × Fin D × Bool)) (A : Operator D) :
    xs.foldl (fun acc o => thermalKraus D E β o * acc) A =
      xs.foldl (fun acc o => thermalKraus D E β o * acc) 1 * A := by
  induction xs generalizing A with
  | nil => simp
  | cons o xs ih =>
    simp only [List.foldl_cons]
    rw [ih (thermalKraus D E β o * A), ih (thermalKraus D E β o * 1),
      Matrix.mul_one, Matrix.mul_assoc]

theorem thermalHistoryKraus_succ (D : ℕ) (E : Fin D → ℝ) (β : ℝ) {n : ℕ}
    (hist : Fin (n + 1) → Fin D × Fin D × Bool) :
    thermalHistoryKraus D E β hist =
      thermalHistoryKraus D E β (fun k => hist k.succ) * thermalKraus D E β (hist 0) := by
  simpa only [thermalHistoryKraus, List.ofFn_succ, List.foldl_cons, Matrix.mul_one] using
    thermalKraus_foldl_mul D E β (List.ofFn (fun k : Fin n => hist k.succ))
      (thermalKraus D E β (hist 0))

noncomputable def thermalHistoryInstrument (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    (n : ℕ) → Instrument (Fin n → Fin D × Fin D × Bool) D D
  | 0 => Instrument.ofBranches (fun _ => LinearMap.id)
      (fun _ => (QuantumChannel.id D).completelyPositive) (by
        intro A
        simp)
  | n + 1 =>
      let chain := (thermalInstrument D hD E β).seq (thermalHistoryInstrument D hD E β n)
      let e := consEquiv' (O := Fin D × Fin D × Bool) n
      { branch := fun hist => chain.branch (e.symm hist)
        cp := fun hist => chain.cp (e.symm hist)
        tni := fun hist => chain.tni (e.symm hist)
        total := by
          intro A
          exact (congrArg Matrix.trace
            (e.symm.sum_comp (fun op => chain.branch op A))).trans (chain.total A) }

private theorem thermalHistoryInstrument_forget (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ)
    (β : ℝ) : ∀ (n : ℕ) (A : Operator D),
    (thermalHistoryInstrument D hD E β n).forget.map A
      = (thermalPowerChannel D hD E β n).map A := by
  intro n
  induction n with
  | zero =>
    intro A
    rw [thermalPowerChannel_iterate D hD E β 0 A]
    simp
    rfl
  | succ n ih =>
    intro A
    have hsum : ((thermalHistoryInstrument D hD E β (n+1)).forget.map A)
        = (thermalHistoryInstrument D hD E β n).forget.map
          ((thermalInstrument D hD E β).forget.map A) := by
      rw [Instrument.forget_apply (thermalHistoryInstrument D hD E β (n+1)),
        Instrument.forget_apply (thermalInstrument D hD E β),
        Instrument.forget_apply (thermalHistoryInstrument D hD E β n)]
      rw [sum_cons]
      simp only [thermalHistoryInstrument, Instrument.seq, consEquiv',
        Fin.cons_zero, Fin.cons_succ, LinearMap.comp_apply, map_sum]
      exact Finset.sum_comm
    rw [hsum, ih]
    rfl

theorem measured_metropolis_history_three_counts (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ)
    (β : ℝ) (n : ℕ) (hist : Fin n → Fin D × Fin D × Bool) :
    (thermalHistoryInstrument D hD E β n).forget.map = (thermalPowerChannel D hD E β n).map ∧
    (thermalHistoryInstrument D hD E β n).branch hist = conjBranch (thermalHistoryKraus D E β hist) ∧
    (∑ k : Fin n, (observedLeaf 1 (thermalProgram D E β (hist k).2.1)
      (thermalLeaf D hD E β (hist k).2.1 (hist k).1 (hist k).2.2)).gates)=2*n ∧
    (∑ k : Fin n, (observedLeaf 1 (thermalProgram D E β (hist k).2.1)
      (thermalLeaf D hD E β (hist k).2.1 (hist k).1 (hist k).2.2)).measurements)=2*n ∧
    (∑ k : Fin n, (observedLeaf 1 (thermalProgram D E β (hist k).2.1)
      (thermalLeaf D hD E β (hist k).2.1 (hist k).1 (hist k).2.2)).queries)=0 := by
  refine ⟨LinearMap.ext (thermalHistoryInstrument_forget D hD E β n), ?_, ?_, ?_, ?_⟩
  · induction n with
    | zero =>
      have h1 : thermalHistoryKraus D E β hist = 1 := by simp [thermalHistoryKraus]
      rw [h1, conjBranch_one]
      rfl
    | succ n ih =>
      have hcomp : (thermalHistoryInstrument D hD E β (n+1)).branch hist
          = ((thermalHistoryInstrument D hD E β n).branch (fun k => hist k.succ)).comp
            ((thermalInstrument D hD E β).branch (hist 0)) := rfl
      rw [hcomp, ih, thermalInstrument_branch', conjBranch_comp, thermalHistoryKraus_succ]
  · have hleaf : ∀ k : Fin n,
        (observedLeaf 1 (thermalProgram D E β (hist k).2.1)
          (thermalLeaf D hD E β (hist k).2.1 (hist k).1 (hist k).2.2)).gates = 2 :=
      fun k => ((measured_metropolis_leaf_resources D hD E β (hist k).2.1).2.2.2
        (hist k).1 (hist k).2.2).2.2.1
    calc ∑ k : Fin n, (observedLeaf 1 (thermalProgram D E β (hist k).2.1)
          (thermalLeaf D hD E β (hist k).2.1 (hist k).1 (hist k).2.2)).gates
        = ∑ k : Fin n, (2:ℕ) := Finset.sum_congr rfl fun k _ => hleaf k
      _ = 2 * n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        omega
  · have hleaf : ∀ k : Fin n,
        (observedLeaf 1 (thermalProgram D E β (hist k).2.1)
          (thermalLeaf D hD E β (hist k).2.1 (hist k).1 (hist k).2.2)).measurements = 2 :=
      fun k => ((measured_metropolis_leaf_resources D hD E β (hist k).2.1).2.2.2
        (hist k).1 (hist k).2.2).2.2.2
    calc ∑ k : Fin n, (observedLeaf 1 (thermalProgram D E β (hist k).2.1)
          (thermalLeaf D hD E β (hist k).2.1 (hist k).1 (hist k).2.2)).measurements
        = ∑ k : Fin n, (2:ℕ) := Finset.sum_congr rfl fun k _ => hleaf k
      _ = 2 * n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        omega
  · have hleaf : ∀ k : Fin n,
        (observedLeaf 1 (thermalProgram D E β (hist k).2.1)
          (thermalLeaf D hD E β (hist k).2.1 (hist k).1 (hist k).2.2)).queries = 0 :=
      fun k => ((measured_metropolis_leaf_resources D hD E β (hist k).2.1).2.2.2
        (hist k).1 (hist k).2.2).2.1
    calc ∑ k : Fin n, (observedLeaf 1 (thermalProgram D E β (hist k).2.1)
          (thermalLeaf D hD E β (hist k).2.1 (hist k).1 (hist k).2.2)).queries
        = ∑ k : Fin n, (0:ℕ) := Finset.sum_congr rfl fun k _ => hleaf k
      _ = 0 := by simp

end Qatlib.Concepts.LindbladFlow.GkslSemigroup
