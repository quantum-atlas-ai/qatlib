/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeQuantumMachineDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeStandardDefs
import Qatlib.Concepts.UniformBqp.Phi3Compile.StandardModelDefs
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Mul
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeMachineCompletion
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.UniformBqp.Phi3Compile

open Qatlib
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.UniformBqp.Phi3Compile
open scoped BigOperators Classical Matrix ComplexConjugate

variable {n : ℕ}

abbrev AddrReg (n : ℕ) := Qatlib.Foundations.PureStateMath.Reg n

structure AddrGate (n : ℕ) where

  target : Fin n

  pattern : Qatlib.Foundations.PureStateMath.Reg n
  deriving DecidableEq

def AddrGate.lo (g : AddrGate n) : Qatlib.Foundations.PureStateMath.Reg n :=
  Function.update g.pattern g.target false

def AddrGate.hi (g : AddrGate n) : Qatlib.Foundations.PureStateMath.Reg n :=
  Function.update g.pattern g.target true

def AddrGate.matches (g : AddrGate n) (x : Qatlib.Foundations.PureStateMath.Reg n) : Prop :=
  ∀ i, i ≠ g.target → x i = g.pattern i

instance (g : AddrGate n) (x : Qatlib.Foundations.PureStateMath.Reg n) : Decidable (g.matches x) :=
  Fintype.decidableForallFintype

def AddrGate.eval (g : AddrGate n) (x : Qatlib.Foundations.PureStateMath.Reg n) : Qatlib.Foundations.PureStateMath.Reg n :=
  if g.matches x then Function.update x g.target (!x g.target) else x

theorem AddrGate.matches_lo (g : AddrGate n) : g.matches g.lo := by
  intro i hi
  rw [AddrGate.lo, Function.update_of_ne hi false g.pattern]

theorem AddrGate.matches_hi (g : AddrGate n) : g.matches g.hi := by
  intro i hi
  rw [AddrGate.hi, Function.update_of_ne hi true g.pattern]

theorem AddrGate.eval_lo (g : AddrGate n) : g.eval g.lo = g.hi := by
  rw [AddrGate.eval, if_pos g.matches_lo]
  funext i
  by_cases hi : i = g.target
  · subst hi
    simp [AddrGate.lo, AddrGate.hi]
  · have h1 : g.lo i = g.pattern i := by
      rw [AddrGate.lo]
      exact Function.update_of_ne hi false g.pattern
    have h2 : g.hi i = g.pattern i := by
      rw [AddrGate.hi]
      exact Function.update_of_ne hi true g.pattern
    rw [Function.update_of_ne hi (!g.lo g.target) g.lo, h1, h2]

theorem AddrGate.eval_hi (g : AddrGate n) : g.eval g.hi = g.lo := by
  rw [AddrGate.eval, if_pos g.matches_hi]
  funext i
  by_cases hi : i = g.target
  · subst hi
    simp [AddrGate.hi, AddrGate.lo]
  · have h1 : g.lo i = g.pattern i := by
      rw [AddrGate.lo]
      exact Function.update_of_ne hi false g.pattern
    have h2 : g.hi i = g.pattern i := by
      rw [AddrGate.hi]
      exact Function.update_of_ne hi true g.pattern
    rw [Function.update_of_ne hi (!g.hi g.target) g.hi, h2, h1]

theorem AddrGate.lo_ne_hi (g : AddrGate n) : g.lo ≠ g.hi := by
  intro h
  have hz := congrArg (fun x : Qatlib.Foundations.PureStateMath.Reg n => x g.target) h
  simp [AddrGate.lo, AddrGate.hi] at hz

theorem AddrGate.eval_of_ne (g : AddrGate n) {x : Qatlib.Foundations.PureStateMath.Reg n}
    (hx : x ≠ g.lo) (hx' : x ≠ g.hi) : g.eval x = x := by
  have hn : ¬ g.matches x := by
    intro hm
    have hxupd : x = Function.update g.pattern g.target (x g.target) := by
      funext i
      by_cases hi : i = g.target
      · subst hi
        simp
      · rw [hm i hi, Function.update_of_ne hi (x g.target) g.pattern]
    cases hb : x g.target with
    | false =>
      have : x = g.lo := by
        rw [hxupd]
        simp [AddrGate.lo, hb]
      exact hx this
    | true =>
      have : x = g.hi := by
        rw [hxupd]
        simp [AddrGate.hi, hb]
      exact hx' this
  rw [AddrGate.eval, if_neg hn]

theorem AddrGate.eval_eq_swap (g : AddrGate n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    g.eval x = Equiv.swap g.lo g.hi x := by
  by_cases hx : x = g.lo
  · subst x
    rw [AddrGate.eval_lo]
    simp [Equiv.swap_apply_left]
  by_cases hx' : x = g.hi
  · subst x
    rw [AddrGate.eval_hi]
    simp [Equiv.swap_apply_right]
  rw [AddrGate.eval_of_ne g hx hx']
  exact (Equiv.swap_apply_of_ne_of_ne (a := g.lo) (b := g.hi) (x := x) hx hx').symm

noncomputable def AddrGate.matrix (g : AddrGate n) :
    Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ :=
  injectionFrame (Equiv.swap g.lo g.hi)

abbrev AddrWord (n : ℕ) := List (AddrGate n)

def AddrWord.eval : List (AddrGate n) → Qatlib.Foundations.PureStateMath.Reg n → Qatlib.Foundations.PureStateMath.Reg n
  | [], x => x
  | g :: l, x => AddrWord.eval l (g.eval x)

noncomputable def AddrWord.matrix :
    List (AddrGate n) → Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ
  | [] => 1
  | g :: l => AddrWord.matrix l * AddrGate.matrix g

theorem AddrWord.eval_append (a b : AddrWord n) :
    ∀ x : Qatlib.Foundations.PureStateMath.Reg n,
      AddrWord.eval (a ++ b) x = AddrWord.eval b (AddrWord.eval a x) := by
  induction a with
  | nil => intro x; rfl
  | cons g a ih =>
    intro x
    have h1 : AddrWord.eval ((g :: a) ++ b) x = AddrWord.eval (a ++ b) (g.eval x) := rfl
    rw [h1, ih (g.eval x)]
    rfl

theorem AddrGate.matrix_single (g : AddrGate n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    g.matrix *ᵥ Pi.single x 1 = Pi.single (g.eval x) 1 := by
  rw [AddrGate.matrix]
  ext y
  rw [injectionFrame_equiv_mulVec]
  simp only [Pi.single_apply, Equiv.symm_apply_eq, AddrGate.eval_eq_swap]

theorem AddrWord.matrix_single (w : AddrWord n) :
    ∀ x : Qatlib.Foundations.PureStateMath.Reg n,
      AddrWord.matrix w *ᵥ Pi.single x 1 = Pi.single (AddrWord.eval w x) 1 := by
  induction w with
  | nil =>
    intro x
    have h1 : (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ)
        *ᵥ Pi.single x 1 = Pi.single x 1 := Matrix.one_mulVec _
    have h2 : AddrWord.eval ([] : AddrWord n) x = x := rfl
    rw [AddrWord.matrix, h1, h2]
  | cons g l ih =>
    intro x
    have h1 : AddrWord.matrix (g :: l) = AddrWord.matrix l * AddrGate.matrix g := rfl
    rw [h1, ← Matrix.mulVec_mulVec, AddrGate.matrix_single, ih (g.eval x)]
    rfl

theorem AddrWord.matrix_append (a b : AddrWord n) :
    AddrWord.matrix (a ++ b) = AddrWord.matrix b * AddrWord.matrix a := by
  induction a with
  | nil => simp [AddrWord.matrix]
  | cons g a ih =>
    have h1 : AddrWord.matrix ((g :: a) ++ b) = AddrWord.matrix (a ++ b) * AddrGate.matrix g := rfl
    have h2 : AddrWord.matrix (g :: a) = AddrWord.matrix a * AddrGate.matrix g := rfl
    rw [h1, ih, h2]
    simp only [Matrix.mul_assoc]

theorem AddrGate.eval_injective (g : AddrGate n) : Function.Injective g.eval := by
  intro x y h
  rw [AddrGate.eval_eq_swap, AddrGate.eval_eq_swap] at h
  exact (Equiv.swap g.lo g.hi).injective h

theorem AddrWord.eval_injective (w : AddrWord n) : Function.Injective (AddrWord.eval w) := by
  induction w with
  | nil => intro a b h; exact h
  | cons g l ih =>
    intro a b h
    have h1 : g.eval a = g.eval b := ih (by
      simpa only [AddrWord.eval] using! h)
    exact (AddrGate.eval_injective g) h1

noncomputable def AddrWord.perm (w : AddrWord n) : Equiv.Perm (Qatlib.Foundations.PureStateMath.Reg n) :=
  Equiv.ofBijective (AddrWord.eval w)
    ⟨AddrWord.eval_injective w,
      (Finite.injective_iff_surjective.mp (AddrWord.eval_injective w))⟩

theorem AddrWord.perm_apply (w : AddrWord n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    AddrWord.perm w x = AddrWord.eval w x := rfl

def flipQubits (ds : List (Fin n)) (w : Qatlib.Foundations.PureStateMath.Reg n) : Qatlib.Foundations.PureStateMath.Reg n :=
  ds.foldl (fun acc d => Function.update acc d (!acc d)) w

theorem flipQubits_apply (ds : List (Fin n)) (w : Qatlib.Foundations.PureStateMath.Reg n) (hnd : ds.Nodup)
    (i : Fin n) :
    flipQubits ds w i = if i ∈ ds then !w i else w i := by
  induction ds generalizing w with
  | nil => simp [flipQubits]
  | cons d ds ih =>
    have hnd' : d ∉ ds := (List.nodup_cons.mp hnd).1
    have hnd2 : ds.Nodup := (List.nodup_cons.mp hnd).2
    by_cases hid : i = d
    · subst i
      have h := ih (w := Function.update w d (!w d)) hnd2
      simp only [hnd', if_false] at h
      rw [show flipQubits (d :: ds) w d = flipQubits ds (Function.update w d (!w d)) d from rfl, h]
      simp
    · have h := ih (w := Function.update w d (!w d)) hnd2
      rw [show flipQubits (d :: ds) w i = flipQubits ds (Function.update w d (!w d)) i from rfl, h]
      rw [Function.update_of_ne hid (!w d) w]
      simp [hid]

def diffQubits (u v : Qatlib.Foundations.PureStateMath.Reg n) : List (Fin n) :=
  (List.finRange n).filter (fun i => u i ≠ v i)

theorem mem_diffQubits {u v : Qatlib.Foundations.PureStateMath.Reg n} {i : Fin n} :
    i ∈ diffQubits u v ↔ u i ≠ v i := by
  simp [diffQubits]

theorem diffQubits_nodup (u v : Qatlib.Foundations.PureStateMath.Reg n) : (diffQubits u v).Nodup :=
  (List.nodup_finRange n).filter (fun i => u i ≠ v i)

theorem diffQubits_length_le (u v : Qatlib.Foundations.PureStateMath.Reg n) : (diffQubits u v).length ≤ n := by
  have hsub : (diffQubits u v).toFinset ⊆ (List.finRange n).toFinset := by
    intro i hi
    rw [List.mem_toFinset] at hi
    rw [List.mem_toFinset]
    exact List.mem_finRange i
  have hcard : (diffQubits u v).toFinset.card ≤ (List.finRange n).toFinset.card :=
    Finset.card_le_card hsub
  have h1 : (diffQubits u v).toFinset.card = (diffQubits u v).length :=
    List.toFinset_card_of_nodup (diffQubits_nodup u v)
  have h2 : (List.finRange n).toFinset.card = (List.finRange n).length :=
    List.toFinset_card_of_nodup (List.nodup_finRange n)
  rw [h1, h2] at hcard
  rw [List.length_finRange] at hcard
  omega

theorem diffQubits_eq_nil_iff {u v : Qatlib.Foundations.PureStateMath.Reg n} :
    diffQubits u v = [] ↔ u = v := by
  constructor
  · intro h
    funext i
    by_contra hne
    have hm : i ∈ diffQubits u v := mem_diffQubits.mpr hne
    rw [h] at hm
    simp at hm
  · intro h
    apply List.filter_eq_nil_iff.mpr
    intro i hi hpt
    have hne' : u i ≠ v i := of_decide_eq_true hpt
    have h3 : u i = v i := congrArg (fun x : Qatlib.Foundations.PureStateMath.Reg n => x i) h
    exact hne' h3

theorem flipQubits_diffQubits (u v : Qatlib.Foundations.PureStateMath.Reg n) :
    flipQubits (diffQubits u v) u = v := by
  funext i
  have h := flipQubits_apply (diffQubits u v) u (diffQubits_nodup u v) i
  simp only [mem_diffQubits] at h
  cases hu : u i <;> cases hv : v i <;> simp_all

def chainWord : List (Fin n) → Qatlib.Foundations.PureStateMath.Reg n → AddrWord n
  | [], _ => []
  | [d], w => [⟨d, w⟩]
  | d :: e :: rest, w =>
      ⟨d, w⟩ :: (chainWord (e :: rest) (Function.update w d (!w d))) ++ [⟨d, w⟩]

theorem AddrGate.swap_eq (d : Fin n) (w : Qatlib.Foundations.PureStateMath.Reg n) :
    Equiv.swap (⟨d, w⟩ : AddrGate n).lo (⟨d, w⟩ : AddrGate n).hi
      = Equiv.swap w (Function.update w d (!w d)) := by
  by_cases hd : w d = false
  · have h1 : (⟨d, w⟩ : AddrGate n).lo = w := by
      funext i
      by_cases hi : i = d
      · subst hi
        simp [AddrGate.lo, hd]
      · rw [AddrGate.lo, Function.update_of_ne hi false w]
    have h2 : (⟨d, w⟩ : AddrGate n).hi = Function.update w d true := by
      funext i
      by_cases hi : i = d
      · subst hi
        simp [AddrGate.hi]
      · rw [AddrGate.hi, Function.update_of_ne hi true w]
    have h3 : Function.update w d (!w d) = Function.update w d true := by
      funext i
      by_cases hi : i = d
      · subst hi
        simp [hd]
      · rw [Function.update_of_ne hi (!w d) w, Function.update_of_ne hi true w]
    rw [h1, h2, h3]
  · have hdt : w d = true := Bool.eq_true_of_not_eq_false hd
    have h1 : (⟨d, w⟩ : AddrGate n).lo = Function.update w d false := by
      funext i
      by_cases hi : i = d
      · subst hi
        simp [AddrGate.lo]
      · rw [AddrGate.lo, Function.update_of_ne hi false w]
    have h2 : (⟨d, w⟩ : AddrGate n).hi = w := by
      funext i
      by_cases hi : i = d
      · subst hi
        simp [AddrGate.hi, hdt]
      · rw [AddrGate.hi, Function.update_of_ne hi true w]
    have h3 : Function.update w d (!w d) = Function.update w d false := by
      funext i
      by_cases hi : i = d
      · subst hi
        simp [hdt]
      · rw [Function.update_of_ne hi (!w d) w, Function.update_of_ne hi false w]
    rw [h1, h2, h3, Equiv.swap_comm]

theorem swap_conj (u w v : Qatlib.Foundations.PureStateMath.Reg n) (huw : u ≠ w) (hwv : w ≠ v)
    (huv : u ≠ v) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Equiv.swap u w (Equiv.swap w v (Equiv.swap u w x)) = Equiv.swap u v x := by
  have hwu : w ≠ u := Ne.symm huw
  have hvw : v ≠ w := Ne.symm hwv
  have hvu : v ≠ u := Ne.symm huv
  by_cases hx : x = u
  · subst x
    have h1 : Equiv.swap u w v = v :=
        Equiv.swap_apply_of_ne_of_ne (a := u) (b := w) (x := v) hvu hvw
    have h2 : Equiv.swap w v w = v := Equiv.swap_apply_left w v
    have h3 : Equiv.swap u w u = w := Equiv.swap_apply_left u w
    have h4 : Equiv.swap u v u = v := Equiv.swap_apply_left u v
    rw [h3, h2, h1, h4]
  by_cases hx' : x = v
  · subst x
    have h1 : Equiv.swap u w v = v :=
        Equiv.swap_apply_of_ne_of_ne (a := u) (b := w) (x := v) hvu hvw
    have h5 : Equiv.swap w v v = w := Equiv.swap_apply_right w v
    have h6 : Equiv.swap u w w = u := Equiv.swap_apply_right u w
    have h7 : Equiv.swap u v v = u := Equiv.swap_apply_right u v
    rw [h1, h5, h6, h7]
  by_cases hxw : x = w
  · subst x
    have h3 : Equiv.swap u w u = w := Equiv.swap_apply_left u w
    have h6 : Equiv.swap u w w = u := Equiv.swap_apply_right u w
    have h8 : Equiv.swap w v u = u :=
        Equiv.swap_apply_of_ne_of_ne (a := w) (b := v) (x := u) huw huv
    have h9 : Equiv.swap u v w = w :=
        Equiv.swap_apply_of_ne_of_ne (a := u) (b := v) (x := w) hwu hwv
    rw [h6, h8, h3, h9]
  · have h10 : Equiv.swap u w x = x := Equiv.swap_apply_of_ne_of_ne (a := u) (b := w) (x := x) hx hxw
    have h11 : Equiv.swap w v x = x :=
        Equiv.swap_apply_of_ne_of_ne (a := w) (b := v) (x := x) hxw hx'
    have h12 : Equiv.swap u v x = x :=
        Equiv.swap_apply_of_ne_of_ne (a := u) (b := v) (x := x) hx hx'
    simp only [h10, h11, h12]

theorem chainWord_eval : ∀ (ds : List (Fin n)) (w : Qatlib.Foundations.PureStateMath.Reg n),
    ∀ (_hnd : ds.Nodup) (x : Qatlib.Foundations.PureStateMath.Reg n),
      AddrWord.eval (chainWord ds w) x = Equiv.swap w (flipQubits ds w) x := by
  intro ds
  induction ds with
  | nil =>
    intro w _ x
    have h1 : AddrWord.eval (chainWord ([] : List (Fin n)) w) x = x := rfl
    have h2 : flipQubits ([] : List (Fin n)) w = w := rfl
    have h3 : Equiv.swap w w x = x := by simp
    rw [h1, h2, h3]
  | cons d ds ih =>
    intro w hnd x
    cases ds with
    | nil =>
      rw [show chainWord [d] w = [⟨d, w⟩] from rfl]
      simp only [AddrWord.eval]
      have hfl : flipQubits [d] w = Function.update w d (!w d) := by
        simp [flipQubits]
      have hgate : ∀ y : Qatlib.Foundations.PureStateMath.Reg n,
          (⟨d, w⟩ : AddrGate n).eval y = Equiv.swap w (Function.update w d (!w d)) y := by
        intro y
        rw [AddrGate.eval_eq_swap, AddrGate.swap_eq]
      rw [hfl, hgate]
    | cons e rest =>
      have hnd' : d ∉ e :: rest := (List.nodup_cons.mp hnd).1
      have hnd2 : (e :: rest).Nodup := (List.nodup_cons.mp hnd).2
      have hne1 : w ≠ Function.update w d (!w d) := by
        intro h
        have hz := congrArg (fun x : Qatlib.Foundations.PureStateMath.Reg n => x d) h
        simp [Function.update_self] at hz
      have hne2 : Function.update w d (!w d)
          ≠ flipQubits (e :: rest) (Function.update w d (!w d)) := by
        intro h
        have hz : (Function.update w d (!w d)) e
            = flipQubits (e :: rest) (Function.update w d (!w d)) e :=
          congrArg (fun x : Qatlib.Foundations.PureStateMath.Reg n => x e) h
        have he := flipQubits_apply (e :: rest) (Function.update w d (!w d)) hnd2 e
        simp only [List.mem_cons_self, if_true] at he
        rw [he] at hz
        cases hA : (Function.update w d (!w d)) e <;> simp at hz
      have hne3 : w ≠ flipQubits (e :: rest) (Function.update w d (!w d)) := by
        intro h
        have hz : w d = flipQubits (e :: rest) (Function.update w d (!w d)) d :=
          congrArg (fun x : Qatlib.Foundations.PureStateMath.Reg n => x d) h
        have hd' := flipQubits_apply (e :: rest) (Function.update w d (!w d)) hnd2 d
        simp only [hnd', if_false] at hd'
        rw [hd'] at hz
        simp [Function.update_self] at hz
      have hstep : flipQubits (d :: e :: rest) w
          = flipQubits (e :: rest) (Function.update w d (!w d)) := by
        simp only [flipQubits, List.foldl_cons]
      have hgate : ∀ y : Qatlib.Foundations.PureStateMath.Reg n,
          (⟨d, w⟩ : AddrGate n).eval y = Equiv.swap w (Function.update w d (!w d)) y := by
        intro y
        rw [AddrGate.eval_eq_swap, AddrGate.swap_eq]
      have hrec := ih (w := Function.update w d (!w d)) hnd2
        (Equiv.swap w (Function.update w d (!w d)) x)
      rw [show chainWord (d :: e :: rest) w
          = ⟨d, w⟩ :: (chainWord (e :: rest) (Function.update w d (!w d))) ++ [⟨d, w⟩] from rfl]
      simp only [AddrWord.eval, List.cons_append]
      rw [AddrWord.eval_append]
      simp only [AddrWord.eval]
      simp only [hgate, hrec]
      rw [hstep]
      exact swap_conj w (Function.update w d (!w d))
        (flipQubits (e :: rest) (Function.update w d (!w d))) hne1 hne2 hne3 x

def transpositionWord (u v : Qatlib.Foundations.PureStateMath.Reg n) : AddrWord n :=
  chainWord (diffQubits u v) u

theorem transpositionWord_eval (u v : Qatlib.Foundations.PureStateMath.Reg n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    AddrWord.eval (transpositionWord u v) x = Equiv.swap u v x := by
  rw [transpositionWord, chainWord_eval (diffQubits u v) u (diffQubits_nodup u v) x]
  rw [flipQubits_diffQubits]

theorem transpositionWord_matrix (u v : Qatlib.Foundations.PureStateMath.Reg n) :
    AddrWord.matrix (transpositionWord u v) = swapWordMatrix [(u, v)] := by
  apply Matrix.ext_of_mulVec_single
  intro x
  rw [AddrWord.matrix_single, transpositionWord_eval, swapWordMatrix_single]
  rfl

theorem chainWord_length (ds : List (Fin n)) (w : Qatlib.Foundations.PureStateMath.Reg n) (hne : ds ≠ []) :
    (chainWord ds w).length = 2 * ds.length - 1 := by
  induction ds generalizing w with
  | nil => simp at hne
  | cons d ds ih =>
    cases ds with
    | nil => simp [chainWord]
    | cons e rest =>
      have hne' : e :: rest ≠ [] := by simp
      simp only [chainWord, List.length_append, List.length_cons, List.length_nil]
      rw [ih (w := Function.update w d (!w d)) hne']
      simp only [List.length_cons]
      omega

theorem transpositionWord_length (u v : Qatlib.Foundations.PureStateMath.Reg n) (hne : u ≠ v) :
    (transpositionWord u v).length = 2 * (diffQubits u v).length - 1 := by
  rw [transpositionWord, chainWord_length _ _ (by
    intro h
    exact hne (diffQubits_eq_nil_iff.mp h))]

theorem transpositionWord_length_le (u v : Qatlib.Foundations.PureStateMath.Reg n) (hne : u ≠ v) :
    (transpositionWord u v).length ≤ 2 * n - 1 := by
  rw [transpositionWord_length u v hne]
  have := diffQubits_length_le u v
  omega

def AddrWord.amp (w : AddrWord n) (x y : Qatlib.Foundations.PureStateMath.Reg n) : ℂ :=
  if AddrWord.eval w x = y then 1 else 0

theorem AddrWord.amp_zero_or_one (w : AddrWord n) (x y : Qatlib.Foundations.PureStateMath.Reg n) :
    AddrWord.amp w x y = 0 ∨ AddrWord.amp w x y = 1 := by
  unfold AddrWord.amp
  split <;> simp

theorem AddrWord.amp_eq_one_iff (w : AddrWord n) (x y : Qatlib.Foundations.PureStateMath.Reg n) :
    AddrWord.amp w x y = 1 ↔ AddrWord.eval w x = y := by
  unfold AddrWord.amp
  by_cases h : AddrWord.eval w x = y
  · simp [h]
  · simp [h]

theorem AddrWord.amp_eq_zero_iff (w : AddrWord n) (x y : Qatlib.Foundations.PureStateMath.Reg n) :
    AddrWord.amp w x y = 0 ↔ AddrWord.eval w x ≠ y := by
  unfold AddrWord.amp
  by_cases h : AddrWord.eval w x = y
  · simp [h]
  · simp [h]

theorem AddrWord.amp_eq_one_of_eq (w : AddrWord n) (x y : Qatlib.Foundations.PureStateMath.Reg n)
    (h : AddrWord.eval w x = y) : AddrWord.amp w x y = 1 := by
  unfold AddrWord.amp
  rw [if_pos h]

theorem AddrWord.amp_eq_zero_of_ne (w : AddrWord n) (x y : Qatlib.Foundations.PureStateMath.Reg n)
    (h : AddrWord.eval w x ≠ y) : AddrWord.amp w x y = 0 := by
  unfold AddrWord.amp
  rw [if_neg h]

theorem AddrWord.matrix_entry (w : AddrWord n) (x y : Qatlib.Foundations.PureStateMath.Reg n) :
    AddrWord.matrix w y x = AddrWord.amp w x y := by
  have h := congrFun (AddrWord.matrix_single w x) y
  rw [Pi.single_apply] at h
  rw [Matrix.mulVec] at h
  have hdot : (fun j => AddrWord.matrix w y j) ⬝ᵥ Pi.single x 1
      = AddrWord.matrix w y x := by
    simp only [dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero]
    exact Fintype.sum_ite_eq' x (fun j => AddrWord.matrix w y j)
  rw [hdot] at h
  unfold AddrWord.amp
  by_cases hc : AddrWord.eval w x = y
  · rw [if_pos hc]
    simp [hc] at h
    exact h
  · rw [if_neg hc]
    simp [Ne.symm hc] at h
    exact h

theorem AddrWord.matrix_eq_injectionFrame (w : AddrWord n) :
    AddrWord.matrix w = injectionFrame (AddrWord.perm w) := by
  apply Matrix.ext
  intro x y
  rw [injectionFrame, AddrWord.perm_apply]
  rw [AddrWord.matrix_entry w y x]
  unfold AddrWord.amp
  by_cases hc : AddrWord.eval w y = x
  · rw [if_pos hc, if_pos hc.symm]
  · rw [if_neg hc, if_neg (Ne.symm hc)]

noncomputable def AddrWord.ampVec (w : AddrWord n) (ψ : Qatlib.Foundations.PureStateMath.Reg n → ℂ) :
    Qatlib.Foundations.PureStateMath.Reg n → ℂ :=
  fun y => ∑ x, AddrWord.amp w x y * ψ x

theorem AddrWord.mulVec_eq_ampVec (w : AddrWord n) (ψ : Qatlib.Foundations.PureStateMath.Reg n → ℂ) :
    AddrWord.matrix w *ᵥ ψ = AddrWord.ampVec w ψ := by
  funext y
  rw [Matrix.mulVec, AddrWord.ampVec]
  apply Finset.sum_congr rfl
  intro x _
  simp only [AddrWord.matrix_entry]

theorem AddrWord.mulVec_apply (w : AddrWord n) (ψ : Qatlib.Foundations.PureStateMath.Reg n → ℂ)
    (y : Qatlib.Foundations.PureStateMath.Reg n) :
    (AddrWord.matrix w *ᵥ ψ) y = ψ ((AddrWord.perm w).symm y) := by
  rw [AddrWord.matrix_eq_injectionFrame, injectionFrame_equiv_mulVec]

def moveToQtm : Move → QtmMove
  | .left => .left
  | .stay => .stay
  | .right => .right

def qtmMoveToMove : QtmMove → Move
  | .left => .left
  | .stay => .stay
  | .right => .right

theorem moveToQtm_qtmMoveToMove (m : Move) : (qtmMoveToMove (moveToQtm m)) = m := by
  cases m <;> rfl

theorem qtmMoveToMove_moveToQtm (d : QtmMove) : (moveToQtm (qtmMoveToMove d)) = d := by
  cases d <;> rfl

theorem qtmMove_sum_univ {M : Type*} [AddCommMonoid M] (f : QtmMove → M) :
    ∑ d : QtmMove, f d = f .left + f .stay + f .right := by
  have hu : (Finset.univ : Finset QtmMove) = {.left, .stay, .right} := by decide
  rw [hu]
  simp [add_assoc]

theorem sum_move_eq_sum_qtm {M : Type*} [AddCommMonoid M] (F : Move → M) :
    (∑ m : Move, F m) = ∑ d : QtmMove, F (qtmMoveToMove d) := by
  have h1 := Move.sum_univ F
  have h2 := qtmMove_sum_univ (fun d => F (qtmMoveToMove d))
  rw [h1, h2]
  rfl

theorem sum_comm3 {Q A D M : Type*} [Fintype Q] [Fintype A] [Fintype D]
    [AddCommMonoid M] (X : D → Q → A → M) :
    (∑ q' : Q, ∑ b : A, ∑ d : D, X d q' b) = ∑ d : D, ∑ q' : Q, ∑ b : A, X d q' b := by
  have h1 : (∑ q' : Q, ∑ b : A, ∑ d : D, X d q' b)
      = ∑ q' : Q, ∑ d : D, ∑ b : A, X d q' b := by
    apply Finset.sum_congr rfl
    intro q' _
    exact Finset.sum_comm
  have h2 : (∑ q' : Q, ∑ d : D, ∑ b : A, X d q' b)
      = ∑ d : D, ∑ q' : Q, ∑ b : A, X d q' b := by
    symm
    exact Finset.sum_comm
  exact h1.trans h2

def qtmStep {Q A : Type*} (R : Rule Q A) : Q → A → QtmMove → Q → A → ℂ :=
  fun q a d q' b => R.amplitude q a (qtmMoveToMove d) q' b

def stayFree {Q A : Type*} (R : Rule Q A) : Prop :=
  ∀ q a q' b, R.amplitude q a Move.stay q' b = 0

theorem qtm_norm_of_global {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (q : Q) (a : A) :
    ∑ q' : Q, ∑ b : A, ∑ d : QtmMove, ‖qtmStep R q a d q' b‖ ^ 2 = 1 := by
  have hconv : (∑ t : Move × Q × A, ‖R.amplitude q a t.1 t.2.1 t.2.2‖ ^ 2)
      = ∑ m : Move, ∑ q' : Q, ∑ b : A, ‖R.amplitude q a m q' b‖ ^ 2 := by
    simp_rw [Fintype.sum_prod_type]
  calc
    (∑ q' : Q, ∑ b : A, ∑ d : QtmMove, ‖qtmStep R q a d q' b‖ ^ 2)
        = ∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
            ‖R.amplitude q a (qtmMoveToMove d) q' b‖ ^ 2 := by
          simp only [qtmStep]
          exact sum_comm3 _
    _ = ∑ m : Move, ∑ q' : Q, ∑ b : A, ‖R.amplitude q a m q' b‖ ^ 2 := by
          rw [sum_move_eq_sum_qtm]
    _ = 1 := by rw [← hconv]; exact R.local_norm_of_global h q a

theorem qtm_sameCell_of_global {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (q₁ q₂ : Q) (a₁ a₂ : A) (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    ∑ q' : Q, ∑ b : A, ∑ d : QtmMove,
      star (qtmStep R q₁ a₁ d q' b) * qtmStep R q₂ a₂ d q' b = 0 := by
  have hconv : (∑ t : Move × Q × A,
      star (R.amplitude q₁ a₁ t.1 t.2.1 t.2.2) * R.amplitude q₂ a₂ t.1 t.2.1 t.2.2)
      = (∑ m : Move, ∑ q' : Q, ∑ b : A,
        star (R.amplitude q₁ a₁ m q' b) * R.amplitude q₂ a₂ m q' b) := by
    simp_rw [Fintype.sum_prod_type]
  calc
    (∑ q' : Q, ∑ b : A, ∑ d : QtmMove,
        star (qtmStep R q₁ a₁ d q' b) * qtmStep R q₂ a₂ d q' b)
        = ∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
            star (R.amplitude q₁ a₁ (qtmMoveToMove d) q' b)
              * R.amplitude q₂ a₂ (qtmMoveToMove d) q' b := by
          simp only [qtmStep]
          exact sum_comm3 _
    _ = ∑ m : Move, ∑ q' : Q, ∑ b : A,
            star (R.amplitude q₁ a₁ m q' b) * R.amplitude q₂ a₂ m q' b := by
          rw [sum_move_eq_sum_qtm]
    _ = 0 := by rw [← hconv]; exact R.local_sameCell_of_global h q₁ q₂ a₁ a₂ hne

theorem qtm_rightLeft_of_global {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (q₁ q₂ : Q) (a₁ a₂ : A) (c d : A) :
    ∑ q' : Q, qtmStep R q₁ a₁ QtmMove.right q' c * star (qtmStep R q₂ a₂ QtmMove.left q' d) = 0 := by
  have hnat : (∑ q' : Q, R.amplitude q₁ a₁ Move.right q' c
      * star (R.amplitude q₂ a₂ Move.left q' d)) = 0 :=
    R.local_rightLeft_of_global h q₁ q₂ a₁ a₂ c d
  simpa only [qtmStep, qtmMoveToMove] using! hnat

def toLocalQTM {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (R : Rule Q A) (q0 : Q) (hs : stayFree R) (hw : R.GloballyWellformed) : LocalQTM Q A where
  blank := R.blank
  start := q0
  step := qtmStep R
  wf_norm := by
    intro q a
    exact qtm_norm_of_global R hw q a
  wf_sameCell := by
    intro q₁ a₁ q₂ a₂ hne
    exact qtm_sameCell_of_global R hw q₁ q₂ a₁ a₂ hne
  wf_rightStay := by
    intro q₁ a₁ q₂ a₂ c d
    apply Finset.sum_eq_zero
    intro q' _
    simp only [qtmStep, qtmMoveToMove]
    rw [hs q₂ a₂ q' d]
    simp only [star_zero, mul_zero, eq_self]
  wf_stayLeft := by
    intro q₁ a₁ q₂ a₂ c d
    apply Finset.sum_eq_zero
    intro q' _
    simp only [qtmStep, qtmMoveToMove]
    rw [hs q₁ a₁ q' c]
    simp only [zero_mul, eq_self]
  wf_rightLeft := by
    intro q₁ a₁ q₂ a₂ c d
    exact qtm_rightLeft_of_global R hw q₁ q₂ a₁ a₂ c d

inductive OracleAccess where

  | inputAccess

  | labelCompare

  | recordAccess
  deriving DecidableEq, Fintype

structure OracleTariff where

  inputFee : ℝ

  labelFee : ℝ

  recordFee : ℝ

def OracleTariff.total (t : OracleTariff) : ℝ :=
  t.inputFee + t.labelFee + t.recordFee

structure OracleRequest (Q A : Type*) where

  address : ℤ

  label : Q

  record : A
  deriving DecidableEq

def windowOracleRequest {t : ℕ} {Q A : Type*} (c : WindowCfg t Q A) : OracleRequest Q A :=
  ⟨(c.head : ℕ), c.state, c.tape c.head⟩

def toOracleQTM {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (M : LocalQTM Q A) (q : Q) (ans : A → A) : OracleQTM Q A where
  machine := M
  queryStates := {q}
  oracleAnswer := ans

end Qatlib.Concepts.UniformBqp.Phi3Compile
