/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Qatlib.Concepts.WalkFind.QRAMModel.OrdinaryGateQRAMFallbackQuan
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fintype

/-!
# Finite permutation families and reversible implementations

This module defines additive Feistel permutations, proves an obstruction to approximate
independence for two rounds on two binary coordinates, and constructs finite reversible
implementations of Boolean truth tables and arbitrary finite permutations. The circuit
terminology follows [NielsenChuang2010].

`allPermutationFamily` enumerates every permutation, giving exact tuple probabilities and
approximate independence at every requested order.
`efficientPermutationFamily_fullIndependence_endpoint` combines this enumeration with canonical
binary encodings and explicit bounds on seed size, register width, and implementation length.

## Main statements

* `twoRoundFeistel_not_approxIndependent`: the two-round binary obstruction.
* `canonicalFinitePermutation_clog_words`: exact forward and inverse implementations of any
  finite permutation.
* `efficientPermutationFamily_fullIndependence_endpoint`: a permutation family with full-order
  independence and explicit resource bounds.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.WalkFind.QRAMModel

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.SearchAlgorithm

/-- The additive Feistel permutation sending `(x, y)` to `(y, x + f y)`. -/
def additiveFeistelRound {K : Type*} [AddGroup K] (f : K → K) : Equiv.Perm (K × K) where
  toFun z := (z.2, z.1 + f z.2)
  invFun z := (z.2 - f z.1, z.1)
  left_inv z := by simp
  right_inv z := by simp

/-- The inverse additive Feistel round sends `z` to `(z.2 - f z.1, z.1)`. -/
theorem additiveFeistelRound_symm_apply {K : Type*} [AddGroup K]
    (f : K → K) (z : K × K) :
    (additiveFeistelRound f).symm z = (z.2 - f z.1, z.1) := rfl

/-- The permutation obtained by applying the additive Feistel rounds for `f` and then `g`. -/
def twoRoundFeistel {K : Type*} [AddGroup K] (f g : K → K) : Equiv.Perm (K × K) :=
  (additiveFeistelRound f).trans (additiveFeistelRound g)

/-- Two distinct inputs with the same right coordinate have distinct first output coordinates
after two Feistel rounds. -/
theorem twoRoundFeistel_sharedRight_obstruction {K : Type*} [AddGroup K]
    (f g : K → K) (x x' y : K) (hxx' : x ≠ x') :
    (twoRoundFeistel f g (x,y)).1 ≠ (twoRoundFeistel f g (x',y)).1 := by
  change x + f y ≠ x' + f y
  exact fun h => hxx' (add_right_cancel h)

/-- Two inputs with distinct left coordinates and a common right coordinate cannot both map to
outputs with the same first coordinate under two Feistel rounds. -/
theorem twoRoundFeistel_impossibleAssignment {K : Type*} [AddGroup K]
    (f g : K → K) (x x' y u v v' : K) (hxx' : x ≠ x') :
    ¬(twoRoundFeistel f g (x,y) = (u,v) ∧
      twoRoundFeistel f g (x',y) = (u,v')) := by
  rintro ⟨hfirst, hsecond⟩
  apply twoRoundFeistel_sharedRight_obstruction f g x x' y hxx'
  rw [hfirst, hsecond]

/-- The composition of three additive Feistel rounds with round functions `f`, `g`, and `h`, in
that order. -/
def threeRoundFeistel {K : Type*} [AddGroup K] (f g h : K → K) : Equiv.Perm (K × K) :=
  ((additiveFeistelRound f).trans (additiveFeistelRound g)).trans (additiveFeistelRound h)

/-- The explicit forward coordinate formula for three additive Feistel rounds. -/
theorem threeRoundFeistel_apply {K : Type*} [AddGroup K]
    (f g h : K → K) (x y : K) :
    threeRoundFeistel f g h (x,y) =
      (y + g (x + f y), x + f y + h (y + g (x + f y))) := rfl

/-- The explicit inverse coordinate formula for three additive Feistel rounds. -/
theorem threeRoundFeistel_symm_apply {K : Type*} [AddGroup K]
    (f g h : K → K) (u v : K) :
    (threeRoundFeistel f g h).symm (u,v) =
      (v - h u - f (u - g (v - h u)), u - g (v - h u)) := rfl

/-- The three-round Feistel permutation transported to `Fin q` through the equivalence
`encoding`. -/
def encodedThreeRoundFeistel {K : Type*} [AddGroup K] {q : ℕ}
    (encoding : Fin q ≃ K × K) (f g h : K → K) : Equiv.Perm (Fin q) :=
  (encoding.trans (threeRoundFeistel f g h)).trans encoding.symm

/-- Encoding the output of the transported permutation agrees with applying the three-round
Feistel permutation to the encoded input. -/
theorem encodedThreeRoundFeistel_forward {K : Type*} [AddGroup K] {q : ℕ}
    (encoding : Fin q ≃ K × K) (f g h : K → K) (i : Fin q) :
    encoding (encodedThreeRoundFeistel encoding f g h i) =
      threeRoundFeistel f g h (encoding i) := by
  simp [encodedThreeRoundFeistel]

/-- Encoding the output of the inverse transported permutation agrees with applying the inverse
three-round Feistel permutation to the encoded input. -/
theorem encodedThreeRoundFeistel_inverse {K : Type*} [AddGroup K] {q : ℕ}
    (encoding : Fin q ≃ K × K) (f g h : K → K) (i : Fin q) :
    encoding ((encodedThreeRoundFeistel encoding f g h).symm i) =
      (threeRoundFeistel f g h).symm (encoding i) := by
  simp [encodedThreeRoundFeistel]

/-- No family of two-round Feistel permutations on two binary coordinates satisfies
`ApproxIndependent 2 (1/2)` after transport through `encoding`. -/
theorem twoRoundFeistel_not_approxIndependent {R : ℕ}
    (encoding : Fin 4 ≃ ZMod 2 × ZMod 2)
    (f g : Fin R → ZMod 2 → ZMod 2) :
    ¬ApproxIndependent 2 (1/2) (fun s =>
      (encoding.trans (twoRoundFeistel (f s) (g s))).trans encoding.symm) := by
  classical
  let inputs : Fin 2 → Fin 4 := ![encoding.symm (0,0), encoding.symm (1,0)]
  let outputs : Fin 2 → Fin 4 := ![encoding.symm (0,0), encoding.symm (0,1)]
  have hi : Function.Injective inputs := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [inputs] at hab ⊢
  have hj : Function.Injective outputs := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [outputs] at hab ⊢
  intro happrox
  have hbound := (happrox 2 (by omega) (by omega) inputs outputs hi hj).1
  have himpossible (s : Fin R) :
      ¬∀ z, ((encoding.trans (twoRoundFeistel (f s) (g s))).trans encoding.symm)
        (inputs z) = outputs z := by
    intro h
    have hfirst := congrArg encoding (h 0)
    have hsecond := congrArg encoding (h 1)
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, inputs, outputs,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hfirst hsecond
    exact twoRoundFeistel_impossibleAssignment (f s) (g s)
      (0 : ZMod 2) 1 0 0 0 1 (by decide) ⟨hfirst, hsecond⟩
  have hprobability : eventProbability (fun s => ∀ z,
      ((encoding.trans (twoRoundFeistel (f s) (g s))).trans encoding.symm)
        (inputs z) = outputs z) = 0 := by
    unfold eventProbability
    simp only [himpossible, Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div]
  rw [hprobability] at hbound
  norm_num [Nat.descFactorial] at hbound

noncomputable section
open scoped Classical

/-- The `m`-bit pattern obtained by reading the register `x` at the control locations `c 0, …, c
(m - 1)`. -/
def finiteControlPattern {N : ℕ} (c : ℕ → Fin N) (m : ℕ) (x : Reg N) : Reg m :=
  fun i => x (c i.val)

/-- Updating a location disjoint from the first `m` controls leaves the extracted control
pattern unchanged. -/
theorem finiteControlPattern_update {N : ℕ} (c : ℕ → Fin N) (m : ℕ)
    (t : Fin N) (hct : ∀ i < m, c i ≠ t) (x : Reg N) (v : Bool) :
    finiteControlPattern c m (Function.update x t v) = finiteControlPattern c m x := by
  ext i
  exact Function.update_of_ne (hct i.val i.isLt) _ _

/-- Distinct control and workspace locations support a legal finite gate word that flips the
target exactly when the control pattern belongs to `patterns`. Its length is at most
`patterns.length * (62 * m + 1)`. -/
theorem finitePatternListX_word {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (m : ℕ)
    (hc : Set.InjOn c (Set.Iio m)) (hw : Set.InjOn w (Set.Iio (m-2)))
    (hcw : ∀ i < m, ∀ j < m-2, c i ≠ w j)
    (hct : ∀ i < m, c i ≠ t) (hwt : ∀ j < m-2, w j ≠ t)
    (patterns : List (Reg m)) (hnodup : patterns.Nodup) :
    ∃ word : List FiniteGateCode, finiteWordLegal N word = true ∧
      word.length ≤ patterns.length*(62*m+1) ∧
      ∀ x : Reg N, Run 1 (finiteCodeCircuit N word) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ decide (finiteControlPattern c m x ∈ patterns))) := by
  induction patterns with
  | nil =>
    refine ⟨[], rfl, by simp, ?_⟩
    intro x
    simp [finiteCodeCircuit]
  | cons pattern patterns ih =>
    obtain ⟨hp, hn⟩ := List.nodup_cons.mp hnodup
    obtain ⟨first, hfirst, hfirstlen, hfirstsem⟩ :=
      finitePatternX_word c w t m pattern hc hw hcw hct hwt
    obtain ⟨rest, hrest, hrestlen, hrestsem⟩ := ih hn
    refine ⟨first++rest, ?_, ?_, ?_⟩
    · simp only [finiteWordLegal, List.all_append, Bool.and_eq_true]
      exact ⟨hfirst, hrest⟩
    · simp only [List.length_append, List.length_cons]
      rw [Nat.add_mul]
      omega
    · intro x
      have hflag : decide (∀ i : Fin m, x (c i.val) = pattern i) =
          decide (finiteControlPattern c m x = pattern) := by
        congr 1
        exact propext funext_iff.symm
      simp only [finiteCodeCircuit, List.map_append, run_append]
      change Run 1 (finiteCodeCircuit N rest)
        (Run 1 (finiteCodeCircuit N first) (Qatlib.Foundations.PureStateMath.Ket x)) = _
      rw [hfirstsem, hrestsem, finiteControlPattern_update c m t hct, hflag]
      congr 1
      rw [Function.update_self, Function.update_idem]
      by_cases hx : finiteControlPattern c m x = pattern
      · simp [hx, hp]
      · simp [hx]

/-- A Boolean function of `m` control bits can be XORed into a disjoint target by a legal finite
gate word of length at most `2^m * (62 * m + 1)`, using the specified disjoint workspace. -/
theorem finiteTruthTableX_word {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (m : ℕ)
    (hc : Set.InjOn c (Set.Iio m)) (hw : Set.InjOn w (Set.Iio (m-2)))
    (hcw : ∀ i < m, ∀ j < m-2, c i ≠ w j)
    (hct : ∀ i < m, c i ≠ t) (hwt : ∀ j < m-2, w j ≠ t)
    (f : Reg m → Bool) :
    ∃ word : List FiniteGateCode, finiteWordLegal N word = true ∧
      word.length ≤ 2^m*(62*m+1) ∧
      ∀ x : Reg N, Run 1 (finiteCodeCircuit N word) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ f (finiteControlPattern c m x))) := by
  let patterns := (Finset.univ.filter (fun p : Reg m => f p = true)).toList
  obtain ⟨word, hword, hlength, hsem⟩ := finitePatternListX_word c w t m hc hw hcw hct hwt
    patterns (Finset.nodup_toList _)
  refine ⟨word, hword, ?_, ?_⟩
  · apply hlength.trans
    apply Nat.mul_le_mul_right
    dsimp only [patterns]
    rw [Finset.length_toList]
    exact (Finset.card_filter_le _ _).trans (by simp [Reg])
  · intro x
    rw [hsem]
    congr 2
    apply Bool.eq_iff_iff.mpr
    simp [patterns]

/-- The register update assigning `x t ^^ f (x c)` to location `c` and `x c` to location `t`. -/
def booleanFeistelAction {N : ℕ} (c t : Fin N) (f : Bool → Bool) (x : Reg N) : Reg N :=
  Function.update (Function.update x c (x t ^^ f (x c))) t (x c)

/-- The reverse register update assigning `x c ^^ f (x t)` to location `t` and `x t` to location
`c`. -/
def booleanFeistelInverse {N : ℕ} (c t : Fin N) (f : Bool → Bool) (x : Reg N) : Reg N :=
  Function.update (Function.update x t (x c ^^ f (x t))) c (x t)

/-- On distinct locations `c` and `t`, `booleanFeistelInverse` is a left inverse of
`booleanFeistelAction`. -/
theorem booleanFeistel_leftInverse {N : ℕ} (c t : Fin N) (hct : c ≠ t)
    (f : Bool → Bool) : Function.LeftInverse
      (booleanFeistelInverse c t f) (booleanFeistelAction c t f) := by
  intro x
  ext j
  by_cases hjc : j = c
  · subst j
    simp [booleanFeistelAction, booleanFeistelInverse, hct]
  · by_cases hjt : j = t
    · subst j
      simp [booleanFeistelAction, booleanFeistelInverse, hct, hct.symm]
    · simp [booleanFeistelAction, booleanFeistelInverse, hjc, hjt]

/-- On distinct locations `c` and `t`, `booleanFeistelInverse` is a right inverse of
`booleanFeistelAction`. -/
theorem booleanFeistel_rightInverse {N : ℕ} (c t : Fin N) (hct : c ≠ t)
    (f : Bool → Bool) : Function.RightInverse
      (booleanFeistelInverse c t f) (booleanFeistelAction c t f) := by
  intro x
  ext j
  by_cases hjc : j = c
  · subst j
    simp [booleanFeistelAction, booleanFeistelInverse, hct, hct.symm]
  · by_cases hjt : j = t
    · subst j
      simp [booleanFeistelAction, booleanFeistelInverse, hct.symm]
    · simp [booleanFeistelAction, booleanFeistelInverse, hjc, hjt]

/-- A Boolean Feistel update on distinct locations has an exact legal finite gate implementation
of length at most `315` on computational basis states. -/
theorem booleanFeistel_word {N : ℕ} (c t : Fin N) (hct : c ≠ t) (f : Bool → Bool) :
    ∃ word : List FiniteGateCode, finiteWordLegal N word = true ∧ word.length ≤ 315 ∧
      ∀ x : Reg N, Run 1 (finiteCodeCircuit N word) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (booleanFeistelAction c t f x) := by
  obtain ⟨toggle, htoggle, htogglelen, htogglesem⟩ :=
    finiteTruthTableX_word (fun _ => c) (fun _ => c) t 1
      (by intro i hi j hj _; change i < 1 at hi; change j < 1 at hj; omega)
      (by intro i hi; simp at hi)
      (by intro i hi j hj; omega)
      (by intro i hi; exact hct)
      (by intro j hj; omega)
      (fun p => f (p 0))
  obtain ⟨swap, hswap, hswaplen, hswapsem⟩ :=
    finitePatternSwap_word (fun _ => c) (fun _ => c) c t 0 (fun i => i.elim0)
      (by intro i hi; simp at hi) (by intro i hi; simp at hi)
      (by intro i hi; omega) (by intro i hi; omega) (by intro i hi; omega)
      (by intro j hj; omega) (by intro j hj; omega) hct
  refine ⟨toggle++swap, ?_, ?_, ?_⟩
  · simp only [finiteWordLegal, List.all_append, Bool.and_eq_true]
    exact ⟨htoggle, hswap⟩
  · simp only [List.length_append] at *
    norm_num at htogglelen hswaplen
    omega
  · intro x
    simp only [finiteCodeCircuit, List.map_append, run_append]
    change Run 1 (finiteCodeCircuit N swap)
      (Run 1 (finiteCodeCircuit N toggle) (Qatlib.Foundations.PureStateMath.Ket x)) = _
    rw [htogglesem, hswapsem]
    simp only [finiteControlPattern,
      Function.update_self, IsEmpty.forall_iff, if_true, Function.update_idem]
    congr 1
    ext j
    by_cases hjc : j = c
    · subst j
      simp [booleanFeistelAction, hct]
    · by_cases hjt : j = t
      · subst j
        simp [booleanFeistelAction, hct, hct.symm]
      · simp [booleanFeistelAction, hjc, hjt]

/-- A Boolean Feistel update and its inverse have exact legal finite gate implementations whose
combined length is at most `630`. -/
theorem booleanFeistel_forward_backward_words {N : ℕ} (c t : Fin N) (hct : c ≠ t)
    (f : Bool → Bool) :
    ∃ forward backward : List FiniteGateCode,
      finiteWordLegal N forward = true ∧ finiteWordLegal N backward = true ∧
      forward.length + backward.length ≤ 630 ∧
      (∀ x : Reg N, Run 1 (finiteCodeCircuit N forward) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (booleanFeistelAction c t f x)) ∧
      (∀ x : Reg N, Run 1 (finiteCodeCircuit N backward) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (booleanFeistelInverse c t f x)) := by
  obtain ⟨word, hword, hlen, hsem⟩ := booleanFeistel_word c t hct f
  have hinverse :=
      finite_gate_word_paid_adjoint_semantics N word
      (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) hword
  refine ⟨word, finiteWordAdjoint word, hword, hinverse.1, by omega, hsem, ?_⟩
  intro x
  have hrun := (finite_gate_word_paid_adjoint_semantics N word
    (Qatlib.Foundations.PureStateMath.Ket (booleanFeistelInverse c t f x)) hword).2.2.1
  simp only [finiteCodeCircuit, List.map_append, run_append] at hrun
  change Run 1 (finiteCodeCircuit N (finiteWordAdjoint word))
    (Run 1 (finiteCodeCircuit N word) (Qatlib.Foundations.PureStateMath.Ket (booleanFeistelInverse c t f x))) =
      Qatlib.Foundations.PureStateMath.Ket (booleanFeistelInverse c t f x) at hrun
  rw [hsem, booleanFeistel_rightInverse c t hct f x] at hrun
  exact hrun

/-- The register permutation given by a Boolean Feistel update on two distinct locations, with
inverse `booleanFeistelInverse`. -/
def booleanFeistelPerm {N : ℕ} (c t : Fin N) (hct : c ≠ t)
    (f : Bool → Bool) : Equiv.Perm (Reg N) where
  toFun := booleanFeistelAction c t f
  invFun := booleanFeistelInverse c t f
  left_inv := booleanFeistel_leftInverse c t hct f
  right_inv := booleanFeistel_rightInverse c t hct f

set_option backward.isDefEq.respectTransparency true in

/-- There exists a permutation of `Fin 4` with legal forward and inverse two-bit implementations
of combined length at most `630` in the canonical binary encoding. -/
theorem canonicalFourFeistel_words (f : Bool → Bool) :
    ∃ (π : Equiv.Perm (Fin 4)) (forward backward : List FiniteGateCode),
      finiteWordLegal 2 forward = true ∧ finiteWordLegal 2 backward = true ∧
      forward.length + backward.length ≤ 630 ∧
      (∀ i, Run 1 (finiteCodeCircuit 2 forward) (Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv 2).symm i)) =
        Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv 2).symm (π i))) ∧
      (∀ i, Run 1 (finiteCodeCircuit 2 backward) (Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv 2).symm i)) =
        Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv 2).symm (π.symm i))) := by
  let action := booleanFeistelPerm (1 : Fin 2) (0 : Fin 2) (by decide) f
  let π : Equiv.Perm (Fin 4) :=
    (((bitVecEquiv 2).symm).trans action).trans (bitVecEquiv 2)
  obtain ⟨forward, backward, hforward, hbackward, hlength, hforwardsem, hbackwardsem⟩ :=
    booleanFeistel_forward_backward_words (1 : Fin 2) (0 : Fin 2) (by decide) f
  refine ⟨π, forward, backward, hforward, hbackward, hlength, ?_, ?_⟩
  · intro i
    simpa only [π, Equiv.trans_apply, Equiv.symm_apply_apply, action, booleanFeistelPerm,
      Equiv.coe_fn_mk] using! hforwardsem ((bitVecEquiv 2).symm i)
  · intro i
    simpa only [π, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply,
      action, booleanFeistelPerm, Equiv.coe_fn_symm_mk] using! hbackwardsem ((bitVecEquiv 2).symm i)

/-- The concatenation of three `m`-bit registers `a`, `b`, and `work`, in that order. -/
def tripleBinaryRegister (m : ℕ) (a b work : Reg m) : Reg (3*m) := fun i =>
  if ha : i.val < m then a ⟨i.val, ha⟩
  else if hb : i.val < 2*m then b ⟨i.val-m, by omega⟩
  else work ⟨i.val-2*m, by omega⟩

/-- For positive `m`, a legal word of length at most `m * 2^m * (62 * m + 1)` XORs `f a` into
the middle register while preserving the first and workspace registers. -/
theorem finiteTruthTableVector_word (m : ℕ) (hm : 0 < m) (f : Reg m → Reg m) :
    ∃ word : List FiniteGateCode, finiteWordLegal (3*m) word = true ∧
      word.length ≤ m*2^m*(62*m+1) ∧
      ∀ a b work : Reg m,
        Run 1 (finiteCodeCircuit (3*m) word) (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a b work)) =
          Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a (fun i => b i ^^ f a i) work) := by
  let c : ℕ → Fin (3*m) := fun i => ⟨i%m, by have := Nat.mod_lt i hm; omega⟩
  let w : ℕ → Fin (3*m) := fun i => ⟨2*m+i%m, by have := Nat.mod_lt i hm; omega⟩
  have hc : Set.InjOn c (Set.Iio m) := by
    intro i hi j hj hij
    have := congrArg Fin.val hij
    simpa only [c, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using! this
  have hw : Set.InjOn w (Set.Iio (m-2)) := by
    intro i hi j hj hij
    change i < m-2 at hi
    change j < m-2 at hj
    have heq := congrArg Fin.val hij
    have him : i < m := by omega
    have hjm : j < m := by omega
    simp only [w, Nat.mod_eq_of_lt him, Nat.mod_eq_of_lt hjm] at heq
    omega
  have hcw : ∀ i < m, ∀ j < m-2, c i ≠ w j := by
    intro i hi j hj hij
    have := congrArg Fin.val hij
    simp only [c, w, Nat.mod_eq_of_lt hi] at this
    omega
  have hcontrol (a b work : Reg m) :
      finiteControlPattern c m (tripleBinaryRegister m a b work) = a := by
    ext i
    simp only [finiteControlPattern, c, Nat.mod_eq_of_lt i.isLt,
      tripleBinaryRegister, i.isLt, dif_pos]
  have hpartial (S : Finset (Fin m)) :
      ∃ word : List FiniteGateCode, finiteWordLegal (3*m) word = true ∧
        word.length ≤ S.card*(2^m*(62*m+1)) ∧
        ∀ a b work : Reg m,
          Run 1 (finiteCodeCircuit (3*m) word) (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a b work)) =
            Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a
              (fun i => b i ^^ if i ∈ S then f a i else false) work) := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨[], rfl, by simp, ?_⟩
      intro a b work
      simp [finiteCodeCircuit]
    | @insert j S hj ih =>
      let t : Fin (3*m) := ⟨m+j.val, by omega⟩
      have hct : ∀ i < m, c i ≠ t := by
        intro i hi hij
        have := congrArg Fin.val hij
        simp only [c, t, Nat.mod_eq_of_lt hi] at this
        omega
      have hwt : ∀ i < m-2, w i ≠ t := by
        intro i hi hij
        have := congrArg Fin.val hij
        simp only [w, t] at this
        omega
      obtain ⟨toggle, htoggle, htogglelen, htogglesem⟩ :=
        finiteTruthTableX_word c w t m hc hw hcw hct hwt (fun a => f a j)
      obtain ⟨initialWord, hprefix, hprefixlen, hprefixsem⟩ := ih
      refine ⟨initialWord++toggle, ?_, ?_, ?_⟩
      · simp only [finiteWordLegal, List.all_append, Bool.and_eq_true]
        exact ⟨hprefix, htoggle⟩
      · rw [List.length_append, Finset.card_insert_of_notMem hj, Nat.add_mul]
        omega
      · intro a b work
        simp only [finiteCodeCircuit, List.map_append, run_append]
        change Run 1 (finiteCodeCircuit (3*m) toggle)
          (Run 1 (finiteCodeCircuit (3*m) initialWord) (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a b work))) = _
        rw [hprefixsem, htogglesem, hcontrol]
        congr 1
        ext i
        by_cases hit : i = t
        · subst i
          have hjbound : m+j.val < 2*m := by omega
          simp [tripleBinaryRegister, t, hjbound, hj]
        · by_cases hia : i.val < m
          · simp [Function.update_of_ne hit, tripleBinaryRegister, hia]
          · by_cases hib : i.val < 2*m
            · have hij : (⟨i.val-m, by omega⟩ : Fin m) ≠ j := by
                intro hij
                apply hit
                apply Fin.ext
                have := congrArg Fin.val hij
                change i.val = m+j.val
                change i.val-m = j.val at this
                omega
              simp [Function.update_of_ne hit, tripleBinaryRegister, hia, hib, hij]
            · simp [Function.update_of_ne hit, tripleBinaryRegister, hia, hib]
  obtain ⟨word, hword, hlen, hsem⟩ := hpartial Finset.univ
  refine ⟨word, hword, by simpa [Nat.mul_assoc] using! hlen, ?_⟩
  intro a b work
  simpa only [Finset.mem_univ, if_true] using! hsem a b work

/-- A Boolean Feistel update with constant false round function swaps the `j`th bits of the
first two blocks of `tripleBinaryRegister`. -/
theorem tripleBinaryRegister_swap_bit (m : ℕ) (j : Fin m) (a b work : Reg m) :
    booleanFeistelAction (⟨j.val, by omega⟩ : Fin (3*m))
      (⟨m+j.val, by omega⟩ : Fin (3*m)) (fun _ => false) (tripleBinaryRegister m a b work) =
        tripleBinaryRegister m (Function.update a j (b j)) (Function.update b j (a j)) work := by
  ext i
  have hjbound : m+j.val < 2*m := by omega
  have hm : m ≠ 0 := by omega
  by_cases hij : i.val = j.val
  · have hieq : i = (⟨j.val, by omega⟩ : Fin (3*m)) := Fin.ext hij
    rw [hieq]
    simp [booleanFeistelAction, tripleBinaryRegister, j.isLt, hjbound,
      Function.update, Fin.ext_iff, hm]
  · by_cases hij2 : i.val = m+j.val
    · have hieq : i = (⟨m+j.val, by omega⟩ : Fin (3*m)) := Fin.ext hij2
      rw [hieq]
      simp [booleanFeistelAction, tripleBinaryRegister, hjbound, Function.update]
    · have hne1 : i ≠ (⟨j.val, by omega⟩ : Fin (3*m)) := fun h => hij (congrArg Fin.val h)
      have hne2 : i ≠ (⟨m+j.val, by omega⟩ : Fin (3*m)) := fun h => hij2 (congrArg Fin.val h)
      by_cases hia : i.val < m
      · have hnej : (⟨i.val, hia⟩ : Fin m) ≠ j := fun h => hij (congrArg Fin.val h)
        simp [booleanFeistelAction, tripleBinaryRegister, hia, hne1, hne2, hnej]
      · by_cases hib : i.val < 2*m
        · have hnej : (⟨i.val-m, by omega⟩ : Fin m) ≠ j := by
            intro h
            have hv := congrArg Fin.val h
            change i.val-m = j.val at hv
            omega
          simp [booleanFeistelAction, tripleBinaryRegister, hia, hib, hne1, hne2, hnej]
        · simp [booleanFeistelAction, tripleBinaryRegister, hia, hib, hne1, hne2]

/-- A legal finite gate word of length at most `315 * m` swaps the first two `m`-bit blocks
while preserving the workspace block. -/
theorem tripleBinaryRegister_swap_word (m : ℕ) :
    ∃ word : List FiniteGateCode, finiteWordLegal (3*m) word = true ∧
      word.length ≤ 315*m ∧ ∀ a b work : Reg m,
        Run 1 (finiteCodeCircuit (3*m) word) (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a b work)) =
          Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m b a work) := by
  have hpartial (S : Finset (Fin m)) :
      ∃ word : List FiniteGateCode, finiteWordLegal (3*m) word = true ∧
        word.length ≤ S.card*315 ∧ ∀ a b work : Reg m,
          Run 1 (finiteCodeCircuit (3*m) word) (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a b work)) =
            Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m (fun i => if i ∈ S then b i else a i)
              (fun i => if i ∈ S then a i else b i) work) := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨[], rfl, by simp, ?_⟩
      intro a b work
      simp [finiteCodeCircuit]
    | @insert j S hj ih =>
      let c : Fin (3*m) := ⟨j.val, by omega⟩
      let t : Fin (3*m) := ⟨m+j.val, by omega⟩
      have hct : c ≠ t := by
        intro h
        have := congrArg Fin.val h
        change j.val = m+j.val at this
        omega
      obtain ⟨swap, hswap, hswaplen, hswapsem⟩ := booleanFeistel_word c t hct (fun _ => false)
      obtain ⟨initialWord, hinitial, hinitiallen, hinitialsem⟩ := ih
      refine ⟨initialWord++swap, ?_, ?_, ?_⟩
      · simp only [finiteWordLegal, List.all_append, Bool.and_eq_true]
        exact ⟨hinitial, hswap⟩
      · rw [List.length_append, Finset.card_insert_of_notMem hj, Nat.add_mul]
        omega
      · intro a b work
        simp only [finiteCodeCircuit, List.map_append, run_append]
        change Run 1 (finiteCodeCircuit (3*m) swap)
          (Run 1 (finiteCodeCircuit (3*m) initialWord) (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a b work))) = _
        rw [hinitialsem, hswapsem]
        change Qatlib.Foundations.PureStateMath.Ket (booleanFeistelAction (⟨j.val, by omega⟩ : Fin (3*m))
          (⟨m+j.val, by omega⟩ : Fin (3*m)) (fun _ => false) _) = _
        rw [tripleBinaryRegister_swap_bit]
        simp only [hj, if_false]
        congr 2 <;> ext i <;> by_cases hij : i = j <;>
          simp [hij, hj, Function.update]
  obtain ⟨word, hword, hlen, hsem⟩ := hpartial Finset.univ
  refine ⟨word, hword, by simpa [Nat.mul_comm] using! hlen, ?_⟩
  intro a b work
  simpa only [Finset.mem_univ, if_true] using! hsem a b work

/-- For positive `m`, any permutation of `m`-bit registers and its inverse have exact legal
implementations using two zero-initialized auxiliary blocks. Their combined length is at
most `4 * m * 2^m * (62 * m + 1) + 630 * m`. -/
theorem binaryPermutation_truthTable_words (m : ℕ) (hm : 0 < m)
    (π : Equiv.Perm (Reg m)) :
    ∃ forward backward : List FiniteGateCode,
      finiteWordLegal (3*m) forward = true ∧ finiteWordLegal (3*m) backward = true ∧
      forward.length + backward.length ≤ 4*m*2^m*(62*m+1)+630*m ∧
      (∀ a : Reg m, Run 1 (finiteCodeCircuit (3*m) forward)
        (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a (fun _ => false) (fun _ => false))) =
          Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m (π a) (fun _ => false) (fun _ => false))) ∧
      (∀ a : Reg m, Run 1 (finiteCodeCircuit (3*m) backward)
        (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a (fun _ => false) (fun _ => false))) =
          Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m (π.symm a) (fun _ => false) (fun _ => false))) := by
  obtain ⟨compute, hcompute, hcomputelen, hcomputesem⟩ := finiteTruthTableVector_word m hm π
  obtain ⟨swap, hswap, hswaplen, hswapsem⟩ := tripleBinaryRegister_swap_word m
  obtain ⟨erase, herase, heraselen, herasesem⟩ := finiteTruthTableVector_word m hm π.symm
  let word := compute++swap++erase
  have hword : finiteWordLegal (3*m) word = true := by
    simp only [word, finiteWordLegal, List.all_append, Bool.and_eq_true]
    exact ⟨⟨hcompute, hswap⟩, herase⟩
  have hlen : word.length ≤ 2*m*2^m*(62*m+1)+315*m := by
    dsimp only [word]
    simp only [List.length_append]
    nlinarith
  have hsem (a : Reg m) : Run 1 (finiteCodeCircuit (3*m) word)
      (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a (fun _ => false) (fun _ => false))) =
        Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m (π a) (fun _ => false) (fun _ => false)) := by
    simp only [word, finiteCodeCircuit, List.map_append, run_append]
    change Run 1 (finiteCodeCircuit (3*m) erase)
      (Run 1 (finiteCodeCircuit (3*m) swap)
        (Run 1 (finiteCodeCircuit (3*m) compute) _)) = _
    rw [hcomputesem, hswapsem, herasesem]
    simp only [Bool.false_xor, Equiv.symm_apply_apply, Bool.xor_self]
  have hinverse := finite_gate_word_paid_adjoint_semantics (3*m) word
    (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) hword
  refine ⟨word, finiteWordAdjoint word, hword, hinverse.1, ?_, hsem, ?_⟩
  · rw [hinverse.2.1]
    nlinarith
  · intro a
    have hrun := (finite_gate_word_paid_adjoint_semantics (3*m) word
      (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m (π.symm a) (fun _ => false) (fun _ => false))) hword).2.2.1
    simp only [finiteCodeCircuit, List.map_append, run_append] at hrun
    change Run 1 (finiteCodeCircuit (3*m) (finiteWordAdjoint word))
      (Run 1 (finiteCodeCircuit (3*m) word) _) = _ at hrun
    rw [hsem, Equiv.apply_symm_apply] at hrun
    exact hrun

/-- A uniformly chosen permutation maps any prescribed injective `m`-tuple of inputs to any
prescribed injective `m`-tuple of outputs with probability `1 / q.descFactorial m`. -/
theorem uniformAllPermutation_probability {q m : ℕ}
    (inputs outputs : Fin m → Fin q) (hi : Function.Injective inputs)
    (hj : Function.Injective outputs) :
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin q) =>
      ∀ z, σ (inputs z) = outputs z)).card : ℝ) /
        Fintype.card (Equiv.Perm (Fin q)) = 1/(q.descFactorial m : ℝ) := by
  let inputEmbedding : Fin m ↪ Fin q := ⟨inputs, hi⟩
  let outputEmbedding : Fin m ↪ Fin q := ⟨outputs, hj⟩
  let F : Equiv.Perm (Fin q) → (Fin m ↪ Fin q) :=
    fun σ => inputEmbedding.trans σ.toEmbedding
  let count := (Finset.univ.filter (fun σ => F σ = outputEmbedding)).card
  have hcount (target : Fin m ↪ Fin q) :
      (Finset.univ.filter (fun σ => F σ = target)).card = count := by
    obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair outputs target hj target.injective
    let e : {σ : Equiv.Perm (Fin q) // F σ = outputEmbedding} ≃
        {σ : Equiv.Perm (Fin q) // F σ = target} :=
      { toFun := fun σ => ⟨ρ*σ.val, by
          apply Function.Embedding.ext
          intro z
          change ρ (σ.val (inputs z)) = target z
          have h := congrArg (fun embedding : Fin m ↪ Fin q => embedding z) σ.property
          change σ.val (inputs z) = outputs z at h
          rw [h, hρ]⟩
        invFun := fun σ => ⟨ρ⁻¹*σ.val, by
          apply Function.Embedding.ext
          intro z
          change ρ.symm (σ.val (inputs z)) = outputs z
          have h := congrArg (fun embedding : Fin m ↪ Fin q => embedding z) σ.property
          change σ.val (inputs z) = target z at h
          rw [h, ← hρ z, Equiv.symm_apply_apply]⟩
        left_inv := by intro σ; ext1; simp
        right_inv := by intro σ; ext1; simp }
    symm
    exact (Fintype.card_subtype _).symm.trans
      ((Fintype.card_congr e).trans (Fintype.card_subtype _))
  have htotalNat : Fintype.card (Equiv.Perm (Fin q)) =
      Fintype.card (Fin m ↪ Fin q)*count := by
    calc
      Fintype.card (Equiv.Perm (Fin q)) =
          ∑ target : Fin m ↪ Fin q, (Finset.univ.filter (fun σ => F σ = target)).card := by
        simpa only [Finset.card_univ] using! Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset (Equiv.Perm (Fin q))))
          (t := (Finset.univ : Finset (Fin m ↪ Fin q))) (f := F)
          (by intro σ _; exact Finset.mem_univ (F σ))
      _ = _ := by simp only [hcount, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  have hcardTarget : Fintype.card (Fin m ↪ Fin q) = q.descFactorial m := by simp
  letI : Nonempty (Fin m ↪ Fin q) := ⟨inputEmbedding⟩
  have hG : (Fintype.card (Equiv.Perm (Fin q)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hY : (q.descFactorial m : ℝ) ≠ 0 := by
    rw [← hcardTarget]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin m ↪ Fin q) ≠ 0)
  have htotal : (Fintype.card (Equiv.Perm (Fin q)) : ℝ) =
      (q.descFactorial m : ℝ)*(count : ℝ) := by
    rw [← hcardTarget]
    exact_mod_cast htotalNat
  have hfiber : Finset.univ.filter (fun σ : Equiv.Perm (Fin q) =>
      ∀ z, σ (inputs z) = outputs z) =
        Finset.univ.filter (fun σ => F σ = outputEmbedding) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; apply Function.Embedding.ext; intro z; exact h z
    · intro h z
      exact congrArg (fun embedding : Fin m ↪ Fin q => embedding z) h
  rw [hfiber]
  change (count : ℝ)/Fintype.card (Equiv.Perm (Fin q)) = _
  field_simp [hG, hY]
  nlinarith [htotal]

/-- An enumeration of all permutations of `Fin q` by seeds in `Fin q.factorial`. -/
def allPermutationFamily (q : ℕ) : Fin q.factorial → Equiv.Perm (Fin q) :=
  (Fintype.equivFinOfCardEq (by simp [Fintype.card_perm])).symm

/-- The enumerated permutation family realizes prescribed injective input and output tuples with
probability `1 / q.descFactorial m`. -/
theorem allPermutationFamily_probability {q m : ℕ}
    (inputs outputs : Fin m → Fin q) (hi : Function.Injective inputs)
    (hj : Function.Injective outputs) :
    eventProbability (fun s => ∀ z, allPermutationFamily q s (inputs z) = outputs z) =
      1/(q.descFactorial m : ℝ) := by
  let encoding : Fin q.factorial ≃ Equiv.Perm (Fin q) :=
    (Fintype.equivFinOfCardEq (by simp [Fintype.card_perm])).symm
  have hcard := Fintype.card_congr (encoding.subtypeEquivOfSubtype
    (p := fun σ : Equiv.Perm (Fin q) => ∀ z, σ (inputs z) = outputs z))
  have hden : Fintype.card (Equiv.Perm (Fin q)) = q.factorial := by simp [Fintype.card_perm]
  have hstat := uniformAllPermutation_probability inputs outputs hi hj
  rw [hden] at hstat
  apply Eq.trans ?_ hstat
  unfold eventProbability
  congr 1
  norm_cast
  simpa only [Fintype.card_subtype, allPermutationFamily, encoding] using! hcard

/-- For positive `t`, the family of all permutations satisfies `ApproxIndependent d (1 / t)` for
every `d`. -/
theorem allPermutationFamily_approxIndependent (q d t : ℕ) (ht : 0 < t) :
    ApproxIndependent d (1/(t : ℝ)) (allPermutationFamily q) := by
  intro m _ hmq inputs outputs hi hj
  rw [allPermutationFamily_probability inputs outputs hi hj]
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hden : 0 < (q.descFactorial m : ℝ) := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hmq)
  have hnonneg : 0 ≤ (1/(t : ℝ)) := le_of_lt (one_div_pos.mpr htR)
  constructor <;> apply (div_le_div_iff_of_pos_right hden).mpr <;> linarith

/-- For `q ≥ 1`, the binary ceiling logarithm of `q.factorial + 1` is at most `q * Nat.clog 2 (q
+ 1)`. -/
theorem allPermutationFamily_seed_bound (q : ℕ) (hq : 1 ≤ q) :
    Nat.clog 2 (q.factorial+1) ≤ q*Nat.clog 2 (q+1) := by
  apply Nat.clog_le_of_le_pow
  have hqpow : q+1 ≤ 2^Nat.clog 2 (q+1) := Nat.le_pow_clog (by decide) (q+1)
  have hfactorial : q.factorial+1 ≤ (q+1)^q := by
    calc
      q.factorial+1 ≤ q^q+1 := Nat.add_le_add_right (Nat.factorial_le_pow q) 1
      _ ≤ (q+1)^q := by
        have h := pow_add_pow_le (Nat.zero_le q) (by omega : 0 ≤ (1 : ℕ))
          (by omega : q ≠ 0)
        simpa only [one_pow] using! h
  calc
    q.factorial+1 ≤ (q+1)^q := hfactorial
    _ ≤ (2^Nat.clog 2 (q+1))^q := Nat.pow_le_pow_left hqpow q
    _ = 2^(q*Nat.clog 2 (q+1)) := by rw [← pow_mul, Nat.mul_comm]

/-- The register formed by prepending `h` false bits to the `m`-bit register `a`. -/
def zeroPrefixBinaryRegister (h m : ℕ) (a : Reg m) : Reg (h+m) := fun i =>
  if hi : i.val < h then false else a ⟨i.val-h, by omega⟩

/-- The encoded value of an `(n + 1)`-bit register is its last bit plus twice the encoded value
of its first `n` bits. -/
theorem bitVecEquiv_succ_value (n : ℕ) (a : Reg (n+1)) :
    ((bitVecEquiv (n+1)) a).val =
      (if a (Fin.last n) then 1 else 0) +
        2*((bitVecEquiv n) (fun i => a i.castSucc)).val := by
  have hsplit : regSuccEquiv n a = ((fun i => a i.castSucc), a (Fin.last n)) := rfl
  have hcast : ∀ (e : 2^n*2 = 2^(n+1)) (y : Fin (2^n*2)),
      ((Equiv.cast (congrArg Fin e)) y).val = y.val := by
    intro e y
    cases e
    rfl
  change ((Equiv.cast (congrArg Fin (Nat.pow_succ 2 n).symm))
    (finProdFinEquiv ((Equiv.prodCongr (bitVecEquiv n) boolEquivFin2) (regSuccEquiv n a)))).val = _
  rw [hcast (Nat.pow_succ 2 n).symm, hsplit]
  cases a (Fin.last n) <;> rfl

/-- Prepending false bits preserves the natural-number value of a register under `bitVecEquiv`. -/
theorem zeroPrefixBinaryRegister_value (h m : ℕ) (a : Reg m) :
    ((bitVecEquiv (h+m)) (zeroPrefixBinaryRegister h m a)).val =
      ((bitVecEquiv m) a).val := by
  induction m with
  | zero =>
    have hzero : zeroPrefixBinaryRegister h 0 a = ZeroStr h := by
      ext i
      simp [zeroPrefixBinaryRegister, ZeroStr]
    simp only [Nat.add_zero, hzero, bitVecEquiv_zeroStr, bitVecEquiv_zero]
    simp
  | succ m ih =>
    have hlast : zeroPrefixBinaryRegister h (m+1) a (Fin.last (h+m)) = a (Fin.last m) := by
      simp [zeroPrefixBinaryRegister]
      congr 1
    have hinit : (fun i : Fin (h+m) => zeroPrefixBinaryRegister h (m+1) a i.castSucc) =
        zeroPrefixBinaryRegister h m (fun i => a i.castSucc) := by
      ext i
      simp only [zeroPrefixBinaryRegister, Fin.val_castSucc]
      split_ifs <;> rfl
    change ((bitVecEquiv ((h+m)+1)) (zeroPrefixBinaryRegister h (m+1) a)).val = _
    rw [bitVecEquiv_succ_value (h+m), hlast, hinit, ih, bitVecEquiv_succ_value]

/-- A Boolean Feistel update with constant false round function swaps the `j`th bits of the
first and third blocks. -/
theorem tripleBinaryRegister_outer_swap_bit (m : ℕ) (j : Fin m) (a b work : Reg m) :
    booleanFeistelAction (⟨j.val, by omega⟩ : Fin (3*m))
      (⟨2*m+j.val, by omega⟩ : Fin (3*m)) (fun _ => false) (tripleBinaryRegister m a b work) =
        tripleBinaryRegister m (Function.update a j (work j)) b (Function.update work j (a j)) := by
  ext i
  have hjm := j.isLt
  have hm : m ≠ 0 := by omega
  have hjnot : ¬2*m+j.val < m := by omega
  have hjnot2 : ¬2*m+j.val < 2*m := by omega
  by_cases hij : i.val = j.val
  · have hieq : i = (⟨j.val, by omega⟩ : Fin (3*m)) := Fin.ext hij
    rw [hieq]
    simp [booleanFeistelAction, tripleBinaryRegister, j.isLt, hjnot, hjnot2,
      Function.update, Fin.ext_iff, hm]
  · by_cases hij2 : i.val = 2*m+j.val
    · have hieq : i = (⟨2*m+j.val, by omega⟩ : Fin (3*m)) := Fin.ext hij2
      rw [hieq]
      simp [booleanFeistelAction, tripleBinaryRegister, hjnot, hjnot2, Function.update]
    · have hne1 : i ≠ (⟨j.val, by omega⟩ : Fin (3*m)) := fun h => hij (congrArg Fin.val h)
      have hne2 : i ≠ (⟨2*m+j.val, by omega⟩ : Fin (3*m)) := fun h => hij2 (congrArg Fin.val h)
      by_cases hia : i.val < m
      · have hnej : (⟨i.val, hia⟩ : Fin m) ≠ j := fun h => hij (congrArg Fin.val h)
        simp [booleanFeistelAction, tripleBinaryRegister, hia, hne1, hne2, hnej]
      · by_cases hib : i.val < 2*m
        · simp [booleanFeistelAction, tripleBinaryRegister, hia, hib, hne1, hne2]
        · have hnej : (⟨i.val-2*m, by omega⟩ : Fin m) ≠ j := by
            intro h
            have hv := congrArg Fin.val h
            change i.val-2*m = j.val at hv
            omega
          simp [booleanFeistelAction, tripleBinaryRegister, hia, hib, hne1, hne2, hnej]

/-- A legal finite gate word of length at most `315 * m` swaps the first and third blocks while
preserving the middle block. -/
theorem tripleBinaryRegister_outer_swap_word (m : ℕ) :
    ∃ word : List FiniteGateCode, finiteWordLegal (3*m) word = true ∧
      word.length ≤ 315*m ∧ ∀ a b work : Reg m,
        Run 1 (finiteCodeCircuit (3*m) word) (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a b work)) =
          Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m work b a) := by
  have hpartial (S : Finset (Fin m)) :
      ∃ word : List FiniteGateCode, finiteWordLegal (3*m) word = true ∧
        word.length ≤ S.card*315 ∧ ∀ a b work : Reg m,
          Run 1 (finiteCodeCircuit (3*m) word) (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a b work)) =
            Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m (fun i => if i ∈ S then work i else a i) b
              (fun i => if i ∈ S then a i else work i)) := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨[], rfl, by simp, ?_⟩
      intro a b work
      simp [finiteCodeCircuit]
    | @insert j S hj ih =>
      let c : Fin (3*m) := ⟨j.val, by omega⟩
      let t : Fin (3*m) := ⟨2*m+j.val, by omega⟩
      have hct : c ≠ t := by
        intro h
        have := congrArg Fin.val h
        change j.val = 2*m+j.val at this
        omega
      obtain ⟨swap, hswap, hswaplen, hswapsem⟩ := booleanFeistel_word c t hct (fun _ => false)
      obtain ⟨initialWord, hinitial, hinitiallen, hinitialsem⟩ := ih
      refine ⟨initialWord++swap, ?_, ?_, ?_⟩
      · simp only [finiteWordLegal, List.all_append, Bool.and_eq_true]
        exact ⟨hinitial, hswap⟩
      · rw [List.length_append, Finset.card_insert_of_notMem hj, Nat.add_mul]
        omega
      · intro a b work
        simp only [finiteCodeCircuit, List.map_append, run_append]
        change Run 1 (finiteCodeCircuit (3*m) swap)
          (Run 1 (finiteCodeCircuit (3*m) initialWord) (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m a b work))) = _
        rw [hinitialsem, hswapsem]
        change Qatlib.Foundations.PureStateMath.Ket (booleanFeistelAction (⟨j.val, by omega⟩ : Fin (3*m))
          (⟨2*m+j.val, by omega⟩ : Fin (3*m)) (fun _ => false) _) = _
        rw [tripleBinaryRegister_outer_swap_bit]
        simp only [hj, if_false]
        congr 2 <;> ext i <;> by_cases hij : i = j <;> simp [hij, hj, Function.update]
  obtain ⟨word, hword, hlen, hsem⟩ := hpartial Finset.univ
  refine ⟨word, hword, by simpa [Nat.mul_comm] using! hlen, ?_⟩
  intro a b work
  simpa only [Finset.mem_univ, if_true] using! hsem a b work

/-- For positive `m`, any permutation and its inverse can act exactly on the third block with
the first two blocks initialized and returned to zero. The legal forward and inverse words
have combined length at most `4 * m * 2^m * (62 * m + 1) + 1890 * m`. -/
theorem canonicalBlockPermutation_words (m : ℕ) (hm : 0 < m) (π : Equiv.Perm (Reg m)) :
    ∃ forward backward : List FiniteGateCode,
      finiteWordLegal (3*m) forward = true ∧ finiteWordLegal (3*m) backward = true ∧
      forward.length + backward.length ≤ 4*m*2^m*(62*m+1)+1890*m ∧
      (∀ a : Reg m, Run 1 (finiteCodeCircuit (3*m) forward)
        (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m (fun _ => false) (fun _ => false) a)) =
          Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m (fun _ => false) (fun _ => false) (π a))) ∧
      (∀ a : Reg m, Run 1 (finiteCodeCircuit (3*m) backward)
        (Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m (fun _ => false) (fun _ => false) a)) =
          Qatlib.Foundations.PureStateMath.Ket (tripleBinaryRegister m (fun _ => false) (fun _ => false) (π.symm a))) := by
  obtain ⟨forward, backward, hforward, hbackward, hlength, hforwardsem, hbackwardsem⟩ :=
    binaryPermutation_truthTable_words m hm π
  obtain ⟨swap, hswap, hswaplen, hswapsem⟩ := tripleBinaryRegister_outer_swap_word m
  refine ⟨swap++forward++swap, swap++backward++swap, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [finiteWordLegal, List.all_append, Bool.and_eq_true]
    exact ⟨⟨hswap, hforward⟩, hswap⟩
  · simp only [finiteWordLegal, List.all_append, Bool.and_eq_true]
    exact ⟨⟨hswap, hbackward⟩, hswap⟩
  · simp only [List.length_append]
    nlinarith
  · intro a
    simp only [finiteCodeCircuit, List.map_append, run_append]
    change Run 1 (finiteCodeCircuit (3*m) swap)
      (Run 1 (finiteCodeCircuit (3*m) forward) (Run 1 (finiteCodeCircuit (3*m) swap) _)) = _
    rw [hswapsem, hforwardsem, hswapsem]
  · intro a
    simp only [finiteCodeCircuit, List.map_append, run_append]
    change Run 1 (finiteCodeCircuit (3*m) swap)
      (Run 1 (finiteCodeCircuit (3*m) backward) (Run 1 (finiteCodeCircuit (3*m) swap) _)) = _
    rw [hswapsem, hbackwardsem, hswapsem]

/-- Transporting a register along an equality of widths preserves its encoded natural-number
value. -/
theorem bitVecEquiv_cast_value {n k : ℕ} (h : n = k) (a : Reg n) :
    ((bitVecEquiv k) (fun i => a (Fin.cast h.symm i))).val = ((bitVecEquiv n) a).val := by
  subst k
  rfl

/-- The encoded value of three blocks with the first two blocks zero equals the encoded value of
the third block. -/
theorem canonicalTripleBinaryRegister_value (m : ℕ) (a : Reg m) :
    ((bitVecEquiv (3*m)) (tripleBinaryRegister m (fun _ => false) (fun _ => false) a)).val =
      ((bitVecEquiv m) a).val := by
  have hsize : 3*m = 2*m+m := by omega
  rw [← bitVecEquiv_cast_value hsize]
  have hpad : (fun i : Fin (2*m+m) =>
      tripleBinaryRegister m (fun _ => false) (fun _ => false) a (Fin.cast hsize.symm i)) =
        zeroPrefixBinaryRegister (2*m) m a := by
    ext i
    simp only [tripleBinaryRegister, zeroPrefixBinaryRegister, Fin.val_cast]
    by_cases hi : i.val < m
    · have hi2 : i.val < 2*m := by omega
      simp [hi, hi2]
    · by_cases hi2 : i.val < 2*m <;> simp [hi, hi2]
  rw [hpad, zeroPrefixBinaryRegister_value]

/-- If `q ≤ 2^m` and `m > 0`, every permutation of `Fin q` and its inverse have exact legal
implementations on canonically encoded `3 * m`-bit registers, with combined length at most
`4 * m * 2^m * (62 * m + 1) + 1890 * m`. -/
theorem canonicalFinitePermutation_words (q m : ℕ) (hm : 0 < m) (hqm : q ≤ 2^m)
    (π : Equiv.Perm (Fin q)) :
    ∃ (hb : q ≤ 2^(3*m)) (forward backward : List FiniteGateCode),
      finiteWordLegal (3*m) forward = true ∧ finiteWordLegal (3*m) backward = true ∧
      forward.length + backward.length ≤ 4*m*2^m*(62*m+1)+1890*m ∧
      (∀ i, Run 1 (finiteCodeCircuit (3*m) forward)
        (Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv (3*m)).symm (Fin.castLE hb i))) =
          Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv (3*m)).symm (Fin.castLE hb (π i)))) ∧
      (∀ i, Run 1 (finiteCodeCircuit (3*m) backward)
        (Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv (3*m)).symm (Fin.castLE hb i))) =
          Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv (3*m)).symm (Fin.castLE hb (π.symm i)))) := by
  let encode : Fin q → Reg m := fun i => (bitVecEquiv m).symm (Fin.castLE hqm i)
  have hencode : Function.Injective encode := by
    intro i j h
    have h' := congrArg (bitVecEquiv m) h
    simpa only [encode, Equiv.apply_symm_apply, Fin.castLE_inj] using! h'
  let padded := π.viaFintypeEmbedding ⟨encode, hencode⟩
  have hpadded (i : Fin q) : padded (encode i) = encode (π i) :=
    Equiv.Perm.viaFintypeEmbedding_apply_image π ⟨encode,hencode⟩ i
  have hpaddedinv (i : Fin q) : padded.symm (encode i) = encode (π.symm i) := by
    apply padded.injective
    rw [Equiv.apply_symm_apply, hpadded, Equiv.apply_symm_apply]
  have hb : q ≤ 2^(3*m) :=
    hqm.trans (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : m ≤ 3*m))
  have hcanonical (i : Fin q) :
      tripleBinaryRegister m (fun _ => false) (fun _ => false) (encode i) =
        (bitVecEquiv (3*m)).symm (Fin.castLE hb i) := by
    apply (bitVecEquiv (3*m)).injective
    apply Fin.ext
    rw [Equiv.apply_symm_apply, canonicalTripleBinaryRegister_value]
    simp only [encode, Equiv.apply_symm_apply, Fin.val_castLE]
  obtain ⟨forward, backward, hforward, hbackward, hlen, hforwardsem, hbackwardsem⟩ :=
    canonicalBlockPermutation_words m hm padded
  refine ⟨hb, forward, backward, hforward, hbackward, hlen, ?_, ?_⟩
  · intro i
    simpa only [hpadded, hcanonical] using! hforwardsem (encode i)
  · intro i
    simpa only [hpaddedinv, hcanonical] using! hbackwardsem (encode i)

/-- For `q ≥ 2`, every permutation of `Fin q` and its inverse have exact legal implementations
at width `3 * Nat.clog 2 (q + 1)` with combined word length at most `10000 * (q + 1)^4`. -/
theorem canonicalFinitePermutation_clog_words (q : ℕ) (hq : 2 ≤ q)
    (π : Equiv.Perm (Fin q)) :
    ∃ (hb : q ≤ 2^(3*Nat.clog 2 (q+1))) (forward backward : List FiniteGateCode),
      finiteWordLegal (3*Nat.clog 2 (q+1)) forward = true ∧
      finiteWordLegal (3*Nat.clog 2 (q+1)) backward = true ∧
      forward.length + backward.length ≤ 10000*(q+1)^4 ∧
      (∀ i, Run 1 (finiteCodeCircuit (3*Nat.clog 2 (q+1)) forward)
        (Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv (3*Nat.clog 2 (q+1))).symm (Fin.castLE hb i))) =
          Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv (3*Nat.clog 2 (q+1))).symm (Fin.castLE hb (π i)))) ∧
      (∀ i, Run 1 (finiteCodeCircuit (3*Nat.clog 2 (q+1)) backward)
        (Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv (3*Nat.clog 2 (q+1))).symm (Fin.castLE hb i))) =
          Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv (3*Nat.clog 2 (q+1))).symm (Fin.castLE hb (π.symm i)))) := by
  let m := Nat.clog 2 (q+1)
  have hm : 0 < m := Nat.clog_pos (by decide) (by omega)
  have hqm : q ≤ 2^m := (Nat.le_succ q).trans (Nat.le_pow_clog (by decide) (q+1))
  have hmq : m ≤ q :=
    Nat.clog_le_of_le_pow (Nat.succ_le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))
  have hpow : 2^m ≤ 2*(q+1) := by
    have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < q+1)
    change 2^(m-1) < q+1 at hpred
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.pow_succ]
    omega
  obtain ⟨hb, forward, backward, hforward, hbackward, hlen, hforwardsem, hbackwardsem⟩ :=
    canonicalFinitePermutation_words q m hm hqm π
  refine ⟨hb, forward, backward, hforward, hbackward, ?_, hforwardsem, hbackwardsem⟩
  have hmajor : 4*m*2^m*(62*m+1) ≤ 4*q*(2*(q+1))*(62*q+1) := by gcongr
  apply hlen.trans
  calc
    4*m*2^m*(62*m+1)+1890*m ≤ 4*q*(2*(q+1))*(62*q+1)+1890*q := by omega
    _ ≤ 10000*(q+1)^4 := by
      nlinarith [Nat.zero_le (q^4), Nat.zero_le (q^3), Nat.zero_le (q^2)]

/-- There is a universal positive constant giving, for every `q ≥ 2` and `t ≥ 1`, a canonically
encoded permutation family satisfying `ApproxIndependent q (1 / t)`. The family has legal
exact forward and inverse words and satisfies the stated seed, width, and word-length
bounds. -/
theorem efficientPermutationFamily_fullIndependence_endpoint :
    ∃ C : ℝ, 0 < C ∧ ∀ q t : ℕ, 2 ≤ q → 1 ≤ t →
      ∃ (R b : ℕ) (π : Fin R → Equiv.Perm (Fin q))
        (encode : Fin q → Reg b) (forward backward : Fin R → List FiniteGateCode),
        0 < R ∧ Function.Injective encode ∧
        (∃ hb : q ≤ 2^b, ∀ i, encode i = (bitVecEquiv b).symm (Fin.castLE hb i)) ∧
        ApproxIndependent q (1/(t : ℝ)) π ∧
        (Nat.clog 2 (R+1) : ℝ) ≤ C*((q : ℝ)^2*Nat.clog 2 (q+1)+q*Nat.clog 2 (t+1)+1) ∧
        (b : ℝ) ≤ C*(q+Nat.clog 2 (q+1)+Nat.clog 2 (t+1)+1)^4 ∧
        (∀ s, finiteWordLegal b (forward s) = true ∧ finiteWordLegal b (backward s) = true ∧
          ((forward s).length+(backward s).length : ℝ) ≤
            C*(q+Nat.clog 2 (q+1)+Nat.clog 2 (t+1)+1)^8 ∧
          (∀ i, Run 1 (finiteCodeCircuit b (forward s)) (Qatlib.Foundations.PureStateMath.Ket (encode i)) = Qatlib.Foundations.PureStateMath.Ket (encode (π s i))) ∧
          (∀ i, Run 1 (finiteCodeCircuit b (backward s)) (Qatlib.Foundations.PureStateMath.Ket (encode i)) = Qatlib.Foundations.PureStateMath.Ket (encode ((π s).symm i)))) := by
  refine ⟨10000, by norm_num, ?_⟩
  intro q t hq ht
  let m := Nat.clog 2 (q+1)
  let D := q+m+Nat.clog 2 (t+1)+1
  have hm : 0 < m := Nat.clog_pos (by decide) (by omega)
  have hmq : m ≤ q :=
    Nat.clog_le_of_le_pow (Nat.succ_le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))
  have hqm : q ≤ 2^m := (Nat.le_succ q).trans (Nat.le_pow_clog (by decide) (q+1))
  have hb : q ≤ 2^(3*m) := hqm.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  let encode : Fin q → Reg (3*m) := fun i => (bitVecEquiv (3*m)).symm (Fin.castLE hb i)
  have hencode : Function.Injective encode := by
    intro i j h
    have h' := congrArg (bitVecEquiv (3*m)) h
    simpa only [encode, Equiv.apply_symm_apply, Fin.castLE_inj] using! h'
  have hwords (s : Fin q.factorial) :
      ∃ forward backward : List FiniteGateCode,
        finiteWordLegal (3*m) forward = true ∧ finiteWordLegal (3*m) backward = true ∧
        forward.length+backward.length ≤ 10000*(q+1)^4 ∧
        (∀ i, Run 1 (finiteCodeCircuit (3*m) forward) (Qatlib.Foundations.PureStateMath.Ket (encode i)) =
          Qatlib.Foundations.PureStateMath.Ket (encode (allPermutationFamily q s i))) ∧
        (∀ i, Run 1 (finiteCodeCircuit (3*m) backward) (Qatlib.Foundations.PureStateMath.Ket (encode i)) =
          Qatlib.Foundations.PureStateMath.Ket (encode ((allPermutationFamily q s).symm i))) := by
    obtain ⟨hb', forward, backward, hforward, hbackward, hlen, hforwardsem, hbackwardsem⟩ :=
      canonicalFinitePermutation_clog_words q hq (allPermutationFamily q s)
    exact ⟨forward, backward, hforward, hbackward, hlen, hforwardsem, hbackwardsem⟩
  choose forward backward hforward hbackward hlen hforwardsem hbackwardsem using hwords
  refine ⟨q.factorial, 3*m, allPermutationFamily q, encode, forward, backward,
    Nat.factorial_pos q, hencode, ⟨hb, fun _ => rfl⟩,
    allPermutationFamily_approxIndependent q q t (by omega), ?_, ?_, ?_⟩
  · have hs : (Nat.clog 2 (q.factorial+1) : ℝ) ≤ (q : ℝ)*m := by
      exact_mod_cast allPermutationFamily_seed_bound q (by omega)
    have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
    have hmR : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hqmR : (q : ℝ)*m ≤ (q : ℝ)^2*m :=
      mul_le_mul_of_nonneg_right (by nlinarith) hmR
    have hterm : 0 ≤ (q : ℝ)*Nat.clog 2 (t+1) := by positivity
    have hprod : 0 ≤ (q : ℝ)^2*m := by positivity
    nlinarith
  · have hDpos : 0 < D := by dsimp [D]; omega
    have hDpow : D ≤ D^4 := by
      simpa only [pow_one] using! Nat.pow_le_pow_right hDpos (by decide : 1 ≤ 4)
    have hmD : m ≤ D := by dsimp [D]; omega
    have hmem : 3*m ≤ 10000*D^4 := by omega
    exact_mod_cast hmem
  · intro s
    refine ⟨hforward s, hbackward s, ?_, hforwardsem s, hbackwardsem s⟩
    have hDpos : 0 < D := by dsimp [D]; omega
    have hfirst : (q+1)^4 ≤ D^4 := Nat.pow_le_pow_left (by dsimp [D]; omega) 4
    have hsecond : D^4 ≤ D^8 := Nat.pow_le_pow_right hDpos (by decide : 4 ≤ 8)
    have hclock : (forward s).length+(backward s).length ≤ 10000*D^8 :=
      (hlen s).trans (Nat.mul_le_mul_left 10000 (hfirst.trans hsecond))
    exact_mod_cast hclock

end
end Qatlib.Concepts.WalkFind.SearchAlgorithm
