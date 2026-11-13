/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis

/-!
# Gray-path two-level gate synthesis

This module synthesizes two-level unitaries on a nonempty qubit register using legal local
reflection-gate words. `grayCanonicalPair_table` handles an all-true control pattern,
`grayAdjacentPair_table` changes the control polarities, and `grayPair_table` connects arbitrary
distinct basis addresses by a Gray path.

The exact word-length bounds count the path blocks and polarity changes explicitly, following
the controlled-gate synthesis framework of [BarencoEtAl1995].

## Main statements

* `grayCanonicalPair_table`: constructs a canonical pair table of length at most `256 * (k +
  1)^2`.
* `grayAdjacentPair_table`: adds at most `2 * k` gates for a general adjacent pair.
* `grayPair_table`: gives a bound with `2 * d - 1` blocks, where `d` is the Hamming distance.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.GateTables.GrayUniversal
open Matrix
open scoped Classical BigOperators

/-- Enumerates the wires other than target `t` at indices below `k`, returning `t` at larger
indices. -/
def grayControlWires {k : ℕ} (t : Fin (k+1)) : ℕ → Fin (k+1) :=
  fun i => if h : i < k then t.succAbove ⟨i,h⟩ else t

/-- The register address with bit `b` at target `t` and true at every other wire. -/
def grayControlAddress {k : ℕ} (t : Fin (k+1)) (b : Bool) : Reg (k+1) :=
  fun w => if w = t then b else true

/-- The control-wire enumeration is injective on indices less than `k`. -/
private theorem grayControlWires_inj {k : ℕ} (t : Fin (k+1)) :
    Set.InjOn (grayControlWires t) (Set.Iio k) := by
  intro i hi j hj he
  change i < k at hi
  change j < k at hj
  simp only [grayControlWires, dif_pos hi, dif_pos hj] at he
  exact congrArg Fin.val (Fin.succAbove_right_injective he)

/-- Every enumerated control wire with index below `k` differs from the target. -/
private theorem grayControlWires_ne {k : ℕ} (t : Fin (k+1)) (i : ℕ) (hi : i < k) :
    grayControlWires t i ≠ t := by
  simp only [grayControlWires, dif_pos hi]
  exact Fin.succAbove_ne t _

/-- The prefix conjunction of the enumerated controls is true exactly when every non-target wire
is true. -/
private theorem grayControls_true_iff {k : ℕ} (t : Fin (k+1)) (x : Reg (k+1)) :
    noWorkPrefixAnd (fun i => x (grayControlWires t i)) k = true ↔
      ∀ w, w ≠ t → x w = true := by
  simp only [noWorkPrefixAnd, List.all_eq_true, List.mem_range]
  constructor
  · intro h w hw
    obtain ⟨i,rfl⟩ := Fin.exists_succAbove_eq hw
    have hh := h i.val i.isLt
    simpa only [grayControlWires, dif_pos i.isLt] using! hh
  · intro h i hi
    simp only [grayControlWires, dif_pos hi]
    exact h _ (Fin.succAbove_ne t _)

/-- The canonical addresses with false and true target bits are distinct. -/
private theorem grayControlAddress_ne {k : ℕ} (t : Fin (k+1)) :
    grayControlAddress t false ≠ grayControlAddress t true := by
  intro h
  have hh := congrFun h t
  simp [grayControlAddress] at hh

/-- Updating the target bit of a canonical address gives the canonical address with that new
target bit. -/
private theorem grayControlAddress_update {k : ℕ} (t : Fin (k+1)) (b c : Bool) :
    Function.update (grayControlAddress t b) t c = grayControlAddress t c := by
  funext w
  by_cases hw : w = t
  · subst w
    simp [grayControlAddress]
  · simp [hw, grayControlAddress]

/-- A unitary on the canonical address pair has a legal reflection-word implementation of length
at most `256 * (k + 1)^2`, acting correctly on every state. -/
theorem grayCanonicalPair_table {k : ℕ} (t : Fin (k+1))
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
      gs.length ≤ 256*(k+1)^2 ∧ ∀ ψ : QState (Reg (k+1)),
        Run 1 (reflectionCompile gs) ψ =
          twoLevelMatrix (.pair (grayControlAddress t false) (grayControlAddress t true) U) *ᵥ ψ := by
  obtain ⟨gs,hgs,hlen,hr⟩ := noWork_multi_control_wire_table k (grayControlWires t) t
    (grayControlWires_inj t) (grayControlWires_ne t) U hU
  have hk (q : Reg (k+1)) : Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket q) =
      twoLevelMatrix (.pair (grayControlAddress t false) (grayControlAddress t true) U) *ᵥ Qatlib.Foundations.PureStateMath.Ket q := by
    have hrun := hr q (Qatlib.Foundations.PureStateMath.Ket (q t))
    rw [multiWireState_ket] at hrun
    rw [hrun, known_two_level_pair_update _ _ U (grayControlAddress_ne t)]
    by_cases hc : noWorkPrefixAnd (fun i => q (grayControlWires t i)) k = true
    · have hq : q = grayControlAddress t (q t) := by
        funext w
        by_cases hw : w = t
        · simp [hw, grayControlAddress]
        · simp [hw, grayControlAddress, (grayControls_true_iff t q).mp hc w hw]
      cases hb : q t
      · have hqe : q = grayControlAddress t false := by simpa only [hb] using! hq
        subst q
        rw [if_pos hc]
        simp [grayControlAddress_update, multiWireState, ApplyGate, Matrix.mulVec,
          dotProduct, Qatlib.Foundations.PureStateMath.Ket, (grayControlAddress_ne t).symm]
        module
      · have hqe : q = grayControlAddress t true := by simpa only [hb] using! hq
        subst q
        rw [if_pos hc]
        simp [grayControlAddress_update, multiWireState, ApplyGate, Matrix.mulVec,
          dotProduct, Qatlib.Foundations.PureStateMath.Ket, grayControlAddress_ne t]
        module
    · have hfalse : noWorkPrefixAnd (fun i => q (grayControlWires t i)) k = false :=
        Bool.eq_false_iff.mpr hc
      have hqf : q ≠ grayControlAddress t false := by
        intro he
        subst q
        apply hc
        apply (grayControls_true_iff t _).mpr
        intro w hw
        simp [grayControlAddress, hw]
      have hqt : q ≠ grayControlAddress t true := by
        intro he
        subst q
        apply hc
        apply (grayControls_true_iff t _).mpr
        intro w hw
        simp [grayControlAddress, hw]
      simp [hfalse, applyGate_one, Qatlib.Foundations.PureStateMath.Ket, hqf.symm, hqt.symm]
  refine ⟨gs,hgs,hlen,?_⟩
  intro ψ
  conv_lhs => arg 3; rw [state_ket_expansion ψ]
  rw [run_reflectionCompile_sum]
  simp only [run_reflectionCompile_smul, hk]
  conv_rhs => arg 2; rw [state_ket_expansion ψ]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]

/-- Conjugation by Pauli X reverses both Boolean indices of a two-by-two matrix. -/
private theorem grayReverseBlock (B : Matrix Bool Bool ℂ) :
    PauliX * B * PauliX = fun a b => B (!a) (!b) := by
  ext a b
  cases a <;> cases b <;> simp [PauliX, permMatrix, Matrix.mul_apply]

/-- Reversing the ordered address pair and conjugating its block by Pauli X preserves the
two-level matrix. -/
private theorem grayPair_reverse {k : ℕ} (x y : Reg (k+1)) (hxy : x ≠ y)
    (B : Matrix Bool Bool ℂ) :
    twoLevelMatrix (.pair y x (PauliX*B*PauliX)) = twoLevelMatrix (.pair x y B) := by
  rw [grayReverseBlock]
  ext u v
  by_cases hux : u = x <;> by_cases huy : u = y <;>
    by_cases hvx : v = x <;> by_cases hvy : v = y <;>
    by_cases huv : u = v <;> simp_all [twoLevelMatrix]

/-- A unitary on two addresses differing at exactly the specified wire has a legal
reflection-word implementation of length at most `256 * (k + 1)^2 + 2 * k`. -/
theorem grayAdjacentPair_table {k : ℕ} (x y : Reg (k+1)) (t : Fin (k+1))
    (ht : x t ≠ y t) (hother : ∀ w, w ≠ t → x w = y w)
    (B : Matrix Bool Bool ℂ) (hB : B ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
      gs.length ≤ 256*(k+1)^2 + 2*k ∧ ∀ ψ : QState (Reg (k+1)),
        Run 1 (reflectionCompile gs) ψ = twoLevelMatrix (.pair x y B) *ᵥ ψ := by
  have hxy : x ≠ y := fun he => ht (congrFun he t)
  let as := knownAddressFlips x (grayControlAddress t (x t))
  have has : reflectionLegal as := (knownAddressFlips_spec x _).1
  have halen : as.length ≤ k := by
    simp only [as, knownAddressFlips, knownFlipSteps, List.length_map, Finset.length_toList]
    calc
      _ ≤ ((Finset.univ : Finset (Fin (k+1))).erase t).card := by
        apply Finset.card_le_card
        intro w hw
        have hne := (Finset.mem_filter.mp hw).2
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_univ _⟩
        intro he
        subst w
        simp [grayControlAddress] at hne
      _ = k := by simp
  let A := reflectionProgramMatrix as
  have hA : A ∈ unitaryGroup (Reg (k+1)) ℂ := reflectionProgramMatrix_unitary as has
  have hx : A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket (grayControlAddress t (x t)) := by
    simpa only [A, run_reflectionCompile, ApplyGate] using! (knownAddressFlips_spec x _).2.2
  have hy : A *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket (grayControlAddress t (y t)) := by
    change ApplyGate (reflectionProgramMatrix as) (Qatlib.Foundations.PureStateMath.Ket y) = _
    rw [← run_reflectionCompile]
    dsimp only [as]
    rw [knownAddressFlips, knownFlipSteps_action _ (Finset.nodup_toList _)]
    congr 1
    funext w
    by_cases hw : w = t
    · subst w
      simp [Finset.mem_toList, grayControlAddress]
    · simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
        grayControlAddress, if_neg hw, hother w hw]
      cases y w <;> simp
  let rs := reflectionAdjoint as
  have hrs : reflectionLegal rs := reflectionAdjoint_legal as has
  have hrlen : rs.length = as.length := reflectionAdjoint_length as
  have hlocal (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
      ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
        gs.length ≤ 256*(k+1)^2 + 2*k ∧ ∀ ψ : QState (Reg (k+1)),
          Run 1 (reflectionCompile gs) ψ =
            Aᴴ *ᵥ (twoLevelMatrix (.pair (grayControlAddress t false)
              (grayControlAddress t true) U) *ᵥ (A *ᵥ ψ)) := by
    obtain ⟨bs,hbs,hblen,hb⟩ := grayCanonicalPair_table t U hU
    refine ⟨as ++ bs ++ rs, ?_, ?_, ?_⟩
    · simp only [reflectionLegal_append]
      exact ⟨⟨has,hbs⟩,hrs⟩
    · simp only [List.length_append,hrlen]
      omega
    · intro ψ
      rw [reflectionCompile_append,reflectionCompile_append,run_append,run_append,
        run_reflectionCompile,hb,run_reflectionCompile,reflectionAdjoint_matrix as has]
      rfl
  cases hb : x t
  · have hyb : y t = true := by cases he : y t <;> simp_all
    obtain ⟨gs,hgs,hlen,hr⟩ := hlocal B hB
    refine ⟨gs,hgs,hlen,?_⟩
    intro ψ
    rw [hr]
    apply known_two_level_unitary_conjugate A hA x y _ _ hxy (grayControlAddress_ne t)
    · simpa only [hb] using! hx
    · simpa only [hyb] using! hy
  · have hyb : y t = false := by cases he : y t <;> simp_all
    have hU : PauliX*B*PauliX ∈ unitaryGroup Bool ℂ :=
      (unitaryGroup Bool ℂ).mul_mem ((unitaryGroup Bool ℂ).mul_mem pauliX_unitary hB) pauliX_unitary
    obtain ⟨gs,hgs,hlen,hr⟩ := hlocal (PauliX*B*PauliX) hU
    refine ⟨gs,hgs,hlen,?_⟩
    intro ψ
    rw [hr]
    have he := known_two_level_unitary_conjugate A hA y x _ _ hxy.symm
      (grayControlAddress_ne t) (by simpa only [hyb] using! hy)
      (by simpa only [hb] using! hx) (PauliX*B*PauliX) ψ
    rw [he, grayPair_reverse x y hxy B]

/-- The finite set of wire positions at which two register addresses differ. -/
def grayDifference {n : ℕ} (x y : Reg n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => x w ≠ y w)

/-- The difference set is empty exactly when the two register addresses are equal. -/
private theorem grayDifference_empty {n : ℕ} (x y : Reg n) :
    grayDifference x y = ∅ ↔ x = y := by
  constructor
  · intro h
    funext w
    by_contra hw
    have hm : w ∈ grayDifference x y := by simp [grayDifference, hw]
    rw [h] at hm
    simp at hm
  · rintro rfl
    simp [grayDifference]

/-- Updating one coordinate of `x` to its value in `y` removes that coordinate from the
difference set. -/
theorem grayDifference_update {n : ℕ} (x y : Reg n) (t : Fin n) :
    grayDifference (Function.update x t (y t)) y = (grayDifference x y).erase t := by
  ext w
  by_cases hw : w = t
  · subst w
    simp [grayDifference]
  · simp [grayDifference, hw]

/-- The two-level Pauli X block on distinct addresses `x` and `z` sends the ket at `x` to the
ket at `z`. -/
private theorem graySwap_ket {n : ℕ} (x z : Reg n) (hxz : x ≠ z) :
    twoLevelMatrix (.pair x z PauliX) *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket z := by
  rw [known_two_level_pair_update x z PauliX hxz]
  simp [Qatlib.Foundations.PureStateMath.Ket, hxz.symm, PauliX, permMatrix]

/-- The two-level Pauli X block fixes every basis ket outside its two distinct addresses. -/
private theorem graySwap_other_ket {n : ℕ} (x z q : Reg n)
    (hxz : x ≠ z) (hqx : q ≠ x) (hqz : q ≠ z) :
    twoLevelMatrix (.pair x z PauliX) *ᵥ Qatlib.Foundations.PureStateMath.Ket q = Qatlib.Foundations.PureStateMath.Ket q := by
  rw [known_two_level_pair_update x z PauliX hxz]
  simp [Qatlib.Foundations.PureStateMath.Ket, hqx.symm, hqz.symm]

/-- A unitary on distinct addresses `x` and `y` has a legal reflection-word implementation of
length at most `(2 * d - 1) * (256 * (k + 1)^2 + 2 * k)`, where `d` is their Hamming
distance. The compiled word acts as the two-level matrix on every state. -/
theorem grayPair_table {k : ℕ} (x y : Reg (k+1)) (hxy : x ≠ y)
    (B : Matrix Bool Bool ℂ) (hB : B ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
      gs.length ≤ (2*(grayDifference x y).card-1) * (256*(k+1)^2+2*k) ∧
      ∀ ψ : QState (Reg (k+1)), Run 1 (reflectionCompile gs) ψ =
        twoLevelMatrix (.pair x y B) *ᵥ ψ := by
  classical
  have hgeneral (d : ℕ) : ∀ (x y : Reg (k+1)), (grayDifference x y).card = d → x ≠ y →
      ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
        gs.length ≤ (2*d-1) * (256*(k+1)^2+2*k) ∧
        ∀ ψ : QState (Reg (k+1)), Run 1 (reflectionCompile gs) ψ =
          twoLevelMatrix (.pair x y B) *ᵥ ψ := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro x y hd hxy
      have hdpos : 0 < d := by
        rw [← hd, Finset.card_pos]
        by_contra he
        apply hxy
        apply (grayDifference_empty x y).mp
        exact Finset.not_nonempty_iff_eq_empty.mp he
      obtain ⟨t,ht⟩ : ∃ t, x t ≠ y t := by
        by_contra he
        push Not at he
        exact hxy (funext he)
      have htm : t ∈ grayDifference x y := by simp [grayDifference, ht]
      by_cases hd1 : d = 1
      · have hsingle : grayDifference x y = {t} := by
          obtain ⟨w,hw⟩ := Finset.card_eq_one.mp (hd.trans hd1)
          have htw : t = w := by simpa only [hw,Finset.mem_singleton] using! htm
          simpa only [← htw] using! hw
        have hother : ∀ w, w ≠ t → x w = y w := by
          intro w hw
          by_contra he
          have hm : w ∈ grayDifference x y := by simp [grayDifference, he]
          rw [hsingle] at hm
          exact hw (Finset.mem_singleton.mp hm)
        obtain ⟨gs,hgs,hlen,hr⟩ := grayAdjacentPair_table x y t ht hother B hB
        refine ⟨gs,hgs,?_,hr⟩
        simpa only [hd1, Nat.reduceMul, Nat.reduceSub, one_mul] using! hlen
      · let z := Function.update x t (y t)
        have hzcard : (grayDifference z y).card = d-1 := by
          rw [grayDifference_update, Finset.card_erase_of_mem htm, hd]
        have hzy : z ≠ y := by
          intro he
          have hempty := (grayDifference_empty z y).mpr he
          rw [hempty, Finset.card_empty] at hzcard
          omega
        have hxz : x ≠ z := by
          intro he
          have het := congrFun he t
          simp only [z,Function.update_self] at het
          exact ht het
        obtain ⟨as,has,halen,ha⟩ := grayAdjacentPair_table x z t
          (by simpa only [z,Function.update_self] using! ht)
          (fun w hw => by simp [z,hw]) PauliX pauliX_unitary
        obtain ⟨bs,hbs,hblen,hb⟩ := ih (d-1) (by omega) z y hzcard hzy
        let rs := reflectionAdjoint as
        have hrs : reflectionLegal rs := reflectionAdjoint_legal as has
        have hrlen : rs.length = as.length := reflectionAdjoint_length as
        let A := reflectionProgramMatrix as
        have hA : A ∈ unitaryGroup (Reg (k+1)) ℂ := reflectionProgramMatrix_unitary as has
        have hx : A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket z := by
          have hh := (ha (Qatlib.Foundations.PureStateMath.Ket x)).trans (graySwap_ket x z hxz)
          simpa only [A,run_reflectionCompile,ApplyGate] using! hh
        have hy : A *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket y := by
          have hh :=
              (ha (Qatlib.Foundations.PureStateMath.Ket y)).trans
              (graySwap_other_ket x z y hxz hxy.symm hzy.symm)
          simpa only [A,run_reflectionCompile,ApplyGate] using! hh
        refine ⟨as ++ bs ++ rs, ?_, ?_, ?_⟩
        · simp only [reflectionLegal_append]
          exact ⟨⟨has,hbs⟩,hrs⟩
        · simp only [List.length_append,hrlen]
          calc
            _ ≤ (256*(k+1)^2+2*k) + (2*(d-1)-1)*(256*(k+1)^2+2*k) +
                (256*(k+1)^2+2*k) := add_le_add (add_le_add halen hblen) halen
            _ = ((2*(d-1)-1)+2)*(256*(k+1)^2+2*k) := by ring
            _ = _ := by congr 1; omega
        · intro ψ
          rw [reflectionCompile_append,reflectionCompile_append,run_append,run_append,
            run_reflectionCompile,hb,run_reflectionCompile,reflectionAdjoint_matrix as has]
          exact known_two_level_unitary_conjugate A hA x y z y hxy hzy hx hy B ψ
  exact hgeneral _ x y rfl hxy

end Qatlib.Concepts.GateTables.GrayUniversal
