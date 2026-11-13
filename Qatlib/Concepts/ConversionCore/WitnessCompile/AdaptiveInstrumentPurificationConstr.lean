/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationStat
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetPhaseWordAssemblyQuan
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.List.GetD

/-!
# Register constructions for adaptive purification

Explicit register permutations and basis frames extend source gates and alphabet oracles to a
purification space containing a branch record and a spare address register. The constructions
preserve unitarity and intertwine the original operators with their embedded versions.

`sourcePurify_swapLayer` and `sourcePurifyFlip_conj` provide the oracle identities used to
synchronize adaptive branches. These are finite register implementations in the circuit
framework of [NielsenChuang2010].

## Main statements

* `sourcePurifyIn` and `sourcePurifyOut`: initialization and output embeddings.
* `sourcePurifyGate_unitary`: unitarity of lifted known gates.
* `sourcePurify_swapLayer`: the spare-address identity for a clean state.
* `sourcePurifyFlip_conj`: conjugation implementing the adjoint oracle.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.HspRecovery.RecordExtract

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
noncomputable section

/-- Multiplying the matrices of two finite-register maps gives the matrix of their composition. -/
theorem sourcePermMatrix_mul {T : Type} [Fintype T] [DecidableEq T]
    (f g : T → T) :
    permMatrix f * permMatrix g=permMatrix (f ∘ g) := by
  ext i j
  simp only [Matrix.mul_apply,permMatrix,Matrix.of_apply,Function.comp_apply]
  rw [Finset.sum_eq_single (g j)]
  · by_cases h : i=f (g j) <;> simp [h]
  · intro k _ hk
    simp [hk]
  · simp
end
noncomputable section

/-- The conjugate transpose of an equivalence permutation matrix is the permutation matrix of
its inverse. -/
theorem sourcePermMatrix_conjTranspose {T : Type} [Fintype T] [DecidableEq T]
    (e : T ≃ T) : (permMatrix ⇑e)ᴴ=permMatrix ⇑e.symm := by
  ext i j
  simp only [Matrix.conjTranspose_apply,permMatrix,Matrix.of_apply]
  by_cases h : j=e i
  · rw [if_pos h,star_one,if_pos]
    exact ((congrArg e.symm h).trans (Equiv.symm_apply_apply e i)).symm
  · rw [if_neg h,star_zero,if_neg]
    intro hi
    exact h ((Equiv.symm_apply_eq e).mp hi.symm)
end
noncomputable section

/-- A permutation matrix acts on a state by precomposition with the inverse equivalence. -/
theorem sourcePermMatrix_equiv_mulVec {T : Type} [Fintype T] [DecidableEq T]
    (e : T ≃ T) (φ : QState T) : permMatrix ⇑e *ᵥ φ=fun i => φ (e.symm i) := by
  ext i
  simp only [Matrix.mulVec,dotProduct,permMatrix,Matrix.of_apply]
  rw [Finset.sum_eq_single (e.symm i)]
  · simp [Equiv.apply_symm_apply]
  · intro k _ hk
    have h : i≠e k := fun hh =>
      hk (((Equiv.symm_apply_apply e k).symm).trans (congrArg e.symm hh).symm)
    simp [h]
  · simp
end
noncomputable section

/-- The source-register equivalence that adds the padded input symbol to the value register. -/
def sourceSmallShift {X H : Type} {n q : ℕ} (input : X → Fin n → Fin (q+1)) (x : X) {r : ℕ} :
    SourceSpace n q H r ≃ SourceSpace n q H r where
  toFun s := ((s.1.1,s.1.2+sourcePaddedSymbol input x s.1.1),s.2)
  invFun s := ((s.1.1,s.1.2-sourcePaddedSymbol input x s.1.1),s.2)
  left_inv s := by rcases s with ⟨⟨a,v⟩,bj⟩; simp
  right_inv s := by rcases s with ⟨⟨a,v⟩,bj⟩; simp
end
noncomputable section

/-- The source alphabet oracle is the permutation matrix of `sourceSmallShift`. -/
theorem sourceAlphabetOracle_eq_permMatrix {X H : Type} [DecidableEq H] {n q r : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    sourceAlphabetOracle (W:=(Bool × H) × Fin r) input x=
      permMatrix ⇑(sourceSmallShift (r:=r) input x) := by
  ext p t
  rcases p with ⟨⟨a,v⟩,bj⟩
  rcases t with ⟨⟨a',v'⟩,bj'⟩
  simp [sourceAlphabetOracle,permMatrix,sourceSmallShift,Prod.ext_iff]
end
noncomputable section

/-- The involutive source-register equivalence that negates the value register. -/
def sourceSmallFlip {H : Type} {n q r : ℕ} :
    SourceSpace n q H r ≃ SourceSpace n q H r where
  toFun s := ((s.1.1,-s.1.2),s.2)
  invFun s := ((s.1.1,-s.1.2),s.2)
  left_inv s := by rcases s with ⟨⟨a,v⟩,bj⟩; simp
  right_inv s := by rcases s with ⟨⟨a,v⟩,bj⟩; simp
end
noncomputable section

/-- Conjugating the source shift by value negation gives its inverse. -/
theorem sourceSmallFlip_conj_shift {X H : Type} {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) {r : ℕ} :
    (sourceSmallShift (H:=H) (r:=r) input x).symm=
      (sourceSmallFlip (H:=H) (n:=n) (q:=q) (r:=r)).trans
        ((sourceSmallShift (H:=H) (r:=r) input x).trans (sourceSmallFlip (H:=H) (n:=n) (q:=q) (r:=r))) := by
  apply Equiv.ext
  rintro ⟨⟨a,v⟩,bj⟩
  show ((a,v-sourcePaddedSymbol input x a),bj)=((a,-(-v+sourcePaddedSymbol input x a)),bj)
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · show v-sourcePaddedSymbol input x a=-(-v+sourcePaddedSymbol input x a)
      rw [neg_add_rev,neg_neg,sub_eq_add_neg]
      exact add_comm _ _
  · rfl
end
noncomputable section

/-- The lift of a source-register equivalence that preserves the branch record and spare address
register. -/
def sourcePurifyLift {H : Type} {n q r L : ℕ}
    (e : SourceSpace n q H r ≃ SourceSpace n q H r) :
    Fin L × SourceSpace n q H r × Fin (n+1) ≃ Fin L × SourceSpace n q H r × Fin (n+1) where
  toFun y := (y.1,e y.2.1,y.2.2)
  invFun y := (y.1,e.symm y.2.1,y.2.2)
  left_inv y := by rcases y with ⟨l,s,w⟩; simp
  right_inv y := by rcases y with ⟨l,s,w⟩; simp
end
noncomputable section

/-- The involution that swaps the source address with the spare address register. -/
def sourcePurifySwap {H : Type} {n q r L : ℕ} :
    Fin L × SourceSpace n q H r × Fin (n+1) ≃ Fin L × SourceSpace n q H r × Fin (n+1) where
  toFun y := (y.1,((y.2.2,y.2.1.1.2),y.2.1.2),y.2.1.1.1)
  invFun y := (y.1,((y.2.2,y.2.1.1.2),y.2.1.2),y.2.1.1.1)
  left_inv y := by rcases y with ⟨l,⟨⟨a,v⟩,bj⟩,w⟩; rfl
  right_inv y := by rcases y with ⟨l,⟨⟨a,v⟩,bj⟩,w⟩; rfl
end
noncomputable section

/-- The permutation matrix that negates the source value register in the purification space. -/
def sourcePurifyFlipGate {H : Type} [DecidableEq H] {n q r L : ℕ} :
    Matrix (Fin L × SourceSpace n q H r × Fin (n+1))
      (Fin L × SourceSpace n q H r × Fin (n+1)) ℂ :=
  permMatrix ⇑(sourcePurifyLift (sourceSmallFlip (H:=H) (n:=n) (q:=q) (r:=r)))
end
noncomputable section

/-- The permutation matrix that swaps the source and spare address registers. -/
def sourcePurifySwapGate {H : Type} [DecidableEq H] {n q r L : ℕ} :
    Matrix (Fin L × SourceSpace n q H r × Fin (n+1))
      (Fin L × SourceSpace n q H r × Fin (n+1)) ℂ :=
  permMatrix ⇑(sourcePurifySwap (H:=H) (n:=n) (q:=q) (r:=r) (L:=L))
end
noncomputable section

/-- The source alphabet oracle lifted to the purification space while preserving record and
spare address. -/
def sourcePurifyOracle {X H : Type} [DecidableEq H] {n q : ℕ} (input : X → Fin n → Fin (q+1)) (x : X)
    {r L : ℕ} : Matrix (Fin L × SourceSpace n q H r × Fin (n+1))
      (Fin L × SourceSpace n q H r × Fin (n+1)) ℂ :=
  permMatrix ⇑(sourcePurifyLift (sourceSmallShift (r:=r) input x))
end
noncomputable section

/-- The lifted purification oracle is unitary. -/
theorem sourcePurifyOracle_unitary {X H : Type} [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) {r L : ℕ} :
    sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L) ∈
      Matrix.unitaryGroup (Fin L × SourceSpace n q H r × Fin (n+1)) ℂ :=
  permMatrix_unitary_of_injective (Equiv.injective _)
end
noncomputable section

/-- On states supported at the padded spare address `n`, the swap-adjoint-oracle-swap-oracle
layer acts as the lifted oracle. -/
theorem sourcePurify_swapLayer {X H : Type} [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    {n q r L : ℕ} (input : X → Fin n → Fin (q+1)) (x : X)
    (st : QState (Fin L × SourceSpace n q H r × Fin (n+1)))
    (hclean : ∀ (l : Fin L) (s : SourceSpace n q H r) (w : Fin (n+1)),
      w≠(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1)) → st (l,s,w)=0) :
    (permMatrix ⇑(sourcePurifySwap (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)) *
      (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L))ᴴ *
      permMatrix ⇑(sourcePurifySwap (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)) *
      sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L)) *ᵥ st=
    sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L) *ᵥ st := by
  set σe := sourcePurifyLift (sourceSmallShift (r:=r) input x) with hσ
  set τe := sourcePurifySwap (H:=H) (n:=n) (q:=q) (r:=r) (L:=L) with hτ
  have s1 : sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L) *ᵥ st=
      fun y => st (σe.symm y) := sourcePermMatrix_equiv_mulVec σe st
  have s2 : permMatrix ⇑τe *ᵥ (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L) *ᵥ st)=
      fun y => st (σe.symm (τe.symm y)) := by
    rw [s1]
    exact sourcePermMatrix_equiv_mulVec τe _
  have s3 : (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L))ᴴ *ᵥ
      (permMatrix ⇑τe *ᵥ (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L) *ᵥ st))=
      fun y => st (σe.symm (τe.symm (σe y))) := by
    rw [s2]
    have h := sourcePermMatrix_equiv_mulVec σe.symm
      (fun y => st (σe.symm (τe.symm y)))
    rw [Equiv.symm_symm] at h
    rw [hσ,hτ,sourcePurifyOracle,sourcePermMatrix_conjTranspose]
    exact h
  have s4 : permMatrix ⇑τe *ᵥ ((sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L))ᴴ *ᵥ
      (permMatrix ⇑τe *ᵥ (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L) *ᵥ st)))=
      fun y => st (σe.symm (τe.symm (σe (τe.symm y)))) := by
    rw [s3]
    exact sourcePermMatrix_equiv_mulVec τe _
  calc (permMatrix ⇑τe * (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L))ᴴ *
        permMatrix ⇑τe * sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L)) *ᵥ st
      = permMatrix ⇑τe *ᵥ ((sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L))ᴴ *ᵥ
        (permMatrix ⇑τe *ᵥ (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L) *ᵥ st))) := by
        simp only [← Matrix.mulVec_mulVec]
    _ = fun y => st (σe.symm (τe.symm (σe (τe.symm y)))) := s4
    _ = fun y => st (σe.symm y) := by
        funext y
        obtain ⟨l,⟨⟨a,v⟩,bj⟩,w⟩ := y
        by_cases hw : w=(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1))
        · subst hw
          show st (l,((a,v+sourcePaddedSymbol input x ⟨n,Nat.lt_succ_self n⟩-
            sourcePaddedSymbol input x a),bj),⟨n,Nat.lt_succ_self n⟩)=
            st (l,((a,v-sourcePaddedSymbol input x a),bj),⟨n,Nat.lt_succ_self n⟩)
          simp [sourcePaddedSymbol]
        · show st (l,((a,v+sourcePaddedSymbol input x w-sourcePaddedSymbol input x a),bj),w)=
            st (l,((a,v-sourcePaddedSymbol input x a),bj),w)
          rw [hclean l ((a,v+sourcePaddedSymbol input x w-sourcePaddedSymbol input x a),bj) w hw,
            hclean l ((a,v-sourcePaddedSymbol input x a),bj) w hw]
    _ = sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L) *ᵥ st := s1.symm
end
noncomputable section

/-- Summing over the purification space with record and spare address fixed reduces to a sum
over source states. -/
theorem sourcePurifyGate_sum {H : Type} [Fintype H] [DecidableEq H] {n q r L : ℕ}
    (f : Fin L → SourceSpace n q H r → Fin (n+1) → ℂ)
    (l : Fin L) (w : Fin (n+1)) :
    (∑ y : Fin L × SourceSpace n q H r × Fin (n+1),
      (if y.1=l ∧ y.2.2=w then f y.1 y.2.1 y.2.2 else 0))=
    ∑ s : SourceSpace n q H r, f l s w := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single l]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s'' _
    rw [Finset.sum_eq_single w]
    · simp
    · intro w'' _ hw''
      simp [hw'']
    · simp
  · intro l'' _ hll''
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro s'' _
    apply Finset.sum_eq_zero
    intro w'' _
    simp [hll'']
  · simp
end
noncomputable section

/-- The lifted source matrix acting identically on the record and spare address registers. -/
def sourcePurifyGate {H : Type} [DecidableEq H] {n q r L : ℕ}
    (U : Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ) :
    Matrix (Fin L × SourceSpace n q H r × Fin (n+1))
      (Fin L × SourceSpace n q H r × Fin (n+1)) ℂ :=
  fun y y' => if y.1=y'.1 ∧ y.2.2=y'.2.2 then U y.2.1 y'.2.1 else 0
end
noncomputable section

/-- Lifting source matrices to purification gates preserves multiplication. -/
theorem sourcePurifyGate_mul {H : Type} [Fintype H] [DecidableEq H] {n q r L : ℕ}
    (U V : Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ) :
    sourcePurifyGate (n:=n) (q:=q) (r:=r) (L:=L) (U*V)=
      sourcePurifyGate (n:=n) (q:=q) (r:=r) (L:=L) U*sourcePurifyGate (n:=n) (q:=q) (L:=L) V := by
  ext ⟨l,s,w⟩ ⟨l',s',w'⟩
  simp only [sourcePurifyGate,Matrix.mul_apply]
  by_cases h : l=l' ∧ w=w'
  · obtain ⟨rfl,rfl⟩ := h
    rw [if_pos ⟨rfl,rfl⟩]
    have key : ∀ x : Fin L × SourceSpace n q H r × Fin (n+1),
        (if l=x.1 ∧ w=x.2.2 then U s x.2.1 else 0)*(if x.1=l ∧ x.2.2=w then V x.2.1 s' else 0)=
        (if x.1=l ∧ x.2.2=w then U s x.2.1*V x.2.1 s' else 0) := by
      intro ⟨l'',s'',w''⟩
      show (if l=l'' ∧ w=w'' then U s s'' else 0)*(if l''=l ∧ w''=w then V s'' s' else 0)=
        (if l''=l ∧ w''=w then U s s''*V s'' s' else 0)
      by_cases h1 : l=l'' ∧ w=w''
      · obtain ⟨rfl,rfl⟩ := h1
        rw [if_pos ⟨rfl,rfl⟩,if_pos ⟨rfl,rfl⟩,if_pos ⟨rfl,rfl⟩]
      · have h2 : ¬(l''=l ∧ w''=w) := fun ⟨a,b⟩ => h1 ⟨a.symm,b.symm⟩
        simp [h1,h2]
    rw [Finset.sum_congr rfl (fun x _ => key x),sourcePurifyGate_sum
      (fun l'' s'' w'' => U s s''*V s'' s') l w]
  · rw [if_neg h,eq_comm]
    apply Finset.sum_eq_zero
    intro ⟨l'',s'',w''⟩ _
    by_cases h1 : l=l'' ∧ w=w''
    · obtain ⟨rfl,rfl⟩ := h1
      by_cases h2 : l=l' ∧ w=w'
      · exact absurd h2 h
      · rw [if_pos ⟨rfl,rfl⟩,if_neg h2,mul_zero]
    · rw [if_neg h1,zero_mul]
end
noncomputable section

/-- Lifting the identity source matrix gives the identity purification gate. -/
theorem sourcePurifyGate_one {H : Type} [Fintype H] [DecidableEq H] {n q r L : ℕ} :
    sourcePurifyGate (n:=n) (q:=q) (r:=r) (L:=L)
      (1 : Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ)=1 := by
  ext ⟨l,s,w⟩ ⟨l',s',w'⟩
  simp only [sourcePurifyGate,Matrix.one_apply,Prod.mk.injEq]
  by_cases h : l=l' ∧ w=w'
  · obtain ⟨rfl,rfl⟩ := h
    by_cases hs : s=s' <;> simp [hs]
  · rw [if_neg h,if_neg]
    exact fun hh => h ⟨hh.1,hh.2.2⟩
end
noncomputable section

/-- Lifting a source matrix commutes with conjugate transpose. -/
theorem sourcePurifyGate_conjTranspose {H : Type} [Fintype H] [DecidableEq H] {n q r L : ℕ}
    (U : Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ) :
    (sourcePurifyGate (n:=n) (q:=q) (r:=r) (L:=L) U)ᴴ=
      sourcePurifyGate (n:=n) (q:=q) (r:=r) (L:=L) Uᴴ := by
  ext ⟨l,s,w⟩ ⟨l',s',w'⟩
  simp only [sourcePurifyGate,Matrix.conjTranspose_apply]
  by_cases h : l=l' ∧ w=w'
  · obtain ⟨rfl,rfl⟩ := h
    simp
  · rw [if_neg (fun hh => h ⟨hh.1.symm,hh.2.symm⟩),if_neg h,star_zero]
end
noncomputable section

/-- Lifting a unitary source matrix gives a unitary purification gate. -/
theorem sourcePurifyGate_unitary {H : Type} [Fintype H] [DecidableEq H] {n q r L : ℕ}
    (U : Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ)
    (hU : U ∈ Matrix.unitaryGroup _ ℂ) :
    sourcePurifyGate (n:=n) (q:=q) (r:=r) (L:=L) U ∈ Matrix.unitaryGroup _ ℂ := by
  have hu : Uᴴ*U=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.1
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,sourcePurifyGate_conjTranspose,
    ← sourcePurifyGate_mul,hu,sourcePurifyGate_one]
end
noncomputable section

/-- The basis embedding initializing record zero and spare address `n`. -/
def sourcePurifyIn {H : Type} [DecidableEq H] {n q r L : ℕ} (hL : 0 < L) :
    Matrix (Fin L × SourceSpace n q H r × Fin (n+1)) (SourceSpace n q H r) ℂ :=
  sourceBasisFrame (fun t : SourceSpace n q H r => (⟨0,hL⟩,t,⟨n,Nat.lt_succ_self n⟩))
end
noncomputable section

/-- The basis embedding adjoining spare address `n` to an already recorded source state. -/
def sourcePurifyOut {H : Type} [DecidableEq H] {n q r L : ℕ} :
    Matrix (Fin L × SourceSpace n q H r × Fin (n+1)) (Fin L × SourceSpace n q H r) ℂ :=
  sourceBasisFrame (fun p : Fin L × SourceSpace n q H r => (p.1,p.2,⟨n,Nat.lt_succ_self n⟩))
end
noncomputable section

/-- The purification input embedding is an isometry. -/
theorem sourcePurifyIn_isometry {H : Type} [Fintype H] [DecidableEq H] {n q r L : ℕ}
    (hL : 0 < L) : (sourcePurifyIn (H := H) (n:=n) (q:=q) (r:=r) (L:=L) hL)ᴴ*
      sourcePurifyIn (H := H) (n:=n) (q:=q) (r:=r) (L:=L) hL=1 := by
  unfold sourcePurifyIn
  apply sourceBasisFrame_isometry
  intro t t' h
  exact congrArg (fun y => y.2.1) h
end
noncomputable section

/-- The purification output embedding is an isometry. -/
theorem sourcePurifyOut_isometry {H : Type} [Fintype H] [DecidableEq H] {n q r L : ℕ} :
    (sourcePurifyOut (H := H) (n:=n) (q:=q) (r:=r) (L:=L))ᴴ*
      sourcePurifyOut (H := H) (n:=n) (q:=q) (r:=r) (L:=L)=1 := by
  unfold sourcePurifyOut
  apply sourceBasisFrame_isometry
  intro t t' h
  have h' := Prod.ext_iff.mp h
  exact Prod.ext h'.1 (Prod.ext_iff.mp h'.2).1
end
noncomputable section

/-- The purification input embedding places the original amplitudes at record zero and spare
address `n`, with zero amplitudes elsewhere. -/
theorem sourcePurifyIn_apply {H : Type} [Fintype H] [DecidableEq H] {n q r L : ℕ} (hL : 0 < L)
    (ψ : QState (SourceSpace n q H r)) :
    sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=L) hL *ᵥ ψ=
      fun y : Fin L × SourceSpace n q H r × Fin (n+1) =>
        if y.1=⟨0,hL⟩ ∧ y.2.2=⟨n,Nat.lt_succ_self n⟩ then ψ y.2.1 else 0 := by
  funext ⟨l,s,w⟩
  simp only [sourcePurifyIn,sourceBasisFrame,Matrix.mulVec,dotProduct]
  rw [Finset.sum_eq_single s]
  · by_cases h : (l,s,w)=(⟨0,hL⟩,s,⟨n,Nat.lt_succ_self n⟩)
    · rw [if_pos h]
      simp only [Prod.mk.injEq] at h
      rw [if_pos ⟨h.1,h.2.2⟩]
      simp
    · rw [if_neg h,if_neg]
      · simp
      · intro hh
        exact h (Prod.ext hh.1 (Prod.ext rfl hh.2))
  · intro t _ ht
    by_cases h : (l,s,w)=(⟨0,hL⟩,t,⟨n,Nat.lt_succ_self n⟩)
    · simp only [Prod.mk.injEq] at h
      exact absurd h.2.1 (Ne.symm ht)
    · simp [h]
  · simp
end
noncomputable section

/-- The purification output embedding preserves recorded amplitudes at spare address `n` and
vanishes elsewhere. -/
theorem sourcePurifyOut_apply {H : Type} [Fintype H] [DecidableEq H] {n q r L : ℕ}
    (φ : QState (Fin L × SourceSpace n q H r)) :
    sourcePurifyOut (n:=n) (q:=q) (r:=r) (L:=L) *ᵥ φ=
      fun y : Fin L × SourceSpace n q H r × Fin (n+1) =>
        if y.2.2=⟨n,Nat.lt_succ_self n⟩ then φ (y.1,y.2.1) else 0 := by
  funext ⟨l,s,w⟩
  simp only [sourcePurifyOut,sourceBasisFrame,Matrix.mulVec,dotProduct]
  rw [Finset.sum_eq_single (l,s)]
  · by_cases h : (l,s,w)=(l,s,⟨n,Nat.lt_succ_self n⟩)
    · rw [if_pos h]
      simp only [Prod.mk.injEq] at h
      rw [if_pos h.2.2]
      simp
    · rw [if_neg h,if_neg]
      · simp
      · intro hh
        exact h (Prod.ext rfl (Prod.ext rfl hh))
  · intro ⟨l',s'⟩ _ ht
    by_cases h : (l,s,w)=(l',s',⟨n,Nat.lt_succ_self n⟩)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl,rfl,_⟩ := h
      exact absurd rfl ht
    · simp [h]
  · simp
end
noncomputable section

/-- A matrix intertwines a basis frame with another matrix if its entries agree on the encoded
image and its encoded columns vanish outside that image. -/
theorem sourceBasisFrame_commute_mul {S T : Type} [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T]
    (c : T → S) (hc : Function.Injective c) (A : Matrix S S ℂ) (B : Matrix T T ℂ)
    (h1 : ∀ t t', A (c t) (c t')=B t t')
    (h2 : ∀ s t, (∀ t₀, s≠c t₀) → A s (c t)=0) :
    A*sourceBasisFrame c=sourceBasisFrame c*B := by
  ext s t
  simp only [Matrix.mul_apply,sourceBasisFrame]
  rw [Finset.sum_eq_single (c t)]
  · rw [if_pos rfl,mul_one]
    by_cases hs : ∃ t₀, s=c t₀
    · obtain ⟨t₀,rfl⟩ := hs
      rw [h1,Finset.sum_eq_single t₀]
      · rw [if_pos rfl,one_mul]
      · intro t' _ ht'
        rw [if_neg (fun hh => ht' ((hc hh).symm)),zero_mul]
      · simp
    · rw [h2 s t (fun t₀ ht₀ => hs ⟨t₀,ht₀⟩)]
      symm
      apply Finset.sum_eq_zero
      intro t' _
      by_cases h' : s=c t'
      · exact absurd ⟨t',h'⟩ hs
      · rw [if_neg h',zero_mul]
  · intro y _ hyt
    rw [if_neg hyt,mul_zero]
  · simp
end
noncomputable section

/-- The lifted oracle intertwines the purification input embedding with the original alphabet
oracle. -/
theorem sourcePurifyOracle_mul_in {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q r L : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) (hL : 0 < L) :
    sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L) *
      sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=L) hL=
    sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=L) hL *
      sourceAlphabetOracle (W := (Bool × H) × Fin r) input x := by
  rw [sourceAlphabetOracle_eq_permMatrix]
  unfold sourcePurifyOracle sourcePurifyIn
  refine sourceBasisFrame_permutation
    (S := Fin L × SourceSpace n q H r × Fin (n+1)) (T := SourceSpace n q H r)
    (e := fun t : SourceSpace n q H r => (⟨0,hL⟩,t,⟨n,Nat.lt_succ_self n⟩))
    (σ := ⇑(sourcePurifyLift (sourceSmallShift (r:=r) input x)))
    (τ := sourceSmallShift (r:=r) input x) ?_
  intro t
  rfl
end
noncomputable section

/-- A matrix intertwining identity yields the corresponding equality after applying both sides
to a state. -/
theorem sourcePurify_narrow {H S T : Type} [Fintype H] [DecidableEq H] [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T]
    (A : Matrix S S ℂ) (B : Matrix H H ℂ) (F : Matrix S H ℂ) (ψ : QState H)
    (h : A*F=F*B) : A *ᵥ (F *ᵥ ψ)=F *ᵥ (B *ᵥ ψ) := by
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,h]
end
noncomputable section

/-- The lifted known gate intertwines the purification input embedding with the original known
gate. -/
theorem sourcePurifyGate_mul_in {H : Type} [Fintype H] [DecidableEq H] {n q r L : ℕ}
    (U : Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ) (hL : 0 < L) :
    sourcePurifyGate (n:=n) (q:=q) (r:=r) (L:=L) U*sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=L) hL=
    sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=L) hL*U := by
  unfold sourcePurifyIn
  refine sourceBasisFrame_commute_mul
    (S := Fin L × SourceSpace n q H r × Fin (n+1)) (T := SourceSpace n q H r)
    (c := fun t : SourceSpace n q H r => (⟨0,hL⟩,t,⟨n,Nat.lt_succ_self n⟩))
    (A := sourcePurifyGate (n:=n) (q:=q) (r:=r) (L:=L) U) (B := U) ?_ ?_ ?_
  · intro t t' h
    exact congrArg (fun y => y.2.1) h
  · intro t t'
    simp [sourcePurifyGate]
  · intro s t hs
    simp only [sourcePurifyGate]
    by_cases hc : s.1=⟨0,hL⟩ ∧ s.2.2=⟨n,Nat.lt_succ_self n⟩
    · obtain ⟨h1,h2⟩ := hc
      exact (hs s.2.1 (Prod.ext h1 (Prod.ext rfl h2))).elim
    · simp [hc]
end
noncomputable section

/-- Conjugating the lifted oracle by the purification value-negation gate gives the adjoint
lifted oracle. -/
theorem sourcePurifyFlip_conj {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q r L : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=L) *
      sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L) *
      sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=L) =
    (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L))ᴴ := by
  unfold sourcePurifyFlipGate
  have hlift : ∀ w : Fin L × SourceSpace n q H r × Fin (n+1),
      ⇑(sourcePurifyLift (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)
          (sourceSmallFlip (H:=H) (n:=n) (q:=q) (r:=r)))
        (⇑(sourcePurifyLift (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)
            (sourceSmallShift (r:=r) input x))
          (⇑(sourcePurifyLift (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)
              (sourceSmallFlip (H:=H) (n:=n) (q:=q) (r:=r))) w)) =
      ⇑((sourcePurifyLift (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)
        (sourceSmallShift (r:=r) input x)).symm) w := by
    intro ⟨l,s,w⟩
    show (l,sourceSmallFlip (H:=H) (sourceSmallShift (r:=r) input x (sourceSmallFlip (H:=H) s)),w)=
      (l,(sourceSmallShift (r:=r) input x).symm s,w)
    have hc : (sourceSmallShift (r:=r) input x).symm s =
        sourceSmallFlip (H:=H) (sourceSmallShift (r:=r) input x (sourceSmallFlip (H:=H) s)) :=
      congrArg (fun e : SourceSpace n q H r ≃ SourceSpace n q H r => e s)
        (sourceSmallFlip_conj_shift (H:=H) (r:=r) input x)
    exact Prod.ext rfl (Prod.ext hc.symm rfl)
  ext y z
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,sourcePurifyOracle,permMatrix,
    Matrix.of_apply]
  rw [Finset.sum_eq_single
    (⇑(sourcePurifyLift (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)
      (sourceSmallFlip (H:=H) (n:=n) (q:=q) (r:=r))) z)]
  · rw [Finset.sum_eq_single
      (⇑(sourcePurifyLift (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)
        (sourceSmallShift (r:=r) input x))
        (⇑(sourcePurifyLift (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)
          (sourceSmallFlip (H:=H) (n:=n) (q:=q) (r:=r))) z))]
    · simp only [ite_true,mul_one]
      by_cases h : z = ⇑(sourcePurifyLift (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)
          (sourceSmallShift (r:=r) input x)) y
      · simp [h,hlift]
      · rw [if_neg h,star_zero]
        refine if_neg (fun hh => h ?_)
        rw [hlift z] at hh
        have hy : ⇑(sourcePurifyLift (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)
            (sourceSmallShift (r:=r) input x)) y = z := by
          rw [hh,Equiv.apply_symm_apply]
        exact hy.symm
    · intro j _ hj
      simp [hj]
    · simp
  · intro k _ hk
    simp [hk]
  · simp
end
end Qatlib.Concepts.ConversionCore.WitnessCompile
