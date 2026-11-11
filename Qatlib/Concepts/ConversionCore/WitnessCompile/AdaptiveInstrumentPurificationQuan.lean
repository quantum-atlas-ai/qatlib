/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationStat
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetPhaseWordAssemblyQuan
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.List.GetD
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationAux
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationConstr
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationProgram

/-!
# Adaptive purification in an enlarged source space

A finite encoding packs branch records, the original workspace, and a spare address into one
enlarged source workspace. `sourcePurifySpaceEquiv` preserves the clean spare-address embedding
and transports the lifted oracle to the ordinary alphabet oracle.

`adaptiveInstrumentPurification` uses this equivalence to obtain exact recorded-output
simulation by a legal source word. This supplies a computation-model bridge for the coherent and
noncoherent state conversion definitions in [LeeEtAl2011].

## Main statements

* `sourcePurifyCode_injective` and `sourcePurifyCode_surjective`: correctness of the workspace
  encoding.
* `sourcePurifyRelabel_oracle`: compatibility with the alphabet oracle.
* `adaptiveInstrumentPurification`: the purification specification.

## References

* [Lee et al., 2011][LeeEtAl2011]
* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.HspRecovery.RecordExtract

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The workspace code placing spare address `n` in the first `L*r` positions and all other
spare addresses after them. -/
def sourcePurifyCode {L r n : ℕ} (p : Fin L × Fin r × Fin (n+1)) : ℕ :=
  if p.2.2.val=n then p.1.val*r+p.2.1.val
  else L*r+(p.1.val*r+p.2.1.val)*n+p.2.2.val

/-- At spare address `n`, the purification code is the packed record-and-workspace index
`l.val*r+j.val`. -/
@[simp] theorem sourcePurifyCode_top {L r n : ℕ} (l : Fin L) (j : Fin r) :
    sourcePurifyCode (l,j,(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1)))=l.val*r+j.val := by
  simp only [sourcePurifyCode,if_true]

/-- A spare address other than `n` is encoded as `L*r+(l.val*r+j.val)*n+w.val`. -/
@[simp] theorem sourcePurifyCode_off {L r n : ℕ} (l : Fin L) (j : Fin r)
    (w : Fin (n+1)) (hw : w.val≠n) :
    sourcePurifyCode (l,j,w)=L*r+(l.val*r+j.val)*n+w.val := by
  simp only [sourcePurifyCode,if_neg hw]

/-- For positive workspace and record sizes, the purification code is below `L*r*(n+1)`. -/
theorem sourcePurifyCode_lt {L r n : ℕ} (_hr : 0<r) (_hL : 0<L)
    (p : Fin L × Fin r × Fin (n+1)) : sourcePurifyCode p<L*r*(n+1) := by
  have hp3 := p.2.2.isLt
  have hband : p.1.val*r+p.2.1.val<L*r := by
    have h1 : (p.1.val+1)*r≤L*r := Nat.mul_le_mul_right r (by have := p.1.isLt; omega)
    have h2 : (p.1.val+1)*r=p.1.val*r+r := by ring
    have := p.2.1.isLt
    omega
  have hE : L*r*(n+1)=L*r+L*r*n := by ring
  unfold sourcePurifyCode
  by_cases hw : p.2.2.val=n
  · rw [if_pos hw]; omega
  · rw [if_neg hw]
    have h3 : (p.1.val*r+p.2.1.val)*n+p.2.2.val<L*r*n := by
      have ha : ((p.1.val*r+p.2.1.val)+1)*n≤L*r*n := Nat.mul_le_mul_right n (by omega)
      have hb : ((p.1.val*r+p.2.1.val)+1)*n=(p.1.val*r+p.2.1.val)*n+n := by ring
      omega
    omega

/-- For positive workspace size, the purification workspace code is injective. -/
theorem sourcePurifyCode_injective {L r n : ℕ} (hr : 0<r) :
    Function.Injective (sourcePurifyCode (L := L) (r := r) (n := n)) := by
  intro a b hab
  unfold sourcePurifyCode at hab
  by_cases hwa : a.2.2.val=n <;> by_cases hwb : b.2.2.val=n
  · rw [if_pos hwa,if_pos hwb] at hab
    have h1 : a.2.1.val=b.2.1.val := by
      have ha' : (a.1.val*r+a.2.1.val)%r=a.2.1.val := by
        rw [Nat.add_comm (a.1.val*r) a.2.1.val,Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt a.2.1.isLt]
      have hb' : (b.1.val*r+b.2.1.val)%r=b.2.1.val := by
        rw [Nat.add_comm (b.1.val*r) b.2.1.val,Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt b.2.1.isLt]
      have h : (a.1.val*r+a.2.1.val)%r=(b.1.val*r+b.2.1.val)%r :=
        congrArg (fun z => z%r) hab
      rw [ha',hb'] at h
      exact h
    have h2 : a.1.val*r=b.1.val*r := by omega
    exact Prod.ext (Fin.ext (Nat.eq_of_mul_eq_mul_right hr h2))
      (Prod.ext (Fin.ext h1) (Fin.ext (by omega)))
  · rw [if_pos hwa,if_neg hwb] at hab
    exfalso
    have ha : a.1.val*r+a.2.1.val<L*r := by
      have h1 : (a.1.val+1)*r≤L*r := Nat.mul_le_mul_right r (by have := a.1.isLt; omega)
      have h2 : (a.1.val+1)*r=a.1.val*r+r := by ring
      have := a.2.1.isLt
      omega
    have hb : b.2.2.val<n := by have := b.2.2.isLt; omega
    omega
  · rw [if_neg hwa,if_pos hwb] at hab
    exfalso
    have hb : b.1.val*r+b.2.1.val<L*r := by
      have h1 : (b.1.val+1)*r≤L*r := Nat.mul_le_mul_right r (by have := b.1.isLt; omega)
      have h2 : (b.1.val+1)*r=b.1.val*r+r := by ring
      have := b.2.1.isLt
      omega
    have ha : a.2.2.val<n := by have := a.2.2.isLt; omega
    omega
  · rw [if_neg hwa,if_neg hwb] at hab
    have hna : a.2.2.val<n := by have := a.2.2.isLt; omega
    have hnb : b.2.2.val<n := by have := b.2.2.isLt; omega
    have hstrip : (a.1.val*r+a.2.1.val)*n+a.2.2.val=
        (b.1.val*r+b.2.1.val)*n+b.2.2.val := by omega
    have h1 : a.2.2.val=b.2.2.val := by
      have ha' : ((a.1.val*r+a.2.1.val)*n+a.2.2.val)%n=a.2.2.val := by
        rw [Nat.add_comm ((a.1.val*r+a.2.1.val)*n) a.2.2.val,
          Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hna]
      have hb' : ((b.1.val*r+b.2.1.val)*n+b.2.2.val)%n=b.2.2.val := by
        rw [Nat.add_comm ((b.1.val*r+b.2.1.val)*n) b.2.2.val,
          Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hnb]
      have h : ((a.1.val*r+a.2.1.val)*n+a.2.2.val)%n=
          ((b.1.val*r+b.2.1.val)*n+b.2.2.val)%n := congrArg (fun z => z%n) hstrip
      rw [ha',hb'] at h
      exact h
    have hn0 : 0<n := by omega
    have hC : (a.1.val*r+a.2.1.val)*n=(b.1.val*r+b.2.1.val)*n := by omega
    have hcc : a.1.val*r+a.2.1.val=b.1.val*r+b.2.1.val :=
      Nat.eq_of_mul_eq_mul_right hn0 hC
    have h2 : a.2.1.val=b.2.1.val := by
      have ha' : (a.1.val*r+a.2.1.val)%r=a.2.1.val := by
        rw [Nat.add_comm (a.1.val*r) a.2.1.val,Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt a.2.1.isLt]
      have hb' : (b.1.val*r+b.2.1.val)%r=b.2.1.val := by
        rw [Nat.add_comm (b.1.val*r) b.2.1.val,Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt b.2.1.isLt]
      have h : (a.1.val*r+a.2.1.val)%r=(b.1.val*r+b.2.1.val)%r :=
        congrArg (fun z => z%r) hcc
      rw [ha',hb'] at h
      exact h
    have h3 : a.1.val*r=b.1.val*r := by omega
    exact Prod.ext (Fin.ext (Nat.eq_of_mul_eq_mul_right hr h3))
      (Prod.ext (Fin.ext h2) (Fin.ext h1))

/-- For positive workspace size, every index below `L*r*(n+1)` is represented by a purification
code. -/
theorem sourcePurifyCode_surjective {L r n : ℕ} (hr : 0<r) (k : Fin (L*r*(n+1))) :
    ∃ p : Fin L × Fin r × Fin (n+1), sourcePurifyCode p=k.val := by
  by_cases hk : k.val<L*r
  · refine ⟨(⟨k.val/r,Nat.div_lt_of_lt_mul (by
        have h1 := Nat.mul_comm L r; omega)⟩,
      ⟨k.val%r,Nat.mod_lt _ hr⟩,⟨n,Nat.lt_succ_self n⟩),?_⟩
    rw [sourcePurifyCode_top]
    have hc : (k.val/r)*r+k.val%r=k.val := by
      rw [Nat.mul_comm (k.val/r) r]; exact Nat.div_add_mod k.val r
    exact hc
  · have hkge : L*r≤k.val := Nat.le_of_not_lt hk
    have hn : n≠0 := by intro h0; exact hk (by simpa [h0] using! k.isLt)
    have hn0 : 0<n := Nat.pos_of_ne_zero hn
    have hE : L*r*(n+1)=L*r+L*r*n := by ring
    have hVlt : k.val-L*r<L*r*n := by have := k.isLt; omega
    have hC : (k.val-L*r)/n<L*r := Nat.div_lt_of_lt_mul (by
      have h1 := Nat.mul_comm n (L*r); omega)
    have hC' : (k.val-L*r)/n/r<L := Nat.div_lt_of_lt_mul (by
      have h1 := Nat.mul_comm L r; omega)
    refine ⟨(⟨(k.val-L*r)/n/r,hC'⟩,
      ⟨(k.val-L*r)/n%r,Nat.mod_lt _ hr⟩,
      ⟨(k.val-L*r)%n,Nat.lt_succ_of_lt (Nat.mod_lt _ hn0)⟩),?_⟩
    have hw : (k.val-L*r)%n≠n := by have := Nat.mod_lt (k.val-L*r) hn0; omega
    have hc2 : ((k.val-L*r)/n/r)*r+(k.val-L*r)/n%r=(k.val-L*r)/n := by
      rw [Nat.mul_comm ((k.val-L*r)/n/r) r]; exact Nat.div_add_mod ((k.val-L*r)/n) r
    have hm2 : k.val-L*r=((k.val-L*r)/n)*n+(k.val-L*r)%n := by
      rw [Nat.mul_comm ((k.val-L*r)/n) n]; exact (Nat.div_add_mod (k.val-L*r) n).symm
    rw [sourcePurifyCode_off _ _ _ hw,hc2,Nat.add_assoc,← hm2]
    exact (Nat.add_comm _ _).trans (Nat.sub_add_cancel hkge)

/-- The source-space map preserving the source registers and packing the record, workspace, and
spare address into the enlarged workspace. -/
def sourcePurifyFullMap {H : Type} (n q r L : ℕ) (hr : 0<r) (hL : 0<L)
    (y : Fin L × SourceSpace n q H r × Fin (n+1)) : SourceSpace n q H (L*r*(n+1)) :=
  (y.2.1.1,(y.2.1.2.1,⟨sourcePurifyCode (y.1,y.2.1.2.2,y.2.2),
    sourcePurifyCode_lt hr hL (y.1,y.2.1.2.2,y.2.2)⟩))

/-- The full purification source-space map is bijective. -/
theorem sourcePurifyFullMap_bijective {H : Type} (n q r L : ℕ) (hr : 0<r) (hL : 0<L) :
    Function.Bijective (sourcePurifyFullMap (H := H) n q r L hr hL) := by
  constructor
  · intro a b hab
    have ha : a.2.1.1=b.2.1.1 := by
      have h := congrArg (fun w : SourceSpace n q H (L*r*(n+1)) => w.1) hab
      simpa only [sourcePurifyFullMap] using! h
    have hb : a.2.1.2.1=b.2.1.2.1 := by
      have h := congrArg (fun w : SourceSpace n q H (L*r*(n+1)) => w.2.1) hab
      simpa only [sourcePurifyFullMap] using! h
    have hcode : sourcePurifyCode (a.1,a.2.1.2.2,a.2.2)=
        sourcePurifyCode (b.1,b.2.1.2.2,b.2.2) := by
      have h := congrArg (fun w : SourceSpace n q H (L*r*(n+1)) => w.2.2.val) hab
      simpa only [sourcePurifyFullMap] using! h
    obtain ⟨hl,hrest⟩ := Prod.ext_iff.mp (sourcePurifyCode_injective hr hcode)
    obtain ⟨hj,hw⟩ := Prod.ext_iff.mp hrest
    exact Prod.ext hl (Prod.ext (Prod.ext ha (Prod.ext hb hj)) hw)
  · intro p
    obtain ⟨t,ht⟩ := sourcePurifyCode_surjective (L := L) (r := r) (n := n) hr p.2.2
    refine ⟨(t.1,(p.1,(p.2.1,t.2.1)),t.2.2),?_⟩
    show sourcePurifyFullMap (H := H) n q r L hr hL (t.1,(p.1,(p.2.1,t.2.1)),t.2.2)=p
    simp only [sourcePurifyFullMap]
    exact Prod.ext rfl (Prod.ext rfl (Fin.ext ht))

/-- The equivalence between the explicit purification register space and the source space with
workspace size `L*r*(n+1)`. -/
def sourcePurifySpaceEquiv {H : Type} (n q r L : ℕ) (hr : 0<r) (hL : 0<L) :
    (Fin L × SourceSpace n q H r × Fin (n+1)) ≃ SourceSpace n q H (L*r*(n+1)) :=
  Equiv.ofBijective (sourcePurifyFullMap (H := H) n q r L hr hL)
    (sourcePurifyFullMap_bijective (H := H) n q r L hr hL)

/-- On spare address `n`, the purification-space equivalence agrees with the tree-record
encoding. -/
theorem sourcePurifySpaceEquiv_code {H : Type} {n q r L : ℕ} (hr : 0<r) (hL : 0<L)
    (hRle : L*r≤L*r*(n+1)) (l : Fin L) (s : SourceSpace n q H r) :
    sourcePurifySpaceEquiv n q r L hr hL (l,s,⟨n,Nat.lt_succ_self n⟩)=
      sourceTreeCode n q r L (L*r*(n+1)) hRle (l,s) := by
  show sourcePurifyFullMap (H := H) n q r L hr hL (l,s,⟨n,Nat.lt_succ_self n⟩)=
      sourceTreeCode n q r L (L*r*(n+1)) hRle (l,s)
  simp only [sourcePurifyFullMap,sourceTreeCode]
  exact Prod.ext rfl (Prod.ext rfl (Fin.ext (by
    simp only [sourcePurifyCode,if_true])))

/-- Relabeling the lifted purification oracle by the workspace equivalence gives the alphabet
oracle on the enlarged source space. -/
theorem sourcePurifyRelabel_oracle {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q r L : ℕ} (hr : 0<r) (hL : 0<L)
    (input : X → Fin n → Fin (q+1)) (x : X) :
    relabelGate (sourcePurifySpaceEquiv (H := H) n q r L hr hL)
        (sourcePurifyOracle (n := n) (q := q) input x (r := r) (L := L)) =
      sourceAlphabetOracle (W := (Bool × H) × Fin (L*r*(n+1))) input x := by
  rw [sourceAlphabetOracle_eq_permMatrix (r := L*r*(n+1))]
  unfold sourcePurifyOracle
  apply sourceRelabelGate_permMatrix
  intro y
  rfl

/-- Legal adaptive computations satisfy the exact recorded-output purification specification
with at most twice their oracle-call count. This supports the coherent and noncoherent
models of [Lee et al., Definitions 2.1 and 2.2][LeeEtAl2011]. -/
theorem adaptiveInstrumentPurification : AdaptiveInstrumentPurification := by
  intro X H _ _ _ _ _ n q r hr input T hT
  have hL : 0<max 1 (sourceAdaptiveLeaves T) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  obtain ⟨P,hPleg,hPcalls,hPtrans⟩ :=
    sourceAdaptive_purify_program (X := X) (H := H) hr input T hT hL
  let e := sourcePurifySpaceEquiv (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) hr hL
  let R := (max 1 (sourceAdaptiveLeaves T))*r*(n+1)
  have hRpos : 0<R := Nat.mul_pos (Nat.mul_pos hL hr) (Nat.succ_pos n)
  have hRle : (max 1 (sourceAdaptiveLeaves T))*r≤R :=
    Nat.le_mul_of_pos_right (max 1 (sourceAdaptiveLeaves T)*r) (Nat.succ_pos n)
  have hIso : (sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R)ᴴ*
      sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R=1 :=
    sourceTreeFrame_isometry (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R hRle
  have hcode : ∀ (l : Fin (max 1 (sourceAdaptiveLeaves T))) (s : SourceSpace n q H r),
      e (l,s,⟨n,Nat.lt_succ_self n⟩)=
        sourceTreeCode n q r (max 1 (sourceAdaptiveLeaves T)) R hRle (l,s) := by
    intro l s
    exact sourcePurifySpaceEquiv_code (H := H) (n := n) (q := q) (r := r)
      (L := max 1 (sourceAdaptiveLeaves T)) hr hL hRle l s
  refine ⟨R,hRpos,sourceRelabelWord e (sourcePurificationProgramWord P),hRle,
    sourceRelabelWord_legal e _ (sourcePurificationProgramWord_legal P hPleg),?_,?_⟩
  · show sourceWordCalls (sourceRelabelWord e (sourcePurificationProgramWord P))≤_
    rw [sourceRelabelWord_calls]
    exact hPcalls
  · refine ⟨hIso,?_⟩
    intro x ψ
    have hOu : sourceAlphabetOracle (W := (Bool × H) × Fin r) input x ∈
        Matrix.unitaryGroup _ ℂ := by
      rw [sourceAlphabetOracle_eq_permMatrix]
      exact permMatrix_unitary_of_injective (Equiv.injective _)
    have hOconj : relabelGate e
        (sourcePurifyOracle (n := n) (q := q) input x (r := r)
          (L := max 1 (sourceAdaptiveLeaves T))) =
        sourceAlphabetOracle (W := (Bool × H) × Fin R) input x :=
      sourcePurifyRelabel_oracle (H := H) (n := n) (q := q) (r := r)
        (L := max 1 (sourceAdaptiveLeaves T)) hr hL input x
    have hM : sourceWordMatrix (sourceAlphabetOracle (W := (Bool × H) × Fin R) input x)
        (sourceRelabelWord e (sourcePurificationProgramWord P))=
        relabelGate e (sourceWordMatrix
          (sourcePurifyOracle (n := n) (q := q) input x (r := r)
            (L := max 1 (sourceAdaptiveLeaves T))) (sourcePurificationProgramWord P)) := by
      rw [← hOconj]
      exact sourceRelabelWord_matrix e _ _
    have hts : TensorState (Ket (⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves T)))) ψ=
        (sourceBasisFrame (fun s : SourceSpace n q H r =>
          ((⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves T))),s)))*ᵥ ψ := by
      funext p
      rcases p with ⟨l,s⟩
      simp only [TensorState,Ket,sourceBasisFrame,Matrix.mulVec,dotProduct]
      rw [Finset.sum_eq_single s]
      · by_cases hl : l=(⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves T)))
        · subst hl; simp
        · rw [if_neg hl,if_neg (fun h => hl (Prod.ext_iff.mp h).1)]
      · intro t _ ht
        rw [if_neg (fun h => ht (Prod.ext_iff.mp h).2.symm),zero_mul]
      · intro hs; exact absurd (Finset.mem_univ s) hs
    have hin : (sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R)*ᵥ
        TensorState (Ket (⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves T)))) ψ=
        sourceBasisFrame (⇑e)*ᵥ
          (sourcePurifyIn (n := n) (q := q) (r := r)
            (L := max 1 (sourceAdaptiveLeaves T)) hL*ᵥ ψ) := by
      rw [sourceTreeFrame_eq_basis (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R hRle, hts]
      unfold sourcePurifyIn
      rw [Matrix.mulVec_mulVec,sourceBasisFrame_mul]
      have hfun : (sourceTreeCode n q r (max 1 (sourceAdaptiveLeaves T)) R hRle)∘
          (fun s : SourceSpace n q H r =>
            ((⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves T))),s))=
          (⇑e)∘(fun s : SourceSpace n q H r =>
            ((⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves T))),s,⟨n,Nat.lt_succ_self n⟩)) := by
        funext s
        exact (hcode ⟨0,hL⟩ s).symm
      rw [hfun]
      rw [Matrix.mulVec_mulVec,sourceBasisFrame_mul]
    have hout : sourceBasisFrame (⇑e)*ᵥ
        ((sourcePurifyOut (n := n) (q := q) (r := r)
          (L := max 1 (sourceAdaptiveLeaves T)))*ᵥ
        sourceAdaptivePure (sourceAlphabetOracle input x) T ψ)=
        (sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R)*ᵥ
        sourceAdaptivePure (sourceAlphabetOracle input x) T ψ := by
      rw [sourceTreeFrame_eq_basis (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R hRle]
      unfold sourcePurifyOut
      rw [Matrix.mulVec_mulVec,sourceBasisFrame_mul]
      have hfun : (⇑e)∘(fun p : Fin (max 1 (sourceAdaptiveLeaves T)) × SourceSpace n q H r =>
          (p.1,p.2,⟨n,Nat.lt_succ_self n⟩))=
        sourceTreeCode n q r (max 1 (sourceAdaptiveLeaves T)) R hRle := by
        funext p
        exact hcode p.1 p.2
      rw [hfun]
    refine ⟨?_,?_,?_⟩
    · rw [hM,hin]
      rw [Matrix.mulVec_mulVec,sourceRelabelGate_mul_basisFrame e _,← Matrix.mulVec_mulVec]
      rw [hPtrans x ψ]
      exact hout
    · intro hnorm
      rw [sourceAdaptive_branches_mass _ hOu T hT ψ,norm_toEuclidean_fromVec_sq]
      exact hnorm
    · exact fun p t => sourceAdaptive_density_pure _ T ψ p t

end Qatlib.Concepts.ConversionCore.WitnessCompile
