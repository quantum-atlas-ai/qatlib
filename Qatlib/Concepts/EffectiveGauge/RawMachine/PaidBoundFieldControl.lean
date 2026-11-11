/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundThresholdBudget

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Bound Field Control

Raw Machine constructions for Effective Gauge.
Defines `Slot`, `Label`, `Local`.
Proves `frame_target`, `lift`, `start_call`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidBoundCompression.Fields

/-- Four original fields are retained as binary words for subsequent
orientation and repeated threshold calls. Parsing itself uses NatReadEmit. -/
inductive Slot where
  | raw | reader | markers | payload | temporary | encoded | field (i : Fin 4)
  deriving DecidableEq,Fintype
/-- Constructors for Label in the Raw Machine construction. -/
inductive Label where
  | start (l : Fin 1)
  | read (i : Fin 4) (l : NatReadEmit.Label)
  | discard (l : Fin 1)
  | done
  deriving DecidableEq,Fintype
/-- Initialize the machine label at its first instruction. -/
instance : Inhabited Label := ⟨.start 0⟩
/-- Abbreviation for Local in the Raw Machine construction. -/
abbrev Local := NatReadEmit.Local
/-- Abbreviation for Config in the Raw Machine construction. -/
abbrev Config := TM2.Cfg (fun _ : Slot => Bool) Label Local
/-- Definition of get IO in the Raw Machine construction. -/
def getIO (v : Local) := v.2
/-- Definition of put IO in the Raw Machine construction. -/
def putIO (v : Local) (w : Option Bool) : Local := (v.1,w)
/-- Definition of start Code in the Raw Machine construction. -/
def startCode : Fin 2 → Slot | 0 => .raw | _ => .reader
/-- Definition of read Code in the Raw Machine construction. -/
def readCode (i : Fin 4) : NatReadEmit.Slot → Slot
  | .reader => .reader
  | .markers => .markers
  | .payload => .payload
  | .value => .field i
  | .temporary => .temporary
  | .output => .encoded
/-- Definition of after Read in the Raw Machine construction. -/
def afterRead (i : Fin 4) : Label :=
  if h : i.val+1<4 then .read ⟨i.val+1,h⟩ default else .discard 0
/-- Definition of program in the Raw Machine construction. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .start l => StackCall.stmt startCode Label.start (.read 0 default) getIO putIO (Stacks.transferProgram l)
  | .read i l => StackCall.stmt (readCode i) (Label.read i) (afterRead i) id (fun _ w => w) (NatReadEmit.program l)
  | .discard l => StackCall.stmt (fun _ : Fin 1 => Slot.encoded) Label.discard .done getIO putIO (Normalization.drainProgram l)
  | .done => .load (fun _ => default) .halt
/-- Definition of state in the Raw Machine construction. -/
def state (fields : Fin 4 → CanonicalCodec.Bits) (raw reader encoded : CanonicalCodec.Bits) : Slot → CanonicalCodec.Bits
  | .field i => fields i
  | .raw => raw
  | .reader => reader
  | .encoded => encoded
  | _ => []
/-- Abbreviation for operands in the Raw Machine construction. -/
abbrev operands := PaidFractionInverse.operands
/-- Definition of read Last in the Raw Machine construction. -/
def readLast (n : ℕ) : Local := ((true,CheckedNat.lastField n.bits none),none)

/-- Original `frame_target` guarantee for the `PaidBoundFieldControl` construction; the complete source hypotheses are retained. -/
private theorem frame_target {K : Type} [DecidableEq K] (code : K → Slot) (hinj : Function.Injective code)
    (S T : Slot → CanonicalCodec.Bits) (data : K → CanonicalCodec.Bits)
    (hi : ∀ k,T (code k)=data k) (ho : ∀ j,(∀ k,code k≠j) → T j=S j) : StackCall.frame code S data=T := by
  classical
  funext j
  by_cases hj : ∃ k,code k=j
  · obtain ⟨k,rfl⟩ := hj
    rw [StackCall.frame_at code S data hinj,hi]
  · rw [WordValidator.frame_outside code S data j (by simpa using hj)]
    exact (ho j (by simpa using hj)).symm

/-- Original `lift` guarantee for the `PaidBoundFieldControl` construction; the complete source hypotheses are retained. -/
private theorem lift {K Λ σ : Type} [DecidableEq K]
    (code : K → Slot) (hinj : Function.Injective code) (labels : Λ → Label) (ret : Label)
    (get : Local → σ) (put : Local → σ → Local)
    (hg : ∀ v x,get (put v x)=x) (hp : ∀ v x y,put (put v x) y=put v y) (hs : ∀ v,put v (get v)=v)
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (hcode : ∀ l,program (labels l)=StackCall.stmt code labels ret get put (M l))
    (v : Local) (S T : Slot → CanonicalCodec.Bits) (s t : K → CanonicalCodec.Bits) (l : Λ) (last : σ) (budget : ℕ)
    (e : Stacks.Execution M ⟨some l,get v,s⟩ ⟨none,last,t⟩ budget)
    (hS : ∀ k,S (code k)=s k) (hT : ∀ k,T (code k)=t k)
    (hout : ∀ j,(∀ k,code k≠j) → T j=S j) :
    Stacks.Execution program ⟨some (labels l),v,S⟩ ⟨some ret,put v last,T⟩ budget := by
  obtain ⟨ticks,hr,hc⟩ := e
  obtain ⟨hn,hnc⟩ := StackCall.execution code labels ret get put (StackCall.frame code S)
    (fun data k => StackCall.frame_at code S data hinj k)
    (fun data k bits => StackCall.frame_update code S data hinj k bits)
    hg hp M program hcode v ticks _ _ hr
  have hi := StackCall.frame_same code S s hinj hS
  have hf := frame_target code hinj S T t hT hout
  refine ⟨ticks,?_,?_⟩
  · simpa only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,hs,hi,hf] using hn
  · simpa only [StackCall.cfg,Option.map_some,Option.getD_some,hs,hi] using hnc.trans_le hc

/-- Original `start_call` guarantee for the `PaidBoundFieldControl` construction; the complete source hypotheses are retained. -/
theorem start_call (bits : CanonicalCodec.Bits) (v : Local) :
    Stacks.Execution program ⟨some (.start 0),v,state (fun _ => []) bits.reverse [] []⟩
      ⟨some (.read 0 default),putIO v none,state (fun _ => []) [] bits []⟩
      (20*(1+bits.length)^2) := by
  have hinj : Function.Injective startCode := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all [startCode]
  have hr := Stacks.transfer_run bits.reverse [] (getIO v)
  have hc := Stacks.transfer_clock bits.reverse [] (getIO v)
  simp only [List.length_reverse,List.length_nil,Nat.add_zero,List.reverse_reverse,List.append_nil] at hr hc
  refine lift startCode hinj Label.start (.read 0 default) getIO putIO
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) Stacks.transferProgram (fun _ => rfl) v
    _ _ _ _ _ _ _ ⟨bits.length+1,hr,hc.le.trans (by nlinarith)⟩ ?_ ?_ ?_
  · intro k; fin_cases k <;> rfl
  · intro k; fin_cases k <;> rfl
  · intro k hk
    cases k <;> first | rfl | exact (hk 0 rfl).elim | exact (hk 1 rfl).elim

/-- Original `read_call` guarantee for the `PaidBoundFieldControl` construction; the complete source hypotheses are retained. -/
theorem read_call (i : Fin 4) (n : ℕ) (tail encoded : CanonicalCodec.Bits)
    (fields : Fin 4 → CanonicalCodec.Bits) (v : Local) (he : fields i=[]) :
    Stacks.Execution program ⟨some (.read i default),v,state fields [] (CanonicalCodec.natBits n++tail) encoded⟩
      ⟨some (afterRead i),readLast n,
        state (Function.update fields i n.bits) [] tail ((CanonicalCodec.natBits n).reverse++encoded)⟩
      (500*(1+(CanonicalCodec.natBits n++tail).length+encoded.length)^2) := by
  have hinj : Function.Injective (readCode i) := by intro a b h; cases a <;> cases b <;> simp_all [readCode]
  obtain ⟨ticks,hr,hc⟩ := NatReadEmit.complete n tail encoded v
  refine lift (readCode i) hinj (Label.read i) (afterRead i) id (fun _ w => w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) NatReadEmit.program (fun _ => rfl) v
    _ _ _ _ _ _ _ ⟨ticks,hr,hc⟩ ?_ ?_ ?_
  · intro k; cases k <;> simp [readCode,state,NatReadEmit.store,he]
  · intro k; cases k <;> simp [readCode,state,NatReadEmit.store]
  · intro k hk
    cases k with
    | field j =>
      have h : i≠j := fun h => hk .value (congrArg Slot.field h)
      simp [state,Ne.symm h]
    | _ => first | rfl | exact (hk .reader rfl).elim | exact (hk .output rfl).elim

/-- Original `discard_call` guarantee for the `PaidBoundFieldControl` construction; the complete source hypotheses are retained. -/
theorem discard_call (fields : Fin 4 → CanonicalCodec.Bits) (encoded : CanonicalCodec.Bits) (v : Local) :
    Stacks.Execution program ⟨some (.discard 0),v,state fields [] [] encoded⟩
      ⟨some .done,putIO v none,state fields [] [] []⟩
      (encoded.length^2+3*encoded.length+3) := by
  have hr := Normalization.drain_run encoded (getIO v)
  have hc := Normalization.drain_clock encoded (getIO v)
  refine lift (fun _ : Fin 1 => Slot.encoded) (fun _ _ _ => Subsingleton.elim _ _) Label.discard .done
    getIO putIO (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) Normalization.drainProgram (fun _ => rfl)
    v _ _ _ _ _ _ _ ⟨encoded.length+1,hr,hc.le⟩ ?_ ?_ ?_
  · intro k; fin_cases k; rfl
  · intro k; fin_cases k; rfl
  · intro k hk
    cases k <;> first | rfl | exact (hk 0 rfl).elim

/-- Original `done_step` guarantee for the `PaidBoundFieldControl` construction; the complete source hypotheses are retained. -/
theorem done_step (fields : Fin 4 → CanonicalCodec.Bits) (v : Local) :
    Stacks.Execution program ⟨some .done,v,state fields [] [] []⟩
      ⟨none,default,state fields [] [] []⟩ 1 := by
  refine ⟨1,rfl,le_rfl⟩

end PaidBoundCompression.Fields
end Qatlib.Concepts.EffectiveGauge.RawMachine
