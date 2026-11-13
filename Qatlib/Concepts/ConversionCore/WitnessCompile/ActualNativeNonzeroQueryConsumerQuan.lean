/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.ActualNativeNonzeroQueryConsumerStat
import Qatlib.Concepts.GramQueryCore.ModelSemantics.NativeCodeSemanticsQuan
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Size
import Qatlib.Concepts.GateVocabulary.LocalReflectionGates

/-!
# A native program with a nonzero query count

An explicit four-wire program solves the two-label state conversion problem using one oracle
call and four known gates. `nativeTwoLabel_exact` verifies the conversion on clean states, using
the elementary gate identities described in [NielsenChuang2010].

A constant-output Turing machine provides a uniform compiler for this program, yielding
`actualNativeNonzeroQueryConsumer` with explicit resource bounds.

## Main statements

* `nativeTwoLabelProgram`: the concrete native program.
* `nativeConstantTM_output`: the output and running time of the constant-output machine.
* `actualNativeNonzeroQueryConsumer`: a native compiler satisfying the nonzero-query
  specification.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped Classical BigOperators

/-- The four-wire native program for the two-label problem, consisting of one query, a swap, and
a three-gate flag flip. -/
def nativeTwoLabelProgram : SourceNativeProgram :=
  ⟨4,[.query [0,1] false,.local (.swap 1 3),.local (.h 2),
    .local (.cp 2 2 1 false),.local (.h 2)]⟩

/-- The two-label native program is legal for `sourceTwoLabelProblem`. -/
theorem nativeTwoLabelProgram_legal : sourceNativeLegal sourceTwoLabelProblem nativeTwoLabelProgram := by
  intro s hs
  change s ∈ ([.query [0,1] false,.local (.swap 1 3),.local (.h 2),
    .local (.cp 2 2 1 false),.local (.h 2)] : List (SourceNativeStep 4)) at hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact ⟨by decide,by decide⟩
  rcases List.mem_cons.mp hs with rfl | hs
  · trivial
  rcases List.mem_cons.mp hs with rfl | hs
  · trivial
  rcases List.mem_cons.mp hs with rfl | hs
  · change 1 ≤ 3
    omega
  rcases List.mem_cons.mp hs with rfl | hs
  · trivial
  exact False.elim (List.not_mem_nil hs)

/-- The two-label native program makes exactly one oracle call. -/
theorem nativeTwoLabelProgram_calls : sourceNativeCalls nativeTwoLabelProgram = 1 := rfl

/-- The two-label native program uses exactly four known gates. -/
theorem nativeTwoLabelProgram_gates : sourceNativeGates nativeTwoLabelProgram = 4 := rfl

/-- A lifted permutation matrix maps a basis state by applying the permutation to the selected
wires and preserving the remaining wires. -/
theorem nativeWireLift_perm_ket {w : ℕ} (ws : List (Fin w)) (hws : ws.Nodup)
    (f : Reg ws.length → Reg ws.length) (z : Reg w) :
    nativeWireLift ws hws (permMatrix f) *ᵥ Qatlib.Foundations.PureStateMath.Ket z =
      Qatlib.Foundations.PureStateMath.Ket ((nativeWireSplit ws hws).symm (f (nativeWireSplit ws hws z).1,(nativeWireSplit ws hws z).2)) := by
  let e := nativeWireSplit ws hws
  ext t
  rw [mulVec_ket_apply,nativeWireLift_apply]
  have hother : (∀ i : Fin w, i ∉ ws → t i=z i) ↔ (e t).2=(e z).2 := by
    constructor
    · intro h
      funext i
      exact h i.val i.property
    · intro h i hi
      exact congrFun h ⟨i,hi⟩
  have hpoint : t=e.symm (f (e z).1,(e z).2) ↔ (e t).1=f (e z).1 ∧ (e t).2=(e z).2 := by
    constructor
    · intro h
      rw [h,e.apply_symm_apply]
      exact ⟨rfl,rfl⟩
    · intro h
      apply e.injective
      rw [e.apply_symm_apply]
      exact Prod.ext h.1 h.2
  change (if ∀ i : Fin w, i ∉ ws → t i=z i then
      (if (e t).1=f (e z).1 then (1 : ℂ) else 0) else 0) =
    (if t=e.symm (f (e z).1,(e z).2) then 1 else 0)
  by_cases ha : (e t).1=f (e z).1
  · by_cases hb : (e t).2=(e z).2
    · rw [if_pos (hother.mpr hb),if_pos ha,if_pos (hpoint.mpr ⟨ha,hb⟩)]
    · rw [if_neg (fun h => hb (hother.mp h)),if_neg (fun h => hb (hpoint.mp h).2)]
  · have hp : ¬t=e.symm (f (e z).1,(e z).2) := fun h => ha (hpoint.mp h).1
    rw [if_neg hp]
    by_cases hb : ∀ i : Fin w, i ∉ ws → t i=z i
    · rw [if_pos hb,if_neg ha]
    · rw [if_neg hb]

/-- The native clean embedding of a basis state is the basis state at its encoded frame index. -/
theorem nativeFrame_ket (d : SourceRationalProblem) (w : ℕ) (tag : Bool) (h : Fin d.dimension) :
    sourceNativeClean d w tag (Qatlib.Foundations.PureStateMath.Ket h) = Qatlib.Foundations.PureStateMath.Ket (sourceRegBits w (nativeFrameIndex d (tag,h))) := by
  have hs : (fun p : Bool × Fin d.dimension => if p.1=tag then Qatlib.Foundations.PureStateMath.Ket h p.2 else 0) = Qatlib.Foundations.PureStateMath.Ket (tag,h) := by
    ext p
    by_cases hb : p.1=tag <;> by_cases hh : p.2=h <;> simp [Qatlib.Foundations.PureStateMath.Ket,Prod.ext_iff,hb,hh]
  unfold sourceNativeClean
  rw [hs]
  ext z
  simp only [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket]
  rw [Finset.sum_eq_single (tag,h)]
  · simp [sourceNativeFrame,nativeFrameIndex]
  · intro t _ ht
    simp [ht]
  · simp

/-- The initial state of the two-label problem is the zero basis state for either input label. -/
theorem nativeTwoLabel_start (x : Fin 2) :
    sourceRationalState (sourceTwoLabelProblem.start x) = Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) := by
  change (fun h : Fin 2 => (((if h=0 then 1 else 0 : ℚ) : ℂ)+((0 : ℚ) : ℂ)*Complex.I)) = Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)
  funext h
  by_cases hh : h=0 <;> simp [Qatlib.Foundations.PureStateMath.Ket,hh]

/-- The target state of the two-label problem is the basis state indexed by the input label. -/
theorem nativeTwoLabel_target (x : Fin 2) :
    sourceRationalState (sourceTwoLabelProblem.target x) = Qatlib.Foundations.PureStateMath.Ket x := by
  change (fun h : Fin 2 => (((if h=x then 1 else 0 : ℚ) : ℂ)+((0 : ℚ) : ℂ)*Complex.I)) = Qatlib.Foundations.PureStateMath.Ket x
  funext h
  by_cases hh : h=x <;> simp [Qatlib.Foundations.PureStateMath.Ket,hh]

/-- The native two-label query maps the zero register to the register encoding `2*x.val`. -/
theorem nativeTwoLabel_query (x : Fin 2) :
    sourceNativeStepMatrix sourceTwoLabelProblem x 4 (.query [0,1] false) *ᵥ
      Qatlib.Foundations.PureStateMath.Ket (sourceRegBits 4 0) = Qatlib.Foundations.PureStateMath.Ket (sourceRegBits 4 (2*x.val)) := by
  let ws : List (Fin 4) := [0,1]
  have hws : ws.Nodup := by decide
  have hlen :
      ws.length=sourceAddressBits sourceTwoLabelProblem+sourceValueBits sourceTwoLabelProblem := by
        decide
  have hmatrix : sourceNativeStepMatrix sourceTwoLabelProblem x 4 (.query ws false) =
      nativeWireLift ws hws (permMatrix (nativeValueAction sourceTwoLabelProblem x)) := by
    ext p t
    rw [nativeWireLift_apply]
    simp only [sourceNativeStepMatrix,dif_pos hlen,Bool.false_eq_true,↓reduceIte,sourceNativeValueOracle_eq]
    rfl
  rw [hmatrix,nativeWireLift_perm_ket]
  congr 1
  apply (nativeWireSplit ws hws).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · have hsel (v : ℕ) : (nativeWireSplit ws hws (sourceRegBits 4 v)).1 = sourceRegBits 2 v := by
      funext i
      fin_cases i <;> rfl
    have haction : nativeValueAction sourceTwoLabelProblem x (sourceRegBits 2 0) = sourceRegBits 2 (2*x.val) := by
      have ha : sourceAddressBits sourceTwoLabelProblem=1 := by decide
      unfold nativeValueAction
      simp only [ha]
      simp [nativeSymbol,nativeAddressPart,nativeAnswerPart,sourceRegBits,
        sourceRegNumber,sourceTwoLabelProblem,Nat.mod_eq_of_lt x.isLt]
      rfl
    rw [hsel 0,haction,hsel (2*x.val)]
  · funext i
    have hi : i.val.val=2 ∨ i.val.val=3 := by
      have ht := i.val.isLt
      have hn := i.property
      have h0 : i.val.val ≠ 0 := by
        intro h
        have he : i.val=(0 : Fin 4) := Fin.ext h
        apply hn
        rw [he]
        exact List.mem_cons_self
      have h1 : i.val.val ≠ 1 := by
        intro h
        have he : i.val=(1 : Fin 4) := Fin.ext h
        apply hn
        rw [he]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      omega
    rcases hi with hi | hi
    all_goals fin_cases x
    all_goals change Nat.testBit 0 i.val.val = Nat.testBit _ i.val.val
    all_goals rw [hi]
    all_goals decide

open Turing

/-- The emission transition for a fixed output word, alternating writes of its bits in reverse
order with moves to the left. -/
def nativeConstEmit (out : List Bool) (st : Fin (2*out.length+1)) :
    Option (Fin (2*out.length+1) × TM0.Stmt (Option Bool)) :=
  if hs : st.val < 2*out.length-1 then
    some (⟨st.val+1,by omega⟩,
      if st.val%2=0 then .write (some (out.getD (out.length-1-st.val/2) false)) else .move .left)
  else none

/-- A Turing machine that scans its input to the first blank and then emits the fixed Boolean
word `out`. -/
def nativeConstantTM (out : List Bool) : TM0.Machine (Option Bool) (Fin (2*out.length+1)) :=
  fun st c => if st.val=0 then
    match c with | some _ => some (0,.move .right) | none => nativeConstEmit out st
  else nativeConstEmit out st

/-- The result of iterating a Turing machine transition `n` times from configuration `c`, with
`none` propagated after halting. -/
def nativeTMRun {Λ : Type} [Inhabited Λ] (M : TM0.Machine (Option Bool) Λ)
    (n : ℕ) (c : TM0.Cfg (Option Bool) Λ) : Option (TM0.Cfg (Option Bool) Λ) :=
  (flip bind (TM0.step M))^[n] (some c)

/-- After a successful first transition, an `n+1` step run equals the `n` step run from the
successor configuration. -/
theorem nativeTMRun_succ_some {Λ : Type} [Inhabited Λ] (M : TM0.Machine (Option Bool) Λ)
    (n : ℕ) (c c' : TM0.Cfg (Option Bool) Λ) (hs : TM0.step M c = some c') :
    nativeTMRun M (n+1) c = nativeTMRun M n c' := by
  unfold nativeTMRun
  rw [Function.iterate_succ_apply]
  change (flip bind (TM0.step M))^[n] (TM0.step M c) = _
  rw [hs]

/-- Running from the initial tape agrees with `BitMachineAfter`. -/
theorem nativeTMRun_initial {Λ : Type} [Inhabited Λ] (M : TM0.Machine (Option Bool) Λ)
    (input : List (Option Bool)) (n : ℕ) :
    nativeTMRun M n (TM0.init input) = BitMachineAfter M input n := by
  exact (bitMachineAfter_eq_iterate M input n).symm

/-- A successful run of `n` steps can be followed by `m` further steps to obtain the run of
`n+m` steps. -/
theorem nativeTMRun_add_some {Λ : Type} [Inhabited Λ] (M : TM0.Machine (Option Bool) Λ)
    (n m : ℕ) (c c' : TM0.Cfg (Option Bool) Λ) (hs : nativeTMRun M n c = some c') :
    nativeTMRun M (n+m) c = nativeTMRun M m c' := by
  unfold nativeTMRun at hs ⊢
  rw [Nat.add_comm n m,Function.iterate_add_apply,hs]

/-- The constant-output machine scans a nonblank input symbol by moving right without changing
its control state. -/
theorem nativeConst_step_scan (out : List Bool) (b : Bool) (left : List (Option Bool)) (rest : List Bool) :
    TM0.step (nativeConstantTM out) ⟨0,Tape.mk₂ left (some b::rest.map some)⟩ =
      some ⟨0,Tape.mk₂ (some b::left) (rest.map some)⟩ := by
  simp [TM0.step,nativeConstantTM,Tape.mk₂,Tape.mk',Tape.move,ListBlank.head_mk,
    ListBlank.tail_mk,ListBlank.cons_mk]

/-- Scanning a Boolean input word takes its length in steps and leaves the reversed word on the
left of the tape head. -/
theorem nativeConst_scan (out bits : List Bool) (left : List (Option Bool)) :
    nativeTMRun (nativeConstantTM out) bits.length ⟨0,Tape.mk₂ left (bits.map some)⟩ =
      some ⟨0,Tape.mk₂ (bits.reverse.map some ++ left) []⟩ := by
  induction bits generalizing left with
  | nil => rfl
  | cons b bits ih =>
    rw [List.length_cons]
    rw [nativeTMRun_succ_some _ _ _ _ (by simpa only [List.map_cons] using! nativeConst_step_scan out b left bits)]
    simpa [List.reverse_cons,List.map_append,List.append_assoc] using! ih (some b::left)

/-- At an emission write state with `r` bits remaining, the constant-output machine writes bit
`r-1` of `out`. -/
theorem nativeConst_write (out : List Bool) (r : ℕ) (hr : 0<r) (hrL : r ≤ out.length)
    (head : Option Bool) (hhead : out.length=r → head=none) :
    nativeConstantTM out ⟨2*(out.length-r),by omega⟩ head =
      some (⟨2*(out.length-r)+1,by omega⟩,.write (some (out.getD (r-1) false))) := by
  have hb : 2*(out.length-r) < 2*out.length-1 := by omega
  have he : (2*(out.length-r))%2=0 := by omega
  have hi : out.length-1-(2*(out.length-r))/2 = r-1 := by omega
  by_cases hzero : out.length=r
  · have hh := hhead hzero
    simp only [nativeConstantTM,if_pos (by omega : 2*(out.length-r)=0),hh]
    simp only [nativeConstEmit,dif_pos hb,he,↓reduceIte,hi]
  · simp only [nativeConstantTM,if_neg (by omega : ¬2*(out.length-r)=0)]
    simp only [nativeConstEmit,dif_pos hb,he,↓reduceIte,hi]

/-- At an emission move state with more than one bit remaining, the constant-output machine
moves left and advances its control state. -/
theorem nativeConst_moveLeft (out : List Bool) (r : ℕ) (hr : 1<r) (hrL : r ≤ out.length)
    (head : Option Bool) :
    nativeConstantTM out ⟨2*(out.length-r)+1,by omega⟩ head =
      some (⟨2*(out.length-r)+2,by omega⟩,.move .left) := by
  have hb : 2*(out.length-r)+1 < 2*out.length-1 := by omega
  have he : (2*(out.length-r)+1)%2≠0 := by omega
  simp only [nativeConstantTM,if_neg (by omega : ¬2*(out.length-r)+1=0)]
  simp only [nativeConstEmit,dif_pos hb,he,↓reduceIte]

/-- For nonempty output, the final emission control state has no successor transition. -/
theorem nativeConst_halt (out : List Bool) (hL : 0<out.length) (head : Option Bool) :
    nativeConstantTM out ⟨2*out.length-1,by omega⟩ head = none := by
  simp [nativeConstantTM,nativeConstEmit,show 2*out.length-1≠0 by omega]

/-- Prepending the bit at position `r` to the suffix starting at `r+1` recovers the suffix
starting at `r`. -/
theorem nativeGetD_drop (out : List Bool) (r : ℕ) (hr : r<out.length) :
    out.getD r false :: out.drop (r+1) = out.drop r := by
  induction out generalizing r with
  | nil => simp at hr
  | cons b out ih =>
    cases r with
    | zero => rfl
    | succ r =>
      have hr' : r<out.length := by simpa using! hr
      simpa using! ih r hr'

/-- From the stated emission configuration with `r` bits remaining, `2*r-1` steps produce the
full output suffix at the final control state. -/
theorem nativeConst_emit_run (out : List Bool) (r : ℕ) (hr : 0<r) (hrL : r ≤ out.length)
    (head : Option Bool) (left : ListBlank (Option Bool)) (hhead : out.length=r → head=none) :
    ∃ cfg : TM0.Cfg (Option Bool) (Fin (2*out.length+1)),
      nativeTMRun (nativeConstantTM out) (2*r-1)
        ⟨⟨2*(out.length-r),by omega⟩,⟨head,left,ListBlank.mk ((out.drop r).map some)⟩⟩ = some cfg ∧
      cfg.q = ⟨2*out.length-1,by omega⟩ ∧ cfg.Tape.right₀ = ListBlank.mk (out.map some) := by
  induction r generalizing head left with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r=0
    · subst r
      let cfg : TM0.Cfg (Option Bool) (Fin (2*out.length+1)) :=
        ⟨⟨2*out.length-1,by omega⟩,⟨some (out.getD 0 false),left,ListBlank.mk ((out.drop 1).map some)⟩⟩
      have hw := nativeConst_write out 1 hr hrL head hhead
      have hnum : 2*(out.length-1)+1=2*out.length-1 := by omega
      have hstep : TM0.step (nativeConstantTM out)
          ⟨⟨2*(out.length-1),by omega⟩,⟨head,left,ListBlank.mk ((out.drop 1).map some)⟩⟩ = some cfg := by
        simp only [TM0.step,hw,Option.map_some,Tape.write,hnum,cfg]
      refine ⟨cfg,?_,rfl,?_⟩
      · rw [nativeTMRun_succ_some _ 0 _ _ hstep]
        rfl
      · change (ListBlank.mk ((out.drop 1).map some)).cons (some (out.getD 0 false)) = _
        rw [ListBlank.cons_mk]
        congr 1
        rw [← List.map_cons,nativeGetD_drop out 0 (by omega),List.drop_zero]
    · have hrp : 0<r := by omega
      have hi : r<out.length := by omega
      let st : Fin (2*out.length+1) := ⟨2*(out.length-(r+1)),by omega⟩
      let c : TM0.Cfg (Option Bool) (Fin (2*out.length+1)) :=
        ⟨st,⟨head,left,ListBlank.mk ((out.drop (r+1)).map some)⟩⟩
      let c1 : TM0.Cfg (Option Bool) (Fin (2*out.length+1)) :=
        ⟨⟨st.val+1,by dsimp [st]; omega⟩,
          ⟨some (out.getD r false),left,ListBlank.mk ((out.drop (r+1)).map some)⟩⟩
      let c2 : TM0.Cfg (Option Bool) (Fin (2*out.length+1)) :=
        ⟨⟨2*(out.length-r),by omega⟩,
          ⟨left.head,left.tail,ListBlank.mk ((out.drop r).map some)⟩⟩
      have hw := nativeConst_write out (r+1) hr hrL head hhead
      have hm := nativeConst_moveLeft out (r+1) (by omega) hrL (some (out.getD r false))
      have hs1 : TM0.step (nativeConstantTM out) c = some c1 := by
        simp only [TM0.step,c,st,hw,Option.map_some,Tape.write,Nat.add_sub_cancel,c1]
      have hs2 : TM0.step (nativeConstantTM out) c1 = some c2 := by
        have hn : 2*(out.length-(r+1))+2 = 2*(out.length-r) := by omega
        simp only [TM0.step,c1,st,hm,Option.map_some,Tape.move,hn,c2]
        congr 2
        rw [ListBlank.cons_mk,← List.map_cons,nativeGetD_drop out r hi]
      obtain ⟨cfg,hcfg,hq,hout⟩ := ih hrp (by omega) left.head left.tail (by intro h; omega)
      refine ⟨cfg,?_,hq,hout⟩
      have hn : 2*(r+1)-1 = (2*r-1)+1+1 := by omega
      rw [hn,nativeTMRun_succ_some _ _ _ _ hs1,nativeTMRun_succ_some _ _ _ _ hs2]
      exact hcfg

/-- For nonempty `out`, the constant-output machine reaches a halting configuration with right
tape `out` after `input.length+2*out.length-1` steps. -/
theorem nativeConstantTM_output (out : List Bool) (hL : 0<out.length) (input : List Bool) :
    ∃ cfg : TM0.Cfg (Option Bool) (Fin (2*out.length+1)),
      BitMachineAfter (nativeConstantTM out) (input.map some) (input.length+2*out.length-1) = some cfg ∧
      TM0.step (nativeConstantTM out) cfg = none ∧ cfg.Tape.right₀ = ListBlank.mk (out.map some) := by
  let mid : TM0.Cfg (Option Bool) (Fin (2*out.length+1)) :=
    ⟨0,Tape.mk₂ (input.reverse.map some) []⟩
  have hscan : nativeTMRun (nativeConstantTM out) input.length (TM0.init (input.map some)) = some mid := by
    simpa [TM0.init,Tape.mk₁,mid] using! nativeConst_scan out input []
  obtain ⟨cfg,hrun,hq,hout⟩ := nativeConst_emit_run out out.length hL le_rfl none
    (ListBlank.mk (input.reverse.map some)) (by intro _; rfl)
  have hrun' : nativeTMRun (nativeConstantTM out) (2*out.length-1) mid = some cfg := by
    simpa [mid,Tape.mk₂,Tape.mk',ListBlank.head_mk,ListBlank.tail_mk] using! hrun
  refine ⟨cfg,?_,?_,hout⟩
  · have hn : input.length+2*out.length-1 = input.length+(2*out.length-1) := by omega
    rw [← nativeTMRun_initial,hn,nativeTMRun_add_some _ _ _ _ _ hscan]
    exact hrun'
  · cases cfg with
    | mk q tape =>
      (try dsimp only at hq)
      subst q
      simp only [TM0.step,nativeConst_halt out hL,Option.map_none]

/-- The encoded natural number `sourceNatBits k` has length at most `2*k+1`. -/
theorem nativeNatBits_length (k : ℕ) : (sourceNatBits k).length ≤ 2*k+1 := by
  have h : k.bits.length ≤ k := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr k.lt_two_pow_self
  simp only [sourceNatBits,List.length_append,List.length_replicate,List.length_singleton]
  omega

/-- The resource constant `2*(sourceNativeProgramBits nativeTwoLabelProgram).length+8` used for
the constant native compiler. -/
def nativeTwoLabelConstant : ℕ := 2*(sourceNativeProgramBits nativeTwoLabelProgram).length+8

/-- The compiler returning `nativeTwoLabelProgram` has compiler-time bound
`nativeTwoLabelConstant` with exponent one. -/
theorem nativeTwoLabel_compiler :
    sourceNativeCompilerTime (fun _ _ => nativeTwoLabelProgram) nativeTwoLabelConstant 1 := by
  let out := sourceNativeProgramBits nativeTwoLabelProgram
  have hL : 0<out.length := by decide
  refine ⟨2*out.length,nativeConstantTM out,?_⟩
  intro d k
  obtain ⟨cfg,hrun,hhalt,hout⟩ :=
      nativeConstantTM_output out hL (sourceNatBits k++sourceProblemBits d)
  refine ⟨(sourceNatBits k++sourceProblemBits d).length+2*out.length-1,cfg,?_,hrun,hhalt,?_⟩
  · have hn := nativeNatBits_length k
    simp only [List.length_append,nativeTwoLabelProgram_calls,pow_one,nativeTwoLabelConstant]
    change _ ≤ (2*out.length+8)*(1+(sourceProblemBits d).length+k+1)
    have hs := Nat.sub_le ((sourceNatBits k).length+(sourceProblemBits d).length+2*out.length) 1
    nlinarith [Nat.zero_le (out.length*k),Nat.zero_le (out.length*(sourceProblemBits d).length)]
  · intro i
    rw [hout,ListBlank.nth_mk]
    exact (List.getD_default_eq_getI _).symm

/-- The native Hadamard gate matrix equals the Hadamard matrix lifted to its designated wire. -/
theorem native_h_eq_wire {n : ℕ} (a : Fin n) :
    localGateMatrix (.h a) = wireGate n a Hadamard := by
  ext x y
  rw [localGateMatrix_h,wireGate_apply]

/-- The native phase gate with coincident wire indices and unit phase parameter equals the
lifted Pauli Z matrix. -/
theorem native_phase_eq_wire {n : ℕ} (a : Fin n) :
    localGateMatrix (.cp a a 1 false) = wireGate n a PauliZ := by
  have hang : dyadicPhaseAngle 1 false=Real.pi := by
    simp [dyadicPhaseAngle]
  ext x y
  rw [localGateMatrix_cp,wireGate_apply]
  by_cases he : x=y
  · subst y
    cases hx : x a <;> simp [PauliZ,hang,Complex.exp_pi_mul_I]
  · rw [if_neg he]
    by_cases hs : ∀ k : Fin n, k≠a → x k=y k
    · have ha : x a≠y a := by
        intro h
        apply he
        funext k
        by_cases hk : k=a
        · subst k;exact h
        · exact hs k hk
      rw [if_pos hs]
      simp [PauliZ,ha]
    · rw [if_neg hs]

/-- Conjugating Pauli Z by the Hadamard matrix gives Pauli X. -/
theorem native_hzh : Hadamard * PauliZ * Hadamard=PauliX := by
  ext i j
  simp only [Hadamard,PauliZ,PauliX,permMatrix,Matrix.mul_apply,
    Matrix.of_apply,Matrix.diagonal_apply,Fintype.sum_bool]
  cases i <;> cases j <;> simp <;> ring_nf <;> norm_num [sqrt2_sq]

/-- The native Hadamard-phase-Hadamard sequence flips the designated bit of a basis register. -/
theorem native_flag_flip {n : ℕ} (a : Fin n) (z : Reg n) :
    (localGateMatrix (.h a) * localGateMatrix (.cp a a 1 false) * localGateMatrix (.h a)) *ᵥ Qatlib.Foundations.PureStateMath.Ket z =
      Qatlib.Foundations.PureStateMath.Ket (Function.update z a (!z a)) := by
  rw [native_h_eq_wire,native_phase_eq_wire,wireGate_mul,wireGate_mul,native_hzh]
  change ApplyGate (wireGate n a PauliX) (Qatlib.Foundations.PureStateMath.Ket z) = _
  rw [applyGate_wireGate_ket]
  cases hz : z a <;> simp [PauliX,permMatrix]

/-- The native swap of wires one and three changes the two-label register encoding from
`2*x.val` to `8*x.val`. -/
theorem nativeTwoLabel_swap (x : Fin 2) :
    localGateMatrix (.swap (1 : Fin 4) 3) *ᵥ Qatlib.Foundations.PureStateMath.Ket (sourceRegBits 4 (2*x.val)) =
      Qatlib.Foundations.PureStateMath.Ket (sourceRegBits 4 (8*x.val)) := by
  change permMatrix (fun z : Reg 4 => fun i => z (Equiv.swap 1 3 i)) *ᵥ _ = _
  change ApplyGate (permMatrix (fun z : Reg 4 => fun i => z (Equiv.swap 1 3 i))) _ = _
  rw [applyGate_permMatrix_ket (by intro z; funext i; simp)]
  congr 1
  funext i
  fin_cases x <;> fin_cases i <;> decide

/-- The three-gate flag flip changes the two-label register encoding from `8*x.val` to
`4+8*x.val`. -/
theorem nativeTwoLabel_flip (x : Fin 2) :
    (localGateMatrix (.h (2 : Fin 4)) * localGateMatrix (.cp 2 2 1 false) * localGateMatrix (.h 2)) *ᵥ
      Qatlib.Foundations.PureStateMath.Ket (sourceRegBits 4 (8*x.val)) = Qatlib.Foundations.PureStateMath.Ket (sourceRegBits 4 (4+8*x.val)) := by
  rw [native_flag_flip]
  congr 1
  funext i
  fin_cases x <;> fin_cases i <;> decide

/-- The complete two-label native program maps the zero basis register to the basis register
encoding `4+8*x.val`. -/
theorem nativeTwoLabel_basis (x : Fin 2) :
    sourceNativeMatrix sourceTwoLabelProblem x nativeTwoLabelProgram *ᵥ Qatlib.Foundations.PureStateMath.Ket (sourceRegBits 4 0) =
      Qatlib.Foundations.PureStateMath.Ket (sourceRegBits 4 (4+8*x.val)) := by
  let H := localGateMatrix (.h (2 : Fin 4))
  let Z := localGateMatrix (.cp (2 : Fin 4) 2 1 false)
  let S := localGateMatrix (.swap (1 : Fin 4) 3)
  let Q := sourceNativeStepMatrix sourceTwoLabelProblem x 4 (.query [0,1] false)
  have hm : sourceNativeMatrix sourceTwoLabelProblem x nativeTwoLabelProgram = H*Z*H*S*Q := by
    change H*(Z*(H*(S*(Q*(1 : Matrix (Reg 4) (Reg 4) ℂ))))) = H*Z*H*S*Q
    simp only [Matrix.mul_one,Matrix.mul_assoc]
  rw [hm]
  have hv : (H*Z*H*S*Q) *ᵥ Qatlib.Foundations.PureStateMath.Ket (sourceRegBits 4 0) =
      (H*Z*H) *ᵥ (S *ᵥ (Q *ᵥ Qatlib.Foundations.PureStateMath.Ket (sourceRegBits 4 0))) := by
    simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]
  erw [hv,nativeTwoLabel_query,nativeTwoLabel_swap]
  exact nativeTwoLabel_flip x

/-- The native two-label program exactly maps each clean initial state to its clean target
state. -/
theorem nativeTwoLabel_exact (x : Fin 2) :
    sourceNativeMatrix sourceTwoLabelProblem x nativeTwoLabelProgram *ᵥ
      sourceNativeClean sourceTwoLabelProblem 4 false (sourceRationalState (sourceTwoLabelProblem.start x)) =
    sourceNativeClean sourceTwoLabelProblem 4 true (sourceRationalState (sourceTwoLabelProblem.target x)) := by
  rw [nativeTwoLabel_start,nativeTwoLabel_target]
  erw [nativeFrame_ket sourceTwoLabelProblem 4 false (0 : Fin 2),
    nativeFrame_ket sourceTwoLabelProblem 4 true x]
  change sourceNativeMatrix sourceTwoLabelProblem x nativeTwoLabelProgram *ᵥ Qatlib.Foundations.PureStateMath.Ket (sourceRegBits 4 0) =
    Qatlib.Foundations.PureStateMath.Ket (sourceRegBits 4 (4+x.val*8))
  rw [Nat.mul_comm x.val 8]
  exact nativeTwoLabel_basis x

/-- The real part of the overlap between the native program output and the clean target state
equals one. -/
theorem nativeTwoLabel_overlap (x : Fin 2) :
    (∑ z : Reg 4, star ((sourceNativeMatrix sourceTwoLabelProblem x nativeTwoLabelProgram *ᵥ
      sourceNativeClean sourceTwoLabelProblem 4 false (sourceRationalState (sourceTwoLabelProblem.start x))) z)*
      sourceNativeClean sourceTwoLabelProblem 4 true (sourceRationalState (sourceTwoLabelProblem.target x)) z).re = 1 := by
  rw [nativeTwoLabel_exact,nativeTwoLabel_target]
  erw [nativeFrame_ket sourceTwoLabelProblem 4 true x]
  simp [Qatlib.Foundations.PureStateMath.Ket]

/-- There exists a uniformly compiled native program satisfying
`ActualNativeNonzeroQueryConsumer`, witnessed by the explicit two-label program. -/
theorem actualNativeNonzeroQueryConsumer : ActualNativeNonzeroQueryConsumer := by
  have hc : 8 ≤ nativeTwoLabelConstant := by
    unfold nativeTwoLabelConstant
    omega
  refine ⟨nativeTwoLabelConstant,1,(fun _ _ => nativeTwoLabelProgram),by omega,by decide,
    nativeTwoLabel_compiler,?_⟩
  intro k hk
  change sourceNativeLegal sourceTwoLabelProblem nativeTwoLabelProgram ∧
    0<sourceNativeCalls nativeTwoLabelProgram ∧
    sourceNativeCalls nativeTwoLabelProgram ≤ nativeTwoLabelConstant*4^k*(k+1) ∧
    sourceNativeGates nativeTwoLabelProgram ≤ nativeTwoLabelConstant*(1+(sourceProblemBits sourceTwoLabelProblem).length+k+sourceNativeCalls nativeTwoLabelProgram)^1 ∧
    sourceAddressBits sourceTwoLabelProblem+sourceValueBits sourceTwoLabelProblem+1+sourcePayloadBits sourceTwoLabelProblem ≤ 4 ∧
    4 ≤ nativeTwoLabelConstant*(1+(sourceProblemBits sourceTwoLabelProblem).length+k)^1 ∧ _
  refine ⟨nativeTwoLabelProgram_legal,?_,?_,?_,?_,?_,?_⟩
  · rw [nativeTwoLabelProgram_calls]
    omega
  · rw [nativeTwoLabelProgram_calls]
    have hp : 0<(4 : ℕ)^k := pow_pos (by decide) k
    have hp' : 1≤nativeTwoLabelConstant*4^k := by nlinarith
    nlinarith [Nat.zero_le (nativeTwoLabelConstant*4^k*k)]
  · rw [nativeTwoLabelProgram_gates,nativeTwoLabelProgram_calls,pow_one]
    nlinarith [Nat.zero_le (nativeTwoLabelConstant*(sourceProblemBits sourceTwoLabelProblem).length),
      Nat.zero_le (nativeTwoLabelConstant*k)]
  · decide
  · rw [pow_one]
    nlinarith [Nat.zero_le (nativeTwoLabelConstant*(sourceProblemBits sourceTwoLabelProblem).length),
      Nat.zero_le (nativeTwoLabelConstant*k)]
  · intro x
    erw [nativeTwoLabel_overlap]
    exact Real.sqrt_le_one.mpr (sub_le_self _ (pow_nonneg (by norm_num) k))

end Qatlib.Concepts.ConversionCore.WitnessCompile
