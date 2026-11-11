/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeMcx

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.RiskEstimation.PolyRotation
/-! Literal signed-control wrapper: X the zero controls in input order,
execute the positive word, then X them in reverse order. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for native Flip Word in the native signed mcx model. -/
def nativeFlipWord {N : ℕ} (L : List (Fin N)) : List (ReflectionGate N) :=
  L.map (fun w => .inl (w,PauliX))

/-- Construction for native Flip Basis in the native signed mcx model. -/
def nativeFlipBasis {N : ℕ} : List (Fin N) → Reg N → Reg N
  | [],x => x
  | w::ws,x => nativeFlipBasis ws (Function.update x w (!(x w)))

/-- The emitted sequence of X gates acts by the corresponding successive basis-bit updates. -/
theorem nativeFlipWord_basis {N : ℕ} (L : List (Fin N)) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (nativeFlipWord L)) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (nativeFlipBasis L x) := by
  induction L generalizing x with
  | nil => rfl
  | cons w ws ih =>
    have he : nativeFlipWord (w::ws) = [.inl (w,PauliX)]++nativeFlipWord ws := rfl
    rw [he, reflectionCompile_append, run_append, nativeX_basis, ih]
    rfl

/-- Every finite native flip word is a legal elementary program. -/
theorem nativeFlipWord_legal {N : ℕ} (L : List (Fin N)) :
    reflectionLegal (nativeFlipWord L) := by
  intro g hg
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp hg
  exact pauliX_unitary

/-- Appending flip lists composes their successive basis actions in program order. -/
theorem nativeFlipBasis_append {N : ℕ} (L K : List (Fin N)) (x : Reg N) :
    nativeFlipBasis (L++K) x = nativeFlipBasis K (nativeFlipBasis L x) := by
  induction L generalizing x with
  | nil => rfl
  | cons a L ih => exact ih _

/-- Reversing the same flip list restores every initial basis register. -/
theorem nativeFlipBasis_reverse {N : ℕ} (L : List (Fin N)) (x : Reg N) :
    nativeFlipBasis L.reverse (nativeFlipBasis L x) = x := by
  induction L generalizing x with
  | nil => rfl
  | cons a L ih =>
    simp only [List.reverse_cons, nativeFlipBasis, nativeFlipBasis_append, ih]
    simp

/-- The flip action preserves every wire absent from its list. -/
theorem nativeFlipBasis_outside {N : ℕ} (L : List (Fin N)) (x : Reg N) (w : Fin N)
    (hw : w ∉ L) : nativeFlipBasis L x w = x w := by
  induction L generalizing x with
  | nil => rfl
  | cons a L ih =>
    have hwa : w ≠ a := by intro he; exact hw (by simp [he])
    have hwL : w ∉ L := fun he => hw (by simp [he])
    simp only [nativeFlipBasis, ih _ hwL, Function.update_of_ne hwa]

/-- A duplicate-free flip list negates each bit on its selected wires exactly once. -/
theorem nativeFlipBasis_inside {N : ℕ} (L : List (Fin N)) (hnd : L.Nodup)
    (x : Reg N) (w : Fin N) (hw : w ∈ L) : nativeFlipBasis L x w = !(x w) := by
  induction L generalizing x with
  | nil => simp at hw
  | cons a L ih =>
    rcases List.mem_cons.mp hw with he | he
    · subst w
      rw [nativeFlipBasis, nativeFlipBasis_outside L _ a (List.nodup_cons.mp hnd).1,
        Function.update_self]
    · have hwa : w ≠ a := by intro heq; subst w; exact (List.nodup_cons.mp hnd).1 he
      simp only [nativeFlipBasis, ih hnd.tail _ he, Function.update_of_ne hwa]

/-- Flips on other wires commute with an update of the unselected target. -/
theorem nativeFlipBasis_update {N : ℕ} (L : List (Fin N)) (x : Reg N) (t : Fin N)
    (v : Bool) (ht : t ∉ L) :
    nativeFlipBasis L (Function.update x t v) = Function.update (nativeFlipBasis L x) t v := by
  induction L generalizing x with
  | nil => rfl
  | cons a L ih =>
    have hta : t ≠ a := by intro he; exact ht (by simp [he])
    have htL : t ∉ L := fun he => ht (by simp [he])
    simp only [nativeFlipBasis, Function.update_of_ne hta.symm]
    rw [Function.update_comm hta, ih _ htL]

/-- Construction for native Negative Wires in the native signed mcx model. -/
def nativeNegativeWires {N : ℕ} (pattern : List (Fin N × Bool)) : List (Fin N) :=
  (pattern.filter (fun p => !p.2)).map Prod.fst

/-- Negative-control wires form a sublist of the pattern wires in their original order. -/
theorem nativeNegativeWires_sublist {N : ℕ} (pattern : List (Fin N × Bool)) :
    List.Sublist (nativeNegativeWires pattern) (pattern.map Prod.fst) :=
  List.Sublist.map Prod.fst List.filter_sublist

/-- Flipping negative controls turns each signed-pattern match into a positive-control bit. -/
theorem nativeFlipBasis_pattern {N : ℕ} (pattern : List (Fin N × Bool))
    (hnd : (pattern.map Prod.fst).Nodup) (x : Reg N) (p : Fin N × Bool) (hp : p∈pattern) :
    nativeFlipBasis (nativeNegativeWires pattern) x p.1 = (x p.1 == p.2) := by
  have hn := hnd.sublist (nativeNegativeWires_sublist pattern)
  cases hb : p.2 with
  | false =>
    have hw : p.1 ∈ nativeNegativeWires pattern :=
      List.mem_map.mpr ⟨p,List.mem_filter.mpr ⟨hp,by simp [hb]⟩,rfl⟩
    rw [nativeFlipBasis_inside _ hn x _ hw]
    simp
  | true =>
    have hw : p.1 ∉ nativeNegativeWires pattern := by
      intro hw
      obtain ⟨q,hq,he⟩ := List.mem_map.mp hw
      have heq : q=p := List.inj_on_of_nodup_map hnd (List.mem_filter.mp hq).1 hp he
      subst q
      simp [hb] at hq
    rw [nativeFlipBasis_outside _ x _ hw]
    simp

/-- Construction for native Signed Mcx in the native signed mcx model. -/
def nativeSignedMcx {N : ℕ} (pattern : List (Fin N × Bool)) (t : Fin N) (ws : List (Fin N)) :
    List (ReflectionGate N) :=
  nativeFlipWord (nativeNegativeWires pattern) ++
    nativePositiveMcx (pattern.map Prod.fst) t ws ++
    nativeFlipWord (nativeNegativeWires pattern).reverse

/-- Every signed bitstring, arbitrary target input, and clean auxiliary pool.
The returned register differs only at the target. -/
theorem nativeSignedMcx_basis {N : ℕ} (pattern : List (Fin N × Bool)) (t : Fin N)
    (ws : List (Fin N)) (hnd : (pattern.map Prod.fst++[t]++ws).Nodup)
    (hbudget : pattern.length-2 ≤ ws.length) (x : Reg N) (hclean : ∀ w∈ws,x w=false) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (nativeSignedMcx pattern t ws))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ pattern.all (fun p => x p.1 == p.2))) := by
  let L := nativeNegativeWires pattern
  have hn : (pattern.map Prod.fst++(t::ws)).Nodup := by
    simpa only [List.append_assoc, List.singleton_append] using hnd
  obtain ⟨hcs,htws,hdis⟩ := List.nodup_append.mp hn
  have hout (w : Fin N) (hw : w∈t::ws) : w ∉ L := by
    intro hm
    exact hdis w ((nativeNegativeWires_sublist pattern).subset hm) w hw rfl
  have ht := hout t (by simp)
  have hc : ∀ w∈ws,nativeFlipBasis L x w=false := by
    intro w hw
    rw [nativeFlipBasis_outside L x w (hout w (by simp [hw]))]
    exact hclean w hw
  have hall : subsetControlTrue (pattern.map Prod.fst) (nativeFlipBasis L x) =
      pattern.all (fun p => x p.1 == p.2) := by
    apply Bool.eq_iff_iff.mpr
    simp only [subsetControlTrue, List.all_eq_true, List.mem_map]
    constructor
    · intro H p hp
      rw [← nativeFlipBasis_pattern pattern hcs x p hp]
      exact H p.1 ⟨p,hp,rfl⟩
    · intro H w hw
      obtain ⟨p,hp,rfl⟩ := hw
      rw [nativeFlipBasis_pattern pattern hcs x p hp]
      exact H p hp
  simp only [nativeSignedMcx, reflectionCompile_append, run_append]
  rw [nativeFlipWord_basis, nativePositiveMcx_basis _ t ws hnd (by simpa using hbudget) _ hc,
    hall, nativeFlipBasis_outside L x t ht, ← nativeFlipBasis_update L x t _ ht,
    nativeFlipWord_basis, nativeFlipBasis_reverse]

/-- The signed word is legal with distinct control, target and work wires and enough workspace. -/
theorem nativeSignedMcx_legal {N : ℕ} (pattern : List (Fin N × Bool)) (t : Fin N)
    (ws : List (Fin N)) (hnd : (pattern.map Prod.fst++[t]++ws).Nodup)
    (hbudget : pattern.length-2 ≤ ws.length) : reflectionLegal (nativeSignedMcx pattern t ws) := by
  rw [nativeSignedMcx, reflectionLegal_append, reflectionLegal_append]
  exact ⟨⟨nativeFlipWord_legal _,nativePositiveMcx_legal _ t ws hnd (by simpa using hbudget)⟩,
    nativeFlipWord_legal _⟩

/-- Signed compilation charges both negative-control flip lists and the positive MCX table. -/
theorem nativeSignedMcx_length {N : ℕ} (pattern : List (Fin N × Bool)) (t : Fin N)
    (ws : List (Fin N)) (hbudget : pattern.length-2 ≤ ws.length) :
    (nativeSignedMcx pattern t ws).length = 2*(nativeNegativeWires pattern).length +
      (if pattern.length≤1 then 1 else 15*(2*pattern.length-3)) := by
  simp only [nativeSignedMcx, List.length_append, nativeFlipWord, List.length_map,
    List.length_reverse]
  rw [nativePositiveMcx_length _ t ws (by simpa using hbudget)]
  simp only [List.length_map]
  omega

/-- The same signed program uses zero oracle queries and the stated exact elementary gate count. -/
theorem nativeSignedMcx_counts {N : ℕ} (pattern : List (Fin N × Bool)) (t : Fin N)
    (ws : List (Fin N)) (hbudget : pattern.length-2 ≤ ws.length) :
    QueryCount (reflectionCompile (nativeSignedMcx pattern t ws)) = 0 ∧
    GateCount (reflectionCompile (nativeSignedMcx pattern t ws)) =
      2*(nativeNegativeWires pattern).length +
        (if pattern.length≤1 then 1 else 15*(2*pattern.length-3)) := by
  exact ⟨queryCount_reflectionCompile _,
    (gateCount_reflectionCompile _).trans (nativeSignedMcx_length pattern t ws hbudget)⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
