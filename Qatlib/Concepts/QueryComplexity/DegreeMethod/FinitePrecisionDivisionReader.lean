/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs (frame)
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

def store (W : Fin 6 → Bits) (A D B C raw : Bits) : Slot → Bits :=
  Sum.elim W ![A,D,B,C,raw]

@[simp] theorem store_left (W : Fin 6 → Bits) (A D B C raw : Bits) (k : Fin 6) :
    store W A D B C raw (.inl k) = W k := rfl

@[simp] theorem store0 (W : Fin 6 → Bits) (A D B C raw : Bits) : store W A D B C raw (.inr 0) = A := rfl

@[simp] theorem store1 (W : Fin 6 → Bits) (A D B C raw : Bits) : store W A D B C raw (.inr 1) = D := rfl

@[simp] theorem store2 (W : Fin 6 → Bits) (A D B C raw : Bits) : store W A D B C raw (.inr 2) = B := rfl

@[simp] theorem store3 (W : Fin 6 → Bits) (A D B C raw : Bits) : store W A D B C raw (.inr 3) = C := rfl

@[simp] theorem store4 (W : Fin 6 → Bits) (A D B C raw : Bits) : store W A D B C raw (.inr 4) = raw := rfl

@[simp] theorem store_update0 (W : Fin 6 → Bits) (A D B C raw xs : Bits) :
    Function.update (store W A D B C raw) (.inr 0) xs = store W xs D B C raw := by
  funext k; cases k with
  | inl k => simp [store]
  | inr k => fin_cases k <;> simp [store]

@[simp] theorem store_update1 (W : Fin 6 → Bits) (A D B C raw xs : Bits) :
    Function.update (store W A D B C raw) (.inr 1) xs = store W A xs B C raw := by
  funext k; cases k with
  | inl k => simp [store]
  | inr k => fin_cases k <;> simp [store]

@[simp] theorem store_update2 (W : Fin 6 → Bits) (A D B C raw xs : Bits) :
    Function.update (store W A D B C raw) (.inr 2) xs = store W A D xs C raw := by
  funext k; cases k with
  | inl k => simp [store]
  | inr k => fin_cases k <;> simp [store]

@[simp] theorem store_update3 (W : Fin 6 → Bits) (A D B C raw xs : Bits) :
    Function.update (store W A D B C raw) (.inr 3) xs = store W A D B xs raw := by
  funext k; cases k with
  | inl k => simp [store]
  | inr k => fin_cases k <;> simp [store]

@[simp] theorem store_update4 (W : Fin 6 → Bits) (A D B C raw xs : Bits) :
    Function.update (store W A D B C raw) (.inr 4) xs = store W A D B C xs := by
  funext k; cases k with
  | inl k => simp [store]
  | inr k => fin_cases k <;> simp [store]

def readerSteps (A D B C : Bits) : ℕ :=
  2+(2*A.length+1)+(2*D.length+1)+(2*B.length+1)+(C.length+1)

theorem sign_run (sa sb : Bool) (rest : Bits) (W : Fin 6 → Bits) :
    stackRun program 2 ⟨some .signA,Local.init,store W [] [] [] [] (sa::sb::rest)⟩ =
      some ⟨some (.parse 0),{ Local.init with signA:=sa,signB:=sb },store W [] [] [] [] rest⟩ := by
  simp [stackRun,TM2.step,program,TM2.stepAux,Local.load,Local.init]

theorem reader_run (sa sb : Bool) (A D B C : Bits) (W : Fin 6 → Bits) :
    stackRun program (readerSteps A D B C)
      ⟨some .signA,Local.init,store W [] [] [] [] (sa::sb::(frame A++frame D++frame B++C))⟩ =
      some ⟨some .test,parsed sa sb A D B C,store W A.reverse D.reverse B.reverse C.reverse []⟩ := by
  have hA := parse_run 0 A (frame D++frame B++C) [] (store W [] [] [] [] [])
    ({ Local.init with signA:=sa,signB:=sb })
  rw [show (0 : Fin 3).castSucc.castSucc = (0 : Fin 5) from rfl,
    show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl] at hA
  simp only [setTwo,store_update4,store_update0,List.append_nil,nextField] at hA
  have hD := parse_run 1 D (frame B++C) [] (store W A.reverse [] [] [] [])
    (afterWord 0 ({ Local.init with signA:=sa,signB:=sb }) A)
  rw [show (1 : Fin 3).castSucc.castSucc = (1 : Fin 5) from rfl,
    show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl] at hD
  simp only [setTwo,store_update4,store_update1,List.append_nil,nextField] at hD
  have hB := parse_run 2 B C [] (store W A.reverse D.reverse [] [] [])
    (afterWord 1 (afterWord 0 ({ Local.init with signA:=sa,signB:=sb }) A) D)
  rw [show (2 : Fin 3).castSucc.castSucc = (2 : Fin 5) from rfl,
    show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl] at hB
  simp only [setTwo,store_update4,store_update2,List.append_nil,nextField] at hB
  have hC := last_run C [] (store W A.reverse D.reverse B.reverse [] [])
    (afterWord 2 (afterWord 1 (afterWord 0 ({ Local.init with signA:=sa,signB:=sb }) A) D) B)
  simp only [setTwo,store_update4,store_update3,List.append_nil] at hC
  simp only [List.append_assoc] at hA hD ⊢
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd, Nat.reduceLT,
    dite_true, dite_false] at hA hD hB
  norm_num at hA hD hB
  have htwo : (⟨2,by decide⟩ : Fin 3) = 2 := rfl
  try rw [htwo] at hD
  rw [show readerSteps A D B C = 2+((2*A.length+1)+((2*D.length+1)+
    ((2*B.length+1)+(C.length+1)))) by dsimp [readerSteps]; omega]
  rw [run_add,sign_run,Option.bind_some,run_add,hA,Option.bind_some,
    run_add,hD,Option.bind_some,run_add,hB,Option.bind_some]
  exact hC

theorem reader_raw (sa sb : Bool) (A D B C : Bits) :
    stackRun program (readerSteps A D B C)
      (TM2.init (Sum.inr (4 : Fin 5) : Slot) (input sa sb A D B C).reverse) =
      some ⟨some .test,parsed sa sb A D B C,
        store (fun _ => []) A.reverse D.reverse B.reverse C.reverse []⟩ := by
  have hi : (TM2.init (Sum.inr (4 : Fin 5) : Slot) (input sa sb A D B C).reverse :
      TM2.Cfg (fun _ : Slot => Bool) Label Local) =
      ⟨some .signA,Local.init,store (fun _ => []) [] [] [] []
        (sa::sb::(frame A++frame D++frame B++C))⟩ := by
    simp only [TM2.init,input,List.reverse_reverse]
    congr 1
    funext k
    cases k with
    | inl k => simp [store]
    | inr k => fin_cases k <;> simp [store]
  rw [hi]
  exact reader_run sa sb A D B C _

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader
