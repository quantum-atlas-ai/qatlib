/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeMcxPositive

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.RiskEstimation.PolyRotation
/-! All positive-control branches of the native emitter, including zero,
one and two controls. This is a wire-parametric paid gate word, with the
source's k-2 workspace requirement and no opaque MCX primitive. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for native Positive Mcx in the native mcx model. -/
def nativePositiveMcx {N : ℕ} (cs : List (Fin N)) (t : Fin N) (ws : List (Fin N)) :
    List (ReflectionGate N) :=
  match cs with
  | [] => [.inl (t,PauliX)]
  | [a] => [.inr (a,t)]
  | [a,b] => toffoliLocalSteps a b t
  | a::b::c::rest =>
    nativePrefixMcx (a::b::c::rest).dropLast ws ((a::b::c::rest).getLast (by simp)) t

/-- A single native Pauli X instruction toggles its selected computational-basis bit. -/
theorem nativeX_basis {N : ℕ} (t : Fin N) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile [.inl (t,PauliX)]) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (!(x t))) := by
  change ApplyGate (wireGate N t PauliX) (Qatlib.Foundations.PureStateMath.Ket x) = _
  rw [applyGate_wireGate_ket]
  cases hx : x t <;> simp [PauliX, permMatrix]

/-- Distinct controls, target and work wires with sufficient budget give the corrected prefix frame. -/
private theorem nativePrefix_frame {N : ℕ} (cs : List (Fin N)) (t : Fin N) (ws : List (Fin N))
    (hnd : (cs++[t]++ws).Nodup) (hbudget : cs.length-2 ≤ ws.length) :
    subsetRotationFrameCorrected cs.dropLast t ws := by
  have hn : (cs++(t::ws)).Nodup := by simpa only [List.append_assoc, List.singleton_append] using hnd
  obtain ⟨hcs,htws,hdis⟩ := List.nodup_append.mp hn
  refine ⟨hcs.sublist cs.dropLast_sublist, htws.tail, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_dropLast]
    omega
  · intro w hw
    exact hdis w (List.mem_of_mem_dropLast hw) t (by simp)
  · intro w hw he
    exact (List.nodup_cons.mp htws).1 (he ▸ hw)
  · intro w hw u hu
    exact hdis w (List.mem_of_mem_dropLast hw) u (by simp [hu])

/-- Every positive-control branch toggles the target by the conjunction and restores clean work. -/
theorem nativePositiveMcx_basis {N : ℕ} (cs : List (Fin N)) (t : Fin N) (ws : List (Fin N))
    (hnd : (cs++[t]++ws).Nodup) (hbudget : cs.length-2 ≤ ws.length)
    (x : Reg N) (hclean : ∀ w∈ws, x w=false) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (nativePositiveMcx cs t ws))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ subsetControlTrue cs x)) := by
  cases cs with
  | nil => simpa [nativePositiveMcx, subsetControlTrue] using nativeX_basis t x
  | cons a cs =>
    cases cs with
    | nil =>
      have hat : a ≠ t := by intro he; subst t; simp at hnd
      change ApplyGate (cnotGate N a t) (Qatlib.Foundations.PureStateMath.Ket x) = _
      simpa [subsetControlTrue] using applyGate_cnotGate_ket N a t hat x
    | cons b cs =>
      cases cs with
      | nil =>
        have hab : a ≠ b := by intro he; subst b; simp at hnd
        have hat : a ≠ t := by intro he; subst t; simp at hnd
        have hbt : b ≠ t := by intro he; subst t; simp at hnd
        simpa [nativePositiveMcx, subsetControlTrue] using
          (local_toffoli_fifteen_exact N a b t hab hat hbt).2.2 x
      | cons c rest =>
        let L := a::b::c::rest
        have hne : L ≠ [] := by simp [L]
        have hlast : L.getLast hne ∈ L := List.getLast_mem hne
        have hn : (L++(t::ws)).Nodup := by
          simpa only [List.append_assoc, List.singleton_append] using hnd
        have hd := (List.nodup_append.mp hn).2.2
        have hlc : L.getLast hne ∉ ws := fun he => hd _ hlast _ (by simp [he]) rfl
        have hlt : L.getLast hne ≠ t := hd _ hlast _ (by simp)
        have hall : (subsetControlTrue L.dropLast x && x (L.getLast hne)) =
            subsetControlTrue L x := by
          conv_rhs => rw [← List.dropLast_append_getLast hne]
          simp [subsetControlTrue]
        change Run 1 (reflectionCompile (nativePrefixMcx L.dropLast ws (L.getLast hne) t)) _ = _
        rw [nativePrefixMcx_basis L.dropLast ws _ t (by simp [L])
          (nativePrefix_frame L t ws hnd hbudget) hlc hlt x hclean, hall]

/-- The expanded positive-control word is legal under the distinct-wire and work-budget premises. -/
theorem nativePositiveMcx_legal {N : ℕ} (cs : List (Fin N)) (t : Fin N) (ws : List (Fin N))
    (hnd : (cs++[t]++ws).Nodup) (hbudget : cs.length-2 ≤ ws.length) :
    reflectionLegal (nativePositiveMcx cs t ws) := by
  cases cs with
  | nil =>
    intro g hg
    have he : g = .inl (t,PauliX) := by simpa [nativePositiveMcx] using hg
    subst g
    exact pauliX_unitary
  | cons a cs =>
    cases cs with
    | nil =>
      have hat : a ≠ t := by intro he; subst t; simp at hnd
      intro g hg
      have he : g = .inr (a,t) := by simpa [nativePositiveMcx] using hg
      subst g
      exact hat
    | cons b cs =>
      cases cs with
      | nil =>
        have hab : a ≠ b := by intro he; subst b; simp at hnd
        have hat : a ≠ t := by intro he; subst t; simp at hnd
        have hbt : b ≠ t := by intro he; subst t; simp at hnd
        exact toffoliLocalSteps_legal a b t hab hat hbt
      | cons c rest =>
        let L := a::b::c::rest
        have hne : L ≠ [] := by simp [L]
        have hlast : L.getLast hne ∈ L := List.getLast_mem hne
        have hn : (L++(t::ws)).Nodup := by
          simpa only [List.append_assoc, List.singleton_append] using hnd
        have hd := (List.nodup_append.mp hn).2.2
        exact nativePrefixMcx_legal L.dropLast ws _ t (by simp [L])
          (nativePrefix_frame L t ws hnd hbudget)
          (fun he => hd _ hlast _ (List.mem_cons_of_mem t he) rfl) (hd _ hlast _ (by simp))

/-- The zero, one and larger control branches have their exact emitted elementary lengths. -/
theorem nativePositiveMcx_length {N : ℕ} (cs : List (Fin N)) (t : Fin N) (ws : List (Fin N))
    (hbudget : cs.length-2 ≤ ws.length) :
    (nativePositiveMcx cs t ws).length = if cs.length≤1 then 1 else 15*(2*cs.length-3) := by
  cases cs with
  | nil => simp [nativePositiveMcx]
  | cons a cs =>
    cases cs with
    | nil => simp [nativePositiveMcx]
    | cons b cs =>
      cases cs with
      | nil => simp [nativePositiveMcx, toffoliLocalSteps_length]
      | cons c rest =>
        rw [nativePositiveMcx, nativePrefixMcx_length _ _ _ _ (by simpa using hbudget)]
        simp only [List.length_dropLast, List.length_cons]
        rw [ite_eq_right (by omega)]
        omega

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
