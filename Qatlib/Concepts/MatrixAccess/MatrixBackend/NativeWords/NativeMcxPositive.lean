/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeAndLadder

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.RiskEstimation.PolyRotation
/-! The large positive-control branch of the emitted `append_mcx`.
The prefix uses k-2 clean work bits for k controls. Uncompute reuses the
native CCX tables in reverse triple order, as the Python emitter does. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Controls are the prefix S followed by c; S has at least two entries. -/
def nativePrefixMcx {N : ℕ} (S ws : List (Fin N)) (c t : Fin N) :
    List (ReflectionGate N) :=
  ccxTriplesCompile (nativeAndLadder S ws) ++
    toffoliLocalSteps (subsetFlagWireCorrected S t ws) c t ++
    ccxTriplesCompile (nativeAndLadder S ws).reverse

/-- For a nontrivial prefix and sufficient budget, its flag wire belongs to the work pool. -/
theorem nativeFlag_mem_pool {N : ℕ} (S ws : List (Fin N)) (t : Fin N)
    (hlen : 2 ≤ S.length) (hbudget : S.length-1 ≤ ws.length) :
    subsetFlagWireCorrected S t ws ∈ ws := by
  cases S with
  | nil => simp at hlen
  | cons a S =>
    cases S with
    | nil => simp at hlen
    | cons b cs =>
      have hl := subsetActiveWorks_length (a::b::cs) ws hbudget
      cases hw : subsetActiveWorks (a::b::cs) ws with
      | nil => simp [hw] at hl
      | cons w ww =>
        apply List.mem_of_mem_take (i := (a::b::cs).length-1)
        change (subsetActiveWorks (a::b::cs) ws).getLastD t ∈
          subsetActiveWorks (a::b::cs) ws
        rw [hw]
        have he : (w::ww).getLastD t = ww.getLastD w := by
          cases ww <;> simp [List.getLastD]
        rw [he]
        exact List.getLastD_mem_cons

/-- Reverse native CCXs undo compute on every input, with no clean-input premise. -/
theorem nativeAndLadder_uncompute {N : ℕ} (S ws : List (Fin N)) (t : Fin N)
    (h : subsetRotationFrameCorrected S t ws) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (ccxTriplesCompile (nativeAndLadder S ws).reverse))
      (Qatlib.Foundations.PureStateMath.Ket (subsetLadderBasisCorrected S ws x)) = Qatlib.Foundations.PureStateMath.Ket x := by
  have hp := subsetAndLadderCorrected_transport S ws t h
  rw [← hp.2 x, run_reflectionCompile, run_reflectionCompile,
    ccxTriplesCompile_reverse_matrix _ (nativeAndLadder_legal S ws t h),
    nativeAndLadder_compile, ApplyGate, ApplyGate, Matrix.mulVec_mulVec]
  have hu := reflectionProgramMatrix_unitary _ hp.1
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  rw [hu, Matrix.one_mulVec]

/-- The prefix-controlled word is legal under the supported-wire frame and target separation. -/
theorem nativePrefixMcx_legal {N : ℕ} (S ws : List (Fin N)) (c t : Fin N)
    (hlen : 2 ≤ S.length) (h : subsetRotationFrameCorrected S t ws)
    (hc : c ∉ ws) (hct : c ≠ t) : reflectionLegal (nativePrefixMcx S ws c t) := by
  have hne : S ≠ [] := by intro he; simp [he] at hlen
  have hft := subsetFlagWireCorrected_ne S ws t h hne
  have hfc : subsetFlagWireCorrected S t ws ≠ c := by
    intro he
    exact hc (he ▸ nativeFlag_mem_pool S ws t hlen h.2.2.1)
  have hl := nativeAndLadder_legal S ws t h
  intro g hg
  simp only [nativePrefixMcx, List.mem_append] at hg
  rcases hg with (hg|hg)|hg
  · exact ccxTriplesCompile_legal _ hl g hg
  · exact toffoliLocalSteps_legal _ _ _ hfc hft hct g hg
  · apply ccxTriplesCompile_legal _ (fun u hu => hl u (List.mem_reverse.mp hu)) g hg

/-- Exact basis action includes restoration of the whole allocated pool.
Only the initial pool is clean; the target bit is arbitrary. -/
theorem nativePrefixMcx_basis {N : ℕ} (S ws : List (Fin N)) (c t : Fin N)
    (hlen : 2 ≤ S.length) (h : subsetRotationFrameCorrected S t ws)
    (hc : c ∉ ws) (hct : c ≠ t) (x : Reg N) (hclean : ∀ w∈ws, x w=false) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (nativePrefixMcx S ws c t))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (subsetControlTrue S x && x c))) := by
  have hne : S ≠ [] := by intro he; simp [he] at hlen
  have hft := subsetFlagWireCorrected_ne S ws t h hne
  have hfc : subsetFlagWireCorrected S t ws ≠ c := by
    intro he
    exact hc (he ▸ nativeFlag_mem_pool S ws t hlen h.2.2.1)
  have ht : t ∉ ws := by
    intro ht
    exact h.2.2.2.2.1 t ht rfl
  have hflag := subsetLadderBasisCorrected_flag S ws t h hne x hclean
  have hxt := nativeLadder_preserves S ws x t ht
  have hxc := nativeLadder_preserves S ws x c hc
  simp only [nativePrefixMcx, reflectionCompile_append, run_append]
  rw [nativeAndLadder_compile, (subsetAndLadderCorrected_transport S ws t h).2 x,
    (local_toffoli_fifteen_exact N _ c t hfc hft hct).2.2,
    hflag, hxt, hxc, ← subsetLadderBasisCorrected_update S ws t h]
  exact nativeAndLadder_uncompute S ws t h _

/-- Each native CCX costs exactly the pinned fifteen elementary instructions. -/
theorem nativePrefixMcx_length {N : ℕ} (S ws : List (Fin N)) (c t : Fin N)
    (hbudget : S.length-1 ≤ ws.length) :
    (nativePrefixMcx S ws c t).length = 15*(2*(S.length-1)+1) := by
  have hl := subsetAndLadderCorrected_length S ws hbudget
  rw [← nativeAndLadder_compile, ccxTriplesCompile_length] at hl
  simp only [nativePrefixMcx, List.length_append, ccxTriplesCompile_length,
    List.length_reverse, toffoliLocalSteps_length]
  omega

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
