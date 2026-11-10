/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.ProgramModel.NativeProgramSemanticsStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.ProgramModel

open Matrix Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.QlsReadoutSpec.Amplification Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

theorem dataRegister_joinRegisters {h a : ℕ} (x : Reg h) (u : Reg a) :
    dataRegister (joinRegisters x u) = x := by
  funext i
  show joinRegisters x u ⟨i.val, _⟩ = x i
  unfold joinRegisters
  rw [dif_pos i.isLt]

theorem auxRegister_joinRegisters {h a : ℕ} (x : Reg h) (u : Reg a) :
    auxRegister (joinRegisters x u) = u := by
  funext i
  show joinRegisters x u ⟨h + i.val, _⟩ = u i
  unfold joinRegisters
  rw [dif_neg (by omega : ¬(h + i.val : ℕ) < h)]
  show u ⟨(h + i.val) - h, _⟩ = u i
  congr 1
  apply Fin.ext
  show ((h + i.val) - h : ℕ) = i.val
  omega

theorem joinRegisters_dataRegister {h a : ℕ} (w : Reg (h+a)) :
    joinRegisters (dataRegister w) (auxRegister w) = w := by
  funext i
  show (if hi : i.val < h then (dataRegister w) ⟨i.val, hi⟩ else (auxRegister w) ⟨i.val - h, _⟩) = w i
  by_cases hi : i.val < h
  · rw [dif_pos hi]
    show w i = w i
    rfl
  · rw [dif_neg hi]
    show w ⟨h + (i.val - h), _⟩ = w i
    congr 1
    apply Fin.ext
    show ((h + (i.val - h)) : ℕ) = i.val
    omega

def joinEquiv (h a : ℕ) : Reg h × Reg a ≃ Reg (h+a) where
  toFun p := joinRegisters p.1 p.2
  invFun w := (dataRegister w, auxRegister w)
  left_inv p := by
    rcases p with ⟨x, u⟩
    show (dataRegister (joinRegisters x u), auxRegister (joinRegisters x u)) = (x, u)
    rw [dataRegister_joinRegisters, auxRegister_joinRegisters]
  right_inv w := joinRegisters_dataRegister w

theorem sum_joinRegisters {h a : ℕ} {β : Type} [AddCommMonoid β] (f : Reg (h+a) → β) :
    ∑ w : Reg (h+a), f w = ∑ x : Reg h, ∑ u : Reg a, f (joinRegisters x u) := by
  have h1 : ∑ w : Reg (h+a), f w = ∑ p : Reg h × Reg a, f (joinEquiv h a p) :=
    (Equiv.sum_comp (joinEquiv h a) f).symm
  rw [h1, Fintype.sum_prod_type]
  rfl

theorem sum_auxRegister_eq {h a : ℕ} {β : Type} [AddCommMonoid β] (u₀ : Reg a)
    (g : Reg h → β) :
    ∑ w : Reg (h+a), (if auxRegister w = u₀ then g (dataRegister w) else 0) = ∑ x : Reg h, g x := by
  rw [sum_joinRegisters]
  have h1 : ∀ x : Reg h, ∑ u : Reg a,
      (if auxRegister (joinRegisters x u) = u₀ then g (dataRegister (joinRegisters x u)) else 0)
      = g x := by
    intro x
    simp only [dataRegister_joinRegisters, auxRegister_joinRegisters]
    rw [Finset.sum_eq_single u₀]
    · simp
    · intro u _ hu
      simp [hu]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  exact Finset.sum_congr rfl fun x _ => h1 x

theorem nativePadding_apply {h a : ℕ} (w : Reg (h+a)) (x : Reg h) :
    nativePadding h a w x = if w = joinRegisters x (ZeroStr a) then 1 else 0 := rfl

theorem joinRegisters_injective {h a : ℕ} (u : Reg a) :
    Function.Injective (fun x : Reg h => joinRegisters x u) := by
  intro x x' he
  have h1 : dataRegister (joinRegisters x u) = x := dataRegister_joinRegisters x u
  have h2 : dataRegister (joinRegisters x' u) = x' := dataRegister_joinRegisters x' u
  rw [← h1, ← h2]
  exact congrArg dataRegister he

theorem nativePadding_isometry (h a : ℕ) :
    (nativePadding h a)ᴴ * nativePadding h a = 1 := by
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have hsum : (∑ w : Reg (h+a), star (nativePadding h a w x) * nativePadding h a w x')
      = if x = x' then (1 : ℂ) else 0 := by
    have hterm : ∀ w : Reg (h+a),
        star (nativePadding h a w x) * nativePadding h a w x'
        = if w = joinRegisters x (ZeroStr a) ∧ w = joinRegisters x' (ZeroStr a) then (1 : ℂ) else 0 := by
      intro w
      rw [nativePadding_apply, nativePadding_apply]
      by_cases h1 : w = joinRegisters x (ZeroStr a)
      · by_cases h2 : w = joinRegisters x' (ZeroStr a)
        · rw [if_pos h1, if_pos h2, if_pos (And.intro h1 h2)]
          simp
        · rw [if_pos h1, if_neg h2]
          have hn : ¬(w = joinRegisters x (ZeroStr a) ∧ w = joinRegisters x' (ZeroStr a)) :=
            fun hc => h2 hc.2
          rw [if_neg hn]
          simp
      · rw [if_neg h1]
        have hn : ¬(w = joinRegisters x (ZeroStr a) ∧ w = joinRegisters x' (ZeroStr a)) :=
          fun hc => h1 hc.1
        rw [if_neg hn]
        simp [star_zero]
    rw [Finset.sum_congr rfl fun w _ => hterm w]
    have hinj : joinRegisters x (ZeroStr a) = joinRegisters x' (ZeroStr a) ↔ x = x' :=
      ⟨fun he => joinRegisters_injective (ZeroStr a) he, fun he => by rw [he]⟩
    by_cases heq : x = x'
    · subst heq
      have h1 : ∀ w : Reg (h+a),
          (if w = joinRegisters x (ZeroStr a) ∧ w = joinRegisters x (ZeroStr a) then (1 : ℂ) else 0)
          = if w = joinRegisters x (ZeroStr a) then (1 : ℂ) else 0 := by
        intro w
        by_cases hw : w = joinRegisters x (ZeroStr a) <;> simp [hw]
      rw [Finset.sum_congr rfl fun w _ => h1 w]
      rw [Finset.sum_eq_single (joinRegisters x (ZeroStr a))]
      · simp
      · intro w _ hw
        simp [hw]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · rw [if_neg heq]
      have hz : ∀ w : Reg (h+a),
          (if w = joinRegisters x (ZeroStr a) ∧ w = joinRegisters x' (ZeroStr a) then (1 : ℂ) else 0) = 0 := by
        intro w
        by_cases hw : w = joinRegisters x (ZeroStr a) ∧ w = joinRegisters x' (ZeroStr a)
        · exact absurd (hinj.mp (hw.1.symm.trans hw.2)) heq
        · simp [hw]
      rw [Finset.sum_congr rfl fun w _ => hz w]
      simp
  exact hsum

theorem nativePadding_mulVec_normalized {h a : ℕ} (ψ : QState (Reg h)) (hψ : Normalized ψ) :
    Normalized (nativePadding h a *ᵥ ψ) := by
  show ∑ w : Reg (h+a), ‖(nativePadding h a *ᵥ ψ) w‖ ^ 2 = 1
  have hval : ∀ w : Reg (h+a),
      (nativePadding h a *ᵥ ψ) w
      = if auxRegister w = ZeroStr a then ψ (dataRegister w) else 0 := by
    intro w
    show (∑ x : Reg h, nativePadding h a w x * ψ x) = _
    have hsingle : ∀ x : Reg h,
        nativePadding h a w x * ψ x
        = if w = joinRegisters x (ZeroStr a) then ψ x else 0 := by
      intro x
      rw [nativePadding_apply]
      by_cases hw : w = joinRegisters x (ZeroStr a) <;> simp [hw]
    rw [Finset.sum_congr rfl fun x _ => hsingle x]
    by_cases ha : auxRegister w = ZeroStr a
    · have hkey : w = joinRegisters (dataRegister w) (ZeroStr a) :=
        (joinRegisters_dataRegister w).symm.trans
          (congrArg (joinRegisters (dataRegister w)) ha)
      have hsum : (∑ x : Reg h, (if w = joinRegisters x (ZeroStr a) then ψ x else 0))
          = ψ (dataRegister w) := by
        have h1 : ∀ x : Reg h, (if w = joinRegisters x (ZeroStr a) then ψ x else 0)
            = if x = dataRegister w then ψ x else 0 := by
          intro x
          by_cases hx : x = dataRegister w
          · subst hx
            rw [if_pos rfl, if_pos hkey]
          · by_cases hw2 : w = joinRegisters x (ZeroStr a)
            · have : joinRegisters x (ZeroStr a) = joinRegisters (dataRegister w) (ZeroStr a) :=
                hw2.symm.trans hkey
              have hinj := joinRegisters_injective (ZeroStr a) this
              rw [if_neg hx]
              exact absurd hinj hx
            · simp [hx, hw2]
        rw [Finset.sum_congr rfl fun x _ => h1 x]
        rw [Finset.sum_eq_single (dataRegister w)]
        · simp
        · intro x _ hx
          simp [hx]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
      rw [hsum, if_pos ha]
    · have hzero : ∀ x : Reg h, (if w = joinRegisters x (ZeroStr a) then ψ x else 0) = 0 := by
        intro x
        by_cases hw : w = joinRegisters x (ZeroStr a)
        · rw [if_pos hw]
          have ha2 : auxRegister (joinRegisters x (ZeroStr a)) = ZeroStr a :=
            auxRegister_joinRegisters x (ZeroStr a)
          exact absurd (hw ▸ ha2) ha
        · simp [hw]
      rw [Finset.sum_congr rfl fun x _ => hzero x]
      simp [ha]
  rw [Finset.sum_congr rfl fun w _ => by rw [hval w]]
  have hsplit : (∑ w : Reg (h+a), ‖(if auxRegister w = ZeroStr a then ψ (dataRegister w) else 0)‖ ^ 2)
      = ∑ x : Reg h, ‖ψ x‖ ^ 2 := by
    rw [sum_joinRegisters]
    have h1 : ∀ x : Reg h, ∑ u : Reg a,
        ‖(if auxRegister (joinRegisters x u) = ZeroStr a then ψ (dataRegister (joinRegisters x u)) else 0)‖ ^ 2
        = ‖ψ x‖ ^ 2 := by
      intro x
      simp only [dataRegister_joinRegisters, auxRegister_joinRegisters]
      rw [Finset.sum_eq_single (ZeroStr a)]
      · simp
      · intro u _ hu
        simp [hu]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    exact Finset.sum_congr rfl fun x _ => h1 x
  rw [hsplit, hψ]

theorem nativeBranch_one {h a : ℕ} (ψ : QState (Reg (h+a))) (u : Reg a) :
    nativeBranch (1 : Matrix (Reg h) (Reg h) ℂ) ψ u = fun z => ψ (joinRegisters z u) := by
  show (1 : Matrix (Reg h) (Reg h) ℂ)ᴴ *ᵥ (fun z => ψ (joinRegisters z u)) = _
  rw [Matrix.conjTranspose_one, Matrix.one_mulVec]

theorem normVec_sq_nativeBranch_one {h a : ℕ} (ψ : QState (Reg (h+a))) (u : Reg a) :
    normVec (nativeBranch (1 : Matrix (Reg h) (Reg h) ℂ) ψ u) ^ 2
      = ∑ z : Reg h, ‖ψ (joinRegisters z u)‖ ^ 2 := by
  rw [nativeBranch_one]
  show (normVec (fun z => ψ (joinRegisters z u))) ^ 2 = _
  unfold normVec
  exact norm_toEuclidean_fromVec_sq _

private def callBlock {h a : ℕ} (oracles : Fin 2 → Matrix (Reg h) (Reg h) ℂ)
    (j : Fin 2) (c : Option (Fin a)) (value adj : Bool) (u : Reg a) :
    Matrix (Reg h) (Reg h) ℂ :=
  fun z z' =>
    let active := match c with | none => true | some wire => u wire = value
    if active then
      (if adj then (oracles j)ᴴ else oracles j) z z'
    else if z = z' then 1 else 0

theorem callBlock_unitary {h a : ℕ} (oracles : Fin 2 → Matrix (Reg h) (Reg h) ℂ)
    (j : Fin 2) (c : Option (Fin a)) (value adj : Bool) (u : Reg a)
    (hO : oracles j ∈ Matrix.unitaryGroup (Reg h) ℂ) :
    callBlock oracles j c value adj u ∈ Matrix.unitaryGroup (Reg h) ℂ := by
  cases c with
  | none =>
    have h1 : callBlock oracles j none value adj u = (if adj then (oracles j)ᴴ else oracles j) :=
        rfl
    rw [h1]
    cases adj with
    | true => exact Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hO
    | false => exact hO
  | some wire =>
    by_cases hu : u wire = value
    · have h1 : callBlock oracles j (some wire) value adj u = (if adj then (oracles j)ᴴ else oracles j) := by
        funext z z'
        show (if (match some wire with | none => true | some w => u w = value) then _ else _) = _
        simp [hu]
      rw [h1]
      cases adj with
      | true => exact Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hO
      | false => exact hO
    · have h1 : callBlock oracles j (some wire) value adj u = (1 : Matrix (Reg h) (Reg h) ℂ) := by
        funext z z'
        show (if (match some wire with | none => true | some w => u w = value) then _ else _) = _
        simp [hu, Matrix.one_apply]
      rw [h1]
      exact (Matrix.unitaryGroup (Reg h) ℂ).one_mem

theorem nativeStepMatrix_call_aux {h a : ℕ} (oracles : Fin 2 → Matrix (Reg h) (Reg h) ℂ)
    (j : Fin 2) (c : Option (Fin a)) (value adj : Bool) (p q : Reg (h+a)) :
    nativeStepMatrix oracles (.call j c value adj) p q
      = if auxRegister p = auxRegister q then
          callBlock oracles j c value adj (auxRegister p) (dataRegister p) (dataRegister q)
        else 0 := rfl

theorem callBlock_mul_conjTranspose {h a : ℕ} (oracles : Fin 2 → Matrix (Reg h) (Reg h) ℂ)
    (j : Fin 2) (c : Option (Fin a)) (value adj : Bool) (u : Reg a)
    (hO : oracles j ∈ Matrix.unitaryGroup (Reg h) ℂ) :
    callBlock oracles j c value adj u * (callBlock oracles j c value adj u)ᴴ = 1 := by
  have h := callBlock_unitary oracles j c value adj u hO
  rwa [Matrix.mem_unitaryGroup_iff] at h

theorem nativeCallMatrix_mul_conjTranspose {h a : ℕ}
    (oracles : Fin 2 → Matrix (Reg h) (Reg h) ℂ)
    (j : Fin 2) (c : Option (Fin a)) (value adj : Bool)
    (hO : oracles j ∈ Matrix.unitaryGroup (Reg h) ℂ) :
    nativeStepMatrix oracles (.call j c value adj)
      * (nativeStepMatrix oracles (.call j c value adj))ᴴ = 1 := by
  set M := nativeStepMatrix oracles (.call j c value adj)
  set B := callBlock oracles j c value adj
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have hMp : ∀ p r, M p r = if auxRegister p = auxRegister r then B (auxRegister p) (dataRegister p) (dataRegister r) else 0 :=
    fun p r => nativeStepMatrix_call_aux oracles j c value adj p r
  rw [Finset.sum_congr rfl fun r _ => by rw [hMp p r, hMp q r]]
  by_cases hau : auxRegister p = auxRegister q
  · have hsplit : (∑ r : Reg (h+a),
        (if auxRegister p = auxRegister r then B (auxRegister p) (dataRegister p) (dataRegister r) else 0)
          * star (if auxRegister q = auxRegister r then B (auxRegister q) (dataRegister q) (dataRegister r) else 0))
        = ∑ z : Reg h, B (auxRegister p) (dataRegister p) z * star (B (auxRegister q) (dataRegister q) z) := by
      rw [sum_joinRegisters]
      have hz : ∀ x : Reg h, ∑ u : Reg a,
          (if auxRegister p = auxRegister (joinRegisters x u) then B (auxRegister p) (dataRegister p) (dataRegister (joinRegisters x u)) else 0)
            * star (if auxRegister q = auxRegister (joinRegisters x u) then B (auxRegister q) (dataRegister q) (dataRegister (joinRegisters x u)) else 0)
          = B (auxRegister p) (dataRegister p) x * star (B (auxRegister q) (dataRegister q) x) := by
        intro x
        simp only [dataRegister_joinRegisters, auxRegister_joinRegisters]
        have hrew : ∀ u : Reg a,
            (if auxRegister p = u then B (auxRegister p) (dataRegister p) x else 0)
              * star (if auxRegister q = u then B (auxRegister q) (dataRegister q) x else 0)
            = if u = auxRegister p then B (auxRegister p) (dataRegister p) x * star (B (auxRegister q) (dataRegister q) x) else 0 := by
          intro u
          by_cases hu : u = auxRegister p
          · subst hu
            rw [if_pos rfl, if_pos hau.symm]
            simp
          · have hu2 : auxRegister p ≠ u := fun e => hu e.symm
            rw [if_neg hu2, if_neg hu]
            simp
        rw [Finset.sum_congr rfl fun u _ => hrew u]
        rw [Finset.sum_eq_single (auxRegister p)]
        · simp
        · intro u _ hu
          simp [hu]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
      exact Finset.sum_congr rfl fun x _ => hz x
    rw [hsplit]
    have hB : callBlock oracles j c value adj (auxRegister p)
        * (callBlock oracles j c value adj (auxRegister q))ᴴ = 1 := by
      rw [hau]
      exact callBlock_mul_conjTranspose oracles j c value adj (auxRegister q) hO
    have hsum : (∑ z : Reg h, B (auxRegister p) (dataRegister p) z * star (B (auxRegister q) (dataRegister q) z))
        = (B (auxRegister p) * (B (auxRegister q))ᴴ) (dataRegister p) (dataRegister q) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hsum, hB, Matrix.one_apply]
    by_cases hp : p = q
    · simp [hp]
    · have hp2 : dataRegister p ≠ dataRegister q := by
        intro e
        apply hp
        have h1 : p = joinRegisters (dataRegister p) (auxRegister p) :=
          (joinRegisters_dataRegister p).symm
        have h2 : q = joinRegisters (dataRegister q) (auxRegister q) :=
          (joinRegisters_dataRegister q).symm
        rw [h1, h2, e, hau]
      simp [hp, hp2]
  · have hz : ∀ r : Reg (h+a),
        (if auxRegister p = auxRegister r then B (auxRegister p) (dataRegister p) (dataRegister r) else 0)
          * star (if auxRegister q = auxRegister r then B (auxRegister q) (dataRegister q) (dataRegister r) else 0)
        = 0 := by
      intro r
      by_cases hp : auxRegister p = auxRegister r
      · have hq : ¬ auxRegister q = auxRegister r := fun e => hau (hp.trans e.symm)
        rw [if_pos hp, if_neg hq]
        simp
      · rw [if_neg hp]
        simp
    have hz2 : (∑ r : Reg (h+a),
        (if auxRegister p = auxRegister r then B (auxRegister p) (dataRegister p) (dataRegister r) else 0)
          * star (if auxRegister q = auxRegister r then B (auxRegister q) (dataRegister q) (dataRegister r) else 0)) = 0 :=
      Finset.sum_eq_zero fun r _ => hz r
    rw [hz2]
    by_cases hp : p = q
    · exact absurd hp (fun e => hau (congrArg auxRegister e))
    · simp [hp]

theorem nativeCallMatrix_unitary {h a : ℕ} (oracles : Fin 2 → Matrix (Reg h) (Reg h) ℂ)
    (j : Fin 2) (c : Option (Fin a)) (value adj : Bool)
    (hO : oracles j ∈ Matrix.unitaryGroup (Reg h) ℂ) :
    nativeStepMatrix oracles (.call j c value adj)
      ∈ Matrix.unitaryGroup (Reg (h+a)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact nativeCallMatrix_mul_conjTranspose oracles j c value adj hO

theorem nativeStepMatrix_unitary {h a : ℕ} (oracles : Fin 2 → Matrix (Reg h) (Reg h) ℂ)
    (s : NativeStep h a) (hO : ∀ j : Fin 2, oracles j ∈ Matrix.unitaryGroup (Reg h) ℂ) :
    nativeStepMatrix oracles s ∈ Matrix.unitaryGroup (Reg (h+a)) ℂ := by
  rcases s with g | ⟨j, c, value, adj⟩
  · exact localGateMatrix_unitary g
  · exact nativeCallMatrix_unitary oracles j c value adj (hO j)

theorem nativeMatrix_unitary {h : ℕ} (oracles : Fin 2 → Matrix (Reg h) (Reg h) ℂ)
    (p : NativeProgram h) (hO : ∀ j : Fin 2, oracles j ∈ Matrix.unitaryGroup (Reg h) ℂ) :
    nativeMatrix oracles p ∈ Matrix.unitaryGroup (Reg (h+p.ancilla)) ℂ := by
  show (p.steps.map (nativeStepMatrix oracles)).reverse.prod ∈ _
  refine (Matrix.unitaryGroup (Reg (h+p.ancilla)) ℂ).list_prod_mem ?_
  intro m hm
  have hex : ∃ s ∈ p.steps, nativeStepMatrix oracles s = m := by
    rw [← List.mem_map, ← List.mem_reverse]
    exact hm
  obtain ⟨s, hs, rfl⟩ := hex
  exact nativeStepMatrix_unitary oracles s hO

theorem nativeCounts_eq_length {h : ℕ} (p : NativeProgram h) :
    nativeCalls p 0 + nativeCalls p 1 + nativeGates p = p.steps.length := by
  unfold nativeCalls nativeGates
  induction p.steps with
  | nil => rfl
  | cons s l ih =>
    simp only [List.countP_cons, List.length_cons]
    rcases s with g | ⟨j, c, value, adj⟩
    · simp; omega
    · fin_cases j <;> simp <;> omega

theorem nativeMass_one_le_one {h : ℕ} (p : NativeProgram h)
    (out : QState (Reg (h+p.ancilla))) (hout : Normalized out) :
    nativeMass (1 : Matrix (Reg h) (Reg h) ℂ) p out ≤ 1 := by
  have hbr : ∀ u : Reg p.ancilla,
      normVec (nativeBranch (1 : Matrix (Reg h) (Reg h) ℂ) out u) ^ 2
        = ∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2 :=
    fun u => normVec_sq_nativeBranch_one out u
  show ∑ u ∈ p.success.toFinset, normVec (nativeBranch 1 out u) ^ 2 ≤ 1
  rw [Finset.sum_congr rfl fun u _ => hbr u]
  have hfull : (∑ u : Reg p.ancilla, ∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2) = 1 := by
    have key : (∑ u : Reg p.ancilla, ∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2)
        = ∑ w : Reg (h+p.ancilla), ‖out w‖ ^ 2 := by
      conv_lhs => rw [Finset.sum_comm]
      exact (sum_joinRegisters (fun w => ‖out w‖ ^ 2)).symm
    rw [key, hout]
  have hnonneg : ∀ u : Reg p.ancilla, 0 ≤ ∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2 :=
    fun u => Finset.sum_nonneg fun z _ => sq_nonneg _
  calc (∑ u ∈ p.success.toFinset, ∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2)
      ≤ (∑ u : Reg p.ancilla, ∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2) := by
        have h1 : ∑ u ∈ p.success.toFinset, ∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2
            + ∑ u ∈ Finset.univ \ p.success.toFinset, ∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2
            = ∑ u : Reg p.ancilla, ∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2 := by
          rw [add_comm]
          exact Finset.sum_sdiff (Finset.subset_univ _)
        have h2 : 0 ≤ ∑ u ∈ Finset.univ \ p.success.toFinset, ∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2 :=
          Finset.sum_nonneg fun u _ => hnonneg u
        linarith
    _ = 1 := hfull

theorem nativeMass_one_eq_sum {h : ℕ} (p : NativeProgram h)
    (out : QState (Reg (h+p.ancilla))) :
    nativeMass (1 : Matrix (Reg h) (Reg h) ℂ) p out
      = ∑ u ∈ p.success.toFinset, ∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2 := by
  show ∑ u ∈ p.success.toFinset, normVec (nativeBranch 1 out u) ^ 2 = _
  exact Finset.sum_congr rfl fun u _ => normVec_sq_nativeBranch_one out u

theorem pureDensity_eq_outerProduct' {I : Type} (ψ : QState I) :
    pureDensity ψ = outerProduct ψ := rfl

theorem nativeDensity_posSemidef {h : ℕ} (p : NativeProgram h)
    (out : QState (Reg (h+p.ancilla))) (hm : 0 < nativeMass (1 : Matrix (Reg h) (Reg h) ℂ) p out) :
    (nativeDensity (1 : Matrix (Reg h) (Reg h) ℂ) p out).PosSemidef := by
  set mass := nativeMass (1 : Matrix (Reg h) (Reg h) ℂ) p out
  show ((mass : ℂ)⁻¹ • ∑ u ∈ p.success.toFinset,
      pureDensity (nativeBranch (1 : Matrix (Reg h) (Reg h) ℂ) out u)).PosSemidef
  have hsum : (∑ u ∈ p.success.toFinset, pureDensity (nativeBranch (1 : Matrix (Reg h) (Reg h) ℂ) out u)).PosSemidef := by
    refine Matrix.posSemidef_sum _ ?_
    intro u _
    rw [pureDensity_eq_outerProduct']
    exact outerProduct_posSemidef _
  have hcle : (0 : ℂ) ≤ (mass : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv]
    exact_mod_cast inv_nonneg.mpr (le_of_lt hm)
  exact Matrix.PosSemidef.smul hsum hcle

theorem nativeDensity_trace {h : ℕ} (p : NativeProgram h)
    (out : QState (Reg (h+p.ancilla))) (hm : 0 < nativeMass (1 : Matrix (Reg h) (Reg h) ℂ) p out) :
    Matrix.trace (nativeDensity (1 : Matrix (Reg h) (Reg h) ℂ) p out) = 1 := by
  set mass := nativeMass (1 : Matrix (Reg h) (Reg h) ℂ) p out
  have hmass_coe : (mass : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  show Matrix.trace ((mass : ℂ)⁻¹ • ∑ u ∈ p.success.toFinset,
      pureDensity (nativeBranch (1 : Matrix (Reg h) (Reg h) ℂ) out u)) = 1
  rw [Matrix.trace_smul, Matrix.trace_sum]
  have htr : ∀ u ∈ p.success.toFinset,
      Matrix.trace (pureDensity (nativeBranch (1 : Matrix (Reg h) (Reg h) ℂ) out u))
        = ((∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2 : ℝ) : ℂ) := by
    intro u _
    rw [pureDensity_eq_outerProduct', trace_outerProduct, nativeBranch_one]
  rw [Finset.sum_congr rfl htr, ← Complex.ofReal_sum]
  have hsum : (∑ u ∈ p.success.toFinset, ∑ z : Reg h, ‖out (joinRegisters z u)‖ ^ 2 : ℝ) = mass := by
    exact (nativeMass_one_eq_sum p out).symm
  rw [hsum]
  exact inv_mul_cancel₀ hmass_coe

theorem Clause36NativeProgramSemantics_answer : Clause36NativeProgramSemantics := by
  intro h p UA UB hlegal hUA hUB
  set U := nativeMatrix (fun j => if j = 0 then UA else UB) p
  have hO : ∀ j : Fin 2, (fun j => if j = 0 then UA else UB) j
      ∈ Matrix.unitaryGroup (Reg h) ℂ := by
    intro j
    fin_cases j <;> simp [hUA, hUB]
  have hU : U ∈ Matrix.unitaryGroup (Reg (h+p.ancilla)) ℂ :=
    nativeMatrix_unitary (fun j => if j = 0 then UA else UB) p hO
  have hcount : nativeCalls p 0 + nativeCalls p 1 + nativeGates p = p.steps.length :=
    nativeCounts_eq_length p
  have hpadd : (nativePadding h p.ancilla)ᴴ * nativePadding h p.ancilla = 1 :=
    nativePadding_isometry h p.ancilla
  refine ⟨hU, hcount, hpadd, ?_⟩
  intro ψ hψ
  have hpad : Normalized (nativePadding h p.ancilla *ᵥ ψ) :=
    nativePadding_mulVec_normalized ψ hψ
  set out := U *ᵥ (nativePadding h p.ancilla *ᵥ ψ)
  have hout : Normalized out := by
    show Normalized (ApplyGate U (nativePadding h p.ancilla *ᵥ ψ))
    exact normalized_applyGate hU hpad
  have hmass : nativeMass (1 : Matrix (Reg h) (Reg h) ℂ) p out ≤ 1 :=
    nativeMass_one_le_one p out hout
  refine ⟨hout, hmass, ?_⟩
  intro hm
  exact ⟨nativeDensity_posSemidef p out hm, nativeDensity_trace p out hm⟩

end Qatlib.Concepts.QlsReadoutSpec.ProgramModel
