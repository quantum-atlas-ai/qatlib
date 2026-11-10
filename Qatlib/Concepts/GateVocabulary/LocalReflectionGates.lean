/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Foundations.QueryWordCore.Circuit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring

open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Matrix
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

abbrev ReflectionGate (n : ℕ) := Sum (Fin n × Matrix Bool Bool ℂ) (Fin n × Fin n)

def reflectionGateWires {n : ℕ} : ReflectionGate n → Finset (Fin n)
  | Sum.inl (w, _) => {w}
  | Sum.inr (c, t) => {c, t}

def reflectionGateLegal {n : ℕ} : ReflectionGate n → Prop
  | Sum.inl (_, U) => U ∈ Matrix.unitaryGroup Bool ℂ
  | Sum.inr (c, t) => c ≠ t

def reflectionLegal {n : ℕ} (gs : List (ReflectionGate n)) : Prop :=
  ∀ g ∈ gs, reflectionGateLegal g

noncomputable def wireGate (n : ℕ) (w : Fin n) (U : Matrix Bool Bool ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  relabelGate (bitVecEquiv n).symm
    (tensorPauliWireGate n w (relabelGate boolEquivFin2 U))

theorem wireGate_apply (n : ℕ) (w : Fin n) (U : Matrix Bool Bool ℂ) (x y : Reg n) :
    wireGate n w U x y =
      if ∀ k : Fin n, k ≠ w → x k = y k then U (x w) (y w) else 0 := by
  have hentry : ∀ b b' : Bool,
      (relabelGate boolEquivFin2 U) (boolEquivFin2 b) (boolEquivFin2 b') = U b b' := by
    intro b b'
    simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply]
    cases b <;> cases b' <;> rfl
  classical
  simp only [wireGate, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.apply_symm_apply, tensorPauliWireGate, tensorPauliProduct, pauliProductDensity,
    Matrix.of_apply]
  by_cases hsupp : ∀ k : Fin n, k ≠ w → x k = y k
  · rw [if_pos hsupp]
    rw [Finset.prod_eq_single w]
    · rw [if_pos rfl]
      show relabelGate boolEquivFin2 U (boolEquivFin2 (x w)) (boolEquivFin2 (y w)) = _
      rw [hentry]
    · intro k _ hkw
      have hone : (1 : Operator 2) (boolEquivFin2 (x k)) (boolEquivFin2 (y k)) = 1 := by
        rw [Matrix.one_apply, if_pos (congrArg _ (hsupp k hkw))]
      rw [if_neg hkw, hone]
    · intro h
      exact absurd (Finset.mem_univ w) h
  · rw [if_neg hsupp]
    obtain ⟨k, hkw, hne⟩ : ∃ k : Fin n, k ≠ w ∧ x k ≠ y k := by
      by_contra hc
      push Not at hc
      exact hsupp hc
    have hbf : boolEquivFin2 (x k) ≠ boolEquivFin2 (y k) :=
      fun h => hne (boolEquivFin2.injective h)
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    rw [if_neg hkw]
    rw [Matrix.one_apply, if_neg hbf]

private theorem relabelGate_mul' {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T] (e : S ≃ T) (A B : Matrix S S ℂ) :
    relabelGate e (A * B) = relabelGate e A * relabelGate e B := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Equiv.sum_comp e.symm
    (fun k => A (e.symm i) k * B k (e.symm j))).symm

private theorem relabelGate_one' {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T] (e : S ≃ T) : relabelGate e (1 : Matrix S S ℂ) = 1 := by
  ext i j
  simp [relabelGate, Matrix.one_apply]

private theorem relabelGate_conjTranspose' {S T : Type*} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (e : S ≃ T) (U : Matrix S S ℂ) :
    (relabelGate e U)ᴴ = relabelGate e Uᴴ := by
  ext i j
  simp [relabelGate]

private theorem relabelGate_mem_unitary' {S T : Type*} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] {U : Matrix S S ℂ} (hU : U ∈ Matrix.unitaryGroup S ℂ)
    (e : S ≃ T) : relabelGate e U ∈ Matrix.unitaryGroup T ℂ := by
  have hu : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hU)
  have hu' : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hU)
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, relabelGate_conjTranspose',
    ← relabelGate_mul', hu', relabelGate_one']

theorem wireGate_unitary (n : ℕ) (w : Fin n) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    wireGate n w U ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  relabelGate_mem_unitary'
    (tensorPauliWireGate_unitary n w (relabelGate boolEquivFin2 U)
      (relabelGate_mem_unitary' hU boolEquivFin2)) (bitVecEquiv n).symm

theorem wireGate_mul (n : ℕ) (w : Fin n) (U V : Matrix Bool Bool ℂ) :
    wireGate n w U * wireGate n w V = wireGate n w (U * V) := by
  simp only [wireGate, relabelGate_mul', ← tensorPauliWireGate_mul]

theorem wireGate_one (n : ℕ) (w : Fin n) : wireGate n w (1 : Matrix Bool Bool ℂ) = 1 := by
  have htp : tensorPauliWireGate n w (1 : Operator 2) = 1 := by
    have hfun : (fun j : Fin n => if j = w then (1 : Operator 2) else 1)
        = fun _ : Fin n => 1 := by
      funext j
      by_cases h : j = w <;> simp [h]
    rw [tensorPauliWireGate, hfun, tensorPauliProduct_one]
  simp only [wireGate, relabelGate_one', htp]

theorem wireGate_conjTranspose (n : ℕ) (w : Fin n) (U : Matrix Bool Bool ℂ) :
    (wireGate n w U)ᴴ = wireGate n w Uᴴ := by
  simp only [wireGate, relabelGate_conjTranspose', tensorPauliWireGate_conjTranspose]

noncomputable def cnotGate (n : ℕ) (c t : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  permMatrix (fun x : Reg n => Function.update x t (x t ^^ x c))

theorem cnotUpdate_involutive (n : ℕ) (c t : Fin n) (hct : c ≠ t) :
    Function.Involutive (fun x : Reg n => Function.update x t (x t ^^ x c)) := by
  intro x
  funext k
  by_cases hkt : k = t
  · subst hkt
    have hc : c ≠ k := fun h => hct h
    simp only [Function.update_self]
    have hcne : Function.update x k (x k ^^ x c) c = x c := by
      simp only [Function.update]
      rw [dif_neg hc]
    rw [hcne, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  · simp [Function.update, hkt]

theorem cnotGate_unitary (n : ℕ) (c t : Fin n) (hct : c ≠ t) :
    cnotGate n c t ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  permMatrix_unitary (cnotUpdate_involutive n c t hct)

theorem applyGate_cnotGate_ket (n : ℕ) (c t : Fin n) (hct : c ≠ t) (x : Reg n) :
    ApplyGate (cnotGate n c t) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ x c)) :=
  applyGate_permMatrix_ket (cnotUpdate_involutive n c t hct) x

noncomputable def reflectionGateMatrix {n : ℕ} : ReflectionGate n → Matrix (Reg n) (Reg n) ℂ
  | Sum.inl (w, U) => wireGate n w U
  | Sum.inr (c, t) => cnotGate n c t

noncomputable def reflectionCompile {n : ℕ} (gs : List (ReflectionGate n)) :
    Circuit (Reg n) :=
  gs.map (fun g => Step.gate (reflectionGateMatrix g))

noncomputable def reflectionProgramMatrix {n : ℕ} : List (ReflectionGate n) →
    Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | g :: gs => reflectionProgramMatrix gs * reflectionGateMatrix g

theorem run_reflectionCompile {n : ℕ} (gs : List (ReflectionGate n)) (ψ : QState (Reg n)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs) ψ =
      ApplyGate (reflectionProgramMatrix gs) ψ := by
  induction gs generalizing ψ with
  | nil => simp [reflectionCompile, reflectionProgramMatrix]
  | cons g gs ih =>
      simp only [reflectionCompile, List.map_cons, run_gate]
      rw [reflectionProgramMatrix, applyGate_mul]
      exact ih _

theorem reflectionGateMatrix_mem_unitary {n : ℕ} {g : ReflectionGate n}
    (hg : reflectionGateLegal g) :
    reflectionGateMatrix g ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  cases g with
  | inl p =>
      obtain ⟨w, U⟩ := p
      exact wireGate_unitary n w U hg
  | inr p =>
      obtain ⟨c, t⟩ := p
      exact cnotGate_unitary n c t hg

theorem queryCount_reflectionCompile {n : ℕ} (gs : List (ReflectionGate n)) :
    QueryCount (reflectionCompile gs) = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [reflectionCompile, List.map_cons, QueryCount]
      exact ih

theorem gateCount_reflectionCompile {n : ℕ} (gs : List (ReflectionGate n)) :
    GateCount (reflectionCompile gs) = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [reflectionCompile, List.map_cons, GateCount, List.length_cons]
      exact congrArg (· + 1) ih

theorem local_reflection_gate_support_unitarity_counts (n : ℕ)
    (gs : List (ReflectionGate n)) (hgs : reflectionLegal gs) :
    IsUnitaryCircuit (reflectionCompile gs) ∧
    QueryCount (reflectionCompile gs) = 0 ∧
    GateCount (reflectionCompile gs) = gs.length := by
  refine ⟨?_, queryCount_reflectionCompile gs, gateCount_reflectionCompile gs⟩
  intro U hU
  simp only [reflectionCompile, List.mem_map] at hU
  obtain ⟨g, hg_mem, hg_eq⟩ := hU
  injection hg_eq with hg_eq'
  subst hg_eq'
  exact reflectionGateMatrix_mem_unitary (hgs g hg_mem)

noncomputable def tGate : Matrix Bool Bool ℂ := Rz (Real.pi/4)

noncomputable def tGateAdj : Matrix Bool Bool ℂ := Rz (-(Real.pi/4))

noncomputable def toffoliLocalSteps {n : ℕ} (a b t : Fin n) : List (ReflectionGate n) :=
  [Sum.inl (t, Hadamard),
   Sum.inr (b, t),
   Sum.inl (t, tGateAdj),
   Sum.inr (a, t),
   Sum.inl (t, tGate),
   Sum.inr (b, t),
   Sum.inl (t, tGateAdj),
   Sum.inr (a, t),
   Sum.inl (b, tGate),
   Sum.inl (t, tGate),
   Sum.inl (t, Hadamard),
   Sum.inr (a, b),
   Sum.inl (a, tGate),
   Sum.inl (b, tGateAdj),
   Sum.inr (a, b)]

theorem toffoliLocalSteps_length {n : ℕ} (a b t : Fin n) :
    (toffoliLocalSteps a b t).length = 15 := rfl

theorem tGate_mem_unitary : tGate ∈ Matrix.unitaryGroup Bool ℂ := rz_unitary _

theorem tGateAdj_mem_unitary : tGateAdj ∈ Matrix.unitaryGroup Bool ℂ := rz_unitary _

theorem toffoliLocalSteps_legal {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) : reflectionLegal (toffoliLocalSteps a b t) := by
  intro g hg
  simp only [toffoliLocalSteps, List.mem_cons] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | habs
  · exact hadamard_unitary
  · exact hbt
  · exact tGateAdj_mem_unitary
  · exact hat
  · exact tGate_mem_unitary
  · exact hbt
  · exact tGateAdj_mem_unitary
  · exact hat
  · exact tGate_mem_unitary
  · exact tGate_mem_unitary
  · exact hadamard_unitary
  · exact hab
  · exact tGate_mem_unitary
  · exact tGateAdj_mem_unitary
  · exact hab
  · exact absurd habs (by simp)

theorem applyGate_wireGate_ket (n : ℕ) (w : Fin n) (U : Matrix Bool Bool ℂ) (x : Reg n) :
    ApplyGate (wireGate n w U) (Qatlib.Foundations.PureStateMath.Ket x) =
      U false (x w) • Qatlib.Foundations.PureStateMath.Ket (Function.update x w false)
        + U true (x w) • Qatlib.Foundations.PureStateMath.Ket (Function.update x w true) := by
  funext y
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
  rw [Finset.sum_eq_single x (fun j _ hj => by
        rw [if_neg hj, mul_zero])
      (fun h => absurd (Finset.mem_univ x) h)]
  rw [wireGate_apply]
  by_cases hsupp : ∀ k : Fin n, k ≠ w → y k = x k
  · rw [if_pos hsupp]
    cases hb : y w with
    | false =>
        have hy : y = Function.update x w false := by
          funext k
          by_cases hkw : k = w
          · subst hkw; rw [hb, Function.update_self]
          · rw [Function.update_of_ne hkw, hsupp k hkw]
        have hune : Function.update x w false ≠ Function.update x w true := by
          intro h
          have h2 := congrFun h w
          simp at h2
        rw [hy]
        simp only [Qatlib.Foundations.PureStateMath.Ket, smul_eq_mul, Pi.smul_apply,
            Pi.add_apply]
        rw [if_neg hune]
        simp
    | true =>
        have hy : y = Function.update x w true := by
          funext k
          by_cases hkw : k = w
          · subst hkw; rw [hb, Function.update_self]
          · rw [Function.update_of_ne hkw, hsupp k hkw]
        have hune : Function.update x w true ≠ Function.update x w false := by
          intro h
          have h2 := congrFun h w
          simp at h2
        rw [hy]
        simp only [Qatlib.Foundations.PureStateMath.Ket, smul_eq_mul, Pi.smul_apply,
            Pi.add_apply]
        rw [if_neg hune]
        simp
  · rw [if_neg hsupp]
    have hne : ∀ c : Bool, y ≠ Function.update x w c := by
      intro c hy
      subst hy
      exact hsupp (fun k hk => by
        rw [Function.update_of_ne hk])
    have h0 : Qatlib.Foundations.PureStateMath.Ket (Function.update x w false) y = 0 := by
      simp only [Qatlib.Foundations.PureStateMath.Ket]
      rw [if_neg (hne false)]
    have h1 : Qatlib.Foundations.PureStateMath.Ket (Function.update x w true) y = 0 := by
      simp only [Qatlib.Foundations.PureStateMath.Ket]
      rw [if_neg (hne true)]
    simp [h0, h1]

theorem reflectionApplyGate_add {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ)
    (ψ φ : QState I) :
    ApplyGate M (ψ + φ) = ApplyGate M ψ + ApplyGate M φ := Matrix.mulVec_add _ _ _

theorem reflectionApplyGate_smul {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ)
    (c : ℂ) (ψ : QState I) :
    ApplyGate M (c • ψ) = c • ApplyGate M ψ := Matrix.mulVec_smul _ _ _

def tofWire {n : ℕ} (a b t : Fin n) : Fin 3 → Fin n := ![a, b, t]

def tofRestr {n : ℕ} (a b t : Fin n) (x : Reg n) : Reg 3 := fun k => x (tofWire a b t k)

def tofEmb {n : ℕ} (a b t : Fin n) (u : Reg 3) (x : Reg n) : Reg n :=
  fun k => if k = a then u 0 else if k = b then u 1 else if k = t then u 2 else x k

theorem tofEmb_restrict {n : ℕ} (a b t : Fin n) (x : Reg n) :
    tofEmb a b t (tofRestr a b t x) x = x := by
  funext k
  by_cases hka : k = a
  · subst hka; simp [tofEmb, tofRestr, tofWire]
  · by_cases hkb : k = b
    · subst hkb; simp [tofEmb, tofRestr, tofWire, hka]
    · by_cases hkt : k = t
      · subst hkt; simp [tofEmb, tofRestr, tofWire, hka, hkb]
      · simp [tofEmb, hka, hkb, hkt]

theorem tofRestr_emb {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (u : Reg 3) (x : Reg n) : tofRestr a b t (tofEmb a b t u x) = u := by
  have hba : b ≠ a := fun h => hab h.symm
  have hta : t ≠ a := fun h => hat h.symm
  have htb : t ≠ b := fun h => hbt h.symm
  funext k
  fin_cases k <;> simp [tofRestr, tofEmb, tofWire, hba, hta, htb]

theorem tofEmb_emb {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (u w : Reg 3) (x : Reg n) : tofEmb a b t u (tofEmb a b t w x) = tofEmb a b t u x := by
  have hba : b ≠ a := fun h => hab h.symm
  have hta : t ≠ a := fun h => hat h.symm
  have htb : t ≠ b := fun h => hbt h.symm
  funext k
  by_cases hka : k = a
  · subst hka; simp [tofEmb]
  · by_cases hkb : k = b
    · subst hkb; simp [tofEmb, hba]
    · by_cases hkt : k = t
      · subst hkt; simp [tofEmb, hta]
      · simp [tofEmb, hka, hkb, hkt]

def tofCoreWire {n : ℕ} (a b t : Fin n) (w : Fin n) : Fin 3 :=
  if w = a then 0 else if w = b then 1 else 2

def tofCoreGate {n : ℕ} (a b t : Fin n) : ReflectionGate n → ReflectionGate 3
  | Sum.inl (w, U) => Sum.inl (tofCoreWire a b t w, U)
  | Sum.inr (c, t') => Sum.inr (tofCoreWire a b t c, tofCoreWire a b t t')

theorem tofCoreWire_injective {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) {w1 w2 : Fin n} (h1 : w1 = a ∨ w1 = b ∨ w1 = t)
    (h2 : w2 = a ∨ w2 = b ∨ w2 = t) :
    tofCoreWire a b t w1 = tofCoreWire a b t w2 → w1 = w2 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hta : t ≠ a := fun h => hat h.symm
  have htb : t ≠ b := fun h => hbt h.symm
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
    simp [tofCoreWire, hba, hta, htb]

theorem tofEmb_wire {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    {w : Fin n} (hw : w = a ∨ w = b ∨ w = t) (u : Reg 3) (x : Reg n) :
    tofEmb a b t u x w = u (tofCoreWire a b t w) := by
  have hba : b ≠ a := fun h => hab h.symm
  have hta : t ≠ a := fun h => hat h.symm
  have htb : t ≠ b := fun h => hbt h.symm
  rcases hw with rfl | rfl | rfl
  · simp [tofEmb, tofCoreWire]
  · simp [tofEmb, tofCoreWire, hba]
  · simp [tofEmb, tofCoreWire, hta, htb]

theorem tofEmb_update {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (u : Reg 3) (x : Reg n) :
    (∀ c : Bool, tofEmb a b t (Function.update u 0 c) x
      = Function.update (tofEmb a b t u x) a c) ∧
    (∀ c : Bool, tofEmb a b t (Function.update u 1 c) x
      = Function.update (tofEmb a b t u x) b c) ∧
    (∀ c : Bool, tofEmb a b t (Function.update u 2 c) x
      = Function.update (tofEmb a b t u x) t c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    funext k
    by_cases hka : k = a
    · rw [hka]
      simp [tofEmb, Function.update]
    · rw [Function.update_of_ne hka]
      simp [tofEmb, Function.update, hka]
  · intro c
    funext k
    by_cases hka : k = a
    · rw [hka, Function.update_of_ne (show a ≠ b from hab)]
      simp [tofEmb, Function.update]
    · by_cases hkb : k = b
      · rw [hkb]
        simp [tofEmb, Function.update, Ne.symm hab]
      · rw [Function.update_of_ne hkb]
        simp [tofEmb, Function.update, hka, hkb]
  · intro c
    funext k
    by_cases hka : k = a
    · rw [hka, Function.update_of_ne (show a ≠ t from hat)]
      simp [tofEmb, Function.update]
    · by_cases hkb : k = b
      · rw [hkb, Function.update_of_ne (show b ≠ t from hbt)]
        simp [tofEmb, Function.update]
      · by_cases hkt : k = t
        · rw [hkt]
          simp [tofEmb, Function.update, Ne.symm hat, Ne.symm hbt]
        · rw [Function.update_of_ne hkt]
          simp [tofEmb, hka, hkb, hkt]

private theorem sum_filter_update {M : Type*} [AddCommMonoid M] (kw : Fin 3) (u : Reg 3)
    (F : Reg 3 → M) :
    ∑ v : Reg 3, (if ∀ j : Fin 3, j ≠ kw → v j = u j then F v else 0)
      = F (Function.update u kw false) + F (Function.update u kw true) := by
  classical
  have hinj : ∀ c1 c2 : Bool, Function.update u kw c1 = Function.update u kw c2 → c1 = c2 := by
    intro c1 c2 h
    have h2 := congrFun h kw
    simpa [Function.update_self] using h2
  have hfilter : Finset.univ.filter (fun v => ∀ j : Fin 3, j ≠ kw → v j = u j)
      = Finset.univ.image (fun c : Bool => Function.update u kw c) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hsupp
      refine ⟨v kw, ?_⟩
      funext j
      by_cases hj : j = kw
      · subst hj; simp [Function.update_self]
      · rw [Function.update_of_ne hj, hsupp j hj]
    · rintro ⟨c, _, rfl⟩
      intro j hj
      rw [Function.update_of_ne hj]
  have hsplit : ∀ G : Reg 3 → M,
      ∑ v : Reg 3, (if ∀ j : Fin 3, j ≠ kw → v j = u j then G v else 0)
        = ∑ c : Bool, G (Function.update u kw c) := by
    intro G
    rw [← Finset.sum_filter, hfilter, Finset.sum_image]
    · exact fun c1 _ c2 _ h => hinj c1 c2 h
  rw [hsplit F, Fintype.sum_bool]
  exact add_comm _ _

private theorem applyGate_sum_finite {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I I ℂ) (K : J → QState I) (χ : J → ℂ) :
    ApplyGate M (∑ v, χ v • K v) = ∑ v, χ v • ApplyGate M (K v) := by
  rw [show ApplyGate M (∑ v, χ v • K v) = M *ᵥ (∑ v, χ v • K v) from rfl, Matrix.mulVec_sum]
  exact Finset.sum_congr rfl fun v _ => by
    rw [show χ v • ApplyGate M (K v) = χ v • (M *ᵥ K v) from rfl, ← Matrix.mulVec_smul]

private theorem sum_regroup {J : Type*} [Fintype J] {n : ℕ} (φ : J → ℂ) (c : J → J → ℂ)
    (K : J → QState (Reg n)) :
    ∑ v : J, φ v • ∑ w : J, c w v • K w
      = ∑ w : J, (∑ v : J, c w v * φ v) • K w := by
  simp_rw [Finset.smul_sum, smul_smul, mul_comm (φ _)]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => by rw [Finset.sum_smul]

private theorem sum_matrix_regroup {J : Type*} [Fintype J] (P C : J → J → ℂ)
    (φ : J → ℂ) (u : J) :
    ∑ v : J, P u v * (∑ w : J, C w v * φ w)
      = ∑ w : J, (∑ v : J, P u v * C w v) * φ w := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => by ring

private theorem sum_matrix_regroup2 {J : Type*} [Fintype J] (P C : J → J → ℂ)
    (φ : J → ℂ) (u : J) :
    ∑ w : J, P u w * (∑ v : J, C w v * φ v)
      = ∑ v : J, (∑ w : J, P u w * C w v) * φ v := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem tofCoreWire_eq_a {n : ℕ} (a b t : Fin n) : tofCoreWire a b t a = 0 := by
  simp [tofCoreWire]

theorem tofCoreWire_eq_b {n : ℕ} (a b t : Fin n) (hba : b ≠ a) : tofCoreWire a b t b = 1 := by
  simp [tofCoreWire, hba]

theorem tofCoreWire_eq_t {n : ℕ} (a b t : Fin n) (hta : t ≠ a) (htb : t ≠ b) :
    tofCoreWire a b t t = 2 := by
  simp [tofCoreWire, hta, htb]

theorem tofEmb_update_at {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    {w : Fin n} (hw : w = a ∨ w = b ∨ w = t) (u : Reg 3) (x : Reg n) (c : Bool) :
    Function.update (tofEmb a b t u x) w c
      = tofEmb a b t (Function.update u (tofCoreWire a b t w) c) x := by
  obtain ⟨h1, h2, h3⟩ := tofEmb_update a b t hab hat hbt u x
  rcases hw with hwa | hwb | hwt
  · rw [hwa, tofCoreWire_eq_a]
    exact (h1 c).symm
  · rw [hwb]
    have hba : b ≠ a := fun h => hab h.symm
    rw [tofCoreWire_eq_b a b t hba]
    exact (h2 c).symm
  · rw [hwt]
    have hta : t ≠ a := fun h => hat h.symm
    have htb : t ≠ b := fun h => hbt h.symm
    rw [tofCoreWire_eq_t a b t hta htb]
    exact (h3 c).symm

theorem wires_in_set {n : ℕ} (a b t : Fin n) {g : ReflectionGate n}
    (hgw : reflectionGateWires g ⊆ {a, b, t}) :
    ∀ w ∈ reflectionGateWires g, w = a ∨ w = b ∨ w = t := by
  intro w hw
  have hmem : w ∈ ({a, b, t} : Finset (Fin n)) := hgw hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem applyGate_gateMatrix_fibre {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) {g : ReflectionGate n} (hgl : reflectionGateLegal g)
    (hgw : reflectionGateWires g ⊆ {a, b, t}) (u : Reg 3) (x : Reg n) :
    ApplyGate (reflectionGateMatrix g) (Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t u x)) =
      ∑ v : Reg 3, reflectionGateMatrix (tofCoreGate a b t g) v u •
        Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t v x) := by
  cases g with
  | inl p =>
      obtain ⟨w, U⟩ := p
      have hw : w = a ∨ w = b ∨ w = t :=
        wires_in_set a b t hgw w (by
          show w ∈ ({w} : Finset (Fin n))
          simp)
      simp only [reflectionGateMatrix, tofCoreGate]
      rw [applyGate_wireGate_ket, tofEmb_wire a b t hab hat hbt hw,
        tofEmb_update_at a b t hab hat hbt hw, tofEmb_update_at a b t hab hat hbt hw]
      have hentry : ∀ v : Reg 3,
          wireGate 3 (tofCoreWire a b t w) U v u • Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t v x)
            = (if ∀ j : Fin 3, j ≠ tofCoreWire a b t w → v j = u j
                then U (v (tofCoreWire a b t w)) (u (tofCoreWire a b t w))
                  • Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t v x) else 0) := by
        intro v
        rw [wireGate_apply, ite_smul, zero_smul]
      rw [Finset.sum_congr rfl (fun v _ => hentry v), sum_filter_update]
      simp only [Function.update_self]
  | inr p =>
      obtain ⟨c0, t0⟩ := p
      have hct : c0 ≠ t0 := hgl
      have hcw : c0 = a ∨ c0 = b ∨ c0 = t :=
        wires_in_set a b t hgw c0 (by
          show c0 ∈ ({c0, t0} : Finset (Fin n))
          simp)
      have htw : t0 = a ∨ t0 = b ∨ t0 = t :=
        wires_in_set a b t hgw t0 (by
          show t0 ∈ ({c0, t0} : Finset (Fin n))
          simp)
      have hcc : tofCoreWire a b t c0 ≠ tofCoreWire a b t t0 := by
        intro h
        exact hct (tofCoreWire_injective a b t hab hat hbt hcw htw h)
      simp only [reflectionGateMatrix, tofCoreGate]
      rw [applyGate_cnotGate_ket n c0 t0 hct]
      rw [tofEmb_wire a b t hab hat hbt htw, tofEmb_wire a b t hab hat hbt hcw,
        tofEmb_update_at a b t hab hat hbt htw]
      have hsplit :
          ∑ v : Reg 3, cnotGate 3 (tofCoreWire a b t c0) (tofCoreWire a b t t0) v u •
              Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t v x)
            = Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t (Function.update u (tofCoreWire a b t t0)
                (u (tofCoreWire a b t t0) ^^ u (tofCoreWire a b t c0))) x) := by
        rw [Finset.sum_eq_single
          (Function.update u (tofCoreWire a b t t0)
            (u (tofCoreWire a b t t0) ^^ u (tofCoreWire a b t c0)))]
        · show (if Function.update u (tofCoreWire a b t t0)
                (u (tofCoreWire a b t t0) ^^ u (tofCoreWire a b t c0))
                = Function.update u (tofCoreWire a b t t0)
                  (u (tofCoreWire a b t t0) ^^ u (tofCoreWire a b t c0)) then (1:ℂ) else 0)
              • Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t (Function.update u (tofCoreWire a b t t0)
                (u (tofCoreWire a b t t0) ^^ u (tofCoreWire a b t c0))) x)
              = Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t (Function.update u (tofCoreWire a b t t0)
                (u (tofCoreWire a b t t0) ^^ u (tofCoreWire a b t c0))) x)
          rw [if_pos rfl, one_smul]
        · intro v _ hv
          show (if v = Function.update u (tofCoreWire a b t t0)
                (u (tofCoreWire a b t t0) ^^ u (tofCoreWire a b t c0)) then (1:ℂ) else 0)
              • Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t v x) = 0
          rw [if_neg hv, zero_smul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [hsplit]

theorem run_reflectionCompile_fibre {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (gs : List (ReflectionGate n)) (hgl : reflectionLegal gs)
    (hgw : ∀ g ∈ gs, reflectionGateWires g ⊆ {a, b, t}) (x : Reg n) (φ : Reg 3 → ℂ) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs)
        (∑ u : Reg 3, φ u • Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t u x)) =
      ∑ u : Reg 3, (∑ v : Reg 3,
        reflectionProgramMatrix (gs.map (tofCoreGate a b t)) u v * φ v)
        • Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t u x) := by
  induction gs generalizing φ with
  | nil =>
      show (∑ u : Reg 3, φ u • Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t u x)) = _
      simp only [reflectionProgramMatrix, List.map_nil, Matrix.one_apply, ite_mul,
        one_mul, zero_mul]
      exact Finset.sum_congr rfl fun u _ => by
        rw [Fintype.sum_ite_eq u φ]
  | cons g gs ih =>
      have hgll := hgl g List.mem_cons_self
      have hgwg := hgw g List.mem_cons_self
      have hglr : reflectionLegal gs := fun g' hg' => hgl g' (List.mem_cons_of_mem _ hg')
      have hgwr : ∀ g' ∈ gs, reflectionGateWires g' ⊆ {a, b, t} :=
        fun g' hg' => hgw g' (List.mem_cons_of_mem _ hg')
      simp only [reflectionCompile, List.map_cons, run_gate]
      rw [applyGate_sum_finite]
      simp only [applyGate_gateMatrix_fibre a b t hab hat hbt hgll hgwg]
      rw [sum_regroup]
      rw [show (List.map (fun g => Step.gate (reflectionGateMatrix g)) gs)
          = reflectionCompile gs from rfl]
      rw [ih hglr hgwr (fun w => ∑ v : Reg 3,
        reflectionGateMatrix (tofCoreGate a b t g) w v * φ v)]
      simp only [reflectionProgramMatrix, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun u _ =>
        congrArg (· • Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t u x))
          (sum_matrix_regroup2
            (fun j k => reflectionProgramMatrix (gs.map (tofCoreGate a b t)) j k)
            (fun j k => reflectionGateMatrix (tofCoreGate a b t g) j k) φ u)

private theorem sq_sqrt_two : (↑(Real.sqrt 2):ℂ) * (↑(Real.sqrt 2):ℂ) = 2 := by
  simpa only [pow_two] using sqrt2_sq

private theorem inv_sqrt_two_mul : (((Real.sqrt 2 : ℂ))⁻¹) * (((Real.sqrt 2 : ℂ))⁻¹)
    = (2:ℂ)⁻¹ := by
  rw [← mul_inv, sq_sqrt_two]

private theorem update_cons_zero (a b c v : Bool) :
    Function.update (![a, b, c] : Reg 3) 0 v = ![v, b, c] := by
  funext k
  fin_cases k <;> simp [Function.update]

private theorem update_cons_one (a b c v : Bool) :
    Function.update (![a, b, c] : Reg 3) 1 v = ![a, v, c] := by
  funext k
  fin_cases k <;> simp [Function.update]

private theorem update_cons_two (a b c v : Bool) :
    Function.update (![a, b, c] : Reg 3) 2 v = ![a, b, v] := by
  funext k
  fin_cases k <;> simp [Function.update]

private theorem exp_pi4_pos_mul_neg :
    Complex.exp (↑Real.pi / 4 * Complex.I) * Complex.exp (-(↑Real.pi / 4 * Complex.I)) = 1 := by
  rw [← Complex.exp_add,
    show ↑Real.pi / 4 * Complex.I + -(↑Real.pi / 4 * Complex.I) = 0 from by ring,
    Complex.exp_zero]

private theorem exp_pi4_neg_mul_pos :
    Complex.exp (-(↑Real.pi / 4 * Complex.I)) * Complex.exp (↑Real.pi / 4 * Complex.I) = 1 := by
  rw [← Complex.exp_add,
    show -(↑Real.pi / 4 * Complex.I) + ↑Real.pi / 4 * Complex.I = 0 from by ring,
    Complex.exp_zero]

private theorem exp_pi4_pos_sq :
    Complex.exp (↑Real.pi / 4 * Complex.I) * Complex.exp (↑Real.pi / 4 * Complex.I)
      = Complex.I := by
  rw [← Complex.exp_add,
    show ↑Real.pi / 4 * Complex.I + ↑Real.pi / 4 * Complex.I = ↑Real.pi / 2 * Complex.I from by
      field_simp
      ring,
    Complex.exp_pi_div_two_mul_I]

private theorem exp_pi4_neg_sq :
    Complex.exp (-(↑Real.pi / 4 * Complex.I)) * Complex.exp (-(↑Real.pi / 4 * Complex.I))
      = -Complex.I := by
  rw [← Complex.exp_add,
    show -(↑Real.pi / 4 * Complex.I) + -(↑Real.pi / 4 * Complex.I)
      = -(↑Real.pi / 2 * Complex.I) from by
      field_simp
      ring,
    Complex.exp_neg, Complex.exp_pi_div_two_mul_I]
  norm_num

private theorem qstate_eq_reg3 {ψ φ : QState (Reg 3)}
    (h : ∀ b0 b1 b2 : Bool, ψ ![b0, b1, b2] = φ ![b0, b1, b2]) : ψ = φ := by
  funext i
  have hi : i = ![i 0, i 1, i 2] := by funext k; fin_cases k <;> rfl
  rcases hb0 : i 0 with _ | _ <;> rcases hb1 : i 1 with _ | _ <;> rcases hb2 : i 2 with _ | _
  all_goals rw [hi, hb0, hb1, hb2]
  all_goals exact h _ _ _

private theorem flat4 (a b c d e : ℂ) : a * (b * (c * (d * e))) = a * b * (c * d) * e := by
  ring

private theorem exp_chain1 (c : ℂ) :
    Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
      (Complex.exp (↑Real.pi / 4 * Complex.I) *
        (Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
          (Complex.exp (↑Real.pi / 4 * Complex.I) * c))) = c := by
  rw [flat4]
  simp only [exp_pi4_neg_mul_pos, one_mul]

private theorem exp_chain2 (c : ℂ) :
    Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
      (Complex.exp (↑Real.pi / 4 * Complex.I) *
        (Complex.exp (↑Real.pi / 4 * Complex.I) * (c *
          Complex.exp (-(↑Real.pi / 4 * Complex.I))))) = c := by
  rw [show Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
        (Complex.exp (↑Real.pi / 4 * Complex.I) *
          (Complex.exp (↑Real.pi / 4 * Complex.I) * (c *
            Complex.exp (-(↑Real.pi / 4 * Complex.I))))) =
      (Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
          Complex.exp (↑Real.pi / 4 * Complex.I)) *
        (Complex.exp (↑Real.pi / 4 * Complex.I) *
          Complex.exp (-(↑Real.pi / 4 * Complex.I))) * c from by ring]
  simp only [exp_pi4_neg_mul_pos, exp_pi4_pos_mul_neg, one_mul]

private theorem exp_chain3 (c : ℂ) :
    Complex.exp (↑Real.pi / 4 * Complex.I) *
      (Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
        (c * (Complex.exp (↑Real.pi / 4 * Complex.I) *
          Complex.exp (-(↑Real.pi / 4 * Complex.I))))) = c := by
  rw [show Complex.exp (↑Real.pi / 4 * Complex.I) *
        (Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
          (c * (Complex.exp (↑Real.pi / 4 * Complex.I) *
            Complex.exp (-(↑Real.pi / 4 * Complex.I))))) =
      (Complex.exp (↑Real.pi / 4 * Complex.I) *
          Complex.exp (-(↑Real.pi / 4 * Complex.I))) *
        (Complex.exp (↑Real.pi / 4 * Complex.I) *
          Complex.exp (-(↑Real.pi / 4 * Complex.I))) * c from by ring]
  simp only [exp_pi4_pos_mul_neg, exp_pi4_pos_mul_neg, one_mul]

private theorem exp_chain4 (c : ℂ) :
    Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
      (Complex.exp (↑Real.pi / 4 * Complex.I) *
        (c * (Complex.exp (↑Real.pi / 4 * Complex.I) *
          Complex.exp (-(↑Real.pi / 4 * Complex.I))))) = c := by
  rw [show Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
        (Complex.exp (↑Real.pi / 4 * Complex.I) *
          (c * (Complex.exp (↑Real.pi / 4 * Complex.I) *
            Complex.exp (-(↑Real.pi / 4 * Complex.I))))) =
      (Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
          Complex.exp (↑Real.pi / 4 * Complex.I)) *
        (Complex.exp (↑Real.pi / 4 * Complex.I) *
          Complex.exp (-(↑Real.pi / 4 * Complex.I))) * c from by ring]
  simp only [exp_pi4_neg_mul_pos, exp_pi4_pos_mul_neg, one_mul]

private theorem exp_chain5 (c : ℂ) :
    Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
      (Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
        (Complex.exp (↑Real.pi / 4 * Complex.I) * (c *
          Complex.exp (↑Real.pi / 4 * Complex.I)))) = c := by
  rw [show Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
        (Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
          (Complex.exp (↑Real.pi / 4 * Complex.I) * (c *
            Complex.exp (↑Real.pi / 4 * Complex.I)))) =
      (Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
          Complex.exp (-(↑Real.pi / 4 * Complex.I))) *
        (Complex.exp (↑Real.pi / 4 * Complex.I) *
          Complex.exp (↑Real.pi / 4 * Complex.I)) * c from by ring]
  simp only [exp_pi4_neg_sq, exp_pi4_pos_sq, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

private theorem exp_chain6 (c : ℂ) :
    Complex.exp (↑Real.pi / 4 * Complex.I) *
      (Complex.exp (↑Real.pi / 4 * Complex.I) *
        (Complex.exp (↑Real.pi / 4 * Complex.I) * (c *
          Complex.exp (↑Real.pi / 4 * Complex.I)))) = -c := by
  rw [show Complex.exp (↑Real.pi / 4 * Complex.I) *
        (Complex.exp (↑Real.pi / 4 * Complex.I) *
          (Complex.exp (↑Real.pi / 4 * Complex.I) * (c *
            Complex.exp (↑Real.pi / 4 * Complex.I)))) =
      (Complex.exp (↑Real.pi / 4 * Complex.I) *
          Complex.exp (↑Real.pi / 4 * Complex.I)) *
        (Complex.exp (↑Real.pi / 4 * Complex.I) *
          Complex.exp (↑Real.pi / 4 * Complex.I)) * c from by ring]
  simp only [exp_pi4_pos_sq, Complex.I_mul_I, neg_one_mul]

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in

private theorem toffoli_core_run (u : Reg 3) :
    Run (1 : Matrix (Reg 3) (Reg 3) ℂ) (reflectionCompile (toffoliLocalSteps 0 1 2)) (Qatlib.Foundations.PureStateMath.Ket u)
      = Qatlib.Foundations.PureStateMath.Ket (Function.update u 2 (u 2 ^^ (u 0 && u 1))) := by
  rw [run_reflectionCompile]
  rcases h0 : u 0 with _ | _ <;> rcases h1 : u 1 with _ | _ <;> rcases h2 : u 2 with _ | _
  all_goals
    have hu : u = ![u 0, u 1, u 2] := by funext k; fin_cases k <;> rfl
    rw [hu, h0, h1, h2]
    simp only [reflectionProgramMatrix, reflectionGateMatrix, toffoliLocalSteps,
      applyGate_mul, applyGate_wireGate_ket,
      applyGate_cnotGate_ket 3 1 2 (by decide),
      applyGate_cnotGate_ket 3 0 2 (by decide),
      applyGate_cnotGate_ket 3 0 1 (by decide),
      reflectionApplyGate_add, reflectionApplyGate_smul, applyGate_one,
      Hadamard, tGate, tGateAdj, Rz, update_cons_zero, update_cons_one,
      update_cons_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.diagonal_apply, inv_sqrt_two_mul,
      smul_smul, smul_add, add_smul, zero_smul, add_zero, zero_add,
      Matrix.head_cons, Matrix.tail_cons,
      Bool.xor_self, Bool.xor_false, Bool.false_xor, Bool.true_xor, Bool.xor_true,
      Bool.and_self, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and,
      if_true, if_false, Bool.false_eq_true, Bool.true_eq_false]
    refine qstate_eq_reg3 ?_
    intro b0 b1 b2
    rcases b0 <;> rcases b1 <;> rcases b2 <;>
      simp only [Qatlib.Foundations.PureStateMath.Ket, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Matrix.of_apply,
        Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, Bool.false_eq_true,
        Bool.true_eq_false, if_true, if_false, one_mul, mul_one, zero_mul, mul_zero,
        add_zero, zero_add] <;>
      norm_num only [Complex.ofReal_div, Complex.ofReal_neg, neg_mul] <;>
      simp only [exp_chain1, exp_chain2, exp_chain3, exp_chain4, exp_chain5,
        exp_chain6, exp_pi4_pos_mul_neg, inv_sqrt_two_mul, mul_neg] <;>
      norm_num [inv_sqrt_two_mul]
  all_goals
    simp only [exp_chain1, exp_chain2, exp_chain3, exp_chain4, exp_chain5,
      exp_chain6, exp_pi4_pos_mul_neg, inv_sqrt_two_mul, mul_neg]
    norm_num [inv_sqrt_two_mul]
  all_goals
    simp only [← mul_assoc, exp_pi4_pos_mul_neg, exp_pi4_neg_mul_pos, one_mul,
      inv_sqrt_two_mul]
    norm_num

private theorem matrix_eq_of_mulVec_ket {I : Type*} [Fintype I] [DecidableEq I]
    (M N : Matrix I I ℂ) (h : ∀ j, M *ᵥ Qatlib.Foundations.PureStateMath.Ket j = N *ᵥ Qatlib.Foundations.PureStateMath.Ket j) : M = N := by
  ext i j
  have h2 := congrFun (h j) i
  simpa [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket] using h2

private theorem tofUpdate3_involutive :
    Function.Involutive (fun u : Reg 3 => Function.update u 2 (u 2 ^^ (u 0 && u 1))) := by
  intro u
  funext k
  by_cases hk : k = 2
  · subst hk
    simp [Function.update]
  · simp [Function.update, hk]

private theorem toffoli_core_matrix :
    reflectionProgramMatrix (toffoliLocalSteps 0 1 2)
      = permMatrix (fun u : Reg 3 => Function.update u 2 (u 2 ^^ (u 0 && u 1))) := by
  apply matrix_eq_of_mulVec_ket
  intro j
  have h1 : reflectionProgramMatrix (toffoliLocalSteps 0 1 2) *ᵥ Qatlib.Foundations.PureStateMath.Ket j
      = Run (1 : Matrix (Reg 3) (Reg 3) ℂ) (reflectionCompile (toffoliLocalSteps 0 1 2))
          (Qatlib.Foundations.PureStateMath.Ket j) := (run_reflectionCompile _ _).symm
  have h2 : (permMatrix fun u : Reg 3 => Function.update u 2 (u 2 ^^ (u 0 && u 1))) *ᵥ Qatlib.Foundations.PureStateMath.Ket j
      = Qatlib.Foundations.PureStateMath.Ket (Function.update j 2 (j 2 ^^ (j 0 && j 1))) :=
    applyGate_permMatrix_ket tofUpdate3_involutive j
  rw [h1, h2, toffoli_core_run]

private theorem toffoli_map_core {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) :
    (toffoliLocalSteps a b t).map (tofCoreGate a b t) = toffoliLocalSteps 0 1 2 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hta : t ≠ a := fun h => hat h.symm
  have htb : t ≠ b := fun h => hbt h.symm
  simp [toffoliLocalSteps, tofCoreGate, tofCoreWire, hba, hta, htb]

theorem tofEmb_target {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (x : Reg n) :
    tofEmb a b t (Function.update (tofRestr a b t x) 2
        ((tofRestr a b t x) 2 ^^ ((tofRestr a b t x) 0 && (tofRestr a b t x) 1))) x
      = Function.update x t (x t ^^ (x a && x b)) := by
  funext k
  by_cases hkt : k = t
  · rw [hkt]
    simp [tofEmb, tofRestr, tofWire, Function.update, Ne.symm hat, Ne.symm hbt]
  · rw [Function.update_of_ne hkt]
    by_cases hka : k = a
    · rw [hka]
      simp [tofEmb, tofRestr, tofWire, Function.update]
    · by_cases hkb : k = b
      · rw [hkb]
        simp [tofEmb, tofRestr, tofWire, Function.update, Ne.symm hab]
      · simp [tofEmb, hka, hkb, hkt]

private theorem hgw_toffoli {n : ℕ} (a b t : Fin n) {g : ReflectionGate n}
    (hg : g ∈ toffoliLocalSteps a b t) : reflectionGateWires g ⊆ {a, b, t} := by
  simp only [toffoliLocalSteps, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals simp [reflectionGateWires]

theorem local_toffoli_fifteen_exact (n : ℕ) (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) :
    (toffoliLocalSteps a b t).length = 15 ∧
    reflectionLegal (toffoliLocalSteps a b t) ∧
    ∀ x : Reg n, Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (reflectionCompile (toffoliLocalSteps a b t)) (Qatlib.Foundations.PureStateMath.Ket x)
      = Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (x a && x b))) := by
  refine ⟨toffoliLocalSteps_length a b t,
    toffoliLocalSteps_legal a b t hab hat hbt, ?_⟩
  intro x
  have hinit : ∑ u : Reg 3,
      (if u = tofRestr a b t x then (1:ℂ) else 0) • Qatlib.Foundations.PureStateMath.Ket (tofEmb a b t u x) = Qatlib.Foundations.PureStateMath.Ket x := by
    rw [Finset.sum_eq_single (tofRestr a b t x)]
    · rw [if_pos rfl, one_smul, tofEmb_restrict]
    · intro u _ hu
      rw [if_neg hu, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hf := run_reflectionCompile_fibre a b t hab hat hbt (toffoliLocalSteps a b t)
    (toffoliLocalSteps_legal a b t hab hat hbt)
    (fun g hg => hgw_toffoli a b t hg) x
    (fun u => if u = tofRestr a b t x then 1 else 0)
  rw [hinit] at hf
  have hcol : ∀ u : Reg 3,
      (∑ v : Reg 3,
        permMatrix (fun w : Reg 3 => Function.update w 2 (w 2 ^^ (w 0 && w 1))) u v
          * (if v = tofRestr a b t x then (1:ℂ) else 0))
        = permMatrix (fun w : Reg 3 => Function.update w 2 (w 2 ^^ (w 0 && w 1))) u
            (tofRestr a b t x) := by
    intro u
    rw [Finset.sum_eq_single (tofRestr a b t x)]
    · rw [if_pos rfl, mul_one]
    · intro v _ hv
      rw [if_neg hv, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hf, toffoli_map_core a b t hab hat hbt, toffoli_core_matrix]
  simp only [hcol]
  rw [Finset.sum_eq_single
    (Function.update (tofRestr a b t x) 2
      ((tofRestr a b t x) 2 ^^ ((tofRestr a b t x) 0 && (tofRestr a b t x) 1)))]
  have hp1 : permMatrix (fun w : Reg 3 => Function.update w 2 (w 2 ^^ (w 0 && w 1)))
      (Function.update (tofRestr a b t x) 2
        ((tofRestr a b t x) 2 ^^ ((tofRestr a b t x) 0 && (tofRestr a b t x) 1)))
      (tofRestr a b t x) = 1 := by
    simp only [permMatrix, Matrix.of_apply, if_true]
  · rw [hp1, one_smul, tofEmb_target a b t hab hat hbt]
  · intro u _ hu
    have h0 : permMatrix (fun w : Reg 3 => Function.update w 2 (w 2 ^^ (w 0 && w 1))) u
        (tofRestr a b t x) = 0 := by
      simp only [permMatrix, Matrix.of_apply, if_neg hu]
    rw [h0, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

noncomputable def reflectionGateAdjoint {n : ℕ} : ReflectionGate n → ReflectionGate n
  | .inl (w,U) => .inl (w,Uᴴ)
  | .inr p => .inr p

noncomputable def reflectionAdjoint {n : ℕ} (gs : List (ReflectionGate n)) :
    List (ReflectionGate n) := gs.reverse.map reflectionGateAdjoint

theorem reflectionProgramMatrix_append {n : ℕ} (gs hs : List (ReflectionGate n)) :
    reflectionProgramMatrix (gs ++ hs) = reflectionProgramMatrix hs * reflectionProgramMatrix gs := by
  induction gs with
  | nil => simp [reflectionProgramMatrix]
  | cons g gs ih => simp [reflectionProgramMatrix, ih, mul_assoc]

theorem reflectionProgramMatrix_unitary {n : ℕ} (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) : reflectionProgramMatrix gs ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  induction gs with
  | nil => exact (Matrix.unitaryGroup (Reg n) ℂ).one_mem
  | cons g gs ih =>
    exact (Matrix.unitaryGroup (Reg n) ℂ).mul_mem
      (ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg)))
      (reflectionGateMatrix_mem_unitary (hgs g List.mem_cons_self))

theorem reflectionGateAdjoint_legal {n : ℕ} (g : ReflectionGate n)
    (hg : reflectionGateLegal g) : reflectionGateLegal (reflectionGateAdjoint g) := by
  rcases g with ⟨w,U⟩ | ⟨c,t⟩
  · change Uᴴ ∈ Matrix.unitaryGroup Bool ℂ
    change U ∈ Matrix.unitaryGroup Bool ℂ at hg
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hg
  · exact hg

theorem reflectionGateAdjoint_matrix {n : ℕ} (g : ReflectionGate n)
    (hg : reflectionGateLegal g) :
    reflectionGateMatrix (reflectionGateAdjoint g) = (reflectionGateMatrix g)ᴴ := by
  rcases g with ⟨w,U⟩ | ⟨c,t⟩
  · exact (wireGate_conjTranspose n w U).symm
  · exact (permMatrix_conjTranspose (cnotUpdate_involutive n c t hg)).symm

theorem reflectionAdjoint_legal {n : ℕ} (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) : reflectionLegal (reflectionAdjoint gs) := by
  intro g hg
  obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
  exact reflectionGateAdjoint_legal g' (hgs g' (List.mem_reverse.mp hg'))

@[simp] theorem reflectionAdjoint_length {n : ℕ} (gs : List (ReflectionGate n)) :
    (reflectionAdjoint gs).length = gs.length := by simp [reflectionAdjoint]

theorem reflectionAdjoint_matrix {n : ℕ} (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) :
    reflectionProgramMatrix (reflectionAdjoint gs) = (reflectionProgramMatrix gs)ᴴ := by
  induction gs with
  | nil => simp [reflectionAdjoint, reflectionProgramMatrix]
  | cons g gs ih =>
    have htail : reflectionLegal gs := fun g hg => hgs g (List.mem_cons_of_mem _ hg)
    have hcons : reflectionAdjoint (g::gs) = reflectionAdjoint gs ++ [reflectionGateAdjoint g] := by
      simp [reflectionAdjoint]
    rw [hcons, reflectionProgramMatrix_append, reflectionProgramMatrix,
      reflectionProgramMatrix, one_mul, reflectionGateAdjoint_matrix g (hgs g List.mem_cons_self),
      ih htail, reflectionProgramMatrix, Matrix.conjTranspose_mul]

end Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false
namespace Qatlib.Concepts.GateVocabulary.LocalReflectionGates

theorem reflectionCompile_append {n : ℕ} (gs hs : List (ReflectionGate n)) :
    reflectionCompile (gs ++ hs) = reflectionCompile gs ++ reflectionCompile hs :=
  List.map_append

theorem reflectionLegal_append {n : ℕ} (gs hs : List (ReflectionGate n)) :
    reflectionLegal (gs++hs) ↔ reflectionLegal gs ∧ reflectionLegal hs := by
  simp only [reflectionLegal, List.mem_append, or_imp, forall_and]

theorem run_reflectionCompile_smul {n : ℕ} (gs : List (ReflectionGate n)) (c : ℂ)
    (ψ : QState (Reg n)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs) (c • ψ) =
      c • Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs) ψ := by
  simp only [run_reflectionCompile, reflectionApplyGate_smul]

theorem run_reflectionCompile_sum {J : Type*} [Fintype J] {n : ℕ}
    (gs : List (ReflectionGate n)) (ψ : J → QState (Reg n)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs) (∑ j,ψ j) =
      ∑ j, Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs) (ψ j) := by
  simp only [run_reflectionCompile, ApplyGate, Matrix.mulVec_sum]
end Qatlib.Concepts.GateVocabulary.LocalReflectionGates
