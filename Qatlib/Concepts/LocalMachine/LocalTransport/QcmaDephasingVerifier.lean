/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityRefined
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open scoped Classical BigOperators
open scoped ComplexOrder
open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib
open Matrix

def wireTake {q n : ℕ} (z : Reg (q + n)) : Reg q := fun i => z (Fin.castAdd n i)

def wireDrop {q n : ℕ} (z : Reg (q + n)) : Reg n := fun i => z (Fin.natAdd q i)

def wireGlue {q n : ℕ} (y : Reg q) (c : Reg n) : Reg (q + n) := Fin.append y c

theorem wireGlue_take {q n : ℕ} (y : Reg q) (c : Reg n) :
    wireTake (wireGlue y c) = y := by
  funext i
  simp [wireGlue, wireTake, Fin.append_left]

theorem wireGlue_drop {q n : ℕ} (y : Reg q) (c : Reg n) :
    wireDrop (wireGlue y c) = c := by
  funext i
  simp [wireGlue, wireDrop, Fin.append_right]

theorem wire_cases {q n : ℕ} (k : Fin (q + n)) :
    (∃ i : Fin q, k = Fin.castAdd n i) ∨ (∃ j : Fin n, k = Fin.natAdd q j) := by
  rcases Nat.lt_or_ge k.val q with h | h
  · exact Or.inl ⟨⟨k.val, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨k.val - q, by omega⟩, Fin.ext ?_⟩
    simp only [Fin.val_natAdd]
    omega

theorem castAdd_inj' {q n : ℕ} {i j : Fin q} (h : Fin.castAdd n i = Fin.castAdd n j) :
    i = j :=
  Fin.ext (by simpa using congrArg Fin.val h)

theorem wireTake_drop {q n : ℕ} (z : Reg (q + n)) :
    wireGlue (wireTake z) (wireDrop z) = z := by
  funext k
  classical
  rcases wire_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · simp [wireGlue, wireTake, Fin.append_left]
  · simp [wireGlue, wireDrop, Fin.append_right]

theorem wireGlue_inj {q n : ℕ} {y y' : Reg q} {c c' : Reg n}
    (h : wireGlue y c = wireGlue y' c') : y = y' ∧ c = c' := by
  refine ⟨?_, ?_⟩
  · rw [← wireGlue_take y c, ← wireGlue_take y' c', h]
  · rw [← wireGlue_drop y c, ← wireGlue_drop y' c', h]

theorem wireGlue_eq {q n : ℕ} {y y' : Reg q} {c c' : Reg n} :
    wireGlue y c = wireGlue y' c' ↔ y = y' ∧ c = c' :=
  ⟨wireGlue_inj, fun ⟨hy, hc⟩ => by rw [hy, hc]⟩

theorem update_glue_left {q n : ℕ} (y : Reg q) (c : Reg n) (t : Fin q) (v : Bool) :
    Function.update (wireGlue y c) (Fin.castAdd n t) v
      = wireGlue (Function.update y t v) c := by
  funext k
  classical
  rcases wire_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · by_cases hit : i = t
    · subst hit
      simp [wireGlue, Fin.append_left]
    · have hne : Fin.castAdd n i ≠ Fin.castAdd n t := fun h => hit (castAdd_inj' h)
      simp [wireGlue, Fin.append_left, hne, hit]
  · have hne : Fin.natAdd q j ≠ Fin.castAdd n t := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      have ht := t.isLt
      omega
    simp [wireGlue, Fin.append_right, hne]

def regGlueEquiv (q n : ℕ) : (Reg q × Reg n) ≃ Reg (q + n) where
  toFun yc := wireGlue yc.1 yc.2
  invFun z := (wireTake z, wireDrop z)
  left_inv yc := Prod.ext (wireGlue_take yc.1 yc.2) (wireGlue_drop yc.1 yc.2)
  right_inv z := wireTake_drop z

theorem sum_wireGlue {q n : ℕ} (f : Reg (q + n) → ℂ) :
    ∑ z : Reg (q + n), f z = ∑ y : Reg q, ∑ c : Reg n, f (wireGlue y c) := by
  classical
  rw [Fintype.sum_equiv (regGlueEquiv q n).symm f
    (fun p : Reg q × Reg n => f (wireGlue p.1 p.2))
    (fun z => by
      show f z = f (wireGlue (wireTake z) (wireDrop z))
      rw [wireTake_drop])]
  rw [Fintype.sum_prod_type]

theorem natAdd_ne_castAdd {q n : ℕ} (j : Fin n) (i : Fin q) :
    Fin.natAdd q j ≠ Fin.castAdd n i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
  omega

theorem wireGate_embed {q n : ℕ} (w : ℕ) (hw : w < q) (U : Matrix Bool Bool ℂ)
    (za zb : Reg (q + n)) :
    wireGate (q + n) ⟨w, by omega⟩ U za zb
      = if wireDrop za = wireDrop zb
        then wireGate q ⟨w, hw⟩ U (wireTake za) (wireTake zb) else 0 := by
  classical
  rw [wireGate_apply, wireGate_apply]
  have hcond : (∀ k : Fin (q + n), k ≠ (⟨w, by omega⟩ : Fin (q + n)) → za k = zb k)
      ↔ (∀ k : Fin q, k ≠ (⟨w, hw⟩ : Fin q) → wireTake za k = wireTake zb k)
        ∧ (∀ j : Fin n, za (Fin.natAdd q j) = zb (Fin.natAdd q j)) := by
    constructor
    · intro h
      have hidx : (⟨w, by omega⟩ : Fin (q + n)) = Fin.castAdd n (⟨w, hw⟩ : Fin q) :=
        Fin.ext rfl
      refine ⟨fun k hk => h (Fin.castAdd n k) ?_, fun j => h (Fin.natAdd q j) ?_⟩
      · intro hcd
        exact hk (castAdd_inj' (hcd.trans hidx))
      · exact natAdd_ne_castAdd j ⟨w, hw⟩
    · intro hcond' k hk
      rcases wire_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · refine hcond'.1 i (fun h => hk ?_)
        subst h
        rfl
      · exact hcond'.2 j
  by_cases hdrop : wireDrop za = wireDrop zb
  · rw [if_pos hdrop]
    have hd' : ∀ j : Fin n, za (Fin.natAdd q j) = zb (Fin.natAdd q j) :=
      funext_iff.mp hdrop
    by_cases hsmall : ∀ k : Fin q, k ≠ (⟨w, hw⟩ : Fin q) → wireTake za k = wireTake zb k
    · rw [if_pos (hcond.mpr ⟨hsmall, hd'⟩), if_pos hsmall]
      rfl
    · rw [if_neg (fun h => hsmall (hcond.mp h).1), if_neg hsmall]
  · rw [if_neg hdrop]
    have hd' : ¬ (∀ j : Fin n, za (Fin.natAdd q j) = zb (Fin.natAdd q j)) := by
      intro h
      exact hdrop (funext_iff.mpr h)
    rw [if_neg (fun h => hd' (hcond.mp h).2)]

theorem permMatrix_apply {I : Type*} (σ : I → I) (i j : I) :
    permMatrix σ i j = if i = σ j then (1 : ℂ) else 0 := rfl

theorem permUpdateGate_embed {q n : ℕ} (t : ℕ) (ht : t < q) (val : Reg q → Bool)
    (za zb : Reg (q + n)) :
    permMatrix (fun x : Reg (q + n) => Function.update x ⟨t, by omega⟩ (val (wireTake x))) za zb
      = if wireDrop za = wireDrop zb
        then permMatrix (fun y : Reg q => Function.update y ⟨t, ht⟩ (val y))
            (wireTake za) (wireTake zb) else 0 := by
  classical
  show (if za = Function.update zb ⟨t, by omega⟩ (val (wireTake zb)) then (1 : ℂ) else 0)
      = if wireDrop za = wireDrop zb
        then (if wireTake za = Function.update (wireTake zb) (⟨t, ht⟩ : Fin q)
            (val (wireTake zb)) then (1 : ℂ) else 0)
        else 0
  rw [← wireTake_drop za, ← wireTake_drop zb]
  simp only [wireGlue_take, wireGlue_drop]
  rw [show (⟨t, by omega⟩ : Fin (q + n)) = Fin.castAdd n (⟨t, ht⟩ : Fin q) from Fin.ext rfl,
    update_glue_left]
  simp only [wireGlue_eq]
  by_cases hdrop : wireDrop za = wireDrop zb
  · by_cases htake : wireTake za
        = Function.update (wireTake zb) (⟨t, ht⟩ : Fin q) (val (wireTake zb))
    · rw [if_pos ⟨htake, hdrop⟩, if_pos hdrop, if_pos htake]
    · rw [if_neg (fun h => htake h.1), if_pos hdrop, if_neg htake]
  · rw [if_neg (fun h => hdrop h.2), if_neg hdrop]

theorem cnotGate_embed {q n : ℕ} (c t : ℕ) (hc : c < q) (ht : t < q)
    (za zb : Reg (q + n)) :
    cnotGate (q + n) ⟨c, by omega⟩ ⟨t, by omega⟩ za zb
      = if wireDrop za = wireDrop zb
        then cnotGate q ⟨c, hc⟩ ⟨t, ht⟩ (wireTake za) (wireTake zb) else 0 := by
  exact permUpdateGate_embed t ht (fun y : Reg q => y ⟨t, ht⟩ ^^ y ⟨c, hc⟩) za zb

theorem readAddress_take {q n : ℕ} (addresses : List ℕ) (haddrq : ∀ a ∈ addresses, a < q)
    (x : Reg (q + n)) (haddrn : ∀ a ∈ addresses, a < q + n) :
    readAddress (wireTake x) addresses haddrq = readAddress x addresses haddrn := rfl

theorem xorQueryMatrix_embed (A : ClassicalOracle) {q n : ℕ} (addresses : List ℕ) (target : ℕ)
    (hlegq : target < q ∧ (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup)
    (za zb : Reg (q + n)) :
    xorQueryMatrix A (q + n) addresses target za zb
      = if wireDrop za = wireDrop zb
        then xorQueryMatrix A q addresses target (wireTake za) (wireTake zb) else 0 := by
  classical
  have hlegn : target < q + n ∧ (∀ a ∈ addresses, a < q + n) ∧ target ∉ addresses
      ∧ addresses.Nodup :=
    ⟨by omega, fun a ha => by have := hlegq.2.1 a ha; omega, hlegq.2.2.1, hlegq.2.2.2⟩
  have hfun : (xorQueryUpdate A addresses target hlegn.1 hlegn.2.1)
      = (fun x : Reg (q + n) => Function.update x ⟨target, hlegn.1⟩
          ((fun y : Reg q => y ⟨target, hlegq.1⟩ ^^ A addresses.length
            (readAddress y addresses hlegq.2.1)) (wireTake x))) := by
    funext x
    show Function.update x ⟨target, hlegn.1⟩
        (x ⟨target, hlegn.1⟩ ^^ A addresses.length (readAddress x addresses hlegn.2.1))
      = Function.update x ⟨target, hlegn.1⟩
          ((fun y : Reg q => y ⟨target, hlegq.1⟩ ^^ A addresses.length
            (readAddress y addresses hlegq.2.1)) (wireTake x))
    rw [← readAddress_take addresses hlegq.2.1 x hlegn.2.1]
    rfl
  simp only [xorQueryMatrix, dif_pos hlegn, dif_pos hlegq]
  rw [hfun, permUpdateGate_embed target hlegq.1
    (fun y : Reg q => y ⟨target, hlegq.1⟩ ^^ A addresses.length
      (readAddress y addresses hlegq.2.1)) za zb]
  rfl

theorem finiteCodeLegal_mono {q n : ℕ} (gate : FiniteGateCode)
    (h : finiteCodeLegal q gate = true) : finiteCodeLegal (q + n) gate = true := by
  cases gate with
  | h w | x w | t w | tdg w =>
      simp only [finiteCodeLegal] at h ⊢
      have hw : w < q := by simpa using h
      exact decide_eq_true (by omega)
  | cx c t =>
      simp only [finiteCodeLegal] at h ⊢
      have hct : c < q ∧ t < q ∧ c ≠ t := by simpa using h
      exact decide_eq_true (by omega)

theorem instructionLegal_mono {q n : ℕ} (instr : WitnessInstruction)
    (h : instructionLegal q instr) : instructionLegal (q + n) instr := by
  match instr with
  | .fixed gate => exact finiteCodeLegal_mono gate h
  | .oracle addresses target =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact ⟨by omega, fun a ha => by have := h2 a ha; omega, h3, h4⟩

theorem instructionMatrix_embed (A : ClassicalOracle) {q n : ℕ} (instr : WitnessInstruction)
    (hlegal : instructionLegal q instr) (za zb : Reg (q + n)) :
    instructionMatrix A (q + n) instr za zb
      = if wireDrop za = wireDrop zb
        then instructionMatrix A q instr (wireTake za) (wireTake zb) else 0 := by
  classical
  match instr with
  | .fixed gate =>
      match gate with
      | .h w =>
          have hw : w < q := by simpa [instructionLegal, finiteCodeLegal] using hlegal
          simp only [instructionMatrix, finiteCodeMatrix, dif_pos hw,
            dif_pos (show w < q + n by omega)]
          exact wireGate_embed w hw Hadamard za zb
      | .x w =>
          have hw : w < q := by simpa [instructionLegal, finiteCodeLegal] using hlegal
          simp only [instructionMatrix, finiteCodeMatrix, dif_pos hw,
            dif_pos (show w < q + n by omega)]
          exact wireGate_embed w hw PauliX za zb
      | .t w =>
          have hw : w < q := by simpa [instructionLegal, finiteCodeLegal] using hlegal
          simp only [instructionMatrix, finiteCodeMatrix, dif_pos hw,
            dif_pos (show w < q + n by omega)]
          exact wireGate_embed w hw tGate za zb
      | .tdg w =>
          have hw : w < q := by simpa [instructionLegal, finiteCodeLegal] using hlegal
          simp only [instructionMatrix, finiteCodeMatrix, dif_pos hw,
            dif_pos (show w < q + n by omega)]
          exact wireGate_embed w hw tGateAdj za zb
      | .cx c t =>
          have hct : c < q ∧ t < q ∧ c ≠ t := by
            simpa [instructionLegal, finiteCodeLegal] using hlegal
          simp only [instructionMatrix, finiteCodeMatrix, dif_pos hct,
            dif_pos (show c < q + n ∧ t < q + n ∧ c ≠ t by omega)]
          exact cnotGate_embed c t hct.1 hct.2.1 za zb
  | .oracle addresses target =>
      obtain ⟨h1, h2, h3, h4⟩ := hlegal
      exact xorQueryMatrix_embed A addresses target ⟨h1, h2, h3, h4⟩ za zb

theorem instrMatrixProd_embed (A : ClassicalOracle) {q n : ℕ} (l : List WitnessInstruction)
    (hlegal : ∀ i ∈ l, instructionLegal q i) (za zb : Reg (q + n)) :
    ((l.map (instructionMatrix A (q + n))).reverse.prod) za zb
      = if wireDrop za = wireDrop zb
        then ((l.map (instructionMatrix A q)).reverse.prod) (wireTake za) (wireTake zb) else 0 := by
  classical
  induction l generalizing za zb with
  | nil =>
      simp only [List.map_nil, List.reverse_nil, List.prod_nil, Matrix.one_apply]
      by_cases hdrop : wireDrop za = wireDrop zb
      · rw [if_pos hdrop]
        by_cases htake : wireTake za = wireTake zb
        · rw [if_pos htake]
          rw [if_pos (by
            rw [← wireTake_drop za, ← wireTake_drop zb, htake, hdrop])]
        · rw [if_neg htake, if_neg (fun hz => htake (congrArg wireTake hz))]
      · rw [if_neg hdrop, if_neg (fun hz => hdrop (congrArg wireDrop hz))]
  | cons g l ih =>
      have hgl : instructionLegal q g := hlegal g (by simp)
      have hll : ∀ i ∈ l, instructionLegal q i := fun i hi =>
        hlegal i (by simp [hi])
      simp only [List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_singleton, Matrix.mul_apply]
      by_cases hdrop : wireDrop za = wireDrop zb
      · rw [if_pos hdrop]
        have hsummand : ∀ k : Reg (q + n),
            ((l.map (instructionMatrix A (q + n))).reverse.prod) za k
              * instructionMatrix A (q + n) g k zb
              = if wireDrop k = wireDrop za
                then ((l.map (instructionMatrix A q)).reverse.prod) (wireTake za) (wireTake k)
                  * instructionMatrix A q g (wireTake k) (wireTake zb)
                else 0 := by
          intro k
          rw [ih hll za k, instructionMatrix_embed A g hgl k zb]
          by_cases hk : wireDrop za = wireDrop k
          · rw [if_pos hk, if_pos (show wireDrop k = wireDrop zb from hk.symm.trans hdrop),
              if_pos hk.symm]
          · rw [if_neg hk, if_neg (fun h : wireDrop k = wireDrop za => hk h.symm),
              if_neg (fun h : wireDrop k = wireDrop zb => hk (hdrop.trans h.symm)), zero_mul]
        rw [Finset.sum_congr rfl (fun k _ => hsummand k)]
        rw [sum_wireGlue (fun k : Reg (q + n) =>
          (if wireDrop k = wireDrop za
            then ((l.map (instructionMatrix A q)).reverse.prod) (wireTake za) (wireTake k)
              * instructionMatrix A q g (wireTake k) (wireTake zb) else 0))]
        simp only [wireGlue_take, wireGlue_drop]
        have hinner : ∀ ub : Reg q,
            (∑ db : Reg n,
              (if db = wireDrop za
                then ((l.map (instructionMatrix A q)).reverse.prod) (wireTake za) ub
                  * instructionMatrix A q g ub (wireTake zb) else 0))
              = ((l.map (instructionMatrix A q)).reverse.prod) (wireTake za) ub
                * instructionMatrix A q g ub (wireTake zb) := by
          intro ub
          rw [Finset.sum_eq_single (wireDrop za)]
          · rw [if_pos rfl]
          · intro b _ hb
            rw [if_neg hb]
          · intro hcon
            exact absurd (Finset.mem_univ (wireDrop za)) hcon
        rw [Finset.sum_congr rfl (fun ub _ => hinner ub), ← Matrix.mul_apply]
      · rw [if_neg hdrop]
        apply Finset.sum_eq_zero
        intro k _
        rw [ih hll za k]
        by_cases hk : wireDrop za = wireDrop k
        · rw [if_pos hk, instructionMatrix_embed A g hgl k zb,
            if_neg (fun h => hdrop (hk.trans h)), mul_zero]
        · rw [if_neg hk, zero_mul]

theorem permMatrix_id_eq_one {I : Type*} [Fintype I] [DecidableEq I] :
    permMatrix (id : I → I) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [permMatrix, h, Matrix.one_apply]

theorem permMatrix_comp {I : Type*} [Fintype I] [DecidableEq I] (f g : I → I) :
    permMatrix f * permMatrix g = permMatrix (f ∘ g) := by
  ext i j
  classical
  have hterm : ∀ k : I,
      (if i = f k then (1 : ℂ) else 0) * (if k = g j then (1 : ℂ) else 0)
        = if k = g j then (if i = f (g j) then (1 : ℂ) else 0) else 0 := by
    intro k
    by_cases hk : k = g j
    · subst hk
      by_cases h : i = f (g j) <;> simp [h]
    · rw [if_neg hk, mul_zero, if_neg hk]
  simp only [Matrix.mul_apply, permMatrix, Matrix.of_apply]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_ite_eq']
  simp

theorem permMatrix_conj_apply {I : Type*} [Fintype I] [DecidableEq I] (P : I → I)
    (hP : Function.Involutive P) (ρ : Matrix I I ℂ) (k l : I) :
    (permMatrix P * ρ * (permMatrix P)ᴴ) k l = ρ (P k) (P l) := by
  classical
  have h1 : ∀ l : I, (permMatrix P * ρ) k l = ρ (P k) l := by
    intro l
    simp only [Matrix.mul_apply, permMatrix, Matrix.of_apply]
    rw [Finset.sum_eq_single (P k)
        (fun m _ hm => by
          have hne : ¬ (k = P m) := by
            intro h
            have hPP : P k = m := by rw [congrArg P h]; exact hP m
            exact hm hPP.symm
          rw [if_neg hne]
          simp)
        (fun hcon => absurd (Finset.mem_univ (P k)) hcon),
      if_pos ((hP k).symm : k = P (P k))]
    simp
  rw [Matrix.mul_apply]
  simp only [h1]
  simp only [Matrix.conjTranspose_apply, permMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (P l)
      (fun m _ hm => by
        have hne : ¬ (l = P m) := by
          intro h
          have hPP : P l = m := by rw [congrArg P h]; exact hP m
          exact hm hPP.symm
        rw [if_neg hne]
        simp)
      (fun hcon => absurd (Finset.mem_univ (P l)) hcon),
    if_pos ((hP l).symm : l = P (P l))]
  simp

def copyInstruction (p : WitnessVerifierProgram) (i : Fin p.witnessBits) :
    WitnessInstruction :=
  WitnessInstruction.fixed (FiniteGateCode.cx (witnessWire p i).val (programQubits p + i.val))

def copyInstrs (p : WitnessVerifierProgram) :
    (m : ℕ) → m ≤ p.witnessBits → List WitnessInstruction
  | 0, _ => []
  | m + 1, hm => copyInstruction p ⟨m, hm⟩ :: copyInstrs p m (Nat.le_of_lt hm)

def copyInstructions (p : WitnessVerifierProgram) : List WitnessInstruction :=
  copyInstrs p p.witnessBits (Nat.le_refl p.witnessBits)

def dephaseProgram (p : WitnessVerifierProgram) : WitnessVerifierProgram where
  witnessBits := p.witnessBits
  inputBits := p.inputBits
  ancillaBits := p.ancillaBits + p.witnessBits
  outputWire := p.outputWire
  instructions := copyInstructions p ++ p.instructions

theorem dephase_qubits (p : WitnessVerifierProgram) :
    programQubits (dephaseProgram p) = programQubits p + p.witnessBits := by
  simp only [programQubits, dephaseProgram]
  omega

theorem dephaseProgram_instructions (p : WitnessVerifierProgram) :
    (dephaseProgram p).instructions = copyInstructions p ++ p.instructions := rfl

def copySingleUpdate (p : WitnessVerifierProgram) (i : Fin p.witnessBits) :
    Reg (programQubits (dephaseProgram p)) → Reg (programQubits (dephaseProgram p)) :=
  fun z => Function.update z
    (Fin.cast (dephase_qubits p).symm (Fin.natAdd (programQubits p) i))
    (z (Fin.cast (dephase_qubits p).symm (Fin.natAdd (programQubits p) i))
      ^^ z (Fin.cast (dephase_qubits p).symm
        (Fin.castAdd p.witnessBits (witnessWire p i))))

theorem instructionMatrix_copyInstruction (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (i : Fin p.witnessBits) :
    instructionMatrix A (programQubits (dephaseProgram p)) (copyInstruction p i)
      = permMatrix (copySingleUpdate p i) := by
  have hq := dephase_qubits p
  have hc : (witnessWire p i).val < programQubits (dephaseProgram p) := by
    have := (witnessWire p i).isLt
    omega
  have ht : programQubits p + i.val < programQubits (dephaseProgram p) := by
    have := i.isLt
    omega
  have hne : (witnessWire p i).val ≠ programQubits p + i.val := by
    have := (witnessWire p i).isLt
    omega
  simp only [instructionMatrix, finiteCodeMatrix, copyInstruction]
  rw [dif_pos ⟨hc, ht, hne⟩]
  simp only [cnotGate]
  rfl

def copyComp (p : WitnessVerifierProgram) :
    (m : ℕ) → m ≤ p.witnessBits →
    Reg (programQubits (dephaseProgram p)) → Reg (programQubits (dephaseProgram p))
  | 0, _ => id
  | m + 1, hm => copyComp p m (Nat.le_of_lt hm) ∘ copySingleUpdate p ⟨m, hm⟩

theorem copyInstrs_permMatrix (A : ClassicalOracle) (p : WitnessVerifierProgram) :
    ∀ (m : ℕ) (hm : m ≤ p.witnessBits),
    ((copyInstrs p m hm).map (instructionMatrix A (programQubits (dephaseProgram p)))).reverse.prod
      = permMatrix (copyComp p m hm) := by
  intro m
  induction m with
  | zero => intro hm; simp [copyInstrs, copyComp, permMatrix_id_eq_one]
  | succ m ih =>
    intro hm
    simp only [copyInstrs, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton]
    rw [ih (Nat.le_of_lt hm), instructionMatrix_copyInstruction, permMatrix_comp]
    rfl

def copySrcWire (p : WitnessVerifierProgram) (j : Fin p.witnessBits) :
    Fin (programQubits (dephaseProgram p)) :=
  ⟨(j : ℕ), by
    have hq := dephase_qubits p
    have hj := j.isLt
    have hw : p.witnessBits ≤ programQubits p := by simp only [programQubits]; omega
    omega⟩

theorem copySrcWire_val (p : WitnessVerifierProgram) (j : Fin p.witnessBits) :
    (copySrcWire p j : ℕ) = (j : ℕ) := rfl

def copySrcOf (p : WitnessVerifierProgram) (t : Fin (programQubits (dephaseProgram p))) :
    Fin (programQubits (dephaseProgram p)) :=
  if h : (t : ℕ) < programQubits p then t
  else copySrcWire p ⟨(t : ℕ) - programQubits p, by
    have hq := dephase_qubits p
    have ht := t.isLt
    omega⟩

theorem copySrcOf_of_lt (p : WitnessVerifierProgram)
    {t : Fin (programQubits (dephaseProgram p))} (ht : (t : ℕ) < programQubits p) :
    copySrcOf p t = t := by
  show (if h : (t : ℕ) < programQubits p then t
      else copySrcWire p ⟨(t : ℕ) - programQubits p, by
        have hq := dephase_qubits p
        have ht := t.isLt
        omega⟩) = t
  rw [dif_pos ht]

theorem copySrcOf_val (p : WitnessVerifierProgram)
    {t : Fin (programQubits (dephaseProgram p))} (ht : ¬((t : ℕ) < programQubits p)) :
    (copySrcOf p t : ℕ) = (t : ℕ) - programQubits p := by
  simp only [copySrcOf, dif_neg ht]
  rfl

theorem copySrcOf_lt (p : WitnessVerifierProgram)
    {t : Fin (programQubits (dephaseProgram p))} (ht : ¬((t : ℕ) < programQubits p)) :
    (copySrcOf p t : ℕ) < programQubits p := by
  have hq := dephase_qubits p
  have hw : p.witnessBits ≤ programQubits p := by
    simp only [programQubits]
    omega
  have ht2 := t.isLt
  rw [copySrcOf_val p ht]
  omega

def copyUpdate (p : WitnessVerifierProgram) (z : Reg (programQubits (dephaseProgram p))) :
    Reg (programQubits (dephaseProgram p)) :=
  fun k => if (k : ℕ) < programQubits p then z k
    else z (copySrcOf p k) ^^ z k

def partialCopy (p : WitnessVerifierProgram) (m : ℕ) (_hm : m ≤ p.witnessBits)
    (z : Reg (programQubits (dephaseProgram p))) :
    Reg (programQubits (dephaseProgram p)) :=
  fun k => if _hk : (k : ℕ) < programQubits p then z k
    else if _hj : (k : ℕ) - programQubits p < m then
      z (copySrcOf p k) ^^ z k
    else z k

theorem copyComp_eq_partialCopy (p : WitnessVerifierProgram) :
    ∀ (m : ℕ) (hm : m ≤ p.witnessBits) (z : Reg (programQubits (dephaseProgram p))),
    copyComp p m hm z = partialCopy p m hm z := by
  intro m
  induction m with
  | zero =>
    intro hm z
    funext k
    by_cases hk : (k : ℕ) < programQubits p
    · simp only [copyComp, partialCopy, dif_pos hk, id_eq]
    · have hj : ¬((k : ℕ) - programQubits p < 0) := by omega
      simp only [copyComp, partialCopy, dif_neg hk, dif_neg hj, id_eq]
  | succ m ih =>
    intro hm z
    have hm' : m ≤ p.witnessBits := Nat.le_of_lt hm
    have hq := dephase_qubits p
    have hw : p.witnessBits ≤ programQubits p := by
      simp only [programQubits]
      omega
    have hTv : (Fin.cast (dephase_qubits p).symm
        (Fin.natAdd (programQubits p) ⟨m, hm⟩) : ℕ) = programQubits p + m := by simp
    have hWv : (Fin.cast (dephase_qubits p).symm
        (Fin.castAdd p.witnessBits (witnessWire p ⟨m, hm⟩)) : ℕ) = m := by
      simp only [witnessWire]
      simp
    have hval : ∀ kk : Fin (programQubits (dephaseProgram p)),
        kk = Fin.cast (dephase_qubits p).symm (Fin.natAdd (programQubits p) ⟨m, hm⟩)
          ↔ (kk : ℕ) = programQubits p + m := by
      intro kk
      constructor
      · intro h
        have h2 := congrArg Fin.val h
        rw [hTv] at h2
        exact h2
      · intro h
        apply Fin.ext
        rw [hTv]
        omega
    have hidx : ∀ (zz : Reg (programQubits (dephaseProgram p)))
        (k : Fin (programQubits (dephaseProgram p))),
        copySingleUpdate p ⟨m, hm⟩ zz k
          = if k = Fin.cast (dephase_qubits p).symm (Fin.natAdd (programQubits p) ⟨m, hm⟩)
            then zz (Fin.cast (dephase_qubits p).symm (Fin.natAdd (programQubits p) ⟨m, hm⟩))
              ^^ zz (Fin.cast (dephase_qubits p).symm
                (Fin.castAdd p.witnessBits (witnessWire p ⟨m, hm⟩)))
            else zz k := by
      intro zz k
      simp only [copySingleUpdate, Function.update_apply]
    funext k
    simp only [copyComp, Function.comp_apply, ih hm' (copySingleUpdate p ⟨m, hm⟩ z),
      partialCopy, hidx z]
    have hkTval : ∀ kk : Fin (programQubits (dephaseProgram p)),
        ¬((kk : ℕ) = programQubits p + m)
          → kk ≠ Fin.cast (dephase_qubits p).symm (Fin.natAdd (programQubits p) ⟨m, hm⟩) := by
      intro kk hne h
      exact hne ((hval kk).1 h)
    by_cases hkq : (k : ℕ) < programQubits p
    · simp only [dif_pos hkq, if_neg (hkTval k (by omega))]
    · simp only [dif_neg hkq]
      have hsrcval : (copySrcOf p k : ℕ) = (k : ℕ) - programQubits p :=
        copySrcOf_val p hkq
      by_cases hjm : (k : ℕ) - programQubits p < m
      · have hjT : ¬(copySrcOf p k
            = Fin.cast (dephase_qubits p).symm (Fin.natAdd (programQubits p) ⟨m, hm⟩)) := by
          intro h
          have h2 := congrArg Fin.val h
          rw [hTv] at h2
          rw [hsrcval] at h2
          omega
        simp only [dif_pos hjm, if_neg hjT, if_neg (hkTval k (by omega)),
          dif_pos (by omega : (k : ℕ) - programQubits p < m + 1)]
      · by_cases hke : (k : ℕ) - programQubits p = m
        · have hkTe : k = Fin.cast (dephase_qubits p).symm
              (Fin.natAdd (programQubits p) ⟨m, hm⟩) := (hval k).mpr (by omega)
          have hdropeqv : copySrcOf p k
              = Fin.cast (dephase_qubits p).symm
                (Fin.castAdd p.witnessBits (witnessWire p ⟨m, hm⟩)) := by
            apply Fin.ext
            show (copySrcOf p k : ℕ)
              = (Fin.cast (dephase_qubits p).symm
                  (Fin.castAdd p.witnessBits (witnessWire p ⟨m, hm⟩)) : ℕ)
            rw [hsrcval, hWv]
            omega
          simp only [dif_neg (show ¬((k : ℕ) - programQubits p < m) by omega),
            if_pos hkTe, dif_pos (show (k : ℕ) - programQubits p < m + 1 by omega)]
          rw [hdropeqv, hkTe, Bool.xor_comm]
        · simp only [dif_neg (show ¬((k : ℕ) - programQubits p < m) by omega),
            if_neg (hkTval k (by omega)),
            dif_neg (by omega : ¬((k : ℕ) - programQubits p < m + 1))]

theorem partialCopy_full (p : WitnessVerifierProgram)
    (z : Reg (programQubits (dephaseProgram p))) :
    partialCopy p p.witnessBits (Nat.le_refl p.witnessBits) z = copyUpdate p z := by
  funext k
  by_cases hk : (k : ℕ) < programQubits p
  · simp only [partialCopy, copyUpdate, dif_pos hk, if_pos hk]
  · have hq := dephase_qubits p
    have hk2 := k.isLt
    have hjlt : (k : ℕ) - programQubits p < p.witnessBits := by omega
    simp only [partialCopy, copyUpdate, dif_neg hk, if_neg hk, dif_pos hjlt]

theorem copyComp_eq_partialCopy' (p : WitnessVerifierProgram) (m : ℕ) (hm : m ≤ p.witnessBits) :
    copyComp p m hm = partialCopy p m hm := by
  funext z
  exact copyComp_eq_partialCopy p m hm z

theorem partialCopy_full' (p : WitnessVerifierProgram) :
    partialCopy p p.witnessBits (Nat.le_refl p.witnessBits) = copyUpdate p := by
  funext z
  exact partialCopy_full p z

theorem copyMatrix_eq (A : ClassicalOracle) (p : WitnessVerifierProgram) :
    ((copyInstructions p).map (instructionMatrix A (programQubits (dephaseProgram p)))).reverse.prod
      = permMatrix (copyUpdate p) := by
  rw [copyInstructions, copyInstrs_permMatrix A p p.witnessBits (Nat.le_refl p.witnessBits),
    copyComp_eq_partialCopy' p p.witnessBits (Nat.le_refl p.witnessBits), partialCopy_full' p]

theorem copyUpdate_front (p : WitnessVerifierProgram)
    (z : Reg (programQubits (dephaseProgram p))) {t : Fin (programQubits (dephaseProgram p))}
    (ht : (t : ℕ) < programQubits p) : copyUpdate p z t = z t := by
  show (if (t : ℕ) < programQubits p then z t
      else (z (copySrcOf p t) ^^ z t)) = z t
  split
  · rfl
  · next h => exact absurd ht h

theorem copyUpdate_back (p : WitnessVerifierProgram)
    (z : Reg (programQubits (dephaseProgram p))) {t : Fin (programQubits (dephaseProgram p))}
    (ht : ¬((t : ℕ) < programQubits p)) :
    copyUpdate p z t = (z (copySrcOf p t) ^^ z t) := by
  show (if (t : ℕ) < programQubits p then z t
      else (z (copySrcOf p t) ^^ z t)) = (z (copySrcOf p t) ^^ z t)
  split
  · next h => exact absurd h ht
  · rfl

theorem copyUpdate_involutive (p : WitnessVerifierProgram) :
    Function.Involutive (copyUpdate p) := by
  intro z
  funext k
  by_cases hk : (k : ℕ) < programQubits p
  · rw [copyUpdate_front p (copyUpdate p z) hk, copyUpdate_front p z hk]
  · rw [copyUpdate_back p (copyUpdate p z) hk]
    rw [copyUpdate_front p z (copySrcOf_lt p hk)]
    rw [copyUpdate_back p z hk]
    rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

theorem sum_wireGlue_gen {q n : ℕ} {M : Type*} [AddCommMonoid M] (f : Reg (q + n) → M) :
    ∑ z : Reg (q + n), f z = ∑ y : Reg q, ∑ c : Reg n, f (wireGlue y c) := by
  classical
  rw [Fintype.sum_equiv (regGlueEquiv q n).symm f
    (fun p : Reg q × Reg n => f (wireGlue p.1 p.2))
    (fun z => by
      show f z = f (wireGlue (wireTake z) (wireDrop z))
      rw [wireTake_drop])]
  rw [Fintype.sum_prod_type]

def toDephase (p : WitnessVerifierProgram) (z : Reg (programQubits p + p.witnessBits)) :
    Reg (programQubits (dephaseProgram p)) :=
  fun k => z (Fin.cast (dephase_qubits p) k)

def ofDephase (p : WitnessVerifierProgram) (z : Reg (programQubits (dephaseProgram p))) :
    Reg (programQubits p + p.witnessBits) :=
  fun k => z (Fin.cast (dephase_qubits p).symm k)

theorem toDephase_ofDephase (p : WitnessVerifierProgram)
    (z : Reg (programQubits (dephaseProgram p))) :
    toDephase p (ofDephase p z) = z := by
  funext k
  simp only [toDephase, ofDephase]
  exact congrArg z (Fin.ext rfl)

theorem ofDephase_toDephase (p : WitnessVerifierProgram)
    (z : Reg (programQubits p + p.witnessBits)) :
    ofDephase p (toDephase p z) = z := by
  funext k
  simp only [toDephase, ofDephase]
  exact congrArg z (Fin.ext rfl)

def dephaseRegEquiv (p : WitnessVerifierProgram) :
    Reg (programQubits (dephaseProgram p)) ≃ Reg (programQubits p + p.witnessBits) :=
  ⟨ofDephase p, toDephase p, toDephase_ofDephase p, ofDephase_toDephase p⟩

theorem cast_eq_castAdd {q q' w : ℕ} (h : q' = q + w) {k : Fin q'} (hk : (k : ℕ) < q) :
    Fin.cast h k = Fin.castAdd w ⟨(k : ℕ), hk⟩ := Fin.ext rfl

theorem cast_eq_natAdd {q q' w : ℕ} (h : q' = q + w) {k : Fin q'} (hk : ¬((k : ℕ) < q)) :
    Fin.cast h k = Fin.natAdd q ⟨(k : ℕ) - q, by omega⟩ := by
  apply Fin.ext
  show (k : ℕ) = (Fin.natAdd q ⟨(k : ℕ) - q, by omega⟩ : ℕ)
  rw [Fin.val_natAdd]
  show (k : ℕ) = q + ((k : ℕ) - q)
  omega

theorem instructionMatrix_width (A : ClassicalOracle) {q q' : ℕ} (h : q' = q)
    (instr : WitnessInstruction) (za zb : Reg q) :
    instructionMatrix A q' instr (fun k => za (Fin.cast h k)) (fun k => zb (Fin.cast h k))
      = instructionMatrix A q instr za zb := by
  subst h
  rfl

theorem instrMatrixProd_width (A : ClassicalOracle) {q q' : ℕ} (h : q' = q)
    (l : List WitnessInstruction) (za zb : Reg q) :
    ((l.map (instructionMatrix A q')).reverse.prod)
      (fun k => za (Fin.cast h k)) (fun k => zb (Fin.cast h k))
      = ((l.map (instructionMatrix A q)).reverse.prod) za zb := by
  subst h
  rfl

theorem programMatrix_dephase_split (A : ClassicalOracle) (p : WitnessVerifierProgram) :
    programMatrix A (dephaseProgram p)
      = ((p.instructions.map (instructionMatrix A (programQubits (dephaseProgram p)))).reverse.prod
          * permMatrix (copyUpdate p)) := by
  simp only [programMatrix, dephaseProgram_instructions]
  rw [List.map_append, List.reverse_append, List.prod_append, copyMatrix_eq]

theorem dephaseOrigProd_entry (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (hlegal : witnessProgramLegal p) (y y' : Reg (programQubits p))
    (c c' : Reg p.witnessBits) :
    ((p.instructions.map (instructionMatrix A (programQubits (dephaseProgram p)))).reverse.prod)
      (toDephase p (wireGlue y c)) (toDephase p (wireGlue y' c'))
      = if c = c' then programMatrix A p y y' else 0 := by
  show ((p.instructions.map (instructionMatrix A (programQubits (dephaseProgram p)))).reverse.prod)
      (fun k : Fin (programQubits (dephaseProgram p)) =>
        (wireGlue y c) (Fin.cast (dephase_qubits p) k))
      (fun k : Fin (programQubits (dephaseProgram p)) =>
        (wireGlue y' c') (Fin.cast (dephase_qubits p) k))
      = if c = c' then programMatrix A p y y' else 0
  rw [instrMatrixProd_width A (dephase_qubits p) p.instructions (wireGlue y c)
      (wireGlue y' c'),
    instrMatrixProd_embed A p.instructions hlegal.2 (wireGlue y c) (wireGlue y' c')]
  simp only [wireGlue_drop, wireGlue_take, programMatrix]

theorem copyUpdate_toDephase (p : WitnessVerifierProgram) (a : Reg (programQubits p))
    (b : Reg p.witnessBits) :
    copyUpdate p (toDephase p (wireGlue a b))
      = toDephase p (wireGlue a (fun j => a (witnessWire p j) ^^ b j)) := by
  have hw : p.witnessBits ≤ programQubits p := by
    simp only [programQubits]
    omega
  have hq := dephase_qubits p
  have hwit : ∀ j : Fin p.witnessBits,
      witnessWire p j = ⟨(j : ℕ), by have := hw; have := j.isLt; omega⟩ :=
    fun j => Fin.ext rfl
  funext k
  by_cases hk : (k : ℕ) < programQubits p
  · rw [copyUpdate_front p (toDephase p (wireGlue a b)) hk]
    show (wireGlue a b) (Fin.cast (dephase_qubits p) k)
        = (wireGlue a (fun j => a (witnessWire p j) ^^ b j)) (Fin.cast (dephase_qubits p) k)
    rw [cast_eq_castAdd (dephase_qubits p) hk]
    simp only [wireGlue, Fin.append_left]
  · have hkq : (k : ℕ) - programQubits p < p.witnessBits := by
      have := k.isLt
      omega
    rw [copyUpdate_back p (toDephase p (wireGlue a b)) hk]
    have hcastk : Fin.cast (dephase_qubits p) k
        = Fin.natAdd (programQubits p) ⟨(k : ℕ) - programQubits p, hkq⟩ :=
      cast_eq_natAdd (dephase_qubits p) hk
    have hcastsrc : Fin.cast (dephase_qubits p) (copySrcOf p k)
        = Fin.castAdd p.witnessBits ⟨(k : ℕ) - programQubits p,
          by have h1 := copySrcOf_val p hk; have h2 := copySrcOf_lt p hk; omega⟩ := by
      apply Fin.ext
      show (copySrcOf p k : ℕ) = (k : ℕ) - programQubits p
      exact copySrcOf_val p hk
    show ((wireGlue a b) (Fin.cast (dephase_qubits p) (copySrcOf p k))
        ^^ (wireGlue a b) (Fin.cast (dephase_qubits p) k))
      = (wireGlue a (fun j => a (witnessWire p j) ^^ b j)) (Fin.cast (dephase_qubits p) k)
    rw [hcastsrc, hcastk]
    simp only [wireGlue, Fin.append_left, Fin.append_right]
    rw [hwit ⟨(k : ℕ) - programQubits p, hkq⟩]

end Qatlib.Concepts.LocalMachine.LocalTransport
