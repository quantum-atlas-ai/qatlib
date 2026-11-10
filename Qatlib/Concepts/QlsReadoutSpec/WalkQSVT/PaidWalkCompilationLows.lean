/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.PaidWalkCompilationStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators

private theorem controlled_apply {H : Type} [DecidableEq H] {r : ℕ}
    (U : Matrix H H ℂ) (T : Finset (Fin r)) (p t : Space H r) :
    controlled U T p t = if p.2 = t.2 then
      if p.2 ∈ T then U p.1 t.1 else if p.1 = t.1 then 1 else 0 else 0 := rfl

private theorem controlled_mul {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (A B : Matrix H H ℂ) (T : Finset (Fin r)) :
    controlled A T * controlled B T = controlled (A * B) T := by
  ext p t
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Space H r,
      controlled A T p k * controlled B T k t
        = if p.2 = k.2 ∧ k.2 = t.2 then
            (if p.2 ∈ T then A p.1 k.1 * B k.1 t.1
             else if p.1 = k.1 ∧ k.1 = t.1 then (1 : ℂ) else 0)
          else 0 := by
    intro k
    by_cases h1 : p.2 = k.2
    · by_cases h2 : k.2 = t.2
      · rw [if_pos (And.intro h1 h2)]
        rw [controlled_apply, controlled_apply, if_pos h1, if_pos h2]
        by_cases hT : p.2 ∈ T
        · have hTk : k.2 ∈ T := h1 ▸ hT
          rw [if_pos hT, if_pos hTk, if_pos hT]
        · have hTk : k.2 ∉ T := fun hkT => hT (h1 ▸ hkT)
          rw [if_neg hT, if_neg hTk, if_neg hT]
          by_cases ha : p.1 = k.1 <;> by_cases hb : k.1 = t.1 <;> simp [ha, hb]
      · rw [if_neg (fun h => h2 h.2)]
        rw [controlled_apply, controlled_apply, if_pos h1, if_neg h2, mul_zero]
    · rw [if_neg (fun h => h1 h.1)]
      rw [controlled_apply, controlled_apply, if_neg h1, zero_mul]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  by_cases hk : p.2 = t.2
  · have hR : controlled (A * B) T p t
        = if p.2 ∈ T then (A * B) p.1 t.1 else if p.1 = t.1 then (1 : ℂ) else 0 := by
      rw [controlled_apply, if_pos hk]
    have hc : ∀ k : Space H r, (p.2 = k.2 ∧ k.2 = t.2) ↔ k.2 = p.2 := by
      intro k
      constructor
      · rintro ⟨_, hkt⟩
        exact hkt.trans hk.symm
      · intro hk2
        exact ⟨hk2.symm, hk2.trans hk⟩
    by_cases hT : p.2 ∈ T
    · rw [hR, if_pos hT, Matrix.mul_apply]
      simp only [hc, if_pos hT]
      rw [show (∑ x : Space H r, if x.2 = p.2 then A p.1 x.1 * B x.1 t.1 else 0)
          = (∑ x : H, ∑ y : Fin r, if y = p.2 then A p.1 x * B x t.1 else 0) from
        Fintype.sum_prod_type' (fun x y => if y = p.2 then A p.1 x * B x t.1 else 0)]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_ite_eq_of_mem' (Finset.univ) p.2 (fun _ => A p.1 x * B x t.1)
        (Finset.mem_univ _)]
    · rw [hR, if_neg hT]
      simp only [hc, if_neg hT]
      by_cases hp : p.1 = t.1
      · rw [if_pos hp]
        have hite : ∀ x : H,
            (if p.1 = x ∧ x = t.1 then (1 : ℂ) else 0) = if x = t.1 then 1 else 0 := by
          intro x
          by_cases hx : x = t.1
          · rw [if_pos hx, if_pos ⟨hp.trans hx.symm, hx⟩]
          · rw [if_neg hx, if_neg (fun h => hx h.2)]
        rw [show (∑ x : Space H r, if x.2 = p.2 then
              (if p.1 = x.1 ∧ x.1 = t.1 then (1 : ℂ) else 0) else 0)
            = (∑ x : H, ∑ y : Fin r, if y = p.2 then
              (if p.1 = x ∧ x = t.1 then (1 : ℂ) else 0) else 0) from
          Fintype.sum_prod_type' (fun x y =>
            if y = p.2 then (if p.1 = x ∧ x = t.1 then (1 : ℂ) else 0) else 0)]
        rw [show (∑ x : H, ∑ y : Fin r, if y = p.2 then
              (if p.1 = x ∧ x = t.1 then (1 : ℂ) else 0) else 0)
            = ∑ x : H, (if p.1 = x ∧ x = t.1 then (1 : ℂ) else 0) by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.sum_ite_eq_of_mem' (Finset.univ) p.2
            (fun _ => if p.1 = x ∧ x = t.1 then (1 : ℂ) else 0) (Finset.mem_univ _)]]
        rw [show (∑ x : H, (if p.1 = x ∧ x = t.1 then (1 : ℂ) else 0))
            = ∑ x : H, (if x = t.1 then 1 else 0) from
          Finset.sum_congr rfl (fun x _ => hite x)]
        rw [Finset.sum_ite_eq_of_mem' (Finset.univ) t.1 (fun _ => (1 : ℂ))
          (Finset.mem_univ _)]
      · rw [if_neg hp]
        rw [show (∑ x : Space H r, if x.2 = p.2 then
              (if p.1 = x.1 ∧ x.1 = t.1 then (1 : ℂ) else 0) else 0) = 0 by
          rw [Fintype.sum_prod_type' (fun x y =>
            if y = p.2 then (if p.1 = x ∧ x = t.1 then (1 : ℂ) else 0) else 0)]
          refine Finset.sum_eq_zero (fun x _ => ?_)
          rw [Finset.sum_ite_eq_of_mem' (Finset.univ) p.2
            (fun _ => if p.1 = x ∧ x = t.1 then (1 : ℂ) else 0) (Finset.mem_univ _)]
          rw [if_neg (fun h : p.1 = x ∧ x = t.1 => hp (h.1.trans h.2))]]
  · have hR : controlled (A * B) T p t = 0 := by
      rw [controlled_apply, if_neg hk]
    rw [hR]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [if_neg (fun h : p.2 = k.2 ∧ k.2 = t.2 => hk (h.1.trans h.2))]

private theorem controlled_one {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (T : Finset (Fin r)) :
    controlled (1 : Matrix H H ℂ) T = 1 := by
  ext p t
  simp only [controlled_apply, Matrix.one_apply]
  by_cases hk : p.2 = t.2
  · rw [if_pos hk]
    have hbranch : (if p.2 ∈ T then (if p.1 = t.1 then (1 : ℂ) else 0)
        else (if p.1 = t.1 then 1 else 0)) = if p.1 = t.1 then 1 else 0 := by
      by_cases hT : p.2 ∈ T <;> simp [hT]
    rw [hbranch]
    by_cases hp : p.1 = t.1
    · rw [if_pos hp, if_pos (Prod.ext hp hk)]
    · rw [if_neg hp, if_neg (fun he => hp (congrArg Prod.fst he))]
  · rw [if_neg hk, if_neg (fun he => hk (congrArg Prod.snd he))]

private theorem controlled_conjTranspose {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (A : Matrix H H ℂ) (T : Finset (Fin r)) :
    (controlled A T)ᴴ = controlled Aᴴ T := by
  ext p t
  simp only [Matrix.conjTranspose_apply, controlled_apply]
  by_cases hk : p.2 = t.2
  · by_cases hT : p.2 ∈ T
    · have hTt : t.2 ∈ T := hk ▸ hT
      by_cases hp : p.1 = t.1
      · simp [hk, hTt, hp]
      · simp [hk, hTt]
    · have hTt : t.2 ∉ T := fun ht => hT (hk ▸ ht)
      by_cases hp : p.1 = t.1
      · simp [hk, hTt, hp]
      · simp [hk, hTt, hp, eq_comm]
  · simp [hk]
    intro h
    exact (hk h.symm).elim

private theorem controlled_mem_unitary {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (A : Matrix H H ℂ) (T : Finset (Fin r))
    (hA : A ∈ Matrix.unitaryGroup H ℂ) :
    controlled A T ∈ Matrix.unitaryGroup (Space H r) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hAA : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.1 hA
  rw [Matrix.star_eq_conjTranspose, controlled_conjTranspose, controlled_mul,
    show (Aᴴ * A : Matrix H H ℂ) = star A * A by rw [Matrix.star_eq_conjTranspose],
    hAA, controlled_one]

private theorem reflect_mul_self {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (G : Matrix H I ℂ) (hIso : IsIsometry G) :
    (2 • (G * Gᴴ) - 1) * (2 • (G * Gᴴ) - 1) = 1 := by
  have hPP : (G * Gᴴ) * (G * Gᴴ) = G * Gᴴ := by
    calc (G * Gᴴ) * (G * Gᴴ) = G * (Gᴴ * G) * Gᴴ := by simp only [Matrix.mul_assoc]
      _ = G * Gᴴ := by rw [hIso, Matrix.mul_one]
  have h2c : (2 • (G * Gᴴ) : Matrix H H ℂ) = ((2 : ℂ) • (G * Gᴴ)) :=
    (Nat.cast_smul_eq_nsmul (R := ℂ) 2 (G * Gᴴ)).symm
  rw [show (2 • (G * Gᴴ) - 1) * (2 • (G * Gᴴ) - 1)
      = (((2 : ℂ) • (G * Gᴴ)) - 1) * (((2 : ℂ) • (G * Gᴴ)) - 1) by rw [h2c]]
  have hstep : (((2 : ℂ) • (G * Gᴴ)) - 1) * (((2 : ℂ) • (G * Gᴴ)) - 1)
      = (4 : ℂ) • (G * Gᴴ) - (2 : ℂ) • (G * Gᴴ) - (((2 : ℂ) • (G * Gᴴ)) - 1) := by
    rw [sub_mul, mul_sub, mul_sub]
    rw [smul_mul_smul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
    rw [hPP, show ((2 : ℂ) * 2) = 4 from by norm_num]
  have h2smul : (4 : ℂ) • (G * Gᴴ) = (2 : ℂ) • (G * Gᴴ) + (2 : ℂ) • (G * Gᴴ) := by
    rw [show (4 : ℂ) = 2 + 2 from by norm_num, add_smul]
  rw [hstep, h2smul, add_sub_cancel_left, sub_sub_cancel]

private theorem reflect_selfAdjoint {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (G : Matrix H I ℂ) :
    (2 • (G * Gᴴ) - 1 : Matrix H H ℂ)ᴴ = 2 • (G * Gᴴ) - 1 := by
  have hP : (G * Gᴴ : Matrix H H ℂ)ᴴ = G * Gᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_nsmul, Matrix.conjTranspose_one, hP]

private theorem reflect_mem_unitary {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (G : Matrix H I ℂ) (hIso : IsIsometry G) :
    (2 • (G * Gᴴ) - 1 : Matrix H H ℂ) ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    reflect_selfAdjoint, reflect_mul_self G hIso]

private def stepMatrix {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (oracles : ℕ → Matrix H H ℂ) (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) : Matrix (Space H r) (Space H r) ℂ :=
  match s with
  | .known U => U
  | .call i T adj => controlled (if adj then (oracles i)ᴴ else oracles i) T

private def expand {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] {r : ℕ}
    (G : Matrix H I ℂ) : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r → Word H r
  | .known V => [.known V]
  | .call j T adj =>
    let R := controlled (2 • (G * Gᴴ) - 1) T
    if adj then [.known R, .call j T true] else [.call j T false, .known R]

private theorem compileWalk_eq {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] {r : ℕ}
    (G : Matrix H I ℂ) (C : Word H r) :
    compileWalk G C = C.flatMap (expand G) := rfl

private theorem wordMatrix_cons {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (oracles : ℕ → Matrix H H ℂ) (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) (C : Word H r) :
    wordMatrix oracles (s :: C) = wordMatrix oracles C * stepMatrix oracles s := by
  unfold wordMatrix stepMatrix
  simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one]
  rfl

private theorem wordMatrix_nil {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (oracles : ℕ → Matrix H H ℂ) :
    wordMatrix oracles ([] : Word H r) = 1 := rfl

private theorem wordMatrix_append {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (oracles : ℕ → Matrix H H ℂ) (C₁ C₂ : Word H r) :
    wordMatrix oracles (C₁ ++ C₂) = wordMatrix oracles C₂ * wordMatrix oracles C₁ := by
  induction C₁ with
  | nil => simp [wordMatrix_nil]
  | cons s C₁ ih =>
    rw [List.cons_append, wordMatrix_cons, wordMatrix_cons, ih, mul_assoc]

private theorem expand_wordMatrix {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] {r : ℕ}
    (G : Matrix H I ℂ) (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) (U : Matrix H H ℂ) :
    wordMatrix (fun _ => U) (expand G s) = stepMatrix (fun _ => walk G U) s := by
  cases s with
  | known V =>
    show wordMatrix (fun _ => U) ([.known V] : Word H r) = V
    rw [wordMatrix_cons, wordMatrix_nil, one_mul]
    show stepMatrix (fun _ => U) (.known V) = V
    rfl
  | call j T adj =>
    let R := controlled (2 • (G * Gᴴ) - 1) T
    cases adj with
    | false =>
      show wordMatrix (fun _ => U) ([.call j T false, .known R] : Word H r)
        = controlled (walk G U) T
      rw [wordMatrix_cons, wordMatrix_cons, wordMatrix_nil, one_mul]
      show stepMatrix (fun _ => U) (.known R) * stepMatrix (fun _ => U) (.call j T false)
        = controlled (walk G U) T
      show R * controlled U T = controlled (walk G U) T
      rw [show walk G U = (2 • (G * Gᴴ) - 1) * U from rfl, controlled_mul]
    | true =>
      show wordMatrix (fun _ => U) ([.known R, .call j T true] : Word H r)
        = controlled (walk G U)ᴴ T
      rw [wordMatrix_cons, wordMatrix_cons, wordMatrix_nil, one_mul]
      show stepMatrix (fun _ => U) (.call j T true) * stepMatrix (fun _ => U) (.known R)
        = controlled (walk G U)ᴴ T
      show controlled Uᴴ T * R = controlled (walk G U)ᴴ T
      rw [show walk G U = (2 • (G * Gᴴ) - 1) * U from rfl,
        Matrix.conjTranspose_mul, reflect_selfAdjoint, controlled_mul]

private theorem wordMatrix_compileWalk {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (G : Matrix H I ℂ) {r : ℕ} (C : Word H r)
    (U : Matrix H H ℂ) :
    wordMatrix (fun _ => U) (compileWalk G C) = wordMatrix (fun _ => walk G U) C := by
  induction C with
  | nil =>
    rw [compileWalk_eq, List.flatMap_nil, wordMatrix_nil, wordMatrix_nil]
  | cons s C ih =>
    have ih' : wordMatrix (fun _ => U) (C.flatMap (expand G))
        = wordMatrix (fun _ => walk G U) C := by
      rw [← compileWalk_eq]
      exact ih
    rw [compileWalk_eq, List.flatMap_cons, wordMatrix_append, ih',
      wordMatrix_cons, expand_wordMatrix G s U]

private theorem calls_cons {H : Type} {r : ℕ} (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) (C : Word H r)
    (slot : ℕ) :
    calls (s :: C) slot = (match s with
        | .call i _ _ => if i = slot then 1 else 0
        | _ => 0) + calls C slot := by
  unfold calls
  rw [List.countP_cons]
  cases s with
  | known V => simp
  | call i T adj =>
    simp only
    by_cases h : i = slot
    · simp [h]
      exact Nat.add_comm _ _
    · simp [h]

private theorem gateCount_cons {H : Type} {r : ℕ} (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) (C : Word H r) :
    gateCount (s :: C) = (match s with | .known _ => 1 | _ => 0) + gateCount C := by
  unfold gateCount
  rw [List.countP_cons]
  cases s <;> simp [Nat.add_comm]

private theorem calls_expand {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] {r : ℕ}
    (G : Matrix H I ℂ) (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) (slot : ℕ) :
    calls (expand G s) slot = match s with
      | .call i _ _ => if i = slot then 1 else 0
      | _ => 0 := by
  cases s with
  | known V =>
    show calls ([.known V] : Word H r) slot = 0
    rw [calls_cons]
    simp [calls]
  | call j T adj =>
    let R := controlled (2 • (G * Gᴴ) - 1) T
    cases adj with
    | true =>
      show calls ([.known R, .call j T true] : Word H r) slot = if j = slot then 1 else 0
      rw [calls_cons, calls_cons]
      simp [calls]
    | false =>
      show calls ([.call j T false, .known R] : Word H r) slot = if j = slot then 1 else 0
      rw [calls_cons, calls_cons]
      simp [calls]

private theorem gateCount_expand {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] {r : ℕ}
    (G : Matrix H I ℂ) (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) :
    gateCount (expand G s) = 1 := by
  cases s with
  | known V =>
    show gateCount ([.known V] : Word H r) = 1
    rw [gateCount_cons]
    simp [gateCount]
  | call j T adj =>
    let R := controlled (2 • (G * Gᴴ) - 1) T
    cases adj with
    | true =>
      show gateCount ([.known R, .call j T true] : Word H r) = 1
      rw [gateCount_cons, gateCount_cons]
      simp [gateCount]
    | false =>
      show gateCount ([.call j T false, .known R] : Word H r) = 1
      rw [gateCount_cons, gateCount_cons]
      simp [gateCount]

private theorem calls_flatMap {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] {r : ℕ}
    (G : Matrix H I ℂ) (C : Word H r) (slot : ℕ) :
    calls (C.flatMap (expand G)) slot = calls C slot := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    rw [List.flatMap_cons]
    have h1 : calls (expand G s ++ C.flatMap (expand G)) slot
        = calls (expand G s) slot + calls (C.flatMap (expand G)) slot := by
      unfold calls
      rw [List.countP_append]
    rw [h1, calls_expand, calls_cons, ih]

private theorem gateCount_flatMap {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] {r : ℕ}
    (G : Matrix H I ℂ) (C : Word H r) :
    gateCount (C.flatMap (expand G)) = C.length := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    rw [List.flatMap_cons, List.length_cons]
    have h1 : gateCount (expand G s ++ C.flatMap (expand G))
        = gateCount (expand G s) + gateCount (C.flatMap (expand G)) := by
      unfold gateCount
      rw [List.countP_append]
    rw [h1, gateCount_expand, ih, Nat.add_comm]

private theorem length_eq_gateCount_add_calls {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (C : Word H r) (hC : legal 1 C) :
    C.length = gateCount C + calls C 0 := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    have hC' : legal 1 C := fun t ht => hC t (List.mem_cons_of_mem _ ht)
    rw [List.length_cons, gateCount_cons, calls_cons, ih hC']
    cases s with
    | known V =>
      simp only
      abel
    | call i T adj =>
      have hi : i < 1 := hC (.call i T adj) List.mem_cons_self
      have hi0 : i = 0 := by omega
      simp [hi0]
      abel

private theorem legal_expand {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] {r : ℕ}
    (G : Matrix H I ℂ) (hIso : IsIsometry G) (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r)
    (hs : match s with
        | .known U => U ∈ Matrix.unitaryGroup _ ℂ
        | .call i _ _ => i < 1) :
    ∀ t ∈ expand G s, match t with
      | .known U => U ∈ Matrix.unitaryGroup _ ℂ
      | .call i _ _ => i < 1 := by
  cases s with
  | known V =>
    show ∀ t ∈ ([.known V] : Word H r), _
    intro t ht
    have ht' : t = .known V := by simpa using! ht
    subst ht'
    exact hs
  | call j T adj =>
    have hR : (controlled (2 • (G * Gᴴ) - 1) T) ∈ Matrix.unitaryGroup (Space H r) ℂ :=
      controlled_mem_unitary _ T (reflect_mem_unitary G hIso)
    cases adj with
    | true =>
      show ∀ t ∈ ([.known (controlled (2 • (G * Gᴴ) - 1) T), .call j T true] : Word H r), _
      intro t ht
      have ht' : t = .known (controlled (2 • (G * Gᴴ) - 1) T)
          ∨ t = .call j T true := by simpa using! ht
      rcases ht' with rfl | rfl
      · exact hR
      · exact hs
    | false =>
      show ∀ t ∈ ([.call j T false, .known (controlled (2 • (G * Gᴴ) - 1) T)] : Word H r), _
      intro t ht
      have ht' : t = .call j T false
          ∨ t = .known (controlled (2 • (G * Gᴴ) - 1) T) := by simpa using! ht
      rcases ht' with rfl | rfl
      · exact hs
      · exact hR

private theorem legal_flatMap {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] {r : ℕ}
    (G : Matrix H I ℂ) (hIso : IsIsometry G) (C : Word H r) (hC : legal 1 C) :
    legal 1 (C.flatMap (expand G)) := by
  intro t ht
  rw [List.mem_flatMap] at ht
  obtain ⟨s, hsC, hst⟩ := ht
  exact legal_expand G hIso s (hC s hsC) t hst

theorem PaidWalkPaidWalkCompilation_answer : PaidWalkPaidWalkCompilation := by
  intro H I _ _ _ _ G r C hIso hLegal
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [compileWalk_eq]
    exact legal_flatMap G hIso C hLegal
  · rw [compileWalk_eq]
    exact calls_flatMap G C 0
  · rw [compileWalk_eq, gateCount_flatMap]
    exact length_eq_gateCount_add_calls C hLegal
  · intro U _hU
    exact wordMatrix_compileWalk G C U

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
