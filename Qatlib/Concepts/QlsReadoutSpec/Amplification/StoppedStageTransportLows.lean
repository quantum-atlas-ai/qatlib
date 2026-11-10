/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.StoppedStageTransportStat
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ProjectorOrderLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ClockFlagResolutionsLows
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.Phase


open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QlsReadoutSpec.Amplification

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.Amplification

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators ComplexOrder

private theorem star_mul_self_coe (z : ℂ) :
    star z * z = (((‖z‖ ^ 2 : ℝ) : ℂ)) := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  have h : Complex.normSq z = ‖z‖ ^ 2 :=
    (Complex.norm_mul_self_eq_normSq z).symm.trans (pow_two ‖z‖).symm
  rw [h]

private theorem normVec_sq {H : Type} [Fintype H] (v : H → ℂ) :
    normVec v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  show ‖toEuclidean_fromVec v‖ ^ 2 = _
  exact norm_toEuclidean_fromVec_sq v

private theorem star_dotProduct_self {H : Type} [Fintype H] (u : H → ℂ) :
    star u ⬝ᵥ u = (((normVec u) ^ 2 : ℝ) : ℂ) := by
  have hpt : ∀ i : H, star (u i) * (u i) = (((‖u i‖ ^ 2 : ℝ) : ℂ)) := fun i =>
    star_mul_self_coe (u i)
  rw [show star u ⬝ᵥ u = ∑ i, (star u) i * u i from rfl]
  simp only [Pi.star_apply]
  rw [Finset.sum_congr rfl fun i _ => hpt i, ← Complex.ofReal_sum, normVec_sq]

private theorem normVec_unitary_mulVec {H : Type} [Fintype H] [DecidableEq H]
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) (v : H → ℂ) :
    normVec (U *ᵥ v) = normVec v := by
  have hUHU : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
  have key : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec]
    have h1 : (star v ᵥ* Uᴴ) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ (Uᴴ *ᵥ (U *ᵥ v)) :=
      (Matrix.dotProduct_mulVec (star v) Uᴴ (U *ᵥ v)).symm
    rw [h1, Matrix.mulVec_mulVec, hUHU, Matrix.one_mulVec]
  rw [star_dotProduct_self, star_dotProduct_self] at key
  have h2 : normVec (U *ᵥ v) ^ 2 = normVec v ^ 2 := Complex.ofReal_inj.mp key
  exact le_antisymm (le_of_sq_le_sq h2.le (norm_nonneg _))
    (le_of_sq_le_sq h2.ge (norm_nonneg _))

private def callStep {H : Type} (i : ℕ) : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H 1 :=
    .call i Finset.univ false

private def callWord {H : Type} (is : List ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 1 := is.map callStep

private theorem wordMatrix_nil' {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) : wordMatrix U ([] : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 1) = 1 := rfl

private theorem wordMatrix_cons_call {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (i : ℕ) (C : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 1) :
    wordMatrix U (callStep i :: C) = wordMatrix U C * controlled (U i) Finset.univ := by
  unfold wordMatrix callStep
  simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one]
  rfl

private theorem controlled_univ_clean {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (ψ : QState H) (hr : 0 < 1) :
    controlled U Finset.univ *ᵥ clean 1 hr ψ = clean 1 hr (U *ᵥ ψ) := by
  funext p
  rcases p with ⟨h, k⟩
  have hk : k = (⟨0, hr⟩ : Fin 1) := Subsingleton.elim _ _
  subst hk
  show (∑ t : H × Fin 1, controlled U Finset.univ (h, (⟨0, hr⟩ : Fin 1)) t
      * clean 1 hr ψ t) = _
  rw [Fintype.sum_prod_type]
  have hinner : ∀ h' : H,
      (∑ k' : Fin 1, controlled U Finset.univ (h, (⟨0, hr⟩ : Fin 1)) (h', k')
        * clean 1 hr ψ (h', k')) = U h h' * ψ h' := by
    intro h'
    rw [Fin.sum_univ_one]
    show controlled U Finset.univ (h, (⟨0, hr⟩ : Fin 1)) (h', (⟨0, hr⟩ : Fin 1))
        * clean 1 hr ψ (h', (⟨0, hr⟩ : Fin 1)) = U h h' * ψ h'
    show (if (⟨0, hr⟩ : Fin 1) = ⟨0, hr⟩ then
        (if (⟨0, hr⟩ : Fin 1) ∈ (Finset.univ : Finset (Fin 1)) then U h h'
          else if h = h' then 1 else 0) else 0)
        * (if (⟨0, hr⟩ : Fin 1) = ⟨0, hr⟩ then ψ h' else 0) = U h h' * ψ h'
    simp
  rw [Finset.sum_congr rfl fun h' _ => hinner h']
  show (∑ h' : H, U h h' * ψ h') = (U *ᵥ ψ) h
  rfl

private theorem wordMatrix_callWord_clean {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (is : List ℕ) (hr : 0 < 1) :
    ∀ ψ : QState H, wordMatrix U (callWord (H := H) is) *ᵥ clean 1 hr ψ
      = clean 1 hr ((is.map U).reverse.prod *ᵥ ψ) := by
  induction is with
  | nil =>
    intro ψ
    show wordMatrix U ([] : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 1) *ᵥ clean 1 hr ψ
      = clean 1 hr ((1 : Matrix H H ℂ) *ᵥ ψ)
    rw [wordMatrix_nil', Matrix.one_mulVec, Matrix.one_mulVec]
  | cons i is ih =>
    intro ψ
    have hcons : callWord (H := H) (i :: is) = callStep i :: callWord is := rfl
    rw [hcons, wordMatrix_cons_call, ← Matrix.mulVec_mulVec,
      controlled_univ_clean, ih]
    show clean 1 hr ((is.map U).reverse.prod *ᵥ (U i *ᵥ ψ))
      = clean 1 hr (((i :: is).map U).reverse.prod *ᵥ ψ)
    rw [Matrix.mulVec_mulVec]
    congr 1
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one]

private theorem clockState_callWord {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (is : List ℕ) (ψ : QState H) :
    clockState U (callWord (H := H) is) ψ = (is.map U).reverse.prod *ᵥ ψ := by
  funext h
  have hrun := congrFun (wordMatrix_callWord_clean U is (by omega) ψ) (h, 0)
  show run (by omega) U (callWord is) ψ (h, 0) = ((is.map U).reverse.prod *ᵥ ψ) h
  have hclean : clean 1 (by omega) ((is.map U).reverse.prod *ᵥ ψ) (h, 0)
      = ((is.map U).reverse.prod *ᵥ ψ) h := by
    simp [clean]
  have key : run (by omega) U (callWord is) ψ (h, 0)
      = (wordMatrix U (callWord is) *ᵥ clean 1 (by omega) ψ) (h, 0) := rfl
  rw [key, hrun, hclean]

private theorem callWord_prod_unitary {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (is : List ℕ)
    (hU : ∀ i ∈ is, U i ∈ Matrix.unitaryGroup H ℂ) :
    (is.map U).reverse.prod ∈ Matrix.unitaryGroup H ℂ := by
  apply (Matrix.unitaryGroup H ℂ).list_prod_mem
  intro m hm
  rw [List.mem_reverse, List.mem_map] at hm
  obtain ⟨i, hi, rfl⟩ := hm
  exact hU i hi

private theorem comm_callWord_prod {H : Type} [Fintype H] [DecidableEq H]
    (pot : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ) (is : List ℕ)
    (hc : ∀ i ∈ is, pot * U i = U i * pot) :
    pot * (is.map U).reverse.prod = (is.map U).reverse.prod * pot := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have hci : pot * U i = U i * pot := hc i (by simp)
    have ih' : pot * (is.map U).reverse.prod = (is.map U).reverse.prod * pot := by
      apply ih
      intro j hj
      exact hc j (List.mem_cons_of_mem _ hj)
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one]
    rw [← mul_assoc, ih', mul_assoc, hci, ← mul_assoc]

private theorem range_split (j k : ℕ) (hjk : j ≤ k) :
    List.range (k + 1) = List.range (j + 1) ++ (List.range (k - j)).map (fun i => j + i + 1) := by
  have hk : k + 1 = (j + 1) + (k - j) := by omega
  rw [hk, List.range_add]
  congr 1
  exact List.map_congr_left fun i _ => by omega

private theorem plainPrefix_eq_append {H : Type} (j k : ℕ) (hjk : j ≤ k) :
    plainPrefix (H := H) k = plainPrefix j ++ suffixWord j k := by
  show (List.range (k + 1)).map _ = (List.range (j + 1)).map _ ++ (List.range (k - j)).map _
  rw [range_split j k hjk, List.map_append]
  simp only [List.map_map]
  rfl

private theorem suffixWord_eq_callWord {H : Type} (j k : ℕ) :
    suffixWord (H := H) j k = callWord ((List.range (k - j)).map (fun i => j + i + 1)) := by
  unfold suffixWord callWord callStep
  rw [List.map_map]
  rfl

private theorem plainPrefix_eq_callWord {H : Type} (j : ℕ) :
    plainPrefix (H := H) j = callWord (List.range (j + 1)) := rfl

private theorem clockState_plainPrefix_suffix {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (j k : ℕ) (hjk : j ≤ k) (ω : QState H) :
    clockState U (plainPrefix (H := H) k) ω
      = suffixState U j k (clockState U (plainPrefix j) ω) := by
  have hk : plainPrefix (H := H) k = callWord (List.range (k + 1)) := plainPrefix_eq_callWord k
  have hpj : plainPrefix (H := H) j = callWord (List.range (j + 1)) := plainPrefix_eq_callWord j
  rw [hk, clockState_callWord, range_split j k hjk,
    List.map_append, List.reverse_append, List.prod_append]
  rw [← Matrix.mulVec_mulVec]
  have h2 : ((List.range (j + 1)).map U).reverse.prod *ᵥ ω
      = clockState U (plainPrefix j) ω := by
    rw [← clockState_callWord U (List.range (j + 1)) ω, hpj]
  rw [h2]
  show (((List.range (k - j)).map (fun i => j + i + 1)).map U).reverse.prod
        *ᵥ clockState U (plainPrefix j) ω
      = suffixState U j k (clockState U (plainPrefix j) ω)
  rw [show suffixState U j k = clockState U (suffixWord j k) from rfl,
    suffixWord_eq_callWord, clockState_callWord]

private theorem extendClock_eq {H : Type} (m : ℕ) (P : Fin (m + 1) → Matrix H H ℂ)
    (j : Fin (m + 1)) : extendClock m P j.val = P j := by
  unfold extendClock
  rw [dif_pos (Nat.le_of_lt_succ j.isLt)]

theorem Clause4StoppedStageTransport_answer : Clause4StoppedStageTransport := by
  refine ⟨?_, ?_⟩
  · intro H _ _ P U hP hU
    have hPi : P * P = P := hP.1
    have hPs : Pᴴ = P := hP.2
    have hPsStar : star P = P := hP.2
    have hUU : U * Uᴴ = 1 := (Matrix.mem_unitaryGroup_iff).mp hU
    have hUHU : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
    have hA : U * P = P ↔ P * U = P := by
      constructor
      · intro h
        have h1 : P * Uᴴ = P := by
          have h2 := congrArg star h
          rwa [star_mul, hPsStar] at h2
        calc P * U = (P * Uᴴ) * U := by rw [h1]
          _ = P * (Uᴴ * U) := mul_assoc _ _ _
          _ = P * 1 := by rw [hUHU]
          _ = P := mul_one _
      · intro h
        have h1 : Uᴴ * P = P := by
          have h2 := congrArg star h
          rwa [star_mul, hPsStar] at h2
        calc U * P = U * (Uᴴ * P) := by rw [h1]
          _ = (U * Uᴴ) * P := (mul_assoc _ _ _).symm
          _ = 1 * P := by rw [hUU]
          _ = P := one_mul _
    have hB : U * P = P ↔ P * U * P = P := by
      constructor
      · intro h
        have h1 : P * U * P = P * (U * P) := mul_assoc P U P
        rw [h1, h, hPi]
      · intro h
        have hAdj : P * Uᴴ * P = P := by
          have h2 : (P * U * P)ᴴ = Pᴴ := congrArg star h
          have h3 : (P * U * P)ᴴ = P * Uᴴ * P := by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPs]
            exact (mul_assoc _ _ _).symm
          rw [h3] at h2
          rw [hPs] at h2
          exact h2
        have hSH : (U * P - P)ᴴ * (U * P - P) = 0 := by
          rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hPs]
          rw [sub_mul, mul_sub, mul_sub]
          have t1 : P * Uᴴ * (U * P) = P := by
            have h1 : Uᴴ * (U * P) = (Uᴴ * U) * P := (mul_assoc Uᴴ U P).symm
            calc P * Uᴴ * (U * P) = P * (Uᴴ * (U * P)) := mul_assoc _ _ _
              _ = P * ((Uᴴ * U) * P) := by rw [h1]
              _ = P * (1 * P) := by rw [hUHU]
              _ = P * P := by rw [one_mul]
              _ = P := hPi
          have t2 : P * Uᴴ * P = P := hAdj
          have t3 : P * (U * P) = P := by rwa [← mul_assoc]
          rw [t1, t2, t3, hPi]
          abel
        have hS0 : U * P - P = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hSH
        rwa [sub_eq_zero] at hS0
    have hC : U * P = P ↔ U = P + (1 - P) * U * (1 - P) := by
      constructor
      · intro h
        have hPU : P * U = P := hA.mp h
        have h1 : (1 - P : Matrix H H ℂ) * U * (1 - P) = U - P := by
          have hstep1 : (1 - P : Matrix H H ℂ) * U = U - P := by
            rw [sub_mul, one_mul, hPU]
          rw [hstep1]
          rw [mul_sub, mul_one]
          have hstep2 : (U - P : Matrix H H ℂ) * P = U * P - P * P := sub_mul U P P
          rw [hstep2, h, hPi]
          abel
        rw [h1]
        abel
      · intro h
        have h2 : (1 - P : Matrix H H ℂ) * P = 0 := by
          rw [sub_mul, one_mul, hPi, sub_self]
        rw [h, add_mul, hPi]
        have h4 : ((1 - P : Matrix H H ℂ) * U * (1 - P)) * P
            = (1 - P) * U * ((1 - P) * P) := by
          rw [mul_assoc, ← mul_assoc]
        rw [h4, h2, mul_zero, add_zero]
    exact ⟨hA, hB, hC⟩
  · intro H _ _ m P bad U hlegal hstage
    obtain ⟨hUunit, hstagefix⟩ := hstage
    obtain ⟨hP, hP0, hPm, hpsd, hbad, hcomm⟩ := hlegal
    have g3 := Clause3ClockFlagResolutions_answer H m P bad
      ⟨hP, hP0, hPm, hpsd, hbad, hcomm⟩
    have flag_right : ∀ j k : Fin (m + 1), j.val ≤ k.val → P k * P j = P j :=
      fun j k hjk => (g3.1 j k hjk).1
    have pot_proj : ∀ j : Fin (m + 1), IsOrthogonalProjector (potential (P j) bad) :=
      fun j => (g3.1 j j le_rfl).2.2.2.2.2.1
    have pot_prod_left : ∀ j k : Fin (m + 1), j.val ≤ k.val →
        potential (P j) bad * potential (P k) bad = potential (P k) bad :=
      fun j k hjk => (g3.1 j k hjk).2.2.2.2.2.2.2.1

    have htransport : ∀ (j k : Fin (m + 1)), j.val < k.val →
        U k.val * P j = P j ∧ P j * U k.val = P j ∧
        U k.val * potential (P j) bad = potential (P j) bad * U k.val := by
      intro j k hjk
      have hkpos : 0 < k.val := by omega
      have hklem : k.val - 1 < m := by omega
      have hUkPkm : U k.val * P ⟨k.val - 1, by omega⟩ = P ⟨k.val - 1, by omega⟩ := by
        have h := hstagefix (⟨k.val - 1, hklem⟩ : Fin m)
        change U (k.val - 1 + 1) * P ⟨k.val - 1, _⟩ = P ⟨k.val - 1, _⟩ at h
        rw [Nat.sub_add_cancel (by omega : 1 ≤ k.val)] at h
        exact h
      have hjle : j.val ≤ k.val - 1 := by omega
      have hPjPkm : P ⟨k.val - 1, by omega⟩ * P j = P j :=
        flag_right j ⟨k.val - 1, by omega⟩ (by
          show j.val ≤ (⟨k.val - 1, _⟩ : Fin (m + 1)).val
          show j.val ≤ k.val - 1
          exact hjle)
      have hfix : U k.val * P j = P j := by
        calc U k.val * P j = U k.val * (P ⟨k.val - 1, by omega⟩ * P j) := by rw [hPjPkm]
          _ = (U k.val * P ⟨k.val - 1, by omega⟩) * P j := by rw [← mul_assoc]
          _ = P ⟨k.val - 1, by omega⟩ * P j := by rw [hUkPkm]
          _ = P j := hPjPkm
      have hUk : U k.val ∈ Matrix.unitaryGroup H ℂ := hUunit k
      have hUHU : (U k.val)ᴴ * U k.val = 1 := (Matrix.mem_unitaryGroup_iff').mp hUk
      have hfix' : P j * U k.val = P j := by
        have h1 : P j * (U k.val)ᴴ = P j := by
          have h2 := congrArg star hfix
          rwa [star_mul, (hP j).2] at h2
        have h3 : P j * (U k.val)ᴴ * U k.val = P j * U k.val := by rw [h1]
        rw [mul_assoc, hUHU, mul_one] at h3
        exact h3.symm
      have hPjbad : P j * bad = P j * bad * P j := by
        symm
        rw [mul_assoc, ← hcomm j, ← mul_assoc, (hP j).1]
      have hPjbadU : P j * bad * U k.val = P j * bad := by
        calc P j * bad * U k.val = (P j * bad * P j) * U k.val := by rw [← hPjbad]
          _ = P j * bad * (P j * U k.val) := by rw [mul_assoc]
          _ = P j * bad * P j := by rw [hfix']
          _ = P j * bad := hPjbad.symm
      have hcomm_pot : U k.val * potential (P j) bad = potential (P j) bad * U k.val := by
        show U k.val * (1 - P j * bad) = (1 - P j * bad) * U k.val
        rw [mul_sub, mul_one, ← mul_assoc, hfix, sub_mul, one_mul, hPjbadU]
      exact ⟨hfix, hfix', hcomm_pot⟩

    have hnorm : ∀ (j k : Fin (m + 1)) (ψ : QState H), j.val ≤ k.val →
        normVec (potential (P j) bad *ᵥ suffixState U j.val k.val ψ) =
          normVec (potential (P j) bad *ᵥ ψ) := by
      intro j k ψ hjk
      have hs : suffixState U j.val k.val ψ
          = (((List.range (k.val - j.val)).map (fun i => j.val + i + 1)).map U).reverse.prod
              *ᵥ ψ := by
        rw [show suffixState U j.val k.val ψ = clockState U (suffixWord j.val k.val) ψ from rfl,
          suffixWord_eq_callWord, clockState_callWord]
      rw [hs]
      set is := (List.range (k.val - j.val)).map (fun i => j.val + i + 1)
      have hmem : ∀ x ∈ is, j.val < x ∧ x ≤ k.val := by
        intro x hx
        simp only [is, List.mem_map, List.mem_range] at hx
        obtain ⟨t, ht, hx'⟩ := hx
        have hx2 : x = j.val + t + 1 := by
          rw [hx']
        omega
      have hcommW : potential (P j) bad * (is.map U).reverse.prod
          = (is.map U).reverse.prod * potential (P j) bad := by
        apply comm_callWord_prod
        intro i hi
        obtain ⟨hlt, _⟩ := hmem i hi
        exact (htransport j ⟨i, by omega⟩ hlt).2.2.symm
      have hunit : (is.map U).reverse.prod ∈ Matrix.unitaryGroup H ℂ := by
        apply callWord_prod_unitary
        intro i hi
        obtain ⟨_, hle⟩ := hmem i hi
        exact hUunit ⟨i, by omega⟩
      have hkey : potential (P j) bad *ᵥ ((is.map U).reverse.prod *ᵥ ψ)
          = (is.map U).reverse.prod *ᵥ (potential (P j) bad *ᵥ ψ) := by
        rw [Matrix.mulVec_mulVec, hcommW, ← Matrix.mulVec_mulVec]
      rw [hkey, normVec_unitary_mulVec hunit]

    have hmono : ∀ (j k : Fin (m + 1)) (ω : QState H), j.val ≤ k.val →
        plainAmplitude (extendClock m P) bad U ω k.val
          ≤ plainAmplitude (extendClock m P) bad U ω j.val := by
      intro j k ω hjk
      have hej : extendClock m P j.val = P j := extendClock_eq m P j
      have hek : extendClock m P k.val = P k := extendClock_eq m P k
      have hψk : clockState U (plainPrefix k.val) ω
          = suffixState U j.val k.val (clockState U (plainPrefix j.val) ω) :=
        clockState_plainPrefix_suffix U j.val k.val hjk ω
      have hnormj := hnorm j k (clockState U (plainPrefix j.val) ω) hjk
      have hG2 : ∀ ψ : QState H,
          normVec (potential (P k) bad *ᵥ ψ) ≤ normVec (potential (P j) bad *ᵥ ψ) :=
        (Clause2ProjectorOrder_answer H (potential (P k) bad) (potential (P j) bad)
          (pot_proj k) (pot_proj j)).2.2.2.2.2.2.mp (pot_prod_left j k hjk)
      have key1 : plainAmplitude (extendClock m P) bad U ω k.val
          = normVec (potential (P k) bad *ᵥ clockState U (plainPrefix k.val) ω) := by
        unfold plainAmplitude
        rw [hek]
      have key2 : plainAmplitude (extendClock m P) bad U ω j.val
          = normVec (potential (P j) bad *ᵥ clockState U (plainPrefix j.val) ω) := by
        unfold plainAmplitude
        rw [hej]
      rw [key1, key2, hψk]
      exact le_trans (hG2 _) (le_of_eq hnormj)
    exact ⟨htransport, hnorm, hmono⟩

end Qatlib.Concepts.QlsReadoutSpec.Amplification
