/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.AmplifiedSuffixRaysStat
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ProjectorOrderLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ClockFlagResolutionsLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.StoppedStageTransportLows
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QlsReadoutSpec.Amplification

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.Amplification

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators ComplexOrder

private theorem normVec_sq_eq {H : Type} [Fintype H] (v : QState H) :
    normVec v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  show ‖toEuclidean_fromVec v‖ ^ 2 = _
  exact norm_toEuclidean_fromVec_sq v

private theorem normVec_smul_complex {H : Type} [Fintype H] (c : ℂ) (v : QState H) :
    normVec (c • v) = ‖c‖ * normVec v := by
  have key : normVec (c • v) ^ 2 = (‖c‖ * normVec v) ^ 2 := by
    rw [normVec_sq_eq, mul_pow, normVec_sq_eq, Finset.mul_sum]
    simp only [Pi.smul_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [norm_smul, mul_pow]
  exact le_antisymm
    (le_of_sq_le_sq key.le (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (le_of_sq_le_sq key.ge (norm_nonneg _))

private theorem normVec_real_smul {H : Type} [Fintype H] (r : ℝ) (v : QState H) :
    normVec ((r : ℂ) • v) = |r| * normVec v := by
  rw [normVec_smul_complex, Complex.norm_real, Real.norm_eq_abs]

private theorem normState_smul_pos {H : Type} [Fintype H] {r : ℝ} (hr : 0 < r)
    (v : QState H) (hv : normVec v ≠ 0) :
    normState ((r : ℂ) • v) = normState v := by
  have h1 : ((normVec ((r : ℂ) • v) : ℝ) : ℂ) = ((r * normVec v : ℝ) : ℂ) := by
    rw [normVec_real_smul, abs_of_pos hr]
  have hkey : ((normVec ((r : ℂ) • v) : ℂ)⁻¹) • ((r : ℂ) • v)
      = ((normVec v : ℂ)⁻¹) • v := by
    rw [h1, smul_smul]
    have h3 : (((r * normVec v : ℝ) : ℂ)⁻¹ * r) = ((normVec v : ℂ)⁻¹) := by
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have hv0 : (normVec v : ℂ) ≠ 0 := by exact_mod_cast hv
      rw [Complex.ofReal_mul]
      field_simp [hr0, hv0]
    rw [h3]
  exact hkey

private theorem smul_of_normState_eq {H : Type} [Fintype H]
    (a b : QState H) (_ha : 0 < normVec a) (hb : 0 < normVec b)
    (h : normState a = normState b) :
    b = ((normVec b / normVec a : ℝ) : ℂ) • a := by
  have hb0 : (normVec b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hkey : ((normVec a : ℂ)⁻¹) • a = ((normVec b : ℂ)⁻¹) • b := h
  have hsmul : (normVec b : ℂ) • (((normVec a : ℂ)⁻¹) • a)
      = (normVec b : ℂ) • (((normVec b : ℂ)⁻¹) • b) := by rw [hkey]
  rw [smul_smul, smul_smul, mul_inv_cancel₀ hb0, one_smul] at hsmul
  have h2 : ((normVec b : ℂ) * (normVec a : ℂ)⁻¹) = ((normVec b / normVec a : ℝ) : ℂ) := by
    rw [← div_eq_mul_inv, Complex.ofReal_div]
  rw [h2] at hsmul
  exact hsmul.symm

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

private theorem suffixWord_eq_callWord {H : Type} (j k : ℕ) :
    suffixWord (H := H) j k = callWord ((List.range (k - j)).map (fun i => j + i + 1)) := by
  unfold suffixWord callWord callStep
  rw [List.map_map]
  rfl

private theorem suffixState_eq_prod {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (j k : ℕ) (ψ : QState H) :
    suffixState U j k ψ
      = (((List.range (k - j)).map (fun i => U (j + i + 1))).reverse.prod) *ᵥ ψ := by
  show clockState U (suffixWord j k) ψ = _
  rw [suffixWord_eq_callWord, clockState_callWord]
  have hmaps : List.map U (List.map (fun i => j + i + 1) (List.range (k - j)))
      = List.map (fun i => U (j + i + 1)) (List.range (k - j)) := by
    conv_lhs => rw [List.map_map]
    apply List.map_congr_left
    intro i _
    rfl
  rw [hmaps]

private theorem suffixState_self {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (j : ℕ) (ψ : QState H) :
    suffixState U j j ψ = ψ := by
  rw [suffixState_eq_prod, show j - j = 0 from Nat.sub_self j]
  show (((List.range 0).map (fun i => U (j + i + 1))).reverse.prod) *ᵥ ψ = ψ
  rw [List.range_zero, List.map_nil, List.reverse_nil, List.prod_nil, Matrix.one_mulVec]

private theorem suffixState_succ {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (j k : ℕ) (hjk : j ≤ k) (ψ : QState H) :
    suffixState U j (k + 1) ψ = U (k + 1) *ᵥ suffixState U j k ψ := by
  rw [suffixState_eq_prod, suffixState_eq_prod]
  have hsub : k + 1 - j = (k - j) + 1 := by omega
  rw [hsub, List.range_succ, List.map_append, List.map_singleton,
    List.reverse_append, List.reverse_singleton, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one]
  have hjk2 : j + (k - j) + 1 = k + 1 := by omega
  rw [hjk2, Matrix.mulVec_mulVec]

private theorem suffixState_split {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (j k : ℕ) (hjk : j < k) (ψ : QState H) :
    suffixState U j k ψ = suffixState U (j + 1) k (U (j + 1) *ᵥ ψ) := by
  rw [suffixState_eq_prod, suffixState_eq_prod]
  have hsub : k - j = (k - (j + 1)) + 1 := by omega
  rw [hsub, List.range_succ_eq_map, List.map_cons]
  have h0 : U (j + 0 + 1) = U (j + 1) := by simp
  rw [h0, List.map_map]
  have hmap : List.map ((fun i => U (j + i + 1)) ∘ Nat.succ) (List.range (k - (j + 1)))
      = List.map (fun i => U (j + 1 + i + 1)) (List.range (k - (j + 1))) := by
    apply List.map_congr_left
    intro i _
    show U (j + (i + 1) + 1) = U (j + 1 + i + 1)
    rw [show j + (i + 1) + 1 = j + 1 + i + 1 from by omega]
  rw [hmap, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
    ← Matrix.mulVec_mulVec]

private theorem suffixState_smul {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (j k : ℕ) (c : ℂ) (ψ : QState H) :
    suffixState U j k (c • ψ) = c • suffixState U j k ψ := by
  rw [suffixState_eq_prod, suffixState_eq_prod, Matrix.mulVec_smul]

private theorem comm_map_prod {H : Type} [Fintype H] [DecidableEq H]
    (M : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ) (is : List ℕ)
    (hc : ∀ i ∈ is, M * U i = U i * M) :
    M * (is.map U).reverse.prod = (is.map U).reverse.prod * M := by
  induction is with
  | nil => simp
  | cons a as ih =>
    have ha : M * U a = U a * M := hc a (by simp)
    have has : ∀ i ∈ as, M * U i = U i * M := fun i hi => hc i (List.mem_cons_of_mem _ hi)
    have ih' : M * (as.map U).reverse.prod = (as.map U).reverse.prod * M := ih has
    have hform : ((a :: as).map U).reverse.prod = (as.map U).reverse.prod * U a := by
      rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons,
        List.prod_nil, mul_one]
    rw [hform]
    calc M * ((as.map U).reverse.prod * U a) = (M * (as.map U).reverse.prod) * U a := by
          rw [← mul_assoc]
      _ = ((as.map U).reverse.prod * M) * U a := by rw [ih']
      _ = (as.map U).reverse.prod * (M * U a) := by rw [mul_assoc]
      _ = (as.map U).reverse.prod * (U a * M) := by rw [ha]
      _ = ((as.map U).reverse.prod * U a) * M := by rw [← mul_assoc]

private theorem suffixState_commute_left {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (M : Matrix H H ℂ) (j k : ℕ)
    (hc : ∀ i, j < i → i ≤ k → M * U i = U i * M) (ψ : QState H) :
    M *ᵥ suffixState U j k ψ = suffixState U j k (M *ᵥ ψ) := by
  rw [suffixState_eq_prod, suffixState_eq_prod, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hcommW : M * ((List.range (k - j)).map (fun i => U (j + i + 1))).reverse.prod
      = ((List.range (k - j)).map (fun i => U (j + i + 1))).reverse.prod * M := by
    set is := (List.range (k - j)).map (fun i => j + i + 1)
    have hmap : (List.range (k - j)).map (fun i => U (j + i + 1)) = is.map U := by
      unfold is
      rw [List.map_map]
      rfl
    rw [hmap]
    apply comm_map_prod
    intro i hi
    simp only [is, List.mem_map, List.mem_range] at hi
    obtain ⟨t, ht, hi'⟩ := hi
    subst hi'
    exact hc (j + t + 1) (by omega) (by
      have : t < k - j := ht
      omega)
  rw [hcommW]

private def stageGain {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m + 1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (V : ℕ → Matrix H H ℂ) (ω : QState H) (i : ℕ) : ℝ :=
  if hi : i < m then
    normVec (potential (P ⟨i + 1, by omega⟩) bad *ᵥ (U (i + 1) *ᵥ (V i *ᵥ ω))) /
      normVec (potential (P ⟨i + 1, by omega⟩) bad *ᵥ (V (i + 1) *ᵥ ω))
  else 1

private def gainProd {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m + 1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (V : ℕ → Matrix H H ℂ) (ω : QState H) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n) (fun i => stageGain m P bad U V ω i)

theorem Clause6AmplifiedSuffixRays_answer : Clause6AmplifiedSuffixRays := by
  intro H _ _ m P bad U V ω hlegal hstage hnormω hV0 hVunit hass j l k h hjk hlk hjh hlh
  obtain ⟨hP, hP0, hPm, hpsd, hbad, hcomm⟩ := hlegal
  obtain ⟨hUunit, hstagefix⟩ := hstage
  have g3 := Clause3ClockFlagResolutions_answer H m P bad ⟨hP, hP0, hPm, hpsd, hbad, hcomm⟩
  have g4 := Clause4StoppedStageTransport_answer.2 H m P bad U
    ⟨hP, hP0, hPm, hpsd, hbad, hcomm⟩ ⟨hUunit, hstagefix⟩

  have pot_prod : ∀ (p q : Fin (m + 1)), p.val ≤ q.val →
      potential (P q) bad * potential (P p) bad = potential (P q) bad ∧
      potential (P p) bad * potential (P q) bad = potential (P q) bad := by
    intro p q hpq
    have h := (g3.1 p q hpq).2.2.2.2.2.2
    exact ⟨h.1, h.2.1⟩

  have hcommU : ∀ (p : Fin (m + 1)) (i : ℕ), p.val < i → i ≤ m →
      U i * potential (P p) bad = potential (P p) bad * U i := by
    intro p i hlt hle
    exact (g4.1 p ⟨i, by omega⟩ (by
      show p.val < (⟨i, by omega⟩ : Fin (m + 1)).val
      exact hlt)).2.2

  have hgain_pos : ∀ i, 0 < stageGain m P bad U V ω i := by
    intro i
    unfold stageGain
    split_ifs with hi
    · obtain ⟨ha, hb, _⟩ := (hass ⟨i, hi⟩)
      exact div_pos hb ha
    · exact one_pos
  have hprod_pos : ∀ n, 0 < gainProd m P bad U V ω n := by
    intro n
    unfold gainProd
    exact Finset.prod_pos fun i _ => hgain_pos i

  have factor : ∀ n : ℕ, ∀ p q : ℕ, (hq : q ≤ m) → p ≤ q → q - p = n →
      potential (P ⟨q, Nat.lt_succ_of_le hq⟩) bad *ᵥ suffixState U p q (V p *ᵥ ω)
        = ((gainProd m P bad U V ω q / gainProd m P bad U V ω p : ℝ) : ℂ)
            • (potential (P ⟨q, Nat.lt_succ_of_le hq⟩) bad *ᵥ (V q *ᵥ ω)) := by
    intro n
    induction n with
    | zero =>
      intro p q hq hpq hsub
      have hp : p = q := by omega
      rw [hp, suffixState_self, div_self (hprod_pos q).ne', Complex.ofReal_one, one_smul]
    | succ n ih =>
      intro p q hq hpq hsub
      have hlt : p < q := by omega
      have hp_lt_m : p < m := by omega
      have hple : p + 1 ≤ q := by omega
      have hsub2 : q - (p + 1) = n := by omega
      have hq' : q < m + 1 := Nat.lt_succ_of_le hq
      have hpm' : p + 1 < m + 1 := by omega
      set Gq := potential (P ⟨q, hq'⟩) bad with hGq
      set Gp1 := potential (P ⟨p + 1, hpm'⟩) bad with hGp1
      set ψp := V p *ᵥ ω with hψp
      set ψp1 := V (p + 1) *ᵥ ω with hψp1

      have hsplit : suffixState U p q ψp = suffixState U (p + 1) q (U (p + 1) *ᵥ ψp) :=
        suffixState_split U p q hlt ψp

      have habsorb : ∀ χ : QState H,
          Gq *ᵥ suffixState U (p + 1) q (Gp1 *ᵥ χ) = Gq *ᵥ suffixState U (p + 1) q χ := by
        intro χ
        have hprod : Gq * Gp1 = Gq :=
          (pot_prod ⟨p + 1, hpm'⟩ ⟨q, hq'⟩ (by omega)).1
        have hcommS : Gp1 *ᵥ suffixState U (p + 1) q χ
            = suffixState U (p + 1) q (Gp1 *ᵥ χ) := by
          apply suffixState_commute_left
          intro i hlt2 hle2
          exact (hcommU ⟨p + 1, hpm'⟩ i hlt2 (le_trans hle2 hq)).symm
        calc Gq *ᵥ suffixState U (p + 1) q (Gp1 *ᵥ χ)
            = Gq *ᵥ (Gp1 *ᵥ suffixState U (p + 1) q χ) := by rw [hcommS]
          _ = (Gq * Gp1) *ᵥ suffixState U (p + 1) q χ := by rw [Matrix.mulVec_mulVec]
          _ = Gq *ᵥ suffixState U (p + 1) q χ := by rw [hprod]

      have hass' := hass ⟨p, hp_lt_m⟩
      obtain ⟨ha, hb, hdir⟩ := hass'
      have hsmul : Gp1 *ᵥ (U (p + 1) *ᵥ ψp)
          = ((normVec (Gp1 *ᵥ (U (p + 1) *ᵥ ψp))
              / normVec (Gp1 *ᵥ ψp1) : ℝ) : ℂ) • (Gp1 *ᵥ ψp1) :=
        smul_of_normState_eq _ _ ha hb hdir

      have hpeel : Gq *ᵥ suffixState U p q ψp
          = (stageGain m P bad U V ω p : ℂ) • (Gq *ᵥ suffixState U (p + 1) q ψp1) := by
        rw [hsplit]
        have h1 : Gq *ᵥ suffixState U (p + 1) q (U (p + 1) *ᵥ ψp)
            = Gq *ᵥ suffixState U (p + 1) q (Gp1 *ᵥ (U (p + 1) *ᵥ ψp)) := by
          rw [habsorb]
        rw [h1, hsmul, suffixState_smul, Matrix.mulVec_smul]
        have h3 : Gq *ᵥ suffixState U (p + 1) q (Gp1 *ᵥ ψp1)
            = Gq *ᵥ suffixState U (p + 1) q ψp1 := habsorb ψp1
        rw [h3]
        have h4 : (stageGain m P bad U V ω p : ℂ)
            = ((normVec (Gp1 *ᵥ (U (p + 1) *ᵥ ψp))
                / normVec (Gp1 *ᵥ ψp1) : ℝ) : ℂ) := by
          rw [hGp1, hψp, hψp1]
          unfold stageGain
          simp only [dif_pos hp_lt_m]
        rw [← h4]

      have ih' : potential (P ⟨q, hq'⟩) bad *ᵥ suffixState U (p + 1) q (V (p + 1) *ᵥ ω)
          = ((gainProd m P bad U V ω q / gainProd m P bad U V ω (p + 1) : ℝ) : ℂ)
              • (potential (P ⟨q, hq'⟩) bad *ᵥ (V q *ᵥ ω)) :=
        ih (p + 1) q hq hple hsub2
      rw [hpeel, ih', smul_smul]
      congr 1
      have hΓ : gainProd m P bad U V ω (p + 1)
          = gainProd m P bad U V ω p * stageGain m P bad U V ω p := by
        unfold gainProd
        rw [Finset.prod_range_succ, mul_comm]
      have hGp0 : (gainProd m P bad U V ω p : ℂ) ≠ 0 :=
        by exact_mod_cast (hprod_pos p).ne'
      have hGq0 : (gainProd m P bad U V ω q : ℂ) ≠ 0 :=
        by exact_mod_cast (hprod_pos q).ne'
      have hμ0 : (stageGain m P bad U V ω p : ℂ) ≠ 0 :=
        by exact_mod_cast (hgain_pos p).ne'
      have hrew : (gainProd m P bad U V ω (p + 1) : ℂ)
          = (gainProd m P bad U V ω p : ℂ) * (stageGain m P bad U V ω p : ℂ) := by
        rw [← Complex.ofReal_mul, hΓ]
      rw [Complex.ofReal_div, Complex.ofReal_div, hrew]
      field_simp [hGp0, hGq0, hμ0]

  have hjm : j.val ≤ m := by omega
  have hlm : l.val ≤ m := by omega
  have hkm : k.val ≤ m := by omega
  have hhm : h.val ≤ m := by omega
  set w := potential (P k) bad *ᵥ (V k.val *ᵥ ω)
  set wh := potential (P h) bad *ᵥ (V h.val *ᵥ ω)
  have fsj : potential (P k) bad *ᵥ suffixState U j.val k.val (V j.val *ᵥ ω)
      = ((gainProd m P bad U V ω k.val / gainProd m P bad U V ω j.val : ℝ) : ℂ) • w :=
    factor (k.val - j.val) j.val k.val hkm hjk rfl
  have fsl : potential (P k) bad *ᵥ suffixState U l.val k.val (V l.val *ᵥ ω)
      = ((gainProd m P bad U V ω k.val / gainProd m P bad U V ω l.val : ℝ) : ℂ) • w :=
    factor (k.val - l.val) l.val k.val hkm hlk rfl
  have ftj : potential (P h) bad *ᵥ suffixState U j.val h.val (V j.val *ᵥ ω)
      = ((gainProd m P bad U V ω h.val / gainProd m P bad U V ω j.val : ℝ) : ℂ) • wh :=
    factor (h.val - j.val) j.val h.val hhm hjh rfl
  have ftl : potential (P h) bad *ᵥ suffixState U l.val h.val (V l.val *ᵥ ω)
      = ((gainProd m P bad U V ω h.val / gainProd m P bad U V ω l.val : ℝ) : ℂ) • wh :=
    factor (h.val - l.val) l.val h.val hhm hlh rfl

  intro sj sl tj tl hpos1 hpos2

  have hsjeq : sj = potential (P k) bad *ᵥ suffixState U j.val k.val (V j.val *ᵥ ω) := rfl
  have hsleq : sl = potential (P k) bad *ᵥ suffixState U l.val k.val (V l.val *ᵥ ω) := rfl
  have htjeq : tj = potential (P h) bad *ᵥ suffixState U j.val h.val (V j.val *ᵥ ω) := rfl
  have htleq : tl = potential (P h) bad *ᵥ suffixState U l.val h.val (V l.val *ᵥ ω) := rfl

  have hw_pos : 0 < normVec w := by
    have hnorm_eq : normVec (potential (P k) bad
        *ᵥ suffixState U j.val k.val (V j.val *ᵥ ω))
        = |gainProd m P bad U V ω k.val / gainProd m P bad U V ω j.val| * normVec w := by
      rw [fsj, normVec_real_smul]
    have hpos1' : 0 < normVec (potential (P k) bad
        *ᵥ suffixState U j.val k.val (V j.val *ᵥ ω)) := by rw [← hsjeq]; exact hpos1
    rw [hnorm_eq] at hpos1'
    have hpos : 0 < |gainProd m P bad U V ω k.val / gainProd m P bad U V ω j.val| :=
      abs_pos.mpr (div_ne_zero (hprod_pos _).ne' (hprod_pos _).ne')
    by_contra hle
    push Not at hle
    have hle0 : normVec w = 0 := le_antisymm hle (norm_nonneg _)
    rw [hle0, mul_zero] at hpos1'
    exact (lt_irrefl 0) (by linarith)
  have hw_ne : normVec w ≠ 0 := hw_pos.ne'
  have hsnorm : normState (potential (P k) bad *ᵥ suffixState U j.val k.val (V j.val *ᵥ ω))
      = normState w := by
    rw [fsj, normState_smul_pos]
    · exact div_pos (hprod_pos _) (hprod_pos _)
    · exact hw_ne
  have hslnorm : normState (potential (P k) bad *ᵥ suffixState U l.val k.val (V l.val *ᵥ ω))
      = normState w := by
    rw [fsl, normState_smul_pos]
    · exact div_pos (hprod_pos _) (hprod_pos _)
    · exact hw_ne
  show normState (potential (P k) bad *ᵥ suffixState U j.val k.val (V j.val *ᵥ ω))
      = normState (potential (P k) bad *ᵥ suffixState U l.val k.val (V l.val *ᵥ ω))
    ∧ normVec (potential (P h) bad *ᵥ suffixState U j.val h.val (V j.val *ᵥ ω))
        / normVec (potential (P k) bad *ᵥ suffixState U j.val k.val (V j.val *ᵥ ω))
      = normVec (potential (P h) bad *ᵥ suffixState U l.val h.val (V l.val *ᵥ ω))
        / normVec (potential (P k) bad *ᵥ suffixState U l.val k.val (V l.val *ᵥ ω))
  refine ⟨?_, ?_⟩
  · rw [hsnorm, hslnorm]
  · have nsj : normVec (potential (P k) bad *ᵥ suffixState U j.val k.val (V j.val *ᵥ ω))
        = (gainProd m P bad U V ω k.val / gainProd m P bad U V ω j.val) * normVec w := by
      rw [fsj, normVec_real_smul, abs_of_nonneg
        (div_nonneg (hprod_pos _).le (hprod_pos _).le)]
    have nsl : normVec (potential (P k) bad *ᵥ suffixState U l.val k.val (V l.val *ᵥ ω))
        = (gainProd m P bad U V ω k.val / gainProd m P bad U V ω l.val) * normVec w := by
      rw [fsl, normVec_real_smul, abs_of_nonneg
        (div_nonneg (hprod_pos _).le (hprod_pos _).le)]
    have ntj : normVec (potential (P h) bad *ᵥ suffixState U j.val h.val (V j.val *ᵥ ω))
        = (gainProd m P bad U V ω h.val / gainProd m P bad U V ω j.val) * normVec wh := by
      rw [ftj, normVec_real_smul, abs_of_nonneg
        (div_nonneg (hprod_pos _).le (hprod_pos _).le)]
    have ntl : normVec (potential (P h) bad *ᵥ suffixState U l.val h.val (V l.val *ᵥ ω))
        = (gainProd m P bad U V ω h.val / gainProd m P bad U V ω l.val) * normVec wh := by
      rw [ftl, normVec_real_smul, abs_of_nonneg
        (div_nonneg (hprod_pos _).le (hprod_pos _).le)]
    rw [ntj, nsj, ntl, nsl]
    have hjn : (gainProd m P bad U V ω j.val : ℝ) ≠ 0 := (hprod_pos _).ne'
    have hln : (gainProd m P bad U V ω l.val : ℝ) ≠ 0 := (hprod_pos _).ne'
    have hkn : (gainProd m P bad U V ω k.val : ℝ) ≠ 0 := (hprod_pos _).ne'
    have hhn : (gainProd m P bad U V ω h.val : ℝ) ≠ 0 := (hprod_pos _).ne'
    field_simp [hjn, hln, hkn, hhn, hw_ne]

end Qatlib.Concepts.QlsReadoutSpec.Amplification
