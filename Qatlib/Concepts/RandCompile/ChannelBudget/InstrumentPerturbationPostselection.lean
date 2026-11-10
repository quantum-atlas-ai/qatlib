/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Concepts.HspRecovery.SieveLaw.MixedSelectivePerturbation
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditional
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.HspRecovery.SieveLaw

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Matrix Qatlib
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator ENNReal

variable {O : Type} [Fintype O] [DecidableEq O] {D E R : ℕ}

noncomputable def cqRecord (J : Instrument O D E) :
    Operator D →ₗ[ℂ] Matrix (Fin E × O) (Fin E × O) ℂ where
  toFun ρ := fun x y => if x.2 = y.2 then J.branch x.2 ρ x.1 y.1 else 0
  map_add' ρ σ := by
    ext x y
    by_cases h : x.2 = y.2 <;> simp [h, map_add]
  map_smul' c ρ := by
    ext x y
    by_cases h : x.2 = y.2 <;> simp [h, map_smul]

noncomputable def cqFinEquiv (E : ℕ) (O : Type) [Fintype O] [DecidableEq O] :
    (Fin E × O) ≃ Fin (E * Fintype.card O) :=
  ((Equiv.refl (Fin E)).prodCongr (Fintype.equivFin O)).trans finProdFinEquiv

noncomputable def cqRecordFin (J : Instrument O D E) :
    Operator D →ₗ[ℂ] Operator (E * Fintype.card O) where
  toFun ρ := Matrix.reindex (cqFinEquiv E O) (cqFinEquiv E O) (cqRecord J ρ)
  map_add' ρ σ := by
    ext a b
    by_cases h : ((cqFinEquiv E O).symm a).2 = ((cqFinEquiv E O).symm b).2 <;>
      simp [h, map_add]
  map_smul' c ρ := by
    ext a b
    by_cases h : ((cqFinEquiv E O).symm a).2 = ((cqFinEquiv E O).symm b).2 <;>
      simp [h, map_smul]

noncomputable def tensorLeftOn {I : Type} [Fintype I]
    (T : Operator D →ₗ[ℂ] Matrix I I ℂ)
    (X : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    Matrix (I × Fin R) (I × Fin R) ℂ :=
  fun x y => T (fun i j => X (i, x.2) (j, y.2)) x.1 y.1

theorem tensorLeftOn_sub {I : Type} [Fintype I]
    (T S : Operator D →ₗ[ℂ] Matrix I I ℂ)
    (X : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeftOn (T - S) X = tensorLeftOn T X - tensorLeftOn S X := by
  ext x y
  simp [tensorLeftOn, LinearMap.sub_apply, Matrix.sub_apply]

noncomputable def cqBlock (S : Finset O)
    (M : Matrix ((Fin E × O) × Fin R) ((Fin E × O) × Fin R) ℂ) :
    Matrix (Fin E × Fin R) (Fin E × Fin R) ℂ :=
  fun x y => ∑ o ∈ S, M ((x.1, o), x.2) ((y.1, o), y.2)

theorem cqBlock_sub (S : Finset O)
    (M N : Matrix ((Fin E × O) × Fin R) ((Fin E × O) × Fin R) ℂ) :
    cqBlock S (M - N) = cqBlock S M - cqBlock S N := by
  ext x y
  simp [cqBlock, Matrix.sub_apply, Finset.sum_sub_distrib]

private theorem tensorLeft_map_sub (T S : Operator D →ₗ[ℂ] Operator E)
    (X : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (T - S) X = tensorLeft T X - tensorLeft S X := by
  ext x y
  simp [tensorLeft, LinearMap.sub_apply, Matrix.sub_apply]

theorem tensorLeft_cqRecordFin (J : Instrument O D E)
    (X : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (cqRecordFin J) X = Matrix.reindex
      ((cqFinEquiv E O).prodCongr (Equiv.refl (Fin R)))
      ((cqFinEquiv E O).prodCongr (Equiv.refl (Fin R)))
      (tensorLeftOn (cqRecord J) X) := by
  ext a b
  simp only [tensorLeft, cqRecordFin, LinearMap.coe_mk, AddHom.coe_mk, tensorLeftOn,
    cqRecord, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.coe_refl, id_eq, Prod.map_fst, Prod.map_snd]
  rfl

theorem tensorLeft_selective_eq_cqBlock (J : Instrument O D E) (S : Finset O)
    (X : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (selectiveMap J S) X = cqBlock S (tensorLeftOn (cqRecord J) X) := by
  ext x y
  simp only [tensorLeft, selectiveMap, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, cqBlock, tensorLeftOn, cqRecord, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun o _ => ?_
  simp

private noncomputable def cqLift (S : Finset O)
    (U : Matrix (Fin E × Fin R) (Fin E × Fin R) ℂ) :
    Matrix ((Fin E × O) × Fin R) ((Fin E × O) × Fin R) ℂ :=
  fun x y => if x.1.2 = y.1.2 ∧ x.1.2 ∈ S then U (x.1.1, x.2) (y.1.1, y.2) else 0

private theorem cqLift_trace (S : Finset O)
    (U : Matrix (Fin E × Fin R) (Fin E × Fin R) ℂ)
    (M : Matrix ((Fin E × O) × Fin R) ((Fin E × O) × Fin R) ℂ) :
    (cqLift S U * M).trace = (U * cqBlock S M).trace := by
  classical
  have key : ∀ (i : Fin E) (o : O) (a : Fin R) (j : Fin E),
      (∑ p : O, ∑ b : Fin R,
          (if o = p ∧ o ∈ S then U (i, a) (j, b) else 0) * M ((j, p), b) ((i, o), a))
        = ∑ b : Fin R,
            if o ∈ S then U (i, a) (j, b) * M ((j, o), b) ((i, o), a) else 0 := by
    intro i o a j
    by_cases hS : o ∈ S
    · rw [Finset.sum_eq_single o (fun p _ hpo => Finset.sum_eq_zero fun b _ => by
          rw [if_neg (fun hc => hpo hc.1.symm)]; ring)
        (fun ho => absurd (Finset.mem_univ o) ho)]
      simp [hS]
    · rw [Finset.sum_eq_zero (fun p _ => Finset.sum_eq_zero fun b _ => by
          rw [if_neg (fun hc => hS hc.2)]; ring),
        Finset.sum_eq_zero fun b _ => if_neg hS]
  have hL : (cqLift S U * M).trace
      = ∑ i : Fin E, ∑ o : O, ∑ a : Fin R, ∑ j : Fin E, ∑ b : Fin R,
          if o ∈ S then U (i, a) (j, b) * M ((j, o), b) ((i, o), a) else 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, cqLift,
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun o _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => key i o a j
  have hR : (U * cqBlock S M).trace
      = ∑ i : Fin E, ∑ a : Fin R, ∑ j : Fin E, ∑ b : Fin R, ∑ o ∈ S,
          U (i, a) (j, b) * M ((j, o), b) ((i, o), a) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, cqBlock,
      Finset.mul_sum, Fintype.sum_prod_type]
  have hsumite : ∀ (g : O → ℂ),
      (∑ o ∈ (Finset.univ : Finset O), if o ∈ S then g o else 0) = ∑ o ∈ S, g o := by
    intro g
    calc (∑ o ∈ (Finset.univ : Finset O), if o ∈ S then g o else 0)
        = ∑ o ∈ S, (if o ∈ S then g o else 0) :=
          (Finset.sum_subset (Finset.subset_univ S) (fun o _ h => if_neg h)).symm
      _ = ∑ o ∈ S, g o := Finset.sum_congr rfl fun o ho => if_pos ho
  have hcomm : ∀ (G : O → Fin R → Fin E → Fin R → ℂ) (i : Fin E),
      (∑ o ∈ S, ∑ a : Fin R, ∑ j : Fin E, ∑ b : Fin R, G o a j b)
        = (∑ a : Fin R, ∑ j : Fin E, ∑ b : Fin R, ∑ o ∈ S, G o a j b) := by
    intro G i
    calc (∑ o ∈ S, ∑ a : Fin R, ∑ j : Fin E, ∑ b : Fin R, G o a j b)
        = ∑ a : Fin R, ∑ o ∈ S, ∑ j : Fin E, ∑ b : Fin R, G o a j b :=
          Finset.sum_comm
      _ = ∑ a : Fin R, ∑ j : Fin E, ∑ o ∈ S, ∑ b : Fin R, G o a j b := by
          exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a : Fin R, ∑ j : Fin E, ∑ b : Fin R, ∑ o ∈ S, G o a j b := by
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_comm
  rw [hL, hR]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc (∑ o : O, ∑ a : Fin R, ∑ j : Fin E, ∑ b : Fin R,
          if o ∈ S then U (i, a) (j, b) * M ((j, o), b) ((i, o), a) else 0)
      = ∑ o : O, (if o ∈ S then ∑ a : Fin R, ∑ j : Fin E, ∑ b : Fin R,
            U (i, a) (j, b) * M ((j, o), b) ((i, o), a) else 0) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        by_cases ho : o ∈ S <;> simp [ho]
    _ = ∑ o ∈ S, (∑ a : Fin R, ∑ j : Fin E, ∑ b : Fin R,
          U (i, a) (j, b) * M ((j, o), b) ((i, o), a)) := hsumite _
    _ = ∑ a : Fin R, ∑ j : Fin E, ∑ b : Fin R, ∑ o ∈ S,
          U (i, a) (j, b) * M ((j, o), b) ((i, o), a) :=
          hcomm (fun o a j b => U (i, a) (j, b) * M ((j, o), b) ((i, o), a)) i

private theorem cqLift_conj_mul (S : Finset O)
    (U : Matrix (Fin E × Fin R) (Fin E × Fin R) ℂ) (hU : Uᴴ * U = 1) :
    (cqLift S U)ᴴ * cqLift S U
      = Matrix.diagonal (fun x : (Fin E × O) × Fin R => if x.1.2 ∈ S then (1 : ℂ) else 0) := by
  ext r s
  have hexp : ((cqLift S U)ᴴ * cqLift S U) r s
      = ∑ t : (Fin E × O) × Fin R,
          if t.1.2 = r.1.2 ∧ t.1.2 ∈ S ∧ t.1.2 = s.1.2
          then star (U (t.1.1, t.2) (r.1.1, r.2)) * U (t.1.1, t.2) (s.1.1, s.2) else 0 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cqLift]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h1 : t.1.2 = r.1.2 ∧ t.1.2 ∈ S
    · by_cases h2 : t.1.2 = s.1.2 ∧ t.1.2 ∈ S
      · rw [if_pos h1, if_pos h2]
        rw [if_pos (show t.1.2 = r.1.2 ∧ t.1.2 ∈ S ∧ t.1.2 = s.1.2 from
          ⟨h1.1, h1.2, h2.1⟩)]
      · rw [if_pos h1, if_neg h2]
        have hfalse : ¬(t.1.2 = r.1.2 ∧ t.1.2 ∈ S ∧ t.1.2 = s.1.2) := by
          rintro ⟨_, hB, hC⟩
          exact h2 ⟨hC, hB⟩
        rw [if_neg hfalse, mul_zero]
    · have hfalse : ¬(t.1.2 = r.1.2 ∧ t.1.2 ∈ S ∧ t.1.2 = s.1.2) := by
        rintro ⟨hA, hB, _⟩
        exact h1 ⟨hA, hB⟩
      rw [if_neg h1, if_neg hfalse]
      simp
  rw [hexp]
  by_cases hrs : r.1.2 = s.1.2
  · by_cases hS : s.1.2 ∈ S
    · have hS' : r.1.2 ∈ S := by rw [hrs]; exact hS
      have hcond : ∀ t : (Fin E × O) × Fin R,
          (t.1.2 = r.1.2 ∧ t.1.2 ∈ S ∧ t.1.2 = s.1.2) = (t.1.2 = r.1.2) := by
        intro t
        by_cases ht : t.1.2 = r.1.2
        · simp [ht, hrs, hS, hS']
        · simp [ht]
      have key2 : ∀ e : Fin E,
          (∑ o' : O, ∑ b : Fin R,
              if o' = r.1.2 then star (U (e, b) (r.1.1, r.2)) * U (e, b) (s.1.1, s.2)
              else 0)
            = ∑ b : Fin R,
                star (U (e, b) (r.1.1, r.2)) * U (e, b) (s.1.1, s.2) := by
        intro e
        rw [Finset.sum_eq_single r.1.2
          (fun o'' _ ho'' => Finset.sum_eq_zero fun b _ => if_neg ho'')
          (fun ho => absurd (Finset.mem_univ r.1.2) ho)]
        simp
      simp only [hcond, Fintype.sum_prod_type, key2]
      have hUU : (Uᴴ * U) (r.1.1, r.2) (s.1.1, s.2)
          = ∑ e : Fin E, ∑ b : Fin R,
              star (U (e, b) (r.1.1, r.2)) * U (e, b) (s.1.1, s.2) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
      rw [← hUU, hU, Matrix.one_apply, Matrix.diagonal_apply]
      by_cases hrs2 : r = s
      · subst hrs2
        simp [hS']
      · rw [if_neg hrs2]
        have hr' : ¬((r.1.1, r.2) = (s.1.1, s.2)) := by
          intro h
          apply hrs2
          have h1 : r.1.1 = s.1.1 :=
            (congrArg Prod.fst h : (r.1.1, r.2).1 = (s.1.1, s.2).1)
          have h2 : r.2 = s.2 :=
            (congrArg Prod.snd h : (r.1.1, r.2).2 = (s.1.1, s.2).2)
          exact Prod.ext (Prod.ext h1 hrs) h2
        rw [if_neg hr']
    · have hzero : ∀ t : (Fin E × O) × Fin R,
          (if t.1.2 = r.1.2 ∧ t.1.2 ∈ S ∧ t.1.2 = s.1.2
            then star (U (t.1.1, t.2) (r.1.1, r.2)) * U (t.1.1, t.2) (s.1.1, s.2) else 0)
            = 0 := by
        intro t
        by_cases ht : t.1.2 = r.1.2
        · rw [if_neg (by simp [ht, hrs, hS])]
        · rw [if_neg (by simp [ht])]
      simp only [hzero, Finset.sum_const_zero, Matrix.diagonal_apply]
      by_cases hrs2 : r = s
      · rw [if_pos hrs2]
        have hre : r.1.2 = s.1.2 := by rw [hrs2]
        rw [if_neg (by rw [hre]; exact hS)]
      · rw [if_neg hrs2]
  · have hzero : ∀ t : (Fin E × O) × Fin R,
        (if t.1.2 = r.1.2 ∧ t.1.2 ∈ S ∧ t.1.2 = s.1.2
          then star (U (t.1.1, t.2) (r.1.1, r.2)) * U (t.1.1, t.2) (s.1.1, s.2) else 0)
          = 0 := by
      intro t
      rw [if_neg (fun hc => hrs (hc.1.symm.trans hc.2.2))]
    simp only [hzero, Finset.sum_const_zero, Matrix.diagonal_apply]
    rw [if_neg (fun h => hrs (congrArg (fun q => q.1.2) h))]

theorem cqBlock_traceNorm_le (S : Finset O)
    (M : Matrix ((Fin E × O) × Fin R) ((Fin E × O) × Fin R) ℂ) :
    Matrix.traceNorm (cqBlock S M) ≤ Matrix.traceNorm M := by
  classical
  obtain ⟨U, hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U (cqBlock S M)).1
  have hunit : U.valᴴ * U.val = 1 := by
    have h := (@Matrix.mem_unitaryGroup_iff' (Fin E × Fin R)
      (fun a b => Classical.propDecidable (a = b)) _ ℂ _ _).mp U.prop
    ext i j
    have hi := congrFun (congrFun h i) j
    by_cases hij : i = j <;>
      simpa only [Matrix.star_eq_conjTranspose, Matrix.one_apply, hij, ite_true, ite_false] using hi
  have htrace := cqLift_trace S U.val M
  have hWW := cqLift_conj_mul S U.val hunit
  have hnormW : ‖cqLift S U.val‖ ≤ 1 := by
    have h1 : ‖cqLift S U.val‖ * ‖cqLift S U.val‖
        = ‖Matrix.diagonal
            (fun x : (Fin E × O) × Fin R => if x.1.2 ∈ S then (1 : ℂ) else 0)‖ := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self (cqLift S U.val), hWW]
    have h2 : ‖Matrix.diagonal
        (fun x : (Fin E × O) × Fin R => if x.1.2 ∈ S then (1 : ℂ) else 0)‖ ≤ 1 := by
      rw [Matrix.l2_opNorm_diagonal]
      have h3 : ∀ x : (Fin E × O) × Fin R,
          ‖(if x.1.2 ∈ S then (1 : ℂ) else 0)‖ ≤ 1 := by
        intro x
        by_cases hx : x.1.2 ∈ S <;> simp [hx]
      exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr h3
    nlinarith [(norm_nonneg (cqLift S U.val)), h1, h2]
  calc Matrix.traceNorm (cqBlock S M)
      = ((U.val * cqBlock S M).trace).re := hU.symm
    _ = ((cqLift S U.val * M).trace).re := by rw [htrace]
    _ ≤ |((cqLift S U.val * M).trace).re| := le_abs_self _
    _ ≤ ‖(cqLift S U.val * M).trace‖ := Complex.abs_re_le_norm _
    _ ≤ Matrix.traceNorm (cqLift S U.val * M) := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖cqLift S U.val‖ * Matrix.traceNorm M :=
        Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ 1 * Matrix.traceNorm M :=
        mul_le_mul_of_nonneg_right hnormW (Matrix.traceNorm_nonneg _)
    _ = Matrix.traceNorm M := one_mul _

theorem selectiveMap_diamond_le_cqRecordFin (J K : Instrument O D E) (S : Finset O)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm (cqRecordFin J - cqRecordFin K)
      ≤ ENNReal.ofReal ε) :
    Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm (selectiveMap J S - selectiveMap K S)
      ≤ ENNReal.ofReal ε := by
  refine (Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm_le_iff_uniform D E _ ε hε).mpr ?_
  intro r X
  have hcq := (Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm_le_iff_uniform D (E * Fintype.card O)
    (cqRecordFin J - cqRecordFin K) ε hε).mp h r X
  have hsplit : tensorLeft (selectiveMap J S - selectiveMap K S) X
      = cqBlock S (tensorLeftOn (cqRecord J - cqRecord K) X) := by
    rw [tensorLeft_map_sub, tensorLeft_selective_eq_cqBlock,
      tensorLeft_selective_eq_cqBlock, ← cqBlock_sub, ← tensorLeftOn_sub]
  have hcqeq : tensorLeft (cqRecordFin J - cqRecordFin K) X
      = Matrix.reindex ((cqFinEquiv E O).prodCongr (Equiv.refl (Fin r)))
          ((cqFinEquiv E O).prodCongr (Equiv.refl (Fin r)))
          (tensorLeftOn (cqRecord J - cqRecord K) X) := by
    rw [tensorLeft_map_sub, tensorLeft_cqRecordFin, tensorLeft_cqRecordFin, tensorLeftOn_sub]
    rfl
  rw [hsplit]
  calc Matrix.traceNorm (cqBlock S (tensorLeftOn (cqRecord J - cqRecord K) X))
      ≤ Matrix.traceNorm (tensorLeftOn (cqRecord J - cqRecord K) X) :=
        cqBlock_traceNorm_le S _
    _ = Matrix.traceNorm (tensorLeft (cqRecordFin J - cqRecordFin K) X) := by
        rw [hcqeq]
        exact (Qatlib.Concepts.SchattenDiamond.DiamondNorm.diamond_traceNorm_reindex
          ((cqFinEquiv E O).prodCongr (Equiv.refl (Fin r)))
          (tensorLeftOn (cqRecord J - cqRecord K) X)).symm
    _ ≤ ε * Matrix.traceNorm X := hcq

theorem selectiveBranch_error_of_cqDiamond (J K : Instrument O D E) (S : Finset O)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm (cqRecordFin J - cqRecordFin K)
      ≤ ENNReal.ofReal ε) :
    ∀ (R : ℕ) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
      Matrix.traceNorm (tensorLeft (selectiveMap J S - selectiveMap K S) ρ)
        ≤ ε * Matrix.traceNorm ρ := by
  intro R ρ
  have hd := selectiveMap_diamond_le_cqRecordFin J K S hε h
  exact (Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm_le_iff_uniform D E _ ε hε).mp hd R ρ

theorem frontier1 :
    ∀ (O : Type) [Fintype O] [DecidableEq O] (D E R : ℕ) (J K : Instrument O D E)
      (S : Finset O) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) (p ε : ℝ),
      0 ≤ ε → 0 < p → ε < p / 2 → ρ.PosSemidef → Matrix.traceNorm ρ ≤ 1 →
      p ≤ (Matrix.trace (tensorLeft (selectiveMap K S) ρ)).re →
      Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm (cqRecordFin J - cqRecordFin K)
        ≤ ENNReal.ofReal ε →
      Matrix.traceNorm (tensorLeft (selectiveMap J S) ρ
        - tensorLeft (selectiveMap K S) ρ) ≤ ε ∧
      Matrix.traceNorm (tensorLeft (selectiveMap J (Finset.univ \ S)) ρ
        - tensorLeft (selectiveMap K (Finset.univ \ S)) ρ) ≤ ε ∧
      |(Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
        - (Matrix.trace (tensorLeft (selectiveMap K S) ρ)).re| ≤ ε ∧
      0 < (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re ∧
      Matrix.traceNorm (normalizedPositiveBranch (tensorLeft (selectiveMap J S) ρ)
          - normalizedPositiveBranch (tensorLeft (selectiveMap K S) ρ)) ≤ 2 * ε / p := by
  intro O _ _ D E R J K S ρ p ε hε hp hεp hρ hρn hmass hdia
  have hbS := selectiveBranch_error_of_cqDiamond J K S hε hdia R ρ
  have hbF := selectiveBranch_error_of_cqDiamond J K (Finset.univ \ S) hε hdia R ρ
  have hS : Matrix.traceNorm (tensorLeft (selectiveMap J S) ρ
        - tensorLeft (selectiveMap K S) ρ) ≤ ε := by
    rw [← tensorLeft_map_sub _ _ ρ]
    exact (hbS.trans (mul_le_mul_of_nonneg_left hρn hε)).trans_eq (mul_one ε)
  have hF : Matrix.traceNorm (tensorLeft (selectiveMap J (Finset.univ \ S)) ρ
        - tensorLeft (selectiveMap K (Finset.univ \ S)) ρ) ≤ ε := by
    rw [← tensorLeft_map_sub _ _ ρ]
    exact (hbF.trans (mul_le_mul_of_nonneg_left hρn hε)).trans_eq (mul_one ε)
  have hposσ : (tensorLeft (selectiveMap J S) ρ).PosSemidef :=
    tensorLeft_posSemidef (selectiveMap_cp J S) hρ
  have hposτ : (tensorLeft (selectiveMap K S) ρ).PosSemidef :=
    tensorLeft_posSemidef (selectiveMap_cp K S) hρ
  obtain ⟨hmassdiff, _, hnormpart⟩ := positive_selected_output_mass_and_normalization_stability
    (Fin E × Fin R) (tensorLeft (selectiveMap J S) ρ) (tensorLeft (selectiveMap K S) ρ) ε
    hposσ hposτ hε hS
  have hmassτpos : 0 < (Matrix.trace (tensorLeft (selectiveMap K S) ρ)).re :=
    lt_of_lt_of_le hp hmass
  have hηlt : ε < (Matrix.trace (tensorLeft (selectiveMap K S) ρ)).re := by
    have h2 : p / 2 ≤ (Matrix.trace (tensorLeft (selectiveMap K S) ρ)).re / 2 :=
      div_le_div_of_nonneg_right hmass (by norm_num)
    have h3 : (Matrix.trace (tensorLeft (selectiveMap K S) ρ)).re / 2
        < (Matrix.trace (tensorLeft (selectiveMap K S) ρ)).re :=
      half_lt_self hmassτpos
    linarith
  obtain ⟨hposmassJ, hnormbound⟩ := hnormpart hηlt
  refine ⟨hS, hF, hmassdiff, hposmassJ, ?_⟩
  exact hnormbound.trans
    (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hε) hp hmass)

theorem selectiveOnly_with_failure_certificate (J K : Instrument O D E) (S : Finset O)
    (εs εf : ℝ) (h0s : 0 ≤ εs) (h0f : 0 ≤ εf)
    (hs : Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm (selectiveMap J S - selectiveMap K S)
      ≤ ENNReal.ofReal εs)
    (hf : Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm (selectiveMap J (Finset.univ \ S)
        - selectiveMap K (Finset.univ \ S)) ≤ ENNReal.ofReal εf) :
    ∀ (R : ℕ) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
      ρ.PosSemidef → Matrix.traceNorm ρ ≤ 1 →
      Matrix.traceNorm (tensorLeft (selectiveMap J S) ρ
        - tensorLeft (selectiveMap K S) ρ) ≤ εs ∧
      Matrix.traceNorm (tensorLeft (selectiveMap J (Finset.univ \ S)) ρ
        - tensorLeft (selectiveMap K (Finset.univ \ S)) ρ) ≤ εf := by
  intro R ρ hρ hρn
  have e1 :=
      (Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm_le_iff_uniform D E _ εs h0s).mp hs R ρ
  have e2 :=
      (Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm_le_iff_uniform D E _ εf h0f).mp hf R ρ
  constructor
  · rw [← tensorLeft_map_sub _ _ ρ]
    exact (e1.trans (mul_le_mul_of_nonneg_left hρn h0s)).trans_eq (mul_one εs)
  · rw [← tensorLeft_map_sub _ _ ρ]
    exact (e2.trans (mul_le_mul_of_nonneg_left hρn h0f)).trans_eq (mul_one εf)

def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem pauliX_conjTranspose_self : pauliXᴴ = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]

theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

noncomputable def halfAmp : ℝ := (Real.sqrt 2)⁻¹

theorem halfAmp_sq : halfAmp * halfAmp = 1 / 2 := by
  rw [halfAmp, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem halfAmp_sq_complex : (halfAmp : ℂ) * (halfAmp : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, halfAmp_sq]

private theorem conj_ofReal_mul_self (c : ℝ) :
    star ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = ((c * c : ℝ) : ℂ) := by
  rw [show star ((c : ℝ) : ℂ) = (starRingEnd ℂ) ((c : ℝ) : ℂ) from rfl,
    Complex.conj_ofReal, ← Complex.ofReal_mul]

private theorem ofReal_mul_star_self (c : ℝ) :
    ((c : ℝ) : ℂ) * star ((c : ℝ) : ℂ) = ((c * c : ℝ) : ℂ) := by
  rw [show star ((c : ℝ) : ℂ) = (starRingEnd ℂ) ((c : ℝ) : ℂ) from rfl,
    Complex.conj_ofReal, ← Complex.ofReal_mul]

private theorem conj_smul_one_mul {n : ℕ} (c : ℝ) :
    (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * ((c : ℝ) : ℂ) • 1
      = ((c * c : ℝ) : ℂ) • 1 := by
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_mul_assoc,
    Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, conj_ofReal_mul_self]

private theorem conj_smul_pauli_mul (c : ℝ) :
    (((c : ℝ) : ℂ) • pauliX)ᴴ * ((c : ℝ) : ℂ) • pauliX = ((c * c : ℝ) : ℂ) • 1 := by
  simp only [Matrix.conjTranspose_smul, pauliX_conjTranspose_self, smul_mul_assoc,
    Matrix.mul_smul, smul_smul, pauliX_mul_self, conj_ofReal_mul_self]

theorem conjBranch_smul_one (c : ℝ) (ρ : Operator D) :
    conjBranch (((c : ℝ) : ℂ) • 1) ρ = ((c * c : ℝ) : ℂ) • ρ := by
  simp only [conjBranch_apply, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    smul_mul_assoc, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, ofReal_mul_star_self]

theorem conjBranch_smul_pauli (c : ℝ) (ρ : Operator 2) :
    conjBranch (((c : ℝ) : ℂ) • pauliX) ρ
      = ((c * c : ℝ) : ℂ) • (pauliX * ρ * pauliXᴴ) := by
  simp only [conjBranch_apply, Matrix.conjTranspose_smul, smul_mul_assoc,
    Matrix.mul_smul, smul_smul, ofReal_mul_star_self]

def witnessS : Finset (Fin 2) := {0}

def witnessRho : Operator 2 :=
  Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)

noncomputable def witnessJ : Instrument (Fin 2) 2 2 :=
  Instrument.ofKraus (fun _ => (halfAmp : ℂ) • 1)
    (by
      have e0 : (((halfAmp : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
          * ((halfAmp : ℝ) : ℂ) • 1 = ((1 / 2 : ℝ) : ℂ) • 1 := by
        rw [conj_smul_one_mul, halfAmp_sq]
      rw [Fin.sum_univ_two]
      simp only [e0, ← add_smul, ← Complex.ofReal_add]
      rw [show ((1 / 2 : ℝ) + 1 / 2) = 1 by norm_num, Complex.ofReal_one, one_smul])

theorem witnessJ_branch (b : Fin 2) (ρ : Operator 2) :
    witnessJ.branch b ρ = ((halfAmp : ℂ) • 1) * ρ * (((halfAmp : ℂ) • 1))ᴴ := rfl

noncomputable def witnessK : Instrument (Fin 2) 2 2 :=
  Instrument.ofKraus
    (fun b => if b = 0 then (halfAmp : ℂ) • 1 else (halfAmp : ℂ) • pauliX)
    (by
      have e0 : (((halfAmp : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
          * ((halfAmp : ℝ) : ℂ) • 1 = ((1 / 2 : ℝ) : ℂ) • 1 := by
        rw [conj_smul_one_mul, halfAmp_sq]
      have e1 : (((halfAmp : ℝ) : ℂ) • pauliX)ᴴ
          * ((halfAmp : ℝ) : ℂ) • pauliX = ((1 / 2 : ℝ) : ℂ) • 1 := by
        rw [conj_smul_pauli_mul, halfAmp_sq]
      simp only [Fin.sum_univ_two, if_true, (by decide : ¬((1 : Fin 2) = 0)),
        if_false, e0, e1, ← add_smul, ← Complex.ofReal_add]
      rw [show ((1 / 2 : ℝ) + 1 / 2) = 1 by norm_num, Complex.ofReal_one, one_smul])

theorem witnessK_branch (b : Fin 2) (ρ : Operator 2) :
    witnessK.branch b ρ
      = (if b = 0 then (halfAmp : ℂ) • 1 else (halfAmp : ℂ) • pauliX) * ρ
        * ((if b = 0 then (halfAmp : ℂ) • 1 else (halfAmp : ℂ) • pauliX))ᴴ := rfl

theorem selectiveOnly_no_free_failure_witness :
    selectiveMap witnessJ witnessS = selectiveMap witnessK witnessS ∧
    1 ≤ Matrix.traceNorm
      (Qatlib.Concepts.MbqcFlow.FlowDecision.selectedBranch witnessJ (Finset.univ \ witnessS) witnessRho
        - Qatlib.Concepts.MbqcFlow.FlowDecision.selectedBranch witnessK (Finset.univ \ witnessS)
            witnessRho) := by
  constructor
  · have hJ : ∀ ρ : Operator 2, (selectiveMap witnessJ witnessS) ρ
        = conjBranch ((halfAmp : ℂ) • 1) ρ := by
      intro ρ
      simp only [selectiveMap, LinearMap.sum_apply, witnessS, Finset.sum_singleton,
        witnessJ_branch]
      rfl
    have hK : ∀ ρ : Operator 2, (selectiveMap witnessK witnessS) ρ
        = conjBranch ((halfAmp : ℂ) • 1) ρ := by
      intro ρ
      simp only [selectiveMap, LinearMap.sum_apply, witnessS, Finset.sum_singleton,
        witnessK_branch, if_pos]
      rfl
    exact LinearMap.ext fun ρ => (hJ ρ).trans (hK ρ).symm
  · have hset : Finset.univ \ witnessS = ({1} : Finset (Fin 2)) := by
      ext b
      fin_cases b <;> simp [witnessS, Finset.mem_sdiff]
    have hX : pauliX * witnessRho * pauliXᴴ
        = Matrix.diagonal (fun i : Fin 2 => if i = 1 then (1 : ℂ) else 0) := by
      rw [pauliX_conjTranspose_self]
      have h1 : pauliX * witnessRho
          = (Matrix.of ![![0, 0], ![1, 0]] : Matrix (Fin 2) (Fin 2) ℂ) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [pauliX, witnessRho, Matrix.mul_apply, Matrix.diagonal_apply,
            Matrix.of_apply, Fin.sum_univ_two]
      rw [h1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pauliX, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply,
          Fin.sum_univ_two]
    have hJ1 : Qatlib.Concepts.MbqcFlow.FlowDecision.selectedBranch witnessJ ({1} : Finset (Fin 2))
        witnessRho = ((1 / 2 : ℝ) : ℂ) • witnessRho := by
      simp only [Qatlib.Concepts.MbqcFlow.FlowDecision.selectedBranch, Finset.sum_singleton,
        witnessJ_branch, ← conjBranch_apply]
      rw [conjBranch_smul_one, halfAmp_sq]
    have hK1 : Qatlib.Concepts.MbqcFlow.FlowDecision.selectedBranch witnessK ({1} : Finset (Fin 2))
        witnessRho = ((1 / 2 : ℝ) : ℂ) • (pauliX * witnessRho * pauliXᴴ) := by
      simp only [Qatlib.Concepts.MbqcFlow.FlowDecision.selectedBranch, Finset.sum_singleton,
        witnessK_branch, if_neg (by decide : ¬((1 : Fin 2) = 0))]
      rw [← conjBranch_apply, conjBranch_smul_pauli, halfAmp_sq]
    rw [hset, hJ1, hK1, hX]
    have hdiff :
        (((1 / 2 : ℝ) : ℂ) • witnessRho
            - ((1 / 2 : ℝ) : ℂ)
              • Matrix.diagonal (fun i : Fin 2 => if i = 1 then (1 : ℂ) else 0))
      = Matrix.diagonal
          (fun i : Fin 2 => if i = 0 then ((1 / 2 : ℝ) : ℂ) else -((1 / 2 : ℝ) : ℂ)) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [witnessRho, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          Matrix.diagonal_apply]
    rw [hdiff]
    refine (Matrix.traceNorm_eq_max_re_tr_U
      (Matrix.diagonal
        (fun i : Fin 2 => if i = 0 then ((1 / 2 : ℝ) : ℂ)
          else -((1 / 2 : ℝ) : ℂ)))).2 ?_
    refine ⟨⟨Matrix.diagonal (fun i => if i = 0 then (1 : ℂ) else -1), ?_⟩, ?_⟩
    · refine (@Matrix.mem_unitaryGroup_iff' (Fin 2)
        (fun a b => Classical.propDecidable (a = b)) _ ℂ _ _ _).mpr ?_
      rw [Matrix.star_eq_conjTranspose]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.one_apply, Fin.sum_univ_two]
    · have hVD : (Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℂ) else -1)) *
            (Matrix.diagonal (fun i : Fin 2 => if i = 0 then ((1 / 2 : ℝ) : ℂ)
              else -((1 / 2 : ℝ) : ℂ)))
            = Matrix.diagonal (fun i : Fin 2 => if i = 0 then ((1 / 2 : ℝ) : ℂ)
              else ((1 / 2 : ℝ) : ℂ)) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_two]
      rw [hVD, Matrix.trace_diagonal, Fin.sum_univ_two]
      simp only [(by decide : (0 : Fin 2) = 0), (by decide : ¬((1 : Fin 2) = 0)),
        if_true, if_false, Complex.add_re, Complex.ofReal_re]
      norm_num

end Qatlib.Concepts.RandCompile.ChannelBudget
