/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryDefs
import Mathlib.Algebra.Order.Floor.Semiring
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitCompile
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedRelabel
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPairedExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitMixed
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuitTransport
import Qatlib.Concepts.AdversaryBounds.AdvDuality.VariableKrausStatistics
import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachinePrefix
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryFourBitWitness
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversarySdpDuality
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal ComplexConjugate
open Qatlib
open Qatlib


open Qatlib.Concepts.AdversaryBounds.OptimizedAdv
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
variable {n q : ℕ} [NeZero q] {W H : Type}
variable {n q : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {n q d s : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {d : ℕ}
variable {X K : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
variable {X K : Type} [Fintype X] [Fintype K] [DecidableEq K]
variable [DecidableEq X]
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.SdpDuality.StrongDuality
open scoped InnerProductSpace
open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
noncomputable section
omit [Fintype X] in

theorem spectralDomainEmbedding_gram (e : X → Y) (he : Function.Injective e) :
    (spectralDomainEmbedding e)ᴴ * spectralDomainEmbedding e = 1 := by
  classical
  ext x x'
  simp [spectralDomainEmbedding,Matrix.mul_apply,Matrix.conjTranspose_apply,he.eq_iff,Matrix.one_apply]
end
noncomputable section

theorem spectralDomainEmbedding_norm_le (e : X → Y) (he : Function.Injective e) :
    ‖spectralDomainEmbedding e‖ ≤ 1 := by
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self (spectralDomainEmbedding e)
  rw [spectralDomainEmbedding_gram e he] at hh
  have hn := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_one_le (I := X)
  nlinarith [norm_nonneg (spectralDomainEmbedding e)]
end
noncomputable section

theorem spectralDomainEmbedding_norm (e : X → Y) (he : Function.Injective e) (G : Matrix X X ℂ) :
    ‖spectralDomainEmbedding e*G*(spectralDomainEmbedding e)ᴴ‖ = ‖G‖ := by
  have hn := spectralDomainEmbedding_norm_le e he
  have hid : (spectralDomainEmbedding e)ᴴ *
      (spectralDomainEmbedding e*G*(spectralDomainEmbedding e)ᴴ) * spectralDomainEmbedding e = G := by
    calc
      _ = ((spectralDomainEmbedding e)ᴴ*spectralDomainEmbedding e) * G *
          ((spectralDomainEmbedding e)ᴴ*spectralDomainEmbedding e) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [spectralDomainEmbedding_gram e he]; simp
  have hb (A : Matrix X X ℂ) : ‖spectralDomainEmbedding e*A*(spectralDomainEmbedding e)ᴴ‖ ≤ ‖A‖ := by
    calc
      _ ≤ (‖spectralDomainEmbedding e‖*‖A‖)*‖(spectralDomainEmbedding e)ᴴ‖ :=
        (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ (1*‖A‖)*1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
      _ = _ := by ring
  apply le_antisymm (hb G)
  calc
    ‖G‖ = ‖(spectralDomainEmbedding e)ᴴ *
        (spectralDomainEmbedding e*G*(spectralDomainEmbedding e)ᴴ) * spectralDomainEmbedding e‖ := by rw [hid]
    _ ≤ (‖(spectralDomainEmbedding e)ᴴ‖*‖spectralDomainEmbedding e*G*(spectralDomainEmbedding e)ᴴ‖)*
        ‖spectralDomainEmbedding e‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*‖spectralDomainEmbedding e*G*(spectralDomainEmbedding e)ᴴ‖)*1 := by
      rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = _ := by ring
end
noncomputable section
omit [DecidableEq X] [Fintype Y] in

theorem spectralDomainEmbedding_filter {K : Type} (e : X → Y)
    (inputX : X → K → Bool) (inputY : Y → K → Bool) (hi : ∀ x, inputY (e x)=inputX x)
    (G : Matrix X X ℂ) (i : K) :
    genAdvFilter inputY (spectralDomainEmbedding e*G*(spectralDomainEmbedding e)ᴴ) i =
      spectralDomainEmbedding e * genAdvFilter inputX G i * (spectralDomainEmbedding e)ᴴ := by
  classical
  ext u v
  by_cases hd : inputY u i ≠ inputY v i
  · simp only [genAdvFilter,if_pos hd,Matrix.mul_apply,Finset.sum_mul,Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : e x=u <;> by_cases hy : e y=v
    · have hh : inputX x i ≠ inputX y i := by
        rw [← congrFun (hi x) i,← congrFun (hi y) i,hx,hy]
        exact hd
      simp [spectralDomainEmbedding,hx,hy,hh]
    all_goals simp [spectralDomainEmbedding,hx,hy]
  · simp only [genAdvFilter,if_neg hd,Matrix.mul_apply,Finset.sum_mul,Matrix.conjTranspose_apply]
    symm
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : e x=u <;> by_cases hy : e y=v
    · have hh : inputX x i = inputX y i := by
        rw [← congrFun (hi x) i,← congrFun (hi y) i,hx,hy]
        exact not_ne_iff.mp hd
      simp [spectralDomainEmbedding,hx,hy,hh]
    all_goals simp [spectralDomainEmbedding,hx,hy]
end
noncomputable section

theorem norm_submatrix_equiv (e : X ≃ Y) (G : Matrix Y Y ℂ) : ‖G.submatrix e e‖ = ‖G‖ := by
  have he : spectralDomainEmbedding e.symm*G*(spectralDomainEmbedding e.symm)ᴴ = G.submatrix e e := by
    ext x z
    simp [spectralDomainEmbedding,Matrix.mul_apply,Matrix.conjTranspose_apply,Equiv.symm_apply_eq]
  rw [← he]
  exact spectralDomainEmbedding_norm e.symm e.symm.injective G
end
noncomputable section

theorem forceAll_some {n : ℕ} (b : Fin n → Bool) : forceAll (fun i => some (b i)) = some b := by
  simp [forceAll]
end
noncomputable section

theorem iterateFlat_total {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) (w : Fin (n^d) → Bool) :
    iterateFlat (fun u => some (f u)) d w = some (iterateTotal f d w) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hh : iterateFlat (fun u => some (f u)) (d+1) w =
        some (f (fun i => iterateTotal f d (fun j => w ((powIndexSplit n d).symm (j,i))))) := by
      simp only [iterateFlat,ih]
      rw [forceAll_some]
      rfl
    have he : iterateTotal f (d+1) w =
        f (fun i => iterateTotal f d (fun j => w ((powIndexSplit n d).symm (j,i)))) := by
      unfold iterateTotal
      rw [hh]
      rfl
    exact hh.trans (congrArg some he.symm)
end
noncomputable section

theorem iterateTotal_succ {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) (w : Fin (n^(d+1)) → Bool) :
    iterateTotal f (d+1) w = f (fun i => iterateTotal f d (iteratedWordSplit n d w i)) := by
  unfold iterateTotal
  change ((forceAll (fun i => iterateFlat (fun u => some (f u)) d (iteratedWordSplit n d w i))) >>= _).getD false = _
  simp_rw [iterateFlat_total]
  rw [forceAll_some]
  rfl
end
noncomputable section

theorem booleanQueryGamma_hermitian : booleanQueryGamma.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  cases x <;> cases y <;> norm_num [booleanQueryGamma]
end
noncomputable section

theorem booleanQueryGamma_norm : ‖booleanQueryGamma‖ = 1 := by
  have hu : booleanQueryGammaᴴ * booleanQueryGamma = 1 := by
    ext x y
    cases x <;> cases y <;>
      norm_num [booleanQueryGamma,Matrix.mul_apply,Fintype.sum_bool,Matrix.conjTranspose_apply]
  have hn := Matrix.l2_opNorm_conjTranspose_mul_self booleanQueryGamma
  rw [hu,norm_one] at hn
  nlinarith [norm_nonneg booleanQueryGamma]
end
noncomputable section

theorem zeroDepthGamma_facts {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (zeroDepthGamma n).IsHermitian ∧ ‖zeroDepthGamma n‖ = 1 ∧
    (∀ x y, iterateTotal f 0 x = iterateTotal f 0 y → zeroDepthGamma n x y = 0) ∧
    (∀ i, ‖genAdvFilter (fun w : Fin (n^0) → Bool => w) (zeroDepthGamma n) i‖ ≤ 1) := by
  refine ⟨booleanQueryGamma_hermitian.submatrix _,?_,?_,?_⟩
  · rw [zeroDepthGamma,norm_submatrix_equiv,booleanQueryGamma_norm]
  · intro x y hxy
    change (if x 0 ≠ y 0 then (1 : ℂ) else 0) = 0
    have he : x 0 = y 0 := hxy
    rw [if_neg (not_not.mpr he)]
  · intro i
    have hi : i=0 := Fin.eq_zero i
    subst i
    have he : genAdvFilter (fun w : Fin (n^0) → Bool => w) (zeroDepthGamma n) 0 = zeroDepthGamma n := by
      ext x y
      change (if x 0 ≠ y 0 then (if x 0 ≠ y 0 then (1 : ℂ) else 0) else 0) =
        if x 0 ≠ y 0 then 1 else 0
      split_ifs <;> rfl
    rw [he,zeroDepthGamma,norm_submatrix_equiv,booleanQueryGamma_norm]
end
noncomputable section

theorem genAdvFilter_complex_real_smul {X K : Type} (input : X → K → Bool)
    (G : Matrix X X ℂ) (t : ℝ) (i : K) :
    genAdvFilter input (t • G) i = t • genAdvFilter input G i := by
  ext x y
  change (if input x i ≠ input y i then t • G x y else 0) = t •
      (if input x i ≠ input y i then G x y else 0)
  split_ifs <;> simp_all only [smul_zero]
end
noncomputable section

theorem iteratedWordSplit_filter {n d : ℕ}
    (G : Matrix (Fin n → (Fin (n^d) → Bool)) (Fin n → (Fin (n^d) → Bool)) ℂ)
    (q : Fin (n^(d+1))) :
    genAdvFilter (fun w : Fin (n^(d+1)) → Bool => w)
      (G.submatrix (iteratedWordSplit n d) (iteratedWordSplit n d)) q =
    (weightedAdvFilter (weightedAdvInput (fun (_ : Fin n) (w : Fin (n^d) → Bool) => w)) G
      ⟨((powIndexSplit n d) q).2,((powIndexSplit n d) q).1⟩).submatrix
        (iteratedWordSplit n d) (iteratedWordSplit n d) := by
  ext x y
  change (if x q ≠ y q then G (iteratedWordSplit n d x) (iteratedWordSplit n d y) else 0) =
    (if x ((powIndexSplit n d).symm ((powIndexSplit n d) q)) ≠
        y ((powIndexSplit n d).symm ((powIndexSplit n d) q)) then
      G (iteratedWordSplit n d x) (iteratedWordSplit n d y) else 0)
  rw [Equiv.symm_apply_apply]
end
noncomputable section

theorem iteratedAdversaryStep_facts {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hA : A.IsHermitian) (hzA : ∀ x y, f x=f y → A x y=0)
    (hfA : ∀ i, ‖genAdvFilter (fun w : Fin n → Bool => w) A i‖ ≤ 1)
    (d : ℕ) (B : Matrix (Fin (n^d) → Bool) (Fin (n^d) → Bool) ℂ)
    (hB : B.IsHermitian) (hzB : ∀ x y, iterateTotal f d x=iterateTotal f d y → B x y=0)
    (hfB : ∀ i, ‖genAdvFilter (fun w : Fin (n^d) → Bool => w) B i‖ ≤ 1)
    (hBN : 0 < ‖B‖) :
    (iteratedAdversaryStep f A d B).IsHermitian ∧
    (∀ x y, iterateTotal f (d+1) x=iterateTotal f (d+1) y → iteratedAdversaryStep f A d B x y=0) ∧
    ‖iteratedAdversaryStep f A d B‖ = ‖A‖*‖B‖ ∧
    (∀ i, ‖genAdvFilter (fun w : Fin (n^(d+1)) → Bool => w) (iteratedAdversaryStep f A d B) i‖ ≤ 1) := by
  let C := weightedAdvGamma (fun (_ : Fin n) => iterateTotal f d) f A (fun _ => B)
  let c : ℝ := (‖B‖^(n-1))⁻¹
  have hc : 0 < c := inv_pos.mpr (pow_pos hBN _)
  have hC : C.IsHermitian := weightedAdvGamma_isHermitian _ _ _ _ hA (fun _ => hB)
  have hCn : ‖C‖ = ‖A‖*‖B‖^n := by
    simpa only [C,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using!
      weightedAdvGamma_norm_eq (fun (_ : Fin n) => iterateTotal f d) f A (fun _ => B) hA (fun _ => hB) (fun _ => hzB)
  have hpow : ‖B‖^n = ‖B‖^(n-1)*‖B‖ := by
    have he : n-1+1=n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
    simpa only [he] using! (pow_succ ‖B‖ (n-1))
  refine ⟨(hC.submatrix _).smul (show IsSelfAdjoint c by simp [IsSelfAdjoint]),?_,?_,?_⟩
  · intro x y hxy
    change c • C (iteratedWordSplit n d x) (iteratedWordSplit n d y) = 0
    have hz := weightedAdvGamma_same_output_zero (fun (_ : Fin n) => iterateTotal f d) f A (fun _ => B)
      hzA (iteratedWordSplit n d x) (iteratedWordSplit n d y)
    have he : f (fun i => iterateTotal f d (iteratedWordSplit n d x i)) =
        f (fun i => iterateTotal f d (iteratedWordSplit n d y i)) := by
      simpa only [iterateTotal_succ] using! hxy
    have hzero : C (iteratedWordSplit n d x) (iteratedWordSplit n d y) = 0 := hz he
    rw [hzero,smul_zero]
  · change ‖c • C.submatrix (iteratedWordSplit n d) (iteratedWordSplit n d)‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc,norm_submatrix_equiv,hCn,hpow]
    dsimp only [c]
    field_simp [pow_ne_zero _ hBN.ne']
  · intro q
    change ‖genAdvFilter (fun w : Fin (n^(d+1)) → Bool => w)
      (c • C.submatrix (iteratedWordSplit n d) (iteratedWordSplit n d)) q‖ ≤ 1
    rw [genAdvFilter_complex_real_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hc,
      iteratedWordSplit_filter,norm_submatrix_equiv]
    let p := ((powIndexSplit n d) q).2
    let j := ((powIndexSplit n d) q).1
    have hh := weightedAdvGamma_filter_norm_eq (fun (_ : Fin n) => iterateTotal f d) f A (fun _ => B)
      (fun (_ : Fin n) (w : Fin (n^d) → Bool) => w) hA (fun _ => hB) hzA (fun _ => hzB) p j
    have he : (∏ i ∈ Finset.univ.erase p, ‖B‖) = ‖B‖^(n-1) := by
      simp only [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,Fintype.card_fin]
    change c * ‖weightedAdvFilter
        (weightedAdvInput (fun (_ : Fin n) (w : Fin (n^d) → Bool) => w)) C ⟨p,j⟩‖ ≤ 1
    rw [hh,he]
    have hfa : ‖advFilter id A p‖ ≤ 1 := hfA p
    have hfb : ‖advFilter (fun w : Fin (n^d) → Bool => w) B j‖ ≤ 1 := hfB j
    have hb : ‖advFilter id A p‖*‖advFilter (fun w : Fin (n^d) → Bool => w) B j‖ ≤ 1 := by
      simpa only [mul_one] using! mul_le_mul hfa hfb (norm_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)
    calc
      c*(‖advFilter id A p‖*‖advFilter (fun w : Fin (n^d) → Bool => w) B j‖*‖B‖^(n-1)) ≤
          c*(1*‖B‖^(n-1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg _) _)) hc.le
      _ = 1 := by dsimp only [c]; field_simp
end
noncomputable section

theorem iteratedAdversaryGamma_facts {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hA : A.IsHermitian) (hzA : ∀ x y, f x=f y → A x y=0)
    (hfA : ∀ i, ‖genAdvFilter (fun w : Fin n → Bool => w) A i‖ ≤ 1)
    (hAN : 0 < ‖A‖) (d : ℕ) :
    (iteratedAdversaryGamma f A d).IsHermitian ∧
    (∀ x y, iterateTotal f d x=iterateTotal f d y → iteratedAdversaryGamma f A d x y=0) ∧
    ‖iteratedAdversaryGamma f A d‖ = ‖A‖^d ∧
    (∀ i, ‖genAdvFilter (fun w : Fin (n^d) → Bool => w) (iteratedAdversaryGamma f A d) i‖ ≤ 1) := by
  induction d with
  | zero =>
    have h := zeroDepthGamma_facts f
    exact ⟨h.1,h.2.2.1,h.2.1.trans (pow_zero ‖A‖).symm,h.2.2.2⟩
  | succ d ih =>
    have hBN : 0 < ‖iteratedAdversaryGamma f A d‖ := by rw [ih.2.2.1]; exact pow_pos hAN d
    have hh := iteratedAdversaryStep_facts hn f A hA hzA hfA d (iteratedAdversaryGamma f A d)
      ih.1 ih.2.1 ih.2.2.2 hBN
    refine ⟨hh.1,hh.2.1,?_,hh.2.2.2⟩
    rw [iteratedAdversaryGamma,hh.2.2.1,ih.2.2.1,pow_succ]
    ring
end
noncomputable section

theorem normalized_adversary_le_source {X K : Type} [Fintype X] [DecidableEq X]
    [Fintype K] [Nonempty K] (input : X → K → Bool) (f : X → Bool)
    (G : Matrix X X ℂ) (hG : G.IsHermitian) (hz : ∀ x y, f x=f y → G x y=0)
    (hN : 0 < ‖G‖) (hf : ∀ i, ‖genAdvFilter input G i‖ ≤ 1) :
    ENNReal.ofReal ‖G‖ ≤ advPmValue input f := by
  have hm : maxFilterNorm input G ≤ 1 := ciSup_le hf
  have hval : ENNReal.ofReal ‖G‖ ≤ advPmWitnessValue input G := by
    unfold advPmWitnessValue
    by_cases he : maxFilterNorm input G=0
    · rw [he,ENNReal.ofReal_zero,ENNReal.div_zero (ENNReal.ofReal_ne_zero_iff.mpr hN)]
      exact le_top
    · have hd : 0 < maxFilterNorm input G := lt_of_le_of_ne (maxFilterNorm_nonneg input G) (Ne.symm he)
      rw [← ENNReal.ofReal_div_of_pos hd]
      apply ENNReal.ofReal_le_ofReal
      exact (le_div_iff₀ hd).mpr (mul_le_of_le_one_right hN.le hm)
  exact hval.trans (le_iSup_of_le ⟨G,hG,hz,norm_pos_iff.mp hN⟩ le_rfl)
end
noncomputable section

theorem iteratedAdversaryGamma_source_bound {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hA : A.IsHermitian) (hzA : ∀ x y, f x=f y → A x y=0)
    (hfA : ∀ i, ‖genAdvFilter (fun w : Fin n → Bool => w) A i‖ ≤ 1)
    (hAN : 0 < ‖A‖) (d : ℕ) :
    ENNReal.ofReal (‖A‖^d) ≤ advPmValue (fun w : Fin (n^d) → Bool => w) (iterateTotal f d) := by
  letI : NeZero (n^d) := ⟨pow_ne_zero _ (Nat.ne_zero_of_lt hn)⟩
  have hh := iteratedAdversaryGamma_facts hn f A hA hzA hfA hAN d
  have hN : 0 < ‖iteratedAdversaryGamma f A d‖ := by rw [hh.2.2.1]; exact pow_pos hAN d
  have hb := normalized_adversary_le_source (fun w : Fin (n^d) → Bool => w) (iterateTotal f d)
    (iteratedAdversaryGamma f A d) hh.1 hh.2.1 hN hh.2.2.2
  rwa [hh.2.2.1] at hb
end
noncomputable section

theorem word_adversary_maxFilter_pos {n : ℕ} (f : (Fin n → Bool) → Bool)
    (G : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hz : ∀ x y, f x=f y → G x y=0) (hne : G≠0) : 0 < maxFilterNorm (fun w : Fin n → Bool => w) G := by
  obtain ⟨x,y,hxy⟩ : ∃ x y, G x y ≠ 0 := by
    by_contra h
    apply hne
    ext x y
    exact not_not.mp (not_exists.mp (not_exists.mp h x) y)
  have hneq : x≠y := fun he => hxy (hz x y (congrArg f he))
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hneq
  have hh : genAdvFilter (fun w : Fin n → Bool => w) G i ≠ 0 := by
    intro he
    have hexy := congrArg (fun M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ => M x y) he
    change (if x i ≠ y i then G x y else 0)=0 at hexy
    rw [if_pos hi] at hexy
    exact hxy hexy
  have hnorm := norm_pos_iff.mpr hh
  exact hnorm.trans_le
      (le_ciSup (Set.finite_range (fun i => ‖genAdvFilter (fun w : Fin n → Bool => w) G i‖)).bddAbove i)
end
noncomputable section

theorem normalizeWordAdversary_facts {n : ℕ} (f : (Fin n → Bool) → Bool)
    (G : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : G.IsHermitian) (hz : ∀ x y, f x=f y → G x y=0) (hne : G≠0) :
    (normalizeWordAdversary G).IsHermitian ∧
    (∀ x y, f x=f y → normalizeWordAdversary G x y=0) ∧
    0 < ‖normalizeWordAdversary G‖ ∧
    (∀ i, ‖genAdvFilter (fun w : Fin n → Bool => w) (normalizeWordAdversary G) i‖ ≤ 1) ∧
    advPmWitnessValue (fun w : Fin n → Bool => w) G = ENNReal.ofReal ‖normalizeWordAdversary G‖ := by
  have hm := word_adversary_maxFilter_pos f G hz hne
  have hc : 0 < (maxFilterNorm (fun w : Fin n → Bool => w) G)⁻¹ := inv_pos.mpr hm
  have hN : 0 < ‖G‖ := norm_pos_iff.mpr hne
  have he : ‖normalizeWordAdversary G‖ = ‖G‖/maxFilterNorm (fun w : Fin n → Bool => w) G := by
    rw [normalizeWordAdversary,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    ring
  refine ⟨hG.smul (show IsSelfAdjoint ((maxFilterNorm (fun w : Fin n → Bool => w) G)⁻¹ : ℝ) by simp [IsSelfAdjoint]),?_,?_,?_,?_⟩
  · intro x y hxy
    change ((maxFilterNorm (fun w : Fin n → Bool => w) G)⁻¹ : ℝ) • G x y = 0
    rw [hz x y hxy,smul_zero]
  · rw [he]
    exact div_pos hN hm
  · intro i
    rw [normalizeWordAdversary,genAdvFilter_complex_real_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    have hle :=
        le_ciSup (Set.finite_range (fun i => ‖genAdvFilter (fun w : Fin n → Bool => w) G i‖)).bddAbove i
    change (maxFilterNorm (fun w : Fin n → Bool => w) G)⁻¹ *
      ‖genAdvFilter (fun w : Fin n → Bool => w) G i‖ ≤ 1
    calc
      _ ≤ (maxFilterNorm (fun w : Fin n → Bool => w) G)⁻¹ * maxFilterNorm (fun w : Fin n → Bool => w) G :=
        mul_le_mul_of_nonneg_left hle hc.le
      _ = 1 := inv_mul_cancel₀ hm.ne'
  · rw [he,advPmWitnessValue,← ENNReal.ofReal_div_of_pos hm]
end
noncomputable section

theorem advPmValue_iterateTotal {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) (d : ℕ) :
    advPmValue (fun w : Fin n → Bool => w) f ^ d ≤
      advPmValue (fun w : Fin (n^d) → Bool => w) (iterateTotal f d) := by
  by_cases hd : d=0
  · subst d
    rw [pow_zero]
    have hh := zeroDepthGamma_facts f
    have hN : 0 < ‖zeroDepthGamma n‖ := by rw [hh.2.1]; norm_num
    have hb := normalized_adversary_le_source (fun w : Fin (n^0) → Bool => w) (iterateTotal f 0)
      (zeroDepthGamma n) hh.1 hh.2.2.1 hN hh.2.2.2
    simpa only [hh.2.1,ENNReal.ofReal_one] using! hb
  · unfold advPmValue
    rw [ENNReal.iSup_pow_of_ne_zero hd]
    apply iSup_le
    intro G
    have hh := normalizeWordAdversary_facts f G.val G.property.1 G.property.2.1 G.property.2.2
    have hb := iteratedAdversaryGamma_source_bound hn f (normalizeWordAdversary G.val)
      hh.1 hh.2.1 hh.2.2.2.1 hh.2.2.1 d
    rw [hh.2.2.2.2]
    simpa only [ENNReal.ofReal_pow (norm_nonneg _)] using! hb
end
noncomputable section

theorem advPmValue_mono_of_injective {X Y K : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype K]
    (e : X → Y) (he : Function.Injective e)
    (inputX : X → K → Bool) (fX : X → Bool) (inputY : Y → K → Bool) (fY : Y → Bool)
    (hi : ∀ x, inputY (e x)=inputX x) (hf : ∀ x, fY (e x)=fX x) :
    advPmValue inputX fX ≤ advPmValue inputY fY := by
  unfold advPmValue
  apply iSup_le
  intro G
  let H := spectralDomainEmbedding e*G.val*(spectralDomainEmbedding e)ᴴ
  have hH : H.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ G.property.1
  have hN : ‖H‖=‖G.val‖ := spectralDomainEmbedding_norm e he G.val
  have hne : H≠0 := by
    intro hz
    have hh := norm_pos_iff.mpr G.property.2.2
    rw [← hN,hz,norm_zero] at hh
    exact (lt_irrefl 0) hh
  have hzero : ∀ u v, fY u=fY v → H u v=0 := by
    intro u v huv
    dsimp only [H]
    simp only [Matrix.mul_apply,Finset.sum_mul,Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : e x=u <;> by_cases hy : e y=v
    · have heq : fX x=fX y := by rw [← hf x,← hf y,hx,hy]; exact huv
      simp [spectralDomainEmbedding,hx,hy,G.property.2.1 x y heq]
    all_goals simp [spectralDomainEmbedding,hx,hy]
  have hfilter : maxFilterNorm inputY H=maxFilterNorm inputX G.val := by
    unfold maxFilterNorm
    congr 1
    funext i
    rw [spectralDomainEmbedding_filter e inputX inputY hi,
      spectralDomainEmbedding_norm e he]
  have hval : advPmWitnessValue inputY H=advPmWitnessValue inputX G.val := by
    rw [advPmWitnessValue,advPmWitnessValue,hN,hfilter]
  rw [← hval]
  exact le_iSup_of_le ⟨H,hH,hzero,hne⟩ le_rfl
end
noncomputable section
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

theorem sixBit_source_embedding : Function.Injective kushilevitzInputW ∧
    ∀ x : Fin 20, monotoneSixBitG (kushilevitzInputW x)=kushilevitzFunW x := by
  decide +kernel
end
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
variable {n q : ℕ} [NeZero q] {W H : Type}
variable {n q : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {n q d s : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {d : ℕ}
variable {X K : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
variable {X K : Type} [Fintype X] [Fintype K] [DecidableEq K]
variable [DecidableEq X]
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.SdpDuality.StrongDuality
open scoped InnerProductSpace
open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
set_option maxRecDepth 100000 in
noncomputable section

theorem monotoneSixBit_source_base :
    ENNReal.ofReal (2+3*Real.sqrt 5/5) ≤ advPmValue (fun w : Fin 6 → Bool => w) monotoneSixBitG := by
  apply advPmValue_kushilevitz_ge.trans
  exact advPmValue_mono_of_injective kushilevitzInputW sixBit_source_embedding.1
    kushilevitzInputW kushilevitzFunW (fun w : Fin 6 → Bool => w) monotoneSixBitG
    (fun _ => rfl) sixBit_source_embedding.2
end
noncomputable section

theorem monotoneSixBit_iterated_source_bound (d : ℕ) :
    ENNReal.ofReal ((2+3*Real.sqrt 5/5)^d) ≤
      advPmValue (fun w : Fin (6^d) → Bool => w) (iterateTotal monotoneSixBitG d) := by
  have hp := pow_le_pow_left' monotoneSixBit_source_base d
  rw [← ENNReal.ofReal_pow (show (0 : ℝ) ≤ 2+3*Real.sqrt 5/5 by positivity)] at hp
  exact hp.trans (advPmValue_iterateTotal (by norm_num) monotoneSixBitG d)
end
noncomputable section

theorem monotoneSixBit_iterated_optimized_bound (d : ℕ) :
    advPmValue (fun w : Fin 6 → Bool => w) monotoneSixBitG ^ d ≤
      advPmValue (fun w : Fin (6^d) → Bool => w) (iterateTotal monotoneSixBitG d) :=
  advPmValue_iterateTotal (by norm_num) monotoneSixBitG d
end
noncomputable section

theorem ambainis_four_bit_iterated_bound (d : ℕ) :
    ENNReal.ofReal ((2.5135 : ℝ)^d) ≤
      advPmValue (fun w : Fin (4^d) → Bool => w) (iterateTotal ambainisSorted4 d) := by
  have hp := pow_le_pow_left' ambainis_four_bit_printed_bound d
  have he : (25135/10000 : ℝ) = (2.5135 : ℝ) := by norm_num
  rw [he] at hp
  rw [← ENNReal.ofReal_pow (show (0 : ℝ) ≤ 2.5135 by norm_num)] at hp
  exact hp.trans (advPmValue_iterateTotal (by norm_num) ambainisSorted4 d)
end
noncomputable section

theorem flatCertificateUnion_valid {n m l : ℕ} (e : Fin l ≃ Fin m × Fin n)
    (f : (Fin n → Bool) → Bool) (g : (Fin m → Bool) → Bool) (w : Fin l → Bool)
    (S : Finset (Fin n)) (T : Fin n → Finset (Fin m))
    (hS : IsCertificate f (fun i => g (fun j => w (e.symm (j,i)))) S)
    (hT : ∀ i ∈ S, IsCertificate g (fun j => w (e.symm (j,i))) (T i)) :
    IsCertificate (flatBooleanCompose e f g) w (flatCertificateUnion e S T) := by
  intro v hv
  apply hS
  intro i hi
  apply hT i hi
  intro j hj
  exact hv (e.symm (j,i)) (Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩)
end
noncomputable section

theorem flatCertificateUnion_card {n m l : ℕ} (e : Fin l ≃ Fin m × Fin n)
    (S : Finset (Fin n)) (T : Fin n → Finset (Fin m)) (a c : ℕ)
    (hS : S.card ≤ a) (hT : ∀ i ∈ S, (T i).card ≤ c) :
    (flatCertificateUnion e S T).card ≤ a*c := by
  calc
    (flatCertificateUnion e S T).card ≤ ∑ i ∈ S, ((T i).image (fun j => e.symm (j,i))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i ∈ S, (T i).card := Finset.sum_le_sum (fun i _ => Finset.card_image_le)
    _ ≤ ∑ i ∈ S, c := Finset.sum_le_sum (fun i hi => hT i hi)
    _ = S.card*c := by simp
    _ ≤ a*c := Nat.mul_le_mul_right c hS
end
noncomputable section

theorem flatCertificateBlock_sum {n m l : ℕ} (e : Fin l ≃ Fin m × Fin n) (T : Finset (Fin l)) :
    (∑ i, (flatCertificateBlock e T i).card) = T.card := by
  have hcard (i : Fin n) : (flatCertificateBlock e T i).card = (T.filter (fun q => (e q).2=i)).card := by
    apply Finset.card_bij (fun j _ => e.symm (j,i))
    · intro j hj
      have hmem : e.symm (j,i) ∈ T := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨hmem,by simp⟩
    · intro a _ b _ hab
      have hh := e.symm.injective hab
      exact congrArg Prod.fst hh
    · intro q hq
      have hh := (Finset.mem_filter.mp hq).2
      refine ⟨(e q).1,?_,?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        have heq : ((e q).1,i)=e q := by rw [← hh]
        rw [heq,e.symm_apply_apply]
        exact (Finset.mem_filter.mp hq).1
      · have heq : ((e q).1,i)=e q := by rw [← hh]
        rw [heq,e.symm_apply_apply]
  simp_rw [hcard]
  clear hcard
  induction T using Finset.induction_on with
  | empty => simp
  | @insert q T hq ih =>
    have hval (i : Fin n) : ((insert q T).filter (fun a => (e a).2=i)).card =
        (T.filter (fun a => (e a).2=i)).card + if (e q).2=i then 1 else 0 := by
      have hnot : q ∉ T.filter (fun a => (e a).2=i) := fun h => hq (Finset.mem_filter.mp h).1
      by_cases hh : (e q).2=i
      · simp [Finset.filter_insert,hh,hnot]
      · simp [Finset.filter_insert,hh]
    simp_rw [hval]
    rw [Finset.sum_add_distrib,ih,Finset.card_insert_of_notMem hq]
    simp
end
noncomputable section

theorem forcedOuterCertificate_valid {n m l : ℕ} (e : Fin l ≃ Fin m × Fin n)
    (f : (Fin n → Bool) → Bool) (g : (Fin m → Bool) → Bool) (w : Fin l → Bool)
    (T : Finset (Fin l)) (hT : IsCertificate (flatBooleanCompose e f g) w T) :
    IsCertificate f (fun i => g (fun j => w (e.symm (j,i)))) (forcedOuterCertificate e g w T) := by
  intro u hu
  have hex (i : Fin n) : ∃ v : Fin m → Bool, g v=u i ∧
      ∀ j ∈ flatCertificateBlock e T i, v j=w (e.symm (j,i)) := by
    by_cases he : u i=g (fun j => w (e.symm (j,i)))
    · exact ⟨fun j => w (e.symm (j,i)),he.symm,fun _ _ => rfl⟩
    · have hnot : ¬IsCertificate g (fun j => w (e.symm (j,i))) (flatCertificateBlock e T i) := by
        intro hc
        have hi : i ∈ forcedOuterCertificate e g w T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩
        exact he (hu i hi)
      unfold IsCertificate at hnot
      push Not at hnot
      obtain ⟨v,hv,hg⟩ := hnot
      have hval : g v=u i := by
        cases ha : g v <;> cases hb : u i <;> cases hc : g (fun j => w (e.symm (j,i))) <;> simp_all
      exact ⟨v,hval,hv⟩
  choose v hv using hex
  let z : Fin l → Bool := fun q => v ((e q).2) ((e q).1)
  have hmatch : ∀ q ∈ T, z q=w q := by
    intro q hq
    have hmem : (e q).1 ∈ flatCertificateBlock e T ((e q).2) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simpa using! hq
    have hh := (hv ((e q).2)).2 ((e q).1) hmem
    simpa only [e.symm_apply_apply] using! hh
  have hvalue : flatBooleanCompose e f g z=f u := by
    unfold flatBooleanCompose
    congr 1
    funext i
    have he : (fun j => z (e.symm (j,i)))=v i := by funext j; simp [z]
    rw [he,(hv i).1]
  have hh := hT z hmatch
  rw [hvalue] at hh
  exact hh
end
noncomputable section

theorem flatCertificate_product_lower {n m l : ℕ} (e : Fin l ≃ Fin m × Fin n)
    (f : (Fin n → Bool) → Bool) (g : (Fin m → Bool) → Bool) (w : Fin l → Bool)
    (a c : ℕ)
    (hout : ∀ S, IsCertificate f (fun i => g (fun j => w (e.symm (j,i)))) S → a ≤ S.card)
    (hin : ∀ i S, IsCertificate g (fun j => w (e.symm (j,i))) S → c ≤ S.card)
    (T : Finset (Fin l)) (hT : IsCertificate (flatBooleanCompose e f g) w T) : a*c ≤ T.card := by
  let S := forcedOuterCertificate e g w T
  have hS : a ≤ S.card := hout S (forcedOuterCertificate_valid e f g w T hT)
  calc
    a*c ≤ S.card*c := Nat.mul_le_mul_right c hS
    _ = ∑ i ∈ S, c := by simp
    _ ≤ ∑ i ∈ S, (flatCertificateBlock e T i).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact hin i _ (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, (flatCertificateBlock e T i).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ => Nat.zero_le _)
    _ = T.card := flatCertificateBlock_sum e T
end
noncomputable section

theorem iterateTotal_succ_eq_flat {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) :
    iterateTotal f (d+1) = flatBooleanCompose (powIndexSplit n d) f (iterateTotal f d) := by
  funext w
  exact iterateTotal_succ f d w
end
noncomputable section

theorem monotoneSixBit_iterate_const (b : Bool) (d : ℕ) :
    iterateTotal monotoneSixBitG d (fun _ => b) = b := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [iterateTotal_succ]
    change monotoneSixBitG (fun _ => iterateTotal monotoneSixBitG d (fun _ => b)) = b
    simp only [ih]
    cases b
    · exact allZeros_g
    · exact allOnes_g
end
noncomputable section

theorem monotoneSixBit_iterated_certificates (d : ℕ) : ∀ w : Fin (6^d) → Bool,
    ∃ S : Finset (Fin (6^d)), S.card ≤ 3^d ∧ IsCertificate (iterateTotal monotoneSixBitG d) w S := by
  induction d with
  | zero =>
    intro w
    refine ⟨{0},by simp,?_⟩
    intro v hv
    change v 0 = w 0
    exact hv 0 (by simp)
  | succ d ih =>
    intro w
    let e := powIndexSplit 6 d
    let u : Fin 6 → Bool := fun i => iterateTotal monotoneSixBitG d (fun j => w (e.symm (j,i)))
    obtain ⟨S,hSc,hS⟩ := exists_cert_le_three u
    choose T hT using (fun i : Fin 6 => ih (fun j => w (e.symm (j,i))))
    refine ⟨flatCertificateUnion e S T,?_,?_⟩
    · have hc := flatCertificateUnion_card e S T 3 (3^d) hSc (fun i _ => (hT i).1)
      simpa only [pow_succ,mul_comm] using! hc
    · rw [iterateTotal_succ_eq_flat]
      exact flatCertificateUnion_valid e monotoneSixBitG (iterateTotal monotoneSixBitG d) w S T hS
        (fun i _ => (hT i).2)
end
noncomputable section

theorem monotoneSixBit_iterated_certificate_lower (b : Bool) (d : ℕ) :
    ∀ S : Finset (Fin (6^d)), IsCertificate (iterateTotal monotoneSixBitG d) (fun _ => b) S → 3^d ≤ S.card := by
  induction d with
  | zero =>
    intro S hS
    change 1 ≤ S.card
    by_contra hn
    have hz : S=∅ := Finset.card_eq_zero.mp (by omega)
    have hh := hS (fun _ => !b) (by simp [hz])
    change (!b)=b at hh
    cases b <;> simp at hh
  | succ d ih =>
    intro S hS
    rw [iterateTotal_succ_eq_flat] at hS
    have houter : ∀ T, IsCertificate monotoneSixBitG
        (fun i : Fin 6 => iterateTotal monotoneSixBitG d
          (fun j => (fun _ : Fin (6^(d+1)) => b) ((powIndexSplit 6 d).symm (j,i)))) T → 3 ≤ T.card := by
      intro T hT
      have hTb : IsCertificate monotoneSixBitG (fun _ => b) T := by
        simpa only [monotoneSixBit_iterate_const] using! hT
      have hbase : (3 : WithTop ℕ) ≤ minCertSize monotoneSixBitG (fun _ => b) := by
        cases b
        · exact three_le_minCertSize_allZeros
        · exact three_le_minCertSize_allOnes
      exact_mod_cast hbase.trans (minCertSize_le_card hTb)
    have hinner : ∀ (i : Fin 6) T, IsCertificate (iterateTotal monotoneSixBitG d)
        (fun j => (fun _ : Fin (6^(d+1)) => b) ((powIndexSplit 6 d).symm (j,i))) T → 3^d ≤ T.card := by
      intro i T hT
      exact ih T hT
    have hh := flatCertificate_product_lower (powIndexSplit 6 d) monotoneSixBitG
      (iterateTotal monotoneSixBitG d) (fun _ => b) 3 (3^d) houter hinner S hS
    simpa only [pow_succ,mul_comm] using! hh
end
noncomputable section

theorem certComplexity_monotoneSixBit_iterate (d : ℕ) (b : Bool) :
    certComplexity (iterateTotal monotoneSixBitG d) b = (3^d : WithTop ℕ) := by
  apply le_antisymm
  · rw [certComplexity_eq_iSup]
    apply iSup_le
    intro w
    split_ifs with h
    · obtain ⟨S,hS,hc⟩ := monotoneSixBit_iterated_certificates d w
      exact (minCertSize_le_card hc).trans (by exact_mod_cast hS)
    · exact bot_le
  · have hmin := le_minCertSize (monotoneSixBit_iterated_certificate_lower b d)
    rw [certComplexity_eq_iSup]
    apply hmin.trans
    apply le_iSup_of_le (fun _ => b)
    rw [if_pos (monotoneSixBit_iterate_const b d)]
end
noncomputable section

theorem certificates_cross_intersection {n : ℕ} (f : (Fin n → Bool) → Bool)
    (x y : Fin n → Bool) (S T : Finset (Fin n))
    (hS : IsCertificate f x S) (hT : IsCertificate f y T) (hxy : f x≠f y) :
    ∃ i ∈ S ∩ T, x i≠y i := by
  by_contra h
  have he (i : Fin n) (hi : i ∈ S ∩ T) : x i=y i := by
    by_contra hn
    exact h ⟨i,hi,hn⟩
  let z : Fin n → Bool := fun i => if i ∈ S then x i else y i
  have hs : f z=f x := hS z (by intro i hi; simp [z,hi])
  have ht : f z=f y := hT z (by
    intro i hi
    by_cases his : i ∈ S
    · simp [z,his,he i (Finset.mem_inter.mpr ⟨his,hi⟩)]
    · simp [z,his])
  exact hxy (hs.symm.trans ht)
end
noncomputable section

theorem advValue_le_of_source_certificates {n C : ℕ} (f : (Fin n → Bool) → Bool)
    (hnc : ∃ x y, f x≠f y) (c : (Fin n → Bool) → Finset (Fin n))
    (hcard : ∀ x, (c x).card ≤ C) (hc : ∀ x, IsCertificate f x (c x)) :
    advValue (fun w : Fin n → Bool => w) f ≤ ENNReal.ofReal (C : ℝ) := by
  obtain ⟨a,b,hab⟩ := hnc
  have hnc : ∃ x y, f x≠f y := ⟨a,b,hab⟩
  have hd (x : Fin n → Bool) : ∃ y, f x≠f y := by
    by_cases hx : f x=f a
    · exact ⟨b,fun hh => hab (hx.symm.trans hh)⟩
    · exact ⟨a,hx⟩
  have hpos (x : Fin n → Bool) : 0<(c x).card := by
    obtain ⟨y,hxy⟩ := hd x
    obtain ⟨j,hj,_⟩ := certificates_cross_intersection f x y (c x) (c y) (hc x) (hc y) hxy
    exact Finset.card_pos.mpr ⟨j,(Finset.mem_inter.mp hj).1⟩
  have hposR (x : Fin n → Bool) : 0<((c x).card : ℝ) := by exact_mod_cast hpos x
  have hC : 0<(C : ℝ) := (hposR a).trans_le (by exact_mod_cast hcard a)
  let p (x : Fin n → Bool) (i : Fin n) : ℝ := if i ∈ c x then 1/((c x).card : ℝ) else 0
  have hp : IsProbabilityFamily p := by
    constructor
    · intro x i
      dsimp [p]
      split_ifs <;> positivity
    · intro x
      simp [p,Finset.sum_ite_mem,(hposR x).ne']
  have hpair (x y : Fin n → Bool) (hxy : f x≠f y) :
      1/(C : ℝ) ≤ advMinimaxTerm (fun w : Fin n → Bool => w) (fun _ => 1) p x y := by
    obtain ⟨j,hj,hneq⟩ := certificates_cross_intersection f x y (c x) (c y) (hc x) (hc y) hxy
    have hjx := (Finset.mem_inter.mp hj).1
    have hjy := (Finset.mem_inter.mp hj).2
    have hx :=
        one_div_le_one_div_of_le (hposR x) (show ((c x).card : ℝ) ≤ C by exact_mod_cast hcard x)
    have hy :=
        one_div_le_one_div_of_le (hposR y) (show ((c y).card : ℝ) ≤ C by exact_mod_cast hcard y)
    have hprod : (1/(C : ℝ))^2 ≤ (1/((c x).card : ℝ))*(1/((c y).card : ℝ)) := by
      simpa only [pow_two] using! mul_le_mul hx hy (by positivity : 0 ≤ 1/(C : ℝ))
        (by positivity : 0 ≤ 1/((c x).card : ℝ))
    calc
      1/(C : ℝ) ≤ Real.sqrt ((1/((c x).card : ℝ))*(1/((c y).card : ℝ))) := Real.le_sqrt_of_sq_le hprod
      _ = (if x j≠y j then Real.sqrt (p x j*p y j)/(1 : ℝ) else 0) := by simp [p,hjx,hjy,hneq]
      _ ≤ advMinimaxTerm (fun w : Fin n → Bool => w) (fun _ => 1) p x y := by
        change (if x j≠y j then Real.sqrt (p x j*p y j)/(1 : ℝ) else 0) ≤
          ∑ i, if x i≠y i then Real.sqrt (p x i*p y i)/(1 : ℝ) else 0
        exact Finset.single_le_sum (f := fun i => if x i≠y i then Real.sqrt (p x i*p y i)/(1 : ℝ) else 0)
          (fun i _ => by (try dsimp only); split_ifs <;> positivity) (Finset.mem_univ j)
  rw [advValue,advAlphaR_eq_minimax (fun w : Fin n → Bool => w) f (fun _ => 1) (by intro i; norm_num) hnc]
  exact (minimax_value_le_witness _ _ _ p hp).trans
    (minimaxWitnessValue_le_of_pair _ _ _ p C hC hnc hpair)
end
noncomputable section

theorem monotoneSixBit_iterated_advValue_upper (d : ℕ) :
    advValue (fun w : Fin (6^d) → Bool => w) (iterateTotal monotoneSixBitG d) ≤
      ENNReal.ofReal ((3 : ℝ)^d) := by
  choose c hc using monotoneSixBit_iterated_certificates d
  have hnc : ∃ x y, iterateTotal monotoneSixBitG d x≠iterateTotal monotoneSixBitG d y := by
    refine ⟨fun _ => false,fun _ => true,?_⟩
    rw [monotoneSixBit_iterate_const,monotoneSixBit_iterate_const]
    decide
  have hb := advValue_le_of_source_certificates (iterateTotal monotoneSixBitG d) hnc c
    (fun x => (hc x).1) (fun x => (hc x).2)
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using! hb
end
noncomputable section

theorem certificate_rate_identity (d : ℕ) :
    (((3^d*3^d : ℕ) : ℝ)) ^ (0.549 : ℝ) = ((3 : ℝ) ^ (1.098 : ℝ))^d := by
  push_cast
  rw [← pow_two,← Real.rpow_natCast_mul (show 0 ≤ (3 : ℝ)^d by positivity) 2]
  norm_num only [show (2 : ℝ)*(0.549 : ℝ)=(1.098 : ℝ) by norm_num]
  convert! (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) (1.098 : ℝ) d).symm using 1 <;> norm_num
end
noncomputable section

theorem monotoneSixBit_iterated_certificate_rate (d : ℕ) :
    ENNReal.ofReal ((((3^d*3^d : ℕ) : ℝ)) ^ (0.549 : ℝ)) ≤
      advPmValue (fun w : Fin (6^d) → Bool => w) (iterateTotal monotoneSixBitG d) := by
  rw [certificate_rate_identity]
  have hh : ((3 : ℝ)^(1.098 : ℝ))^d ≤ (2+3*Real.sqrt 5/5)^d :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) three_rpow_1098_le d
  exact (ENNReal.ofReal_le_ofReal hh).trans (monotoneSixBit_iterated_source_bound d)
end
noncomputable section

theorem monotoneSixBit_iterated_fixed_certificate_rate (d : ℕ) (hd : 1≤d) :
    ENNReal.ofReal ((((3*3 : ℕ) : ℝ)) ^ (0.549 : ℝ)) ≤
      advPmValue (fun w : Fin (6^d) → Bool => w) (iterateTotal monotoneSixBitG d) := by
  have hn : (3*3 : ℕ) ≤ 3^d*3^d := by
    have hp : 3 ≤ (3 : ℕ)^d := by simpa using! pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 3) hd
    exact Nat.mul_le_mul hp hp
  have hr := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ ((3*3 : ℕ) : ℝ))
    (show (((3*3 : ℕ) : ℝ)) ≤ (((3^d*3^d : ℕ) : ℝ)) by exact_mod_cast hn) (by norm_num : (0 : ℝ) ≤ 0.549)
  exact (ENNReal.ofReal_le_ofReal hr).trans (monotoneSixBit_iterated_certificate_rate d)
end
noncomputable section

theorem monotoneSixBit_iterated_adversary_rate (d : ℕ) :
    ENNReal.ofReal ((advValue (fun w : Fin (6^d) → Bool => w)
      (iterateTotal monotoneSixBitG d)).toReal ^ (1.098 : ℝ)) ≤
      advPmValue (fun w : Fin (6^d) → Bool => w) (iterateTotal monotoneSixBitG d) := by
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top (monotoneSixBit_iterated_advValue_upper d)
  rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3^d)] at ht
  have hr := Real.rpow_le_rpow ENNReal.toReal_nonneg ht (by norm_num : (0 : ℝ) ≤ 1.098)
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) (1.098 : ℝ) d] at hr
  have hh : ((3 : ℝ)^(1.098 : ℝ))^d ≤ (2+3*Real.sqrt 5/5)^d :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) three_rpow_1098_le d
  exact (ENNReal.ofReal_le_ofReal (hr.trans hh)).trans (monotoneSixBit_iterated_source_bound d)
end
noncomputable section
omit [Fintype Y] in

theorem spectralDomainEmbedding_apply_image (e : X → Y) (he : Function.Injective e)
    (G : Matrix X X ℂ) (x z : X) :
    (spectralDomainEmbedding e*G*(spectralDomainEmbedding e)ᴴ) (e x) (e z)=G x z := by
  simp [spectralDomainEmbedding,Matrix.mul_apply,Matrix.conjTranspose_apply,he.eq_iff]
end
noncomputable section
omit [DecidableEq X] [Fintype Y] in

theorem spectralDomainEmbedding_row_zero (e : X → Y) (G : Matrix X X ℂ)
    (y : Y) (hy : ¬∃ x,e x=y) (z : Y) :
    (spectralDomainEmbedding e*G*(spectralDomainEmbedding e)ᴴ) y z=0 := by
  have hh (x : X) : e x ≠ y := fun hx => hy ⟨x,hx⟩
  simp [spectralDomainEmbedding,Matrix.mul_apply,hh]
end
noncomputable section
omit [Fintype X] [DecidableEq X] in

theorem spectralDomainEmbedding_compress (e : X → Y)
    (G : Matrix Y Y ℂ) :
    (spectralDomainEmbedding e)ᴴ * G * spectralDomainEmbedding e=G.submatrix e e := by
  ext x z
  simp [spectralDomainEmbedding,Matrix.mul_apply,Matrix.conjTranspose_apply]
end
noncomputable section

theorem norm_submatrix_injective_le (e : X → Y) (he : Function.Injective e)
    (G : Matrix Y Y ℂ) : ‖G.submatrix e e‖ ≤ ‖G‖ := by
  rw [← spectralDomainEmbedding_compress e]
  have hn := spectralDomainEmbedding_norm_le e he
  calc
    _ ≤ (‖(spectralDomainEmbedding e)ᴴ‖*‖G‖)*‖spectralDomainEmbedding e‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*‖G‖)*1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = _ := by ring
end
noncomputable section

theorem norm_submatrix_supported (e : X → Y) (he : Function.Injective e)
    (G : Matrix Y Y ℂ) (hG : G.IsHermitian)
    (hz : ∀ y, (¬∃ x,e x=y) → ∀ z,G y z=0) : ‖G.submatrix e e‖=‖G‖ := by
  have hid : spectralDomainEmbedding e*(G.submatrix e e)*(spectralDomainEmbedding e)ᴴ=G := by
    ext y z
    by_cases hy : ∃ x,e x=y
    · obtain ⟨x,rfl⟩ := hy
      by_cases hz' : ∃ x,e x=z
      · obtain ⟨u,rfl⟩ := hz'
        exact spectralDomainEmbedding_apply_image e he _ x u
      · have hcol : ∀ u, G u z=0 := by
          intro u
          rw [← hG.apply u z,hz z hz' u,star_zero]
        have hh (u : X) : e u ≠ z := fun hu => hz' ⟨u,hu⟩
        rw [hcol]
        simp [spectralDomainEmbedding,Matrix.mul_apply,Matrix.conjTranspose_apply,hh]
    · rw [spectralDomainEmbedding_row_zero e _ y hy z,hz y hy z]
  calc
    ‖G.submatrix e e‖ = ‖spectralDomainEmbedding e*(G.submatrix e e)*(spectralDomainEmbedding e)ᴴ‖ :=
      (spectralDomainEmbedding_norm e he _).symm
    _ = ‖G‖ := congrArg norm hid
end
noncomputable section
abbrev PartialIterateDomain {n : ℕ} (f : (Fin n → Bool) → Option Bool) (d : ℕ) :=
  {w : Fin (n^d) → Bool // iterateFlat f d w ≠ none}
end
noncomputable section

theorem option_some_getD {a : Option Bool} (h : a≠none) : a=some (a.getD false) := by
  cases a with
  | none => exact (h rfl).elim
  | some b => rfl
end
noncomputable section

theorem forceAll_valid {n : ℕ} (bs : Fin n → Option Bool) :
    forceAll bs≠none ↔ ∀ i, bs i≠none := by
  unfold forceAll
  split_ifs with h
  · constructor
    · intro _ i
      have hi := h i
      cases he : bs i <;> simp_all
    · intro _; simp
  · simp only [ne_eq,not_true_eq_false,false_iff]
    intro hh
    apply h
    intro i
    cases he : bs i
    · exact (hh i he).elim
    · rfl
end
noncomputable section

theorem forceAll_getD {n : ℕ} (bs : Fin n → Option Bool) (h : ∀ i, bs i≠none) :
    forceAll bs=some (fun i => (bs i).getD false) := by
  have he : bs=(fun i => some ((bs i).getD false)) := funext (fun i => option_some_getD (h i))
  conv_lhs => rw [he]
  exact forceAll_some _
end
noncomputable section

theorem iterateFlat_children_valid {n : ℕ} (f : (Fin n → Bool) → Option Bool)
    (d : ℕ) (w : Fin (n^(d+1)) → Bool) (h : iterateFlat f (d+1) w≠none) :
    ∀ i,iterateFlat f d (iteratedWordSplit n d w i)≠none := by
  apply (forceAll_valid _).mp
  intro he
  apply h
  change forceAll (fun i => iterateFlat f d (iteratedWordSplit n d w i)) >>= f = none
  rw [he]
  rfl
end
noncomputable section

theorem iterateFlat_succ_of_children {n : ℕ} (f : (Fin n → Bool) → Option Bool)
    (d : ℕ) (w : Fin (n^(d+1)) → Bool)
    (h : ∀ i,iterateFlat f d (iteratedWordSplit n d w i)≠none) :
    iterateFlat f (d+1) w=f (fun i => (iterateFlat f d (iteratedWordSplit n d w i)).getD false) := by
  change forceAll (fun i => iterateFlat f d (iteratedWordSplit n d w i)) >>= f = _
  rw [forceAll_getD _ h]
  rfl
end
noncomputable section
def iteratedPartialSplit {n : ℕ} (f : (Fin n → Bool) → Option Bool) (d : ℕ)
    (w : PartialIterateDomain f (d+1)) : Fin n → PartialIterateDomain f d :=
  fun i => ⟨iteratedWordSplit n d w.val i,iterateFlat_children_valid f d w.val w.property i⟩
end
noncomputable section

theorem iteratedPartialSplit_injective {n : ℕ} (f : (Fin n → Bool) → Option Bool) (d : ℕ) :
    Function.Injective (iteratedPartialSplit f d) := by
  intro x y he
  apply Subtype.ext
  apply (iteratedWordSplit n d).injective
  funext i
  exact congrArg Subtype.val (congrFun he i)
end
noncomputable section

theorem iteratedPartialSplit_value {n : ℕ} (f : (Fin n → Bool) → Option Bool) (d : ℕ)
    (w : PartialIterateDomain f (d+1)) :
    f (fun i => domValue (iterateFlat f d) (iteratedPartialSplit f d w i))=
      iterateFlat f (d+1) w.val := by
  exact (iterateFlat_succ_of_children f d w.val (iterateFlat_children_valid f d w.val w.property)).symm
end
noncomputable section

theorem iteratedPartialSplit_range {n : ℕ} (f : (Fin n → Bool) → Option Bool) (d : ℕ)
    (x : Fin n → PartialIterateDomain f d) :
    (∃ w,iteratedPartialSplit f d w=x) ↔ f (fun i => domValue (iterateFlat f d) (x i))≠none := by
  constructor
  · rintro ⟨w,rfl⟩
    rw [iteratedPartialSplit_value f d w]
    exact w.property
  · intro h
    let w := (iteratedWordSplit n d).symm (fun i => (x i).val)
    have he : ∀ i,iteratedWordSplit n d w i=(x i).val := by intro i; simp [w]
    have hc : ∀ i,iterateFlat f d (iteratedWordSplit n d w i)≠none := by
      intro i; rw [he]; exact (x i).property
    have hw : iterateFlat f (d+1) w≠none := by
      rw [iterateFlat_succ_of_children f d w hc]
      simpa only [he,domValue] using! h
    refine ⟨⟨w,hw⟩,?_⟩
    funext i
    exact Subtype.ext (he i)
end
noncomputable section

def partialAdversaryStep {n : ℕ} (f : (Fin n → Bool) → Option Bool)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (d : ℕ)
    (B : Matrix (PartialIterateDomain f d) (PartialIterateDomain f d) ℂ) :
    Matrix (PartialIterateDomain f (d+1)) (PartialIterateDomain f (d+1)) ℂ :=
  ((‖B‖^(n-1))⁻¹ : ℝ) •
    (weightedAdvGamma (fun (_ : Fin n) => domValue (iterateFlat f d))
      (fun u => (f u).getD false) A (fun _ => B)).submatrix
        (iteratedPartialSplit f d) (iteratedPartialSplit f d)
end
noncomputable section

theorem iteratedPartialSplit_filter {n d : ℕ} (f : (Fin n → Bool) → Option Bool)
    (G : Matrix (Fin n → PartialIterateDomain f d) (Fin n → PartialIterateDomain f d) ℂ)
    (q : Fin (n^(d+1))) :
    genAdvFilter (fun w : PartialIterateDomain f (d+1) => w.val)
      (G.submatrix (iteratedPartialSplit f d) (iteratedPartialSplit f d)) q =
    (weightedAdvFilter (weightedAdvInput (fun (_ : Fin n) (w : PartialIterateDomain f d) => w.val)) G
      ⟨((powIndexSplit n d) q).2,((powIndexSplit n d) q).1⟩).submatrix
        (iteratedPartialSplit f d) (iteratedPartialSplit f d) := by
  ext x y
  change (if x.val q ≠ y.val q then G (iteratedPartialSplit f d x) (iteratedPartialSplit f d y) else 0) =
    (if x.val ((powIndexSplit n d).symm ((powIndexSplit n d) q)) ≠
        y.val ((powIndexSplit n d).symm ((powIndexSplit n d) q)) then
      G (iteratedPartialSplit f d x) (iteratedPartialSplit f d y) else 0)
  rw [Equiv.symm_apply_apply]
end
noncomputable section

theorem partialAdversaryStep_facts {n : ℕ} (hn : 0<n) (f : (Fin n → Bool) → Option Bool)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hA : A.IsHermitian) (hzA : ∀ x y, (f x).getD false=(f y).getD false → A x y=0)
    (hrA : ∀ u, f u=none → ∀ v,A u v=0)
    (hfA : ∀ i, ‖genAdvFilter (fun w : Fin n → Bool => w) A i‖ ≤ 1)
    (d : ℕ) (B : Matrix (PartialIterateDomain f d) (PartialIterateDomain f d) ℂ)
    (hB : B.IsHermitian)
    (hzB : ∀ x y, domValue (iterateFlat f d) x=domValue (iterateFlat f d) y → B x y=0)
    (hfB : ∀ i, ‖genAdvFilter (fun w : PartialIterateDomain f d => w.val) B i‖ ≤ 1)
    (hBN : 0<‖B‖) :
    (partialAdversaryStep f A d B).IsHermitian ∧
    (∀ x y, domValue (iterateFlat f (d+1)) x=domValue (iterateFlat f (d+1)) y →
      partialAdversaryStep f A d B x y=0) ∧
    ‖partialAdversaryStep f A d B‖=‖A‖*‖B‖ ∧
    (∀ i, ‖genAdvFilter (fun w : PartialIterateDomain f (d+1) => w.val)
      (partialAdversaryStep f A d B) i‖ ≤ 1) := by
  let C := weightedAdvGamma (fun (_ : Fin n) => domValue (iterateFlat f d))
    (fun u => (f u).getD false) A (fun _ => B)
  let e := iteratedPartialSplit f d
  have hi : Function.Injective e := iteratedPartialSplit_injective f d
  let c : ℝ := (‖B‖^(n-1))⁻¹
  have hc : 0<c := inv_pos.mpr (pow_pos hBN _)
  have hC : C.IsHermitian := weightedAdvGamma_isHermitian _ _ _ _ hA (fun _ => hB)
  have hCn : ‖C‖=‖A‖*‖B‖^n := by
    simpa only [C,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using!
      weightedAdvGamma_norm_eq (fun (_ : Fin n) => domValue (iterateFlat f d))
        (fun u => (f u).getD false) A (fun _ => B) hA (fun _ => hB) (fun _ => hzB)
  have hCr : ∀ y, (¬∃ x,e x=y) → ∀ z,C y z=0 := by
    intro y hy z
    have hnone : f (fun i => domValue (iterateFlat f d) (y i))=none := by
      by_contra hh
      exact hy ((iteratedPartialSplit_range f d y).mpr hh)
    change A (fun i => domValue (iterateFlat f d) (y i)) _ * _=0
    rw [hrA _ hnone _,zero_mul]
  have heN : ‖C.submatrix e e‖=‖C‖ := norm_submatrix_supported e hi C hC hCr
  have hpow : ‖B‖^n=‖B‖^(n-1)*‖B‖ := by
    have hn' : n-1+1=n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
    simpa only [hn'] using! pow_succ ‖B‖ (n-1)
  refine ⟨(hC.submatrix _).smul (show IsSelfAdjoint c by simp [IsSelfAdjoint]),?_,?_,?_⟩
  · intro x y hxy
    change c • C (e x) (e y)=0
    have he (w : PartialIterateDomain f (d+1)) :
        (f (fun i => domValue (iterateFlat f d) (e w i))).getD false=
          domValue (iterateFlat f (d+1)) w :=
      congrArg (fun a : Option Bool => a.getD false) (iteratedPartialSplit_value f d w)
    have hz := weightedAdvGamma_same_output_zero (fun (_ : Fin n) => domValue (iterateFlat f d))
      (fun u => (f u).getD false) A (fun _ => B) hzA (e x) (e y)
    have hzero : C (e x) (e y)=0 := hz ((he x).trans (hxy.trans (he y).symm))
    rw [hzero,smul_zero]
  · change ‖c • C.submatrix e e‖=_
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc,heN,hCn,hpow]
    dsimp only [c]
    field_simp [pow_ne_zero _ hBN.ne']
  · intro q
    change ‖genAdvFilter (fun w : PartialIterateDomain f (d+1) => w.val)
      (c • C.submatrix e e) q‖≤1
    rw [genAdvFilter_complex_real_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    change c * ‖genAdvFilter (fun w : PartialIterateDomain f (d+1) => w.val)
      (C.submatrix (iteratedPartialSplit f d) (iteratedPartialSplit f d)) q‖≤1
    rw [iteratedPartialSplit_filter]
    let p := ((powIndexSplit n d) q).2
    let j := ((powIndexSplit n d) q).1
    have hcomp := norm_submatrix_injective_le e hi
      (weightedAdvFilter (weightedAdvInput (fun (_ : Fin n) (w : PartialIterateDomain f d) => w.val)) C ⟨p,j⟩)
    apply (mul_le_mul_of_nonneg_left hcomp hc.le).trans
    have hh := weightedAdvGamma_filter_norm_eq (fun (_ : Fin n) => domValue (iterateFlat f d))
      (fun u => (f u).getD false) A (fun _ => B)
      (fun (_ : Fin n) (w : PartialIterateDomain f d) => w.val) hA (fun _ => hB) hzA (fun _ => hzB) p j
    have hprod : (∏ i ∈ Finset.univ.erase p, ‖B‖)=‖B‖^(n-1) := by
      simp only [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,Fintype.card_fin]
    change c * ‖weightedAdvFilter
        (weightedAdvInput (fun (_ : Fin n) (w : PartialIterateDomain f d) => w.val)) C ⟨p,j⟩‖≤1
    rw [hh,hprod]
    have hb : ‖advFilter id A p‖*‖advFilter (fun w : PartialIterateDomain f d => w.val) B j‖≤1 := by
      simpa only [mul_one] using!
          mul_le_mul (hfA p) (hfB j) (norm_nonneg _) (show (0 : ℝ)≤1 by norm_num)
    calc
      c*(‖advFilter id A p‖*‖advFilter (fun w : PartialIterateDomain f d => w.val) B j‖*‖B‖^(n-1)) ≤
          c*(1*‖B‖^(n-1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg _) _)) hc.le
      _ = 1 := by dsimp only [c]; field_simp
end
noncomputable section

def partialZeroWordEquiv {n : ℕ} (f : (Fin n → Bool) → Option Bool) : PartialIterateDomain f 0 ≃ Bool where
  toFun := fun w => w.val 0
  invFun := fun b => ⟨fun _ => b,by simp [iterateFlat]⟩
  left_inv := by
    intro w
    apply Subtype.ext
    funext i
    have hi : i=0 := Fin.eq_zero i
    subst i
    rfl
  right_inv := by intro b; rfl
end
noncomputable section
def partialZeroGamma {n : ℕ} (f : (Fin n → Bool) → Option Bool) :
    Matrix (PartialIterateDomain f 0) (PartialIterateDomain f 0) ℂ :=
  booleanQueryGamma.submatrix (partialZeroWordEquiv f) (partialZeroWordEquiv f)
end
noncomputable section

theorem partialZeroGamma_facts {n : ℕ} (f : (Fin n → Bool) → Option Bool) :
    (partialZeroGamma f).IsHermitian ∧ ‖partialZeroGamma f‖=1 ∧
    (∀ x y, domValue (iterateFlat f 0) x=domValue (iterateFlat f 0) y → partialZeroGamma f x y=0) ∧
    (∀ i, ‖genAdvFilter (fun w : PartialIterateDomain f 0 => w.val) (partialZeroGamma f) i‖≤1) := by
  refine ⟨booleanQueryGamma_hermitian.submatrix _,?_,?_,?_⟩
  · rw [partialZeroGamma,norm_submatrix_equiv,booleanQueryGamma_norm]
  · intro x y hxy
    change (if x.val 0≠y.val 0 then (1 : ℂ) else 0)=0
    have he : x.val 0=y.val 0 := hxy
    rw [if_neg (not_not.mpr he)]
  · intro i
    have hi : i=0 := Fin.eq_zero i
    subst i
    have he : genAdvFilter (fun w : PartialIterateDomain f 0 => w.val) (partialZeroGamma f) 0=partialZeroGamma f := by
      ext x y
      change (if x.val 0≠y.val 0 then (if x.val 0≠y.val 0 then (1 : ℂ) else 0) else 0)=
        if x.val 0≠y.val 0 then 1 else 0
      split_ifs <;> rfl
    rw [he,partialZeroGamma,norm_submatrix_equiv,booleanQueryGamma_norm]
end
noncomputable section

def partialAdversaryGamma {n : ℕ} (f : (Fin n → Bool) → Option Bool)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    (d : ℕ) → Matrix (PartialIterateDomain f d) (PartialIterateDomain f d) ℂ
  | 0 => partialZeroGamma f
  | d+1 => partialAdversaryStep f A d (partialAdversaryGamma f A d)
end
noncomputable section

theorem partialAdversaryGamma_facts {n : ℕ} (hn : 0<n) (f : (Fin n → Bool) → Option Bool)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hA : A.IsHermitian) (hzA : ∀ x y, (f x).getD false=(f y).getD false → A x y=0)
    (hrA : ∀ u, f u=none → ∀ v,A u v=0)
    (hfA : ∀ i, ‖genAdvFilter (fun w : Fin n → Bool => w) A i‖≤1)
    (hAN : 0<‖A‖) (d : ℕ) :
    (partialAdversaryGamma f A d).IsHermitian ∧
    (∀ x y, domValue (iterateFlat f d) x=domValue (iterateFlat f d) y → partialAdversaryGamma f A d x y=0) ∧
    ‖partialAdversaryGamma f A d‖=‖A‖^d ∧
    (∀ i, ‖genAdvFilter (fun w : PartialIterateDomain f d => w.val) (partialAdversaryGamma f A d) i‖≤1) := by
  induction d with
  | zero =>
    have h := partialZeroGamma_facts f
    exact ⟨h.1,h.2.2.1,h.2.1.trans (pow_zero ‖A‖).symm,h.2.2.2⟩
  | succ d ih =>
    have hBN : 0<‖partialAdversaryGamma f A d‖ := by rw [ih.2.2.1]; exact pow_pos hAN d
    have hh := partialAdversaryStep_facts hn f A hA hzA hrA hfA d (partialAdversaryGamma f A d)
      ih.1 ih.2.1 ih.2.2.2 hBN
    refine ⟨hh.1,hh.2.1,?_,hh.2.2.2⟩
    rw [partialAdversaryGamma,hh.2.2.1,ih.2.2.1,pow_succ]
    ring
end
noncomputable section

theorem partialAdversaryGamma_source_bound {n : ℕ} (hn : 0<n) (f : (Fin n → Bool) → Option Bool)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hA : A.IsHermitian) (hzA : ∀ x y, (f x).getD false=(f y).getD false → A x y=0)
    (hrA : ∀ u, f u=none → ∀ v,A u v=0)
    (hfA : ∀ i, ‖genAdvFilter (fun w : Fin n → Bool => w) A i‖≤1)
    (hAN : 0<‖A‖) (d : ℕ) :
    ENNReal.ofReal (‖A‖^d) ≤ advPmValue (fun w : PartialIterateDomain f d => w.val) (domValue (iterateFlat f d)) := by
  haveI : Nonempty (Fin (n^d)) := ⟨⟨0,pow_pos hn d⟩⟩
  have hh := partialAdversaryGamma_facts hn f A hA hzA hrA hfA hAN d
  have hp : 0<‖partialAdversaryGamma f A d‖ := by rw [hh.2.2.1]; exact pow_pos hAN d
  have hb := normalized_adversary_le_source (fun w : PartialIterateDomain f d => w.val)
    (domValue (iterateFlat f d)) (partialAdversaryGamma f A d) hh.1 hh.2.1 hp hh.2.2.2
  rwa [hh.2.2.1] at hb
end
noncomputable section

theorem sixBit_partial_source_embedding : ∀ x : Fin 20,
    sixBitF (kushilevitzInputW x)=some (kushilevitzFunW x) := by decide
end
noncomputable section

def sixBitPartialBaseGamma : Matrix (Fin 6 → Bool) (Fin 6 → Bool) ℂ :=
  spectralDomainEmbedding kushilevitzInputW*kushilevitzGammaW*(spectralDomainEmbedding kushilevitzInputW)ᴴ
end
noncomputable section

theorem sixBitPartialBaseGamma_facts :
    sixBitPartialBaseGamma.IsHermitian ∧
    (∀ x y, (sixBitF x).getD false=(sixBitF y).getD false → sixBitPartialBaseGamma x y=0) ∧
    (∀ u, sixBitF u=none → ∀ v,sixBitPartialBaseGamma u v=0) ∧
    (∀ i, ‖genAdvFilter (fun w : Fin 6 → Bool => w) sixBitPartialBaseGamma i‖≤1) ∧
    (2+3*Real.sqrt 5/5)≤‖sixBitPartialBaseGamma‖ := by
  obtain ⟨hG,hz,hFB,hN⟩ := theorem21RealizedWitness
  have hi := sixBit_source_embedding.1
  refine ⟨Matrix.isHermitian_mul_mul_conjTranspose _ hG,?_,?_,?_,?_⟩
  · intro u v huv
    dsimp only [sixBitPartialBaseGamma]
    simp only [Matrix.mul_apply,Finset.sum_mul,Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : kushilevitzInputW x=u <;> by_cases hy : kushilevitzInputW y=v
    · have heq : kushilevitzFunW x=kushilevitzFunW y := by
        have he := huv
        rw [← hx,← hy,sixBit_partial_source_embedding,sixBit_partial_source_embedding] at he
        exact he
      simp [spectralDomainEmbedding,hx,hy,hz x y heq]
    all_goals simp [spectralDomainEmbedding,hx,hy]
  · intro u hu v
    have hnot : ¬∃ x,kushilevitzInputW x=u := by
      rintro ⟨x,rfl⟩
      have he := sixBit_partial_source_embedding x
      rw [hu] at he
      simp at he
    exact spectralDomainEmbedding_row_zero _ _ u hnot v
  · intro i
    rw [sixBitPartialBaseGamma,spectralDomainEmbedding_filter kushilevitzInputW kushilevitzInputW
      (fun w : Fin 6 → Bool => w) (fun _ => rfl),spectralDomainEmbedding_norm _ hi]
    have hm : maxFilterNorm kushilevitzInputW kushilevitzGammaW≤1 :=
      (maxFilterNorm_le_advFilterBound _ _).trans hFB
    exact (le_ciSup (Set.finite_range (fun i => ‖genAdvFilter kushilevitzInputW kushilevitzGammaW i‖)).bddAbove i).trans hm
  · rw [sixBitPartialBaseGamma,spectralDomainEmbedding_norm _ hi]
    exact hN
end
noncomputable section

theorem sixBit_partial_iterated_source_bound (d : ℕ) :
    ENNReal.ofReal ((2+3*Real.sqrt 5/5)^d) ≤
      advPmValue (fun w : PartialIterateDomain sixBitF d => w.val) (domValue (iterateFlat sixBitF d)) := by
  have h := sixBitPartialBaseGamma_facts
  have hp : 0<‖sixBitPartialBaseGamma‖ :=
    (by nlinarith [Real.sqrt_nonneg 5] : 0<2+3*Real.sqrt 5/5).trans_le h.2.2.2.2
  have hh := partialAdversaryGamma_source_bound (by norm_num : 0<6) sixBitF sixBitPartialBaseGamma
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 hp d
  exact (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by nlinarith [Real.sqrt_nonneg 5]) h.2.2.2.2 d)).trans hh
end
noncomputable section

theorem iterateFlat_outputs {n : ℕ} (f : (Fin n → Bool) → Option Bool)
    (hf : ∀ b,∃ w,f w=some b) (d : ℕ) (b : Bool) :
    ∃ w : Fin (n^d) → Bool,iterateFlat f d w=some b := by
  induction d generalizing b with
  | zero => exact ⟨fun _ => b,rfl⟩
  | succ d ih =>
    obtain ⟨u,hu⟩ := hf b
    choose bs hbs using (fun i : Fin n => ih (u i))
    let w := (iteratedWordSplit n d).symm bs
    have he (i : Fin n) : iteratedWordSplit n d w i=bs i := by simp [w]
    have hc (i : Fin n) : iterateFlat f d (iteratedWordSplit n d w i)≠none := by
      rw [he,hbs]; simp
    refine ⟨w,?_⟩
    rw [iterateFlat_succ_of_children f d w hc]
    have hv : (fun i => (iterateFlat f d (iteratedWordSplit n d w i)).getD false)=u := by
      funext i
      rw [he,hbs]
      rfl
    rw [hv,hu]
end
noncomputable section

theorem sixBitF_outputs (b : Bool) : ∃ w,sixBitF w=some b := by
  cases b
  · exact ⟨kushilevitzInputW 0,by decide⟩
  · exact ⟨kushilevitzInputW 17,by decide⟩
end
noncomputable section

theorem hamming_iterated_split {n d : ℕ} (x y : Fin (n^(d+1)) → Bool) :
    hamming x y=∑ i,hamming (iteratedWordSplit n d x i) (iteratedWordSplit n d y i) := by
  have hh := flatCertificateBlock_sum (powIndexSplit n d) (Finset.univ.filter (fun q => x q≠y q))
  simpa [hamming,flatCertificateBlock,iteratedWordSplit] using! hh.symm
end
noncomputable section

theorem sixBit_iterate_hamming_lower (d : ℕ) (x y : Fin (6^d) → Bool)
    (hx : iterateFlat sixBitF d x≠none) (hy : iterateFlat sixBitF d y≠none)
    (hxy : (iterateFlat sixBitF d x).getD false≠(iterateFlat sixBitF d y).getD false) :
    2^d≤hamming x y := by
  induction d with
  | zero =>
    have hn : x 0≠y 0 := hxy
    have hi : (0 : Fin (6^0))∈Finset.univ.filter (fun q => x q≠y q) := by simp [hn]
    exact Finset.one_le_card.mpr ⟨0,hi⟩
  | succ d ih =>
    let bx := iteratedWordSplit 6 d x
    let by' := iteratedWordSplit 6 d y
    have hcx := iterateFlat_children_valid sixBitF d x hx
    have hcy := iterateFlat_children_valid sixBitF d y hy
    let u : Fin 6 → Bool := fun i => (iterateFlat sixBitF d (bx i)).getD false
    let v : Fin 6 → Bool := fun i => (iterateFlat sixBitF d (by' i)).getD false
    have hux : sixBitF u=iterateFlat sixBitF (d+1) x :=
      (iterateFlat_succ_of_children sixBitF d x hcx).symm
    have hvy : sixBitF v=iterateFlat sixBitF (d+1) y :=
      (iterateFlat_succ_of_children sixBitF d y hcy).symm
    have hun : u≠v := by
      intro he
      apply hxy
      rw [← hux,← hvy,he]
    have hvalidu : sixBitF u=some ((iterateFlat sixBitF (d+1) x).getD false) :=
      hux.trans (option_some_getD hx)
    have hvalidv : sixBitF v=some ((iterateFlat sixBitF (d+1) y).getD false) :=
      hvy.trans (option_some_getD hy)
    have hdist : 2≤hamming u v :=
        hamming_two_le (sixBitF_weight hvalidu) (sixBitF_weight hvalidv) hun
    let S := Finset.univ.filter (fun i : Fin 6 => u i≠v i)
    calc
      2^(d+1)=2*2^d := by rw [pow_succ]; ring
      _ ≤ S.card*2^d := Nat.mul_le_mul_right _ hdist
      _ = ∑ i ∈ S,2^d := by simp
      _ ≤ ∑ i ∈ S,hamming (bx i) (by' i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact ih (bx i) (by' i) (hcx i) (hcy i) (Finset.mem_filter.mp hi).2
      _ ≤ ∑ i,hamming (bx i) (by' i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ => Nat.zero_le _)
      _ = hamming x y := (hamming_iterated_split x y).symm
end
noncomputable section

theorem relativeHamming_iterate_sixBitF_lower (d : ℕ) :
    (1/3 : ℝ)^d≤relativeHamming (iterateFlat sixBitF d) := by
  obtain ⟨x,hx⟩ := iterateFlat_outputs sixBitF sixBitF_outputs d false
  obtain ⟨y,hy⟩ := iterateFlat_outputs sixBitF sixBitF_outputs d true
  haveI : Nonempty {w : (Fin (6^d) → Bool) × (Fin (6^d) → Bool) //
      iterateFlat sixBitF d w.1=some false ∧ iterateFlat sixBitF d w.2=some true} := ⟨⟨(x,y),hx,hy⟩⟩
  have hh : (2 : ℝ)^d ≤ ⨅ w : {w : (Fin (6^d) → Bool) × (Fin (6^d) → Bool) //
      iterateFlat sixBitF d w.1=some false ∧ iterateFlat sixBitF d w.2=some true},
      ((hamming w.val.1 w.val.2 : ℕ) : ℝ) := by
    apply le_ciInf
    intro w
    have hw1 : iterateFlat sixBitF d w.val.1≠none := by rw [w.property.1]; simp
    have hw2 : iterateFlat sixBitF d w.val.2≠none := by rw [w.property.2]; simp
    have hn : (iterateFlat sixBitF d w.val.1).getD false≠(iterateFlat sixBitF d w.val.2).getD false := by
      rw [w.property.1,w.property.2]; decide
    exact_mod_cast sixBit_iterate_hamming_lower d w.val.1 w.val.2 hw1 hw2 hn
  have hd : 0<(6 : ℝ)^d := pow_pos (by norm_num) d
  unfold relativeHamming
  rw [if_neg (by positivity : ¬(6^d : ℕ)=0)]
  push_cast
  calc
    (1/3 : ℝ)^d=(2 : ℝ)^d/(6 : ℝ)^d := by rw [← div_pow]; norm_num
    _ ≤ _ := div_le_div_of_nonneg_right hh hd.le
end
noncomputable section

theorem sixBit_partial_iterated_property_rate (d : ℕ) :
    ENNReal.ofReal ((1/relativeHamming (iterateFlat sixBitF d))^(1.098 : ℝ)) ≤
      advPmValue (fun w : PartialIterateDomain sixBitF d => w.val) (domValue (iterateFlat sixBitF d)) := by
  have hd := relativeHamming_iterate_sixBitF_lower d
  have hp : 0<(1/3 : ℝ)^d := pow_pos (by norm_num) d
  have hε : 0<relativeHamming (iterateFlat sixBitF d) := hp.trans_le hd
  have hi : 1/relativeHamming (iterateFlat sixBitF d)≤(3 : ℝ)^d := by
    have hh := one_div_le_one_div_of_le hp hd
    simpa only [← _root_.one_div_pow,one_div_div,div_one] using! hh
  have hr := Real.rpow_le_rpow (by positivity : 0≤1/relativeHamming (iterateFlat sixBitF d)) hi
    (by norm_num : (0 : ℝ)≤1.098)
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ)≤3) (1.098 : ℝ) d] at hr
  have hn := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num : (0 : ℝ)≤3) _ ) three_rpow_1098_le d
  exact (ENNReal.ofReal_le_ofReal (hr.trans hn)).trans (sixBit_partial_iterated_source_bound d)
end
noncomputable section

theorem stageA_general_adversary_clause19_full_endpoint_v2 : Qatlib.Concepts.AdversaryBounds.AdvDuality.clause19Prop := by
  refine ⟨?_,relativeHamming_sixBitF,advPmValue_kushilevitz_rate,?_,?_,?_,
    certComplexity_monotoneSixBitG_eq_three.1,certComplexity_monotoneSixBitG_eq_three.2,?_,?_,?_,?_⟩
  · have he : (25135/10000 : ℝ)=(2.5135 : ℝ) := by norm_num
    simpa only [he] using! ambainis_four_bit_printed_bound
  · exact fun d _ => sixBit_partial_iterated_property_rate d
  · exact fun d _ => monotoneSixBit_iterated_source_bound d
  · exact fun d _ => monotoneSixBit_iterated_optimized_bound d
  · exact fun d _ => ⟨certComplexity_monotoneSixBit_iterate d false,certComplexity_monotoneSixBit_iterate d true⟩
  · exact fun d _ => monotoneSixBit_iterated_certificate_rate d
  · exact monotoneSixBit_iterated_fixed_certificate_rate
  · exact fun d _ => monotoneSixBit_iterated_adversary_rate d
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality
