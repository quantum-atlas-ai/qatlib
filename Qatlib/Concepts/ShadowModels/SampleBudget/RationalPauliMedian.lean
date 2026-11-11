/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowVariance.ShadowPurityConsumers
import Qatlib.Concepts.ShadowModels.SampleBudget.RationalLinearSelection

/-!
# Rational qubit purity medians

This module implements a rational qubit purity group estimator and an odd-block median using
`qSelect`. Record equivalences transport probabilities, means, and variance bounds between
native one-qubit records and the tensor Pauli model.

The main guarantees identify the rational output with the real purity median, give its classical
and quantum resource counts, and provide a computable tolerance-dependent block budget with a
median failure bound. See [HuangKuengPreskill2020] for background.

## Main statements

* `native_pauli_same_record_purity_mean_and_derived_variance`: unbiasedness and a `100/m`
  mean-square bound.
* `native_pauli_linear_median_same_output_and_all_ledgers`: output equality and resource counts.
* `native_pauli_computable_tolerance_budget_and_purity_probability`: the explicit rational
  tolerance budget.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false


open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowVariance
open Qatlib.Concepts.ShadowModels.UStatBackend
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
namespace Qatlib.Concepts.ShadowModels.SampleBudget

/-- View a native single-qubit measurement record as a record indexed by the one-qubit register. -/
def onePauliRecord (x : Fin 3 × Bool) : Fin 1 → Fin 3 × Bool := fun _ => x
/-- Embed a sequence of native single-qubit records into the tensor Pauli record format. -/
def onePauliRecords {m : ℕ} (ω : Fin m → Fin 3 × Bool) : Fin m → Fin 1 → Fin 3 × Bool :=
  fun j => onePauliRecord (ω j)
/-- The counted rational purity U-statistic computed from a group of native single-qubit
records. -/
def nativePauliGroup {m : ℕ} (ω : Fin m → Fin 3 × Bool) : ℚ × ℕ × ℕ :=
  tensorPurityURationalCounted 1 (onePauliRecords ω)
/-- The rational median of `2*r+1` group purity estimates, together with the accumulated group
counters and selection comparison count. -/
def nativePauliMedian (m r : ℕ) (ω : Fin (2*r+1) → Fin m → Fin 3 × Bool) :
    ℚ × ℕ × ℕ × ℕ :=
  let groups := List.ofFn (fun b => nativePauliGroup (ω b))
  let result := qSelect (groups.map Prod.fst) r
  (result.1,(groups.map (fun z => z.2.1)).sum,(groups.map (fun z => z.2.2)).sum,result.2)

/-- The computable block size `max 2 (Nat.ceil (1600/ε²))` for a rational tolerance. -/
def nativePauliBlockBudget (ε : ℚ) : ℕ := max 2 (Nat.ceil (1600/ε^2))

open Matrix
open scoped Classical BigOperators ComplexOrder
/-- The total product probability of record blocks for which the native purity median differs
from the state's purity by more than `ε`. -/
noncomputable def nativePauliBadMass (m r : ℕ) (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (ε : ℝ) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → Fin m → Fin 3 × Bool =>
    ε < |((nativePauliMedian m r ω).1 : ℝ)-(Matrix.trace (ρ*ρ)).re|),
    ∏ b, (pauliRecordDist ρ hρ).probOf (ω b)

/-- A one-qubit tensor product operator is its sole factor. -/
theorem nativePauli_single_product (A : Fin 1 → Operator 2) : tensorPauliProduct 1 A=A 0 := by
  have hb : (bitVecEquiv 1).symm=(fun r : Fin 2 => fun _ : Fin 1 => boolEquivFin2.symm r) := by
    funext r i
    fin_cases r <;> fin_cases i <;> decide
  ext i j
  simp [tensorPauliProduct,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,
    pauliProductDensity,hb]

/-- A native one-qubit record has the same probability as its embedding in the one-qubit tensor
Pauli law. -/
theorem nativePauli_record_law (ρ : Operator 2) (hρ : IsDensityOperator ρ) (o : Fin 3 × Bool) :
    (pauliRecordDist ρ hρ).prob o=(tensorPauliLaw 1 ρ hρ).prob (onePauliRecord o) := by
  have hk : tensorPauliKraus 1 (onePauliRecord o)=pauliRecordKraus o := by
    change tensorPauliProduct 1 (fun _ => pauliRecordKraus o)=pauliRecordKraus o
    exact nativePauli_single_product _
  simp only [pauliRecordDist,tensorPauliLaw,instrumentProb,pauliShadowRecordInstrument,
    tensorPauliInstrument,Instrument.ofKraus_branch,hk]

/-- The rational group estimate casts to the tensor purity U-statistic, both group counters
equal `m.choose 2`, and groups of size below two return zero; native and tensor record
probabilities also agree. -/
theorem native_pauli_rational_group_and_physical_record_bridge :
    ∀ (m : ℕ) (ω : Fin m → Fin 3 × Bool),
      ((nativePauliGroup ω).1 : ℝ)=tensorPurityU 1 (onePauliRecords ω) ∧
      (nativePauliGroup ω).2.1=m.choose 2 ∧ (nativePauliGroup ω).2.2=m.choose 2 ∧
      (m<2 → (nativePauliGroup ω).1=0) ∧
      ∀ (ρ : Operator 2) (hρ : IsDensityOperator ρ) (o : Fin 3 × Bool),
        (pauliRecordDist ρ hρ).prob o=(tensorPauliLaw 1 ρ hρ).prob (onePauliRecord o) := by
  intro m ω
  obtain ⟨hv,hp,hl⟩ := tensorPurityURationalCounted_spec 1 m (onePauliRecords ω)
  refine ⟨hv,hp,by simpa using! hl,?_,nativePauli_record_law⟩
  intro hm
  have hchoose : m.choose 2=0 := Nat.choose_eq_zero_of_lt hm
  simp [nativePauliGroup,tensorPurityURationalCounted,hchoose]

/-- The equivalence between native single-qubit records and records indexed by `Fin 1`. -/
def onePauliRecordEquiv : (Fin 3 × Bool) ≃ (Fin 1 → Fin 3 × Bool) where
  toFun := onePauliRecord
  invFun o := o 0
  left_inv _ := rfl
  right_inv o := by
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    rfl

/-- The equivalence between native record sequences of length `m` and one-qubit tensor record
sequences. -/
def onePauliRecordsEquiv (m : ℕ) : (Fin m → Fin 3 × Bool) ≃ (Fin m → Fin 1 → Fin 3 × Bool) :=
  Equiv.piCongrRight (fun _ => onePauliRecordEquiv)

/-- The joint probability of a native record sequence equals that of its tensor-format
embedding. -/
theorem nativePauli_record_probOf (m : ℕ) (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (ω : Fin m → Fin 3 × Bool) :
    (pauliRecordDist ρ hρ).probOf ω=(tensorPauliLaw 1 ρ hρ).probOf (onePauliRecords ω) := by
  unfold FinDist.probOf
  apply Finset.prod_congr rfl
  intro j _
  exact nativePauli_record_law ρ hρ (ω j)

/-- Weighted sums over native record sequences equal weighted sums over the corresponding
one-qubit tensor record sequences. -/
theorem nativePauli_sum_transport (m : ℕ) (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (F : (Fin m → Fin 1 → Fin 3 × Bool) → ℝ) :
    (∑ ω : Fin m → Fin 3 × Bool,(pauliRecordDist ρ hρ).probOf ω*F (onePauliRecords ω))=
      ∑ ω : Fin m → Fin 1 → Fin 3 × Bool,(tensorPauliLaw 1 ρ hρ).probOf ω*F ω := by
  simp_rw [nativePauli_record_probOf]
  exact (onePauliRecordsEquiv m).sum_comp
    (fun ω => (tensorPauliLaw 1 ρ hρ).probOf ω*F ω)

/-- For groups of at least two native records, the rational purity estimate is unbiased and its
expected squared error is at most `100/m`. -/
theorem native_pauli_same_record_purity_mean_and_derived_variance :
    ∀ (m : ℕ) (ρ : Operator 2) (hρ : IsDensityOperator ρ),2 ≤ m →
    (∑ ω : Fin m → Fin 3 × Bool,(pauliRecordDist ρ hρ).probOf ω*((nativePauliGroup ω).1 : ℝ))=
      (Matrix.trace (ρ*ρ)).re ∧
    (∑ ω : Fin m → Fin 3 × Bool,(pauliRecordDist ρ hρ).probOf ω*
      (((nativePauliGroup ω).1 : ℝ)-(Matrix.trace (ρ*ρ)).re)^2)≤100/(m : ℝ) := by
  intro m ρ hρ hm
  have hgroup (ω : Fin m → Fin 3 × Bool) :
      ((nativePauliGroup ω).1 : ℝ)=tensorPurityU 1 (onePauliRecords ω) :=
    (native_pauli_rational_group_and_physical_record_bridge m ω).1
  simp_rw [hgroup]
  refine ⟨?_,?_⟩
  · rw [nativePauli_sum_transport m ρ hρ (tensorPurityU 1)]
    have hU (ω : Fin m → Fin 1 → Fin 3 × Bool) :
        tensorPurityU 1 ω=pairUStatistic (tensorPurityKernel 1) ω :=
      (finite_pair_u_statistic_actual_value_and_count _ m _ ω).1
    simp_rw [hU]
    rw [finite_pair_u_statistic_unbiased _ _ m _ hm]
    exact (tensor_purity_actual_pair_kernel_and_mean 1 (fun _ => (0,false))
      (fun _ => (0,false))).2.2 ρ hρ
  · rw [nativePauli_sum_transport m ρ hρ
      (fun ω => (tensorPurityU 1 ω-(Matrix.trace (ρ*ρ)).re)^2)]
    have hv := (tensor_purity_derived_moment_and_variance_bounds 1 m ρ hρ hm).2.2
    have hmp : (0 : ℝ)< m := by exact_mod_cast (by omega : 0 < m)
    have hminus : (1 : ℝ)≤(m-1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ m-1)
    have hden : (m : ℝ)≤(m : ℝ)*(m-1 : ℕ) := by nlinarith
    have hfrac : (50 : ℝ)/((m : ℝ)*(m-1 : ℕ))≤50/(m : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hmp hden
    norm_num at hv
    have hb : 20/(m : ℝ)+50/((m : ℝ)*(m-1 : ℕ))≤100/(m : ℝ) := by
      have he : (20 : ℝ)/m+50/m=70/m := by ring
      have hm0 : 0≤(1 : ℝ)/m := by positivity
      have h70 : (70 : ℝ)/m≤100/m := by
        rw [div_le_div_iff_of_pos_right hmp]
        norm_num
      linarith
    exact hv.trans hb

/-- The rational native median equals the real tensor purity median, its group counters are
`(2*r+1) * m.choose 2`, its selection cost is at most `10000 * (2*r+1)`, and its
fresh-record quantum resources have the stated exact counts. -/
theorem native_pauli_linear_median_same_output_and_all_ledgers :
    ∀ (m r : ℕ) (ω : Fin (2*r+1) → Fin m → Fin 3 × Bool),
      ((nativePauliMedian m r ω).1 : ℝ)=tensorPurityMedian 1 m (2*r+1)
        (fun b => onePauliRecords (ω b)) ∧
      (nativePauliMedian m r ω).2.1=(2*r+1)*m.choose 2 ∧
      (nativePauliMedian m r ω).2.2.1=(2*r+1)*m.choose 2 ∧
      (nativePauliMedian m r ω).2.2.2≤10000*(2*r+1) ∧
      tensorPauliFreshResourceCounts 1 m (2*r+1) (fun b => onePauliRecords (ω b))=
        ((2*r+1)*m,2*((2*r+1)*m),(2*r+1)*m,0) := by
  intro m r ω
  let v : Fin (2*r+1) → ℚ := fun b => (nativePauliGroup (ω b)).1
  have hs := rational_selection_median_exact_real_sorted_semantics r v
  have hv : ((nativePauliMedian m r ω).1 : ℝ)=sortedBlockMedian r (fun j => (v j : ℝ)) := by
    simpa only [nativePauliMedian,List.map_ofFn,Function.comp_def,v] using! hs.1
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hv]
    have hvalue : (fun j => (v j : ℝ))=fun b => tensorPurityU 1 (onePauliRecords (ω b)) := by
      funext b
      exact (native_pauli_rational_group_and_physical_record_bridge m (ω b)).1
    rw [hvalue]
    unfold sortedBlockMedian tensorPurityMedian
    have hdiv : (2*r+1)/2=r := by omega
    rw [hdiv]
  · simp only [nativePauliMedian,List.map_ofFn,Function.comp_def,List.sum_ofFn]
    simp_rw [(native_pauli_rational_group_and_physical_record_bridge m _).2.1]
    simp
  · simp only [nativePauliMedian,List.map_ofFn,Function.comp_def,List.sum_ofFn]
    simp_rw [(native_pauli_rational_group_and_physical_record_bridge m _).2.2.1]
    simp
  · simpa only [nativePauliMedian,List.map_ofFn,Function.comp_def,v] using! hs.2
  · simpa only [Nat.mul_one,Nat.one_mul] using!
      tensorPauliFreshResourceCounts_spec 1 m (2*r+1) (fun b => onePauliRecords (ω b))

/-- For a positive rational tolerance, the native block budget is at least two and makes the
displayed scaled purity variance bound at most the squared tolerance. -/
theorem nativePauli_budget_spec (ε : ℚ) (hε : 0<ε) :
    2≤nativePauliBlockBudget ε ∧
    16*(4*(5 : ℝ)^1/(nativePauliBlockBudget ε : ℝ)+
      2*(25 : ℝ)^1/((nativePauliBlockBudget ε : ℝ)*(nativePauliBlockBudget ε-1 : ℕ)))≤
        (ε : ℝ)^2 := by
  let m := nativePauliBlockBudget ε
  have hm : 2 ≤ m := le_max_left _ _
  have hceil : (1600/ε^2 : ℚ)≤(m : ℚ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 2 (Nat.ceil ((1600 : ℚ)/ε^(2 : ℕ)))))
  have hreal : (1600 : ℝ)/(ε : ℝ)^2≤(m : ℝ) := by exact_mod_cast hceil
  have he : (0 : ℝ)<(ε : ℝ) := by exact_mod_cast hε
  have hmp : (0 : ℝ)<(m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hminus : (1 : ℝ)≤(m-1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ m-1)
  have hden : (m : ℝ)≤(m : ℝ)*(m-1 : ℕ) := by nlinarith
  have hfrac : (50 : ℝ)/((m : ℝ)*(m-1 : ℕ))≤50/(m : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hmp hden
  have hraw : (1600 : ℝ)≤(m : ℝ)*(ε : ℝ)^2 := by
    have h := (div_le_iff₀ (pow_pos he 2)).mp hreal
    nlinarith
  have hgood : (1600 : ℝ)/(m : ℝ)≤(ε : ℝ)^2 := (div_le_iff₀ hmp).mpr (by nlinarith)
  refine ⟨hm,?_⟩
  change 16*(4*(5 : ℝ)^1/(m : ℝ)+2*(25 : ℝ)^1/((m : ℝ)*(m-1 : ℕ)))≤_
  norm_num
  have heq : 16*((20 : ℝ)/m+50/m)=1120/m := by ring
  have hb : (1120 : ℝ)/m≤1600/m := by
    rw [div_le_div_iff_of_pos_right hmp]
    norm_num
  linarith

/-- The equivalence between `2*r+1` blocks of native records and blocks of one-qubit tensor
records. -/
def onePauliBlocksEquiv (m r : ℕ) :
    (Fin (2*r+1) → Fin m → Fin 3 × Bool) ≃
      (Fin (2*r+1) → Fin m → Fin 1 → Fin 3 × Bool) :=
  Equiv.piCongrRight (fun _ => onePauliRecordsEquiv m)

/-- The native median failure mass equals the failure mass of the tensor purity median under the
blockwise record equivalence. -/
theorem nativePauli_badMass_eq (m r : ℕ) (ρ : Operator 2) (hρ : IsDensityOperator ρ) (ε : ℝ) :
    nativePauliBadMass m r ρ hρ ε=
      ∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → Fin m → Fin 1 → Fin 3 × Bool =>
        ε < |tensorPurityMedian 1 m (2*r+1) ω-(Matrix.trace (ρ*ρ)).re|),
          ∏ b,(tensorPauliLaw 1 ρ hρ).probOf (ω b) := by
  unfold nativePauliBadMass
  rw [Finset.sum_filter,Finset.sum_filter,← (onePauliBlocksEquiv m r).sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  have hprob : (∏ b,(pauliRecordDist ρ hρ).probOf (ω b))=
      ∏ b,(tensorPauliLaw 1 ρ hρ).probOf (onePauliRecords (ω b)) := by
    apply Finset.prod_congr rfl
    intro b _
    exact nativePauli_record_probOf m ρ hρ (ω b)
  rw [(native_pauli_linear_median_same_output_and_all_ledgers m r ω).1,hprob]
  rfl

/-- For every positive rational tolerance, the computable native block budget is at least two
and bounds the purity median failure mass by `2^(2*r+1) * (1/16)^(r+1)`. -/
theorem native_pauli_computable_tolerance_budget_and_purity_probability :
    ∀ (r : ℕ) (ρ : Operator 2) (hρ : IsDensityOperator ρ) (ε : ℚ),0<ε →
      2≤nativePauliBlockBudget ε ∧
      nativePauliBadMass (nativePauliBlockBudget ε) r ρ hρ (ε : ℝ)≤
        (2 : ℝ)^(2*r+1)*(1/16 : ℝ)^(r+1) := by
  intro r ρ hρ ε hε
  obtain ⟨hm,hbudget⟩ := nativePauli_budget_spec ε hε
  refine ⟨hm,?_⟩
  rw [nativePauli_badMass_eq]
  exact tensor_purity_same_born_records_median_bound 1 (nativePauliBlockBudget ε) r ρ hρ
    (ε : ℝ) hm (by exact_mod_cast hε) hbudget

end Qatlib.Concepts.ShadowModels.SampleBudget
