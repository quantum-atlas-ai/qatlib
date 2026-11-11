/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecodingDefs

/-!
# Steane-code decoding and recovery accounting

The seven-qubit CSS decoder recovers every Pauli label of weight at most one
from its syndrome. The module proves zero residual error, minimum-weight
soundness, preservation of the encoded reference for the resulting residual,
and recovery-cost identities. It also checks fault and space-time bounds for
the concrete round gadget defined by this development.

The code originates in [Steane1996], within the CSS construction of
[Calderbank & Shor][CalderbankShor1996]. Stabilizer background is [Gottesman1997];
the numerical gadget bounds here refer to the local cost and fault model.
-/
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.CodingDecoding.CssRecovery

open Matrix
open Qatlib
open scoped Classical

/-- The Steane parity-check matrix sends a unit label to its corresponding column. -/
theorem steaneH_mulVec_single (i : Fin 7) :
    steaneH *ᵥ (unitLabel i) = steaneCol i := by
  funext k
  simp [Matrix.mulVec, dotProduct, steaneH, steaneCol, unitLabel, Finset.sum_ite_eq']

/-- Multiplication by the Steane parity-check matrix commutes with scalar multiplication over
`ZMod 2`. -/
theorem steaneH_mulVec_smul (x : ZMod 2) (v : Fin 7 → ZMod 2) :
    steaneH *ᵥ (x • v) = x • steaneH *ᵥ v := by
  simp [Matrix.mulVec_smul]

/-- A binary vector supported at a single index is its value at that index times the
corresponding unit label. -/
theorem eq_smul_unitLabel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ZMod 2) {a : ι} (h : ∀ i, i ≠ a → x i = 0) :
    x = x a • (unitLabel a) := by
  funext i
  by_cases hi : i = a
  · subst hi
    simp [unitLabel, Pi.smul_apply]
  · have hx0 : x i = 0 := h i hi
    simp [unitLabel, Pi.smul_apply, hx0, hi]

/-- Every element of `ZMod 2` is either zero or one. -/
theorem zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  exact (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b

/-- Every element of `ZMod 2` sums with itself to zero. -/
theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

/-- A Pauli label of weight at most one is zero or is a single-site X, Z, or combined XZ label. -/
theorem pauliWeight_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x z : ι → ZMod 2) (h : pauliWeight x z ≤ 1) :
    (x = 0 ∧ z = 0) ∨
    (∃ a : ι, x = unitLabel a ∧ z = 0) ∨
    (∃ a : ι, x = 0 ∧ z = unitLabel a) ∨
    (∃ a : ι, x = unitLabel a ∧ z = unitLabel a) := by
  classical
  have hcard : (Finset.univ.filter fun i => x i ≠ 0 ∨ z i ≠ 0).card ≤ 1 := h
  have hcases : (Finset.univ.filter fun i => x i ≠ 0 ∨ z i ≠ 0).card = 0 ∨
      (Finset.univ.filter fun i => x i ≠ 0 ∨ z i ≠ 0).card = 1 := by omega
  rcases hcases with hz' | ho'
  · have hempty : Finset.univ.filter (fun i => x i ≠ 0 ∨ z i ≠ 0) = ∅ :=
      Finset.card_eq_zero.mp hz'
    left
    constructor
    · funext i
      by_contra hx
      have hi : i ∈ Finset.univ.filter (fun j => x j ≠ 0 ∨ z j ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl hx⟩
      rw [hempty] at hi
      simp at hi
    · funext i
      by_contra hz
      have hi : i ∈ Finset.univ.filter (fun j => x j ≠ 0 ∨ z j ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr hz⟩
      rw [hempty] at hi
      simp at hi
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp ho'
    have hout : ∀ i, i ≠ a → x i = 0 ∧ z i = 0 := by
      intro i hi
      have hnot : i ∉ Finset.univ.filter (fun j => x j ≠ 0 ∨ z j ≠ 0) := by
        rw [ha]
        simp [hi]
      constructor
      · by_contra hx
        have him : i ∈ Finset.univ.filter (fun j => x j ≠ 0 ∨ z j ≠ 0) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl hx⟩
        rw [ha] at him
        exact absurd (Finset.mem_singleton.mp him) hi
      · by_contra hz
        have him : i ∈ Finset.univ.filter (fun j => x j ≠ 0 ∨ z j ≠ 0) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr hz⟩
        rw [ha] at him
        exact absurd (Finset.mem_singleton.mp him) hi
    have hxa : x a = 0 ∨ x a = 1 := zmod2_eq_zero_or_one (x a)
    have hza : z a = 0 ∨ z a = 1 := zmod2_eq_zero_or_one (z a)
    rcases hxa with hxa0 | hxa1
    · rcases hza with hza0 | hza1
      · left
        refine ⟨?_, ?_⟩
        · funext i
          by_cases hi : i = a
          · subst hi; simp [hxa0]
          · exact (hout i hi).1
        · funext i
          by_cases hi : i = a
          · subst hi; simp [hza0]
          · exact (hout i hi).2
      · right; right; left
        refine ⟨a, ?_, ?_⟩
        · funext i
          by_cases hi : i = a
          · subst hi; simp [hxa0]
          · exact (hout i hi).1
        · rw [eq_smul_unitLabel z (fun i hi => (hout i hi).2)]
          simp [hza1, one_smul]
    · rcases hza with hza0 | hza1
      · right; left
        refine ⟨a, ?_, ?_⟩
        · rw [eq_smul_unitLabel x (fun i hi => (hout i hi).1)]
          simp [hxa1, one_smul]
        · funext i
          by_cases hi : i = a
          · subst hi; simp [hza0]
          · exact (hout i hi).2
      · right; right; right
        refine ⟨a, ?_, ?_⟩
        · rw [eq_smul_unitLabel x (fun i hi => (hout i hi).1)]
          simp [hxa1, one_smul]
        · rw [eq_smul_unitLabel z (fun i hi => (hout i hi).2)]
          simp [hza1, one_smul]

/-- The zero Pauli label has weight zero. -/
theorem pauliWeight_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    pauliWeight (0 : ι → ZMod 2) (0 : ι → ZMod 2) = 0 := by
  classical
  simp [pauliWeight]

/-- A single-site X label has Pauli weight one. -/
theorem pauliWeight_unit_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    pauliWeight (unitLabel a) (0 : ι → ZMod 2) = 1 := by
  classical
  unfold pauliWeight
  have hfilter : Finset.univ.filter (fun i => unitLabel a i ≠ 0 ∨ (0 : ι → ZMod 2) i ≠ 0)
      = {a} := by
    ext i
    simp [unitLabel]
  rw [hfilter]
  simp

/-- The Pauli weight of two unit labels is one when their sites coincide and two otherwise. -/
theorem pauliWeight_unit_unit {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    pauliWeight (unitLabel a) (unitLabel b) = if a = b then 1 else 2 := by
  classical
  unfold pauliWeight
  have hfilter : Finset.univ.filter (fun i => unitLabel a i ≠ 0 ∨ unitLabel b i ≠ 0)
      = {a} ∪ {b} := by
    ext i
    by_cases ha : i = a
    · subst ha; simp [unitLabel]
    · by_cases hb : i = b
      · subst hb; simp [unitLabel]
      · simp [unitLabel, ha, hb]
  rw [hfilter]
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/-- A single-site Z label has Pauli weight one. -/
theorem pauliWeight_zero_unit {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    pauliWeight (0 : ι → ZMod 2) (unitLabel a) = 1 := by
  classical
  unfold pauliWeight
  have hfilter : Finset.univ.filter (fun i => (0 : ι → ZMod 2) i ≠ 0 ∨ unitLabel a i ≠ 0)
      = {a} := by
    ext i
    simp [unitLabel]
  rw [hfilter]
  simp

/-- A Pauli label with nonzero X component has weight at least one. -/
theorem pauliWeight_ge_one_of_ne_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e f : ι → ZMod 2} (h : e ≠ 0) : 1 ≤ pauliWeight e f := by
  classical
  have hmem : ∃ i, e i ≠ 0 := by
    by_contra hcon
    have hall : ∀ i, e i = 0 := by
      intro i
      by_contra hi
      exact hcon ⟨i, hi⟩
    exact h (funext hall)
  obtain ⟨i, hi⟩ := hmem
  have hin : i ∈ Finset.univ.filter fun k => e k ≠ 0 ∨ f k ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl hi⟩
  have hpos : 0 < (Finset.univ.filter fun k => e k ≠ 0 ∨ f k ≠ 0).card :=
    Finset.card_pos.mpr ⟨i, hin⟩
  unfold pauliWeight
  omega

/-- A Pauli label with nonzero Z component has weight at least one. -/
theorem pauliWeight_ge_one_of_ne {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e f : ι → ZMod 2} (h : f ≠ 0) : 1 ≤ pauliWeight e f := by
  classical
  have hmem : ∃ i, f i ≠ 0 := by
    by_contra hcon
    have hall : ∀ i, f i = 0 := by
      intro i
      by_contra hi
      exact hcon ⟨i, hi⟩
    exact h (funext hall)
  obtain ⟨i, hi⟩ := hmem
  have hin : i ∈ Finset.univ.filter fun k => e k ≠ 0 ∨ f k ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr hi⟩
  have hpos : 0 < (Finset.univ.filter fun k => e k ≠ 0 ∨ f k ≠ 0).card :=
    Finset.card_pos.mpr ⟨i, hin⟩
  unfold pauliWeight
  omega

/-- The Steane Pauli syndrome consists of the parity-check products of the Z and X components,
in that order. -/
theorem steaneSyndrome (e : PauliLabel (Fin 7)) :
    pauliSyndrome steaneData e = (steaneH *ᵥ e.2, steaneH *ᵥ e.1) := rfl

/-- The Steane single-site label is the corresponding unit label. -/
theorem steaneSingle_eq (a : Fin 7) : steaneSingle a = unitLabel a := rfl

/-- The Steane correction for a single-site X syndrome returns that X label. -/
theorem steaneCorr_singleX (a : Fin 7) :
    steaneCorr (0, steaneCol a) = (unitLabel a, 0) := by
  simp [steaneCorr, steaneCorrX, steaneCorrZ, steaneCol_ne_zero a, steaneColIdx_col a,
    steaneSingle_eq]

/-- The Steane correction for a single-site Z syndrome returns that Z label. -/
theorem steaneCorr_singleZ (a : Fin 7) :
    steaneCorr (steaneCol a, 0) = (0, unitLabel a) := by
  simp [steaneCorr, steaneCorrX, steaneCorrZ, steaneCol_ne_zero a, steaneColIdx_col a,
    steaneSingle_eq]

/-- The Steane correction for a single-site combined XZ syndrome returns the same combined
label. -/
theorem steaneCorr_singleY (a : Fin 7) :
    steaneCorr (steaneCol a, steaneCol a) = (unitLabel a, unitLabel a) := by
  simp [steaneCorr, steaneCorrX, steaneCorrZ, steaneCol_ne_zero a, steaneColIdx_col a,
    steaneSingle_eq]

/-- The Steane syndrome decoder returns the original Pauli label for any error
of weight at most one; see [Steane, error-correcting codes][Steane1996]. -/
theorem steaneDecoder_corrects_weight_one (e : PauliLabel (Fin 7))
    (h : pauliWeight e.1 e.2 ≤ 1) :
    steaneCorr (pauliSyndrome steaneData e) = e := by
  rcases pauliWeight_le_one e.1 e.2 h with hzero | hx | hz | hxy
  · have he : e = (0, 0) := Prod.ext hzero.1 hzero.2
    rw [he]
    simp [steaneCorr, steaneCorrX, steaneCorrZ, pauliSyndrome, steaneData, Matrix.mulVec_zero]
  · obtain ⟨a, hx1, hz1⟩ := hx
    have he : e = (unitLabel a, 0) := Prod.ext hx1 hz1
    rw [he]
    simp only [pauliSyndrome, steaneData, Matrix.mulVec_zero, steaneH_mulVec_single a]
    exact steaneCorr_singleX a
  · obtain ⟨a, hx1, hz1⟩ := hz
    have he : e = (0, unitLabel a) := Prod.ext hx1 hz1
    rw [he]
    simp only [pauliSyndrome, steaneData, Matrix.mulVec_zero, steaneH_mulVec_single a]
    exact steaneCorr_singleZ a
  · obtain ⟨a, hx1, hz1⟩ := hxy
    have he : e = (unitLabel a, unitLabel a) := Prod.ext hx1 hz1
    rw [he]
    simp only [pauliSyndrome, steaneData, steaneH_mulVec_single a]
    exact steaneCorr_singleY a

/-- The Steane decoder leaves zero residual label for every Pauli label of weight at most one. -/
theorem steaneDecoder_residual_zero (e : PauliLabel (Fin 7))
    (h : pauliWeight e.1 e.2 ≤ 1) :
    residualLabel steaneDecoder e = (0, 0) := by
  have hc : steaneCorr (pauliSyndrome steaneData e) = e :=
    steaneDecoder_corrects_weight_one e h
  show (e.1 + (steaneCorr (pauliSyndrome steaneData e)).1,
    e.2 + (steaneCorr (pauliSyndrome steaneData e)).2) = (0, 0)
  have hx : e.1 + e.1 = 0 := by funext i; exact zmod2_add_self _
  have hz : e.2 + e.2 = 0 := by funext i; exact zmod2_add_self _
  rw [hc, hx, hz]

/-- The zero Pauli label is a Steane stabilizer label. -/
theorem steaneIsStabilizerLabel_zero : IsStabilizerLabel steaneData (0, 0) := by
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · simp [steaneData]
  · simp [steaneData]

/-- The Steane decoder corrects every Pauli label of weight at most one, as in the seven-qubit
code of [Steane1996]. -/
theorem steaneDecoder_correctsUpTo : CorrectsUpTo steaneDecoder 1 := by
  intro e he
  rw [steaneDecoder_residual_zero e he]
  exact steaneIsStabilizerLabel_zero

/-- For a nonzero X-error syndrome component, the X correction is the single-site label indexed
by that syndrome column. -/
theorem steaneCorrX_index (η : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) (h : η.2 ≠ 0) :
    steaneCorrX η = steaneSingle (steaneColIdx η.2) := by
  simp [steaneCorrX, h]

/-- For a nonzero Z-error syndrome component, the Z correction is the single-site label indexed
by that syndrome column. -/
theorem steaneCorrZ_index (η : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) (h : η.1 ≠ 0) :
    steaneCorrZ η = steaneSingle (steaneColIdx η.1) := by
  simp [steaneCorrZ, h]

/-- The Steane X correction vanishes when its syndrome component is zero. -/
theorem steaneCorrX_zero (η : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) (h : η.2 = 0) :
    steaneCorrX η = 0 := by
  simp [steaneCorrX, h]

/-- The Steane Z correction vanishes when its syndrome component is zero. -/
theorem steaneCorrZ_zero (η : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) (h : η.1 = 0) :
    steaneCorrZ η = 0 := by
  simp [steaneCorrZ, h]

/-- The Steane decoder satisfies the minimum-weight soundness predicate. -/
theorem steaneDecoder_minimumWeightSound : MinimumWeightSound steaneDecoder := by
  intro η e he
  show pauliWeight (steaneCorrX η) (steaneCorrZ η) ≤ pauliWeight e.1 e.2

  have hcorr_le2 : pauliWeight (steaneCorrX η) (steaneCorrZ η) ≤ 2 := by
    by_cases hx0 : η.2 = 0
    · by_cases hz0 : η.1 = 0
      · rw [steaneCorrX_zero η hx0, steaneCorrZ_zero η hz0]
        rw [pauliWeight_zero]
        omega
      · rw [steaneCorrX_zero η hx0, steaneCorrZ_index η hz0]
        simp only [steaneSingle_eq]
        rw [pauliWeight_zero_unit]
        omega
    · by_cases hz0 : η.1 = 0
      · rw [steaneCorrZ_zero η hz0, steaneCorrX_index η hx0]
        simp only [steaneSingle_eq]
        rw [pauliWeight_unit_zero]
        omega
      · rw [steaneCorrX_index η hx0, steaneCorrZ_index η hz0]
        simp only [steaneSingle_eq, pauliWeight_unit_unit]
        split <;> omega

  by_cases hwt0 : pauliWeight e.1 e.2 = 0
  · have he0 : e = (0, 0) := by
      rcases pauliWeight_le_one e.1 e.2 (by omega) with hzero | hx1 | hz1 | hxy1
      · exact Prod.ext hzero.1 hzero.2
      · exfalso
        obtain ⟨a, hax, haz⟩ := hx1
        have : pauliWeight e.1 e.2 = 1 := by rw [hax, haz, pauliWeight_unit_zero]
        omega
      · exfalso
        obtain ⟨a, hax, haz⟩ := hz1
        have : pauliWeight e.1 e.2 = 1 := by rw [hax, haz, pauliWeight_zero_unit]
        omega
      · exfalso
        obtain ⟨a, hax, haz⟩ := hxy1
        have : pauliWeight e.1 e.2 = 1 := by rw [hax, haz, pauliWeight_unit_unit]; simp
        omega
    have hη : η = (0, 0) := by
      have h1 : η.1 = 0 := by
        have := congrArg Prod.fst he
        simpa [pauliSyndrome, steaneData, he0, Matrix.mulVec_zero] using this.symm
      have h2 : η.2 = 0 := by
        have := congrArg Prod.snd he
        simpa [pauliSyndrome, steaneData, he0, Matrix.mulVec_zero] using this.symm
      exact Prod.ext h1 h2
    rw [hη]
    have hcorrX : steaneCorrX (0, 0) = 0 := steaneCorrX_zero _ rfl
    have hcorrZ : steaneCorrZ (0, 0) = 0 := steaneCorrZ_zero _ rfl
    rw [hcorrX, hcorrZ, pauliWeight_zero]
    omega
  · by_cases hwt1 : pauliWeight e.1 e.2 = 1
    · rcases pauliWeight_le_one e.1 e.2 (by omega) with hzero | hx1 | hz1 | hxy1
      · exfalso
        have : pauliWeight e.1 e.2 = 0 := by rw [hzero.1, hzero.2, pauliWeight_zero]
        omega
      · obtain ⟨a, hax, haz⟩ := hx1
        have hη : η = (0, steaneCol a) := by
          have h1 : η.1 = 0 := by
            have := congrArg Prod.fst he
            simpa [pauliSyndrome, steaneData, haz, Matrix.mulVec_zero] using this.symm
          have h2 : η.2 = steaneCol a := by
            have := congrArg Prod.snd he
            simpa [pauliSyndrome, steaneData, hax, steaneH_mulVec_single a] using this.symm
          exact Prod.ext h1 h2
        rw [hη]
        have hcorrX : steaneCorrX (0, steaneCol a) = unitLabel a := by
          simp [steaneCorrX, steaneCol_ne_zero a, steaneColIdx_col a, steaneSingle_eq]
        have hcorrZ : steaneCorrZ (0, steaneCol a) = 0 := by
          simp [steaneCorrZ]
        rw [hcorrX, hcorrZ, pauliWeight_unit_zero]
        have : pauliWeight e.1 e.2 = 1 := by rw [hax, haz, pauliWeight_unit_zero]
        omega
      · obtain ⟨a, hax, haz⟩ := hz1
        have hη : η = (steaneCol a, 0) := by
          have h1 : η.1 = steaneCol a := by
            have := congrArg Prod.fst he
            simpa [pauliSyndrome, steaneData, haz, steaneH_mulVec_single a] using this.symm
          have h2 : η.2 = 0 := by
            have := congrArg Prod.snd he
            simpa [pauliSyndrome, steaneData, hax, Matrix.mulVec_zero] using this.symm
          exact Prod.ext h1 h2
        rw [hη]
        have hcorrX : steaneCorrX (steaneCol a, 0) = 0 := by
          simp [steaneCorrX]
        have hcorrZ : steaneCorrZ (steaneCol a, 0) = unitLabel a := by
          simp [steaneCorrZ, steaneCol_ne_zero a, steaneColIdx_col a, steaneSingle_eq]
        rw [hcorrX, hcorrZ, pauliWeight_zero_unit]
        have : pauliWeight e.1 e.2 = 1 := by rw [hax, haz, pauliWeight_zero_unit]
        omega
      · obtain ⟨a, hax, haz⟩ := hxy1
        have hη : η = (steaneCol a, steaneCol a) := by
          have h1 : η.1 = steaneCol a := by
            have := congrArg Prod.fst he
            simpa [pauliSyndrome, steaneData, haz, steaneH_mulVec_single a] using this.symm
          have h2 : η.2 = steaneCol a := by
            have := congrArg Prod.snd he
            simpa [pauliSyndrome, steaneData, hax, steaneH_mulVec_single a] using this.symm
          exact Prod.ext h1 h2
        rw [hη]
        have hcorrX : steaneCorrX (steaneCol a, steaneCol a) = unitLabel a := by
          simp [steaneCorrX, steaneCol_ne_zero a, steaneColIdx_col a, steaneSingle_eq]
        have hcorrZ : steaneCorrZ (steaneCol a, steaneCol a) = unitLabel a := by
          simp [steaneCorrZ, steaneCol_ne_zero a, steaneColIdx_col a, steaneSingle_eq]
        rw [hcorrX, hcorrZ]
        rw [pauliWeight_unit_unit]
        simp
        have : pauliWeight e.1 e.2 = 1 := by rw [hax, haz, pauliWeight_unit_unit]; simp
        omega
    · have : 2 ≤ pauliWeight e.1 e.2 := by omega
      omega

/-- Every Steane stabilizer label preserves logical reference states. -/
theorem steaneStabilizerLabel_preserves (e : PauliLabel (Fin 7))
    (he : IsStabilizerLabel steaneData e) :
    LogicalReferencePreserved steaneData e :=
  logicalReferencePreserved_of_stabilizer steaneData he

/-- The residual after decoding a Pauli label of weight at most one preserves logical reference
states. -/
theorem steaneResidual_preserves (e : PauliLabel (Fin 7)) (h : pauliWeight e.1 e.2 ≤ 1) :
    LogicalReferencePreserved steaneData (residualLabel steaneDecoder e) := by
  rw [steaneDecoder_residual_zero e h]
  exact logicalReferencePreserved_of_stabilizer steaneData steaneIsStabilizerLabel_zero

/-- The Steane recovery cost consists of syndrome extraction plus correction gates, the syndrome
measurements, and the decoder's classical running time. -/
theorem steaneRecoveryCost (η : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) :
    (recoveryCost steaneData steaneDecoder η).gates
        = syndromeExtractionGates steaneData + correctionGates (steaneCorr η) ∧
      (recoveryCost steaneData steaneDecoder η).measurements = syndromeMeasurements steaneData ∧
      (recoveryCost steaneData steaneDecoder η).classicalTime = steaneDecoder.decodeTime η := by
  simp [recoveryCost, steaneDecoder]

/-- Every Pauli label has a realizing recovery receipt for the Steane code and decoder. -/
theorem steaneRecoveryReceipt (e : PauliLabel (Fin 7)) :
    ∃ r : RecoveryReceipt steaneData steaneDecoder, r.Realizes e := by
  refine ⟨{ η := pauliSyndrome steaneData e
            applied := steaneCorr (pauliSyndrome steaneData e)
            cost := recoveryCost steaneData steaneDecoder (pauliSyndrome steaneData e) }, ?_⟩
  exact ⟨rfl, rfl, rfl⟩

/-- Two elements of `ZMod 2` sum to zero exactly when they are equal. -/
theorem zmod2_add_eq_zero_iff : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide

/-- The Steane decoder corrects Pauli errors of weight at most one in a single shot with zero
syndrome-noise budget. -/
theorem steaneDecoder_singleShot : CorrectsSingleShotNoisyUpTo steaneDecoder 1 0 := by
  intro e ηobs he hd
  have hd0 : ηobs = pauliSyndrome steaneData e := by
    have h := hd
    unfold syndromeDist at h
    have h1 : bitWeight ((pauliSyndrome steaneData e).1 + ηobs.1) = 0 := by omega
    have h2 : bitWeight ((pauliSyndrome steaneData e).2 + ηobs.2) = 0 := by omega
    have hz1 : (pauliSyndrome steaneData e).1 + ηobs.1 = 0 := bitWeight_eq_zero h1
    have hz2 : (pauliSyndrome steaneData e).2 + ηobs.2 = 0 := bitWeight_eq_zero h2
    have e1 : (pauliSyndrome steaneData e).1 = ηobs.1 := by
      funext i
      exact (zmod2_add_eq_zero_iff _ _).mp (congrFun hz1 i)
    have e2 : (pauliSyndrome steaneData e).2 = ηobs.2 := by
      funext i
      exact (zmod2_add_eq_zero_iff _ _).mp (congrFun hz2 i)
    exact Prod.ext e1.symm e2.symm
  rw [hd0]
  exact steaneDecoder_correctsUpTo e he

/-- For a Pauli error of weight at most one, correcting its true syndrome leaves a Steane
stabilizer label. -/
theorem steaneDecoder_succeeds_on_true_syndrome (e : PauliLabel (Fin 7))
    (h : pauliWeight e.1 e.2 ≤ 1) :
    IsStabilizerLabel steaneData
      (residualFromObserved steaneDecoder e (pauliSyndrome steaneData e)) :=
  steaneDecoder_correctsUpTo e h

/-- The sum of Bernoulli subset weights over all subsets of a finite set is one. -/
theorem binom_subset_sum_eq_one {α : Type} [Fintype α] [DecidableEq α] (p : ℝ) (U : Finset α) :
    ∑ T ∈ U.powerset, p ^ T.card * (1 - p) ^ (U.card - T.card) = 1 := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert a U ha ih =>
      have hcard : (insert a U).card = U.card + 1 := by simp [ha]
      rw [Finset.sum_powerset_insert ha
        (fun T => p ^ T.card * (1 - p) ^ ((insert a U).card - T.card))]
      have hfirst : (∑ T ∈ U.powerset, p ^ T.card * (1 - p) ^ ((insert a U).card - T.card))
          = (1 - p) * (∑ T ∈ U.powerset, p ^ T.card * (1 - p) ^ (U.card - T.card)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        have hle : T.card ≤ U.card :=
          Finset.card_le_card (Finset.mem_powerset.mp hT)
        have hsub : (insert a U).card - T.card = (U.card - T.card) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      have hsecond :
          (∑ T ∈ U.powerset, p ^ (insert a T).card *
            (1 - p) ^ ((insert a U).card - (insert a T).card))
          = p * (∑ T ∈ U.powerset, p ^ T.card * (1 - p) ^ (U.card - T.card)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        have hle : T.card ≤ U.card :=
          Finset.card_le_card (Finset.mem_powerset.mp hT)
        have hnot : a ∉ T := fun hmem => ha (Finset.mem_powerset.mp hT hmem)
        have h1 : (insert a T).card = T.card + 1 := by simp [hnot]
        have h2 : (insert a U).card - (T.card + 1) = (U.card - T.card) := by omega
        rw [h1, h2, pow_succ]
        ring
      rw [hfirst, hsecond, ih]
      ring

/-- The Steane noise weights sum to one over all fault subsets. -/
theorem steaneNoiseLaw_sum_one (ζ : ℕ) (p : ℝ) :
    ∑ F ∈ (Finset.univ : Finset (Finset (Fin ζ))), steaneNoiseLaw ζ p F = 1 := by
  have hset : (Finset.univ : Finset (Finset (Fin ζ)))
      = (Finset.univ : Finset (Fin ζ)).powerset := by
    ext F
    constructor
    · intro hF
      exact Finset.mem_powerset.mpr (Finset.subset_univ F)
    · intro hF
      exact Finset.mem_univ F
  rw [hset]
  have h := binom_subset_sum_eq_one p (Finset.univ : Finset (Fin ζ))
  simpa [steaneNoiseLaw, Fintype.card_fin] using h

/-- For `0 ≤ p ≤ 1`, the Steane noise law satisfies the adversarial fault budget with `ζ`
locations. -/
theorem steaneNoiseLaw_adversarial (ζ : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    AdversarialFaultBudget (steaneNoiseLaw ζ p) ζ := by
  refine ⟨?_, ?_, ?_⟩
  · intro F
    unfold steaneNoiseLaw
    positivity
  · exact steaneNoiseLaw_sum_one ζ p
  · intro F hF
    have hle : F.card ≤ (Finset.univ : Finset (Fin ζ)).card :=
      Finset.card_le_card (Finset.subset_univ F)
    have hcard : (Finset.univ : Finset (Fin ζ)).card = ζ := by simp
    omega

/-- The Steane round gadget satisfies ideal correctness. -/
theorem steaneRoundGadget_idealCorrect : steaneRoundGadget.IsIdealCorrect := by
  refine ⟨steaneIsStabilizerLabel_zero, ?_⟩
  decide

/-- A nonzero coordinate of `steaneResidualX F` must lie in the fault set `F`. -/
theorem steaneResidualX_ne_zero {F : Finset (Fin 7)} {k : Fin 7}
    (h : steaneResidualX F k ≠ 0) : k ∈ F := by
  by_contra hk
  simp [steaneResidualX, hk] at h

/-- The Steane round gadget satisfies fault tolerance at one fault. -/
theorem steaneRoundGadget_faultTolerant : steaneRoundGadget.IsFaultTolerantAt 1 := by
  intro F hF
  have hsub : Finset.univ.filter (fun i : Fin 7 =>
      steaneResidualX F i ≠ 0 ∨ (0 : Fin 7 → ZMod 2) i ≠ 0) ⊆ F := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hi with hi | hi
    · exact steaneResidualX_ne_zero hi
    · simp at hi
  have hcard : (Finset.univ.filter (fun i : Fin 7 =>
      steaneResidualX F i ≠ 0 ∨ (0 : Fin 7 → ZMod 2) i ≠ 0)).card ≤ F.card :=
    Finset.card_le_card hsub
  show pauliWeight (steaneResidualX F) (0 : Fin 7 → ZMod 2) ≤ 1
  unfold pauliWeight
  exact hcard.trans hF

/-- The single Steane round gadget has cumulative spacetime cost twenty-one. -/
theorem steaneCumulativeSpaceTime : cumulativeSpaceTime [steaneRoundGadget] = 21 := by
  simp [cumulativeSpaceTime, steaneRoundGadget]

/-- The single Steane round gadget has peak space cost seven. -/
theorem steanePeakSpace : peakSpace [steaneRoundGadget] = 7 := by
  simp [peakSpace, steaneRoundGadget]

/-- The composed error-window expression for one Steane round, space seven, and tolerance one is
`21 * p ^ 2`. -/
theorem steaneComposedErrWindow (p : ℝ) :
    composedErrWindow [steaneRoundGadget] 7 1 p = 21 * p ^ 2 := by
  have hchoose : Nat.choose 7 2 = 21 := by decide
  simp [composedErrWindow, hchoose]

/-- The composed failure-mass expression for one Steane round with tolerance one is `21 * p ^
2`. -/
theorem steaneComposedFailureMass (p : ℝ) :
    composedFailureMass [steaneRoundGadget] 1 p = 21 * p ^ 2 := by
  have hchoose : Nat.choose 7 2 = 21 := by decide
  simp [composedFailureMass, GadgetSpec.failureMass, steaneRoundGadget, hchoose]

/-- The finite fault-tolerance parameter record built from the Steane code, decoder, and
syndrome-round gadget. -/
def steaneFtRealization : FtRealization where
  N := 7
  mX := 3
  mZ := 3
  code := steaneData
  prog := steaneDecoder
  t := 1
  ζ := 7
  gadgets := [steaneRoundGadget]
  pTh := 0
  ε := 0
  budget := cumulativeSpaceTime [steaneRoundGadget]
  peak := peakSpace [steaneRoundGadget]

end Qatlib.Concepts.CodingDecoding.CssRecovery
