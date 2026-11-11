/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.MeasurementGateSemantics
import Qatlib.Concepts.SpinorSampling.Model.BornCurrentRecords

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Native Born Bridge

Native Born Bridge constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open scoped BigOperators
open Qatlib ShiftCircuit

/-- Constructors for Measurement Gate in the native born bridge model. -/
inductive MeasurementGate (n : ℕ) where
  | native (gate : NativeGate (Fin n))
  | sdg (wire : Fin n)

/-- Construction for velocity Word in the native born bridge model. -/
def velocityWord (d r : ℕ) (j : Fin d) (positiveNeighbor : Bool) :
    List (MeasurementGate (registerWidth d r)) :=
  [.native (.h (testWire d r))] ++
    (nativeWord (if positiveNeighbor then (spatialIncrementWord d r j).reverse
      else spatialIncrementWord d r j)).map MeasurementGate.native ++
    [.sdg (testWire d r), .native (.h (testWire d r))]

/-- Construction for spin Readout Wire in the native born bridge model. -/
def spinReadoutWire (d r : ℕ) : Fin (d*r+1) := ⟨d*r,Nat.lt_succ_self _⟩

/-- Construction for spin Word in the native born bridge model. -/
def spinWord (d r : ℕ) (p : Fin 3) : List (MeasurementGate (d*r+1)) :=
  if p=0 then [.native (.h (spinReadoutWire d r))] else
    if p=1 then [.sdg (spinReadoutWire d r), .native (.h (spinReadoutWire d r))] else []

/-- Construction for spin Decode in the native born bridge model. -/
def spinDecode (d r : ℕ) (x : Reg (d*r+1)) : (Fin d → Fin (2^r)) × Bool :=
  ((fun j => littleAddress r (fun i => x (Fin.castSucc (finProdFinEquiv (j,i))))), x (spinReadoutWire d r))

/-- Construction for velocity Record in the native born bridge model. -/
def velocityRecord (d r : ℕ) (positiveNeighbor : Bool) (x : Reg (registerWidth d r)) :
    (Fin d → Fin (2^r)) × Bool :=
  (siteAddress d r x, if positiveNeighbor then x (testWire d r) else !x (testWire d r))

noncomputable section

/-- Construction for measurement Matrix in the native born bridge model. -/
def measurementMatrix {n : ℕ} : MeasurementGate n → ReflectionGate n
  | .native g => nativeMatrix g
  | .sdg w => .inl (w,readoutSdgMatrix)

/-- Construction for measurement Program in the native born bridge model. -/
def measurementProgram {n : ℕ} (word : List (MeasurementGate n)) : Circuit (Reg n) :=
  reflectionCompile (word.map measurementMatrix)

/-- Complete original `measurement_program_counts` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem measurement_program_counts {n : ℕ} (word : List (MeasurementGate n)) :
    QueryCount (measurementProgram word)=0 ∧ GateCount (measurementProgram word)=word.length := by
  constructor
  · exact queryCount_reflectionCompile _
  · simpa only [measurementProgram,List.length_map] using gateCount_reflectionCompile (word.map measurementMatrix)

/-- Complete original `readout_sdg_unitary` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem readout_sdg_unitary : readoutSdgMatrix ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext b c
  cases b <;> cases c <;>
    simp [readoutSdgMatrix, Matrix.mul_apply, Matrix.diagonal_apply]

/-- Complete original `velocity_word_legal` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem velocity_word_legal (d r : ℕ) (j : Fin d) (positiveNeighbor : Bool) :
    reflectionLegal ((velocityWord d r j positiveNeighbor).map measurementMatrix) := by
  let selected := if positiveNeighbor then (spatialIncrementWord d r j).reverse else spatialIncrementWord d r j
  have hg : ∀ g ∈ spatialIncrementWord d r j, legal g :=
    increment_aux_legal [testWire d r] (axisWires d r j) (workWires d r) (layout_wires_nodup d r j)
  have hsel : ∀ g ∈ selected, legal g := by
    cases positiveNeighbor
    · exact hg
    · simpa only [selected, ite_true, List.mem_reverse] using hg
  have hshift : reflectionLegal ((nativeWord selected).map nativeMatrix) := by
    rw [native_word_compile]
    exact compile_bits_legal selected hsel
  intro g hgate
  have hmem : g=.inl (testWire d r,Hadamard) ∨ g∈(nativeWord selected).map nativeMatrix ∨
      g=.inl (testWire d r,readoutSdgMatrix) ∨ g=.inl (testWire d r,Hadamard) := by
    simp only [velocityWord, List.map_append, List.map_cons, List.map_nil,
      List.map_map, Function.comp_def, measurementMatrix, nativeMatrix, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hgate
    exact hgate
  rcases hmem with h | h | h | h
  · subst g
    exact hadamard_unitary
  · exact hshift g h
  · subst g
    exact readout_sdg_unitary
  · subst g
    exact hadamard_unitary

/-- Complete original `spin_word_legal` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem spin_word_legal (d r : ℕ) (p : Fin 3) :
    reflectionLegal ((spinWord d r p).map measurementMatrix) := by
  fin_cases p <;>
    simp [spinWord, measurementMatrix, nativeMatrix, reflectionLegal, reflectionGateLegal,
      hadamard_unitary, readout_sdg_unitary]

-- The physical low-endian neighbor is the same spatial equivalence used by L_h.
/-- Complete original `decoded_neighbor_eq_original` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem decoded_neighbor_eq_original (d r : ℕ) (j : Fin d) :
    decodedNeighbor d r j=periodicUnitShift d (2^r) j := by
  apply Equiv.ext
  intro s
  funext k
  apply (ZMod.finEquiv (2^r)).injective
  rw [periodic_unit_shift_coordinates]
  by_cases hk : k=j
  · simp [decodedNeighbor, Equiv.piCongrRight, hk, finRotate_apply]
  · simp [decodedNeighbor, Equiv.piCongrRight, hk]

/-- Abbreviation for Measurement Label in the native born bridge model. -/
abbrev MeasurementLabel (d r : ℕ) := Bool × ((Fin d → Fin (2^r)) × Bool)

/-- Construction for encode Label in the native born bridge model. -/
def encodeLabel (d r : ℕ) (z : MeasurementLabel d r) : Reg (registerWidth d r) :=
  encodeClean d r z.2.1 z.2.2 z.1

/-- Complete original `encode_label_injective` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem encode_label_injective (d r : ℕ) : Function.Injective (encodeLabel d r) := by
  intro z w h
  have hs := congrArg (siteAddress d r) h
  have hspin := congrFun h (spinWire d r)
  have ht := congrFun h (testWire d r)
  simp only [encodeLabel, encode_clean_site] at hs
  simp only [encodeLabel, encode_clean_spin] at hspin
  simp only [encodeLabel, encode_clean_test] at ht
  exact Prod.ext ht (Prod.ext hs hspin)

/-- Complete original `site_address_update_off` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
private theorem site_address_update_off (d r : ℕ) (x : Reg (registerWidth d r))
    (w : Fin (registerWidth d r)) (b : Bool) (hw : ∀ j, w ∉ axisWires d r j) :
    siteAddress d r (Function.update x w b)=siteAddress d r x := by
  funext j
  change littleAddress r (fun i => Function.update x w b (axisWire d r j i))=
    littleAddress r (fun i => x (axisWire d r j i))
  congr 1
  funext i
  have hne : axisWire d r j i ≠ w := by
    intro h
    exact hw j (List.mem_ofFn.mpr ⟨i,h⟩)
  exact Function.update_of_ne hne _ _

/-- Complete original `spin_test_ne` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
private theorem spin_test_ne (d r : ℕ) : spinWire d r ≠ testWire d r := by
  intro h
  have hh := congrArg Fin.val h
  change d*r=d*r+1 at hh
  omega

/-- Complete original `work_readout_ne` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
private theorem work_readout_ne (d r : ℕ) (i : Fin (r-2)) :
    workWire d r i ≠ spinWire d r ∧ workWire d r i ≠ testWire d r := by
  constructor <;> intro h <;> have hh := congrArg Fin.val h
  · change d*r+2+i.val=d*r at hh
    omega
  · change d*r+2+i.val=d*r+1 at hh
    omega

/-- Complete original `encode_clean_update_test` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem encode_clean_update_test (d r : ℕ) (s : Fin d → Fin (2^r)) (spin test b : Bool) :
    Function.update (encodeClean d r s spin test) (testWire d r) b=encodeClean d r s spin b := by
  apply layout_readout_injective d r
  · simp only [site_address_update_off d r _ _ _ (test_wire_not_axis d r), encode_clean_site]
  · simp only [Function.update_of_ne (spin_test_ne d r), encode_clean_spin]
  · simp only [Function.update_self, encode_clean_test]
  · intro i
    simp only [Function.update_of_ne (work_readout_ne d r i).2, encode_clean_work]

/-- Complete original `encode_clean_update_spin` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem encode_clean_update_spin (d r : ℕ) (s : Fin d → Fin (2^r)) (spin test b : Bool) :
    Function.update (encodeClean d r s spin test) (spinWire d r) b=encodeClean d r s b test := by
  apply layout_readout_injective d r
  · simp only [site_address_update_off d r _ _ _ (spin_wire_not_axis d r), encode_clean_site]
  · simp only [Function.update_self, encode_clean_spin]
  · simp only [Function.update_of_ne (spin_test_ne d r).symm, encode_clean_test]
  · intro i
    simp only [Function.update_of_ne (work_readout_ne d r i).1, encode_clean_work]

/-- Construction for encode Amplitude in the native born bridge model. -/
def encodeAmplitude (d r : ℕ) (f : Bool → ((Fin d → Fin (2^r)) × Bool) → ℂ) :
    QState (Reg (registerWidth d r)) :=
  ∑ z : MeasurementLabel d r, f z.1 z.2 • Ket (encodeLabel d r z)

/-- Complete original `encode_amplitude_apply_label` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem encode_amplitude_apply_label (d r : ℕ)
    (f : Bool → ((Fin d → Fin (2^r)) × Bool) → ℂ) (z : MeasurementLabel d r) :
    encodeAmplitude d r f (encodeLabel d r z)=f z.1 z.2 := by
  simp only [encodeAmplitude, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Qatlib.Foundations.PureStateMath.ket_apply]
  rw [Finset.sum_eq_single z]
  · simp
  · intro w _ hw
    have hne : encodeLabel d r z ≠ encodeLabel d r w := by
      intro h
      exact hw ((encode_label_injective d r h).symm)
    simp only [ite_eq_right hne, mul_zero]
  · simp

/-- Complete original `test_wire_ket` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem test_wire_ket (d r : ℕ) (U : Matrix Bool Bool ℂ) (z : MeasurementLabel d r) :
    ApplyGate (wireGate (registerWidth d r) (testWire d r) U) (Ket (encodeLabel d r z)) =
      ∑ b : Bool, U b z.1 • Ket (encodeLabel d r (b,z.2)) := by
  rw [applyGate_wireGate_ket]
  simp only [encodeLabel, encode_clean_test, encode_clean_update_test, Fintype.sum_bool]
  exact add_comm _ _

/-- Complete original `spin_wire_ket` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem spin_wire_ket (d r : ℕ) (U : Matrix Bool Bool ℂ) (z : MeasurementLabel d r) :
    ApplyGate (wireGate (registerWidth d r) (spinWire d r) U) (Ket (encodeLabel d r z)) =
      ∑ b : Bool, U b z.2.2 • Ket (encodeLabel d r (z.1,z.2.1,b)) := by
  rw [applyGate_wireGate_ket]
  simp only [encodeLabel, encode_clean_spin, encode_clean_update_spin, Fintype.sum_bool]
  exact add_comm _ _

/-- Complete original `apply_gate_sum_smul` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
private theorem apply_gate_sum_smul {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (U : Matrix I I ℂ) (f : J → QState I) (a : J → ℂ) :
    ApplyGate U (∑ j, a j • f j)=∑ j, a j • ApplyGate U (f j) := by
  change Matrix.mulVec U (∑ j, a j • f j)=_
  rw [Matrix.mulVec_sum]
  exact Finset.sum_congr rfl fun j _ => Matrix.mulVec_smul _ _ _

/-- Construction for test Action in the native born bridge model. -/
def testAction {S : Type*} (U : Matrix Bool Bool ℂ) (f : Bool → S × Bool → ℂ)
    (b : Bool) (x : S × Bool) : ℂ := ApplyGate U (fun q => f q x) b

/-- Construction for spin Action in the native born bridge model. -/
def spinAction {S : Type*} (U : Matrix Bool Bool ℂ) (f : Bool → S × Bool → ℂ)
    (b : Bool) (x : S × Bool) : ℂ := ApplyGate U (fun q => f b (x.1,q)) x.2

/-- Complete original `test_action_h` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem test_action_h {S : Type*} (f : Bool → S × Bool → ℂ) :
    testAction Hadamard f=readoutH f := by
  funext b x
  exact (readout_h_apply_gate f b x).symm

/-- Complete original `test_action_sdg` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem test_action_sdg {S : Type*} (f : Bool → S × Bool → ℂ) :
    testAction readoutSdgMatrix f=readoutSdg f := by
  funext b x
  exact (readout_sdg_apply_gate f b x).symm

/-- Complete original `test_matrix_transport` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem test_matrix_transport (d r : ℕ) (U : Matrix Bool Bool ℂ)
    (f : Bool → ((Fin d → Fin (2^r)) × Bool) → ℂ) :
    ApplyGate (wireGate (registerWidth d r) (testWire d r) U) (encodeAmplitude d r f) =
      encodeAmplitude d r (testAction U f) := by
  unfold encodeAmplitude
  rw [apply_gate_sum_smul]
  simp_rw [test_wire_ket, Finset.smul_sum, smul_smul]
  simp only [testAction, ApplyGate, Matrix.mulVec, dotProduct, Finset.sum_smul]
  conv_lhs => rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type]
  calc
    _ = ∑ c : Bool, ∑ b : Bool, ∑ x : (Fin d → Fin (2^r)) × Bool,
        (f c x*U b c) • Ket (encodeLabel d r (b,x)) := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm
    _ = ∑ b : Bool, ∑ c : Bool, ∑ x : (Fin d → Fin (2^r)) × Bool,
        (f c x*U b c) • Ket (encodeLabel d r (b,x)) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      simp only [mul_comm]

/-- Complete original `spin_matrix_transport` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem spin_matrix_transport (d r : ℕ) (U : Matrix Bool Bool ℂ)
    (f : Bool → ((Fin d → Fin (2^r)) × Bool) → ℂ) :
    ApplyGate (wireGate (registerWidth d r) (spinWire d r) U) (encodeAmplitude d r f) =
      encodeAmplitude d r (spinAction U f) := by
  unfold encodeAmplitude
  rw [apply_gate_sum_smul]
  simp_rw [spin_wire_ket, Finset.smul_sum, smul_smul]
  simp only [spinAction, ApplyGate, Matrix.mulVec, dotProduct, Finset.sum_smul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- Complete original `encode_controlled_site` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem encode_controlled_site (d r : ℕ)
    (p : (Fin d → Fin (2^r)) ≃ (Fin d → Fin (2^r))) (z : MeasurementLabel d r) :
    encodeLabel d r (controlledSiteBasis p z)=
      encodeClean d r (if z.1 then p z.2.1 else z.2.1) z.2.2 z.1 := by
  rcases z with ⟨b,s,spin⟩
  cases b <;> rfl

/-- Complete original `encoded_permuted_sum` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem encoded_permuted_sum (d r : ℕ) (e : MeasurementLabel d r ≃ MeasurementLabel d r)
    (f : MeasurementLabel d r → ℂ) :
    (∑ z, f z • Ket (encodeLabel d r (e z))) =
      ∑ z, f (e.symm z) • Ket (encodeLabel d r z) := by
  simpa only [Equiv.symm_apply_apply] using
    e.sum_comp (fun z => f (e.symm z) • Ket (encodeLabel d r z))

/-- Complete original `encoded_controlled_sum` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem encoded_controlled_sum (d r : ℕ)
    (p : (Fin d → Fin (2^r)) ≃ (Fin d → Fin (2^r)))
    (f : Bool → ((Fin d → Fin (2^r)) × Bool) → ℂ) :
    (∑ z : MeasurementLabel d r, f z.1 z.2 •
      Ket (encodeClean d r (if z.1 then p z.2.1 else z.2.1) z.2.2 z.1)) =
      encodeAmplitude d r (controlledSite p f) := by
  calc
    _ = ∑ z : MeasurementLabel d r, f z.1 z.2 •
        Ket (encodeLabel d r (controlledSiteBasis p z)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [encode_controlled_site]
    _ = ∑ z : MeasurementLabel d r,
        f ((controlledSiteBasis p).symm z).1 ((controlledSiteBasis p).symm z).2 •
          Ket (encodeLabel d r z) := encoded_permuted_sum d r (controlledSiteBasis p) _
    _ = _ := rfl

/-- Construction for forward Shift Program in the native born bridge model. -/
def forwardShiftProgram (d r : ℕ) (j : Fin d) : Circuit (Reg (registerWidth d r)) :=
  reflectionCompile ((nativeWord (spatialIncrementWord d r j)).map nativeMatrix)

/-- Construction for reverse Shift Program in the native born bridge model. -/
def reverseShiftProgram (d r : ℕ) (j : Fin d) : Circuit (Reg (registerWidth d r)) :=
  reflectionCompile ((nativeWord (spatialIncrementWord d r j).reverse).map nativeMatrix)

/-- Complete original `forward_shift_transport` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem forward_shift_transport (d r : ℕ) (j : Fin d)
    (f : Bool → ((Fin d → Fin (2^r)) × Bool) → ℂ) :
    Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
      (forwardShiftProgram d r j) (encodeAmplitude d r f) =
      encodeAmplitude d r (controlledSite (decodedNeighbor d r j) f) := by
  unfold forwardShiftProgram
  change Run 1 _ (∑ z : MeasurementLabel d r,
    f z.1 z.2 • Ket (encodeClean d r z.2.1 z.2.2 z.1)) = _
  rw [native_spatial_increment_encoded_superposition]
  exact encoded_controlled_sum d r (decodedNeighbor d r j) f

/-- Complete original `reverse_shift_transport` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem reverse_shift_transport (d r : ℕ) (j : Fin d)
    (f : Bool → ((Fin d → Fin (2^r)) × Bool) → ℂ) :
    Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
      (reverseShiftProgram d r j) (encodeAmplitude d r f) =
      encodeAmplitude d r (controlledSite (decodedNeighbor d r j).symm f) := by
  unfold reverseShiftProgram
  change Run 1 _ (∑ z : MeasurementLabel d r,
    f z.1 z.2 • Ket (encodeClean d r z.2.1 z.2.2 z.1)) = _
  rw [native_spatial_reverse_encoded_superposition]
  exact encoded_controlled_sum d r (decodedNeighbor d r j).symm f

/-- True selects the positive neighbor in the velocity record, hence basis -1. -/
def velocityProgram (d r : ℕ) (j : Fin d) (positiveNeighbor : Bool) :
    Circuit (Reg (registerWidth d r)) := measurementProgram (velocityWord d r j positiveNeighbor)

/-- Complete original `velocity_program_expand` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem velocity_program_expand (d r : ℕ) (j : Fin d) (positiveNeighbor : Bool) :
    velocityProgram d r j positiveNeighbor =
      [Step.gate (wireGate (registerWidth d r) (testWire d r) Hadamard)] ++
        (if positiveNeighbor then reverseShiftProgram d r j else forwardShiftProgram d r j) ++
        [Step.gate (wireGate (registerWidth d r) (testWire d r) readoutSdgMatrix),
         Step.gate (wireGate (registerWidth d r) (testWire d r) Hadamard)] := by
  cases positiveNeighbor <;>
    simp [velocityProgram, measurementProgram, velocityWord, measurementMatrix, nativeMatrix,
      reflectionCompile, reflectionGateMatrix, forwardShiftProgram, reverseShiftProgram,
      List.map_append, List.map_map, Function.comp_def]

/-- Complete original `velocity_program_unitary` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem velocity_program_unitary (d r : ℕ) (j : Fin d) (positiveNeighbor : Bool) :
    IsUnitaryCircuit (velocityProgram d r j positiveNeighbor) :=
  (local_reflection_gate_support_unitarity_counts (registerWidth d r)
    ((velocityWord d r j positiveNeighbor).map measurementMatrix) (velocity_word_legal d r j positiveNeighbor)).1

/-- Complete original `velocity_program_counts` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem velocity_program_counts (d r : ℕ) (j : Fin d) (positiveNeighbor : Bool) :
    QueryCount (velocityProgram d r j positiveNeighbor)=0 ∧
      GateCount (velocityProgram d r j positiveNeighbor)=(velocityWord d r j positiveNeighbor).length :=
  measurement_program_counts _

/-- Complete original `velocity_program_evolution_positive` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem velocity_program_evolution_positive (d r : ℕ) (j : Fin d)
    (f : Bool → ((Fin d → Fin (2^r)) × Bool) → ℂ) :
    Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
      (velocityProgram d r j true) (encodeAmplitude d r f) =
      encodeAmplitude d r (readoutH (readoutSdg
        (controlledSite (decodedNeighbor d r j).symm (readoutH f)))) := by
  simp only [velocity_program_expand, ite_true, run_append, run_gate, run_nil,
    test_matrix_transport, reverse_shift_transport, test_action_h, test_action_sdg]

/-- Complete original `velocity_program_evolution_negative` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem velocity_program_evolution_negative (d r : ℕ) (j : Fin d)
    (f : Bool → ((Fin d → Fin (2^r)) × Bool) → ℂ) :
    Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
      (velocityProgram d r j false) (encodeAmplitude d r f) =
      encodeAmplitude d r (readoutH (readoutSdg
        (controlledSite (decodedNeighbor d r j) (readoutH f)))) := by
  simp only [velocity_program_expand, Bool.false_eq_true, ite_false, run_append, run_gate, run_nil,
    test_matrix_transport, forward_shift_transport, test_action_h, test_action_sdg]

/-- Complete original `velocity_program_supplied_state` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem velocity_program_supplied_state (d r : ℕ) (j : Fin d) (positiveNeighbor : Bool)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) :
    Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
      (velocityProgram d r j positiveNeighbor)
      (encodeAmplitude d r (suppliedAncillaState a b c k)) =
      encodeAmplitude d r (velocityGateState a b c k
        (if positiveNeighbor then periodicUnitShift d (2^r) j else (periodicUnitShift d (2^r) j).symm)) := by
  cases positiveNeighbor
  · simpa only [velocityGateState, decoded_neighbor_eq_original, Equiv.symm_symm,
      Bool.false_eq_true, ite_false] using
      velocity_program_evolution_negative d r j (suppliedAncillaState a b c k)
  · simpa only [velocityGateState, decoded_neighbor_eq_original, ite_true] using
      velocity_program_evolution_positive d r j (suppliedAncillaState a b c k)

/-- Construction for basis At in the native born bridge model. -/
def basisAt (d r : ℕ) (s : Fin d → Fin (2^r)) (spin test : Bool) (work : Reg (r-2)) :
    Reg (registerWidth d r) := (layoutEquiv d r).symm (s,spin,test,work)

/-- Complete original `decode_basis_at` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem decode_basis_at (d r : ℕ) (s : Fin d → Fin (2^r)) (spin test : Bool) (work : Reg (r-2)) :
    decodeLayout d r (basisAt d r s spin test work)=(s,spin,test,work) :=
  (layoutEquiv d r).apply_symm_apply _

/-- Complete original `encode_amplitude_at_clean` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem encode_amplitude_at_clean (d r : ℕ)
    (f : Bool → ((Fin d → Fin (2^r)) × Bool) → ℂ)
    (s : Fin d → Fin (2^r)) (spin test : Bool) :
    encodeAmplitude d r f (basisAt d r s spin test (fun _ => false))=f test (s,spin) :=
  encode_amplitude_apply_label d r f (test,s,spin)

/-- Complete original `encode_amplitude_at_dirty` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem encode_amplitude_at_dirty (d r : ℕ)
    (f : Bool → ((Fin d → Fin (2^r)) × Bool) → ℂ)
    (s : Fin d → Fin (2^r)) (spin test : Bool) (work : Reg (r-2))
    (hw : work ≠ (fun _ => false)) : encodeAmplitude d r f (basisAt d r s spin test work)=0 := by
  simp only [encodeAmplitude, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro z _
  have hne : basisAt d r s spin test work ≠ encodeLabel d r z := by
    intro h
    have hd := congrArg (decodeLayout d r) h
    rw [decode_basis_at] at hd
    change (s,spin,test,work)=decodeLayout d r (encodeClean d r z.2.1 z.2.2 z.1) at hd
    rw [decode_encode_clean] at hd
    exact hw (congrArg (fun q : LayoutData d r => q.2.2.2) hd)
  simp only [Qatlib.Foundations.PureStateMath.ket_apply, ite_eq_right hne, mul_zero]

/-- Literal Born marginal: all spin/work outcomes are included, never conditioned. -/
def physicalVelocityMass (d r : ℕ) (ψ : QState (Reg (registerWidth d r)))
    (out : (Fin d → Fin (2^r)) × Bool) : ℝ :=
  ∑ spin : Bool, ∑ work : Reg (r-2), BornProb ψ (basisAt d r out.1 spin out.2 work)

/-- Complete original `physical_velocity_mass_encoded` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem physical_velocity_mass_encoded (d r : ℕ)
    (f : Bool → ((Fin d → Fin (2^r)) × Bool) → ℂ)
    (out : (Fin d → Fin (2^r)) × Bool) :
    physicalVelocityMass d r (encodeAmplitude d r f) out =
      ∑ spin : Bool, BornProb (f out.2) (out.1,spin) := by
  unfold physicalVelocityMass
  apply Finset.sum_congr rfl
  intro spin _
  rw [Finset.sum_eq_single (fun _ => false)]
  · simp only [BornProb, encode_amplitude_at_clean]
  · intro work _ hw
    rw [BornProb, encode_amplitude_at_dirty d r f out.1 spin out.2 work hw]
    simp
  · simp

/-- Complete original `physical_velocity_mass_total` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem physical_velocity_mass_total (d r : ℕ) (ψ : QState (Reg (registerWidth d r))) :
    (∑ out : (Fin d → Fin (2^r)) × Bool, physicalVelocityMass d r ψ out) =
      ∑ x : Reg (registerWidth d r), BornProb ψ x := by
  calc
    _ = ∑ z : LayoutData d r, BornProb ψ ((layoutEquiv d r).symm z) := by
      simp only [physicalVelocityMass, basisAt, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = _ := (layoutEquiv d r).symm.sum_comp (BornProb ψ)

/-- Complete original `physical_velocity_mass_supplied` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem physical_velocity_mass_supplied (d r : ℕ) (j : Fin d) (positiveNeighbor : Bool)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (out : (Fin d → Fin (2^r)) × Bool) :
    physicalVelocityMass d r
      (Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
        (velocityProgram d r j positiveNeighbor) (encodeAmplitude d r (suppliedAncillaState a b c k))) out =
      velocityBornMass a b c k
        (if positiveNeighbor then periodicUnitShift d (2^r) j else (periodicUnitShift d (2^r) j).symm) out := by
  rw [velocity_program_supplied_state, physical_velocity_mass_encoded]
  rfl

/-- Complete original `native_velocity_normalized` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_velocity_normalized (d r : ℕ) (j : Fin d) (positiveNeighbor : Bool)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    Normalized (Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
      (velocityProgram d r j positiveNeighbor) (encodeAmplitude d r (suppliedAncillaState a b c k))) := by
  change (∑ x, BornProb _ x)=1
  rw [← physical_velocity_mass_total]
  simp_rw [physical_velocity_mass_supplied, velocity_born_mass a b c k hz]
  rw [Fintype.sum_prod_type]
  simp_rw [signed_record_cell_mass]
  simp [nsmul_eq_mul]

/-- Complete original `native_supplied_input_normalized` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_supplied_input_normalized (d r : ℕ)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    Normalized (encodeAmplitude d r (suppliedAncillaState a b c k)) := by
  change (∑ x, BornProb _ x)=1
  rw [← physical_velocity_mass_total]
  simp_rw [physical_velocity_mass_encoded]
  simpa [Normalized, Fintype.sum_prod_type, Fintype.sum_bool, BornProb, suppliedAncillaState] using
    supplied_spin_state_normalized a b c k hz

/-- Construction for native Current Weight in the native born bridge model. -/
def nativeCurrentWeight (d r : ℕ) (j : Fin d) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (out : (Fin d → Fin (2^r)) × Bool) : ℝ :=
  (physicalVelocityMass d r
      (Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
        (velocityProgram d r j true) (encodeAmplitude d r (suppliedAncillaState a b c k))) out +
   physicalVelocityMass d r
      (Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
        (velocityProgram d r j false) (encodeAmplitude d r (suppliedAncillaState a b c k))) (out.1,!out.2))/2

/-- Complete original `native_current_weight_eq` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_current_weight_eq (d r : ℕ) (j : Fin d) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (out : (Fin d → Fin (2^r)) × Bool) :
    nativeCurrentWeight d r j a b c k out =
      signedRecordWeight (spinorCurrentMean a b c k (periodicUnitShift d (2^r)) j) out := by
  unfold nativeCurrentWeight
  rw [physical_velocity_mass_supplied, physical_velocity_mass_supplied]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  exact current_born_mass a b c k hz (periodicUnitShift d (2^r) j) out

/-- Construction for native Current Law in the native born bridge model. -/
def nativeCurrentLaw (d r : ℕ) (j : Fin d) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) : FinDist ((Fin d → Fin (2^r)) × Bool) where
  prob := nativeCurrentWeight d r j a b c k
  nonneg out := by
    unfold nativeCurrentWeight physicalVelocityMass BornProb
    positivity
  sum_one := by
    simp_rw [native_current_weight_eq d r j a b c k hz]
    rw [Fintype.sum_prod_type]
    simp_rw [signed_record_cell_mass]
    simp [nsmul_eq_mul]

/-- Complete original `law_eq_of_prob` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
private theorem law_eq_of_prob {X : Type*} [Fintype X] (p q : FinDist X)
    (h : ∀ x, p.prob x=q.prob x) : p=q := by
  cases p with
  | mk p hp hs =>
    cases q with
    | mk q hq ht =>
      have he : p=q := funext h
      subst q
      rfl

/-- Complete original `native_current_law_eq_macro` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_current_law_eq_macro (d r : ℕ) (j : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    nativeCurrentLaw d r j a b c k hz=currentCircuitLaw a b c k hz (periodicUnitShift d (2^r) j) := by
  apply law_eq_of_prob
  intro out
  exact (native_current_weight_eq d r j a b c k hz out).trans
    (current_born_mass a b c k hz (periodicUnitShift d (2^r) j) out).symm

/-- Complete original `native_current_law_eq_signed` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_current_law_eq_signed (d r : ℕ) (j : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    nativeCurrentLaw d r j a b c k hz =
      signedRecordLaw (spinorCurrentMean a b c k (periodicUnitShift d (2^r)) j)
        (spinor_current_mean_bound a b c k hz (periodicUnitShift d (2^r)) j) := by
  rw [native_current_law_eq_macro]
  exact current_circuit_law_eq a b c k hz (periodicUnitShift d (2^r) j)
    (spinor_current_mean_bound a b c k hz (periodicUnitShift d (2^r)) j)

/-- Construction for native Velocity Record Law in the native born bridge model. -/
def nativeVelocityRecordLaw (d r : ℕ) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (nv Kv : ℕ) :
    FinDist (Fin d → Fin Kv → Fin nv → (Fin d → Fin (2^r)) × Bool) :=
  finiteFamilyLaw (fun j => cohortLaw (cohortLaw (nativeCurrentLaw d r j a b c k hz) nv) Kv)

/-- Complete original `native_velocity_record_law_eq` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_velocity_record_law_eq (d r : ℕ) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (nv Kv : ℕ) :
    nativeVelocityRecordLaw d r a b c k hz nv Kv =
      velocityRecordLaw (spinorCurrentMean a b c k (periodicUnitShift d (2^r)))
        (spinor_current_mean_bound a b c k hz (periodicUnitShift d (2^r))) nv Kv := by
  simp only [nativeVelocityRecordLaw, velocityRecordLaw, native_current_law_eq_signed]

/-- Pauli circuits have exactly dr+1 wires, with no test or AND workspace. -/
def positionEquiv (d r : ℕ) : Reg (d*r) ≃ (Fin d → Fin (2^r)) :=
  (Equiv.arrowCongr (finProdFinEquiv : Fin d × Fin r ≃ Fin (d*r)) (Equiv.refl Bool)).symm.trans
    ((Equiv.curry (Fin d) (Fin r) Bool).trans (Equiv.piCongrRight (fun _ => littleEndianEquiv r)))

/-- Complete original `position_equiv_apply` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem position_equiv_apply (d r : ℕ) (x : Reg (d*r)) (j : Fin d) :
    positionEquiv d r x j=littleAddress r (fun i => x (finProdFinEquiv (j,i))) := rfl

/-- Construction for spin Layout Equiv in the native born bridge model. -/
def spinLayoutEquiv (d r : ℕ) : Reg (d*r+1) ≃ ((Fin d → Fin (2^r)) × Bool) :=
  (regSuccEquiv (d*r)).trans (Equiv.prodCongr (positionEquiv d r) (Equiv.refl Bool))

/-- Complete original `spin_layout_decode` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem spin_layout_decode (d r : ℕ) (x : Reg (d*r+1)) : spinLayoutEquiv d r x=spinDecode d r x := rfl

/-- Construction for spin Encode in the native born bridge model. -/
def spinEncode (d r : ℕ) (s : Fin d → Fin (2^r)) (spin : Bool) : Reg (d*r+1) :=
  (spinLayoutEquiv d r).symm (s,spin)

/-- Complete original `spin_decode_encode` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem spin_decode_encode (d r : ℕ) (s : Fin d → Fin (2^r)) (spin : Bool) :
    spinDecode d r (spinEncode d r s spin)=(s,spin) := (spinLayoutEquiv d r).apply_symm_apply _

/-- Complete original `spin_encode_readout` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
@[simp] theorem spin_encode_readout (d r : ℕ) (s : Fin d → Fin (2^r)) (spin : Bool) :
    spinEncode d r s spin (spinReadoutWire d r)=spin := congrArg Prod.snd (spin_decode_encode d r s spin)

/-- Complete original `spin_layout_update` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem spin_layout_update (d r : ℕ) (x : Reg (d*r+1)) (b : Bool) :
    spinLayoutEquiv d r (Function.update x (spinReadoutWire d r) b)=((spinLayoutEquiv d r x).1,b) := by
  apply Prod.ext
  · change positionEquiv d r (Fin.init (Function.update x (spinReadoutWire d r) b))=
      positionEquiv d r (Fin.init x)
    congr 1
    funext i
    change Function.update x (spinReadoutWire d r) b (Fin.castSucc i)=x (Fin.castSucc i)
    have hne : Fin.castSucc i ≠ spinReadoutWire d r := by
      intro h
      have hv := congrArg Fin.val h
      have hi := i.isLt
      change i.val=d*r at hv
      omega
    exact Function.update_of_ne hne _ _
  · exact Function.update_self _ _ _

/-- Complete original `spin_encode_update` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem spin_encode_update (d r : ℕ) (s : Fin d → Fin (2^r)) (spin b : Bool) :
    Function.update (spinEncode d r s spin) (spinReadoutWire d r) b=spinEncode d r s b := by
  apply (spinLayoutEquiv d r).injective
  rw [spin_layout_update]
  change (((spinLayoutEquiv d r) ((spinLayoutEquiv d r).symm (s,spin))).1,b)=
    (spinLayoutEquiv d r) ((spinLayoutEquiv d r).symm (s,b))
  simp only [Equiv.apply_symm_apply]

/-- Complete original `narrow_spin_wire_ket` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem narrow_spin_wire_ket (d r : ℕ) (U : Matrix Bool Bool ℂ)
    (s : Fin d → Fin (2^r)) (spin : Bool) :
    ApplyGate (wireGate (d*r+1) (spinReadoutWire d r) U) (Ket (spinEncode d r s spin)) =
      ∑ b : Bool, U b spin • Ket (spinEncode d r s b) := by
  rw [applyGate_wireGate_ket]
  simp only [spin_encode_readout, spin_encode_update, Fintype.sum_bool]
  exact add_comm _ _

/-- Construction for encode Spin Amplitude in the native born bridge model. -/
def encodeSpinAmplitude (d r : ℕ) (f : Bool → (Fin d → Fin (2^r)) → ℂ) : QState (Reg (d*r+1)) :=
  ∑ z : (Fin d → Fin (2^r)) × Bool, f z.2 z.1 • Ket (spinEncode d r z.1 z.2)

/-- Construction for spin Rotate in the native born bridge model. -/
def spinRotate {S : Type*} (U : Matrix Bool Bool ℂ) (f : Bool → S → ℂ) (b : Bool) (x : S) : ℂ :=
  ApplyGate U (fun q => f q x) b

/-- Complete original `spin_rotate_h` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem spin_rotate_h {S : Type*} (f : Bool → S → ℂ) : spinRotate Hadamard f=readoutH f := by
  funext b x
  exact (readout_h_apply_gate f b x).symm

/-- Complete original `spin_rotate_sdg` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem spin_rotate_sdg {S : Type*} (f : Bool → S → ℂ) : spinRotate readoutSdgMatrix f=readoutSdg f := by
  funext b x
  exact (readout_sdg_apply_gate f b x).symm

/-- Complete original `narrow_spin_matrix_transport` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem narrow_spin_matrix_transport (d r : ℕ) (U : Matrix Bool Bool ℂ)
    (f : Bool → (Fin d → Fin (2^r)) → ℂ) :
    ApplyGate (wireGate (d*r+1) (spinReadoutWire d r) U) (encodeSpinAmplitude d r f) =
      encodeSpinAmplitude d r (spinRotate U f) := by
  unfold encodeSpinAmplitude
  rw [apply_gate_sum_smul]
  simp_rw [narrow_spin_wire_ket, Finset.smul_sum, smul_smul]
  simp only [spinRotate, ApplyGate, Matrix.mulVec, dotProduct, Finset.sum_smul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- Construction for spin Program in the native born bridge model. -/
def spinProgram (d r : ℕ) (p : Fin 3) : Circuit (Reg (d*r+1)) := measurementProgram (spinWord d r p)

/-- Complete original `spin_program_unitary` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem spin_program_unitary (d r : ℕ) (p : Fin 3) : IsUnitaryCircuit (spinProgram d r p) :=
  (local_reflection_gate_support_unitarity_counts (d*r+1)
    ((spinWord d r p).map measurementMatrix) (spin_word_legal d r p)).1

/-- Complete original `spin_program_counts` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem spin_program_counts (d r : ℕ) (p : Fin 3) :
    QueryCount (spinProgram d r p)=0 ∧ GateCount (spinProgram d r p)=(spinWord d r p).length :=
  measurement_program_counts _

/-- Complete original `spin_program_supplied_state` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem spin_program_supplied_state (d r : ℕ) (p : Fin 3)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) :
    Run (1 : Matrix (Reg (d*r+1)) (Reg (d*r+1)) ℂ)
      (spinProgram d r p) (encodeSpinAmplitude d r (suppliedSpinState a b c k)) =
      encodeSpinAmplitude d r (spinGateState a b c k p) := by
  fin_cases p <;>
    simp [spinProgram, spinWord, measurementProgram, measurementMatrix, nativeMatrix,
      reflectionCompile, reflectionGateMatrix, run_gate, run_nil, narrow_spin_matrix_transport,
      spin_rotate_h, spin_rotate_sdg, spinGateState]

/-- Complete original `encode_spin_amplitude_apply` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem encode_spin_amplitude_apply (d r : ℕ) (f : Bool → (Fin d → Fin (2^r)) → ℂ)
    (out : (Fin d → Fin (2^r)) × Bool) :
    encodeSpinAmplitude d r f ((spinLayoutEquiv d r).symm out)=f out.2 out.1 := by
  simp only [encodeSpinAmplitude, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Qatlib.Foundations.PureStateMath.ket_apply]
  rw [Finset.sum_eq_single out]
  · simp [spinEncode]
  · intro z _ hz
    have hne : (spinLayoutEquiv d r).symm out ≠ spinEncode d r z.1 z.2 := by
      intro h
      change (spinLayoutEquiv d r).symm out=(spinLayoutEquiv d r).symm z at h
      exact hz ((spinLayoutEquiv d r).symm.injective h).symm
    simp only [ite_eq_right hne, mul_zero]
  · simp

/-- Construction for native Spin Weight in the native born bridge model. -/
def nativeSpinWeight (d r : ℕ) (p : Fin 3) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (out : (Fin d → Fin (2^r)) × Bool) : ℝ :=
  BornProb (Run (1 : Matrix (Reg (d*r+1)) (Reg (d*r+1)) ℂ)
    (spinProgram d r p) (encodeSpinAmplitude d r (suppliedSpinState a b c k)))
    ((spinLayoutEquiv d r).symm out)

/-- Complete original `native_spin_weight_eq_macro` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_spin_weight_eq_macro (d r : ℕ) (p : Fin 3) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (out : (Fin d → Fin (2^r)) × Bool) :
    nativeSpinWeight d r p a b c k out=spinBornMass a b c k p out := by
  unfold nativeSpinWeight
  rw [spin_program_supplied_state]
  simp only [BornProb, encode_spin_amplitude_apply, spinBornMass]

/-- Complete original `native_spin_weight_eq` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_spin_weight_eq (d r : ℕ) (p : Fin 3) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (out : (Fin d → Fin (2^r)) × Bool) :
    nativeSpinWeight d r p a b c k out=signedRecordWeight (pauliField a b c k p) out := by
  rw [native_spin_weight_eq_macro, spin_born_mass a b c k hz]

/-- Complete original `native_spin_input_normalized` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_spin_input_normalized (d r : ℕ) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    Normalized (encodeSpinAmplitude d r (suppliedSpinState a b c k)) := by
  change (∑ x, BornProb _ x)=1
  rw [← (spinLayoutEquiv d r).symm.sum_comp (BornProb (encodeSpinAmplitude d r (suppliedSpinState a b c k)))]
  simp only [BornProb, encode_spin_amplitude_apply]
  exact supplied_spin_state_normalized a b c k hz

/-- Complete original `native_spin_output_normalized` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_spin_output_normalized (d r : ℕ) (p : Fin 3) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    Normalized (Run (1 : Matrix (Reg (d*r+1)) (Reg (d*r+1)) ℂ)
      (spinProgram d r p) (encodeSpinAmplitude d r (suppliedSpinState a b c k))) := by
  change (∑ x, BornProb _ x)=1
  rw [← (spinLayoutEquiv d r).symm.sum_comp (BornProb
    (Run (1 : Matrix (Reg (d*r+1)) (Reg (d*r+1)) ℂ)
      (spinProgram d r p) (encodeSpinAmplitude d r (suppliedSpinState a b c k))))]
  change (∑ out, nativeSpinWeight d r p a b c k out)=1
  simp_rw [native_spin_weight_eq d r p a b c k hz]
  rw [Fintype.sum_prod_type]
  simp_rw [signed_record_cell_mass]
  simp [nsmul_eq_mul]

/-- Construction for native Spin Law in the native born bridge model. -/
def nativeSpinLaw (d r : ℕ) (p : Fin 3) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) : FinDist ((Fin d → Fin (2^r)) × Bool) where
  prob := nativeSpinWeight d r p a b c k
  nonneg out := sq_nonneg _
  sum_one := by
    simp_rw [native_spin_weight_eq d r p a b c k hz]
    rw [Fintype.sum_prod_type]
    simp_rw [signed_record_cell_mass]
    simp [nsmul_eq_mul]

/-- Complete original `native_spin_law_eq_signed` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_spin_law_eq_signed (d r : ℕ) (p : Fin 3) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    nativeSpinLaw d r p a b c k hz=signedRecordLaw (pauliField a b c k p)
      (unit_spin_component_bound (pauliField a b c k) (pauli_field_unit a b c k hz) p) := by
  apply law_eq_of_prob
  exact native_spin_weight_eq d r p a b c k hz

/-- Construction for native Total Record Law in the native born bridge model. -/
def nativeTotalRecordLaw (d r : ℕ) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (nv Kv ns Ks : ℕ) :
    FinDist (TotalRecordData (Fin d → Fin (2^r)) d nv Kv ns Ks) :=
  independentPairLaw
    (finiteFamilyLaw (fun j => cohortLaw (cohortLaw (nativeCurrentLaw d r j a b c k hz) nv) Kv))
    (finiteFamilyLaw (fun i : Fin 3 × Fin d => cohortLaw (cohortLaw (nativeSpinLaw d r i.1 a b c k hz) ns) Ks))

/-- Complete original `native_total_record_law_eq` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_total_record_law_eq (d r : ℕ) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (nv Kv ns Ks : ℕ) :
    nativeTotalRecordLaw d r a b c k hz nv Kv ns Ks =
      totalRecordLaw (spinorCurrentMean a b c k (periodicUnitShift d (2^r)))
        (spinor_current_mean_bound a b c k hz (periodicUnitShift d (2^r)))
        (pauliField a b c k)
        (fun p x => unit_spin_component_bound (pauliField a b c k) (pauli_field_unit a b c k hz) p x)
        nv Kv ns Ks := by
  simp only [nativeTotalRecordLaw, totalRecordLaw, native_current_law_eq_signed, native_spin_law_eq_signed]

set_option synthInstance.maxSize 1024 in
/-- Complete original `native_zero_spin_estimator_accuracy` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_zero_spin_estimator_accuracy {d r : ℕ} (κ lam U η δ eb : ℚ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) κ lam U η=some coef)
    (hd : 0 < d) (hκ : 0 < κ) (hU : 0 ≤ U) (hη : 0 < η) (hδ : 0 < δ)
    (heb0 : 0 ≤ eb) (heb : eb ≤ coef.maxTargetError) (hγ : coef.gamma=0)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ) (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x| ≤ (U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x| ≤ (eb : ℝ)) :
    let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
    let e := periodicUnitShift d (2^r)
    finiteBadMass (nativeVelocityRecordLaw d r a b c k hz p.velocityRecords p.velocityBlocks)
      (fun z => (velocityOnlyOutputQ (2^(d*r)) û coef.alpha coef.beta (U+eb) z : ℝ))
      (spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) (κ : ℝ) (lam : ℝ)) (η : ℝ) ≤ (δ : ℝ)/2 := by
  simpa only [native_velocity_record_law_eq] using
    executed_plan_accuracy_zero_spin κ lam U η δ eb coef hc hd hκ hU hη hδ heb0 heb hγ a b c k hz u û hu htarget

set_option synthInstance.maxSize 1024 in
/-- Complete original `native_estimator_accuracy` guarantee for `NativeBornBridge`; all source hypotheses and output obligations are retained. -/
theorem native_estimator_accuracy {d r : ℕ} (κ lam U η δ eb : ℚ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) κ lam U η=some coef)
    (hd : 0 < d) (hκ : 0 < κ) (hU : 0 ≤ U) (hη : 0 < η) (hδ : 0 < δ)
    (heb0 : 0 ≤ eb) (heb : eb ≤ coef.maxTargetError) (hγ : 0 < coef.gamma)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ) (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x| ≤ (U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x| ≤ (eb : ℝ)) :
    let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
    let e := periodicUnitShift d (2^r)
    finiteBadMass (nativeTotalRecordLaw d r a b c k hz p.velocityRecords p.velocityBlocks p.spinRecords p.spinBlocks)
      (fun z => (totalMedianOutputQ (2^(d*r)) û (fun j => periodicDoubleShift d (2^r) j) coef.alpha coef.beta (U+eb) coef.gamma z : ℝ))
      (spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) (κ : ℝ) (lam : ℝ)) (η : ℝ) ≤ (δ : ℝ) := by
  simpa only [native_total_record_law_eq] using
    executed_plan_accuracy κ lam U η δ eb coef hc hd hκ hU hη hδ heb0 heb hγ a b c k hz u û hu htarget

end
end Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge


#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.measurement_program_counts
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.readout_sdg_unitary
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.velocity_word_legal
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_word_legal
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.decoded_neighbor_eq_original
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.encode_label_injective
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.encode_clean_update_test
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.encode_clean_update_spin
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.encode_amplitude_apply_label
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.test_wire_ket
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_wire_ket
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.test_action_h
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.test_action_sdg
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.test_matrix_transport
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_matrix_transport
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.encode_controlled_site
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.encoded_permuted_sum
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.encoded_controlled_sum
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.forward_shift_transport
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.reverse_shift_transport
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.velocity_program_expand
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.velocity_program_unitary
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.velocity_program_counts
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.velocity_program_evolution_positive
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.velocity_program_evolution_negative
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.velocity_program_supplied_state
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.decode_basis_at
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.encode_amplitude_at_clean
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.encode_amplitude_at_dirty
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.physical_velocity_mass_encoded
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.physical_velocity_mass_total
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.physical_velocity_mass_supplied
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_velocity_normalized
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_supplied_input_normalized
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_current_weight_eq
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_current_law_eq_macro
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_current_law_eq_signed
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_velocity_record_law_eq
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.position_equiv_apply
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_layout_decode
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_decode_encode
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_encode_readout
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_layout_update
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_encode_update
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.narrow_spin_wire_ket
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_rotate_h
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_rotate_sdg
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.narrow_spin_matrix_transport
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_program_unitary
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_program_counts
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.spin_program_supplied_state
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.encode_spin_amplitude_apply
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_spin_weight_eq_macro
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_spin_weight_eq
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_spin_input_normalized
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_spin_output_normalized
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_spin_law_eq_signed
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_total_record_law_eq
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_zero_spin_estimator_accuracy
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.native_estimator_accuracy
