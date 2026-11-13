/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveAlgorithmDihe
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Representation Fourier transport and the physical dihedral sieve

This module constructs the dihedral Fourier transform `representationFourier` from a cyclic
Fourier transform and frequency-dependent qubit basis changes. The equivalence
`FourierEncoding.decodeEquiv` organizes its coordinates into one-dimensional and two-dimensional
representation blocks, while `Irreps.canonicalFamily`, `TypedFourier.typedFourier_kernel`, and
`FixedSubspace.canonical_label_law` identify the matrix coefficients, dimension count, and
hidden-reflection label probabilities.

The charged execution `PhysicalTrace.runT` connects actual record preparation, pair extraction,
and parity readout to the sieve of [Kuperberg2005]. Its marginal agrees with the actual sieve,
and `actualSieveConsumer` combines the success bound with query, gate, measurement, and
live-record bounds; `frontier1` collects the Fourier, record, extraction, and consumer
statements.

## Main statements

* `finiteFourierTransport` packages unitarity, the dimension count, the typed Fourier kernel,
  and its normalization.
* `representationRecordTransport` connects representation-basis records to physical preparation
  and the canonical label law.
* `explicitExtractionLaw` gives the two equally weighted sum-frequency and difference-frequency
  extraction branches.
* `actualSieveConsumer` establishes the actual parity sieve's probability and resource
  guarantees.
- `frontier1` combines the four transport and execution guarantees.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.SieveAlgorithm
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HspRecovery.OpenSieve

open Qatlib   Matrix
open scoped Classical BigOperators

variable {N : ℕ} [NeZero N]

/-- The qubit basis change at frequency `k`: Hadamard for a self-negative frequency, Pauli X
when the negative frequency has smaller residue, and identity otherwise. -/
def representationBasisGate (k : ZMod N) : Matrix Bool Bool ℂ :=
  if k = -k then Hadamard else if (-k).val < k.val then PauliX else 1

omit [NeZero N] in

/-- Every frequency-dependent representation basis change is unitary. -/
theorem representationBasisGate_unitary (k : ZMod N) :
    representationBasisGate k ∈ Matrix.unitaryGroup Bool ℂ := by
  unfold representationBasisGate
  split_ifs
  · exact hadamard_unitary
  · exact pauliX_unitary
  · exact (Matrix.unitaryGroup Bool ℂ).one_mem

/-- The dihedral representation Fourier transform obtained by applying the cyclic Fourier
transform to the frequency register and then the controlled representation basis change. -/
def representationFourier : Matrix (ZMod N × Bool) (ZMod N × Bool) ℂ :=
  Select representationBasisGate * TensorGate (zmodQFTGate (N := N)) (1 : Matrix Bool Bool ℂ)

/-- The representation Fourier transform is unitary for nonzero modulus `N`. -/
theorem representationFourier_unitary :
    representationFourier (N := N) ∈ Matrix.unitaryGroup (ZMod N × Bool) ℂ :=
  (Matrix.unitaryGroup _ ℂ).mul_mem (select_unitary _ representationBasisGate_unitary)
    (tensorGate_unitary (zmodQFTGate_unitary (NeZero.pos N)) (Matrix.unitaryGroup Bool ℂ).one_mem)

/-- Each entry of the representation Fourier transform is the normalized cyclic character
`ZMod.stdAddChar (k*a)` multiplied by the corresponding qubit basis-change entry. -/
theorem representationFourier_kernel (k a : ZMod N) (b t : Bool) :
    representationFourier (k,b) (a,t) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (k*a) * representationBasisGate k b t := by
  unfold representationFourier
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Select, Matrix.of_apply,
    TensorGate, Matrix.kroneckerMap, Matrix.one_apply]
  rw [Finset.sum_eq_single k]
  · simp only [if_true, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ t), zmodQFTGate_apply]
    ring
  · intro j _ hj
    have hkj : k ≠ j := Ne.symm hj
    simp only [if_neg hkj, zero_mul, Finset.sum_const_zero]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

section ActualRecord

variable {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]

/-- The representation basis change on a dihedral record, controlled by its frequency and
tensored with the identity on the oracle-output register. -/
def representationRecordGate : Matrix (DihedralReg N × S) (DihedralReg N × S) ℂ :=
  TensorGate (Select (representationBasisGate (N := N))) (1 : Matrix S S ℂ)

omit [AddCommGroup S] in

/-- The representation basis change on the joint record and oracle-output registers is unitary. -/
theorem representationRecordGate_unitary :
    representationRecordGate (N := N) (S := S) ∈ Matrix.unitaryGroup (DihedralReg N × S) ℂ :=
  tensorGate_unitary (select_unitary _ representationBasisGate_unitary) (Matrix.unitaryGroup S ℂ).one_mem

/-- The joint dihedral record state after applying the frequency-controlled representation basis
change. -/
def representationJoint (f : DihedralReg N → S) : QState (DihedralReg N × S) :=
  ApplyGate representationRecordGate (dihedralRecordJoint N f)

/-- The joint representation-basis record state has total squared norm one. -/
theorem representationJoint_normalized (f : DihedralReg N → S) : Normalized (representationJoint f) :=
  normalized_applyGate representationRecordGate_unitary (normalized_dihedralRecordJoint N f)

/-- Applying the adjoint representation record gate recovers the original joint dihedral record
state. -/
theorem representationJoint_readback (f : DihedralReg N → S) :
    (representationRecordGate (N := N) (S := S))ᴴ *ᵥ representationJoint f = dihedralRecordJoint N f := by
  unfold representationJoint ApplyGate
  rw [Matrix.mulVec_mulVec]
  have hu := Matrix.mem_unitaryGroup_iff'.mp (representationRecordGate_unitary (N := N) (S := S))
  change representationRecordGateᴴ * representationRecordGate = 1 at hu
  rw [hu, Matrix.one_mulVec]

/-- At fixed frequency and oracle output, a representation-basis amplitude is the qubit
basis-change matrix applied to the original two record amplitudes. -/
theorem representationJoint_apply (f : DihedralReg N → S) (k : ZMod N) (b : Bool) (z : S) :
    representationJoint f ((k,b),z) =
      ∑ t : Bool, representationBasisGate k b t * dihedralRecordJoint N f ((k,t),z) := by
  simp only [representationJoint, ApplyGate, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, representationRecordGate, TensorGate, Matrix.kroneckerMap,
    Matrix.of_apply, Select, Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  simp_rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ z)]
  rw [Finset.sum_eq_single k]
  · simp only [if_true]
  · intro j _ hj
    have hkj : k ≠ j := Ne.symm hj
    simp only [if_neg hkj, Finset.sum_const_zero]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

/-- For an oracle hiding reflection `s`, each frequency row factors into an oracle-output
amplitude and the basis-changed dihedral phase qubit. The oracle-output amplitudes have
total squared norm `1/N`. -/
theorem representationJoint_factor (f : DihedralReg N → S) (s k : ZMod N)
    (hf : DihedralReflectionHides N f s) :
    ∃ gamma : S → ℂ, (∑ z, ‖gamma z‖^2) = 1/(N : ℝ) ∧
      ∀ b z, representationJoint f ((k,b),z) =
        gamma z * (representationBasisGate k *ᵥ dihedralQubitState N s k) b := by
  obtain ⟨gamma, hnorm, hfactor⟩ :=
      Qatlib.Concepts.HspRecovery.RecordExtract.clause27_recordFactor N S f s hf k
  refine ⟨gamma, hnorm, ?_⟩
  intro b z
  rw [representationJoint_apply]
  simp_rw [hfactor]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- For an oracle hiding reflection `s`, every frequency row of the representation-basis joint
state has Born mass `1/N`. -/
theorem representation_row_mass (f : DihedralReg N → S) (s k : ZMod N)
    (hf : DihedralReflectionHides N f s) :
    (∑ b : Bool, ∑ z : S, ‖representationJoint f ((k,b),z)‖^2) = 1/(N : ℝ) := by
  obtain ⟨gamma, hnorm, hfactor⟩ := representationJoint_factor f s k hf
  have hv : Normalized (representationBasisGate k *ᵥ dihedralQubitState N s k) :=
    normalized_applyGate (representationBasisGate_unitary k) (normalized_dihedralQubitState N s k)
  simp_rw [hfactor, norm_mul, mul_pow, ← Finset.sum_mul]
  rw [← Finset.mul_sum, hnorm]
  change (1/(N : ℝ)) * (∑ b : Bool,
      ‖(representationBasisGate k *ᵥ dihedralQubitState N s k) b‖^2) = _
  rw [show (∑ b : Bool, ‖(representationBasisGate k *ᵥ dihedralQubitState N s k) b‖^2) = 1 from hv,
    mul_one]

end ActualRecord

namespace FourierEncoding

/-- Frequencies in `ZMod N` equal to their own negatives, indexing the one-dimensional
representation blocks. -/
abbrev SelfFreq (N : ℕ) := {k : ZMod N // k = -k}
/-- Canonical representatives of distinct frequency pairs `{k, -k}`, chosen by requiring the
residue of `k` to be smaller than that of `-k`. -/
abbrev PairFreq (N : ℕ) := {k : ZMod N // k.val < (-k).val}
/-- Representation labels consisting of a self-negative frequency with a Boolean character sign,
or a canonical pair frequency. -/
abbrev Label (N : ℕ) := Sum (SelfFreq N × Bool) (PairFreq N)

/-- The block dimension of a representation label, equal to one for self-frequency labels and
two for pair-frequency labels. -/
abbrev dim {N : ℕ} : Label N → ℕ
  | .inl _ => 1
  | .inr _ => 2

/-- Fourier coordinates expressed as a representation label together with row and column indices
in its block. -/
abbrev Typed (N : ℕ) := Σ L : Label N, Fin (dim L) × Fin (dim L)
/-- Raw Fourier coordinates consisting of a modular frequency and a Boolean qubit index. -/
abbrev Raw (N : ℕ) := ZMod N × Bool

variable {N : ℕ} [NeZero N]

omit [NeZero N] in

/-- A canonical pair frequency is distinct from its negative. -/
theorem pair_not_self (k : PairFreq N) : k.1 ≠ -k.1 := by
  intro he
  have hv : k.1.val = (-k.1).val := congrArg ZMod.val he
  have hk := k.2
  omega

/-- If a frequency is distinct from its negative and its residue is not smaller, then its
negative has strictly smaller residue. -/
theorem negative_of_not_self_not_positive (k : ZMod N)
    (hs : k ≠ -k) (hp : ¬k.val < (-k).val) : (-k).val < k.val := by
  have hne : k.val ≠ (-k).val := by
    intro he
    exact hs ((ZMod.val_injective N) he)
  omega

/-- Converts a raw frequency-qubit coordinate into a representation label and block indices. A
non-self frequency selects row zero or one according to its position in the canonical
negative pair. -/
def decode (x : Raw N) : Typed N :=
  let k := x.1
  let b := x.2
  if hs : k = -k then
    ⟨.inl (⟨k, hs⟩, b), ((0 : Fin 1), (0 : Fin 1))⟩
  else if hp : k.val < (-k).val then
    ⟨.inr ⟨k, hp⟩, ((0 : Fin 2), boolEquivFin2 b)⟩
  else
    ⟨.inr ⟨-k, by
      simpa only [neg_neg] using! negative_of_not_self_not_positive k hs hp⟩,
      ((1 : Fin 2), boolEquivFin2 b)⟩

/-- Converts a typed representation coordinate back to a raw frequency-qubit coordinate, using
the pair-block row to choose the frequency sign. -/
def encode : Typed N → Raw N
  | ⟨.inl (k, b), _⟩ => (k.1, b)
  | ⟨.inr k, (i, j)⟩ =>
      (if (i : Fin 2) = 0 then k.1 else -k.1, boolEquivFin2.symm j)

/-- Decoding a self-negative frequency gives its one-dimensional label, with the Boolean
coordinate selecting the character sign. -/
theorem decode_self (k : SelfFreq N) (b : Bool) :
    decode (k.1, b) =
      ⟨.inl (k, b), ((0 : Fin 1), (0 : Fin 1))⟩ := by
  dsimp only [decode]
  rw [dif_pos k.2]

/-- Decoding a canonical pair representative gives row zero of its two-dimensional block and
preserves the Boolean column index. -/
theorem decode_positive (k : PairFreq N) (b : Bool) :
    decode (k.1, b) =
      ⟨.inr k, ((0 : Fin 2), boolEquivFin2 b)⟩ := by
  dsimp only [decode]
  rw [dif_neg (pair_not_self k), dif_pos k.2]

/-- Decoding the negative of a canonical pair representative gives row one of the same block and
preserves the Boolean column index. -/
theorem decode_negative (k : PairFreq N) (b : Bool) :
    decode (-k.1, b) =
      ⟨.inr k, ((1 : Fin 2), boolEquivFin2 b)⟩ := by
  have hs : -k.1 ≠ -(-k.1) := by
    intro he
    apply pair_not_self k
    exact (by simpa only [neg_neg] using! he : -k.1 = k.1).symm
  have hp : ¬(-k.1).val < (-(-k.1)).val := by
    rw [neg_neg]
    exact not_lt_of_ge k.2.le
  dsimp only [decode]
  rw [dif_neg hs, dif_neg hp]
  apply Sigma.ext
  · apply congrArg Sum.inr
    apply Subtype.ext
    exact neg_neg k.1
  · rfl

/-- Encoding a decoded raw Fourier coordinate returns the original coordinate. -/
theorem encode_decode (x : Raw N) : encode (decode x) = x := by
  rcases x with ⟨k, b⟩
  by_cases hs : k = -k
  · rw [decode_self (⟨k, hs⟩ : SelfFreq N) b]
    rfl
  · by_cases hp : k.val < (-k).val
    · rw [decode_positive (⟨k, hp⟩ : PairFreq N) b]
      change (k, boolEquivFin2.symm (boolEquivFin2 b)) = (k, b)
      rw [boolEquivFin2.symm_apply_apply]
    · let c : PairFreq N := ⟨-k, by
        simpa only [neg_neg] using! negative_of_not_self_not_positive k hs hp⟩
      have hd : decode (k, b) =
          ⟨.inr c, ((1 : Fin 2), boolEquivFin2 b)⟩ := by
        have hc := decode_negative c b
        dsimp only [c] at hc ⊢
        simpa only [neg_neg] using! hc
      rw [hd]
      change (-(-k), boolEquivFin2.symm (boolEquivFin2 b)) = (k, b)
      rw [neg_neg, boolEquivFin2.symm_apply_apply]

/-- Decoding an encoded typed Fourier coordinate returns the original label and block indices. -/
theorem decode_encode (x : Typed N) : decode (encode x) = x := by
  rcases x with ⟨L, i, j⟩
  cases L with
  | inl kb =>
      rcases kb with ⟨k, b⟩
      change Fin 1 at i
      change Fin 1 at j
      have hi : i = 0 := Fin.eq_zero i
      have hj : j = 0 := Fin.eq_zero j
      subst i
      subst j
      exact decode_self k b
  | inr k =>
      change Fin 2 at i
      change Fin 2 at j
      fin_cases i
      · change decode (k.1, boolEquivFin2.symm j) =
          ⟨.inr k, ((0 : Fin 2), j)⟩
        rw [decode_positive, boolEquivFin2.apply_symm_apply]
      · change decode (-k.1, boolEquivFin2.symm j) =
          ⟨.inr k, ((1 : Fin 2), j)⟩
        rw [decode_negative, boolEquivFin2.apply_symm_apply]

/-- The equivalence between raw frequency-qubit coordinates and typed representation-block
coordinates. -/
def decodeEquiv : Raw N ≃ Typed N where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

/-- The number of typed Fourier coordinates is the sum of the squared representation-block
dimensions. -/
theorem typed_card : Fintype.card (Typed N) =
    ∑ L : Label N, (dim L) ^ 2 := by
  simp only [Typed, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, pow_two]

/-- There are `2*N` raw frequency-qubit coordinates. -/
theorem raw_card : Fintype.card (Raw N) = 2 * N := by
  simp only [Raw, Fintype.card_prod, ZMod.card, Fintype.card_bool, Nat.mul_comm]

/-- The squared dimensions of the canonical representation labels sum to the dihedral group
order `2*N`. -/
theorem dimensionCount : (∑ L : Label N, (dim L) ^ 2) = 2 * N := by
  have hc : Fintype.card (Raw N) = Fintype.card (Typed N) :=
    Fintype.card_congr (decodeEquiv (N := N))
  exact (typed_card (N := N)).symm.trans (hc.symm.trans (raw_card (N := N)))

/-- Every frequency modulo one equals its negative. -/
theorem self_one (k : ZMod 1) : k = -k := Subsingleton.elim _ _

/-- Every frequency modulo two equals its negative. -/
theorem self_two (k : ZMod 2) : k = -k := (ZMod.neg_eq_self_mod_two k).symm

/-- There are no canonical distinct-frequency pairs modulo one. -/
theorem no_pair_one (k : PairFreq 1) : False := pair_not_self k (self_one k.1)

/-- There are no canonical distinct-frequency pairs modulo two. -/
theorem no_pair_two (k : PairFreq 2) : False := pair_not_self k (self_two k.1)

end FourierEncoding

namespace PhysicalTrace

/-- A physical sieve record consisting of a frequency modulo `2^n` and a normalized qubit state. -/
abbrev Record (n : ℕ) := ZMod (2 ^ n) × NormQ

/-- Resource counters for fresh record preparations, pair extractions, and final parity
readouts. -/
structure Charge where
  fresh : ℕ
  pairs : ℕ
  reads : ℕ
  deriving DecidableEq

/-- The resource charge with all three counters equal to zero. -/
def zeroCharge : Charge := ⟨0, 0, 0⟩

/-- Adds the fresh-preparation, pair-extraction, and readout charges of two sequential
computations componentwise. -/
def serial (c d : Charge) : Charge :=
  ⟨c.fresh + d.fresh, c.pairs + d.pairs, c.reads + d.reads⟩

/-- Increments the fresh-record preparation counter by one. -/
def chargeFresh (c : Charge) : Charge :=
  ⟨c.fresh + 1, c.pairs, c.reads⟩

/-- Increments the pair-extraction counter by one. -/
def chargePair (c : Charge) : Charge :=
  ⟨c.fresh, c.pairs + 1, c.reads⟩

/-- The oracle-query charge, equal to the number of fresh record preparations. -/
def queries (c : Charge) : ℕ := c.fresh

/-- The total number of charged preparation, pair-extraction, and readout operations. -/
def macros (c : Charge) : ℕ := c.fresh + c.pairs + c.reads

/-- The measurement charge obtained by summing the fresh-preparation, pair-extraction, and
readout counters. -/
def measurements (c : Charge) : ℕ := c.fresh + c.pairs + c.reads

/-- Pointwise equal probability kernels give equal distributions after binding against the same
input distribution. -/
private theorem bind_kernel_congr {α β : Type*} (p : PMF α)
    (f g : α → PMF β) (h : ∀ a, f a = g a) : p.bind f = p.bind g :=
  congrArg (fun k : α → PMF β => p.bind k) (funext h)

/-- Forgetting charges after separately mapping values and charges is the same as mapping the
values of the original marginal. -/
private theorem map_fst_map {α β : Type*} (p : PMF (α × Charge))
    (f : α → β) (c : Charge → Charge) :
    (p.map (fun st => (f st.1, c st.2))).map Prod.fst =
      (p.map Prod.fst).map f := by
  calc
    (p.map (fun st => (f st.1, c st.2))).map Prod.fst =
        p.map (f ∘ Prod.fst) :=
      PMF.map_comp (p := p) (f := fun st => (f st.1, c st.2))
        (g := Prod.fst)
    _ = (p.map Prod.fst).map f :=
      (PMF.map_comp (p := p) (f := Prod.fst) (g := f)).symm

/-- Sequentially composes charged probability distributions and adds the resource counters of
the two stages. -/
def writerBind {α β : Type*} (p : PMF (α × Charge))
    (k : α → PMF (β × Charge)) : PMF (β × Charge) :=
  p.bind fun st => (k st.1).map fun out => (out.1, serial st.2 out.2)

/-- Forgetting charges in a sequential charged computation gives the ordinary bind of the value
marginals. -/
theorem writerBind_map {α β : Type*} (p : PMF (α × Charge))
    (k : α → PMF (β × Charge)) :
    (writerBind p k).map Prod.fst =
      (p.map Prod.fst).bind (fun a => (k a).map Prod.fst) := by
  unfold writerBind
  rw [PMF.map_bind, PMF.bind_map]
  apply bind_kernel_congr
  intro st
  exact PMF.map_comp (p := k st.1)
    (f := fun out => (out.1, serial st.2 out.2)) (g := Prod.fst)

/-- Samples the requested number of actual dihedral records, retaining their frequencies and
normalized qubits and charging one fresh preparation per sample. -/
def freshT (n : ℕ) {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) : ℕ → PMF (List (Record n) × Charge)
  | 0 => pure ([], zeroCharge)
  | r + 1 =>
    (dihedralActualRecord (2 ^ n) f).bind fun q =>
      (freshT n f r).map fun st =>
        ((q.1, q.2.2) :: st.1, chargeFresh st.2)

/-- The value marginal of charged fresh-record sampling is the actual fresh-record distribution. -/
theorem freshT_map (n : ℕ) {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) (r : ℕ) :
    (freshT n f r).map Prod.fst = actualFreshRecords (2 ^ n) f r := by
  induction r with
  | zero =>
      change (PMF.pure (([] : List (Record n)), zeroCharge)).map Prod.fst = PMF.pure []
      exact PMF.pure_map (f := Prod.fst) (a := (([] : List (Record n)), zeroCharge))
  | succ r ih =>
      rw [freshT, actualFreshRecords, PMF.map_bind]
      apply bind_kernel_congr
      intro q
      rw [map_fst_map, ih]

/-- Processes a list of record pairs by physical extraction, retaining successful
difference-frequency records and charging one extraction per input pair. -/
def layerAuxT (n : ℕ) :
    List (Record n × Record n) → PMF (List (Record n) × Charge)
  | [] => pure ([], zeroCharge)
  | ((k, χ), (ℓ, χ')) :: ps =>
    (dihedralExtraction χ.val χ'.val χ.property χ'.property).bind fun q =>
      (layerAuxT n ps).map fun st =>
        ((if q.1 then (k - ℓ, q.2) :: st.1 else st.1), chargePair st.2)

/-- Forgetting the extraction charges in the pair-processing routine gives the actual auxiliary
sieve layer distribution. -/
theorem layerAuxT_map (n : ℕ) (ps : List (Record n × Record n)) :
    (layerAuxT n ps).map Prod.fst = actualLayerAux n ps := by
  induction ps with
  | nil =>
      change (PMF.pure (([] : List (Record n)), zeroCharge)).map Prod.fst = PMF.pure []
      exact PMF.pure_map (f := Prod.fst) (a := (([] : List (Record n)), zeroCharge))
  | cons p ps ih =>
      rcases p with ⟨⟨k, χ⟩, ⟨ℓ, χ'⟩⟩
      rw [layerAuxT, actualLayerAux, PMF.map_bind]
      apply bind_kernel_congr
      intro q
      rw [map_fst_map (p := layerAuxT n ps)
        (f := fun tail : List (Record n) =>
          if q.1 then (k - ℓ, q.2) :: tail else tail) (c := chargePair), ih]

/-- A charged sieve layer that pairs records using the chosen frequency window and offset, then
performs physical pair extraction. -/
def layerT (n w t : ℕ) (L : List (Record n)) :
    PMF (List (Record n) × Charge) :=
  layerAuxT n (sievePairWith n Prod.fst w t L)

/-- The value marginal of a charged sieve layer is the actual sieve layer distribution. -/
theorem layerT_map (n w t : ℕ) (L : List (Record n)) :
    (layerT n w t L).map Prod.fst = actualLayer n w t L :=
  layerAuxT_map n (sievePairWith n Prod.fst w t L)

/-- Iterates the charged sieve layers with the scheduled window widths and offsets, accumulating
their resource counters. -/
def recT (n m : ℕ) {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) :
    ℕ → List (Record n) → PMF (List (Record n) × Charge)
  | 0, L => pure (L, zeroCharge)
  | j + 1, L => writerBind (recT n m f j L)
      (fun L' => layerT n (sieveWindowWidth n m j) (m * j) L')

/-- Forgetting charges in the iterated sieve gives the actual recursive sieve distribution. -/
theorem recT_map (n m : ℕ) {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) (j : ℕ) (L : List (Record n)) :
    (recT n m f j L).map Prod.fst = actualSieveRec n m f j L := by
  induction j with
  | zero =>
      change (PMF.pure (L, zeroCharge)).map Prod.fst = PMF.pure L
      exact PMF.pure_map (f := Prod.fst) (a := (L, zeroCharge))
  | succ j ih =>
      rw [recT, writerBind_map, ih, actualSieveRec]
      apply bind_kernel_congr
      intro L'
      exact layerT_map n (sieveWindowWidth n m j) (m * j) L'

/-- Reads the parity qubit of the first record with frequency `2^(n-1)`, charging one readout
when such a record exists and returning `none` otherwise. -/
def readT (n : ℕ) (L : List (Record n)) : PMF (Option Bool × Charge) :=
  match L.find? (fun r => decide (r.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) with
  | none => pure (none, zeroCharge)
  | some r => (parityReadout r.2.val r.2.property).map fun b =>
      (some b, ⟨0, 0, 1⟩)

/-- The value marginal of charged parity readout is the actual readout distribution. -/
theorem readT_map (n : ℕ) (L : List (Record n)) :
    (readT n L).map Prod.fst = actualReadout n L := by
  unfold readT actualReadout
  cases h : L.find?
      (fun r => decide (r.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) with
  | none =>
      change (PMF.pure ((none : Option Bool), zeroCharge)).map Prod.fst = PMF.pure none
      exact PMF.pure_map (f := Prod.fst) (a := ((none : Option Bool), zeroCharge))
  | some r => simp only [PMF.map_comp, Function.comp_def]

/-- The charged physical sieve execution: prepare `24*2^(3*m)` fresh records, run `m` sieve
layers, and attempt parity readout. -/
def runT (n m : ℕ) {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) : PMF (Option Bool × Charge) :=
  writerBind (freshT n f (24 * 2 ^ (3 * m))) fun L =>
    writerBind (recT n m f m L) (readT n)

/-- The output marginal of the charged physical execution is the actual dihedral sieve
distribution. -/
theorem runT_map (n m : ℕ) {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) :
    (runT n m f).map Prod.fst = dihedralSieveActual n m f := by
  rw [runT, writerBind_map, freshT_map, dihedralSieveActual, PMF.bind_bind]
  apply bind_kernel_congr
  intro L
  rw [writerBind_map, recT_map]
  apply bind_kernel_congr
  intro L'
  exact readT_map n L'

/-- For an oracle hiding reflection `s`, the charged physical sieve's output marginal equals the
ideal sieve output distribution for `s`. -/
theorem runT_actual_bridge (n m : ℕ) (S : Type)
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s) :
    (runT n m f).map Prod.fst = (dihedralSieveRun n m s).1 := by
  rw [runT_map, dihedralSieveBridge n m S f s hf]

/-- For an oracle hiding reflection `s`, the charged sieve assigns zero probability to a
returned Boolean different from the parity of `s.val`. -/
theorem runT_wrong_zero (n m : ℕ) (S : Type)
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s)
    (b : Bool) (hb : b ≠ decide (s.val % 2 = 1)) :
    ((runT n m f).map Prod.fst) (some b) = 0 := by
  rw [runT_actual_bridge n m S f s hf]
  exact dihedralSieveWrongAnswerZero n m s b hb

/-- For an oracle hiding reflection `s`, `n` at least two, and `m` the ceiling of `sqrt (n-1)`,
the charged physical sieve returns the parity of `s.val` with mass at least `ENNReal.ofReal
((1 - exp (-2^(m/3-2)))^m - 2^(-2^m))`, with the exponential expression evaluated over the
reals. -/
theorem runT_success (n : ℕ) (hn : 2 ≤ n) (S : Type)
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s) :
    let m := Nat.ceil (Real.sqrt ((n : ℝ) - 1))
    ENNReal.ofReal
      ((1 - Real.exp (-(2 : ℝ) ^ ((m : ℝ) / 3 - 2))) ^ m -
        (2 : ℝ) ^ (-((2 ^ m : ℕ) : ℝ))) ≤
      ((runT n m f).map Prod.fst) (some (decide (s.val % 2 = 1))) := by
  (try dsimp only)
  rw [runT_actual_bridge n _ S f s hf]
  exact (dihedralSieveAlgorithm n hn S f s hf).2.1

end PhysicalTrace

namespace PhysicalTrace
open Qatlib
open scoped Classical

/-- Every supported outcome of a charged sequential composition comes from supported outcomes of
both stages, with their charges added componentwise. -/
theorem writerBind_support {α β : Type*} (p : PMF (α × Charge))
    (k : α → PMF (β × Charge)) (z : β × Charge)
    (hz : z ∈ (writerBind p k).support) :
    ∃ x ∈ p.support, ∃ y ∈ (k x.1).support,
      (y.1, serial x.2 y.2) = z := by
  rw [writerBind, PMF.mem_support_bind_iff] at hz
  obtain ⟨x, hx, hz⟩ := hz
  rw [PMF.mem_support_map_iff] at hz
  obtain ⟨y, hy, he⟩ := hz
  exact ⟨x, hx, y, hy, he⟩

/-- Every supported result of `r` fresh preparations contains exactly `r` records and has fresh
charge `r`, with no pair or readout charges. -/
theorem freshT_inv (n : ℕ) {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2^n) → S) (r : ℕ) :
    ∀ st ∈ (freshT n f r).support,
      st.1.length = r ∧ st.2.fresh = r ∧
      st.2.pairs = 0 ∧ st.2.reads = 0 := by
  induction r with
  | zero =>
      intro st h
      change st ∈ (PMF.pure (([] : List (Record n)), zeroCharge)).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst st
      exact ⟨rfl, rfl, rfl, rfl⟩
  | succ r ih =>
      intro st h
      rw [freshT, PMF.mem_support_bind_iff] at h
      obtain ⟨q, _hq, h⟩ := h
      rw [PMF.mem_support_map_iff] at h
      obtain ⟨tail, ht, he⟩ := h
      subst st
      obtain ⟨hlen, hR, hE, hB⟩ := ih tail ht
      dsimp only [chargeFresh]
      simp only [List.length_cons]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Every supported pair-processing result contains at most one record per input pair and
charges exactly one extraction per pair, with no fresh or readout charges. -/
theorem layerAuxT_inv (n : ℕ) (ps : List (Record n × Record n)) :
    ∀ st ∈ (layerAuxT n ps).support,
      st.1.length ≤ ps.length ∧ st.2.fresh = 0 ∧
      st.2.pairs = ps.length ∧ st.2.reads = 0 := by
  induction ps with
  | nil =>
      intro st h
      change st ∈ (PMF.pure (([] : List (Record n)), zeroCharge)).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst st
      exact ⟨Nat.le_refl 0, rfl, rfl, rfl⟩
  | cons p ps ih =>
      rcases p with ⟨⟨k, χ⟩, ⟨ℓ, χ'⟩⟩
      intro st h
      rw [layerAuxT, PMF.mem_support_bind_iff] at h
      obtain ⟨q, _hq, h⟩ := h
      rw [PMF.mem_support_map_iff] at h
      obtain ⟨tail, ht, he⟩ := h
      subst st
      obtain ⟨hlen, hR, hE, hB⟩ := ih tail ht
      cases hb : q.1 <;>
        simp [chargePair, hR, hE, hB] <;> omega

/-- A supported sieve layer has no fresh or readout charge, uses at most half as many pairs as
input records, and retains at most one record per pair. The sum of its pair charge and
output length is at most the input length. -/
theorem layerT_inv (n w t : ℕ) (L : List (Record n))
    (st : List (Record n) × Charge) (h : st ∈ (layerT n w t L).support) :
    st.2.fresh = 0 ∧ st.2.reads = 0 ∧
      2*st.2.pairs ≤ L.length ∧ st.1.length ≤ st.2.pairs ∧
      st.2.pairs + st.1.length ≤ L.length := by
  obtain ⟨hlen, hR, hE, hB⟩ :=
    layerAuxT_inv n (sievePairWith n Prod.fst w t L) st h
  have hp := sievePairWith_length_bound n (α := Record n) Prod.fst w t L
  refine ⟨hR, hB, ?_, ?_, ?_⟩ <;> omega

/-- Every supported iterated sieve result has no fresh or readout charges, and its total pair
charge plus surviving record count is at most the initial record count. -/
theorem recT_inv (n m : ℕ) {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2^n) → S) (j : ℕ) (L : List (Record n)) :
    ∀ st ∈ (recT n m f j L).support,
      st.2.fresh = 0 ∧ st.2.reads = 0 ∧
      st.2.pairs + st.1.length ≤ L.length := by
  induction j with
  | zero =>
      intro st h
      change st ∈ (PMF.pure (L, zeroCharge)).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst st
      refine ⟨rfl, rfl, ?_⟩
      change 0 + L.length ≤ L.length
      omega
  | succ j ih =>
      intro st h
      change st ∈ (writerBind (recT n m f j L)
        (fun L' => layerT n (sieveWindowWidth n m j) (m*j) L')).support at h
      obtain ⟨x, hx, y, hy, he⟩ := writerBind_support _ _ _ h
      subst st
      obtain ⟨hxR, hxB, hxE⟩ := ih x hx
      obtain ⟨hyR, hyB, _hpair, _hlen, hyE⟩ :=
        layerT_inv n (sieveWindowWidth n m j) (m*j) x.1 y hy
      dsimp only [serial]
      refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Every supported parity-readout outcome has no fresh or pair charges and incurs at most one
readout. -/
theorem readT_inv (n : ℕ) (L : List (Record n))
    (st : Option Bool × Charge) (h : st ∈ (readT n L).support) :
    st.2.fresh = 0 ∧ st.2.pairs = 0 ∧ st.2.reads ≤ 1 := by
  cases hf : L.find?
      (fun r => decide (r.1 = ((2^(n-1):ℕ):ZMod (2^n)))) with
  | none =>
      change st ∈ (readT n L).support at h
      simp only [readT, hf] at h
      change st ∈ (PMF.pure ((none : Option Bool), zeroCharge)).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst st
      exact ⟨rfl, rfl, Nat.zero_le 1⟩
  | some r =>
      simp only [readT, hf, PMF.mem_support_map_iff] at h
      obtain ⟨b, _hb, he⟩ := h
      subst st
      exact ⟨rfl, rfl, Nat.le_refl 1⟩

/-- Every supported full sieve execution charges exactly `24*2^(3*m)` fresh preparations, at
most that many pair extractions, and at most one readout. -/
theorem runT_inv (n m : ℕ) {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2^n) → S) (st : Option Bool × Charge)
    (h : st ∈ (runT n m f).support) :
    st.2.fresh = 24*2^(3*m) ∧
      st.2.pairs ≤ 24*2^(3*m) ∧ st.2.reads ≤ 1 := by
  unfold runT at h
  obtain ⟨x, hx, y, hy, he⟩ := writerBind_support _ _ _ h
  obtain ⟨u, hu, v, hv, hvy⟩ := writerBind_support _ _ _ hy
  subst y
  subst st
  obtain ⟨hxlen, hxR, hxE, hxB⟩ := freshT_inv n f (24*2^(3*m)) x hx
  obtain ⟨huR, huB, huE⟩ := recT_inv n m f m x.1 u hu
  obtain ⟨hvR, hvE, hvB⟩ := readT_inv n u.1 v hv
  dsimp only [serial]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Every supported full sieve execution uses exactly `24*2^(3*m)` oracle queries and has macro
and measurement charges at most `2*(24*2^(3*m))+1`. -/
theorem runT_costs (n m : ℕ) {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2^n) → S) (st : Option Bool × Charge)
    (h : st ∈ (runT n m f).support) :
    queries st.2 = 24*2^(3*m) ∧
      macros st.2 ≤ 2*(24*2^(3*m))+1 ∧
      measurements st.2 ≤ 2*(24*2^(3*m))+1 := by
  obtain ⟨hR,hE,hB⟩ := runT_inv n m f st h
  dsimp only [queries, macros, measurements]
  refine ⟨?_, ?_, ?_⟩ <;> omega

end PhysicalTrace

namespace PhysicalTrace
open Qatlib

/-- Every supported recursive sieve state has at most `R` records when the input does. Any
subsequent pairing of that state also occupies at most `R` input record slots. -/
theorem recT_live_stage (n m : ℕ) {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2^n) → S) (j : ℕ) (L : List (Record n))
    (R w t : ℕ) (hL : L.length ≤ R)
    (st : List (Record n) × Charge) (h : st ∈ (recT n m f j L).support) :
    st.1.length ≤ R ∧
      2*(sievePairWith n Prod.fst w t st.1).length ≤ R := by
  obtain ⟨_hR,_hB,hE⟩ := recT_inv n m f j L st h
  have hp := sievePairWith_length_bound n (α := Record n) Prod.fst w t st.1
  constructor <;> omega

/-- Bounds retained outputs plus the two slots for each unfinished pair by the original `2 * p`
slots, provided at most one output is kept per completed pair. -/
theorem pair_live_slots_bound (p done kept : ℕ)
    (hdone : done ≤ p) (hkept : kept ≤ done) :
    kept + 2*(p-done) ≤ 2*p := by omega

end PhysicalTrace

namespace MatrixBlocks

/-- Alias for frequencies in `ZMod N` that equal their additive negatives. -/
abbrev SelfFreq := FourierEncoding.SelfFreq
/-- Alias for representatives of pairs of opposite frequencies, chosen by `k.val < (-k).val`. -/
abbrev PairFreq := FourierEncoding.PairFreq

/-- The complex sign associated with a Boolean, equal to `1` for `false` and `-1` for `true`. -/
def epsilon (b : Bool) : ℂ := if b then -1 else 1
/-- Selects `k` when the Boolean is `false` and `-k` when it is `true`. -/
def signed (k : ZMod N) (r : Bool) : ZMod N := if r then -k else k

/-- Every value of the standard additive character of `ZMod N` has `N`th power equal to `1`. -/
theorem character_pow_modulus (k : ZMod N) : ZMod.stdAddChar k ^ N = 1 := by
  rw [← ZMod.stdAddChar.map_nsmul_eq_pow]
  simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]

/-- The standard additive character values at `(-k) * s` and `k * s` multiply to `1`. -/
theorem character_neg_mul (s k : ZMod N) :
    ZMod.stdAddChar ((-k) * s) * ZMod.stdAddChar (k * s) = 1 := by
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  simp only [neg_mul, neg_add_cancel, AddChar.map_zero_eq_one]

/-- Raising the standard additive character at `k` to `a.val` gives its value at `k * a`. -/
theorem character_power_val (k a : ZMod N) :
    ZMod.stdAddChar k ^ a.val = ZMod.stdAddChar (k * a) := by
  rw [← ZMod.stdAddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

/-- The one-dimensional dihedral coefficient at a self-opposite frequency, given by the rotation
character times the Boolean reflection sign when `t` is true. -/
def selfCoefficient (k : SelfFreq N) (b : Bool) (a : ZMod N) (t : Bool) : ℂ :=
  ZMod.stdAddChar (k.1 * a) * if t then epsilon b else 1

/-- The one-dimensional rotation matrix whose sole diagonal entry is the standard additive
character at the self-opposite frequency `k`. -/
def selfX (k : SelfFreq N) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal fun _ => ZMod.stdAddChar k.1

/-- The one-dimensional reflection matrix with sole diagonal entry `epsilon b`. -/
def selfY (b : Bool) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal fun _ => epsilon b

/-- The one-dimensional rotation matrix `selfX k` is unitary. -/
theorem selfX_unitary (k : SelfFreq N) : selfX k ∈ Matrix.unitaryGroup (Fin 1) ℂ :=
  diagonal_mem_unitaryGroup _ fun _ => norm_stdAddChar _

/-- The one-dimensional reflection matrix `selfY b` is unitary. -/
theorem selfY_unitary (b : Bool) : selfY b ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  apply diagonal_mem_unitaryGroup
  intro i
  cases b <;> norm_num [epsilon]

/-- The `N`th power of the one-dimensional rotation matrix `selfX k` is the identity. -/
theorem selfX_order (k : SelfFreq N) : selfX k ^ N = 1 := by
  rw [selfX, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact character_pow_modulus k.1

/-- The square of the one-dimensional reflection matrix `selfY b` is the identity. -/
theorem selfY_order (b : Bool) : selfY b ^ 2 = 1 := by
  rw [selfY, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  cases b <;> norm_num [epsilon]

/-- The one-dimensional rotation and reflection matrices satisfy the dihedral relation:
conjugation by `selfY b` gives the adjoint of `selfX k`. -/
theorem self_relation (k : SelfFreq N) (b : Bool) :
    selfY b * selfX k * selfY b = (selfX k)ᴴ := by
  simp only [selfX, selfY, Matrix.diagonal_mul_diagonal, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  change epsilon b * ZMod.stdAddChar k.1 * epsilon b =
    star (ZMod.stdAddChar k.1)
  have hc : star (ZMod.stdAddChar k.1) = ZMod.stdAddChar k.1 := by
    change (starRingEnd ℂ) (ZMod.stdAddChar k.1) = _
    rw [conj_stdAddChar, ← k.2]
  rw [hc]
  cases b <;> simp [epsilon]

/-- The one-dimensional irreducible dihedral representation determined by a self-opposite
frequency `k` and reflection sign `epsilon b`. -/
def selfIrrep (k : SelfFreq N) (b : Bool) : DihedralIrrep N where
  dim := 1
  rhoX := selfX k
  rhoY := selfY b
  unitaryX := selfX_unitary k
  unitaryY := selfY_unitary b
  orderX := selfX_order k
  orderY := selfY_order b
  relation := self_relation k b
  irreducible := by
    intro M _ _
    refine ⟨M 0 0, ?_⟩
    ext i j
    have hi := Fin.eq_zero i
    have hj := Fin.eq_zero j
    subst i
    subst j
    simp

/-- The sole matrix coefficient of the generator word for rotation `a` and reflection bit `t` in
`selfIrrep k b` equals `selfCoefficient k b a t`. -/
theorem selfCoefficient_is_matrix_coefficient (k : SelfFreq N) (b : Bool)
    (a : ZMod N) (t : Bool) :
    ((selfIrrep k b).rhoX ^ a.val * (selfIrrep k b).rhoY ^ (if t then 1 else 0)) (0 : Fin 1) (0 : Fin 1) =
      selfCoefficient k b a t := by
  change (selfX k ^ a.val * selfY b ^ (if t then 1 else 0 : ℕ)) (0 : Fin 1) (0 : Fin 1) = _
  cases t <;>
    simp [selfCoefficient, selfX, selfY, Matrix.diagonal_pow, character_power_val]

/-- The two-dimensional diagonal rotation matrix with standard character entries at `k * a` and
`(-k) * a`, indexed by `false` and `true` respectively. -/
def rotation (k a : ZMod N) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun r => ZMod.stdAddChar (signed k r * a)

/-- The dihedral matrix block obtained from `rotation k a` by right multiplication with `PauliX`
when the reflection bit `t` is true. -/
def pairBlock (k a : ZMod N) (t : Bool) : Matrix Bool Bool ℂ :=
  rotation k a * if t then PauliX else 1

/-- The diagonal rotation matrix `rotation k a` is unitary for every frequency and rotation
parameter. -/
theorem rotation_unitary (k a : ZMod N) : rotation k a ∈ Matrix.unitaryGroup Bool ℂ :=
  diagonal_mem_unitaryGroup _ fun _ => norm_stdAddChar _

/-- Every dihedral matrix block `pairBlock k a t` is unitary. -/
theorem pairBlock_unitary (k a : ZMod N) (t : Bool) :
    pairBlock k a t ∈ Matrix.unitaryGroup Bool ℂ := by
  unfold pairBlock
  apply (Matrix.unitaryGroup Bool ℂ).mul_mem (rotation_unitary k a)
  cases t
  · exact (Matrix.unitaryGroup Bool ℂ).one_mem
  · exact pauliX_unitary

/-- Addition of rotation parameters corresponds to multiplication of the rotation matrices. -/
theorem rotation_add (k a c : ZMod N) :
    rotation k (a + c) = rotation k a * rotation k c := by
  rw [rotation, rotation, rotation, Matrix.diagonal_mul_diagonal]
  congr 1
  funext r
  change ZMod.stdAddChar (signed k r * (a + c)) =
    ZMod.stdAddChar (signed k r * a) * ZMod.stdAddChar (signed k r * c)
  rw [mul_add, ZMod.stdAddChar.map_add_eq_mul]

/-- The rotation matrix at `a` is the `a.val`th power of the rotation matrix at `1`. -/
theorem rotation_as_power (k a : ZMod N) : rotation k a = rotation k 1 ^ a.val := by
  rw [rotation, rotation, Matrix.diagonal_pow]
  congr 1
  funext r
  simpa only [Pi.pow_apply, mul_one] using! (character_power_val (signed k r) a).symm

/-- Expresses each dihedral matrix block as the `a.val`th power of the rotation generator
followed by the reflection generator to exponent `0` or `1`. -/
theorem pairBlock_is_generator_word (k a : ZMod N) (t : Bool) :
    pairBlock k a t = rotation k 1 ^ a.val * PauliX ^ (if t then 1 else 0) := by
  unfold pairBlock
  rw [rotation_as_power]
  cases t <;> simp

/-- The `N`th power of the two-dimensional rotation generator is the identity. -/
theorem rotation_generator_order (k : ZMod N) : rotation k 1 ^ N = 1 := by
  rw [rotation, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext r
  simpa only [Pi.pow_apply, mul_one] using! character_pow_modulus (signed k r)

/-- The Boolean reflection matrix `PauliX` squares to the identity. -/
theorem reflection_order : PauliX ^ 2 = (1 : Matrix Bool Bool ℂ) := by
  rw [pow_two]
  exact permMatrix_mul_self Bool.not_not

/-- Negating the rotation parameter gives the adjoint of the rotation matrix. -/
theorem rotation_neg (k a : ZMod N) : rotation k (-a) = (rotation k a)ᴴ := by
  rw [rotation, rotation, Matrix.diagonal_conjTranspose]
  congr 1
  funext r
  change ZMod.stdAddChar (signed k r * -a) = star (ZMod.stdAddChar (signed k r * a))
  rw [mul_neg]
  exact (conj_stdAddChar _).symm

/-- Conjugating a rotation matrix by `PauliX` negates its rotation parameter. -/
theorem reflection_rotation_reflection (k a : ZMod N) :
    PauliX * rotation k a * PauliX = rotation k (-a) := by
  ext i j
  cases i <;> cases j <;>
    simp [rotation, signed, PauliX, permMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply, mul_neg, neg_mul]

/-- The two-dimensional rotation generator and `PauliX` satisfy the dihedral relation, with
reflection conjugation giving the rotation adjoint. -/
theorem pair_generator_relation (k : ZMod N) :
    PauliX * rotation k 1 * PauliX = (rotation k 1)ᴴ :=
  (reflection_rotation_reflection k 1).trans (rotation_neg k 1)

/-- At a frequency in `PairFreq N`, every matrix commuting with both the rotation generator and
`PauliX` is a scalar multiple of the identity. -/
theorem pair_commutant_scalar (k : PairFreq N) (M : Matrix Bool Bool ℂ)
    (hX : M * rotation k.1 1 = rotation k.1 1 * M)
    (hY : M * PauliX = PauliX * M) : ∃ c : ℂ, M = c • 1 := by
  have hne : ZMod.stdAddChar k.1 ≠ ZMod.stdAddChar (-k.1) := by
    intro he
    have hv := congrArg ZMod.val (ZMod.injective_stdAddChar he)
    exact (Nat.ne_of_lt k.2) hv
  have h01 : M false true * ZMod.stdAddChar (-k.1) =
      ZMod.stdAddChar k.1 * M false true := by
    have he := congrArg (fun A : Matrix Bool Bool ℂ => A false true) hX
    simpa [rotation, signed, Matrix.mul_apply, Fintype.sum_bool] using! he
  have h10 : M true false * ZMod.stdAddChar k.1 =
      ZMod.stdAddChar (-k.1) * M true false := by
    have he := congrArg (fun A : Matrix Bool Bool ℂ => A true false) hX
    simpa [rotation, signed, Matrix.mul_apply, Fintype.sum_bool] using! he
  have hz01 : M false true = 0 := by
    have he : M false true * (ZMod.stdAddChar (-k.1) - ZMod.stdAddChar k.1) = 0 := by
      calc
        _ = M false true * ZMod.stdAddChar (-k.1) -
            ZMod.stdAddChar k.1 * M false true := by ring
        _ = 0 := sub_eq_zero.mpr h01
    exact (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hne.symm)
  have hz10 : M true false = 0 := by
    have he : M true false * (ZMod.stdAddChar k.1 - ZMod.stdAddChar (-k.1)) = 0 := by
      calc
        _ = M true false * ZMod.stdAddChar k.1 -
            ZMod.stdAddChar (-k.1) * M true false := by ring
        _ = 0 := sub_eq_zero.mpr h10
    exact (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hne)
  have hd : M false false = M true true := by
    have he := congrArg (fun A : Matrix Bool Bool ℂ => A false true) hY
    simpa [PauliX, permMatrix, Matrix.mul_apply, Fintype.sum_bool] using! he
  refine ⟨M false false, ?_⟩
  ext i j
  cases i <;> cases j <;> simp [Matrix.smul_apply, hz01, hz10, hd]

/-- Transposing a rotation followed by `PauliX` moves `PauliX` to the left of the same rotation. -/
theorem right_reflection_transpose (k s : ZMod N) :
    (rotation k s * PauliX)ᵀ = PauliX * rotation k s := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.transpose_apply, rotation, signed, PauliX, permMatrix,
      Matrix.mul_apply, Matrix.diagonal_apply]

/-- Multiplication of the matrix blocks follows the dihedral law: the first reflection bit
determines the sign of the second rotation, and reflection bits combine by XOR. -/
theorem pairBlock_mul (k a c : ZMod N) (t u : Bool) :
    pairBlock k a t * pairBlock k c u =
      pairBlock k (a + if t then -c else c) (Bool.xor t u) := by
  ext i j
  cases t <;> cases u <;> cases i <;> cases j <;>
    simp [pairBlock, rotation, signed, PauliX, permMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply, mul_add, mul_neg, neg_mul,
      ZMod.stdAddChar.map_add_eq_mul]

/-- The `false` row of a matrix block has character value at `k * a` in column `t` and vanishes
in the other column. -/
theorem pairBlock_false_row (k a : ZMod N) (b t : Bool) :
    pairBlock k a t false b =
      ZMod.stdAddChar (k * a) * if b = t then 1 else 0 := by
  cases b <;> cases t <;>
    simp [pairBlock, rotation, signed, PauliX, permMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply]

/-- The `true` row of a matrix block has character value at `(-k) * a` in column `!t` and
vanishes in the other column. -/
theorem pairBlock_true_row (k a : ZMod N) (b t : Bool) :
    pairBlock k a t true b =
      ZMod.stdAddChar ((-k) * a) * if b = !t then 1 else 0 := by
  cases b <;> cases t <;>
    simp [pairBlock, rotation, signed, PauliX, permMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply]

omit [NeZero N] in

/-- For the chosen representative of a pair of opposite frequencies, the representation basis
gate is the identity. -/
theorem basis_positive (k : PairFreq N) : representationBasisGate k.1 = 1 := by
  have hs : k.1 ≠ -k.1 := by
    intro he
    have hv := congrArg ZMod.val he
    have hk := k.2
    omega
  have hn : ¬(-k.1).val < k.1.val := not_lt_of_ge k.2.le
  rw [representationBasisGate, if_neg hs, if_neg hn]

omit [NeZero N] in

/-- At the negative of a chosen paired frequency representative, the representation basis gate
is `PauliX`. -/
theorem basis_negative (k : PairFreq N) : representationBasisGate (-k.1) = PauliX := by
  have hs : -k.1 ≠ -(-k.1) := by
    intro he
    have hv := congrArg ZMod.val he
    have hk := k.2
    simp only [neg_neg] at hv
    omega
  have hn : (-(-k.1)).val < (-k.1).val := by simpa only [neg_neg] using! k.2
  rw [representationBasisGate, if_neg hs, if_pos hn]

/-- At a self-opposite frequency, the representation Fourier kernel is the one-dimensional
coefficient scaled by `1 / sqrt N` and `1 / sqrt 2`. -/
theorem kernel_self (k : SelfFreq N) (a : ZMod N) (b t : Bool) :
    representationFourier (k.1, b) (a, t) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * selfCoefficient k b a t := by
  rw [representationFourier_kernel, representationBasisGate, if_pos k.2]
  cases b <;> cases t <;> simp [Hadamard, selfCoefficient, epsilon] <;> ring

/-- At a chosen paired frequency representative, the representation Fourier kernel is `1 / sqrt
N` times the `false` row of its matrix block. -/
theorem kernel_pair_positive (k : PairFreq N) (a : ZMod N) (b t : Bool) :
    representationFourier (k.1, b) (a, t) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * pairBlock k.1 a t false b := by
  rw [representationFourier_kernel, basis_positive, pairBlock_false_row]
  cases b <;> cases t <;> simp

/-- At the negative of a chosen paired frequency representative, the representation Fourier
kernel is `1 / sqrt N` times the `true` row of its matrix block. -/
theorem kernel_pair_negative (k : PairFreq N) (a : ZMod N) (b t : Bool) :
    representationFourier (-k.1, b) (a, t) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * pairBlock k.1 a t true b := by
  rw [representationFourier_kernel, basis_negative, pairBlock_true_row]
  cases b <;> cases t <;> simp [PauliX, permMatrix]

/-- The dihedral qubit phases at opposite frequencies multiply to `1`. -/
theorem phase_negative (s k : ZMod N) :
    dihedralQubitPhase N s (-k) * dihedralQubitPhase N s k = 1 := by
  rw [dihedralQubitPhase_eq_stdAddChar, dihedralQubitPhase_eq_stdAddChar]
  exact character_neg_mul s k

/-- Applying `PauliX` to the dihedral qubit state at `-k` gives the state at `k` multiplied by
the phase at `-k`. -/
theorem pauliX_negative_state (s k : ZMod N) :
    PauliX *ᵥ dihedralQubitState N s (-k) =
      dihedralQubitPhase N s (-k) • dihedralQubitState N s k := by
  ext b
  change ApplyGate (permMatrix Bool.not) (dihedralQubitState N s (-k)) b = _
  rw [applyGate_permMatrix Bool.not_not]
  cases b
  · simp only [dihedralQubitState, Bool.not_false, Bool.cond_true, Bool.cond_false,
      Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [dihedralQubitState, Bool.not_true, Bool.cond_false, Bool.cond_true,
      Pi.smul_apply, smul_eq_mul]
    calc
      (1 : ℂ) / Real.sqrt 2 * 1 =
          ((1 : ℂ) / Real.sqrt 2) *
            (dihedralQubitPhase N s (-k) * dihedralQubitPhase N s k) := by
              rw [phase_negative]
      _ = _ := by ring

omit [NeZero N] in

/-- The representation basis gate fixes the dihedral qubit state at a chosen paired frequency
representative. -/
theorem basis_positive_state (k : PairFreq N) (s : ZMod N) :
    representationBasisGate k.1 *ᵥ dihedralQubitState N s k.1 = dihedralQubitState N s k.1 := by
  rw [basis_positive, Matrix.one_mulVec]

/-- The representation basis gate sends the dihedral qubit state at a negative paired frequency
to the representative state multiplied by the negative-frequency phase. -/
theorem basis_negative_state (k : PairFreq N) (s : ZMod N) :
    representationBasisGate (-k.1) *ᵥ dihedralQubitState N s (-k.1) =
      dihedralQubitPhase N s (-k.1) • dihedralQubitState N s k.1 := by
  rw [basis_negative, pauliX_negative_state]

/-- After applying the representation basis gate, the dihedral qubit state at a negative paired
frequency agrees with the representative state up to a scalar of norm one. -/
theorem basis_negative_upToPhase (k : PairFreq N) (s : ZMod N) :
    UpToPhase (representationBasisGate (-k.1) *ᵥ dihedralQubitState N s (-k.1))
      (dihedralQubitState N s k.1) :=
  ⟨_, norm_dihedralQubitPhase N s (-k.1), basis_negative_state k s⟩

omit [NeZero N] in

/-- At a self-opposite frequency, component `b` after the representation basis gate equals `(1 +
epsilon b * dihedralQubitPhase N s k.1) / 2`. -/
theorem self_hadamard_state (k : SelfFreq N) (s : ZMod N) (b : Bool) :
    (representationBasisGate k.1 *ᵥ dihedralQubitState N s k.1) b =
      (1 + epsilon b * dihedralQubitPhase N s k.1) / 2 := by
  have hhalf : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, ← pow_two, sqrt2_sq]
  have hformula : (representationBasisGate k.1 *ᵥ dihedralQubitState N s k.1) b =
      ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) *
        (1 + epsilon b * dihedralQubitPhase N s k.1) := by
    rw [representationBasisGate, if_pos k.2]
    cases b <;>
      simp [Matrix.mulVec, dotProduct, Hadamard,
        dihedralQubitState, epsilon, one_div] <;> ring
  rw [hformula, hhalf]
  ring

/-- The dihedral qubit phase at a self-opposite frequency squares to `1`. -/
theorem self_phase_square (k : SelfFreq N) (s : ZMod N) :
    dihedralQubitPhase N s k.1 ^ 2 = 1 := by
  have hp := phase_negative s k.1
  rw [← k.2] at hp
  simpa only [pow_two] using! hp

/-- The dihedral qubit phase at a self-opposite frequency is either `1` or `-1`. -/
theorem self_phase_dichotomy (k : SelfFreq N) (s : ZMod N) :
    dihedralQubitPhase N s k.1 = 1 ∨ dihedralQubitPhase N s k.1 = -1 :=
  sq_eq_one_iff.mp (self_phase_square k s)

omit [NeZero N] in

/-- If the phase at a self-opposite frequency equals `epsilon b`, applying the representation
basis gate produces exactly the basis state `Ket b`. -/
theorem self_readout_ket (k : SelfFreq N) (s : ZMod N) (b : Bool)
    (hphase : dihedralQubitPhase N s k.1 = epsilon b) :
    representationBasisGate k.1 *ᵥ dihedralQubitState N s k.1 = Ket b := by
  ext t
  rw [self_hadamard_state, hphase]
  cases b <;> cases t <;> norm_num [epsilon, Ket]

/-- At every self-opposite frequency, there is a Boolean whose sign equals the dihedral qubit
phase and whose basis state is produced by the representation basis gate. -/
theorem self_readout_exists (k : SelfFreq N) (s : ZMod N) :
    ∃ b : Bool, dihedralQubitPhase N s k.1 = epsilon b ∧
      representationBasisGate k.1 *ᵥ dihedralQubitState N s k.1 = Ket b := by
  rcases self_phase_dichotomy k s with hp | hp
  · have he : dihedralQubitPhase N s k.1 = epsilon false := hp
    exact ⟨false, he, self_readout_ket k s false he⟩
  · have he : dihedralQubitPhase N s k.1 = epsilon true := hp
    exact ⟨true, he, self_readout_ket k s true he⟩

end MatrixBlocks

namespace Preparation

/-- The quantum Fourier transform over `ZMod N` sends the zero basis state to the uniform state. -/
theorem zmodQFT_prepares_uniform (N : ℕ) [NeZero N] :
    ApplyGate (zmodQFTGate (N := N)) (Ket (0 : ZMod N)) = Uniform (ZMod N) := by
  funext k
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Ket, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, zmodQFTGate_apply, Uniform, ZMod.card,
    AddChar.map_zero_eq_one]

/-- The Hadamard gate sends the `false` basis state to the uniform Boolean state. -/
theorem hadamard_prepares_uniform :
    ApplyGate Hadamard (Ket false) = Uniform Bool := by
  rw [applyGate_hadamard_ket_false]
  funext b
  simpa only [Plus, Uniform, Fintype.card_bool] using! hadamard_apply_false b

/-- The tensor product of uniform states on two finite types is the uniform state on their
product. -/
theorem tensor_uniform {I J : Type*} [Fintype I] [Fintype J] :
    TensorState (Uniform I) (Uniform J) = Uniform (I × J) := by
  funext p
  simp only [TensorState, Uniform, Fintype.card_prod, Nat.cast_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg (Fintype.card I)), Complex.ofReal_mul, mul_inv]

section Fresh

variable {N : ℕ} [NeZero N]
variable {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]

/-- Prepares the dihedral source register using the `ZMod N` quantum Fourier transform and a
Hadamard gate, tensored with the identity on the oracle output register. -/
def preparationGate : Matrix (DihedralReg N × S) (DihedralReg N × S) ℂ :=
  TensorGate (TensorGate (zmodQFTGate (N := N)) Hadamard) (1 : Matrix S S ℂ)

/-- The basis input with zero cyclic coordinate, Boolean coordinate `false`, and zero oracle
output coordinate. -/
def zeroInput : QState (DihedralReg N × S) :=
  Ket (((0 : ZMod N), false), (0 : S))

omit [AddCommGroup S] in

/-- The gate preparing the dihedral source register is unitary. -/
theorem preparationGate_unitary :
    preparationGate (N := N) (S := S) ∈ Matrix.unitaryGroup (DihedralReg N × S) ℂ :=
  tensorGate_unitary
    (tensorGate_unitary (zmodQFTGate_unitary (NeZero.pos N)) hadamard_unitary)
    (Matrix.unitaryGroup S ℂ).one_mem

/-- Applying the preparation gate to `zeroInput` gives a uniform dihedral source register
tensored with the zero basis state of the oracle output register. -/
theorem preparationGate_zero :
    ApplyGate (preparationGate (N := N) (S := S)) zeroInput =
      TensorState (Uniform (DihedralReg N)) (Ket (0 : S)) := by
  change ApplyGate preparationGate (Ket (((0 : ZMod N), false), (0 : S))) = _
  rw [← tensorState_ket_ket ((0 : ZMod N), false) (0 : S)]
  unfold preparationGate
  rw [applyGate_tensorGate, applyGate_one]
  rw [← tensorState_ket_ket (0 : ZMod N) false]
  rw [applyGate_tensorGate, zmodQFT_prepares_uniform, hadamard_prepares_uniform,
    tensor_uniform]

/-- The circuit that prepares a uniform dihedral source, executes `dihedralRecordCircuit`, and
applies the representation basis gate to the resulting record. -/
def freshRepresentationCircuit : Circuit (DihedralReg N × S) :=
  Step.gate preparationGate ::
    (dihedralRecordCircuit (N := N) (S := S) ++
      [Step.gate (representationRecordGate (N := N) (S := S))])

/-- Appends the adjoint representation record gate to `freshRepresentationCircuit` to return the
record to its original basis. -/
def freshReadbackCircuit : Circuit (DihedralReg N × S) :=
  freshRepresentationCircuit (N := N) (S := S) ++
    [Step.gate ((representationRecordGate (N := N) (S := S))ᴴ)]

omit [AddCommGroup S] in

/-- Every gate step of `freshRepresentationCircuit` is unitary. -/
theorem freshRepresentationCircuit_unitary :
    IsUnitaryCircuit (freshRepresentationCircuit (N := N) (S := S)) := by
  simp only [freshRepresentationCircuit, isUnitaryCircuit_gate, isUnitaryCircuit_append,
    isUnitaryCircuit_nil, and_true]
  exact ⟨preparationGate_unitary, dihedralRecordCircuit_unitary N,
    representationRecordGate_unitary⟩

omit [AddCommGroup S] in

/-- Every gate step of `freshReadbackCircuit` is unitary. -/
theorem freshReadbackCircuit_unitary :
    IsUnitaryCircuit (freshReadbackCircuit (N := N) (S := S)) := by
  simp only [freshReadbackCircuit, isUnitaryCircuit_append, isUnitaryCircuit_gate,
    isUnitaryCircuit_nil, and_true]
  exact ⟨freshRepresentationCircuit_unitary,
    conjTranspose_mem_unitaryGroup representationRecordGate_unitary⟩

/-- Running `freshRepresentationCircuit` with the additive oracle for `f` on `zeroInput`
produces the representation record state `representationJoint f`. -/
theorem freshRepresentationCircuit_run (f : DihedralReg N → S) :
    Run (AddOracle f) (freshRepresentationCircuit (N := N) (S := S)) zeroInput =
      representationJoint f := by
  change Run (AddOracle f)
    (dihedralRecordCircuit (N := N) (S := S) ++ [Step.gate representationRecordGate])
    (ApplyGate preparationGate zeroInput) = _
  rw [preparationGate_zero, run_append]
  rfl

/-- Running `freshReadbackCircuit` with the additive oracle for `f` on `zeroInput` produces the
original record state `dihedralRecordJoint N f`. -/
theorem freshReadbackCircuit_run (f : DihedralReg N → S) :
    Run (AddOracle f) (freshReadbackCircuit (N := N) (S := S)) zeroInput =
      dihedralRecordJoint N f := by
  rw [freshReadbackCircuit, run_append, freshRepresentationCircuit_run]
  change (representationRecordGate (N := N) (S := S))ᴴ *ᵥ representationJoint f = _
  exact representationJoint_readback f

omit [Fintype S] [AddCommGroup S] in

/-- The fresh representation circuit contains exactly one oracle query. -/
theorem freshRepresentationCircuit_queryCount :
    QueryCount (freshRepresentationCircuit (N := N) (S := S)) = 1 := rfl

omit [Fintype S] [AddCommGroup S] in

/-- The fresh representation circuit contains exactly three gate steps. -/
theorem freshRepresentationCircuit_gateCount :
    GateCount (freshRepresentationCircuit (N := N) (S := S)) = 3 := rfl

omit [Fintype S] [AddCommGroup S] in

/-- The fresh representation circuit has total size four, counting its gate and query steps. -/
theorem freshRepresentationCircuit_size :
    Size (freshRepresentationCircuit (N := N) (S := S)) = 4 := rfl

omit [Fintype S] [AddCommGroup S] in

/-- The fresh readback circuit contains exactly one oracle query. -/
theorem freshReadbackCircuit_queryCount :
    QueryCount (freshReadbackCircuit (N := N) (S := S)) = 1 := rfl

omit [Fintype S] [AddCommGroup S] in

/-- The fresh readback circuit contains exactly four gate steps. -/
theorem freshReadbackCircuit_gateCount :
    GateCount (freshReadbackCircuit (N := N) (S := S)) = 4 := rfl

omit [Fintype S] [AddCommGroup S] in

/-- The fresh readback circuit has total size five, counting its gate and query steps. -/
theorem freshReadbackCircuit_size :
    Size (freshReadbackCircuit (N := N) (S := S)) = 5 := rfl

/-- Running the fresh representation circuit from `zeroInput` with any additive oracle for `f`
yields a normalized state. -/
theorem freshRepresentationCircuit_normalized (f : DihedralReg N → S) :
    Normalized (Run (AddOracle f) freshRepresentationCircuit zeroInput) := by
  rw [freshRepresentationCircuit_run]
  exact representationJoint_normalized f

/-- Running the fresh readback circuit from `zeroInput` with any additive oracle for `f` yields
a normalized state. -/
theorem freshReadbackCircuit_normalized (f : DihedralReg N → S) :
    Normalized (Run (AddOracle f) freshReadbackCircuit zeroInput) := by
  rw [freshReadbackCircuit_run]
  exact normalized_dihedralRecordJoint N f

end Fresh
end Preparation

namespace RowTransport

open MatrixBlocks

/-- Scaling a qubit state by a complex scalar scales its outer product by the squared norm of
that scalar. -/
theorem scalar_outer (u : ℂ) (v : QState Bool) :
    outerProduct (u • v) = ((‖u‖^2 : ℝ) : ℂ) • outerProduct v := by
  ext i j
  simp only [outerProduct_apply, Pi.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply]
  calc
    u * v i * ((starRingEnd ℂ) u * (starRingEnd ℂ) (v j)) =
        (u * (starRingEnd ℂ) u) * (v i * (starRingEnd ℂ) (v j)) := by ring
    _ = _ := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

variable {N : ℕ} [NeZero N]
variable {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]

/-- The unnormalized qubit density matrix at frequency `k`, obtained by summing outer products
over the oracle-output register. -/
def rowDensity (f : DihedralReg N → S) (k : ZMod N) : Matrix Bool Bool ℂ :=
  ∑ z : S, outerProduct (fun b => representationJoint f ((k,b),z))

/-- For an oracle hiding reflection `s`, the density at frequency `k` is `1/N` times the outer
product of the basis-transformed dihedral phase qubit. -/
theorem rowDensity_factor (f : DihedralReg N → S) (s k : ZMod N)
    (hf : DihedralReflectionHides N f s) :
    rowDensity f k = ((1/(N : ℝ) : ℝ) : ℂ) •
      outerProduct (representationBasisGate k *ᵥ dihedralQubitState N s k) := by
  obtain ⟨gamma, hn, hfct⟩ := representationJoint_factor f s k hf
  have he : ∀ z, (fun b => representationJoint f ((k,b),z)) =
      gamma z • (representationBasisGate k *ᵥ dihedralQubitState N s k) := by
    intro z
    funext b
    exact hfct b z
  simp only [rowDensity, he, scalar_outer, ← Finset.sum_smul, ← Complex.ofReal_sum, hn]

/-- At the canonical frequency of a nonself-conjugate pair, a hiding oracle yields `1/N` times
the outer product of the corresponding dihedral phase qubit. -/
theorem pair_positive_density (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : PairFreq N) :
    rowDensity f k.1 = ((1/(N : ℝ) : ℝ) : ℂ) • outerProduct (dihedralQubitState N s k.1) := by
  rw [rowDensity_factor f s k.1 hf, basis_positive_state]

/-- At the negative frequency of a canonical pair, a hiding oracle yields the same density `1/N`
times the outer product of the canonical-frequency dihedral phase qubit. -/
theorem pair_negative_density (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : PairFreq N) :
    rowDensity f (-k.1) = ((1/(N : ℝ) : ℝ) : ℂ) • outerProduct (dihedralQubitState N s k.1) := by
  rw [rowDensity_factor f s (-k.1) hf, basis_negative_state, scalar_outer,
    norm_dihedralQubitPhase, one_pow, Complex.ofReal_one, one_smul]

/-- For an oracle hiding reflection `s`, the total Born mass of the two frequencies in a
canonical pair is `2/N`. -/
theorem pair_label_mass (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : PairFreq N) :
    (∑ b : Bool, ∑ z : S, ‖representationJoint f ((k.1,b),z)‖^2) +
      (∑ b : Bool, ∑ z : S, ‖representationJoint f ((-k.1,b),z)‖^2) = 2/(N : ℝ) := by
  rw [representation_row_mass f s k.1 hf, representation_row_mass f s (-k.1) hf]
  ring

/-- At a self-conjugate frequency, a hiding oracle assigns mass `1/N` to the bit whose sign
equals the dihedral phase and zero to the other bit. -/
theorem self_character_mass (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : SelfFreq N) (bit b : Bool)
    (hbit : dihedralQubitPhase N s k.1 = epsilon bit) :
    (∑ z : S, ‖representationJoint f ((k.1,b),z)‖^2) =
      if b = bit then 1/(N : ℝ) else 0 := by
  obtain ⟨gamma, hn, hfct⟩ := representationJoint_factor f s k.1 hf
  simp_rw [hfct, self_readout_ket k s bit hbit, Ket]
  by_cases hb : b = bit
  · simp only [hb, if_true, mul_one]
    exact hn
  · simp only [if_neg hb, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]

end RowTransport

namespace Resources

open PhysicalTrace Preparation

variable {N : ℕ} [NeZero N]
variable {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]

/-- The record distribution obtained by Born sampling the fresh readback circuit and retaining
the frequency, oracle output, and associated normalized qubit state. -/
def preparedRecord (f : DihedralReg N → S) : PMF (ZMod N × S × NormQ) :=
  (bornDistribution (Run (AddOracle f) freshReadbackCircuit zeroInput)
    (freshReadbackCircuit_normalized f)).map fun q =>
      (q.1.1, q.2, actualRecordState (fun t =>
        Run (AddOracle f) freshReadbackCircuit zeroInput ((q.1.1,t),q.2)))

/-- The record distribution prepared by the fresh readback circuit equals the actual dihedral
record distribution. -/
theorem preparedRecord_eq (f : DihedralReg N → S) :
    preparedRecord f = dihedralActualRecord N f := by
  unfold preparedRecord
  simp_rw [freshReadbackCircuit_run]
  rfl

/-- One step of charged fresh-record generation samples the circuit-prepared record, prepends
its frequency and qubit state, and increments the fresh-record charge. -/
theorem freshT_prepared (n : ℕ) (f : DihedralReg (2^n) → S) (r : ℕ) :
    freshT n f (r+1) = (preparedRecord f).bind fun q =>
      (freshT n f r).map fun st =>
        ((q.1,q.2.2)::st.1, chargeFresh st.2) := by
  rw [preparedRecord_eq]
  rfl

/-- The oracle query count obtained by charging one fresh readback circuit for each fresh record
in a trace. -/
def circuitQueries (n : ℕ) (S : Type) [DecidableEq S] (c : Charge) : ℕ :=
  QueryCount (freshReadbackCircuit (N := 2^n) (S := S)) * c.fresh

/-- The gate count obtained from fresh readback circuits, one CNOT per pair extraction, and one
Hadamard per readout. -/
def circuitGates (n : ℕ) (S : Type) [DecidableEq S] (c : Charge) : ℕ :=
  GateCount (freshReadbackCircuit (N := 2^n) (S := S)) * c.fresh +
    GateCount ([Step.gate CNOT] : Circuit (Bool × Bool)) * c.pairs +
    GateCount ([Step.gate Hadamard] : Circuit Bool) * c.reads

/-- Every supported charged sieve run uses `R = 24 * 2^(3*m)` queries, at most `5*R + 1` gates,
and at most `2*R + 1` measurements. -/
theorem circuitCosts (n m : ℕ) (f : DihedralReg (2^n) → S)
    (st : Option Bool × Charge) (h : st ∈ (runT n m f).support) :
    circuitQueries n S st.2 = 24*2^(3*m) ∧
      circuitGates n S st.2 ≤ 5*(24*2^(3*m))+1 ∧
      measurements st.2 ≤ 2*(24*2^(3*m))+1 := by
  obtain ⟨hR,hE,hB⟩ := runT_inv n m f st h
  change 1*st.2.fresh = _ ∧ 4*st.2.fresh+1*st.2.pairs+1*st.2.reads ≤ _ ∧
    st.2.fresh+st.2.pairs+st.2.reads ≤ _
  constructor
  · omega
  · constructor <;> omega

/-- Generating `r` fresh records produces a list of length at most `R` whenever `r ≤ R`. -/
theorem fresh_live (n : ℕ) (f : DihedralReg (2^n) → S) (R r : ℕ) (hr : r ≤ R)
    (st : List (Record n) × Charge) (h : st ∈ (freshT n f r).support) :
    st.1.length ≤ R := by
  have ht := (freshT_inv n f r st h).1
  omega

/-- If the original pairs occupy at most `R` record slots, the outputs retained from a processed
prefix together with the two slots per unprocessed pair still occupy at most `R` slots. -/
theorem pair_prefix_live (n R : ℕ) (done rest : List (Record n × Record n))
    (hslots : 2*(done++rest).length ≤ R)
    (st : List (Record n) × Charge) (h : st ∈ (layerAuxT n done).support) :
    st.1.length + 2*rest.length ≤ R := by
  have ht := (layerAuxT_inv n done st h).1
  simp only [List.length_append] at hslots
  omega

omit [DecidableEq S] [AddCommGroup S] in

/-- The dihedral source register and oracle-output workspace have total cardinality `2 * 2^n *
Fintype.card S`. -/
theorem source_workspace_card (n : ℕ) :
    Fintype.card (DihedralReg (2^n) × S) = 2*(2^n)*Fintype.card S := by
  simp only [DihedralReg, Fintype.card_prod, ZMod.card, Fintype.card_bool]
  ac_rfl

end Resources

namespace TypedFourier

open FourierEncoding MatrixBlocks

variable {N : ℕ} [NeZero N]

/-- The unscaled matrix coefficient selected by a typed Fourier index, using a self-frequency
character or an entry of the two-dimensional pair block. -/
def coefficient : Typed N → Raw N → ℂ
  | ⟨.inl (k,b), _⟩, (a,t) => selfCoefficient k b a t
  | ⟨.inr k, (i,j)⟩, (a,t) =>
      pairBlock k.1 a t (boolEquivFin2.symm i) (boolEquivFin2.symm j)

/-- The Fourier normalization factor, equal to `1 / (sqrt N * sqrt 2)` for one-dimensional
labels and `1 / sqrt N` for two-dimensional labels. -/
def scale : Label N → ℂ
  | .inl _ => (Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹
  | .inr _ => (Real.sqrt (N : ℝ) : ℂ)⁻¹

/-- The representation Fourier kernel with its output index reindexed by the typed label and
matrix-coordinate encoding. -/
def typedFourier (j : Typed N) (g : Raw N) : ℂ :=
  representationFourier (encode j) g

/-- Each typed Fourier kernel entry is the label-dependent normalization factor times the
corresponding unscaled matrix coefficient. -/
theorem typedFourier_kernel (j : Typed N) (g : Raw N) :
    typedFourier j g = scale j.1 * coefficient j g := by
  rcases j with ⟨L,i,j⟩
  rcases g with ⟨a,t⟩
  cases L with
  | inl kb =>
    rcases kb with ⟨k,b⟩
    change Fin 1 at i
    change Fin 1 at j
    have hi := Fin.eq_zero i
    have hj := Fin.eq_zero j
    subst i
    subst j
    exact kernel_self k a b t
  | inr k =>
    change Fin 2 at i
    change Fin 2 at j
    fin_cases i
    · exact kernel_pair_positive k a (boolEquivFin2.symm j) t
    · exact kernel_pair_negative k a (boolEquivFin2.symm j) t

/-- Decoding a raw output index before evaluating the typed Fourier kernel recovers the original
representation Fourier entry. -/
theorem typedFourier_readback (g h : Raw N) :
    typedFourier (decode g) h = representationFourier g h := by
  rw [typedFourier, encode_decode]

end TypedFourier

namespace Irreps

open MatrixBlocks

/-- The complex algebra equivalence that reindexes Boolean matrices as matrices indexed by `Fin
2`. -/
abbrev boolFin : Matrix Bool Bool ℂ ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ boolEquivFin2

/-- Reindexing a Boolean matrix preserves each entry at the corresponding `Fin 2` row and
column. -/
theorem boolFin_apply (A : Matrix Bool Bool ℂ) (r c : Bool) :
    boolFin A (boolEquivFin2 r) (boolEquivFin2 c) = A r c := by
  change A (boolEquivFin2.symm (boolEquivFin2 r))
    (boolEquivFin2.symm (boolEquivFin2 c)) = A r c
  rw [boolEquivFin2.symm_apply_apply, boolEquivFin2.symm_apply_apply]

/-- The Boolean-to-`Fin 2` matrix reindexing commutes with conjugate transpose. -/
theorem boolFin_star (A : Matrix Bool Bool ℂ) : boolFin Aᴴ = (boolFin A)ᴴ := rfl

/-- The Boolean-to-`Fin 2` matrix reindexing commutes with complex scalar multiplication. -/
theorem boolFin_smul (z : ℂ) (A : Matrix Bool Bool ℂ) :
    boolFin (z • A) = z • boolFin A := rfl

/-- Reindexing a unitary Boolean matrix by `Fin 2` preserves unitarity. -/
theorem boolFin_unitary (A : Matrix Bool Bool ℂ)
    (hA : A ∈ Matrix.unitaryGroup Bool ℂ) :
    boolFin A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hA ⊢
  change boolFin Aᴴ * boolFin A = 1
  rw [← map_mul, hA, map_one]

variable {N : ℕ} [NeZero N]

/-- The two-dimensional irreducible dihedral representation associated to a canonical frequency
pair, with diagonal rotation and Pauli-X reflection generators. -/
abbrev pairIrrep (k : FourierEncoding.PairFreq N) : DihedralIrrep N where
  dim := 2
  rhoX := boolFin (rotation k.1 1)
  rhoY := boolFin PauliX
  unitaryX := boolFin_unitary _ (rotation_unitary k.1 1)
  unitaryY := boolFin_unitary _ pauliX_unitary
  orderX := by
    rw [← map_pow, rotation_generator_order, map_one]
  orderY := by
    rw [← map_pow, reflection_order, map_one]
  relation := by
    rw [← map_mul, ← map_mul, pair_generator_relation]
    exact boolFin_star _
  irreducible := by
    intro M hX hY
    have hX' : boolFin.symm M * rotation k.1 1 = rotation k.1 1 * boolFin.symm M := by
      have hh := congrArg boolFin.symm hX
      simpa only [map_mul, boolFin.symm_apply_apply] using! hh
    have hY' : boolFin.symm M * PauliX = PauliX * boolFin.symm M := by
      have hh := congrArg boolFin.symm hY
      simpa only [map_mul, boolFin.symm_apply_apply] using! hh
    obtain ⟨z, hz⟩ := pair_commutant_scalar k (boolFin.symm M) hX' hY'
    refine ⟨z, ?_⟩
    calc
      M = boolFin (boolFin.symm M) := (boolFin.apply_symm_apply M).symm
      _ = boolFin (z • 1) := congrArg boolFin hz
      _ = z • 1 := by rw [boolFin_smul, map_one]

/-- A generator-word matrix coefficient of the pair representation equals the corresponding
Boolean pair-block entry. -/
theorem pair_matrix_coefficient (k : FourierEncoding.PairFreq N) (a : ZMod N)
    (t r c : Bool) :
    ((pairIrrep k).rhoX ^ a.val * (pairIrrep k).rhoY ^ (if t then 1 else 0))
      (boolEquivFin2 r) (boolEquivFin2 c) = pairBlock k.1 a t r c := by
  change (boolFin (rotation k.1 1) ^ a.val *
    boolFin PauliX ^ (if t then 1 else 0 : ℕ))
      (boolEquivFin2 r) (boolEquivFin2 c) = _
  rw [← map_pow, ← map_pow, ← map_mul, ← pairBlock_is_generator_word]
  exact boolFin_apply _ r c

/-- The pair representation's rotation generator is diagonal with additive-character entries at
the positive and negative frequencies. -/
theorem pair_rotation_diagonal (k : FourierEncoding.PairFreq N) :
    (pairIrrep k).rhoX =
      Matrix.diagonal (fun i : Fin 2 => ZMod.stdAddChar (signed k.1 (boolEquivFin2.symm i))) := by
  ext i j
  change rotation k.1 1 (boolEquivFin2.symm i) (boolEquivFin2.symm j) = _
  by_cases h : i = j
  · subst j
    simp [rotation]
  · have hn : boolEquivFin2.symm i ≠ boolEquivFin2.symm j :=
      fun he => h (boolEquivFin2.symm.injective he)
    simp [rotation, h, hn]

/-- A complex scalar intertwining multiplication by two distinct complex numbers must vanish. -/
theorem scalar_intertwiner_zero (x a b : ℂ) (hab : a ≠ b)
    (h : x * b = a * x) : x = 0 := by
  have hz : x * (b - a) = 0 := by
    calc
      _ = x * b - a * x := by ring
      _ = 0 := sub_eq_zero.mpr h
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hab.symm)

/-- A matrix intertwining two diagonal matrices with disjoint sets of diagonal entries must be
zero. -/
theorem diagonal_intertwiner_zero {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (a : I → ℂ) (b : J → ℂ)
    (hsep : ∀ i j, a i ≠ b j) (M : Matrix I J ℂ)
    (h : M * Matrix.diagonal b = Matrix.diagonal a * M) : M = 0 := by
  ext i j
  have he := congrArg (fun A : Matrix I J ℂ => A i j) h
  change (M * Matrix.diagonal b) i j = (Matrix.diagonal a * M) i j at he
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  exact scalar_intertwiner_zero (M i j) (a i) (b j) (hsep i j) he

/-- The map assigning the signs `1` and `-1` to Boolean values is injective. -/
theorem epsilon_injective : Function.Injective epsilon := by
  intro b c h
  cases b <;> cases c <;> first | rfl | norm_num [epsilon] at h

omit [NeZero N] in

/-- If signed frequencies from two canonical pairs coincide, the canonical pair representatives
are equal. -/
theorem pair_spectrum_equal (k l : FourierEncoding.PairFreq N) (r c : Bool)
    (he : signed k.1 r = signed l.1 c) : k = l := by
  apply Subtype.ext
  cases r <;> cases c
  · exact he
  · change k.1 = -l.1 at he
    have hk : (-l.1).val < l.1.val := by simpa only [he, neg_neg] using! k.2
    exact False.elim ((not_lt_of_ge l.2.le) hk)
  · change -k.1 = l.1 at he
    have hl : (-k.1).val < k.1.val := by simpa only [← he, neg_neg] using! l.2
    exact False.elim ((not_lt_of_ge k.2.le) hl)
  · change -k.1 = -l.1 at he
    exact neg_injective he

omit [NeZero N] in

/-- A self-conjugate frequency cannot equal either signed frequency of a canonical
nonself-conjugate pair. -/
theorem self_pair_spectrum_ne (k : FourierEncoding.SelfFreq N)
    (l : FourierEncoding.PairFreq N) (r : Bool) : k.1 ≠ signed l.1 r := by
  intro he
  have hs : signed l.1 r = -(signed l.1 r) := by
    rw [← he]
    exact k.2
  cases r
  · change l.1 = -l.1 at hs
    exact FourierEncoding.pair_not_self l hs
  · change -l.1 = -(-l.1) at hs
    apply FourierEncoding.pair_not_self l
    simpa only [neg_neg] using! hs.symm

/-- The canonical irreducible representation assigned to a Fourier label, using a
one-dimensional self-frequency representation or a two-dimensional pair representation. -/
def canonicalIrrep : FourierEncoding.Label N → DihedralIrrep N
  | .inl (k, b) => selfIrrep k b
  | .inr k => pairIrrep k

/-- The dimension of a canonical irreducible representation agrees with the dimension encoded by
its Fourier label. -/
theorem canonicalIrrep_dim (L : FourierEncoding.Label N) :
    (canonicalIrrep L).dim = FourierEncoding.dim L := by
  cases L <;> rfl

/-- The squared dimensions of the canonical irreducible representations sum to the dihedral
group order `2*N`. -/
theorem canonicalIrrep_dimensionCount :
    (∑ L : FourierEncoding.Label N, (canonicalIrrep L).dim ^ 2) = 2 * N := by
  simpa only [canonicalIrrep_dim] using! (FourierEncoding.dimensionCount (N := N))

/-- Every matrix intertwining both generators of canonical irreducible representations with
distinct labels is zero. -/
theorem canonicalIrrep_inequivalent (L K : FourierEncoding.Label N) (hLK : L ≠ K)
    (M : Matrix (Fin (canonicalIrrep L).dim) (Fin (canonicalIrrep K).dim) ℂ)
    (hX : M * (canonicalIrrep K).rhoX = (canonicalIrrep L).rhoX * M)
    (hY : M * (canonicalIrrep K).rhoY = (canonicalIrrep L).rhoY * M) : M = 0 := by
  cases L with
  | inl kb =>
    rcases kb with ⟨k, b⟩
    cases K with
    | inl lc =>
      rcases lc with ⟨l, c⟩
      change Matrix (Fin 1) (Fin 1) ℂ at M
      by_cases hkl : k = l
      · subst l
        have hbc : b ≠ c := by
          intro he
          subst c
          exact hLK rfl
        change M * selfY c = selfY b * M at hY
        apply diagonal_intertwiner_zero (fun _ : Fin 1 => epsilon b)
          (fun _ : Fin 1 => epsilon c) (fun _ _ he => hbc (epsilon_injective he)) M hY
      · change M * selfX l = selfX k * M at hX
        apply diagonal_intertwiner_zero (fun _ : Fin 1 => ZMod.stdAddChar k.1)
          (fun _ : Fin 1 => ZMod.stdAddChar l.1) ?_ M hX
        intro i j he
        exact hkl (Subtype.ext (ZMod.injective_stdAddChar he))
    | inr l =>
      change Matrix (Fin 1) (Fin 2) ℂ at M
      change M * (pairIrrep l).rhoX = selfX k * M at hX
      rw [pair_rotation_diagonal] at hX
      apply diagonal_intertwiner_zero (fun _ : Fin 1 => ZMod.stdAddChar k.1)
        (fun j : Fin 2 => ZMod.stdAddChar (signed l.1 (boolEquivFin2.symm j))) ?_ M hX
      intro i j he
      exact self_pair_spectrum_ne k l (boolEquivFin2.symm j) (ZMod.injective_stdAddChar he)
  | inr k =>
    cases K with
    | inl lc =>
      rcases lc with ⟨l, c⟩
      change Matrix (Fin 2) (Fin 1) ℂ at M
      change M * selfX l = (pairIrrep k).rhoX * M at hX
      rw [pair_rotation_diagonal] at hX
      apply diagonal_intertwiner_zero
        (fun i : Fin 2 => ZMod.stdAddChar (signed k.1 (boolEquivFin2.symm i)))
        (fun _ : Fin 1 => ZMod.stdAddChar l.1) ?_ M hX
      intro i j he
      exact self_pair_spectrum_ne l k (boolEquivFin2.symm i)
        (ZMod.injective_stdAddChar he).symm
    | inr l =>
      change Matrix (Fin 2) (Fin 2) ℂ at M
      change M * (pairIrrep l).rhoX = (pairIrrep k).rhoX * M at hX
      rw [pair_rotation_diagonal, pair_rotation_diagonal] at hX
      apply diagonal_intertwiner_zero
        (fun i : Fin 2 => ZMod.stdAddChar (signed k.1 (boolEquivFin2.symm i)))
        (fun j : Fin 2 => ZMod.stdAddChar (signed l.1 (boolEquivFin2.symm j))) ?_ M hX
      intro i j he
      have hkl := pair_spectrum_equal k l (boolEquivFin2.symm i) (boolEquivFin2.symm j)
        (ZMod.injective_stdAddChar he)
      exact hLK (congrArg Sum.inr hkl)

/-- The canonical family of dihedral irreducible representations, equipped with the
squared-dimension count and vanishing intertwiners between distinct labels. -/
def canonicalFamily : IrrepFamily N (FourierEncoding.Label N) where
  irrep := canonicalIrrep
  dimensionCount := canonicalIrrep_dimensionCount
  inequivalent := canonicalIrrep_inequivalent

/-- At a self-conjugate frequency, the representation Fourier kernel is the one-dimensional
representation coefficient scaled by `1 / (sqrt N * sqrt 2)`. -/
theorem actual_kernel_self (k : FourierEncoding.SelfFreq N) (e : Bool)
    (a : ZMod N) (t : Bool) :
    representationFourier (k.1, e) (a, t) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ *
        ((selfIrrep k e).rhoX ^ a.val * (selfIrrep k e).rhoY ^ (if t then 1 else 0))
          (0 : Fin 1) (0 : Fin 1) := by
  rw [selfCoefficient_is_matrix_coefficient]
  exact kernel_self k a e t

/-- At a canonical positive frequency, the representation Fourier kernel is `1 / sqrt N` times
the first-row coefficient of the pair representation. -/
theorem actual_kernel_pair_positive (k : FourierEncoding.PairFreq N)
    (a : ZMod N) (b t : Bool) :
    representationFourier (k.1, b) (a, t) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
        ((pairIrrep k).rhoX ^ a.val * (pairIrrep k).rhoY ^ (if t then 1 else 0))
          (boolEquivFin2 false) (boolEquivFin2 b) := by
  rw [pair_matrix_coefficient]
  exact kernel_pair_positive k a b t

/-- At the negative of a canonical frequency, the representation Fourier kernel is `1 / sqrt N`
times the second-row coefficient of the pair representation. -/
theorem actual_kernel_pair_negative (k : FourierEncoding.PairFreq N)
    (a : ZMod N) (b t : Bool) :
    representationFourier (-k.1, b) (a, t) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
        ((pairIrrep k).rhoX ^ a.val * (pairIrrep k).rhoY ^ (if t then 1 else 0))
          (boolEquivFin2 true) (boolEquivFin2 b) := by
  rw [pair_matrix_coefficient]
  exact kernel_pair_negative k a b t

end Irreps

namespace ProjectorLaw

open MatrixBlocks FourierEncoding TypedFourier

variable {N : ℕ} [NeZero N]

/-- The complex conjugate of the dihedral qubit phase is the additive character evaluated at
`(-k)*s`. -/
theorem phase_conj (s k : ZMod N) :
    (starRingEnd ℂ) (dihedralQubitPhase N s k) = ZMod.stdAddChar ((-k)*s) := by
  rw [dihedralQubitPhase_eq_stdAddChar, conj_stdAddChar, neg_mul]

/-- The dihedral phase qubit's outer product is one half of the sum of the identity and the
reflection matrix `PauliX * rotation k s`. -/
theorem qubit_density_projector (s k : ZMod N) :
    outerProduct (dihedralQubitState N s k) =
      (2 : ℂ)⁻¹ • ((1 : Matrix Bool Bool ℂ) + PauliX * rotation k s) := by
  have hh : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, ← pow_two, sqrt2_sq]
  have hn : dihedralQubitPhase N s k * ZMod.stdAddChar ((-k)*s) = 1 := by
    rw [dihedralQubitPhase_eq_stdAddChar, mul_comm]
    exact character_neg_mul s k
  ext i j
  cases i <;> cases j <;>
    simp only [outerProduct_apply, dihedralQubitState, Bool.cond_false, Bool.cond_true,
      one_div, map_mul, map_inv₀, Complex.conj_ofReal, Matrix.smul_apply,
      smul_eq_mul, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      rotation, Matrix.diagonal_apply, signed, PauliX, permMatrix, Matrix.of_apply,
      Fintype.sum_bool, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true,
      if_true, if_false, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
  · exact hh
  · rw [← mul_assoc, hh, phase_conj]
  · rw [mul_assoc, mul_comm (dihedralQubitPhase N s k), ← mul_assoc, hh,
      dihedralQubitPhase_eq_stdAddChar]
  · rw [phase_conj]
    calc
      _ = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) *
          (dihedralQubitPhase N s k * ZMod.stdAddChar ((-k)*s)) := by ring
      _ = _ := by rw [hh, hn, mul_one]

/-- The squared norm of the Fourier normalization factor is the label dimension divided by
`2*N`. -/
theorem scale_norm (L : Label N) :
    ‖scale L‖^2 = (dim L : ℝ)/(2*(N : ℝ)) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  cases L with
  | inl _ =>
    simp only [scale, dim, norm_mul, mul_pow, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg N), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Nat.cast_one]
    field_simp
  | inr _ =>
    simp only [scale, dim, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg N),
      Nat.cast_ofNat]
    field_simp

end ProjectorLaw

namespace FixedSubspace

open MatrixBlocks Irreps

variable {N : ℕ} [NeZero N]

/-- The pair representation's reflection operator at `s` is the reindexing of `PauliX * rotation
k.1 s`. -/
theorem pair_reflection (k : FourierEncoding.PairFreq N) (s : ZMod N) :
    reflectionElem (pairIrrep k) s = boolFin (PauliX * rotation k.1 s) := by
  change boolFin PauliX * boolFin (rotation k.1 1) ^ s.val = _
  rw [← map_pow, ← map_mul, ← rotation_as_power]

/-- The reflection operator in every canonical two-dimensional pair representation has trace
zero. -/
theorem pair_reflection_trace (k : FourierEncoding.PairFreq N) (s : ZMod N) :
    Matrix.trace (reflectionElem (pairIrrep k) s) = 0 := by
  rw [pair_reflection]
  unfold Matrix.trace
  rw [Fin.sum_univ_two]
  change boolFin (PauliX * rotation k.1 s) (boolEquivFin2 false) (boolEquivFin2 false) +
    boolFin (PauliX * rotation k.1 s) (boolEquivFin2 true) (boolEquivFin2 true) = 0
  rw [boolFin_apply, boolFin_apply]
  simp [PauliX, permMatrix, rotation, Matrix.mul_apply]

/-- The reflection-fixed subspace of a canonical pair representation has dimension one. -/
theorem pair_dimFixed (k : FourierEncoding.PairFreq N) (s : ZMod N) :
    dimFixed (pairIrrep k) s = 1 := by
  have hd := Qatlib.Concepts.HspRecovery.RecordExtract.irrep_dimFixed_eq_trace (pairIrrep k) s
  rw [pair_reflection_trace] at hd
  change (dimFixed (pairIrrep k) s : ℂ) = ((2 : ℂ) + 0) / 2 at hd
  norm_num at hd
  exact_mod_cast hd

/-- The reflection trace in a one-dimensional self-frequency representation is its Boolean sign
times the dihedral qubit phase. -/
theorem self_reflection_trace (k : FourierEncoding.SelfFreq N) (b : Bool) (s : ZMod N) :
    Matrix.trace (reflectionElem (selfIrrep k b) s) =
      epsilon b * dihedralQubitPhase N s k.1 := by
  change Matrix.trace (selfY b * selfX k ^ s.val) = _
  rw [selfY, selfX, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Fin.sum_univ_one]
  change epsilon b * ZMod.stdAddChar k.1 ^ s.val = _
  rw [character_power_val, dihedralQubitPhase_eq_stdAddChar]

/-- A self-frequency representation has a one-dimensional reflection-fixed subspace precisely
when its phase equals its Boolean sign, and dimension zero otherwise. -/
theorem self_dimFixed (k : FourierEncoding.SelfFreq N) (b : Bool) (s : ZMod N) :
    dimFixed (selfIrrep k b) s =
      if ZMod.stdAddChar (k.1 * s) = epsilon b then 1 else 0 := by
  have hd := Qatlib.Concepts.HspRecovery.RecordExtract.irrep_dimFixed_eq_trace (selfIrrep k b) s
  rw [self_reflection_trace] at hd
  have hd1 : (selfIrrep k b).dim = 1 := rfl
  rw [hd1, Nat.cast_one] at hd
  change (dimFixed (selfIrrep k b) s : ℂ) =
    ((1 : ℂ) + epsilon b * dihedralQubitPhase N s k.1) / 2 at hd
  rw [← dihedralQubitPhase_eq_stdAddChar N s k.1]
  rcases self_phase_dichotomy k s with hp | hp <;> cases b <;>
    norm_num [epsilon, hp] at hd ⊢ <;> exact_mod_cast hd

/-- Every canonical pair representation has label mass `2/N` for any hidden reflection
parameter. -/
theorem pair_repLabelMass (k : FourierEncoding.PairFreq N) (s : ZMod N) :
    repLabelMass (pairIrrep k) s = 2 / (N : ℝ) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  change (2 : ℝ) * (dimFixed (pairIrrep k) s : ℝ) * 2 / (2 * (N : ℝ)) = _
  rw [pair_dimFixed]
  push_cast
  field_simp [hN]

/-- A self-frequency representation has label mass `1/N` when its phase matches its Boolean sign
and zero otherwise. -/
theorem self_repLabelMass (k : FourierEncoding.SelfFreq N) (b : Bool) (s : ZMod N) :
    repLabelMass (selfIrrep k b) s =
      if ZMod.stdAddChar (k.1 * s) = epsilon b then 1 / (N : ℝ) else 0 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold repLabelMass
  have hd1 : (selfIrrep k b).dim = 1 := rfl
  rw [hd1, Nat.cast_one]
  rw [self_dimFixed]
  split_ifs <;> norm_num
  field_simp [hN]

/-- The projector onto the reflection-fixed subspace of a pair representation is the reindexed
outer product of the corresponding dihedral phase qubit. -/
theorem pair_fixed_projector (k : FourierEncoding.PairFreq N) (s : ZMod N) :
    (2 : ℂ)⁻¹ • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + reflectionElem (pairIrrep k) s) =
      boolFin (outerProduct (dihedralQubitState N s k.1)) := by
  rw [pair_reflection, ProjectorLaw.qubit_density_projector, boolFin_smul, map_add, map_one]

section ActualLabel

variable {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]

/-- For a hiding oracle, the total Born mass of a canonical frequency pair equals the
representation-theoretic label mass of its pair representation. -/
theorem actual_pair_label (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : FourierEncoding.PairFreq N) :
    (∑ b : Bool, ∑ z : S, ‖representationJoint f ((k.1,b),z)‖ ^ 2) +
      (∑ b : Bool, ∑ z : S, ‖representationJoint f ((-k.1,b),z)‖ ^ 2) =
      repLabelMass (pairIrrep k) s := by
  rw [pair_repLabelMass]
  exact RowTransport.pair_label_mass f s hf k

/-- For a hiding oracle, the Born mass of a self-frequency and sign label equals the
representation-theoretic label mass of its one-dimensional representation. -/
theorem actual_self_label (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : FourierEncoding.SelfFreq N) (b : Bool) :
    (∑ z : S, ‖representationJoint f ((k.1,b),z)‖ ^ 2) =
      repLabelMass (selfIrrep k b) s := by
  obtain ⟨bit, hbit, _⟩ := self_readout_exists k s
  rw [RowTransport.self_character_mass f s hf k bit b hbit, self_repLabelMass]
  rw [← dihedralQubitPhase_eq_stdAddChar N s k.1, hbit]
  by_cases hb : b = bit
  · subst b
    simp
  · have he : epsilon bit ≠ epsilon b := fun h => hb (epsilon_injective h).symm
    rw [if_neg hb, if_neg he]

/-- The Born mass assigned to a Fourier label, summing the relevant self-frequency entry or both
rows of a canonical frequency pair over the oracle-output register. -/
def labelBornMass (f : DihedralReg N → S) : FourierEncoding.Label N → ℝ
  | .inl (k,b) => ∑ z : S, ‖representationJoint f ((k.1,b),z)‖ ^ 2
  | .inr k =>
      (∑ b : Bool, ∑ z : S, ‖representationJoint f ((k.1,b),z)‖ ^ 2) +
      (∑ b : Bool, ∑ z : S, ‖representationJoint f ((-k.1,b),z)‖ ^ 2)

/-- For an oracle hiding reflection `s`, every canonical Fourier label has Born mass equal to
its representation-theoretic label mass. -/
theorem canonical_label_law (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (L : FourierEncoding.Label N) :
    labelBornMass f L = repLabelMass (canonicalFamily.irrep L) s := by
  cases L with
  | inl kb =>
    rcases kb with ⟨k,b⟩
    exact actual_self_label f s hf k b
  | inr k => exact actual_pair_label f s hf k

/-- For a hiding oracle, the reindexed density at a canonical positive frequency is `1/N` times
the reflection-fixed projector of its pair representation. -/
theorem actual_positive_fixed_density (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : FourierEncoding.PairFreq N) :
    boolFin (RowTransport.rowDensity f k.1) = ((1 / (N : ℝ) : ℝ) : ℂ) •
      ((2 : ℂ)⁻¹ • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + reflectionElem (pairIrrep k) s)) := by
  rw [RowTransport.pair_positive_density f s hf k, boolFin_smul, ← pair_fixed_projector]

/-- For a hiding oracle, the reindexed density at the negative of a canonical frequency is `1/N`
times the same reflection-fixed projector of its pair representation. -/
theorem actual_negative_fixed_density (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : FourierEncoding.PairFreq N) :
    boolFin (RowTransport.rowDensity f (-k.1)) = ((1 / (N : ℝ) : ℝ) : ℂ) •
      ((2 : ℂ)⁻¹ • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + reflectionElem (pairIrrep k) s)) := by
  rw [RowTransport.pair_negative_density f s hf k, boolFin_smul, ← pair_fixed_projector]

end ActualLabel
end FixedSubspace

namespace LabelEvent

open FourierEncoding

variable {N : ℕ} [NeZero N]
variable {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]

/-- The total Born mass of raw measurement outcomes whose decoded Fourier label is `L`, summed
over the oracle-output register. -/
def labelEventMass (f : DihedralReg N → S) (L : Label N) : ℝ :=
  ∑ g : Raw N, ∑ z : S, if (decode g).1 = L then ‖representationJoint f (g,z)‖^2 else 0

/-- The mass of a decoded label event equals the sum of squared amplitudes over all typed row
and column indices for that label and all oracle outputs. -/
theorem labelEventMass_eq_typed (f : DihedralReg N → S) (L : Label N) :
    labelEventMass f L =
      ∑ i : Fin (dim L), ∑ j : Fin (dim L), ∑ z : S,
        ‖representationJoint f (encode ⟨L,(i,j)⟩,z)‖^2 := by
  let h : Typed N → ℝ := fun j => ∑ z : S,
    if j.1 = L then ‖representationJoint f (encode j,z)‖^2 else 0
  have he := (decodeEquiv (N := N)).sum_comp h
  change (∑ g : Raw N, ∑ z : S, if (decode g).1 = L then
    ‖representationJoint f (encode (decode g),z)‖^2 else 0) = _ at he
  simp only [encode_decode] at he
  rw [show labelEventMass f L = ∑ j : Typed N, h j from he]
  rw [Fintype.sum_sigma]
  apply (Finset.sum_eq_single L ?_ ?_).trans
  · simp only [h, if_true, Fintype.sum_prod_type]
  · intro K _ hK
    simp only [h, if_neg hK, Finset.sum_const_zero]
  · intro hL
    exact (hL (Finset.mem_univ L)).elim

/-- The mass of a decoded Fourier-label event agrees with the casewise Born mass assigned to
that label. -/
theorem labelEventMass_eq_born (f : DihedralReg N → S) (L : Label N) :
    labelEventMass f L = FixedSubspace.labelBornMass f L := by
  rw [labelEventMass_eq_typed]
  cases L with
  | inl kb =>
    rcases kb with ⟨k,b⟩
    simp only [dim, Fin.sum_univ_one, encode, FixedSubspace.labelBornMass]
  | inr k =>
    simp only [dim, Fin.sum_univ_two, encode, FixedSubspace.labelBornMass,
      Fintype.sum_bool]
    simp only [if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
    change (∑ z : S, ‖representationJoint f ((k.1,false),z)‖^2) +
        (∑ z : S, ‖representationJoint f ((k.1,true),z)‖^2) +
        ((∑ z : S, ‖representationJoint f ((-k.1,false),z)‖^2) +
          (∑ z : S, ‖representationJoint f ((-k.1,true),z)‖^2)) = _
    ac_rfl

/-- For a hiding oracle, the mass of each decoded Fourier-label event equals the
representation-theoretic label mass in the canonical family. -/
theorem labelEventMass_eq_repLabelMass (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (L : Label N) :
    labelEventMass f L = Qatlib.Concepts.HspRecovery.RecordExtract.repLabelMass
      (Irreps.canonicalFamily.irrep L) s := by
  rw [labelEventMass_eq_born]
  exact FixedSubspace.canonical_label_law f s hf L

end LabelEvent

/-- For every nonzero modulus, the representation Fourier transform is unitary, the canonical
squared dimensions sum to `2*N`, and the typed kernel factors into its scale and matrix
coefficient. The squared scale norm is the label dimension divided by `2*N`. -/
def FiniteFourierTransport : Prop :=
  ∀ (N : ℕ) [NeZero N],
    representationFourier (N := N) ∈ Matrix.unitaryGroup (DihedralReg N) ℂ ∧
    (∑ L : FourierEncoding.Label N, (Irreps.canonicalFamily.irrep L).dim^2) = 2*N ∧
    (∀ j : FourierEncoding.Typed N, ∀ g : FourierEncoding.Raw N,
      TypedFourier.typedFourier j g = TypedFourier.scale j.1 * TypedFourier.coefficient j g) ∧
    (∀ L : FourierEncoding.Label N,
      ‖TypedFourier.scale L‖^2 = (FourierEncoding.dim L : ℝ)/(2*(N : ℝ)))

/-- The representation Fourier transform satisfies `FiniteFourierTransport`, including
unitarity, the dimension count, the coefficient formula, and the scale norm law. -/
theorem finiteFourierTransport : FiniteFourierTransport := by
  intro N _
  exact ⟨representationFourier_unitary, Irreps.canonicalIrrep_dimensionCount,
    TypedFourier.typedFourier_kernel, ProjectorLaw.scale_norm⟩

/-- For every hiding oracle over a nonzero modulus, the circuit prepares the normalized
representation joint state, and readback yields the actual record distribution, with the
specified pair densities and representation-theoretic label probabilities. Self-conjugate
frequencies place mass `1/N` on the phase-matching sign and zero on the other sign. -/
def RepresentationRecordTransport : Prop :=
  ∀ (N : ℕ) [NeZero N] (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg N → S) (s : ZMod N), DihedralReflectionHides N f s →
    Normalized (representationJoint f) ∧
    Run (AddOracle f) Preparation.freshRepresentationCircuit Preparation.zeroInput =
      representationJoint f ∧
    Resources.preparedRecord f = dihedralActualRecord N f ∧
    (∀ k : FourierEncoding.PairFreq N,
      RowTransport.rowDensity f k.1 = ((1/(N : ℝ) : ℝ) : ℂ) •
        outerProduct (dihedralQubitState N s k.1) ∧
      RowTransport.rowDensity f (-k.1) = ((1/(N : ℝ) : ℝ) : ℂ) •
        outerProduct (dihedralQubitState N s k.1) ∧
      (∑ b : Bool, ∑ z : S, ‖representationJoint f ((k.1,b),z)‖^2) +
        (∑ b : Bool, ∑ z : S, ‖representationJoint f ((-k.1,b),z)‖^2) = 2/(N : ℝ)) ∧
    (∀ L : FourierEncoding.Label N,
      LabelEvent.labelEventMass f L = repLabelMass (Irreps.canonicalFamily.irrep L) s) ∧
    (∀ k : FourierEncoding.SelfFreq N, ∃ bit : Bool,
      dihedralQubitPhase N s k.1 = MatrixBlocks.epsilon bit ∧
      ∀ b : Bool, (∑ z : S, ‖representationJoint f ((k.1,b),z)‖^2) =
        if b = bit then 1/(N : ℝ) else 0)

/-- Circuit preparation, record readback, pair densities, canonical label masses, and
self-frequency sign probabilities satisfy `RepresentationRecordTransport`. -/
theorem representationRecordTransport : RepresentationRecordTransport := by
  intro N _ S _ _ _ f s hf
  refine ⟨representationJoint_normalized f, Preparation.freshRepresentationCircuit_run f,
    Resources.preparedRecord_eq f, ?_, LabelEvent.labelEventMass_eq_repLabelMass f s hf, ?_⟩
  · intro k
    exact ⟨RowTransport.pair_positive_density f s hf k,
      RowTransport.pair_negative_density f s hf k, RowTransport.pair_label_mass f s hf k⟩
  · intro k
    obtain ⟨bit,hbit,_hout⟩ := MatrixBlocks.self_readout_exists k s
    exact ⟨bit,hbit,fun b => RowTransport.self_character_mass f s hf k bit b hbit⟩

/-- Extraction of two dihedral phase qubits has exactly two outcomes of mass `1/2`, with
normalized states equal up to unit complex scalars to the sum-frequency and
difference-frequency qubits. -/
def ExplicitExtractionLaw : Prop :=
  ∀ (N : ℕ) [NeZero N] (s k l : ZMod N),
    ∃ plus minus : QState Bool, ∃ _hp : Normalized plus, ∃ _hm : Normalized minus,
    ∃ u v : ℂ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      plus = u • dihedralQubitState N s (k+l) ∧
      minus = v • dihedralQubitState N s (k-l) ∧
      ∀ (b : Bool) (q : QState Bool) (hq : Normalized q),
        dihedralExtraction (dihedralQubitState N s k) (dihedralQubitState N s l)
          (normalized_dihedralQubitState N s k) (normalized_dihedralQubitState N s l) (b,⟨q,hq⟩) =
          if (b = false ∧ q = plus) ∨ (b = true ∧ q = minus) then 1/2 else 0

/-- Dihedral phase-qubit extraction satisfies `ExplicitExtractionLaw`, with equally weighted
sum-frequency and difference-frequency branches up to phase. -/
theorem explicitExtractionLaw : ExplicitExtractionLaw := by
  intro N _ s k l
  exact dihedralExtractionLaw N s k l

/-- For a hiding oracle with `n ≥ 2` and `m = ceil(sqrt(n - 1))`, the charged sieve has the
actual sieve output law, zero probability of a wrong parity, and the explicit exponential
lower bound on correct-parity success. With `R = 24 * 2^(3*m)`, its supported traces use
exactly `R` queries, at most `5*R + 1` gates and `2*R + 1` measurements, its fresh and
intermediate pair-processing lists fit within `R` record slots, and its source workspace has
cardinality `2 * 2^n * Fintype.card S`. -/
def ActualSieveConsumer : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg (2^n) → S) (s : ZMod (2^n)),
      DihedralReflectionHides (2^n) f s →
    let m := Nat.ceil (Real.sqrt ((n : ℝ)-1))
    let R := 24*2^(3*m)
    (PhysicalTrace.runT n m f).map Prod.fst =
      Qatlib.Concepts.HspRecovery.SieveAlgorithm.dihedralSieveActual n m f ∧
    (∀ b : Bool, b ≠ decide (s.val % 2 = 1) →
      ((PhysicalTrace.runT n m f).map Prod.fst) (some b) = 0) ∧
    ENNReal.ofReal ((1 - Real.exp (-(2 : ℝ)^((m : ℝ)/3-2)))^m -
      (2 : ℝ)^(-((2^m : ℕ) : ℝ))) ≤
      ((PhysicalTrace.runT n m f).map Prod.fst) (some (decide (s.val % 2 = 1))) ∧
    (∀ st ∈ (PhysicalTrace.runT n m f).support,
      Resources.circuitQueries n S st.2 = R ∧
      Resources.circuitGates n S st.2 ≤ 5*R+1 ∧ PhysicalTrace.measurements st.2 ≤ 2*R+1) ∧
    (∀ r : ℕ, r ≤ R → ∀ st ∈ (PhysicalTrace.freshT n f r).support, st.1.length ≤ R) ∧
    (∀ (L : List (PhysicalTrace.Record n)) (j w t : ℕ), L.length ≤ R →
      ∀ st ∈ (PhysicalTrace.recT n m f j L).support,
        st.1.length ≤ R ∧ 2*(Qatlib.Concepts.HspRecovery.SieveAlgorithm.sievePairWith
          n Prod.fst w t st.1).length ≤ R) ∧
    (∀ done rest : List (PhysicalTrace.Record n × PhysicalTrace.Record n),
      2*(done++rest).length ≤ R → ∀ st ∈ (PhysicalTrace.layerAuxT n done).support,
        st.1.length + 2*rest.length ≤ R) ∧
    Fintype.card (DihedralReg (2^n) × S) = 2*(2^n)*Fintype.card S

/-- The actual dihedral sieve satisfies `ActualSieveConsumer`, including its parity success law,
trace costs, live-record bounds, and workspace cardinality. -/
theorem actualSieveConsumer : ActualSieveConsumer := by
  intro n hn S _ _ _ f s hf
  (try dsimp only)
  refine ⟨PhysicalTrace.runT_map n _ f,
    fun b hb => PhysicalTrace.runT_wrong_zero n _ S f s hf b hb,
    PhysicalTrace.runT_success n hn S f s hf, Resources.circuitCosts n _ f,
    fun r hr st hst => Resources.fresh_live n f _ r hr st hst,
    ?_, fun done rest hslots st hst => Resources.pair_prefix_live n _ done rest hslots st hst,
    Resources.source_workspace_card n⟩
  intro L j w t hL st hst
  exact PhysicalTrace.recT_live_stage n _ f j L _ w t hL st hst

/-- The finite Fourier transform, representation-record transport, explicit two-qubit extraction
law, and actual sieve consumer properties all hold. -/
theorem frontier1 :
    FiniteFourierTransport ∧ RepresentationRecordTransport ∧
      ExplicitExtractionLaw ∧ ActualSieveConsumer :=
  ⟨finiteFourierTransport, representationRecordTransport, explicitExtractionLaw, actualSieveConsumer⟩

end Qatlib.Concepts.HspRecovery.OpenSieve
