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
set_option warningAsError false
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

def representationBasisGate (k : ZMod N) : Matrix Bool Bool ℂ :=
  if k = -k then Hadamard else if (-k).val < k.val then PauliX else 1

omit [NeZero N] in

theorem representationBasisGate_unitary (k : ZMod N) :
    representationBasisGate k ∈ Matrix.unitaryGroup Bool ℂ := by
  unfold representationBasisGate
  split_ifs
  · exact hadamard_unitary
  · exact pauliX_unitary
  · exact (Matrix.unitaryGroup Bool ℂ).one_mem

def representationFourier : Matrix (ZMod N × Bool) (ZMod N × Bool) ℂ :=
  Select representationBasisGate * TensorGate (zmodQFTGate (N := N)) (1 : Matrix Bool Bool ℂ)

theorem representationFourier_unitary :
    representationFourier (N := N) ∈ Matrix.unitaryGroup (ZMod N × Bool) ℂ :=
  (Matrix.unitaryGroup _ ℂ).mul_mem (select_unitary _ representationBasisGate_unitary)
    (tensorGate_unitary (zmodQFTGate_unitary (NeZero.pos N)) (Matrix.unitaryGroup Bool ℂ).one_mem)

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

def representationRecordGate : Matrix (DihedralReg N × S) (DihedralReg N × S) ℂ :=
  TensorGate (Select (representationBasisGate (N := N))) (1 : Matrix S S ℂ)

omit [AddCommGroup S] in

theorem representationRecordGate_unitary :
    representationRecordGate (N := N) (S := S) ∈ Matrix.unitaryGroup (DihedralReg N × S) ℂ :=
  tensorGate_unitary (select_unitary _ representationBasisGate_unitary) (Matrix.unitaryGroup S ℂ).one_mem

def representationJoint (f : DihedralReg N → S) : QState (DihedralReg N × S) :=
  ApplyGate representationRecordGate (dihedralRecordJoint N f)

theorem representationJoint_normalized (f : DihedralReg N → S) : Normalized (representationJoint f) :=
  normalized_applyGate representationRecordGate_unitary (normalized_dihedralRecordJoint N f)

theorem representationJoint_readback (f : DihedralReg N → S) :
    (representationRecordGate (N := N) (S := S))ᴴ *ᵥ representationJoint f = dihedralRecordJoint N f := by
  unfold representationJoint ApplyGate
  rw [Matrix.mulVec_mulVec]
  have hu := Matrix.mem_unitaryGroup_iff'.mp (representationRecordGate_unitary (N := N) (S := S))
  change representationRecordGateᴴ * representationRecordGate = 1 at hu
  rw [hu, Matrix.one_mulVec]

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

abbrev SelfFreq (N : ℕ) := {k : ZMod N // k = -k}
abbrev PairFreq (N : ℕ) := {k : ZMod N // k.val < (-k).val}
abbrev Label (N : ℕ) := Sum (SelfFreq N × Bool) (PairFreq N)

abbrev dim {N : ℕ} : Label N → ℕ
  | .inl _ => 1
  | .inr _ => 2

abbrev Typed (N : ℕ) := Σ L : Label N, Fin (dim L) × Fin (dim L)
abbrev Raw (N : ℕ) := ZMod N × Bool

variable {N : ℕ} [NeZero N]

omit [NeZero N] in

theorem pair_not_self (k : PairFreq N) : k.1 ≠ -k.1 := by
  intro he
  have hv : k.1.val = (-k.1).val := congrArg ZMod.val he
  have hk := k.2
  omega

theorem negative_of_not_self_not_positive (k : ZMod N)
    (hs : k ≠ -k) (hp : ¬k.val < (-k).val) : (-k).val < k.val := by
  have hne : k.val ≠ (-k).val := by
    intro he
    exact hs ((ZMod.val_injective N) he)
  omega

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

def encode : Typed N → Raw N
  | ⟨.inl (k, b), _⟩ => (k.1, b)
  | ⟨.inr k, (i, j)⟩ =>
      (if (i : Fin 2) = 0 then k.1 else -k.1, boolEquivFin2.symm j)

theorem decode_self (k : SelfFreq N) (b : Bool) :
    decode (k.1, b) =
      ⟨.inl (k, b), ((0 : Fin 1), (0 : Fin 1))⟩ := by
  dsimp only [decode]
  rw [dif_pos k.2]

theorem decode_positive (k : PairFreq N) (b : Bool) :
    decode (k.1, b) =
      ⟨.inr k, ((0 : Fin 2), boolEquivFin2 b)⟩ := by
  dsimp only [decode]
  rw [dif_neg (pair_not_self k), dif_pos k.2]

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

def decodeEquiv : Raw N ≃ Typed N where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

theorem typed_card : Fintype.card (Typed N) =
    ∑ L : Label N, (dim L) ^ 2 := by
  simp only [Typed, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, pow_two]

theorem raw_card : Fintype.card (Raw N) = 2 * N := by
  simp only [Raw, Fintype.card_prod, ZMod.card, Fintype.card_bool, Nat.mul_comm]

theorem dimensionCount : (∑ L : Label N, (dim L) ^ 2) = 2 * N := by
  have hc : Fintype.card (Raw N) = Fintype.card (Typed N) :=
    Fintype.card_congr (decodeEquiv (N := N))
  exact (typed_card (N := N)).symm.trans (hc.symm.trans (raw_card (N := N)))

theorem self_one (k : ZMod 1) : k = -k := Subsingleton.elim _ _

theorem self_two (k : ZMod 2) : k = -k := (ZMod.neg_eq_self_mod_two k).symm

theorem no_pair_one (k : PairFreq 1) : False := pair_not_self k (self_one k.1)

theorem no_pair_two (k : PairFreq 2) : False := pair_not_self k (self_two k.1)

end FourierEncoding

namespace PhysicalTrace

abbrev Record (n : ℕ) := ZMod (2 ^ n) × NormQ

structure Charge where
  fresh : ℕ
  pairs : ℕ
  reads : ℕ
  deriving DecidableEq

def zeroCharge : Charge := ⟨0, 0, 0⟩

def serial (c d : Charge) : Charge :=
  ⟨c.fresh + d.fresh, c.pairs + d.pairs, c.reads + d.reads⟩

def chargeFresh (c : Charge) : Charge :=
  ⟨c.fresh + 1, c.pairs, c.reads⟩

def chargePair (c : Charge) : Charge :=
  ⟨c.fresh, c.pairs + 1, c.reads⟩

def queries (c : Charge) : ℕ := c.fresh

def macros (c : Charge) : ℕ := c.fresh + c.pairs + c.reads

def measurements (c : Charge) : ℕ := c.fresh + c.pairs + c.reads

private theorem bind_kernel_congr {α β : Type*} (p : PMF α)
    (f g : α → PMF β) (h : ∀ a, f a = g a) : p.bind f = p.bind g :=
  congrArg (fun k : α → PMF β => p.bind k) (funext h)

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

def writerBind {α β : Type*} (p : PMF (α × Charge))
    (k : α → PMF (β × Charge)) : PMF (β × Charge) :=
  p.bind fun st => (k st.1).map fun out => (out.1, serial st.2 out.2)

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

def freshT (n : ℕ) {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) : ℕ → PMF (List (Record n) × Charge)
  | 0 => pure ([], zeroCharge)
  | r + 1 =>
    (dihedralActualRecord (2 ^ n) f).bind fun q =>
      (freshT n f r).map fun st =>
        ((q.1, q.2.2) :: st.1, chargeFresh st.2)

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

def layerAuxT (n : ℕ) :
    List (Record n × Record n) → PMF (List (Record n) × Charge)
  | [] => pure ([], zeroCharge)
  | ((k, χ), (ℓ, χ')) :: ps =>
    (dihedralExtraction χ.val χ'.val χ.property χ'.property).bind fun q =>
      (layerAuxT n ps).map fun st =>
        ((if q.1 then (k - ℓ, q.2) :: st.1 else st.1), chargePair st.2)

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

def layerT (n w t : ℕ) (L : List (Record n)) :
    PMF (List (Record n) × Charge) :=
  layerAuxT n (sievePairWith n Prod.fst w t L)

theorem layerT_map (n w t : ℕ) (L : List (Record n)) :
    (layerT n w t L).map Prod.fst = actualLayer n w t L :=
  layerAuxT_map n (sievePairWith n Prod.fst w t L)

def recT (n m : ℕ) {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) :
    ℕ → List (Record n) → PMF (List (Record n) × Charge)
  | 0, L => pure (L, zeroCharge)
  | j + 1, L => writerBind (recT n m f j L)
      (fun L' => layerT n (sieveWindowWidth n m j) (m * j) L')

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

def readT (n : ℕ) (L : List (Record n)) : PMF (Option Bool × Charge) :=
  match L.find? (fun r => decide (r.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) with
  | none => pure (none, zeroCharge)
  | some r => (parityReadout r.2.val r.2.property).map fun b =>
      (some b, ⟨0, 0, 1⟩)

theorem readT_map (n : ℕ) (L : List (Record n)) :
    (readT n L).map Prod.fst = actualReadout n L := by
  unfold readT actualReadout
  cases h : L.find?
      (fun r => decide (r.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) with
  | none =>
      change (PMF.pure ((none : Option Bool), zeroCharge)).map Prod.fst = PMF.pure none
      exact PMF.pure_map (f := Prod.fst) (a := ((none : Option Bool), zeroCharge))
  | some r => simp only [PMF.map_comp, Function.comp_def]

def runT (n m : ℕ) {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) : PMF (Option Bool × Charge) :=
  writerBind (freshT n f (24 * 2 ^ (3 * m))) fun L =>
    writerBind (recT n m f m L) (readT n)

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

theorem runT_actual_bridge (n m : ℕ) (S : Type)
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s) :
    (runT n m f).map Prod.fst = (dihedralSieveRun n m s).1 := by
  rw [runT_map, dihedralSieveBridge n m S f s hf]

theorem runT_wrong_zero (n m : ℕ) (S : Type)
    [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s)
    (b : Bool) (hb : b ≠ decide (s.val % 2 = 1)) :
    ((runT n m f).map Prod.fst) (some b) = 0 := by
  rw [runT_actual_bridge n m S f s hf]
  exact dihedralSieveWrongAnswerZero n m s b hb

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

theorem layerT_inv (n w t : ℕ) (L : List (Record n))
    (st : List (Record n) × Charge) (h : st ∈ (layerT n w t L).support) :
    st.2.fresh = 0 ∧ st.2.reads = 0 ∧
      2*st.2.pairs ≤ L.length ∧ st.1.length ≤ st.2.pairs ∧
      st.2.pairs + st.1.length ≤ L.length := by
  obtain ⟨hlen, hR, hE, hB⟩ :=
    layerAuxT_inv n (sievePairWith n Prod.fst w t L) st h
  have hp := sievePairWith_length_bound n (α := Record n) Prod.fst w t L
  refine ⟨hR, hB, ?_, ?_, ?_⟩ <;> omega

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

theorem pair_live_slots_bound (p done kept : ℕ)
    (hdone : done ≤ p) (hkept : kept ≤ done) :
    kept + 2*(p-done) ≤ 2*p := by omega

end PhysicalTrace

namespace MatrixBlocks

abbrev SelfFreq := FourierEncoding.SelfFreq
abbrev PairFreq := FourierEncoding.PairFreq

def epsilon (b : Bool) : ℂ := if b then -1 else 1
def signed (k : ZMod N) (r : Bool) : ZMod N := if r then -k else k

theorem character_pow_modulus (k : ZMod N) : ZMod.stdAddChar k ^ N = 1 := by
  rw [← ZMod.stdAddChar.map_nsmul_eq_pow]
  simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]

theorem character_neg_mul (s k : ZMod N) :
    ZMod.stdAddChar ((-k) * s) * ZMod.stdAddChar (k * s) = 1 := by
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  simp only [neg_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem character_power_val (k a : ZMod N) :
    ZMod.stdAddChar k ^ a.val = ZMod.stdAddChar (k * a) := by
  rw [← ZMod.stdAddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

def selfCoefficient (k : SelfFreq N) (b : Bool) (a : ZMod N) (t : Bool) : ℂ :=
  ZMod.stdAddChar (k.1 * a) * if t then epsilon b else 1

def selfX (k : SelfFreq N) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal fun _ => ZMod.stdAddChar k.1

def selfY (b : Bool) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal fun _ => epsilon b

theorem selfX_unitary (k : SelfFreq N) : selfX k ∈ Matrix.unitaryGroup (Fin 1) ℂ :=
  diagonal_mem_unitaryGroup _ fun _ => norm_stdAddChar _

theorem selfY_unitary (b : Bool) : selfY b ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  apply diagonal_mem_unitaryGroup
  intro i
  cases b <;> norm_num [epsilon]

theorem selfX_order (k : SelfFreq N) : selfX k ^ N = 1 := by
  rw [selfX, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact character_pow_modulus k.1

theorem selfY_order (b : Bool) : selfY b ^ 2 = 1 := by
  rw [selfY, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  cases b <;> norm_num [epsilon]

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

theorem selfCoefficient_is_matrix_coefficient (k : SelfFreq N) (b : Bool)
    (a : ZMod N) (t : Bool) :
    ((selfIrrep k b).rhoX ^ a.val * (selfIrrep k b).rhoY ^ (if t then 1 else 0)) (0 : Fin 1) (0 : Fin 1) =
      selfCoefficient k b a t := by
  change (selfX k ^ a.val * selfY b ^ (if t then 1 else 0 : ℕ)) (0 : Fin 1) (0 : Fin 1) = _
  cases t <;>
    simp [selfCoefficient, selfX, selfY, Matrix.diagonal_pow, character_power_val]

def rotation (k a : ZMod N) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun r => ZMod.stdAddChar (signed k r * a)

def pairBlock (k a : ZMod N) (t : Bool) : Matrix Bool Bool ℂ :=
  rotation k a * if t then PauliX else 1

theorem rotation_unitary (k a : ZMod N) : rotation k a ∈ Matrix.unitaryGroup Bool ℂ :=
  diagonal_mem_unitaryGroup _ fun _ => norm_stdAddChar _

theorem pairBlock_unitary (k a : ZMod N) (t : Bool) :
    pairBlock k a t ∈ Matrix.unitaryGroup Bool ℂ := by
  unfold pairBlock
  apply (Matrix.unitaryGroup Bool ℂ).mul_mem (rotation_unitary k a)
  cases t
  · exact (Matrix.unitaryGroup Bool ℂ).one_mem
  · exact pauliX_unitary

theorem rotation_add (k a c : ZMod N) :
    rotation k (a + c) = rotation k a * rotation k c := by
  rw [rotation, rotation, rotation, Matrix.diagonal_mul_diagonal]
  congr 1
  funext r
  change ZMod.stdAddChar (signed k r * (a + c)) =
    ZMod.stdAddChar (signed k r * a) * ZMod.stdAddChar (signed k r * c)
  rw [mul_add, ZMod.stdAddChar.map_add_eq_mul]

theorem rotation_as_power (k a : ZMod N) : rotation k a = rotation k 1 ^ a.val := by
  rw [rotation, rotation, Matrix.diagonal_pow]
  congr 1
  funext r
  simpa only [Pi.pow_apply, mul_one] using! (character_power_val (signed k r) a).symm

theorem pairBlock_is_generator_word (k a : ZMod N) (t : Bool) :
    pairBlock k a t = rotation k 1 ^ a.val * PauliX ^ (if t then 1 else 0) := by
  unfold pairBlock
  rw [rotation_as_power]
  cases t <;> simp

theorem rotation_generator_order (k : ZMod N) : rotation k 1 ^ N = 1 := by
  rw [rotation, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext r
  simpa only [Pi.pow_apply, mul_one] using! character_pow_modulus (signed k r)

theorem reflection_order : PauliX ^ 2 = (1 : Matrix Bool Bool ℂ) := by
  rw [pow_two]
  exact permMatrix_mul_self Bool.not_not

theorem rotation_neg (k a : ZMod N) : rotation k (-a) = (rotation k a)ᴴ := by
  rw [rotation, rotation, Matrix.diagonal_conjTranspose]
  congr 1
  funext r
  change ZMod.stdAddChar (signed k r * -a) = star (ZMod.stdAddChar (signed k r * a))
  rw [mul_neg]
  exact (conj_stdAddChar _).symm

theorem reflection_rotation_reflection (k a : ZMod N) :
    PauliX * rotation k a * PauliX = rotation k (-a) := by
  ext i j
  cases i <;> cases j <;>
    simp [rotation, signed, PauliX, permMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply, mul_neg, neg_mul]

theorem pair_generator_relation (k : ZMod N) :
    PauliX * rotation k 1 * PauliX = (rotation k 1)ᴴ :=
  (reflection_rotation_reflection k 1).trans (rotation_neg k 1)

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

theorem right_reflection_transpose (k s : ZMod N) :
    (rotation k s * PauliX)ᵀ = PauliX * rotation k s := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.transpose_apply, rotation, signed, PauliX, permMatrix,
      Matrix.mul_apply, Matrix.diagonal_apply]

theorem pairBlock_mul (k a c : ZMod N) (t u : Bool) :
    pairBlock k a t * pairBlock k c u =
      pairBlock k (a + if t then -c else c) (Bool.xor t u) := by
  ext i j
  cases t <;> cases u <;> cases i <;> cases j <;>
    simp [pairBlock, rotation, signed, PauliX, permMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply, mul_add, mul_neg, neg_mul,
      ZMod.stdAddChar.map_add_eq_mul]

theorem pairBlock_false_row (k a : ZMod N) (b t : Bool) :
    pairBlock k a t false b =
      ZMod.stdAddChar (k * a) * if b = t then 1 else 0 := by
  cases b <;> cases t <;>
    simp [pairBlock, rotation, signed, PauliX, permMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply]

theorem pairBlock_true_row (k a : ZMod N) (b t : Bool) :
    pairBlock k a t true b =
      ZMod.stdAddChar ((-k) * a) * if b = !t then 1 else 0 := by
  cases b <;> cases t <;>
    simp [pairBlock, rotation, signed, PauliX, permMatrix, Matrix.mul_apply,
      Matrix.diagonal_apply]

omit [NeZero N] in

theorem basis_positive (k : PairFreq N) : representationBasisGate k.1 = 1 := by
  have hs : k.1 ≠ -k.1 := by
    intro he
    have hv := congrArg ZMod.val he
    have hk := k.2
    omega
  have hn : ¬(-k.1).val < k.1.val := not_lt_of_ge k.2.le
  rw [representationBasisGate, if_neg hs, if_neg hn]

omit [NeZero N] in

theorem basis_negative (k : PairFreq N) : representationBasisGate (-k.1) = PauliX := by
  have hs : -k.1 ≠ -(-k.1) := by
    intro he
    have hv := congrArg ZMod.val he
    have hk := k.2
    simp only [neg_neg] at hv
    omega
  have hn : (-(-k.1)).val < (-k.1).val := by simpa only [neg_neg] using! k.2
  rw [representationBasisGate, if_neg hs, if_pos hn]

theorem kernel_self (k : SelfFreq N) (a : ZMod N) (b t : Bool) :
    representationFourier (k.1, b) (a, t) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * selfCoefficient k b a t := by
  rw [representationFourier_kernel, representationBasisGate, if_pos k.2]
  cases b <;> cases t <;> simp [Hadamard, selfCoefficient, epsilon] <;> ring

theorem kernel_pair_positive (k : PairFreq N) (a : ZMod N) (b t : Bool) :
    representationFourier (k.1, b) (a, t) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * pairBlock k.1 a t false b := by
  rw [representationFourier_kernel, basis_positive, pairBlock_false_row]
  cases b <;> cases t <;> simp

theorem kernel_pair_negative (k : PairFreq N) (a : ZMod N) (b t : Bool) :
    representationFourier (-k.1, b) (a, t) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * pairBlock k.1 a t true b := by
  rw [representationFourier_kernel, basis_negative, pairBlock_true_row]
  cases b <;> cases t <;> simp [PauliX, permMatrix]

theorem phase_negative (s k : ZMod N) :
    dihedralQubitPhase N s (-k) * dihedralQubitPhase N s k = 1 := by
  rw [dihedralQubitPhase_eq_stdAddChar, dihedralQubitPhase_eq_stdAddChar]
  exact character_neg_mul s k

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

theorem basis_positive_state (k : PairFreq N) (s : ZMod N) :
    representationBasisGate k.1 *ᵥ dihedralQubitState N s k.1 = dihedralQubitState N s k.1 := by
  rw [basis_positive, Matrix.one_mulVec]

theorem basis_negative_state (k : PairFreq N) (s : ZMod N) :
    representationBasisGate (-k.1) *ᵥ dihedralQubitState N s (-k.1) =
      dihedralQubitPhase N s (-k.1) • dihedralQubitState N s k.1 := by
  rw [basis_negative, pauliX_negative_state]

theorem basis_negative_upToPhase (k : PairFreq N) (s : ZMod N) :
    UpToPhase (representationBasisGate (-k.1) *ᵥ dihedralQubitState N s (-k.1))
      (dihedralQubitState N s k.1) :=
  ⟨_, norm_dihedralQubitPhase N s (-k.1), basis_negative_state k s⟩

omit [NeZero N] in

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

theorem self_phase_square (k : SelfFreq N) (s : ZMod N) :
    dihedralQubitPhase N s k.1 ^ 2 = 1 := by
  have hp := phase_negative s k.1
  rw [← k.2] at hp
  simpa only [pow_two] using! hp

theorem self_phase_dichotomy (k : SelfFreq N) (s : ZMod N) :
    dihedralQubitPhase N s k.1 = 1 ∨ dihedralQubitPhase N s k.1 = -1 :=
  sq_eq_one_iff.mp (self_phase_square k s)

omit [NeZero N] in

theorem self_readout_ket (k : SelfFreq N) (s : ZMod N) (b : Bool)
    (hphase : dihedralQubitPhase N s k.1 = epsilon b) :
    representationBasisGate k.1 *ᵥ dihedralQubitState N s k.1 = Ket b := by
  ext t
  rw [self_hadamard_state, hphase]
  cases b <;> cases t <;> norm_num [epsilon, Ket]

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

theorem zmodQFT_prepares_uniform (N : ℕ) [NeZero N] :
    ApplyGate (zmodQFTGate (N := N)) (Ket (0 : ZMod N)) = Uniform (ZMod N) := by
  funext k
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Ket, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, zmodQFTGate_apply, Uniform, ZMod.card,
    AddChar.map_zero_eq_one]

theorem hadamard_prepares_uniform :
    ApplyGate Hadamard (Ket false) = Uniform Bool := by
  rw [applyGate_hadamard_ket_false]
  funext b
  simpa only [Plus, Uniform, Fintype.card_bool] using! hadamard_apply_false b

theorem tensor_uniform {I J : Type*} [Fintype I] [Fintype J] :
    TensorState (Uniform I) (Uniform J) = Uniform (I × J) := by
  funext p
  simp only [TensorState, Uniform, Fintype.card_prod, Nat.cast_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg (Fintype.card I)), Complex.ofReal_mul, mul_inv]

section Fresh

variable {N : ℕ} [NeZero N]
variable {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]

def preparationGate : Matrix (DihedralReg N × S) (DihedralReg N × S) ℂ :=
  TensorGate (TensorGate (zmodQFTGate (N := N)) Hadamard) (1 : Matrix S S ℂ)

def zeroInput : QState (DihedralReg N × S) :=
  Ket (((0 : ZMod N), false), (0 : S))

omit [AddCommGroup S] in

theorem preparationGate_unitary :
    preparationGate (N := N) (S := S) ∈ Matrix.unitaryGroup (DihedralReg N × S) ℂ :=
  tensorGate_unitary
    (tensorGate_unitary (zmodQFTGate_unitary (NeZero.pos N)) hadamard_unitary)
    (Matrix.unitaryGroup S ℂ).one_mem

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

def freshRepresentationCircuit : Circuit (DihedralReg N × S) :=
  Step.gate preparationGate ::
    (dihedralRecordCircuit (N := N) (S := S) ++
      [Step.gate (representationRecordGate (N := N) (S := S))])

def freshReadbackCircuit : Circuit (DihedralReg N × S) :=
  freshRepresentationCircuit (N := N) (S := S) ++
    [Step.gate ((representationRecordGate (N := N) (S := S))ᴴ)]

omit [AddCommGroup S] in

theorem freshRepresentationCircuit_unitary :
    IsUnitaryCircuit (freshRepresentationCircuit (N := N) (S := S)) := by
  simp only [freshRepresentationCircuit, isUnitaryCircuit_gate, isUnitaryCircuit_append,
    isUnitaryCircuit_nil, and_true]
  exact ⟨preparationGate_unitary, dihedralRecordCircuit_unitary N,
    representationRecordGate_unitary⟩

omit [AddCommGroup S] in

theorem freshReadbackCircuit_unitary :
    IsUnitaryCircuit (freshReadbackCircuit (N := N) (S := S)) := by
  simp only [freshReadbackCircuit, isUnitaryCircuit_append, isUnitaryCircuit_gate,
    isUnitaryCircuit_nil, and_true]
  exact ⟨freshRepresentationCircuit_unitary,
    conjTranspose_mem_unitaryGroup representationRecordGate_unitary⟩

theorem freshRepresentationCircuit_run (f : DihedralReg N → S) :
    Run (AddOracle f) (freshRepresentationCircuit (N := N) (S := S)) zeroInput =
      representationJoint f := by
  change Run (AddOracle f)
    (dihedralRecordCircuit (N := N) (S := S) ++ [Step.gate representationRecordGate])
    (ApplyGate preparationGate zeroInput) = _
  rw [preparationGate_zero, run_append]
  rfl

theorem freshReadbackCircuit_run (f : DihedralReg N → S) :
    Run (AddOracle f) (freshReadbackCircuit (N := N) (S := S)) zeroInput =
      dihedralRecordJoint N f := by
  rw [freshReadbackCircuit, run_append, freshRepresentationCircuit_run]
  change (representationRecordGate (N := N) (S := S))ᴴ *ᵥ representationJoint f = _
  exact representationJoint_readback f

omit [Fintype S] [AddCommGroup S] in

theorem freshRepresentationCircuit_queryCount :
    QueryCount (freshRepresentationCircuit (N := N) (S := S)) = 1 := rfl

omit [Fintype S] [AddCommGroup S] in

theorem freshRepresentationCircuit_gateCount :
    GateCount (freshRepresentationCircuit (N := N) (S := S)) = 3 := rfl

omit [Fintype S] [AddCommGroup S] in

theorem freshRepresentationCircuit_size :
    Size (freshRepresentationCircuit (N := N) (S := S)) = 4 := rfl

omit [Fintype S] [AddCommGroup S] in

theorem freshReadbackCircuit_queryCount :
    QueryCount (freshReadbackCircuit (N := N) (S := S)) = 1 := rfl

omit [Fintype S] [AddCommGroup S] in

theorem freshReadbackCircuit_gateCount :
    GateCount (freshReadbackCircuit (N := N) (S := S)) = 4 := rfl

omit [Fintype S] [AddCommGroup S] in

theorem freshReadbackCircuit_size :
    Size (freshReadbackCircuit (N := N) (S := S)) = 5 := rfl

theorem freshRepresentationCircuit_normalized (f : DihedralReg N → S) :
    Normalized (Run (AddOracle f) freshRepresentationCircuit zeroInput) := by
  rw [freshRepresentationCircuit_run]
  exact representationJoint_normalized f

theorem freshReadbackCircuit_normalized (f : DihedralReg N → S) :
    Normalized (Run (AddOracle f) freshReadbackCircuit zeroInput) := by
  rw [freshReadbackCircuit_run]
  exact normalized_dihedralRecordJoint N f

end Fresh
end Preparation

namespace RowTransport

open MatrixBlocks

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

def rowDensity (f : DihedralReg N → S) (k : ZMod N) : Matrix Bool Bool ℂ :=
  ∑ z : S, outerProduct (fun b => representationJoint f ((k,b),z))

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

theorem pair_positive_density (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : PairFreq N) :
    rowDensity f k.1 = ((1/(N : ℝ) : ℝ) : ℂ) • outerProduct (dihedralQubitState N s k.1) := by
  rw [rowDensity_factor f s k.1 hf, basis_positive_state]

theorem pair_negative_density (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : PairFreq N) :
    rowDensity f (-k.1) = ((1/(N : ℝ) : ℝ) : ℂ) • outerProduct (dihedralQubitState N s k.1) := by
  rw [rowDensity_factor f s (-k.1) hf, basis_negative_state, scalar_outer,
    norm_dihedralQubitPhase, one_pow, Complex.ofReal_one, one_smul]

theorem pair_label_mass (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : PairFreq N) :
    (∑ b : Bool, ∑ z : S, ‖representationJoint f ((k.1,b),z)‖^2) +
      (∑ b : Bool, ∑ z : S, ‖representationJoint f ((-k.1,b),z)‖^2) = 2/(N : ℝ) := by
  rw [representation_row_mass f s k.1 hf, representation_row_mass f s (-k.1) hf]
  ring

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

def preparedRecord (f : DihedralReg N → S) : PMF (ZMod N × S × NormQ) :=
  (bornDistribution (Run (AddOracle f) freshReadbackCircuit zeroInput)
    (freshReadbackCircuit_normalized f)).map fun q =>
      (q.1.1, q.2, actualRecordState (fun t =>
        Run (AddOracle f) freshReadbackCircuit zeroInput ((q.1.1,t),q.2)))

theorem preparedRecord_eq (f : DihedralReg N → S) :
    preparedRecord f = dihedralActualRecord N f := by
  unfold preparedRecord
  simp_rw [freshReadbackCircuit_run]
  rfl

theorem freshT_prepared (n : ℕ) (f : DihedralReg (2^n) → S) (r : ℕ) :
    freshT n f (r+1) = (preparedRecord f).bind fun q =>
      (freshT n f r).map fun st =>
        ((q.1,q.2.2)::st.1, chargeFresh st.2) := by
  rw [preparedRecord_eq]
  rfl

def circuitQueries (n : ℕ) (S : Type) [DecidableEq S] (c : Charge) : ℕ :=
  QueryCount (freshReadbackCircuit (N := 2^n) (S := S)) * c.fresh

def circuitGates (n : ℕ) (S : Type) [DecidableEq S] (c : Charge) : ℕ :=
  GateCount (freshReadbackCircuit (N := 2^n) (S := S)) * c.fresh +
    GateCount ([Step.gate CNOT] : Circuit (Bool × Bool)) * c.pairs +
    GateCount ([Step.gate Hadamard] : Circuit Bool) * c.reads

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

theorem fresh_live (n : ℕ) (f : DihedralReg (2^n) → S) (R r : ℕ) (hr : r ≤ R)
    (st : List (Record n) × Charge) (h : st ∈ (freshT n f r).support) :
    st.1.length ≤ R := by
  have ht := (freshT_inv n f r st h).1
  omega

theorem pair_prefix_live (n R : ℕ) (done rest : List (Record n × Record n))
    (hslots : 2*(done++rest).length ≤ R)
    (st : List (Record n) × Charge) (h : st ∈ (layerAuxT n done).support) :
    st.1.length + 2*rest.length ≤ R := by
  have ht := (layerAuxT_inv n done st h).1
  simp only [List.length_append] at hslots
  omega

omit [DecidableEq S] [AddCommGroup S] in

theorem source_workspace_card (n : ℕ) :
    Fintype.card (DihedralReg (2^n) × S) = 2*(2^n)*Fintype.card S := by
  simp only [DihedralReg, Fintype.card_prod, ZMod.card, Fintype.card_bool]
  ac_rfl

end Resources

namespace TypedFourier

open FourierEncoding MatrixBlocks

variable {N : ℕ} [NeZero N]

def coefficient : Typed N → Raw N → ℂ
  | ⟨.inl (k,b), _⟩, (a,t) => selfCoefficient k b a t
  | ⟨.inr k, (i,j)⟩, (a,t) =>
      pairBlock k.1 a t (boolEquivFin2.symm i) (boolEquivFin2.symm j)

def scale : Label N → ℂ
  | .inl _ => (Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹
  | .inr _ => (Real.sqrt (N : ℝ) : ℂ)⁻¹

def typedFourier (j : Typed N) (g : Raw N) : ℂ :=
  representationFourier (encode j) g

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

theorem typedFourier_readback (g h : Raw N) :
    typedFourier (decode g) h = representationFourier g h := by
  rw [typedFourier, encode_decode]

end TypedFourier

namespace Irreps

open MatrixBlocks

abbrev boolFin : Matrix Bool Bool ℂ ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ boolEquivFin2

theorem boolFin_apply (A : Matrix Bool Bool ℂ) (r c : Bool) :
    boolFin A (boolEquivFin2 r) (boolEquivFin2 c) = A r c := by
  change A (boolEquivFin2.symm (boolEquivFin2 r))
    (boolEquivFin2.symm (boolEquivFin2 c)) = A r c
  rw [boolEquivFin2.symm_apply_apply, boolEquivFin2.symm_apply_apply]

theorem boolFin_star (A : Matrix Bool Bool ℂ) : boolFin Aᴴ = (boolFin A)ᴴ := rfl

theorem boolFin_smul (z : ℂ) (A : Matrix Bool Bool ℂ) :
    boolFin (z • A) = z • boolFin A := rfl

theorem boolFin_unitary (A : Matrix Bool Bool ℂ)
    (hA : A ∈ Matrix.unitaryGroup Bool ℂ) :
    boolFin A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hA ⊢
  change boolFin Aᴴ * boolFin A = 1
  rw [← map_mul, hA, map_one]

variable {N : ℕ} [NeZero N]

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

theorem pair_matrix_coefficient (k : FourierEncoding.PairFreq N) (a : ZMod N)
    (t r c : Bool) :
    ((pairIrrep k).rhoX ^ a.val * (pairIrrep k).rhoY ^ (if t then 1 else 0))
      (boolEquivFin2 r) (boolEquivFin2 c) = pairBlock k.1 a t r c := by
  change (boolFin (rotation k.1 1) ^ a.val *
    boolFin PauliX ^ (if t then 1 else 0 : ℕ))
      (boolEquivFin2 r) (boolEquivFin2 c) = _
  rw [← map_pow, ← map_pow, ← map_mul, ← pairBlock_is_generator_word]
  exact boolFin_apply _ r c

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

theorem scalar_intertwiner_zero (x a b : ℂ) (hab : a ≠ b)
    (h : x * b = a * x) : x = 0 := by
  have hz : x * (b - a) = 0 := by
    calc
      _ = x * b - a * x := by ring
      _ = 0 := sub_eq_zero.mpr h
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hab.symm)

theorem diagonal_intertwiner_zero {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (a : I → ℂ) (b : J → ℂ)
    (hsep : ∀ i j, a i ≠ b j) (M : Matrix I J ℂ)
    (h : M * Matrix.diagonal b = Matrix.diagonal a * M) : M = 0 := by
  ext i j
  have he := congrArg (fun A : Matrix I J ℂ => A i j) h
  change (M * Matrix.diagonal b) i j = (Matrix.diagonal a * M) i j at he
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  exact scalar_intertwiner_zero (M i j) (a i) (b j) (hsep i j) he

theorem epsilon_injective : Function.Injective epsilon := by
  intro b c h
  cases b <;> cases c <;> first | rfl | norm_num [epsilon] at h

omit [NeZero N] in

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

def canonicalIrrep : FourierEncoding.Label N → DihedralIrrep N
  | .inl (k, b) => selfIrrep k b
  | .inr k => pairIrrep k

theorem canonicalIrrep_dim (L : FourierEncoding.Label N) :
    (canonicalIrrep L).dim = FourierEncoding.dim L := by
  cases L <;> rfl

theorem canonicalIrrep_dimensionCount :
    (∑ L : FourierEncoding.Label N, (canonicalIrrep L).dim ^ 2) = 2 * N := by
  simpa only [canonicalIrrep_dim] using! (FourierEncoding.dimensionCount (N := N))

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

def canonicalFamily : IrrepFamily N (FourierEncoding.Label N) where
  irrep := canonicalIrrep
  dimensionCount := canonicalIrrep_dimensionCount
  inequivalent := canonicalIrrep_inequivalent

theorem actual_kernel_self (k : FourierEncoding.SelfFreq N) (e : Bool)
    (a : ZMod N) (t : Bool) :
    representationFourier (k.1, e) (a, t) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ *
        ((selfIrrep k e).rhoX ^ a.val * (selfIrrep k e).rhoY ^ (if t then 1 else 0))
          (0 : Fin 1) (0 : Fin 1) := by
  rw [selfCoefficient_is_matrix_coefficient]
  exact kernel_self k a e t

theorem actual_kernel_pair_positive (k : FourierEncoding.PairFreq N)
    (a : ZMod N) (b t : Bool) :
    representationFourier (k.1, b) (a, t) =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
        ((pairIrrep k).rhoX ^ a.val * (pairIrrep k).rhoY ^ (if t then 1 else 0))
          (boolEquivFin2 false) (boolEquivFin2 b) := by
  rw [pair_matrix_coefficient]
  exact kernel_pair_positive k a b t

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

theorem phase_conj (s k : ZMod N) :
    (starRingEnd ℂ) (dihedralQubitPhase N s k) = ZMod.stdAddChar ((-k)*s) := by
  rw [dihedralQubitPhase_eq_stdAddChar, conj_stdAddChar, neg_mul]

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

theorem pair_reflection (k : FourierEncoding.PairFreq N) (s : ZMod N) :
    reflectionElem (pairIrrep k) s = boolFin (PauliX * rotation k.1 s) := by
  change boolFin PauliX * boolFin (rotation k.1 1) ^ s.val = _
  rw [← map_pow, ← map_mul, ← rotation_as_power]

theorem pair_reflection_trace (k : FourierEncoding.PairFreq N) (s : ZMod N) :
    Matrix.trace (reflectionElem (pairIrrep k) s) = 0 := by
  rw [pair_reflection]
  unfold Matrix.trace
  rw [Fin.sum_univ_two]
  change boolFin (PauliX * rotation k.1 s) (boolEquivFin2 false) (boolEquivFin2 false) +
    boolFin (PauliX * rotation k.1 s) (boolEquivFin2 true) (boolEquivFin2 true) = 0
  rw [boolFin_apply, boolFin_apply]
  simp [PauliX, permMatrix, rotation, Matrix.mul_apply]

theorem pair_dimFixed (k : FourierEncoding.PairFreq N) (s : ZMod N) :
    dimFixed (pairIrrep k) s = 1 := by
  have hd := Qatlib.Concepts.HspRecovery.RecordExtract.irrep_dimFixed_eq_trace (pairIrrep k) s
  rw [pair_reflection_trace] at hd
  change (dimFixed (pairIrrep k) s : ℂ) = ((2 : ℂ) + 0) / 2 at hd
  norm_num at hd
  exact_mod_cast hd

theorem self_reflection_trace (k : FourierEncoding.SelfFreq N) (b : Bool) (s : ZMod N) :
    Matrix.trace (reflectionElem (selfIrrep k b) s) =
      epsilon b * dihedralQubitPhase N s k.1 := by
  change Matrix.trace (selfY b * selfX k ^ s.val) = _
  rw [selfY, selfX, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Fin.sum_univ_one]
  change epsilon b * ZMod.stdAddChar k.1 ^ s.val = _
  rw [character_power_val, dihedralQubitPhase_eq_stdAddChar]

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

theorem pair_repLabelMass (k : FourierEncoding.PairFreq N) (s : ZMod N) :
    repLabelMass (pairIrrep k) s = 2 / (N : ℝ) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  change (2 : ℝ) * (dimFixed (pairIrrep k) s : ℝ) * 2 / (2 * (N : ℝ)) = _
  rw [pair_dimFixed]
  push_cast
  field_simp [hN]

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

theorem pair_fixed_projector (k : FourierEncoding.PairFreq N) (s : ZMod N) :
    (2 : ℂ)⁻¹ • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + reflectionElem (pairIrrep k) s) =
      boolFin (outerProduct (dihedralQubitState N s k.1)) := by
  rw [pair_reflection, ProjectorLaw.qubit_density_projector, boolFin_smul, map_add, map_one]

section ActualLabel

variable {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]

theorem actual_pair_label (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : FourierEncoding.PairFreq N) :
    (∑ b : Bool, ∑ z : S, ‖representationJoint f ((k.1,b),z)‖ ^ 2) +
      (∑ b : Bool, ∑ z : S, ‖representationJoint f ((-k.1,b),z)‖ ^ 2) =
      repLabelMass (pairIrrep k) s := by
  rw [pair_repLabelMass]
  exact RowTransport.pair_label_mass f s hf k

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

def labelBornMass (f : DihedralReg N → S) : FourierEncoding.Label N → ℝ
  | .inl (k,b) => ∑ z : S, ‖representationJoint f ((k.1,b),z)‖ ^ 2
  | .inr k =>
      (∑ b : Bool, ∑ z : S, ‖representationJoint f ((k.1,b),z)‖ ^ 2) +
      (∑ b : Bool, ∑ z : S, ‖representationJoint f ((-k.1,b),z)‖ ^ 2)

theorem canonical_label_law (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (L : FourierEncoding.Label N) :
    labelBornMass f L = repLabelMass (canonicalFamily.irrep L) s := by
  cases L with
  | inl kb =>
    rcases kb with ⟨k,b⟩
    exact actual_self_label f s hf k b
  | inr k => exact actual_pair_label f s hf k

theorem actual_positive_fixed_density (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : FourierEncoding.PairFreq N) :
    boolFin (RowTransport.rowDensity f k.1) = ((1 / (N : ℝ) : ℝ) : ℂ) •
      ((2 : ℂ)⁻¹ • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + reflectionElem (pairIrrep k) s)) := by
  rw [RowTransport.pair_positive_density f s hf k, boolFin_smul, ← pair_fixed_projector]

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

def labelEventMass (f : DihedralReg N → S) (L : Label N) : ℝ :=
  ∑ g : Raw N, ∑ z : S, if (decode g).1 = L then ‖representationJoint f (g,z)‖^2 else 0

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

theorem labelEventMass_eq_repLabelMass (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (L : Label N) :
    labelEventMass f L = Qatlib.Concepts.HspRecovery.RecordExtract.repLabelMass
      (Irreps.canonicalFamily.irrep L) s := by
  rw [labelEventMass_eq_born]
  exact FixedSubspace.canonical_label_law f s hf L

end LabelEvent

def FiniteFourierTransport : Prop :=
  ∀ (N : ℕ) [NeZero N],
    representationFourier (N := N) ∈ Matrix.unitaryGroup (DihedralReg N) ℂ ∧
    (∑ L : FourierEncoding.Label N, (Irreps.canonicalFamily.irrep L).dim^2) = 2*N ∧
    (∀ j : FourierEncoding.Typed N, ∀ g : FourierEncoding.Raw N,
      TypedFourier.typedFourier j g = TypedFourier.scale j.1 * TypedFourier.coefficient j g) ∧
    (∀ L : FourierEncoding.Label N,
      ‖TypedFourier.scale L‖^2 = (FourierEncoding.dim L : ℝ)/(2*(N : ℝ)))

theorem finiteFourierTransport : FiniteFourierTransport := by
  intro N _
  exact ⟨representationFourier_unitary, Irreps.canonicalIrrep_dimensionCount,
    TypedFourier.typedFourier_kernel, ProjectorLaw.scale_norm⟩

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

theorem explicitExtractionLaw : ExplicitExtractionLaw := by
  intro N _ s k l
  exact dihedralExtractionLaw N s k l

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

theorem frontier1 :
    FiniteFourierTransport ∧ RepresentationRecordTransport ∧
      ExplicitExtractionLaw ∧ ActualSieveConsumer :=
  ⟨finiteFourierTransport, representationRecordTransport, explicitExtractionLaw, actualSieveConsumer⟩

end Qatlib.Concepts.HspRecovery.OpenSieve
