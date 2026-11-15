/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary
public import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
public import Qatlib.Concepts.UnbiasedBases.ThreeBasis.SolovayKitaevCount
public import Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixAccess.RitzPipeline Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2 Qatlib.Concepts.UnbiasedBases.ThreeBasis.CSD.SolovayKitaev
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.BinaryCompare
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.CountedTake
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StateEcho
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.ValidatorSemantics
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.EmitterCore
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NativeEcho
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Parsing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.WordValidator
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.CopyEvolution.Discriminate Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Concepts.MatrixAccess.RitzPipeline
open QuantumInfo.CliffordT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

noncomputable section

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.MiddleWindowFixedWord

open Matrix
open scoped Matrix.Norms.L2Operator

open Qatlib
open Qatlib
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis

def wire0 : Fin 1 := ⟨0, by omega⟩

def prim1 (i : ℕ) : LocalQFTGate 1 :=
  if i % 7 = 0 then .h wire0
  else if i % 7 = 1 then .cp wire0 wire0 1 true
  else if i % 7 = 2 then .cp wire0 wire0 1 false
  else if i % 7 = 3 then .cp wire0 wire0 2 true
  else if i % 7 = 4 then .cp wire0 wire0 2 false
  else if i % 7 = 5 then .cp wire0 wire0 3 true
  else .cp wire0 wire0 3 false

/-- Every enumerated one-wire primitive is a fixed primitive. -/
theorem prim1_legal (i : ℕ) : IsFixedPrim (prim1 i) := by
  unfold prim1
  split_ifs <;> first | exact True.intro | (simp only [IsFixedPrim]; omega)

/-- Reducing the primitive index modulo seven leaves the enumerated gate unchanged. -/
theorem prim1_mod (i : ℕ) : prim1 (i % 7) = prim1 i := by
  unfold prim1
  rw [Nat.mod_mod_of_dvd i (by omega)]

def wordOfAux : ℕ → ℕ → List (LocalQFTGate 1)
  | 0, _ => []
  | ℓ + 1, n => prim1 (n % 7) :: wordOfAux ℓ (n / 7)

/-- The auxiliary word has length equal to its requested length. -/
theorem wordOfAux_length (ℓ n : ℕ) : (wordOfAux ℓ n).length = ℓ := by
  induction ℓ generalizing n with
  | zero => rfl
  | succ ℓ ih => simp [wordOfAux, ih]

/-- Every gate in an auxiliary word is a fixed primitive. -/
theorem wordOfAux_legal (ℓ n : ℕ) : ∀ g ∈ wordOfAux ℓ n, IsFixedPrim g := by
  induction ℓ generalizing n with
  | zero => simp [wordOfAux]
  | succ ℓ ih =>
      intro g hg
      simp only [wordOfAux, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact prim1_legal _
      · exact ih _ g hg

/-- There are exactly two one-wire registers. -/
theorem card_reg1 : Fintype.card (Reg 1) = 2 := by
  simp [Reg, Fintype.card_pi, Finset.prod_const, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin]

/-- Each term of a finite nonnegative real sum is at most the whole sum. -/
theorem single_le_sum_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (b : ι) : f b ≤ ∑ i, f i := by
  have h : f b + ∑ i ∈ Finset.univ.erase b, f i = ∑ i, f i :=
    Finset.add_sum_erase Finset.univ f (Finset.mem_univ b)
  have hrest : 0 ≤ ∑ i ∈ Finset.univ.erase b, f i :=
    Finset.sum_nonneg fun i _ => hf i
  linarith

/-- The norm of a one-wire state coordinate is at most its Euclidean norm. -/
theorem norm_le_of_reg1 {v : QState (Reg 1)} {x : Reg 1} :
    ‖v x‖ ≤ ‖toEuclidean_fromVec v‖ := by
  have hsq : (‖v x‖ : ℝ) ^ 2 ≤ ‖toEuclidean_fromVec v‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq]
    exact single_le_sum_nonneg (fun z : Reg 1 => (‖v z‖ : ℝ) ^ 2)
      (fun z => sq_nonneg _) x
  have habs : |(‖v x‖ : ℝ)| ≤ |‖toEuclidean_fromVec v‖| :=
    sq_le_sq (a := (‖v x‖ : ℝ)) (b := ‖toEuclidean_fromVec v‖) |>.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at habs

/-- A one-wire matrix with entries bounded in norm by a nonnegative constant has operator norm
at most three times that constant. -/
theorem opNorm_le_of_entry_bound {D : ℝ} (hD : 0 ≤ D) {A : Matrix (Reg 1) (Reg 1) ℂ}
    (h : ∀ y x, ‖A y x‖ ≤ D) : ‖A‖ ≤ 3 * D := by
  have h3 : 0 ≤ 3 * D := by positivity
  refine l2_opNorm_le_of_mulVec_le h3 A (fun v => ?_)
  have hrow : ∀ y : Reg 1, ‖(A *ᵥ v) y‖ ≤ 2 * D * ‖toEuclidean_fromVec v‖ := by
    intro y
    have hdot : (A *ᵥ v) y = ∑ x : Reg 1, A y x * v x := rfl
    rw [hdot]
    calc ‖∑ x : Reg 1, A y x * v x‖ ≤ ∑ x : Reg 1, ‖A y x * v x‖ :=
          norm_sum_le (Finset.univ : Finset (Reg 1)) (fun x : Reg 1 => A y x * v x)
      _ ≤ ∑ x : Reg 1, D * ‖toEuclidean_fromVec v‖ := by
          refine Finset.sum_le_sum fun x _ => ?_
          have hAx := h y x
          have hvx := norm_le_of_reg1 (v := v) (x := x)
          rw [Complex.norm_mul]
          exact mul_le_mul hAx hvx (norm_nonneg (v x)) hD
      _ = 2 * D * ‖toEuclidean_fromVec v‖ := by
          rw [Finset.sum_const, Finset.card_univ, card_reg1, two_smul]
          ring
  have hsq : (‖toEuclidean_fromVec (A *ᵥ v)‖ : ℝ) ^ 2
      ≤ (3 * D) ^ 2 * ‖toEuclidean_fromVec v‖ ^ 2 := by
    have hnormv : ∑ i : Reg 1, ‖v i‖ ^ 2 = ‖toEuclidean_fromVec v‖ ^ 2 :=
      (norm_toEuclidean_fromVec_sq v).symm
    rw [norm_toEuclidean_fromVec_sq, ← hnormv]
    have h1 : ∑ y : Reg 1, ‖(A *ᵥ v) y‖ ^ 2
        ≤ 2 * (2 * D * ‖toEuclidean_fromVec v‖) ^ 2 := by
      have h2 : ∑ y : Reg 1, ‖(A *ᵥ v) y‖ ^ 2
          ≤ ∑ y : Reg 1, (2 * D * ‖toEuclidean_fromVec v‖) ^ 2 :=
        Finset.sum_le_sum fun y _ => by
          have hy := hrow y
          have habs : |(‖(A *ᵥ v) y‖ : ℝ)| ≤ |2 * D * ‖toEuclidean_fromVec v‖| := by
            rw [abs_of_nonneg (norm_nonneg ((A *ᵥ v) y)),
              abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD)
                (norm_nonneg (toEuclidean_fromVec v)))]
            exact hy
          exact sq_le_sq (a := (‖(A *ᵥ v) y‖ : ℝ))
            (b := 2 * D * ‖toEuclidean_fromVec v‖) |>.mpr habs
      rw [Finset.sum_const, Finset.card_univ, card_reg1, two_smul] at h2
      linarith
    nlinarith [sq_nonneg (D * ‖toEuclidean_fromVec v‖)]
  have hfin : ‖toEuclidean_fromVec (A *ᵥ v)‖ ≤ 3 * D * ‖toEuclidean_fromVec v‖ := by
    have h4 : (‖toEuclidean_fromVec (A *ᵥ v)‖ : ℝ) ^ 2
        ≤ (3 * D * ‖toEuclidean_fromVec v‖) ^ 2 := by
      rw [show (3 * D * ‖toEuclidean_fromVec v‖) ^ 2
          = (3 * D) ^ 2 * ‖toEuclidean_fromVec v‖ ^ 2 from by ring]
      exact hsq
    have h5 : |(‖toEuclidean_fromVec (A *ᵥ v)‖ : ℝ)|
        ≤ |3 * D * ‖toEuclidean_fromVec v‖| :=
      sq_le_sq (a := (‖toEuclidean_fromVec (A *ᵥ v)‖ : ℝ))
        (b := 3 * D * ‖toEuclidean_fromVec v‖) |>.mp h4
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h5
  linarith [norm_nonneg (toEuclidean_fromVec (A *ᵥ v))]

def matCoord (M : Matrix (Reg 1) (Reg 1) ℂ) (c : Bool × Bool × Bool) : ℝ :=
  match c with
  | (b, y, x) => if b then (M (fun _ => y) (fun _ => x)).im else (M (fun _ => y) (fun _ => x)).re

/-- Every entry of a one-wire matrix whose conjugate transpose times itself is identity has norm
at most one. -/
theorem unitary_entry_le_one {U : Matrix (Reg 1) (Reg 1) ℂ} (hU : Uᴴ * U = 1) (y x : Reg 1) :
    ‖U y x‖ ≤ 1 := by
  have hdiag : ∑ z : Reg 1, (Uᴴ) x z * U z x = 1 := by
    have h1 : (Uᴴ * U) x x = ∑ z : Reg 1, (Uᴴ) x z * U z x := rfl
    rw [hU, Matrix.one_apply, ite_eq_left rfl] at h1
    exact h1.symm
  have hsum : ∑ z : Reg 1, Complex.normSq (U z x) = 1 := by
    have hcast : ∑ z : Reg 1, ((Complex.normSq (U z x) : ℝ) : ℂ) = 1 := by
      refine Eq.trans (Finset.sum_congr rfl fun z _ => ?_) hdiag
      rw [Matrix.conjTranspose_apply]
      exact Complex.normSq_eq_conj_mul_self
    have hcast2 : ((∑ z : Reg 1, Complex.normSq (U z x) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      exact hcast
    exact Complex.ofReal_inj.mp hcast2
  have hsingle : Complex.normSq (U y x) ≤ 1 := by
    rw [← hsum]
    exact single_le_sum_nonneg (fun z : Reg 1 => Complex.normSq (U z x))
      (fun z => Complex.normSq_nonneg (U z x)) y
  have hnorm : (‖U y x‖ : ℝ) ^ 2 = Complex.normSq (U y x) :=
    (Complex.normSq_eq_norm_sq (U y x)).symm
  have hnn : 0 ≤ ‖U y x‖ := norm_nonneg _
  nlinarith [hnn]

/-- Every real matrix coordinate has absolute value at most one when all complex entries have
norm at most one. -/
theorem matCoord_abs_le_one {M : Matrix (Reg 1) (Reg 1) ℂ} (hM : ∀ y x, ‖M y x‖ ≤ 1)
    (c : Bool × Bool × Bool) : |matCoord M c| ≤ 1 := by
  obtain ⟨b, y, x⟩ := c
  have hentry := hM (fun _ => y) (fun _ => x)
  cases b
  · simp only [matCoord]
    exact le_trans (Complex.abs_re_le_norm _) hentry
  · simp only [matCoord]
    exact le_trans (Complex.abs_im_le_norm _) hentry

noncomputable def coordFloor (x : ℝ) (k : ℕ) : ℕ := Nat.floor ((x + 1) * 16 * 2 ^ k)

/-- For coordinates of absolute value at most one, the coordinate floor index at precision `k`
is less than two raised to the sum of `k` and six. -/
theorem coordFloor_lt (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) : coordFloor x k < 2 ^ (k + 6) := by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hx2 : x + 1 ≤ 2 := by linarith [abs_le.mp hx]
  have hbound : (x + 1) * 16 * 2 ^ k < ((2 ^ (k + 6) : ℕ) : ℝ) := by
    have h3 : ((2 ^ (k + 6) : ℕ) : ℝ) = 64 * 2 ^ k := by
      rw [Nat.cast_pow, show ((2 : ℕ) : ℝ) = 2 from rfl]
      rw [show (2 : ℝ) ^ (k + 6) = ((2 : ℝ) ^ 6) * ((2 : ℝ) ^ k) from by
          rw [← pow_add, Nat.add_comm]]
      norm_num
    have hmul : (x + 1) * 2 ^ k ≤ 2 * 2 ^ k :=
      mul_le_mul_of_nonneg_right hx2 hpos.le
    rw [h3]
    nlinarith [hpos, hmul]
  have hnn : 0 ≤ (x + 1) * 16 * 2 ^ k := by
    have hx1 : 0 ≤ x + 1 := by linarith [abs_le.mp hx]
    exact mul_nonneg (mul_nonneg hx1 (show (0 : ℝ) ≤ 16 by norm_num)) hpos.le
  exact Nat.floor_lt hnn |>.mpr hbound

/-- Equal coordinate floor indices force two coordinates in the unit interval in absolute value
to differ by less than the stated grid spacing. -/
theorem coordFloor_eq_lt (k : ℕ) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (h : coordFloor x k = coordFloor y k) :
    |x - y| < 1 / (16 * 2 ^ k) := by
  have hpos : (0 : ℝ) < 16 * 2 ^ k := by positivity
  have hnnx : 0 ≤ (x + 1) * 16 * 2 ^ k := by
    have : 0 ≤ x + 1 := by linarith [abs_le.mp hx]
    positivity
  have hnny : 0 ≤ (y + 1) * 16 * 2 ^ k := by
    have : 0 ≤ y + 1 := by linarith [abs_le.mp hy]
    positivity
  have hx1 : (coordFloor x k : ℝ) ≤ (x + 1) * 16 * 2 ^ k := Nat.floor_le hnnx
  have hx2 : (x + 1) * 16 * 2 ^ k < (coordFloor x k : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((x + 1) * 16 * 2 ^ k)
    simpa using! this
  have hy1 : (coordFloor y k : ℝ) ≤ (y + 1) * 16 * 2 ^ k := Nat.floor_le hnny
  have hy2 : (y + 1) * 16 * 2 ^ k < (coordFloor y k : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((y + 1) * 16 * 2 ^ k)
    simpa using! this
  rw [h] at hx1 hx2
  have habslt : |(x + 1) * 16 * 2 ^ k - (y + 1) * 16 * 2 ^ k| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have heq : (x + 1) * 16 * 2 ^ k - (y + 1) * 16 * 2 ^ k = (x - y) * (16 * 2 ^ k) := by
    ring
  rw [heq, abs_mul, abs_of_pos hpos] at habslt
  field_simp
  linarith

noncomputable def boxOf (M : Matrix (Reg 1) (Reg 1) ℂ) (k : ℕ) (hM : ∀ y x, ‖M y x‖ ≤ 1) :
    (Bool × Bool × Bool) → Fin (2 ^ (k + 6)) :=
  fun c => ⟨coordFloor (matCoord M c) k, coordFloor_lt k (matCoord_abs_le_one hM c)⟩

/-- The norm of a complex number is at most the sum of the absolute values of its real and
imaginary parts. -/
theorem abs_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |Complex.re z| + |Complex.im z| := by
  have h1 : (‖z‖ : ℝ) ^ 2 = Complex.re z * Complex.re z + Complex.im z * Complex.im z := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have h2 : 0 ≤ |Complex.re z| + |Complex.im z| := by positivity
  have h3 : (|Complex.re z| + |Complex.im z|) ^ 2
      = Complex.re z * Complex.re z + Complex.im z * Complex.im z
        + 2 * |Complex.re z| * |Complex.im z| := by
    have hexpand : (|Complex.re z| + |Complex.im z|) ^ 2
        = |Complex.re z| * |Complex.re z| + 2 * |Complex.re z| * |Complex.im z|
          + |Complex.im z| * |Complex.im z| := by ring
    have habs1 : |Complex.re z| * |Complex.re z| = Complex.re z * Complex.re z :=
      abs_mul_abs_self _
    have habs2 : |Complex.im z| * |Complex.im z| = Complex.im z * Complex.im z :=
      abs_mul_abs_self _
    rw [hexpand, habs1, habs2]
    ring
  have h4 : (‖z‖ : ℝ) ^ 2 ≤ (|Complex.re z| + |Complex.im z|) ^ 2 := by
    rw [h1, h3]
    nlinarith [abs_nonneg (Complex.re z), abs_nonneg (Complex.im z)]
  have h6 := sq_le_sq.mp h4
  rwa [abs_of_nonneg (norm_nonneg z), abs_of_nonneg h2] at h6

/-- One-wire matrices in the same coordinate box differ entrywise by at most twice the grid
spacing. -/
theorem boxOf_eq_entry (k : ℕ) (U V : Matrix (Reg 1) (Reg 1) ℂ)
    (hU : ∀ y x, ‖U y x‖ ≤ 1) (hV : ∀ y x, ‖V y x‖ ≤ 1)
    (h : boxOf U k hU = boxOf V k hV) (y x : Reg 1) :
    ‖U y x - V y x‖ ≤ 2 / (16 * 2 ^ k) := by
  have hfun : ∀ c : Bool × Bool × Bool,
      coordFloor (matCoord U c) k = coordFloor (matCoord V c) k := by
    intro c
    have hc := congrFun h c
    simpa [boxOf] using! hc
  have hcoord : ∀ b : Bool, ∀ yb xb : Bool,
      |matCoord U (b, yb, xb) - matCoord V (b, yb, xb)| < 1 / (16 * 2 ^ k) := by
    intro b yb xb
    refine coordFloor_eq_lt k (matCoord_abs_le_one hU (b, yb, xb))
      (matCoord_abs_le_one hV (b, yb, xb)) (hfun (b, yb, xb))
  have hkey : ∀ yb xb : Bool,
      ‖U (fun _ => yb) (fun _ => xb) - V (fun _ => yb) (fun _ => xb)‖
        ≤ 2 / (16 * 2 ^ k) := by
    intro yb xb
    have hdelta : ‖U (fun _ => yb) (fun _ => xb) - V (fun _ => yb) (fun _ => xb)‖
        ≤ |matCoord U (false, yb, xb) - matCoord V (false, yb, xb)|
          + |matCoord U (true, yb, xb) - matCoord V (true, yb, xb)| := by
      have hle := abs_le_abs_re_add_abs_im (U (fun _ => yb) (fun _ => xb)
        - V (fun _ => yb) (fun _ => xb))
      simp only [matCoord, Complex.sub_re, Complex.sub_im] at hle ⊢
      exact hle
    have hlt : |matCoord U (false, yb, xb) - matCoord V (false, yb, xb)|
        + |matCoord U (true, yb, xb) - matCoord V (true, yb, xb)|
        < 2 / (16 * 2 ^ k) := by
      rw [show (2 : ℝ) / (16 * 2 ^ k) = 1 / (16 * 2 ^ k) + 1 / (16 * 2 ^ k) from by
          field_simp
          norm_num]
      exact add_lt_add (hcoord false yb xb) (hcoord true yb xb)
    exact le_of_lt (lt_of_le_of_lt hdelta hlt)
  rcases reg1_cases y with hy | hy <;> rcases reg1_cases x with hx | hx <;>
    simp only [hy, hx] <;> exact hkey _ _

/-- The conjugate transpose of a one-wire word's matrix multiplied by that matrix is identity. -/
theorem word_matrix_conj_mul_self (gs : List (LocalQFTGate 1)) :
    (localProgramMatrix gs)ᴴ * localProgramMatrix gs = 1 := by
  have hu := word_matrix_unitary gs
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  exact hu

/-- A one-wire word's matrix multiplied by its conjugate transpose is identity. -/
theorem word_matrix_mul_conj_self (gs : List (LocalQFTGate 1)) :
    localProgramMatrix gs * (localProgramMatrix gs)ᴴ = 1 := by
  have hu := word_matrix_unitary gs
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu
  exact hu

/-- Every entry of a one-wire word's program matrix has norm at most one. -/
theorem word_matrix_entry_le_one (gs : List (LocalQFTGate 1)) (y x : Reg 1) :
    ‖localProgramMatrix gs y x‖ ≤ 1 :=
  unitary_entry_le_one (word_matrix_conj_mul_self gs) y x

/-- Every one-wire word's program matrix has norm one. -/
theorem word_matrix_norm_eq_one (gs : List (LocalQFTGate 1)) :
    ‖localProgramMatrix gs‖ = 1 :=
  l2_norm_unitary_eq_one (word_matrix_unitary gs)

/-- The conjugate transpose of a one-wire word's program matrix has norm one. -/
theorem word_matrix_conjTranspose_norm (gs : List (LocalQFTGate 1)) :
    ‖(localProgramMatrix gs)ᴴ‖ = 1 := by
  rw [Matrix.l2_opNorm_conjTranspose, word_matrix_norm_eq_one]

/-- The conjugate transpose of a one-wire word's program matrix satisfies both unitary
identities. -/
theorem word_matrix_star_unitary (gs : List (LocalQFTGate 1)) :
    ((localProgramMatrix gs)ᴴ)ᴴ * (localProgramMatrix gs)ᴴ = 1 ∧
      (localProgramMatrix gs)ᴴ * ((localProgramMatrix gs)ᴴ)ᴴ = 1 := by
  rw [Matrix.conjTranspose_conjTranspose]
  exact ⟨word_matrix_mul_conj_self gs, word_matrix_conj_mul_self gs⟩

/-- A one-wire word's program matrix and its conjugate transpose have the same norm distance
from identity. -/
theorem word_matrix_star_dist (gs : List (LocalQFTGate 1)) :
    ‖(localProgramMatrix gs)ᴴ - 1‖ = ‖localProgramMatrix gs - 1‖ := by
  have h : (localProgramMatrix gs)ᴴ - 1 = (localProgramMatrix gs - 1)ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  rw [h, Matrix.l2_opNorm_conjTranspose]

/-- Twice the grid spacing is the inverse of two raised to the sum of `k` and three. -/
theorem half_pow_split (k : ℕ) : 2 / (16 * 2 ^ k) = ((2 : ℝ) ⁻¹) ^ (k + 3) := by
  have hdenom : (0 : ℝ) < 16 * 2 ^ k := by positivity
  have hd : (16 * 2 ^ k : ℝ) ≠ 0 := hdenom.ne'
  have hkey : ((2 : ℝ) ⁻¹) ^ (k + 3) * (16 * 2 ^ k) = 2 := by
    have hpair : (((2 : ℝ) ⁻¹) ^ k) * ((2 : ℝ) ^ k) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
    rw [pow_add, show ((2 : ℝ) ⁻¹) ^ 3 = 1 / 8 from by norm_num,
      show (16 : ℝ) = 2 * 8 from by norm_num]
    nlinarith [hpair]
  show (2 : ℝ) * (16 * 2 ^ k)⁻¹ = ((2 : ℝ) ⁻¹) ^ (k + 3)
  exact mul_right_cancel₀ hd (by
    show (2 : ℝ) * (16 * 2 ^ k)⁻¹ * (16 * 2 ^ k)
      = ((2 : ℝ) ⁻¹) ^ (k + 3) * (16 * 2 ^ k)
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
    exact hkey.symm)

/-- Three times the inverse of two raised to the sum of `k` and three is at most the inverse of
two raised to `k`. -/
theorem three_le_half (k : ℕ) : 3 * (((2 : ℝ) ⁻¹) ^ (k + 3)) ≤ ((2 : ℝ) ⁻¹) ^ k := by
  have hpos : (0 : ℝ) < ((2 : ℝ) ⁻¹) ^ k := by positivity
  have hpair : (((2 : ℝ) ⁻¹) ^ k) * (((2 : ℝ) ⁻¹) ^ 3) = ((2 : ℝ) ⁻¹) ^ (k + 3) :=
    (pow_add ((2 : ℝ) ⁻¹) k 3).symm
  rw [show ((2 : ℝ) ⁻¹) ^ 3 = ((1 : ℝ) / 8) from by norm_num] at hpair
  rw [← hpair]
  linarith [hpos]

/-- A map between finite types with smaller codomain has two distinct inputs with equal images. -/
theorem exists_ne_map_eq_of_card_lt {ι β : Type*} [Fintype ι] [DecidableEq β]
    [Fintype β] (f : ι → β) (h : Fintype.card β < Fintype.card ι) :
    ∃ x ∈ (Finset.univ : Finset ι), ∃ y ∈ (Finset.univ : Finset ι), x ≠ y ∧ f x = f y := by
  have h1 : ((Finset.univ : Finset ι).image f).card ≤ Fintype.card β := by
    refine le_trans (Finset.card_le_card (Finset.subset_univ
      ((Finset.univ : Finset ι).image f))) ?_
    rw [Finset.card_univ]
  have hc : ((Finset.univ : Finset ι).image f).card < (Finset.univ : Finset ι).card := by
    rw [Finset.card_univ]
    exact lt_of_le_of_lt h1 h
  exact Finset.exists_ne_map_eq_of_card_image_lt hc

/-- There exists a fixed primitive word of length at most sixteen times `k` plus ninety-eight
whose matrix is within the requested tolerance of identity. -/
theorem pigeonhole_nearIdentity (k : ℕ) :
    ∃ W : List (LocalQFTGate 1), (∀ g ∈ W, IsFixedPrim g) ∧ W.length ≤ 16 * k + 98 ∧
      ‖localProgramMatrix W - 1‖ ≤ tolerance k := by
  have hcard_box : Fintype.card ((Bool × Bool × Bool) → Fin (2 ^ (k + 6)))
      = 2 ^ (8 * k + 48) := by
    have h1 : Fintype.card ((Bool × Bool × Bool) → Fin (2 ^ (k + 6)))
        = (2 ^ (k + 6)) ^ (2 * 2 * 2) := by
      simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_bool, Fintype.card_fin]
    rw [h1, show 2 * 2 * 2 = 8 from rfl, ← pow_mul]
    congr 1
    omega
  have hlt : (2 ^ (8 * k + 48) : ℕ) < 7 ^ (8 * k + 49) := by
    have h1 : (2 : ℕ) ^ (8 * k + 48) < 2 ^ (8 * k + 49) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h2 : (2 : ℕ) ^ (8 * k + 49) ≤ 7 ^ (8 * k + 49) :=
      Nat.pow_le_pow_left (by norm_num) (8 * k + 49)
    exact lt_of_lt_of_le h1 h2
  have hpigeon := exists_ne_map_eq_of_card_lt
    (fun i : Fin (7 ^ (8 * k + 49)) =>
      boxOf (localProgramMatrix (wordOfAux (8 * k + 49) i.val)) k
        (word_matrix_entry_le_one (wordOfAux (8 * k + 49) i.val)))
    (β := (Bool × Bool × Bool) → Fin (2 ^ (k + 6)))
    (by rw [hcard_box, Fintype.card_fin]; exact hlt)
  obtain ⟨i, -, j, -, hne, hbox⟩ := hpigeon
  have hUV : boxOf (localProgramMatrix (wordOfAux (8 * k + 49) i.val)) k
        (word_matrix_entry_le_one (wordOfAux (8 * k + 49) i.val))
      = boxOf (localProgramMatrix (wordOfAux (8 * k + 49) j.val)) k
        (word_matrix_entry_le_one (wordOfAux (8 * k + 49) j.val)) := hbox
  have hdist : ‖localProgramMatrix (wordOfAux (8 * k + 49) i.val)
        - localProgramMatrix (wordOfAux (8 * k + 49) j.val)‖ ≤ tolerance k := by
    have hentry2 : ∀ y x, ‖(localProgramMatrix (wordOfAux (8 * k + 49) i.val)
          - localProgramMatrix (wordOfAux (8 * k + 49) j.val)) y x‖ ≤ 2 / (16 * 2 ^ k) := by
      intro y x
      have hsub : ((localProgramMatrix (wordOfAux (8 * k + 49) i.val)
            - localProgramMatrix (wordOfAux (8 * k + 49) j.val)) y x)
          = localProgramMatrix (wordOfAux (8 * k + 49) i.val) y x
            - localProgramMatrix (wordOfAux (8 * k + 49) j.val) y x := rfl
      rw [hsub]
      exact boxOf_eq_entry k _ _ (word_matrix_entry_le_one (wordOfAux (8 * k + 49) i.val))
        (word_matrix_entry_le_one (wordOfAux (8 * k + 49) j.val)) hUV y x
    have hle := opNorm_le_of_entry_bound (by positivity) hentry2
    rw [half_pow_split] at hle
    exact le_trans hle (three_le_half k)
  refine ⟨localProgramAdjoint (wordOfAux (8 * k + 49) j.val)
    ++ wordOfAux (8 * k + 49) i.val, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg | hg
    · exact localProgramAdjoint_legal _ (wordOfAux_legal (8 * k + 49) j.val) g hg
    · exact wordOfAux_legal (8 * k + 49) i.val g hg
  · simp only [List.length_append, localProgramAdjoint_length, wordOfAux_length]
    omega
  · have hword : localProgramMatrix (localProgramAdjoint (wordOfAux (8 * k + 49) j.val)
        ++ wordOfAux (8 * k + 49) i.val)
        = localProgramMatrix (wordOfAux (8 * k + 49) i.val)
          * ((localProgramMatrix (wordOfAux (8 * k + 49) j.val)))ᴴ := by
      rw [localProgramMatrix_append, localProgramAdjoint_matrix]
    rw [hword]
    have hVV := word_matrix_mul_conj_self (wordOfAux (8 * k + 49) j.val)
    have hsplit : localProgramMatrix (wordOfAux (8 * k + 49) i.val)
          * ((localProgramMatrix (wordOfAux (8 * k + 49) j.val)))ᴴ - 1
        = (localProgramMatrix (wordOfAux (8 * k + 49) i.val)
            - localProgramMatrix (wordOfAux (8 * k + 49) j.val))
          * ((localProgramMatrix (wordOfAux (8 * k + 49) j.val)))ᴴ := by
      rw [Matrix.sub_mul, hVV]
    rw [hsplit]
    have hnorm1 := word_matrix_conjTranspose_norm (wordOfAux (8 * k + 49) j.val)
    calc ‖(localProgramMatrix (wordOfAux (8 * k + 49) i.val)
          - localProgramMatrix (wordOfAux (8 * k + 49) j.val))
          * ((localProgramMatrix (wordOfAux (8 * k + 49) j.val)))ᴴ‖
        ≤ ‖localProgramMatrix (wordOfAux (8 * k + 49) i.val)
          - localProgramMatrix (wordOfAux (8 * k + 49) j.val)‖
          * ‖((localProgramMatrix (wordOfAux (8 * k + 49) j.val)))ᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ tolerance k * ‖((localProgramMatrix (wordOfAux (8 * k + 49) j.val)))ᴴ‖ :=
          mul_le_mul_of_nonneg_right hdist (norm_nonneg _)
      _ = tolerance k := by rw [hnorm1, mul_one]

/-- Sandwiching a one-wire matrix between two unitary matrices does not increase its norm. -/
theorem unitary_sandwich_norm (V W X : Matrix (Reg 1) (Reg 1) ℂ)
    (hV : Vᴴ * V = 1 ∧ V * Vᴴ = 1) (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) :
    ‖V * X * W‖ ≤ ‖X‖ := by
  have hnormV : ‖V‖ = 1 := by
    refine l2_norm_unitary_eq_one ?_
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact hV.2
  have hnormW : ‖W‖ = 1 := by
    refine l2_norm_unitary_eq_one ?_
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact hW.2
  calc ‖V * X * W‖ ≤ ‖V * X‖ * ‖W‖ := Matrix.l2_opNorm_mul (V * X) W
    _ ≤ (‖V‖ * ‖X‖) * ‖W‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul V X) (norm_nonneg W)
    _ = ‖X‖ := by rw [hnormV, hnormW, mul_one, one_mul]

/-- Bounds the distance of a unitary commutator from identity by twice the product of the
factors' distances from identity. -/
theorem commutator_dist_le (V W : Matrix (Reg 1) (Reg 1) ℂ)
    (hV : Vᴴ * V = 1 ∧ V * Vᴴ = 1) (hW : Wᴴ * W = 1 ∧ W * Wᴴ = 1) :
    ‖V * W * Vᴴ * Wᴴ - 1‖ ≤ 2 * ‖V - 1‖ * ‖W - 1‖ := by
  have hkey : V * W * Vᴴ * Wᴴ - 1
      = V * ((W - 1) * (Vᴴ - 1) - (Vᴴ - 1) * (W - 1)) * Wᴴ := by
    have hinner : (W - 1) * (Vᴴ - 1) - (Vᴴ - 1) * (W - 1) = W * Vᴴ - Vᴴ * W := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
      abel
    rw [hinner, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc,
      show V * (Vᴴ * W) * Wᴴ = 1 from by
        rw [← Matrix.mul_assoc, hV.2, Matrix.one_mul, hW.2]]
  have hWstar : ((Wᴴ)ᴴ * Wᴴ = 1 ∧ Wᴴ * (Wᴴ)ᴴ = 1) := by
    constructor
    · rw [Matrix.conjTranspose_conjTranspose]; exact hW.2
    · rw [Matrix.conjTranspose_conjTranspose]; exact hW.1
  rw [hkey]
  calc ‖V * ((W - 1) * (Vᴴ - 1) - (Vᴴ - 1) * (W - 1)) * Wᴴ‖
      ≤ ‖(W - 1) * (Vᴴ - 1) - (Vᴴ - 1) * (W - 1)‖ :=
        unitary_sandwich_norm V Wᴴ _ hV hWstar
    _ ≤ ‖(W - 1) * (Vᴴ - 1)‖ + ‖(Vᴴ - 1) * (W - 1)‖ :=
        norm_sub_le ((W - 1) * (Vᴴ - 1)) ((Vᴴ - 1) * (W - 1))
    _ ≤ ‖W - 1‖ * ‖Vᴴ - 1‖ + ‖Vᴴ - 1‖ * ‖W - 1‖ := by
        exact add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ = 2 * ‖V - 1‖ * ‖W - 1‖ := by
        have hct : (V - 1)ᴴ = Vᴴ - 1 := by
          rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
        rw [← hct, Matrix.l2_opNorm_conjTranspose]
        ring

/-- Bounds a commutator word's distance from identity by twice the product of its input words'
distances from identity. -/
theorem commWord_dist_le (V W : List (LocalQFTGate 1)) :
    ‖localProgramMatrix (commWord V W) - 1‖
      ≤ 2 * ‖localProgramMatrix V - 1‖ * ‖localProgramMatrix W - 1‖ := by
  have h2 : ‖(localProgramMatrix W)ᴴ * (localProgramMatrix V)ᴴ
        * ((localProgramMatrix W)ᴴ)ᴴ * ((localProgramMatrix V)ᴴ)ᴴ - 1‖
      ≤ 2 * ‖(localProgramMatrix W)ᴴ - 1‖ * ‖(localProgramMatrix V)ᴴ - 1‖ :=
    commutator_dist_le _ _ (word_matrix_star_unitary W) (word_matrix_star_unitary V)
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose] at h2
  rw [commWord_matrix]
  calc ‖(localProgramMatrix W)ᴴ * (localProgramMatrix V)ᴴ * localProgramMatrix W
        * localProgramMatrix V - 1‖
      ≤ 2 * ‖(localProgramMatrix W)ᴴ - 1‖ * ‖(localProgramMatrix V)ᴴ - 1‖ := h2
    _ = 2 * ‖localProgramMatrix V - 1‖ * ‖localProgramMatrix W - 1‖ := by
        rw [word_matrix_star_dist, word_matrix_star_dist]
        ring

/-- A controlled phase with both selected wires equal is the corresponding one-wire phase
matrix. -/
theorem localGateMatrix_cp_self {n : ℕ} (a : Fin n) (e : ℕ) (neg : Bool) :
    localGateMatrix (.cp a a e neg) = oneWirePhaseMatrix a (dyadicPhaseAngle e neg) := by
  ext x y
  simp only [localGateMatrix_cp, oneWirePhaseMatrix, Matrix.diagonal_apply, Bool.and_self]

/-- The empty one-wire word approximates a scalar dyadic phase when its exponent is at least the
precision plus two. -/
theorem emptyWord_far_scalar (e k : ℕ) (neg : Bool) (hfar : k + 2 ≤ e) :
    approxUpToPhase (localProgramMatrix ([] : List (LocalQFTGate 1)))
      (oneWirePhaseMatrix wire0 (dyadicPhaseAngle e neg)) (tolerance k) := by
  have h := emptyWord_approx_cp (wire0 : Fin 1) wire0 e neg k hfar
  simp only [cleanEmbed_self, localProgramMatrix_nil, Matrix.one_mul, Matrix.mul_one,
    localGateMatrix_cp_self] at h
  exact h

/-- Taking adjoints of both a word and its target preserves the approximation error norm. -/
theorem adjointWord_dist (V : List (LocalQFTGate 1)) (U : Matrix (Reg 1) (Reg 1) ℂ) :
    ‖localProgramMatrix (localProgramAdjoint V) - Uᴴ‖ = ‖localProgramMatrix V - U‖ := by
  rw [localProgramAdjoint_matrix, ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]

/-- A one-wire matrix satisfying both unitary identities has norm one. -/
theorem unitary_norm_eq_one {U : Matrix (Reg 1) (Reg 1) ℂ}
    (hU : Uᴴ * U = 1 ∧ U * Uᴴ = 1) : ‖U‖ = 1 := by
  refine l2_norm_unitary_eq_one ?_
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  exact hU.2

/-- The conjugate transpose of a one-wire unitary matrix has norm one. -/
theorem unitary_conjTranspose_norm {U : Matrix (Reg 1) (Reg 1) ℂ}
    (hU : Uᴴ * U = 1 ∧ U * Uᴴ = 1) : ‖Uᴴ‖ = 1 := by
  rw [Matrix.l2_opNorm_conjTranspose, unitary_norm_eq_one hU]

/-- The conjugate transpose of a one-wire unitary matrix satisfies both unitary identities. -/
theorem unitary_star_unitary {U : Matrix (Reg 1) (Reg 1) ℂ}
    (hU : Uᴴ * U = 1 ∧ U * Uᴴ = 1) : (Uᴴ)ᴴ * Uᴴ = 1 ∧ Uᴴ * (Uᴴ)ᴴ = 1 := by
  rw [Matrix.conjTranspose_conjTranspose]
  exact ⟨hU.2, hU.1⟩

/-- Conjugate transpose preserves a one-wire matrix's norm distance from identity. -/
theorem norm_sub_one_conjTranspose (A : Matrix (Reg 1) (Reg 1) ℂ) :
    ‖Aᴴ - 1‖ = ‖A - 1‖ := by
  have h : Aᴴ - 1 = (A - 1)ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  rw [h, Matrix.l2_opNorm_conjTranspose]

/-- Left multiplication by a matrix of norm at most one does not increase the norm. -/
theorem prefix_norm_le {P D : Matrix (Reg 1) (Reg 1) ℂ} (hP : ‖P‖ ≤ 1) :
    ‖P * D‖ ≤ ‖D‖ := by
  have hpx : ‖P‖ * ‖D‖ ≤ ‖D‖ := by
    rw [mul_comm]
    simpa [mul_one] using! mul_le_mul_of_nonneg_left hP (norm_nonneg D)
  calc ‖P * D‖ ≤ ‖P‖ * ‖D‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖D‖ := hpx

/-- Right multiplication by a matrix of norm at most one does not increase the norm. -/
theorem suffix_norm_le {D P : Matrix (Reg 1) (Reg 1) ℂ} (hP : ‖P‖ ≤ 1) :
    ‖D * P‖ ≤ ‖D‖ := by
  have hdp : ‖D‖ * ‖P‖ ≤ ‖D‖ := by
    simpa [mul_one] using! mul_le_mul_of_nonneg_left hP (norm_nonneg D)
  calc ‖D * P‖ ≤ ‖D‖ * ‖P‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖D‖ := hdp

/-- Sandwiching a matrix between two contractions does not increase its norm. -/
theorem sandwich_norm_le {P X Q : Matrix (Reg 1) (Reg 1) ℂ} (hP : ‖P‖ ≤ 1)
    (hQ : ‖Q‖ ≤ 1) : ‖P * X * Q‖ ≤ ‖X‖ := by
  have hqx : ‖X‖ * ‖Q‖ ≤ ‖X‖ := by
    simpa [mul_one] using! mul_le_mul_of_nonneg_left hQ (norm_nonneg X)
  have hpx : ‖P‖ * ‖X‖ ≤ ‖X‖ := by
    rw [mul_comm]
    simpa [mul_one] using! mul_le_mul_of_nonneg_left hP (norm_nonneg X)
  have hkey : (‖P‖ * ‖X‖) * ‖Q‖ ≤ ‖X‖ := by
    calc (‖P‖ * ‖X‖) * ‖Q‖ = ‖P‖ * (‖X‖ * ‖Q‖) := by ring
      _ ≤ ‖P‖ * ‖X‖ := mul_le_mul_of_nonneg_left hqx (norm_nonneg P)
      _ ≤ ‖X‖ := hpx
  calc ‖P * X * Q‖ ≤ ‖P * X‖ * ‖Q‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖P‖ * ‖X‖) * ‖Q‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul P X) (norm_nonneg Q)
    _ ≤ ‖X‖ := hkey

/-- The product of two one-wire contractions has norm at most one. -/
theorem norm_prod2_le_one {P Q : Matrix (Reg 1) (Reg 1) ℂ}
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) : ‖P * Q‖ ≤ 1 := by
  have hstep1 : ‖P * Q‖ ≤ ‖P‖ * ‖Q‖ := Matrix.l2_opNorm_mul P Q
  have hstep2 : ‖P‖ * ‖Q‖ ≤ 1 * 1 :=
    mul_le_mul hP hQ (norm_nonneg Q) (by norm_num)
  exact le_trans hstep1 (by simpa [mul_one] using! hstep2)

/-- The product of three one-wire contractions has norm at most one. -/
theorem norm_prod3_le_one {P Q R : Matrix (Reg 1) (Reg 1) ℂ}
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hR : ‖R‖ ≤ 1) : ‖P * Q * R‖ ≤ 1 := by
  have hstep1 : ‖P * Q * R‖ ≤ ‖P * Q‖ * ‖R‖ := Matrix.l2_opNorm_mul (P * Q) R
  have hstep2 : ‖P * Q‖ ≤ 1 := norm_prod2_le_one hP hQ
  have hstep3 : ‖P * Q‖ * ‖R‖ ≤ 1 * 1 :=
    mul_le_mul hstep2 hR (norm_nonneg R) (by norm_num)
  exact le_trans hstep1 (by simpa [mul_one] using! hstep3)

/-- Replacing the final factor of the approximate commutator by `V₀` incurs at most the given
approximation error for `aV`. -/
theorem step01 (aW aV V₀ : Matrix (Reg 1) (Reg 1) ℂ)
    (haW : aWᴴ * aW = 1 ∧ aW * aWᴴ = 1) (haV : aVᴴ * aV = 1 ∧ aV * aVᴴ = 1)
    (εv : ℝ) (hv : ‖aV - V₀‖ ≤ εv) :
    ‖aWᴴ * aVᴴ * aW * aV - aWᴴ * aVᴴ * aW * V₀‖ ≤ εv := by
  have hpre3 : ‖aWᴴ * aVᴴ * aW‖ ≤ 1 :=
    norm_prod3_le_one (le_of_eq (unitary_conjTranspose_norm haW))
      (le_of_eq (unitary_conjTranspose_norm haV)) (le_of_eq (unitary_norm_eq_one haW))
  have hsplit : aWᴴ * aVᴴ * aW * aV - aWᴴ * aVᴴ * aW * V₀
      = (aWᴴ * aVᴴ * aW) * (aV - V₀) := (Matrix.mul_sub _ _ _).symm
  rw [hsplit]
  exact le_trans (prefix_norm_le hpre3) hv

/-- Replacing the third factor of the approximate commutator by `W₀` incurs at most the given
approximation error for `aW`. -/
theorem step12 (aW aV W₀ V₀ : Matrix (Reg 1) (Reg 1) ℂ)
    (haW : aWᴴ * aW = 1 ∧ aW * aWᴴ = 1) (haV : aVᴴ * aV = 1 ∧ aV * aVᴴ = 1)
    (hV₀ : V₀ᴴ * V₀ = 1 ∧ V₀ * V₀ᴴ = 1) (εw : ℝ) (hw : ‖aW - W₀‖ ≤ εw) :
    ‖aWᴴ * aVᴴ * aW * V₀ - aWᴴ * aVᴴ * W₀ * V₀‖ ≤ εw := by
  have hpre2 : ‖aWᴴ * aVᴴ‖ ≤ 1 :=
    norm_prod2_le_one (le_of_eq (unitary_conjTranspose_norm haW))
      (le_of_eq (unitary_conjTranspose_norm haV))
  have hsplit : (aWᴴ * aVᴴ) * (aW - W₀) * V₀
      = aWᴴ * aVᴴ * aW * V₀ - aWᴴ * aVᴴ * W₀ * V₀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [← hsplit]
  exact le_trans (sandwich_norm_le hpre2 (le_of_eq (unitary_norm_eq_one hV₀))) hw

/-- Replacing the adjoint of `aV` in the displayed commutator product incurs at most its
approximation error to `V₀`. -/
theorem step23 (aW aV V₀ W₀ : Matrix (Reg 1) (Reg 1) ℂ)
    (haW : aWᴴ * aW = 1 ∧ aW * aWᴴ = 1) (hV₀ : V₀ᴴ * V₀ = 1 ∧ V₀ * V₀ᴴ = 1)
    (hW₀ : W₀ᴴ * W₀ = 1 ∧ W₀ * W₀ᴴ = 1) (εv : ℝ) (hv : ‖aV - V₀‖ ≤ εv) :
    ‖aWᴴ * aVᴴ * W₀ * V₀ - aWᴴ * V₀ᴴ * W₀ * V₀‖ ≤ εv := by
  have hWV : ‖W₀ * V₀‖ ≤ 1 :=
    norm_prod2_le_one (le_of_eq (unitary_norm_eq_one hW₀))
      (le_of_eq (unitary_norm_eq_one hV₀))
  have hsplit : aWᴴ * (aVᴴ - V₀ᴴ) * (W₀ * V₀)
      = aWᴴ * aVᴴ * W₀ * V₀ - aWᴴ * V₀ᴴ * W₀ * V₀ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hadj : ‖aVᴴ - V₀ᴴ‖ = ‖aV - V₀‖ := by
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
  rw [← hsplit]
  have hmid : ‖aWᴴ * (aVᴴ - V₀ᴴ) * (W₀ * V₀)‖ ≤ ‖aVᴴ - V₀ᴴ‖ :=
    sandwich_norm_le (le_of_eq (unitary_conjTranspose_norm haW)) hWV
  rw [hadj] at hmid
  exact le_trans hmid hv

/-- Replacing the adjoint of `aW` in the displayed commutator product incurs at most its
approximation error to `W₀`. -/
theorem step34 (aW W₀ V₀ : Matrix (Reg 1) (Reg 1) ℂ)
    (hV₀ : V₀ᴴ * V₀ = 1 ∧ V₀ * V₀ᴴ = 1) (hW₀ : W₀ᴴ * W₀ = 1 ∧ W₀ * W₀ᴴ = 1)
    (εw : ℝ) (hw : ‖aW - W₀‖ ≤ εw) :
    ‖aWᴴ * V₀ᴴ * W₀ * V₀ - W₀ᴴ * V₀ᴴ * W₀ * V₀‖ ≤ εw := by
  have hpost : ‖V₀ᴴ * W₀ * V₀‖ ≤ 1 :=
    norm_prod3_le_one (le_of_eq (unitary_conjTranspose_norm hV₀))
      (le_of_eq (unitary_norm_eq_one hW₀)) (le_of_eq (unitary_norm_eq_one hV₀))
  have hsplit : (aWᴴ - W₀ᴴ) * (V₀ᴴ * W₀ * V₀)
      = aWᴴ * V₀ᴴ * W₀ * V₀ - W₀ᴴ * V₀ᴴ * W₀ * V₀ := by
    simp only [Matrix.sub_mul, Matrix.mul_assoc]
  have hadj : ‖aWᴴ - W₀ᴴ‖ = ‖aW - W₀‖ := by
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
  rw [← hsplit]
  have hmid : ‖(aWᴴ - W₀ᴴ) * (V₀ᴴ * W₀ * V₀)‖ ≤ ‖aWᴴ - W₀ᴴ‖ :=
    suffix_norm_le hpost
  rw [hadj] at hmid
  exact le_trans hmid hw

/-- Combines two matrix approximation bounds by adding their errors. -/
theorem combine_two (X Y Z : Matrix (Reg 1) (Reg 1) ℂ) (e1 e2 : ℝ)
    (h1 : ‖X - Y‖ ≤ e1) (h2 : ‖Y - Z‖ ≤ e2) : ‖X - Z‖ ≤ e1 + e2 := by
  have hsplit : X - Z = (X - Y) + (Y - Z) := (sub_add_sub_cancel X Y Z).symm
  rw [hsplit]
  exact le_trans (norm_add_le (X - Y) (Y - Z)) (add_le_add h1 h2)

/-- Approximating each of two unitary factors perturbs their commutator by at most twice the sum
of the factor errors. -/
theorem unitary4_stability (aV aW V₀ W₀ : Matrix (Reg 1) (Reg 1) ℂ)
    (haV : aVᴴ * aV = 1 ∧ aV * aVᴴ = 1) (haW : aWᴴ * aW = 1 ∧ aW * aWᴴ = 1)
    (hV₀ : V₀ᴴ * V₀ = 1 ∧ V₀ * V₀ᴴ = 1) (hW₀ : W₀ᴴ * W₀ = 1 ∧ W₀ * W₀ᴴ = 1)
    (εv εw : ℝ) (hv : ‖aV - V₀‖ ≤ εv) (hw : ‖aW - W₀‖ ≤ εw) :
    ‖aWᴴ * aVᴴ * aW * aV - W₀ᴴ * V₀ᴴ * W₀ * V₀‖ ≤ 2 * (εv + εw) := by
  have hA := combine_two (aWᴴ * aVᴴ * W₀ * V₀) (aWᴴ * V₀ᴴ * W₀ * V₀)
    (W₀ᴴ * V₀ᴴ * W₀ * V₀) εv εw
    (step23 aW aV V₀ W₀ haW hV₀ hW₀ εv hv) (step34 aW W₀ V₀ hV₀ hW₀ εw hw)
  have hB := combine_two (aWᴴ * aVᴴ * aW * V₀) (aWᴴ * aVᴴ * W₀ * V₀)
    (W₀ᴴ * V₀ᴴ * W₀ * V₀) εw (εv + εw)
    (step12 aW aV W₀ V₀ haW haV hV₀ εw hw) hA
  have hC := combine_two (aWᴴ * aVᴴ * aW * aV) (aWᴴ * aVᴴ * aW * V₀)
    (W₀ᴴ * V₀ᴴ * W₀ * V₀) εv (εw + (εv + εw))
    (step01 aW aV V₀ haW haV εv hv) hB
  have hfin : εv + (εw + (εv + εw)) = 2 * (εv + εw) := by ring
  exact le_trans hC (le_of_eq hfin)

/-- The commutator word approximates the target unitary commutator with error at most twice the
sum of the word errors. -/
theorem commWord_stability (V W : List (LocalQFTGate 1)) (V₀ W₀ : Matrix (Reg 1) (Reg 1) ℂ)
    (hV₀ : V₀ᴴ * V₀ = 1 ∧ V₀ * V₀ᴴ = 1) (hW₀ : W₀ᴴ * W₀ = 1 ∧ W₀ * W₀ᴴ = 1)
    (εv εw : ℝ) (hv : ‖localProgramMatrix V - V₀‖ ≤ εv)
    (hw : ‖localProgramMatrix W - W₀‖ ≤ εw) :
    ‖localProgramMatrix (commWord V W) - W₀ᴴ * V₀ᴴ * W₀ * V₀‖ ≤ 2 * (εv + εw) := by
  rw [commWord_matrix]
  exact unitary4_stability (localProgramMatrix V) (localProgramMatrix W) V₀ W₀
    ⟨word_matrix_conj_mul_self V, word_matrix_mul_conj_self V⟩
    ⟨word_matrix_conj_mul_self W, word_matrix_mul_conj_self W⟩ hV₀ hW₀ εv εw hv hw

/-- Bounds a commutator word's distance from identity by the target commutator bound plus twice
the sum of approximation errors. -/
theorem skStep_nearIdentity (V W : List (LocalQFTGate 1)) (V₀ W₀ : Matrix (Reg 1) (Reg 1) ℂ)
    (hV₀ : V₀ᴴ * V₀ = 1 ∧ V₀ * V₀ᴴ = 1) (hW₀ : W₀ᴴ * W₀ = 1 ∧ W₀ * W₀ᴴ = 1)
    (δv δw εv εw : ℝ) (hv : ‖localProgramMatrix V - V₀‖ ≤ εv)
    (hw : ‖localProgramMatrix W - W₀‖ ≤ εw)
    (hdv : ‖V₀ - 1‖ ≤ δv) (hdw : ‖W₀ - 1‖ ≤ δw) :
    ‖localProgramMatrix (commWord V W) - 1‖ ≤ 2 * δv * δw + 2 * (εv + εw) := by
  have hstab := commWord_stability V W V₀ W₀ hV₀ hW₀ εv εw hv hw
  have hgc : ‖W₀ᴴ * V₀ᴴ * W₀ * V₀ - 1‖ ≤ 2 * δv * δw := by
    have hswap := commutator_dist_le (W₀ᴴ) (V₀ᴴ) (unitary_star_unitary hW₀)
      (unitary_star_unitary hV₀)
    rw [Matrix.conjTranspose_conjTranspose W₀, Matrix.conjTranspose_conjTranspose V₀] at hswap
    have hW : ‖W₀ᴴ - 1‖ ≤ δw := by rw [norm_sub_one_conjTranspose]; exact hdw
    have hV : ‖V₀ᴴ - 1‖ ≤ δv := by rw [norm_sub_one_conjTranspose]; exact hdv
    have hprod : ‖W₀ᴴ - 1‖ * ‖V₀ᴴ - 1‖ ≤ δw * δv :=
      mul_le_mul hW hV (norm_nonneg (V₀ᴴ - 1)) (le_trans (norm_nonneg (W₀ᴴ - 1)) hW)
    have hscal : 2 * ‖W₀ᴴ - 1‖ * ‖V₀ᴴ - 1‖ ≤ 2 * δv * δw := by
      calc 2 * ‖W₀ᴴ - 1‖ * ‖V₀ᴴ - 1‖ = 2 * (‖W₀ᴴ - 1‖ * ‖V₀ᴴ - 1‖) := by ring
        _ ≤ 2 * (δw * δv) := mul_le_mul_of_nonneg_left hprod (by norm_num)
        _ = 2 * δv * δw := by ring
    exact le_trans hswap hscal
  have hcomb := combine_two (localProgramMatrix (commWord V W))
    (W₀ᴴ * V₀ᴴ * W₀ * V₀) 1 (2 * (εv + εw)) (2 * δv * δw) hstab hgc
  have hfin2 : 2 * (εv + εw) + 2 * δv * δw = 2 * δv * δw + 2 * (εv + εw) := by ring
  exact le_trans hcomb (le_of_eq hfin2)

def wordPow {n : ℕ} : ℕ → List (LocalQFTGate n) → List (LocalQFTGate n)
  | 0, _ => []
  | j + 1, W => W ++ wordPow j W

/-- A successor word power is one copy of the word followed by the preceding power. -/
theorem wordPow_succ {n : ℕ} (j : ℕ) (W : List (LocalQFTGate n)) :
    wordPow (j + 1) W = W ++ wordPow j W := rfl

/-- The length of a word power is the exponent times the original length. -/
theorem wordPow_length {n : ℕ} (j : ℕ) (W : List (LocalQFTGate n)) :
    (wordPow j W).length = j * W.length := by
  induction j with
  | zero => simp [wordPow]
  | succ j ih => rw [wordPow_succ, List.length_append, ih, Nat.succ_mul]; omega

/-- Taking word powers preserves the fixed primitive property of every gate. -/
theorem wordPow_legal {n : ℕ} (j : ℕ) (W : List (LocalQFTGate n))
    (hW : ∀ g ∈ W, IsFixedPrim g) : ∀ g ∈ wordPow j W, IsFixedPrim g := by
  induction j with
  | zero => simp [wordPow]
  | succ j ih =>
      intro g hg
      rw [wordPow_succ, List.mem_append] at hg
      rcases hg with hg | hg
      · exact hW g hg
      · exact ih g hg

/-- The matrix of a word power is the corresponding power of its program matrix. -/
theorem wordPow_matrix {n : ℕ} (j : ℕ) (W : List (LocalQFTGate n)) :
    localProgramMatrix (wordPow j W) = (localProgramMatrix W) ^ j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [wordPow_succ, localProgramMatrix_append, ih, pow_succ]

/-- Every natural power of a one-wire unitary matrix has norm at most one. -/
theorem unitary_pow_norm_le {U : Matrix (Reg 1) (Reg 1) ℂ}
    (hU : Uᴴ * U = 1 ∧ U * Uᴴ = 1) (j : ℕ) : ‖U ^ j‖ ≤ 1 := by
  induction j with
  | zero =>
      rw [pow_zero]
      exact le_of_eq (unitary_norm_eq_one
        (U := (1 : Matrix (Reg 1) (Reg 1) ℂ))
        (by simp [Matrix.conjTranspose_one]))
  | succ j ih =>
      rw [pow_succ]
      have h1 : ‖U ^ j * U‖ ≤ ‖U ^ j‖ := by
        calc ‖U ^ j * U‖ ≤ ‖U ^ j‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
          _ ≤ ‖U ^ j‖ * 1 :=
              mul_le_mul_of_nonneg_left (le_of_eq (unitary_norm_eq_one hU)) (norm_nonneg _)
          _ = ‖U ^ j‖ := by ring
      exact le_trans h1 ih

/-- The distance of a unitary matrix power from identity is at most the exponent times the
original distance. -/
theorem unitary_pow_dist {U : Matrix (Reg 1) (Reg 1) ℂ}
    (hU : Uᴴ * U = 1 ∧ U * Uᴴ = 1) (j : ℕ) :
    ‖U ^ j - 1‖ ≤ j * ‖U - 1‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hsplit : U ^ (j + 1) - 1 = U ^ j * (U - 1) + (U ^ j - 1) := by
        rw [pow_succ, mul_sub, mul_one, sub_add_sub_cancel]
      rw [hsplit]
      have h1 : ‖U ^ j * (U - 1)‖ ≤ ‖U - 1‖ :=
        prefix_norm_le (unitary_pow_norm_le hU j)
      have h2 := norm_add_le (U ^ j * (U - 1)) (U ^ j - 1)
      have h3 := add_le_add h1 ih
      rw [Nat.cast_succ, add_mul, one_mul]
      exact le_trans h2 (by linarith)

/-- The distance of a word power's matrix from identity is at most the exponent times the
original distance. -/
theorem wordPow_dist (W : List (LocalQFTGate 1)) (j : ℕ) :
    ‖localProgramMatrix (wordPow j W) - 1‖
      ≤ j * ‖localProgramMatrix W - 1‖ := by
  rw [wordPow_matrix]
  exact unitary_pow_dist ⟨word_matrix_conj_mul_self W, word_matrix_mul_conj_self W⟩ j

def hConjWord (W : List (LocalQFTGate 1)) : List (LocalQFTGate 1) :=
  [prim1 0] ++ W ++ [prim1 0]

/-- Primitive zero is the one-wire Hadamard gate. -/
theorem prim1_zero : prim1 0 = LocalQFTGate.h wire0 := by simp [prim1]

/-- Primitive five is the negative exponent-three one-wire phase gate. -/
theorem prim1_five : prim1 5 = LocalQFTGate.cp wire0 wire0 3 true := by norm_num [prim1]

/-- Primitive six is the positive exponent-three one-wire phase gate. -/
theorem prim1_six : prim1 6 = LocalQFTGate.cp wire0 wire0 3 false := by norm_num [prim1]

/-- A singleton controlled phase word with repeated control implements the corresponding
one-wire phase matrix. -/
theorem cp_word_matrix (e : ℕ) (neg : Bool) :
    localProgramMatrix [LocalQFTGate.cp wire0 wire0 e neg]
      = oneWirePhaseMatrix wire0 (dyadicPhaseAngle e neg) := by
  rw [localProgramMatrix_cons, localProgramMatrix_nil, Matrix.one_mul,
    localGateMatrix_cp_self]

/-- The singleton primitive-zero word implements the one-wire Hadamard matrix. -/
theorem hWord_matrix :
    localProgramMatrix [prim1 0] = localGateMatrix (LocalQFTGate.h wire0) := by
  rw [prim1_zero]; simp

/-- The one-wire Hadamard matrix is self-adjoint. -/
theorem hWord_star :
    (localGateMatrix (LocalQFTGate.h wire0))ᴴ = localGateMatrix (LocalQFTGate.h wire0) :=
  Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.localGateMatrix_h_star 1 wire0

/-- The one-wire Hadamard matrix satisfies both unitary identities. -/
theorem hWord_unitary :
    (localGateMatrix (LocalQFTGate.h wire0))ᴴ * localGateMatrix (LocalQFTGate.h wire0) = 1 ∧
      localGateMatrix (LocalQFTGate.h wire0)
        * (localGateMatrix (LocalQFTGate.h wire0))ᴴ = 1 := by
  have h1 := Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.localGateMatrix_h_unitary 1 wire0
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h1
  have h2 := Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.localGateMatrix_h_unitary 1 wire0
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h2
  exact ⟨h1, h2⟩

/-- The square of the one-wire Hadamard matrix is identity. -/
theorem hWord_mul :
    localGateMatrix (LocalQFTGate.h wire0) * localGateMatrix (LocalQFTGate.h wire0) = 1 := by
  have h2 := (hWord_unitary).2
  rw [hWord_star] at h2
  exact h2

/-- Hadamard conjugation adds two gates to a word's length. -/
theorem hConjWord_length (W : List (LocalQFTGate 1)) :
    (hConjWord W).length = W.length + 2 := by simp [hConjWord]

/-- Hadamard conjugation preserves the fixed primitive property of every gate. -/
theorem hConjWord_legal (W : List (LocalQFTGate 1)) (hW : ∀ g ∈ W, IsFixedPrim g) :
    ∀ g ∈ hConjWord W, IsFixedPrim g := by
  intro g hg
  have hmem : g ∈ [prim1 0] ++ (W ++ [prim1 0]) := hg
  rcases List.mem_append.mp hmem with hA | hB
  · rw [List.mem_singleton] at hA
    rw [hA]; exact prim1_legal 0
  · rcases List.mem_append.mp hB with hB' | hB'
    · exact hW g hB'
    · rw [List.mem_singleton] at hB'
      rw [hB']; exact prim1_legal 0

/-- The Hadamard-conjugated word's matrix is the Hadamard sandwich of the original matrix. -/
theorem hConjWord_matrix (W : List (LocalQFTGate 1)) :
    localProgramMatrix (hConjWord W)
      = localGateMatrix (LocalQFTGate.h wire0) * localProgramMatrix W
        * localGateMatrix (LocalQFTGate.h wire0) := by
  rw [show hConjWord W = [prim1 0] ++ (W ++ [prim1 0]) from rfl, localProgramMatrix_append,
    localProgramMatrix_append, hWord_matrix]

/-- Hadamard conjugation does not increase a word's matrix distance from identity. -/
theorem hConjWord_dist (W : List (LocalQFTGate 1)) :
    ‖localProgramMatrix (hConjWord W) - 1‖ ≤ ‖localProgramMatrix W - 1‖ := by
  have hH : ‖localGateMatrix (LocalQFTGate.h wire0)‖ = 1 := by
    have h1 := word_matrix_norm_eq_one [prim1 0]
    rw [hWord_matrix] at h1
    exact h1
  have hsplit : localProgramMatrix (hConjWord W) - 1
      = localGateMatrix (LocalQFTGate.h wire0) * (localProgramMatrix W - 1)
        * localGateMatrix (LocalQFTGate.h wire0) := by
    have h1 : localGateMatrix (LocalQFTGate.h wire0)
        * (localProgramMatrix W - 1) * localGateMatrix (LocalQFTGate.h wire0)
        = localGateMatrix (LocalQFTGate.h wire0) * localProgramMatrix W
          * localGateMatrix (LocalQFTGate.h wire0)
          - localGateMatrix (LocalQFTGate.h wire0) * localGateMatrix (LocalQFTGate.h wire0) := by
      rw [mul_sub, sub_mul, mul_one]
    rw [h1, hWord_mul, hConjWord_matrix]
  rw [hsplit]
  exact sandwich_norm_le (le_of_eq hH) (le_of_eq hH)

/-- The commutator word of a word with itself has the identity matrix. -/
theorem commWord_self_exact (V : List (LocalQFTGate 1)) :
    localProgramMatrix (commWord V V) = 1 := by
  rw [commWord_matrix]
  have h1 : (localProgramMatrix V)ᴴ * (localProgramMatrix V)ᴴ * localProgramMatrix V
      * localProgramMatrix V
      = (localProgramMatrix V)ᴴ * (((localProgramMatrix V)ᴴ
          * localProgramMatrix V) * localProgramMatrix V) := by
    simp [Matrix.mul_assoc]
  rw [h1, word_matrix_conj_mul_self V, Matrix.one_mul, word_matrix_conj_mul_self V]

/-- Commuting a word with its Hadamard conjugate gives distance from identity at most twice the
square of the original distance bound. -/
theorem skSharpen_hConj (W : List (LocalQFTGate 1)) (δ : ℝ)
    (hδ : ‖localProgramMatrix W - 1‖ ≤ δ) :
    ‖localProgramMatrix (commWord (hConjWord W) W) - 1‖ ≤ 2 * δ * δ := by
  have h := skStep_nearIdentity (hConjWord W) W (localProgramMatrix (hConjWord W))
    (localProgramMatrix W)
    ⟨word_matrix_conj_mul_self _, word_matrix_mul_conj_self _⟩
    ⟨word_matrix_conj_mul_self _, word_matrix_mul_conj_self _⟩
    δ δ 0 0 (by simp) (by simp) (le_trans (hConjWord_dist W) hδ) hδ
  simpa using! h

/-- The commutator of a word's Hadamard conjugate with the word has length four times the
original length plus four. -/
theorem skSharpen_length (W : List (LocalQFTGate 1)) :
    (commWord (hConjWord W) W).length = 4 * W.length + 4 := by
  rw [commWord_length, hConjWord_length]; omega

/-- Multiplying one-wire phase matrices adds their angles. -/
theorem oneWirePhase_mul (θ ψ : ℝ) :
    oneWirePhaseMatrix (wire0 : Fin 1) θ * oneWirePhaseMatrix wire0 ψ
      = oneWirePhaseMatrix wire0 (θ + ψ) := by
  ext y x
  by_cases hxy : y = x
  · subst hxy
    simp only [oneWirePhaseMatrix, diag_mul_diag, Matrix.diagonal_apply, Pi.mul_apply]
    by_cases hy : y wire0
    · simp only [hy, ite_true]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp [hy]
  · simp only [oneWirePhaseMatrix, diag_mul_diag, Matrix.diagonal_apply, Pi.mul_apply, hxy,
    ite_false]

/-- The one-wire phase matrix at angle zero is identity. -/
theorem oneWirePhase_zero : oneWirePhaseMatrix (wire0 : Fin 1) 0 = 1 := by
  ext y x
  simp only [oneWirePhaseMatrix, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hxy : y = x
  · subst hxy
    by_cases hy : y wire0 <;> simp [hy]
  · simp [hxy]

/-- A natural power of a one-wire phase matrix multiplies its angle by the exponent. -/
theorem oneWirePhase_pow (θ : ℝ) (j : ℕ) :
    (oneWirePhaseMatrix (wire0 : Fin 1) θ) ^ j = oneWirePhaseMatrix wire0 (j * θ) := by
  induction j with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, oneWirePhase_zero]
  | succ j ih => rw [pow_succ, ih, oneWirePhase_mul, Nat.cast_succ, add_mul, one_mul]

/-- A natural power of a Z rotation multiplies its angle by the exponent. -/
theorem rotZ_pow (a : ℝ) (j : ℕ) : (rotZ a) ^ j = rotZ (j * a) := by
  induction j with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, rotZ_zero]
  | succ j ih => rw [pow_succ, ih, rotZ_mul, Nat.cast_succ, add_mul, one_mul]

/-- The complex exponential of two pi times the imaginary unit is one. -/
theorem exp_two_pi_I : Complex.exp ((2 * Real.pi : ℝ) * Complex.I) = 1 := by
  rw [Complex.exp_eq_one_iff]
  refine ⟨1, ?_⟩
  push_cast
  norm_num

/-- The complex exponential of negative two pi times the imaginary unit is one. -/
theorem exp_neg_two_pi_I : Complex.exp (-(2 * Real.pi : ℝ) * Complex.I) = 1 := by
  rw [neg_mul, Complex.exp_neg, exp_two_pi_I, inv_one]

/-- The Z rotation at two pi is identity. -/
theorem rotZ_two_pi : rotZ (2 * Real.pi) = 1 := by
  ext y x
  rcases reg1_cases y with hy | hy <;> rcases reg1_cases x with hx | hx
  · rw [hy, hx, rotZ_00, exp_two_pi_I, one_00]
  · rw [hy, hx, rotZ_01, one_01]
  · rw [hy, hx, rotZ_10, one_10]
  · rw [hy, hx, rotZ_11, exp_neg_two_pi_I, one_11]

/-- The one-wire phase matrix at two pi is identity. -/
theorem oneWirePhase_two_pi : oneWirePhaseMatrix (wire0 : Fin 1) (2 * Real.pi) = 1 := by
  ext y x
  rcases reg1_cases y with hy | hy <;> rcases reg1_cases x with hx | hx
  · rw [hy, hx]; simp [oneWirePhaseMatrix]
  · rw [hy, hx]; simp [oneWirePhaseMatrix]
  · rw [hy, hx]; simp [oneWirePhaseMatrix]
  · rw [hy, hx]; simp [oneWirePhaseMatrix, exp_two_pi_I]

/-- Multiplying the target by a global phase preserves approximation up to phase at the same
error. -/
theorem approxUpToPhase_smul_right {m n : Type*} [Fintype m] [Fintype n]
    {A B : Matrix m n ℂ} (φ : ℝ) {ε : ℝ} :
    approxUpToPhase A (Complex.exp (φ * Complex.I) • B) ε ↔ approxUpToPhase A B ε := by
  constructor
  · rintro ⟨θ, hθ⟩
    refine ⟨θ + φ, ?_⟩
    have hEq : Complex.exp (((θ + φ : ℝ) : ℂ) * Complex.I) • B
        = Complex.exp ((θ : ℝ) * Complex.I)
          • (Complex.exp ((φ : ℝ) * Complex.I) • B) := by
      rw [smul_smul]
      congr 1
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hEq]
    exact hθ
  · rintro ⟨θ, hθ⟩
    refine ⟨θ - φ, ?_⟩
    have hEq : Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I)
        • (Complex.exp ((φ : ℝ) * Complex.I) • B)
        = Complex.exp ((θ : ℝ) * Complex.I) • B := by
      rw [smul_smul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hEq]
    exact hθ

/-- Approximation up to phase is transitive with the two error bounds added. -/
theorem approxUpToPhase_trans {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A B C : Matrix m n ℂ} {ε₁ ε₂ : ℝ}
    (h₁ : approxUpToPhase A B ε₁) (h₂ : approxUpToPhase B C ε₂) :
    approxUpToPhase A C (ε₁ + ε₂) := by
  obtain ⟨θ₁, e₁⟩ := h₁
  obtain ⟨θ₂, e₂⟩ := h₂
  refine ⟨θ₁ + θ₂, ?_⟩
  have hsplit : A - Complex.exp (((θ₁ + θ₂ : ℝ) : ℂ) * Complex.I) • C
      = (A - Complex.exp ((θ₁ : ℝ) * Complex.I) • B)
        + Complex.exp ((θ₁ : ℝ) * Complex.I)
          • (B - Complex.exp ((θ₂ : ℝ) * Complex.I) • C) := by
    rw [smul_sub, smul_smul, ← Complex.exp_add, sub_add_sub_cancel]
    congr 1
    push_cast
    ring
  have hunit : ‖(Complex.exp ((θ₁ : ℝ) * Complex.I) : ℂ)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hsmul : ‖Complex.exp ((θ₁ : ℝ) * Complex.I)
      • (B - Complex.exp ((θ₂ : ℝ) * Complex.I) • C)‖
      = ‖B - Complex.exp ((θ₂ : ℝ) * Complex.I) • C‖ := by
    rw [norm_smul, hunit, one_mul]
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [hsmul]
  exact add_le_add e₁ e₂

/-- Every matrix approximates itself up to phase with zero error. -/
theorem approxUpToPhase_refl {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : approxUpToPhase A A 0 := by
  refine ⟨0, ?_⟩
  rw [show Complex.exp ((0 : ℝ) * Complex.I) = 1 from by simp [Complex.exp_zero], one_smul,
    sub_self]
  exact norm_le_zero_iff.mpr rfl

/-- A one-wire phase matrix equals a Z rotation by negative half the angle times the
corresponding global phase. -/
theorem oneWirePhase_smul_rotZ (θ : ℝ) :
    oneWirePhaseMatrix (0 : Fin 1) θ
      = Complex.exp ((θ / 2 : ℝ) * Complex.I) • rotZ (-θ / 2) := by
  ext y x
  rcases reg1_cases y with hy | hy
  · rcases reg1_cases x with hx | hx
    · rw [hy, hx]
      simp only [oneWirePhaseMatrix, rotZ_apply, Matrix.diagonal_apply,
        Matrix.smul_apply, Bool.false_eq_true, ite_false, ite_true, smul_eq_mul]
      have hsum : ((θ / 2 : ℝ) : ℂ) * Complex.I + ((-θ / 2 : ℝ) : ℂ) * Complex.I = 0 := by
        push_cast
        ring
      rw [← Complex.exp_add, hsum, Complex.exp_zero]
    · have hne : ¬(y = x) := by
        intro h
        rw [hy, hx] at h
        exact absurd (congrFun h ⟨0, by omega⟩) (by simp)
      simp only [oneWirePhaseMatrix, rotZ_apply, Matrix.diagonal_apply, Matrix.smul_apply]
      rw [ite_eq_right hne, ite_eq_right hne]
      simp
  · rcases reg1_cases x with hx | hx
    · have hne : ¬(y = x) := by
        intro h
        rw [hy, hx] at h
        exact absurd (congrFun h ⟨0, by omega⟩) (by simp)
      simp only [oneWirePhaseMatrix, rotZ_apply, Matrix.diagonal_apply, Matrix.smul_apply]
      rw [ite_eq_right hne, ite_eq_right hne]
      simp
    · rw [hy, hx]
      simp only [oneWirePhaseMatrix, rotZ_apply, Matrix.diagonal_apply,
        Matrix.smul_apply, Bool.false_eq_true, ite_true, smul_eq_mul, neg_div, neg_neg]
      have hsum : ((θ / 2 : ℝ) : ℂ) * Complex.I + ((θ / 2 : ℝ) : ℂ) * Complex.I
          = ((θ : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [← Complex.exp_add, hsum]

/-- An imaginary exponential is not one when the cosine of its angle is not one. -/
theorem exp_mul_I_ne_one_of_cos {x : ℝ} (hx : Real.cos x ≠ 1) :
    Complex.exp (x * Complex.I) ≠ 1 := by
  intro he
  apply hx
  have hre := congrArg Complex.re he
  rw [Complex.exp_mul_I, Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, mul_zero, zero_mul, sub_zero, add_zero] at hre
  exact hre

/-- The cosine of one quarter of pi is not one. -/
theorem cos_pi_four_ne_one : Real.cos (Real.pi / 4) ≠ 1 := by
  rw [Real.cos_pi_div_four]
  intro h
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 2 = 2 := by linarith
  rw [h3] at hs
  exact absurd hs (by norm_num)

/-- The positive exponent-three dyadic phase angle is one quarter of pi. -/
theorem dyadicPhaseAngle_three_false : dyadicPhaseAngle 3 false = Real.pi / 4 := by
  show 2 * Real.pi / (2 ^ 3 : ℝ) = Real.pi / 4
  field_simp
  norm_num

/-- The negative exponent-three dyadic phase angle is negative one quarter of pi. -/
theorem dyadicPhaseAngle_three_true : dyadicPhaseAngle 3 true = -(Real.pi / 4) := by
  show -(2 * Real.pi / (2 ^ 3 : ℝ)) = -(Real.pi / 4)
  field_simp
  norm_num

/-- The exponential of either signed exponent-three dyadic phase angle is not one. -/
theorem exp_dyadic_three_ne_one (neg : Bool) :
    Complex.exp (dyadicPhaseAngle 3 neg * Complex.I) ≠ 1 := by
  refine exp_mul_I_ne_one_of_cos ?_
  cases neg with
  | false =>
      rw [dyadicPhaseAngle_three_false]
      exact cos_pi_four_ne_one
  | true =>
      rw [dyadicPhaseAngle_three_true, Real.cos_neg]
      exact cos_pi_four_ne_one

/-- Left multiplication by the adjoint of a diagonal matrix scales each row by the conjugate
diagonal entry. -/
theorem conjDiag_mul_entry {d : Reg 1 → ℂ} (A : Matrix (Reg 1) (Reg 1) ℂ) (y x : Reg 1) :
    ((Matrix.diagonal d)ᴴ * A) y x = (starRingEnd ℂ (d y)) * A y x := by
  rw [Matrix.mul_apply, sum_reg1]
  rcases reg1_cases y with hy | hy
  · rw [hy]
    have hoff : ((Matrix.diagonal d)ᴴ) (fun _ => false) (fun _ => true) = 0 := by
      rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply, ite_eq_right basis_ne']
      simp
    have hdiag : ((Matrix.diagonal d)ᴴ) (fun _ => false) (fun _ => false)
        = (starRingEnd ℂ) (d (fun _ => false)) := by
      rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply, ite_eq_left rfl]
      rfl
    rw [hoff, zero_mul, add_zero, hdiag]
  · rw [hy]
    have hoff : ((Matrix.diagonal d)ᴴ) (fun _ => true) (fun _ => false) = 0 := by
      rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply, ite_eq_right basis_ne]
      simp
    have hdiag : ((Matrix.diagonal d)ᴴ) (fun _ => true) (fun _ => true)
        = (starRingEnd ℂ) (d (fun _ => true)) := by
      rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply, ite_eq_left rfl]
      rfl
    rw [hoff, zero_mul, zero_add, hdiag]

/-- The false-to-false entry of the one-wire Hadamard gate is the inverse square root of two. -/
theorem h_entry_ff : localGateMatrix (LocalQFTGate.h wire0) (fun _ => false) (fun _ => false)
    = (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [show LocalQFTGate.h wire0 = LocalQFTGate.h (0 : Fin 1) from rfl, h1_entries]
  exact hadamard_ff

/-- The true-row, false-column entry of the one-wire Hadamard gate is the inverse square root of
two. -/
theorem h_entry_tf : localGateMatrix (LocalQFTGate.h wire0) (fun _ => true) (fun _ => false)
    = (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [show LocalQFTGate.h wire0 = LocalQFTGate.h (0 : Fin 1) from rfl, h1_entries]
  exact hadamard_tf

/-- The true-to-true entry of the one-wire Hadamard gate is the negative inverse square root of
two. -/
theorem h_entry_tt : localGateMatrix (LocalQFTGate.h wire0) (fun _ => true) (fun _ => true)
    = -((Real.sqrt 2 : ℂ)⁻¹) := by
  rw [show LocalQFTGate.h wire0 = LocalQFTGate.h (0 : Fin 1) from rfl, h1_entries]
  exact hadamard_tt

/-- The false-to-false entry of a one-wire phase matrix is one. -/
theorem oneWire_diag_ff (θ : ℝ) :
    oneWirePhaseMatrix (wire0 : Fin 1) θ (fun _ => false) (fun _ => false) = 1 := by
  simp only [oneWirePhaseMatrix, Matrix.diagonal_apply]
  rfl

/-- The true-to-true entry of a one-wire phase matrix is the exponential of the imaginary angle. -/
theorem oneWire_diag_tt (θ : ℝ) :
    oneWirePhaseMatrix (wire0 : Fin 1) θ (fun _ => true) (fun _ => true)
      = Complex.exp (θ * Complex.I) := by
  simp only [oneWirePhaseMatrix, Matrix.diagonal_apply]
  rfl

/-- The true-row, false-column entry of a Hadamard-conjugated phase matrix is half of one minus
its phase. -/
theorem hMulDiag_h_entry_10 (θ : ℝ) :
    (localGateMatrix (LocalQFTGate.h wire0)
        * Matrix.diagonal (fun x : Reg 1 => if x wire0 then Complex.exp (θ * Complex.I) else 1)
        * localGateMatrix (LocalQFTGate.h wire0)) (fun _ => true) (fun _ => false)
      = (1 - Complex.exp (θ * Complex.I)) * (2 : ℂ)⁻¹ := by
  rw [mul_apply2, Matrix.mul_diagonal, Matrix.mul_diagonal,
    ite_eq_right (show ¬((fun _ : Fin 1 => false) wire0) = true from by simp),
    ite_eq_left (show ((fun _ : Fin 1 => true) wire0) = true from by simp),
    h_entry_tf, h_entry_ff, h_entry_tt]
  have hfirst : (Real.sqrt 2 : ℂ)⁻¹ * 1 * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [inv_sqrt2_mul_mid (1 : ℂ), mul_one]
  have hsecond : (-(Real.sqrt 2 : ℂ)⁻¹ * Complex.exp (θ * Complex.I))
      * (Real.sqrt 2 : ℂ)⁻¹ = -((2 : ℂ)⁻¹ * Complex.exp (θ * Complex.I)) := by
    have hmid := inv_sqrt2_mul_mid (Complex.exp (θ * Complex.I))
    linear_combination -hmid
  rw [hfirst, hsecond, sub_mul, one_mul]
  ring

/-- The Hadamard conjugate of the positive T word does not have the identity matrix. -/
theorem hConj_T_ne_one : localProgramMatrix (hConjWord [prim1 6]) ≠ 1 := by
  intro h
  have h10 : localProgramMatrix (hConjWord [prim1 6]) (fun _ => true) (fun _ => false) = 0 := by
    rw [h]; exact one_10
  rw [hConjWord_matrix, prim1_six, cp_word_matrix 3 false,
    show oneWirePhaseMatrix (wire0 : Fin 1) (dyadicPhaseAngle 3 false)
      = Matrix.diagonal (fun x : Reg 1 =>
          if x wire0 then Complex.exp (dyadicPhaseAngle 3 false * Complex.I) else 1)
      from rfl,
    hMulDiag_h_entry_10] at h10
  rcases mul_eq_zero.mp h10 with h' | h'
  · exact exp_dyadic_three_ne_one false (eq_of_sub_eq_zero h').symm
  · exact absurd h' (inv_ne_zero (by norm_num))

/-- Conjugating the positive exponent-three dyadic phase gives the negative exponent-three
dyadic phase. -/
theorem conj_exp_dyadic_three :
    (starRingEnd ℂ) (Complex.exp (dyadicPhaseAngle 3 false * Complex.I))
      = Complex.exp (dyadicPhaseAngle 3 true * Complex.I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    dyadicPhaseAngle_three_true, dyadicPhaseAngle_three_false]
  congr 1
  push_cast
  ring

/-- The complex exponential of any real imaginary angle has squared norm one. -/
theorem normSq_exp_angle (θ : ℝ) :
    Complex.normSq (Complex.exp (θ * Complex.I)) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  have hre : (θ * Complex.I).re = 0 := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre]
  simp

/-- The commutator word of Hadamard and the positive T gate does not have the identity matrix. -/
theorem commWord_H_T_ne_one : localProgramMatrix (commWord [prim1 0] [prim1 6]) ≠ 1 := by
  intro h
  have h10 : localProgramMatrix (commWord [prim1 0] [prim1 6]) (fun _ => true)
      (fun _ => false) = 0 := by
    rw [h]; exact one_10
  have hshape : (((oneWirePhaseMatrix wire0 (dyadicPhaseAngle 3 false))ᴴ
          * localGateMatrix (LocalQFTGate.h wire0))
        * oneWirePhaseMatrix wire0 (dyadicPhaseAngle 3 false)
      * localGateMatrix (LocalQFTGate.h wire0))
      = (oneWirePhaseMatrix wire0 (dyadicPhaseAngle 3 false))ᴴ
        * ((localGateMatrix (LocalQFTGate.h wire0)
            * oneWirePhaseMatrix wire0 (dyadicPhaseAngle 3 false))
          * localGateMatrix (LocalQFTGate.h wire0)) := by
    simp [Matrix.mul_assoc]
  rw [commWord_matrix, prim1_six, cp_word_matrix 3 false, hWord_matrix,
    hWord_star, hshape,
    show oneWirePhaseMatrix (wire0 : Fin 1) (dyadicPhaseAngle 3 false)
      = Matrix.diagonal (fun x : Reg 1 =>
          if x wire0 then Complex.exp (dyadicPhaseAngle 3 false * Complex.I) else 1)
      from rfl,
    conjDiag_mul_entry,
    ite_eq_left (show ((fun _ : Fin 1 => true) wire0) = true from by simp),
    hMulDiag_h_entry_10] at h10
  have hn : (starRingEnd ℂ) (Complex.exp (dyadicPhaseAngle 3 false * Complex.I))
      * Complex.exp (dyadicPhaseAngle 3 false * Complex.I) = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, normSq_exp_angle]
    push_cast
    rfl
  have hwmul : (starRingEnd ℂ) (Complex.exp (dyadicPhaseAngle 3 false * Complex.I))
      * ((1 - Complex.exp (dyadicPhaseAngle 3 false * Complex.I)) * (2 : ℂ)⁻¹)
      = (Complex.exp (dyadicPhaseAngle 3 true * Complex.I) - 1) * (2 : ℂ)⁻¹ := by
    have h1 : (starRingEnd ℂ) (Complex.exp (dyadicPhaseAngle 3 false * Complex.I))
        * (1 - Complex.exp (dyadicPhaseAngle 3 false * Complex.I))
        = Complex.exp (dyadicPhaseAngle 3 true * Complex.I) - 1 := by
      rw [mul_sub, mul_one, hn, ← conj_exp_dyadic_three]
    calc (starRingEnd ℂ) (Complex.exp (dyadicPhaseAngle 3 false * Complex.I))
        * ((1 - Complex.exp (dyadicPhaseAngle 3 false * Complex.I)) * (2 : ℂ)⁻¹)
        = ((starRingEnd ℂ) (Complex.exp (dyadicPhaseAngle 3 false * Complex.I))
            * (1 - Complex.exp (dyadicPhaseAngle 3 false * Complex.I))) * (2 : ℂ)⁻¹ :=
            (mul_assoc _ _ _).symm
      _ = (Complex.exp (dyadicPhaseAngle 3 true * Complex.I) - 1) * (2 : ℂ)⁻¹ := by rw [h1]
  rw [hwmul] at h10
  rcases mul_eq_zero.mp h10 with h' | h'
  · exact exp_dyadic_three_ne_one true (eq_of_sub_eq_zero h')
  · exact absurd h' (inv_ne_zero (by norm_num))

/-- Every entry norm of a one-wire matrix is bounded by its operator norm. -/
theorem entry_le_opNorm (A : Matrix (Reg 1) (Reg 1) ℂ) (y x : Reg 1) : ‖A y x‖ ≤ ‖A‖ := by
  set v : QState (Reg 1) := fun z => if z = x then 1 else 0 with hv
  have hvx : v x = 1 := by simp [hv]
  have hvz : ∀ z : Reg 1, z ≠ x → v z = 0 := fun z hz => by simp [hv, hz]
  have hvnorm : ‖toEuclidean_fromVec v‖ = 1 := by
    have hsq : ‖toEuclidean_fromVec v‖ ^ 2 = 1 := by
      rw [norm_toEuclidean_fromVec_sq,
        Finset.sum_eq_single_of_mem x (Finset.mem_univ x)
          (fun b _ hb => by rw [hvz b hb]; simp), hvx]
      simp
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · have hnn : 0 ≤ ‖toEuclidean_fromVec v‖ := norm_nonneg _
      linarith
  have hentry : (A *ᵥ v) y = A y x := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x)
        (fun b _ hb => by rw [hvz b hb, mul_zero]), hvx, mul_one]
  have hmul := l2_norm_mulVec_fromVec_le A v
  rw [hvnorm, mul_one] at hmul
  calc ‖A y x‖ = ‖(A *ᵥ v) y‖ := by rw [hentry]
    _ ≤ ‖toEuclidean_fromVec (A *ᵥ v)‖ := norm_le_of_reg1
    _ ≤ ‖A‖ := hmul

/-- The constantly false and constantly true one-wire registers are distinct. -/
theorem reg1_ff_ne_tt : ¬((fun _ => false : Reg 1) = (fun _ => true : Reg 1)) := by
  intro h
  exact absurd (congrFun h ⟨0, by omega⟩) (by simp)

def zWord : List (LocalQFTGate 1) := [prim1 1]

/-- Primitive one is the negative exponent-one one-wire phase gate. -/
theorem prim1_one : prim1 1 = LocalQFTGate.cp wire0 wire0 1 true := by norm_num [prim1]

/-- The negative exponent-one dyadic phase angle is negative pi. -/
theorem dyadicPhaseAngle_one_true : dyadicPhaseAngle 1 true = -Real.pi := by
  show -(2 * Real.pi / (2 ^ 1 : ℝ)) = -Real.pi
  norm_num

/-- The complex exponential of pi times the imaginary unit is negative one. -/
theorem exp_pi_I : Complex.exp (Real.pi * Complex.I) = -1 := by
  rw [Complex.exp_mul_I]
  norm_num [Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im, Real.cos_pi, Real.sin_pi]

/-- The Z word implements the one-wire phase matrix at pi. -/
theorem zWord_matrix :
    localProgramMatrix zWord = oneWirePhaseMatrix (wire0 : Fin 1) Real.pi := by
  rw [zWord, prim1_one, cp_word_matrix 1 true, dyadicPhaseAngle_one_true]
  ext y x
  rcases reg1_cases y with hy | hy <;> rcases reg1_cases x with hx | hx
  · rw [hy, hx]; simp [oneWirePhaseMatrix]
  · rw [hy, hx]; simp [oneWirePhaseMatrix]
  · rw [hy, hx]; simp [oneWirePhaseMatrix]
  · rw [hy, hx]
    simp only [oneWirePhaseMatrix, Matrix.diagonal_apply, ite_true, neg_mul, Complex.exp_neg,
      exp_pi_I]
    norm_num

/-- The false-to-false entry of the Z word's matrix is one. -/
theorem zWord_entry_ff : localProgramMatrix zWord (fun _ => false) (fun _ => false) = 1 := by
  rw [zWord_matrix]; exact oneWire_diag_ff Real.pi

/-- The true-to-true entry of the Z word's matrix is negative one. -/
theorem zWord_entry_tt : localProgramMatrix zWord (fun _ => true) (fun _ => true) = -1 := by
  rw [zWord_matrix, oneWire_diag_tt, exp_pi_I]

/-- Every off-diagonal entry of the Z word's matrix is zero. -/
theorem zWord_entry_off {y x : Reg 1} (h : y ≠ x) : localProgramMatrix zWord y x = 0 := by
  rw [zWord_matrix]
  simp [oneWirePhaseMatrix, Matrix.diagonal_apply, h]

/-- The square of the Z word's matrix is identity. -/
theorem zWord_mul : localProgramMatrix zWord * localProgramMatrix zWord = 1 := by
  rw [zWord_matrix, oneWirePhase_mul,
    show Real.pi + Real.pi = 2 * Real.pi from by ring, oneWirePhase_two_pi]

def zProjWord (W : List (LocalQFTGate 1)) : List (LocalQFTGate 1) :=
  W ++ zWord ++ W ++ zWord

/-- The Z-projection word has twice the original word's length plus two. -/
theorem zProjWord_length (W : List (LocalQFTGate 1)) :
    (zProjWord W).length = 2 * W.length + 2 := by
  simp only [zProjWord, zWord, List.length_append, List.length_singleton]
  omega

/-- The Z-projection word preserves the fixed primitive property of every gate. -/
theorem zProjWord_legal (W : List (LocalQFTGate 1)) (hW : ∀ g ∈ W, IsFixedPrim g) :
    ∀ g ∈ zProjWord W, IsFixedPrim g := by
  intro g hg
  have hdisj : g ∈ W ∨ g = prim1 1 := by
    simp only [zProjWord, zWord, List.mem_append, List.mem_singleton] at hg
    tauto
  rcases hdisj with h | h
  · exact hW g h
  · rw [h]; exact prim1_legal 1

/-- The Z-projection word implements the product of Z, the original word, Z, and the original
word again. -/
theorem zProjWord_matrix (W : List (LocalQFTGate 1)) :
    localProgramMatrix (zProjWord W)
      = localProgramMatrix zWord * localProgramMatrix W
        * localProgramMatrix zWord * localProgramMatrix W := by
  simp only [zProjWord, zWord, localProgramMatrix_append, localProgramMatrix_cons,
    localProgramMatrix_nil, Matrix.one_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- Left multiplication by the Z word's matrix scales each row by its diagonal Z entry. -/
theorem mul_zWord_left_entry (U : Matrix (Reg 1) (Reg 1) ℂ) (y x : Reg 1) :
    (localProgramMatrix zWord * U) y x = localProgramMatrix zWord y y * U y x := by
  rw [Matrix.mul_apply, sum_reg1]
  rcases reg1_cases y with hy | hy
  · rw [hy, zWord_entry_ff, zWord_entry_off reg1_ff_ne_tt, one_mul, zero_mul, add_zero]
  · rw [hy, zWord_entry_off (Ne.symm reg1_ff_ne_tt), zWord_entry_tt, zero_mul, neg_one_mul,
      zero_add]

/-- Gives all four entries of the Z-projection product in terms of entries of the original
one-wire matrix. -/
theorem zProj_entries (U : Matrix (Reg 1) (Reg 1) ℂ) :
    (localProgramMatrix zWord * U * localProgramMatrix zWord * U) (fun _ => false)
        (fun _ => true)
      = U (fun _ => false) (fun _ => true)
          * (U (fun _ => false) (fun _ => false) - U (fun _ => true) (fun _ => true)) ∧
    (localProgramMatrix zWord * U * localProgramMatrix zWord * U) (fun _ => true)
        (fun _ => false)
      = U (fun _ => true) (fun _ => false)
          * (U (fun _ => true) (fun _ => true) - U (fun _ => false) (fun _ => false)) ∧
    (localProgramMatrix zWord * U * localProgramMatrix zWord * U) (fun _ => false)
        (fun _ => false)
      = U (fun _ => false) (fun _ => false) * U (fun _ => false) (fun _ => false)
          - U (fun _ => false) (fun _ => true) * U (fun _ => true) (fun _ => false) ∧
    (localProgramMatrix zWord * U * localProgramMatrix zWord * U) (fun _ => true)
        (fun _ => true)
      = U (fun _ => true) (fun _ => true) * U (fun _ => true) (fun _ => true)
          - U (fun _ => false) (fun _ => true) * U (fun _ => true) (fun _ => false) := by
  have hAA : localProgramMatrix zWord * U * localProgramMatrix zWord * U
      = (localProgramMatrix zWord * U) * (localProgramMatrix zWord * U) := by noncomm_ring
  constructor
  · rw [hAA, Matrix.mul_apply, sum_reg1, mul_zWord_left_entry, mul_zWord_left_entry,
      mul_zWord_left_entry, zWord_entry_ff, zWord_entry_tt]
    ring
  · constructor
    · rw [hAA, Matrix.mul_apply, sum_reg1, mul_zWord_left_entry, mul_zWord_left_entry,
        mul_zWord_left_entry, zWord_entry_ff, zWord_entry_tt]
      ring
    · constructor
      · rw [hAA, Matrix.mul_apply, sum_reg1, mul_zWord_left_entry, mul_zWord_left_entry,
          mul_zWord_left_entry, zWord_entry_ff, zWord_entry_tt]
        ring
      · rw [hAA, Matrix.mul_apply, sum_reg1, mul_zWord_left_entry, mul_zWord_left_entry,
          mul_zWord_left_entry, zWord_entry_ff, zWord_entry_tt]
        ring

/-- The squared norms of the two entries in each column of a word's matrix sum to one. -/
theorem word_col_norm_sq (V : List (LocalQFTGate 1)) (x : Reg 1) :
    ‖localProgramMatrix V (fun _ => false) x‖ ^ 2
      + ‖localProgramMatrix V (fun _ => true) x‖ ^ 2 = 1 := by
  have hdiag : ∑ z : Reg 1, ((localProgramMatrix V)ᴴ) x z * localProgramMatrix V z x = 1 := by
    have h1 : (((localProgramMatrix V)ᴴ * localProgramMatrix V) x x
        = ∑ z : Reg 1, ((localProgramMatrix V)ᴴ) x z * localProgramMatrix V z x) := rfl
    rw [word_matrix_conj_mul_self V, Matrix.one_apply, ite_eq_left rfl] at h1
    exact h1.symm
  have hcast : ((∑ z : Reg 1, Complex.normSq (localProgramMatrix V z x) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum]
    refine Eq.trans (Finset.sum_congr rfl fun z _ => ?_) hdiag
    rw [Matrix.conjTranspose_apply, Complex.star_def]
    exact Complex.normSq_eq_conj_mul_self
  have hreal : ∑ z : Reg 1, Complex.normSq (localProgramMatrix V z x) = 1 :=
    Complex.ofReal_inj.mp hcast
  have hsplit : ∑ z : Reg 1, Complex.normSq (localProgramMatrix V z x)
      = Complex.normSq (localProgramMatrix V (fun _ => false) x)
        + Complex.normSq (localProgramMatrix V (fun _ => true) x) := by
    have hc : ((∑ z : Reg 1, Complex.normSq (localProgramMatrix V z x) : ℝ) : ℂ)
        = ((Complex.normSq (localProgramMatrix V (fun _ => false) x)
            + Complex.normSq (localProgramMatrix V (fun _ => true) x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, Complex.ofReal_add]
      exact sum_reg1 (fun z => (Complex.normSq (localProgramMatrix V z x) : ℂ))
    exact Complex.ofReal_inj.mp hc
  rw [hsplit, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hreal
  exact hreal

/-- For a nonzero complex number of norm at most one, its distance from its normalization is one
minus its norm. -/
theorem norm_sub_self_div_norm {c : ℂ} (h1 : ‖c‖ ≤ 1) (h0 : c ≠ 0) :
    ‖c - c / ‖c‖‖ = 1 - ‖c‖ := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr h0
  have hstep : c - c / ‖c‖ = c * (1 - ((‖c‖ : ℝ) : ℂ)⁻¹) := by
    rw [div_eq_mul_inv, mul_sub, mul_one]
  have hmid : ‖(1 : ℂ) - ((‖c‖ : ℝ) : ℂ)⁻¹‖ = (1 - ‖c‖) * (‖c‖)⁻¹ := by
    have htne : (((‖c‖ : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
    have hcast : ((‖c‖ - 1 : ℝ) : ℂ) = (((‖c‖ : ℝ) : ℂ)) - 1 := by
      push_cast
      ring
    have hsub : (1 : ℂ) - ((‖c‖ : ℝ) : ℂ)⁻¹
        = (((‖c‖ - 1 : ℝ) : ℂ)) * (((‖c‖ : ℝ) : ℂ)⁻¹) := by
      rw [hcast, sub_mul, mul_inv_cancel₀ htne, one_mul]
    have hle : (‖c‖ - 1 : ℝ) ≤ 0 := by linarith
    have hn1 : ‖(((‖c‖ - 1 : ℝ) : ℂ))‖ = 1 - ‖c‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hle]
      ring
    have hn2 : ‖(((‖c‖ : ℝ) : ℂ)⁻¹)‖ = (‖c‖)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    rw [hsub, Complex.norm_mul, hn1, hn2]
  rw [hstep, Complex.norm_mul, hmid]
  field_simp

/-- If a word is within `δ` of identity and `δ` is at most one half, its Z-projection is within
nine times the square of `δ` of a phase-scaled diagonal phase matrix. -/
theorem zProjWord_nearDiagonal (W : List (LocalQFTGate 1)) {δ : ℝ}
    (hδ : ‖localProgramMatrix W - 1‖ ≤ δ) (hδle : δ ≤ 1 / 2) :
    ∃ α φ : ℝ, ‖localProgramMatrix (zProjWord W)
        - Complex.exp (α * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) φ‖
      ≤ 9 * δ * δ := by
  have hδ2 : 0 ≤ δ := le_trans (norm_nonneg _) hδ

  have hUff : ‖localProgramMatrix W (fun _ => false) (fun _ => false) - 1‖ ≤ δ := by
    have h := entry_le_opNorm (localProgramMatrix W - 1) (fun _ => false) (fun _ => false)
    rw [Matrix.sub_apply, Matrix.one_apply, ite_eq_left rfl] at h
    exact h.trans hδ
  have hUtt : ‖localProgramMatrix W (fun _ => true) (fun _ => true) - 1‖ ≤ δ := by
    have h := entry_le_opNorm (localProgramMatrix W - 1) (fun _ => true) (fun _ => true)
    rw [Matrix.sub_apply, Matrix.one_apply, ite_eq_left rfl] at h
    exact h.trans hδ
  have hUft : ‖localProgramMatrix W (fun _ => false) (fun _ => true)‖ ≤ δ := by
    have h := entry_le_opNorm (localProgramMatrix W - 1) (fun _ => false) (fun _ => true)
    rw [Matrix.sub_apply, Matrix.one_apply, ite_eq_right reg1_ff_ne_tt, sub_zero] at h
    exact h.trans hδ
  have hUtf : ‖localProgramMatrix W (fun _ => true) (fun _ => false)‖ ≤ δ := by
    have h := entry_le_opNorm (localProgramMatrix W - 1) (fun _ => true) (fun _ => false)
    rw [Matrix.sub_apply, Matrix.one_apply, ite_eq_right (Ne.symm reg1_ff_ne_tt), sub_zero] at h
    exact h.trans hδ

  have hcolf := word_col_norm_sq W (fun _ => false)
  have hcolt := word_col_norm_sq W (fun _ => true)
  have hUtf_le : ‖localProgramMatrix W (fun _ => true) (fun _ => false)‖ ^ 2 ≤ δ * δ := by
    have hsum : (δ - ‖localProgramMatrix W (fun _ => true) (fun _ => false)‖)
        * (δ + ‖localProgramMatrix W (fun _ => true) (fun _ => false)‖) ≥ 0 :=
      mul_nonneg (sub_nonneg.mpr hUtf) (by
        have := norm_nonneg (localProgramMatrix W (fun _ => true) (fun _ => false))
        linarith)
    nlinarith [hsum]
  have hUft_le : ‖localProgramMatrix W (fun _ => false) (fun _ => true)‖ ^ 2 ≤ δ * δ := by
    have hsum : (δ - ‖localProgramMatrix W (fun _ => false) (fun _ => true)‖)
        * (δ + ‖localProgramMatrix W (fun _ => false) (fun _ => true)‖) ≥ 0 :=
      mul_nonneg (sub_nonneg.mpr hUft) (by
        have := norm_nonneg (localProgramMatrix W (fun _ => false) (fun _ => true))
        linarith)
    nlinarith [hsum]
  have hpos1 : 0 ≤ 1 - δ * δ := by nlinarith
  have hUff_ge : 1 - δ * δ ≤ ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖ := by
    have hsq : (1 - δ * δ) ^ 2
        ≤ ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖ ^ 2 := by
      nlinarith [hcolf]
    have habs := (sq_le_sq
      (a := 1 - δ * δ)
      (b := ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖)).mp hsq
    rwa [abs_of_nonneg hpos1, abs_of_nonneg (norm_nonneg _)] at habs
  have hUtt_ge : 1 - δ * δ ≤ ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖ := by
    have hsq : (1 - δ * δ) ^ 2
        ≤ ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖ ^ 2 := by
      nlinarith [hcolt]
    have habs := (sq_le_sq
      (a := 1 - δ * δ)
      (b := ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖)).mp hsq
    rwa [abs_of_nonneg hpos1, abs_of_nonneg (norm_nonneg _)] at habs

  set c0 : ℂ := localProgramMatrix (zProjWord W) (fun _ => false) (fun _ => false) with hc0def
  set c1 : ℂ := localProgramMatrix (zProjWord W) (fun _ => true) (fun _ => true) with hc1def
  have hproj := zProj_entries (localProgramMatrix W)
  rw [← zProjWord_matrix W] at hproj
  have hdiagdiff1 : ‖localProgramMatrix W (fun _ => true) (fun _ => true)
      - localProgramMatrix W (fun _ => false) (fun _ => false)‖ ≤ 2 * δ := by
    have hrev : ‖(1 : ℂ) - localProgramMatrix W (fun _ => false) (fun _ => false)‖
        = ‖localProgramMatrix W (fun _ => false) (fun _ => false) - 1‖ :=
      (norm_sub_rev _ _).symm
    calc ‖localProgramMatrix W (fun _ => true) (fun _ => true)
          - localProgramMatrix W (fun _ => false) (fun _ => false)‖
        = ‖(localProgramMatrix W (fun _ => true) (fun _ => true) - 1)
            + ((1 : ℂ) - localProgramMatrix W (fun _ => false) (fun _ => false))‖ := by
              rw [sub_add_sub_cancel]
      _ ≤ ‖localProgramMatrix W (fun _ => true) (fun _ => true) - 1‖
            + ‖(1 : ℂ) - localProgramMatrix W (fun _ => false) (fun _ => false)‖ :=
              norm_add_le _ _
      _ = ‖localProgramMatrix W (fun _ => true) (fun _ => true) - 1‖
          + ‖localProgramMatrix W (fun _ => false) (fun _ => false) - 1‖ := by rw [hrev]
      _ ≤ δ + δ := add_le_add hUtt hUff
      _ = 2 * δ := by ring
  have hdiagdiff0 : ‖localProgramMatrix W (fun _ => false) (fun _ => false)
      - localProgramMatrix W (fun _ => true) (fun _ => true)‖ ≤ 2 * δ := by
    have hrev : ‖(1 : ℂ) - localProgramMatrix W (fun _ => true) (fun _ => true)‖
        = ‖localProgramMatrix W (fun _ => true) (fun _ => true) - 1‖ :=
      (norm_sub_rev _ _).symm
    calc ‖localProgramMatrix W (fun _ => false) (fun _ => false)
          - localProgramMatrix W (fun _ => true) (fun _ => true)‖
        = ‖(localProgramMatrix W (fun _ => false) (fun _ => false) - 1)
            + ((1 : ℂ) - localProgramMatrix W (fun _ => true) (fun _ => true))‖ := by
              rw [sub_add_sub_cancel]
      _ ≤ ‖localProgramMatrix W (fun _ => false) (fun _ => false) - 1‖
            + ‖(1 : ℂ) - localProgramMatrix W (fun _ => true) (fun _ => true)‖ :=
              norm_add_le _ _
      _ = ‖localProgramMatrix W (fun _ => false) (fun _ => false) - 1‖
          + ‖localProgramMatrix W (fun _ => true) (fun _ => true) - 1‖ := by rw [hrev]
      _ ≤ δ + δ := add_le_add hUff hUtt
      _ = 2 * δ := by ring
  have hcross : ‖localProgramMatrix W (fun _ => false) (fun _ => true)‖
      * ‖localProgramMatrix W (fun _ => true) (fun _ => false)‖ ≤ δ * δ :=
    mul_le_mul hUft hUtf (norm_nonneg _) (le_trans (norm_nonneg _) hUft)
  have hVft : ‖localProgramMatrix (zProjWord W) (fun _ => false) (fun _ => true)‖
      ≤ 2 * δ * δ := by
    rw [hproj.1, Complex.norm_mul]
    calc ‖localProgramMatrix W (fun _ => false) (fun _ => true)‖
          * ‖localProgramMatrix W (fun _ => false) (fun _ => false)
            - localProgramMatrix W (fun _ => true) (fun _ => true)‖
        ≤ δ * (2 * δ) := mul_le_mul hUft hdiagdiff0 (norm_nonneg _)
            (le_trans (norm_nonneg _) hUft)
      _ = 2 * δ * δ := by ring
  have hVtf : ‖localProgramMatrix (zProjWord W) (fun _ => true) (fun _ => false)‖
      ≤ 2 * δ * δ := by
    rw [hproj.2.1, Complex.norm_mul]
    calc ‖localProgramMatrix W (fun _ => true) (fun _ => false)‖
          * ‖localProgramMatrix W (fun _ => true) (fun _ => true)
            - localProgramMatrix W (fun _ => false) (fun _ => false)‖
        ≤ δ * (2 * δ) := mul_le_mul hUtf hdiagdiff1 (norm_nonneg _)
            (le_trans (norm_nonneg _) hUtf)
      _ = 2 * δ * δ := by ring

  have hprod0 : localProgramMatrix W (fun _ => false) (fun _ => false)
      * localProgramMatrix W (fun _ => false) (fun _ => false)
      - localProgramMatrix W (fun _ => false) (fun _ => true)
        * localProgramMatrix W (fun _ => true) (fun _ => false) = c0 := hproj.2.2.1.symm
  have hprod1 : localProgramMatrix W (fun _ => true) (fun _ => true)
      * localProgramMatrix W (fun _ => true) (fun _ => true)
      - localProgramMatrix W (fun _ => false) (fun _ => true)
        * localProgramMatrix W (fun _ => true) (fun _ => false) = c1 := hproj.2.2.2.symm
  have hc0lo : 1 - 3 * δ * δ ≤ ‖c0‖ := by
    have hsqq : (1 - δ * δ) * (1 - δ * δ)
        ≤ ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖
          * ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖ := by
      nlinarith [hUff_ge]
    have hstep : ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖
          * ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖
          - ‖localProgramMatrix W (fun _ => false) (fun _ => true)‖
            * ‖localProgramMatrix W (fun _ => true) (fun _ => false)‖ ≤ ‖c0‖ := by
      have h1 := norm_sub_norm_le
        (localProgramMatrix W (fun _ => false) (fun _ => false)
          * localProgramMatrix W (fun _ => false) (fun _ => false))
        (localProgramMatrix W (fun _ => false) (fun _ => true)
          * localProgramMatrix W (fun _ => true) (fun _ => false))
      rwa [Complex.norm_mul, Complex.norm_mul, hprod0] at h1
    have h0 : 1 - 3 * δ * δ
        ≤ ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖
          * ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖ - δ * δ := by
      nlinarith [hsqq, hpos1]
    refine le_trans h0 ?_
    calc ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖
            * ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖ - δ * δ
        ≤ ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖
            * ‖localProgramMatrix W (fun _ => false) (fun _ => false)‖
          - ‖localProgramMatrix W (fun _ => false) (fun _ => true)‖
            * ‖localProgramMatrix W (fun _ => true) (fun _ => false)‖ :=
            sub_le_sub_left hcross _
      _ ≤ ‖c0‖ := hstep
  have hc1lo : 1 - 3 * δ * δ ≤ ‖c1‖ := by
    have hsqq : (1 - δ * δ) * (1 - δ * δ)
        ≤ ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖
          * ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖ := by
      nlinarith [hUtt_ge]
    have hstep : ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖
          * ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖
          - ‖localProgramMatrix W (fun _ => false) (fun _ => true)‖
            * ‖localProgramMatrix W (fun _ => true) (fun _ => false)‖ ≤ ‖c1‖ := by
      have h1 := norm_sub_norm_le
        (localProgramMatrix W (fun _ => true) (fun _ => true)
          * localProgramMatrix W (fun _ => true) (fun _ => true))
        (localProgramMatrix W (fun _ => false) (fun _ => true)
          * localProgramMatrix W (fun _ => true) (fun _ => false))
      rwa [Complex.norm_mul, Complex.norm_mul, hprod1] at h1
    have h0 : 1 - 3 * δ * δ
        ≤ ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖
          * ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖ - δ * δ := by
      nlinarith [hsqq, hpos1]
    refine le_trans h0 ?_
    calc ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖
            * ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖ - δ * δ
        ≤ ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖
            * ‖localProgramMatrix W (fun _ => true) (fun _ => true)‖
          - ‖localProgramMatrix W (fun _ => false) (fun _ => true)‖
            * ‖localProgramMatrix W (fun _ => true) (fun _ => false)‖ :=
            sub_le_sub_left hcross _
      _ ≤ ‖c1‖ := hstep
  have hc0hi : ‖c0‖ ≤ 1 :=
    unitary_entry_le_one (word_matrix_conj_mul_self (zProjWord W)) _ _
  have hc1hi : ‖c1‖ ≤ 1 :=
    unitary_entry_le_one (word_matrix_conj_mul_self (zProjWord W)) _ _
  have hc0pos : 0 < ‖c0‖ := by
    have h1 : (0 : ℝ) < 1 - 3 * δ * δ := by nlinarith
    nlinarith
  have hc1pos : 0 < ‖c1‖ := by
    have h1 : (0 : ℝ) < 1 - 3 * δ * δ := by nlinarith
    nlinarith
  have hc0ne : c0 ≠ 0 := norm_ne_zero_iff.mp (fun h => by
    rw [h] at hc0pos; exact absurd hc0pos (by norm_num))
  have hc1ne : c1 ≠ 0 := norm_ne_zero_iff.mp (fun h => by
    rw [h] at hc1pos; exact absurd hc1pos (by norm_num))

  set T : Matrix (Reg 1) (Reg 1) ℂ :=
    Matrix.diagonal (fun x : Reg 1 => if x wire0 then c1 / ‖c1‖ else c0 / ‖c0‖) with hTdef
  have hTff : T (fun _ => false) (fun _ => false) = c0 / ‖c0‖ := by
    rw [hTdef]; simp [Matrix.diagonal_apply]
  have hTtt : T (fun _ => true) (fun _ => true) = c1 / ‖c1‖ := by
    rw [hTdef]; simp [Matrix.diagonal_apply]
  have hToff {y x : Reg 1} (h : y ≠ x) : T y x = 0 := by
    rw [hTdef]; simp [Matrix.diagonal_apply, h]
  have hVT : ‖localProgramMatrix (zProjWord W) - T‖ ≤ 3 * (3 * δ * δ) := by
    refine opNorm_le_of_entry_bound (by positivity) ?_
    intro y x
    rcases reg1_cases y with hy | hy <;> rcases reg1_cases x with hx | hx
    · rw [hy, hx, Matrix.sub_apply, hTff, ← hc0def, norm_sub_self_div_norm hc0hi hc0ne]
      nlinarith
    · rw [hy, hx, Matrix.sub_apply, hToff reg1_ff_ne_tt, sub_zero]
      exact le_trans hVft (by nlinarith)
    · rw [hy, hx, Matrix.sub_apply, hToff (Ne.symm reg1_ff_ne_tt), sub_zero]
      exact le_trans hVtf (by nlinarith)
    · rw [hy, hx, Matrix.sub_apply, hTtt, ← hc1def, norm_sub_self_div_norm hc1hi hc1ne]
      nlinarith
  have hinv0 : ((‖c0‖ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hc0pos.ne'
  have hinv1 : ((‖c1‖ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hc1pos.ne'
  have hphase0 : Complex.exp (Complex.arg c0 * Complex.I) = c0 / ‖c0‖ := by
    rw [div_eq_mul_inv]
    calc Complex.exp (Complex.arg c0 * Complex.I)
        = (((‖c0‖ : ℝ) : ℂ))⁻¹ * ((((‖c0‖ : ℝ) : ℂ))
            * Complex.exp (Complex.arg c0 * Complex.I)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hinv0, one_mul]
      _ = (((‖c0‖ : ℝ) : ℂ))⁻¹ * c0 := by rw [Complex.norm_mul_exp_arg_mul_I c0]
      _ = c0 * (((‖c0‖ : ℝ) : ℂ))⁻¹ := mul_comm _ _
  have hnormc1c0 : ‖c1 * (starRingEnd ℂ) c0‖ = ‖c1‖ * ‖c0‖ := by
    rw [Complex.norm_mul, Complex.norm_conj]
  have hc0conj_ne : (starRingEnd ℂ) c0 ≠ 0 := star_ne_zero.mpr hc0ne
  have hc1c0ne : c1 * (starRingEnd ℂ) c0 ≠ 0 := mul_ne_zero hc1ne hc0conj_ne
  have hcast : ((‖c1 * (starRingEnd ℂ) c0‖ : ℝ) : ℂ)
      = ((‖c1‖ * ‖c0‖ : ℝ) : ℂ) := by
    rw [hnormc1c0]
  have hBAinv : ((‖c1‖ * ‖c0‖ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact mul_ne_zero hc1pos.ne' hc0pos.ne'
  have hphase1 : Complex.exp (Complex.arg (c1 * (starRingEnd ℂ) c0) * Complex.I)
      = c1 * (starRingEnd ℂ) c0 / ‖c1 * (starRingEnd ℂ) c0‖ := by
    rw [hcast, div_eq_mul_inv]
    calc Complex.exp (Complex.arg (c1 * (starRingEnd ℂ) c0) * Complex.I)
        = ((‖c1‖ * ‖c0‖ : ℝ) : ℂ)⁻¹ * (((‖c1‖ * ‖c0‖ : ℝ) : ℂ)
            * Complex.exp (Complex.arg (c1 * (starRingEnd ℂ) c0) * Complex.I)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hBAinv, one_mul]
      _ = ((‖c1‖ * ‖c0‖ : ℝ) : ℂ)⁻¹ * (c1 * (starRingEnd ℂ) c0) := by
          rw [← hcast, Complex.norm_mul_exp_arg_mul_I (c1 * (starRingEnd ℂ) c0)]
      _ = c1 * (starRingEnd ℂ) c0 * ((‖c1‖ * ‖c0‖ : ℝ) : ℂ)⁻¹ := mul_comm _ _
  have hconjsq : c0 * (starRingEnd ℂ) c0
      = (((‖c0‖ : ℝ) : ℂ)) * (((‖c0‖ : ℝ) : ℂ)) := by
    have hB : (Complex.normSq c0 : ℂ)
        = (((‖c0‖ : ℝ) : ℂ)) * (((‖c0‖ : ℝ) : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      ring
    rw [mul_comm c0 ((starRingEnd ℂ) c0)]
    rw [← Complex.normSq_eq_conj_mul_self, hB]
  have hprod : Complex.exp (Complex.arg c0 * Complex.I)
      * Complex.exp (Complex.arg (c1 * (starRingEnd ℂ) c0) * Complex.I) = c1 / ‖c1‖ := by
    rw [hphase0, hphase1, hcast, Complex.ofReal_mul]
    simp only [div_eq_mul_inv, mul_inv]
    have rearr : c0 * (((‖c0‖ : ℝ) : ℂ))⁻¹
          * (c1 * ((starRingEnd ℂ) c0)
            * (((((‖c1‖ : ℝ) : ℂ))⁻¹) * ((((‖c0‖ : ℝ) : ℂ))⁻¹)))
        = c1 * (c0 * ((starRingEnd ℂ) c0))
          * (((((‖c0‖ : ℝ) : ℂ))⁻¹) * ((((‖c0‖ : ℝ) : ℂ))⁻¹)
            * ((((‖c1‖ : ℝ) : ℂ))⁻¹)) := by
      ring
    rw [rearr, hconjsq]
    field_simp
  have hTphase : T = Complex.exp (Complex.arg c0 * Complex.I)
      • oneWirePhaseMatrix (wire0 : Fin 1) (Complex.arg (c1 * (starRingEnd ℂ) c0)) := by
    ext y x
    rcases reg1_cases y with hy | hy <;> rcases reg1_cases x with hx | hx
    · rw [hy, hx, hTff]
      simp only [oneWirePhaseMatrix, Matrix.diagonal_apply, Bool.false_eq_true, ite_false,
        ite_true, Matrix.smul_apply, smul_eq_mul, mul_one]
      exact hphase0.symm
    · rw [hy, hx, hToff reg1_ff_ne_tt]
      simp [oneWirePhaseMatrix, Matrix.diagonal_apply, Matrix.smul_apply, smul_zero,
        reg1_ff_ne_tt]
    · rw [hy, hx, hToff (Ne.symm reg1_ff_ne_tt)]
      simp [oneWirePhaseMatrix, Matrix.diagonal_apply, Matrix.smul_apply, smul_zero,
        Ne.symm reg1_ff_ne_tt]
    · rw [hy, hx, hTtt]
      simp only [oneWirePhaseMatrix, Matrix.diagonal_apply, Bool.false_eq_true, ite_true,
        Matrix.smul_apply, smul_eq_mul]
      exact hprod.symm
  refine ⟨Complex.arg c0, Complex.arg (c1 * (starRingEnd ℂ) c0), ?_⟩
  rw [← hTphase]
  calc ‖localProgramMatrix (zProjWord W) - T‖ ≤ 3 * (3 * δ * δ) := hVT
    _ = 9 * δ * δ := by ring

/-- The distance between equal powers of two unitary matrices is at most the exponent times
their original distance. -/
theorem unitary_pow_sub (U V : Matrix (Reg 1) (Reg 1) ℂ)
    (hU : Uᴴ * U = 1 ∧ U * Uᴴ = 1) (hV : Vᴴ * V = 1 ∧ V * Vᴴ = 1) (j : ℕ) :
    ‖U ^ j - V ^ j‖ ≤ (j : ℝ) * ‖U - V‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hsplit : U ^ (j + 1) - V ^ (j + 1)
          = U ^ j * (U - V) + (U ^ j - V ^ j) * V := by
        rw [pow_succ, pow_succ, Matrix.mul_sub, Matrix.sub_mul]
        noncomm_ring
      rw [hsplit]
      have h1 : ‖U ^ j * (U - V)‖ ≤ ‖U - V‖ :=
        prefix_norm_le (unitary_pow_norm_le hU j)
      have h2 : ‖(U ^ j - V ^ j) * V‖ ≤ ‖U ^ j - V ^ j‖ :=
        suffix_norm_le (le_of_eq (unitary_norm_eq_one hV))
      have h3 := norm_add_le (U ^ j * (U - V)) ((U ^ j - V ^ j) * V)
      rw [Nat.cast_succ, add_mul, one_mul]
      linarith

/-- Complex conjugation negates the real angle in an imaginary exponential. -/
theorem exp_conj_angle (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp (x * Complex.I)) = Complex.exp (-(x * Complex.I)) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- The star of an imaginary exponential negates its real angle. -/
theorem exp_star_angle (x : ℝ) :
    star (Complex.exp (x * Complex.I)) = Complex.exp (-(x * Complex.I)) :=
  exp_conj_angle x

/-- The adjoint of a one-wire phase matrix negates its angle. -/
theorem oneWirePhase_star (θ : ℝ) :
    (oneWirePhaseMatrix (wire0 : Fin 1) θ)ᴴ = oneWirePhaseMatrix (wire0 : Fin 1) (-θ) := by
  ext y x
  rcases reg1_cases y with hy | hy <;> rcases reg1_cases x with hx | hx
  · rw [hy, hx]
    simp [oneWirePhaseMatrix, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  · rw [hy, hx]
    simp [oneWirePhaseMatrix, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      reg1_ff_ne_tt, Ne.symm reg1_ff_ne_tt]
  · rw [hy, hx]
    simp [oneWirePhaseMatrix, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      reg1_ff_ne_tt, Ne.symm reg1_ff_ne_tt]
  · rw [hy, hx]
    simp [oneWirePhaseMatrix, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      exp_star_angle, neg_mul]

/-- Every one-wire phase matrix satisfies both unitary identities. -/
theorem oneWirePhase_unitary (θ : ℝ) :
    (oneWirePhaseMatrix (wire0 : Fin 1) θ)ᴴ * oneWirePhaseMatrix wire0 θ = 1 ∧
      oneWirePhaseMatrix wire0 θ * (oneWirePhaseMatrix wire0 θ)ᴴ = 1 := by
  rw [oneWirePhase_star, oneWirePhase_mul, oneWirePhase_mul,
    show -θ + θ = 0 from by ring, show θ + -θ = 0 from by ring, oneWirePhase_zero]
  constructor <;> rfl

/-- A one-wire phase matrix multiplied by a global phase satisfies both unitary identities. -/
theorem phaseSmul_unitary (α φ : ℝ) :
    ((Complex.exp (α * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) φ)ᴴ
        * (Complex.exp (α * Complex.I) • oneWirePhaseMatrix wire0 φ) = 1) ∧
      ((Complex.exp (α * Complex.I) • oneWirePhaseMatrix wire0 φ)
        * ((Complex.exp (α * Complex.I) • oneWirePhaseMatrix wire0 φ)ᴴ) = 1) := by
  have hu := oneWirePhase_unitary φ
  have hc : star (Complex.exp (α * Complex.I)) * Complex.exp (α * Complex.I) = 1 := by
    show (starRingEnd ℂ) (Complex.exp (α * Complex.I)) * Complex.exp (α * Complex.I) = 1
    rw [← Complex.normSq_eq_conj_mul_self, normSq_exp_angle]
    exact Complex.ofReal_one
  constructor
  · rw [Matrix.conjTranspose_smul, smul_mul_smul]
    rw [hc, one_smul]
    exact hu.1
  · rw [Matrix.conjTranspose_smul, smul_mul_smul]
    rw [show Complex.exp (α * Complex.I) * star (Complex.exp (α * Complex.I))
          = star (Complex.exp (α * Complex.I)) * Complex.exp (α * Complex.I) from
        mul_comm _ _, hc, one_smul]
    exact hu.2

/-- A scalar multiple of a matrix raised to a natural power is the corresponding scalar power
times the matrix power. -/
theorem smul_pow_matrix (c : ℂ) (A : Matrix (Reg 1) (Reg 1) ℂ) (j : ℕ) :
    (c • A) ^ j = c ^ j • A ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, pow_succ, pow_succ, ih, smul_mul_assoc, Matrix.mul_smul, smul_smul]

/-- Powering a seed word multiplies its tracked phase angles and its approximation error bound
by the exponent. -/
theorem seedPow_track (S : List (LocalQFTGate 1)) (α φ τ : ℝ)
    (htrack : ‖localProgramMatrix S
        - Complex.exp (α * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) φ‖ ≤ τ) (j : ℕ) :
    ‖localProgramMatrix (wordPow j S)
        - Complex.exp ((j : ℝ) * α * Complex.I)
          • oneWirePhaseMatrix (wire0 : Fin 1) ((j : ℝ) * φ)‖
      ≤ (j : ℝ) * τ := by
  have hstab := unitary_pow_sub (localProgramMatrix S)
    (Complex.exp (α * Complex.I) • oneWirePhaseMatrix wire0 φ)
    ⟨word_matrix_conj_mul_self S, word_matrix_mul_conj_self S⟩ (phaseSmul_unitary α φ) j
  have hpower : (Complex.exp (α * Complex.I)
      • oneWirePhaseMatrix (wire0 : Fin 1) φ) ^ j
      = Complex.exp ((j : ℝ) * α * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) ((j : ℝ) * φ) := by
    rw [smul_pow_matrix, oneWirePhase_pow, ← Complex.exp_nat_mul]
    have hsc : Complex.exp ((j : ℂ) * (α * Complex.I))
        = Complex.exp (((j : ℝ) * α) * Complex.I) := by
      congr 1
      push_cast
      ring
    rw [hsc]
  rw [← wordPow_matrix, hpower] at hstab
  refine le_trans hstab ?_
  exact mul_le_mul_of_nonneg_left htrack (Nat.cast_nonneg j)

/-- The distance of an imaginary exponential from one is bounded by the absolute angle. -/
theorem norm_exp_sub_one_angle (h : ℝ) :
    ‖Complex.exp (h * Complex.I) - 1‖ ≤ |h| := by
  have hcos : Real.sin h ^ 2 + Real.cos h ^ 2 = 1 := Real.sin_sq_add_cos_sq h
  have hhalf : Real.sin (h / 2) ^ 2 = (1 - Real.cos h) / 2 := by
    rw [Real.sin_sq_eq_half_sub, two_mul, add_halves]
    ring
  have hsq : (Real.cos h - 1) ^ 2 + Real.sin h ^ 2 = (2 * Real.sin (h / 2)) ^ 2 := by
    have h4 : (2 * Real.sin (h / 2)) ^ 2 = 2 - 2 * Real.cos h := by
      rw [mul_pow, hhalf]
      ring
    rw [h4]
    linear_combination hcos
  have hreim : Complex.normSq (Complex.exp (h * Complex.I) - 1)
      = (Real.cos h - 1) ^ 2 + Real.sin h ^ 2 := by
    rw [Complex.normSq_apply, Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im]
    ring
  have habs : |2 * Real.sin (h / 2)| ≤ |h| := by
    rcases eq_or_ne h 0 with h0 | h0
    · rw [h0]
      simp
    · have h1 := Real.abs_sin_lt_abs (div_ne_zero h0 (by norm_num : (2 : ℝ) ≠ 0))
      have h2 : |2 * Real.sin (h / 2)| = 2 * |Real.sin (h / 2)| := by
        rw [abs_mul, abs_two]
      rw [h2]
      calc 2 * |Real.sin (h / 2)| ≤ 2 * |h / 2| :=
            mul_le_mul_of_nonneg_left h1.le (by norm_num)
        _ = |h| := by
            rw [abs_div, abs_two]
            field_simp
  refine le_of_sq_le_sq ?_ (abs_nonneg h)
  rw [← Complex.normSq_eq_norm_sq, hreim, hsq]
  exact sq_le_sq.mpr (by rw [abs_abs]; exact habs)

/-- The distance between two imaginary exponentials is bounded by the absolute difference of
their real angles. -/
theorem norm_exp_sub_exp_angle (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ |a - b| := by
  have hkey : Complex.exp (b * Complex.I) * Complex.exp ((a - b) * Complex.I)
      = Complex.exp (a * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [show Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)
        = Complex.exp (b * Complex.I) * (Complex.exp ((a - b) * Complex.I) - 1) from by
      rw [mul_sub, hkey, mul_one],
    Complex.norm_mul, Complex.norm_exp]
  have hre : ((b : ℝ) * Complex.I).re = 0 := by
    simp
  rw [hre, Real.exp_zero, one_mul]
  have hfin := norm_exp_sub_one_angle (a - b)
  rwa [Complex.ofReal_sub] at hfin

/-- The distance between two one-wire phase matrices is at most three times the absolute
difference of their angles. -/
theorem oneWirePhase_dist (ψ₁ ψ₂ : ℝ) :
    ‖oneWirePhaseMatrix (wire0 : Fin 1) ψ₁ - oneWirePhaseMatrix wire0 ψ₂‖
      ≤ 3 * |ψ₁ - ψ₂| := by
  refine opNorm_le_of_entry_bound (by positivity) ?_
  intro y x
  rcases reg1_cases y with hy | hy <;> rcases reg1_cases x with hx | hx
  · rw [hy, hx]
    simp [oneWirePhaseMatrix, Matrix.diagonal_apply, Matrix.sub_apply, sub_self]
  · rw [hy, hx]
    simp [oneWirePhaseMatrix, Matrix.diagonal_apply, reg1_ff_ne_tt,
      Ne.symm reg1_ff_ne_tt]
  · rw [hy, hx]
    simp [oneWirePhaseMatrix, Matrix.diagonal_apply, reg1_ff_ne_tt,
      Ne.symm reg1_ff_ne_tt]
  · rw [hy, hx]
    simp only [oneWirePhaseMatrix, Matrix.diagonal_apply, Matrix.sub_apply]
    exact le_trans (norm_exp_sub_exp_angle ψ₁ ψ₂) (by linarith)

/-- Every nonnegative real number lies within half a positive step of some natural multiple of
that step. -/
theorem exists_round_mul_le {φ : ℝ} (hφ : 0 < φ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ j : ℕ, |(j : ℝ) * φ - θ| ≤ φ / 2 := by
  have hr : 0 ≤ θ / φ := div_nonneg hθ hφ.le
  obtain ⟨j, hj⟩ : ∃ j : ℕ, |(j : ℝ) - θ / φ| ≤ 1 / 2 := by
    set r := θ / φ with hrdef
    obtain ⟨f, hfle, hflt⟩ : ∃ f : ℕ, (f : ℝ) ≤ r ∧ r < (f : ℝ) + 1 :=
      ⟨Nat.floor r, Nat.floor_le hr, (Nat.lt_floor_add_one r)⟩
    by_cases hc : r - (f : ℝ) ≤ 1 / 2
    · refine ⟨f, ?_⟩
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      exact hc
    · refine ⟨f + 1, ?_⟩
      have hcast : ((f + 1 : ℕ) : ℝ) = (f : ℝ) + 1 := by norm_num
      rw [abs_sub_comm, abs_of_nonpos (by linarith)]
      have h1 : r - (f : ℝ) - 1 < 0 := by linarith
      have h2 : (1 : ℝ) - (r - (f : ℝ)) ≤ 1 / 2 := by linarith
      linarith
  refine ⟨j, ?_⟩
  have hmul : |(j : ℝ) * φ - θ| = φ * |(j : ℝ) - θ / φ| := by
    have hstep : (j : ℝ) * φ - θ = φ * ((j : ℝ) - θ / φ) := by
      field_simp
    rw [hstep, abs_mul, abs_of_pos hφ]
  rw [hmul]
  calc φ * |(j : ℝ) - θ / φ| ≤ φ * (1 / 2) :=
        mul_le_mul_of_nonneg_left hj hφ.le
    _ = φ / 2 := by ring

/-- A seed tracking a positive phase yields a word power approximating any nonnegative target
phase, with the stated accumulated error and exact length. -/
theorem seedPowerNet (S : List (LocalQFTGate 1)) (α φ τ θ : ℝ)
    (htrack : ‖localProgramMatrix S
        - Complex.exp (α * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) φ‖ ≤ τ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ) :
    ∃ j : ℕ, approxUpToPhase (localProgramMatrix (wordPow j S))
      (oneWirePhaseMatrix (wire0 : Fin 1) θ) ((j : ℝ) * τ + 3 * φ / 2) ∧
      (wordPow j S).length = j * S.length := by
  obtain ⟨j, hj⟩ := exists_round_mul_le hφ hθ
  have htrackj := seedPow_track S α φ τ htrack j
  refine ⟨j, ?_, wordPow_length j S⟩
  show ∃ ψ : ℝ, ‖localProgramMatrix (wordPow j S)
      - (Complex.exp (ψ * Complex.I)) • oneWirePhaseMatrix (wire0 : Fin 1) θ‖
      ≤ (j : ℝ) * τ + 3 * φ / 2
  refine ⟨(j : ℝ) * α, ?_⟩
  show ‖localProgramMatrix (wordPow j S)
      - Complex.exp ((Complex.ofReal ((j : ℝ) * α)) * Complex.I)
        • oneWirePhaseMatrix (wire0 : Fin 1) θ‖
      ≤ (j : ℝ) * τ + 3 * φ / 2
  have hs' : Complex.exp ((((j : ℝ) : ℂ)) * (((α : ℝ) : ℂ)) * Complex.I)
      = Complex.exp ((Complex.ofReal ((j : ℝ) * α)) * Complex.I) := by
    push_cast
    ring
  rw [hs'] at htrackj
  have hsplit : localProgramMatrix (wordPow j S)
      - Complex.exp ((Complex.ofReal ((j : ℝ) * α)) * Complex.I)
        • oneWirePhaseMatrix (wire0 : Fin 1) θ
      = (localProgramMatrix (wordPow j S)
          - Complex.exp ((Complex.ofReal ((j : ℝ) * α)) * Complex.I)
            • oneWirePhaseMatrix (wire0 : Fin 1) ((j : ℝ) * φ))
        + Complex.exp ((Complex.ofReal ((j : ℝ) * α)) * Complex.I)
          • (oneWirePhaseMatrix (wire0 : Fin 1) ((j : ℝ) * φ)
            - oneWirePhaseMatrix (wire0 : Fin 1) θ) := by
    rw [smul_sub, sub_add_sub_cancel]
  have hphase1 : ‖Complex.exp ((Complex.ofReal ((j : ℝ) * α)) * Complex.I)
      • (oneWirePhaseMatrix (wire0 : Fin 1) ((j : ℝ) * φ)
        - oneWirePhaseMatrix (wire0 : Fin 1) θ)‖
      ≤ 3 * |(j : ℝ) * φ - θ| := by
    have hunit : ‖Complex.exp ((Complex.ofReal ((j : ℝ) * α)) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : ((Complex.ofReal ((j : ℝ) * α) * Complex.I)).re = 0 := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im]
        ring
      rw [hre]
      simp
    rw [norm_smul, hunit, one_mul]
    exact oneWirePhase_dist _ _
  have h1 := add_le_add htrackj hphase1
  have h2 : 3 * |(j : ℝ) * φ - θ| ≤ 3 * φ / 2 := by
    rw [le_div_iff₀ (show (0 : ℝ) < 2 by norm_num)]
    nlinarith [hj, hφ]
  calc ‖localProgramMatrix (wordPow j S)
        - Complex.exp ((Complex.ofReal ((j : ℝ) * α)) * Complex.I)
          • oneWirePhaseMatrix (wire0 : Fin 1) θ‖
      = ‖(localProgramMatrix (wordPow j S)
          - Complex.exp ((Complex.ofReal ((j : ℝ) * α)) * Complex.I)
            • oneWirePhaseMatrix (wire0 : Fin 1) ((j : ℝ) * φ))
        + Complex.exp ((Complex.ofReal ((j : ℝ) * α)) * Complex.I)
          • (oneWirePhaseMatrix (wire0 : Fin 1) ((j : ℝ) * φ)
            - oneWirePhaseMatrix (wire0 : Fin 1) θ)‖ := by rw [hsplit]
    _ ≤ ‖localProgramMatrix (wordPow j S)
          - Complex.exp ((Complex.ofReal ((j : ℝ) * α)) * Complex.I)
            • oneWirePhaseMatrix (wire0 : Fin 1) ((j : ℝ) * φ)‖
        + ‖Complex.exp ((Complex.ofReal ((j : ℝ) * α)) * Complex.I)
          • (oneWirePhaseMatrix (wire0 : Fin 1) ((j : ℝ) * φ)
            - oneWirePhaseMatrix (wire0 : Fin 1) θ)‖ := norm_add_le _ _
    _ ≤ (j : ℝ) * τ + 3 * φ / 2 := by linarith

/-- Adjoint powers of a seed tracking a positive phase approximate any nonpositive target phase
with the stated accumulated error. -/
theorem seedPowerNet_neg (S : List (LocalQFTGate 1)) (α φ τ θ : ℝ)
    (htrack : ‖localProgramMatrix S
        - Complex.exp (α * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) φ‖ ≤ τ)
    (hφ : 0 < φ) (hθ : θ ≤ 0) :
    ∃ j : ℕ, approxUpToPhase (localProgramMatrix (localProgramAdjoint (wordPow j S)))
      (oneWirePhaseMatrix (wire0 : Fin 1) θ) ((j : ℝ) * τ + 3 * φ / 2) := by
  obtain ⟨j, hj, -⟩ := seedPowerNet S α φ τ (-θ) htrack hφ (by linarith)
  obtain ⟨β, hβ⟩ := hj
  refine ⟨j, -β, ?_⟩
  have hconj : (Complex.exp (β * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) (-θ))ᴴ
      = Complex.exp (↑(-β) * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) θ := by
    have hscalar : Complex.exp (↑(-β) * Complex.I) = Complex.exp (-(↑β * Complex.I)) := by
      congr 1
      push_cast
      ring
    rw [Matrix.conjTranspose_smul, oneWirePhase_star, exp_star_angle, neg_neg, hscalar]
  rw [← hconj]
  exact (le_of_eq (adjointWord_dist (wordPow j S)
    (Complex.exp (β * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) (-θ)))).trans hβ

/-- For every positive precision, there exists a short fixed primitive seed quadratically close
to a phase-scaled diagonal phase matrix. -/
theorem pigeonhole_diagonalSeed (m : ℕ) (hm : 1 ≤ m) :
    ∃ S : List (LocalQFTGate 1), (∀ g ∈ S, IsFixedPrim g) ∧ S.length ≤ 2 * (16 * m + 98) + 2 ∧
      ∃ α φ : ℝ, ‖localProgramMatrix S
        - Complex.exp (α * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) φ‖
        ≤ 9 * tolerance m * tolerance m := by
  obtain ⟨W, hlegal, hlen, hdist⟩ := pigeonhole_nearIdentity m
  have htolle : tolerance m ≤ 1 / 2 := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hle : tolerance (m' + 1) = ((2 : ℝ) ⁻¹) ^ m' * (1 / 2) := by
      unfold tolerance
      rw [pow_add, pow_one]
      norm_num
    rw [hle]
    have hle1 : ((2 : ℝ) ⁻¹) ^ m' ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  obtain ⟨α, φ, htrack⟩ := zProjWord_nearDiagonal W hdist htolle
  exact ⟨zProjWord W, zProjWord_legal W hlegal, by
    rw [zProjWord_length]; omega, α, φ, htrack⟩

/-- A singleton dyadic phase gate of exponent at most three is a fixed primitive word
implementing its target with zero phase-adjusted error. -/
theorem exactLetter_slice (e : ℕ) (he : e ≤ 3) (neg : Bool) :
    (∀ g ∈ [LocalQFTGate.cp wire0 wire0 e neg], IsFixedPrim g) ∧
    approxUpToPhase (localProgramMatrix [LocalQFTGate.cp wire0 wire0 e neg])
      (oneWirePhaseMatrix (wire0 : Fin 1) (dyadicPhaseAngle e neg)) 0 := by
  refine ⟨by simp [IsFixedPrim, he], 0, ?_⟩
  rw [show Complex.exp ((0 : ℝ) * Complex.I) = 1 from by simp, one_smul, cp_word_matrix e neg,
    sub_self]
  exact norm_le_zero_iff.mpr rfl

def tracksDiag (W : List (LocalQFTGate 1)) (β p E : ℝ) : Prop :=
  ‖localProgramMatrix W
    - Complex.exp (β * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) p‖ ≤ E

/-- The empty word tracks zero global phase and zero diagonal phase with zero error. -/
theorem tracksDiag_nil : tracksDiag [] 0 0 0 := by
  rw [tracksDiag]
  simp [localProgramMatrix_nil, oneWirePhase_zero]

/-- The positive T word tracks a diagonal phase of one quarter of pi with zero global phase and
zero error. -/
theorem tracksDiag_T : tracksDiag [prim1 6] 0 (Real.pi / 4) 0 := by
  rw [tracksDiag, prim1_six, cp_word_matrix 3 false, dyadicPhaseAngle_three_false,
    show Complex.exp ((0 : ℝ) * Complex.I) = 1 from by simp, one_smul, sub_self]
  exact norm_le_zero_iff.mpr rfl

/-- Two positive T gates track a diagonal phase of one half of pi with zero global phase and
zero error. -/
theorem tracksDiag_T2 : tracksDiag [prim1 6, prim1 6] 0 (Real.pi / 2) 0 := by
  have hM : localProgramMatrix [prim1 6, prim1 6]
      = oneWirePhaseMatrix (wire0 : Fin 1) (Real.pi / 2) := by
    rw [show [prim1 6, prim1 6] = [prim1 6] ++ [prim1 6] from rfl, localProgramMatrix_append,
      prim1_six, cp_word_matrix 3 false, dyadicPhaseAngle_three_false, oneWirePhase_mul,
      show Real.pi / 4 + Real.pi / 4 = Real.pi / 2 from by ring]
  rw [tracksDiag, hM, show Complex.exp ((0 : ℝ) * Complex.I) = 1 from by simp, one_smul,
    sub_self]
  exact norm_le_zero_iff.mpr rfl

/-- Appending two words adds their tracked global phases, diagonal phases, and error bounds. -/
theorem tracksDiag_append (W₁ W₂ : List (LocalQFTGate 1)) (β₁ β₂ p₁ p₂ E₁ E₂ : ℝ)
    (h₁ : tracksDiag W₁ β₁ p₁ E₁) (h₂ : tracksDiag W₂ β₂ p₂ E₂) :
    tracksDiag (W₁ ++ W₂) (β₁ + β₂) (p₁ + p₂) (E₁ + E₂) := by
  have hphase : (Complex.exp (β₂ * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) p₂)
      * (Complex.exp (β₁ * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) p₁)
      = Complex.exp (Complex.ofReal (β₁ + β₂) * Complex.I)
        • oneWirePhaseMatrix (wire0 : Fin 1) (p₁ + p₂) := by
    rw [smul_mul_assoc, Matrix.mul_smul, smul_smul, oneWirePhase_mul,
      show p₂ + p₁ = p₁ + p₂ from by ring]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsplit : localProgramMatrix (W₁ ++ W₂)
      - Complex.exp (Complex.ofReal (β₁ + β₂) * Complex.I)
        • oneWirePhaseMatrix (wire0 : Fin 1) (p₁ + p₂)
      = (localProgramMatrix W₂
          - Complex.exp (β₂ * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) p₂)
        * localProgramMatrix W₁
      + (Complex.exp (β₂ * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) p₂)
        * (localProgramMatrix W₁
          - Complex.exp (β₁ * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) p₁) := by
    rw [localProgramMatrix_append, ← hphase, Matrix.sub_mul, Matrix.mul_sub,
      sub_add_sub_cancel]
  rw [tracksDiag, hsplit]
  have hn1 : ‖(localProgramMatrix W₂
      - Complex.exp (β₂ * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) p₂)
      * localProgramMatrix W₁‖ ≤ E₂ :=
    le_trans (suffix_norm_le (D := _) (P := localProgramMatrix W₁)
      ((word_matrix_norm_eq_one W₁).le)) h₂
  have hn2 : ‖(Complex.exp (β₂ * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) p₂)
      * (localProgramMatrix W₁
        - Complex.exp (β₁ * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) p₁)‖ ≤ E₁ :=
    le_trans (prefix_norm_le (D := _)
      ((unitary_norm_eq_one (phaseSmul_unitary β₂ p₂)).le)) h₁
  exact (norm_add_le _ _).trans (by linarith)

/-- Taking a word power multiplies its tracked phases and error bound by the exponent. -/
theorem seedPow_tracksDiag (S : List (LocalQFTGate 1)) (α φ τ : ℝ)
    (h : tracksDiag S α φ τ) (j : ℕ) :
    tracksDiag (wordPow j S) ((j : ℝ) * α) ((j : ℝ) * φ) ((j : ℝ) * τ) := by
  have h0 := seedPow_track S α φ τ h j
  rw [tracksDiag]
  have hcast : Complex.exp (Complex.ofReal ((j : ℝ) * α) * Complex.I)
      = Complex.exp ((j : ℝ) * α * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hcast]
  exact h0

/-- Prepending an exact diagonal phase word adds its phase to the tracked diagonal phase without
increasing the error. -/
theorem tracksDiag_exact_prefix (T W : List (LocalQFTGate 1)) (pT β p E : ℝ)
    (hT : tracksDiag T 0 pT 0) (h : tracksDiag W β p E) :
    tracksDiag (T ++ W) (0 + β) (pT + p) (0 + E) :=
  tracksDiag_append T W 0 β pT p 0 E hT h

/-- Bounds a finite tail of the geometric series with ratio one quarter by the corresponding
infinite tail. -/
theorem sum_quarter_geom_range_le (a n : ℕ) :
    ∑ i ∈ Finset.range n, ((4 : ℝ) ⁻¹) ^ (a + i)
      ≤ ((4 : ℝ) ⁻¹) ^ a / (1 - (4 : ℝ) ⁻¹) := by
  have hsplit : ∑ i ∈ Finset.range n, ((4 : ℝ) ⁻¹) ^ (a + i)
      = ((4 : ℝ) ⁻¹) ^ a * ∑ i ∈ Finset.range n, ((4 : ℝ) ⁻¹) ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [← pow_add])
  have hinner : ∑ i ∈ Finset.range n, ((4 : ℝ) ⁻¹) ^ i ≤ 1 / (1 - (4 : ℝ) ⁻¹) := by
    rw [Finset.range_eq_Ico, geom_sum_Ico' (by norm_num : ((4 : ℝ) ⁻¹) ≠ 1) (Nat.zero_le n),
      div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 1 - (4 : ℝ) ⁻¹)]
    have hq : (0 : ℝ) ≤ ((4 : ℝ) ⁻¹) ^ n := pow_nonneg (by norm_num) n
    simp only [pow_zero]
    linarith
  rw [hsplit]
  calc ((4 : ℝ) ⁻¹) ^ a * ∑ i ∈ Finset.range n, ((4 : ℝ) ⁻¹) ^ i
      ≤ ((4 : ℝ) ⁻¹) ^ a * (1 / (1 - (4 : ℝ) ⁻¹)) :=
        mul_le_mul_of_nonneg_left hinner (pow_nonneg (by norm_num) a)
    _ = ((4 : ℝ) ⁻¹) ^ a / (1 - (4 : ℝ) ⁻¹) := by ring

/-- A ladder of phase-tracking seeds yields a fixed primitive approximation to a nonnegative
target angle with explicit length and accumulated error bounds. -/
theorem seedLadder (S : ℕ → List (LocalQFTGate 1)) (φ τ : ℕ → ℝ)
    (c C t R θ : ℝ) (L₀ L₁ e s₁ : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hR : 2 * C ≤ R) (hθ : 0 ≤ θ) (ht : 0 ≤ t) (hes : e ≤ s₁ + 1)
    (hθR : θ ≤ R * ((2 : ℝ) ⁻¹) ^ e)
    (hseed : ∀ s, e ≤ s → s ≤ s₁ →
      (∀ g ∈ S s, IsFixedPrim g) ∧ c * ((2 : ℝ) ⁻¹) ^ s ≤ φ s ∧ φ s ≤ C * ((2 : ℝ) ⁻¹) ^ s ∧
      τ s ≤ t * ((4 : ℝ) ⁻¹) ^ s ∧ (S s).length ≤ L₀ * s + L₁ ∧
      ∃ α, tracksDiag (S s) α (φ s) (τ s)) :
    ∃ W : List (LocalQFTGate 1), (∀ g ∈ W, IsFixedPrim g)
      ∧ W.length ≤ Nat.ceil (R / c) * ((s₁ + 1 - e) * (L₀ * s₁ + L₁))
      ∧ approxUpToPhase (localProgramMatrix W)
          (oneWirePhaseMatrix (wire0 : Fin 1) θ)
          (Nat.ceil (R / c) * t * (((4 : ℝ) ⁻¹) ^ e / (1 - (4 : ℝ) ⁻¹))
            + 3 * R * ((2 : ℝ) ⁻¹) ^ (s₁ + 1)) := by
  have hRnn : 0 ≤ R := le_trans (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) hR
  have key : ∀ n : ℕ, e + n ≤ s₁ + 1 → ∃ W : List (LocalQFTGate 1),
      (∀ g ∈ W, IsFixedPrim g)
      ∧ W.length ≤ Nat.ceil (R / c) * ∑ i ∈ Finset.range n, (L₀ * (e + i) + L₁)
      ∧ ∃ β p E, tracksDiag W β p E ∧ p ≤ θ ∧ θ - p ≤ R * ((2 : ℝ) ⁻¹) ^ (e + n)
        ∧ E ≤ Nat.ceil (R / c) * t * ∑ i ∈ Finset.range n, ((4 : ℝ) ⁻¹) ^ (e + i) := by
    intro n
    induction n with
    | zero =>
        intro _
        refine ⟨[], by simp, by simp, 0, 0, 0, tracksDiag_nil, hθ, ?_, ?_⟩
        · rw [Nat.add_zero, sub_zero]
          exact hθR
        · rw [Finset.range_zero, Finset.sum_empty]
          norm_num
    | succ n ih =>
        intro hle
        obtain ⟨W, hWlegal, hWlen, β, p, E, hWtrack, hpθ, hres, hE⟩ := ih (by omega)
        set s := e + n with hs
        obtain ⟨hSlegal, hφlo, hφhi, hτhi, hSlen, α, hα⟩ := hseed s (by omega) (by omega)
        have hφpos : 0 < φ s :=
          lt_of_lt_of_le (mul_pos hc (pow_pos (by norm_num) _)) hφlo
        have hrnn : 0 ≤ θ - p := sub_nonneg.mpr hpθ
        obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = Nat.floor ((θ - p) / φ s) := ⟨_, rfl⟩
        have hjle : (j : ℝ) ≤ (θ - p) / φ s := by
          rw [hjdef]
          exact Nat.floor_le (div_nonneg hrnn hφpos.le)
        have hjφle : (j : ℝ) * φ s ≤ θ - p := by
          refine le_trans (mul_le_mul_of_nonneg_right hjle hφpos.le) ?_
          rw [div_mul_cancel₀ _ hφpos.ne']
        have hjlt : (θ - p) / φ s < (j : ℝ) + 1 := by
          rw [hjdef]
          exact Nat.lt_floor_add_one _
        have hreslt : θ - p - (j : ℝ) * φ s < φ s := by
          have h1 : θ - p < ((j : ℝ) + 1) * φ s := by
            rw [div_lt_iff₀ hφpos] at hjlt
            linarith
          linarith
        have hp'le : p + (j : ℝ) * φ s ≤ θ := by linarith
        have hjJ : j ≤ Nat.ceil (R / c) := by
          have h2 : (θ - p) / φ s ≤ R / c := by
            have hmul : (θ - p) * c ≤ R * φ s := by
              calc (θ - p) * c ≤ R * ((2 : ℝ) ⁻¹) ^ s * c :=
                    mul_le_mul_of_nonneg_right hres hc.le
                _ = R * (c * ((2 : ℝ) ⁻¹) ^ s) := by ring
                _ ≤ R * φ s := mul_le_mul_of_nonneg_left hφlo hRnn
            rw [le_div_iff₀ hc, div_mul_eq_mul_div, div_le_iff₀ hφpos]
            exact hmul
          have h3 : R / c ≤ (Nat.ceil (R / c) : ℝ) := Nat.le_ceil (R / c)
          exact Nat.cast_le.mp ((hjle.trans h2).trans h3)
        have hmem : s ∉ Finset.Ico e s := by simp
        refine ⟨W ++ wordPow j (S s),
          fun g hg => by
            rcases List.mem_append.mp hg with hg | hg
            · exact hWlegal g hg
            · exact wordPow_legal _ _ hSlegal g hg,
          ?_, β + (j : ℝ) * α, p + (j : ℝ) * φ s, E + (j : ℝ) * τ s,
          tracksDiag_append W (wordPow j (S s)) β ((j : ℝ) * α) p ((j : ℝ) * φ s) E
            ((j : ℝ) * τ s) hWtrack
            (seedPow_tracksDiag (S s) α (φ s) (τ s) hα _),
          hp'le, ?_, ?_⟩
        · rw [List.length_append, wordPow_length, Finset.sum_range_succ]
          have hterm : j * (S s).length ≤ Nat.ceil (R / c) * (L₀ * s + L₁) :=
            Nat.mul_le_mul hjJ hSlen
          calc W.length + j * (S s).length
              ≤ Nat.ceil (R / c) * ∑ i ∈ Finset.range n, (L₀ * (e + i) + L₁)
                + Nat.ceil (R / c) * (L₀ * s + L₁) := add_le_add hWlen hterm
            _ = Nat.ceil (R / c) * (∑ i ∈ Finset.range n, (L₀ * (e + i) + L₁)
                + (L₀ * s + L₁)) := by ring
        · have hR' : C * ((2 : ℝ) ⁻¹) ^ s ≤ R * ((2 : ℝ) ⁻¹) ^ (s + 1) := by
            have hsplit : R * ((2 : ℝ) ⁻¹) ^ (s + 1)
                = (R * ((2 : ℝ) ⁻¹) ^ s) * (2 : ℝ) ⁻¹ := by
              rw [pow_succ]
              ring
            rw [hsplit]
            calc C * ((2 : ℝ) ⁻¹) ^ s = (2 * C * ((2 : ℝ) ⁻¹) ^ s) * (2 : ℝ) ⁻¹ := by ring
              _ ≤ (R * ((2 : ℝ) ⁻¹) ^ s) * (2 : ℝ) ⁻¹ := by
                  refine mul_le_mul_of_nonneg_right ?_ (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ⁻¹)
                  exact mul_le_mul_of_nonneg_right hR (pow_nonneg (by norm_num) s)
          have hrew : θ - (p + (j : ℝ) * φ s) = (θ - p) - (j : ℝ) * φ s := by ring
          rw [hrew]
          exact le_trans (le_of_lt hreslt) (le_trans hφhi hR')
        · rw [Finset.sum_range_succ]
          have hτnn : 0 ≤ τ s := le_trans (norm_nonneg _) hα
          have hJnn : (0 : ℝ) ≤ Nat.ceil (R / c) := Nat.cast_nonneg _
          have hterm2 : (j : ℝ) * τ s ≤ Nat.ceil (R / c) * (t * ((4 : ℝ) ⁻¹) ^ s) :=
            mul_le_mul (Nat.cast_le.mpr hjJ) hτhi hτnn hJnn
          calc E + (j : ℝ) * τ s
              ≤ Nat.ceil (R / c) * t * ∑ i ∈ Finset.range n, ((4 : ℝ) ⁻¹) ^ (e + i)
                + Nat.ceil (R / c) * (t * ((4 : ℝ) ⁻¹) ^ s) := add_le_add hE hterm2
            _ = Nat.ceil (R / c) * t * (∑ i ∈ Finset.range n, ((4 : ℝ) ⁻¹) ^ (e + i)
                + ((4 : ℝ) ⁻¹) ^ s) := by ring
  obtain ⟨W, hWlegal, hWlen, β, p, E, hWtrack, hpθ, hres, hE⟩ :=
    key (s₁ + 1 - e) (by omega)
  rw [tracksDiag] at hWtrack
  rw [show e + (s₁ + 1 - e) = s₁ + 1 from by omega] at hres
  have hcard : ∑ i ∈ Finset.range (s₁ + 1 - e), (L₀ * (e + i) + L₁)
      ≤ (s₁ + 1 - e) * (L₀ * s₁ + L₁) := by
    have hmono : ∀ i ∈ Finset.range (s₁ + 1 - e), L₀ * (e + i) + L₁ ≤ L₀ * s₁ + L₁ := by
      intro i hi
      have hi1 : e + i ≤ s₁ := by
        have := Finset.mem_range.mp hi
        omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left L₀ hi1) L₁
    calc ∑ i ∈ Finset.range (s₁ + 1 - e), (L₀ * (e + i) + L₁)
        ≤ ∑ _i ∈ Finset.range (s₁ + 1 - e), (L₀ * s₁ + L₁) := Finset.sum_le_sum hmono
      _ = (s₁ + 1 - e) * (L₀ * s₁ + L₁) := by
          rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
  have hE' : E ≤ Nat.ceil (R / c) * t * (((4 : ℝ) ⁻¹) ^ e / (1 - (4 : ℝ) ⁻¹)) := by
    refine le_trans hE ?_
    exact mul_le_mul_of_nonneg_left (sum_quarter_geom_range_le e (s₁ + 1 - e))
      (mul_nonneg (Nat.cast_nonneg _) ht)
  refine ⟨W, hWlegal, le_trans hWlen (Nat.mul_le_mul_left (Nat.ceil (R / c)) hcard), β, ?_⟩
  have hsplit : localProgramMatrix W
      - Complex.exp (β * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) θ
      = (localProgramMatrix W
          - Complex.exp (β * Complex.I) • oneWirePhaseMatrix (wire0 : Fin 1) p)
        + Complex.exp (β * Complex.I)
          • (oneWirePhaseMatrix (wire0 : Fin 1) p
            - oneWirePhaseMatrix (wire0 : Fin 1) θ) := by
    rw [smul_sub]
    exact (sub_add_sub_cancel _ _ _).symm
  have h2 : ‖Complex.exp (β * Complex.I)
      • (oneWirePhaseMatrix (wire0 : Fin 1) p - oneWirePhaseMatrix (wire0 : Fin 1) θ)‖
      ≤ 3 * R * ((2 : ℝ) ⁻¹) ^ (s₁ + 1) := by
    have hunit : ‖Complex.exp (β * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (β * Complex.I).re = 0 := by simp
      rw [hre]
      simp
    rw [norm_smul, hunit, one_mul,
      show (3 : ℝ) * R * ((2 : ℝ) ⁻¹) ^ (s₁ + 1)
        = 3 * (R * ((2 : ℝ) ⁻¹) ^ (s₁ + 1)) from by ring]
    refine le_trans (oneWirePhase_dist p θ) ?_
    have hpθ' : |p - θ| ≤ R * ((2 : ℝ) ⁻¹) ^ (s₁ + 1) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hpθ)]
      linarith
    exact mul_le_mul_of_nonneg_left hpθ' (by norm_num)
  rw [hsplit]
  exact (norm_add_le _ _).trans (by linarith)

/-- A phase-tracking seed ladder satisfying the stated error budget yields a bounded-length
approximation to the dyadic target phase at the requested tolerance. -/
theorem middleWindow_ladderSlice (S : ℕ → List (LocalQFTGate 1)) (φ τ : ℕ → ℝ)
    (c C t R : ℝ) (L₀ L₁ e k s₁ : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hR : 2 * C ≤ R) (hRπ : 2 * Real.pi ≤ R) (ht : 0 ≤ t)
    (hes : e ≤ s₁ + 1)
    (hnum : Nat.ceil (R / c) * t * (((4 : ℝ) ⁻¹) ^ e / (1 - (4 : ℝ) ⁻¹))
      + 3 * R * ((2 : ℝ) ⁻¹) ^ (s₁ + 1) ≤ ((2 : ℝ) ⁻¹) ^ k)
    (hseed : ∀ s, e ≤ s → s ≤ s₁ →
      (∀ g ∈ S s, IsFixedPrim g) ∧ c * ((2 : ℝ) ⁻¹) ^ s ≤ φ s ∧ φ s ≤ C * ((2 : ℝ) ⁻¹) ^ s ∧
      τ s ≤ t * ((4 : ℝ) ⁻¹) ^ s ∧ (S s).length ≤ L₀ * s + L₁ ∧
      ∃ α, tracksDiag (S s) α (φ s) (τ s)) :
    ∃ W : List (LocalQFTGate 1), (∀ g ∈ W, IsFixedPrim g)
      ∧ W.length ≤ Nat.ceil (R / c) * ((s₁ + 1 - e) * (L₀ * s₁ + L₁))
      ∧ approxUpToPhase (localProgramMatrix W)
          (oneWirePhaseMatrix (wire0 : Fin 1) (2 * Real.pi * ((2 : ℝ) ⁻¹) ^ e))
          (tolerance k) := by
  obtain ⟨W, hlegal, hlen, happrox⟩ :=
    seedLadder S φ τ c C t R (2 * Real.pi * ((2 : ℝ) ⁻¹) ^ e) L₀ L₁ e s₁ hc hC hR
      (by positivity) ht hes
      (mul_le_mul_of_nonneg_right hRπ (pow_nonneg (by norm_num) _)) hseed
  obtain ⟨ψ, hψ⟩ := happrox
  exact ⟨W, hlegal, hlen, ψ, le_trans hψ hnum⟩

/-- Two consecutive Hadamard primitives have the identity program matrix. -/
theorem hh_word_exact : localProgramMatrix [prim1 0, prim1 0] = 1 := by
  change localProgramMatrix ([prim1 0] ++ [prim1 0]) = 1
  rw [localProgramMatrix_append, hWord_matrix, hWord_mul]

/-- A positive T primitive followed by its adjoint has the identity program matrix. -/
theorem t_adj_word_exact : localProgramMatrix [prim1 6, prim1 5] = 1 := by
  rw [prim1_five, prim1_six, localProgramMatrix_cons, localProgramMatrix_cons, localProgramMatrix_nil,
    Matrix.one_mul, localGateMatrix_cp_self, localGateMatrix_cp_self, oneWirePhase_mul,
    dyadicPhaseAngle_three_true, dyadicPhaseAngle_three_false,
    show -(Real.pi / 4) + Real.pi / 4 = 0 from by ring, oneWirePhase_zero]

/-- The auxiliary words indexed by zero and forty-one at length `n` plus two have the same
program matrix. -/
theorem wordOfAux_collision (n : ℕ) :
    localProgramMatrix (wordOfAux (n + 2) 0) = localProgramMatrix (wordOfAux (n + 2) 41) := by
  have h0 : wordOfAux (n + 2) 0 = [prim1 0, prim1 0] ++ wordOfAux n 0 := by
    simp only [wordOfAux]
    rfl
  have h41 : wordOfAux (n + 2) 41 = [prim1 6, prim1 5] ++ wordOfAux n 0 := by
    simp only [wordOfAux]
    rfl
  rw [h0, h41, localProgramMatrix_append, localProgramMatrix_append, hh_word_exact, t_adj_word_exact,
    Matrix.mul_one]

/-- The quotient word formed from the two specified colliding auxiliary words has the identity
program matrix. -/
theorem collision_quotient_exact (n : ℕ) :
    localProgramMatrix (localProgramAdjoint (wordOfAux (n + 2) 41) ++ wordOfAux (n + 2) 0) = 1 := by
  rw [localProgramMatrix_append, localProgramAdjoint_matrix, wordOfAux_collision,
    word_matrix_mul_conj_self]

/-- The stated geometric ladder error budget is at most the requested tolerance. -/
theorem precise_ladder_budget (e k : ℕ) :
    (8 : ℝ) * tolerance (k + 5) * (((4 : ℝ)⁻¹) ^ e / (1 - (4 : ℝ)⁻¹))
      + 3 * 8 * ((2 : ℝ)⁻¹) ^ (k + 6) ≤ tolerance k := by
  have hfour : ((4 : ℝ)⁻¹) ^ e ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hnonneg : (0 : ℝ) ≤ ((2 : ℝ)⁻¹) ^ k := pow_nonneg (by norm_num) _
  have hm := mul_nonneg hnonneg (sub_nonneg.mpr hfour)
  simp only [tolerance, pow_add] at ⊢
  norm_num at ⊢
  nlinarith

/-- Seeds with the stated dyadic phase, error, and length bounds yield an explicit
bounded-length approximation to the target dyadic phase at the requested tolerance. -/
theorem precise_middle_slice
    (S : ℕ → List (LocalQFTGate 1)) (φ τ : ℕ → ℝ) (A B D e k : ℕ)
    (he : e ≤ k + 6)
    (hseed : ∀ s, e ≤ s → s ≤ k + 5 →
      (∀ g ∈ S s, IsFixedPrim g) ∧ ((2 : ℝ)⁻¹) ^ s ≤ φ s ∧
      φ s ≤ 4 * ((2 : ℝ)⁻¹) ^ s ∧
      τ s ≤ tolerance (k + 5) * ((4 : ℝ)⁻¹) ^ s ∧
      (S s).length ≤ A * s + (B * k + D) ∧
      ∃ α, tracksDiag (S s) α (φ s) (τ s)) :
    ∃ W : List (LocalQFTGate 1), (∀ g ∈ W, IsFixedPrim g) ∧
      W.length ≤ 8 * ((k + 6 - e) * (A * (k + 5) + (B * k + D))) ∧
      approxUpToPhase (localProgramMatrix W)
        (oneWirePhaseMatrix (wire0 : Fin 1) (2 * Real.pi * ((2 : ℝ)⁻¹) ^ e)) (tolerance k) := by
  have hnum : Nat.ceil ((8 : ℝ) / 1) * tolerance (k + 5)
        * (((4 : ℝ)⁻¹) ^ e / (1 - (4 : ℝ)⁻¹))
      + 3 * 8 * ((2 : ℝ)⁻¹) ^ ((k + 5) + 1) ≤ ((2 : ℝ)⁻¹) ^ k := by
    have h := precise_ladder_budget e k
    simpa [tolerance, Nat.add_assoc] using! h
  obtain ⟨W, hlegal, hlen, happrox⟩ :=
    middleWindow_ladderSlice S φ τ 1 4 (tolerance (k + 5)) 8 A (B * k + D) e k (k + 5)
      (by norm_num) (by norm_num) (by norm_num)
      (by have hp := Real.pi_lt_four; linarith) (tolerance_nonneg _) (by omega)
      hnum (by
        intro s hs hs'
        have h := hseed s hs hs'
        simpa using! h)
  refine ⟨W, hlegal, ?_, happrox⟩
  simpa [Nat.add_assoc] using! hlen

open Qatlib
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo (tPhase)
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2 QuantumInfo.CliffordT

def oneWireEquiv : Reg 1 ≃ Fin 2 := bitVecEquiv 1

/-- The inverse one-wire equivalence sends zero to the constantly false register. -/
theorem oneWireEquiv_symm_zero : oneWireEquiv.symm 0 = fun _ => false := by decide

/-- The inverse one-wire equivalence sends one to the constantly true register. -/
theorem oneWireEquiv_symm_one : oneWireEquiv.symm 1 = fun _ => true := by decide

/-- Reindexing the primitive Hadamard word gives `hGateM`. -/
theorem reindex_h : relabelGate oneWireEquiv (localProgramMatrix [prim1 0]) = hGateM := by
  rw [hWord_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, oneWireEquiv_symm_zero,
      oneWireEquiv_symm_one, h1_entries, Qatlib.Foundations.PureStateMath.Hadamard, hGateM, wire0]

/-- Reindexing the positive T word gives `tGateM`. -/
theorem reindex_t : relabelGate oneWireEquiv (localProgramMatrix [prim1 6]) = tGateM := by
  rw [prim1_six, cp_word_matrix, dyadicPhaseAngle_three_false]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, oneWireEquiv_symm_zero,
      oneWireEquiv_symm_one, oneWirePhaseMatrix, Matrix.diagonal_apply, basis_ne, basis_ne', tGateM, tPhase, wire0]

/-- Reindexing one-wire matrices preserves multiplication. -/
theorem reindex_mul (A B : Matrix (Reg 1) (Reg 1) ℂ) :
    relabelGate oneWireEquiv (A * B)
      = relabelGate oneWireEquiv A * relabelGate oneWireEquiv B := by
  exact map_mul (Matrix.reindexAlgEquiv ℂ ℂ oneWireEquiv) A B

/-- Reindexing one-wire matrices preserves natural powers. -/
theorem reindex_pow (A : Matrix (Reg 1) (Reg 1) ℂ) (n : ℕ) :
    relabelGate oneWireEquiv (A ^ n) = (relabelGate oneWireEquiv A) ^ n := by
  exact map_pow (Matrix.reindexAlgEquiv ℂ ℂ oneWireEquiv) A n

def skLetter (i : Fin 3) : List (LocalQFTGate 1) :=
  ![[prim1 0], [prim1 6], wordPow 7 [prim1 6]] i

def skWord : List (Fin 3) → List (LocalQFTGate 1)
  | [] => []
  | i :: is => skWord is ++ skLetter i

/-- Every gate in a Solovay-Kitaev letter word is a fixed primitive. -/
theorem skLetter_legal (i : Fin 3) : ∀ g ∈ skLetter i, IsFixedPrim g := by
  fin_cases i
  · intro g hg
    simp [skLetter] at hg
    subst g
    exact prim1_legal 0
  · intro g hg
    simp [skLetter] at hg
    subst g
    exact prim1_legal 6
  · have hT : ∀ g ∈ [prim1 6], IsFixedPrim g := by
      intro g hg
      simp at hg
      subst g
      exact prim1_legal 6
    simpa [skLetter] using! wordPow_legal 7 [prim1 6] hT

/-- Each Solovay-Kitaev letter word has length at most seven. -/
theorem skLetter_length (i : Fin 3) : (skLetter i).length ≤ 7 := by
  fin_cases i <;> simp [skLetter, wordPow_length]

/-- Reindexing a Solovay-Kitaev letter word's matrix gives its corresponding `ctGen` generator. -/
theorem skLetter_matrix (i : Fin 3) :
    relabelGate oneWireEquiv (localProgramMatrix (skLetter i)) = ctGen i := by
  fin_cases i
  · simpa [skLetter, ctGen] using! reindex_h
  · simpa [skLetter, ctGen] using! reindex_t
  · have ht : relabelGate oneWireEquiv (localGateMatrix (prim1 6)) = tGateM := by
      simpa using! reindex_t
    simp [skLetter, ctGen, wordPow_matrix, reindex_pow, ht]

/-- Every gate in a Solovay-Kitaev word is a fixed primitive. -/
theorem skWord_legal (w : List (Fin 3)) : ∀ g ∈ skWord w, IsFixedPrim g := by
  induction w with
  | nil => simp [skWord]
  | cons i is ih =>
      intro g hg
      simp only [skWord, List.mem_append] at hg
      rcases hg with hg | hg
      · exact ih g hg
      · exact skLetter_legal i g hg

/-- A Solovay-Kitaev word has length at most seven times its index word's length. -/
theorem skWord_length (w : List (Fin 3)) : (skWord w).length ≤ 7 * w.length := by
  induction w with
  | nil => simp [skWord]
  | cons i is ih =>
      simp only [skWord, List.length_append, List.length_cons]
      have h := skLetter_length i
      omega

/-- Reindexing a Solovay-Kitaev word's matrix gives `ctEval` of its index word. -/
theorem skWord_matrix (w : List (Fin 3)) :
    relabelGate oneWireEquiv (localProgramMatrix (skWord w)) = ctEval w := by
  induction w with
  | nil =>
      simp only [skWord, localProgramMatrix_nil, ctEval_nil]
      change (Matrix.reindexAlgEquiv ℂ ℂ oneWireEquiv) 1 = 1
      exact map_one _
  | cons i is ih =>
      rw [skWord, localProgramMatrix_append, reindex_mul, skLetter_matrix, ih, ctEval_cons]

/-- Reindexing the Z rotation by negative half an angle gives the Euler Z rotation matrix for
that angle. -/
theorem reindex_rotZ (θ : ℝ) :
    relabelGate oneWireEquiv (rotZ (-θ / 2)) = QuantumInfo.Euler.rzMat θ := by
  rw [QuantumInfo.Euler.rzMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, oneWireEquiv_symm_zero,
      oneWireEquiv_symm_one, rotZ, QuantumInfo.Euler.expI, wire0, basis_ne, basis_ne'] <;>
    congr 1 <;> push_cast <;> ring

/-- An approximation to the reindexed Euler Z rotation yields the same-error approximation up to
phase by the corresponding Solovay-Kitaev word. -/
theorem skWord_phase_approx (θ ε : ℝ) (w : List (Fin 3))
    (h : ‖QuantumInfo.Euler.rzMat θ - ctEval w‖ ≤ ε) :
    approxUpToPhase (localProgramMatrix (skWord w))
      (oneWirePhaseMatrix (wire0 : Fin 1) θ) ε := by
  have hrelabel := Qatlib.Foundations.PureStateMath.BornBridge.l2_norm_relabelGate_sub oneWireEquiv
    (rotZ (-θ / 2)) (localProgramMatrix (skWord w))
  rw [reindex_rotZ, skWord_matrix] at hrelabel
  have hrot : ‖localProgramMatrix (skWord w) - rotZ (-θ / 2)‖ ≤ ε := by
    rw [norm_sub_rev, ← hrelabel]
    exact h
  have happ : approxUpToPhase (localProgramMatrix (skWord w)) (rotZ (-θ / 2)) ε := by
    refine ⟨0, ?_⟩
    simpa using! hrot
  rw [show wire0 = (0 : Fin 1) from Subsingleton.elim _ _, oneWirePhase_smul_rotZ]
  exact (approxUpToPhase_smul_right (θ / 2)).mpr happ

/-- Bounds the stated polylogarithmic expression of exponent at most four by an explicit quartic
polynomial in the precision. -/
theorem polylog_quartic_bound (K α : ℝ) (p k : ℕ)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hα4 : α ≤ 4) :
    K * (Real.log ((((2 : ℝ)⁻¹) ^ (k + p))⁻¹)) ^ α
      ≤ (Nat.ceil K : ℝ) * (((p + 1 : ℕ) : ℝ) ^ 4) * (((k + 1 : ℕ) : ℝ) ^ 4) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hinv : (((2 : ℝ)⁻¹) ^ (k + p))⁻¹ = (2 : ℝ) ^ (k + p) := by simp [inv_pow]
  rw [hinv, Real.log_pow]
  have hkpn : (0 : ℝ) ≤ ((k + p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hx0 : 0 ≤ ((k + p : ℕ) : ℝ) * Real.log 2 := mul_nonneg hkpn hlog
  have hx1 : ((k + p : ℕ) : ℝ) * Real.log 2 ≤ ((p + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    have h1 : ((k + p : ℕ) : ℝ) * Real.log 2 ≤ ((k + p : ℕ) : ℝ) := by nlinarith
    have h2 : ((k + p : ℕ) : ℝ) ≤ ((p + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (Nat.cast_nonneg (α := ℝ) p)]
    linarith
  have hbase : 1 ≤ ((p + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) p,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (Nat.cast_nonneg (α := ℝ) p)]
  have hpow1 := Real.rpow_le_rpow hx0 hx1 hα
  have hpow2 := Real.rpow_le_rpow_of_exponent_le hbase hα4
  have hpow : (((k + p : ℕ) : ℝ) * Real.log 2) ^ α
      ≤ (((p + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) ^ (4 : ℕ) := by
    have h2 : (((p + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) ^ (4 : ℝ)
        = (((p + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) ^ (4 : ℕ) := by
      exact Real.rpow_natCast _ 4
    rw [h2] at hpow2
    exact hpow1.trans hpow2
  calc K * (((k + p : ℕ) : ℝ) * Real.log 2) ^ α
      ≤ (Nat.ceil K : ℝ) * ((((p + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) ^ (4 : ℕ)) :=
        mul_le_mul (Nat.le_ceil K) hpow (Real.rpow_nonneg hx0 _) (Nat.cast_nonneg _)
    _ = (Nat.ceil K : ℝ) * (((p + 1 : ℕ) : ℝ) ^ 4) * (((k + 1 : ℕ) : ℝ) ^ 4) := by
        rw [mul_pow]
        ring

/-- At every positive precision, each one-wire phase admits a fixed primitive approximation
within the requested tolerance, with a uniform quartic length bound in the precision
incremented by one. -/
theorem exists_sk_word_uniform :
    ∃ C : ℕ, ∀ (θ : ℝ) (k : ℕ), 1 ≤ k →
      ∃ W : List (LocalQFTGate 1), (∀ g ∈ W, IsFixedPrim g) ∧
        W.length ≤ C * (k + 1) ^ 4 ∧
        approxUpToPhase (localProgramMatrix W) (oneWirePhaseMatrix (wire0 : Fin 1) θ)
          (tolerance k) := by
  obtain ⟨K, e, hK, he, hbase⟩ := exists_word_approx_polylog
  obtain ⟨p, hp⟩ := exists_pow_lt_of_lt_one he (show ((2 : ℝ)⁻¹) < 1 by norm_num)
  refine ⟨7 * Nat.ceil K * (p + 1) ^ 4, ?_⟩
  intro θ k hk
  have hpowk : ((2 : ℝ)⁻¹) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpowp : 0 ≤ ((2 : ℝ)⁻¹) ^ p := pow_nonneg (by norm_num) _
  have hepsle : tolerance (k + p) ≤ e := by
    unfold tolerance
    rw [pow_add]
    exact (mul_le_of_le_one_left hpowp hpowk).trans (le_of_lt hp)
  have hepspos : 0 < tolerance (k + p) := by
    unfold tolerance
    positivity
  have htol : tolerance (k + p) ≤ tolerance k := by
    unfold tolerance
    rw [pow_add]
    have hpone : ((2 : ℝ)⁻¹) ^ p ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) k) hpone
  have hU : QuantumInfo.Euler.rzMat θ ∈ su2Set := by
    refine ⟨QuantumInfo.Euler.rzMat_mem_unitaryGroup θ, ?_⟩
    exact axisRot_det (by norm_num) θ
  obtain ⟨w, hw, hlen⟩ := hbase (tolerance (k + p)) hepspos hepsle _ hU
  refine ⟨skWord w, skWord_legal w, ?_, ?_⟩
  · have hpoly := polylog_quartic_bound K skExponent p k hK.le skExponent_pos.le
        (le_of_lt skExponent_lt_four)
    have hreal : ((skWord w).length : ℝ) ≤
        ((7 * Nat.ceil K * (p + 1) ^ 4 * (k + 1) ^ 4 : ℕ) : ℝ) := by
      have hW : ((skWord w).length : ℝ) ≤ 7 * (w.length : ℝ) := by
        exact_mod_cast skWord_length w
      have hlen' : (w.length : ℝ) ≤ K *
          Real.log ((((2 : ℝ)⁻¹) ^ (k + p))⁻¹) ^ skExponent := by
        simpa [tolerance] using! hlen
      calc ((skWord w).length : ℝ) ≤ 7 * (w.length : ℝ) := hW
        _ ≤ 7 * (K * Real.log ((((2 : ℝ)⁻¹) ^ (k + p))⁻¹) ^ skExponent) :=
          mul_le_mul_of_nonneg_left hlen' (by norm_num)
        _ ≤ 7 * ((Nat.ceil K : ℝ) * (((p + 1 : ℕ) : ℝ) ^ 4) *
              (((k + 1 : ℕ) : ℝ) ^ 4)) := mul_le_mul_of_nonneg_left hpoly (by norm_num)
        _ = ((7 * Nat.ceil K * (p + 1) ^ 4 * (k + 1) ^ 4 : ℕ) : ℝ) := by
          push_cast
          ring
    exact_mod_cast hreal
  · obtain ⟨α, hα⟩ := skWord_phase_approx θ (tolerance (k + p)) w hw
    exact ⟨α, hα.trans htol⟩

/-- There exists a scalar phase synthesizer with a uniform quartic bound in the sum of exponent
and precision. -/
theorem sk_scalar_synthesizer_exists :
    ∃ S : ScalarPhaseSynthesizer, ∃ C : ℕ, ∀ (neg : Bool) (e k : ℕ), 4 ≤ e → 1 ≤ k →
      (S.emit neg e k).length ≤ C * (e + k) ^ 4 := by
  classical
  obtain ⟨C, hC⟩ := exists_sk_word_uniform
  let emit : Bool → ℕ → ℕ → List (LocalQFTGate 1) := fun neg e k =>
    if hk : 1 ≤ k then Classical.choose (hC (dyadicPhaseAngle e neg) k hk) else []
  have hbounded : ∀ (neg : Bool) (e k : ℕ), 4 ≤ e → 1 ≤ k →
      (emit neg e k).length ≤ C * (e + k) ^ 4 := by
    intro neg e k he hk
    have hh : emit neg e k = Classical.choose (hC (dyadicPhaseAngle e neg) k hk) := by
      simp [emit, hk]
    rw [hh]
    have hlen := (Classical.choose_spec (hC (dyadicPhaseAngle e neg) k hk)).2.1
    exact hlen.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) 4))
  refine ⟨{ emit := emit, legal := ?_, correct := ?_, bounded := ⟨C, 4, hbounded⟩ }, C, hbounded⟩
  · intro neg e k g hg
    by_cases hk : 1 ≤ k
    · have hh : emit neg e k = Classical.choose (hC (dyadicPhaseAngle e neg) k hk) := by
        simp [emit, hk]
      rw [hh] at hg
      exact (Classical.choose_spec (hC (dyadicPhaseAngle e neg) k hk)).1 g hg
    · simp [emit, hk] at hg
  · intro neg e k he hk
    have hh : emit neg e k = Classical.choose (hC (dyadicPhaseAngle e neg) k hk) := by
      simp [emit, hk]
    rw [hh]
    have hc := (Classical.choose_spec (hC (dyadicPhaseAngle e neg) k hk)).2.2
    simpa [wire0] using! hc

noncomputable def skScalarSynthesizer : ScalarPhaseSynthesizer :=
  Classical.choose sk_scalar_synthesizer_exists

/-- The chosen Solovay-Kitaev scalar synthesizer has a uniform quartic length bound in exponent
plus precision. -/
theorem sk_scalar_quartic : ∃ C : ℕ, ∀ (neg : Bool) (e k : ℕ), 4 ≤ e → 1 ≤ k →
    (skScalarSynthesizer.emit neg e k).length ≤ C * (e + k) ^ 4 :=
  Classical.choose_spec sk_scalar_synthesizer_exists

noncomputable def skGateCoefficient : ℕ := Classical.choose sk_scalar_quartic

/-- Bounds the chosen scalar synthesizer's output length by `skGateCoefficient` times the fourth
power of the sum of exponent and precision. -/
theorem sk_scalar_quartic_bound (neg : Bool) (e k : ℕ) (he : 4 ≤ e) (hk : 1 ≤ k) :
    (skScalarSynthesizer.emit neg e k).length ≤ skGateCoefficient * (e + k) ^ 4 :=
  Classical.choose_spec sk_scalar_quartic neg e k he hk

/-- The Solovay-Kitaev scalar synthesizer emits a nonempty word in the stated middle range of
exponents and precisions. -/
theorem sk_scalar_nonempty {e k : ℕ} (neg : Bool) (he : 4 ≤ e) (hk : e ≤ k + 1)
    (hkk : 1 ≤ k) : skScalarSynthesizer.emit neg e k ≠ [] := by
  intro hempty
  obtain ⟨α, hα⟩ := skScalarSynthesizer.correct neg e k he hkk
  rw [hempty, localProgramMatrix_nil] at hα
  have hfar := Qatlib.Concepts.MatrixAccess.RitzPipeline.middleWindow_empty_far
    (w := 1) (a := wire0) (c := wire0) e k neg he hk hkk α
  rw [localGateMatrix_cp_self] at hfar
  exact (not_lt_of_ge hα) hfar

/-- Every positive-precision request is accepted by the transported Solovay-Kitaev synthesizer's
next segment. -/
theorem frontier1 :
    ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k →
      Accepts w g k (nextSegment (transportSynth skScalarSynthesizer) w g k) :=
  Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis.frontier1 skScalarSynthesizer

/-- The transported Solovay-Kitaev synthesizer's next segment uses at most one extra wire. -/
theorem frontier1_ancilla (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    (nextSegment (transportSynth skScalarSynthesizer) w g k).width ≤ w + 1 :=
  Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis.frontier1_ancilla skScalarSynthesizer w g k

/-- Bounds the transported Solovay-Kitaev segment length by the stated explicit fifth-degree
polynomial in request size. -/
theorem frontier1_explicitLedger (w : ℕ) (g : LocalQFTGate w) (k : ℕ) (hk : 1 ≤ k) :
    (nextSegment (transportSynth skScalarSynthesizer) w g k).word.length
      ≤ (23 + skGateCoefficient * 16) * (requestSize w g k) ^ 5 := by
  simpa using! Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis.frontier1_ledger
    skScalarSynthesizer skGateCoefficient 4 sk_scalar_quartic_bound w g k hk

/-- The transported Solovay-Kitaev segment lengths possess a uniform fifth-degree polynomial bound
in request size. -/
theorem frontier1_polynomial :
    ∃ C : ℕ, ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k →
      (nextSegment (transportSynth skScalarSynthesizer) w g k).word.length
        ≤ (23 + C * 16) * (requestSize w g k) ^ 5 := by
  exact ⟨skGateCoefficient, frontier1_explicitLedger⟩

open Qatlib
open Qatlib

def isOneWireHT (g : LocalQFTGate 1) : Prop := g = prim1 0 ∨ g = prim1 6

/-- Every gate in a Solovay-Kitaev letter word satisfies `isOneWireHT`. -/
theorem skLetter_onlyHT (i : Fin 3) : ∀ g ∈ skLetter i, isOneWireHT g := by
  fin_cases i <;> intro g hg <;> simp [skLetter, wordPow, isOneWireHT] at hg ⊢ <;> aesop

/-- Every gate in a Solovay-Kitaev word satisfies `isOneWireHT`. -/
theorem skWord_onlyHT (w : List (Fin 3)) : ∀ g ∈ skWord w, isOneWireHT g := by
  induction w with
  | nil => simp [skWord]
  | cons i is ih =>
      intro g hg
      simp only [skWord, List.mem_append] at hg
      rcases hg with hg | hg
      · exact ih g hg
      · exact skLetter_onlyHT i g hg

/-- Every one-wire phase has a Solovay-Kitaev index word giving the requested approximation with
a uniform quartic gate-length bound. -/
theorem exists_sk_indices_uniform :
    ∃ C : ℕ, ∀ (θ : ℝ) (k : ℕ), 1 ≤ k →
      ∃ w : List (Fin 3), (skWord w).length ≤ C * (k + 1) ^ 4 ∧
        approxUpToPhase (localProgramMatrix (skWord w)) (oneWirePhaseMatrix (wire0 : Fin 1) θ)
          (tolerance k) := by
  obtain ⟨K, e, hK, he, hbase⟩ := exists_word_approx_polylog
  obtain ⟨p, hp⟩ := exists_pow_lt_of_lt_one he (show ((2 : ℝ)⁻¹) < 1 by norm_num)
  refine ⟨7 * Nat.ceil K * (p + 1) ^ 4, ?_⟩
  intro θ k hk
  have hpowk : ((2 : ℝ)⁻¹) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpowp : 0 ≤ ((2 : ℝ)⁻¹) ^ p := pow_nonneg (by norm_num) _
  have hepsle : tolerance (k + p) ≤ e := by
    unfold tolerance
    rw [pow_add]
    exact (mul_le_of_le_one_left hpowp hpowk).trans (le_of_lt hp)
  have hepspos : 0 < tolerance (k + p) := by
    unfold tolerance
    positivity
  have htol : tolerance (k + p) ≤ tolerance k := by
    unfold tolerance
    rw [pow_add]
    have hpone : ((2 : ℝ)⁻¹) ^ p ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) k) hpone
  have hU : QuantumInfo.Euler.rzMat θ ∈ su2Set := by
    refine ⟨QuantumInfo.Euler.rzMat_mem_unitaryGroup θ, ?_⟩
    exact axisRot_det (by norm_num) θ
  obtain ⟨w, hw, hlen⟩ := hbase (tolerance (k + p)) hepspos hepsle _ hU
  refine ⟨w, ?_, ?_⟩
  · have hpoly := polylog_quartic_bound K skExponent p k hK.le skExponent_pos.le
        (le_of_lt skExponent_lt_four)
    have hreal : ((skWord w).length : ℝ) ≤
        ((7 * Nat.ceil K * (p + 1) ^ 4 * (k + 1) ^ 4 : ℕ) : ℝ) := by
      have hW : ((skWord w).length : ℝ) ≤ 7 * (w.length : ℝ) := by
        exact_mod_cast skWord_length w
      have hlen' : (w.length : ℝ) ≤ K *
          Real.log ((((2 : ℝ)⁻¹) ^ (k + p))⁻¹) ^ skExponent := by
        simpa [tolerance] using! hlen
      calc ((skWord w).length : ℝ) ≤ 7 * (w.length : ℝ) := hW
        _ ≤ 7 * (K * Real.log ((((2 : ℝ)⁻¹) ^ (k + p))⁻¹) ^ skExponent) :=
          mul_le_mul_of_nonneg_left hlen' (by norm_num)
        _ ≤ 7 * ((Nat.ceil K : ℝ) * (((p + 1 : ℕ) : ℝ) ^ 4) *
              (((k + 1 : ℕ) : ℝ) ^ 4)) := mul_le_mul_of_nonneg_left hpoly (by norm_num)
        _ = ((7 * Nat.ceil K * (p + 1) ^ 4 * (k + 1) ^ 4 : ℕ) : ℝ) := by
          push_cast
          ring
    exact_mod_cast hreal
  · obtain ⟨α, hα⟩ := skWord_phase_approx θ (tolerance (k + p)) w hw
    exact ⟨α, hα.trans htol⟩

/-- There exists a scalar phase synthesizer using only one-wire H and T gates with a uniform
quartic length bound. -/
theorem ht_scalar_exists :
    ∃ S : ScalarPhaseSynthesizer, ∃ C : ℕ,
      (∀ (neg : Bool) (e k : ℕ), 4 ≤ e → 1 ≤ k →
        (S.emit neg e k).length ≤ C * (e + k) ^ 4) ∧
      (∀ (neg : Bool) (e k : ℕ) g, g ∈ S.emit neg e k → isOneWireHT g) := by
  classical
  obtain ⟨C, hC⟩ := exists_sk_indices_uniform
  let emit : Bool → ℕ → ℕ → List (LocalQFTGate 1) := fun neg e k =>
    if hk : 1 ≤ k then skWord (Classical.choose (hC (dyadicPhaseAngle e neg) k hk)) else []
  have hbounded : ∀ (neg : Bool) (e k : ℕ), 4 ≤ e → 1 ≤ k →
      (emit neg e k).length ≤ C * (e + k) ^ 4 := by
    intro neg e k he hk
    have hh : emit neg e k = skWord (Classical.choose (hC (dyadicPhaseAngle e neg) k hk)) := by
      simp [emit, hk]
    rw [hh]
    have hlen := (Classical.choose_spec (hC (dyadicPhaseAngle e neg) k hk)).1
    exact hlen.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) 4))
  have hshape : ∀ (neg : Bool) (e k : ℕ) g, g ∈ emit neg e k → isOneWireHT g := by
    intro neg e k g hg
    by_cases hk : 1 ≤ k
    · have hh : emit neg e k = skWord (Classical.choose (hC (dyadicPhaseAngle e neg) k hk)) := by
        simp [emit, hk]
      rw [hh] at hg
      exact skWord_onlyHT _ g hg
    · simp [emit, hk] at hg
  refine ⟨{ emit := emit, legal := ?_, correct := ?_, bounded := ⟨C, 4, hbounded⟩ },
    C, hbounded, hshape⟩
  · intro neg e k g hg
    rcases hshape neg e k g hg with rfl | rfl
    · exact prim1_legal 0
    · exact prim1_legal 6
  · intro neg e k he hk
    have hh : emit neg e k = skWord (Classical.choose (hC (dyadicPhaseAngle e neg) k hk)) := by
      simp [emit, hk]
    rw [hh]
    have hc := (Classical.choose_spec (hC (dyadicPhaseAngle e neg) k hk)).2
    simpa [wire0] using! hc

noncomputable def htScalar : ScalarPhaseSynthesizer := Classical.choose ht_scalar_exists
noncomputable def htCoefficient : ℕ := Classical.choose (Classical.choose_spec ht_scalar_exists)

/-- Bounds the H and T scalar synthesizer's output length by `htCoefficient` times the fourth
power of the sum of exponent and precision. -/
theorem htScalar_bound (neg : Bool) (e k : ℕ) (he : 4 ≤ e) (hk : 1 ≤ k) :
    (htScalar.emit neg e k).length ≤ htCoefficient * (e + k) ^ 4 :=
  (Classical.choose_spec (Classical.choose_spec ht_scalar_exists)).1 neg e k he hk

/-- Every gate emitted by the H and T scalar synthesizer satisfies `isOneWireHT`. -/
theorem htScalar_shape (neg : Bool) (e k : ℕ) (g : LocalQFTGate 1)
    (hg : g ∈ htScalar.emit neg e k) : isOneWireHT g :=
  (Classical.choose_spec (Classical.choose_spec ht_scalar_exists)).2 neg e k g hg

def htOneWire (b : Bool) : LocalQFTGate 1 :=
  if b then .cp 0 0 3 false else .h 0

def htReflection {n : ℕ} (i : Fin n) (b : Bool) : ReflectionGate n :=
  if b then .inl (i, tGate) else .inl (i, Hadamard)

/-- Lifting a Boolean-encoded H or T gate to a wire agrees with its reflection gate matrix. -/
theorem lift_ht_matrix {n : ℕ} (i : Fin n) (b : Bool) :
    localGateMatrix (liftToWire i (htOneWire b)) = reflectionGateMatrix (htReflection i b) := by
  cases b with
  | false =>
      ext x y
      rw [show liftToWire i (htOneWire false) = .h i from rfl]
      change localGateMatrix (.h i) x y = wireGate n i Hadamard x y
      rw [localGateMatrix_h, wireGate_apply]
  | true =>
      ext x y
      rw [show liftToWire i (htOneWire true) = .cp i i 3 false from rfl]
      change localGateMatrix (.cp i i 3 false) x y = wireGate n i tGate x y
      rw [localGateMatrix_cp, wireGate_apply]
      have hang : dyadicPhaseAngle 3 false = Real.pi / 4 := by
        simp [dyadicPhaseAngle]
        ring
      by_cases hxy : x = y
      · subst y
        cases hx : x i <;> simp [tGate, Rz, hang]
      · rw [ite_eq_right hxy]
        by_cases hs : ∀ k : Fin n, k ≠ i → x k = y k
        · have hi : x i ≠ y i := by
            intro h
            apply hxy
            funext k
            by_cases hk : k = i
            · subst k; exact h
            · exact hs k hk
          rw [ite_eq_left hs]
          cases hx : x i <;> cases hy : y i <;>
            simp_all [tGate, Rz]
        · rw [ite_eq_right hs]

/-- The lifted local word of Boolean-encoded H and T gates has the same matrix as its reflection
word. -/
theorem lift_ht_word_matrix {n : ℕ} (i : Fin n) (bs : List Bool) :
    localProgramMatrix ((bs.map htOneWire).map (liftToWire i)) =
      reflectionProgramMatrix (bs.map (htReflection i)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, localProgramMatrix_cons, reflectionProgramMatrix, ih]
      rw [lift_ht_matrix]

/-- The CNOT word's matrix equals `cnotGate` when its control and target differ. -/
theorem cnot_matrix_bridge {n : ℕ} (c t : Fin n) (hct : c ≠ t) :
    localProgramMatrix (cnotWord c t) = cnotGate n c t := by
  rw [cnotWord_matrix c t hct, cnotGate]
  congr 1
  funext z i
  by_cases hi : i = t
  · subst i
    cases hc : z c <;> cases ht : z t <;> simp [cnotUpdate, Function.update, hc, ht]
  · simp [cnotUpdate, Function.update, hi]

/-- The AND word with repeated control implements CNOT from that control to the last wire. -/
theorem same_control_andWord {w : ℕ} (a : Fin w) :
    localProgramMatrix (andWord a a) = cnotGate (w + 1) (liftFin a) (lastWire w) := by
  rw [andWord, ite_eq_left rfl]
  exact cnot_matrix_bridge _ _ (liftFin_ne_lastWire a)

/-- The Toffoli gate on lifted controls and the last wire equals the AND update permutation
matrix. -/
theorem toffoli_and_update {w : ℕ} (a c : Fin w) :
    Qatlib.Concepts.GateVocabulary.GateVocab.toffoliGate (liftFin a) (liftFin c) (lastWire w)
      = permMatrix (andUpdate a c) := by
  unfold Qatlib.Concepts.GateVocabulary.GateVocab.toffoliGate
  congr 1
  funext x j
  by_cases hj : j = lastWire w
  · subst j
    cases ha : x (liftFin a) <;> cases hc : x (liftFin c) <;>
      cases ht : x (lastWire w) <;>
      simp [Qatlib.Concepts.GateVocabulary.GateVocab.toffoliUpdate, andUpdate, flipAt, ha, hc,
          ht]
  · by_cases h : x (liftFin a) && x (liftFin c)
    · simp [Qatlib.Concepts.GateVocabulary.GateVocab.toffoliUpdate, andUpdate, flipAt,
        Function.update, hj, h]
    · simp [Qatlib.Concepts.GateVocabulary.GateVocab.toffoliUpdate, andUpdate,
        Function.update, hj, h]

/-- A CNOT gate with distinct control and target equals the matrix of its local CNOT word. -/
theorem cnotGate_local {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    cnotGate n a b = localProgramMatrix (cnotWord a b) := by
  rw [cnotWord_matrix a b hab]
  unfold cnotGate
  congr 1
  funext x j
  by_cases hj : j = b
  · subst j
    cases ha : x a <;> cases hb : x b <;>
      simp [Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis.cnotUpdate,
        Function.update, ha, hb]
  · simp [Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis.cnotUpdate,
      Function.update, hj]

noncomputable def reflectionAndWord {w : ℕ} (a c : Fin w) : List (ReflectionGate (w + 1)) :=
  if a = c then [Sum.inr (liftFin a, lastWire w)]
  else toffoliLocalSteps (liftFin a) (liftFin c) (lastWire w)

/-- The reflection AND word has the same matrix as the local AND word. -/
theorem reflectionAndWord_matrix {w : ℕ} (a c : Fin w) :
    reflectionProgramMatrix (reflectionAndWord a c) = localProgramMatrix (andWord a c) := by
  by_cases hac : a = c
  · subst hac
    rw [reflectionAndWord, ite_eq_left rfl, reflectionProgramMatrix,
      reflectionProgramMatrix, Matrix.one_mul, reflectionGateMatrix,
      cnotGate_local _ _ (liftFin_ne_lastWire a), andWord, ite_eq_left rfl]
  · rw [reflectionAndWord, ite_eq_right hac,
      toffoli_fifteen_matrix (liftFin a) (liftFin c) (lastWire w)
        (fun h => hac (liftFin_injective h)) (liftFin_ne_lastWire a) (liftFin_ne_lastWire c),
      toffoli_and_update, andWord_matrix]

/-- The reflection AND word has length at most fifteen. -/
theorem reflectionAndWord_length {w : ℕ} (a c : Fin w) :
    (reflectionAndWord a c).length ≤ 15 := by
  by_cases hac : a = c
  · subst hac
    simp [reflectionAndWord]
  · simp [reflectionAndWord, hac, toffoliLocalSteps_length]

/-- The seventh power of the T phase is its inverse. -/
theorem tPhase_seven : QuantumInfo.tPhase ^ 7 = QuantumInfo.tPhaseInv := by
  calc QuantumInfo.tPhase ^ 7 = QuantumInfo.tPhase ^ 7 * (QuantumInfo.tPhase * QuantumInfo.tPhaseInv) := by rw [QuantumInfo.tPhase_mul_inv, mul_one]
    _ = (QuantumInfo.tPhase ^ 7 * QuantumInfo.tPhase) * QuantumInfo.tPhaseInv := by ring
    _ = QuantumInfo.tPhaseInv := by rw [← pow_succ, QuantumInfo.tPhase_pow_eight, one_mul]

/-- The seventh power of the T gate is its adjoint. -/
theorem tGate_seven : tGate ^ 7 = tGateAdj := by
  unfold tGate tGateAdj Rz
  rw [Matrix.diagonal_pow]
  congr 1
  funext b
  cases b
  · simp
  · change QuantumInfo.tPhase ^ 7 = QuantumInfo.tPhaseInv
    exact tPhase_seven

/-- Taking a power of a wire gate is equivalent to applying the powered one-wire matrix on that
wire. -/
theorem wireGate_pow (n : ℕ) (i : Fin n) (U : Matrix Bool Bool ℂ) (m : ℕ) :
    (wireGate n i U) ^ m = wireGate n i (U ^ m) := by
  induction m with
  | zero => simp [wireGate_one]
  | succ m ih => rw [pow_succ, ih, wireGate_mul, pow_succ]

/-- Repeating a one-wire reflection gate implements the corresponding power of its wire matrix. -/
theorem reflectionRepeat_matrix {n : ℕ} (i : Fin n) (U : Matrix Bool Bool ℂ) (m : ℕ) :
    reflectionProgramMatrix (List.replicate m (Sum.inl (i, U) : ReflectionGate n))
      = (wireGate n i U) ^ m := by
  induction m with
  | zero => simp [reflectionProgramMatrix]
  | succ m ih => simp [List.replicate_succ, reflectionProgramMatrix, reflectionGateMatrix, ih, pow_succ]

/-- Seven T reflection gates on a wire implement the adjoint T reflection gate. -/
theorem reflectionSevenT {n : ℕ} (i : Fin n) :
    reflectionProgramMatrix (List.replicate 7 (Sum.inl (i, tGate) : ReflectionGate n))
      = reflectionGateMatrix (Sum.inl (i, tGateAdj)) := by
  rw [reflectionRepeat_matrix, wireGate_pow, tGate_seven]
  rfl

noncomputable def expandTAdj {n : ℕ} (g : ReflectionGate n) : List (ReflectionGate n) := by
  classical
  exact match g with
    | Sum.inl (i, U) => if U = tGateAdj then List.replicate 7 (Sum.inl (i, tGate)) else [g]
    | Sum.inr _ => [g]

/-- Expanding an adjoint T gate preserves the original reflection gate matrix. -/
theorem expandTAdj_matrix {n : ℕ} (g : ReflectionGate n) :
    reflectionProgramMatrix (expandTAdj g) = reflectionGateMatrix g := by
  classical
  cases g with
  | inl p =>
      rcases p with ⟨i,U⟩
      by_cases h : U = tGateAdj
      · subst U
        simpa [expandTAdj] using! reflectionSevenT i
      · simp [expandTAdj, h, reflectionProgramMatrix]
  | inr p => simp [expandTAdj, reflectionProgramMatrix]

noncomputable def expandAdjWord {n : ℕ} (gs : List (ReflectionGate n)) : List (ReflectionGate n) :=
  gs.flatMap expandTAdj

/-- Expanding adjoint T gates throughout a word preserves its reflection program matrix. -/
theorem expandAdjWord_matrix {n : ℕ} (gs : List (ReflectionGate n)) :
    reflectionProgramMatrix (expandAdjWord gs) = reflectionProgramMatrix gs := by
  induction gs with
  | nil => simp [expandAdjWord, reflectionProgramMatrix]
  | cons g gs ih =>
      simp only [expandAdjWord, List.flatMap_cons, reflectionProgramMatrix_append,
        reflectionProgramMatrix, expandTAdj_matrix] at ih ⊢
      rw [ih]

/-- Expanding adjoint T gates increases a word's length by at most a factor of seven. -/
theorem expandAdjWord_length {n : ℕ} (gs : List (ReflectionGate n)) :
    (expandAdjWord gs).length ≤ 7 * gs.length := by
  have hlen : ∀ g : ReflectionGate n, (expandTAdj g).length ≤ 7 := by
    classical
    intro g
    cases g with
    | inl p =>
        rcases p with ⟨i,U⟩
        by_cases h : U = tGateAdj <;> simp [expandTAdj, h]
    | inr p => simp [expandTAdj]
  induction gs with
  | nil => simp [expandAdjWord]
  | cons g gs ih =>
      simp only [expandAdjWord, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
      have h := hlen g
      omega

def isHTCPre {n : ℕ} : ReflectionGate n → Prop
  | Sum.inl (_, U) => U = Hadamard ∨ U = tGate ∨ U = tGateAdj
  | Sum.inr (c, t) => c ≠ t

def isHTC {n : ℕ} : ReflectionGate n → Prop
  | Sum.inl (_, U) => U = Hadamard ∨ U = tGate
  | Sum.inr (c, t) => c ≠ t

/-- Every gate satisfying `isHTC` is a legal reflection gate. -/
theorem isHTC_legal {n : ℕ} (g : ReflectionGate n) (hg : isHTC g) : reflectionGateLegal g := by
  cases g with
  | inl p =>
      rcases p with ⟨i,U⟩
      change U = Hadamard ∨ U = tGate at hg
      rcases hg with rfl | rfl
      · exact hadamard_unitary
      · exact tGate_mem_unitary
  | inr p => exact hg

/-- Expanding a gate satisfying `isHTCPre` produces only gates satisfying `isHTC`. -/
theorem expandTAdj_HTC {n : ℕ} (g : ReflectionGate n) (hg : isHTCPre g) :
    ∀ x ∈ expandTAdj g, isHTC x := by
  classical
  cases g with
  | inl p =>
      rcases p with ⟨i,U⟩
      change U = Hadamard ∨ U = tGate ∨ U = tGateAdj at hg
      by_cases h : U = tGateAdj
      · subst U
        intro x hx
        simp [expandTAdj] at hx
        subst x
        simp [isHTC]
      · intro x hx
        simp [expandTAdj, h] at hx
        subst x
        change U = Hadamard ∨ U = tGate
        rcases hg with hh | hh | hh
        · exact Or.inl hh
        · exact Or.inr hh
        · exact False.elim (h hh)
  | inr p =>
      rcases p with ⟨c,t⟩
      intro x hx
      simp [expandTAdj] at hx
      subst x
      exact hg

/-- Expanding a word whose gates satisfy `isHTCPre` produces only gates satisfying `isHTC`. -/
theorem expandAdjWord_HTC {n : ℕ} (gs : List (ReflectionGate n))
    (hgs : ∀ g ∈ gs, isHTCPre g) : ∀ g ∈ expandAdjWord gs, isHTC g := by
  intro g hg
  simp only [expandAdjWord, List.mem_flatMap] at hg
  obtain ⟨x,hx,hg⟩ := hg
  exact expandTAdj_HTC x (hgs x hx) g hg

/-- Every step in the local Toffoli decomposition satisfies `isHTCPre` when its three wires are
distinct. -/
theorem toffoli_onlyHTCPre {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) : ∀ g ∈ toffoliLocalSteps a b t, isHTCPre g := by
  simp [toffoliLocalSteps, isHTCPre, hab, hat, hbt]

/-- Every gate in the reflection AND word satisfies `isHTCPre`. -/
theorem reflectionAndWord_onlyHTCPre {w : ℕ} (a c : Fin w) :
    ∀ g ∈ reflectionAndWord a c, isHTCPre g := by
  by_cases hac : a = c
  · subst hac
    simp [reflectionAndWord, isHTCPre, liftFin_ne_lastWire]
  · rw [reflectionAndWord, ite_eq_right hac]
    exact toffoli_onlyHTCPre _ _ _ (fun h => hac (liftFin_injective h))
      (liftFin_ne_lastWire a) (liftFin_ne_lastWire c)

def htBool (g : LocalQFTGate 1) : Bool :=
  match g with
  | .h _ => false
  | _ => true

/-- Decoding the Boolean encoding of a gate satisfying `isOneWireHT` recovers that gate. -/
theorem htOneWire_htBool (g : LocalQFTGate 1) (hg : isOneWireHT g) :
    htOneWire (htBool g) = g := by
  rcases hg with hg | hg
  · subst g
    simp [htBool, htOneWire, prim1_zero, wire0]
  · subst g
    simp [htBool, htOneWire, prim1_six, wire0]

/-- Encoding and then decoding a word of one-wire H and T gates recovers the original word. -/
theorem htBool_recover (W : List (LocalQFTGate 1)) (hW : ∀ g ∈ W, isOneWireHT g) :
    (W.map htBool).map htOneWire = W := by
  induction W with
  | nil => rfl
  | cons g gs ih =>
      have hg : isOneWireHT g := hW g (by simp)
      have hgs : ∀ g ∈ gs, isOneWireHT g := fun g hg => hW g (by simp [hg])
      simp only [List.map_cons]
      rw [htOneWire_htBool g hg, ih hgs]

def reflectionScalarWord {n : ℕ} (i : Fin n) (W : List (LocalQFTGate 1)) :
    List (ReflectionGate n) := (W.map htBool).map (htReflection i)

/-- The reflection scalar word has the same matrix as the original H and T word lifted to the
selected wire. -/
theorem reflectionScalarWord_matrix {n : ℕ} (i : Fin n) (W : List (LocalQFTGate 1))
    (hW : ∀ g ∈ W, isOneWireHT g) :
    reflectionProgramMatrix (reflectionScalarWord i W)
      = localProgramMatrix (W.map (liftToWire i)) := by
  have h := lift_ht_word_matrix i (W.map htBool)
  rw [htBool_recover W hW] at h
  exact h.symm

/-- Converting a scalar word to a reflection scalar word preserves its length. -/
theorem reflectionScalarWord_length {n : ℕ} (i : Fin n) (W : List (LocalQFTGate 1)) :
    (reflectionScalarWord i W).length = W.length := by simp [reflectionScalarWord]

/-- Every gate in a reflection scalar word satisfies `isHTCPre`. -/
theorem reflectionScalarWord_onlyHTCPre {n : ℕ} (i : Fin n) (W : List (LocalQFTGate 1)) :
    ∀ g ∈ reflectionScalarWord i W, isHTCPre g := by
  intro g hg
  simp only [reflectionScalarWord, List.mem_map] at hg
  obtain ⟨b, hb, rfl⟩ := hg
  cases b <;> simp [htReflection, isHTCPre]

noncomputable def htcRawWord (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ) :
    List (ReflectionGate (w + 1)) :=
  if k + 2 ≤ e then [] else
    reflectionAndWord a c ++ reflectionScalarWord (lastWire w) (htScalar.emit neg e k)
      ++ reflectionAndWord a c

/-- The raw H, T, and CNOT reflection word has the same matrix as the transported scalar word. -/
theorem htcRawWord_matrix (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ) :
    reflectionProgramMatrix (htcRawWord w a c e neg k)
      = localProgramMatrix (transportEmit htScalar w a c e neg k) := by
  by_cases hf : k + 2 ≤ e
  · simp [htcRawWord, transportEmit, hf, reflectionProgramMatrix, localProgramMatrix_nil]
  · rw [htcRawWord, ite_eq_right hf, transportEmit_middle htScalar a c e neg k hf]
    rw [reflectionProgramMatrix_append, reflectionProgramMatrix_append,
      reflectionAndWord_matrix,
      reflectionScalarWord_matrix _ _ (htScalar_shape neg e k)]
    rw [andConjugate, localProgramMatrix_append, localProgramMatrix_append]

/-- Every gate in the raw H, T, and CNOT word satisfies `isHTCPre`. -/
theorem htcRawWord_pre (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ) :
    ∀ g ∈ htcRawWord w a c e neg k, isHTCPre g := by
  by_cases hf : k + 2 ≤ e
  · simp [htcRawWord, hf]
  · intro g hg
    simp only [htcRawWord, ite_eq_right hf, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact reflectionAndWord_onlyHTCPre a c g hg
    · exact reflectionScalarWord_onlyHTCPre _ _ g hg
    · exact reflectionAndWord_onlyHTCPre a c g hg

/-- The raw H, T, and CNOT word has length at most thirty plus the scalar synthesizer's output
length. -/
theorem htcRawWord_length (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ) :
    (htcRawWord w a c e neg k).length ≤ 30 + (htScalar.emit neg e k).length := by
  by_cases hf : k + 2 ≤ e
  · simp [htcRawWord, hf]
  · simp only [htcRawWord, ite_eq_right hf, List.length_append, reflectionScalarWord_length]
    have h := reflectionAndWord_length a c
    omega

noncomputable def htcWord (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ) :
    List (ReflectionGate (w + 1)) := expandAdjWord (htcRawWord w a c e neg k)

/-- The expanded H, T, and CNOT word has the same matrix as the transported scalar word. -/
theorem htcWord_matrix (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ) :
    reflectionProgramMatrix (htcWord w a c e neg k)
      = localProgramMatrix (transportEmit htScalar w a c e neg k) := by
  rw [htcWord, expandAdjWord_matrix, htcRawWord_matrix]

/-- Every gate in the expanded H, T, and CNOT word satisfies `isHTC`. -/
theorem htcWord_onlyHTC (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ) :
    ∀ g ∈ htcWord w a c e neg k, isHTC g :=
  expandAdjWord_HTC _ (htcRawWord_pre w a c e neg k)

/-- The expanded H, T, and CNOT word is reflection-legal. -/
theorem htcWord_legal (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ) :
    reflectionLegal (htcWord w a c e neg k) :=
  fun g hg => isHTC_legal g (htcWord_onlyHTC w a c e neg k g hg)

/-- The H, T, and CNOT word approximates the requested controlled phase on clean inputs up to
global phase at the requested tolerance. -/
theorem htcWord_correct (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : 4 ≤ e) (hk : 1 ≤ k) :
    approxUpToPhase (reflectionProgramMatrix (htcWord w a c e neg k) * cleanEmbed w (w + 1))
      (cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg)) (tolerance k) := by
  rw [htcWord_matrix]
  exact transportEmit_correct htScalar w a c e neg k he hk

/-- The H, T, and CNOT word restores the ancilla within the requested tolerance. -/
theorem htcWord_clean (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : 4 ≤ e) (hk : 1 ≤ k) :
    ancillaRestored w (reflectionProgramMatrix (htcWord w a c e neg k)
      * cleanEmbed w (w + 1)) (tolerance k) := by
  rw [htcWord_matrix]
  exact transportEmit_clean htScalar w a c e neg k he hk

/-- The H, T, and CNOT word has length at most seven times thirty plus seven times the scalar
word's length. -/
theorem htcWord_length (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ) :
    (htcWord w a c e neg k).length ≤ 7 * (30 + (htScalar.emit neg e k).length) := by
  exact (expandAdjWord_length _).trans
    (Nat.mul_le_mul_left 7 (htcRawWord_length w a c e neg k))

/-- Compiling the H, T, and CNOT word incurs zero oracle queries. -/
theorem htcWord_zero_queries (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ) :
    QueryCount (reflectionCompile (htcWord w a c e neg k)) = 0 :=
  queryCount_reflectionCompile _

/-- The compiled H, T, and CNOT word has gate count equal to its word length. -/
theorem htcWord_gateCount (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ) :
    GateCount (reflectionCompile (htcWord w a c e neg k))
      = (htcWord w a c e neg k).length := gateCount_reflectionCompile _

/-- Bounds the H, T, and CNOT word's length by the stated explicit quartic polynomial in request
size. -/
theorem htcWord_polynomial (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : 4 ≤ e) (hk : 1 ≤ k) :
    (htcWord w a c e neg k).length ≤
      (210 + 112 * htCoefficient) * (requestSize w (.cp a c e neg) k) ^ 4 := by
  by_cases hf : k + 2 ≤ e
  · simp [htcWord, htcRawWord, hf, expandAdjWord]
  · set N := requestSize w (.cp a c e neg) k with hN
    have hsize : k + 1 ≤ N := requestSize_ge_succ_k _ k
    have hsum : e + k ≤ 2 * N := by omega
    have hpow : (e + k) ^ 4 ≤ (2 * N) ^ 4 := Nat.pow_le_pow_left hsum 4
    have hNpos : 0 < N := by omega
    have hN4pos : 0 < N ^ 4 := pow_pos hNpos 4
    have hN4 : 1 ≤ N ^ 4 := by omega
    have hraw := htcWord_length w a c e neg k
    have hs := htScalar_bound neg e k he hk
    calc (htcWord w a c e neg k).length ≤ 7 * (30 + (htScalar.emit neg e k).length) := hraw
      _ ≤ 7 * (30 + htCoefficient * (e + k) ^ 4) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left hs _)
      _ ≤ 7 * (30 + htCoefficient * (2 * N) ^ 4) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hpow) _)
      _ = 210 + 112 * htCoefficient * N ^ 4 := by ring
      _ ≤ (210 + 112 * htCoefficient) * N ^ 4 := by nlinarith

/-- The H and T scalar synthesizer emits a nonempty word in the stated middle range of exponents
and precisions. -/
theorem htScalar_nonempty {e k : ℕ} (neg : Bool) (he : 4 ≤ e) (hk : e ≤ k + 1)
    (hkk : 1 ≤ k) : htScalar.emit neg e k ≠ [] := by
  intro hempty
  obtain ⟨α, hα⟩ := htScalar.correct neg e k he hkk
  rw [hempty, localProgramMatrix_nil] at hα
  have hfar := Qatlib.Concepts.MatrixAccess.RitzPipeline.middleWindow_empty_far
    (w := 1) (a := wire0) (c := wire0) e k neg he hk hkk α
  rw [localGateMatrix_cp_self] at hfar
  exact (not_lt_of_ge hα) hfar

/-- The H, T, and CNOT synthesis word satisfies the gate restriction, legality, zero-query,
approximation, ancilla restoration, and explicit quartic length guarantees. -/
theorem frontier1_htc (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : 4 ≤ e) (hk : 1 ≤ k) :
    (∀ g ∈ htcWord w a c e neg k, isHTC g) ∧
    reflectionLegal (htcWord w a c e neg k) ∧
    QueryCount (reflectionCompile (htcWord w a c e neg k)) = 0 ∧
    approxUpToPhase (reflectionProgramMatrix (htcWord w a c e neg k) * cleanEmbed w (w + 1))
      (cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg)) (tolerance k) ∧
    ancillaRestored w (reflectionProgramMatrix (htcWord w a c e neg k)
      * cleanEmbed w (w + 1)) (tolerance k) ∧
    (htcWord w a c e neg k).length ≤
      (210 + 112 * htCoefficient) * (requestSize w (.cp a c e neg) k) ^ 4 :=
  ⟨htcWord_onlyHTC w a c e neg k, htcWord_legal w a c e neg k,
    htcWord_zero_queries w a c e neg k, htcWord_correct w a c e neg k he hk,
    htcWord_clean w a c e neg k he hk, htcWord_polynomial w a c e neg k he hk⟩

open scoped Kronecker

noncomputable def scalarControlCoefficient : ℕ := Classical.choose exists_sk_indices_uniform

noncomputable def scalarControlIndex (θ : ℝ) (k : ℕ) : List (Fin 3) := by
  classical
  exact if hk : 1 ≤ k then
    Classical.choose ((Classical.choose_spec exists_sk_indices_uniform) θ k hk) else []

noncomputable def scalarControlWord (w : ℕ) (θ : ℝ) (k : ℕ) : List (ReflectionGate (w + 1)) :=
  reflectionScalarWord (lastWire w) (skWord (scalarControlIndex θ k))

/-- Every gate in a reflection scalar word satisfies `isHTC`. -/
theorem reflectionScalarWord_onlyHTC {n : ℕ} (i : Fin n) (W : List (LocalQFTGate 1)) :
    ∀ g ∈ reflectionScalarWord i W, isHTC g := by
  intro g hg
  simp only [reflectionScalarWord, List.mem_map] at hg
  obtain ⟨b, hb, rfl⟩ := hg
  cases b <;> simp [htReflection, isHTC]

/-- Lifting a scalar word to the last wire preserves its phase-adjusted approximation error norm
for any target angle. -/
theorem liftedScalar_error_norm (w : ℕ) (L : List (LocalQFTGate 1)) (θ φ : ℝ) :
    ‖localProgramMatrix (L.map (liftToWire (lastWire w)))
        - Complex.exp (φ * Complex.I) • oneWirePhaseMatrix (lastWire w) θ‖
      = ‖localProgramMatrix L
          - Complex.exp (φ * Complex.I) • oneWirePhaseMatrix (0 : Fin 1) θ‖ := by
  have h : localProgramMatrix (L.map (liftToWire (lastWire w)))
        - Complex.exp (φ * Complex.I) • oneWirePhaseMatrix (lastWire w) θ
      = relabelGate (regSuccView w).symm
          ((1 : Matrix (Reg w) (Reg w) ℂ) ⊗ₖ
            (localProgramMatrix L - Complex.exp (φ * Complex.I)
              • oneWirePhaseMatrix (0 : Fin 1) θ)) := by
    rw [liftedWord_tensor, oneWirePhaseMatrix_lift, relabelGate_sub_smul,
      ← Matrix.kronecker_smul, ← Qatlib.Concepts.ReferenceError.RefTraceError.kronecker_sub_right]
  rw [h, l2_norm_relabelGate, l2_norm_kronecker, l2_norm_one_eq, one_mul]

/-- Every gate in the scalar control word satisfies `isHTC`. -/
theorem scalarControlWord_onlyHTC (w : ℕ) (θ : ℝ) (k : ℕ) :
    ∀ g ∈ scalarControlWord w θ k, isHTC g :=
  reflectionScalarWord_onlyHTC _ _

/-- The scalar control word is reflection-legal. -/
theorem scalarControlWord_legal (w : ℕ) (θ : ℝ) (k : ℕ) :
    reflectionLegal (scalarControlWord w θ k) :=
  fun g hg => isHTC_legal g (scalarControlWord_onlyHTC w θ k g hg)

/-- Compiling the scalar control word incurs zero oracle queries. -/
theorem scalarControlWord_zero (w : ℕ) (θ : ℝ) (k : ℕ) :
    QueryCount (reflectionCompile (scalarControlWord w θ k)) = 0 := queryCount_reflectionCompile _

/-- The compiled scalar control word has gate count equal to its word length. -/
theorem scalarControlWord_gateCount (w : ℕ) (θ : ℝ) (k : ℕ) :
    GateCount (reflectionCompile (scalarControlWord w θ k))
      = (scalarControlWord w θ k).length := gateCount_reflectionCompile _

/-- The scalar control word approximates the last-wire phase matrix up to global phase at the
requested tolerance. -/
theorem scalarControlWord_correct (w : ℕ) (θ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    approxUpToPhase (reflectionProgramMatrix (scalarControlWord w θ k))
      (oneWirePhaseMatrix (lastWire w) θ) (tolerance k) := by
  have hidx : scalarControlIndex θ k =
      Classical.choose ((Classical.choose_spec exists_sk_indices_uniform) θ k hk) := by
    simp [scalarControlIndex, hk]
  have hspec := Classical.choose_spec ((Classical.choose_spec exists_sk_indices_uniform) θ k hk)
  have hcorrect := hspec.2
  rw [← hidx] at hcorrect
  obtain ⟨φ, hφ⟩ := hcorrect
  refine ⟨φ, ?_⟩
  rw [scalarControlWord, reflectionScalarWord_matrix _ _ (skWord_onlyHT _)]
  have hsmall : ‖localProgramMatrix (skWord (scalarControlIndex θ k))
      - Complex.exp (φ * Complex.I) • oneWirePhaseMatrix (0 : Fin 1) θ‖ ≤ tolerance k := by
    simpa [wire0] using! hφ
  exact (liftedScalar_error_norm w (skWord (scalarControlIndex θ k)) θ φ).le.trans hsmall

/-- The scalar control word has length at most `scalarControlCoefficient` times the fourth power
of the precision incremented by one. -/
theorem scalarControlWord_length (w : ℕ) (θ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (scalarControlWord w θ k).length ≤ scalarControlCoefficient * (k + 1) ^ 4 := by
  have hidx : scalarControlIndex θ k =
      Classical.choose ((Classical.choose_spec exists_sk_indices_uniform) θ k hk) := by
    simp [scalarControlIndex, hk]
  have hspec := Classical.choose_spec ((Classical.choose_spec exists_sk_indices_uniform) θ k hk)
  have hlen := hspec.1
  rw [← hidx] at hlen
  simpa [scalarControlWord, reflectionScalarWord_length, scalarControlCoefficient] using! hlen

/-- The last-wire phase matrix is diagonal and applies its phase exactly when the last input bit
is true. -/
theorem scalarControl_target_entry (w : ℕ) (θ : ℝ) (y x : Reg (w + 1)) :
    oneWirePhaseMatrix (lastWire w) θ y x =
      if y = x then (if x (lastWire w) then Complex.exp (θ * Complex.I) else 1) else 0 := by
  by_cases h : y = x
  · subst y
    simp [oneWirePhaseMatrix, Matrix.diagonal_apply]
  · simp [oneWirePhaseMatrix, Matrix.diagonal_apply, h]

def lastControlView (w : ℕ) : Reg (w + 1) ≃ Bool × Reg w :=
  (regSuccView w).trans ((Equiv.prodCongr (Equiv.refl (Reg w)) Qatlib.Concepts.GateVocabulary.GateVocab.regOneBool).trans
    (Equiv.prodComm (Reg w) Bool))

/-- The last-control view splits a register into its last bit and its original-wire register. -/
theorem lastControlView_apply (w : ℕ) (z : Reg (w + 1)) :
    lastControlView w z = (z (lastWire w), fun i => z (liftFin i)) := by
  simp [lastControlView, regSuccView_apply, Qatlib.Concepts.GateVocabulary.GateVocab.regOneBool,
      Equiv.funUnique]

/-- The last-wire phase matrix is the relabeled controlled oracle for a scalar multiple of
identity. -/
theorem scalarControl_target_controlOracle (w : ℕ) (θ : ℝ) :
    oneWirePhaseMatrix (lastWire w) θ = relabelGate (lastControlView w).symm
      (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle
        (Complex.exp (θ * Complex.I) • (1 : Matrix (Reg w) (Reg w) ℂ))) := by
  ext y x
  rw [oneWirePhaseMatrix, Matrix.diagonal_apply, relabelGate_entry, Equiv.symm_symm]
  rw [lastControlView_apply, lastControlView_apply]
  simp only [Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle, Qatlib.Concepts.BlockEncoding.LCU.select,
    Matrix.of_apply, Prod.fst, Prod.snd, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have heq : y = x ↔ y (lastWire w) = x (lastWire w) ∧
      (fun i => y (liftFin i)) = fun i => x (liftFin i) := by
    constructor
    · intro h; subst x; simp
    · rintro ⟨hb, hd⟩
      apply (lastControlView w).injective
      simp [lastControlView_apply, hb, hd]
  by_cases h : y = x
  · subst x
    cases hb : y (lastWire w) <;> simp [hb]
  · have hne : ¬(y (lastWire w) = x (lastWire w) ∧
      (fun i => y (liftFin i)) = fun i => x (liftFin i)) := fun hs => h (heq.mpr hs)
    by_cases hb : y (lastWire w) = x (lastWire w)
    · have hd : (fun i => y (liftFin i)) ≠ fun i => x (liftFin i) := fun hs => hne ⟨hb, hs⟩
      cases hx : x (lastWire w) <;> simp_all [Matrix.one_apply]
    · simp [h, hb]

/-- The controlled oracle of a phase-scaled matrix factors into the controlled scalar phase and
the controlled oracle of the original matrix. -/
theorem controlOracle_scalar_decomposition {H : Type} [Fintype H] [DecidableEq H]
    (θ : ℝ) (V : Matrix H H ℂ) :
    Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (Complex.exp (θ * Complex.I) • V) =
      Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle
          (Complex.exp (θ * Complex.I) • (1 : Matrix H H ℂ)) *
        Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle V := by
  rw [Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle_mul, Matrix.smul_mul,
      Matrix.one_mul]

/-- The scalar control word approximates the relabeled controlled scalar oracle up to global
phase at the requested tolerance. -/
theorem scalarControlWord_correct_controlOracle (w : ℕ) (θ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    approxUpToPhase (reflectionProgramMatrix (scalarControlWord w θ k))
      (relabelGate (lastControlView w).symm
        (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle
          (Complex.exp (θ * Complex.I) • (1 : Matrix (Reg w) (Reg w) ℂ)))) (tolerance k) := by
  rw [← scalarControl_target_controlOracle]
  exact scalarControlWord_correct w θ k hk

/-- The scalar control word satisfies the gate restriction, legality, zero-query, phase
approximation, and explicit quartic length guarantees. -/
theorem frontier_controlled_scalar (w : ℕ) (θ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (∀ g ∈ scalarControlWord w θ k, isHTC g) ∧
    reflectionLegal (scalarControlWord w θ k) ∧
    QueryCount (reflectionCompile (scalarControlWord w θ k)) = 0 ∧
    approxUpToPhase (reflectionProgramMatrix (scalarControlWord w θ k))
      (oneWirePhaseMatrix (lastWire w) θ) (tolerance k) ∧
    (scalarControlWord w θ k).length ≤ scalarControlCoefficient * (k + 1) ^ 4 :=
  ⟨scalarControlWord_onlyHTC w θ k, scalarControlWord_legal w θ k,
    scalarControlWord_zero w θ k, scalarControlWord_correct w θ k hk,
    scalarControlWord_length w θ k hk⟩

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.MiddleWindowFixedWord
