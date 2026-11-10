/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BlackBoxHam09.MainResults.Defs

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Matrix.Norms.L2Operator BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : ℕ}

structure Ham (ι : Type) [Fintype ι] where
  mat : Matrix ι ι ℂ
  herm : mat.IsHermitian

def spectralNorm (H : Ham ι) : ℝ := ‖H.mat‖

def colSumNorm (H : Ham ι) : ℝ := sSup (Set.range fun j : ι => ∑ k, ‖H.mat j k‖)

def maxEntryNorm (H : Ham ι) : ℝ := sSup (Set.range fun p : ι × ι => ‖H.mat p.1 p.2‖)

def IsColumnSparse (H : Ham ι) (D : ℕ) : Prop :=
  ∀ j : ι, (Finset.univ.filter (fun k : ι => H.mat j k ≠ 0)).card ≤ D

theorem maxEntryNorm_nonneg (H : Ham ι) : 0 ≤ maxEntryNorm H := by
  unfold maxEntryNorm
  exact Real.sSup_nonneg (by rintro _ ⟨p, rfl⟩; exact norm_nonneg _)

theorem norm_entry_le_maxEntryNorm (H : Ham ι) (j k : ι) :
    ‖H.mat j k‖ ≤ maxEntryNorm H := by
  unfold maxEntryNorm
  exact le_csSup (Set.finite_range _).bddAbove ⟨(j, k), rfl⟩

def band (H : Ham ι) (a b : ℝ) : Matrix ι ι ℂ :=
  fun j k => if a < ‖H.mat j k‖ ∧ ‖H.mat j k‖ ≤ b then H.mat j k else 0

def magThresholds (H : Ham ι) : Finset ℝ :=
  insert 0 (Finset.univ.image fun p : ι × ι => ‖H.mat p.1 p.2‖)

theorem magThresholds_nonempty (H : Ham ι) : (magThresholds H).Nonempty :=
  ⟨0, Finset.mem_insert_self 0 _⟩

def breakNorm (H : Ham ι) : ℝ :=
  max 1 (if spectralNorm H = 0 then 1 else
    ((magThresholds H).sup' (magThresholds_nonempty H) fun b =>
      (magThresholds H).sup' (magThresholds_nonempty H) fun a => ‖band H a b‖)
      / spectralNorm H)

theorem breakNorm_ge_one (H : Ham ι) : 1 ≤ breakNorm H := le_max_left _ _

theorem band_apply (H : Ham ι) (a b : ℝ) (j k : ι) :
    band H a b j k = if a < ‖H.mat j k‖ ∧ ‖H.mat j k‖ ≤ b then H.mat j k else 0 := rfl

theorem band_eq_zero_of_le (H : Ham ι) {a b : ℝ} (h : b ≤ a) : band H a b = 0 := by
  ext j k
  rw [band_apply, Matrix.zero_apply, if_neg]
  rintro ⟨h1, h2⟩
  linarith

theorem band_threshold_div_le_breakNorm (H : Ham ι) {a b : ℝ}
    (ha : a ∈ magThresholds H) (hb : b ∈ magThresholds H) (hH : 0 < spectralNorm H) :
    ‖band H a b‖ / spectralNorm H ≤ breakNorm H := by
  have hinner : ‖band H a b‖ ≤
      (magThresholds H).sup' (magThresholds_nonempty H) (fun a' => ‖band H a' b‖) :=
    Finset.le_sup' (fun a' => ‖band H a' b‖) ha
  have houter : (magThresholds H).sup' (magThresholds_nonempty H) (fun a' => ‖band H a' b‖) ≤
      (magThresholds H).sup' (magThresholds_nonempty H)
        (fun b' => (magThresholds H).sup' (magThresholds_nonempty H) (fun a => ‖band H a b'‖)) :=
    Finset.le_sup' (fun b' => (magThresholds H).sup' (magThresholds_nonempty H)
      (fun a => ‖band H a b'‖)) hb
  have hle : ‖band H a b‖ ≤
      (magThresholds H).sup' (magThresholds_nonempty H)
        (fun b' => (magThresholds H).sup' (magThresholds_nonempty H) (fun a => ‖band H a b'‖)) :=
    le_trans hinner houter
  have hratio : ‖band H a b‖ / spectralNorm H ≤
      ((magThresholds H).sup' (magThresholds_nonempty H)
        (fun b' => (magThresholds H).sup' (magThresholds_nonempty H) (fun a => ‖band H a b'‖)))
        / spectralNorm H :=
    div_le_div_of_nonneg_right hle (le_of_lt hH)
  have hne : spectralNorm H ≠ 0 := ne_of_gt hH
  have hbr : breakNorm H = max 1
      (((magThresholds H).sup' (magThresholds_nonempty H)
        (fun b' => (magThresholds H).sup' (magThresholds_nonempty H) (fun a => ‖band H a b'‖)))
        / spectralNorm H) := by
    unfold breakNorm
    rw [if_neg hne]
  rw [hbr]
  exact le_trans hratio (le_max_right _ _)

theorem real_smul_eq_complex_smul (r : ℝ) (A : Matrix ι ι ℂ) :
    r • A = (r : ℂ) • A := by
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

def evolution (H : Ham ι) (t : ℝ) : Matrix ι ι ℂ := HamiltonianEvolution H.mat t

theorem evolution_def (H : Ham ι) (t : ℝ) :
    evolution H t = NormedSpace.exp ((-Complex.I * (t : ℂ)) • H.mat) := rfl

theorem evolution_eq_dysonPropagator (H : Ham ι) (t : ℝ) :
    evolution H t =
      Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution
        (Complex.I • H.mat) t := by
  unfold evolution HamiltonianEvolution
    Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution
  rw [real_smul_eq_complex_smul]
  rw [smul_smul]
  congr 1
  push_cast
  ring

theorem evolution_mem_unitaryGroup (H : Ham ι) (t : ℝ) :
    evolution H t ∈ Matrix.unitaryGroup ι ℂ :=
  hamiltonianEvolution_unitary H.herm t

@[simp] theorem evolution_zero (H : Ham ι) : evolution H 0 = 1 :=
  hamiltonianEvolution_zero H.mat

theorem evolution_add (H : Ham ι) (s t : ℝ) :
    evolution H (s + t) = evolution H s * evolution H t :=
  hamiltonianEvolution_add H.mat s t

abbrev Register (ι : Type) (L : ℕ) := ι × ι × Reg L

def regXor (z φ : Reg L) : Reg L := fun i => Bool.xor (z i) (φ i)

def oraclePerm (φ : ι × ι → Reg L) (p : Register ι L) : Register ι L :=
  (p.1, p.2.1, regXor p.2.2 (φ (p.1, p.2.1)))

@[simp] theorem regXor_regXor (z φ : Reg L) : regXor (regXor z φ) φ = z := by
  funext i
  cases hz : z i <;> cases hφ : φ i <;> simp [regXor, hz, hφ]

def valueOracle (φ : ι × ι → Reg L) : Matrix (Register ι L) (Register ι L) ℂ :=
  fun p q => if q = oraclePerm φ p then 1 else 0

@[simp] theorem oraclePerm_involutive (φ : ι × ι → Reg L) (p : Register ι L) :
    oraclePerm φ (oraclePerm φ p) = p := by
  simp [oraclePerm, regXor_regXor]

theorem valueOracle_apply (φ : ι × ι → Reg L) (j k : ι) (z : Reg L) :
    valueOracle φ (j, k, z) =
      Qatlib.Foundations.PureStateMath.Ket (j, k, regXor z (φ (j, k))) := by
  funext q
  unfold valueOracle oraclePerm
  by_cases h : q = (j, k, regXor z (φ (j, k)))
  · subst h
    simp [Qatlib.Foundations.PureStateMath.Ket]
  · simp [h, Qatlib.Foundations.PureStateMath.Ket]

theorem valueOracle_mul_self (φ : ι × ι → Reg L) :
    valueOracle φ * valueOracle φ = 1 := by
  ext p q
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (oraclePerm φ p)]
  · have h1 : valueOracle φ p (oraclePerm φ p) = 1 := by
      show (if oraclePerm φ p = oraclePerm φ p then (1 : ℂ) else 0) = 1
      rw [if_pos rfl]
    have h2 : valueOracle φ (oraclePerm φ p) q = (if q = p then 1 else 0) := by
      show (if q = oraclePerm φ (oraclePerm φ p) then (1 : ℂ) else 0) = _
      rw [oraclePerm_involutive]
    rw [h1, one_mul, h2]
    by_cases h : q = p
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hpq => h hpq.symm)]
  · intro r _ hr
    have hpr : valueOracle φ p r = 0 := by
      show (if r = oraclePerm φ p then (1 : ℂ) else 0) = 0
      rw [if_neg hr]
    rw [hpr, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem valueOracle_transpose (φ : ι × ι → Reg L) :
    (valueOracle φ)ᵀ = valueOracle φ := by
  ext p q
  rw [Matrix.transpose_apply]
  by_cases hq : p = oraclePerm φ q
  · have hq' : q = oraclePerm φ p := by rw [hq, oraclePerm_involutive]
    show (if p = oraclePerm φ q then (1 : ℂ) else 0) =
      (if q = oraclePerm φ p then (1 : ℂ) else 0)
    rw [if_pos hq, if_pos hq']
  · have hq' : q ≠ oraclePerm φ p := by
      intro h
      exact hq (by rw [h]; exact (oraclePerm_involutive φ p).symm)
    show (if p = oraclePerm φ q then (1 : ℂ) else 0) =
      (if q = oraclePerm φ p then (1 : ℂ) else 0)
    rw [if_neg hq, if_neg hq']

theorem valueOracle_star (φ : ι × ι → Reg L) :
    star (valueOracle φ) = valueOracle φ := by
  ext p q
  rw [Matrix.star_apply]
  by_cases hq : p = oraclePerm φ q
  · have hq' : q = oraclePerm φ p := by rw [hq, oraclePerm_involutive]
    show star (if p = oraclePerm φ q then (1 : ℂ) else 0) =
      (if q = oraclePerm φ p then (1 : ℂ) else 0)
    rw [if_pos hq, if_pos hq']
    simp
  · have hq' : q ≠ oraclePerm φ p := by
      intro h
      exact hq (by rw [h]; exact (oraclePerm_involutive φ p).symm)
    show star (if p = oraclePerm φ q then (1 : ℂ) else 0) =
      (if q = oraclePerm φ p then (1 : ℂ) else 0)
    rw [if_neg hq, if_neg hq']
    simp

theorem valueOracle_mem_unitaryGroup (φ : ι × ι → Reg L) :
    valueOracle φ ∈ Matrix.unitaryGroup (Register ι L) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [valueOracle_star]
  exact valueOracle_mul_self φ

variable {D : ℕ}

structure BlackBox (ι : Type) [Fintype ι] [DecidableEq ι] (D L : ℕ) where
  H : Ham ι
  OH : Matrix (Register ι L) (Register ι L) ℂ
  OF : Matrix (Register ι L) (Register ι L) ℂ
  OH_mem : OH ∈ Matrix.unitaryGroup (Register ι L) ℂ
  OF_mem : OF ∈ Matrix.unitaryGroup (Register ι L) ℂ

  value_encoding : ∃ (φ : ι × ι → Reg L) (dec : Reg L → ℂ),
    (∀ j k, dec (φ (j, k)) = H.mat j k) ∧ OH = valueOracle φ

inductive Step2 (ι : Type) (L : ℕ) where
  | gate : Matrix (Register ι L) (Register ι L) ℂ → Step2 ι L
  | queryH : Step2 ι L
  | queryF : Step2 ι L

abbrev Circuit2 (ι : Type) (L : ℕ) := List (Step2 ι L)

def QueryCount2 : Circuit2 ι L → ℕ
  | [] => 0
  | Step2.gate _ :: C => QueryCount2 C
  | Step2.queryH :: C => QueryCount2 C + 1
  | Step2.queryF :: C => QueryCount2 C + 1

def Run2 (OH OF : Matrix (Register ι L) (Register ι L) ℂ) :
    Circuit2 ι L → QState (Register ι L) → QState (Register ι L)
  | [], ψ => ψ
  | Step2.gate U :: C, ψ => Run2 OH OF C (ApplyGate U ψ)
  | Step2.queryH :: C, ψ => Run2 OH OF C (ApplyGate OH ψ)
  | Step2.queryF :: C, ψ => Run2 OH OF C (ApplyGate OF ψ)

def IsUnitaryCircuit2 : Circuit2 ι L → Prop
  | [] => True
  | Step2.gate U :: C => U ∈ Matrix.unitaryGroup (Register ι L) ℂ ∧ IsUnitaryCircuit2 C
  | Step2.queryH :: C => IsUnitaryCircuit2 C
  | Step2.queryF :: C => IsUnitaryCircuit2 C

@[simp] theorem queryCount2_nil : QueryCount2 ([] : Circuit2 ι L) = 0 := rfl

@[simp] theorem queryCount2_gate (U : Matrix (Register ι L) (Register ι L) ℂ) (C : Circuit2 ι L) :
    QueryCount2 (Step2.gate U :: C) = QueryCount2 C := rfl

@[simp] theorem queryCount2_queryH (C : Circuit2 ι L) :
    QueryCount2 (Step2.queryH :: C) = QueryCount2 C + 1 := rfl

@[simp] theorem queryCount2_queryF (C : Circuit2 ι L) :
    QueryCount2 (Step2.queryF :: C) = QueryCount2 C + 1 := rfl

theorem queryCount2_append (C D : Circuit2 ι L) :
    QueryCount2 (C ++ D) = QueryCount2 C + QueryCount2 D := by
  induction C with
  | nil => simp
  | cons s C ih => cases s <;> simp [QueryCount2, ih] <;> omega

def RepeatCircuit2 (C : Circuit2 ι L) : ℕ → Circuit2 ι L
  | 0 => []
  | k + 1 => C ++ RepeatCircuit2 C k

theorem queryCount2_repeatCircuit (C : Circuit2 ι L) (k : ℕ) :
    QueryCount2 (RepeatCircuit2 C k) = k * QueryCount2 C := by
  induction k with
  | zero => simp [RepeatCircuit2]
  | succ k ih => rw [RepeatCircuit2, queryCount2_append, ih, Nat.succ_mul]; omega

theorem isUnitaryCircuit2_append (C D : Circuit2 ι L) :
    IsUnitaryCircuit2 (C ++ D) ↔ IsUnitaryCircuit2 C ∧ IsUnitaryCircuit2 D := by
  induction C with
  | nil => simp [IsUnitaryCircuit2]
  | cons s C ih => cases s <;> simp [IsUnitaryCircuit2, ih, and_assoc]

theorem isUnitaryCircuit2_repeatCircuit {C : Circuit2 ι L} (hC : IsUnitaryCircuit2 C)
    (k : ℕ) : IsUnitaryCircuit2 (RepeatCircuit2 C k) := by
  induction k with
  | zero => simp [RepeatCircuit2, IsUnitaryCircuit2]
  | succ k ih => rw [RepeatCircuit2, isUnitaryCircuit2_append]; exact ⟨hC, ih⟩

variable [Inhabited ι]

def inputState (ψ : ι → ℂ) : QState (Register ι L) :=
  fun p => if p.2.1 = default ∧ p.2.2 = ZeroStr L then ψ p.1 else 0

def readout (ρ : QState (Register ι L)) (j : ι) : ℂ := ρ (j, default, ZeroStr L)

def implementedMap (BB : BlackBox ι D L) (C : Circuit2 ι L) : Matrix ι ι ℂ :=
  fun j i => readout (Run2 BB.OH BB.OF C (inputState (Qatlib.Foundations.PureStateMath.Ket i))) j

def simulationError (K E : Matrix ι ι ℂ) : ℝ := (1 / 2) * Matrix.traceNorm (K - E)

def SimulableWithin (BB : BlackBox ι D L) (t δ q : ℝ) : Prop :=
  ∃ C : Circuit2 ι L,
    IsUnitaryCircuit2 C ∧
    implementedMap BB C ∈ Matrix.unitaryGroup ι ℂ ∧
    (QueryCount2 C : ℝ) ≤ q ∧
    simulationError (implementedMap BB C) (evolution BB.H t) ≤ δ

theorem simulationError_triangle (K M E : Matrix ι ι ℂ) :
    simulationError K E ≤ simulationError K M + simulationError M E := by
  unfold simulationError
  have h : (K - E).traceNorm ≤ (K - M).traceNorm + (M - E).traceNorm := by
    have hdecomp : K - E = (K - M) + (M - E) := by abel
    rw [hdecomp]
    exact Matrix.traceNorm_add_le _ _
  linarith

theorem simulableWithin_mono {BB : BlackBox ι D L} {t δ δ' q q' : ℝ}
    (hδ : δ ≤ δ') (hq : q ≤ q') (h : SimulableWithin BB t δ q) :
    SimulableWithin BB t δ' q' := by
  obtain ⟨C, hC, hU, hQ, hE⟩ := h
  exact ⟨C, hC, hU, le_trans hQ hq, le_trans hE hδ⟩

def sigmaRow (H : Ham ι) (j : ι) : ℝ := ∑ k, ‖H.mat j k‖

def maxAbs (x : ι → ℝ) : ℝ := ‖x‖

theorem maxAbs_nonneg (x : ι → ℝ) : 0 ≤ maxAbs x := norm_nonneg x

def diagMatrix (x : ι → ℝ) : Matrix ι ι ℂ := Matrix.diagonal fun j => (x j : ℂ)

theorem diagMatrix_norm (x : ι → ℝ) : ‖diagMatrix x‖ = maxAbs x := by
  unfold diagMatrix maxAbs
  rw [Matrix.l2_opNorm_diagonal]
  simp [Pi.norm_def]

def sandwich (H : Ham ι) (x : ι → ℝ) : Matrix ι ι ℂ :=
  diagMatrix x * H.mat + H.mat * diagMatrix x + diagMatrix x * H.mat * diagMatrix x

theorem sandwich_norm_le (H : Ham ι) (x : ι → ℝ) (ε Λ1 : ℝ) (hε : 0 ≤ ε)
    (hΛ1 : 0 < Λ1) :
    ‖(ε / Λ1) • sandwich H x‖ ≤
      (ε * spectralNorm H / Λ1) * (2 * maxAbs x + (maxAbs x) ^ 2) := by
  have hm : 0 ≤ maxAbs x := maxAbs_nonneg x
  have hH : 0 ≤ spectralNorm H := norm_nonneg _
  have h1 : ‖diagMatrix x * H.mat‖ ≤ maxAbs x * spectralNorm H := by
    calc ‖diagMatrix x * H.mat‖ ≤ ‖diagMatrix x‖ * ‖H.mat‖ := Matrix.l2_opNorm_mul _ _
      _ = maxAbs x * spectralNorm H := by rw [diagMatrix_norm, spectralNorm]
  have h2 : ‖H.mat * diagMatrix x‖ ≤ maxAbs x * spectralNorm H := by
    calc ‖H.mat * diagMatrix x‖ ≤ ‖H.mat‖ * ‖diagMatrix x‖ := Matrix.l2_opNorm_mul _ _
      _ = maxAbs x * spectralNorm H := by rw [diagMatrix_norm, spectralNorm]; ring
  have h3 : ‖diagMatrix x * H.mat * diagMatrix x‖ ≤ maxAbs x ^ 2 * spectralNorm H := by
    calc ‖diagMatrix x * H.mat * diagMatrix x‖
        ≤ ‖diagMatrix x * H.mat‖ * ‖diagMatrix x‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (maxAbs x * spectralNorm H) * maxAbs x :=
          mul_le_mul h1 (le_of_eq (diagMatrix_norm x)) (norm_nonneg _) (mul_nonneg hm hH)
      _ = maxAbs x ^ 2 * spectralNorm H := by ring
  have hsum : ‖sandwich H x‖ ≤ (2 * maxAbs x + maxAbs x ^ 2) * spectralNorm H := by
    calc ‖sandwich H x‖
        = ‖diagMatrix x * H.mat + H.mat * diagMatrix x +
            diagMatrix x * H.mat * diagMatrix x‖ := rfl
      _ ≤ ‖diagMatrix x * H.mat + H.mat * diagMatrix x‖ +
            ‖diagMatrix x * H.mat * diagMatrix x‖ := norm_add_le _ _
      _ ≤ (‖diagMatrix x * H.mat‖ + ‖H.mat * diagMatrix x‖) +
            ‖diagMatrix x * H.mat * diagMatrix x‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ (2 * maxAbs x + maxAbs x ^ 2) * spectralNorm H := by
            nlinarith [h1, h2, h3]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ε / Λ1)]
  have heq : (ε / Λ1) * ((2 * maxAbs x + maxAbs x ^ 2) * spectralNorm H)
      = (ε * spectralNorm H / Λ1) * (2 * maxAbs x + maxAbs x ^ 2) := by ring
  rw [← heq]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

theorem lemma7_error_amplification (H : Ham ι) (x : ι → ℝ) (ε Λ1 t : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : maxAbs x ≤ ε) (hΛ1 : 0 < Λ1)
    (ht : 0 ≤ t) :
    (t * Λ1 / ε) * ‖(ε / Λ1) • sandwich H x‖ ≤ 3 * spectralNorm H * t * ε := by
  have hb := sandwich_norm_le H x ε Λ1 (le_of_lt hε) hΛ1
  have hstep : (t * Λ1 / ε) * ‖(ε / Λ1) • sandwich H x‖ ≤
      (t * Λ1 / ε) * ((ε * spectralNorm H / Λ1) *
        (2 * maxAbs x + (maxAbs x) ^ 2)) := by
    gcongr
  have hm : 0 ≤ maxAbs x := maxAbs_nonneg x
  have hH0 : 0 ≤ spectralNorm H := norm_nonneg _
  have hsimp : (t * Λ1 / ε) * ((ε * spectralNorm H / Λ1) *
        (2 * maxAbs x + (maxAbs x) ^ 2))
      = t * spectralNorm H * (2 * maxAbs x + (maxAbs x) ^ 2) := by
    field_simp
  rw [hsimp] at hstep
  have hkey : 2 * maxAbs x + (maxAbs x) ^ 2 ≤ 3 * ε := by nlinarith
  have hc : 0 ≤ t * spectralNorm H := mul_nonneg ht hH0
  calc (t * Λ1 / ε) * ‖(ε / Λ1) • sandwich H x‖
      ≤ t * spectralNorm H * (2 * maxAbs x + (maxAbs x) ^ 2) := hstep
    _ ≤ t * spectralNorm H * (3 * ε) := by gcongr
    _ = 3 * spectralNorm H * t * ε := by ring

def walkTarget (H : Ham ι) (Λ1 ε : ℝ) (ζ : ι → QState (Register ι L)) (j : ι) :
    QState (Register ι L) :=
  fun p =>
    (if p.2.1 = default ∧ p.2.2 = ZeroStr L then
        (Real.sqrt (ε / Λ1) : ℂ) * star (H.mat j p.1) else 0) +
      (if p.2.2 = ZeroStr L then 0 else
        (Real.sqrt (1 - ε * sigmaRow H j / Λ1) : ℂ) * ζ j p)

def PreparesWalkStateWithin (BB : BlackBox ι D L) (Λ1 ε q : ℝ) : Prop :=
  ∃ C : Circuit2 ι L,
    IsUnitaryCircuit2 C ∧ (QueryCount2 C : ℝ) ≤ q ∧
    ∀ j : ι, ∃ ζ : ι → QState (Register ι L), ∃ θ : ℝ,
      Run2 BB.OH BB.OF C (inputState (Qatlib.Foundations.PureStateMath.Ket j)) =
        Complex.exp (θ * Complex.I) • walkTarget BB.H Λ1 ε ζ j

def firstTermAmp (H : Ham ι) (Λ1 ε : ℝ) (j k : ι) : ℂ :=
  (Real.sqrt (ε / Λ1) : ℂ) * star (H.mat j k)

def PreparesWalkStateApproxWithin (BB : BlackBox ι D L) (Λ1 ε q : ℝ) : Prop :=
  ∃ C : Circuit2 ι L,
    IsUnitaryCircuit2 C ∧ (QueryCount2 C : ℝ) ≤ q ∧
    ∀ j : ι, ∃ ρ : QState (Register ι L),
      Run2 BB.OH BB.OF C (inputState (Qatlib.Foundations.PureStateMath.Ket j)) = ρ ∧
      ∀ k : ι, ‖ρ (k, default, ZeroStr L) - firstTermAmp BB.H Λ1 ε j k‖ ≤
        ε * ‖firstTermAmp BB.H Λ1 ε j k‖

def lemma6QueryExpr (Λ1 ε : ℝ) (D : ℕ) (Λmax : ℝ) : ℝ :=
  Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) + 1

def unitaryMaxEntry {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  sSup (Set.range fun p : Fin N × Fin N => ‖U p.1 p.2‖)

def unitaryColSum {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  sSup (Set.range fun j : Fin N => ∑ k, ‖U j k‖)

def unitaryColSumBound {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (Λ1 : ℝ) : Prop :=
  unitaryColSum U ≤ Λ1 ∧ unitaryColSum (Matrix.conjTranspose U) ≤ Λ1

def BlockEncodes {N : ℕ} (BB : BlackBox (Bool × Fin N) N L)
    (U : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (∀ j : Fin N, BB.H.mat (false, j) (false, j) = 0 ∧ BB.H.mat (true, j) (true, j) = 0) ∧
  (∀ j k : Fin N, BB.H.mat (false, j) (true, k) = U j k) ∧
  (∀ j k : Fin N, BB.H.mat (true, j) (false, k) = star (U k j))

def UnitaryImplementsWithin {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hN : 0 < N)
    (δ q : ℝ) : Prop :=
  letI : Inhabited (Fin N) := ⟨⟨0, hN⟩⟩
  ∃ (L : ℕ), ∃ BB : BlackBox (Bool × Fin N) N L,
    BlockEncodes BB U ∧ SimulableWithin BB (Real.pi / 2) δ q

def UnitaryImplementsWithBreakWithin {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hN : 0 < N)
    (Υ δ q : ℝ) : Prop :=
  letI : Inhabited (Fin N) := ⟨⟨0, hN⟩⟩
  ∃ (L : ℕ), ∃ BB : BlackBox (Bool × Fin N) N L,
    BlockEncodes BB U ∧ breakNorm BB.H ≤ Υ ∧ SimulableWithin BB (Real.pi / 2) δ q

def loglog (D : ℕ) : ℝ := Real.log (Real.log (D : ℝ))

def loglogSafe (D : ℕ) : ℝ := max 1 (loglog D)

def logSafe (D : ℕ) : ℝ := max 1 (Real.log (D : ℝ))

def theorem1QueryExpr (Λ : ℝ) (D : ℕ) (Λmax t δ : ℝ) : ℝ :=
  Λ * t / Real.sqrt δ + (D : ℝ) * Λmax * t + 1

def theorem2QueryExpr (Λ : ℝ) (D : ℕ) (t δ : ℝ) : ℝ :=
  Real.rpow (D : ℝ) (2 / 3) * Real.rpow (loglogSafe D * Λ * t) (4 / 3) *
    Real.rpow δ (-(1 / 3))

def lemma8QueryExpr (Λ Λ1 Λmax : ℝ) (D : ℕ) (t δ : ℝ) : ℝ :=
  Real.rpow t (3 / 2) * Real.sqrt (Λmax * (D : ℝ) * Λ1 * Λ / δ)

def theorem9QueryExpr (Λ Υ : ℝ) (D : ℕ) (t δ : ℝ) : ℝ :=
  Real.sqrt (Υ * (D : ℝ) / δ) * Real.rpow (logSafe D) (7 / 4) *
    Real.rpow (Λ * t) (3 / 2)

def corollary3QueryExpr (N : ℕ) (δ : ℝ) : ℝ :=
  Real.rpow (N : ℝ) (2 / 3) * Real.rpow (loglogSafe N) (4 / 3) *
    Real.rpow δ (-(1 / 3))

def corollary12QueryExpr (N : ℕ) (Λ1 Λmax δ : ℝ) : ℝ :=
  Real.sqrt (Λmax * (N : ℝ) * Λ1 / δ)

def corollary13QueryExpr (N : ℕ) (Υ δ : ℝ) : ℝ :=
  Real.sqrt (Υ * (N : ℝ) / δ) * Real.rpow (logSafe N) (7 / 4)

end Qatlib.Papers.BlackBoxHam09.MainResults.Defs
