/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessDefs
import Qatlib.Concepts.QmaCompleteness.HistoryHam.SpectralForrelation
import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessEnergy
import Mathlib.Algebra.Ring.BooleanRing

/-!
# QMA verifier constructions and amplification counterexample

This module establishes verifier resource bounds and constructs finite gate programs realizing
`forrWitnessMass`. The reversible macros in `cnotAuxMacro` compile through `cnotAuxCompile`, and
`clause1_clause2` packages the resulting acceptance identity as a `QmaVerifier`.

The one-qubit verifier `cnotAuxV0` also yields `cnotAux_clause1_counterexample`, which refutes
the particular tail-statistic amplification claim `cnotAux_Clause1`. QMA amplification and the
surrounding Hamiltonian-complexity setting are discussed in [MarriottWatrous2005] and
[KempeKitaevRegev2006].

## Main statements

* `clause1_partial_resources`: witness-preserving program-length and description-bit bounds.
* `cnotAux_clause1_counterexample`: failure of the specified universal amplification claim.
* `clause1_clause2`: finite verifier realization of forrelation witness mass.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false

open Matrix
open scoped BigOperators

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.QmaCompleteness.HistoryHam

section Clause1Resources

/-- Summing a constant natural number over a mapped gate list gives the list length times that
number. -/
private theorem sum_map_const (l : List FiniteGateCode) (r : ℕ) :
    (l.map (fun _ : FiniteGateCode => r)).sum = l.length * r := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.add_mul]
    omega

/-- Under the stated completeness and soundness hypotheses, a verifier exists with the same
witness-qubit counts and the displayed program-length and description-bit bounds, quadratic
in `k + 1`. -/
theorem clause1_partial_resources :
    ∀ (Lyes Lno : List Bool → Prop) (V : QmaVerifier),
      (∀ x : List Bool, Lyes x →
        ∃ ψ : QState (Reg (V.witnessQubits x.length)),
          Normalized ψ ∧ 2 / 3 ≤ qmaAcceptProb V x ψ) →
      (∀ x : List Bool, Lno x →
        ∀ ψ : QState (Reg (V.witnessQubits x.length)), Normalized ψ →
          qmaAcceptProb V x ψ ≤ 1 / 3) →
      ∀ k : ℕ, ∃ V' : QmaVerifier,
        (∀ mₓ : ℕ, V'.witnessQubits mₓ = V.witnessQubits mₓ) ∧
        (∃ c : ℕ, ∀ x : List Bool,
          (V'.program x).length
            ≤ c * ((k + 1) ^ 2 * ((V.program x).length + V.auxQubits x.length + 16) + 1)) ∧
        (∃ c : ℕ, ∀ x : List Bool,
          qmaProgramBits V' x
            ≤ c * ((k + 1) ^ 2 * ((V.program x).length + V.auxQubits x.length + 16)
              * (qmaRegisterSize V x.length + 1) + 1)) := by
  intro _ _ V _ _ k
  refine ⟨V, fun _ => rfl, ⟨1, ?_⟩, ⟨4, ?_⟩⟩
  · intro x
    have hk : (1 : ℕ) ≤ (k + 1) ^ 2 := by
      have hp : (0 : ℕ) < (k + 1) ^ 2 := Nat.pow_pos (by omega : 0 < k + 1)
      omega
    have h1 : (1 : ℕ) * (V.program x).length ≤ (k + 1) ^ 2 * (V.program x).length :=
      Nat.mul_le_mul hk (le_refl _)
    have h2 : (k + 1) ^ 2 * (V.program x).length
        ≤ (k + 1) ^ 2 * ((V.program x).length + V.auxQubits x.length + 16) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · intro x
    have hk : (1 : ℕ) ≤ (k + 1) ^ 2 := by
      have hp : (0 : ℕ) < (k + 1) ^ 2 := Nat.pow_pos (by omega : 0 < k + 1)
      omega
    have hL : (V.program x).length
        ≤ (k + 1) ^ 2 * ((V.program x).length + V.auxQubits x.length + 16) := by
      have h1 : (1 : ℕ) * (V.program x).length ≤ (k + 1) ^ 2 * (V.program x).length :=
        Nat.mul_le_mul hk (le_refl _)
      have h2 : (k + 1) ^ 2 * (V.program x).length
          ≤ (k + 1) ^ 2 * ((V.program x).length + V.auxQubits x.length + 16) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hbits : qmaProgramBits V x
        = (V.program x).length * (3 + 2 * qmaRegisterSize V x.length) := by
      rw [qmaProgramBits, sum_map_const, qmaCodeBits]
    rw [hbits]
    have h1 : (V.program x).length * (3 + 2 * qmaRegisterSize V x.length)
        ≤ (V.program x).length * (4 * (qmaRegisterSize V x.length + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : (V.program x).length * (4 * (qmaRegisterSize V x.length + 1))
        ≤ ((k + 1) ^ 2 * ((V.program x).length + V.auxQubits x.length + 16))
            * (4 * (qmaRegisterSize V x.length + 1)) :=
      Nat.mul_le_mul_right _ hL
    have h3 : ((k + 1) ^ 2 * ((V.program x).length + V.auxQubits x.length + 16))
        * (4 * (qmaRegisterSize V x.length + 1))
        = 4 * ((k + 1) ^ 2 * ((V.program x).length + V.auxQubits x.length + 16)
          * (qmaRegisterSize V x.length + 1)) := by ring
    omega

end Clause1Resources
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option warningAsError false
open Matrix
open scoped BigOperators
set_option maxHeartbeats 800000

/-- Adding zero on the right leaves a natural number unchanged. -/
theorem cnotAux_smoke (n : ℕ) : n + 0 = n := by
  exact add_zero n
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option warningAsError false
open Matrix
open scoped BigOperators
set_option maxHeartbeats 800000
open scoped BigOperators Classical

/-- The equivalence between one-bit registers and Boolean values, given by evaluation at the
unique wire. -/
def cnotAux_reclause1Equiv : Reg 1 ≃ Bool where
  toFun p := p 0
  invFun b _ := b
  left_inv p := by funext i; simp [Subsingleton.elim i 0]
  right_inv _ := rfl

/-- A sum over one-bit registers is the sum of its values at the constant false and constant
true registers. -/
theorem cnotAux_sum_reclause1 {γ : Type*} [AddCommMonoid γ] (f : Reg 1 → γ) :
    ∑ p : Reg 1, f p = f (fun _ => false) + f (fun _ => true) := by
  have h1 : ∑ p : Reg 1, f p = ∑ b : Bool, f (cnotAux_reclause1Equiv.symm b) :=
    Fintype.sum_equiv cnotAux_reclause1Equiv f (fun b => f (cnotAux_reclause1Equiv.symm b)) (by intro x; simp)
  rw [h1, Fintype.sum_bool]
  simp only [cnotAux_reclause1Equiv]
  exact add_comm _ _

/-- On a one-wire register, `wireGate` has the same entries as the underlying Boolean-indexed
matrix. -/
theorem cnotAux_wireGate1 (U : Matrix Bool Bool ℂ) (w : Fin 1) (p q : Reg 1) :
    wireGate 1 w U p q = U (p 0) (q 0) := by
  rw [wireGate_apply]
  have hvac : ∀ k : Fin 1, k ≠ w → p k = q k := by
    intro k hk; exact absurd (Subsingleton.elim k w) hk
  rw [if_pos hvac]
  have hp : p w = p 0 := congrArg p (Subsingleton.elim w 0)
  have hq : q w = q 0 := congrArg q (Subsingleton.elim w 0)
  rw [hp, hq]

/-- The action of a wired one-qubit matrix is the sum of its two matrix entries times the
corresponding input amplitudes. -/
theorem cnotAux_wireGate1_mulVec (U : Matrix Bool Bool ℂ) (w : Fin 1) (φ : QState (Reg 1))
    (p : Reg 1) :
    (wireGate 1 w U).mulVec φ p
      = U (p 0) false * φ (fun _ => false) + U (p 0) true * φ (fun _ => true) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [cnotAux_sum_reclause1]
  show (fun q => wireGate 1 w U p q * φ q) (fun _ => false)
      + (fun q => wireGate 1 w U p q * φ q) (fun _ => true) = _
  simp only [cnotAux_wireGate1]

/-- With no witness or auxiliary qubits, the output component of `qmaRegSplit` is the unique
input bit. -/
theorem cnotAux_regSplit00_out (p : Reg 1) : (qmaRegSplit 0 0 p).2 = fun _ => p 0 := by
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  rw [hj]
  show (qmaRegSplit 0 0 p).2 0 = p 0
  rfl

/-- The zero-qubit computational basis state has amplitude one at the unique register. -/
theorem cnotAux_ket_zero_0 : Qatlib.Foundations.PureStateMath.Ket (ZeroStr 0) (fun _ => false : Reg 0) = 1 := by
  show (if (fun _ => false : Reg 0) = ZeroStr 0 then (1 : ℂ) else 0) = 1
  exact if_pos rfl

/-- The one-qubit zero basis state has amplitude one at false and zero at true. -/
theorem cnotAux_ket_zero_1 (b : Bool) :
    Qatlib.Foundations.PureStateMath.Ket (ZeroStr 1) (fun _ => b : Reg 1) = if b = false then (1 : ℂ) else 0 := by
  show (if (fun _ => b : Reg 1) = ZeroStr 1 then (1 : ℂ) else 0) = _
  by_cases hb : (fun _ => b : Reg 1) = ZeroStr 1
  · rw [if_pos hb]
    have hbf : b = false := congrFun hb 0
    rw [if_pos hbf]
  · rw [if_neg hb]
    have hbf : ¬ b = false := by
      intro h; apply hb; funext i; simp [ZeroStr, h]
    rw [if_neg hbf]

/-- With no witness or auxiliary qubits, initialization multiplies the unique witness amplitude
by the indicator that the output bit is false. -/
theorem cnotAux_initState_eq (ψ : QState (Reg 0)) (p : Reg 1) :
    qmaInitialState 0 0 ψ p = ψ (fun _ => false) * (if p 0 = false then 1 else 0) := by
  have hw : (qmaRegSplit 0 0 p).1.1 = (fun _ => false : Reg 0) := Subsingleton.elim _ _
  have ha : (qmaRegSplit 0 0 p).1.2 = (fun _ => false : Reg 0) := Subsingleton.elim _ _
  have ho := cnotAux_regSplit00_out p
  rw [qmaInitialState, TensorState, TensorState]
  simp only [hw, ha, ho]
  rw [cnotAux_ket_zero_0, cnotAux_ket_zero_1]
  by_cases hp : p 0 = false <;> simp [hp]

/-- The encoded Hadamard gate on one wire acts by the usual two-term matrix-vector formula. -/
theorem cnotAux_fc_h_mulVec (φ : QState (Reg 1)) (p : Reg 1) :
    (finiteCodeMatrix 1 (FiniteGateCode.h 0)).mulVec φ p
      = Hadamard (p 0) false * φ (fun _ => false) + Hadamard (p 0) true * φ (fun _ => true) := by
  simp only [finiteCodeMatrix]
  rw [dif_pos (by omega : (0 : ℕ) < 1)]
  exact cnotAux_wireGate1_mulVec Hadamard _ φ p

/-- The encoded T gate on one wire acts by the usual two-term matrix-vector formula. -/
theorem cnotAux_fc_t_mulVec (φ : QState (Reg 1)) (p : Reg 1) :
    (finiteCodeMatrix 1 (FiniteGateCode.t 0)).mulVec φ p
      = tGate (p 0) false * φ (fun _ => false) + tGate (p 0) true * φ (fun _ => true) := by
  simp only [finiteCodeMatrix]
  rw [dif_pos (by omega : (0 : ℕ) < 1)]
  exact cnotAux_wireGate1_mulVec tGate _ φ p

/-- The encoded Pauli X gate on one wire acts by the usual two-term matrix-vector formula. -/
theorem cnotAux_fc_x_mulVec (φ : QState (Reg 1)) (p : Reg 1) :
    (finiteCodeMatrix 1 (FiniteGateCode.x 0)).mulVec φ p
      = PauliX (p 0) false * φ (fun _ => false) + PauliX (p 0) true * φ (fun _ => true) := by
  simp only [finiteCodeMatrix]
  rw [dif_pos (by omega : (0 : ℕ) < 1)]
  exact cnotAux_wireGate1_mulVec PauliX _ φ p

/-- The one-wire gate word applying Hadamard, T, Hadamard, and Pauli X in that order. -/
noncomputable def cnotAuxV0prog : List FiniteGateCode :=
  [FiniteGateCode.h 0, FiniteGateCode.t 0, FiniteGateCode.h 0, FiniteGateCode.x 0]

/-- The matrix of `cnotAuxV0prog` is the product X H T H, with the first executed gate on the
right. -/
theorem cnotAux_fwm_prog :
    finiteWordMatrix 1 cnotAuxV0prog
      = finiteCodeMatrix 1 (FiniteGateCode.x 0) * finiteCodeMatrix 1 (FiniteGateCode.h 0)
        * finiteCodeMatrix 1 (FiniteGateCode.t 0) * finiteCodeMatrix 1 (FiniteGateCode.h 0) := by
  simp [finiteWordMatrix, cnotAuxV0prog]

/-- The complex phase exp(iπ/4) used in the one-qubit verifier. -/
noncomputable def cnotAuxOmega : ℂ :=
  Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- The real and imaginary parts of `cnotAuxOmega` both equal √2/2. -/
theorem cnotAuxOmega_re_im : cnotAuxOmega.re = Real.sqrt 2 / 2 ∧ cnotAuxOmega.im = Real.sqrt 2 / 2 := by
  have h : (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) = ((Real.pi : ℂ) / 4) * Complex.I := by
    push_cast
    ring
  unfold cnotAuxOmega
  rw [h]
  exact exp_pi_div_four_re_im

/-- The T gate is diagonal with entries one and `cnotAuxOmega`. -/
theorem cnotAux_tGate_vals :
    tGate false false = 1 ∧ tGate false true = 0 ∧ tGate true false = 0
      ∧ tGate true true = cnotAuxOmega := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [tGate, Rz]
  · simp [tGate, Rz]
  · simp [tGate, Rz]
  · simp [tGate, Rz, cnotAuxOmega]

/-- The first Hadamard gate gives both output basis states the unique witness amplitude divided
by √2. -/
theorem cnotAux_stage1 (ψ : QState (Reg 0)) (p : Reg 1) :
    (finiteCodeMatrix 1 (FiniteGateCode.h 0)).mulVec (qmaInitialState 0 0 ψ) p
      = (Real.sqrt 2 : ℂ)⁻¹ * ψ (fun _ => false) := by
  rw [cnotAux_fc_h_mulVec]
  rw [cnotAux_initState_eq, cnotAux_initState_eq]
  by_cases hp : p 0 = false
  · simp [hp, Hadamard]
  · have hpt : p 0 = true := by cases h : p 0 <;> simp_all
    simp [hpt, Hadamard]

/-- Applying T to the equal-amplitude state multiplies its true-bit amplitude by `cnotAuxOmega`. -/
theorem cnotAux_stage2 (ψ : QState (Reg 0)) (p : Reg 1) :
    (finiteCodeMatrix 1 (FiniteGateCode.t 0)).mulVec
        (fun _ => (Real.sqrt 2 : ℂ)⁻¹ * ψ (fun _ => false)) p
      = (if p 0 = false then (1 : ℂ) else cnotAuxOmega)
          * (Real.sqrt 2 : ℂ)⁻¹ * ψ (fun _ => false) := by
  rw [cnotAux_fc_t_mulVec]
  have h := cnotAux_tGate_vals
  by_cases hp : p 0 = false
  · simp [hp, h.1, h.2.1]
  · have hpt : p 0 = true := by cases h' : p 0 <;> simp_all
    simp [hpt, h.2.2.1, h.2.2.2]
    ring

/-- The second Hadamard produces amplitudes proportional to `1 + cnotAuxOmega` and `1 -
cnotAuxOmega` for false and true, respectively. -/
theorem cnotAux_stage3 (ψ : QState (Reg 0)) (p : Reg 1) :
    (finiteCodeMatrix 1 (FiniteGateCode.h 0)).mulVec
        (fun q => (if q 0 = false then (1 : ℂ) else cnotAuxOmega)
          * (Real.sqrt 2 : ℂ)⁻¹ * ψ (fun _ => false)) p
      = (if p 0 = false then 1 + cnotAuxOmega else 1 - cnotAuxOmega)
          * (Real.sqrt 2 : ℂ)⁻¹ ^ 2 * ψ (fun _ => false) := by
  rw [cnotAux_fc_h_mulVec]
  by_cases hp : p 0 = false
  · simp [hp, Hadamard]
    ring
  · have hpt : p 0 = true := by cases h' : p 0 <;> simp_all
    simp [hpt, Hadamard]
    ring

/-- The final Pauli X swaps the amplitudes proportional to `1 + cnotAuxOmega` and `1 -
cnotAuxOmega`. -/
theorem cnotAux_stage4 (ψ : QState (Reg 0)) (p : Reg 1) :
    (finiteCodeMatrix 1 (FiniteGateCode.x 0)).mulVec
        (fun q => (if q 0 = false then 1 + cnotAuxOmega else 1 - cnotAuxOmega)
          * (Real.sqrt 2 : ℂ)⁻¹ ^ 2 * ψ (fun _ => false)) p
      = (if p 0 = false then 1 - cnotAuxOmega else 1 + cnotAuxOmega)
          * (Real.sqrt 2 : ℂ)⁻¹ ^ 2 * ψ (fun _ => false) := by
  rw [cnotAux_fc_x_mulVec]
  by_cases hp : p 0 = false
  · simp [hp, PauliX, permMatrix]
  · have hpt : p 0 = true := by cases h' : p 0 <;> simp_all
    simp [hpt, PauliX, permMatrix]

/-- The square of the complex reciprocal of √2 is the reciprocal of two. -/
theorem cnotAux_sqrt2_inv_sq : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (2 : ℂ)⁻¹ := by
  rw [inv_pow, sqrt2_sq]

/-- Running `cnotAuxV0prog` on the initialized zero-qubit witness gives amplitudes `(1 -
cnotAuxOmega) / 2` and `(1 + cnotAuxOmega) / 2`, scaled by the witness amplitude. -/
theorem cnotAux_final_state (ψ : QState (Reg 0)) (p : Reg 1) :
    (finiteWordMatrix 1 cnotAuxV0prog).mulVec (qmaInitialState 0 0 ψ) p
      = (if p 0 = false then (1 - cnotAuxOmega) / 2 else (1 + cnotAuxOmega) / 2)
          * ψ (fun _ => false) := by
  have s1 : (finiteCodeMatrix 1 (FiniteGateCode.h 0)).mulVec (qmaInitialState 0 0 ψ)
      = (fun _ => (Real.sqrt 2 : ℂ)⁻¹ * ψ (fun _ => false)) :=
    funext (cnotAux_stage1 ψ)
  have s2 : (finiteCodeMatrix 1 (FiniteGateCode.t 0)).mulVec
        (fun _ => (Real.sqrt 2 : ℂ)⁻¹ * ψ (fun _ => false))
      = (fun q => (if q 0 = false then (1 : ℂ) else cnotAuxOmega)
          * (Real.sqrt 2 : ℂ)⁻¹ * ψ (fun _ => false)) :=
    funext (cnotAux_stage2 ψ)
  have s3 : (finiteCodeMatrix 1 (FiniteGateCode.h 0)).mulVec
        (fun q => (if q 0 = false then (1 : ℂ) else cnotAuxOmega)
          * (Real.sqrt 2 : ℂ)⁻¹ * ψ (fun _ => false))
      = (fun q => (if q 0 = false then 1 + cnotAuxOmega else 1 - cnotAuxOmega)
          * (Real.sqrt 2 : ℂ)⁻¹ ^ 2 * ψ (fun _ => false)) :=
    funext (cnotAux_stage3 ψ)
  rw [cnotAux_fwm_prog]
  simp only [← Matrix.mulVec_mulVec]
  rw [s1, s2, s3]
  rw [cnotAux_stage4]
  by_cases hp : p 0 = false
  · rw [if_pos hp, if_pos hp, cnotAux_sqrt2_inv_sq, div_eq_mul_inv]
  · rw [if_neg hp, if_neg hp, cnotAux_sqrt2_inv_sq, div_eq_mul_inv]

/-- The true-bit amplitude after `cnotAuxV0prog` is `(1 + cnotAuxOmega) / 2` times the unique
witness amplitude. -/
theorem cnotAux_final_state_true (ψ : QState (Reg 0)) :
    (finiteWordMatrix 1 cnotAuxV0prog).mulVec (qmaInitialState 0 0 ψ) (fun _ => true)
      = (1 + cnotAuxOmega) / 2 * ψ (fun _ => false) := by
  rw [cnotAux_final_state]
  simp

/-- Every one-bit register is the constant function with value its unique bit. -/
theorem cnotAux_reclause1_eq (p : Reg 1) : p = fun _ => p 0 := by
  funext i; simp [Subsingleton.elim i 0]

/-- With no witness or auxiliary qubits, the verifier output bit is the unique register bit. -/
theorem cnotAux_qmaOutputBit (p : Reg 1) : qmaOutputBit 0 0 p = p 0 := by
  simp [qmaOutputBit, cnotAux_regSplit00_out]

/-- For a one-qubit verifier with no witness or auxiliary qubits, the acceptance event consists
of registers whose unique bit is true. -/
theorem cnotAux_acceptEvent_eq : qmaAcceptEvent 0 0
    = (Finset.univ : Finset (Reg 1)).filter (fun p => p 0 = true) := by
  ext p
  simp only [qmaAcceptEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show qmaOutputBit 0 0 p = p 0 from cnotAux_qmaOutputBit p]

/-- The acceptance mass of a one-qubit state is the squared norm of its true-bit amplitude. -/
theorem cnotAux_measure_accept (φ : QState (Reg 1)) :
    MeasureProb φ (qmaAcceptEvent 0 0) = ‖φ (fun _ => true)‖ ^ 2 := by
  unfold MeasureProb
  rw [cnotAux_acceptEvent_eq, Finset.sum_filter]
  rw [show (∑ p : Reg 1, if p 0 = true then BornProb φ p else 0)
      = (if (fun _ => false) 0 = true then BornProb φ (fun _ => false) else 0)
          + (if (fun _ => true) 0 = true then BornProb φ (fun _ => true) else 0)
        from cnotAux_sum_reclause1 _]
  simp
  simp [BornProb]

/-- The verifier with no witness or auxiliary qubits that runs the fixed one-wire program
`cnotAuxV0prog` on every input. -/
noncomputable def cnotAuxV0 : QmaVerifier where
  witnessQubits := fun _ => 0
  auxQubits := fun _ => 0
  program := fun _ => cnotAuxV0prog
  legal := by
    intro x
    simp [finiteWordLegal, cnotAuxV0prog, finiteCodeLegal]
  sizeBound := ⟨2, 0, by intro x; simp [cnotAuxV0prog]⟩

/-- The acceptance mass of `cnotAuxV0` is the squared witness amplitude times the squared norm
of `(1 + cnotAuxOmega) / 2`. -/
theorem cnotAuxV0_accept (ψ : QState (Reg 0)) (x : List Bool) :
    qmaAcceptProb cnotAuxV0 x ψ = ‖ψ (fun _ => false)‖ ^ 2 * ‖(1 + cnotAuxOmega) / 2‖ ^ 2 := by
  show MeasureProb
      (Run (1 : Matrix (Reg 1) (Reg 1) ℂ) (finiteCodeCircuit 1 cnotAuxV0prog)
        (qmaInitialState 0 0 ψ)) (qmaAcceptEvent 0 0)
      = ‖ψ (fun _ => false)‖ ^ 2 * ‖(1 + cnotAuxOmega) / 2‖ ^ 2
  rw [run_finiteCodeCircuit, cnotAux_measure_accept, cnotAux_final_state_true, norm_mul, mul_pow]
  ring

/-- A sum over zero-bit registers equals its value at the unique register. -/
theorem cnotAux_sum_reclause0 {γ : Type*} [AddCommMonoid γ] (f : Reg 0 → γ) :
    ∑ p : Reg 0, f p = f (fun _ => false) := by
  have h : ∀ p : Reg 0, p = fun _ => false := fun p => Subsingleton.elim p _
  rw [Finset.sum_eq_single (fun _ => false)]
  · intro b _ hb; exact absurd (h b) hb
  · intro hm; exact absurd (Finset.mem_univ _) hm

/-- A zero-qubit state is normalized exactly when its unique amplitude has squared norm one. -/
theorem cnotAux_normalized_reclause0 (ψ : QState (Reg 0)) :
    Normalized ψ ↔ ‖ψ (fun _ => false)‖ ^ 2 = 1 := by
  unfold Normalized
  rw [cnotAux_sum_reclause0]

/-- The computational basis state of the unique zero-bit register is normalized. -/
theorem cnotAux_ket_normalized : Normalized (Qatlib.Foundations.PureStateMath.Ket (fun _ => false : Reg 0)) := by
  rw [cnotAux_normalized_reclause0]
  simp [Qatlib.Foundations.PureStateMath.Ket]

/-- The real and imaginary parts of `1 + cnotAuxOmega` are `1 + Real.sqrt 2 / 2` and `Real.sqrt
2 / 2`. -/
theorem cnotAux_omega_sum_re_im :
    (1 + cnotAuxOmega : ℂ).re = 1 + Real.sqrt 2 / 2 ∧ (1 + cnotAuxOmega : ℂ).im = Real.sqrt 2 / 2 := by
  constructor
  · rw [Complex.add_re, Complex.one_re]
    exact congrArg (fun t => (1:ℝ) + t) cnotAuxOmega_re_im.1
  · rw [Complex.add_im, Complex.one_im]
    have h := cnotAuxOmega_re_im.2
    linarith

/-- The squared norm of `(1 + cnotAuxOmega) / 2` equals `(2 + Real.sqrt 2) / 4`. -/
theorem cnotAux_halfsum_norm : ‖(1 + cnotAuxOmega) / 2‖ ^ 2 = (2 + Real.sqrt 2) / 4 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hre := cnotAux_omega_sum_re_im.1
  have him := cnotAux_omega_sum_re_im.2
  have hsq : (1 + Real.sqrt 2 / 2) * (1 + Real.sqrt 2 / 2)
      + (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 2 + Real.sqrt 2 := by
    nlinarith [h2]
  have hns : Complex.normSq (1 + cnotAuxOmega) = 2 + Real.sqrt 2 := by
    rw [Complex.normSq_apply, hre, him]
    exact hsq
  have h4 : Complex.normSq (2:ℂ) = 4 := by
    rw [Complex.normSq_apply]
    norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_div, hns, h4]

/-- The real square root of two is at least two thirds. -/
theorem cnotAux_sqrt2_ge_two_thirds : (2 / 3 : ℝ) ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

/-- Three times the real square root of two is at least two. -/
theorem cnotAux_three_sqrt2_ge : (2 : ℝ) ≤ 3 * Real.sqrt 2 := by
  have h := cnotAux_sqrt2_ge_two_thirds
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  calc 2 = 3 * (2 / 3) := by ring
    _ ≤ 3 * Real.sqrt 2 := mul_le_mul_of_nonneg_left h h3

/-- The acceptance constant `(2 + Real.sqrt 2) / 4` is at least two thirds. -/
theorem cnotAux_halfsum_ge : (2 / 3 : ℝ) ≤ (2 + Real.sqrt 2) / 4 := by
  have h3 : (0:ℝ) < 3 := by norm_num
  have h4 : (0:ℝ) < 4 := by norm_num
  rw [div_le_iff₀ h3]
  rw [div_mul_eq_mul_div, le_div_iff₀ h4]
  nlinarith [cnotAux_three_sqrt2_ge]

/-- Successive scalar multiplications of the identity matrix equal multiplication by the product
of the scalars. -/
theorem cnotAux_foldr_smul {m w : ℕ} (l : List (Fin m)) (α : Fin m → ℂ) :
    (List.foldr (fun j (M : Matrix (Reg w) (Reg w) ℂ) => α j • M) 1 l)
      = ((l.map α).prod) • 1 := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.foldr_cons, ih, List.map_cons, List.prod_cons, smul_smul]

/-- For a scalar acceptance operator `c • 1`, each pattern operator is the identity scaled by
the product of `c` or `1 - c` selected by the pattern bits. -/
theorem cnotAux_pattern_smul (w m : ℕ) (c : ℂ) (b : Fin m → Bool) :
    qmaMwPatternOperator w (c • 1 : Matrix (Reg w) (Reg w) ℂ) m b
      = (∏ j : Fin m, (if b j then c else 1 - c)) • 1 := by
  have hsub : (1 : Matrix (Reg w) (Reg w) ℂ) - c • 1 = (1 - c) • 1 := by
    rw [sub_smul, one_smul]
  have hmul : ∀ (α : ℂ) (M : Matrix (Reg w) (Reg w) ℂ), (α • 1) * M = α • M := by
    intro α M
    rw [smul_mul, one_mul]
  unfold qmaMwPatternOperator
  have hfold : ∀ l : List (Fin m),
      (List.foldr (fun j M => (if b j then c • 1 else (1 : Matrix (Reg w) (Reg w) ℂ) - c • 1) * M) 1 l)
        = (List.foldr (fun j M => (if b j then c else 1 - c) • M) 1 l) := by
    intro l
    induction l with
    | nil => rfl
    | cons j l ih =>
      simp only [List.foldr_cons, ih]
      by_cases hb : b j
      · simp [hb, hmul]
      · simp [hb, hsub, hmul]
  rw [hfold, cnotAux_foldr_smul]
  rw [show (List.finRange m).map (fun j => if b j then c else 1 - c)
        = List.ofFn (fun j => if b j then c else 1 - c) from List.ofFn_eq_map.symm]
  rw [List.prod_ofFn]

/-- The squared norm of a product of pattern-selected complex factors is the product of their
squared norms. -/
theorem cnotAux_pattern_norm (m : ℕ) (c : ℂ) (b : Fin m → Bool) :
    ‖(∏ j : Fin m, (if b j then c else 1 - c) : ℂ)‖ ^ 2
      = ∏ j : Fin m, (if b j then ‖c‖ ^ 2 else ‖1 - c‖ ^ 2) := by
  rw [norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hb : b j = true <;> simp [hb]

/-- For a normalized witness and acceptance operator `c • 1`, the tail acceptance mass is at
most `(‖c‖ ^ 2 + ‖1 - c‖ ^ 2) ^ m`. -/
theorem cnotAux_tail_bound {w a m j₀ : ℕ} (Uv : Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ)
    (c : ℂ) (ψ : QState (Reg w))
    (hQ : qmaAcceptanceOperator w a Uv = c • 1) (hψ : Normalized ψ) :
    qmaMwTailAcceptProb w a Uv m j₀ ψ ≤ (‖c‖ ^ 2 + ‖1 - c‖ ^ 2) ^ m := by
  have hnorm : ∑ y : Reg w, ‖ψ y‖ ^ 2 = 1 := hψ
  have hweight : ∀ b : Fin m → Bool,
      ∑ y : Reg w, ‖(qmaMwPatternOperator w (qmaAcceptanceOperator w a Uv) m b *ᵥ ψ) y‖ ^ 2
        = ∏ j : Fin m, (if b j then ‖c‖ ^ 2 else ‖1 - c‖ ^ 2) := by
    intro b
    rw [hQ, cnotAux_pattern_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hsum : (∑ y : Reg w, ‖((∏ j : Fin m, (if b j then c else 1 - c) : ℂ)) * ψ y‖ ^ 2)
        = (∑ y : Reg w,
            ‖((∏ j : Fin m, (if b j then c else 1 - c) : ℂ))‖ ^ 2 * ‖ψ y‖ ^ 2) :=
      Finset.sum_congr rfl fun y _ => by rw [norm_mul, mul_pow]
    rw [hsum, ← Finset.mul_sum, hnorm, mul_one]
    exact cnotAux_pattern_norm m c b
  have hterm : ∀ b : Fin m → Bool,
      (if j₀ ≤ qmaTrueCount m b then
        ∑ y : Reg w, ‖(qmaMwPatternOperator w (qmaAcceptanceOperator w a Uv) m b *ᵥ ψ) y‖ ^ 2
      else 0)
      ≤ ∏ j : Fin m, (if b j then ‖c‖ ^ 2 else ‖1 - c‖ ^ 2) := by
    intro b
    rw [hweight b]
    by_cases hc : j₀ ≤ qmaTrueCount m b
    · rw [if_pos hc]
    · rw [if_neg hc]
      positivity
  have hpow : (∑ p : Fin m → Bool, ∏ j : Fin m, (if p j then ‖c‖ ^ 2 else ‖1 - c‖ ^ 2))
      = (‖c‖ ^ 2 + ‖1 - c‖ ^ 2) ^ m := by
    rw [← Fintype.sum_pow (fun v : Bool => if v then ‖c‖ ^ 2 else ‖1 - c‖ ^ 2) m]
    simp
  unfold qmaMwTailAcceptProb
  calc (∑ b : Fin m → Bool,
        if j₀ ≤ qmaTrueCount m b then
          ∑ y : Reg w, ‖(qmaMwPatternOperator w (qmaAcceptanceOperator w a Uv) m b *ᵥ ψ) y‖ ^ 2
        else 0)
      ≤ ∑ b : Fin m → Bool, ∏ j : Fin m, (if b j then ‖c‖ ^ 2 else ‖1 - c‖ ^ 2) :=
        Finset.sum_le_sum fun b _ => hterm b
    _ = (‖c‖ ^ 2 + ‖1 - c‖ ^ 2) ^ m := hpow

/-- The real constant `(2 + Real.sqrt 2) / 4` giving the normalized acceptance probability of
`cnotAuxV0`. -/
noncomputable def cnotAuxC : ℝ := (2 + Real.sqrt 2) / 4

/-- The sum of the squares of `cnotAuxC` and its complement is three quarters. -/
theorem cnotAuxC_sq_add : cnotAuxC ^ 2 + (1 - cnotAuxC) ^ 2 = 3 / 4 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold cnotAuxC
  field_simp
  nlinarith [h2]

/-- The constant `cnotAuxC` is at least two thirds. -/
theorem cnotAuxC_ge : (2 / 3 : ℝ) ≤ cnotAuxC := cnotAux_halfsum_ge

/-- The constant `cnotAuxC` is nonnegative. -/
theorem cnotAuxC_nonneg : 0 ≤ cnotAuxC := by
  unfold cnotAuxC
  positivity

/-- A sum over `Reg (0 + 0 + 1)` splits into the values at the constant false and constant true
registers. -/
theorem cnotAux_sum_reclause1_gen {γ : Type*} [AddCommMonoid γ] (f : Reg (0 + 0 + 1) → γ) :
    ∑ p : Reg (0 + 0 + 1), f p = f (fun _ => false) + f (fun _ => true) :=
  cnotAux_sum_reclause1 f

/-- The 128th power of three quarters is at most one half. -/
theorem cnotAux_rho_le : ((3 / 4 : ℝ) ^ 128) ≤ 1 / 2 := by
  have h : (3 / 4 : ℝ) ^ 128 ≤ (3 / 4) ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num : 3 ≤ 128)
  have h3 : ((3 / 4 : ℝ) ^ 3) = 27 / 64 := by norm_num
  rw [h3] at h
  norm_num at h ⊢

/-- Every matrix indexed by zero-bit registers is its unique entry times the identity matrix. -/
theorem cnotAux_scalar_mat0 (M : Matrix (Reg 0) (Reg 0) ℂ) :
    M = (M (fun _ => false) (fun _ => false)) • 1 := by
  ext p q
  rw [Subsingleton.elim p (fun _ => false), Subsingleton.elim q (fun _ => false)]
  simp

/-- The zero-witness, zero-auxiliary embedding has value one exactly when the output bit is
false. -/
theorem cnotAux_embed_eq (z : Reg 1) (y : Reg 0) :
    qmaWitnessEmbed 0 0 z y = if z 0 = false then 1 else 0 := by
  have hw : qmaWitnessBits 0 0 z = y := Subsingleton.elim _ _
  have ha : qmaAncillaBits 0 0 z = ZeroStr 0 := Subsingleton.elim _ _
  have ho : qmaOutputBit 0 0 z = z 0 := cnotAux_qmaOutputBit z
  unfold qmaWitnessEmbed
  simp only [Matrix.of_apply, hw, ha, ho]
  by_cases h : z 0 = false <;> simp [h]

/-- The unique entry of the zero-witness acceptance operator is the sum of squared moduli of
accepting entries in the false-input column of the verifier matrix. -/
theorem cnotAux_Q_entry (Uv : Matrix (Reg 1) (Reg 1) ℂ) :
    qmaAcceptanceOperator 0 0 Uv (fun _ => false) (fun _ => false)
      = ∑ z : Reg 1, if z 0 = true then
          (starRingEnd ℂ (Uv z (fun _ => false))) * Uv z (fun _ => false) else 0 := by
  have hE : ∀ z : Reg 1, qmaWitnessEmbed 0 0 z (fun _ => false) = if z 0 = false then 1 else 0 :=
    fun z => cnotAux_embed_eq z _
  have hP : ∀ z z' : Reg 1, qmaAcceptProjector 0 0 z z'
      = if z = z' then (if z 0 = true then (1 : ℂ) else 0) else 0 := by
    intro z z'
    unfold qmaAcceptProjector
    rw [Matrix.diagonal_apply]
    by_cases h : z = z' <;> simp [h, cnotAux_qmaOutputBit]
  unfold qmaAcceptanceOperator
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hE, hP, cnotAux_sum_reclause0,
    cnotAux_sum_reclause1, cnotAux_sum_reclause1_gen]
  simp
  ring_nf
  all_goals
    intro h
    exact absurd (congrFun h 0) (by decide)

/-- Initializing the unique zero-qubit basis state gives the one-qubit false basis column. -/
theorem cnotAux_ket_col : qmaInitialState 0 0 (Qatlib.Foundations.PureStateMath.Ket (fun _ => false : Reg 0))
    = (fun q : Reg 1 => if q 0 = false then (1 : ℂ) else 0) := by
  funext q
  rw [cnotAux_initState_eq]
  simp [Qatlib.Foundations.PureStateMath.Ket]

/-- The false-input column of the verifier matrix for `cnotAuxV0` has entries `(1 -
cnotAuxOmega) / 2` and `(1 + cnotAuxOmega) / 2`. -/
theorem cnotAuxUv_col (x : List Bool) (p : Reg 1) :
    qmaVerifierUnitary cnotAuxV0 x p (fun _ => false)
      = (if p 0 = false then (1 - cnotAuxOmega) / 2 else (1 + cnotAuxOmega) / 2) := by
  have h2 : (qmaVerifierUnitary cnotAuxV0 x).mulVec
        (qmaInitialState 0 0 (Qatlib.Foundations.PureStateMath.Ket (fun _ => false : Reg 0))) p
      = qmaVerifierUnitary cnotAuxV0 x p (fun _ => false) := by
    rw [cnotAux_ket_col]
    show (qmaVerifierUnitary cnotAuxV0 x *ᵥ (fun q : Reg 1 => if q 0 = false then (1 : ℂ) else 0)) p
      = _
    simp only [Matrix.mulVec, dotProduct]
    refine (cnotAux_sum_reclause1 _).trans ?_
    simp
    try rfl
  have h3 : (qmaVerifierUnitary cnotAuxV0 x).mulVec
        (qmaInitialState 0 0 (Qatlib.Foundations.PureStateMath.Ket (fun _ => false : Reg 0))) p
      = (if p 0 = false then (1 - cnotAuxOmega) / 2 else (1 + cnotAuxOmega) / 2)
          * Qatlib.Foundations.PureStateMath.Ket (fun _ => false : Reg 0) (fun _ => false) := by
    show (finiteWordMatrix 1 cnotAuxV0prog).mulVec
        (qmaInitialState 0 0 (Qatlib.Foundations.PureStateMath.Ket (fun _ => false : Reg 0))) p = _
    rw [cnotAux_final_state]
  rw [← h2, h3]
  simp [Qatlib.Foundations.PureStateMath.Ket]
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option warningAsError false
open Matrix
open scoped BigOperators
set_option maxHeartbeats 800000
open scoped BigOperators Classical
open Classical in
open Qatlib
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib

/-- The false-input column formula for `cnotAuxV0` holds with registers written explicitly as
functions from `Fin 1` to `Bool`. -/
theorem cnotAuxUv_col_fin (x : List Bool) (p : Fin 1 → Bool) :
    qmaVerifierUnitary cnotAuxV0 x p (fun _ : Fin 1 => false)
      = (if p 0 = false then (1 - cnotAuxOmega) / 2 else (1 + cnotAuxOmega) / 2) :=
  cnotAuxUv_col x p

/-- The unique entry of the acceptance operator of `cnotAuxV0` is the complex embedding of
`cnotAuxC`. -/
theorem cnotAux_Q_val (x : List Bool) :
    qmaAcceptanceOperator 0 0 (qmaVerifierUnitary cnotAuxV0 x) (fun _ => false) (fun _ => false)
      = ((cnotAuxC : ℝ) : ℂ) := by
  rw [cnotAux_Q_entry, cnotAux_sum_reclause1]
  have hc0 : ¬ ((fun _ : Reg 1 => false) 0 = true) := by decide
  have hc1 : (fun _ : Reg 1 => true) 0 = true := by decide
  rw [if_neg hc0, if_pos hc1, zero_add]
  have hA : qmaVerifierUnitary cnotAuxV0 x (fun (p : Fin 1) => true) (fun (p : Fin 1) => false)
      = (1 + cnotAuxOmega) / 2 := cnotAuxUv_col_fin x (fun _ => true)
  rw [hA]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, cnotAux_halfsum_norm]
  rfl

/-- The acceptance operator of `cnotAuxV0` is the identity scaled by the complex embedding of
`cnotAuxC`. -/
theorem cnotAux_acceptance_op (x : List Bool) :
    qmaAcceptanceOperator 0 0 (qmaVerifierUnitary cnotAuxV0 x)
      = ((cnotAuxC : ℝ) : ℂ) • 1 := by
  have h := cnotAux_scalar_mat0 (qmaAcceptanceOperator 0 0 (qmaVerifierUnitary cnotAuxV0 x))
  rw [h, cnotAux_Q_val]

/-- The constant `cnotAuxC` is at most one. -/
theorem cnotAuxC_le_one : cnotAuxC ≤ 1 := by
  unfold cnotAuxC
  have hs : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

/-- The squared complex norms of `cnotAuxC` and its complement sum to three quarters. -/
theorem cnotAuxC_norm : ‖((cnotAuxC : ℝ) : ℂ)‖ ^ 2 + ‖(1 : ℂ) - ((cnotAuxC : ℝ) : ℂ)‖ ^ 2 = 3 / 4 := by
  simp only [← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  nlinarith [cnotAuxC_sq_add]

/-- The 128th power of three quarters is strictly less than one half. -/
theorem cnotAux_rho_lt : ((3 / 4 : ℝ) ^ 128) < 1 / 2 := by
  have h : (3 / 4 : ℝ) ^ 128 ≤ (3 / 4) ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num : 3 ≤ 128)
  have h3 : ((3 / 4 : ℝ) ^ 3) = 27 / 64 := by norm_num
  rw [h3] at h
  have h4 : (27 / 64 : ℝ) < 1 / 2 := by norm_num
  linarith

/-- The universal claim of witness-preserving amplification realizing the specified tail
statistic, with exponentially small clean-acceptance error and the stated resource bounds. -/
def cnotAux_Clause1 : Prop :=
  (∀ (Lyes Lno : List Bool → Prop) (V : QmaVerifier),
      (∀ x : List Bool, Lyes x →
        ∃ ψ : QState (Reg (V.witnessQubits x.length)),
          Normalized ψ ∧ 2 / 3 ≤ qmaAcceptProb V x ψ) →
      (∀ x : List Bool, Lno x →
        ∀ ψ : QState (Reg (V.witnessQubits x.length)), Normalized ψ →
          qmaAcceptProb V x ψ ≤ 1 / 3) →
      ∀ k : ℕ,
        ∃ V' : QmaVerifier,
          (∀ mₓ : ℕ, V'.witnessQubits mₓ = V.witnessQubits mₓ) ∧
          (qmaMwRealizes V V' (64 * k + 64) (16 * k + 16)) ∧
          (∀ x : List Bool, Lyes x →
            ∃ ψ : QState (Reg (V'.witnessQubits x.length)), Normalized ψ ∧
              1 - ((2 : ℝ)⁻¹) ^ k ≤ qmaCleanAcceptProb V' x ψ) ∧
          (∀ x : List Bool, Lno x →
            ∀ ψ : QState (Reg (V'.witnessQubits x.length)), Normalized ψ →
              qmaCleanAcceptProb V' x ψ ≤ ((2 : ℝ)⁻¹) ^ k) ∧
          (∃ c : ℕ, ∀ x : List Bool,
            (V'.program x).length
              ≤ c * ((k + 1) ^ 2 * ((V.program x).length + V.auxQubits x.length + 16) + 1)) ∧
          (∃ c : ℕ, ∀ x : List Bool,
            qmaProgramBits V' x
              ≤ c * ((k + 1) ^ 2 * ((V.program x).length + V.auxQubits x.length + 16)
                * (qmaRegisterSize V x.length + 1) + 1)))

/-- The scalar-operator tail bound remains valid after transporting the verifier matrix along an
equality of witness-qubit counts. -/
theorem cnotAux_tail_bound_cast {w' w a m j₀ : ℕ} (h : w' = w)
    (Uv : Matrix (Reg (w + a + 1)) (Reg (w + a + 1)) ℂ) (c : ℂ) (ψ : QState (Reg w'))
    (hQ : qmaAcceptanceOperator w a Uv = c • 1) (hψ : Normalized ψ) :
    qmaMwTailAcceptProb w' a (cast (by rw [h]) Uv) m j₀ ψ
      ≤ (‖c‖ ^ 2 + ‖1 - c‖ ^ 2) ^ m := by
  subst h
  exact cnotAux_tail_bound Uv c ψ hQ hψ

/-- The universal amplification claim `cnotAux_Clause1` is false. -/
theorem cnotAux_clause1_counterexample : ¬ cnotAux_Clause1 := by
  intro h
  have hyes : ∀ x : List Bool, (fun _ => True) x →
      ∃ ψ : QState (Reg (cnotAuxV0.witnessQubits x.length)),
        Normalized ψ ∧ 2 / 3 ≤ qmaAcceptProb cnotAuxV0 x ψ := by
    intro x _
    refine ⟨(Qatlib.Foundations.PureStateMath.Ket (I := Reg 0) (fun _ => false) : QState (Reg (cnotAuxV0.witnessQubits x.length))),
      cnotAux_ket_normalized, ?_⟩
    have hacc :=
        cnotAuxV0_accept (Qatlib.Foundations.PureStateMath.Ket (I := Reg 0) (fun _ => false)) x
    rw [hacc]
    have hket :
        ‖Qatlib.Foundations.PureStateMath.Ket (I := Reg 0) (fun _ => false)
        (fun _ => false)‖ ^ 2 = 1 := by simp [Qatlib.Foundations.PureStateMath.Ket]
    rw [hket, one_mul, cnotAux_halfsum_norm]
    exact cnotAux_halfsum_ge
  have hno : ∀ x : List Bool, (fun _ => False) x →
      ∀ ψ : QState (Reg (cnotAuxV0.witnessQubits x.length)), Normalized ψ →
        qmaAcceptProb cnotAuxV0 x ψ ≤ 1 / 3 := by
    intro x hx
    exact absurd hx (by simp)
  obtain ⟨V', hww, hreal, hcomp, _, _, _⟩ :=
    h (fun _ => True) (fun _ => False) cnotAuxV0 hyes hno 1
  obtain ⟨ψ', hnorm', hle⟩ := hcomp [] (trivial : True)
  have hreal' := hreal [] (hww 0) ψ'
  have hbound0 : qmaMwTailAcceptProb (V'.witnessQubits ([] : List Bool).length)
      (cnotAuxV0.auxQubits ([] : List Bool).length)
      (cast (by rw [hww (([] : List Bool).length)]) (qmaVerifierUnitary cnotAuxV0 []))
      (64 * 1 + 64) (16 * 1 + 16) ψ'
      ≤ (‖((cnotAuxC : ℝ) : ℂ)‖ ^ 2 + ‖(1 : ℂ) - ((cnotAuxC : ℝ) : ℂ)‖ ^ 2) ^ (64 * 1 + 64) :=
    cnotAux_tail_bound_cast (hww (([] : List Bool).length)) (qmaVerifierUnitary cnotAuxV0 [])
      ((cnotAuxC : ℝ) : ℂ) ψ' (cnotAux_acceptance_op []) hnorm'
  have hjoin : (1 / 2 : ℝ)
      ≤ (‖((cnotAuxC : ℝ) : ℂ)‖ ^ 2 + ‖(1 : ℂ) - ((cnotAuxC : ℝ) : ℂ)‖ ^ 2) ^ (64 * 1 + 64) := by
    have h1 : (1 - ((2 : ℝ)⁻¹) ^ (1 : ℕ)) = 1 / 2 := by norm_num
    have hle' : (1 / 2 : ℝ) ≤ qmaCleanAcceptProb V' [] ψ' := by
      rw [← h1]
      exact hle
    refine le_trans hle' ?_
    rw [hreal']
    exact hbound0
  have h3 : ((‖((cnotAuxC : ℝ) : ℂ)‖ ^ 2 + ‖(1 : ℂ) - ((cnotAuxC : ℝ) : ℂ)‖ ^ 2)
      ^ (64 * 1 + 64)) = ((3 / 4 : ℝ) ^ (64 * 1 + 64)) := by rw [cnotAuxC_norm]
  rw [h3] at hjoin
  have h2 : ((3 / 4 : ℝ) ^ (64 * 1 + 64)) < 1 / 2 := cnotAux_rho_lt
  linarith [hjoin, h2]

/-- The conjunction of the displayed universal amplification claim and universal
forrelation-verifier realization claim is false. -/
theorem clause1_clause_counter : ¬
    ((∀ (Lyes Lno : List Bool → Prop) (V : QmaVerifier),
        (∀ x : List Bool, Lyes x →
          ∃ ψ : QState (Reg (V.witnessQubits x.length)),
            Normalized ψ ∧ 2 / 3 ≤ qmaAcceptProb V x ψ) →
        (∀ x : List Bool, Lno x →
          ∀ ψ : QState (Reg (V.witnessQubits x.length)), Normalized ψ →
            qmaAcceptProb V x ψ ≤ 1 / 3) →
        ∀ k : ℕ,
          ∃ V' : QmaVerifier,
            (∀ mₓ : ℕ, V'.witnessQubits mₓ = V.witnessQubits mₓ) ∧
            (qmaMwRealizes V V' (64 * k + 64) (16 * k + 16)) ∧
            (∀ x : List Bool, Lyes x →
              ∃ ψ : QState (Reg (V'.witnessQubits x.length)), Normalized ψ ∧
                1 - ((2 : ℝ)⁻¹) ^ k ≤ qmaCleanAcceptProb V' x ψ) ∧
            (∀ x : List Bool, Lno x →
              ∀ ψ : QState (Reg (V'.witnessQubits x.length)), Normalized ψ →
                qmaCleanAcceptProb V' x ψ ≤ ((2 : ℝ)⁻¹) ^ k) ∧
            (∃ c : ℕ, ∀ x : List Bool,
              (V'.program x).length
                ≤ c * ((k + 1) ^ 2 * ((V.program x).length + V.auxQubits x.length + 16) + 1)) ∧
            (∃ c : ℕ, ∀ x : List Bool,
              qmaProgramBits V' x
                ≤ c * ((k + 1) ^ 2 * ((V.program x).length + V.auxQubits x.length + 16)
                  * (qmaRegisterSize V x.length + 1) + 1)))
    ∧ (∀ (n : ℕ) (S U : Reg n → Bool),
        ∃ (Vf : QmaVerifier) (c : ℕ) (hw : ∀ mₓ : ℕ, Vf.witnessQubits mₓ = n),
          (∀ x : List Bool, (Vf.program x).length ≤ c) ∧
          (∀ (x : List Bool) (ψ : QState (Reg n)),
            qmaAcceptProbW Vf n hw x ψ = forrWitnessMass n S U ψ))) := by
  intro h
  exact cnotAux_clause1_counterexample h.1

/-- The one-gate program applying Pauli X to wire zero. -/
def cnotAuxX0prog : List FiniteGateCode := [FiniteGateCode.x 0]

/-- The verifier with no witness or auxiliary qubits that applies Pauli X to its output wire. -/
def cnotAuxX0 : QmaVerifier where
  witnessQubits := fun _ => 0
  auxQubits := fun _ => 0
  program := fun _ => cnotAuxX0prog
  legal := by
    intro x
    simp [finiteWordLegal, cnotAuxX0prog, finiteCodeLegal]
  sizeBound := ⟨1, 0, by intro x; simp [cnotAuxX0prog]⟩

/-- The verifier with no witness or auxiliary qubits and an empty gate program. -/
def cnotAuxE0 : QmaVerifier where
  witnessQubits := fun _ => 0
  auxQubits := fun _ => 0
  program := fun _ => []
  legal := by
    intro x
    simp [finiteWordLegal]
  sizeBound := ⟨1, 0, by intro x; simp⟩

/-- The matrix of `cnotAuxX0prog` is the encoded Pauli X matrix on wire zero. -/
theorem cnotAux_fwm_x0 : finiteWordMatrix 1 cnotAuxX0prog
    = finiteCodeMatrix 1 (FiniteGateCode.x 0) := by
  simp [finiteWordMatrix, cnotAuxX0prog]

/-- The acceptance mass of `cnotAuxX0` equals the squared norm of the unique witness amplitude. -/
theorem cnotAuxX0_accept (ψ : QState (Reg 0)) (x : List Bool) :
    qmaAcceptProb cnotAuxX0 x ψ = ‖ψ (fun _ => false)‖ ^ 2 := by
  show MeasureProb
      (Run (1 : Matrix (Reg 1) (Reg 1) ℂ) (finiteCodeCircuit 1 cnotAuxX0prog)
        (qmaInitialState 0 0 ψ)) (qmaAcceptEvent 0 0)
      = _
  rw [run_finiteCodeCircuit, cnotAux_measure_accept]
  have h : (finiteWordMatrix 1 cnotAuxX0prog).mulVec (qmaInitialState 0 0 ψ) (fun _ => true)
      = ψ (fun _ => false) := by
    rw [cnotAux_fwm_x0, cnotAux_fc_x_mulVec, cnotAux_initState_eq]
    simp [PauliX, permMatrix]
  rw [h]

/-- The empty-program verifier `cnotAuxE0` has zero acceptance mass for every zero-qubit
witness. -/
theorem cnotAuxE0_accept (ψ : QState (Reg 0)) (x : List Bool) :
    qmaAcceptProb cnotAuxE0 x ψ = 0 := by
  show MeasureProb
      (Run (1 : Matrix (Reg 1) (Reg 1) ℂ) (finiteCodeCircuit 1 [])
        (qmaInitialState 0 0 ψ)) (qmaAcceptEvent 0 0)
      = _
  rw [run_finiteCodeCircuit, cnotAux_measure_accept]
  have h : (finiteWordMatrix 1 ([] : List FiniteGateCode)).mulVec
      (qmaInitialState 0 0 ψ) (fun _ => true) = 0 := by
    rw [show (finiteWordMatrix 1 ([] : List FiniteGateCode)) = 1 from rfl, Matrix.one_mulVec,
      cnotAux_initState_eq]
    simp
  rw [h]
  simp

/-- On zero-bit registers, a characteristic projector has its unique entry equal to the Boolean
indicator of its predicate. -/
theorem cnotAux_char0 (f : Reg 0 → Bool) (z z' : Reg 0) :
    charProjector 0 f z z' = if f z then 1 else 0 := by
  rw [charProjector, Matrix.diagonal_apply]
  have hzz : z = z' := Subsingleton.elim _ _
  rw [if_pos hzz]

/-- The unique matrix entry of the zero-qubit Hadamard transform is one. -/
theorem cnotAux_hadamard0 (z z' : Reg 0) : HadamardN 0 z z' = 1 := by
  simp [HadamardN]

/-- On zero-bit registers, the projector-Hadamard-projector product is the product of the two
predicate indicators. -/
theorem cnotAux_chain0 (S U : Reg 0 → Bool) (z z' : Reg 0) :
    (charProjector 0 U * HadamardN 0 * charProjector 0 S) z z'
      = (if U (fun _ => false) then (1 : ℂ) else 0) * (if S (fun _ => false) then 1 else 0) := by
  have h1 : (charProjector 0 U * HadamardN 0 * charProjector 0 S) z z'
      = ∑ k : Reg 0, (charProjector 0 U * HadamardN 0) z k * charProjector 0 S k z' := by
    rw [Matrix.mul_apply]
  rw [h1, cnotAux_sum_reclause0]
  have h2 : (charProjector 0 U * HadamardN 0) z (fun _ => false)
      = ∑ k : Reg 0, charProjector 0 U z k * HadamardN 0 k (fun _ => false) := by
    rw [Matrix.mul_apply]
  rw [h2, cnotAux_sum_reclause0]
  rw [cnotAux_char0, cnotAux_hadamard0, cnotAux_char0]
  rw [show z = (fun _ => false) from Subsingleton.elim _ _]
  rw [mul_one]

/-- Matrix-vector multiplication on zero-bit registers multiplies the unique matrix entry by the
unique state amplitude. -/
theorem cnotAux_mul0 (M : Matrix (Reg 0) (Reg 0) ℂ) (ψ : QState (Reg 0)) :
    M.mulVec ψ = (fun _ => M (fun _ => false) (fun _ => false) * ψ (fun _ => false)) := by
  funext y
  rw [Matrix.mulVec, dotProduct, cnotAux_sum_reclause0]
  rw [Subsingleton.elim y (fun _ => false)]

/-- Zero-qubit forrelation witness mass is the squared witness amplitude when both predicates
hold at the unique register, and zero otherwise. -/
theorem cnotAux_forr0 (S U : Reg 0 → Bool) (ψ : QState (Reg 0)) :
    forrWitnessMass 0 S U ψ
      = (if S (fun _ => false) ∧ U (fun _ => false) then ‖ψ (fun _ => false)‖ ^ 2 else 0) := by
  unfold forrWitnessMass
  rw [norm_toEuclidean_fromVec_sq, cnotAux_sum_reclause0]
  rw [cnotAux_mul0]
  rw [show (charProjector 0 U * HadamardN 0 * charProjector 0 S) (fun _ => false) (fun _ => false)
      = (if U (fun _ => false) then (1 : ℂ) else 0) * (if S (fun _ => false) then 1 else 0)
      from cnotAux_chain0 _ _ _ _]
  by_cases hs : S (fun _ => false) <;> by_cases hu : U (fun _ => false) <;> simp [hs, hu]

/-- Every pair of predicates on zero-bit registers has a verifier with zero witness qubits and
uniformly bounded program length whose acceptance mass equals the forrelation witness mass. -/
theorem clause1_clause2_zero : ∀ (S U : Reg 0 → Bool),
    ∃ (Vf : QmaVerifier) (c : ℕ) (hw : ∀ mₓ : ℕ, Vf.witnessQubits mₓ = 0),
      (∀ x : List Bool, (Vf.program x).length ≤ c) ∧
      (∀ (x : List Bool) (ψ : QState (Reg 0)),
        qmaAcceptProbW Vf 0 hw x ψ = forrWitnessMass 0 S U ψ) := by
  intro S U
  by_cases h : S (fun _ => false) ∧ U (fun _ => false)
  · refine ⟨cnotAuxX0, 1, fun _ => rfl, ?_, ?_⟩
    · intro x
      simp [cnotAuxX0, cnotAuxX0prog]
    · intro x ψ
      rw [cnotAux_forr0, if_pos h]
      exact cnotAuxX0_accept ψ x
  · refine ⟨cnotAuxE0, 1, fun _ => rfl, ?_, ?_⟩
    · intro x
      simp [cnotAuxE0]
    · intro x ψ
      rw [cnotAux_forr0, if_neg h]
      exact cnotAuxE0_accept ψ x

/-- Multiplying two `permMatrix` matrices corresponds to composing their defining functions in
the same order. -/
theorem cnotAux_permMatrix_mul {I : Type*} [Fintype I] [DecidableEq I] (σ τ : I → I) :
    permMatrix σ * permMatrix τ = permMatrix (fun j => σ (τ j)) := by
  ext i k
  simp only [permMatrix, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (τ k)]
  · by_cases h : i = σ (τ k) <;> simp [h]
  · intro j _ hj
    by_cases hjk : j = τ k
    · exact absurd hjk hj
    · rw [if_neg hjk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (τ k)) h

/-- A matrix sending every computational basis state at `x` to the basis state at `σ x` equals
`permMatrix σ`. -/
theorem cnotAux_matrix_eq_of_ket {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (σ : I → I) (h : ∀ x : I, M.mulVec (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (σ x)) :
    M = permMatrix σ := by
  ext i j
  have h2 := congrFun (h j) i
  simpa [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, permMatrix] using h2

/-- The matrix of concatenated gate words is the matrix of the second word times the matrix of
the first. -/
theorem cnotAux_fwm_append (N : ℕ) (gs hs : List FiniteGateCode) :
    finiteWordMatrix N (gs ++ hs) = finiteWordMatrix N hs * finiteWordMatrix N gs := by
  induction gs with
  | nil => simp [finiteWordMatrix]
  | cons g gs ih =>
    rw [List.cons_append, finiteWordMatrix, ih, finiteWordMatrix, mul_assoc]

/-- The bounds-checked construction of a gate at an already valid wire equals that wire gate. -/
theorem cnotAux_dif_wire {N : ℕ} (w : Fin N) (U : Matrix Bool Bool ℂ) :
    (if h : w.val < N then wireGate N ⟨w.val, h⟩ U else 1) = wireGate N w U := by
  rw [dif_pos w.isLt]

/-- A Pauli X gate on wire `w` is the permutation matrix that flips the bit at `w`. -/
theorem cnotAux_wireGate_pauliX (N : ℕ) (w : Fin N) :
    wireGate N w PauliX = permMatrix (fun p : Reg N => Function.update p w (!p w)) := by
  classical
  ext x y
  rw [wireGate_apply]
  simp only [permMatrix, Matrix.of_apply]
  by_cases hsupp : ∀ k : Fin N, k ≠ w → x k = y k
  · rw [if_pos hsupp]
    have hxy : x = Function.update y w (!y w) ↔ x w = !y w := by
      constructor
      · intro h
        have := congrFun h w
        simpa [Function.update] using this
      · intro h
        funext k
        by_cases hk : k = w
        · subst hk; rw [h]; simp [Function.update]
        · rw [Function.update_of_ne hk, hsupp k hk]
    by_cases hx : x w = !y w
    · rw [if_pos (hxy.2 hx)]
      simp [PauliX, permMatrix, hx]
    · have hne : x ≠ Function.update y w (!y w) := fun h => hx (hxy.1 h)
      rw [if_neg hne]
      simp [PauliX, permMatrix, hx]
  · rw [if_neg hsupp]
    have hne : x ≠ Function.update y w (!y w) := by
      intro h
      exact hsupp (fun k hk => by rw [h, Function.update_of_ne hk])
    rw [if_neg hne]

/-- The finite code for Pauli X at a valid wire denotes the permutation that flips that wire. -/
theorem cnotAux_fc_x (N : ℕ) (w : Fin N) :
    finiteCodeMatrix N (FiniteGateCode.x w.val)
      = permMatrix (fun p : Reg N => Function.update p w (!p w)) := by
  simp only [finiteCodeMatrix, cnotAux_dif_wire]
  exact cnotAux_wireGate_pauliX N w

/-- For distinct control and target wires, the encoded controlled X denotes the permutation that
replaces the target by its XOR with the control. -/
theorem cnotAux_fc_cx (N : ℕ) (c t : Fin N) (hct : c ≠ t) :
    finiteCodeMatrix N (FiniteGateCode.cx c.val t.val)
      = permMatrix (fun p : Reg N => Function.update p t (p t ^^ p c)) := by
  have hne : c.val ≠ t.val := fun h => hct (Fin.val_injective h)
  have hpos : c.val < N ∧ t.val < N ∧ c.val ≠ t.val := ⟨c.isLt, t.isLt, hne⟩
  have h1 : finiteCodeMatrix N (FiniteGateCode.cx c.val t.val) = cnotGate N c t := by
    simp only [finiteCodeMatrix, dif_pos hpos]
  rw [h1]
  rfl

/-- The fifteen-gate Hadamard, T, inverse T, and controlled X word used to implement a Toffoli
gate. -/
def cnotAuxTofCode (a b t : ℕ) : List FiniteGateCode :=
  [FiniteGateCode.h t, FiniteGateCode.cx b t, FiniteGateCode.tdg t, FiniteGateCode.cx a t,
   FiniteGateCode.t t, FiniteGateCode.cx b t, FiniteGateCode.tdg t, FiniteGateCode.cx a t,
   FiniteGateCode.t b, FiniteGateCode.t t, FiniteGateCode.h t, FiniteGateCode.cx a b,
   FiniteGateCode.t a, FiniteGateCode.tdg b, FiniteGateCode.cx a b]

/-- For three pairwise distinct wires, `cnotAuxTofCode` denotes the permutation that flips the
target exactly when both control bits are true. -/
theorem cnotAux_fwm_tofCode (N : ℕ) (a b t : Fin N) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    finiteWordMatrix N (cnotAuxTofCode a.val b.val t.val)
      = permMatrix (fun p : Reg N => Function.update p t (p t ^^ (p a && p b))) := by
  have hne1 : a.val ≠ b.val := fun h => hab (Fin.val_injective h)
  have hne2 : a.val ≠ t.val := fun h => hat (Fin.val_injective h)
  have hne3 : b.val ≠ t.val := fun h => hbt (Fin.val_injective h)

  have hbridge : finiteWordMatrix N (cnotAuxTofCode a.val b.val t.val)
      = reflectionProgramMatrix (toffoliLocalSteps a b t) := by
    simp only [cnotAuxTofCode, toffoliLocalSteps, finiteWordMatrix, reflectionProgramMatrix,
      reflectionGateMatrix, finiteCodeMatrix, cnotAux_dif_wire]
    rw [show (if h : a.val < N ∧ b.val < N ∧ a.val ≠ b.val
          then cnotGate N ⟨a.val, h.1⟩ ⟨b.val, h.2.1⟩ else 1) = cnotGate N a b
        from by rw [dif_pos (⟨a.isLt, b.isLt, hne1⟩ : a.val < N ∧ b.val < N ∧ a.val ≠ b.val)],
      show (if h : b.val < N ∧ t.val < N ∧ b.val ≠ t.val
          then cnotGate N ⟨b.val, h.1⟩ ⟨t.val, h.2.1⟩ else 1) = cnotGate N b t
        from by rw [dif_pos (⟨b.isLt, t.isLt, hne3⟩ : b.val < N ∧ t.val < N ∧ b.val ≠ t.val)],
      show (if h : a.val < N ∧ t.val < N ∧ a.val ≠ t.val
          then cnotGate N ⟨a.val, h.1⟩ ⟨t.val, h.2.1⟩ else 1) = cnotGate N a t
        from by rw [dif_pos (⟨a.isLt, t.isLt, hne2⟩ : a.val < N ∧ t.val < N ∧ a.val ≠ t.val)]]

  have hm : reflectionProgramMatrix (toffoliLocalSteps a b t)
      = permMatrix (fun p : Reg N => Function.update p t (p t ^^ (p a && p b))) := by
    refine cnotAux_matrix_eq_of_ket _ _ ?_
    intro x
    have h1 := (local_toffoli_fifteen_exact N a b t hab hat hbt).2.2 x
    rw [run_reflectionCompile] at h1
    exact h1
  rw [hbridge, hm]

/-- Register-indexed reversible gate macros consisting of a bit flip, a controlled bit flip, or
a Toffoli operation. -/
inductive cnotAuxMacro (N : ℕ) where
  | xw (w : Fin N)
  | cxw (c t : Fin N)
  | tofw (a b t : Fin N)

/-- The wire distinctness condition for a reversible macro: no restriction for X, distinct
control and target for controlled X, and pairwise distinct wires for Toffoli. -/
def cnotAuxMacroOk : {N : ℕ} → cnotAuxMacro N → Prop
  | _, .xw _ => True
  | _, .cxw c t => c ≠ t
  | _, .tofw a b t => a ≠ b ∧ a ≠ t ∧ b ≠ t

/-- The finite gate word implementing a reversible macro, using the fifteen-gate decomposition
for Toffoli. -/
def cnotAuxMacroWord {N : ℕ} : cnotAuxMacro N → List FiniteGateCode
  | .xw w => [FiniteGateCode.x w.val]
  | .cxw c t => [FiniteGateCode.cx c.val t.val]
  | .tofw a b t => cnotAuxTofCode a.val b.val t.val

/-- The register map of a reversible macro, updating its target by a bit flip or a controlled
XOR. -/
def cnotAuxMacroPerm {N : ℕ} : cnotAuxMacro N → Reg N → Reg N
  | .xw w => fun p => Function.update p w (!p w)
  | .cxw c t => fun p => Function.update p t (p t ^^ p c)
  | .tofw a b t => fun p => Function.update p t (p t ^^ (p a && p b))

/-- Compilation of a macro list by concatenating the finite gate word of each macro. -/
def cnotAuxCompile {N : ℕ} (ms : List (cnotAuxMacro N)) : List FiniteGateCode :=
  List.flatMap cnotAuxMacroWord ms

/-- The register map obtained by applying the macro maps from left to right. -/
def cnotAuxFold {N : ℕ} (ms : List (cnotAuxMacro N)) : Reg N → Reg N :=
  fun p => ms.foldl (fun q m => cnotAuxMacroPerm m q) p

/-- The empty macro list acts as the identity on registers. -/
theorem cnotAux_fold_nil {N : ℕ} : cnotAuxFold ([] : List (cnotAuxMacro N)) = _root_.id := rfl

/-- Executing a nonempty macro list applies its head macro before executing its tail. -/
theorem cnotAux_fold_cons {N : ℕ} (m : cnotAuxMacro N) (ms : List (cnotAuxMacro N)) :
    cnotAuxFold (m :: ms) = fun p => cnotAuxFold ms (cnotAuxMacroPerm m p) := rfl

/-- Executing concatenated macro lists composes the second register map after the first. -/
theorem cnotAux_fold_append {N : ℕ} (ms ns : List (cnotAuxMacro N)) :
    cnotAuxFold (ms ++ ns) = fun p => cnotAuxFold ns (cnotAuxFold ms p) := by
  funext p
  simp only [cnotAuxFold, List.foldl_append]

/-- Compilation preserves concatenation of macro lists. -/
theorem cnotAux_compile_append {N : ℕ} (ms ns : List (cnotAuxMacro N)) :
    cnotAuxCompile (ms ++ ns) = cnotAuxCompile ms ++ cnotAuxCompile ns := by
  simp [cnotAuxCompile, List.flatMap_append]

/-- Compiling a nonempty macro list concatenates the head macro word with the compiled tail. -/
theorem cnotAux_compile_cons {N : ℕ} (m : cnotAuxMacro N) (ms : List (cnotAuxMacro N)) :
    cnotAuxCompile (m :: ms) = cnotAuxMacroWord m ++ cnotAuxCompile ms := by
  simp [cnotAuxCompile]

/-- For a macro satisfying `cnotAuxMacroOk`, its compiled gate word denotes the matrix of its
register map. -/
theorem cnotAux_fwm_macroWord {N : ℕ} (m : cnotAuxMacro N) (hm : cnotAuxMacroOk m) :
    finiteWordMatrix N (cnotAuxMacroWord m) = permMatrix (cnotAuxMacroPerm m) := by
  rcases m with w | ⟨c, t⟩ | ⟨a, b, t⟩
  · simp only [cnotAuxMacroWord, cnotAuxMacroPerm, finiteWordMatrix, cnotAux_fc_x]
    rw [one_mul]
  · simp only [cnotAuxMacroWord, cnotAuxMacroPerm, finiteWordMatrix, cnotAux_fc_cx _ _ _ hm]
    rw [one_mul]
  · simp only [cnotAuxMacroWord, cnotAuxMacroPerm]
    exact cnotAux_fwm_tofCode N a b t hm.1 hm.2.1 hm.2.2

/-- A macro list whose macros satisfy `cnotAuxMacroOk` compiles to the matrix of its sequential
register map. -/
theorem cnotAux_fwm_compile {N : ℕ} (ms : List (cnotAuxMacro N))
    (hok : ∀ m ∈ ms, cnotAuxMacroOk m) :
    finiteWordMatrix N (cnotAuxCompile ms) = permMatrix (cnotAuxFold ms) := by
  induction ms with
  | nil =>
    simp only [cnotAuxCompile, List.flatMap_nil, cnotAux_fold_nil]
    rw [show (finiteWordMatrix N ([] : List FiniteGateCode)) = 1 from rfl]
    ext i j
    simp [permMatrix, Matrix.one_apply]
  | cons m ms ih =>
    rw [cnotAux_compile_cons, cnotAux_fwm_append, cnotAux_fwm_macroWord m (hok m List.mem_cons_self),
      ih (fun m' hm' => hok m' (List.mem_cons_of_mem _ hm')), cnotAux_permMatrix_mul,
      cnotAux_fold_cons]

/-- If the register map of a macro list equals an involutive function, that register map is
involutive. -/
theorem cnotAux_fold_involution {N : ℕ} (ms : List (cnotAuxMacro N)) (σ : Reg N → Reg N)
    (hσ : cnotAuxFold ms = σ) (hinv : Function.Involutive σ) : Function.Involutive (cnotAuxFold ms) := by
  rw [hσ]; exact hinv

/-- The property that `σ` changes only wire `fl`, XORing its bit with a Boolean function `G`
that is invariant under arbitrary updates to `fl`. -/
def cnotAuxFlipShape {N : ℕ} (fl : Fin N) (σ : Reg N → Reg N) : Prop :=
  ∃ G : Reg N → Bool,
    (∀ p, σ p = Function.update p fl (p fl ^^ G p)) ∧ (∀ p b, G (Function.update p fl b) = G p)

/-- Every register map satisfying `cnotAuxFlipShape fl` is an involution. -/
theorem cnotAux_flipShape_involutive {N : ℕ} {fl : Fin N} {σ : Reg N → Reg N}
    (h : cnotAuxFlipShape fl σ) : Function.Involutive σ := by
  obtain ⟨G, hσ, hG⟩ := h
  intro p
  rw [hσ (σ p), hσ p]
  have hGp : G (Function.update p fl (p fl ^^ G p)) = G p := hG p (p fl ^^ G p)
  rw [hGp]
  have hfl : Function.update p fl (p fl ^^ G p) fl = (p fl ^^ G p) := by
    simp [Function.update]
  rw [hfl, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  funext k
  by_cases hk : k = fl
  · subst hk; simp [Function.update]
  · simp [Function.update, hk]

/-- The composite `fun p => σ (τ p)` satisfies `cnotAuxFlipShape fl` whenever both `σ` and `τ`
satisfy that property. -/
theorem cnotAux_flipShape_comp {N : ℕ} {fl : Fin N} {σ τ : Reg N → Reg N}
    (hσ : cnotAuxFlipShape fl σ) (hτ : cnotAuxFlipShape fl τ) :
    cnotAuxFlipShape fl (fun p => σ (τ p)) := by
  obtain ⟨G, hσ, hG⟩ := hσ
  obtain ⟨H, hτ, hH⟩ := hτ
  refine ⟨fun p => (G p ^^ H p), ?_, ?_⟩
  · intro p
    show σ (τ p) = Function.update p fl (p fl ^^ (G p ^^ H p))
    have hGp : G (Function.update p fl (p fl ^^ H p)) = G p := hG p (p fl ^^ H p)
    rw [hσ, hτ, hGp]
    funext k
    by_cases hk : k = fl
    · subst hk
      simp [Function.update, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]
    · simp [Function.update, hk, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]
  · intro p b
    show (G (Function.update p fl b) ^^ H (Function.update p fl b)) = (G p ^^ H p)
    rw [hG p b, hH p b]

/-- The identity map on `Reg N` satisfies `cnotAuxFlipShape fl` for every wire `fl`. -/
theorem cnotAux_flipShape_id {N : ℕ} (fl : Fin N) : cnotAuxFlipShape fl (_root_.id : Reg N → Reg N) := by
  refine ⟨fun _ => false, ?_, ?_⟩
  · intro p
    show p = Function.update p fl (p fl ^^ false)
    funext k
    by_cases hk : k = fl <;> simp [Function.update, hk, Bool.xor_false]
  · intro p b; rfl

/-- Conjugating a map satisfying `cnotAuxFlipShape fl` by an involution `τ` preserves this
property, provided `τ` fixes the bit at `fl` and commutes with every update to that wire. -/
theorem cnotAux_flipShape_conj {N : ℕ} {fl : Fin N} {σ τ : Reg N → Reg N}
    (hσ : cnotAuxFlipShape fl σ) (hcomm : ∀ p b, τ (Function.update p fl b)
      = Function.update (τ p) fl b) (hinv : Function.Involutive τ)
    (hfl : ∀ p, τ p fl = p fl) : cnotAuxFlipShape fl (fun p => τ (σ (τ p))) := by
  obtain ⟨G, hσ, hG⟩ := hσ
  refine ⟨fun p => G (τ p), ?_, ?_⟩
  · intro p
    show τ (σ (τ p)) = Function.update p fl (p fl ^^ G (τ p))
    rw [hσ (τ p), hcomm (τ p) (τ p fl ^^ G (τ p))]
    have h2 : τ (τ p) = p := hinv p
    have h3 : τ p fl = p fl := hfl p
    rw [h2, h3]
  · intro p b
    show G (τ (Function.update p fl b)) = G (τ p)
    rw [hcomm p b]
    exact hG (τ p) b

/-- The Boolean conjunction of the bits of `p` at the wires in `ws`, computed by `List.all` and
equal to `true` for the empty list. -/
def cnotAuxAllTrue {N : ℕ} (ws : List (Fin N)) (p : Reg N) : Bool :=
  ws.all fun w => p w

/-- The condition that `ws` and `as` each have pairwise distinct wires, are disjoint from each
other, and contain no occurrence of the flag wire `fl`. -/
def cnotAuxWiresOK {N : ℕ} (fl : Fin N) (ws as : List (Fin N)) : Prop :=
  List.Pairwise (· ≠ ·) ws ∧ List.Pairwise (· ≠ ·) as ∧ List.Disjoint ws as
    ∧ (∀ w ∈ ws, w ≠ fl) ∧ (∀ a ∈ as, a ≠ fl)

/-- The recursive macro list that uses an X on `fl` for no controls, a CNOT for one control, and
a Toffoli compute, recursive mark, and Toffoli uncompute for at least two controls. The last
case consumes the first auxiliary wire, while two or more controls with no auxiliary wire
produce the empty list. -/
def cnotAuxMarkAll {N : ℕ} (fl : Fin N) : List (Fin N) → List (Fin N) → List (cnotAuxMacro N)
  | [], _ => [cnotAuxMacro.xw fl]
  | [w], _ => [cnotAuxMacro.cxw w fl]
  | w1 :: w2 :: rest, a :: as =>
      cnotAuxMacro.tofw w1 w2 a :: cnotAuxMarkAll fl (a :: rest) as ++ [cnotAuxMacro.tofw w1 w2 a]
  | _ :: _ :: _, [] => []

/-- From `cnotAuxWiresOK fl [] as`, extracts that every auxiliary wire differs from `fl` and
that the auxiliary wires are pairwise distinct. -/
theorem cnotAux_wiresOK_nil {N : ℕ} {fl : Fin N} {as : List (Fin N)} (h : cnotAuxWiresOK fl [] as) :
    (∀ a ∈ as, a ≠ fl) ∧ List.Pairwise (· ≠ ·) as := ⟨h.2.2.2.2, h.2.1⟩

/-- From `cnotAuxWiresOK fl (w :: ws) as`, extracts that `w` and every wire in `ws` differ from
`fl`, that `ws` has pairwise distinct wires, and that `w` differs from every wire in `ws`. -/
theorem cnotAux_wiresOK_cons {N : ℕ} {fl : Fin N} {w : Fin N} {ws as : List (Fin N)}
    (h : cnotAuxWiresOK fl (w :: ws) as) :
    w ≠ fl ∧ (∀ x ∈ ws, x ≠ fl) ∧ List.Pairwise (· ≠ ·) ws ∧ (∀ x ∈ ws, w ≠ x) := by
  have hp := h.1
  simp only [List.pairwise_cons] at hp
  exact ⟨h.2.2.2.1 w List.mem_cons_self, fun x hx => h.2.2.2.1 x (List.mem_cons_of_mem _ hx),
    hp.2, hp.1⟩

/-- A valid wire layout with controls `w1 :: w2 :: rest` and auxiliaries `a :: as` yields a
valid layout with controls `a :: rest` and auxiliaries `as`. It also ensures that the
Toffoli macro on `w1`, `w2`, and `a` satisfies `cnotAuxMacroOk`, that these three wires are
pairwise distinct, and that `a` differs from `fl`. -/
theorem cnotAux_wiresOK_step {N : ℕ} {fl : Fin N} {w1 w2 a : Fin N} {rest as : List (Fin N)}
    (h : cnotAuxWiresOK fl (w1 :: w2 :: rest) (a :: as)) :
    cnotAuxWiresOK fl (a :: rest) as ∧ cnotAuxMacroOk (cnotAuxMacro.tofw w1 w2 a)
      ∧ w1 ≠ w2 ∧ w1 ≠ a ∧ w2 ≠ a ∧ a ≠ fl := by
  have hws : List.Pairwise (· ≠ ·) (w1 :: w2 :: rest) := h.1
  have has : List.Pairwise (· ≠ ·) (a :: as) := h.2.1
  have hdis : List.Disjoint (w1 :: w2 :: rest) (a :: as) := h.2.2.1
  have hflw : ∀ w ∈ w1 :: w2 :: rest, w ≠ fl := h.2.2.2.1
  have hfla : ∀ x ∈ a :: as, x ≠ fl := h.2.2.2.2
  simp only [List.pairwise_cons] at hws has
  have hmemRest : ∀ x ∈ rest, x ∈ w1 :: w2 :: rest :=
    fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
  have ha_notin : a ∉ w1 :: w2 :: rest := fun hh =>
    List.disjoint_left.mp hdis hh (List.mem_cons_self)
  have ha_ne_rest : ∀ x ∈ rest, a ≠ x := fun x hx hax =>
    ha_notin (hax ▸ hmemRest x hx)
  have ha_notin_as : a ∉ as := fun hx => has.1 a hx rfl
  have hw1_ne_a : w1 ≠ a := by
    intro h
    rw [← h] at ha_notin
    exact ha_notin List.mem_cons_self
  have hw2_ne_a : w2 ≠ a := by
    intro h
    rw [← h] at ha_notin
    exact ha_notin (List.mem_cons_of_mem _ List.mem_cons_self)
  have hdis' : List.Disjoint (a :: rest) as := by
    intro x hx1 hx2
    rcases List.mem_cons.mp hx1 with rfl | hx1
    · exact ha_notin_as hx2
    · exact List.disjoint_left.mp hdis (hmemRest x hx1) (List.mem_cons_of_mem _ hx2)
  have hpairA : List.Pairwise (· ≠ ·) (a :: rest) :=
    List.Pairwise.cons ha_ne_rest hws.2.2
  refine ⟨⟨hpairA, has.2, hdis', ?_, ?_⟩,
    ⟨hws.1 w2 (List.mem_cons_self), hw1_ne_a, hw2_ne_a⟩, hws.1 w2 (List.mem_cons_self),
    hw1_ne_a, hw2_ne_a, hfla a (List.mem_cons_self)⟩
  · intro w hw
    rcases List.mem_cons.mp hw with hw | hw
    · rw [hw]
      exact hfla a (List.mem_cons_self)
    · exact hflw w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
  · intro x hx
    exact hfla x (List.mem_cons_of_mem _ hx)

/-- The register permutation `cnotAuxMacroPerm (cnotAuxMacro.tofw a b t)` is an involution when
its three wires are pairwise distinct. -/
theorem cnotAux_tofPerm_involutive {N : ℕ} (a b t : Fin N) (_hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) : Function.Involutive (cnotAuxMacroPerm (cnotAuxMacro.tofw a b t)) := by
  intro p
  have ha : Function.update p t (p t ^^ (p a && p b)) a = p a :=
    Function.update_of_ne hat _ _
  have hb : Function.update p t (p t ^^ (p a && p b)) b = p b :=
    Function.update_of_ne hbt _ _
  have ht : Function.update p t (p t ^^ (p a && p b)) t = (p t ^^ (p a && p b)) :=
    Function.update_self _ _ _
  simp only [cnotAuxMacroPerm, ha, hb, ht]
  simp [Function.update, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, hat, hbt]

/-- The Toffoli register map on wires `a`, `b`, and `t` commutes with updating a wire `fl`
distinct from all three. -/
theorem cnotAux_tofPerm_comm {N : ℕ} (a b t fl : Fin N) (hfl : fl ≠ a ∧ fl ≠ b ∧ fl ≠ t) (p : Reg N)
    (c : Bool) :
    cnotAuxMacroPerm (cnotAuxMacro.tofw a b t) (Function.update p fl c)
      = Function.update (cnotAuxMacroPerm (cnotAuxMacro.tofw a b t) p) fl c := by
  have ha : Function.update p fl c a = p a := Function.update_of_ne (Ne.symm hfl.1) _ _
  have hb : Function.update p fl c b = p b := Function.update_of_ne (Ne.symm hfl.2.1) _ _
  have ht : Function.update p fl c t = p t := Function.update_of_ne (Ne.symm hfl.2.2) _ _
  simp only [cnotAuxMacroPerm, ha, hb, ht]
  funext k
  by_cases hk : k = fl
  · rw [hk]
    have h1 : Function.update (Function.update p fl c) t (p t ^^ (p a && p b)) fl
        = (Function.update p fl c) fl := Function.update_of_ne hfl.2.2 _ _
    have h2 : (Function.update p fl c) fl = c := Function.update_self _ _ _
    have h3 : Function.update (Function.update p t (p t ^^ (p a && p b))) fl c fl = c :=
      Function.update_self _ _ _
    rw [h1, h2, h3]
  · by_cases hkt : k = t
    · rw [hkt]
      have h1 : Function.update (Function.update p fl c) t (p t ^^ (p a && p b)) t
          = (p t ^^ (p a && p b)) := Function.update_self _ _ _
      have h2 : Function.update (Function.update p t (p t ^^ (p a && p b))) fl c t
          = (Function.update p t (p t ^^ (p a && p b))) t :=
        Function.update_of_ne (Ne.symm hfl.2.2) _ _
      have h3 : (Function.update p t (p t ^^ (p a && p b))) t = (p t ^^ (p a && p b)) :=
        Function.update_self _ _ _
      rw [h1, h2, h3]
    · have h1 : Function.update (Function.update p fl c) t (p t ^^ (p a && p b)) k
          = (Function.update p fl c) k := Function.update_of_ne hkt _ _
      have h2 : (Function.update p fl c) k = p k := Function.update_of_ne hk _ _
      have h3 : Function.update (Function.update p t (p t ^^ (p a && p b))) fl c k
          = Function.update p t (p t ^^ (p a && p b)) k := Function.update_of_ne hk _ _
      have h4 : Function.update p t (p t ^^ (p a && p b)) k = p k := Function.update_of_ne hkt _ _
      rw [h1, h2, h3, h4]

/-- The Toffoli register map on wires `a`, `b`, and `t` preserves the bit at any wire `fl`
distinct from all three. -/
theorem cnotAux_tofPerm_fl {N : ℕ} (a b t fl : Fin N) (hfl : fl ≠ a ∧ fl ≠ b ∧ fl ≠ t) (p : Reg N) :
    cnotAuxMacroPerm (cnotAuxMacro.tofw a b t) p fl = p fl :=
  Function.update_of_ne hfl.2.2 _ _

/-- Two Boolean functions that agree on every wire in `ws` have equal conjunctions under
`ws.all`. -/
theorem cnotAux_all_congr {N : ℕ} (ws : List (Fin N)) (f g : Fin N → Bool)
    (h : ∀ w ∈ ws, f w = g w) : ws.all f = ws.all g := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have h1 : f w = g w := h w (List.mem_cons_self)
    have h2 : ws.all f = ws.all g := ih (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))
    simp only [List.all_cons, h1, h2]

/-- The conjunction `cnotAuxAllTrue (w :: ws) p` equals the Boolean conjunction of `p w` and
`cnotAuxAllTrue ws p`. -/
theorem cnotAux_allTrue_cons {N : ℕ} (w : Fin N) (ws : List (Fin N)) (p : Reg N) :
    cnotAuxAllTrue (w :: ws) p = (p w && cnotAuxAllTrue ws p) := by
  simp [cnotAuxAllTrue, List.all_cons]

/-- For a layout satisfying `cnotAuxWiresOK` with `ws.length ≤ as.length + 1`, the fold of
`cnotAuxMarkAll fl ws as` changes only `fl` by XOR with a Boolean function invariant under
updates to `fl`. When every auxiliary wire in `as` is zero, this function equals
`cnotAuxAllTrue ws`. -/
theorem cnotAux_markAll_shape {N : ℕ} (fl : Fin N) :
    ∀ (ws as : List (Fin N)), cnotAuxWiresOK fl ws as → ws.length ≤ as.length + 1 →
    ∃ G : Reg N → Bool,
      (∀ p, cnotAuxFold (cnotAuxMarkAll fl ws as) p = Function.update p fl (p fl ^^ G p))
      ∧ (∀ p b, G (Function.update p fl b) = G p)
      ∧ (∀ p, (∀ a ∈ as, p a = false) → G p = cnotAuxAllTrue ws p) := by
  suffices hgen : ∀ (k : ℕ) (ws as : List (Fin N)), ws.length = k → cnotAuxWiresOK fl ws as →
      ws.length ≤ as.length + 1 →
      (∃ G : Reg N → Bool,
        (∀ p, cnotAuxFold (cnotAuxMarkAll fl ws as) p = Function.update p fl (p fl ^^ G p))
        ∧ (∀ p b, G (Function.update p fl b) = G p)
        ∧ (∀ p, (∀ a ∈ as, p a = false) → G p = cnotAuxAllTrue ws p)) by
    intro ws as hok hlen
    exact hgen ws.length ws as rfl hok hlen
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro ws as hk hok hlen
    cases ws with
    | nil =>
      refine ⟨fun _ => true, ?_, ?_, ?_⟩
      · intro p
        simp [cnotAuxMarkAll, cnotAuxFold, cnotAuxMacroPerm, List.foldl_cons, List.foldl_nil,
          Function.update, Bool.xor_true]
      · intro p b; rfl
      · intro p _; rfl
    | cons w ws' =>
      cases ws' with
      | nil =>
        have hwfl : w ≠ fl := (cnotAux_wiresOK_cons hok).1
        refine ⟨fun p => p w, ?_, ?_, ?_⟩
        · intro p
          simp [cnotAuxMarkAll, cnotAuxFold, cnotAuxMacroPerm, List.foldl_cons, List.foldl_nil,
            Function.update]
        · intro p b
          show (Function.update p fl b) w = p w
          exact Function.update_of_ne hwfl b p
        · intro p _
          simp [cnotAuxAllTrue]
      | cons w2 rest =>
        cases as with
        | nil =>
          exfalso
          simp only [List.length_cons, List.length_nil] at hlen
          omega
        | cons a as' =>
          obtain ⟨hok', htof, hw12, hw1a, hw2a, hafl⟩ := cnotAux_wiresOK_step hok
          have hlen' : (a :: rest).length ≤ as'.length + 1 := by
            simp only [List.length_cons] at hlen ⊢
            omega
          have hk' : (a :: rest).length < k := by
            rw [← hk]
            simp only [List.length_cons]
            omega
          obtain ⟨G, hG, hGfl, hGclean⟩ := ih (a :: rest).length hk' (a :: rest) as' rfl hok' hlen'
          set τ : Reg N → Reg N := cnotAuxMacroPerm (cnotAuxMacro.tofw w w2 a) with hτ
          have hτinv : Function.Involutive τ := by
            rw [hτ]
            exact cnotAux_tofPerm_involutive w w2 a hw12 hw1a hw2a
          have hflall : (fl ≠ w ∧ fl ≠ w2 ∧ fl ≠ a) :=
            ⟨Ne.symm (hok.2.2.2.1 w (List.mem_cons_self)),
              Ne.symm (hok.2.2.2.1 w2 (List.mem_cons_of_mem _ (List.mem_cons_self))),
              Ne.symm hafl⟩
          have hτcomm : ∀ (p : Reg N) (b : Bool),
              τ (Function.update p fl b) = Function.update (τ p) fl b := by
            intro p b
            rw [hτ]
            exact cnotAux_tofPerm_comm w w2 a fl hflall p b
          have hτfl : ∀ p : Reg N, τ p fl = p fl := by
            intro p
            rw [hτ]
            exact cnotAux_tofPerm_fl w w2 a fl hflall p
          have hτa : ∀ p : Reg N, τ p a = (p a ^^ (p w && p w2)) := by
            intro p
            rw [hτ]
            simp only [cnotAuxMacroPerm, Function.update_self]
          have hτne : ∀ (p : Reg N) (x : Fin N), x ≠ a → τ p x = p x := by
            intro p x hx
            rw [hτ]
            simp only [cnotAuxMacroPerm]
            exact Function.update_of_ne hx _ _
          refine ⟨fun p => G (τ p), ?_, ?_, ?_⟩
          · intro p
            have hfold : cnotAuxFold (cnotAuxMarkAll fl (w :: w2 :: rest) (a :: as')) p
                = τ (cnotAuxFold (cnotAuxMarkAll fl (a :: rest) as') (τ p)) := by
              rw [show cnotAuxMarkAll fl (w :: w2 :: rest) (a :: as')
                  = (cnotAuxMacro.tofw w w2 a :: cnotAuxMarkAll fl (a :: rest) as')
                      ++ [cnotAuxMacro.tofw w w2 a] from rfl,
                cnotAux_fold_append, cnotAux_fold_cons]
              simp only [cnotAuxFold, List.foldl_cons, List.foldl_nil, hτ]
            rw [hfold, hG, hτcomm, hτinv p, hτfl p]
          · intro p b
            show G (τ (Function.update p fl b)) = G (τ p)
            rw [hτcomm p b, hGfl]
          · intro p hp
            show G (τ p) = cnotAuxAllTrue (w :: w2 :: rest) p
            have hpas : ∀ x ∈ as', p x = false := fun x hx => hp x (List.mem_cons_of_mem _ hx)
            have hτas : ∀ x ∈ as', τ p x = p x := by
              intro x hx
              apply hτne
              intro hax
              exact List.disjoint_left.mp hok'.2.2.1 List.mem_cons_self (by rw [← hax]; exact hx)
            have hGτ : G (τ p) = cnotAuxAllTrue (a :: rest) (τ p) := hGclean (τ p) (by
              intro x hx
              rw [hτas x hx]
              exact hpas x hx)
            rw [hGτ, cnotAux_allTrue_cons]
            have hrest : cnotAuxAllTrue rest (τ p) = cnotAuxAllTrue rest p :=
              cnotAux_all_congr rest _ _ (fun x hx => hτne p x
                (fun hax => (List.pairwise_cons.mp hok'.1).1 x hx hax.symm))
            rw [hrest, hτa]
            have hpa : p a = false := hp a (List.mem_cons_self)
            rw [hpa, Bool.false_xor, Bool.and_assoc]
            simp only [cnotAux_allTrue_cons]

/-- The total register size `n + (n + 2) + 1`, comprising `n` witness wires, `n + 2` auxiliary
wires, and one output wire. -/
def cnotAuxN (n : ℕ) : ℕ := n + (n + 2) + 1

/-- The embedding of witness index `i : Fin n` into `Fin (cnotAuxN n)` at the same numeric index
`i.val`. -/
def cnotAuxWit (n : ℕ) (i : Fin n) : Fin (cnotAuxN n) :=
    ⟨i.val, by have h := i.isLt; show i.val < n + (n + 2) + 1; omega⟩

/-- The first flag wire, located at numeric index `n` in the register of size `cnotAuxN n`. -/
def cnotAuxFlS (n : ℕ) : Fin (cnotAuxN n) := ⟨n, by show n < n + (n + 2) + 1; omega⟩

/-- The second flag wire, located at numeric index `n + 1` in the register of size `cnotAuxN n`. -/
def cnotAuxFlU (n : ℕ) : Fin (cnotAuxN n) := ⟨n + 1, by show n + 1 < n + (n + 2) + 1; omega⟩

/-- The ladder auxiliary wire associated with `j : Fin n`, located at numeric index `n + 2 +
j.val`. -/
def cnotAuxLad (n : ℕ) (j : Fin n) : Fin (cnotAuxN n) :=
    ⟨n + 2 + j.val, by have h := j.isLt; show n + 2 + j.val < n + (n + 2) + 1; omega⟩

/-- The output wire at numeric index `2 * n + 2`, the last wire in the register of size
`cnotAuxN n`. -/
def cnotAuxOut (n : ℕ) : Fin (cnotAuxN n) := ⟨2 * n + 2, by show 2 * n + 2 < n + (n + 2) + 1; omega⟩

/-- The witness subregister of `p`, obtained by restricting it to the wires `cnotAuxWit n i` for
`i : Fin n`. -/
def cnotAuxWitPart {n : ℕ} (p : Reg (cnotAuxN n)) : Reg n := fun i => p (cnotAuxWit n i)

/-- The condition that every ladder auxiliary wire `cnotAuxLad n j` of `p` has bit value
`false`. -/
def cnotAuxLadZero {n : ℕ} (p : Reg (cnotAuxN n)) : Prop := ∀ j : Fin n, p (cnotAuxLad n j) = false

/-- The list of all witness wires, obtained by mapping `cnotAuxWit n` over `List.finRange n` in
increasing index order. -/
def cnotAuxWitL (n : ℕ) : List (Fin (cnotAuxN n)) := (List.finRange n).map (cnotAuxWit n)

/-- The list of all ladder auxiliary wires, obtained by mapping `cnotAuxLad n` over
`List.finRange n` in increasing index order. -/
def cnotAuxLadL (n : ℕ) : List (Fin (cnotAuxN n)) := (List.finRange n).map (cnotAuxLad n)

/-- Equality of the embedded witness wires `cnotAuxWit n i` and `cnotAuxWit n j` implies `i =
j`. -/
theorem cnotAux_wit_inj {n : ℕ} {i j : Fin n} (h : cnotAuxWit n i = cnotAuxWit n j) : i = j := by
  apply Fin.val_injective
  simpa [cnotAuxWit] using congrArg Fin.val h

/-- Every witness wire `cnotAuxWit n i` differs from every ladder auxiliary wire `cnotAuxLad n
j`. -/
theorem cnotAux_wit_ne_lad {n : ℕ} (i j : Fin n) : cnotAuxWit n i ≠ cnotAuxLad n j := by
  intro h
  have h2 := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  simp only [cnotAuxWit, cnotAuxLad, cnotAuxFlS, cnotAuxFlU, cnotAuxOut] at h2
  clear h
  omega

/-- Every witness wire `cnotAuxWit n i` differs from the first flag wire `cnotAuxFlS n`. -/
theorem cnotAux_wit_ne_flS {n : ℕ} (i : Fin n) : cnotAuxWit n i ≠ cnotAuxFlS n := by
  intro h
  have h2 := congrArg Fin.val h
  have hi := i.isLt
  simp only [cnotAuxWit, cnotAuxLad, cnotAuxFlS, cnotAuxFlU, cnotAuxOut] at h2
  clear h
  omega

/-- Every witness wire `cnotAuxWit n i` differs from the second flag wire `cnotAuxFlU n`. -/
theorem cnotAux_wit_ne_flU {n : ℕ} (i : Fin n) : cnotAuxWit n i ≠ cnotAuxFlU n := by
  intro h
  have h2 := congrArg Fin.val h
  have hi := i.isLt
  simp only [cnotAuxWit, cnotAuxLad, cnotAuxFlS, cnotAuxFlU, cnotAuxOut] at h2
  clear h
  omega

/-- Every witness wire `cnotAuxWit n i` differs from the output wire `cnotAuxOut n`. -/
theorem cnotAux_wit_ne_out {n : ℕ} (i : Fin n) : cnotAuxWit n i ≠ cnotAuxOut n := by
  intro h
  have h2 := congrArg Fin.val h
  have hi := i.isLt
  simp only [cnotAuxWit, cnotAuxLad, cnotAuxFlS, cnotAuxFlU, cnotAuxOut] at h2
  clear h
  omega

/-- Every ladder auxiliary wire `cnotAuxLad n j` differs from the first flag wire `cnotAuxFlS
n`. -/
theorem cnotAux_lad_ne_flS {n : ℕ} (j : Fin n) : cnotAuxLad n j ≠ cnotAuxFlS n := by
  intro h
  have h2 := congrArg Fin.val h
  have hj := j.isLt
  simp only [cnotAuxWit, cnotAuxLad, cnotAuxFlS, cnotAuxFlU, cnotAuxOut] at h2
  clear h
  omega

/-- Every ladder auxiliary wire `cnotAuxLad n j` differs from the second flag wire `cnotAuxFlU
n`. -/
theorem cnotAux_lad_ne_flU {n : ℕ} (j : Fin n) : cnotAuxLad n j ≠ cnotAuxFlU n := by
  intro h
  have h2 := congrArg Fin.val h
  have hj := j.isLt
  simp only [cnotAuxWit, cnotAuxLad, cnotAuxFlS, cnotAuxFlU, cnotAuxOut] at h2
  clear h
  omega

/-- Every ladder auxiliary wire `cnotAuxLad n j` differs from the output wire `cnotAuxOut n`. -/
theorem cnotAux_lad_ne_out {n : ℕ} (j : Fin n) : cnotAuxLad n j ≠ cnotAuxOut n := by
  intro h
  have h2 := congrArg Fin.val h
  have hj := j.isLt
  simp only [cnotAuxWit, cnotAuxLad, cnotAuxFlS, cnotAuxFlU, cnotAuxOut] at h2
  clear h
  omega

/-- The two flag wires `cnotAuxFlS n` and `cnotAuxFlU n` are distinct. -/
theorem cnotAux_flS_ne_flU {n : ℕ} : cnotAuxFlS n ≠ cnotAuxFlU n := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [cnotAuxWit, cnotAuxLad, cnotAuxFlS, cnotAuxFlU, cnotAuxOut] at h2
  clear h
  omega

/-- The first flag wire `cnotAuxFlS n` differs from the output wire `cnotAuxOut n`. -/
theorem cnotAux_flS_ne_out {n : ℕ} : cnotAuxFlS n ≠ cnotAuxOut n := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [cnotAuxWit, cnotAuxLad, cnotAuxFlS, cnotAuxFlU, cnotAuxOut] at h2
  clear h
  omega

/-- The second flag wire `cnotAuxFlU n` differs from the output wire `cnotAuxOut n`. -/
theorem cnotAux_flU_ne_out {n : ℕ} : cnotAuxFlU n ≠ cnotAuxOut n := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [cnotAuxWit, cnotAuxLad, cnotAuxFlS, cnotAuxFlU, cnotAuxOut] at h2
  clear h
  omega

/-- Equality of the ladder wires `cnotAuxLad n i` and `cnotAuxLad n j` implies `i = j`. -/
theorem cnotAux_lad_inj {n : ℕ} {i j : Fin n} (h : cnotAuxLad n i = cnotAuxLad n j) : i = j := by
  apply Fin.val_injective
  simpa [cnotAuxLad] using congrArg Fin.val h

/-- The witness wire list `cnotAuxWitL n` contains no duplicate entries. -/
theorem cnotAux_witL_nodup (n : ℕ) : (cnotAuxWitL n).Nodup := by
  simp only [cnotAuxWitL]
  exact List.Nodup.map (fun i j h => cnotAux_wit_inj h) (List.nodup_finRange n)

/-- The ladder auxiliary wire list `cnotAuxLadL n` contains no duplicate entries. -/
theorem cnotAux_ladL_nodup (n : ℕ) : (cnotAuxLadL n).Nodup := by
  simp only [cnotAuxLadL]
  exact List.Nodup.map (fun i j h => cnotAux_lad_inj h) (List.nodup_finRange n)

/-- A wire belongs to `cnotAuxWitL n` exactly when it equals `cnotAuxWit n i` for some `i : Fin
n`. -/
theorem cnotAux_witL_mem {n : ℕ} {w : Fin (cnotAuxN n)} :
    w ∈ cnotAuxWitL n ↔ ∃ i : Fin n, cnotAuxWit n i = w := by
  simp [cnotAuxWitL]

/-- A wire belongs to `cnotAuxLadL n` exactly when it equals `cnotAuxLad n j` for some `j : Fin
n`. -/
theorem cnotAux_ladL_mem {n : ℕ} {w : Fin (cnotAuxN n)} :
    w ∈ cnotAuxLadL n ↔ ∃ j : Fin n, cnotAuxLad n j = w := by
  simp [cnotAuxLadL]

/-- The entries of the witness wire list `cnotAuxWitL n` are pairwise unequal. -/
theorem cnotAux_witL_pairwise (n : ℕ) : List.Pairwise (· ≠ ·) (cnotAuxWitL n) :=
  List.nodup_iff_pairwise_ne.mp (cnotAux_witL_nodup n)

/-- The entries of the ladder auxiliary wire list `cnotAuxLadL n` are pairwise unequal. -/
theorem cnotAux_ladL_pairwise (n : ℕ) : List.Pairwise (· ≠ ·) (cnotAuxLadL n) :=
  List.nodup_iff_pairwise_ne.mp (cnotAux_ladL_nodup n)

/-- The witness wire list `cnotAuxWitL n` and ladder auxiliary wire list `cnotAuxLadL n` are
disjoint. -/
theorem cnotAux_witL_disj_ladL (n : ℕ) : List.Disjoint (cnotAuxWitL n) (cnotAuxLadL n) := by
  intro w hw1 hw2
  obtain ⟨i, hi⟩ := cnotAux_witL_mem.mp hw1
  obtain ⟨j, hj⟩ := cnotAux_ladL_mem.mp hw2
  rw [← hi] at hj
  exact cnotAux_wit_ne_lad i j hj.symm

/-- The witness and ladder wire lists satisfy `cnotAuxWiresOK` with the first flag wire
`cnotAuxFlS n`. -/
theorem cnotAux_wiresOK_flS (n : ℕ) :
    cnotAuxWiresOK (cnotAuxFlS n) (cnotAuxWitL n) (cnotAuxLadL n) := by
  refine ⟨cnotAux_witL_pairwise n, cnotAux_ladL_pairwise n, cnotAux_witL_disj_ladL n, ?_, ?_⟩
  · intro w hw
    obtain ⟨i, hi⟩ := cnotAux_witL_mem.mp hw
    rw [← hi]
    exact cnotAux_wit_ne_flS i
  · intro a ha
    obtain ⟨j, hj⟩ := cnotAux_ladL_mem.mp ha
    rw [← hj]
    exact cnotAux_lad_ne_flS j

/-- The witness and ladder wire lists satisfy `cnotAuxWiresOK` with the second flag wire
`cnotAuxFlU n`. -/
theorem cnotAux_wiresOK_flU (n : ℕ) :
    cnotAuxWiresOK (cnotAuxFlU n) (cnotAuxWitL n) (cnotAuxLadL n) := by
  refine ⟨cnotAux_witL_pairwise n, cnotAux_ladL_pairwise n, cnotAux_witL_disj_ladL n, ?_, ?_⟩
  · intro w hw
    obtain ⟨i, hi⟩ := cnotAux_witL_mem.mp hw
    rw [← hi]
    exact cnotAux_wit_ne_flU i
  · intro a ha
    obtain ⟨j, hj⟩ := cnotAux_ladL_mem.mp ha
    rw [← hj]
    exact cnotAux_lad_ne_flU j

/-- The witness wire list `cnotAuxWitL n` has length `n`. -/
theorem cnotAux_witL_len (n : ℕ) : (cnotAuxWitL n).length = n := by
  simp [cnotAuxWitL]

/-- The ladder auxiliary wire list `cnotAuxLadL n` has length `n`. -/
theorem cnotAux_ladL_len (n : ℕ) : (cnotAuxLadL n).length = n := by
  simp [cnotAuxLadL]

/-- The list of X macros on witness wires `cnotAuxWit n i` for precisely those indices where `z
i = false`, in increasing index order. -/
def cnotAuxXConj {n : ℕ} (z : Reg n) : List (cnotAuxMacro (cnotAuxN n)) :=
  ((List.finRange n).filter (fun i => decide (z i = false))).map (fun i => cnotAuxMacro.xw (cnotAuxWit n i))

/-- The macro list `cnotAuxXConj z`, followed by `cnotAuxMarkAll` on the witness and ladder wire
lists with flag `fl`, followed by `cnotAuxXConj z` again. -/
def cnotAuxMarkOne {n : ℕ} (fl : Fin (cnotAuxN n)) (z : Reg n) : List (cnotAuxMacro (cnotAuxN n)) :=
  cnotAuxXConj z ++ cnotAuxMarkAll fl (cnotAuxWitL n) (cnotAuxLadL n) ++ cnotAuxXConj z

/-- The macro list formed by concatenating `cnotAuxMarkOne fl z` over the `Finset.toList`
enumeration of all words `z : Reg n` satisfying `f z = true`. -/
noncomputable def cnotAuxMarkWord {n : ℕ} (fl : Fin (cnotAuxN n)) (f : Reg n → Bool) :
    List (cnotAuxMacro (cnotAuxN n)) :=
  ((Finset.univ.filter (fun z : Reg n => f z)).toList).flatMap (cnotAuxMarkOne fl)

/-- Folding X macros over a list `ws` without duplicates negates exactly the bits at wires
belonging to `ws` and preserves every other bit. -/
theorem cnotAux_fold_xw {N : ℕ} (ws : List (Fin N)) (hws : ws.Nodup) :
    cnotAuxFold (ws.map cnotAuxMacro.xw) = (fun p k => if k ∈ ws then Bool.not (p k) else p k) := by
  induction ws with
  | nil =>
    funext p k
    simp [cnotAuxFold]
  | cons w ws ih =>
    have hrest : ws.Nodup := (List.nodup_cons.mp hws).2
    have hw : w ∉ ws := (List.nodup_cons.mp hws).1
    have hih := ih hrest
    funext p k
    simp only [List.map_cons, cnotAux_fold_cons, cnotAuxMacroPerm, hih, List.mem_cons]
    by_cases hk : k = w
    · subst hk
      simp [Function.update, hw]
    · have h1 : (Function.update p w (Bool.not (p w))) k = p k := Function.update_of_ne hk _ _
      rw [h1]
      by_cases hk2 : k ∈ ws <;> simp [hk, hk2]

/-- For a list `zs` without duplicates, the right fold of the Booleans `decide (x = z)` by XOR,
starting at `false`, equals `decide (x ∈ zs)`. -/
theorem cnotAux_xor_decide {α : Type*} [DecidableEq α] (zs : List α) (hzs : zs.Nodup) (x : α) :
    zs.foldr (fun z acc => decide (x = z) ^^ acc) false = decide (x ∈ zs) := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hrest : zs.Nodup := (List.nodup_cons.mp hzs).2
    have hz : z ∉ zs := (List.nodup_cons.mp hzs).1
    simp only [List.foldr_cons, List.mem_cons]
    by_cases hx : x = z
    · have hmem : ¬ (x ∈ zs) := by
        intro hh
        rw [hx] at hh
        exact hz hh
      subst hx
      simp [ih hrest, hmem]
    · simp [hx, ih hrest]

/-- The register map obtained by folding `cnotAuxXConj z` negates precisely the witness wires
whose corresponding bit of `z` is `false` and preserves all other wires. -/
theorem cnotAux_xConj_perm {n : ℕ} (z : Reg n) (p : Reg (cnotAuxN n)) :
    cnotAuxFold (cnotAuxXConj z) p
      = (fun k => if ∃ i : Fin n, cnotAuxWit n i = k ∧ z i = false then Bool.not (p k) else p k) := by
  have hndL : ((List.finRange n).filter (fun i => decide (z i = false))).Nodup :=
    List.Nodup.sublist (List.filter_sublist) (List.nodup_finRange n)
  have hnd : ((List.finRange n).filter (fun i => decide (z i = false)) |>.map (cnotAuxWit n)).Nodup :=
    List.Nodup.map (fun i j h => cnotAux_wit_inj h) hndL
  have hkey2 : cnotAuxXConj z
      = (((List.finRange n).filter (fun i => decide (z i = false))).map (cnotAuxWit n)).map cnotAuxMacro.xw := by
    simp only [cnotAuxXConj, List.map_map]
    rfl
  rw [hkey2, cnotAux_fold_xw _ hnd]
  funext k
  simp only []
  by_cases hk : ∃ i : Fin n, cnotAuxWit n i = k ∧ z i = false
  · obtain ⟨i, hi, hzi⟩ := hk
    have hmem : k ∈ List.map (cnotAuxWit n) ((List.finRange n).filter (fun i => decide (z i = false))) := by
      rw [← hi]
      refine List.mem_map.mpr ⟨i, ?_, rfl⟩
      simp only [List.mem_filter, List.mem_finRange, true_and]
      exact decide_eq_true hzi
    rw [if_pos hmem, if_pos ⟨i, hi, hzi⟩]
  · have hmem : k ∉ List.map (cnotAuxWit n) ((List.finRange n).filter (fun i => decide (z i = false))) := by
      intro hh
      obtain ⟨i, hi, heq⟩ := List.mem_map.mp hh
      simp only [List.mem_filter, List.mem_finRange, true_and] at hi
      exact hk ⟨i, heq, of_decide_eq_true hi⟩
    rw [if_neg hmem, if_neg hk]

/-- At a wire `k`, the fold of `cnotAuxXConj z` returns `Bool.not (p k)` exactly when `k =
cnotAuxWit n i` for some index with `z i = false`, and returns `p k` otherwise. -/
theorem cnotAux_xConj_perm_apply {n : ℕ} (z : Reg n) (p : Reg (cnotAuxN n)) (k : Fin (cnotAuxN n)) :
    cnotAuxFold (cnotAuxXConj z) p k
      = if ∃ i : Fin n, cnotAuxWit n i = k ∧ z i = false then Bool.not (p k) else p k := by
  rw [cnotAux_xConj_perm]

/-- Applying the register map obtained by folding `cnotAuxXConj z` twice returns the original
register `p`. -/
theorem cnotAux_xConj_involutive {n : ℕ} (z : Reg n) (p : Reg (cnotAuxN n)) :
    cnotAuxFold (cnotAuxXConj z) (cnotAuxFold (cnotAuxXConj z) p) = p := by
  funext k
  rw [cnotAux_xConj_perm_apply, cnotAux_xConj_perm_apply]
  by_cases hk : ∃ i : Fin n, cnotAuxWit n i = k ∧ z i = false
  · rw [if_pos hk, if_pos hk]
    cases p k <;> rfl
  · rw [if_neg hk, if_neg hk]

/-- Updating a register at wire `a` to `v` and then to `w` equals updating it once at `a` to
`w`. -/
theorem cnotAux_update_update {N : ℕ} (f : Reg N) (a : Fin N) (v w : Bool) :
    Function.update (Function.update f a v) a w = Function.update f a w := by
  funext k
  by_cases hk : k = a
  · rw [hk]
    simp [Function.update]
  · simp [Function.update, hk]

/-- The condition `cnotAuxLadZero p` is equivalent to every wire in `cnotAuxLadL n` having bit
value `false` in `p`. -/
theorem cnotAux_ladZero_iff {n : ℕ} (p : Reg (cnotAuxN n)) :
    cnotAuxLadZero p ↔ ∀ a ∈ cnotAuxLadL n, p a = false := by
  constructor
  · intro h a ha
    obtain ⟨j, hj⟩ := cnotAux_ladL_mem.mp ha
    rw [← hj]
    exact h j
  · intro h j
    exact h (cnotAuxLad n j) (cnotAux_ladL_mem.mpr ⟨j, rfl⟩)

/-- The fold of `cnotAuxXConj z` preserves the bit at `fl` whenever every wire in `cnotAuxWitL
n` differs from `fl`. -/
theorem cnotAux_xConj_fl {n : ℕ} (z : Reg n) (fl : Fin (cnotAuxN n))
    (hfl : ∀ w ∈ cnotAuxWitL n, w ≠ fl) (p : Reg (cnotAuxN n)) :
    cnotAuxFold (cnotAuxXConj z) p fl = p fl := by
  rw [cnotAux_xConj_perm]
  simp only []
  have hne : ¬ (∃ i : Fin n, cnotAuxWit n i = fl ∧ z i = false) := by
    intro hh
    obtain ⟨i, hi, _⟩ := hh
    exact hfl (cnotAuxWit n i) (cnotAux_witL_mem.mpr ⟨i, rfl⟩) hi
  rw [if_neg hne]

/-- The fold of `cnotAuxXConj z` commutes with any update to `fl` whenever every wire in
`cnotAuxWitL n` differs from `fl`. -/
theorem cnotAux_xConj_comm {n : ℕ} (z : Reg n) (fl : Fin (cnotAuxN n))
    (hfl : ∀ w ∈ cnotAuxWitL n, w ≠ fl) (p : Reg (cnotAuxN n)) (b : Bool) :
    cnotAuxFold (cnotAuxXConj z) (Function.update p fl b)
      = Function.update (cnotAuxFold (cnotAuxXConj z) p) fl b := by
  funext k
  by_cases hk : k = fl
  · rw [hk]
    have hne : ¬ (∃ i : Fin n, cnotAuxWit n i = fl ∧ z i = false) := by
      intro hh
      obtain ⟨i, hi, _⟩ := hh
      exact hfl (cnotAuxWit n i) (cnotAux_witL_mem.mpr ⟨i, rfl⟩) hi
    rw [cnotAux_xConj_perm_apply z (Function.update p fl b) fl, if_neg hne,
        Function.update_self fl b p, Function.update_self fl b (cnotAuxFold (cnotAuxXConj z) p)]
  · rw [Function.update_of_ne hk b (cnotAuxFold (cnotAuxXConj z) p),
        cnotAux_xConj_perm_apply z (Function.update p fl b) k,
        cnotAux_xConj_perm_apply z p k, Function.update_of_ne hk b p]

/-- The register map obtained by folding `cnotAuxXConj z` preserves the condition
`cnotAuxLadZero`. -/
theorem cnotAux_xConj_lad {n : ℕ} (z : Reg n) (p : Reg (cnotAuxN n)) (hp : cnotAuxLadZero p) :
    cnotAuxLadZero (cnotAuxFold (cnotAuxXConj z) p) := by
  intro j
  rw [cnotAux_xConj_perm]
  simp only []
  have hne : ¬ (∃ i : Fin n, cnotAuxWit n i = cnotAuxLad n j ∧ z i = false) := by
    intro hh
    obtain ⟨i, hi, _⟩ := hh
    exact cnotAux_wit_ne_lad i j hi
  rw [if_neg hne]
  exact hp j

/-- After folding `cnotAuxXConj z`, the conjunction of all witness bits equals `decide
(cnotAuxWitPart p = z)`. -/
theorem cnotAux_xConj_allTrue {n : ℕ} (z : Reg n) (p : Reg (cnotAuxN n)) :
    cnotAuxAllTrue (cnotAuxWitL n) (cnotAuxFold (cnotAuxXConj z) p) = decide (cnotAuxWitPart p = z) := by
  have hex_iff : ∀ i : Fin n,
      ((∃ i' : Fin n, cnotAuxWit n i' = cnotAuxWit n i ∧ z i' = false) ↔ (z i = false)) := by
    intro i
    constructor
    · intro h
      obtain ⟨i', hi', hz⟩ := h
      have : i' = i := cnotAux_wit_inj hi'
      subst this
      exact hz
    · intro h
      exact ⟨i, rfl, h⟩
  have key : cnotAuxAllTrue (cnotAuxWitL n) (cnotAuxFold (cnotAuxXConj z) p) = true ↔ cnotAuxWitPart p = z := by
    constructor
    · intro hh
      have hall : ∀ w ∈ cnotAuxWitL n, cnotAuxFold (cnotAuxXConj z) p w = true :=
        List.all_eq_true.mp hh
      funext i
      have hi := hall (cnotAuxWit n i) (cnotAux_witL_mem.mpr ⟨i, rfl⟩)
      rw [cnotAux_xConj_perm] at hi
      simp only [] at hi
      by_cases hex : ∃ i', cnotAuxWit n i' = cnotAuxWit n i ∧ z i' = false
      · rw [if_pos hex] at hi
        have hzi : z i = false := (hex_iff i).mp hex
        have : p (cnotAuxWit n i) = false := by
          cases hp : p (cnotAuxWit n i) with
          | false => rfl
          | true =>
            rw [hp] at hi
            simp at hi
        simp [cnotAuxWitPart, this, hzi]
      · rw [if_neg hex] at hi
        have hzi : z i = true := by
          cases hzi : z i
          · exact absurd ((hex_iff i).mpr hzi) hex
          · rfl
        have : p (cnotAuxWit n i) = true := hi
        simp [cnotAuxWitPart, this, hzi]
    · intro hh
      apply List.all_eq_true.mpr
      intro w hw
      obtain ⟨i, hi⟩ := cnotAux_witL_mem.mp hw
      rw [← hi]
      have hi2 := congrFun hh i
      rw [cnotAux_xConj_perm]
      simp only []
      by_cases hex : ∃ i', cnotAuxWit n i' = cnotAuxWit n i ∧ z i' = false
      · rw [if_pos hex]
        have hzi : z i = false := (hex_iff i).mp hex
        have : p (cnotAuxWit n i) = false := by
          simp [cnotAuxWitPart] at hi2
          rw [hzi] at hi2
          exact hi2
        simp [Bool.not, this]
      · rw [if_neg hex]
        have hzi : z i = true := by
          cases hzi : z i
          · exact absurd ((hex_iff i).mpr hzi) hex
          · rfl
        have : p (cnotAuxWit n i) = true := by
          simp [cnotAuxWitPart] at hi2
          rw [hzi] at hi2
          exact hi2
        exact this
  by_cases h : cnotAuxWitPart p = z
  · rw [decide_eq_true h]
    exact key.mpr h
  · rw [decide_eq_false h]
    cases ha : cnotAuxAllTrue (cnotAuxWitL n) (cnotAuxFold (cnotAuxXConj z) p)
    · rfl
    · exact absurd (key.mp ha) h

/-- Under the stated `cnotAuxWiresOK` and length conditions, the fold of `cnotAuxMarkOne fl z`
changes only `fl` by XOR with a Boolean function invariant under updates to `fl`. On
registers satisfying `cnotAuxLadZero`, this function equals `decide (cnotAuxWitPart p = z)`. -/
theorem cnotAux_markOne_shape {n : ℕ} (fl : Fin (cnotAuxN n)) (z : Reg n)
    (hok : cnotAuxWiresOK fl (cnotAuxWitL n) (cnotAuxLadL n))
    (hlen : (cnotAuxWitL n).length ≤ (cnotAuxLadL n).length + 1) :
    ∃ G : Reg (cnotAuxN n) → Bool,
      (∀ p, cnotAuxFold (cnotAuxMarkOne fl z) p
        = Function.update p fl (p fl ^^ G p))
      ∧ (∀ p b, G (Function.update p fl b) = G p)
      ∧ (∀ p, cnotAuxLadZero p → G p = decide (cnotAuxWitPart p = z)) := by
  obtain ⟨G0, hG0, hG0fl, hG0clean⟩ :=
      cnotAux_markAll_shape fl (cnotAuxWitL n) (cnotAuxLadL n) hok hlen
  have hflwit : ∀ w ∈ cnotAuxWitL n, w ≠ fl := hok.2.2.2.1
  have hfold : ∀ p : Reg (cnotAuxN n),
      cnotAuxFold (cnotAuxMarkOne fl z) p
        = cnotAuxFold (cnotAuxXConj z) (cnotAuxFold (cnotAuxMarkAll fl (cnotAuxWitL n) (cnotAuxLadL n))
            (cnotAuxFold (cnotAuxXConj z) p)) := by
    intro p
    simp only [cnotAuxMarkOne, cnotAux_fold_append]
  refine ⟨fun p => G0 (cnotAuxFold (cnotAuxXConj z) p), ?_, ?_, ?_⟩
  · intro p
    rw [hfold, hG0]
    rw [cnotAux_xConj_comm z fl hflwit]
    rw [cnotAux_xConj_fl z fl hflwit]
    rw [cnotAux_xConj_involutive z p]
  · intro p b
    show G0 (cnotAuxFold (cnotAuxXConj z) (Function.update p fl b)) = G0
        (cnotAuxFold (cnotAuxXConj z) p)
    rw [cnotAux_xConj_comm z fl hflwit]
    exact hG0fl _ _
  · intro p hp
    show G0 (cnotAuxFold (cnotAuxXConj z) p) = decide (cnotAuxWitPart p = z)
    have hlad : cnotAuxLadZero (cnotAuxFold (cnotAuxXConj z) p) := cnotAux_xConj_lad z p hp
    rw [hG0clean (cnotAuxFold (cnotAuxXConj z) p) ((cnotAux_ladZero_iff _).mp hlad)]
    exact cnotAux_xConj_allTrue z p

/-- Folding the concatenation of `cnotAuxMarkOne fl z` over a list `zs` equals the left fold
that applies each corresponding register map in list order. -/
theorem cnotAux_fold_flatMap {n : ℕ} (fl : Fin (cnotAuxN n)) (zs : List (Reg n)) :
    cnotAuxFold (zs.flatMap (cnotAuxMarkOne fl)) = fun p =>
      zs.foldl (fun q z => cnotAuxFold (cnotAuxMarkOne fl z) q) p := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    funext p
    simp only [List.flatMap_cons, cnotAux_fold_append, ih, List.foldl_cons]

/-- Under the stated `cnotAuxWiresOK` and length conditions, the fold of `cnotAuxMarkWord fl f`
changes only `fl` by XOR with a Boolean function invariant under updates to `fl`. On
registers satisfying `cnotAuxLadZero`, this function equals `f (cnotAuxWitPart p)`. -/
theorem cnotAux_markWord_shape {n : ℕ} (fl : Fin (cnotAuxN n)) (f : Reg n → Bool)
    (hok : cnotAuxWiresOK fl (cnotAuxWitL n) (cnotAuxLadL n))
    (hlen : (cnotAuxWitL n).length ≤ (cnotAuxLadL n).length + 1) :
    ∃ G : Reg (cnotAuxN n) → Bool,
      (∀ p, cnotAuxFold (cnotAuxMarkWord fl f) p
        = Function.update p fl (p fl ^^ G p))
      ∧ (∀ p b, G (Function.update p fl b) = G p)
      ∧ (∀ p, cnotAuxLadZero p → G p = f (cnotAuxWitPart p)) := by
  have hzsN : ((Finset.univ.filter (fun z : Reg n => f z)).toList).Nodup :=
    Finset.nodup_toList _
  have hzsF : ∀ z ∈ (Finset.univ.filter (fun z : Reg n => f z)).toList, f z = true := by
    intro z hz
    simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact hz

  have hone : ∀ z : Reg n,
      ∃ G : Reg (cnotAuxN n) → Bool,
        (∀ p, cnotAuxFold (cnotAuxMarkOne fl z) p = Function.update p fl (p fl ^^ G p))
        ∧ (∀ p b, G (Function.update p fl b) = G p)
        ∧ (∀ p, cnotAuxLadZero p → G p = decide (cnotAuxWitPart p = z)) :=
    fun z => cnotAux_markOne_shape fl z hok hlen

  suffices hgen : ∀ zs : List (Reg n), zs.Nodup → (∀ z ∈ zs, f z = true) →
      ∃ G : Reg (cnotAuxN n) → Bool,
        (∀ p, cnotAuxFold (zs.flatMap (cnotAuxMarkOne fl)) p = Function.update p fl (p fl ^^ G p))
        ∧ (∀ p b, G (Function.update p fl b) = G p)
        ∧ (∀ p, cnotAuxLadZero p →
            G p = zs.foldr (fun z acc => decide (cnotAuxWitPart p = z) ^^ acc) false) by
    obtain ⟨G, hG, hGfl, hGclean⟩ := hgen _ hzsN hzsF
    refine ⟨G, ?_, hGfl, ?_⟩
    · intro p
      have : cnotAuxMarkWord fl f
          = (Finset.univ.filter (fun z : Reg n => f z)).toList.flatMap (cnotAuxMarkOne fl) := rfl
      rw [this, hG]
    · intro p hp
      rw [hGclean p hp, cnotAux_xor_decide _ hzsN]
      simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
      cases f (cnotAuxWitPart p) <;> rfl
  intro zs
  induction zs with
  | nil =>
    intro _ _
    refine ⟨fun _ => false, ?_, ?_, ?_⟩
    · intro p
      funext k
      by_cases hk : k = fl <;> simp [cnotAuxFold, Function.update, hk, Bool.xor_false]
    · intro p b; rfl
    · intro p _; rfl
  | cons z zs ih =>
    intro hnd hall
    have hnd' : zs.Nodup := (List.nodup_cons.mp hnd).2
    have hall' : ∀ z' ∈ zs, f z' = true := fun z' hz' => hall z' (List.mem_cons_of_mem _ hz')
    obtain ⟨Gz, hGz, hGzfl, hGzclean⟩ := hone z
    obtain ⟨G', hG', hG'fl, hG'clean⟩ := ih hnd' hall'
    refine ⟨fun p => Gz p ^^ G' p, ?_, ?_, ?_⟩
    · intro p
      have hf : cnotAuxFold ((z :: zs).flatMap (cnotAuxMarkOne fl)) p
          = cnotAuxFold (zs.flatMap (cnotAuxMarkOne fl)) (cnotAuxFold (cnotAuxMarkOne fl z) p) := by
        simp only [List.flatMap_cons, cnotAux_fold_append]
      rw [hf, hGz, hG']
      have hself : Function.update p fl (p fl ^^ Gz p) fl = (p fl ^^ Gz p) :=
        Function.update_self fl (p fl ^^ Gz p) p
      have hG'eq : G' (Function.update p fl (p fl ^^ Gz p)) = G' p :=
        hG'fl p (p fl ^^ Gz p)
      rw [hself, hG'eq]
      have hupd : Function.update (Function.update p fl (p fl ^^ Gz p)) fl ((p fl ^^ Gz p) ^^ G' p)
          = Function.update p fl ((p fl ^^ Gz p) ^^ G' p) :=
        cnotAux_update_update p fl (p fl ^^ Gz p) ((p fl ^^ Gz p) ^^ G' p)
      rw [hupd]
      show Function.update p fl ((p fl ^^ Gz p) ^^ G' p)
          = Function.update p fl (p fl ^^ (Gz p ^^ G' p))
      rw [Bool.xor_assoc]
    · intro p b
      simp only [hGzfl p b, hG'fl p b]
    · intro p hp
      have h1 : Gz p = decide (cnotAuxWitPart p = z) := hGzclean p hp
      have h2 : G' p = zs.foldr (fun z acc => decide (cnotAuxWitPart p = z) ^^ acc) false :=
        hG'clean p hp
      show (Gz p ^^ G' p)
          = List.foldr (fun z acc => decide (cnotAuxWitPart p = z) ^^ acc) false (z :: zs)
      rw [h1, h2]
      simp only [List.foldr_cons]

/-- Every macro occurring in `cnotAuxXConj z` satisfies `cnotAuxMacroOk`. -/
theorem cnotAux_xConj_ok {n : ℕ} (z : Reg n) : ∀ m ∈ cnotAuxXConj z, cnotAuxMacroOk m := by
  intro m hm
  simp only [cnotAuxXConj, List.mem_map] at hm
  obtain ⟨i, _, heq⟩ := hm
  rw [← heq]
  trivial

/-- If `cnotAuxWiresOK fl ws as` and `ws.length ≤ as.length + 1`, every macro occurring in
`cnotAuxMarkAll fl ws as` satisfies `cnotAuxMacroOk`. -/
theorem cnotAux_markAll_ok {N : ℕ} (fl : Fin N) :
    ∀ (ws as : List (Fin N)), cnotAuxWiresOK fl ws as → ws.length ≤ as.length + 1 →
      ∀ m ∈ cnotAuxMarkAll fl ws as, cnotAuxMacroOk m := by
  suffices hgen : ∀ (k : ℕ) (ws as : List (Fin N)), ws.length = k →
      cnotAuxWiresOK fl ws as → ws.length ≤ as.length + 1 →
      ∀ m ∈ cnotAuxMarkAll fl ws as, cnotAuxMacroOk m by
    intro ws as hok hlen
    exact hgen ws.length ws as rfl hok hlen
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro ws as hk hok hlen
    cases ws with
    | nil =>
      intro m hm
      simp only [cnotAuxMarkAll, List.mem_singleton] at hm
      rw [hm]
      trivial
    | cons w ws' =>
      cases ws' with
      | nil =>
        intro m hm
        simp only [cnotAuxMarkAll, List.mem_singleton] at hm
        rw [hm]
        exact (cnotAux_wiresOK_cons hok).1
      | cons w2 rest =>
        cases as with
        | nil =>
          exfalso
          simp only [List.length_cons, List.length_nil] at hlen
          omega
        | cons a as' =>
          obtain ⟨hok', htof, hw12, hw1a, hw2a, hafl⟩ := cnotAux_wiresOK_step hok
          have hlen' : (a :: rest).length ≤ as'.length + 1 := by
            simp only [List.length_cons] at hlen ⊢
            omega
          have hk' : (a :: rest).length < k := by
            rw [← hk]
            simp only [List.length_cons]
            omega
          have ih' := ih (a :: rest).length hk' (a :: rest) as' rfl hok' hlen'
          intro m hm
          have key : cnotAuxMarkAll fl (w :: w2 :: rest) (a :: as')
              = (cnotAuxMacro.tofw w w2 a :: cnotAuxMarkAll fl (a :: rest) as')
                  ++ [cnotAuxMacro.tofw w w2 a] := rfl
          rw [key] at hm
          rcases List.mem_append.mp hm with h | h
          · rcases List.mem_cons.mp h with h | h
            · rw [h]; exact htof
            · exact ih' m h
          · have h2 : m = cnotAuxMacro.tofw w w2 a := List.mem_singleton.mp h
            rw [h2]; exact htof

/-- Under the stated `cnotAuxWiresOK` and length conditions for the witness and ladder lists,
every macro occurring in `cnotAuxMarkOne fl z` satisfies `cnotAuxMacroOk`. -/
theorem cnotAux_markOne_ok {n : ℕ} (fl : Fin (cnotAuxN n)) (z : Reg n)
    (hok : cnotAuxWiresOK fl (cnotAuxWitL n) (cnotAuxLadL n))
    (hlen : (cnotAuxWitL n).length ≤ (cnotAuxLadL n).length + 1) :
    ∀ m ∈ cnotAuxMarkOne fl z, cnotAuxMacroOk m := by
  intro m hm
  have key : cnotAuxMarkOne fl z
      = (cnotAuxXConj z ++ cnotAuxMarkAll fl (cnotAuxWitL n) (cnotAuxLadL n)) ++ cnotAuxXConj z := rfl
  rw [key] at hm
  rcases List.mem_append.mp hm with h | h
  · rcases List.mem_append.mp h with h | h
    · exact cnotAux_xConj_ok z m h
    · exact cnotAux_markAll_ok fl _ _ hok hlen m h
  · exact cnotAux_xConj_ok z m h

/-- Under the stated `cnotAuxWiresOK` and length conditions for the witness and ladder lists,
every macro occurring in `cnotAuxMarkWord fl f` satisfies `cnotAuxMacroOk`. -/
theorem cnotAux_markWord_ok {n : ℕ} (fl : Fin (cnotAuxN n)) (f : Reg n → Bool)
    (hok : cnotAuxWiresOK fl (cnotAuxWitL n) (cnotAuxLadL n))
    (hlen : (cnotAuxWitL n).length ≤ (cnotAuxLadL n).length + 1) :
    ∀ m ∈ cnotAuxMarkWord fl f, cnotAuxMacroOk m := by
  intro m hm
  simp only [cnotAuxMarkWord, List.mem_flatMap] at hm
  obtain ⟨z, _, hmz⟩ := hm
  exact cnotAux_markOne_ok fl z hok hlen m hmz

/-- For an involution `σ` on registers, multiplying a state `φ` by `permMatrix σ` gives the
state `fun p => φ (σ p)`. -/
theorem cnotAux_permMatrix_mulVec {N : ℕ} {σ : Reg N → Reg N} (hinv : Function.Involutive σ)
    (φ : QState (Reg N)) :
    (permMatrix σ).mulVec φ = fun p => φ (σ p) := by
  funext p
  simp only [Matrix.mulVec, dotProduct]
  show (∑ j : Reg N, permMatrix σ p j * φ j) = φ (σ p)
  have hkey : ∀ j : Reg N, (p = σ j) ↔ (j = σ p) := by
    intro j
    constructor
    · intro h
      have h2 : σ p = σ (σ j) := congrArg σ h
      rw [hinv j] at h2
      exact h2.symm
    · intro h
      have h2 : σ j = σ (σ p) := congrArg σ h
      rw [hinv p] at h2
      exact h2.symm
  simp only [permMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ p)]
  · have hp : p = σ (σ p) := (hinv p).symm
    rw [if_pos hp, one_mul]
  · intro b _ hb
    have hne : ¬ (p = σ b) := fun h => hb ((hkey b).mp h)
    rw [if_neg hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (σ p)) h

/-- The support condition that `φ p = 0` whenever `p` fails `cnotAuxLadZero`, so nonzero
amplitudes occur only on registers whose ladder auxiliary bits are all zero. -/
def cnotAuxLadSupp {n : ℕ} (φ : QState (Reg (cnotAuxN n))) : Prop :=
  ∀ p : Reg (cnotAuxN n), ¬ cnotAuxLadZero p → φ p = 0

/-- Updating a wire `fl` distinct from every ladder auxiliary wire preserves `cnotAuxLadZero` in
both directions. -/
theorem cnotAux_ladZero_update {n : ℕ} (p : Reg (cnotAuxN n)) (fl : Fin (cnotAuxN n)) (b : Bool)
    (hfl : ∀ j : Fin n, fl ≠ cnotAuxLad n j) :
    cnotAuxLadZero (Function.update p fl b) ↔ cnotAuxLadZero p := by
  constructor <;> intro h j
  · have hj : cnotAuxLad n j ≠ fl := fun e => hfl j e.symm
    have h1 := h j
    rwa [Function.update_of_ne hj b p] at h1
  · have hj : cnotAuxLad n j ≠ fl := fun e => hfl j e.symm
    rw [Function.update_of_ne hj b p]
    exact h j

/-- Under the stated layout, length, and flag separation conditions, the compiled matrix for
`cnotAuxMarkWord fl f` sends a state satisfying `cnotAuxLadSupp` to the state with amplitude
`φ (Function.update p fl (p fl ^^ f (cnotAuxWitPart p)))` at `p`. -/
theorem cnotAux_markWord_mulVec {n : ℕ} (fl : Fin (cnotAuxN n)) (f : Reg n → Bool)
    (hok : cnotAuxWiresOK fl (cnotAuxWitL n) (cnotAuxLadL n))
    (hlen : (cnotAuxWitL n).length ≤ (cnotAuxLadL n).length + 1)
    (hfl : ∀ j : Fin n, fl ≠ cnotAuxLad n j)
    (φ : QState (Reg (cnotAuxN n))) (hφ : cnotAuxLadSupp φ) :
    (finiteWordMatrix (cnotAuxN n) (cnotAuxCompile (cnotAuxMarkWord fl f))).mulVec φ
      = fun p => φ (Function.update p fl (p fl ^^ f (cnotAuxWitPart p))) := by
  obtain ⟨G, hG, hGfl, hGclean⟩ := cnotAux_markWord_shape fl f hok hlen
  have hinv : Function.Involutive (cnotAuxFold (cnotAuxMarkWord fl f)) :=
    cnotAux_flipShape_involutive ⟨G, hG, hGfl⟩
  rw [cnotAux_fwm_compile (cnotAuxMarkWord fl f) (cnotAux_markWord_ok fl f hok hlen),
    cnotAux_permMatrix_mulVec hinv φ]
  funext p
  rw [hG p]
  by_cases hp : cnotAuxLadZero p
  · rw [hGclean p hp]
  · have hn1 : ¬ cnotAuxLadZero (Function.update p fl (p fl ^^ G p)) := by
      rw [cnotAux_ladZero_update p fl (p fl ^^ G p) hfl]
      exact hp
    have hn2 : ¬ cnotAuxLadZero (Function.update p fl (p fl ^^ f (cnotAuxWitPart p))) := by
      rw [cnotAux_ladZero_update p fl (p fl ^^ f (cnotAuxWitPart p)) hfl]
      exact hp
    rw [hφ _ hn1, hφ _ hn2]

/-- For pairwise distinct wires `a`, `b`, and `t`, the compiled Toffoli matrix sends `φ` to the
state with amplitude `φ (Function.update p t (p t ^^ (p a && p b)))` at `p`. -/
theorem cnotAux_tof_mulVec {N : ℕ} (a b t : Fin N) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (φ : QState (Reg N)) :
    (finiteWordMatrix N (cnotAuxTofCode a.val b.val t.val)).mulVec φ
      = fun p => φ (Function.update p t (p t ^^ (p a && p b))) := by
  rw [cnotAux_fwm_tofCode N a b t hab hat hbt]
  exact cnotAux_permMatrix_mulVec (cnotAux_tofPerm_involutive a b t hab hat hbt) φ

/-- The finite gate program applying a Hadamard gate to each witness wire `cnotAuxWit n i`, in
increasing order of `i : Fin n`. -/
def cnotAuxHProg (n : ℕ) : List FiniteGateCode :=
  (List.finRange n).map (fun i => FiniteGateCode.h (cnotAuxWit n i).val)

/-- The register obtained by replacing the first `n` bits of `p` with the word `x` and retaining
`p` at every index at least `n`. -/
def cnotAuxJoin {n : ℕ} (x : Reg n) (p : Reg (cnotAuxN n)) : Reg (cnotAuxN n) :=
  fun k => if h : k.val < n then x ⟨k.val, h⟩ else p k

/-- The witness subregister of `cnotAuxJoin x p` is exactly `x`. -/
theorem cnotAux_join_witPart {n : ℕ} (x : Reg n) (p : Reg (cnotAuxN n)) :
    cnotAuxWitPart (cnotAuxJoin x p) = x := by
  funext i
  show cnotAuxJoin x p (cnotAuxWit n i) = x i
  simp only [cnotAuxJoin]
  rw [dif_pos (show (cnotAuxWit n i).val < n from i.isLt)]
  rfl

/-- The register `cnotAuxJoin x p` agrees with `p` at every wire whose numeric index is at least
`n`. -/
theorem cnotAux_join_off {n : ℕ} (x : Reg n) (p : Reg (cnotAuxN n)) {k : Fin (cnotAuxN n)}
    (hk : n ≤ k.val) : cnotAuxJoin x p k = p k := by
  simp only [cnotAuxJoin]
  rw [dif_neg (by omega : ¬ k.val < n)]

/-- For functions into a commutative monoid, agreement on every entry of `ws` implies equality
of the products of `ws.map f` and `ws.map g`. -/
theorem cnotAux_prod_map_congr {α β : Type*} [CommMonoid β] {f g : α → β} :
    ∀ (ws : List α), (∀ v ∈ ws, f v = g v) → (ws.map f).prod = (ws.map g).prod := by
  intro ws
  induction ws with
  | nil => intro _; rfl
  | cons v vs ih =>
    intro h
    simp only [List.map_cons, List.prod_cons]
    rw [h v List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- For a list `ws` without duplicates, the matrix entry of the Hadamard program on those wires
is the product of the single-qubit `Hadamard (p w) (q w)` entries if `p` and `q` agree off
`ws`, and zero otherwise. -/
theorem cnotAux_hWord_apply {N : ℕ} (ws : List (Fin N)) :
    ws.Nodup → ∀ (p q : Reg N),
    finiteWordMatrix N (ws.map (fun w => FiniteGateCode.h w.val)) p q
      = ((ws.map (fun w => Hadamard (p w) (q w))).prod : ℂ)
          * (if ∀ k : Fin N, k ∉ ws → p k = q k then (1 : ℂ) else 0) := by
  induction ws with
  | nil =>
    intro _ p q
    simp only [List.map_nil]
    rw [show (finiteWordMatrix N ([] : List FiniteGateCode))
        = (1 : Matrix (Reg N) (Reg N) ℂ) from rfl]
    rw [Matrix.one_apply, List.prod_nil, one_mul]
    by_cases h : p = q
    · rw [if_pos h]
      have h2 : ∀ k : Fin N, k ∉ ([] : List (Fin N)) → p k = q k := fun k _ => by rw [h]
      rw [if_pos h2]
    · rw [if_neg h]
      have h2 : ¬ ∀ k : Fin N, k ∉ ([] : List (Fin N)) → p k = q k := by
        intro hh
        apply h
        funext k
        exact hh k List.not_mem_nil
      rw [if_neg h2]
  | cons w ws' ih =>
    intro hws p q
    have hnd' : ws'.Nodup := (List.nodup_cons.mp hws).2
    have hw : w ∉ ws' := (List.nodup_cons.mp hws).1
    have ih' : ∀ (p q : Reg N),
        finiteWordMatrix N (ws'.map (fun v => FiniteGateCode.h v.val)) p q
          = ((ws'.map (fun v => Hadamard (p v) (q v))).prod : ℂ)
              * (if ∀ k : Fin N, k ∉ ws' → p k = q k then (1 : ℂ) else 0) := ih hnd'
    rw [List.map_cons, finiteWordMatrix, Matrix.mul_apply,
      show finiteCodeMatrix N (FiniteGateCode.h w.val) = wireGate N w Hadamard
        by simp only [finiteCodeMatrix, cnotAux_dif_wire]]
    simp only [wireGate_apply]
    have hA : ∀ (p r : Reg N),
        finiteWordMatrix N (ws'.map (fun v => FiniteGateCode.h v.val)) p r
          = ((ws'.map (fun v => Hadamard (p v) (r v))).prod : ℂ)
              * (if ∀ k : Fin N, k ∉ ws' → p k = r k then (1 : ℂ) else 0) := ih'
    rw [Finset.sum_eq_single (Function.update q w (p w))]
    · have hne : ∀ k : Fin N, k ≠ w → Function.update q w (p w) k = q k := fun k hk =>
        Function.update_of_ne hk (p w) q
      have hB : (if ∀ k : Fin N, k ≠ w → Function.update q w (p w) k = q k
          then Hadamard (Function.update q w (p w) w) (q w) else 0)
          = Hadamard (p w) (q w) := by
        rw [if_pos hne, Function.update_self]
      have hAv : ∀ v ∈ ws', Function.update q w (p w) v = q v := by
        intro v hv
        have hvw : v ≠ w := by
          intro h
          exact hw (by rw [← h]; exact hv)
        exact Function.update_of_ne hvw (p w) q
      have hAprod : (ws'.map (fun v => Hadamard (p v) (Function.update q w (p w) v))).prod
          = (ws'.map (fun v => Hadamard (p v) (q v))).prod :=
        cnotAux_prod_map_congr ws' (fun v hv => by rw [hAv v hv])
      have hAcond : (∀ k : Fin N, k ∉ ws' → p k = Function.update q w (p w) k)
          ↔ (∀ k : Fin N, k ∉ w :: ws' → p k = q k) := by
        constructor
        · intro hh k hk
          have hk1 : k ∉ ws' := fun e => hk (List.mem_cons_of_mem _ e)
          have hk2 : k ≠ w := fun e => hk (by rw [e]; exact List.mem_cons_self)
          have h1 := hh k hk1
          rwa [Function.update_of_ne hk2 (p w) q] at h1
        · intro hh k hk
          by_cases hk' : k = w
          · rw [hk', Function.update_self]
          · have hk2 : k ∉ w :: ws' := by
              intro e
              rcases List.mem_cons.mp e with e | e
              · exact hk' e
              · exact hk e
            have h1 := hh k hk2
            rwa [Function.update_of_ne hk' (p w) q]
      rw [hA p (Function.update q w (p w)), hAprod, hB, List.map_cons, List.prod_cons]
      by_cases hc : ∀ k : Fin N, k ∉ w :: ws' → p k = q k
      · rw [if_pos (hAcond.mpr hc), if_pos hc]
        ring
      · have hcn : ¬ ∀ k : Fin N, k ∉ ws' → p k = Function.update q w (p w) k :=
          fun hh => hc (hAcond.mp hh)
        rw [if_neg hcn, if_neg hc]
        ring
    · intro r _ hr
      by_cases hne : ∀ k : Fin N, k ≠ w → r k = q k
      · have hrw : r w ≠ p w := by
          intro h
          apply hr
          funext k
          by_cases hk : k = w
          · rw [hk, h, Function.update_self]
          · rw [Function.update_of_ne hk (p w) q]
            exact hne k hk
        have hAzero : finiteWordMatrix N (ws'.map (fun v => FiniteGateCode.h v.val)) p r = 0 := by
          rw [hA p r]
          rw [if_neg]
          · exact mul_zero _
          · intro hh
            exact hrw (hh w hw).symm
        rw [hAzero, zero_mul]
      · have hex : ∃ k : Fin N, k ≠ w ∧ r k ≠ q k := by
          by_contra hh
          apply hne
          intro k hk
          by_contra h2
          exact hh ⟨k, hk, h2⟩
        obtain ⟨k, hk, hkq⟩ := hex
        rw [if_neg]
        · exact mul_zero _
        · intro hh
          exact hkq (hh k hk)
    · intro h
      exact absurd (Finset.mem_univ (Function.update q w (p w))) h

/-- The program `cnotAuxHProg n` equals the list obtained by mapping each witness wire in
`cnotAuxWitL n` to its Hadamard gate code. -/
theorem cnotAux_hProg_eq (n : ℕ) :
    cnotAuxHProg n = (cnotAuxWitL n).map (fun w => FiniteGateCode.h w.val) := by
  simp only [cnotAuxHProg, cnotAuxWitL, List.map_map]
  rfl

/-- The matrix entry of `cnotAuxHProg n` at `p` and `q` equals `HadamardN n (cnotAuxWitPart p)
(cnotAuxWitPart q)` when the registers agree outside the witness wires, and zero otherwise. -/
theorem cnotAux_hBlock_apply (n : ℕ) (p q : Reg (cnotAuxN n)) :
    finiteWordMatrix (cnotAuxN n) (cnotAuxHProg n) p q
      = HadamardN n (cnotAuxWitPart p) (cnotAuxWitPart q)
          * (if ∀ k : Fin (cnotAuxN n), k ∉ cnotAuxWitL n → p k = q k then (1 : ℂ) else 0) := by
  have h1 : ((cnotAuxWitL n).map (fun w => Hadamard (p w) (q w))).prod
      = ∏ i : Fin n, Hadamard (p (cnotAuxWit n i)) (q (cnotAuxWit n i)) := by
    simp only [cnotAuxWitL, List.map_map]
    rw [← List.ofFn_eq_map]
    exact Fin.prod_ofFn _
  rw [cnotAux_hProg_eq, cnotAux_hWord_apply _ (cnotAux_witL_nodup n), h1]
  rfl

/-- At the witness wire `cnotAuxWit n i`, the register `cnotAuxJoin x p` has bit value `x i`. -/
theorem cnotAux_join_wit {n : ℕ} (x : Reg n) (p : Reg (cnotAuxN n)) (i : Fin n) :
    cnotAuxJoin x p (cnotAuxWit n i) = x i := by
  simp only [cnotAuxJoin]
  rw [dif_pos (show (cnotAuxWit n i).val < n from i.isLt)]
  rfl

/-- The register `cnotAuxJoin x p` agrees with `p` at any wire distinct from every witness wire
`cnotAuxWit n i`. -/
theorem cnotAux_join_ne_wit {n : ℕ} (x : Reg n) (p : Reg (cnotAuxN n)) {k : Fin (cnotAuxN n)}
    (hk : ∀ i : Fin n, cnotAuxWit n i ≠ k) : cnotAuxJoin x p k = p k := by
  apply cnotAux_join_off
  by_contra hlt
  exact hk ⟨k.val, lt_of_not_ge hlt⟩ rfl

/-- Replacing the witness subregister of `p` with that of `q` yields `q` exactly when `p` and
`q` agree at all wires outside `cnotAuxWitL n`. -/
theorem cnotAux_offWit_iff_join {n : ℕ} (p q : Reg (cnotAuxN n)) :
    (cnotAuxJoin (cnotAuxWitPart q) p = q) ↔ (∀ k : Fin (cnotAuxN n), k ∉ cnotAuxWitL n → p k = q k) := by
  constructor
  · intro hj k hk
    have hne : ∀ i : Fin n, cnotAuxWit n i ≠ k := by
      intro i hi
      exact hk (cnotAux_witL_mem.mpr ⟨i, hi⟩)
    have h1 : cnotAuxJoin (cnotAuxWitPart q) p k = p k :=
        cnotAux_join_ne_wit (cnotAuxWitPart q) p hne
    rw [← h1, hj]
  · intro h
    funext k
    by_cases hk : ∃ i : Fin n, cnotAuxWit n i = k
    · obtain ⟨i, hi⟩ := hk
      rw [← hi]
      rw [cnotAux_join_wit]
      rfl
    · have hne : ∀ i : Fin n, cnotAuxWit n i ≠ k := fun i hi => hk ⟨i, hi⟩
      rw [cnotAux_join_ne_wit (cnotAuxWitPart q) p hne]
      exact h k (fun e => hk (cnotAux_witL_mem.mp e))

/-- At a register `p`, applying the matrix of `cnotAuxHProg n` to `φ` gives the sum over `x' :
Reg n` of `HadamardN n (cnotAuxWitPart p) x' * φ (cnotAuxJoin x' p)`. -/
theorem cnotAux_hBlock_mulVec (n : ℕ) (φ : QState (Reg (cnotAuxN n))) (p : Reg (cnotAuxN n)) :
    (finiteWordMatrix (cnotAuxN n) (cnotAuxHProg n)).mulVec φ p
      = ∑ x' : Reg n, HadamardN n (cnotAuxWitPart p) x' * φ (cnotAuxJoin x' p) := by
  simp only [Matrix.mulVec, dotProduct]
  show (∑ q : Reg (cnotAuxN n),
      finiteWordMatrix (cnotAuxN n) (cnotAuxHProg n) p q * φ q) = _
  simp only [cnotAux_hBlock_apply]
  have hfac : ∀ q : Reg (cnotAuxN n),
      (HadamardN n (cnotAuxWitPart p) (cnotAuxWitPart q)
          * (if ∀ k : Fin (cnotAuxN n), k ∉ cnotAuxWitL n → p k = q k then (1 : ℂ) else 0)) * φ q
        = (if cnotAuxJoin (cnotAuxWitPart q) p = q
          then HadamardN n (cnotAuxWitPart p) (cnotAuxWitPart q) * φ q else 0) := by
    intro q
    by_cases h : cnotAuxJoin (cnotAuxWitPart q) p = q
    · rw [if_pos ((cnotAux_offWit_iff_join p q).mp h), if_pos h]
      ring
    · rw [if_neg (fun hh => h ((cnotAux_offWit_iff_join p q).mpr hh)), if_neg h]
      ring
  rw [show (∑ q : Reg (cnotAuxN n),
        (HadamardN n (cnotAuxWitPart p) (cnotAuxWitPart q)
          * (if ∀ k : Fin (cnotAuxN n), k ∉ cnotAuxWitL n → p k = q k then (1 : ℂ) else 0)) * φ q)
      = (∑ q : Reg (cnotAuxN n), (if cnotAuxJoin (cnotAuxWitPart q) p = q
          then HadamardN n (cnotAuxWitPart p) (cnotAuxWitPart q) * φ q else 0))
        from Finset.sum_congr rfl fun q _ => hfac q]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun x' _ => cnotAuxJoin x' p) ?_ ?_ ?_ ?_
  · intro x' _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [cnotAux_join_witPart]⟩
  · intro a1 _ a2 _ heq
    have h1 := congrArg cnotAuxWitPart heq
    rwa [cnotAux_join_witPart, cnotAux_join_witPart] at h1
  · intro q hq
    refine ⟨cnotAuxWitPart q, Finset.mem_univ _, ?_⟩
    exact (Finset.mem_filter.mp hq).2
  · intro x' _
    rw [cnotAux_join_witPart]

/-- The condition that both flag bits, all ladder auxiliary bits, and the output bit of `p` are
`false`, with no restriction on its witness bits. -/
def cnotAuxClean0 {n : ℕ} (p : Reg (cnotAuxN n)) : Prop :=
  p (cnotAuxFlS n) = false ∧ p (cnotAuxFlU n) = false ∧ cnotAuxLadZero p ∧ p (cnotAuxOut n) = false

/-- The embedding of auxiliary index `j : Fin (n + 2)` into the full register at numeric index
`n + j`. -/
def cnotAuxAnc (n : ℕ) (j : Fin (n + 2)) : Fin (cnotAuxN n) :=
  ⟨n + (j : ℕ), by
    have h := j.isLt
    show n + (j : ℕ) < n + (n + 2) + 1
    omega⟩

/-- Auxiliary index zero is the first flag wire: `cnotAuxAnc n 0 = cnotAuxFlS n`. -/
theorem cnotAux_anc_zero (n : ℕ) : cnotAuxAnc n 0 = cnotAuxFlS n := by
  apply Fin.ext
  show n + 0 = n
  omega

/-- Auxiliary index one is the second flag wire: `cnotAuxAnc n 1 = cnotAuxFlU n`. -/
theorem cnotAux_anc_one (n : ℕ) : cnotAuxAnc n 1 = cnotAuxFlU n := by
  apply Fin.ext
  show n + 1 = n + 1
  rfl

/-- For `i : Fin n`, the auxiliary wire at index `2 + i.val` equals the ladder wire `cnotAuxLad
n i`. -/
theorem cnotAux_anc_lad (n : ℕ) (i : Fin n) :
    cnotAuxAnc n ⟨2 + (i : ℕ), by
      have h := i.isLt
      show 2 + (i : ℕ) < n + 2
      omega⟩ = cnotAuxLad n i := by
  apply Fin.ext
  show n + (2 + (i : ℕ)) = n + 2 + (i : ℕ)
  omega

/-- For a verifier with `n` witness wires and `n + 2` auxiliary wires, `qmaWitnessBits n (n + 2)
p` equals `cnotAuxWitPart p`. -/
theorem cnotAux_witnessBits_eq (n : ℕ) (p : Reg (cnotAuxN n)) :
    qmaWitnessBits n (n + 2) p = cnotAuxWitPart p := by
  funext i
  show qmaWitnessBits n (n + 2) p i = p (cnotAuxWit n i)
  have h1 : qmaWitnessBits n (n + 2) p i
      = p (Fin.castAdd 1 (Fin.castAdd (n + 2) i)) := rfl
  have h2 : (Fin.castAdd 1 (Fin.castAdd (n + 2) i) : Fin (cnotAuxN n)) = cnotAuxWit n i := by
    apply Fin.ext
    rfl
  rw [h1, h2]

/-- For this register layout, `qmaOutputBit n (n + 2) p` equals the bit of `p` at `cnotAuxOut
n`. -/
theorem cnotAux_outputBit_eq (n : ℕ) (p : Reg (cnotAuxN n)) :
    qmaOutputBit n (n + 2) p = p (cnotAuxOut n) := by
  have h1 : qmaOutputBit n (n + 2) p = p (Fin.natAdd (n + (n + 2)) 0) := rfl
  have h2 : (Fin.natAdd (n + (n + 2)) 0 : Fin (cnotAuxN n)) = cnotAuxOut n := by
    apply Fin.ext
    show (n + (n + 2)) + 0 = 2 * n + 2
    omega
  rw [h1, h2]

/-- For this register layout, the auxiliary bit `qmaAncillaBits n (n + 2) p j` equals `p
(cnotAuxAnc n j)`. -/
theorem cnotAux_ancillaBits_eq (n : ℕ) (p : Reg (cnotAuxN n)) (j : Fin (n + 2)) :
    qmaAncillaBits n (n + 2) p j = p (cnotAuxAnc n j) := by
  have h1 : qmaAncillaBits n (n + 2) p j
      = p (Fin.castAdd 1 (Fin.natAdd n j)) := rfl
  have h2 : (Fin.castAdd 1 (Fin.natAdd n j) : Fin (cnotAuxN n)) = cnotAuxAnc n j := by
    apply Fin.ext
    rfl
  rw [h1, h2]

/-- The computational basis state `Ket (ZeroStr m)` has amplitude one at `ZeroStr m` and zero at
every other register. -/
theorem cnotAux_ket_zero {m : ℕ} (a : Reg m) :
    Qatlib.Foundations.PureStateMath.Ket (ZeroStr m) a = if a = ZeroStr m then (1 : ℂ) else 0 := rfl

/-- A register `a : Reg m` equals `ZeroStr m` exactly when `a j = false` for every `j : Fin m`. -/
theorem cnotAux_zeroStr_iff {m : ℕ} (a : Reg m) :
    (a = ZeroStr m) ↔ (∀ j : Fin m, a j = false) := by
  constructor
  · intro h j; rw [h]; rfl
  · intro h; funext j; exact h j

/-- All bits extracted by `qmaAncillaBits n (n + 2) p` are zero exactly when both flag bits of
`p` are `false` and `cnotAuxLadZero p` holds. -/
theorem cnotAux_ancilla_zero_iff (n : ℕ) (p : Reg (cnotAuxN n)) :
    (∀ j : Fin (n + 2), qmaAncillaBits n (n + 2) p j = false)
      ↔ (p (cnotAuxFlS n) = false ∧ p (cnotAuxFlU n) = false ∧ cnotAuxLadZero p) := by
  constructor
  · intro h
    have hs := h 0
    have hu := h 1
    have hl : cnotAuxLadZero p := by
      intro i
      have h2 := h ⟨2 + (i : ℕ), by
        have hi := i.isLt
        show 2 + (i : ℕ) < n + 2
        omega⟩
      rw [cnotAux_ancillaBits_eq, cnotAux_anc_lad] at h2
      exact h2
    refine ⟨?_, ?_, hl⟩
    · rw [cnotAux_ancillaBits_eq, cnotAux_anc_zero] at hs
      exact hs
    · rw [cnotAux_ancillaBits_eq, cnotAux_anc_one] at hu
      exact hu
  · intro h j
    rw [cnotAux_ancillaBits_eq]
    by_cases hj0 : (j : ℕ) = 0
    · have key : cnotAuxAnc n j = cnotAuxFlS n := by
        apply Fin.ext
        show n + (j : ℕ) = n
        rw [hj0]
        omega
      rw [key]
      exact h.1
    · by_cases hj1 : (j : ℕ) = 1
      · have key : cnotAuxAnc n j = cnotAuxFlU n := by
          apply Fin.ext
          show n + (j : ℕ) = n + 1
          rw [hj1]
        rw [key]
        exact h.2.1
      · have hge : 2 ≤ (j : ℕ) := by omega
        have hex : ∃ i : Fin n, (i : ℕ) = (j : ℕ) - 2 := by
          refine ⟨⟨(j : ℕ) - 2, ?_⟩, rfl⟩
          have hj := j.isLt
          omega
        obtain ⟨i, hi⟩ := hex
        have key : cnotAuxAnc n j = cnotAuxLad n i := by
          apply Fin.ext
          show n + (j : ℕ) = n + 2 + (i : ℕ)
          rw [hi]
          omega
        rw [key]
        exact h.2.2 i

/-- The amplitude `qmaInitialState n (n + 2) ψ p` equals `ψ (cnotAuxWitPart p)` if
`cnotAuxClean0 p` holds, and equals zero otherwise. -/
theorem cnotAux_initState_shape (n : ℕ) (ψ : QState (Reg n)) (p : Reg (cnotAuxN n)) :
    qmaInitialState n (n + 2) ψ p
      = ψ (cnotAuxWitPart p) * (if cnotAuxClean0 p then (1 : ℂ) else 0) := by
  have hsplit : qmaRegSplit n (n + 2) p
      = ((qmaWitnessBits n (n + 2) p, qmaAncillaBits n (n + 2) p),
          fun _ : Fin 1 => qmaOutputBit n (n + 2) p) := by
    apply Prod.ext
    · apply Prod.ext
      · funext i
        show qmaWitnessBits n (n + 2) p i = qmaWitnessBits n (n + 2) p i
        rfl
      · funext j
        show qmaAncillaBits n (n + 2) p j = qmaAncillaBits n (n + 2) p j
        rfl
    · funext j
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      rw [hj]
      rfl
  rw [qmaInitialState, hsplit, TensorState, TensorState]
  simp only [Prod.mk.eta]
  have hket1 : (Qatlib.Foundations.PureStateMath.Ket (ZeroStr (n + 2)) (qmaAncillaBits n (n + 2) p) : ℂ)
      = if (∀ j : Fin (n + 2), qmaAncillaBits n (n + 2) p j = false) then 1 else 0 := by
    rw [cnotAux_ket_zero]
    by_cases h : qmaAncillaBits n (n + 2) p = ZeroStr (n + 2)
    · rw [if_pos h]
      have hall : ∀ j : Fin (n + 2), qmaAncillaBits n (n + 2) p j = false :=
        (cnotAux_zeroStr_iff _).mp h
      rw [if_pos hall]
    · rw [if_neg h]
      have hneg : ¬ ∀ j : Fin (n + 2), qmaAncillaBits n (n + 2) p j = false := by
        intro hh
        exact h ((cnotAux_zeroStr_iff _).mpr hh)
      rw [if_neg hneg]
  have hket2 : (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 1) (fun _ : Fin 1 => qmaOutputBit n (n + 2) p) : ℂ)
      = if qmaOutputBit n (n + 2) p = false then 1 else 0 := by
    rw [cnotAux_ket_zero]
    by_cases h : qmaOutputBit n (n + 2) p = false
    · have heq : (fun _ : Fin 1 => qmaOutputBit n (n + 2) p) = ZeroStr 1 := by
        funext j
        show qmaOutputBit n (n + 2) p = false
        exact h
      rw [if_pos heq, if_pos h]
    · have hne : ¬ (fun _ : Fin 1 => qmaOutputBit n (n + 2) p) = ZeroStr 1 := by
        intro heq
        exact h (congrFun heq 0)
      rw [if_neg hne, if_neg h]
  rw [hket1, hket2, cnotAux_witnessBits_eq]
  simp only [cnotAux_ancilla_zero_iff, cnotAux_outputBit_eq]
  show (ψ (cnotAuxWitPart p)
      * (if p (cnotAuxFlS n) = false ∧ p (cnotAuxFlU n) = false ∧ cnotAuxLadZero p then (1 : ℂ) else 0))
        * (if p (cnotAuxOut n) = false then (1 : ℂ) else 0)
      = ψ (cnotAuxWitPart p) * (if cnotAuxClean0 p then (1 : ℂ) else 0)
  have hclean : cnotAuxClean0 p
      ↔ (p (cnotAuxFlS n) = false ∧ p (cnotAuxFlU n) = false ∧ cnotAuxLadZero p) ∧ p (cnotAuxOut n) = false :=
    ⟨fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩, fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩⟩
  by_cases h1 : p (cnotAuxFlS n) = false ∧ p (cnotAuxFlU n) = false ∧ cnotAuxLadZero p
  · by_cases h2 : p (cnotAuxOut n) = false
    · rw [if_pos h1, if_pos h2, if_pos (hclean.mpr ⟨h1, h2⟩)]
      ring
    · rw [if_pos h1, if_neg h2, if_neg (fun hh => h2 (hclean.mp hh).2)]
      ring
  · rw [if_neg h1, if_neg (fun hh => h1 (hclean.mp hh).1)]
    ring

/-- The finite gate program that marks `S` in `cnotAuxFlS`, applies Hadamard gates to the
witness, marks `U` in `cnotAuxFlU`, and applies a Toffoli gate from the two flags to
`cnotAuxOut`. -/
noncomputable def cnotAuxProg (n : ℕ) (S U : Reg n → Bool) : List FiniteGateCode :=
  cnotAuxCompile (cnotAuxMarkWord (cnotAuxFlS n) S) ++ cnotAuxHProg n
    ++ cnotAuxCompile (cnotAuxMarkWord (cnotAuxFlU n) U)
    ++ cnotAuxTofCode (cnotAuxFlS n).val (cnotAuxFlU n).val (cnotAuxOut n).val

/-- The matrix of `cnotAuxProg` is the product of its four stage matrices, with the final
Toffoli matrix on the left and the initial `S` marking matrix on the right. -/
theorem cnotAux_fwm_proclause4 (n : ℕ) (S U : Reg n → Bool) :
    finiteWordMatrix (cnotAuxN n) (cnotAuxProg n S U)
      = (finiteWordMatrix (cnotAuxN n)
            (cnotAuxTofCode (cnotAuxFlS n).val (cnotAuxFlU n).val (cnotAuxOut n).val))
        * ((finiteWordMatrix (cnotAuxN n) (cnotAuxCompile (cnotAuxMarkWord (cnotAuxFlU n) U)))
          * ((finiteWordMatrix (cnotAuxN n) (cnotAuxHProg n))
            * (finiteWordMatrix (cnotAuxN n) (cnotAuxCompile (cnotAuxMarkWord (cnotAuxFlS n) S))))) := by
  simp only [cnotAuxProg]
  rw [cnotAux_fwm_append, cnotAux_fwm_append, cnotAux_fwm_append]

/-- The initial state `qmaInitialState n (n + 2) ψ` has zero amplitude whenever any ladder wire
is true, for every witness vector `ψ`. -/
theorem cnotAux_init_ladSupp (n : ℕ) (ψ : QState (Reg n)) : cnotAuxLadSupp (qmaInitialState n (n + 2) ψ) := by
  intro p hp
  rw [cnotAux_initState_shape]
  by_contra h
  have hne : ¬ cnotAuxClean0 p := by
    intro hc
    exact hp hc.2.2.1
  rw [if_neg hne] at h
  exact h (mul_zero _)

/-- The witness and ladder wire lists have no repetitions, are disjoint, and both avoid the flag
`cnotAuxFlS n`, as required by `cnotAuxWiresOK`. -/
theorem cnotAux_wiresOK_layoutS (n : ℕ) :
    cnotAuxWiresOK (cnotAuxFlS n) (cnotAuxWitL n) (cnotAuxLadL n) := cnotAux_wiresOK_flS n

/-- The witness and ladder wire lists have no repetitions, are disjoint, and both avoid the flag
`cnotAuxFlU n`, as required by `cnotAuxWiresOK`. -/
theorem cnotAux_wiresOK_layoutU (n : ℕ) :
    cnotAuxWiresOK (cnotAuxFlU n) (cnotAuxWitL n) (cnotAuxLadL n) := cnotAux_wiresOK_flU n

/-- The number of wires in `cnotAuxWitL n` is at most one more than the number in `cnotAuxLadL
n`. -/
theorem cnotAux_hlen_layout (n : ℕ) :
    (cnotAuxWitL n).length ≤ (cnotAuxLadL n).length + 1 := by
  rw [cnotAux_witL_len, cnotAux_ladL_len]
  omega

/-- The flag wire `cnotAuxFlS n` differs from every ladder wire `cnotAuxLad n j`. -/
theorem cnotAux_flS_not_lad (n : ℕ) (j : Fin n) : cnotAuxFlS n ≠ cnotAuxLad n j :=
  fun h => cnotAux_lad_ne_flS j h.symm

/-- The flag wire `cnotAuxFlU n` differs from every ladder wire `cnotAuxLad n j`. -/
theorem cnotAux_flU_not_lad (n : ℕ) (j : Fin n) : cnotAuxFlU n ≠ cnotAuxLad n j :=
  fun h => cnotAux_lad_ne_flU j h.symm

/-- On a vector satisfying `cnotAuxLadSupp`, the compiled `S` marking program acts by evaluating
the input amplitude after toggling `cnotAuxFlS n` by `S (cnotAuxWitPart p)`. -/
theorem cnotAux_markS_mulVec (n : ℕ) (S : Reg n → Bool) (φ : QState (Reg (cnotAuxN n)))
    (hφ : cnotAuxLadSupp φ) :
    (finiteWordMatrix (cnotAuxN n) (cnotAuxCompile (cnotAuxMarkWord (cnotAuxFlS n) S))).mulVec φ
      = fun p => φ (Function.update p (cnotAuxFlS n) (p (cnotAuxFlS n) ^^ S (cnotAuxWitPart p))) :=
  cnotAux_markWord_mulVec (cnotAuxFlS n) S (cnotAux_wiresOK_flS n) (cnotAux_hlen_layout n)
    (fun j => cnotAux_flS_not_lad n j) φ hφ

/-- On a vector satisfying `cnotAuxLadSupp`, the compiled `U` marking program acts by evaluating
the input amplitude after toggling `cnotAuxFlU n` by `U (cnotAuxWitPart p)`. -/
theorem cnotAux_markU_mulVec (n : ℕ) (U : Reg n → Bool) (φ : QState (Reg (cnotAuxN n)))
    (hφ : cnotAuxLadSupp φ) :
    (finiteWordMatrix (cnotAuxN n) (cnotAuxCompile (cnotAuxMarkWord (cnotAuxFlU n) U))).mulVec φ
      = fun p => φ (Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p))) :=
  cnotAux_markWord_mulVec (cnotAuxFlU n) U (cnotAux_wiresOK_flU n) (cnotAux_hlen_layout n)
    (fun j => cnotAux_flU_not_lad n j) φ hφ

/-- The compiled Toffoli gate controlled by `cnotAuxFlS n` and `cnotAuxFlU n` acts on any vector
by evaluating its amplitude after toggling `cnotAuxOut n` by the conjunction of the flag
bits. -/
theorem cnotAux_tofLayout_mulVec (n : ℕ) (φ : QState (Reg (cnotAuxN n))) :
    (finiteWordMatrix (cnotAuxN n)
        (cnotAuxTofCode (cnotAuxFlS n).val (cnotAuxFlU n).val (cnotAuxOut n).val)).mulVec φ
      = fun p => φ (Function.update p (cnotAuxOut n)
          (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n)))) :=
  cnotAux_tof_mulVec (cnotAuxFlS n) (cnotAuxFlU n) (cnotAuxOut n)
    (cnotAux_flS_ne_flU) (cnotAux_flS_ne_out) (cnotAux_flU_ne_out) φ

/-- If the Boolean exclusive or `a ^^ b` is false, then `a = b`. -/
theorem cnotAux_xor_eq_false {a b : Bool} (h : (a ^^ b) = false) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Equal Boolean values `a` and `b` have `a ^^ b = false`. -/
theorem cnotAux_xor_of_eq {a b : Bool} (h : a = b) : (a ^^ b) = false := by
  cases a <;> cases b <;> simp_all

/-- The sum of `HadamardN n y x * ψ x` over witness strings `x` satisfying `S x = b`, with all
other summands zero. -/
noncomputable def cnotAuxCSum {n : ℕ} (S : Reg n → Bool) (ψ : QState (Reg n)) (b : Bool) (y : Reg n) : ℂ :=
  ∑ x : Reg n, (if b = S x then HadamardN n y x * ψ x else 0)

/-- The basis register condition that all ladder bits are false, the `S` flag equals `S
(cnotAuxWitPart p)`, and the `U` flag and output bit are false. -/
def cnotAuxSupp1 {n : ℕ} (S : Reg n → Bool) (p : Reg (cnotAuxN n)) : Prop :=
  cnotAuxLadZero p ∧ p (cnotAuxFlS n) = S (cnotAuxWitPart p) ∧ p (cnotAuxFlU n) = false ∧ p (cnotAuxOut n) = false

/-- The basis register condition that all ladder bits, the `U` flag, and the output bit are
false, with no restriction on the witness or `S` flag. -/
def cnotAuxSupp2 {n : ℕ} (p : Reg (cnotAuxN n)) : Prop :=
  cnotAuxLadZero p ∧ p (cnotAuxFlU n) = false ∧ p (cnotAuxOut n) = false

/-- The basis register condition that all ladder bits are false, the `U` flag equals `U
(cnotAuxWitPart p)`, and the output bit is false. -/
def cnotAuxSupp3 {n : ℕ} (U : Reg n → Bool) (p : Reg (cnotAuxN n)) : Prop :=
  cnotAuxLadZero p ∧ p (cnotAuxFlU n) = U (cnotAuxWitPart p) ∧ p (cnotAuxOut n) = false

/-- The basis register condition that all ladder bits are false, the `U` flag equals `U
(cnotAuxWitPart p)`, and the output bit equals the conjunction of the `S` and `U` flags. -/
def cnotAuxSupp4 {n : ℕ} (U : Reg n → Bool) (p : Reg (cnotAuxN n)) : Prop :=
  cnotAuxLadZero p ∧ p (cnotAuxFlU n) = U (cnotAuxWitPart p) ∧ p (cnotAuxOut n) = (p (cnotAuxFlS n) && p (cnotAuxFlU n))

/-- Updating `cnotAuxFlS n` to any Boolean value leaves `cnotAuxWitPart p` unchanged. -/
theorem cnotAux_witPart_update_flS (n : ℕ) (p : Reg (cnotAuxN n)) (b : Bool) :
    cnotAuxWitPart (Function.update p (cnotAuxFlS n) b) = cnotAuxWitPart p := by
  funext i
  exact Function.update_of_ne (cnotAux_wit_ne_flS i) b p

/-- Updating `cnotAuxFlU n` to any Boolean value leaves `cnotAuxWitPart p` unchanged. -/
theorem cnotAux_witPart_update_flU (n : ℕ) (p : Reg (cnotAuxN n)) (b : Bool) :
    cnotAuxWitPart (Function.update p (cnotAuxFlU n) b) = cnotAuxWitPart p := by
  funext i
  exact Function.update_of_ne (cnotAux_wit_ne_flU i) b p

/-- Updating `cnotAuxOut n` to any Boolean value leaves `cnotAuxWitPart p` unchanged. -/
theorem cnotAux_witPart_update_out (n : ℕ) (p : Reg (cnotAuxN n)) (b : Bool) :
    cnotAuxWitPart (Function.update p (cnotAuxOut n) b) = cnotAuxWitPart p := by
  funext i
  exact Function.update_of_ne (cnotAux_wit_ne_out i) b p

/-- Updating the flag `cnotAuxFlS n` preserves, in both directions, the condition
`cnotAuxLadZero` that all ladder bits are false. -/
theorem cnotAux_ladZero_update_flS (n : ℕ) (p : Reg (cnotAuxN n)) (b : Bool) :
    cnotAuxLadZero (Function.update p (cnotAuxFlS n) b) ↔ cnotAuxLadZero p :=
  cnotAux_ladZero_update p (cnotAuxFlS n) b (fun j => cnotAux_flS_not_lad n j)

/-- Updating the flag `cnotAuxFlU n` preserves, in both directions, the condition
`cnotAuxLadZero` that all ladder bits are false. -/
theorem cnotAux_ladZero_update_flU (n : ℕ) (p : Reg (cnotAuxN n)) (b : Bool) :
    cnotAuxLadZero (Function.update p (cnotAuxFlU n) b) ↔ cnotAuxLadZero p :=
  cnotAux_ladZero_update p (cnotAuxFlU n) b (fun j => cnotAux_flU_not_lad n j)

/-- Updating the output wire `cnotAuxOut n` preserves, in both directions, the condition
`cnotAuxLadZero` that all ladder bits are false. -/
theorem cnotAux_ladZero_update_out (n : ℕ) (p : Reg (cnotAuxN n)) (b : Bool) :
    cnotAuxLadZero (Function.update p (cnotAuxOut n) b) ↔ cnotAuxLadZero p :=
  cnotAux_ladZero_update p (cnotAuxOut n) b (fun j => (cnotAux_lad_ne_out j).symm)

/-- Toggling the `S` flag by `S (cnotAuxWitPart p)` produces a register satisfying
`cnotAuxClean0` exactly when the original register satisfies `cnotAuxSupp1 S`. -/
theorem cnotAux_clean0_flS (n : ℕ) (S : Reg n → Bool) (p : Reg (cnotAuxN n)) :
    cnotAuxClean0 (Function.update p (cnotAuxFlS n) (p (cnotAuxFlS n) ^^ S (cnotAuxWitPart p)))
      ↔ cnotAuxSupp1 S p := by
  have hU : Function.update p (cnotAuxFlS n) (p (cnotAuxFlS n) ^^ S (cnotAuxWitPart p)) (cnotAuxFlU n)
      = p (cnotAuxFlU n) :=
    Function.update_of_ne (Ne.symm cnotAux_flS_ne_flU) _ _
  have hO : Function.update p (cnotAuxFlS n) (p (cnotAuxFlS n) ^^ S (cnotAuxWitPart p)) (cnotAuxOut n)
      = p (cnotAuxOut n) :=
    Function.update_of_ne (Ne.symm cnotAux_flS_ne_out) _ _
  have hS : Function.update p (cnotAuxFlS n) (p (cnotAuxFlS n) ^^ S (cnotAuxWitPart p)) (cnotAuxFlS n)
      = (p (cnotAuxFlS n) ^^ S (cnotAuxWitPart p)) := Function.update_self _ _ _
  constructor <;> intro h
  · have h1 : (p (cnotAuxFlS n) ^^ S (cnotAuxWitPart p)) = false := by rw [← hS]; exact h.1
    have h2 : p (cnotAuxFlS n) = S (cnotAuxWitPart p) := cnotAux_xor_eq_false h1
    show cnotAuxLadZero p ∧ p (cnotAuxFlS n) = S (cnotAuxWitPart p)
        ∧ p (cnotAuxFlU n) = false ∧ p (cnotAuxOut n) = false
    refine ⟨(cnotAux_ladZero_update_flS n p _).mp h.2.2.1, h2, ?_, ?_⟩
    · rw [← hU]; exact h.2.1
    · rw [← hO]; exact h.2.2.2
  · have h2 : (p (cnotAuxFlS n) ^^ S (cnotAuxWitPart p)) = false := cnotAux_xor_of_eq h.2.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hS]; exact h2
    · rw [hU]; exact h.2.2.1
    · exact (cnotAux_ladZero_update_flS n p _).mpr h.1
    · rw [hO]; exact h.2.2.2

/-- Replacing the witness part of `p` by `x` gives `cnotAuxSupp1 S` exactly when `p` satisfies
`cnotAuxSupp2` and its `S` flag equals `S x`. -/
theorem cnotAux_supp1_join {n : ℕ} (S : Reg n → Bool) (x : Reg n) (p : Reg (cnotAuxN n)) :
    cnotAuxSupp1 S (cnotAuxJoin x p) ↔ (cnotAuxSupp2 p ∧ p (cnotAuxFlS n) = S x) := by
  have hflS : cnotAuxJoin x p (cnotAuxFlS n) = p (cnotAuxFlS n) :=
    cnotAux_join_ne_wit x p (fun i => cnotAux_wit_ne_flS i)
  have hflU : cnotAuxJoin x p (cnotAuxFlU n) = p (cnotAuxFlU n) :=
    cnotAux_join_ne_wit x p (fun i => cnotAux_wit_ne_flU i)
  have hout : cnotAuxJoin x p (cnotAuxOut n) = p (cnotAuxOut n) :=
    cnotAux_join_ne_wit x p (fun i => cnotAux_wit_ne_out i)
  have hlad : cnotAuxLadZero (cnotAuxJoin x p) ↔ cnotAuxLadZero p := by
    constructor <;> intro hh j
    · have h1 := hh j
      rw [cnotAux_join_ne_wit x p (fun i => cnotAux_wit_ne_lad i j)] at h1
      exact h1
    · rw [cnotAux_join_ne_wit x p (fun i => cnotAux_wit_ne_lad i j)]
      exact hh j
  constructor <;> intro h
  · show (cnotAuxLadZero p ∧ p (cnotAuxFlU n) = false ∧ p (cnotAuxOut n) = false) ∧ p (cnotAuxFlS n) = S x
    refine ⟨⟨hlad.mp h.1, ?_, ?_⟩, ?_⟩
    · rw [← hflU]; exact h.2.2.1
    · rw [← hout]; exact h.2.2.2
    · have h2 := h.2.1
      rw [hflS, cnotAux_join_witPart] at h2
      exact h2
  · show cnotAuxLadZero (cnotAuxJoin x p) ∧ cnotAuxJoin x p (cnotAuxFlS n) = S (cnotAuxWitPart (cnotAuxJoin x p))
        ∧ cnotAuxJoin x p (cnotAuxFlU n) = false ∧ cnotAuxJoin x p (cnotAuxOut n) = false
    refine ⟨hlad.mpr h.1.1, ?_, ?_, ?_⟩
    · rw [hflS, cnotAux_join_witPart]
      exact h.2
    · rw [hflU]; exact h.1.2.1
    · rw [hout]; exact h.1.2.2

/-- Toggling the `U` flag by `U (cnotAuxWitPart p)` produces a register satisfying
`cnotAuxSupp2` exactly when the original register satisfies `cnotAuxSupp3 U`. -/
theorem cnotAux_supp2_update_flU {n : ℕ} (U : Reg n → Bool) (p : Reg (cnotAuxN n)) :
    cnotAuxSupp2 (Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)))
      ↔ cnotAuxSupp3 U p := by
  have hO : Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)) (cnotAuxOut n)
      = p (cnotAuxOut n) := Function.update_of_ne (Ne.symm cnotAux_flU_ne_out) _ _
  have hS : Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)) (cnotAuxFlU n)
      = (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)) := Function.update_self _ _ _
  constructor <;> intro h
  · have h1 : (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)) = false := by rw [← hS]; exact h.2.1
    have h2 : p (cnotAuxFlU n) = U (cnotAuxWitPart p) := cnotAux_xor_eq_false h1
    show cnotAuxLadZero p ∧ p (cnotAuxFlU n) = U (cnotAuxWitPart p) ∧ p (cnotAuxOut n) = false
    refine ⟨(cnotAux_ladZero_update_flU n p _).mp h.1, h2, ?_⟩
    rw [← hO]; exact h.2.2
  · show cnotAuxLadZero (Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)))
        ∧ Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)) (cnotAuxFlU n) = false
        ∧ Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)) (cnotAuxOut n) = false
    have h2 : (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)) = false := cnotAux_xor_of_eq h.2.1
    refine ⟨(cnotAux_ladZero_update_flU n p _).mpr h.1, ?_, ?_⟩
    · rw [hS]; exact h2
    · rw [hO]; exact h.2.2

/-- Toggling the output bit by the conjunction of the flag bits produces `cnotAuxSupp3 U`
exactly when the original register satisfies `cnotAuxSupp4 U`. -/
theorem cnotAux_supp3_update_out {n : ℕ} (U : Reg n → Bool) (p : Reg (cnotAuxN n)) :
    cnotAuxSupp3 U (Function.update p (cnotAuxOut n) (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n))))
      ↔ cnotAuxSupp4 U p := by
  have hU : Function.update p (cnotAuxOut n) (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n)))
      (cnotAuxFlU n) = p (cnotAuxFlU n) :=
    Function.update_of_ne cnotAux_flU_ne_out _ _
  have hO : Function.update p (cnotAuxOut n) (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n)))
      (cnotAuxOut n) = (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n))) := Function.update_self _ _ _
  have hwit : cnotAuxWitPart (Function.update p (cnotAuxOut n)
      (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n)))) = cnotAuxWitPart p :=
    cnotAux_witPart_update_out n p _
  constructor <;> intro h
  · have h1 : (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n))) = false := by
      rw [← hO]; exact h.2.2
    have h2 : p (cnotAuxOut n) = (p (cnotAuxFlS n) && p (cnotAuxFlU n)) := cnotAux_xor_eq_false h1
    show cnotAuxLadZero p ∧ p (cnotAuxFlU n) = U (cnotAuxWitPart p)
        ∧ p (cnotAuxOut n) = (p (cnotAuxFlS n) && p (cnotAuxFlU n))
    refine ⟨(cnotAux_ladZero_update_out n p _).mp h.1, ?_, h2⟩
    have h3 := h.2.1
    rw [hwit, hU] at h3
    exact h3
  · show cnotAuxLadZero (Function.update p (cnotAuxOut n)
          (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n))))
        ∧ Function.update p (cnotAuxOut n) (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n)))
            (cnotAuxFlU n) = U (cnotAuxWitPart (Function.update p (cnotAuxOut n)
          (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n)))))
        ∧ Function.update p (cnotAuxOut n) (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n)))
            (cnotAuxOut n) = false
    have h2 : (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n))) = false :=
      cnotAux_xor_of_eq h.2.2
    refine ⟨(cnotAux_ladZero_update_out n p _).mpr h.1, ?_, ?_⟩
    · rw [hU, hwit]; exact h.2.1
    · rw [hO]; exact h2

/-- After the initial `S` marking stage, the amplitude at `p` is `ψ (cnotAuxWitPart p)` when
`cnotAuxSupp1 S p` holds and is zero otherwise. -/
theorem cnotAux_amp1 (n : ℕ) (S : Reg n → Bool) (ψ : QState (Reg n)) (p : Reg (cnotAuxN n)) :
    (finiteWordMatrix (cnotAuxN n) (cnotAuxCompile (cnotAuxMarkWord (cnotAuxFlS n) S))).mulVec
        (qmaInitialState n (n + 2) ψ) p
      = ψ (cnotAuxWitPart p) * (if cnotAuxSupp1 S p then (1 : ℂ) else 0) := by
  rw [cnotAux_markS_mulVec n S (qmaInitialState n (n + 2) ψ) (cnotAux_init_ladSupp n ψ)]
  show qmaInitialState n (n + 2) ψ
        (Function.update p (cnotAuxFlS n) (p (cnotAuxFlS n) ^^ S (cnotAuxWitPart p)))
      = ψ (cnotAuxWitPart p) * (if cnotAuxSupp1 S p then (1 : ℂ) else 0)
  rw [cnotAux_initState_shape]
  have hwit := cnotAux_witPart_update_flS n p (p (cnotAuxFlS n) ^^ S (cnotAuxWitPart p))
  have hif : (if cnotAuxClean0
        (Function.update p (cnotAuxFlS n) (p (cnotAuxFlS n) ^^ S (cnotAuxWitPart p)))
        then (1 : ℂ) else 0)
      = (if cnotAuxSupp1 S p then (1 : ℂ) else 0) := by
    by_cases hc : cnotAuxClean0
        (Function.update p (cnotAuxFlS n) (p (cnotAuxFlS n) ^^ S (cnotAuxWitPart p)))
    · rw [if_pos hc, if_pos ((cnotAux_clean0_flS n S p).mp hc)]
    · rw [if_neg hc, if_neg (fun hh => hc ((cnotAux_clean0_flS n S p).mpr hh))]
  exact congrArg₂ (· * ·) (congrArg ψ hwit) hif

/-- The witness Hadamard stage sends the amplitude formula supported on `cnotAuxSupp1 S` to
`cnotAuxCSum S ψ (p (cnotAuxFlS n)) (cnotAuxWitPart p)` on `cnotAuxSupp2`, and to zero
elsewhere. -/
theorem cnotAux_amp2 (n : ℕ) (S : Reg n → Bool) (ψ : QState (Reg n)) (p : Reg (cnotAuxN n)) :
    (finiteWordMatrix (cnotAuxN n) (cnotAuxHProg n)).mulVec
        (fun q => ψ (cnotAuxWitPart q) * (if cnotAuxSupp1 S q then (1 : ℂ) else 0)) p
      = (if cnotAuxSupp2 p then cnotAuxCSum S ψ (p (cnotAuxFlS n)) (cnotAuxWitPart p) else 0) := by
  rw [cnotAux_hBlock_mulVec n (fun q => ψ (cnotAuxWitPart q) * (if cnotAuxSupp1 S q then (1 : ℂ) else 0)) p]
  show (∑ x' : Reg n, HadamardN n (cnotAuxWitPart p) x'
        * (ψ (cnotAuxWitPart (cnotAuxJoin x' p)) * (if cnotAuxSupp1 S (cnotAuxJoin x' p) then (1 : ℂ) else 0)))
      = (if cnotAuxSupp2 p then cnotAuxCSum S ψ (p (cnotAuxFlS n)) (cnotAuxWitPart p) else 0)
  by_cases h : cnotAuxSupp2 p
  · rw [if_pos h]
    have hrew : ∀ x' : Reg n,
        HadamardN n (cnotAuxWitPart p) x'
          * (ψ (cnotAuxWitPart (cnotAuxJoin x' p)) * (if cnotAuxSupp1 S (cnotAuxJoin x' p) then (1 : ℂ) else 0))
        = (if p (cnotAuxFlS n) = S x' then HadamardN n (cnotAuxWitPart p) x' * ψ x' else 0) := by
      intro x'
      rw [cnotAux_join_witPart]
      have h1 : cnotAuxSupp1 S (cnotAuxJoin x' p) ↔ (cnotAuxSupp2 p ∧ p (cnotAuxFlS n) = S x') :=
        cnotAux_supp1_join S x' p
      by_cases h2 : p (cnotAuxFlS n) = S x'
      · rw [if_pos h2, if_pos (h1.mpr ⟨h, h2⟩), mul_one]
      · rw [if_neg h2, if_neg (fun hh => h2 (h1.mp hh).2)]
        simp
    exact Finset.sum_congr rfl (fun x' _ => hrew x')
  · rw [if_neg h]
    have hrew0 : ∀ x' : Reg n,
        HadamardN n (cnotAuxWitPart p) x'
          * (ψ (cnotAuxWitPart (cnotAuxJoin x' p)) * (if cnotAuxSupp1 S (cnotAuxJoin x' p) then (1 : ℂ) else 0))
        = 0 := by
      intro x'
      rw [cnotAux_join_witPart, if_neg (fun hh => h ((cnotAux_supp1_join S x' p).mp hh).1)]
      simp
    exact Finset.sum_eq_zero (fun x' _ => hrew0 x')

/-- The `U` marking stage sends the `cnotAuxCSum` amplitude formula supported on `cnotAuxSupp2`
to the same formula supported on `cnotAuxSupp3 U`. -/
theorem cnotAux_amp3 (n : ℕ) (S U : Reg n → Bool) (ψ : QState (Reg n)) (p : Reg (cnotAuxN n)) :
    (finiteWordMatrix (cnotAuxN n) (cnotAuxCompile (cnotAuxMarkWord (cnotAuxFlU n) U))).mulVec
        (fun q => if cnotAuxSupp2 q then cnotAuxCSum S ψ (q (cnotAuxFlS n)) (cnotAuxWitPart q) else 0) p
      = (if cnotAuxSupp3 U p then cnotAuxCSum S ψ (p (cnotAuxFlS n)) (cnotAuxWitPart p) else 0) := by
  have hlad : cnotAuxLadSupp
      (fun q => if cnotAuxSupp2 q then cnotAuxCSum S ψ (q (cnotAuxFlS n)) (cnotAuxWitPart q) else 0) := by
    intro q hq
    show (if cnotAuxSupp2 q then cnotAuxCSum S ψ (q (cnotAuxFlS n)) (cnotAuxWitPart q) else 0) = 0
    exact if_neg (fun hh => hq hh.1)
  rw [cnotAux_markU_mulVec n U _ hlad]
  show (if cnotAuxSupp2 (Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)))
      then cnotAuxCSum S ψ
          (Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)) (cnotAuxFlS n))
          (cnotAuxWitPart (Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p))))
      else 0)
    = if cnotAuxSupp3 U p then cnotAuxCSum S ψ (p (cnotAuxFlS n)) (cnotAuxWitPart p) else 0
  have hflS : Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)) (cnotAuxFlS n)
      = p (cnotAuxFlS n) := Function.update_of_ne cnotAux_flS_ne_flU _ _
  have hwit : cnotAuxWitPart (Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)))
      = cnotAuxWitPart p := cnotAux_witPart_update_flU n p _
  by_cases hc : cnotAuxSupp2
      (Function.update p (cnotAuxFlU n) (p (cnotAuxFlU n) ^^ U (cnotAuxWitPart p)))
  · rw [if_pos hc, if_pos ((cnotAux_supp2_update_flU U p).mp hc), hflS, hwit]
  · rw [if_neg hc, if_neg (fun hh => hc ((cnotAux_supp2_update_flU U p).mpr hh))]

/-- The final Toffoli stage sends the `cnotAuxCSum` amplitude formula supported on `cnotAuxSupp3
U` to the same formula supported on `cnotAuxSupp4 U`. -/
theorem cnotAux_amp4 (n : ℕ) (S U : Reg n → Bool) (ψ : QState (Reg n)) (p : Reg (cnotAuxN n)) :
    (finiteWordMatrix (cnotAuxN n)
        (cnotAuxTofCode (cnotAuxFlS n).val (cnotAuxFlU n).val (cnotAuxOut n).val)).mulVec
        (fun q => if cnotAuxSupp3 U q then cnotAuxCSum S ψ (q (cnotAuxFlS n)) (cnotAuxWitPart q) else 0) p
      = (if cnotAuxSupp4 U p then cnotAuxCSum S ψ (p (cnotAuxFlS n)) (cnotAuxWitPart p) else 0) := by
  rw [cnotAux_tofLayout_mulVec n (fun q =>
      if cnotAuxSupp3 U q then cnotAuxCSum S ψ (q (cnotAuxFlS n)) (cnotAuxWitPart q) else 0)]
  show (if cnotAuxSupp3 U (Function.update p (cnotAuxOut n)
          (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n))))
      then cnotAuxCSum S ψ
          (Function.update p (cnotAuxOut n)
            (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n))) (cnotAuxFlS n))
          (cnotAuxWitPart (Function.update p (cnotAuxOut n)
            (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n)))))
      else 0)
    = if cnotAuxSupp4 U p then cnotAuxCSum S ψ (p (cnotAuxFlS n)) (cnotAuxWitPart p) else 0
  have hflS : Function.update p (cnotAuxOut n)
      (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n))) (cnotAuxFlS n) = p (cnotAuxFlS n) :=
    Function.update_of_ne cnotAux_flS_ne_out _ _
  have hwit : cnotAuxWitPart (Function.update p (cnotAuxOut n)
      (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n)))) = cnotAuxWitPart p :=
    cnotAux_witPart_update_out n p _
  by_cases hc : cnotAuxSupp3 U (Function.update p (cnotAuxOut n)
      (p (cnotAuxOut n) ^^ (p (cnotAuxFlS n) && p (cnotAuxFlU n))))
  · rw [if_pos hc, if_pos ((cnotAux_supp3_update_out U p).mp hc), hflS, hwit]
  · rw [if_neg hc, if_neg (fun hh => hc ((cnotAux_supp3_update_out U p).mpr hh))]

/-- Running `cnotAuxProg n S U` on the initial witness state gives amplitude `cnotAuxCSum S ψ (p
(cnotAuxFlS n)) (cnotAuxWitPart p)` at registers satisfying `cnotAuxSupp4 U`, and zero
elsewhere. -/
theorem cnotAux_finalAmplitude (n : ℕ) (S U : Reg n → Bool) (ψ : QState (Reg n)) (p : Reg (cnotAuxN n)) :
    (finiteWordMatrix (cnotAuxN n) (cnotAuxProg n S U)).mulVec (qmaInitialState n (n + 2) ψ) p
      = (if cnotAuxSupp4 U p then cnotAuxCSum S ψ (p (cnotAuxFlS n)) (cnotAuxWitPart p) else 0) := by
  have h1 : (finiteWordMatrix (cnotAuxN n) (cnotAuxCompile (cnotAuxMarkWord (cnotAuxFlS n) S))).mulVec
        (qmaInitialState n (n + 2) ψ)
      = (fun q => ψ (cnotAuxWitPart q) * (if cnotAuxSupp1 S q then (1 : ℂ) else 0)) :=
    funext (fun q => cnotAux_amp1 n S ψ q)
  have h2 : (finiteWordMatrix (cnotAuxN n) (cnotAuxHProg n)).mulVec
        (fun q => ψ (cnotAuxWitPart q) * (if cnotAuxSupp1 S q then (1 : ℂ) else 0))
      = (fun q => if cnotAuxSupp2 q then cnotAuxCSum S ψ (q (cnotAuxFlS n)) (cnotAuxWitPart q) else 0) :=
    funext (fun q => cnotAux_amp2 n S ψ q)
  have h3 : (finiteWordMatrix (cnotAuxN n) (cnotAuxCompile (cnotAuxMarkWord (cnotAuxFlU n) U))).mulVec
        (fun q => if cnotAuxSupp2 q then cnotAuxCSum S ψ (q (cnotAuxFlS n)) (cnotAuxWitPart q) else 0)
      = (fun q => if cnotAuxSupp3 U q then cnotAuxCSum S ψ (q (cnotAuxFlS n)) (cnotAuxWitPart q) else 0) :=
    funext (fun q => cnotAux_amp3 n S U ψ q)
  have h4 : (finiteWordMatrix (cnotAuxN n)
        (cnotAuxTofCode (cnotAuxFlS n).val (cnotAuxFlU n).val (cnotAuxOut n).val)).mulVec
        (fun q => if cnotAuxSupp3 U q then cnotAuxCSum S ψ (q (cnotAuxFlS n)) (cnotAuxWitPart q) else 0)
      = (fun q => if cnotAuxSupp4 U q then cnotAuxCSum S ψ (q (cnotAuxFlS n)) (cnotAuxWitPart q) else 0) :=
    funext (fun q => cnotAux_amp4 n S U ψ q)
  rw [cnotAux_fwm_proclause4 n S U, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, h1, h2, h3, h4]

/-- The register with `S` flag and output bit true, `U` flag equal to `U y`, and every other bit
false. -/
def cnotAuxAccBase {n : ℕ} (U : Reg n → Bool) (y : Reg n) : Reg (cnotAuxN n) :=
  fun k => if k = cnotAuxFlS n then true
    else if k = cnotAuxFlU n then U y
    else if k = cnotAuxOut n then true
    else false

/-- The register obtained by placing witness string `y` into the witness wires of
`cnotAuxAccBase U y` using `cnotAuxJoin`. -/
def cnotAuxCanon {n : ℕ} (U : Reg n → Bool) (y : Reg n) : Reg (cnotAuxN n) :=
  cnotAuxJoin y (cnotAuxAccBase U y)

/-- The value of `cnotAuxAccBase U y` is true on the `S` flag and output wire, is `U y` on the
`U` flag, and is false on every remaining wire. -/
theorem cnotAux_accBase_eq {n : ℕ} (U : Reg n → Bool) (y : Reg n) (k : Fin (cnotAuxN n)) :
    cnotAuxAccBase U y k = if k = cnotAuxFlS n then true
      else if k = cnotAuxFlU n then U y
      else if k = cnotAuxOut n then true else false :=
  rfl

/-- The `S` flag of `cnotAuxAccBase U y` is true. -/
theorem cnotAux_accBase_flS {n : ℕ} (U : Reg n → Bool) (y : Reg n) :
    cnotAuxAccBase U y (cnotAuxFlS n) = true := by
  rw [cnotAux_accBase_eq, if_pos rfl]

/-- The `U` flag of `cnotAuxAccBase U y` equals `U y`. -/
theorem cnotAux_accBase_flU {n : ℕ} (U : Reg n → Bool) (y : Reg n) :
    cnotAuxAccBase U y (cnotAuxFlU n) = U y := by
  rw [cnotAux_accBase_eq, if_neg (Ne.symm cnotAux_flS_ne_flU), if_pos rfl]

/-- The output bit of `cnotAuxAccBase U y` is true. -/
theorem cnotAux_accBase_out {n : ℕ} (U : Reg n → Bool) (y : Reg n) :
    cnotAuxAccBase U y (cnotAuxOut n) = true := by
  rw [cnotAux_accBase_eq, if_neg (Ne.symm cnotAux_flS_ne_out), if_neg (Ne.symm cnotAux_flU_ne_out),
    if_pos rfl]

/-- Every ladder bit of `cnotAuxAccBase U y` is false. -/
theorem cnotAux_accBase_lad {n : ℕ} (U : Reg n → Bool) (y : Reg n) (j : Fin n) :
    cnotAuxAccBase U y (cnotAuxLad n j) = false := by
  rw [cnotAux_accBase_eq, if_neg (cnotAux_lad_ne_flS j), if_neg (cnotAux_lad_ne_flU j),
    if_neg (cnotAux_lad_ne_out j)]

/-- The witness part of `cnotAuxCanon U y` is exactly `y`. -/
theorem cnotAuxCanon_wit {n : ℕ} (U : Reg n → Bool) (y : Reg n) :
    cnotAuxWitPart (cnotAuxCanon U y) = y :=
  cnotAux_join_witPart y (cnotAuxAccBase U y)

/-- The value of `cnotAuxCanon U y` on witness wire `cnotAuxWit n i` is `y i`. -/
theorem cnotAuxCanon_wit_apply {n : ℕ} (U : Reg n → Bool) (y : Reg n) (i : Fin n) :
    cnotAuxCanon U y (cnotAuxWit n i) = y i := by
  show cnotAuxJoin y (cnotAuxAccBase U y) (cnotAuxWit n i) = y i
  exact cnotAux_join_wit y (cnotAuxAccBase U y) i

/-- On any wire outside the witness wires, `cnotAuxCanon U y` agrees with `cnotAuxAccBase U y`. -/
theorem cnotAuxCanon_off {n : ℕ} (U : Reg n → Bool) (y : Reg n) {k : Fin (cnotAuxN n)}
    (hk : ∀ i : Fin n, cnotAuxWit n i ≠ k) :
    cnotAuxCanon U y k = cnotAuxAccBase U y k :=
  cnotAux_join_ne_wit y (cnotAuxAccBase U y) hk

/-- The `S` flag of `cnotAuxCanon U y` is true. -/
theorem cnotAuxCanon_flS {n : ℕ} (U : Reg n → Bool) (y : Reg n) :
    cnotAuxCanon U y (cnotAuxFlS n) = true := by
  rw [cnotAuxCanon_off U y (fun i => cnotAux_wit_ne_flS i), cnotAux_accBase_flS]

/-- The `U` flag of `cnotAuxCanon U y` equals `U y`. -/
theorem cnotAuxCanon_flU {n : ℕ} (U : Reg n → Bool) (y : Reg n) :
    cnotAuxCanon U y (cnotAuxFlU n) = U y := by
  rw [cnotAuxCanon_off U y (fun i => cnotAux_wit_ne_flU i), cnotAux_accBase_flU]

/-- The output bit of `cnotAuxCanon U y` is true. -/
theorem cnotAuxCanon_out {n : ℕ} (U : Reg n → Bool) (y : Reg n) :
    cnotAuxCanon U y (cnotAuxOut n) = true := by
  rw [cnotAuxCanon_off U y (fun i => cnotAux_wit_ne_out i), cnotAux_accBase_out]

/-- Every ladder bit of `cnotAuxCanon U y` is false. -/
theorem cnotAuxCanon_lad {n : ℕ} (U : Reg n → Bool) (y : Reg n) (j : Fin n) :
    cnotAuxCanon U y (cnotAuxLad n j) = false := by
  rw [cnotAuxCanon_off U y (fun i => cnotAux_wit_ne_lad i j), cnotAux_accBase_lad]

/-- Every wire in the `cnotAuxN n` register is a witness wire, the `S` flag, the `U` flag, a
ladder wire, or the output wire. -/
theorem cnotAux_wire_cases {n : ℕ} (k : Fin (cnotAuxN n)) :
    (∃ i : Fin n, cnotAuxWit n i = k) ∨ k = cnotAuxFlS n ∨ k = cnotAuxFlU n
      ∨ (∃ j : Fin n, cnotAuxLad n j = k) ∨ k = cnotAuxOut n := by
  have hk : k.val < n + (n + 2) + 1 := k.isLt
  by_cases h1 : k.val < n
  · left
    exact ⟨⟨k.val, h1⟩, Fin.ext rfl⟩
  · by_cases h2 : k.val = n
    · right; left; exact Fin.ext h2
    · by_cases h3 : k.val = n + 1
      · right; right; left; exact Fin.ext h3
      · by_cases h4 : k.val = 2 * n + 2
        · right; right; right; right; exact Fin.ext h4
        · right; right; right; left
          have h5 : n + 2 ≤ k.val ∧ k.val < 2 * n + 2 := by omega
          refine ⟨⟨k.val - (n + 2), by omega⟩, Fin.ext ?_⟩
          show n + 2 + (k.val - (n + 2)) = k.val
          omega

/-- A register satisfying `cnotAuxSupp4 U` with true output has both flags true and satisfies `U
(cnotAuxWitPart p) = true`. -/
theorem cnotAux_supp4_accept {n : ℕ} (U : Reg n → Bool) (p : Reg (cnotAuxN n))
    (h : p (cnotAuxOut n) = true ∧ cnotAuxSupp4 U p) :
    p (cnotAuxFlS n) = true ∧ p (cnotAuxFlU n) = true ∧ U (cnotAuxWitPart p) = true := by
  have h1 : (p (cnotAuxFlS n) && p (cnotAuxFlU n)) = true := by rw [← h.2.2.2]; exact h.1
  have h2 : p (cnotAuxFlS n) = true ∧ p (cnotAuxFlU n) = true := by
    cases h1s : p (cnotAuxFlS n) <;> cases h1u : p (cnotAuxFlU n) <;> simp_all
  exact ⟨h2.1, h2.2, h.2.2.1.symm.trans h2.2⟩

/-- The canonical register `cnotAuxCanon U y` satisfies `cnotAuxSupp4 U` exactly when `U y =
true`. -/
theorem cnotAuxCanon_supp4 {n : ℕ} (U : Reg n → Bool) (y : Reg n) :
    cnotAuxSupp4 U (cnotAuxCanon U y) ↔ U y = true := by
  show (cnotAuxLadZero (cnotAuxCanon U y)
      ∧ cnotAuxCanon U y (cnotAuxFlU n) = U (cnotAuxWitPart (cnotAuxCanon U y))
      ∧ cnotAuxCanon U y (cnotAuxOut n)
        = (cnotAuxCanon U y (cnotAuxFlS n) && cnotAuxCanon U y (cnotAuxFlU n)))
    ↔ U y = true
  constructor
  · intro h
    rw [cnotAuxCanon_out, cnotAuxCanon_flS, cnotAuxCanon_flU, cnotAuxCanon_wit] at h
    exact (h.2.2.trans (rfl : (true && U y) = U y)).symm
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro j
      rw [cnotAuxCanon_lad]
    · rw [cnotAuxCanon_flU, cnotAuxCanon_wit]
    · rw [cnotAuxCanon_out, cnotAuxCanon_flS, cnotAuxCanon_flU, h]
      rfl

/-- Any register satisfying `cnotAuxSupp4 U` with true output equals `cnotAuxCanon U` applied to
its witness part. -/
theorem cnotAux_canon_of_accept {n : ℕ} (U : Reg n → Bool) (p : Reg (cnotAuxN n))
    (h : p (cnotAuxOut n) = true ∧ cnotAuxSupp4 U p) :
    cnotAuxCanon U (cnotAuxWitPart p) = p := by
  funext k
  rcases cnotAux_wire_cases k with ⟨i, rfl⟩ | rfl | rfl | ⟨j, rfl⟩ | rfl
  · rw [cnotAuxCanon_wit_apply]
    rfl
  · rw [cnotAuxCanon_flS]
    exact (cnotAux_supp4_accept U p h).1.symm
  · rw [cnotAuxCanon_flU]
    exact h.2.2.1.symm
  · rw [cnotAuxCanon_lad]
    exact (h.2.1 j).symm
  · rw [cnotAuxCanon_out]
    exact h.1.symm

/-- Summing `f (cnotAuxWitPart p)` over registers with true output satisfying `cnotAuxSupp4 U`
equals the sum of `f y` over witness strings with `U y = true`. -/
theorem cnotAux_sum_accept {n : ℕ} (U : Reg n → Bool) (f : Reg n → ℝ) :
    ∑ p : Reg (cnotAuxN n),
      (if p (cnotAuxOut n) = true ∧ cnotAuxSupp4 U p then f (cnotAuxWitPart p) else 0)
      = ∑ y : Reg n, (if U y = true then f y else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij (fun p _ => cnotAuxWitPart p) ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (cnotAux_supp4_accept U p (Finset.mem_filter.mp hp).2).2.2⟩
  · intro p1 hp1 p2 hp2 heq
    have heq2 : cnotAuxWitPart p1 = cnotAuxWitPart p2 := heq
    have h1 := cnotAux_canon_of_accept U p1 (Finset.mem_filter.mp hp1).2
    have h2 := cnotAux_canon_of_accept U p2 (Finset.mem_filter.mp hp2).2
    refine h1.symm.trans ((congrArg (cnotAuxCanon U) heq2).trans h2)
  · intro y hy
    refine ⟨cnotAuxCanon U y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact ⟨cnotAuxCanon_out U y, (cnotAuxCanon_supp4 U y).mpr (Finset.mem_filter.mp hy).2⟩
    · exact cnotAuxCanon_wit U y
  · intro p _
    rfl

/-- Multiplication by `charProjector n f` preserves the amplitude at `x` when `f x` is true and
sets it to zero otherwise. -/
theorem cnotAux_char_mulVec (n : ℕ) (f : Reg n → Bool) (φ : QState (Reg n)) :
    (charProjector n f).mulVec φ = fun x => (if f x then (1 : ℂ) else 0) * φ x := by
  funext x
  show (charProjector n f).mulVec φ x = _
  rw [show charProjector n f = Matrix.diagonal (fun x => if f x then (1 : ℂ) else 0) from rfl,
    Matrix.mulVec_diagonal]

/-- The amplitude of `HadamardN n` applied to `v` at `y` is the sum of `HadamardN n y x * v x`
over all witness strings `x`. -/
theorem cnotAux_hadamard_mulVec {n : ℕ} (v : QState (Reg n)) (y : Reg n) :
    (HadamardN n).mulVec v y = ∑ x : Reg n, HadamardN n y x * v x := by
  simp only [Matrix.mulVec, dotProduct]

/-- The amplitude of `(charProjector n U * HadamardN n * charProjector n S).mulVec ψ` at `y`
equals `cnotAuxCSum S ψ true y` if `U y` is true and equals zero otherwise. -/
theorem cnotAux_chain_apply (n : ℕ) (S U : Reg n → Bool) (ψ : QState (Reg n)) (y : Reg n) :
    ((charProjector n U * HadamardN n * charProjector n S).mulVec ψ) y
      = (if U y then (1 : ℂ) else 0) * cnotAuxCSum S ψ true y := by
  have hcomp : ((charProjector n U * HadamardN n) * charProjector n S).mulVec ψ
      = (charProjector n U).mulVec ((HadamardN n).mulVec ((charProjector n S).mulVec ψ)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hcomp]
  rw [cnotAux_char_mulVec n U ((HadamardN n).mulVec ((charProjector n S).mulVec ψ))]
  show (if U y then (1 : ℂ) else 0) * (HadamardN n).mulVec ((charProjector n S).mulVec ψ) y
      = (if U y then (1 : ℂ) else 0) * cnotAuxCSum S ψ true y
  rw [cnotAux_hadamard_mulVec]
  have hS : ∀ x : Reg n, (charProjector n S).mulVec ψ x
      = (if S x then (1 : ℂ) else 0) * ψ x := by
    intro x
    exact congrFun (cnotAux_char_mulVec n S ψ) x
  simp only [hS]
  have hsum : (∑ x : Reg n, HadamardN n y x * ((if S x then (1 : ℂ) else 0) * ψ x))
      = cnotAuxCSum S ψ true y := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : S x = true
    · simp [h]
    · have h2 : ¬(true = S x) := fun hh => h hh.symm
      simp [h, h2]
  rw [hsum]

/-- The acceptance mass after `cnotAuxProg n S U` is the sum of `‖cnotAuxCSum S ψ true y‖ ^ 2`
over witness strings satisfying `U y = true`. -/
theorem cnotAux_accept_sum_form (n : ℕ) (S U : Reg n → Bool) (ψ : QState (Reg n)) :
    MeasureProb
      ((finiteWordMatrix (cnotAuxN n) (cnotAuxProg n S U)).mulVec (qmaInitialState n (n + 2) ψ))
      (qmaAcceptEvent n (n + 2))
      = ∑ y : Reg n, (if U y = true then ‖cnotAuxCSum S ψ true y‖ ^ 2 else 0) := by
  unfold MeasureProb BornProb
  show (∑ i ∈ Finset.univ.filter (fun p => qmaOutputBit n (n + 2) p),
      ‖(finiteWordMatrix (cnotAuxN n) (cnotAuxProg n S U)).mulVec (qmaInitialState n (n + 2) ψ) i‖ ^ 2)
    = ∑ y : Reg n, (if U y = true then ‖cnotAuxCSum S ψ true y‖ ^ 2 else 0)
  rw [Finset.sum_filter]
  simp only [cnotAux_outputBit_eq]
  have hamp := fun q : Reg (cnotAuxN n) => cnotAux_finalAmplitude n S U ψ q
  have hsum : (∑ p : Reg (cnotAuxN n),
        if p (cnotAuxOut n) = true
          then ‖(finiteWordMatrix (cnotAuxN n) (cnotAuxProg n S U)).mulVec
              (qmaInitialState n (n + 2) ψ) p‖ ^ 2 else 0)
      = ∑ p : Reg (cnotAuxN n),
        (if p (cnotAuxOut n) = true ∧ cnotAuxSupp4 U p
          then ‖cnotAuxCSum S ψ true (cnotAuxWitPart p)‖ ^ 2 else 0) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hamp p]
    by_cases ho : p (cnotAuxOut n) = true
    · by_cases hs : cnotAuxSupp4 U p
      · have h4 := cnotAux_supp4_accept U p ⟨ho, hs⟩
        rw [if_pos ho, if_pos hs, if_pos ⟨ho, hs⟩, h4.1]
      · rw [if_pos ho, if_neg hs, if_neg (fun hh => hs hh.2)]
        simp
    · rw [if_neg ho, if_neg (fun hh => ho hh.1)]
  exact hsum.trans (cnotAux_sum_accept U (fun y => ‖cnotAuxCSum S ψ true y‖ ^ 2))

/-- The witness mass `forrWitnessMass n S U ψ` is the sum of `‖cnotAuxCSum S ψ true y‖ ^ 2` over
witness strings satisfying `U y = true`. -/
theorem cnotAux_forr_mass (n : ℕ) (S U : Reg n → Bool) (ψ : QState (Reg n)) :
    forrWitnessMass n S U ψ
      = ∑ y : Reg n, (if U y = true then ‖cnotAuxCSum S ψ true y‖ ^ 2 else 0) := by
  unfold forrWitnessMass
  rw [norm_toEuclidean_fromVec_sq]
  apply Finset.sum_congr rfl
  intro y _
  rw [cnotAux_chain_apply n S U ψ y]
  by_cases h : U y = true
  · simp [h]
  · simp [h]

/-- Executing the finite code circuit for `cnotAuxProg n S U` from `qmaInitialState n (n + 2) ψ`
has acceptance mass exactly `forrWitnessMass n S U ψ`. -/
theorem cnotAux_accept_eq_forr (n : ℕ) (S U : Reg n → Bool) (ψ : QState (Reg n)) :
    MeasureProb
      (Run (1 : Matrix (Reg (cnotAuxN n)) (Reg (cnotAuxN n)) ℂ)
        (finiteCodeCircuit (cnotAuxN n) (cnotAuxProg n S U))
        (qmaInitialState n (n + 2) ψ))
      (qmaAcceptEvent n (n + 2))
      = forrWitnessMass n S U ψ := by
  rw [run_finiteCodeCircuit, cnotAux_accept_sum_form]
  exact (cnotAux_forr_mass n S U ψ).symm

/-- The finite gate word `cnotAuxTofCode a.val b.val t.val` is legal on `N` wires when its two
controls and target are pairwise distinct elements of `Fin N`. -/
theorem cnotAux_tof_legal {N : ℕ} (a b t : Fin N) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    finiteWordLegal N (cnotAuxTofCode a.val b.val t.val) = true := by
  have ha : a.val < N := a.isLt
  have hb : b.val < N := b.isLt
  have ht : t.val < N := t.isLt
  have hab' : a.val ≠ b.val := fun h => hab (Fin.val_injective h)
  have hat' : a.val ≠ t.val := fun h => hat (Fin.val_injective h)
  have hbt' : b.val ≠ t.val := fun h => hbt (Fin.val_injective h)
  simp [finiteWordLegal, cnotAuxTofCode, finiteCodeLegal, ha, hb, ht, hab', hat', hbt']

/-- Every finite gate in `cnotAuxMacroWord m` is legal on `cnotAuxN n` wires when `m` satisfies
`cnotAuxMacroOk`. -/
theorem cnotAux_macroWord_legal {n : ℕ} (m : cnotAuxMacro (cnotAuxN n)) (hm : cnotAuxMacroOk m) :
    (cnotAuxMacroWord m).all (finiteCodeLegal (cnotAuxN n)) = true := by
  cases m with
  | xw w =>
    show (List.all [FiniteGateCode.x w.val] (finiteCodeLegal (cnotAuxN n))) = true
    rw [List.all_eq_true]
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    show decide (w.val < cnotAuxN n) = true
    exact decide_eq_true w.isLt
  | cxw c t =>
    show (List.all [FiniteGateCode.cx c.val t.val] (finiteCodeLegal (cnotAuxN n))) = true
    rw [List.all_eq_true]
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    show decide (c.val < cnotAuxN n ∧ t.val < cnotAuxN n ∧ c.val ≠ t.val) = true
    exact decide_eq_true ⟨c.isLt, t.isLt, fun h => hm (Fin.val_injective h)⟩
  | tofw a b t =>
    exact cnotAux_tof_legal a b t hm.1 hm.2.1 hm.2.2

/-- Compiling a list of macros with `cnotAuxCompile` produces a legal finite gate word when
every macro satisfies `cnotAuxMacroOk`. -/
theorem cnotAux_compile_legal {n : ℕ} (ms : List (cnotAuxMacro (cnotAuxN n)))
    (hok : ∀ m ∈ ms, cnotAuxMacroOk m) :
    finiteWordLegal (cnotAuxN n) (cnotAuxCompile ms) = true := by
  show List.all (cnotAuxCompile ms) (finiteCodeLegal (cnotAuxN n)) = true
  rw [cnotAuxCompile, List.all_eq_true]
  intro g hg
  rw [List.mem_flatMap] at hg
  obtain ⟨m, hm, hgm⟩ := hg
  exact List.all_eq_true.mp (cnotAux_macroWord_legal m (hok m hm)) g hgm

/-- The witness Hadamard program `cnotAuxHProg n` is a legal finite gate word on `cnotAuxN n`
wires. -/
theorem cnotAux_hProg_legal (n : ℕ) : finiteWordLegal (cnotAuxN n) (cnotAuxHProg n) = true := by
  show List.all (cnotAuxHProg n) (finiteCodeLegal (cnotAuxN n)) = true
  rw [cnotAuxHProg, List.all_eq_true]
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨i, _, rfl⟩ := hg
  show decide ((cnotAuxWit n i).val < cnotAuxN n) = true
  exact decide_eq_true (cnotAuxWit n i).isLt

/-- The complete program `cnotAuxProg n S U` is a legal finite gate word on `cnotAuxN n` wires
for all predicates `S` and `U`. -/
theorem cnotAuxProg_legal (n : ℕ) (S U : Reg n → Bool) :
    finiteWordLegal (cnotAuxN n) (cnotAuxProg n S U) = true := by
  show List.all (cnotAuxProg n S U) (finiteCodeLegal (cnotAuxN n)) = true
  rw [cnotAuxProg, List.all_append, List.all_append, List.all_append]
  have hA : List.all (cnotAuxCompile (cnotAuxMarkWord (cnotAuxFlS n) S)) (finiteCodeLegal (cnotAuxN n)) = true :=
    cnotAux_compile_legal (cnotAuxMarkWord (cnotAuxFlS n) S)
      (cnotAux_markWord_ok (cnotAuxFlS n) S (cnotAux_wiresOK_flS n) (cnotAux_hlen_layout n))
  have hB : List.all (cnotAuxHProg n) (finiteCodeLegal (cnotAuxN n)) = true := cnotAux_hProg_legal n
  have hC : List.all (cnotAuxCompile (cnotAuxMarkWord (cnotAuxFlU n) U)) (finiteCodeLegal (cnotAuxN n)) = true :=
    cnotAux_compile_legal (cnotAuxMarkWord (cnotAuxFlU n) U)
      (cnotAux_markWord_ok (cnotAuxFlU n) U (cnotAux_wiresOK_flU n) (cnotAux_hlen_layout n))
  have hD : List.all (cnotAuxTofCode (cnotAuxFlS n).val (cnotAuxFlU n).val (cnotAuxOut n).val)
      (finiteCodeLegal (cnotAuxN n)) = true :=
    cnotAux_tof_legal (cnotAuxFlS n) (cnotAuxFlU n) (cnotAuxOut n) cnotAux_flS_ne_flU cnotAux_flS_ne_out cnotAux_flU_ne_out
  rw [hA, hB, hC, hD]
  decide

/-- The input independent `QmaVerifier` with `n` witness qubits, `n + 2` auxiliary qubits, and
program `cnotAuxProg n S U`, equipped with legality and a constant program length bound. -/
noncomputable def cnotAuxVf (n : ℕ) (S U : Reg n → Bool) : QmaVerifier where
  witnessQubits := fun _ => n
  auxQubits := fun _ => n + 2
  program := fun _ => cnotAuxProg n S U
  legal := by
    intro x
    show finiteWordLegal (cnotAuxN n) (cnotAuxProg n S U) = true
    exact cnotAuxProg_legal n S U
  sizeBound := ⟨(cnotAuxProg n S U).length, 0, fun _ => by simp⟩

/-- For every `n`, `S`, and `U`, there is a verifier using exactly `n` witness qubits and a
uniform constant program length bound whose acceptance mass on every input and witness `ψ`
is `forrWitnessMass n S U ψ`. -/
theorem clause1_clause2 : ∀ (n : ℕ) (S U : Reg n → Bool),
    ∃ (Vf : QmaVerifier) (c : ℕ) (hw : ∀ mₓ : ℕ, Vf.witnessQubits mₓ = n),
      (∀ x : List Bool, (Vf.program x).length ≤ c) ∧
      (∀ (x : List Bool) (ψ : QState (Reg n)),
        qmaAcceptProbW Vf n hw x ψ = forrWitnessMass n S U ψ) := by
  intro n S U
  refine ⟨cnotAuxVf n S U, (cnotAuxProg n S U).length, fun _ => rfl, ?_, ?_⟩
  · intro x
    show (cnotAuxProg n S U).length ≤ (cnotAuxProg n S U).length
    exact le_refl _
  · intro x ψ
    exact cnotAux_accept_eq_forr n S U ψ
end Qatlib.Concepts.QmaCompleteness.HistoryHam
