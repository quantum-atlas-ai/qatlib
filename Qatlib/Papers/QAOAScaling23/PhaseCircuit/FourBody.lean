/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOAScaling23.QuantumPrep.LABSPhase
public import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
public import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitControl

@[expose] public section

/-!
# Four-body LABS phase compilation

Figure S14 of arXiv:2308.02342v2 uses CNOTs from the outer wires into the
inner wires. The middle `Rzz(θ)` has exponent `-iθ (Z ⊗ Z)/2`.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth (applyGate_diagonal_ket)
open Qatlib.Papers.QAOAScaling23.LABSDefs (spin)
open Qatlib.Papers.QAOAScaling23.QuantumPrep (fourBodySpin twoBodySpin)

namespace Qatlib.Papers.QAOAScaling23.PhaseCircuit

/-- The phase for an eigenvalue of a Pauli coupling at rotation angle `θ`. -/
def couplingPhase (θ z : ℝ) : ℂ := Complex.exp ((-(θ / 2) * z : ℝ) * Complex.I)

/-- A two-wire Rzz matrix embedded into an arbitrary computational register. -/
def rzz {n : ℕ} (θ : ℝ) (j k : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x => couplingPhase θ (spin (x j) * spin (x k)))

/-- The four-wire Z rotation to be implemented by Fig. S14. -/
def rzzzz {n : ℕ} (θ : ℝ) (i j k l : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x => couplingPhase θ (spin (x i) * spin (x j) * spin (x k) * spin (x l)))

/-- A diagonal Pauli coupling gives the indicated half-angle matrix exponential. -/
private theorem diagonal_coupling_eq_exp {n : ℕ} (θ : ℝ) (z : Reg n → ℝ) :
    Matrix.diagonal (fun x => couplingPhase θ (z x)) =
      NormedSpace.exp ((-(θ : ℂ) / 2 * Complex.I) • Matrix.diagonal (fun x => (z x : ℂ))) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext x
  simp only [couplingPhase, Pi.exp_def, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  push_cast
  congr 1
  ring

/-- The embedded Rzz has the native half-angle exponent on the two selected wires. -/
theorem rzz_eq_exp {n : ℕ} (θ : ℝ) (j k : Fin n) :
    rzz θ j k = NormedSpace.exp
      ((-(θ : ℂ) / 2 * Complex.I) • Matrix.diagonal (fun x : Reg n =>
        ((spin (x j) * spin (x k) : ℝ) : ℂ))) :=
  diagonal_coupling_eq_exp θ _

/-- The intended four-wire gate is exactly the exponential of the product of the four Z eigenvalues. -/
theorem rzzzz_eq_exp {n : ℕ} (θ : ℝ) (i j k l : Fin n) :
    rzzzz θ i j k l = NormedSpace.exp
      ((-(θ : ℂ) / 2 * Complex.I) • Matrix.diagonal (fun x : Reg n =>
        ((spin (x i) * spin (x j) * spin (x k) * spin (x l) : ℝ) : ℂ))) :=
  diagonal_coupling_eq_exp θ _

/-- The five explicit instructions of Fig. S14, in execution order. -/
def figureS14Circuit {n : ℕ} (θ : ℝ) (i j k l : Fin n) : Circuit (Reg n) :=
  [.gate (cnotGate n i j), .gate (cnotGate n l k), .gate (rzz θ j k),
    .gate (cnotGate n l k), .gate (cnotGate n i j)]

/-- XOR of register bits multiplies the corresponding Z eigenvalues. -/
private theorem spin_xor (a b : Bool) : spin (a ^^ b) = spin a * spin b := by
  cases a <;> cases b <;> norm_num [spin]

/-- Unit-modulus entries make the Rzz instruction unitary. -/
theorem rzz_unitary {n : ℕ} (θ : ℝ) (j k : Fin n) :
    rzz θ j k ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  apply diagonal_mem_unitaryGroup
  intro x
  simp [couplingPhase, Complex.norm_exp, Complex.mul_re]

/-- Each Rzz eigenvalue on a basis vector is the phase of its two spin factors. -/
theorem rzz_ket {n : ℕ} (θ : ℝ) (j k : Fin n) (x : Reg n) :
    ApplyGate (rzz θ j k) (Ket x) = couplingPhase θ (spin (x j) * spin (x k)) • Ket x :=
  applyGate_diagonal_ket _ x

/-- Matrix action is complex linear on a scaled ket. -/
private theorem gate_smul {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ) (a : ℂ) (x : QState (Reg n)) :
    ApplyGate U (a • x) = a • ApplyGate U x := by
  rw [ApplyGate, ApplyGate, Matrix.mulVec_smul]

/-- The four CNOTs compute the two pair parities and then restore the input register. -/
theorem figureS14_ket {n : ℕ} (θ : ℝ) (i j k l : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l)
    (oracle : Matrix (Reg n) (Reg n) ℂ) (x : Reg n) :
    Run oracle (figureS14Circuit θ i j k l) (Ket x) =
      couplingPhase θ (spin (x i) * spin (x j) * spin (x k) * spin (x l)) • Ket x := by
  let f (y : Reg n) := Function.update y j (y j ^^ y i)
  let g (y : Reg n) := Function.update y k (y k ^^ y l)
  have hf : Function.Involutive f := cnotUpdate_involutive n i j hij
  have hg : Function.Involutive g := cnotUpdate_involutive n l k hkl.symm
  have hfk (y : Reg n) : ApplyGate (cnotGate n i j) (Ket y) = Ket (f y) :=
    applyGate_cnotGate_ket n i j hij y
  have hgk (y : Reg n) : ApplyGate (cnotGate n l k) (Ket y) = Ket (g y) :=
    applyGate_cnotGate_ket n l k hkl.symm y
  have hm : spin (g (f x) j) * spin (g (f x) k) =
      spin (x i) * spin (x j) * spin (x k) * spin (x l) := by
    simp only [f, g, Function.update_self, Function.update_of_ne hjk,
      Function.update_of_ne hjk.symm, Function.update_of_ne hjl.symm, spin_xor]
    ring
  simp only [figureS14Circuit, run_gate, run_nil, hfk, hgk, rzz_ket, gate_smul, hg (f x), hf x, hm]

/-- The whole four-wire matrix equals the conjugation by the directed CNOTs in Fig. S14. -/
theorem rzzzz_eq_cnot_conj {n : ℕ} (θ : ℝ) (i j k l : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l) :
    rzzzz θ i j k l =
      (cnotGate n i j * cnotGate n l k) * rzz θ j k * (cnotGate n l k * cnotGate n i j) := by
  apply Matrix.ext
  intro a x
  let G := (cnotGate n i j * cnotGate n l k) * rzz θ j k * (cnotGate n l k * cnotGate n i j)
  change rzzzz θ i j k l a x = G a x
  rw [← applyGate_eq_mulVec_ket (rzzzz θ i j k l) x a, ← applyGate_eq_mulVec_ket G x a]
  have hk := congrFun (figureS14_ket θ i j k l hij hjk hkl hjl 1 x) a
  rw [rzzzz, applyGate_diagonal_ket]
  simpa only [G, figureS14Circuit, run_gate, run_nil, applyGate_mul] using hk.symm

/-- The five-instruction word realizes the four-wire gate on every input state. -/
theorem figureS14_run {n : ℕ} (θ : ℝ) (i j k l : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l)
    (oracle : Matrix (Reg n) (Reg n) ℂ) (ψ : QState (Reg n)) :
    Run oracle (figureS14Circuit θ i j k l) ψ = ApplyGate (rzzzz θ i j k l) ψ := by
  rw [rzzzz_eq_cnot_conj θ i j k l hij hjk hkl hjl]
  simp only [figureS14Circuit, run_gate, run_nil, applyGate_mul]

/-- Exactly four CNOT occurrences and the middle Rzz give a unitary five-gate word with no queries. -/
theorem figureS14_resources {n : ℕ} (θ : ℝ) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l) :
    GateCount (figureS14Circuit θ i j k l) = 5 ∧
      QueryCount (figureS14Circuit θ i j k l) = 0 ∧ IsUnitaryCircuit (figureS14Circuit θ i j k l) := by
  simp [figureS14Circuit, cnotGate_unitary n i j hij, cnotGate_unitary n l k hkl.symm, rzz_unitary]

/-- The coefficient two of a valid four-body term in Eq. (4) requires angle `4γ` in Fig. S14. -/
theorem fourBody_term_phase {n : ℕ} (γ : ℝ) (i t k : Fin n)
    (h : 0 < t.val ∧ t.val < k.val ∧ i.val + k.val + t.val < n)
    (oracle : Matrix (Reg n) (Reg n) ℂ) (x : Reg n) :
    Run oracle (figureS14Circuit (4 * γ) i ⟨i.val + t.val, by omega⟩
      ⟨i.val + k.val, by omega⟩ ⟨i.val + k.val + t.val, h.2.2⟩) (Ket x) =
      Complex.exp ((-γ * (2 * fourBodySpin x i t k) : ℝ) * Complex.I) • Ket x := by
  have hij : i ≠ (⟨i.val + t.val, by omega⟩ : Fin n) := ne_of_lt (by
    change i.val < i.val + t.val
    omega)
  have hjk : (⟨i.val + t.val, by omega⟩ : Fin n) ≠ ⟨i.val + k.val, by omega⟩ := ne_of_lt (by
    change i.val + t.val < i.val + k.val
    omega)
  have hkl : (⟨i.val + k.val, by omega⟩ : Fin n) ≠ ⟨i.val + k.val + t.val, h.2.2⟩ := ne_of_lt (by
    change i.val + k.val < i.val + k.val + t.val
    omega)
  have hjl : (⟨i.val + t.val, by omega⟩ : Fin n) ≠ ⟨i.val + k.val + t.val, h.2.2⟩ := ne_of_lt (by
    change i.val + t.val < i.val + k.val + t.val
    omega)
  have hangle (z : ℝ) : -((4 * γ) / 2) * z = -γ * (2 * z) := by ring
  rw [figureS14_ket _ _ _ _ _ hij hjk hkl hjl, couplingPhase, fourBodySpin, dite_eq_left h, hangle]

/-- The coefficient one of a valid two-body term in Eq. (4) requires angle `2γ`. -/
theorem twoBody_term_phase {n : ℕ} (γ : ℝ) (i k : Fin n)
    (h : 0 < k.val ∧ i.val + 2 * k.val < n) (x : Reg n) :
    ApplyGate (rzz (2 * γ) i ⟨i.val + 2 * k.val, h.2⟩) (Ket x) =
      Complex.exp ((-γ * twoBodySpin x i k : ℝ) * Complex.I) • Ket x := by
  have hangle : -((2 * γ) / 2) = -γ := by ring
  rw [rzz_ket, couplingPhase, twoBodySpin, dite_eq_left h, hangle]

end Qatlib.Papers.QAOAScaling23.PhaseCircuit
