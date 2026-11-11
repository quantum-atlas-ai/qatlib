/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.Clifford
import Qatlib.Concepts.UnbiasedBases.ThreeBasis.AmplitudeAmplification

/-!
# The T gate and a single-qubit magic state

This module defines the phase `tPhase`, the register operations `tGate` and `tGateInv`, and the
state `magicState` obtained by applying T to the plus state. It develops the phase identities
and Pauli conjugation formulas underlying the Clifford and magic-state framework
[BravyiKitaev2005].

## Main statements

* `tGate_tGate`: two T gates on one wire equal the S gate.
* `tGate_conj_X_not_pauli`: conjugating single-qubit X by T is not a scalar multiple of any
  Pauli operator.
* `inner_magicState_self`: the magic state has inner product one with itself.

## References

* [Bravyi and Kitaev, 2005][BravyiKitaev2005]
-/

set_option warningAsError false

section

open scoped ComplexConjugate

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo

variable {n : ℕ}

/-- The complex phase `exp (iπ / 4)` used by the T gate. -/
noncomputable def tPhase : ℂ := Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- The complex phase `exp (-iπ / 4)` used by the inverse T gate. -/
noncomputable def tPhaseInv : ℂ := Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I)

/-- Multiplying `tPhase` by `tPhaseInv` gives one. -/
lemma tPhase_mul_inv : tPhase * tPhaseInv = 1 := by
  rw [tPhase, tPhaseInv, ← Complex.exp_add,
    show ((Real.pi / 4 : ℝ) : ℂ) * Complex.I + ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I = 0
      from by push_cast; ring, Complex.exp_zero]

/-- Multiplying `tPhaseInv` by `tPhase` gives one. -/
lemma tPhaseInv_mul : tPhaseInv * tPhase = 1 := by
  rw [mul_comm]
  exact tPhase_mul_inv

/-- The square of `tPhase` is the imaginary unit. -/
lemma tPhase_sq : tPhase * tPhase = Complex.I := by
  rw [tPhase, ← Complex.exp_add,
    show ((Real.pi / 4 : ℝ) : ℂ) * Complex.I + ((Real.pi / 4 : ℝ) : ℂ) * Complex.I
        = (Real.pi : ℂ) / 2 * Complex.I from by push_cast; ring,
    Complex.exp_pi_div_two_mul_I]

/-- The eighth power of `tPhase` is one. -/
theorem tPhase_pow_eight : tPhase ^ 8 = 1 := by
  rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, pow_two, tPhase_sq, show (4 : ℕ) = 2 * 2 from rfl,
    pow_mul, Complex.I_sq]
  norm_num

/-- The phase `tPhase` is nonzero. -/
lemma tPhase_ne_zero : tPhase ≠ 0 := Complex.exp_ne_zero _

/-- The real number `√2 / 2` equals the reciprocal of `√2`. -/
lemma sqrt_two_div_two : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  field_simp
  linarith [h22]

/-- The phase `tPhase` equals `(1 + i) / √2`. -/
lemma tPhase_eq : tPhase = (Real.sqrt 2 : ℂ)⁻¹ * (1 + Complex.I) := by
  rw [tPhase, exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four,
    sqrt_two_div_two]
  push_cast
  ring

/-- The phase `tPhaseInv` equals `(1 - i) / √2`. -/
lemma tPhaseInv_eq : tPhaseInv = (Real.sqrt 2 : ℂ)⁻¹ * (1 - Complex.I) := by
  rw [tPhaseInv, exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four, sqrt_two_div_two]
  push_cast
  ring

/-- Applies T on wire `j`, multiplying amplitudes whose `j`th bit is one by `tPhase`. -/
noncomputable def tGate (j : Fin n) (ψ : QReg n) : QReg n :=
  (WithLp.equiv 2 ((Fin n → Fin 2) → ℂ)).symm
    (fun z => tPhase ^ ((z j : Fin 2) : ℕ) * ψ z)

/-- Applies the inverse T gate on wire `j`, multiplying amplitudes whose `j`th bit is one by
`tPhaseInv`. -/
noncomputable def tGateInv (j : Fin n) (ψ : QReg n) : QReg n :=
  (WithLp.equiv 2 ((Fin n → Fin 2) → ℂ)).symm
    (fun z => tPhaseInv ^ ((z j : Fin 2) : ℕ) * ψ z)

/-- The amplitude of `tGate j ψ` at `z` is `tPhase` raised to the bit `z j`, times `ψ z`. -/
@[simp] lemma tGate_apply (j : Fin n) (ψ : QReg n) (z : Fin n → Fin 2) :
    tGate j ψ z = tPhase ^ ((z j : Fin 2) : ℕ) * ψ z := rfl

/-- The amplitude of `tGateInv j ψ` at `z` is `tPhaseInv` raised to the bit `z j`, times `ψ z`. -/
@[simp] lemma tGateInv_apply (j : Fin n) (ψ : QReg n) (z : Fin n → Fin 2) :
    tGateInv j ψ z = tPhaseInv ^ ((z j : Fin 2) : ℕ) * ψ z := rfl

/-- Applying the inverse T gate followed by T on the same wire restores the state. -/
lemma tGate_tGateInv (j : Fin n) (ψ : QReg n) : tGate j (tGateInv j ψ) = ψ := by
  ext z
  rw [tGate_apply, tGateInv_apply, ← mul_assoc, ← mul_pow, tPhase_mul_inv, one_pow, one_mul]

/-- Applying T followed by its inverse on the same wire restores the state. -/
lemma tGateInv_tGate (j : Fin n) (ψ : QReg n) : tGateInv j (tGate j ψ) = ψ := by
  ext z
  rw [tGateInv_apply, tGate_apply, ← mul_assoc, ← mul_pow, tPhaseInv_mul, one_pow, one_mul]

/-- Applying T twice on wire `j` equals applying S on that wire. -/
theorem tGate_tGate (j : Fin n) (ψ : QReg n) : tGate j (tGate j ψ) = sGate j ψ := by
  ext z
  rw [tGate_apply, tGate_apply, sGate_apply, ← mul_assoc, ← mul_pow, tPhase_sq]

/-- The binary vector with value one at `j` and zero at every other coordinate. -/
def unitV (j : Fin n) : Fin n → Fin 2 := fun i => if i = j then 1 else 0

/-- The vector `unitV j` has value one at `j`. -/
lemma unitV_apply_self (j : Fin n) : unitV j j = 1 := if_pos rfl

/-- The binary dot product of `unitV j` with `w` extracts the bit `w j`. -/
lemma bdot_unitV (j : Fin n) (w : Fin n → Fin 2) : bdot (unitV j) w = w j := by
  rw [bdot, Finset.sum_eq_single j
    (fun i _ hij => by rw [unitV, if_neg hij, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), unitV, if_pos rfl, one_mul]

/-- Conjugating X on wire `j` by T yields `1 / √2` times the sum of X and `i` times the Pauli
operator with both labels `unitV j`. -/
theorem tGate_conj_X (j : Fin n) (ψ : QReg n) :
    tGate j (pauliOp (unitV j) 0 (tGateInv j ψ))
      = (Real.sqrt 2 : ℂ)⁻¹
          • (pauliOp (unitV j) 0 ψ + Complex.I • pauliOp (unitV j) (unitV j) ψ) := by
  ext z
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_add, Pi.add_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, tGate_apply, pauliOp_apply,
    tGateInv_apply, pauliOp_apply, pauliOp_apply, pauliSign_zero_left, one_mul,
    pauliSign, bdot_unitV, Pi.add_apply z (unitV j) j, unitV_apply_self]
  generalize hu : z j = u
  generalize hX : ψ.ofLp (z + unitV j) = X
  rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) u with h | h <;> subst h
  · rw [show ((0 : Fin 2) + 1) = 1 from rfl, show signChar 1 = (-1 : ℂ) from rfl,
      show (((0 : Fin 2)) : ℕ) = 0 from rfl, show (((1 : Fin 2)) : ℕ) = 1 from rfl,
      pow_zero, pow_one, tPhaseInv_eq]
    ring
  · rw [show ((1 : Fin 2) + 1) = 0 from rfl, signChar_zero,
      show (((1 : Fin 2)) : ℕ) = 1 from rfl, show (((0 : Fin 2)) : ℕ) = 0 from rfl,
      pow_zero, pow_one, tPhase_eq]
    ring

/-- The T gate commutes with complex scalar multiplication. -/
lemma tGate_smul (j : Fin n) (c : ℂ) (ψ : QReg n) :
    tGate j (c • ψ) = c • tGate j ψ := by
  ext z
  rw [tGate_apply, WithLp.ofLp_smul, Pi.smul_apply, WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, tGate_apply]
  ring

/-- A computational basis state is an eigenvector of T with eigenvalue `tPhase` raised to its
bit on the selected wire. -/
lemma tGate_basisState (j : Fin n) (w : Fin n → Fin 2) :
    tGate j (basisState w) = tPhase ^ ((w j : Fin 2) : ℕ) • basisState w := by
  ext z
  rw [tGate_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisState_apply]
  by_cases hz : z = w
  · subst hz
    rfl
  · rw [if_neg hz, mul_zero, mul_zero]

/-- A computational basis state is an eigenvector of inverse T with eigenvalue `tPhaseInv`
raised to its bit on the selected wire. -/
lemma tGateInv_basisState (j : Fin n) (w : Fin n → Fin 2) :
    tGateInv j (basisState w) = tPhaseInv ^ ((w j : Fin 2) : ℕ) • basisState w := by
  ext z
  rw [tGateInv_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisState_apply]
  by_cases hz : z = w
  · subst hz
    rfl
  · rw [if_neg hz, mul_zero, mul_zero]

/-- Conjugating X on wire `j` by T flips the `j`th basis bit and multiplies by the product of
the inverse input phase and the output phase. -/
lemma tconjX_basisState (j : Fin n) (w : Fin n → Fin 2) :
    tGate j (pauliOp (unitV j) 0 (tGateInv j (basisState w)))
      = (tPhaseInv ^ ((w j : Fin 2) : ℕ)
          * tPhase ^ ((w j + 1 : Fin 2) : ℕ)) • basisState (w + unitV j) := by
  rw [tGateInv_basisState, pauliOp_smul, pauliOp_basisState, pauliSign_zero_left, one_smul,
    tGate_smul, tGate_basisState,
    show (w + unitV j) j = w j + 1 from by
      rw [Pi.add_apply, unitV_apply_self], smul_smul]

/-- On one qubit, T-conjugated X cannot equal a fixed complex scalar times a Pauli operator on
every state. -/
theorem tGate_conj_X_not_pauli :
    ¬ ∃ (c : ℂ) (a b : Fin 1 → Fin 2), ∀ ψ : QReg 1,
      tGate 0 (pauliOp (unitV 0) 0 (tGateInv 0 ψ)) = c • pauliOp a b ψ := by
  rintro ⟨c, a, b, h⟩
  have h0 := h (basisState (fun _ => 0))
  have h1 := h (basisState (fun _ => 1))
  rw [tconjX_basisState, pauliOp_basisState] at h0 h1
  have e0 := congrArg (fun v : QReg 1 => v ((fun _ => 0) + unitV 0)) h0
  have e1 := congrArg (fun v : QReg 1 => v ((fun _ => 1) + unitV 0)) h1
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisState_apply, ite_true,
    show ((0 : Fin 2) + 1) = 1 from rfl, show ((1 : Fin 2) + 1) = 0 from rfl,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at e0 e1
  rcases (by decide : ∀ v : Fin 1 → Fin 2, v = (fun _ => 0) ∨ v = (fun _ => 1)) a
    with ha | ha <;> subst ha
  · rw [if_neg (by decide : ¬((fun _ => 0) + unitV 0 : Fin 1 → Fin 2)
        = (fun _ => 0) + (fun _ => 0)), mul_zero, mul_zero] at e0
    exact tPhase_ne_zero e0
  · rw [if_pos (by decide : ((fun _ => 0) + unitV 0 : Fin 1 → Fin 2)
        = (fun _ => 0) + (fun _ => 1)), mul_one] at e0
    rw [if_pos (by decide : ((fun _ => 1) + unitV 0 : Fin 1 → Fin 2)
        = (fun _ => 1) + (fun _ => 1)), mul_one] at e1

    rw [pauliSign, show bdot b (fun _ => 0) = 0 from by
        rw [bdot, Fin.sum_univ_one, mul_zero], signChar_zero, mul_one] at e0
    rw [pauliSign, show bdot b (fun _ => 1) = b 0 from by
        rw [bdot, Fin.sum_univ_one, mul_one]] at e1

    have hcomb : Complex.I = tPhase * tPhase := tPhase_sq.symm
    rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) (b 0) with hb | hb <;> rw [hb] at e1
    · rw [signChar_zero, mul_one] at e1

      have : Complex.I = 1 := by
        rw [hcomb]
        nth_rewrite 2 [e0]
        rw [← e1, tPhase_mul_inv]
      have him := congrArg Complex.im this
      norm_num [Complex.I_im, Complex.one_im] at him
    · rw [show signChar 1 = (-1 : ℂ) from rfl, mul_neg_one] at e1

      have : Complex.I = -1 := by
        rw [hcomb]
        nth_rewrite 2 [e0]
        rw [show c = -tPhaseInv from by rw [e1, neg_neg], mul_neg, tPhase_mul_inv]
      have him := congrArg Complex.im this
      norm_num at him

/-- The single-qubit state obtained by applying H and then T to the zero basis state. -/
noncomputable def magicState : QReg 1 :=
  tGate 0 (hGate 0 (basisState (fun _ => 0)))

/-- The amplitude of `magicState` at `z` is `tPhase` raised to `z 0`, divided by `√2`. -/
lemma magicState_apply (z : Fin 1 → Fin 2) :
    magicState z = (Real.sqrt 2 : ℂ)⁻¹ * tPhase ^ ((z 0 : Fin 2) : ℕ) := by
  rw [magicState, tGate_apply, hGate_apply, Fin.sum_univ_two]
  rw [show (Function.update z 0 0 : Fin 1 → Fin 2) = (fun _ => 0) from by
      funext i
      rw [Subsingleton.elim i 0, Function.update_self],
    show (Function.update z 0 1 : Fin 1 → Fin 2) = (fun _ => 1) from by
      funext i
      rw [Subsingleton.elim i 0, Function.update_self],
    basisState_apply, basisState_apply, if_pos rfl,
    if_neg (by intro hc; exact absurd (congrFun hc 0) (by decide))]
  simp only [mul_zero, mul_one, add_zero, signChar_zero]
  ring

/-- The inner product of `magicState` with itself equals one. -/
lemma inner_magicState_self : inner ℂ magicState magicState = 1 := by
  have hterm : ∀ z : Fin 1 → Fin 2,
      conj (magicState z) * magicState z = (2 : ℂ)⁻¹ := by
    intro z
    rw [magicState_apply, map_mul, map_pow, map_inv₀, Complex.conj_ofReal,
      show conj tPhase = tPhaseInv from by
        rw [tPhase, tPhaseInv, ← Complex.exp_conj]
        congr 1
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
        push_cast
        ring,
      show (Real.sqrt 2 : ℂ)⁻¹ * tPhaseInv ^ ((z 0 : Fin 2) : ℕ)
          * ((Real.sqrt 2 : ℂ)⁻¹ * tPhase ^ ((z 0 : Fin 2) : ℕ))
        = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * (tPhaseInv * tPhase)
            ^ ((z 0 : Fin 2) : ℕ) from by rw [mul_pow]; ring,
      tPhaseInv_mul, one_pow, mul_one, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply']
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
  norm_num

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo
