/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Tactic

@[expose] public section

/-!
# The three-wire Gray base case of Lemma 7.1

This module formalises the three-wire parity-controlled construction underlying
[BarencoEtAl1995], Lemma 7.1. A doubly controlled one-qubit unitary is assembled from the
three nonempty subsets of the two control wires in reflected-Gray order. Each step is a
parity-controlled one-qubit gate: the target receives `V` or `Vᴴ` according to the parity of the
selected control bits, exactly as in the paper's Gray-path construction. The word has three
parity-controlled gates, and its exact matrix is the doubly controlled unitary whenever
`V * V = U`.

The results give full computational-basis semantics on every control fibre. The general
`n`-wire matrix equality and the implementation of the parity controls using singly controlled
gates and XOR transport remain open here.

## Main statements

* `parityGate_mulVec_ket`: action of one parity-controlled gate on a basis ket.
* `grayBase3_exact`: the four control fibres of the three-step word.
* `grayBase3_eq_fullCtrl`: the compiled three-step word equals the doubly controlled gate.

## References

* [Barenco et al., 1995][BarencoEtAl1995], Section 7, Lemma 7.1.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ElemGates95.MultiControl

/-- Parity-controlled gate. -/
noncomputable def parityGate {n : ℕ} (t : Fin n) (S : Finset (Fin n))
    (W : Matrix Bool Bool ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  fun x y =>
    if ∀ k : Fin n, k ≠ t → x k = y k then
      (if Odd ((S.filter (fun k => x k)).card) then W (x t) (y t)
        else (1 : Matrix Bool Bool ℂ) (x t) (y t))
    else 0

/-- A parity-controlled gate sends a basis ket to the identity unless the parity of the selected
control bits is odd, in which case it applies `W` to the target fibre. -/
theorem parityGate_mulVec_ket {n : ℕ} (t : Fin n) (S : Finset (Fin n))
    (hS : t ∉ S) (W : Matrix Bool Bool ℂ) (x : Reg n) :
    parityGate t S W *ᵥ Ket x =
      if Odd ((S.filter (fun k => x k)).card) then
        (∑ b : Bool, W b (x t) • Ket (Function.update x t b))
      else Ket x := by
  classical
  funext y
  simp only [Matrix.mulVec, dotProduct, Ket]
  by_cases hxy : ∀ k : Fin n, k ≠ t → x k = y k
  · have hfilt : S.filter (fun k => y k) = S.filter (fun k => x k) := by
      apply Finset.filter_congr
      intro k hk
      have hkt : k ≠ t := fun h => hS (h ▸ hk)
      rw [hxy k hkt]
    have hPG : parityGate t S W y x =
        (if Odd ((S.filter (fun k => x k)).card) then W (y t) (x t)
          else (1 : Matrix Bool Bool ℂ) (y t) (x t)) := by
      simp only [parityGate, ite_eq_left (fun k hk => (hxy k hk).symm), hfilt]
    rw [Finset.sum_eq_single x]
    · rw [hPG]
      by_cases hodd : Odd ((S.filter (fun k => x k)).card)
      · rw [ite_eq_left hodd, ite_eq_left hodd, Finset.sum_apply]
        have hupd : Function.update x t (y t) = y := by
          funext k
          by_cases hkt : k = t
          · subst hkt; simp
          · simp [hkt, hxy k hkt]
        rw [Finset.sum_eq_single (y t)]
        · rw [hupd]
          simp [ket_self]
        · intro b _ hb
          have hy : y ≠ Function.update x t b := by
            intro hy
            apply hb
            have := congrFun hy t
            simpa using this.symm
          rw [Pi.smul_apply, smul_eq_mul, ket_apply, ite_eq_right hy]
          simp
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [ite_eq_right hodd, ite_eq_right hodd]
        by_cases hyt : y t = x t
        · have hyx : y = x := by
            funext k
            by_cases hkt : k = t
            · subst hkt; exact hyt
            · exact (hxy k hkt).symm
          rw [hyx]
          simp
        · have hyx : y ≠ x := fun h => hyt (by rw [h])
          rw [Matrix.one_apply, ite_eq_right hyt, ket_ne hyx]
          simp
    · intro z _ hz
      rw [ite_eq_right hz]
      simp [parityGate]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hnot : ¬ ∀ k : Fin n, k ≠ t → y k = x k :=
      fun h => hxy (fun k hk => (h k hk).symm)
    have hPG : parityGate t S W y x = 0 := by
      simp only [parityGate, ite_eq_right hnot]
    rw [Finset.sum_eq_single x]
    · rw [hPG]
      by_cases hodd : Odd ((S.filter (fun k => x k)).card)
      · rw [ite_eq_left hodd, Finset.sum_apply]
        simp only [zero_mul]
        apply Eq.symm
        apply Finset.sum_eq_zero
        intro b _
        have hy : y ≠ Function.update x t b := by
          intro hy
          apply hnot
          intro k hk
          rw [hy]
          simp [Function.update, hk]
        rw [Pi.smul_apply, smul_eq_mul, ket_apply, ite_eq_right hy]
        simp
      · rw [ite_eq_right hodd]
        have hyx : y ≠ x := by
          intro h
          apply hnot
          rw [h]
          intro k hk
          rfl
        rw [show Ket x y = 0 from ket_ne hyx]
        simp
    · intro z _ hz
      rw [ite_eq_right hz]
      simp [parityGate]
    · intro h; exact absurd (Finset.mem_univ _) h



/-- A parity-controlled gate acts on a superposition supported on one target fibre by either
leaving the coefficient vector fixed or multiplying it by `W`, according to the parity of the
control bits. -/
theorem parityGate_mulVec_targetSum {n : ℕ} (t : Fin n) (S : Finset (Fin n))
    (hS : t ∉ S) (W : Matrix Bool Bool ℂ) (x : Reg n) (c : Bool → ℂ) :
    parityGate t S W *ᵥ (∑ b : Bool, c b • Ket (Function.update x t b)) =
      if Odd ((S.filter (fun k => x k)).card) then
        (∑ b : Bool, (W *ᵥ c) b • Ket (Function.update x t b))
      else (∑ b : Bool, c b • Ket (Function.update x t b)) := by
  classical
  by_cases hodd : Odd ((S.filter (fun k => x k)).card)
  · rw [ite_eq_left hodd]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
    have hstep : ∀ b : Bool,
        parityGate t S W *ᵥ Ket (Function.update x t b) =
          ∑ b' : Bool, W b' b • Ket (Function.update x t b') := by
      intro b
      have hbodd : Odd ((S.filter (fun k => Function.update x t b k)).card) := by
        have hf : S.filter (fun k => Function.update x t b k) = S.filter (fun k => x k) := by
          apply Finset.filter_congr
          intro k hk
          have hkt : k ≠ t := fun h => hS (h ▸ hk)
          simp [Function.update, hkt]
        rw [hf]; exact hodd
      rw [parityGate_mulVec_ket t S hS W (Function.update x t b), ite_eq_left hbodd]
      simp only [Function.update_self, Function.update_idem]
    simp only [hstep, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b' _
    rw [← Finset.sum_smul]
    congr 1
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · rw [ite_eq_right hodd]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
    apply Finset.sum_congr rfl
    intro b _
    have hbodd : ¬ Odd ((S.filter (fun k => Function.update x t b k)).card) := by
      have hf : S.filter (fun k => Function.update x t b k) = S.filter (fun k => x k) := by
        apply Finset.filter_congr
        intro k hk
        have hkt : k ≠ t := fun h => hS (h ▸ hk)
        simp [Function.update, hkt]
      rw [hf]; exact hodd
    rw [parityGate_mulVec_ket t S hS W (Function.update x t b), ite_eq_right hbodd]



/-- The fully controlled gate applies `U` exactly when every wire other than the target is true. -/
noncomputable def fullCtrlGate {n : ℕ} (t : Fin n) (U : Matrix Bool Bool ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  fun x y =>
    if ∀ k : Fin n, k ≠ t → x k = y k then
      (if ∀ k : Fin n, k ≠ t → x k = true then U (x t) (y t)
        else (1 : Matrix Bool Bool ℂ) (x t) (y t))
    else 0

/-- A fully controlled gate applies `U` to the target fibre exactly when every control wire is
true and acts as the identity otherwise. -/
theorem fullCtrlGate_mulVec_ket {n : ℕ} (t : Fin n) (U : Matrix Bool Bool ℂ) (x : Reg n) :
    fullCtrlGate t U *ᵥ Ket x =
      if ∀ k : Fin n, k ≠ t → x k = true then
        (∑ b : Bool, U b (x t) • Ket (Function.update x t b))
      else Ket x := by
  classical
  funext y
  simp only [Matrix.mulVec, dotProduct, Ket]
  by_cases hxy : ∀ k : Fin n, k ≠ t → x k = y k
  · have hagree : ∀ k : Fin n, k ≠ t → y k = x k := fun k hk => (hxy k hk).symm
    have hPG : fullCtrlGate t U y x =
        (if ∀ k : Fin n, k ≠ t → x k = true then U (y t) (x t)
          else (1 : Matrix Bool Bool ℂ) (y t) (x t)) := by
      by_cases hall : ∀ k : Fin n, k ≠ t → x k = true
      · have hyall : ∀ k : Fin n, k ≠ t → y k = true := by
          intro k hk
          rw [← hxy k hk]
          exact hall k hk
        rw [fullCtrlGate, ite_eq_left hagree, ite_eq_left hyall, ite_eq_left hall]
      · have hynot : ¬ ∀ k : Fin n, k ≠ t → y k = true := by
          intro h
          apply hall
          intro k hk
          have := h k hk
          rwa [← hxy k hk] at this
        rw [fullCtrlGate, ite_eq_left hagree, ite_eq_right hynot, ite_eq_right hall]
    rw [Finset.sum_eq_single x]
    · rw [hPG]
      by_cases hall : ∀ k : Fin n, k ≠ t → x k = true
      · rw [ite_eq_left hall, ite_eq_left hall, Finset.sum_apply]
        have hupd : Function.update x t (y t) = y := by
          funext k
          by_cases hkt : k = t
          · subst hkt; simp
          · simp [hkt, hxy k hkt]
        rw [Finset.sum_eq_single (y t)]
        · rw [hupd]
          simp [ket_self]
        · intro b _ hb
          have hy : y ≠ Function.update x t b := by
            intro hy
            apply hb
            have := congrFun hy t
            simpa using this.symm
          rw [Pi.smul_apply, smul_eq_mul, ket_apply, ite_eq_right hy]
          simp
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [ite_eq_right hall, ite_eq_right hall]
        by_cases hyt : y t = x t
        · have hyx : y = x := by
            funext k
            by_cases hkt : k = t
            · subst hkt; exact hyt
            · exact (hxy k hkt).symm
          rw [hyx]
          simp
        · have hyx : y ≠ x := fun h => hyt (by rw [h])
          rw [Matrix.one_apply, ite_eq_right hyt, ket_ne hyx]
          simp
    · intro z _ hz
      rw [ite_eq_right hz]
      simp [fullCtrlGate]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hnot : ¬ ∀ k : Fin n, k ≠ t → y k = x k :=
      fun h => hxy (fun k hk => (h k hk).symm)
    have hPG : fullCtrlGate t U y x = 0 := by
      simp only [fullCtrlGate, ite_eq_right hnot]
    rw [Finset.sum_eq_single x]
    · rw [hPG]
      by_cases hall : ∀ k : Fin n, k ≠ t → x k = true
      · rw [ite_eq_left hall, Finset.sum_apply]
        simp only [zero_mul]
        apply Eq.symm
        apply Finset.sum_eq_zero
        intro b _
        have hy : y ≠ Function.update x t b := by
          intro hy
          apply hnot
          intro k hk
          rw [hy]
          simp [Function.update, hk]
        rw [Pi.smul_apply, smul_eq_mul, ket_apply, ite_eq_right hy]
        simp
      · rw [ite_eq_right hall]
        have hyx : y ≠ x := by
          intro h
          apply hnot
          rw [h]
          intro k hk
          rfl
        rw [show Ket x y = 0 from ket_ne hyx]
        simp
    · intro z _ hz
      rw [ite_eq_right hz]
      simp [fullCtrlGate]
    · intro h; exact absurd (Finset.mem_univ _) h



/-- Every computational basis ket is the trivial target-fibre superposition with coefficient
matrix the identity. -/
theorem ket_eq_targetSum {n : ℕ} (t : Fin n) (x : Reg n) :
    Ket x = ∑ b : Bool, (1 : Matrix Bool Bool ℂ) b (x t) • Ket (Function.update x t b) := by
  classical
  funext y
  simp only [Finset.sum_apply, Ket, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (y t)]
  · by_cases hyt : y t = x t
    · have hupd : Function.update x t (y t) = x := by
        funext k
        by_cases hkt : k = t
        · subst hkt; simp [hyt]
        · simp [Function.update, hkt]
      rw [hupd, Matrix.one_apply, ite_eq_left hyt]
      by_cases hyx : y = x
      · rw [hyx]; simp
      · have : ¬ y = x := hyx
        simp [this]
    · rw [Matrix.one_apply, ite_eq_right hyt]
      have hyx : ¬ y = x := fun h => hyt (by rw [h])
      simp [hyx]
  · intro b _ hb
    have hy : y ≠ Function.update x t b := by
      intro h
      apply hb
      have := congrFun h t
      simpa using this.symm
    rw [ite_eq_right hy]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h



/-- The matrix of the three-step Gray word for two controls: parity gates on `{0}`, `{0,1}`, and
`{1}`, in execution order. -/
noncomputable def grayBase3Matrix (V : Matrix Bool Bool ℂ) : Matrix (Reg 3) (Reg 3) ℂ :=
  parityGate 2 (({1} : Finset (Fin 3))) V *
    parityGate 2 (({0, 1} : Finset (Fin 3))) Vᴴ *
    parityGate 2 (({0} : Finset (Fin 3))) V

/-- A parity-controlled step: a control subset together with a one-qubit matrix. -/
abbrev ParityStep (n : ℕ) := Finset (Fin n) × Matrix Bool Bool ℂ

/-- Compile a list of parity-controlled steps, with the first listed step acting first. -/
noncomputable def compileSteps {n : ℕ} (t : Fin n) :
    List (ParityStep n) → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | g :: gs => compileSteps t gs * parityGate t g.1 g.2

/-- The three-step reflected-Gray word for `n = 3`: the nonempty Gray subsets `{0}`, `{0,1}`,
and `{1}`, with alternating `V` and `Vᴴ`. -/
noncomputable def grayBase3Word (V : Matrix Bool Bool ℂ) : List (ParityStep 3) :=
  [(({0} : Finset (Fin 3)), V), (({0, 1} : Finset (Fin 3)), Vᴴ),
    (({1} : Finset (Fin 3)), V)]

/-- The compiled three-step word is the product used in `grayBase3Matrix`. -/
theorem grayBase3Word_compile (V : Matrix Bool Bool ℂ) :
    compileSteps (2 : Fin 3) (grayBase3Word V) = grayBase3Matrix V := by
  simp [compileSteps, grayBase3Word, grayBase3Matrix]

/-- The three-step Gray word has exactly three parity-controlled steps. -/
theorem grayBase3Word_length (V : Matrix Bool Bool ℂ) :
    (grayBase3Word V).length = 3 := rfl

/-- Pointwise form of `parityGate_mulVec_targetSum`, with the coefficient vector selected by an
explicit parity test. -/
theorem parityGate_mulVec_targetSum_ite {n : ℕ} (t : Fin n) (S : Finset (Fin n))
    (hS : t ∉ S) (W : Matrix Bool Bool ℂ) (x : Reg n) (c : Bool → ℂ) :
    parityGate t S W *ᵥ (∑ b : Bool, c b • Ket (Function.update x t b)) =
      ∑ b : Bool,
        (if Odd ((S.filter (fun k => x k)).card) then W *ᵥ c else c) b •
          Ket (Function.update x t b) := by
  classical
  by_cases hodd : Odd ((S.filter (fun k => x k)).card)
  · rw [parityGate_mulVec_targetSum t S hS W x c, ite_eq_left hodd]
    simp [hodd]
  · rw [parityGate_mulVec_targetSum t S hS W x c, ite_eq_right hodd]
    simp [hodd]

/-- The first step of the three-wire Gray word, controlled by the parity of wire `0`, expresses
its result as a target-fibre superposition with coefficient matrix `V` or the identity. -/
theorem parityGate_zero_mulVec_ket (V : Matrix Bool Bool ℂ) (x : Reg 3) :
    parityGate 2 (({0} : Finset (Fin 3))) V *ᵥ Ket x =
      ∑ b : Bool,
        (if Odd (({0} : Finset (Fin 3)).filter (fun k => x k)).card then V else 1)
          b (x 2) • Ket (Function.update x 2 b) := by
  classical
  by_cases hodd : Odd (({0} : Finset (Fin 3)).filter (fun k => x k)).card
  · rw [parityGate_mulVec_ket 2 _ (by simp) V x, ite_eq_left hodd]
    simp [hodd]
  · rw [parityGate_mulVec_ket 2 _ (by simp) V x, ite_eq_right hodd]
    rw [ket_eq_targetSum (2 : Fin 3) x]
    simp [hodd]











/-- On the control fibre with both controls false, the three-wire Gray word acts as the
identity. -/
theorem grayBase3_allFalse (V : Matrix Bool Bool ℂ) (x : Reg 3)
    (h0 : x 0 = false) (h1 : x 1 = false) :
    grayBase3Matrix V *ᵥ Ket x = Ket x := by
  have hf0 : (({0} : Finset (Fin 3)).filter (fun k => x k)) = ∅ := by
    ext k; fin_cases k <;> simp [h0]
  have hf01 : (({0, 1} : Finset (Fin 3)).filter (fun k => x k)) = ∅ := by
    ext k; fin_cases k <;> simp [h0, h1]
  have hf1 : (({1} : Finset (Fin 3)).filter (fun k => x k)) = ∅ := by
    ext k; fin_cases k <;> simp [h1]
  have ho0 : ¬ Odd (({0} : Finset (Fin 3)).filter (fun k => x k)).card := by
    rw [hf0]; simp
  have ho01 : ¬ Odd (({0, 1} : Finset (Fin 3)).filter (fun k => x k)).card := by
    rw [hf01]; simp
  have ho1 : ¬ Odd (({1} : Finset (Fin 3)).filter (fun k => x k)).card := by
    rw [hf1]; simp
  rw [grayBase3Matrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [parityGate_mulVec_ket 2 _ (by simp) V x, ite_eq_right ho0,
    parityGate_mulVec_ket 2 _ (by simp) Vᴴ x, ite_eq_right ho01,
    parityGate_mulVec_ket 2 _ (by simp) V x, ite_eq_right ho1]



/-- On the control fibre with first control true and second control false, the three-wire Gray
word acts as the identity, the `Vᴴ` step cancelling the preceding `V` step. -/
theorem grayBase3_trueFalse (V : Matrix Bool Bool ℂ)
    (hV : V ∈ Matrix.unitaryGroup Bool ℂ) (x : Reg 3)
    (h0 : x 0 = true) (h1 : x 1 = false) :
    grayBase3Matrix V *ᵥ Ket x = Ket x := by
  classical
  have hVleft : Vᴴ * V = 1 := (Matrix.mem_unitaryGroup_iff').mp hV
  have hf0 : (({0} : Finset (Fin 3)).filter (fun k => x k)) = {0} := by
    ext k; fin_cases k <;> simp [h0]
  have hf01 : (({0, 1} : Finset (Fin 3)).filter (fun k => x k)) = {0} := by
    ext k; fin_cases k <;> simp [h0, h1]
  have hf1 : (({1} : Finset (Fin 3)).filter (fun k => x k)) = ∅ := by
    ext k; fin_cases k <;> simp [h1]
  have ho0 : Odd (({0} : Finset (Fin 3)).filter (fun k => x k)).card := by
    rw [hf0]; norm_num
  have ho01 : Odd (({0, 1} : Finset (Fin 3)).filter (fun k => x k)).card := by
    rw [hf01]; norm_num
  have ho1 : ¬ Odd (({1} : Finset (Fin 3)).filter (fun k => x k)).card := by
    rw [hf1]; simp
  let c1 : Bool → ℂ := fun b => V b (x 2)
  let c2 : Bool → ℂ := Vᴴ *ᵥ c1
  have hstep1 : parityGate 2 (({0} : Finset (Fin 3))) V *ᵥ Ket x =
      ∑ b : Bool, c1 b • Ket (Function.update x 2 b) := by
    rw [parityGate_zero_mulVec_ket V x]
    simp [ho0, c1]
  have hstep2 : parityGate 2 (({0, 1} : Finset (Fin 3))) Vᴴ *ᵥ
      (∑ b : Bool, c1 b • Ket (Function.update x 2 b)) =
      ∑ b : Bool, c2 b • Ket (Function.update x 2 b) := by
    rw [parityGate_mulVec_targetSum_ite 2 _ (by simp) Vᴴ x c1]
    simp [ho01, c2]
  have hstep3 : parityGate 2 (({1} : Finset (Fin 3))) V *ᵥ
      (∑ b : Bool, c2 b • Ket (Function.update x 2 b)) =
      ∑ b : Bool, c2 b • Ket (Function.update x 2 b) := by
    rw [parityGate_mulVec_targetSum_ite 2 _ (by simp) V x c2]
    simp [ho1]
  have hc2 : c2 = fun b => (1 : Matrix Bool Bool ℂ) b (x 2) := by
    funext b
    have hmul : c2 b = (Vᴴ * V) b (x 2) := by
      simp [c2, c1, Matrix.mulVec, Matrix.mul_apply, dotProduct]
    rw [hmul, hVleft]
  rw [grayBase3Matrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hstep1, hstep2, hstep3]
  rw [hc2, ← ket_eq_targetSum (2 : Fin 3) x]



/-- On the control fibre with first control false and second control true, the three-wire Gray
word acts as the identity, the final `V` step cancelling the preceding `Vᴴ` step. -/
theorem grayBase3_falseTrue (V : Matrix Bool Bool ℂ)
    (hV : V ∈ Matrix.unitaryGroup Bool ℂ) (x : Reg 3)
    (h0 : x 0 = false) (h1 : x 1 = true) :
    grayBase3Matrix V *ᵥ Ket x = Ket x := by
  classical
  have hVright : V * Vᴴ = 1 := (Matrix.mem_unitaryGroup_iff).mp hV
  have hf0 : (({0} : Finset (Fin 3)).filter (fun k => x k)) = ∅ := by
    ext k; fin_cases k <;> simp [h0]
  have hf01 : (({0, 1} : Finset (Fin 3)).filter (fun k => x k)) = {1} := by
    ext k; fin_cases k <;> simp [h0, h1]
  have hf1 : (({1} : Finset (Fin 3)).filter (fun k => x k)) = {1} := by
    ext k; fin_cases k <;> simp [h1]
  have ho0 : ¬ Odd (({0} : Finset (Fin 3)).filter (fun k => x k)).card := by
    rw [hf0]; simp
  have ho01 : Odd (({0, 1} : Finset (Fin 3)).filter (fun k => x k)).card := by
    rw [hf01]; norm_num
  have ho1 : Odd (({1} : Finset (Fin 3)).filter (fun k => x k)).card := by
    rw [hf1]; norm_num
  let c1 : Bool → ℂ := fun b => Vᴴ b (x 2)
  let c2 : Bool → ℂ := V *ᵥ c1
  have hstep1 : parityGate 2 (({0} : Finset (Fin 3))) V *ᵥ Ket x = Ket x := by
    rw [parityGate_mulVec_ket 2 _ (by simp) V x, ite_eq_right ho0]
  have hstep2 : parityGate 2 (({0, 1} : Finset (Fin 3))) Vᴴ *ᵥ Ket x =
      ∑ b : Bool, c1 b • Ket (Function.update x 2 b) := by
    rw [parityGate_mulVec_ket 2 _ (by simp) Vᴴ x, ite_eq_left ho01]
  have hstep3 : parityGate 2 (({1} : Finset (Fin 3))) V *ᵥ
      (∑ b : Bool, c1 b • Ket (Function.update x 2 b)) =
      ∑ b : Bool, c2 b • Ket (Function.update x 2 b) := by
    rw [parityGate_mulVec_targetSum_ite 2 _ (by simp) V x c1]
    simp [ho1, c2]
  have hc2 : c2 = fun b => (1 : Matrix Bool Bool ℂ) b (x 2) := by
    funext b
    have hmul : c2 b = (V * Vᴴ) b (x 2) := by
      simp [c2, c1, Matrix.mulVec, Matrix.mul_apply, dotProduct]
    rw [hmul, hVright]
  rw [grayBase3Matrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hstep1, hstep2, hstep3]
  rw [hc2, ← ket_eq_targetSum (2 : Fin 3) x]

/-- On the control fibre with both controls true, the three-wire Gray word applies `U = V * V`
to the target fibre. -/
theorem grayBase3_trueTrue (V U : Matrix Bool Bool ℂ) (hVV : V * V = U) (x : Reg 3)
    (h0 : x 0 = true) (h1 : x 1 = true) :
    grayBase3Matrix V *ᵥ Ket x =
      ∑ b : Bool, U b (x 2) • Ket (Function.update x 2 b) := by
  classical
  have hf0 : (({0} : Finset (Fin 3)).filter (fun k => x k)) = {0} := by
    ext k; fin_cases k <;> simp [h0]
  have hf01 : (({0, 1} : Finset (Fin 3)).filter (fun k => x k)) = {0, 1} := by
    ext k; fin_cases k <;> simp [h0, h1]
  have hf1 : (({1} : Finset (Fin 3)).filter (fun k => x k)) = {1} := by
    ext k; fin_cases k <;> simp [h1]
  have ho0 : Odd (({0} : Finset (Fin 3)).filter (fun k => x k)).card := by
    rw [hf0]; norm_num
  have ho01 : ¬ Odd (({0, 1} : Finset (Fin 3)).filter (fun k => x k)).card := by
    rw [hf01]; norm_num
  have ho1 : Odd (({1} : Finset (Fin 3)).filter (fun k => x k)).card := by
    rw [hf1]; norm_num
  let c1 : Bool → ℂ := fun b => V b (x 2)
  let c2 : Bool → ℂ := V *ᵥ c1
  have hstep1 : parityGate 2 (({0} : Finset (Fin 3))) V *ᵥ Ket x =
      ∑ b : Bool, c1 b • Ket (Function.update x 2 b) := by
    rw [parityGate_mulVec_ket 2 _ (by simp) V x, ite_eq_left ho0]
  have hstep2 : parityGate 2 (({0, 1} : Finset (Fin 3))) Vᴴ *ᵥ
      (∑ b : Bool, c1 b • Ket (Function.update x 2 b)) =
      ∑ b : Bool, c1 b • Ket (Function.update x 2 b) := by
    rw [parityGate_mulVec_targetSum_ite 2 _ (by simp) Vᴴ x c1]
    simp [ho01]
  have hstep3 : parityGate 2 (({1} : Finset (Fin 3))) V *ᵥ
      (∑ b : Bool, c1 b • Ket (Function.update x 2 b)) =
      ∑ b : Bool, c2 b • Ket (Function.update x 2 b) := by
    rw [parityGate_mulVec_targetSum_ite 2 _ (by simp) V x c1]
    simp [ho1, c2]
  have hc2 : c2 = fun b => U b (x 2) := by
    funext b
    have hmul : c2 b = (V * V) b (x 2) := by
      simp [c2, c1, Matrix.mulVec, Matrix.mul_apply, dotProduct]
    rw [hmul, hVV]
  rw [grayBase3Matrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hstep1, hstep2, hstep3, hc2]



/-- The three-wire Gray word implements the doubly controlled gate on every computational basis
input: it applies `U` to the target exactly when both controls are true. -/
theorem grayBase3_exact (V U : Matrix Bool Bool ℂ)
    (hV : V ∈ Matrix.unitaryGroup Bool ℂ) (hVV : V * V = U) (x : Reg 3) :
    grayBase3Matrix V *ᵥ Ket x =
      if x 0 && x 1 then
        (∑ b : Bool, U b (x 2) • Ket (Function.update x 2 b))
      else Ket x := by
  by_cases h0 : x 0 = true
  · by_cases h1 : x 1 = true
    · rw [ite_eq_left (by simp [h0, h1])]
      exact grayBase3_trueTrue V U hVV x h0 h1
    · have h1f : x 1 = false := by cases h : x 1 <;> simp_all
      rw [ite_eq_right (by simp [h0, h1f])]
      exact grayBase3_trueFalse V hV x h0 h1f
  · have h0f : x 0 = false := by cases h : x 0 <;> simp_all
    by_cases h1 : x 1 = true
    · rw [ite_eq_right (by simp [h0f, h1])]
      exact grayBase3_falseTrue V hV x h0f h1
    · have h1f : x 1 = false := by cases h : x 1 <;> simp_all
      rw [ite_eq_right (by simp [h0f, h1f])]
      exact grayBase3_allFalse V x h0f h1f



/-- The compiled three-step Gray word for `n = 3` is exactly the doubly controlled unitary
whenever `V * V = U`. This gives the matrix identity for the three-wire parity construction. -/
theorem grayBase3_eq_fullCtrl (V U : Matrix Bool Bool ℂ)
    (hV : V ∈ Matrix.unitaryGroup Bool ℂ) (hVV : V * V = U) :
    grayBase3Matrix V = fullCtrlGate (2 : Fin 3) U := by
  classical
  have hcond : ∀ y : Reg 3,
      ((∀ k : Fin 3, k ≠ 2 → y k = true) ↔ (y 0 && y 1) = true) := by
    intro y
    constructor
    · intro h
      simp [h 0 (by decide), h 1 (by decide)]
    · intro h k hk
      fin_cases k <;> simp_all
  have hKet : ∀ y : Reg 3, Ket y = Pi.single y 1 := by
    intro y; funext j; simp [Ket, Pi.single_apply]
  ext x y
  have hx := congrFun (grayBase3_exact V U hV hVV y) x
  have hf := congrFun (fullCtrlGate_mulVec_ket (2 : Fin 3) U y) x
  have hleft : (grayBase3Matrix V *ᵥ Ket y) x = grayBase3Matrix V x y := by
    simp [Matrix.mulVec, hKet y]
  have hright : (fullCtrlGate (2 : Fin 3) U *ᵥ Ket y) x = fullCtrlGate (2 : Fin 3) U x y := by
    simp [Matrix.mulVec, hKet y]
  calc grayBase3Matrix V x y
      = (grayBase3Matrix V *ᵥ Ket y) x := hleft.symm
    _ = (if y 0 && y 1 then
          (∑ b : Bool, U b (y 2) • Ket (Function.update y 2 b)) else Ket y) x := hx
    _ = (if (∀ k : Fin 3, k ≠ 2 → y k = true) then
          (∑ b : Bool, U b (y 2) • Ket (Function.update y 2 b)) else Ket y) x := by
        by_cases h : (y 0 && y 1) = true
        · have hall : ∀ k : Fin 3, k ≠ 2 → y k = true := (hcond y).mpr h
          rw [ite_eq_left h, ite_eq_left hall]
        · have hynot : ¬ ∀ k : Fin 3, k ≠ 2 → y k = true :=
            fun hall => h ((hcond y).mp hall)
          rw [ite_eq_right h, ite_eq_right hynot]
    _ = (fullCtrlGate (2 : Fin 3) U *ᵥ Ket y) x := hf.symm
    _ = fullCtrlGate (2 : Fin 3) U x y := hright

/-- Compiling the three parity-controlled steps gives the doubly controlled unitary. -/
theorem grayBase3_word_exact (V U : Matrix Bool Bool ℂ)
    (hV : V ∈ Matrix.unitaryGroup Bool ℂ) (hVV : V * V = U) :
    compileSteps (2 : Fin 3) (grayBase3Word V) = fullCtrlGate (2 : Fin 3) U := by
  rw [grayBase3Word_compile]
  exact grayBase3_eq_fullCtrl V U hV hVV

end Qatlib.Papers.ElemGates95.MultiControl
