/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Defs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open scoped BigOperators Classical

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ClusterPatterns.CnotPatterns

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns

private def readoutRow {w m : ℕ} (z : Fin w → Bool) (xp : Fin (2 ^ m)) : Reg (w + m) :=
  fun t => if h : (t : ℕ) < w then z ⟨t, h⟩
    else (bitVecEquiv m).symm xp ⟨(t : ℕ) - w, by omega⟩

theorem reg_ext {w m : ℕ} (u v : Reg (w + m))
    (hmeas : ∀ j : Fin w, u (Fin.castLE (by omega : w ≤ w + m) j) = v (Fin.castLE (by omega) j))
    (hout : ∀ k : Fin m, u (Fin.natAdd w k) = v (Fin.natAdd w k)) : u = v := by
  funext t
  by_cases ht : (t : ℕ) < w
  · have ht' : t = Fin.castLE (by omega : w ≤ w + m) ⟨t, ht⟩ := by
      ext; simp
    rw [ht']; exact hmeas _
  · have ht' : t = Fin.natAdd w ⟨(t : ℕ) - w, by omega⟩ := by
      ext; simp; omega
    rw [ht']; exact hout _

theorem readoutRow_meas {w m : ℕ} (z : Fin w → Bool) (xp : Fin (2 ^ m)) (j : Fin w) :
    readoutRow z xp (Fin.castLE (by omega : w ≤ w + m) j) = z j := by
  simp [readoutRow]

theorem readoutRow_out {w m : ℕ} (z : Fin w → Bool) (xp : Fin (2 ^ m)) (k : Fin m) :
    readoutRow z xp (Fin.natAdd w k) = (bitVecEquiv m).symm xp k := by
  simp [readoutRow]

theorem readoutRow_eq {w m : ℕ} (z : Fin w → Bool) (xp : Fin (2 ^ m)) (u : Reg (w + m))
    (h1 : ∀ j : Fin w, u (Fin.castLE (by omega : w ≤ w + m) j) = z j)
    (h2 : bitVecEquiv m (fun k => u (Fin.natAdd w k)) = xp) : u = readoutRow z xp := by
  apply reg_ext
  · intro j; rw [h1]; exact (readoutRow_meas z xp j).symm
  · intro k
    have h2' : (bitVecEquiv m).symm xp = (fun k => u (Fin.natAdd w k)) :=
      (Equiv.symm_apply_eq (bitVecEquiv m)).mpr h2.symm
    rw [show u (Fin.natAdd w k) = (bitVecEquiv m).symm xp k from (congrFun h2' k).symm]
    exact (readoutRow_out z xp k).symm

def mpOutBit {n w m : ℕ} (P : MpPattern n w m) (s : Fin w → Bool)
    (xp : Fin (2 ^ m)) (k : Fin m) : Bool :=
  xor (P.xCorr k s) ((bitVecEquiv m).symm xp k)

def flipRow {n w m : ℕ} (P : MpPattern n w m) (s : Fin w → Bool) (u : Reg (w + m)) :
    Reg (w + m) :=
  fun t => if h : (t : ℕ) < w then u t
    else xor (P.xCorr ⟨(t : ℕ) - w, by omega⟩ s) (u t)

theorem flipRow_meas {n w m : ℕ} (P : MpPattern n w m) (s : Fin w → Bool)
    (u : Reg (w + m)) (j : Fin w) :
    flipRow P s u (Fin.castLE (by omega : w ≤ w + m) j) = u (Fin.castLE (by omega) j) := by
  have hlt : (↑(Fin.castLE (by omega : w ≤ w + m) j) : ℕ) < w := by
    rw [Fin.val_castLE]; exact j.isLt
  simp only [flipRow]
  rw [dif_pos hlt]

theorem flipRow_out {n w m : ℕ} (P : MpPattern n w m) (s : Fin w → Bool)
    (u : Reg (w + m)) (k : Fin m) :
    flipRow P s u (Fin.natAdd w k) = xor (P.xCorr k s) (u (Fin.natAdd w k)) := by
  have hlt : ¬ (↑(Fin.natAdd w k) : ℕ) < w := by
    rw [Fin.val_natAdd]; omega
  simp only [flipRow]
  rw [dif_neg hlt]
  congr 1
  congr 1
  ext
  simp [Fin.val_natAdd, Nat.add_sub_cancel_left]

noncomputable def corePre {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) (s : Fin w → Bool) :
    Matrix (Fin (2 ^ m)) (Reg n) ℂ :=
  Matrix.of fun xp y =>
    (∏ k : Fin m, if P.zCorr k s && mpOutBit P s xp k then (-1 : ℂ) else 1) *
      ∑ c : Reg (w + m),
        (∏ j : Fin w, star (mpSVector (mpAdaptiveAngle P s j) (s j)
            (c (Fin.castLE (by omega : w ≤ w + m) j))))
          * (if ∀ v : Fin m, c (Fin.natAdd w v) = mpOutBit P s xp v then (1 : ℂ) else 0)
          * (P.entangler * mpLoadMatrix P resource) c y

noncomputable def core {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) (s : Fin w → Bool) :
    Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) ℂ :=
  Matrix.reindex (Equiv.refl _) (bitVecEquiv n) (corePre P resource s)

theorem readout_mul {w m : ℕ} (z : Fin w → Bool) {ρ : Type*} [Fintype ρ]
    (M : Matrix (Reg (w + m)) ρ ℂ) :
    mpReadout w m z * M = Matrix.of fun xp y => M (readoutRow z xp) y := by
  ext xp y
  rw [Matrix.mul_apply]
  simp only [mpReadout, Matrix.of_apply]
  rw [Finset.sum_eq_single (readoutRow z xp)]
  · rw [if_pos, one_mul]
    exact ⟨fun j => readoutRow_meas z xp j,
      by simp only [readoutRow_out]; exact Equiv.apply_symm_apply (bitVecEquiv m) xp⟩
  · intro u _ hne
    rw [if_neg, zero_mul]
    intro hc
    exact hne (readoutRow_eq z xp u hc.1 hc.2)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem corr_mul {n w m : ℕ} (P : MpPattern n w m) (s : Fin w → Bool) {ρ : Type*} [Fintype ρ]
    (M : Matrix (Reg (w + m)) ρ ℂ) :
    mpCorrection P s * M = Matrix.of fun u y =>
      (∏ k : Fin m, if P.zCorr k s && flipRow P s u (Fin.natAdd w k) then (-1 : ℂ) else 1)
        * M (flipRow P s u) y := by
  ext u y
  rw [Matrix.mul_apply]
  simp only [mpCorrection, Matrix.of_apply]
  rw [Finset.sum_eq_single (flipRow P s u)]
  · have hmeas0 : ∀ j : Fin w, u (Fin.castLE (by omega : w ≤ w + m) j)
        = flipRow P s u (Fin.castLE (by omega) j) := by
      intro j; rw [flipRow_meas]
    have hout0 : ∀ k : Fin m, u (Fin.natAdd w k)
        = xor (P.xCorr k s) (flipRow P s u (Fin.natAdd w k)) := by
      intro k
      rw [flipRow_out P s u k]
      simp [← Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    rw [if_pos hmeas0, if_pos hout0]
  · intro u' _ hne
    by_cases hmeas : ∀ j : Fin w, u (Fin.castLE (by omega : w ≤ w + m) j)
        = u' (Fin.castLE (by omega) j)
    · by_cases hout : ∀ k : Fin m, u (Fin.natAdd w k)
          = xor (P.xCorr k s) (u' (Fin.natAdd w k))
      · exfalso
        apply hne
        apply reg_ext
        · intro j
          exact (hmeas j).symm.trans (flipRow_meas P s u j).symm
        · intro k
          have hx : xor (P.xCorr k s) (u (Fin.natAdd w k)) = u' (Fin.natAdd w k) := by
            rw [hout k]
            simp [← Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
          exact hx.symm.trans (flipRow_out P s u k).symm
      · rw [if_pos hmeas, if_neg hout, zero_mul]
    · rw [if_neg hmeas, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem proj_mul {n w m : ℕ} (P : MpPattern n w m) (s : Fin w → Bool) {ρ : Type*} [Fintype ρ]
    (M : Matrix (Reg (w + m)) ρ ℂ) :
    mpProjector P s * M = Matrix.of fun a y =>
      (∏ j : Fin w, mpSVector (mpAdaptiveAngle P s j) (s j)
          (a (Fin.castLE (by omega : w ≤ w + m) j)))
        * ∑ b : Reg (w + m),
            (∏ j : Fin w, star (mpSVector (mpAdaptiveAngle P s j) (s j)
                (b (Fin.castLE (by omega) j))))
              * (if ∀ v : Fin m, b (Fin.natAdd w v) = a (Fin.natAdd w v) then (1 : ℂ) else 0)
              * M b y := by
  ext a y
  rw [Matrix.mul_apply]
  simp only [mpProjector, Matrix.of_apply]
  have hterm : ∀ b : Reg (w + m),
      (∏ j : Fin w, mpSVector (mpAdaptiveAngle P s j) (s j)
            (a (Fin.castLE (by omega : w ≤ w + m) j))
          * star (mpSVector (mpAdaptiveAngle P s j) (s j) (b (Fin.castLE (by omega) j))))
        * (if ∀ v : Fin m, a (Fin.natAdd w v) = b (Fin.natAdd w v) then (1 : ℂ) else 0)
        * M b y
      = (∏ j : Fin w, mpSVector (mpAdaptiveAngle P s j) (s j)
            (a (Fin.castLE (by omega : w ≤ w + m) j)))
          * ((∏ j : Fin w, star (mpSVector (mpAdaptiveAngle P s j) (s j)
                (b (Fin.castLE (by omega) j))))
              * (if ∀ v : Fin m, b (Fin.natAdd w v) = a (Fin.natAdd w v) then (1 : ℂ) else 0)
              * M b y) := by
    intro b
    have hdist : (∏ j : Fin w, mpSVector (mpAdaptiveAngle P s j) (s j)
            (a (Fin.castLE (by omega : w ≤ w + m) j))
          * star (mpSVector (mpAdaptiveAngle P s j) (s j) (b (Fin.castLE (by omega) j))))
        = (∏ j : Fin w, mpSVector (mpAdaptiveAngle P s j) (s j)
            (a (Fin.castLE (by omega : w ≤ w + m) j)))
          * (∏ j : Fin w, star (mpSVector (mpAdaptiveAngle P s j) (s j)
              (b (Fin.castLE (by omega) j)))) := Finset.prod_mul_distrib
    rw [hdist]
    by_cases h : ∀ v : Fin m, a (Fin.natAdd w v) = b (Fin.natAdd w v)
    · have h' : ∀ v : Fin m, b (Fin.natAdd w v) = a (Fin.natAdd w v) := fun v => (h v).symm
      rw [if_pos h, if_pos h']
      ring
    · have h' : ¬ ∀ v : Fin m, b (Fin.natAdd w v) = a (Fin.natAdd w v) :=
        fun hh => h (fun v => (hh v).symm)
      rw [if_neg h, if_neg h']
      ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]

theorem kraus_pre_eq_smul {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) (s z : Fin w → Bool) :
    mpReadout w m z * mpCorrection P s * mpProjector P s * P.entangler * mpLoadMatrix P resource
      = (∏ j : Fin w, mpSVector (mpAdaptiveAngle P s j) (s j) (z j)) • corePre P resource s := by
  have hassoc : mpReadout w m z * mpCorrection P s * mpProjector P s * P.entangler
        * mpLoadMatrix P resource
      = mpReadout w m z
          * (mpCorrection P s * (mpProjector P s * (P.entangler * mpLoadMatrix P resource))) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, readout_mul, corr_mul, proj_mul]
  ext xp y
  simp only [corePre, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have ha_meas : ∀ j : Fin w,
      flipRow P s (readoutRow z xp) (Fin.castLE (by omega : w ≤ w + m) j) = z j := by
    intro j
    rw [flipRow_meas, readoutRow_meas]
  have ha_out : ∀ k : Fin m,
      flipRow P s (readoutRow z xp) (Fin.natAdd w k) = mpOutBit P s xp k := by
    intro k
    rw [flipRow_out, readoutRow_out]
    rfl
  have hA : (∏ j : Fin w, mpSVector (mpAdaptiveAngle P s j) (s j)
        (flipRow P s (readoutRow z xp) (Fin.castLE (by omega : w ≤ w + m) j)))
      = ∏ j : Fin w, mpSVector (mpAdaptiveAngle P s j) (s j) (z j) := by
    apply Finset.prod_congr rfl
    intro j _; rw [ha_meas]
  have hsign : (∏ k : Fin m, if P.zCorr k s
          && flipRow P s (readoutRow z xp) (Fin.natAdd w k) then (-1 : ℂ) else 1)
      = (∏ k : Fin m, if P.zCorr k s && mpOutBit P s xp k then (-1 : ℂ) else 1) := by
    apply Finset.prod_congr rfl
    intro k _; rw [ha_out]
  have hcond : ∀ b : Reg (w + m),
      (∀ v : Fin m, b (Fin.natAdd w v) = flipRow P s (readoutRow z xp) (Fin.natAdd w v))
        ↔ (∀ v : Fin m, b (Fin.natAdd w v) = mpOutBit P s xp v) := by
    intro b
    constructor <;> intro h v
    · exact (h v).trans (ha_out v)
    · exact (h v).trans (ha_out v).symm
  have hdelta : (∑ b : Reg (w + m),
        (∏ j : Fin w, star (mpSVector (mpAdaptiveAngle P s j) (s j) (b (Fin.castLE (by omega) j))))
          * (if ∀ v : Fin m, b (Fin.natAdd w v)
              = flipRow P s (readoutRow z xp) (Fin.natAdd w v) then (1 : ℂ) else 0)
          * (P.entangler * mpLoadMatrix P resource) b y)
      = (∑ c : Reg (w + m),
        (∏ j : Fin w, star (mpSVector (mpAdaptiveAngle P s j) (s j) (c (Fin.castLE (by omega) j))))
          * (if ∀ v : Fin m, c (Fin.natAdd w v) = mpOutBit P s xp v then (1 : ℂ) else 0)
          * (P.entangler * mpLoadMatrix P resource) c y) := by
    apply Finset.sum_congr rfl
    intro b _
    simp only [hcond b]
  rw [hA, hsign, hdelta]
  ring

theorem kraus_eq_smul_core {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) (s z : Fin w → Bool) :
    mpPatternKraus P resource s z
      = (∏ j : Fin w, mpSVector (mpAdaptiveAngle P s j) (s j) (z j)) • core P resource s := by
  unfold mpPatternKraus core
  rw [kraus_pre_eq_smul]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]
end Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
