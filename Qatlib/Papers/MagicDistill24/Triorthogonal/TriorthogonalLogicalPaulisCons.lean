/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalRowsDirectCons
public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalLogicalPaulisStat

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

open Matrix

/-- Shows that every element of `ZMod 2` is zero or one. -/
private theorem zmod2_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  have hlt : b.val < 2 := b.isLt
  have h : b.val = 0 ∨ b.val = 1 := by omega
  rcases h with h | h
  · left
    have h0 : b.val = (0 : ZMod 2).val := by rw [ZMod.val_zero]; exact h
    exact ZMod.val_injective 2 h0
  · right
    have h0 : b.val = (1 : ZMod 2).val := by rw [ZMod.val_one]; exact h
    exact ZMod.val_injective 2 h0

/-- Shows that one plus one is zero in `ZMod 2`. -/
private theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

/-- Shows that `qPhase` converts addition modulo two into multiplication of phases. -/
private theorem qPhase_add (a b : ZMod 2) : qPhase (a + b) = qPhase a * qPhase b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [qPhase, zmod2_one_add_one]

/-- Shows that every binary phase squares to one. -/
private theorem qPhase_mul_self (a : ZMod 2) : qPhase a * qPhase a = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> simp [qPhase]

/-- Cancels two equal binary phase factors around another phase. -/
private theorem qPhase_mul_cancel (a b : ZMod 2) :
    qPhase a * qPhase b * qPhase a = qPhase b := by
  have h : qPhase a * qPhase b * qPhase a = (qPhase a * qPhase a) * qPhase b := by ring
  rw [h, qPhase_mul_self]
  try rw [one_mul]

/-- Shows that the field trace commutes with finite sums. -/
private theorem trace_sum {n : ℕ} (z : Fin n → F1024) :
    ∑ i, f1024Trace (z i) = f1024Trace (∑ i, z i) :=
  (map_sum (Algebra.trace (ZMod 2) F1024) z Finset.univ).symm

/-- Combines a sum of traces of constant multiples into the trace of the constant times the sum. -/
private theorem trace_const_mul_sum {n : ℕ} (c : F1024) (z : Fin n → F1024) :
    ∑ i, f1024Trace (c * z i) = f1024Trace (c * ∑ i, z i) := by
  rw [trace_sum, Finset.mul_sum, ← trace_sum]

/-- Computes the diagonal sigma-weighted pairing of distinguished generator rows. -/
private theorem triPair_rows' {m n k : ℕ} (D : TriorthogonalData m n k)
    (a b : Fin k) :
    ∑ i, D.σ i * D.G (Fin.castLE D.hk a) i * D.G (Fin.castLE D.hk b) i
      = if a = b then D.τ a else 0 := by
  rw [triPair_rows D b a]
  by_cases hab : a = b
  · rw [ite_eq_left hab.symm, ite_eq_left hab]
  · rw [ite_eq_right (fun hc => hab hc.symm), ite_eq_right hab]

/-- Rewrites the product of translation and coordinate indicators using the resulting translated
coordinate condition. -/
private theorem ite_mul_ite {n : ℕ} (v : Fin n → F1024) (x y z : Fin n → F1024)
    (c : ℂ) :
    (if x = z + v then (1 : ℂ) else 0) * (if z = y then c else 0)
      = if x = y + v then (if z = y then c else 0) else 0 := by
  by_cases h1 : x = z + v <;> by_cases h2 : z = y <;> simp [h1, h2]

/-- Computes the matrix entries of a vector qudit X operator followed by a vector qudit Z
operator. -/
theorem xVec_mul_zVec_apply {n : ℕ} (v w : Fin n → F1024)
    (x y : Fin n → F1024) :
    (quditXVec v * quditZVec w) x y
      = if x = y + v then qPhase (∑ i, f1024Trace (w i * y i)) else 0 := by
  rw [Matrix.mul_apply]
  simp only [quditXVec, quditZVec, Matrix.of_apply, Matrix.diagonal_apply,
    ite_mul_ite]
  simp

/-- Rewrites the product of coordinate and translation indicators using the resulting translated
coordinate condition. -/
private theorem ite_mul_ite_zx {n : ℕ} (v : Fin n → F1024) (x y z : Fin n → F1024)
    (c : ℂ) :
    (if x = z then c else 0) * (if z = y + v then (1 : ℂ) else 0)
      = if x = y + v then (if z = x then c else 0) else 0 := by
  by_cases h1 : x = z
  · by_cases h2 : z = y + v
    · have h3 : x = y + v := by rw [h1, h2]
      rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h3, ite_eq_left h1.symm, mul_one]
    · have h3 : x ≠ y + v := fun hc => h2 (h1.symm.trans hc)
      rw [ite_eq_left h1, ite_eq_right h2, mul_zero, ite_eq_right h3]
  · by_cases h2 : z = y + v
    · have h3 : x ≠ y + v := fun hc => h1 (hc.trans h2.symm)
      rw [ite_eq_right h1, zero_mul, ite_eq_right h3]
    · have hne : ¬(z = x) := fun hc => h1 hc.symm
      rw [ite_eq_right h1, ite_eq_right h2, zero_mul, ite_eq_right hne]
      simp

/-- Computes the matrix entries of a vector qudit Z operator followed by a vector qudit X
operator. -/
theorem zVec_mul_xVec_apply {n : ℕ} (v w : Fin n → F1024)
    (x y : Fin n → F1024) :
    (quditZVec w * quditXVec v) x y
      = if x = y + v then qPhase (∑ i, f1024Trace (w i * x i)) else 0 := by
  rw [Matrix.mul_apply]
  simp only [quditXVec, quditZVec, Matrix.of_apply, Matrix.diagonal_apply,
    ite_mul_ite_zx]
  simp

/-- Gives the commutation relation for vector qudit X and Z operators with the trace-pairing
phase. -/
theorem xVec_zVec_comm {n : ℕ} (v w : Fin n → F1024) :
    quditXVec v * quditZVec w
      = qPhase (∑ i, f1024Trace (v i * w i)) • (quditZVec w * quditXVec v) := by
  ext x y
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [xVec_mul_zVec_apply, zVec_mul_xVec_apply]
  by_cases h : x = y + v
  · rw [ite_eq_left h, ite_eq_left h]
    have hxy : ∀ i : Fin n, x i = y i + v i := fun i => congrFun h i
    have hsum : ∑ i, f1024Trace (w i * x i)
        = (∑ i, f1024Trace (w i * y i)) + ∑ i, f1024Trace (v i * w i) := by
      have h1 : ∀ i : Fin n, w i * x i = w i * y i + v i * w i := by
        intro i
        rw [hxy i]
        ring
      calc ∑ i, f1024Trace (w i * x i)
          = ∑ i, f1024Trace (w i * y i + v i * w i) :=
            Finset.sum_congr rfl fun i _ => by rw [h1 i]
        _ = ∑ i, (f1024Trace (w i * y i) + f1024Trace (v i * w i)) :=
            Finset.sum_congr rfl fun i _ => map_add (Algebra.trace (ZMod 2) F1024) _ _
        _ = (∑ i, f1024Trace (w i * y i)) + ∑ i, f1024Trace (v i * w i) :=
            Finset.sum_add_distrib
    rw [hsum, qPhase_add, ← mul_assoc, qPhase_mul_cancel]
  · rw [ite_eq_right h, ite_eq_right h]
    simp

/-- Establishes the logical Pauli operators specified by `TriorthogonalLogicalPaulis`. -/
theorem triorthogonalLogicalPaulis : TriorthogonalLogicalPaulis := by
  intro m n k D a b β γ
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    have hphase : ∑ i, f1024Trace ((β • D.G (Fin.castLE D.hk a)) i * w i) = 0 := by
      have h1 : ∀ i : Fin n, (β • D.G (Fin.castLE D.hk a)) i * w i
          = β * (D.G (Fin.castLE D.hk a) i * w i) := by
        intro i
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl fun i _ => by rw [h1 i], trace_const_mul_sum,
        dot_eq_zero_of_mem_dual D hw (row_mem_triG D (Fin.castLE D.hk a))]
      simp [f1024Trace]
    rw [xVec_zVec_comm, hphase, qPhase_zero, one_smul]
  · intro v hv
    have hphase : ∑ i, f1024Trace (v i * (γ • triGhat D a) i) = 0 := by
      have h1 : ∀ i : Fin n, v i * (γ • triGhat D a) i
          = (γ * (D.τ a)⁻¹) * (D.σ i * D.G (Fin.castLE D.hk a) i * v i) := by
        intro i
        simp only [Pi.smul_apply, smul_eq_mul, triGhat]
        ring
      rw [Finset.sum_congr rfl fun i _ => by rw [h1 i], trace_const_mul_sum,
        sigma_pair_clause0 D a v hv]
      simp [f1024Trace]
    have hcomm := xVec_zVec_comm v (γ • triGhat D a)
    rw [hphase, qPhase_zero, one_smul] at hcomm
    exact hcomm.symm
  · have hphase : ∑ i, f1024Trace ((β • D.G (Fin.castLE D.hk a)) i
          * (γ • triGhat D b) i)
        = f1024Trace (β * γ) * (if a = b then 1 else 0) := by
      have h1 : ∀ i : Fin n, (β • D.G (Fin.castLE D.hk a)) i * (γ • triGhat D b) i
          = (β * γ * (D.τ b)⁻¹)
              * (D.σ i * D.G (Fin.castLE D.hk a) i * D.G (Fin.castLE D.hk b) i) := by
        intro i
        simp only [Pi.smul_apply, smul_eq_mul, triGhat]
        ring
      rw [Finset.sum_congr rfl fun i _ => by rw [h1 i], trace_const_mul_sum]
      by_cases hab : a = b
      · have hrow : ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i
              * D.G (Fin.castLE D.hk b) i = D.τ b := by
          rw [triPair_rows' D b b]
          simp
        have hc : (β * γ * (D.τ b)⁻¹) * D.τ b = β * γ := by
          rw [mul_assoc, inv_mul_cancel₀ (D.hτ b), mul_one]
        rw [hab, hrow, hc]
        simp
      · rw [triPair_rows' D a b, ite_eq_right hab, ite_eq_right hab, mul_zero]
        simp [f1024Trace]
    rw [xVec_zVec_comm, hphase]

end Qatlib.Papers.MagicDistill24.Triorthogonal
