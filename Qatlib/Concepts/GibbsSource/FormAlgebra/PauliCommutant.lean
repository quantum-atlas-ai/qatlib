/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.CssPauli

@[expose] public section


/-! Scalarity of the joint commutant of the complete local Pauli family.
The computational-register representation is fixed by the existing CSS matrices. -/
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib

namespace Qatlib.Concepts.GibbsSource.FormAlgebra

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The phase associated with a bit is nonzero. -/
theorem phaseOfBit_ne_zero (b : ZMod 2) : phaseOfBit b ≠ 0 := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) b with rfl | rfl <;>
    norm_num [phaseOfBit]

/-- The bit phase map is injective. -/
theorem phaseOfBit_injective : Function.Injective phaseOfBit := by
  intro b b' h
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) b with rfl | rfl <;>
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) b' with rfl | rfl <;>
      simp only [phaseOfBit_zero, phaseOfBit_one] at h <;>
      first | rfl | (exfalso; norm_num at h)

/-- Taking the bit dot product with a single-site unit vector reads that site's bit. -/
theorem bitDot_single_left (i : ι) (a : ι → ZMod 2) :
    bitDot (Pi.single i 1) a = a i := by
  rw [bitDot_comm, bitDot_single]

/-- A single-site Pauli Z diagonal entry is the phase of the corresponding register bit. -/
theorem cssPauliZ_single_apply (i : ι) (a : ι → ZMod 2) :
    cssPauliZ (Pi.single i 1) a a = phaseOfBit (a i) := by
  simp [cssPauliZ, bitDot_single_left]

/-- Left multiplication by a CSS Pauli X matrix translates the row index by its bit vector. -/
theorem cssPauliX_mul_apply (x : ι → ZMod 2) (Y : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ)
    (a b : ι → ZMod 2) : (cssPauliX x * Y) a b = Y (a + x) b := by
  classical
  simp only [Matrix.mul_apply, cssPauliX, Matrix.of_apply]
  rw [Finset.sum_eq_single (a + x)]
  · simp [show (a + x) + x = a from by rw [add_assoc, binary_add_self x, add_zero]]
  · intro c _ hc
    have hne : ¬ (a = c + x) := fun hcon =>
      hc (by rw [hcon, add_assoc, binary_add_self x, add_zero])
    simp [hne]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

/-- Right multiplication by a CSS Pauli X matrix translates the column index by its bit vector. -/
theorem cssPauliX_mul_apply_right (x : ι → ZMod 2) (Y : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ)
    (a b : ι → ZMod 2) : (Y * cssPauliX x) a b = Y a (b + x) := by
  classical
  simp only [Matrix.mul_apply, cssPauliX, Matrix.of_apply]
  rw [Finset.sum_eq_single (b + x)]
  · simp
  · intro c _ hc
    simp [hc]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

/-- An operator commuting with every single-site Pauli Z matrix is diagonal. -/
theorem cssPauliZ_comm_diagonal {Y : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ}
    (hZ : ∀ i, Y * cssPauliZ (Pi.single i 1) = cssPauliZ (Pi.single i 1) * Y) :
    Y = Matrix.diagonal (fun a => Y a a) := by
  classical
  ext a b
  by_cases hab : a = b
  · subst hab
    simp
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra h
      push Not at h
      exact hab (funext h)
    have hentry : Y a b * phaseOfBit (b i) = phaseOfBit (a i) * Y a b := by
      have h := congrFun (congrFun (hZ i) a) b
      simpa [Matrix.mul_apply, cssPauliZ, Matrix.diagonal_apply, bitDot_single_left] using h
    have hne : phaseOfBit (a i) = - phaseOfBit (b i) := by
      have h1 := phaseOfBit_mul_self (a i)
      have h2 := phaseOfBit_mul_self (b i)
      have hne' : phaseOfBit (a i) ≠ phaseOfBit (b i) := fun h => hi (phaseOfBit_injective h)
      have hfac : (phaseOfBit (a i) - phaseOfBit (b i))
          * (phaseOfBit (a i) + phaseOfBit (b i)) = 0 := by
        linear_combination h1 - h2
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd (sub_eq_zero.mp h) hne'
      · exact eq_neg_of_add_eq_zero_right (by rw [add_comm]; exact h)
    have hxx : Y a b * phaseOfBit (b i) = -(Y a b * phaseOfBit (b i)) := by
      have h' := hentry
      rw [hne, neg_mul, mul_comm (phaseOfBit (b i)) (Y a b)] at h'
      exact h'
    have h2 : (2 : ℂ) * (Y a b * phaseOfBit (b i)) = 0 := by
      linear_combination (1 : ℂ) * hxx
    have hz : Y a b * phaseOfBit (b i) = 0 :=
      (mul_eq_zero.mp h2).resolve_left (by norm_num)
    rw [Matrix.diagonal_apply, ite_eq_right hab]
    exact (mul_eq_zero.mp hz).resolve_right (phaseOfBit_ne_zero _)

/-- Commuting with every single-site Pauli X makes diagonal entries invariant under each
single-bit flip. -/
theorem cssPauliX_comm_diagonal_step {Y : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ}
    (hX : ∀ i, Y * cssPauliX (Pi.single i 1) = cssPauliX (Pi.single i 1) * Y)
    (u : ι → ZMod 2) (i : ι) :
    Y u u = Y (u + Pi.single i 1) (u + Pi.single i 1) := by
  have h := congrFun (congrFun (hX i) u) (u + Pi.single i 1)
  rw [cssPauliX_mul_apply_right (Pi.single i 1) Y u (u + Pi.single i 1),
    cssPauliX_mul_apply (Pi.single i 1) Y u (u + Pi.single i 1)] at h
  rw [show (u + Pi.single i 1) + Pi.single i 1 = u from by
    rw [add_assoc, binary_add_self (Pi.single i 1), add_zero]] at h
  exact h

/-- An operator commuting with every single-site Pauli X matrix has constant diagonal entries. -/
theorem cssPauliX_comm_diagonal_constant {Y : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ}
    (hX : ∀ i, Y * cssPauliX (Pi.single i 1) = cssPauliX (Pi.single i 1) * Y)
    (a b : ι → ZMod 2) : Y a a = Y b b := by
  classical
  have hsum : (∑ i : ι, Pi.single i ((a + b) i)) = a + b := by
    ext k
    simp only [Finset.sum_apply, Pi.add_apply]
    rw [Finset.sum_eq_single k]
    · simp [Pi.single_eq_same]
    · intro i _ hi
      rw [Pi.single_apply, ite_eq_right (Ne.symm hi)]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have key : ∀ (s : Finset ι) (u : ι → ZMod 2),
      Y u u = Y (u + ∑ i ∈ s, Pi.single i ((a + b) i))
        (u + ∑ i ∈ s, Pi.single i ((a + b) i)) := by
    intro s
    refine Finset.induction_on s ?base ?step
    · intro u; simp
    · intro i s his ih u
      rw [Finset.sum_insert his]
      have hre : u + (Pi.single i ((a + b) i) + ∑ j ∈ s, Pi.single j ((a + b) j))
          = (u + Pi.single i ((a + b) i)) + ∑ j ∈ s, Pi.single j ((a + b) j) := by
        rw [add_assoc]
      have hstep1 : Y u u
          = Y (u + Pi.single i ((a + b) i)) (u + Pi.single i ((a + b) i)) := by
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) ((a + b) i) with h0 | h1'
        · rw [h0, Pi.single_zero, add_zero]
        · rw [h1']
          exact cssPauliX_comm_diagonal_step hX u i
      refine hstep1.trans ?_
      rw [hre]
      exact ih (u + Pi.single i ((a + b) i))
  have hfinal := key Finset.univ a
  rw [hsum] at hfinal
  rw [show a + (a + b) = b from by rw [← add_assoc, binary_add_self a, zero_add]] at hfinal
  exact hfinal

/-- An operator commuting with every single-site Pauli X and Z matrix is a scalar multiple of
the identity. -/
theorem singleSitePauli_commutant_scalar {Y : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ}
    (hX : ∀ i, Y * cssPauliX (Pi.single i 1) = cssPauliX (Pi.single i 1) * Y)
    (hZ : ∀ i, Y * cssPauliZ (Pi.single i 1) = cssPauliZ (Pi.single i 1) * Y) :
    ∃ c : ℂ, Y = c • (1 : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) := by
  classical
  refine ⟨Y 0 0, ?_⟩
  have hdiag := cssPauliZ_comm_diagonal hZ
  have hconst := cssPauliX_comm_diagonal_constant hX
  ext a b
  conv_lhs => rw [hdiag]
  by_cases hab : a = b
  · rw [Matrix.diagonal_apply, ite_eq_left hab, Matrix.smul_apply, Matrix.one_apply, ite_eq_left hab,
      smul_eq_mul, mul_one]
    exact hconst a 0
  · rw [Matrix.diagonal_apply, ite_eq_right hab, Matrix.smul_apply, Matrix.one_apply, ite_eq_right hab]
    simp

end Qatlib.Concepts.GibbsSource.FormAlgebra
