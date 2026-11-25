/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SlowHamSim26.FourierTrunc.FloquetIndices
public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section

/-!
# Hermiticity of the effective and refined Hamiltonians

The Fourier adjoint law makes the effective matrix Hermitian. The
two boundary windows in Eq. (5.12) are disjoint and adjoint to each
other. The source-order wrapper reads the off-diagonal block in
Eq. (4.46) as the coefficient at column index minus row index.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix
open Qatlib.Papers.SlowHamSim26.FourierTrunc
open Qatlib.Papers.SlowHamSim26.Amplification
open Qatlib.Papers.SlowHamSim26.FourierTrunc
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.SlowHamSim26.Amplification

/-- The effective Hamiltonian is Hermitian for the frozen Fourier
index convention when opposite Fourier modes are adjoints. -/
theorem isHermitian_Heff {d L : ℕ} (T : ℝ) (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ)
    (hH : ∀ m : ℤ, (Hm m)ᴴ = Hm (-m)) :
    (Heff T L Hm).IsHermitian := by
  have hz : (Hm 0)ᴴ = Hm 0 := by simpa using hH 0
  have hscalar (l : ℤ) :
      (Matrix.scalar (Fin d) ((l : ℂ) * (omega T : ℂ)))ᴴ =
        Matrix.scalar (Fin d) ((l : ℂ) * (omega T : ℂ)) := by
    rw [Matrix.scalar_apply, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    simp [RCLike.star_def]
  unfold Matrix.IsHermitian
  ext p q
  simp only [Matrix.conjTranspose_apply, Heff]
  by_cases hpq : p.1 = q.1
  · rw [ite_eq_left hpq.symm, ite_eq_left hpq, hpq,
      ← Matrix.conjTranspose_apply, Matrix.conjTranspose_sub, hz, hscalar]
  · rw [ite_eq_right (Ne.symm hpq), ite_eq_right hpq, ← Matrix.conjTranspose_apply, hH, neg_sub]

/-- The forward and backward windows cannot both occur in one boundary block. -/
private theorem boundary_windows_disjoint {L : ℕ} (i j : Fin (2 * L)) :
    let n : ℤ := 2 * (L : ℤ)
    let l := floquetIndexVal L i
    let l' := floquetIndexVal L j
    ¬ ((n - l + 1 ≤ (l' - l) % n ∧ (l' - l) % n ≤ n - 1) ∧
       (n - l' + 1 ≤ (l - l') % n ∧ (l - l') % n ≤ n - 1)) := by
  intro n l l' ⟨h, h'⟩
  have hl : l ≤ L := (floquetIndexVal_mem i).2
  have hl' : l' ≤ L := (floquetIndexVal_mem j).2
  let s := (l' - l) % n + (l - l') % n
  have hs0 : 0 ≤ s - n := by dsimp [s, n] at *; omega
  have hsN : s - n < n := by dsimp [s]; omega
  have hmod : s % n = 0 := by
    dsimp only [s]
    rw [← Int.add_emod, show (l' - l) + (l - l') = 0 by ring, Int.zero_emod]
  have hzero : (s - n) % n = 0 := by
    rw [Int.sub_emod, hmod, Int.emod_self, sub_self, Int.zero_emod]
  have hpos : 0 < s - n := by dsimp [s, n] at *; omega
  rw [Int.emod_eq_of_lt hs0 hsN] at hzero
  exact hpos.ne' hzero

/-- The boundary matrix is Hermitian because the two active windows are
entrywise adjoints of one another. -/
theorem isHermitian_HtildeB {d L : ℕ} (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ) :
    (HtildeB (L := L) Hm).IsHermitian := by
  unfold Matrix.IsHermitian
  ext p q
  let n : ℤ := 2 * (L : ℤ)
  let l := floquetIndexVal L p.1
  let l' := floquetIndexVal L q.1
  let m := (l' - l) % n
  let m' := (l - l') % n
  change star (if n - l' + 1 ≤ m' ∧ m' ≤ n - 1 then Hm m' q.2 p.2
    else if n - l + 1 ≤ m ∧ m ≤ n - 1 then (Hm m)ᴴ q.2 p.2 else 0) =
      if n - l + 1 ≤ m ∧ m ≤ n - 1 then Hm m p.2 q.2
      else if n - l' + 1 ≤ m' ∧ m' ≤ n - 1 then (Hm m')ᴴ p.2 q.2 else 0
  by_cases h : n - l + 1 ≤ m ∧ m ≤ n - 1 <;>
    by_cases h' : n - l' + 1 ≤ m' ∧ m' ≤ n - 1
  · exact (boundary_windows_disjoint p.1 q.1 ⟨h, h'⟩).elim
  · simp only [ite_eq_right h', ite_eq_left h, Matrix.conjTranspose_apply, star_star]
  · simp only [ite_eq_right h, ite_eq_left h', Matrix.conjTranspose_apply]
  · simp only [ite_eq_right h, ite_eq_right h', star_zero]

/-- The frozen refined Hamiltonian inherits Hermiticity from its
ordinary part and the adjoint-completed boundary term. -/
theorem isHermitian_HeffPbc {d L : ℕ} (T : ℝ) (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ)
    (hH : ∀ m : ℤ, (Hm m)ᴴ = Hm (-m)) :
    (HeffPbc (L := L) T Hm).IsHermitian :=
  (isHermitian_Heff T Hm hH).add (isHermitian_HtildeB Hm)

/-- The effective Hamiltonian in the row-column convention of Eq. (4.46).
The frozen matrix is reused with reversed Fourier labels. -/
def sourceHeff {d : ℕ} (T : ℝ) (L : ℕ) (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (2 * L) × Fin d) (Fin (2 * L) × Fin d) ℂ :=
  Heff T L (fun m => Hm (-m))

/-- The off-diagonal block is the Fourier coefficient labeled by column
minus row, exactly as in Eq. (4.46). -/
theorem sourceHeff_offDiagonal {d L : ℕ} (T : ℝ) (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin (2 * L)) (hij : i ≠ j) :
    floquetBlock (sourceHeff T L Hm) i j =
      Hm (floquetIndexVal L j - floquetIndexVal L i) := by
  ext a b
  simp [floquetBlock, sourceHeff, Heff, hij, neg_sub]

/-- Add the boundary term in Eq. (5.12) to the source-order ordinary matrix. -/
def sourceHeffPbc {d L : ℕ} (T : ℝ) (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (2 * L) × Fin d) (Fin (2 * L) × Fin d) ℂ :=
  sourceHeff T L Hm + HtildeB Hm

/-- The source-order periodic Hamiltonian is Hermitian under the Fourier adjoint law. -/
theorem isHermitian_sourceHeffPbc {d L : ℕ} (T : ℝ)
    (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ) (hH : ∀ m : ℤ, (Hm m)ᴴ = Hm (-m)) :
    (sourceHeffPbc (L := L) T Hm).IsHermitian :=
  (isHermitian_Heff T (fun m => Hm (-m)) (fun m => hH (-m))).add
    (isHermitian_HtildeB Hm)

/-- The source-order refined Hamiltonian generates a unitary at every real time. -/
theorem sourcePbc_timeEvol_unitary {d L : ℕ} (T t : ℝ)
    (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ) (hH : ∀ m : ℤ, (Hm m)ᴴ = Hm (-m)) :
    timeEvol (sourceHeffPbc (L := L) T Hm) t ∈ Matrix.unitaryGroup (Fin (2 * L) × Fin d) ℂ := by
  have h := hamiltonianEvolution_unitary (isHermitian_sourceHeffPbc (L := L) T Hm hH) t
  simpa only [HamiltonianEvolution, timeEvol, neg_mul, mul_comm (t : ℂ) Complex.I] using h

end Qatlib.Papers.SlowHamSim26.Amplification
