/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StateTesting26.MainResults.SwapObservable
public import Qatlib.Papers.StateTesting26.MainResults.PurityIdentity

@[expose] public section

/-!
# The two-copy SWAP test as a fixed `t`-copy scheme

Section 1.2.1 and Appendix A of the paper read the purity of a state off a batch of `SWAP(t)`
observables. This module builds the `t = 2`, `k = 1` instance as an honest
`Qatlib.Papers.StateTesting26.MainResults.Model.FixedTCopyScheme d 2 1 Bool`: the POVM whose two
outcome effects are the spectral projectors `½(I + SWAP)` and `½(I − SWAP)` of the swap operator
`Qatlib.Papers.StateTesting26.MainResults.Model.swapTwo`, with the deterministic decision "accept
on the first outcome".

The Born probabilities of that POVM are actual traces
(`Qatlib.Papers.StateTesting26.MainResults.Model.roundProb` applied to the two-copy state
`MState.npow ρ 2`), and the main theorem computes the acceptance probability as `½ + ½ tr(ρ²)`.
This is the swap-test acceptance identity transported to the model layer of this paper and wrapped
in the paper's own scheme interface; it is the `t = 2`, single-block case of the `SWAP(t)` read-out
of Appendix A.

Paper: [arXiv:2604.07460v2](https://arxiv.org/abs/2604.07460v2), Section 1.2.1, Eq. (1.9) and
Appendix A.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.StateTesting26.MainResults.Protocols

open Qatlib.Papers.StateTesting26.MainResults.Model
open Qatlib.Papers.StateTesting26.MainResults
open Qatlib.Papers.StateTesting26.MainResults

/-! ## The swap operator on the two-copy register -/

/-- `SWAP` is an involution on `(ℂ^d)^{⊗2}`. -/
theorem swapTwo_mul_self (d : ℕ) : swapTwo (d := d) * swapTwo (d := d) = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (fun a : Fin 2 => if a = 0 then i 1 else i 0)]
  · by_cases h : i = j
    · subst h
      simp [swapTwo]
    · have h' : ¬(i 1 = j 1 ∧ i 0 = j 0) := fun hh =>
        h (funext fun a => by fin_cases a <;> simp_all)
      simp [swapTwo, h', h]
  · intro k _ hk
    by_cases hc : i 0 = k 1 ∧ i 1 = k 0
    · exfalso
      apply hk
      funext a
      fin_cases a <;> simp_all
    · simp [swapTwo, hc]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `SWAP` is self-adjoint: it is a real permutation matrix. -/
theorem swapTwo_conjTranspose (d : ℕ) : (swapTwo (d := d))ᴴ = swapTwo (d := d) := by
  classical
  ext i j
  simp only [Matrix.conjTranspose_apply, swapTwo]
  by_cases h : i 0 = j 1 ∧ i 1 = j 0
  · have h' : j 0 = i 1 ∧ j 1 = i 0 := ⟨h.2.symm, h.1.symm⟩
    rw [ite_eq_left h', ite_eq_left h]
    simp
  · have h' : ¬(j 0 = i 1 ∧ j 1 = i 0) := fun hh => h ⟨hh.2.symm, hh.1.symm⟩
    rw [ite_eq_right h', ite_eq_right h]
    simp

/-- `1 + SWAP` is Hermitian. -/
theorem isHermitian_one_add_swapTwo (d : ℕ) :
    ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) + swapTwo (d := d)).IsHermitian :=
  Matrix.isHermitian_one.add (swapTwo_conjTranspose d)

/-- `1 - SWAP` is Hermitian. -/
theorem isHermitian_one_sub_swapTwo (d : ℕ) :
    ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) - swapTwo (d := d)).IsHermitian :=
  Matrix.isHermitian_one.sub (swapTwo_conjTranspose d)

/-- Multiplying a Hermitian matrix by the scalar `1/2` keeps it Hermitian. -/
theorem isHermitian_half_smul {d : ℕ} {A : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ}
    (hA : A.IsHermitian) : ((1 / 2 : ℂ) • A).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hA.eq]
  norm_num

/-- `(1 + SWAP)² = 2(1 + SWAP)`: `(1 + SWAP)/2` is idempotent. -/
theorem one_add_swapTwo_mul_self (d : ℕ) :
    ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) + swapTwo (d := d)) *
        (1 + swapTwo (d := d)) = (2 : ℂ) • (1 + swapTwo (d := d)) := by
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, swapTwo_mul_self]
  rw [two_smul]
  abel

/-- `(1 - SWAP)² = 2(1 - SWAP)`: `(1 - SWAP)/2` is idempotent. -/
theorem one_sub_swapTwo_mul_self (d : ℕ) :
    ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) - swapTwo (d := d)) *
        (1 - swapTwo (d := d)) = (2 : ℂ) • (1 - swapTwo (d := d)) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, swapTwo_mul_self]
  rw [two_smul]
  abel

/-- `½(1 + SWAP)` is positive semidefinite, being the projector onto the symmetric subspace. -/
theorem posSemidef_half_one_add_swapTwo (d : ℕ) :
    ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
      + swapTwo (d := d))).PosSemidef := by
  have hstar : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hsq : ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
        + swapTwo (d := d))) * ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
        + swapTwo (d := d))) = ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
        + swapTwo (d := d))) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, one_add_swapTwo_mul_self, smul_smul, smul_smul]
    congr 1
    norm_num
  have heq : ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
        + swapTwo (d := d)))
      = ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
          + swapTwo (d := d)))ᴴ *
        ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
          + swapTwo (d := d))) := by
    rw [Matrix.conjTranspose_smul, isHermitian_one_add_swapTwo, hstar, hsq]
  rw [heq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- `½(1 - SWAP)` is positive semidefinite, being the projector onto the antisymmetric
subspace. -/
theorem posSemidef_half_one_sub_swapTwo (d : ℕ) :
    ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
      - swapTwo (d := d))).PosSemidef := by
  have hstar : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hsq : ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
        - swapTwo (d := d))) * ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
        - swapTwo (d := d))) = ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
        - swapTwo (d := d))) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, one_sub_swapTwo_mul_self, smul_smul, smul_smul]
    congr 1
    norm_num
  have heq : ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
        - swapTwo (d := d)))
      = ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
          - swapTwo (d := d)))ᴴ *
        ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
          - swapTwo (d := d))) := by
    rw [Matrix.conjTranspose_smul, isHermitian_one_sub_swapTwo, hstar, hsq]
  rw [heq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-! ## The swap-test POVM and scheme -/

/-- The two outcome effects of the swap test: `½(I + SWAP)` on the outcome `true` and
`½(I - SWAP)` on the outcome `false`. -/
def swapEffect (d : ℕ) : Bool → HermitianMat (Fin 2 → Fin d) ℂ
  | true => ⟨(1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
      + swapTwo (d := d)), isHermitian_half_smul (isHermitian_one_add_swapTwo d)⟩
  | false => ⟨(1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
      - swapTwo (d := d)), isHermitian_half_smul (isHermitian_one_sub_swapTwo d)⟩

/-- The swap-test POVM on two copies of a `d`-level state. -/
def swapPovm (d : ℕ) : POVM Bool (Fin 2 → Fin d) where
  mats := swapEffect d
  nonneg := by
    intro b
    cases b
    · exact HermitianMat.zero_le_iff.mpr (posSemidef_half_one_sub_swapTwo d)
    · exact HermitianMat.zero_le_iff.mpr (posSemidef_half_one_add_swapTwo d)
  normalized := by
    rw [Fintype.sum_bool]
    apply HermitianMat.ext
    show ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) + swapTwo (d := d))
        + (1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) - swapTwo (d := d)))
      = (1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply]
    by_cases h : i = j
    · simp only [h]
      ring
    · simp only [h]
      ring

/-- The two-copy swap test as a fixed `2`-copy scheme with a single block, accepting on the
first outcome. -/
def swapScheme (d : ℕ) : FixedTCopyScheme d 2 1 Bool where
  povm := swapPovm d
  accept := fun x => x 0

/-! ## The acceptance probability -/

/-- A sum over the outcome vectors of a one-block scheme has exactly two terms. -/
theorem sum_fin_one_arrow_bool (f : (Fin 1 → Bool) → ℝ) :
    (∑ x : Fin 1 → Bool, f x) = f (fun _ => true) + f (fun _ => false) := by
  rw [← Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool).symm (fun b => f (fun _ => b)) f
    (fun _ => rfl), Fintype.sum_bool]

/-- The two-copy state of the model layer is the matrix product of the two copies. -/
theorem npow_two_m {d : ℕ} (ρ : QState d) :
    (MState.npow ρ 2).m = Matrix.piProd (fun _ : Fin 2 => ρ.m) := rfl

/-- The two-copy state is normalised: `tr(ρ ⊗ ρ) = (tr ρ)² = 1`. -/
theorem trace_npow_two {d : ℕ} (ρ : QState d) : ((MState.npow ρ 2).m).trace = 1 := by
  rw [npow_two_m ρ, Matrix.trace_piProd]
  simp

/-- The SWAP observable on the two-copy state of the model layer has trace `tr(ρ²)`. -/
theorem trace_swapTwo_npow_two {d : ℕ} (ρ : QState d) :
    (swapTwo (d := d) * (MState.npow ρ 2).m).trace = (ρ.m * ρ.m).trace := by
  rw [npow_two_m ρ]
  exact trace_swapTwo_tensorPowerMat_two (d := d) ρ.m

/-- **The swap test in the paper's scheme interface**: the one-block two-copy swap test accepts a
normalised state with probability `½ + ½ tr(ρ²)`. -/
theorem swapScheme_acceptProb {d : ℕ} (ρ : QState d) :
    (swapScheme d).acceptProb ρ = (1 / 2 : ℝ) + (1 / 2 : ℝ) * purityReal ρ := by
  have hround : roundProb (swapPovm d) ρ true
      = (((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
        + swapTwo (d := d))) * (MState.npow ρ 2).m).trace.re := by
    change ((swapEffect d true).mat * (MState.npow ρ 2).m).trace.re = _
    rfl
  have htrace : (((1 / 2 : ℂ) • ((1 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
        + swapTwo (d := d))) * (MState.npow ρ 2).m).trace
      = (1 / 2 : ℂ) * (1 + (ρ.m * ρ.m).trace) := by
    rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_add,
      trace_npow_two ρ, trace_swapTwo_npow_two ρ]
    simp only [smul_eq_mul]
  have hvalue : roundProb (swapPovm d) ρ true
      = (1 / 2 : ℝ) + (1 / 2 : ℝ) * purityReal ρ := by
    rw [hround, htrace, purityReal_eq_re_trace_mul]
    have hc : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hc, Complex.mul_re]
    simp
    ring
  rw [← hvalue]
  rw [FixedTCopyScheme.acceptProb, sum_fin_one_arrow_bool]
  simp [swapScheme]

end Qatlib.Papers.StateTesting26.MainResults.Protocols
