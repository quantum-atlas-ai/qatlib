/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS23.MainResults.CircuitGates
import Qatlib.Papers.AdiabaticQLS23.MainResults.OraclePrimitives

/-!
# Circuit compression for the supplied QLS oracles

Computes the clean ancilla corners of the circuit built from the oracle and reflection gates in
[CostaEtAl2025]. The identities for `corner` reduce the full circuit to the interpolating
Hamiltonian multiplied by `sourcePrefactor`.

Given unitary matrix and state-preparation oracles, `supplied_oracle_encoding` packages the
reindexed circuit as a projected unitary encoding of the scaled Hamiltonian.

## Main statements

* `fullCircuit_two_corners`: Computes the corner after fixing the two outer ancillas.
* `oracleCircuit_corner`: Identifies the clean corner with the scaled Hamiltonian.
* `supplied_oracle_encoding`: Constructs the projected unitary encoding from the supplied
  oracles.

## References

* [Costa et al., 2025][CostaEtAl2025]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Qatlib.Papers.AdiabaticQLS23.MainResults.SourceCircuit
open Matrix
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The matrix corner obtained by fixing the outer `Fin 2` row and column indices to zero. -/
def corner (M : Matrix (Fin 2 × K) (Fin 2 × K) ℂ) : Matrix K K ℂ :=
  fun x y => M (0,x) (0,y)

/-- Computes the zero-ancilla corner of the Hadamard and controlled-`T` word as `c ^ 2 • (M + T
* M * T)`. -/
theorem corner_hadamard_word (T M : Matrix K K ℂ) (c : ℝ) :
    corner (hadamardGate c * block2 1 0 0 T * block2 M 0 0 M *
      block2 1 0 0 T * hadamardGate c) = c^2 • (M + T*M*T) := by
  unfold hadamardGate
  simp only [block2_mul,mul_zero,add_zero,zero_add,one_mul,mul_one,
    smul_mul_assoc,mul_smul_comm,smul_smul]
  ext x y
  simp [corner,block2]
  ring

/-- The zero-ancilla corner of `middle U u v c` has zero diagonal blocks and off-diagonal blocks
`c*u` times the identity plus `c*v` times `U` or its conjugate transpose. -/
theorem middle_corner (U : Matrix K K ℂ) (u v c : ℝ) :
    corner (middle U u v c) =
      block2 0 ((c*u) • (1 : Matrix K K ℂ) + (c*v) • U)
        ((c*u) • (1 : Matrix K K ℂ) + (c*v) • Uᴴ) 0 := by
  unfold middle rotationGate selectGate diagonal xGate oracleFlip
  simp only [block2_mul,mul_zero,add_zero,zero_add,one_mul,mul_one,
    smul_mul_assoc,mul_smul_comm,smul_smul]
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;> simp [corner,block2]
  all_goals ring

omit [DecidableEq K] in

/-- Reconstructs a matrix indexed by `Fin 2 × K` from its four block restrictions. -/
theorem block_eta (M : Matrix (Fin 2 × K) (Fin 2 × K) ℂ) :
    block2 (fun x y => M (0,x) (0,y)) (fun x y => M (0,x) (1,y))
      (fun x y => M (1,x) (0,y)) (fun x y => M (1,x) (1,y)) = M := by
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;> rfl

/-- Taking the zero-ancilla corner of multiplication on both sides by `block2 T 0 0 T` gives `T
* corner M * T`. -/
theorem corner_diagonal_conjugate (T : Matrix K K ℂ)
    (M : Matrix (Fin 2 × K) (Fin 2 × K) ℂ) :
    corner (block2 T 0 0 T * M * block2 T 0 0 T) = T * corner M * T := by
  conv_lhs => rw [← block_eta M]
  ext x y
  simp [block2_mul,corner,block2]
  rfl

omit [Fintype K] [DecidableEq K] in

/-- Taking the zero-ancilla corner commutes with matrix addition. -/
theorem corner_add (M N : Matrix (Fin 2 × K) (Fin 2 × K) ℂ) :
    corner (M+N) = corner M + corner N := rfl

omit [Fintype K] [DecidableEq K] in

/-- Taking the zero-ancilla corner commutes with real scalar multiplication. -/
theorem corner_smul (a : ℝ) (M : Matrix (Fin 2 × K) (Fin 2 × K) ℂ) :
    corner (a • M) = a • corner M := rfl

/-- The average `(1 / 2) • (1 + R)`, which is a projection when `R` is a Hermitian involution. -/
def projectorOfReflection (R : Matrix K K ℂ) : Matrix K K ℂ :=
  (1/2:ℝ) • (1+R)

/-- Under `2 * c ^ 2 = 1`, computes two successive zero-ancilla corners of the full circuit
using the weighted oracle blocks and `projectorOfReflection R`. See [CostaEtAl2025]. -/
theorem fullCircuit_two_corners (U R : Matrix K K ℂ) (u v c : ℝ)
    (hc : 2*c^2=1) :
    corner (corner (fullCircuit U R u v c)) =
      block2 0 (((c*u) • (1 : Matrix K K ℂ) + (c*v) • U) * projectorOfReflection R)
        (projectorOfReflection R * ((c*u) • (1 : Matrix K K ℂ) + (c*v) • Uᴴ)) 0 := by
  have hc2 : c^2=(1/2:ℝ) := by linarith
  unfold fullCircuit reflectGate
  rw [corner_hadamard_word, corner_smul, corner_add]
  unfold qControl
  rw [corner_diagonal_conjugate, middle_corner, hc2]
  simp only [block2_mul,mul_zero,zero_mul,one_mul,mul_one,zero_add,add_zero]
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;>
    simp [block2,projectorOfReflection,Matrix.add_mul,Matrix.mul_add,
      smul_smul]
    <;> ring

/-- The ancilla lift of a matrix `R`, given by the Kronecker product of the ancilla identity
with `R`. -/
def liftAnc {A N : Type} [Fintype A] [DecidableEq A] [Fintype N] [DecidableEq N]
    (R : Matrix N N ℂ) : Matrix (A × N) (A × N) ℂ := Matrix.kronecker 1 R

/-- Taking the average of the identity and a matrix commutes with lifting that matrix to an
ancilla register. -/
theorem projector_lift {A N : Type} [Fintype A] [DecidableEq A]
    [Fintype N] [DecidableEq N] (R : Matrix N N ℂ) :
    projectorOfReflection (liftAnc (A:=A) R) = liftAnc (A:=A) (projectorOfReflection R) := by
  ext ⟨a,x⟩ ⟨b,y⟩
  by_cases hab : a=b
  · subst b
    simp [projectorOfReflection,liftAnc,Matrix.one_apply]
  · simp [projectorOfReflection,liftAnc,Matrix.one_apply,hab]

/-- The fixed-ancilla corner of `U * liftAnc Q` equals the corresponding corner of `U`
multiplied on the right by `Q`. -/
theorem ancilla_corner_right {A N : Type} [Fintype A] [DecidableEq A]
    [Fintype N] [DecidableEq N] (a0 : A) (U : Matrix (A × N) (A × N) ℂ)
    (Q : Matrix N N ℂ) (x y : N) :
    (U * liftAnc (A:=A) Q) (a0,x) (a0,y) =
      (Matrix.of (fun i j => U (a0,i) (a0,j)) * Q) x y := by
  simp [Matrix.mul_apply,Fintype.sum_prod_type,liftAnc,
    Matrix.one_apply]

/-- The fixed-ancilla corner of `liftAnc Q * U` equals `Q` multiplied on the left of the
corresponding corner of `U`. -/
theorem ancilla_corner_left {A N : Type} [Fintype A] [DecidableEq A]
    [Fintype N] [DecidableEq N] (a0 : A) (U : Matrix (A × N) (A × N) ℂ)
    (Q : Matrix N N ℂ) (x y : N) :
    (liftAnc (A:=A) Q * U) (a0,x) (a0,y) =
      (Q * Matrix.of (fun i j => U (a0,i) (a0,j))) x y := by
  simp [Matrix.mul_apply,Fintype.sum_prod_type,liftAnc,
    Matrix.one_apply]

/-- The coefficient normalization `rotNorm f` is strictly positive for every real `f`. -/
theorem rotNorm_pos (f : ℝ) : 0 < rotNorm f := by
  unfold rotNorm
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg (f-1/2)]

/-- The normalized interpolation coefficient `(1 - f) / rotNorm f`. -/
def sourceU (f : ℝ) : ℝ := (1-f)/rotNorm f

/-- The normalized interpolation coefficient `f / rotNorm f`. -/
def sourceV (f : ℝ) : ℝ := f/rotNorm f

/-- The Hadamard coefficient `1 / Real.sqrt 2`. -/
def sourceC : ℝ := 1/Real.sqrt 2

/-- The source coefficients satisfy `(sourceU f) ^ 2 + (sourceV f) ^ 2 = 1` and `2 * sourceC ^ 2
= 1`. -/
theorem source_coefficients (f : ℝ) :
    (sourceU f)^2+(sourceV f)^2=1 ∧ 2*sourceC^2=1 := by
  have hn : (rotNorm f)^2=(1-f)^2+f^2 := Real.sq_sqrt (by positivity)
  have hn0 : rotNorm f ≠ 0 := ne_of_gt (rotNorm_pos f)
  constructor
  · unfold sourceU sourceV
    rw [div_pow,div_pow,← add_div,← hn]
    exact div_self (pow_ne_zero 2 hn0)
  · norm_num [sourceC,div_pow,Real.sq_sqrt]

/-- For a unitary state-preparation matrix, the average associated with `sourceReflection`
equals the complement projection of the prepared seed state. -/
theorem projector_prepared {N : Type} [Fintype N] [DecidableEq N]
    (Ub : Matrix N N ℂ) (seed : N) (hUb : Ub ∈ Matrix.unitaryGroup N ℂ) :
    projectorOfReflection (sourceReflection Ub seed) =
      Qb (Ub *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) := by
  rw [sourceReflection_eq_rankOne Ub seed hUb]
  ext x y
  simp [projectorOfReflection,Qb]
  ring

/-- Lifting a unitary matrix by the ancilla identity preserves unitarity. -/
theorem liftAnc_unitary {A N : Type} [Fintype A] [DecidableEq A]
    [Fintype N] [DecidableEq N] (R : Matrix N N ℂ)
    (hR : R ∈ Matrix.unitaryGroup N ℂ) :
    liftAnc (A:=A) R ∈ Matrix.unitaryGroup (A × N) ℂ := by
  exact Matrix.kronecker_mem_unitary
    (U₁:=(1 : Matrix A A ℂ)) (U₂:=R) (Submonoid.one_mem _) hR

/-- If the `a0` corner of `U` is the Hermitian matrix `A0`, the clean corner of the full circuit
has weighted `A0` blocks multiplied by `projectorOfReflection R` on the indicated sides. -/
theorem fullCircuit_clean_corner {Anc N : Type} [Fintype Anc] [DecidableEq Anc]
    [Fintype N] [DecidableEq N] (a0 : Anc)
    (U : Matrix (Anc × N) (Anc × N) ℂ) (R A0 : Matrix N N ℂ)
    (henc : ∀ i j, U (a0,i) (a0,j) = A0 i j) (hA : A0ᴴ=A0)
    (u v c : ℝ) (hc : 2*c^2=1) (h k : Fin 2) (x y : N) :
    fullCircuit U (liftAnc (A:=Anc) R) u v c
      (0,(0,(h,(a0,x)))) (0,(0,(k,(a0,y)))) =
      (block2 0 (((c*u) • (1 : Matrix N N ℂ) + (c*v) • A0) * projectorOfReflection R)
        (projectorOfReflection R * ((c*u) • (1 : Matrix N N ℂ) + (c*v) • A0)) 0)
          (h,x) (k,y) := by
  have hstar : ∀ i j, Uᴴ (a0,i) (a0,j) = A0 i j := by
    intro i j
    have he := congrArg (fun M : Matrix N N ℂ => M i j) hA
    simpa [Matrix.conjTranspose_apply,henc] using he
  let P : Matrix (Anc × N) (Anc × N) ℂ := (c*u) • 1 + (c*v) • U
  let P' : Matrix (Anc × N) (Anc × N) ℂ := (c*u) • 1 + (c*v) • Uᴴ
  have hp : Matrix.of (fun i j => P (a0,i) (a0,j)) =
      (c*u) • (1 : Matrix N N ℂ) + (c*v) • A0 := by
    ext i j
    simp [P,Matrix.one_apply,henc]
  have hp' : Matrix.of (fun i j => P' (a0,i) (a0,j)) =
      (c*u) • (1 : Matrix N N ℂ) + (c*v) • A0 := by
    ext i j
    have hs : (starRingEnd ℂ) (U (a0,j) (a0,i)) = A0 i j := by
      simpa only [Matrix.conjTranspose_apply] using! hstar i j
    simp [P',Matrix.one_apply,hs]
  have he := congrArg (fun M : Matrix (Fin 2 × (Anc × N)) _ ℂ =>
    M (h,(a0,x)) (k,(a0,y))) (fullCircuit_two_corners U (liftAnc (A:=Anc) R) u v c hc)
  rw [projector_lift] at he
  have ht := ancilla_corner_right a0 P (projectorOfReflection R) x y
  have hb := ancilla_corner_left a0 P' (projectorOfReflection R) x y
  rw [hp] at ht
  rw [hp'] at hb
  change fullCircuit U (liftAnc (A:=Anc) R) u v c _ _ = _ at he
  rw [he]
  fin_cases h <;> fin_cases k <;> simp [block2] <;> assumption

/-- The source circuit assembled from the matrix oracle, the lifted prepared-state reflection,
and the normalized interpolation coefficients. -/
def oracleCircuit {Anc N : Type} [Fintype Anc] [DecidableEq Anc]
    [Fintype N] [DecidableEq N]
    (UA : Matrix (Anc × N) (Anc × N) ℂ) (Ub : Matrix N N ℂ) (seed : N) (f : ℝ) :
    Matrix (Fin 2 × (Fin 2 × (Fin 2 × (Anc × N))))
      (Fin 2 × (Fin 2 × (Fin 2 × (Anc × N)))) ℂ :=
  fullCircuit UA (liftAnc (A:=Anc) (sourceReflection Ub seed))
    (sourceU f) (sourceV f) sourceC

/-- The assembled oracle circuit is unitary when both supplied oracles are unitary. See
[CostaEtAl2025]. -/
theorem oracleCircuit_unitary {Anc N : Type} [Fintype Anc] [DecidableEq Anc]
    [Fintype N] [DecidableEq N]
    (UA : Matrix (Anc × N) (Anc × N) ℂ) (Ub : Matrix N N ℂ) (seed : N) (f : ℝ)
    (hUA : UA ∈ Matrix.unitaryGroup _ ℂ) (hUb : Ub ∈ Matrix.unitaryGroup _ ℂ) :
    oracleCircuit UA Ub seed f ∈ Matrix.unitaryGroup _ ℂ :=
  fullCircuit_unitary UA _ hUA (liftAnc_unitary _ (sourceReflection_unitary Ub seed hUb))
    (sourceU f) (sourceV f) sourceC (source_coefficients f).1 (source_coefficients f).2

/-- The Hamiltonian scaling factor `1 / (Real.sqrt 2 * rotNorm f)`. -/
def sourcePrefactor (f : ℝ) : ℝ := 1/(Real.sqrt 2*rotNorm f)

omit [Fintype K] in

/-- The source-weighted combination of the identity and `A0` equals `sourcePrefactor f •
selectBlock f A0`. -/
theorem source_weighted (f : ℝ) (A0 : Matrix K K ℂ) :
    (sourceC*sourceU f) • (1 : Matrix K K ℂ) + (sourceC*sourceV f) • A0 =
      sourcePrefactor f • selectBlock f A0 := by
  have hu : sourceC*sourceU f = sourcePrefactor f*(1-f) := by
    simp [sourceC,sourceU,sourcePrefactor,div_eq_mul_inv,_root_.mul_inv_rev,
      mul_comm,mul_left_comm]
  have hv : sourceC*sourceV f = sourcePrefactor f*f := by
    simp [sourceC,sourceV,sourcePrefactor,div_eq_mul_inv,_root_.mul_inv_rev,
      mul_comm,mul_left_comm]
  rw [hu,hv]
  simp only [selectBlock,smul_add,smul_smul]

/-- The off-diagonal blocks formed from the scaled selected matrix and `Q` assemble to
`sourcePrefactor f • H f A0 Q`. -/
theorem scaled_selected_block (f : ℝ) (A0 Q : Matrix K K ℂ) :
    block2 0 ((sourcePrefactor f • selectBlock f A0)*Q)
      (Q*(sourcePrefactor f • selectBlock f A0)) 0 =
        sourcePrefactor f • H f A0 Q := by
  rw [smul_mul_assoc,mul_smul_comm,← encodedCore_eq_H f A0 Q]
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;> simp [encodedCore,block2]

/-- For a unitary preparation oracle and a Hermitian encoded matrix `A0`, the clean circuit
entries equal those of the scaled Hamiltonian with complement projection onto the
prepared-state orthogonal subspace. See [CostaEtAl2025]. -/
theorem oracleCircuit_corner {Anc N : Type} [Fintype Anc] [DecidableEq Anc]
    [Fintype N] [DecidableEq N] (a0 : Anc) (seed : N)
    (UA : Matrix (Anc × N) (Anc × N) ℂ) (Ub A0 : Matrix N N ℂ)
    (hUb : Ub ∈ Matrix.unitaryGroup N ℂ)
    (henc : ∀ i j, UA (a0,i) (a0,j)=A0 i j) (hA : A0ᴴ=A0)
    (f : ℝ) (h k : Fin 2) (x y : N) :
    oracleCircuit UA Ub seed f (0,(0,(h,(a0,x)))) (0,(0,(k,(a0,y)))) =
      (sourcePrefactor f • H f A0
        (Qb (Ub *ᵥ Qatlib.Foundations.PureStateMath.Ket seed))) (h,x) (k,y) := by
  have he := fullCircuit_clean_corner a0 UA (sourceReflection Ub seed) A0 henc hA
    (sourceU f) (sourceV f) sourceC (source_coefficients f).2 h k x y
  simp only [projector_prepared Ub seed hUb,source_weighted] at he
  rw [scaled_selected_block] at he
  exact he

open Qatlib.Concepts.Execution.WorkspaceCP

/-- Unitary supplied oracles whose clean corner encodes a Hermitian `A0` yield a projected
unitary encoding of the scaled interpolating Hamiltonian after reindexing the circuit. See
[CostaEtAl2025]. -/
theorem supplied_oracle_encoding {Anc N : Type} [Fintype Anc] [DecidableEq Anc]
    [Fintype N] [DecidableEq N] (a0 : Anc) (seed : N)
    (UA : Matrix (Anc × N) (Anc × N) ℂ) (Ub A0 : Matrix N N ℂ)
    (hUA : UA ∈ Matrix.unitaryGroup _ ℂ) (hUb : Ub ∈ Matrix.unitaryGroup _ ℂ)
    (henc : ∀ i j, UA (a0,i) (a0,j)=A0 i j) (hA : A0ᴴ=A0) (f : ℝ) :
    ProjectedUnitaryEncoding
      (sourcePrefactor f • H f A0
        (Qb (Ub *ᵥ Qatlib.Foundations.PureStateMath.Ket seed)))
      (Matrix.reindex layout layout (oracleCircuit UA Ub seed f))
      (cleanFrame (0,(0,a0))) (cleanFrame (0,(0,a0))) := by
  apply encoding_of_raw_corner
  · exact oracleCircuit_unitary UA Ub seed f hUA hUb
  · exact oracleCircuit_corner a0 seed UA Ub A0 hUb henc hA f

/-- For `f ∈ [0, 1]`, `sourcePrefactor f` lies between `1 / Real.sqrt 2` and one. See
[CostaEtAl2025]. -/
theorem sourcePrefactor_bounds {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    1/Real.sqrt 2 ≤ sourcePrefactor f ∧ sourcePrefactor f ≤ 1 :=
  prefactor_bounds h0 h1

/-- Factors the oracle flip as a controlled conjugate-transpose oracle, an `xGate`, and a
controlled oracle. See [CostaEtAl2025]. -/
theorem oracleFlip_controlled_word (U : Matrix K K ℂ) :
    oracleFlip U = block2 1 0 0 Uᴴ * xGate * block2 1 0 0 U := by
  simp [oracleFlip,xGate,block2_mul]

end
end Qatlib.Papers.AdiabaticQLS23.MainResults.SourceCircuit
