/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SymmetryAdv10.MainResults.BlockAudit
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! # Actual dependent finite-block L2 operator norm

Fixed source1012.2112v1 Theorem26, norm core. All block index types,
including empty types and empty individual blocks, are retained.
The norm throughout is the genuine Euclidean operator norm.
-/

set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.L2Operator BigOperators
namespace Qatlib.Papers.SymmetryAdv10.MainResults.BlockNorm
open BlockAudit

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {m : ι → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- The actual i-th Euclidean component of a sigma-indexed vector. -/
def chunk (x : EuclideanSpace ℂ (Σ i, m i)) (i : ι) : EuclideanSpace ℂ (m i) :=
  WithLp.toLp 2 (fun j => x ⟨i,j⟩)

omit [DecidableEq ι] [∀ i, DecidableEq (m i)] in
/-- The genuine squared norm splits as the sum of component squared norms. -/
theorem normSplit (x : EuclideanSpace ℂ (Σ i, m i)) :
    ‖x‖^2=∑ i, ‖chunk x i‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,chunk,Fintype.sum_sigma]

omit [DecidableEq ι] [∀ i, DecidableEq (m i)] in
/-- Restricting to one component cannot increase the Euclidean norm. -/
theorem chunkBound (x : EuclideanSpace ℂ (Σ i, m i)) (i : ι) :
    ‖chunk x i‖≤‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [normSplit]
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖chunk x j‖) (Finset.mem_univ i)

/-- A zero extension into the actual sigma-indexed Euclidean space. -/
def embed (i : ι) (v : EuclideanSpace ℂ (m i)) : EuclideanSpace ℂ (Σ i, m i) :=
  WithLp.toLp 2 (fun p => (Pi.single i (fun j : m i => v j) : (a : ι) → m a → ℂ) p.1 p.2)

omit [∀ i, DecidableEq (m i)] in
/-- Zero extension is an actual Euclidean isometry. -/
theorem embedNorm (i : ι) (v : EuclideanSpace ℂ (m i)) : ‖embed i v‖=‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,embed,Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [Pi.single_eq_of_ne hbi]
  · simp

omit [Fintype ι] [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] in
/-- Extracting the component after zero extension returns the original vector. -/
theorem chunkEmbed (i : ι) (v : EuclideanSpace ℂ (m i)) : chunk (embed i v) i=v := by
  ext j
  simp [chunk,embed]

/-- Actual block multiplication acts component by component. -/
theorem action (D : ∀ i, Matrix (m i) (m i) ℂ)
    (x : EuclideanSpace ℂ (Σ i, m i)) (i : ι) :
    chunk (Matrix.toEuclideanCLM (n := Σ i, m i) (𝕜 := ℂ) (blockDiagSigma m D) x) i=
      Matrix.toEuclideanCLM (n := m i) (𝕜 := ℂ) (D i) (chunk x i) := by
  ext j
  simp [chunk,Matrix.toEuclideanCLM_toLp,Matrix.ofLp_toEuclideanCLM,
    blockDiagSigma,Matrix.mulVec,dotProduct,Fintype.sum_sigma]

/-- With a nonempty block index, the true operator norm is the maximum block norm. -/
theorem normNonempty [Nonempty ι] (D : ∀ i, Matrix (m i) (m i) ℂ) :
    ‖blockDiagSigma m D‖=sSup (Set.range fun i => ‖D i‖) := by
  classical
  let C:=sSup (Set.range fun i => ‖D i‖)
  have hC : 0≤C := Real.sSup_nonneg (by rintro _ ⟨i,rfl⟩; exact norm_nonneg _)
  have hi : ∀ i, ‖D i‖≤C := fun i => le_csSup (Set.finite_range _).bddAbove ⟨i,rfl⟩
  apply le_antisymm
  · rw [← Matrix.l2_opNorm_toEuclideanCLM]
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    simp only [mul_pow,normSplit,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [action]
    have h: ‖Matrix.toEuclideanCLM (n := m i) (𝕜 := ℂ) (D i) (chunk x i)‖≤C*‖chunk x i‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hi i) (norm_nonneg _))
    nlinarith [norm_nonneg (Matrix.toEuclideanCLM (n := m i) (𝕜 := ℂ) (D i) (chunk x i)),
      mul_nonneg hC (norm_nonneg (chunk x i))]
  · change C≤‖blockDiagSigma m D‖
    apply csSup_le
    · exact Set.range_nonempty _
    · rintro _ ⟨i,rfl⟩
      rw [← Matrix.l2_opNorm_toEuclideanCLM]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro v
      calc
        ‖Matrix.toEuclideanCLM (n := m i) (𝕜 := ℂ) (D i) v‖=
            ‖chunk (Matrix.toEuclideanCLM (n := Σ i, m i) (𝕜 := ℂ) (blockDiagSigma m D) (embed i v)) i‖ := by
          rw [action,chunkEmbed]
        _≤‖Matrix.toEuclideanCLM (n := Σ i, m i) (𝕜 := ℂ) (blockDiagSigma m D) (embed i v)‖ := chunkBound _ _
        _≤‖blockDiagSigma m D‖*‖v‖ := by
          simpa only [embedNorm,Matrix.l2_opNorm_toEuclideanCLM] using
            (Matrix.toEuclideanCLM (n := Σ i, m i) (𝕜 := ℂ) (blockDiagSigma m D)).le_opNorm (embed i v)


/-- Every finite dependent block decomposition has exactly the maximum block norm, including empty indices. -/
theorem wholeOriginal (D : ∀ i, Matrix (m i) (m i) ℂ) :
    ‖blockDiagSigma m D‖=sSup (Set.range fun i => ‖D i‖) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    have hz : blockDiagSigma m D=0 := Subsingleton.elim _ _
    rw [hz,norm_zero,Set.range_eq_empty]
    exact Real.sSup_empty.symm
  | inr h =>
    let := h
    exact normNonempty D

end Qatlib.Papers.SymmetryAdv10.MainResults.BlockNorm
