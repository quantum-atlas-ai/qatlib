/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ProjectiveFix.Reset

/-!
# Finite projective continuations and normalization

`zeroRun` applies a finite list of complementary projective outcomes, and `normalize` rescales a
matrix by its real trace. `violatedReset` combines a violated measurement outcome with a local
maximally mixed reset.

For a commuting family, `short_execution` proves that a covering zero-outcome continuation with
positive trace mass yields a positive semidefinite, trace-one matrix in every constraint kernel.
The construction supplies a finite execution segment for the resampling procedure of
[SattathArad2015].

## Main statements

* `zeroRun_satisfies_mem`: each measured commuting projector annihilates the final zero-outcome
  branch.
* `violatedReset_outside`: violated measurement and reset preserve commuting outside
  constraints.
* `short_execution`: positive branch mass gives a normalized common-kernel output.

## References

* [Sattath and Arad, 2015][SattathArad2015]
-/

set_option autoImplicit false
open scoped BigOperators ComplexOrder Matrix Kronecker
namespace Qatlib.Foundations.MatrixAlgebra.ProjectiveFix
noncomputable section
variable {D I : Type*} [Fintype D] [DecidableEq D]

/-- The unnormalized matrix obtained by applying the `false` projective branch successively
along a list of constraints. -/
def zeroRun (P : I → Projector D) (l : List I) (M : Matrix D D ℂ) : Matrix D D ℂ :=
  l.foldl (fun N i => branch (P i) false N) M

/-- A finite sequence of complementary projective branches preserves positive semidefiniteness. -/
theorem zeroRun_pos (P : I → Projector D) (l : List I) {M : Matrix D D ℂ}
    (hM : M.PosSemidef) : (zeroRun P l M).PosSemidef := by
  induction l generalizing M with
  | nil => exact hM
  | cons i l ih => exact ih (branch_pos _ _ hM)

/-- A matrix commuting with every projector in the list retains left annihilation through the
zero-outcome run. -/
theorem zeroRun_preserves (P : I → Projector D) (l : List I) (Q M : Matrix D D ℂ)
    (hc : ∀ i ∈ l, Q * (P i).val = (P i).val * Q) (hM : Q * M = 0) :
    Q * zeroRun P l M = 0 := by
  induction l generalizing M with
  | nil => exact hM
  | cons i l ih =>
    exact ih _ (fun j hj => hc j (List.mem_cons_of_mem i hj))
      (branch_preserves (P i) false Q M (hc i (List.mem_cons_self)) hM)

/-- For a pairwise commuting projector family, every projector occurring in the list annihilates
the final zero-outcome matrix on the left. -/
theorem zeroRun_satisfies_mem (P : I → Projector D)
    (hc : ∀ i j, (P i).val * (P j).val = (P j).val * (P i).val)
    (l : List I) (M : Matrix D D ℂ) (j : I) (hj : j ∈ l) :
    (P j).val * zeroRun P l M = 0 := by
  induction l generalizing M with
  | nil => simp at hj
  | cons i l ih =>
    rcases List.mem_cons.mp hj with rfl | hj
    · exact zeroRun_preserves P l _ _ (fun k _ => hc j k) (branch_zero_satisfies _ M)
    · exact ih _ hj

/-- The matrix `M` scaled by the reciprocal of the real part of its trace. -/
def normalize (M : Matrix D D ℂ) : Matrix D D ℂ := (M.trace.re)⁻¹ • M

omit [DecidableEq D] in

/-- Scaling by the reciprocal real trace preserves positive semidefiniteness for a positive
semidefinite matrix. -/
theorem normalize_pos {M : Matrix D D ℂ} (hM : M.PosSemidef) :
    (normalize M).PosSemidef := by
  exact hM.smul (inv_nonneg.mpr (Complex.nonneg_iff.mp hM.trace_nonneg).1)

omit [DecidableEq D] in

/-- Normalizing a positive semidefinite matrix with positive real trace gives complex trace one. -/
theorem normalize_trace {M : Matrix D D ℂ} (hM : M.PosSemidef) (hp : 0 < M.trace.re) :
    (normalize M).trace = 1 := by
  have him : M.trace.im = 0 := (Complex.nonneg_iff.mp hM.trace_nonneg).2.symm
  apply Complex.ext
  · simp [normalize, hp.ne']
  · simp [normalize, him]

/-- Normalization preserves left annihilation by any matrix. -/
theorem normalize_preserves (Q M : Matrix D D ℂ) (h : Q * M = 0) :
    Q * normalize M = 0 := by simp [normalize, h]

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The violated projective branch followed by local reset of the first register. -/
def violatedReset (P : Projector (A × B)) (M : Matrix (A × B) (A × B) ℂ) :=
  localReset (branch P true M)

/-- A violated measurement followed by local reset preserves positive semidefiniteness. -/
theorem violatedReset_pos (P : Projector (A × B)) {M : Matrix (A × B) (A × B) ℂ}
    (hM : M.PosSemidef) : (violatedReset P M).PosSemidef :=
  localReset_pos (branch_pos P true hM)

/-- When the reset register is nonempty, a violated reset has the same trace as the violated
measurement branch. -/
theorem violatedReset_trace [Nonempty A] (P : Projector (A × B))
    (M : Matrix (A × B) (A × B) ℂ) :
    (violatedReset P M).trace = (branch P true M).trace := localReset_trace _

/-- An outside operator commuting with the measured projector retains left annihilation after
the violated branch and local reset. This is the outside-constraint preservation used in
[SattathArad2015]. -/
theorem violatedReset_outside (P : Projector (A × B)) (Q : Matrix B B ℂ)
    (M : Matrix (A × B) (A × B) ℂ)
    (hc : ((1 : Matrix A A ℂ) ⊗ₖ Q) * P.val = P.val * ((1 : Matrix A A ℂ) ⊗ₖ Q))
    (hM : ((1 : Matrix A A ℂ) ⊗ₖ Q) * M = 0) :
    ((1 : Matrix A A ℂ) ⊗ₖ Q) * violatedReset P M = 0 :=
  localReset_outside_preserves Q _ (branch_preserves P true _ _ hc hM)

/-- For commuting projectors, a violated reset followed by a covering zero-outcome run yields a
positive semidefinite, trace-one common-kernel matrix after normalization, provided the
branch has positive real trace. This describes a finite execution segment of
[SattathArad2015]. -/
theorem short_execution (P : I → Projector (A × B))
    (hc : ∀ i j, (P i).val * (P j).val = (P j).val * (P i).val)
    (i : I) (l : List I) (cover : ∀ j, j ∈ l)
    (M : Matrix (A × B) (A × B) ℂ) (hM : M.PosSemidef)
    (hp : 0 < (zeroRun P l (violatedReset (P i) M)).trace.re) :
    (normalize (zeroRun P l (violatedReset (P i) M))).PosSemidef ∧
    (normalize (zeroRun P l (violatedReset (P i) M))).trace = 1 ∧
    ∀ j, (P j).val * normalize (zeroRun P l (violatedReset (P i) M)) = 0 := by
  have hpos := zeroRun_pos P l (violatedReset_pos (P i) hM)
  exact ⟨normalize_pos hpos, normalize_trace hpos hp,
    fun j => normalize_preserves _ _ (zeroRun_satisfies_mem P hc l _ j (cover j))⟩

end
end Qatlib.Foundations.MatrixAlgebra.ProjectiveFix
