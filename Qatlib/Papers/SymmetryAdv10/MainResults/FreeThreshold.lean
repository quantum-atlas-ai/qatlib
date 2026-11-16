/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SymmetryAdv10.MainResults.SourceModel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! # The old hybrid objective has an unconstrained spectral threshold

Fixed source1012.2112v1 Definition15 requires the bad spectral projector of
the same adversary and threshold. The historical functional permits an
independent zero matrix and arbitrary negative thresholds. With any actual
positive-denominator additive adversary, its objective set is unbounded;
the conditionally complete real supremum then returns zero, not infinity.
-/

set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder
namespace Qatlib.Papers.SymmetryAdv10.MainResults.FreeThreshold
open Qatlib.Papers.SymmetryAdv10.MainResults

/-- The identity is an actual admissible noncoherent junk matrix. -/
theorem junkOne (P : Problem) : P.IsNoncoherentJunk 1 :=
  ⟨Matrix.PosSemidef.one,by intro f; simp⟩

/-- The zero matrix has actual junk overlap zero, without a target-normalization assumption. -/
theorem zeroOverlap (P : Problem) : P.badOverlap 0=0 := by
  have hs : {v : ℝ | ∃ M : Matrix P.F P.F ℂ,
      P.IsNoncoherentJunk M ∧ v=((0 : Matrix P.F P.F ℂ)*Matrix.hadamard P.rhoDot M).trace.re}=
      {0} := by
    ext v
    constructor
    · rintro ⟨M,_,rfl⟩
      simp
    · intro hv
      exact ⟨1,junkOne P,by simpa using Set.mem_singleton_iff.mp hv⟩
  rw [Problem.badOverlap,hs,csSup_singleton]

/-- An arbitrary positive objective value is attainable by the unlinked old threshold. -/
theorem attain (P : Problem) (Γ : Matrix P.F P.F ℂ)
    (hd : 0<P.maxGammaDiff Γ) (eps t : ℝ) (heps : eps<1) (ht : 0<t) :
    ∃ lam : ℝ, lam<1 ∧
      Problem.hybridK lam eps (P.badOverlap 0)/P.maxGammaDiff Γ=t := by
  refine ⟨1-t*P.maxGammaDiff Γ/(1-eps),?_,?_⟩
  · have hpos : 0<t*P.maxGammaDiff Γ/(1-eps) :=
      div_pos (mul_pos ht hd) (by linarith)
    linarith
  · rw [zeroOverlap]
    simp only [Problem.hybridK,Real.sqrt_zero,sub_zero,Real.sq_sqrt (by linarith : 0≤1-eps)]
    field_simp; ring

/-- The actual old feasible objective set is unbounded, conditional on a real positive-denominator witness. -/
theorem unbounded (P : Problem) (Γ : Matrix P.F P.F ℂ)
    (hΓ : P.IsAdditiveAdversary Γ) (hd : 0<P.maxGammaDiff Γ)
    (eps : ℝ) (heps : eps<1) :
    ¬ BddAbove {v : ℝ | ∃ (A B : Matrix P.F P.F ℂ) (lam : ℝ),
      P.IsAdditiveAdversary A ∧ lam<1 ∧
      v=Problem.hybridK lam eps (P.badOverlap B)/P.maxGammaDiff A} := by
  rintro ⟨b,hb⟩
  obtain ⟨lam,hlam,hv⟩:=attain P Γ hd eps (max b 0+1) heps (by positivity)
  have hle:=hb (show max b 0+1∈{v : ℝ | ∃ (A B : Matrix P.F P.F ℂ) (lam : ℝ),
      P.IsAdditiveAdversary A ∧ lam<1 ∧
      v=Problem.hybridK lam eps (P.badOverlap B)/P.maxGammaDiff A}
    from ⟨Γ,0,lam,hΓ,hlam,hv.symm⟩)
  have hmax : b≤max b 0 := le_max_left _ _
  linarith

/-- Real totalized supremum collapses the unbounded historical functional to zero. -/
theorem boundCollapse (P : Problem) (Γ : Matrix P.F P.F ℂ)
    (hΓ : P.IsAdditiveAdversary Γ) (hd : 0<P.maxGammaDiff Γ)
    (eps : ℝ) (heps : eps<1) : P.advHat eps=0 := by
  exact Real.sSup_of_not_bddAbove (unbounded P Γ hΓ hd eps heps)

end Qatlib.Papers.SymmetryAdv10.MainResults.FreeThreshold
