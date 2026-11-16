/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CommGibbsSamp14.MainResults.Support
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-! Machine counterexamples to the exact legacy contracts.
The unrestricted record fields do not describe actual Gibbs operators. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace Qatlib.Papers.CommGibbsSamp14.MainResults.ExtraProbes
open Qatlib.Papers.CommGibbsSamp14.MainResults.Framework

section BoundarySup
local instance : RegionOps Bool where
  full := false
  union _ _ := false
  inter _ _ := false
  boundary _ := false
  subset _ _ := True
  overlap _ _ := True
  gapDist _ _ := 0
  complementDist _ _ := 0

def splitE (r : Bool) (f : ℝ) : ℝ := if r then f else 0

def supSetup : PaperSetup ℝ Bool where
  expect _ := 0
  one := 0
  Eρ := splitE
  EL := splitE
  LD _ _ := 0
  LH _ _ := 0
  supportDist _ _ := 0
  nbrhd _ := false
  supportedIn _ _ := False
  actsIdentityOn _ _ := False
  sites := 1

/-- The unrestricted union map disconnects the two individual expectations from their union. -/
theorem splitRatio (f : ℝ) :
    covRatio splitE true true f = if f = 0 then 0 else 1 := by
  have he : covRatio splitE true true f = ‖f‖ ^ 2 / ‖f‖ ^ 2 := by
    simp [covRatio, splitE, condCov]
  rw [he]
  by_cases hf : f = 0
  · simp [hf]
  · simp [hf]

/-- The actual quotient set consists of zero and one. -/
theorem splitRatioSet :
    {q : ℝ | ∃ f : ℝ, q = covRatio splitE true true f} = {0, 1} := by
  ext q
  constructor
  · rintro ⟨f, rfl⟩
    by_cases hf : f = 0 <;> simp [splitRatio, hf]
  · intro hq
    rcases (show q = 0 ∨ q = 1 by simpa using hq) with rfl | rfl
    · exact ⟨0, by simp [splitRatio]⟩
    · exact ⟨1, by norm_num [splitRatio]⟩

/-- Every original premise of Proposition 16 holds, while its two suprema differ. -/
theorem prop16Refute :
    (splitE = supSetup.Eρ ∨ splitE = supSetup.EL) ∧
      RegionOps.overlap true true ∧
      (∀ f : ℝ, supSetup.supportedIn
          (RegionOps.boundary (RegionOps.union true true)) f →
        (0 : ℝ) = ‖f‖ ^ 2) ∧
      ¬ (sSup {q : ℝ | ∃ f : ℝ, q = covRatio splitE true true f} =
        sSup {q : ℝ | ∃ f : ℝ,
          supSetup.supportedIn (RegionOps.boundary (RegionOps.union true true)) f ∧
          q = covRatioBoundary splitE true true (fun _ => 0) f}) := by
  refine ⟨Or.inl rfl, trivial, ?_, ?_⟩
  · intro f hf
    exact hf.elim
  · rw [splitRatioSet]
    simp [supSetup, Real.sSup_empty]
end BoundarySup

section BoundaryGap
local instance : RegionOps Unit where
  full := ()
  union _ _ := ()
  inter _ _ := ()
  boundary _ := ()
  subset _ _ := True
  overlap _ _ := True
  gapDist _ _ := 0
  complementDist _ _ := 0

def raySetup : PaperSetup ℝ Unit :=
  { Diagnostics.badSetup with LD := fun _ f => -f }

/-- Positive-variance Rayleigh quotients of minus identity are exactly one. -/
theorem rayRatio (f : ℝ) (hf : 0 < condVar (raySetup.EL ()) f) :
    ⟪f, -(raySetup.LD () f)⟫_ℝ / condVar (raySetup.EL ()) f = 1 := by
  have hv : condVar (raySetup.EL ()) f = ‖f‖ ^ 2 := by
    simp [raySetup, Diagnostics.badSetup, condVar_eq_norm_sq]
  have hn : ‖f‖ ^ 2 ≠ 0 := ne_of_gt (hv ▸ hf)
  change ⟪f, -(-f)⟫_ℝ / condVar (raySetup.EL ()) f = 1
  rw [neg_neg, real_inner_self_eq_norm_sq, hv]
  exact div_self hn

/-- The conditional-gap set is the singleton one, with witness f=1. -/
theorem raySet :
    {q : ℝ | ∃ f : ℝ, 0 < condVar (raySetup.EL ()) f ∧
      q = ⟪f, -(raySetup.LD () f)⟫_ℝ / condVar (raySetup.EL ()) f} = {1} := by
  ext q
  constructor
  · rintro ⟨f, hf, hq⟩
    simpa only [Set.mem_singleton_iff] using hq.trans (rayRatio f hf)
  · intro hq
    have hq1 : q = 1 := by simpa using hq
    subst q
    refine ⟨1, ?_, ?_⟩
    · norm_num [raySetup, Diagnostics.badSetup, condVar_eq_norm_sq]
    · norm_num [raySetup, Diagnostics.badSetup, condVar_eq_norm_sq]

/-- All premises of Lemma 22 are satisfied but the boundary restriction deletes every witness. -/
theorem lemma22Refute :
    (∀ f : ℝ, raySetup.supportedIn (RegionOps.boundary ()) f →
      (0 : ℝ) = condVar (raySetup.EL ()) f) ∧
      ¬ (conditionalGap (raySetup.LD ()) (raySetup.EL ()) =
        sInf {q : ℝ | ∃ f : ℝ,
          raySetup.supportedIn (RegionOps.boundary ()) f ∧ 0 < (0 : ℝ) ∧
          q = ⟪f, -(raySetup.LD () f)⟫_ℝ / (0 : ℝ)}) := by
  refine ⟨?_, ?_⟩
  · intro f hf
    exact hf.elim
  · unfold conditionalGap
    rw [raySet]
    simp [raySetup, Diagnostics.badSetup, Real.sInf_empty]
end BoundaryGap

section ProjectorConsistency
local instance : CPMapData ℝ := ⟨fun _ => True⟩
local instance : RegionOps Unit where
  full := ()
  union _ _ := ()
  inter _ _ := ()
  boundary _ := ()
  subset _ _ := True
  overlap _ _ := True
  gapDist _ _ := 0
  complementDist _ _ := 0

def scalarSetup : PaperSetup ℝ Unit :=
  { raySetup with expect := fun f => f + 1, one := 0 }

def decayFlow (t f : ℝ) : ℝ := Real.exp (-t) * f

/-- The literal limit package is satisfied by an actual smooth exponential semigroup. -/
theorem scalarProj (A : Unit) :
    IsLiouvillianProjector scalarSetup.one (scalarSetup.LD A) (scalarSetup.EL A) := by
  refine ⟨decayFlow, ?_, ?_, fun _ => trivial, ?_, ?_, ?_, trivial, ?_⟩
  · intro f
    simp [decayFlow]
  · intro s t f
    simp [decayFlow, Real.exp_add, mul_assoc, mul_left_comm]
  · intro t
    simp [scalarSetup, decayFlow]
  · intro f
    simpa [decayFlow, scalarSetup, raySetup, Diagnostics.badSetup] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.mul_const f)
  · intro f
    simpa [decayFlow, scalarSetup, raySetup, Diagnostics.badSetup] using
      (((hasDerivAt_id (0 : ℝ)).neg.exp).mul_const f)
  · rfl

/-- All premises of old Proposition 9 hold; its consistency conclusion fails at f=1. -/
theorem prop9Refute :
    FrustrationFree scalarSetup.expect scalarSetup.LD ∧
      LocallyReversible scalarSetup.LD ∧
      (∀ A : Unit, IsLiouvillianProjector scalarSetup.one (scalarSetup.LD A) (scalarSetup.EL A)) ∧
      ¬ (∀ A : Unit, IsConditionalExpectation scalarSetup.expect scalarSetup.one (scalarSetup.EL A)) := by
  refine ⟨?_, ?_, scalarProj, ?_⟩
  · intro h A g
    exact h g
  · intro A f g
    simp [scalarSetup, raySetup]
  · intro h
    have hx := (h ()).consistent 1
    norm_num [scalarSetup, raySetup, Diagnostics.badSetup] at hx
end ProjectorConsistency

section FalseClustering
local instance : CPMapData ℝ := ⟨fun _ => True⟩
local instance : RegionOps ℝ where
  full := 0
  union _ _ := 0
  inter _ _ := 0
  boundary _ := 0
  subset _ _ := True
  overlap _ _ := True
  gapDist A _ := A
  complementDist _ _ := 0

def distE (A f : ℝ) : ℝ := if A = 0 then 0 else f

def distSetup : PaperSetup ℝ ℝ where
  expect _ := 0
  one := 0
  Eρ := distE
  EL := distE
  LD _ f := -f
  LH _ f := -f
  supportDist _ _ := 0
  nbrhd _ := 0
  supportedIn _ _ := False
  actsIdentityOn _ _ := False
  sites := 1

def distPotential : IsRLocalCommutingPotential ℝ ℝ where
  term _ := 0
  range := 0
  bound := 1
  bound_pos := by norm_num
  commutes := True

/-- The zero map is a projective expectation for the degenerate literal unit and state. -/
theorem zeroCE :
    IsProjectiveConditionalExpectation (fun _ : ℝ => 0) 0 (fun _ : ℝ => 0) := by
  refine ⟨⟨trivial, rfl, fun _ => rfl, ?_, ?_⟩, fun _ => rfl⟩
  · intro f g
    simp
  · intro f n
    cases n with
    | zero => simpa using (real_inner_self_nonneg (x := f))
    | succ n => simp [Function.iterate_succ_apply']

/-- The identity map is also projective for the same degenerate literal unit and state. -/
theorem idCE :
    IsProjectiveConditionalExpectation (fun _ : ℝ => 0) 0 (id : ℝ → ℝ) := by
  refine ⟨⟨trivial, rfl, fun _ => rfl, fun _ _ => rfl, ?_⟩, fun _ => rfl⟩
  intro f n
  simp [Function.iterate_id]

/-- Every member of the nonnested family satisfies all projective-expectation predicates. -/
theorem distProjective (A : ℝ) :
    IsProjectiveConditionalExpectation distSetup.expect distSetup.one (distE A) := by
  change IsProjectiveConditionalExpectation (fun _ : ℝ => 0) 0 (distE A)
  by_cases hA : A = 0
  · have he : distE A = (fun _ : ℝ => 0) := by
      funext f
      simp [distE, hA]
    rw [he]
    exact zeroCE
  · have he : distE A = (id : ℝ → ℝ) := by
      funext f
      simp [distE, hA]
    rw [he]
    exact idCE

/-- The independent minus-identity generators give a genuine positive local gap everywhere. -/
theorem distGap (A : ℝ) : ∃ lam : ℝ, IsSpectralGap (distSetup.LD A) (distE A) lam := by
  refine ⟨1, by norm_num, ?_⟩
  intro f
  by_cases hA : A = 0
  · simp [distSetup, distE, hA, condVar_eq_norm_sq]
  · simpa [distSetup, distE, hA, condVar_eq_norm_sq, real_inner_self_eq_norm_sq] using
      (sq_nonneg ‖f‖)

/-- Arbitrary distances and union operations invalidate the claimed strong-clustering conclusion. -/
theorem distNoStrong : ¬ ∃ c ξ : ℝ, StrongClustering distE c ξ := by
  rintro ⟨c, ξ, hc, hξ, h⟩
  let r : ℝ := ξ * Real.log (c + 1)
  have hcp : 0 < c + 1 := by linarith
  have hr : 0 < r := mul_pos hξ (Real.log_pos (by linarith))
  have hrn : r ≠ 0 := ne_of_gt hr
  have he : Real.exp (-r / ξ) = (c + 1)⁻¹ := by
    have hd : -r / ξ = -Real.log (c + 1) := by
      dsimp [r]
      field_simp [ne_of_gt hξ]
    rw [hd, Real.exp_neg, Real.exp_log hcp]
  have hb : (1 : ℝ) ≤ c * Real.exp (-r / ξ) := by
    have hs := h r r 1 trivial
    change condCov (distE 0) (distE r 1) (distE r 1) ≤
      c * ‖(1 : ℝ)‖ ^ 2 * Real.exp (-r / ξ) at hs
    simpa [condCov, distE, hrn] using hs
  rw [he] at hb
  have hlt : c * (c + 1)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hcp]
    linarith
  exact (not_le_of_gt hlt) hb

/-- All premises of old Theorem 26 are met but the conclusion is false. -/
theorem theorem26Refute :
    (distE = distSetup.Eρ ∨ distE = distSetup.EL) ∧
      (∀ A : ℝ, IsProjectiveConditionalExpectation distSetup.expect distSetup.one (distE A)) ∧
      (∀ A : ℝ, ∃ lam : ℝ, IsSpectralGap (distSetup.LD A) (distE A) lam) ∧
      ¬ (∃ c ξ : ℝ, StrongClustering distE c ξ) :=
  ⟨Or.inl rfl, distProjective, distGap, distNoStrong⟩
end FalseClustering

end Qatlib.Papers.CommGibbsSamp14.MainResults.ExtraProbes
