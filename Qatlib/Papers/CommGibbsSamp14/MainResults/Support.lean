/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CommGibbsSamp14.MainResults.Framework.ObservableCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section


/-! Preserved abstract support and explicit failures of the old source bridge.
The arbitrary Hilbert-space fields are not a Gibbs construction. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommGibbsSamp14.MainResults
open Qatlib.Papers.CommGibbsSamp14.MainResults.Framework
open scoped InnerProductSpace
variable {V Region : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The legacy marker is only a factorization through two unrestricted functions. -/
def IsMinimalConditionalExpectation (_S : PaperSetup V Region) (_A : Region)
    (E : V → V) : Prop :=
  ∃ (modularConj partialTrace : V → V), ∀ f : V, E f = partialTrace (modularConj f)

/-- Complete positivity and unitality are fields of the supplied limit package. -/
lemma liouvillianProjector_isCP_and_unital
    [CPMapData V] (S : PaperSetup V Region) (A : Region)
    (hProj : IsLiouvillianProjector S.one (S.LD A) (S.EL A)) :
    CPMapData.IsCP (S.EL A) ∧ S.EL A S.one = S.one :=
  ⟨hProj.choose_spec.2.2.2.2.2.2.1, hProj.choose_spec.2.2.2.2.2.2.2⟩

noncomputable def covRatio [RegionOps Region] (E : Region → V → V) (A B : Region)
    (f : V) : ℝ :=
  condCov (E (RegionOps.union A B)) (E A f) (E B f) / ‖f‖ ^ 2

noncomputable def covRatioBoundary [RegionOps Region] (E : Region → V → V) (A B : Region)
    (varBoundary : V → ℝ) (f : V) : ℝ :=
  condCov (E (RegionOps.union A B)) (E A f) (E B f) / varBoundary f

noncomputable def covZero (expect : V → ℝ) (zeroInner : V → V → ℝ) (f g : V) : ℝ :=
  |zeroInner f g - expect f * expect g|

noncomputable def normZero (zeroInner : V → V → ℝ) (f : V) : ℝ :=
  Real.sqrt (zeroInner f f)

def WeakClusteringZero (S : PaperSetup V Region) (zeroInner : V → V → ℝ) (c ξ : ℝ) : Prop :=
  0 < c ∧ 0 < ξ ∧
    ∀ f g : V, covZero S.expect zeroInner f g ≤
      c * normZero zeroInner f * normZero zeroInner g *
        Real.exp (-(S.supportDist f g) / ξ)

def OneInfClustering (S : PaperSetup V Region) (norm1 normInf : V → ℝ) (c ξ : ℝ) : Prop :=
  0 < c ∧ 0 < ξ ∧
    ∀ f g : V, cov S.expect f g ≤
      c * norm1 f * normInf g * Real.exp (-(S.supportDist f g) / ξ)

noncomputable def conditionalGapWith (L : V → V) (var : V → ℝ) : ℝ :=
  sInf {q : ℝ | ∃ f : V, 0 < var f ∧ q = ⟪f, -(L f)⟫_ℝ / var f}

def IsSemigroupOf (T : ℝ → V → V) (one : V) (L : V → V) : Prop :=
  (∀ f : V, T 0 f = f) ∧
    (∀ (s t : ℝ) (f : V), T (s + t) f = T s (T t f)) ∧
    (∀ t : ℝ, T t one = one) ∧
    (∀ f : V, HasDerivAt (fun t : ℝ => T t f) (L f) 0)

def PreparableInPolynomialTime (S : PaperSetup V Region) (T : ℝ → V → V)
    (traceDist : V → V → ℝ) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∃ poly : ℕ → ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ t : ℝ, 0 ≤ t ∧ traceDist (T t S.one) S.one ≤ ε ∧
      t ≤ (poly S.sites : ℝ) * Real.log (1 / ε) / lam

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
/-- Every function satisfies the old minimal-expectation marker. -/
theorem minimalMarker (S : PaperSetup V Region) (A : Region) (E : V → V) :
    IsMinimalConditionalExpectation S A E :=
  ⟨E, id, fun _ => rfl⟩

namespace Diagnostics
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

def badSetup : PaperSetup ℝ Unit where
  expect f := 1 - f
  one := 1
  Eρ _ _ := 0
  EL _ _ := 0
  LD _ _ := 0
  LH _ _ := 0
  supportDist _ _ := 0
  nbrhd _ := ()
  supportedIn _ _ := False
  actsIdentityOn _ _ := False
  sites := 1

def freePotential : IsRLocalCommutingPotential ℝ Unit where
  term _ := 0
  range := 0
  bound := 1
  bound_pos := by norm_num
  commutes := True

/-- Proposition 10 is false under its literal marker: the zero map is not unital. -/
theorem prop10Failure :
    (∀ A : Unit, IsMinimalConditionalExpectation badSetup A (badSetup.Eρ A)) ∧
      ¬ (∀ A : Unit, IsConditionalExpectation badSetup.expect badSetup.one (badSetup.Eρ A)) := by
  refine ⟨fun A => minimalMarker badSetup A _, ?_⟩
  intro h
  have hx := (h ()).unital
  norm_num [badSetup] at hx

/-- The independent zero generator and zero projector violate local primitivity. -/
theorem primitiveFail : ¬ LocallyPrimitive badSetup.LD badSetup.EL := by
  intro h
  have hx := h () 1 rfl
  norm_num [badSetup] at hx

/-- The independent zero generator and zero expectation have no positive spectral gap. -/
theorem zeroGapFailure :
    ¬ HasSizeIndependentGap (fun _ : Unit => badSetup.LD ())
      (fun _ : Unit => badSetup.EL ()) := by
  rintro ⟨lam, hlam, h⟩
  have hx := h () 1
  norm_num [badSetup, condVar_eq_norm_sq] at hx
  exact (not_le_of_gt hlam) hx

/-- Zero conditional maps satisfy strong clustering independently of the generator. -/
theorem freeStrong : StrongClustering badSetup.EL 1 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro A B f _
  simp [badSetup, condCov]
  positivity

/-- An arbitrary expectation functional need not even vanish on the zero observable. -/
theorem weakFailure : ¬ ∃ c ξ : ℝ, WeakClustering badSetup c ξ := by
  rintro ⟨c, ξ, _, _, h⟩
  have hx := h 0 2
  norm_num [badSetup, cov] at hx

/-- An unrestricted trace distance makes the old preparation target false. -/
theorem prepareFailure (T : ℝ → ℝ → ℝ) :
    ¬ PreparableInPolynomialTime badSetup T (fun _ _ => 1) := by
  rintro ⟨lam, _, poly, h⟩
  obtain ⟨t, _, hdist, _⟩ := h (1 / 2) (by norm_num)
  norm_num at hdist

/-- Identity evolution meets the old semigroup premise for the zero generator. -/
theorem identityFlow :
    IsSemigroupOf (fun _ f : ℝ => f) badSetup.one (badSetup.LD ()) := by
  refine ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ => rfl, ?_⟩
  intro f
  simpa [badSetup] using (hasDerivAt_const (0 : ℝ) f)

/-- Both premises of the old preparation corollary hold while its conclusion fails. -/
theorem prepareWitness :
    IsSemigroupOf (fun _ f : ℝ => f) badSetup.one (badSetup.LD ()) ∧
      (∃ c ξ : ℝ, StrongClustering badSetup.EL c ξ) ∧
      ¬ PreparableInPolynomialTime badSetup (fun _ f => f) (fun _ _ => 1) :=
  ⟨identityFlow, ⟨1, 1, freeStrong⟩, prepareFailure _⟩

/-- The one-dimensional equivalence fails when expectation and conditional maps are independent. -/
theorem oneDimFailure :
    ¬ ((∃ c ξ : ℝ, WeakClustering badSetup c ξ) ↔
      (∃ c ξ : ℝ, StrongClustering badSetup.EL c ξ)) := by
  intro h
  exact weakFailure (h.mpr ⟨1, 1, freeStrong⟩)

/-- The heat-bath fields are literally the same zero functions in the countermodel. -/
theorem heatPrimitive : ¬ LocallyPrimitive badSetup.LH badSetup.Eρ := by
  simpa [badSetup] using primitiveFail

/-- Strong clustering holds but the size-independent gap in the informal equivalence fails. -/
theorem strongNoGap :
    StrongClustering badSetup.EL 1 1 ∧
      ¬ HasSizeIndependentGap (fun _ : Unit => badSetup.LD ())
        (fun _ : Unit => badSetup.EL ()) :=
  ⟨freeStrong, zeroGapFailure⟩

/-- An arbitrary temperature label cannot repair an independently chosen zero generator. -/
theorem highTempFailure :
    ¬ ∃ Tc : ℝ, 0 < Tc ∧ ∀ (_i : Unit) (T : ℝ), Tc ≤ T →
      HasSizeIndependentGap (fun _ : Unit => badSetup.LD ())
        (fun _ : Unit => badSetup.EL ()) := by
  rintro ⟨Tc, _, h⟩
  exact zeroGapFailure (h () Tc le_rfl)

/-- Identity conditional maps make the old gap premise vacuous for the zero generator. -/
def fixedSetup : PaperSetup ℝ Unit :=
  { badSetup with EL := fun _ f => f, Eρ := fun _ f => f }

/-- The gapped-family premises of the old preparation theorem can actually be satisfied. -/
theorem fixedGap :
    HasSizeIndependentGap (fun _ : Unit => fixedSetup.LD ())
      (fun _ : Unit => fixedSetup.EL ()) := by
  refine ⟨1, by norm_num, ?_⟩
  intro i f
  simp [fixedSetup, badSetup, condVar_eq_norm_sq]

/-- Even satisfiable gap premises cannot control an arbitrary supplied distance. -/
theorem fixedNoPrep :
    IsSemigroupOf (fun _ f : ℝ => f) fixedSetup.one (fixedSetup.LD ()) ∧
      HasSizeIndependentGap (fun _ : Unit => fixedSetup.LD ())
        (fun _ : Unit => fixedSetup.EL ()) ∧
      HasSizeIndependentGap (fun _ : Unit => fixedSetup.LH ())
        (fun _ : Unit => fixedSetup.Eρ ()) ∧
      ¬ PreparableInPolynomialTime fixedSetup (fun _ f => f) (fun _ _ => 1) := by
  refine ⟨identityFlow, fixedGap, ?_, ?_⟩
  · simpa [fixedSetup, badSetup] using fixedGap
  · rintro ⟨lam, _, poly, h⟩
    obtain ⟨t, _, hd, _⟩ := h (1 / 2) (by norm_num)
    norm_num at hd

/-- A zero expectation gives genuine Cauchy--Schwarz clustering at zero distance. -/
def innerSetup : PaperSetup ℝ Unit :=
  { badSetup with expect := fun _ => 0 }

/-- The unrestricted expectation field can satisfy the old weak-clustering conclusion. -/
theorem innerWeak : WeakClustering innerSetup 1 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro f g
  simpa [cov, innerSetup, badSetup] using real_inner_le_norm f g

def offDiagonal (f g : ℝ) : ℝ := if f = g then 0 else 1

/-- An arbitrary zero-temperature pairing can have zero diagonal and nonzero covariance. -/
theorem offDiagonalFailure : ¬ ∃ c ξ : ℝ, WeakClusteringZero innerSetup offDiagonal c ξ := by
  rintro ⟨c, ξ, _, _, h⟩
  have hx := h 0 1
  norm_num [covZero, normZero, offDiagonal, innerSetup, badSetup] at hx

/-- The complete old zero-temperature equivalence fails for a supplied off-diagonal pairing. -/
theorem zeroCovFailure :
    ¬ ((∃ c ξ : ℝ, WeakClusteringZero innerSetup offDiagonal c ξ) ↔
      (∃ c ξ : ℝ, WeakClustering innerSetup c ξ)) := by
  intro h
  exact offDiagonalFailure (h.mpr ⟨1, 1, innerWeak⟩)

/-- The supplied zero functions need not be norms and cannot bound a nonzero covariance. -/
theorem oneInfZeroFailure :
    ¬ ∃ c ξ : ℝ, OneInfClustering badSetup (fun _ => 0) (fun _ => 0) c ξ := by
  rintro ⟨c, ξ, _, _, h⟩
  have hx := h 0 2
  norm_num [badSetup, cov] at hx

/-- A freely supplied zero restriction distance always meets the old indistinguishability bound. -/
theorem zeroIndist : LocallyIndistinguishable badSetup.EL (fun _ _ _ => 0) 1 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro A B rho sigma _ _ _
  positivity

/-- The old trace-duality equivalence fails when its purported norms and distance are unrelated. -/
theorem oneInfFailure :
    ¬ ((∃ c ξ : ℝ, OneInfClustering badSetup (fun _ => 0) (fun _ => 0) c ξ) ↔
      (∃ c ξ : ℝ, LocallyIndistinguishable badSetup.EL (fun _ _ _ => 0) c ξ)) := by
  intro h
  exact oneInfZeroFailure (h.mpr ⟨1, 1, zeroIndist⟩)

/-- Identity maps satisfy all five conditional-expectation fields even for the bad expectation. -/
theorem fixedProjective (A : Unit) :
    IsProjectiveConditionalExpectation fixedSetup.expect fixedSetup.one (fixedSetup.EL A) := by
  constructor
  · refine ⟨by trivial, rfl, fun _ => rfl, fun _ _ => rfl, ?_⟩
    intro f n
    change ⟪(id^[n]) f, f⟫_ℝ ≥ ⟪(id^[n + 1]) f, f⟫_ℝ
    simp
  · intro f
    rfl

/-- The zero generator has the old strictly positive local gap relative to identity maps. -/
theorem fixedLocalGap (A : Unit) : IsSpectralGap (fixedSetup.LD A) (fixedSetup.EL A) 1 := by
  refine ⟨by norm_num, ?_⟩
  intro f
  simp [fixedSetup, badSetup, condVar_eq_norm_sq]

/-- The old weak-clustering conclusion still fails for the fixed identity conditional maps. -/
theorem fixedWeakFailure : ¬ ∃ c ξ : ℝ, WeakClustering fixedSetup c ξ := by
  rintro ⟨c, ξ, _, _, h⟩
  have hx := h 0 2
  norm_num [cov, fixedSetup, badSetup] at hx

/-- All projectivity and positive-gap premises hold while the old unconditional conclusion fails. -/
theorem gapNoWeak :
    (∀ A : Unit, IsProjectiveConditionalExpectation fixedSetup.expect fixedSetup.one
      (fixedSetup.EL A)) ∧
    (∀ A : Unit, ∃ lam : ℝ, IsSpectralGap (fixedSetup.LD A) (fixedSetup.EL A) lam) ∧
    ¬ (∃ c ξ : ℝ, WeakClustering fixedSetup c ξ) :=
  ⟨fixedProjective, fun A => ⟨1, fixedLocalGap A⟩, fixedWeakFailure⟩

end Diagnostics
end Qatlib.Papers.CommGibbsSamp14.MainResults
