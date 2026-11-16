/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdversaryHam11.MainResults.HamiltonianOracleModel
public import Qatlib.Papers.AdversaryHam11.MainResults.ProgressReduction
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Complete old-interface counterexamples

The endpoint counterexamples exploit epsilon=1, outside the useful source
bounded-error range. The derivative counterexample uses coincident oracle
supports absent from the old structure: it is not a source Hamiltonian-query
algorithm. Every entire original conditional target is retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AdversaryHam11.MainResults
namespace Qatlib.Papers.AdversaryHam11.MainResults.EndpointAudit

/-- The real two-input swap adversary with actual spectral norm one. -/
def gamma : Matrix Bool Bool ℝ := fun x y => if x=y then 0 else 1

/-- The swap spectral norm is one by the actual C-star identity. -/
theorem gammaNorm : ‖gamma‖=1 := by
  have he : star gamma * gamma=1 := by
    ext x y
    cases x <;> cases y <;> simp [gamma,Matrix.mul_apply,Matrix.star_apply]
  have hn := CStarRing.norm_star_mul_self (x:=gamma)
  rw [he,norm_one] at hn
  nlinarith [norm_nonneg gamma]

/-- The positive uniform principal eigenvector of the swap. -/
def delta : Bool → ℝ := fun _ => Real.sqrt (1/2)

/-- The actual principal eigenvector has squared Euclidean norm one. -/
theorem deltaUnit : ∑ x, delta x^2=1 := by
  have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤1/2)
  simp only [Fintype.sum_bool,delta]
  linarith

/-- The actual swap fixes the normalized positive vector. -/
theorem deltaEig : gamma.mulVec delta=‖gamma‖ • delta := by
  ext x
  cases x <;> simp [gammaNorm,gamma,delta,Matrix.mulVec,dotProduct]

/-- A normalized zero-time constant-state algorithm with zero Hamiltonians. -/
def model : HamiltonianModel Bool Unit 1 where
  oracle := fun _ _ => 0
  oracle_bound := by intro x j; simp
  driver := fun _ => 0
  coupling := fun _ => 0
  coupling_bound := by intro t; simp
  totalHam := fun _ _ => 0
  totalHam_eq := by intro x t; simp
  state := fun _ _ _ => 1
  initial := fun _ => 1
  initial_normalized := by simp [Normalized]
  initial_state := by intro x; rfl
  schrodinger := by
    intro x t
    simpa using (hasDerivAt_const t (fun _ : Unit => (1:ℂ)))
  state_normalized := by intro x t; simp [Normalized]

/-- The literal old success interface admits this algorithm at error one. -/
def computes : BoundedErrorComputes model (fun x => x) 1 0 where
  eps_nonneg := by norm_num
  eps_le_one := le_refl _
  accept := 0
  accept_herm := Matrix.isHermitian_zero
  accept_idem := by simp
  complement_idem := by simp
  success := by intro x; cases x <;> simp [Qatlib.Foundations.PureStateMath.Inner,dotProduct,model]

/-- The full literal progress measure of the zero-time witness has norm one. -/
theorem startNorm : ‖progressMeasure gamma delta model.state 0‖=1 := by
  have hh : progressMeasure gamma delta model.state 0=1 := by
    simp [progressMeasure,model,Qatlib.Foundations.PureStateMath.Inner,dotProduct,gamma,delta]
    norm_cast
    have hn : Real.sqrt 2≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [hh,norm_one]



/-- The complete old signed lower-bound target fails at its permitted error-one endpoint. -/
theorem timeFails : ¬(∀
    {X H : Type} [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n : ℕ}
    (M : HamiltonianModel X H n) (f : X → Bool) (Γ : Matrix X X ℝ) (δ : X → ℝ)
    (input : X → Fin n → Bool) (ε T : ℝ)
    (_hinput : Function.Injective input)
    (_hΓsym : Γ.IsSymm)
    (_hΓzero : ∀ x y, f x = f y → Γ x y = 0)
    (_hδunit : ∑ x, δ x ^ 2 = 1)
    (_hδeig : Γ.mulVec δ = (‖Γ‖) • δ)
    (_halg : BoundedErrorComputes M f ε T)
    (_hT : 0 ≤ T),
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * ‖Γ‖ ≤ 2 * (maxFilteredSpec input Γ : ℝ) * T) := by
  intro h
  have hh := h model (fun x => x) gamma delta (fun x _ => x) 1 0
    (by intro x y h; exact congrFun h 0)
    (by ext x y; cases x <;> cases y <;> simp [gamma])
    (by intro x y h; simp [gamma,h]) deltaUnit deltaEig computes (by norm_num)
  norm_num [gammaNorm] at hh


/-- The complete old terminal-overlap target fails at its permitted error-one endpoint. -/
theorem terminalFails : ¬(∀
    {X H : Type} [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n : ℕ}
    (M : HamiltonianModel X H n) (f : X → Bool) (Γ : Matrix X X ℝ) (δ : X → ℝ)
    {ε T : ℝ} (_halg : BoundedErrorComputes M f ε T)
    (_hΓsym : Γ.IsSymm) (_hΓnonneg : ∀ x y, 0 ≤ Γ x y)
    (_hΓzero : ∀ x y, f x = f y → Γ x y = 0)
    (_hδnonneg : ∀ x, 0 ≤ δ x) (_hδunit : ∑ x, δ x ^ 2 = 1)
    (_hδeig : Γ.mulVec δ = (‖Γ‖) • δ),
    ‖progressMeasure Γ δ M.state T‖ ≤ 2 * Real.sqrt (ε * (1 - ε)) * ‖Γ‖) := by
  intro h
  have hh := h model (fun x => x) gamma delta computes
    (by ext x y; cases x <;> cases y <;> simp [gamma])
    (by intro x y; cases x <;> cases y <;> simp [gamma])
    (by intro x y h; simp [gamma,h])
    (by intro x; exact Real.sqrt_nonneg _) deltaUnit deltaEig
  norm_num [gammaNorm,startNorm] at hh


/-- The actual phase generated by four coincident unit oracle terms. -/
def phase (t : ℝ) : ℂ := Complex.exp ((-4*Complex.I)*(t:ℂ))

/-- The actual complex exponential phase has modulus one. -/
theorem phaseNorm (t : ℝ) : ‖phase t‖=1 := by
  simp [phase,Complex.norm_exp,Complex.mul_re]

/-- The phase obeys its exact real-time Schrodinger derivative. -/
theorem phaseDeriv (t : ℝ) : HasDerivAt phase ((-4*Complex.I)*phase t) t := by
  have hr : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 t := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using! (Complex.ofRealCLM.hasDerivAt (x:=t))
  convert (hr.const_mul (-4*Complex.I)).cexp using 1
  · funext u; simp [phase]
  · simp [phase]; ring

/-- The old model permits four unit oracle terms on the same one-dimensional space. -/
def phaseModel : HamiltonianModel Bool Unit 4 where
  oracle := fun x _ => if x then 1 else 0
  oracle_bound := by intro x j; cases x <;> simp
  driver := fun _ => 0
  coupling := fun _ => 1
  coupling_bound := by intro t; simp
  totalHam := fun x _ => if x then (4:ℂ) • (1 : Matrix Unit Unit ℂ) else 0
  totalHam_eq := by
    intro x t
    cases x <;> ext i j <;> cases i <;> cases j <;>
      norm_num [Fin.sum_univ_succ,Matrix.one_apply,Matrix.ofNat_apply]
  state := fun x t _ => if x then phase t else 1
  initial := fun _ => 1
  initial_normalized := by simp [Normalized]
  initial_state := by intro x; cases x <;> simp [phase]
  schrodinger := by
    intro x t
    cases x
    · simpa using (hasDerivAt_const t (fun _ : Unit => (1:ℂ)))
    · apply hasDerivAt_pi.mpr
      intro u
      simpa [Matrix.mulVec,dotProduct,mul_comm,mul_left_comm,mul_assoc] using phaseDeriv t
  state_normalized := by intro x t; cases x <;> simp [Normalized,phaseNorm]

/-- The actual fourfold phase reaches minus i at time pi divided by eight. -/
theorem phaseQuarter : phase (Real.pi/8)=-Complex.I := by
  unfold phase
  have he : (-4*Complex.I)*((Real.pi/8:ℝ):ℂ)=-(Real.pi:ℂ)/2*Complex.I := by
    push_cast
    ring
  rw [he,Complex.exp_neg_pi_div_two_mul_I]


/-- The true normalized swap progress initially equals one. -/
theorem phaseStart : progressMeasure gamma delta phaseModel.state 0=1 := by
  simp [progressMeasure,phaseModel,Qatlib.Foundations.PureStateMath.Inner,
    dotProduct,gamma,delta,phase]
  norm_cast
  have hn : Real.sqrt 2≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

/-- The true swap progress is zero at time pi divided by eight. -/
theorem phaseEnd : progressMeasure gamma delta phaseModel.state (Real.pi/8)=0 := by
  simp [progressMeasure,phaseModel,Qatlib.Foundations.PureStateMath.Inner,
    dotProduct,gamma,delta,phaseQuarter]

/-- Every literal filtered swap has norm at most one. -/
theorem filteredNorm (j : Fin 4) :
    ‖filteredGamma (fun x : Bool => fun _ : Fin 4 => x) gamma j‖≤1 := by
  have he : filteredGamma (fun x : Bool => fun _ : Fin 4 => x) gamma j=gamma := by
    ext x y
    cases x <;> cases y <;> simp [filteredGamma,gamma]
  rw [he,gammaNorm]

/-- The entire old derivative target contradicts its mean-value consequence on the fourfold model. -/
theorem rateFails : ¬(∀
    {X H : Type} [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n : ℕ}
    (M : HamiltonianModel X H n) (f : X → Bool) (Γ : Matrix X X ℝ) (δ : X → ℝ)
    (input : X → Fin n → Bool) {T Mm : ℝ}
    (_hinput : Function.Injective input)
    (_hΓsym : Γ.IsSymm)
    (_hΓzero : ∀ x y, f x = f y → Γ x y = 0)
    (_hδunit : ∑ x, δ x ^ 2 = 1)
    (_hMf : ∀ j : Fin n, ‖filteredGamma input Γ j‖ ≤ Mm)
    (_hMm0 : 0 ≤ Mm)
    (_hT : 0 ≤ T),
    ∃ w' : ℝ → ℂ,
      (∀ t, HasDerivAt (progressMeasure Γ δ M.state) (w' t) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ‖w' t‖ ≤ 2 * Mm)) := by
  intro h
  obtain ⟨w',hd,hb⟩ := h phaseModel (fun x => x) gamma delta (fun x _ => x)
    (T:=Real.pi/8) (Mm:=1)
    (by intro x y h; exact congrFun h 0)
    (by ext x y; cases x <;> cases y <;> simp [gamma])
    (by intro x y h; simp [gamma,h]) deltaUnit filteredNorm
    (by norm_num) (by positivity)
  have hh := timeLowerBound_from_progress
    (w:=progressMeasure gamma delta phaseModel.state) (w':=w')
    (lam:=1) (M:=1) (T:=Real.pi/8) (ε':=0)
    (by positivity) (by norm_num) (by norm_num) hd hb phaseStart
    (by rw [phaseEnd]; norm_num)
  norm_num at hh
  nlinarith [Real.pi_lt_four]

/-- The old assembled nonnegative theorem also fails at error one despite all its premises. -/
theorem nonnegFails : ¬(∀
    {X H : Type} [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n : ℕ}
    (M : HamiltonianModel X H n) (f : X → Bool) (Γ : Matrix X X ℝ) (δ : X → ℝ)
    (input : X → Fin n → Bool) (ε T : ℝ)
    (_hinput : Function.Injective input)
    (_hΓsym : Γ.IsSymm) (_hΓnonneg : ∀ x y, 0 ≤ Γ x y)
    (_hΓzero : ∀ x y, f x = f y → Γ x y = 0)
    (_hδnonneg : ∀ x, 0 ≤ δ x) (_hδunit : ∑ x, δ x ^ 2 = 1)
    (_hδeig : Γ.mulVec δ = (‖Γ‖) • δ)
    (_halg : BoundedErrorComputes M f ε T)
    (_hT : 0 ≤ T),
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * ‖Γ‖ ≤ 2 * (maxFilteredSpec input Γ : ℝ) * T) := by
  intro h
  have hh := h model (fun x => x) gamma delta (fun x _ => x) 1 0
    (by intro x y h; exact congrFun h 0)
    (by ext x y; cases x <;> cases y <;> simp [gamma])
    (by intro x y; cases x <;> cases y <;> simp [gamma])
    (by intro x y h; simp [gamma,h])
    (by intro x; exact Real.sqrt_nonneg _) deltaUnit deltaEig computes (by norm_num)
  norm_num [gammaNorm] at hh

end Qatlib.Papers.AdversaryHam11.MainResults.EndpointAudit
