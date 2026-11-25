/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanCoreFieldLines

/-! Regression consumers for the closed actual Bateman core field lines:
the trefoil magnetic core at the initial slice, the five-fold electric
core, the four-ring-link exponents through the gcd decomposition, and
the transported trefoil core period on a later slice. The least-period
regressions instantiate the same statements at concrete non-degenerate
exponents on real time slices away from zero. -/

@[expose] public section
set_option autoImplicit false

open Qatlib.Papers.KnotLight13.TorusFamily

local notation "Space" => ℝ × ℝ × ℝ

/-- The magnetic trefoil core lap period is strictly positive. -/
example : 0 < batemanCoreLoopPeriod 2 3 1 1 := by
  obtain ⟨-, -, -, h, -, -⟩ :=
    exists_periodicMagneticCoreFieldLine (p := 2) (q := 3) (d := 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (phase := 1) (ζ := 1) (by norm_num)
      (by simp : ((1 : Circle) : ℂ).im = 0)
  exact h

/-- The electric five-fold core carries a closed actual electric line at
time zero, covering the whole core circle. -/
example : ∃ γ : ℝ → Space,
    IsIntegralCurve γ (fun _ => batemanElectricVector 2 5 0) ∧
    Set.range γ = poweredPhysicalCore 2 5 0 (Circle.exp (Real.pi / 2)) := by
  obtain ⟨γ, hcurve, hrange, -⟩ :=
    exists_periodicElectricCoreFieldLine (p := 2) (q := 5) (d := 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (phase := Circle.exp (Real.pi / 2))
      (ζ := Circle.exp (Real.pi / 2)) (by norm_num)
      (by
        have hI : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
          rw [Circle.coe_exp, Complex.exp_mul_I]
          simp
        rw [hI]
        rfl)
  exact ⟨γ, hcurve, hrange⟩

/-- Every point of the magnetic four-ring-link core at time zero lies on
a closed actual magnetic line of the exponent pair (2, 2). -/
example (s : Space) (hs : s ∈ poweredPhysicalCore 2 2 0 1) :
    ∃ γ : ℝ → Space, ∃ T : ℝ,
      IsIntegralCurve γ (fun _ => batemanMagneticVector 2 2 0) ∧
      0 < T ∧ Function.Periodic γ T ∧
      s ∈ Set.range γ ∧ Set.range γ ⊆ poweredPhysicalCore 2 2 0 1 := by
  obtain ⟨γ, T, hcurve, hT, hper, hmem, hsub, -⟩ :=
    exists_periodicMagneticCoreFieldLines_gcd (p := 2) (q := 2) (by norm_num)
      (by norm_num) (by simp : ((1 : Circle) : ℂ).im = 0) 0 hs
  exact ⟨γ, T, hcurve, hT, hper, hmem, hsub⟩

/-- The transported magnetic trefoil core line at time one is periodic
with the ray-Jacobian lap integral as its period. -/
example : ∃ γ : ℝ → Space, ∃ T : ℝ,
    IsIntegralCurve γ (fun _ => batemanMagneticVector 2 3 1) ∧
    Set.range γ = poweredPhysicalCore 2 3 1 1 ∧
    0 < T ∧ Function.Periodic γ T ∧
    ∃ γ₀ : ℝ → Space,
      Function.Periodic γ₀ (batemanCoreLoopPeriod 2 3 1 1) ∧
      T = batemanOrbitClock 1 γ₀ (batemanCoreLoopPeriod 2 3 1 1) := by
  obtain ⟨γ, T, hcurve, hrange, hT, hper, -, -, -, -, γ₀, -, hper₀, hclock⟩ :=
    exists_periodicMagneticCoreFieldLine_slice (p := 2) (q := 3) (d := 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (phase := 1) (ζ := 1) (by norm_num)
      (by simp : ((1 : Circle) : ℂ).im = 0) 1
  exact ⟨γ, T, hcurve, hrange, hT, hper, γ₀, hper₀, hclock⟩

/-- The transported magnetic trefoil core line at time one is
injective on its half-open lap interval, has the ray-clock lap time as
its least positive period, and every return time is a whole number of
laps. -/
example : ∃ γ : ℝ → Space, ∃ T : ℝ,
    IsIntegralCurve γ (fun _ => batemanMagneticVector 2 3 1) ∧
    0 < T ∧ Function.Periodic γ T ∧ Set.InjOn γ (Set.Ico 0 T) ∧
    (∀ S, 0 < S → Function.Periodic γ S → T ≤ S) ∧
    (∀ a b, γ a = γ b ↔ ∃ n : ℤ, a - b = n * T) := by
  obtain ⟨γ, T, hcurve, -, hT, hper, hinj, -, hmin, hmult, -⟩ :=
    exists_periodicMagneticCoreFieldLine_slice (p := 2) (q := 3) (d := 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (phase := 1) (ζ := 1) (by norm_num)
      (by simp : ((1 : Circle) : ℂ).im = 0) 1
  exact ⟨γ, T, hcurve, hT, hper, hinj, hmin, hmult⟩

/-- Half the lap time of the transported electric five-fold core line
at time minus two is not a period: the lap time is genuinely least. -/
example : ∃ γ : ℝ → Space, ∃ T : ℝ,
    IsIntegralCurve γ (fun _ => batemanElectricVector 2 5 (-2)) ∧
    0 < T ∧ Function.Periodic γ T ∧ ¬ Function.Periodic γ (T / 2) := by
  obtain ⟨γ, T, hcurve, -, hT, hper, -, -, hmin, -, -⟩ :=
    exists_periodicElectricCoreFieldLine_slice (p := 2) (q := 5) (d := 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (phase := Circle.exp (Real.pi / 2))
      (ζ := Circle.exp (Real.pi / 2)) (by norm_num)
      (by
        have hI : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
          rw [Circle.coe_exp, Complex.exp_mul_I]
          simp
        rw [hI]
        rfl)
      (-2)
  refine ⟨γ, T, hcurve, hT, hper, ?_⟩
  intro hhalf
  have hle := hmin (T / 2) (by linarith) hhalf
  linarith

/-- The gcd-component instances of the non-coprime exponents (4, 2) on
the time-one slice are once-per-lap injective with least positive
period and whole-number return times. -/
example (s : Space) (hs : s ∈ poweredPhysicalCore 4 2 1 1) :
    ∃ γ : ℝ → Space, ∃ T : ℝ,
      IsIntegralCurve γ (fun _ => batemanMagneticVector 4 2 1) ∧
      0 < T ∧ Function.Periodic γ T ∧
      s ∈ Set.range γ ∧ Set.range γ ⊆ poweredPhysicalCore 4 2 1 1 ∧
      Set.InjOn γ (Set.Ico 0 T) ∧
      (∀ S, 0 < S → Function.Periodic γ S → T ≤ S) ∧
      (∀ a b, γ a = γ b ↔ ∃ n : ℤ, a - b = n * T) := by
  obtain ⟨γ, T, hcurve, hT, hper, hmem, hsub, -, hinj, hmin, hmult⟩ :=
    exists_periodicMagneticCoreFieldLines_gcd (p := 4) (q := 2) (by norm_num)
      (by norm_num) (by simp : ((1 : Circle) : ℂ).im = 0) 1 hs
  exact ⟨γ, T, hcurve, hT, hper, hmem, hsub, hinj, hmin, hmult⟩
