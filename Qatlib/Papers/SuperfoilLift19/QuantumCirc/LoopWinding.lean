/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.QuantumCirc.PhaseCirculation
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Phase lifts of planar wavefunction loops, winding, and the Madelung line integral

[Musser2019Superfoil], p. 154502-2, states that the circulation around a path `C`
is `Γ = ∮_C u · dl = ℏ Δφ / m`, that the phase increment `Δφ` is quantized in
units of `2π`, hence the circulation in units `κ = h/m`, and that a quantum
vortex is a point of zero density around which the phase winds by `2π`. See
[the published article](https://doi.org/10.1103/PhysRevLett.123.154502).

The public module `Qatlib.Papers.SuperfoilLift19.QuantumCirc.PhaseCirculation`
quantizes an abstract real phase lift supplied as a hypothesis. This module
supplies the missing analytic bridge from spatial planar wavefunction data:

* for a complex wave `c` along the reals, differentiable with continuous
  derivative `c'` and nowhere zero on an open window strictly containing the
  loop interval, a differentiable phase lift is *constructed* by integrating
  the imaginary part of the logarithmic derivative `c' / c`, and the polar
  decomposition `c t = ‖c t‖ * phaseFactor (phase t)` is proved
  (`exists_phase_lift`);
* the phase increment of a closed nonvanishing loop is an integer multiple of
  `2π` (`closed_loop_winding`), and any two continuous polar phase lifts of the
  same wave have the same increment (`phase_lift_increment_unique`), so the
  winding integer is a property of the wave;
* any differentiable Madelung phase has the current angular velocity
  `Im (c' / c)` as derivative (`polar_phase_velocity`), and the Madelung
  circulation `(ℏ / mass) ∫ Im (c' / c)`, equivalently the line integral of the
  current expression `Im (ψ* ψ')` against the number density `|ψ|²`, is
  exactly quantized (`circulation_quantized_of_closed`,
  `spatial_current_circulation_quantized`,
  `spatial_madelung_velocity_circulation`);
* a winding-one positive example, the unit vortex `ψ (z) = z` on the unit
  circle, has circulation exactly one quantum `κ = 2πℏ / m`
  (`unit_circle_vortex_circulation`);
* a zero-set counterexample: a closed loop grazing a density-zero vortex core
  admits a smooth polar decomposition whose phase increment is the
  half-quantum `π`, so the nonvanishing hypothesis cannot be dropped
  (`vortex_core_grazing_loop`).

No statement is made about phase lifts through a density zero, Gross--
Pitaevskii existence, or vortex nucleation dynamics; see the module
documentation of `Qatlib.Papers.SuperfoilLift19.QuantumCirc.PhaseCirculation`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.QuantumCirc

open Qatlib.Papers.SuperfoilLift19.QuantumCirc
open scoped Topology

/-- The angular velocity of a differentiable complex wave along a parameter:
the imaginary part of the logarithmic derivative `c' t / c t`. In the Madelung
normalization of [Musser2019Superfoil], `(hbar / mass) * angularVelocity` is the
tangential component of `u = (hbar / mass) ∇phase` along the loop. The value is
junk at a zero of `c`. -/
def angularVelocity (c c' : ℝ → ℂ) (t : ℝ) : ℝ := (c' t / c t).im

/-- The Madelung current density along a parametrized loop: the imaginary part
of `star (c t) * c' t`, i.e. `Im (ψ* ψ')` evaluated on the wave and its
derivative along the loop; dividing by the number density `‖c t‖ ^ 2` and
rescaling by `hbar / mass` gives the tangential velocity. -/
def currentAlong (c c' : ℝ → ℂ) (t : ℝ) : ℝ := (star (c t) * c' t).im

/-- Away from a density zero, the current divided by the number density
`‖c t‖ ^ 2` is the angular velocity of the phase. -/
theorem angularVelocity_eq_currentAlong_div_density {c c' : ℝ → ℂ} {t : ℝ}
    (hc : c t ≠ 0) :
    angularVelocity c c' t = currentAlong c c' t / ‖c t‖ ^ 2 := by
  have hnormSq : star (c t) * c t = ((‖c t‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.star_def]
    rw [Complex.sq_norm (c t), ← Complex.normSq_eq_conj_mul_self]
  refine (eq_div_iff ((by positivity : (0 : ℝ) < ‖c t‖ ^ 2).ne')).mpr ?_
  unfold angularVelocity currentAlong
  have hw : c' t = (c' t / c t) * c t := (div_mul_cancel₀ (c' t) hc).symm
  conv_rhs => rw [hw, mul_comm (c' t / c t) (c t), ← mul_assoc, hnormSq]
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, mul_comm]

/-- A real differentiable function composed with the unit phase factor has the
chain-rule derivative `phaseFactor (f x) * (f' x * I)`. -/
theorem phaseFactor_comp_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ}
    (h : HasDerivAt f f' x) :
    HasDerivAt (fun s => phaseFactor (f s))
      (phaseFactor (f x) * ((f' : ℂ) * Complex.I)) x := by
  have h1 : HasDerivAt (fun s => (f s : ℂ) * Complex.I) ((f' : ℂ) * Complex.I) x :=
    (h.ofReal_comp).mul_const Complex.I
  exact h1.cexp

/-- The phase factor is continuous; used to build loop examples. -/
theorem continuous_phaseFactor : Continuous phaseFactor :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal).mul continuous_const)

/-- A complex number minus `i` times its imaginary part is its real part. -/
private theorem re_sub_im_mul_I (w : ℂ) : w - ((w.im : ℂ) * Complex.I) = ((w.re : ℂ)) := by
  rw [Complex.ext_iff]
  constructor <;> simp

/-- The derivative of the gauged wave `X / pf` when `X = w * v`: the quotient
rule value simplifies to `w.re * (v / pf)`. Used in the construction of the
phase lift. -/
private theorem gauge_quotient_value (w X v pfv : ℂ) (hpf : pfv ≠ 0)
    (hX : X = w * v) :
    (X * pfv - v * (pfv * ((w.im : ℂ) * Complex.I))) / pfv ^ 2 =
      ((w.re : ℂ) * (v / pfv)) := by
  rw [hX]
  have hfac : w * v * pfv - v * (pfv * ((w.im : ℂ) * Complex.I)) =
      v * pfv * (w - ((w.im : ℂ) * Complex.I)) := by
    ring
  rw [hfac, re_sub_im_mul_I]
  field_simp [hpf]

/-- A continuous real function on a loop interval taking only values in the
`2π`-lattice is constant. This discreteness step is what makes winding
information a property of the wave rather than of the chosen lift. -/
theorem lattice_pi_constant {a b : ℝ} {u : ℝ → ℝ}
    (hucont : ContinuousOn u (Set.Icc a b))
    (hlat : ∀ t ∈ Set.Icc a b, ∃ n : ℤ, u t = 2 * Real.pi * (n : ℝ)) :
    ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, u s = u t := by
  have hcore : ∀ p q : ℝ, p ∈ Set.Icc a b → q ∈ Set.Icc a b → u p < u q → False := by
    intro p q hp hq hpq
    obtain ⟨np, hnp⟩ := hlat p hp
    obtain ⟨nq, hnq⟩ := hlat q hq
    have hlt : np < nq := by
      by_contra hcon
      rw [hnp, hnq] at hpq
      have hle : (nq : ℝ) ≤ (np : ℝ) := by exact_mod_cast (by omega : nq ≤ np)
      have hge : (2 * Real.pi) * (nq : ℝ) ≤ (2 * Real.pi) * (np : ℝ) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      linarith [Real.two_pi_pos, hpq, hge]
    have hone : (1 : ℝ) ≤ (nq : ℝ) - (np : ℝ) := by
      have h1 : (1 : ℤ) ≤ nq - np := by omega
      have h2 : ((nq - np : ℤ) : ℝ) = (nq : ℝ) - (np : ℝ) := by push_cast; ring
      rw [← h2]
      exact_mod_cast h1
    have hge : Real.pi ≤ ((nq : ℝ) - (np : ℝ)) * Real.pi := by
      have h2 : 1 * Real.pi ≤ ((nq : ℝ) - (np : ℝ)) * Real.pi :=
        mul_le_mul_of_nonneg_right hone (le_of_lt Real.pi_pos)
      linarith
    have hmid1 : u p < 2 * Real.pi * (np : ℝ) + Real.pi := by
      rw [hnp]
      linarith [Real.pi_pos]
    have hmid2 : 2 * Real.pi * (np : ℝ) + Real.pi < u q := by
      rw [hnq]
      linarith
    have hsub : Set.uIcc p q ⊆ Set.Icc a b := by
      intro r hr
      simp only [Set.mem_uIcc, Set.mem_Icc] at hr ⊢
      rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨hp.1.trans h1, h2.trans hq.2⟩
      · exact ⟨hq.1.trans h1, h2.trans hp.2⟩
    have hivt := intermediate_value_uIcc (ContinuousOn.mono hucont hsub)
    have hmem : 2 * Real.pi * (np : ℝ) + Real.pi ∈ Set.uIcc (u p) (u q) :=
      Set.mem_uIcc.mpr (Or.inl ⟨hmid1.le, hmid2.le⟩)
    have himg := Set.image_mono hsub (hivt hmem)
    obtain ⟨r, hr, hru⟩ := himg
    obtain ⟨nr, hnr⟩ := hlat r hr
    rw [hnr] at hru
    have h1 : (2 * (nr : ℝ)) * Real.pi = (2 * (np : ℝ) + 1) * Real.pi := by
      linarith
    have h2 : ((2 * np + 1 : ℤ) : ℝ) = ((2 * nr : ℤ) : ℝ) := by
      push_cast
      exact mul_right_cancel₀ Real.pi_ne_zero h1.symm
    have h3 : (2 * np + 1 : ℤ) = 2 * nr := by exact_mod_cast h2
    omega
  intro s hs t ht
  rcases lt_trichotomy (u s) (u t) with h | h | h
  · exact absurd (hcore s t hs ht h) not_false
  · exact h
  · exact absurd (hcore t s ht hs h) not_false

/-- **Existence of a differentiable phase lift.** Let `c` be a complex wave
along the reals, differentiable with continuous derivative `c'` and nowhere zero
on an open window `Set.Ioo A B` strictly containing the loop interval
`Set.Icc a b`. Then there is a real phase, differentiable on the loop interval
with derivative the current angular velocity `Im (c' / c)`, which reconstructs
the wave in polar form `c t = ‖c t‖ * phaseFactor (phase t)` and starts at the
principal argument `arg (c a)`. This constructs the phase lift whose
quantization the public module
`Qatlib.Papers.SuperfoilLift19.QuantumCirc.phase_integral_quantized` asserts. -/
theorem exists_phase_lift {A B a b : ℝ} (hA : A < a) (hab : a ≤ b) (hB : b < B)
    {c c' : ℝ → ℂ} (hcd : ∀ t ∈ Set.Ioo A B, HasDerivAt c (c' t) t)
    (hdc' : ContinuousOn c' (Set.Ioo A B)) (hne : ∀ t ∈ Set.Ioo A B, c t ≠ 0) :
    ∃ θ : ℝ → ℝ,
      (∀ t ∈ Set.Icc a b, HasDerivAt θ (angularVelocity c c' t) t) ∧
      (∀ t ∈ Set.Icc a b, c t = (‖c t‖ : ℂ) * phaseFactor (θ t)) ∧
      θ a = Complex.arg (c a) := by
  classical
  have hI : Set.Icc a b ⊆ Set.Ioo A B := by
    intro t ht
    exact ⟨lt_of_lt_of_le hA ht.1, lt_of_le_of_lt ht.2 hB⟩
  have hIab : ∀ t ∈ Set.Icc a b, A < t ∧ t < B := fun t ht =>
    Set.mem_Ioo.mp (hI ht)
  have haoo : a ∈ Set.Ioo A B := ⟨hA, lt_of_le_of_lt hab hB⟩
  have hccont : ContinuousOn c (Set.Ioo A B) := fun t ht =>
    (hcd t ht).continuousAt.continuousWithinAt
  have hwcont : ContinuousOn (fun t => c' t / c t) (Set.Ioo A B) := hdc'.div hccont hne
  have hrrcont : ContinuousOn (fun t => (c' t / c t).re) (Set.Ioo A B) :=
    Complex.continuous_re.comp_continuousOn hwcont
  have himcont' : ContinuousOn (fun t => (c' t / c t).im) (Set.Ioo A B) :=
    Complex.continuous_im.comp_continuousOn hwcont
  -- accumulated real and imaginary parts are primitives on the window
  have key_deriv : ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Ioo A B) →
      ∀ t ∈ Set.Icc a b, HasDerivAt (fun u => ∫ s in a..u, f s) (f t) t := by
    intro f hf t ht
    have hct : ContinuousAt f t :=
      hf.continuousAt (Ioo_mem_nhds (hIab t ht).1 (hIab t ht).2)
    have hsm : StronglyMeasurableAtFilter f (𝓝 t) :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (fun x hx => (hf.continuousAt (Ioo_mem_nhds hx.1 hx.2)).continuousWithinAt) t
        (Set.mem_Ioo.2 (hIab t ht))
    refine intervalIntegral.integral_hasDerivAt_right ?_ hsm hct
    refine ContinuousOn.intervalIntegrable ?_
    refine hf.mono ?_
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    exact ⟨lt_of_lt_of_le hA hs.1, lt_of_le_of_lt (le_trans hs.2 ht.2) hB⟩
  -- the constructed amplitude and phase, written inline
  have hRpos : ∀ t, 0 < ‖c a‖ * Real.exp (∫ s in a..t, (c' s / c s).re) := fun _ =>
    mul_pos (norm_pos_iff.mpr (hne a haoo)) (Real.exp_pos _)
  have hRne : ∀ t, ((‖c a‖ * Real.exp (∫ s in a..t, (c' s / c s).re) : ℝ) : ℂ) ≠ 0 :=
    fun t => by exact_mod_cast (ne_of_gt (hRpos t))
  have hRd : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun t => ‖c a‖ * Real.exp (∫ s in a..t, (c' s / c s).re))
        ((c' t / c t).re * (‖c a‖ * Real.exp (∫ s in a..t, (c' s / c s).re))) t := by
    intro t ht
    have h2 := ((key_deriv _ hrrcont t ht).exp).const_mul ‖c a‖
    exact h2.congr_deriv (by ring)
  have hθd : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun t => Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im)
        ((c' t / c t).im) t := fun t ht =>
    (key_deriv _ himcont' t ht).const_add _
  have hpfne : ∀ t, phaseFactor (Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im) ≠ 0 := by
    intro t
    show Complex.exp
        (((Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im : ℝ) : ℂ) * Complex.I) ≠ 0
    exact Complex.exp_ne_zero _
  have hpfd : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun t => phaseFactor (Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im))
        (phaseFactor (Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im) *
          (((c' t / c t).im : ℂ) * Complex.I)) t := fun t ht =>
    phaseFactor_comp_hasDerivAt (hθd t ht)
  -- the gauged wave `g = c / phaseFactor θ` solves the real ODE `g' = (re w) g`
  have hgd : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun t => c t / phaseFactor
          (Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im))
        (((c' t / c t).re : ℂ) * (c t / phaseFactor
          (Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im))) t := by
    intro t ht
    have hcc := hne t (hI ht)
    have hdiv := HasDerivAt.div (hcd t (hI ht)) (hpfd t ht) (hpfne t)
    exact hdiv.congr_deriv (gauge_quotient_value (c' t / c t) (c' t) (c t)
      (phaseFactor (Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im))
      (hpfne t) (div_mul_cancel₀ (c' t) hcc).symm)
  -- the ratio `h = g / R` is constant, both factors solving the same real ODE
  have hRc : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun t => ((‖c a‖ * Real.exp (∫ s in a..t, (c' s / c s).re) : ℝ) : ℂ))
        (((c' t / c t).re : ℂ) *
          ((‖c a‖ * Real.exp (∫ s in a..t, (c' s / c s).re) : ℝ) : ℂ)) t := by
    intro t ht
    have h2 := (hRd t ht).ofReal_comp
    exact h2.congr_deriv (by push_cast; ring)
  have hderiv0 : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun t => (c t / phaseFactor
          (Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im)) /
        ((‖c a‖ * Real.exp (∫ s in a..t, (c' s / c s).re) : ℝ) : ℂ)) 0 t := by
    intro t ht
    have hR0 : ((‖c a‖ * Real.exp (∫ s in a..t, (c' s / c s).re) : ℝ) : ℂ) ≠ 0 := hRne t
    have hq := HasDerivAt.div (hgd t ht) (hRc t ht) (hRne t)
    exact hq.congr_deriv (by field_simp [hR0]; ring)
  have hcont : ContinuousOn (fun t => (c t / phaseFactor
      (Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im)) /
    ((‖c a‖ * Real.exp (∫ s in a..t, (c' s / c s).re) : ℝ) : ℂ)) (Set.Icc a b) :=
    fun t ht =>
      ((hgd t ht).continuousAt.div (hRc t ht).continuousAt (hRne t)).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun x hx => (hderiv0 x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt)
  have hpfa : phaseFactor (Complex.arg (c a) + ∫ s in a..a, (c' s / c s).im) =
      c a / (‖c a‖ : ℂ) := by
    have hpol := Complex.norm_mul_exp_arg_mul_I (c a)
    have hint0 : ∫ s in a..a, (c' s / c s).im = 0 := intervalIntegral.integral_same
    have hpfeq : phaseFactor (Complex.arg (c a) + ∫ s in a..a, (c' s / c s).im) =
        Complex.exp ((Complex.arg (c a) : ℂ) * Complex.I) := by
      show Complex.exp
        (((Complex.arg (c a) + ∫ s in a..a, (c' s / c s).im : ℝ) : ℂ) * Complex.I) = _
      rw [hint0, add_zero]
    rw [hpfeq, eq_div_iff (show ((‖c a‖ : ℝ) : ℂ) ≠ 0 by
      exact_mod_cast (norm_ne_zero_iff.mpr (hne a haoo)))]
    exact (mul_comm _ _).trans hpol
  have hga : c a / phaseFactor (Complex.arg (c a) + ∫ s in a..a, (c' s / c s).im) =
      (‖c a‖ : ℂ) := by
    rw [hpfa, div_div_eq_mul_div]
    exact mul_div_cancel_left₀ _ (hne a haoo)
  have hint0 : ∫ s in a..a, (c' s / c s).re = 0 := intervalIntegral.integral_same
  have hRa : ((‖c a‖ * Real.exp (∫ s in a..a, (c' s / c s).re) : ℝ) : ℂ) =
      (‖c a‖ : ℂ) := by
    rw [hint0, Real.exp_zero, mul_one]
  have hha : (c a / phaseFactor (Complex.arg (c a) + ∫ s in a..a, (c' s / c s).im)) /
      ((‖c a‖ * Real.exp (∫ s in a..a, (c' s / c s).re) : ℝ) : ℂ) = 1 := by
    rw [hga, hRa]
    exact div_self (by exact_mod_cast (norm_ne_zero_iff.mpr (hne a haoo)))
  have hval : ∀ t ∈ Set.Icc a b,
      c t / phaseFactor (Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im) =
      ((‖c a‖ * Real.exp (∫ s in a..t, (c' s / c s).re) : ℝ) : ℂ) := by
    intro t ht
    have h1 := hconst t ht
    have h0 := hconst a (Set.mem_Icc.2 ⟨le_refl a, hab⟩)
    rw [h0, hha] at h1
    have h2 := h1
    rw [div_eq_one_iff_eq (hRne t)] at h2
    exact h2
  have hpolar : ∀ t ∈ Set.Icc a b,
      c t = ((‖c a‖ * Real.exp (∫ s in a..t, (c' s / c s).re) : ℝ) : ℂ) *
        phaseFactor (Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im) := fun t ht => by
    rw [← hval t ht, div_mul_cancel₀ _ (hpfne t)]
  have hmod : ∀ t ∈ Set.Icc a b,
      ‖c t‖ = ‖c a‖ * Real.exp (∫ s in a..t, (c' s / c s).re) := by
    intro t ht
    have hp := hpolar t ht
    conv_lhs => rw [hp]
    rw [norm_mul, phase_factor_norm, mul_one, Complex.norm_real]
    exact abs_eq_self.mpr (hRpos t).le
  refine ⟨fun t => Complex.arg (c a) + ∫ s in a..t, (c' s / c s).im,
    fun t ht => hθd t ht, ?_, by
      show Complex.arg (c a) + ∫ s in a..a, (c' s / c s).im = Complex.arg (c a)
      rw [intervalIntegral.integral_same, add_zero]⟩
  intro t ht
  rw [hmod t ht, hpolar t ht]

/-- Two continuous polar phase lifts of the same nowhere-zero wave along a
loop interval have the same endpoint increment: the winding information is a
property of the wave, not of the chosen lift. -/
theorem phase_lift_increment_unique {a b : ℝ} (hab : a ≤ b) {c : ℝ → ℂ} {θ₁ θ₂ : ℝ → ℝ}
    (hne : ∀ t ∈ Set.Icc a b, c t ≠ 0)
    (hp1 : ∀ t ∈ Set.Icc a b, c t = (‖c t‖ : ℂ) * phaseFactor (θ₁ t))
    (hp2 : ∀ t ∈ Set.Icc a b, c t = (‖c t‖ : ℂ) * phaseFactor (θ₂ t))
    (hc1 : ContinuousOn θ₁ (Set.Icc a b)) (hc2 : ContinuousOn θ₂ (Set.Icc a b)) :
    θ₁ b - θ₁ a = θ₂ b - θ₂ a := by
  set u : ℝ → ℝ := fun t => θ₁ t - θ₂ t with hudef
  have hucont : ContinuousOn u (Set.Icc a b) := hc1.sub hc2
  have hlat : ∀ t ∈ Set.Icc a b, ∃ n : ℤ, u t = 2 * Real.pi * (n : ℝ) := by
    intro t ht
    have hcc : (‖c t‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr (hne t ht))
    have hpf1 : phaseFactor (θ₁ t) = phaseFactor (θ₂ t) := by
      refine mul_left_cancel₀ hcc ?_
      rw [← hp1 t ht]
      exact hp2 t ht
    have hadd : θ₂ t + u t = θ₁ t := by simp only [hudef]; ring
    have hsplit : phaseFactor (θ₂ t) * phaseFactor (u t) = phaseFactor (θ₂ t) := by
      rw [← phase_factor_add (θ₂ t) (u t), hadd]
      exact hpf1
    have hpf2ne : (phaseFactor (θ₂ t) : ℂ) ≠ 0 := by
      show Complex.exp (((θ₂ t : ℝ) : ℂ) * Complex.I) ≠ 0
      exact Complex.exp_ne_zero _
    have hpfu : phaseFactor (u t) = 1 :=
      mul_left_cancel₀ hpf2ne (by rw [hsplit, mul_one])
    have hclos := (phase_factor_closure_iff_winding (0 : ℝ) (u t)).1 (by
      show phaseFactor (u t) = phaseFactor 0
      rw [hpfu]
      show (1 : ℂ) = Complex.exp (((0 : ℝ) : ℂ) * Complex.I)
      push_cast
      rw [zero_mul, Complex.exp_zero])
    obtain ⟨n, hn⟩ := hclos
    exact ⟨n, by simpa using hn⟩
  have hconst := lattice_pi_constant hucont hlat
  have hb := hconst b ⟨hab, le_refl b⟩ a ⟨le_refl a, hab⟩
  simp only [hudef] at hb
  linarith

/-- The derivative of any differentiable Madelung phase of a nowhere-zero wave
is forced to equal the current angular velocity `Im (c' / c)`: the abstract
phase lift of the public quantization theorem carries exactly the Madelung
velocity, independently of the chosen lift. -/
theorem polar_phase_velocity {A B a b : ℝ} (hA : A < a) (hab : a ≤ b) (hB : b < B)
    {c c' : ℝ → ℂ} (hcd : ∀ t ∈ Set.Ioo A B, HasDerivAt c (c' t) t)
    (hdc' : ContinuousOn c' (Set.Ioo A B)) (hne : ∀ t ∈ Set.Ioo A B, c t ≠ 0)
    {θ : ℝ → ℝ} {dθ : ℝ → ℝ}
    (hpolar : ∀ t ∈ Set.Icc a b, c t = (‖c t‖ : ℂ) * phaseFactor (θ t))
    (hθd : ∀ t ∈ Set.Ioo A B, HasDerivAt θ (dθ t) t) :
    ∀ t ∈ Set.Ioo a b, dθ t = angularVelocity c c' t := by
  have hI : Set.Icc a b ⊆ Set.Ioo A B := by
    intro t ht
    exact ⟨lt_of_lt_of_le hA ht.1, lt_of_le_of_lt ht.2 hB⟩
  obtain ⟨θ₀, hθ₀d, hθ₀polar, -⟩ := exists_phase_lift hA hab hB hcd hdc' hne
  have hθ₀cont : ContinuousOn θ₀ (Set.Icc a b) := fun t ht =>
    (hθ₀d t ht).continuousAt.continuousWithinAt
  have hθcont : ContinuousOn θ (Set.Icc a b) := fun t ht =>
    (hθd t (hI ht)).continuousAt.continuousWithinAt
  have key : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, θ s - θ₀ s = θ t - θ₀ t := by
    intro s hs t ht
    rcases le_total s t with hst | hts
    · have hsub : Set.Icc s t ⊆ Set.Icc a b := fun r hr =>
        ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
      have h := phase_lift_increment_unique hst (fun r hr => hne r (hI (hsub hr)))
        (fun r hr => hpolar r (hsub hr)) (fun r hr => hθ₀polar r (hsub hr))
        (ContinuousOn.mono hθcont hsub) (ContinuousOn.mono hθ₀cont hsub)
      linarith
    · have hsub : Set.Icc t s ⊆ Set.Icc a b := fun r hr =>
        ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩
      have h := phase_lift_increment_unique hts (fun r hr => hne r (hI (hsub hr)))
        (fun r hr => hpolar r (hsub hr)) (fun r hr => hθ₀polar r (hsub hr))
        (ContinuousOn.mono hθcont hsub) (ContinuousOn.mono hθ₀cont hsub)
      linarith
  intro t ht
  have hu : (fun s => θ s - θ₀ s) =ᶠ[𝓝 t] fun _ => θ t - θ₀ t := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact key s ⟨hs.1.le, hs.2.le⟩ t ⟨ht.1.le, ht.2.le⟩
  have hdu : HasDerivAt (fun s => θ s - θ₀ s) (dθ t - angularVelocity c c' t) t :=
    (hθd t (hI ⟨ht.1.le, ht.2.le⟩)).sub (hθ₀d t ⟨ht.1.le, ht.2.le⟩)
  have hzero := hasDerivAt_const t (θ t - θ₀ t)
  have hd0 : deriv (fun s => θ s - θ₀ s) t = 0 :=
    hu.deriv_eq.trans (HasDerivAt.deriv hzero)
  have hv1 : dθ t - angularVelocity c c' t = 0 :=
    (HasDerivAt.deriv hdu).symm.trans hd0
  linarith

/-- **Winding quantization of a closed nonvanishing loop.** If a wave `c` with
a polar phase along the closed loop interval satisfies `c b = c a` and never
vanishes on the loop, then the phase increment is an integer multiple of
`2π`, and the integer is unique. Combined with `phase_lift_increment_unique`
the integer depends only on the wave. This is the integer of [Musser2019Superfoil],
Fig. 1(b), counted by phase jumps around the airfoil. -/
theorem closed_loop_winding {a b : ℝ} (hab : a ≤ b) {c : ℝ → ℂ} {θ : ℝ → ℝ}
    (hne : ∀ t ∈ Set.Icc a b, c t ≠ 0)
    (hpolar : ∀ t ∈ Set.Icc a b, c t = (‖c t‖ : ℂ) * phaseFactor (θ t))
    (hcl : c b = c a) :
    ∃! n : ℤ, θ b - θ a = 2 * Real.pi * (n : ℝ) := by
  have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  have ha : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hnorm : ‖c b‖ = ‖c a‖ := by rw [hcl]
  have hna : (‖c a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr (hne a ha))
  have hpf : phaseFactor (θ b) = phaseFactor (θ a) := by
    refine mul_right_cancel₀ hna ?_
    have hb' : phaseFactor (θ b) * (‖c a‖ : ℂ) = c b := by
      rw [mul_comm, show ((‖c a‖ : ℝ) : ℂ) = ((‖c b‖ : ℝ) : ℂ) by
        exact_mod_cast hnorm.symm]
      exact (hpolar b hb).symm
    rw [hb', hcl]
    exact ((mul_comm _ _).trans (hpolar a ha).symm).symm
  obtain ⟨n, hn⟩ := (phase_factor_closure_iff_winding (θ a) (θ b)).1 hpf
  refine ⟨n, hn, ?_⟩
  intro m hm
  have hnm : (2 * Real.pi : ℝ) * (n : ℝ) = (2 * Real.pi : ℝ) * (m : ℝ) :=
    hn.symm.trans hm
  have hcast : ((n : ℝ)) = ((m : ℝ)) := mul_left_cancel₀ (by positivity) hnm
  exact Int.cast_injective hcast.symm

/-- **Quantized circulation of a closed nonvanishing loop.** The Madelung
circulation, as the interval integral of the current angular velocity
`(hbar / mass) * Im (c' / c)` along a closed loop on which the wave is `C¹`
and nowhere zero on a window of the interval, is an integer multiple of the
circulation quantum `2π hbar / mass`. The integer is the loop winding of
`closed_loop_winding`; the statement is the loop version of `Γ = ∮ u · dl =
(hbar / mass) Δφ` of [Musser2019Superfoil], p. 154502-2. -/
theorem circulation_quantized_of_closed {A B a b : ℝ} (hA : A < a) (hab : a ≤ b) (hB : b < B)
    {c c' : ℝ → ℂ} (hcd : ∀ t ∈ Set.Ioo A B, HasDerivAt c (c' t) t)
    (hdc' : ContinuousOn c' (Set.Ioo A B)) (hne : ∀ t ∈ Set.Ioo A B, c t ≠ 0)
    (hcl : c b = c a) (hbar mass : ℝ) :
    ∃ n : ℤ, (∫ t in a..b, (hbar / mass) * angularVelocity c c' t) =
      quantizedCirculation hbar mass n := by
  have hI : Set.Icc a b ⊆ Set.Ioo A B := by
    intro t ht
    exact ⟨lt_of_lt_of_le hA ht.1, lt_of_le_of_lt ht.2 hB⟩
  obtain ⟨θ, hθd, hpolar, -⟩ := exists_phase_lift hA hab hB hcd hdc' hne
  obtain ⟨n, hn, -⟩ := closed_loop_winding hab (fun t ht => hne t (hI ht)) hpolar hcl
  have hccont : ContinuousOn c (Set.Ioo A B) := fun t ht =>
    (hcd t ht).continuousAt.continuousWithinAt
  have hwcont : ContinuousOn (fun t => c' t / c t) (Set.Ioo A B) := hdc'.div hccont hne
  have himcont : ContinuousOn (fun t => (c' t / c t).im) (Set.Ioo A B) :=
    Complex.continuous_im.comp_continuousOn hwcont
  have hint : IntervalIntegrable (angularVelocity c c') MeasureTheory.volume a b := by
    have hcc : ContinuousOn (angularVelocity c c') (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      exact himcont.mono hI
    exact hcc.intervalIntegrable
  exact ⟨n, phase_integral_quantized hbar mass a b θ (angularVelocity c c') n
    (fun t ht => hθd t (Set.uIcc_of_le hab ▸ ht)) hint hn⟩

/-- **Spatial form of the quantized circulation.** For a planar wavefunction
`wave` evaluated along a closed `C¹` loop `curve` on which the wave never
vanishes, the line integral of the Madelung velocity in current form,
`(hbar / mass) * Im ((wave ∘ curve)' / (wave ∘ curve))`, is an integer
multiple of the circulation quantum. No phase needs to be supplied: the phase
lift is constructed by `exists_phase_lift`. -/
theorem spatial_current_circulation_quantized {A B a b : ℝ}
    (hA : A < a) (hab : a ≤ b) (hB : b < B)
    {wave : ℂ → ℂ} {curve : ℝ → ℂ} {wc : ℝ → ℂ}
    (hwc : ∀ t ∈ Set.Ioo A B, HasDerivAt (fun s => wave (curve s)) (wc t) t)
    (hwc' : ContinuousOn wc (Set.Ioo A B))
    (hne : ∀ t ∈ Set.Ioo A B, wave (curve t) ≠ 0)
    (hcl : curve b = curve a) (hbar mass : ℝ) :
    ∃ n : ℤ, (∫ t in a..b, (hbar / mass) *
        angularVelocity (fun t => wave (curve t)) wc t) =
      quantizedCirculation hbar mass n :=
  circulation_quantized_of_closed hA hab hB hwc hwc' hne (congrArg wave hcl) hbar mass

/-- **The Madelung velocity line integral.** Along a closed `C¹` loop where the
wavefunction is in Madelung polar form with a differentiable phase `phase` and
nowhere zero, the tangential derivative `pc` of the composed phase equals the
current angular velocity at every interior point, and the circulation
computed from `pc` is an integer multiple of the circulation quantum. This
identifies the abstract phase integral of the public module with the actual
Madelung line integral of `u = (hbar / mass) ∇phase`. -/
theorem spatial_madelung_velocity_circulation {A B a b : ℝ}
    (hA : A < a) (hab : a ≤ b) (hB : b < B)
    {wave : ℂ → ℂ} {curve : ℝ → ℂ} {wc : ℝ → ℂ} {phase : ℂ → ℝ} {pc : ℝ → ℝ}
    (hwc : ∀ t ∈ Set.Ioo A B, HasDerivAt (fun s => wave (curve s)) (wc t) t)
    (hwc' : ContinuousOn wc (Set.Ioo A B))
    (hne : ∀ t ∈ Set.Ioo A B, wave (curve t) ≠ 0)
    (hcl : curve b = curve a)
    (hpolar : ∀ t ∈ Set.Icc a b,
      wave (curve t) = (‖wave (curve t)‖ : ℂ) * phaseFactor (phase (curve t)))
    (hpc : ∀ t ∈ Set.Ioo A B, HasDerivAt (fun s => phase (curve s)) (pc t) t)
    (hint : IntervalIntegrable pc MeasureTheory.volume a b)
    (hbar mass : ℝ) :
    (∀ t ∈ Set.Ioo a b, pc t = angularVelocity (fun t => wave (curve t)) wc t) ∧
    ∃ n : ℤ, (∫ t in a..b, (hbar / mass) * pc t) =
      quantizedCirculation hbar mass n := by
  have hI : Set.Icc a b ⊆ Set.Ioo A B := by
    intro t ht
    exact ⟨lt_of_lt_of_le hA ht.1, lt_of_le_of_lt ht.2 hB⟩
  have hvel := polar_phase_velocity hA hab hB hwc hwc' hne hpolar hpc
  refine ⟨hvel, ?_⟩
  obtain ⟨n, hn, -⟩ := closed_loop_winding hab (fun t ht => hne t (hI ht)) hpolar
    (congrArg wave hcl)
  exact ⟨n, phase_integral_quantized hbar mass a b (fun t => phase (curve t)) pc n
    (fun t ht => hpc t (hI (Set.uIcc_of_le hab ▸ ht))) hint hn⟩

/-- **The winding-one example: the unit vortex on the unit circle.** For the
vortex wavefunction `ψ (z) = z`, whose single density zero is the origin, the
counterclockwise unit circle `t ↦ exp (t * I)` on `[0, 2π]` carries unit
density, and the Madelung line integral is exactly one circulation quantum
`κ = 2π hbar / mass` in the positive orientation. -/
theorem unit_circle_vortex_circulation {hbar mass : ℝ}
    (hh : hbar ≠ 0) (hm : mass ≠ 0) :
    (∫ t in 0..2 * Real.pi,
        (hbar / mass) * angularVelocity phaseFactor (fun t => phaseFactor t * Complex.I) t) =
      quantizedCirculation hbar mass 1 := by
  have hcl : phaseFactor (2 * Real.pi) = phaseFactor 0 := by
    show Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((0 : ℝ) : ℂ) * Complex.I)
    have e1 : ((2 * Real.pi : ℝ) : ℂ) * Complex.I =
        ((1 : ℤ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_mul]
      push_cast
      ring
    rw [e1, Complex.exp_int_mul_two_pi_mul_I]
    norm_num
  have hbig : ∃ n : ℤ, (∫ t in 0..2 * Real.pi,
      (hbar / mass) * angularVelocity phaseFactor (fun t => phaseFactor t * Complex.I) t) =
      quantizedCirculation hbar mass n :=
    circulation_quantized_of_closed (A := -1) (a := 0) (b := 2 * Real.pi)
      (B := 2 * Real.pi + 1) (by norm_num) (le_of_lt Real.two_pi_pos)
      (by linarith [Real.two_pi_pos])
      (c := phaseFactor) (c' := fun t => phaseFactor t * Complex.I)
      (fun t ht => (phaseFactor_comp_hasDerivAt (hasDerivAt_id t)).congr_deriv
        (by rw [show (id t : ℝ) = t from rfl]; push_cast; ring))
      (continuous_phaseFactor.mul continuous_const).continuousOn
      (fun t _ => by
        show Complex.exp (((t : ℝ) : ℂ) * Complex.I) ≠ 0
        exact Complex.exp_ne_zero _)
      hcl hbar mass
  obtain ⟨n, hn⟩ := hbig
  have hvel : ∀ t, angularVelocity phaseFactor (fun t => phaseFactor t * Complex.I) t = 1 := by
    intro t
    show ((phaseFactor t * Complex.I) / phaseFactor t).im = 1
    have hdiv : (phaseFactor t * Complex.I) / phaseFactor t = Complex.I := by
      refine mul_div_cancel_left₀ Complex.I ?_
      show Complex.exp (((t : ℝ) : ℂ) * Complex.I) ≠ 0
      exact Complex.exp_ne_zero _
    rw [hdiv]
    simp
  have hint_eq : (∫ t in 0..2 * Real.pi,
      (hbar / mass) * angularVelocity phaseFactor (fun t => phaseFactor t * Complex.I) t) =
      (hbar / mass) * (2 * Real.pi) := by
    rw [intervalIntegral.integral_congr (fun t _ => by rw [hvel t, mul_one]),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  have hz : (2 * Real.pi) * (hbar / mass) ≠ 0 :=
    mul_ne_zero (ne_of_gt Real.two_pi_pos) (div_ne_zero hh hm)
  rw [hint_eq] at hn
  simp only [quantizedCirculation, circulationQuantum] at hn
  have hnX : (2 * Real.pi) * (hbar / mass) = (2 * Real.pi) * (hbar / mass) * (n : ℝ) := by
    linear_combination hn
  have hcast : ((n : ℝ)) = 1 := by
    refine mul_right_cancel₀ hz ?_
    rw [one_mul]
    exact (mul_comm ((n : ℝ)) ((2 * Real.pi) * (hbar / mass))).trans hnX.symm
  have hn1 : n = 1 := by exact_mod_cast hcast
  subst hn1
  rw [hint_eq, quantizedCirculation, circulationQuantum]
  push_cast
  ring

/-- The polar decomposition of the loop `t ↦ (1 + exp (t i)) / 2` of the
vortex wave `ψ (z) = z`: the wave along the loop has amplitude `cos (t / 2)`
and phase `t / 2`. -/
theorem one_add_exp_div_two (t : ℝ) :
    (1 + Complex.exp (((t : ℝ) : ℂ) * Complex.I)) / 2 =
      ((Real.cos (t / 2) : ℝ) : ℂ) * phaseFactor (t / 2) := by
  have h1 : Complex.exp (((t / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((t / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((t : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add,
      show ((t / 2 : ℝ) : ℂ) * Complex.I + ((t / 2 : ℝ) : ℂ) * Complex.I =
        ((t : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  have h2 : Complex.exp ((-((t / 2 : ℝ) : ℂ)) * Complex.I) *
        Complex.exp (((t / 2 : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add,
      show (-((t / 2 : ℝ) : ℂ)) * Complex.I + ((t / 2 : ℝ) : ℂ) * Complex.I = 0 from by
        push_cast; ring,
      Complex.exp_zero]
  rw [Complex.ofReal_cos, Complex.cos]
  unfold phaseFactor
  rw [div_mul_eq_mul_div, add_mul, h1, h2]
  ring

/-- **The zero-set counterexample: a loop grazing a vortex core.** For the
vortex wave `ψ (z) = z` (density zero at the origin, phase winding `2π` around
it), the closed loop `t ↦ (1 + exp (t i)) / 2` on `[-π, π]` passes through the
core at both endpoints: the density `|ψ|²` vanishes at the closing point, the
smooth polar decomposition of `one_add_exp_div_two` has phase `t / 2`, and its
increment `π` is *not* an integer multiple of `2π`. Hence the nonvanishing
hypothesis of `closed_loop_winding` and `circulation_quantized_of_closed`
cannot be dropped: at a density zero the phase increment of a closed loop
carries no winding information. -/
theorem vortex_core_grazing_loop :
    (∀ t : ℝ, (1 + Complex.exp (((t : ℝ) : ℂ) * Complex.I)) / 2 =
      ((Real.cos (t / 2) : ℝ) : ℂ) * phaseFactor (t / 2)) ∧
    (1 + Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I)) / 2 = 0 ∧
    (1 + Complex.exp (((-Real.pi : ℝ) : ℂ) * Complex.I)) / 2 = 0 ∧
    ¬ ∃ n : ℤ, (Real.pi / 2 : ℝ) - (-Real.pi / 2) = 2 * Real.pi * (n : ℝ) := by
  refine ⟨one_add_exp_div_two, ?_, ?_, ?_⟩
  · rw [Complex.exp_pi_mul_I]
    norm_num
  · have e : (((-Real.pi : ℝ) : ℂ) * Complex.I) = -(((Real.pi : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_neg]
      ring
    rw [e, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  · rintro ⟨n, hn⟩
    have h2 : (1 : ℝ) = (2 : ℝ) * (n : ℝ) := by
      refine mul_left_cancel₀ Real.pi_ne_zero ?_
      linarith
    have h3 : ((1 : ℤ) : ℝ) = ((2 * n : ℤ) : ℝ) := by
      push_cast
      exact h2
    have h4 : (1 : ℤ) = 2 * n := Int.cast_injective h3
    omega

end Qatlib.Papers.SuperfoilLift19.QuantumCirc
