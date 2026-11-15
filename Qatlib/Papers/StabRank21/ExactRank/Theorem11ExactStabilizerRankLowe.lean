/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.PauliClifford.ExactRank.ExactRankCollision
public import Qatlib.Papers.StabRank21.ExactRank.Theorem11ExactStabilizerRankStat

@[expose] public section
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
namespace Qatlib.Papers.StabRank21.ExactRank
open Qatlib
open Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank

/-- For an angle strictly between zero and one quarter of pi, its sine is positive and smaller
than its cosine. -/
private theorem sine_cosine_range (θ : ℝ) (hθ : 0 < θ) (hθ4 : θ < Real.pi/4) :
    0 < Real.sin θ ∧ Real.sin θ < Real.cos θ := by
  have hp := Real.pi_pos
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)
  have hc :=
      Real.cos_pos_of_mem_Ioo
      (show θ ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith,by linarith⟩)
  have hcc := Real.cos_pos_of_mem_Ioo
    (show θ+θ ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith,by linarith⟩)
  rw [Real.cos_add] at hcc
  exact ⟨hs,by nlinarith⟩

/-- The magic state angle `magicRbeta` lies strictly between zero and one quarter of pi. -/
private theorem magicRbeta_range : 0 < magicRbeta ∧ magicRbeta < Real.pi/4 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs0 := Real.sqrt_nonneg 3
  have hs1 : 1 < Real.sqrt 3 := by nlinarith
  have hp : 0 < (1 : ℝ)/Real.sqrt 3 := by positivity
  have hl : (1 : ℝ)/Real.sqrt 3 < 1 := (div_lt_one (by positivity)).mpr hs1
  have ha := Real.arccos_pos.mpr hl
  have hb := Real.arccos_lt_pi_div_two.mpr hp
  unfold magicRbeta
  constructor <;> linarith

/-- When `0 < s` and `s < c`, the layer values `c^(n-j)*s^j` strictly decrease with the weight
index up to `n`. -/
private theorem layer_strict (n : ℕ) (c s : ℝ) (hs : 0 < s) (hsc : s < c)
    (i j : ℕ) (hij : i < j) (hj : j ≤ n) :
    c^(n-j)*s^j < c^(n-i)*s^i := by
  have hc : 0 < c := hs.trans hsc
  have hp : s^(j-i) < c^(j-i) := pow_lt_pow_left₀ hsc hs.le (by omega)
  have hsp : s^j=s^i*s^(j-i) := by
    rw [← pow_add]
    congr 1
    omega
  have hcp : c^(n-i)=c^(n-j)*c^(j-i) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = (c^(n-j)*s^i)*s^(j-i) := by rw [hsp]; ring
    _ < (c^(n-j)*s^i)*c^(j-i) := mul_lt_mul_of_pos_left hp (by positivity)
    _ = c^(n-i)*s^i := by rw [hcp]; ring

/-- Under `0 < s` and `s < c`, equal layer values at indices bounded by `n` imply equal indices. -/
private theorem layer_eq_weight (n : ℕ) (c s : ℝ) (hs : 0 < s) (hsc : s < c)
    (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) (he : c^(n-i)*s^i=c^(n-j)*s^j) : i=j := by
  rcases lt_trichotomy i j with h | h | h
  · have hl := layer_strict n c s hs hsc i j h hj
    rw [he] at hl
    exact (lt_irrefl _ hl).elim
  · exact h
  · have hl := layer_strict n c s hs hsc j i h hi
    rw [he] at hl
    exact (lt_irrefl _ hl).elim

/-- The Hamming weight of a Boolean vector is at most its dimension. -/
private theorem weight_le {n : ℕ} (x : BooleanVec n) : cubeWeight x ≤ n := by
  simpa [cubeWeight] using (hammingNorm_le_card_fintype (x := x))

/-- The complex phase `expPiQuarterI` has squared norm one. -/
private theorem phase_normSq : Complex.normSq expPiQuarterI=1 := by
  simp [expPiQuarterI,Complex.normSq_eq_norm_sq,Complex.norm_exp,Complex.mul_re]

/-- The squared norm of a `magicH` amplitude is the cosine squared factor to the zero bit count
times the sine squared factor to the Hamming weight. -/
private theorem magicH_normSq {n : ℕ} (x : BooleanVec n) :
    Complex.normSq (magicH n x)=(Real.cos (Real.pi/8)^2)^(n-cubeWeight x)*
      (Real.sin (Real.pi/8)^2)^cubeWeight x := by
  simp only [magicH,map_mul,map_pow,Complex.normSq_ofReal,pow_two]

/-- The squared norm of a `magicR` amplitude is the corresponding cosine squared factor to the
zero bit count times the sine squared factor to the Hamming weight. -/
private theorem magicR_normSq {n : ℕ} (x : BooleanVec n) :
    Complex.normSq (magicR n x)=(Real.cos magicRbeta^2)^(n-cubeWeight x)*
      (Real.sin magicRbeta^2)^cubeWeight x := by
  simp only [magicR,map_mul,map_pow,Complex.normSq_ofReal,phase_normSq,one_mul,pow_two]

/-- Equal `magicH` amplitudes imply equal Hamming weights. -/
theorem magicH_layer_injective {n : ℕ} (x y : BooleanVec n)
    (he : magicH n x=magicH n y) : cubeWeight x=cubeWeight y := by
  have hr := sine_cosine_range (Real.pi/8) (by positivity) (by linarith [Real.pi_pos])
  have hcs : 0 < Real.cos (Real.pi/8) := hr.1.trans hr.2
  have he' := congrArg Complex.normSq he
  rw [magicH_normSq,magicH_normSq] at he'
  exact layer_eq_weight n _ _ (sq_pos_of_pos hr.1)
    ((sq_lt_sq₀ hr.1.le hcs.le).mpr hr.2) _ _ (weight_le x) (weight_le y) he'

/-- Equal `magicR` amplitudes imply equal Hamming weights. -/
theorem magicR_layer_injective {n : ℕ} (x y : BooleanVec n)
    (he : magicR n x=magicR n y) : cubeWeight x=cubeWeight y := by
  have hr := sine_cosine_range magicRbeta magicRbeta_range.1 magicRbeta_range.2
  have hcs : 0 < Real.cos magicRbeta := hr.1.trans hr.2
  have he' := congrArg Complex.normSq he
  rw [magicR_normSq,magicR_normSq] at he'
  exact layer_eq_weight n _ _ (sq_pos_of_pos hr.1)
    ((sq_lt_sq₀ hr.1.le hcs.le).mpr hr.2) _ _ (weight_le x) (weight_le y) he'

/-- The `magicH` state is nonzero in every dimension. -/
theorem magicH_nonzero (n : ℕ) : magicH n ≠ 0 := by
  intro he
  have hh := congrFun he (0 : BooleanVec n)
  have hr := sine_cosine_range (Real.pi/8) (by positivity) (by linarith [Real.pi_pos])
  have hc : Real.cos (Real.pi/8) ≠ 0 := ne_of_gt (hr.1.trans hr.2)
  have hn : magicH n (0 : BooleanVec n) ≠ 0 := by
    simpa [magicH,cubeWeight] using pow_ne_zero n (Complex.ofReal_ne_zero.mpr hc)
  exact hn hh

/-- The `magicR` state is nonzero in every dimension. -/
theorem magicR_nonzero (n : ℕ) : magicR n ≠ 0 := by
  intro he
  have hh := congrFun he (0 : BooleanVec n)
  have hr := sine_cosine_range magicRbeta magicRbeta_range.1 magicRbeta_range.2
  have hc : Real.cos magicRbeta ≠ 0 := ne_of_gt (hr.1.trans hr.2)
  have hn : magicR n (0 : BooleanVec n) ≠ 0 := by
    simpa [magicR,cubeWeight] using pow_ne_zero n (Complex.ofReal_ne_zero.mpr hc)
  exact hn hh

/-- A nonzero function whose equal amplitudes force equal Hamming weights has stabilizer rank
strictly greater than `n/100`. -/
private theorem rank_bound_of_layers {n : ℕ} (F : BooleanVec n → ℂ) (hF : F ≠ 0)
    (hlayers : ∀ x y, F x=F y → cubeWeight x=cubeWeight y) :
    n/100 < stabilizerRank F := by
  by_contra h
  have hr : stabilizerRank F ≤ n/100 := Nat.le_of_not_gt h
  have h100 : 100*stabilizerRank F ≤ n := by omega
  have hχ : stabilizerRank F ≠ 0 := fun h => hF ((stabilizerRank_eq_zero F).mp h)
  have hn : 1 ≤ n := by omega
  obtain ⟨y,z,hweights,heq⟩ := exact_rank_collision F hn h100 le_rfl
  exact hweights (hlayers y z heq)

/-- Both `magicH n` and `magicR n` have exact stabilizer rank strictly greater than `n/100`. -/
theorem theorem11ExactStabilizerRank : Theorem11ExactStabilizerRank := by
  intro n
  exact ⟨rank_bound_of_layers (magicH n) (magicH_nonzero n) magicH_layer_injective,
    rank_bound_of_layers (magicR n) (magicR_nonzero n) magicR_layer_injective⟩

end Qatlib.Papers.StabRank21.ExactRank
