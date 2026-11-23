/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.GroundLift
public import Qatlib.Papers.SpectralGap11.MainResults.SimulationCost

/-!
# Actual reflection-oracle simulation of the amplified evolution

See [BoixoSomma2012SpectralGap], Lemma 2, Proof 3 and Eq. (9).
[Fixed source](https://arxiv.org/abs/1110.2494v3). The simulator
contains an actual finite program over the given reflection oracle and free
ancilla gates. Its output and query count are computed from that program; its
target is the exponential of the actual amplified Hamiltonian. The coefficient
is uniform in dimension, projector family, penalty and time. The unit offset in
`1+|Lt|` repairs the original skeleton's impossible positive-cost bound at zero
time and states the same large-time asymptotic power law.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Foundations.OperatorErrors.OperatorError

namespace Qatlib.Papers.SpectralGap11.MainResults

open AmplifiedRegister SimulationWord

variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- The target evolution is fixed by the actual amplified Hamiltonian. -/
def amplifiedEvolution (Proj : K → Matrix I I ℂ) (δ t : ℝ) :
    Matrix (I × (K × Bool)) (I × (K × Bool)) ℂ :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • doubledHamiltonian Proj (δ : ℂ))

/-- A simulation stores only its executable oracle program and its proved
accuracy against the fixed amplified evolution. -/
structure ReflectionOracleSimulation (Proj : K → Matrix I I ℂ) (δ t ε : ℝ) where
  program : List Instruction
  approx : ‖execute (lazyOracle Proj) (lazyP (I := I) (K := K))
      (δ / (Fintype.card K : ℝ)) program - amplifiedEvolution Proj δ t‖ ≤ ε

/-- Simulator output is computed by executing its stored program. -/
def ReflectionOracleSimulation.output {Proj : K → Matrix I I ℂ} {δ t ε : ℝ}
    (sim : ReflectionOracleSimulation Proj δ t ε) :
    Matrix (I × (K × Bool)) (I × (K × Bool)) ℂ :=
  execute (lazyOracle Proj) (lazyP (I := I) (K := K)) (δ / (Fintype.card K : ℝ)) sim.program

/-- Oracle cost is computed from the program syntax, rather than supplied. -/
def ReflectionOracleSimulation.queries {Proj : K → Matrix I I ℂ} {δ t ε : ℝ}
    (sim : ReflectionOracleSimulation Proj δ t ε) : ℕ := queryCount sim.program

/-- The actual controlled reflection has operator norm at most one. -/
theorem lazy_oracle_norm_le_one (Proj : K → Matrix I I ℂ)
    (hHerm : ∀ k, (Proj k).IsHermitian) (hProj : ∀ k, Proj k * Proj k = Proj k) :
    ‖lazyOracle Proj‖ ≤ 1 := by
  apply l2_norm_unitary_le_one
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  change lazyOracle Proj * (lazyOracle Proj)ᴴ = 1
  rw [(lazyOracle_hermitian Proj hHerm).eq]
  exact lazyOracle_sq Proj hProj

/-- The actual uniform-ancilla projection has operator norm at most one. -/
theorem lazy_projection_norm_le_one (hK : 0 < Fintype.card K) :
    ‖lazyP (I := I) (K := K)‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (lazyP (I := I) (K := K))
  rw [show (lazyP (I := I) (K := K))ᴴ = lazyP from lazyP_hermitian.eq,
    show lazyP (I := I) (K := K) * lazyP = lazyP from lazyP_sq hK] at h
  nlinarith [norm_nonneg (lazyP (I := I) (K := K))]

/-- The physical splitting after normalizing time by the number of terms. -/
theorem normalized_evolution (Proj : K → Matrix I I ℂ) (δ t : ℝ)
    (hK : 0 < Fintype.card K) :
    ((Fintype.card K : ℝ) * t) •
        (generators (lazyOracle Proj) (lazyP (I := I) (K := K))
          (δ / (Fintype.card K : ℝ))).sum =
      (-Complex.I * (t : ℂ)) • doubledHamiltonian Proj (δ : ℂ) := by
  have hL : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, Complex.ofReal_natCast]
  simp only [generators, List.sum_cons, List.sum_nil, add_zero,
    firstGenerator, secondGenerator, phaseGenerator, Matrix.mul_smul, Matrix.smul_mul,
    doubledHamiltonian, doubledProjectionDifference]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    smul_eq_mul, Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp [hL]
  ring

/-- Lemma 2 with an actual executable simulator and a coefficient fixed before
all instance and time parameters. The normalized order is `2κ`. -/
theorem reflection_oracle_simulation_bound (κ : ℕ) (hκ : 0 < κ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
        (Proj : K → Matrix I I ℂ),
        (∀ k, (Proj k).IsHermitian) →
        (∀ k, Proj k * Proj k = Proj k) →
        0 < Fintype.card K → ∀ (δ : ℝ), |δ| ≤ (Fintype.card K : ℝ) → ∀ (t : ℝ),
        ∃ sim : ReflectionOracleSimulation Proj δ t ε,
          0 < sim.queries ∧
          (sim.queries : ℝ) ≤ C * (1 + |(Fintype.card K : ℝ) * t|) ^
            (1 + 1 / (2 * (κ : ℝ))) := by
  refine ⟨uniformConstant (κ - 1) ε, uniformConstant_pos (κ - 1) ε hε, ?_⟩
  intro J L _ _ _ _ Proj hHerm hProj hK δ hδ t
  let U := lazyOracle Proj
  let P := lazyP (I := J) (K := L)
  let η := δ / (Fintype.card L : ℝ)
  let τ := (Fintype.card L : ℝ) * t
  let r := segments U P η (κ - 1) τ ε
  have hUU : U * U = 1 := lazyOracle_sq Proj hProj
  have hUH : Uᴴ = U := (lazyOracle_hermitian Proj hHerm).eq
  have hPH : Pᴴ = P := lazyP_hermitian.eq
  have hL : (0 : ℝ) < Fintype.card L := by exact_mod_cast hK
  have hη : |η| ≤ 1 := by
    dsimp [η]
    rw [abs_div, abs_of_pos hL]
    exact (div_le_one hL).mpr hδ
  have herr := simulation_error U P η hUU hUH hPH (κ - 1) τ ε hε
  rw [normalized_evolution Proj δ t hK] at herr
  let sim : ReflectionOracleSimulation Proj δ t ε :=
    ⟨program (κ - 1) τ r, herr⟩
  refine ⟨sim, ?_, ?_⟩
  · change 0 < queryCount (program (κ - 1) τ r)
    rw [program_queries]
    have hr : 0 < r := segments_pos U P η (κ - 1) τ ε
    positivity
  · have hcost := program_uniform U P η (lazy_oracle_norm_le_one Proj hHerm hProj)
      (lazy_projection_norm_le_one hK) hη (κ - 1) τ ε hε
    simpa only [ReflectionOracleSimulation.queries, sim, r, τ, Nat.cast_add,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hκ.ne'), Nat.cast_one, sub_add_cancel] using hcost

end Qatlib.Papers.SpectralGap11.MainResults
