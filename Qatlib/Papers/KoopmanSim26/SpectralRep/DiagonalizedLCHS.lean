/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.StaticNoncommutingLCHS
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder

namespace Qatlib.Papers.KoopmanSim26.SpectralRep

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QspSimulation.Achievability

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def propagator (L H : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp (t • (L + Complex.I • H))

noncomputable def spectralUnitary (L H : Matrix I I ℂ) (t k : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((Complex.I * (t : ℂ)) • (H + k • L))

lemma spectralUnitary_eq_hamiltonianEvolution (L H : Matrix I I ℂ) (t k : ℝ) :
    spectralUnitary L H t k = hamiltonianEvolution ((-H) + k • (-L)) t := by
  dsimp only [spectralUnitary, hamiltonianEvolution]
  congr 1
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, Complex.real_smul]
  ring

lemma staticNonunitaryEvolution_neg_neg (L H : Matrix I I ℂ) (t : ℝ) :
    staticNonunitaryEvolution (-L) (-H) t = propagator L H t := by
  dsimp only [staticNonunitaryEvolution, propagator]
  congr 1
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, Complex.real_smul]
  push_cast
  ring

theorem diagonalized_lchs_spectral_representation
    (L H : Matrix I I ℂ) (t : ℝ)
    (hL : (-L).PosSemidef) (hH : H.IsHermitian) (ht : 0 ≤ t) :
    (∀ i j : I, Integrable (fun k : ℝ =>
      ((1/(Real.pi*(1+k^2)) : ℝ) : ℂ) * spectralUnitary L H t k i j)) ∧
    (∫ k : ℝ, (1/(Real.pi*(1+k^2))) • spectralUnitary L H t k) = propagator L H t := by
  obtain ⟨hint, hmain, -⟩ :=
    static_noncommuting_lchs_cauchy_representation I (-L) (-H) t hL hH.neg ht
  refine ⟨fun i j => ?_, ?_⟩
  · have he : (fun k : ℝ => ((1/(Real.pi*(1+k^2)) : ℝ) : ℂ) * spectralUnitary L H t k i j)
        = (fun k : ℝ => ((1/(Real.pi*(1+k^2)) : ℝ) : ℂ) *
            hamiltonianEvolution ((-H) + k • (-L)) t i j) := by
      funext k; rw [spectralUnitary_eq_hamiltonianEvolution]
    rw [he]; exact hint i j
  · have heq : (∫ k : ℝ, (1/(Real.pi*(1+k^2))) • spectralUnitary L H t k) =
        ∫ k : ℝ, (1/(Real.pi*(1+k^2))) • hamiltonianEvolution ((-H) + k • (-L)) t := by
      simp only [spectralUnitary_eq_hamiltonianEvolution]
    rw [heq, hmain, staticNonunitaryEvolution_neg_neg]

end Qatlib.Papers.KoopmanSim26.SpectralRep
