/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.LowerBound.LocalMomentContracts
import Qatlib.Papers.ClassShadows20.LowerBound.LocalShotPauliMomentSubgoalStat
import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
import Qatlib.Papers.ClassShadows20.LowerBound.LocalProductMoments
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
namespace Qatlib.Papers.ClassShadows20.LowerBound
open Matrix
open scoped Classical BigOperators

theorem no_local_real_second_moment_ensemble {J : Type} [Fintype J]
    (κ : FinDist J) (Uf : J → Operator 2) :
    ¬ (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re *
          (Matrix.trace (B * (Uf j)ᴴ * Pp * Uf j)).re =
        ((Matrix.trace A).re * (Matrix.trace B).re +
          (Matrix.trace (A * B)).re) / 6) :=
  qubit_real_second_moment_impossible κ.prob Uf

end Qatlib.Papers.ClassShadows20.LowerBound

namespace Qatlib.Papers.ClassShadows20.LowerBound.HuangKuengPreskill2020
open Matrix
open scoped Classical BigOperators

theorem local_wire_pauli_moments {J : Type} [Fintype J]
    (κ : FinDist J) (Uf : J → Operator 2)
    (hκ1 : ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re =
        (Matrix.trace A).re / 2)
    (hκ2 : ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
      A.IsHermitian → B.IsHermitian →
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re *
          (Matrix.trace (B * (Uf j)ᴴ * Pp * Uf j)).re =
        ((Matrix.trace A).re * (Matrix.trace B).re +
          (Matrix.trace (A * B)).re) / 6)
    (Pp : Operator 2) (hPp : IsPureDensityOperator Pp) (a : Fin 3) :
    (∑ j, κ.prob j * (Matrix.trace (pauliMatrix a * (Uf j)ᴴ * Pp * Uf j)).re = 0) ∧
    (∑ j, κ.prob j * (Matrix.trace (pauliMatrix a * (Uf j)ᴴ * Pp * Uf j)).re ^ 2 = 1/3) := by
  have hmean := hκ1 Pp hPp (pauliMatrix a)
  have hherm : (pauliMatrix a).IsHermitian := pauliMatrix_conjTranspose a
  have hsecond := hκ2 Pp hPp (pauliMatrix a) (pauliMatrix a) hherm hherm
  constructor
  · simpa only [trace_pauliMatrix, Complex.zero_re, zero_div] using hmean
  · norm_num [trace_pauliMatrix, pauliMatrix_mul_self, Matrix.trace_one, pow_two,
      mul_assoc] at hsecond ⊢
    exact hsecond
end Qatlib.Papers.ClassShadows20.LowerBound.HuangKuengPreskill2020

namespace Qatlib.Papers.ClassShadows20.LowerBound.HuangKuengPreskill2020
open Matrix
open scoped Classical BigOperators

theorem localShotPauliMomentSubgoal : LocalShotPauliMomentSubgoal := by
  intro n k J _ _ κ Uf hκU hκ1 hκ2 w _hw ψ hψ a hk hS ε _hε _hε1
  have hwire := fun j b => local_wire_pauli_moments κ Uf hκ1 hκ2 (ψ j) (hψ j) b
  have hm := localPauliOverlap_product_moments κ Uf ψ a hk hS
    (fun j b => (hwire j b).1) (fun j b => (hwire j b).2)
  let Z : (Fin n → J) → ℝ := fun uw => ∏ j, localPauliOverlap Uf (ψ j) (a j) (uw j)
  have haff := local_affine_moments κ.probOf Z k (κ.sum_probOf n) hm.1 hm.2 w ε
  have hpoint : ∀ uw, κ.probOf uw ≠ 0 →
      localShotValue Uf w ψ uw (theorem6CodeState n ε a) = w * (1 + 3 * ε * Z uw) := by
    intro uw hpos
    apply localShotValue_factor Uf w ψ uw hψ
    intro j
    apply hκU
    have hj : κ.prob (uw j) ≠ 0 := by
      intro hz
      apply hpos
      exact Finset.prod_eq_zero (Finset.mem_univ j) hz
    exact lt_of_le_of_ne (κ.nonneg _) (Ne.symm hj)
  have hfirst : (∑ uw, κ.probOf uw * localShotValue Uf w ψ uw (theorem6CodeState n ε a)) =
      ∑ uw, κ.probOf uw * (w * (1 + 3 * ε * Z uw)) := by
    apply Finset.sum_congr rfl
    intro uw _
    by_cases hp : κ.probOf uw = 0
    · simp [hp]
    · rw [hpoint uw hp]
  have hsecond : (∑ uw, κ.probOf uw * (localShotValue Uf w ψ uw (theorem6CodeState n ε a))^2) =
      ∑ uw, κ.probOf uw * (w * (1 + 3 * ε * Z uw))^2 := by
    apply Finset.sum_congr rfl
    intro uw _
    by_cases hp : κ.probOf uw = 0
    · simp [hp]
    · rw [hpoint uw hp]
  constructor
  · exact hfirst.trans haff.1
  · exact le_of_eq (hsecond.trans haff.2)
end Qatlib.Papers.ClassShadows20.LowerBound.HuangKuengPreskill2020
