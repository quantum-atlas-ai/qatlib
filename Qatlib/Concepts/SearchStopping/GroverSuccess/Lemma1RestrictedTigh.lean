/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.GroverSuccess.Lemma1RestrictedStat
import Qatlib.Concepts.LchsSimulation.StaticLchs.FiniteTrigonometricSums
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib

namespace Qatlib.Concepts.SearchStopping.GroverSuccess

open scoped BigOperators

theorem lemma1_cosine_sum_mul (α β : ℝ) (m : ℕ) :
    Real.sin β * (∑ j ∈ Finset.range m, Real.cos (α + 2 * β * j)) =
      Real.sin (m * β) * Real.cos (α + ((m : ℝ) - 1) * β) :=
  cosine_arithmetic_sum_mul α β m

theorem lemma1_cosine_sum (α β : ℝ) (m : ℕ) (hβ : Real.sin β ≠ 0) :
    (∑ j ∈ Finset.range m, Real.cos (α + 2 * β * j)) =
      Real.sin (m * β) * Real.cos (α + ((m : ℝ) - 1) * β) / Real.sin β :=
  cosine_arithmetic_sum α β m hβ

theorem lemma1_odd_cosine_sum_mul (α : ℝ) (m : ℕ) :
    (2 * Real.sin α) * (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * α)) =
      Real.sin (2 * m * α) :=
  cosine_odd_sum_mul α m

theorem lemma1_odd_cosine_sum (α : ℝ) (m : ℕ) (hα : Real.sin α ≠ 0) :
    (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * α)) =
      Real.sin (2 * m * α) / (2 * Real.sin α) :=
  cosine_odd_sum α m hα

theorem lemma1Restricted : Lemma1Restricted :=
  ⟨fun α β m _ hβ => lemma1_cosine_sum α β m hβ,
    fun α m _ hα => lemma1_odd_cosine_sum α m hα⟩

end Qatlib.Concepts.SearchStopping.GroverSuccess
