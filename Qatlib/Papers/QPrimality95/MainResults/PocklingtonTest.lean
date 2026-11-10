/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PrimalityCerts.LucasTests.LucasWitnesses
import Qatlib.Papers.QPrimality95.MainResults.CostDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPrimality95.MainResults

open scoped BigOperators

theorem pocklington_lehmer_sound
    (N : ℕ) (a : ZMod N) (S : Finset ℕ)
    (_hSprime : ∀ p ∈ S, p.Prime)
    (hScover : ∀ q : ℕ, q.Prime → q ∣ N - 1 → q ∈ S)
    (ha : a ^ (N - 1) = 1)
    (hd : ∀ p ∈ S, a ^ ((N - 1) / p) ≠ 1) :
    N.Prime :=
  lucas_primality N a ha (fun q hq hqd => hd q (hScover q hq hqd))

theorem pocklington_lehmer_separate_sound (N : ℕ) (S : Finset ℕ)
    (hcover : ∀ q : ℕ, q.Prime → q ∣ N - 1 → q ∈ S)
    (hw : ∀ q ∈ S, ∃ a : ZMod N,
      a ^ (N - 1) = 1 ∧ a ^ ((N - 1) / q) ≠ 1) : N.Prime :=
  Qatlib.Foundations.PrimalityCerts.LucasTests.separateLucas N
    (fun q hq hqd => hw q (hcover q hq hqd))

theorem pocklington_lehmer_factorization_sound (N : ℕ) (S : Finset ℕ) (β : ℕ → ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hfactor : N - 1 = ∏ p ∈ S, p ^ β p)
    (hw : ∀ p ∈ S, ∃ a : ZMod N,
      a ^ (N - 1) = 1 ∧ a ^ ((N - 1) / p) ≠ 1) : N.Prime :=
  Qatlib.Foundations.PrimalityCerts.LucasTests.separateLucasProduct N S β hprime hfactor hw

theorem pocklington_lehmer_product_sound (N : ℕ) (S : Finset ℕ) (β : ℕ → ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hfactor : N - 1 = ∏ p ∈ S, p ^ β p)
    (a : ZMod N) (ha : a ^ (N - 1) = 1)
    (hd : ∀ p ∈ S, a ^ ((N - 1) / p) ≠ 1) : N.Prime :=
  pocklington_lehmer_factorization_sound N S β hprime hfactor
    (fun p hp => ⟨a, ha, hd p hp⟩)

theorem total_cost_bound_of_subroutine_bounds
    (factCost verifyCost : ℕ → ℝ) (Cf Cv : ℝ)
    (hCpos : 0 < Cf + Cv)
    (hfact : ∀ N : ℕ, 3 ≤ N → factCost N ≤ Cf * mainCost N)
    (hverify : ∀ N : ℕ, 3 ≤ N → verifyCost N ≤ Cv * mainCost N) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      factCost N + verifyCost N ≤ C * mainCost N := by
  refine ⟨Cf + Cv, hCpos, ?_⟩
  intro N hN
  calc
    factCost N + verifyCost N ≤ Cf * mainCost N + Cv * mainCost N :=
      add_le_add (hfact N hN) (hverify N hN)
    _ = (Cf + Cv) * mainCost N := by ring

end Qatlib.Papers.QPrimality95.MainResults
