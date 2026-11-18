/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NoncommHSP98.MainResults.AbelianGen

@[expose] public section

/-!
# Regression instances for the Theorem 1 generation module of [EttingerHoyer1999]

Concrete satisfiable checks on `G = ZMod 2 × ZMod 2` (`AbGroup 2` with both moduli two):

* the Theorem 1 sample count and its power-of-two denominator at `|G| = 4`;
* the assembled Theorem 1 probability bound, instantiated for every subgroup of `G`;
* the uniform law on the trivial subgroup;
* the double annihilator identity and the Fourier Born-law connection, instantiated;
* a satisfiable instance of the Abelian promise interface (the identity oracle
  fulfils the promise for the trivial subgroup).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped BigOperators Classical

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.ExactSimon97.MainResults
open Qatlib.Papers.NoncommHSP98.MainResults

section Z2xZ2

private abbrev m2 : Fin 2 → ℕ := fun _ => 2

private theorem nz2 (i : Fin 2) : NeZero (m2 i) :=
  ZeroLEOneClass.neZero.two (α := ℕ)

attribute [local instance] nz2

private abbrev G2 : Type := AbGroup 2 m2

/-- The ambient group has four elements. -/
example : Fintype.card G2 = 4 := by decide

/-- The Theorem 1 sample count at `|G| = 4` is seven, with denominator at least
`2 * 4 ^ 2`. -/
example : genSampleCount 4 = 7 ∧ 2 * ((4 : ℝ)) ^ 2 ≤ (2 : ℝ) ^ (genSampleCount 4) := by
  refine ⟨by unfold genSampleCount; decide, ?_⟩
  exact two_pow_genSample (by decide)

/-- The uniform law on the trivial subgroup is a point mass at zero. -/
example : (unifOnSub (⊥ : AddSubgroup G2)).prob 0 = 1 := by
  simp [unifOnSub]

/-- The assembled Theorem 1 bound, instantiated for every subgroup of `G = Z2 × Z2`. -/
example (K : AddSubgroup G2) :
    1 - 1 / (Fintype.card G2 : ℝ) ≤
      FinDist.probEvent (L := genSampleCount (Fintype.card G2))
        (unifOnSub (annihilatorGen K))
        (fun hs => annihilatorGen (AddSubgroup.closure (Set.range hs)) = K) :=
  theorem1_abelian_AbGroup K (by decide)

/-- The generation-failure bound instantiated at any subgroup of `G = Z2 × Z2`. -/
example (K : AddSubgroup G2) (l : ℕ) :
    FinDist.probEvent (L := l) (unifOnSub K)
        (fun hs => AddSubgroup.closure (Set.range hs) ≠ K) <
      (Fintype.card ↥K : ℝ) * (1 / 2 : ℝ) ^ l :=
  genFail_lt K l

/-- The double annihilator identity, instantiated. -/
example (K : AddSubgroup G2) : annihilatorGen (annihilatorGen K) = K := annann_eq K

/-- The Fourier Born law of a coset state is the uniform annihilator law, instantiated. -/
example (K : AddSubgroup G2) (s g : G2) :
    BornProb (FG (m := m2) (abelianCosetState K s)) g =
      (unifOnSub (annihilatorGen K)).prob g :=
  fourierBorn_unif K s g

/-- The identity oracle fulfils the Abelian promise for the trivial subgroup, so the
Theorem 1 interface is satisfiable. -/
example : AbelianPromise (⊥ : AddSubgroup G2) (fun g : G2 => (g : G2)) := by
  refine ⟨?_, ?_⟩
  · rintro x y ⟨h, hH, rfl⟩
    have h0 : h = 0 := AddSubgroup.mem_bot.mp hH
    simp [h0]
  · intro x y hxy
    exact ⟨0, AddSubgroup.zero_mem ⊥, by simpa using hxy⟩

end Z2xZ2
