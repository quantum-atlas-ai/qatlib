module

public import Qatlib.Papers.QWalkAmbainis03.GroverInterp.EuclideanClaim5

@[expose] public section

/-!
# Consumer regression for the Euclidean Claim 5 increment

This ordinary-module consumer fixes `ε = 1` and `α = 1 / 400` in three
dimensions, where the orthogonal complement of the start vector can carry
a real quarter-turn with eigenvalues `±i`. The secular root is obtained from
the reflection model via Claim 4.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QatlibTests.QWalkAmbainis03EuclideanClaim5Regression

open Qatlib.Concepts.WalkFind.GroverInterp
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.QWalkAmbainis03.GroverInterp.EuclideanClaim5
open Matrix

/-- A three-dimensional consumer of `claim5_euclidean_resolvent_bound`
with a uniform constant and a secular root obtained from the given reflection. -/
theorem three_level_claim5_euclidean_bound :
    ∃ uniformConstant : ℝ, 0 < uniformConstant ∧
      ∀ (Uf U : Matrix (Fin 3) (Fin 3) ℂ) (start good : Fin 3 → ℂ),
        star U * U = 1 →
        (∀ i j, (U i j).im = 0) →
        (∀ i, (start i).im = 0) →
        (∀ i, (good i).im = 0) →
        (∑ i, ‖start i‖ ^ 2) = 1 →
        (∑ i, ‖good i‖ ^ 2) = 1 →
        (∑ i, star (good i) * start i) = ((1 / 400 : ℝ) : ℂ) →
        U *ᵥ start = start →
        Uf *ᵥ good = -good →
        (∀ v : Fin 3 → ℂ, (∑ i, star (v i) * good i) = 0 → Uf *ᵥ v = v) →
        (∀ (ν : ℂ) (v : Fin 3 → ℂ), U *ᵥ v = ν • v →
          (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
          ∃ θ : ℝ, 1 ≤ θ ∧ θ ≤ 2 * Real.pi - 1 ∧ θ ≠ Real.pi ∧
            ν = Complex.exp (Complex.I * θ)) →
        ∃ β ∈ Set.Icc ((1 : ℝ) * (1 / 400) / Real.sqrt (2 * Real.pi))
            ((13 / 5 : ℝ) * (1 / 400)),
          let y := (U - Complex.exp (Complex.I * β) •
            (1 : Matrix (Fin 3) (Fin 3) ℂ))⁻¹ *ᵥ (U *ᵥ good)
          let coefficient := (1 / 400 : ℝ) * Real.sin β / (2 * (1 - Real.cos β))
          let imaginaryResolvent : EuclideanSpace ℂ (Fin 3) :=
            toEuclidean_fromVec (fun i => ((y i).im : ℂ))
          let euclideanStart : EuclideanSpace ℂ (Fin 3) :=
            toEuclidean_fromVec start
          let residual : EuclideanSpace ℂ (Fin 3) :=
            toEuclidean_fromVec (fun i => ((y i).im : ℂ) - (coefficient : ℂ) * start i)
          groverSecularScalar 3 U good β = 0 ∧
            imaginaryResolvent = coefficient • euclideanStart + residual ∧
            0 < coefficient ∧
            ‖imaginaryResolvent‖ ≤ uniformConstant / 1 ∧
            ‖residual‖ ≤ 2 * β / 1 * coefficient := by
  obtain ⟨uniformConstant, hpositive, hmodel⟩ := claim5_euclidean_resolvent_bound
  refine ⟨uniformConstant, hpositive, ?_⟩
  intro Uf U start good hu hU hsr hgr hsn hgn hoverlap hstart hgood hfix hphase
  obtain ⟨β, hβbounds, hroot, _⟩ := grover_small_overlap_root 3 1 (1 / 400)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Uf U start good hu hU hgr hsn hgn hoverlap hstart hgood hfix hphase
  exact ⟨β, hβbounds, hroot, hmodel 3 1 (1 / 400) β
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hβbounds
    U start good hu hU hsr hgr hsn hgn hoverlap hstart hphase hroot⟩

end QatlibTests.QWalkAmbainis03EuclideanClaim5Regression
