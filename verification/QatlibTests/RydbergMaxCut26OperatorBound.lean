module

public import Qatlib.Papers.RydbergMaxCut26.Resources.OperatorBound

@[expose] public section

set_option autoImplicit false

namespace QatlibTests.RydbergMaxCut26

open Qatlib.Papers.RydbergMaxCut26.Resources
open scoped Matrix.Norms.L2Operator

/-! A concrete two-site consumer keeps the domain nonempty and the off-diagonal coupling visible. -/

/-- The unit envelope bound specializes to a nonzero two-site exchange matrix. -/
theorem two_site_exchange_norm_le_one :
    ‖rydbergExchange (n := 2) (fun _ _ : Fin 2 => (1 / 2 : ℝ))‖ ≤ 1 := by
  have h := rydbergExchange_l2Operator_norm_le 2 (by norm_num)
    (fun _ _ : Fin 2 => (1 / 2 : ℝ)) (1 / 2 : ℝ) (by norm_num)
    (by intro i j hij; norm_num)
  simpa using h

/-- The concrete pair matrix has the expected nonzero exchange entry. -/
theorem two_site_exchange_entry :
    rydbergExchange (n := 2) (fun _ _ : Fin 2 => (1 / 2 : ℝ)) 0 1 = (1 / 2 : ℂ) := by
  norm_num [rydbergExchange]

/-- Equal real pair couplings give the Hermitian two-site exchange operator. -/
theorem two_site_exchange_hermitian :
    (rydbergExchange (n := 2) (fun _ _ : Fin 2 => (1 / 2 : ℝ))).IsHermitian := by
  apply rydbergExchange_isHermitian
  intro i j
  rfl

/-- For two sites separated by at least one unit, unit dipolar strength gives norm at most one. -/
theorem two_site_dipolar_norm_le_one (position : Fin 2 → EuclideanSpace ℝ (Fin 3))
    (hsep : ∀ i j, i ≠ j → 1 ≤ dist (position i) (position j)) :
    ‖rydbergExchange
      (Qatlib.Papers.RydbergMaxCut26.Resources.Dipolar.coupling 1 position)‖ ≤ 1 := by
  simpa using rydbergDipolar_l2Operator_norm_le 2 (by norm_num) 1 position 1 (by norm_num) hsep

end QatlibTests.RydbergMaxCut26
