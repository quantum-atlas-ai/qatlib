/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.QuditF1024
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Theorem51

open Matrix
open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Parameters `(n, k, d, t)` of one code in the family of Theorem 5.1: block size,
logical qudits, `Z`-distance, decoding radius. -/
structure CodeParams where
  n : ℕ
  k : ℕ
  d : ℕ
  t : ℕ

/-- `f = Θ(n)` with positive implicit constants. -/
def ThetaLinear (n f : ℕ → ℕ) : Prop :=
  ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ (∀ i, 0 < n i) ∧
    (∀ i, c1 * (n i : ℝ) ≤ (f i : ℝ)) ∧ (∀ i, (f i : ℝ) ≤ c2 * (n i : ℝ))

/-- The non-Clifford third-level transversal gate `U = U_1^{(7)}` of Theorem 5.1:
in exactly the third level of the Clifford hierarchy. -/
def ThirdLevelGate (U : Matrix F1024 F1024 ℂ) : Prop :=
  InQuditThirdLevel U ∧ ¬ IsQuditClifford U

/-- Poly-time `Z`-decoder of radius `t` for the family `F` (abstracted as
`t = Θ(n)`; the algorithmic decoder is not modelled). -/
def PolyTimeDecoder (F : ℕ → CodeParams) (t : ℕ → ℕ) : Prop :=
  ThetaLinear (fun i => (F i).n) t

/-- Fixed arXiv:2408.07764v2, Theorem 5.1, arithmetic kernel (pp.36–37,
Eqs (199), (202), (203)): hypothesis (199) `k ≤ a - 3g - 1` and `k > 0` force the
distance lower bound (202) to be strictly positive and the decoder-radius range (203)
to be nonempty (`t = 1` admissible). Proven outright. -/
theorem theorem_5_1_param_arithmetic (g a k : ℕ)
    (_hk : 0 < k) (h199 : (k : ℤ) ≤ (a : ℤ) - 3 * (g : ℤ) - 1) :
    (0 : ℤ) < (a : ℤ) - (k : ℤ) - (2 * (g : ℤ) - 2)
      ∧ ∃ t : ℕ, 0 < t
          ∧ 2 * (t : ℤ) ≤ (a : ℤ) - (k : ℤ) - (2 * (g : ℤ) - 2) - (g : ℤ) - 1 := by
  refine ⟨by omega, 1, by norm_num, by omega⟩

end Qatlib.Papers.MagicDistill24.MainResults.Theorem51
