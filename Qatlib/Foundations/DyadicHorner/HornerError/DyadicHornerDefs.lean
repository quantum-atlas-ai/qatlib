/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
namespace Qatlib.Foundations.DyadicHorner.HornerError
set_option autoImplicit false

structure Result where
  value : ℤ
  additions : ℕ
  multiplications : ℕ
  divisions : ℕ
  peakAbs : ℕ
  deriving DecidableEq

def run (b : ℕ) (x : ℤ) : List ℤ → Result
  | [] => ⟨0,0,0,0,0⟩
  | c::cs =>
    let r := run b x cs
    let v := c + (x*r.value)/(2^b : ℤ)
    ⟨v,r.additions+1,r.multiplications+1,r.divisions+1,
      max r.peakAbs (max c.natAbs (max (x*r.value).natAbs v.natAbs))⟩

noncomputable def realValue (cs : List ℝ) (x : ℝ) : ℝ :=
  cs.foldr (fun c acc => c + x*acc) 0

noncomputable def exactValue (b : ℕ) (x : ℤ) (cs : List ℤ) : ℝ :=
  realValue (cs.map (fun (c : ℤ) => (c:ℝ)/(2^b:ℝ))) ((x:ℝ)/(2^b:ℝ))
end Qatlib.Foundations.DyadicHorner.HornerError
