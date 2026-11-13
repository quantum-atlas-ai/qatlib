/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RationalScan.Step2Scan.MatrixOptimizationAlgorithmsDefs

/-!
# Rational Step 2 scan data

This module defines finite rational input tables, a decidable acceptance test, and a row-major
search for the first accepted Step 2 candidate. `Result` records both the selected pair and the
number of visited pairs, allowing copy and draw counts to be computed from the same run. These
definitions support the SDP sampling framework of [BrandaoSvore2017].

## Main definitions

* `Input` and `accepts`: rational tables and the two acceptance inequalities.
* `candidates`, `scan`, and `run`: row-major first-success search.
* `gibbsCopies`, `qDraws`, and `stateCopies`: resource counts from the visited count.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths

namespace Qatlib.Concepts.RationalScan.Step2Scan
set_option autoImplicit false
open scoped BigOperators

/-- The rational bounds, sampling-law tables, draws, estimates, and scalar parameters used by
the finite Step 2 scan. -/
structure Input (m γ Nmax M : ℕ) where
  b : Fin m → ℚ
  law : Fin γ → Fin m → ℚ
  draws : Fin γ → Fin Nmax → Fin M → Fin m
  estA : Fin γ → Fin Nmax → Fin m → ℚ
  estC : Fin γ → Fin Nmax → ℚ
  α : ℚ
  R : ℚ
  κ : ℚ
  ν : ℚ

/-- The rational mass-grid value `d.κ*(N.val+1)`. -/
def mass {m γ Nmax M : ℕ} (d : Input m γ Nmax M) (N : Fin Nmax) : ℚ :=
  d.κ * (N.val + 1)

/-- The Boolean decision of the empirical separation and objective acceptance inequalities for a
candidate pair. -/
def accepts {m γ Nmax M : ℕ} (d : Input m γ Nmax M)
    (p : Fin γ × Fin Nmax) : Bool :=
  decide (d.estC p.1 p.2 / mass d p.2 - (d.κ + d.ν) ≤
    (∑ j : Fin M, d.estA p.1 p.2 (d.draws p.1 p.2 j)) / (M : ℚ) ∧
    (∑ j : Fin M, d.b (d.draws p.1 p.2 j)) / (M : ℚ) ≤
      d.α / mass d p.2 + d.R * (d.κ + d.ν))

/-- All candidate pairs in row-major order, with the outer index preceding the mass-grid index. -/
def candidates (γ Nmax : ℕ) : List (Fin γ × Fin Nmax) :=
  (List.finRange γ).flatMap fun k => (List.finRange Nmax).map fun N => (k,N)

/-- The optional selected candidate pair and the number of pairs visited by a scan. -/
structure Result (γ Nmax : ℕ) where
  choice : Option (Fin γ × Fin Nmax)
  visited : ℕ
  deriving DecidableEq

/-- The recursive first-success scan, counting every tested candidate and returning no choice
after exhausting the list. -/
def scan {m γ Nmax M : ℕ} (d : Input m γ Nmax M) :
    List (Fin γ × Fin Nmax) → Result γ Nmax
  | [] => ⟨none,0⟩
  | p :: ps => if accepts d p then ⟨some p,1⟩ else
      let r := scan d ps
      ⟨r.choice,r.visited+1⟩

/-- The scan of all candidate pairs in row-major order. -/
def run {m γ Nmax M : ℕ} (d : Input m γ Nmax M) : Result γ Nmax :=
  scan d (candidates γ Nmax)

/-- The Gibbs-copy count `M*r.visited` attached to a scan result. -/
def gibbsCopies {γ Nmax : ℕ} (M : ℕ) (r : Result γ Nmax) : ℕ := M*r.visited

/-- The sampling-law draw count `M*r.visited` attached to a scan result. -/
def qDraws {γ Nmax : ℕ} (M : ℕ) (r : Result γ Nmax) : ℕ := M*r.visited

/-- The state-copy count `(M+1)*L*r.visited` attached to a scan result. -/
def stateCopies {γ Nmax : ℕ} (M L : ℕ) (r : Result γ Nmax) : ℕ := (M+1)*L*r.visited

end Qatlib.Concepts.RationalScan.Step2Scan
