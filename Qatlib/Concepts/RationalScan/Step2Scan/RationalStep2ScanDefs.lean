/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RationalScan.Step2Scan.MatrixOptimizationAlgorithmsDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths

namespace Qatlib.Concepts.RationalScan.Step2Scan
set_option autoImplicit false
open scoped BigOperators

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

def mass {m γ Nmax M : ℕ} (d : Input m γ Nmax M) (N : Fin Nmax) : ℚ :=
  d.κ * (N.val + 1)

def accepts {m γ Nmax M : ℕ} (d : Input m γ Nmax M)
    (p : Fin γ × Fin Nmax) : Bool :=
  decide (d.estC p.1 p.2 / mass d p.2 - (d.κ + d.ν) ≤
    (∑ j : Fin M, d.estA p.1 p.2 (d.draws p.1 p.2 j)) / (M : ℚ) ∧
    (∑ j : Fin M, d.b (d.draws p.1 p.2 j)) / (M : ℚ) ≤
      d.α / mass d p.2 + d.R * (d.κ + d.ν))

def candidates (γ Nmax : ℕ) : List (Fin γ × Fin Nmax) :=
  (List.finRange γ).flatMap fun k => (List.finRange Nmax).map fun N => (k,N)

structure Result (γ Nmax : ℕ) where
  choice : Option (Fin γ × Fin Nmax)
  visited : ℕ
  deriving DecidableEq

def scan {m γ Nmax M : ℕ} (d : Input m γ Nmax M) :
    List (Fin γ × Fin Nmax) → Result γ Nmax
  | [] => ⟨none,0⟩
  | p :: ps => if accepts d p then ⟨some p,1⟩ else
      let r := scan d ps
      ⟨r.choice,r.visited+1⟩

def run {m γ Nmax M : ℕ} (d : Input m γ Nmax M) : Result γ Nmax :=
  scan d (candidates γ Nmax)

def gibbsCopies {γ Nmax : ℕ} (M : ℕ) (r : Result γ Nmax) : ℕ := M*r.visited

def qDraws {γ Nmax : ℕ} (M : ℕ) (r : Result γ Nmax) : ℕ := M*r.visited

def stateCopies {γ Nmax : ℕ} (M L : ℕ) (r : Result γ Nmax) : ℕ := (M+1)*L*r.visited

end Qatlib.Concepts.RationalScan.Step2Scan
