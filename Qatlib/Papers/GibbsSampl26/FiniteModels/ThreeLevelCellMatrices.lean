/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ExchangeCellFrame

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Literal matrices for the nonparity three-level cell

The projectors use psi=(0,1,2,2i)/3. The full independent-weight spectral
filter is evaluated entry by entry with kernel-checkable arithmetic.
The source table is the original six raw physical Pauli matrices.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelWordDual

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

/-- The original Pauli order is XI, YI, ZI, IX, IY, IZ. -/
def sourceLabel : Fin 6 → Fin 2 × Fin 3 :=
  ![(0,0), (0,1), (0,2), (1,0), (1,1), (1,2)]

def source (k : Fin 6) : Operator 4 :=
  ExchangeCell.proposals (sourceLabel k)

/-- The same nonreal vector as in the analytic cell certificate. -/
def psi : Fin 4 → ℂ := ![0, 1/3, 2/3, 2*Complex.I/3]

def pOne : Operator 4 := !![1,0,0,0; 0,0,0,0; 0,0,0,0; 0,0,0,0]

def pTwo : Operator 4 := fun i j => psi i * star (psi j)

def pZero : Operator 4 := 1 - pOne - pTwo

def projectors : Fin 3 → Operator 4 := ![pZero, pOne, pTwo]

/-- Three independent real off-diagonal spectral filter weights. -/
def weights (r t u : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, (r:ℂ), (t:ℂ); (r:ℂ), 1, (u:ℂ); (t:ℂ), (u:ℂ), 1]

def filtered (r t u : ℝ) (k : Fin 6) : Operator 4 :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    weights r t u i j • (projectors i * source k * projectors j)

local macro "cell_arith" : tactic => `(tactic|
  norm_num [Complex.ext_iff, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.normSq_apply, Complex.conj_re, Complex.conj_im] <;> ring)

/-- Source Label bijective for the stated finite source data. -/
theorem sourceLabel_bijective : Function.Bijective sourceLabel := by decide +kernel

/-- Original source for the stated finite source data. -/
theorem original_source (k : Fin 6) :
    fullPauliFamily 2 (sourceLabel k) = ExchangeCell.liftAlg (source k) :=
  ExchangeCell.original_pauli_table (sourceLabel k)

/-- P Two entries for the stated finite source data. -/
theorem pTwo_entries :
    pTwo = !![0,0,0,0;
      0,1/9,2/9,-2*Complex.I/9;
      0,2/9,4/9,-4*Complex.I/9;
      0,2*Complex.I/9,4*Complex.I/9,4/9] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pTwo, psi] <;> cell_arith

def filteredEntries (r t u : ℂ) : Fin 6 → Operator 4 :=
  ![!![0, -2*r/9 + 2*u/9, 5*r/9 + 4*u/9, 4*Complex.I*r/9 - 4*Complex.I*u/9;
       -2*r/9 + 2*u/9, 0, 4*Complex.I*t/9 - 4*Complex.I/9, 5*t/9 + 4/9;
       5*r/9 + 4*u/9, -4*Complex.I*t/9 + 4*Complex.I/9, 0, 2*t/9 - 2/9;
       -4*Complex.I*r/9 + 4*Complex.I*u/9, 5*t/9 + 4/9, 2*t/9 - 2/9, 0],
    !![0, 2*Complex.I*r/9 - 2*Complex.I*u/9, -5*Complex.I*r/9 - 4*Complex.I*u/9, 4*r/9 - 4*u/9;
       -2*Complex.I*r/9 + 2*Complex.I*u/9, 28*t/81 - 28/81, 20*t/81 - 20/81, -29*Complex.I*t/81 - 52*Complex.I/81;
       5*Complex.I*r/9 + 4*Complex.I*u/9, 20*t/81 - 20/81, 32/81 - 32*t/81, 14*Complex.I*t/81 - 14*Complex.I/81;
       4*r/9 - 4*u/9, 29*Complex.I*t/81 + 52*Complex.I/81, -14*Complex.I*t/81 + 14*Complex.I/81, 4*t/81 - 4/81],
    !![1, 0, 0, 0;
       0, 32*t/81 + 49/81, 28*t/81 - 28/81, -28*Complex.I*t/81 + 28*Complex.I/81;
       0, 28*t/81 - 28/81, -16*t/81 - 65/81, 16*Complex.I*t/81 - 16*Complex.I/81;
       0, 28*Complex.I*t/81 - 28*Complex.I/81, -16*Complex.I*t/81 + 16*Complex.I/81, -16*t/81 - 65/81],
    !![0, 8*r/9 + u/9, -2*r/9 + 2*u/9, 2*Complex.I*r/9 - 2*Complex.I*u/9;
       8*r/9 + u/9, 0, -2*Complex.I*t/9 + 2*Complex.I/9, 2*t/9 - 2/9;
       -2*r/9 + 2*u/9, 2*Complex.I*t/9 - 2*Complex.I/9, 0, 8*t/9 + 1/9;
       -2*Complex.I*r/9 + 2*Complex.I*u/9, 2*t/9 - 2/9, 8*t/9 + 1/9, 0],
    !![0, -8*Complex.I*r/9 - Complex.I*u/9, 2*Complex.I*r/9 - 2*Complex.I*u/9, 2*r/9 - 2*u/9;
       8*Complex.I*r/9 + Complex.I*u/9, 16/81 - 16*t/81, 14/81 - 14*t/81, 14*Complex.I*t/81 - 14*Complex.I/81;
       -2*Complex.I*r/9 + 2*Complex.I*u/9, 14/81 - 14*t/81, 8*t/81 - 8/81, -8*Complex.I*t/81 - 73*Complex.I/81;
       2*r/9 - 2*u/9, -14*Complex.I*t/81 + 14*Complex.I/81, 8*Complex.I*t/81 + 73*Complex.I/81, 8*t/81 - 8/81],
    !![1, 0, 0, 0;
       0, -16*t/81 - 65/81, 4*t/81 - 4/81, 32*Complex.I*t/81 - 32*Complex.I/81;
       0, 4*t/81 - 4/81, 80*t/81 + 1/81, -8*Complex.I*t/81 + 8*Complex.I/81;
       0, -32*Complex.I*t/81 + 32*Complex.I/81, 8*Complex.I*t/81 - 8*Complex.I/81, -64*t/81 - 17/81]]


/-- Filtered eq entries for the stated finite source data. -/
theorem filtered_eq_entries (r t u : ℝ) (k : Fin 6) :
    filtered r t u k = filteredEntries (r:ℂ) (t:ℂ) (u:ℂ) k := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [filtered, weights, projectors, pZero, pOne, pTwo_entries,
      source, sourceLabel, ExchangeCell.proposals, filteredEntries,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul] <;>
    cell_arith


end

end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelWordDual
