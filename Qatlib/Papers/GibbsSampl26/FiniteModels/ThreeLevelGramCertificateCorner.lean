/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelGramCertificate
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCellMatrices
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClusterColumns
public import Mathlib.Tactic.FinCases

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Complete literal scalar-corner Gram sandwich

The 96 rows are the six original Pauli commutators, flattened in row-major
order. The 15 input columns are P1+P2, P2 and the fixed thirteen-column fast
basis F. Exact kernel checks bind every source row, the F*F metric, and both
coefficient identities to the complete literal positivity certificates.
This is the scalar corner; no continuum Bernstein positivity is asserted.
-/

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelGramCertificateCorner

open Matrix ThreeLevelGramCertificate
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option Elab.async false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000


def sourceReal : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 1, 0;
    0, 0, 0, 1;
    1, 0, 0, 0;
    0, 1, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, (-1), 0;
    0, 0, 0, (-1)],
    !![0, 1, 0, 0;
    1, 0, 0, 0;
    0, 0, 0, 1;
    0, 0, 1, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![1, 0, 0, 0;
    0, (-1), 0, 0;
    0, 0, 1, 0;
    0, 0, 0, (-1)]]

def sourceImag : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, (-1), 0;
    0, 0, 0, (-1);
    1, 0, 0, 0;
    0, 1, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![0, (-1), 0, 0;
    1, 0, 0, 0;
    0, 0, 0, (-1);
    0, 0, 1, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]]

def inputReal : Matrix (Fin 16) (Fin 15) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (1/9), (1/9), 0, 0, 0, 0, (16/27), (2/27), 0, 0, (2/27), (-8/27), 0, 0, 0;
    (2/9), (2/9), 0, 0, 0, 0, (2/27), (25/27), 0, 0, (-2/27), (-1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (25/27), 0, 0, 0, (-4/27), 0, (2/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    (2/9), (2/9), 0, 0, 0, 0, (2/27), (-2/27), 0, 0, (25/27), (-1/27), 0, 0, 0;
    (4/9), (4/9), 0, 0, 0, 0, (-8/27), (-1/27), 0, 0, (-1/27), (35/54), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-4/27), 0, 0, 0, (19/27), 0, (4/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (25/27);
    0, 0, 0, 0, 0, 0, 0, 0, (4/27), 0, 0, 0, (8/27), 0, (-4/27);
    (4/9), (4/9), 0, 0, 0, 0, (-8/27), (-1/27), 0, 0, (-1/27), (-19/54), 0, 0, 0]

def inputImag : Matrix (Fin 16) (Fin 15) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    (-2/9), (-2/9), 0, 0, 0, 0, (-2/27), (2/27), 0, 0, (2/27), (1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    0, 0, 0, 0, 0, 0, 0, 0, (-1/27), 0, 0, 0, (-2/27), 0, (1/27);
    (-4/9), (-4/9), 0, 0, 0, 0, (-4/27), (4/27), 0, 0, (4/27), (2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (2/9), (2/9), 0, 0, 0, 0, (2/27), (-2/27), 0, 0, (-2/27), (-1/27), 0, 0, 0;
    (4/9), (4/9), 0, 0, 0, 0, (4/27), (-4/27), 0, 0, (-4/27), (-2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-1/27), 0, 0, 0, (-2/27), 0, (1/27)]

def stackReal : Matrix (Fin 96) (Fin 15) ℚ :=
  !![0, 0, 0, (-1), 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    (2/9), (2/9), 0, 0, (-1), 0, (2/27), (-2/27), 0, 0, (25/27), (-1/27), 0, 0, 0;
    (-5/9), (4/9), 0, 0, 0, 0, (-8/27), (-1/27), 0, 0, (-1/27), (35/54), 0, 0, 0;
    0, 0, (-1), 0, 0, 0, 0, 0, (-4/27), 0, 0, 0, (19/27), 0, (4/27);
    (-2/9), (-2/9), 0, 0, 0, 0, (-2/27), (-25/27), 0, 0, (2/27), (1/27), 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-23/27), 0, 0, 0, (8/27), 0, (23/27);
    0, 0, 0, 0, 0, (-1), 0, 0, (4/27), 0, 0, 0, (8/27), 0, (-4/27);
    (1/3), (1/3), 0, 0, 0, 0, (-8/9), (-1/9), 0, 0, (-1/9), (-1/18), 0, 0, 0;
    (5/9), (-4/9), 0, 0, 0, 0, (8/27), (1/27), 0, 0, (1/27), (-35/54), 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, (4/27), 0, 0, 0, (-19/27), 0, (-4/27);
    0, 0, 0, 1, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0;
    (-2/9), (-2/9), 0, 0, 1, 0, (-2/27), (2/27), 0, 0, (-25/27), (1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, (-4/27), 0, 0, 0, (-8/27), 0, (4/27);
    (-1/3), (-1/3), 0, 0, 0, 0, (8/9), (1/9), 0, 0, (1/9), (1/18), 0, 0, 0;
    (2/9), (2/9), 0, 0, 0, 0, (2/27), (25/27), 0, 0, (-2/27), (-1/27), 0, (-1), 0;
    0, 0, 0, 0, 0, 0, 0, 0, (23/27), 0, 0, 0, (-8/27), 0, (-23/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    0, 0, 0, 0, 0, 0, 0, 0, (-1/27), 0, 0, 0, (-2/27), 0, (1/27);
    (-4/9), (-4/9), 0, 0, 0, 0, (-4/27), (4/27), 0, 0, (4/27), (2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (4/9), (4/9), 0, 0, 0, 0, (4/27), (-4/27), 0, 0, (-4/27), (-2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-1/9), 0, 0, 0, (-2/9), 0, (1/9);
    0, 0, 0, 0, 0, 0, 0, 0, (-1/27), 0, 0, 0, (-2/27), 0, (1/27);
    (-4/9), (-4/9), 0, 0, 0, 0, (-4/27), (4/27), 0, 0, (4/27), (2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    (4/9), (4/9), 0, 0, 0, 0, (4/27), (-4/27), 0, 0, (-4/27), (-2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-1/9), 0, 0, 0, (-2/9), 0, (1/9);
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (4/9), (4/9), 0, 0, 0, 0, (4/27), (50/27), 0, 0, (-4/27), (-2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (50/27), 0, 0, 0, (-8/27), 0, (4/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, (-2), 0, 0, 0, 0, 0;
    (-4/9), (-4/9), 0, 0, 0, 0, (-4/27), (4/27), 0, 0, (-50/27), (2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-2), 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-4/27), 0, 0, 0, (-8/27), 0, (-50/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, (-1), 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-8/9), (1/9), 0, 0, 0, 0, (16/27), (2/27), 0, 0, (2/27), (-8/27), 0, 0, 0;
    (2/9), (2/9), 0, 0, (-1), 0, (2/27), (25/27), 0, 0, (-2/27), (-1/27), 0, 0, 0;
    0, 0, 0, (-1), 0, 0, 0, 0, (25/27), 0, 0, 0, (-4/27), 0, (2/27);
    (8/9), (-1/9), 0, 0, 0, 0, (-16/27), (-2/27), 0, 0, (-2/27), (8/27), 0, 0, 0;
    0, 0, 1, 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, (-25/27), 0, 0, 0, (4/27), 0, (-2/27);
    (-2/9), (-2/9), 0, 0, 1, 0, (-2/27), (-25/27), 0, 0, (2/27), (1/27), 0, 0, 0;
    (-2/9), (-2/9), 0, 0, 0, 0, (-2/27), (2/27), 0, 0, (-25/27), (1/27), 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), (-1), 0, 0, (4/27), 0, (25/27);
    0, 0, 0, 0, 0, 0, 0, 0, (8/27), 0, 0, 0, (-11/27), 0, (-8/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 1, 0, 0, (-4/27), 0, (-25/27);
    (2/9), (2/9), 0, 0, 0, 0, (2/27), (-2/27), 0, 0, (25/27), (-1/27), 0, (-1), 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-8/27), 0, 0, 0, (11/27), 0, (8/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    (-2/9), (-2/9), 0, 0, 0, 0, (-2/27), (2/27), 0, 0, (2/27), (1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-2/9), (-2/9), 0, 0, 0, 0, (-2/27), (2/27), 0, 0, (2/27), (1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    (2/9), (2/9), 0, 0, 0, 0, (2/27), (-2/27), 0, 0, (-2/27), (-1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (2/9), (2/9), 0, 0, 0, 0, (2/27), (-2/27), 0, 0, (-2/27), (-1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, (-2), 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-4/9), (-4/9), 0, 0, 0, 0, (-4/27), (-50/27), 0, 0, (4/27), (2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (4/9), (4/9), 0, 0, 0, 0, (4/27), (-4/27), 0, 0, (50/27), (-2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-8/27), 0, 0, 0, (38/27), 0, (8/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-2), 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-8/27), 0, 0, 0, (-16/27), 0, (8/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def stackImag : Matrix (Fin 96) (Fin 15) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    0, 0, 0, 0, 0, 0, 0, 0, (-1/27), 0, 0, 0, (-2/27), 0, (1/27);
    (-4/9), (-4/9), 0, 0, 0, 0, (-4/27), (4/27), 0, 0, (4/27), (2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    (4/9), (4/9), 0, 0, 0, 0, (4/27), (-4/27), 0, 0, (-4/27), (-2/27), 0, 0, 0;
    (4/9), (4/9), 0, 0, 0, 0, (4/27), (-4/27), 0, 0, (-4/27), (-2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-1/9), 0, 0, 0, (-2/9), 0, (1/9);
    0, 0, 0, 0, 0, 0, 0, 0, (1/27), 0, 0, 0, (2/27), 0, (-1/27);
    (4/9), (4/9), 0, 0, 0, 0, (4/27), (-4/27), 0, 0, (-4/27), (-2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    (-4/9), (-4/9), 0, 0, 0, 0, (-4/27), (4/27), 0, 0, (4/27), (2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (1/9), 0, 0, 0, (2/9), 0, (-1/9);
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    (-4/9), (-4/9), 0, 0, 0, 0, (-4/27), (4/27), 0, 0, (4/27), (2/27), 0, 0, 0;
    0, 0, 0, (-1), 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0;
    (-2/9), (-2/9), 0, 0, (-1), 0, (-2/27), (2/27), 0, 0, (-25/27), (1/27), 0, 0, 0;
    (5/9), (-4/9), 0, 0, 0, 0, (8/27), (1/27), 0, 0, (1/27), (-35/54), 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, (4/27), 0, 0, 0, (-19/27), 0, (-4/27);
    (-2/9), (-2/9), 0, 0, 0, 0, (-2/27), (-25/27), 0, 0, (2/27), (1/27), 0, (-1), 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, (-1);
    0, 0, 0, 0, 0, 1, 0, 0, (-4/27), 0, 0, 0, (-8/27), 0, (4/27);
    (-1/3), (-1/3), 0, 0, 0, 0, (8/9), (1/9), 0, 0, (1/9), (1/18), 0, 0, 0;
    (5/9), (-4/9), 0, 0, 0, 0, (8/27), (1/27), 0, 0, (1/27), (-35/54), 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, (4/27), 0, 0, 0, (-19/27), 0, (-4/27);
    0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    (2/9), (2/9), 0, 0, 1, 0, (2/27), (-2/27), 0, 0, (25/27), (-1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, (-4/27), 0, 0, 0, (-8/27), 0, (4/27);
    (-1/3), (-1/3), 0, 0, 0, 0, (8/9), (1/9), 0, 0, (1/9), (1/18), 0, 0, 0;
    (2/9), (2/9), 0, 0, 0, 0, (2/27), (25/27), 0, 0, (-2/27), (-1/27), 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-4/27), 0, 0, 0, (-8/27), 0, (4/27);
    (-4/9), (-4/9), 0, 0, 0, 0, (-4/27), (4/27), 0, 0, (4/27), (2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (4/27), 0, 0, 0, (8/27), 0, (-4/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-4/9), (-4/9), 0, 0, 0, 0, (-4/27), (4/27), 0, 0, (4/27), (2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    (-2/9), (-2/9), 0, 0, 0, 0, (-2/27), (2/27), 0, 0, (2/27), (1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (2/9), (2/9), 0, 0, 0, 0, (2/27), (-2/27), 0, 0, (-2/27), (-1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    (2/9), (2/9), 0, 0, 0, 0, (2/27), (-2/27), 0, 0, (-2/27), (-1/27), 0, 0, 0;
    (8/9), (8/9), 0, 0, 0, 0, (8/27), (-8/27), 0, 0, (-8/27), (-4/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-2/9), (-2/9), 0, 0, 0, 0, (-2/27), (2/27), 0, 0, (2/27), (1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-8/9), (-8/9), 0, 0, 0, 0, (-8/27), (8/27), 0, 0, (8/27), (4/27), 0, 0, 0;
    0, 0, (-1), 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (8/9), (-1/9), 0, 0, 0, 0, (-16/27), (-2/27), 0, 0, (-2/27), (8/27), 0, 0, 0;
    (-2/9), (-2/9), 0, 0, (-1), 0, (-2/27), (-25/27), 0, 0, (2/27), (1/27), 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, (-25/27), 0, 0, 0, (4/27), 0, (-2/27);
    (8/9), (-1/9), 0, 0, 0, 0, (-16/27), (-2/27), 0, 0, (-2/27), (8/27), 0, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, (-25/27), 0, 0, 0, (4/27), 0, (-2/27);
    (2/9), (2/9), 0, 0, 1, 0, (2/27), (25/27), 0, 0, (-2/27), (-1/27), 0, 0, 0;
    (-2/9), (-2/9), 0, 0, 0, 0, (-2/27), (2/27), 0, 0, (-25/27), (1/27), 0, (-1), 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 1, 0, 0, (-4/27), 0, (-25/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 1, 0, 0, (-4/27), 0, (-25/27);
    (2/9), (2/9), 0, 0, 0, 0, (2/27), (-2/27), 0, 0, (25/27), (-1/27), 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (4/27), 0, 0, 0, (8/27), 0, (-4/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-4/27), 0, 0, 0, (-8/27), 0, (4/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-8/9), (-8/9), 0, 0, 0, 0, (-8/27), (8/27), 0, 0, (8/27), (4/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-8/9), (-8/9), 0, 0, 0, 0, (-8/27), (8/27), 0, 0, (8/27), (4/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def metricReal : Matrix (Fin 15) (Fin 15) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, (16/27), (2/27), 0, 0, (2/27), (-8/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, (2/27), (25/27), 0, 0, (-2/27), (-1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (25/27), 0, 0, 0, (-4/27), 0, (2/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, (2/27), (-2/27), 0, 0, (25/27), (-1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, (-8/27), (-1/27), 0, 0, (-1/27), (35/54), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-4/27), 0, 0, 0, (19/27), 0, (4/27);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (25/27)]

def metricImag : Matrix (Fin 15) (Fin 15) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (2/27), 0, 0, 0, (4/27), 0, (-2/27);
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    0, 0, 0, 0, 0, 0, (-2/27), (2/27), 0, 0, (2/27), (1/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-2/27), 0, 0, 0, (-4/27), 0, (2/27);
    0, 0, 0, 0, 0, 0, 0, 0, (-1/27), 0, 0, 0, (-2/27), 0, (1/27);
    0, 0, 0, 0, 0, 0, (-4/27), (4/27), 0, 0, (4/27), (2/27), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, (2/27), (-2/27), 0, 0, (-2/27), (-1/27), 0, 0, 0]

def flatIndex (i j : Fin 4) : Fin 16 := ⟨4 * i.val + j.val, by omega⟩
def sourceIndex (a : Fin 96) : Fin 6 := ⟨a.val / 16, by omega⟩
def rowIndex (a : Fin 96) : Fin 4 := ⟨a.val % 16 / 4, by omega⟩
def columnIndex (a : Fin 96) : Fin 4 := ⟨a.val % 4, by omega⟩

def inputMatrixReal (c : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => inputReal (flatIndex i j) c

def inputMatrixImag (c : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => inputImag (flatIndex i j) c

def commutatorReal (a : Fin 6) (c : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  (sourceReal a * inputMatrixReal c - sourceImag a * inputMatrixImag c) -
    (inputMatrixReal c * sourceReal a - inputMatrixImag c * sourceImag a)

def commutatorImag (a : Fin 6) (c : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  (sourceReal a * inputMatrixImag c + sourceImag a * inputMatrixReal c) -
    (inputMatrixReal c * sourceImag a + inputMatrixImag c * sourceReal a)

/-- Stack row 0 for the stated finite source data. -/
private theorem stack_row_0 :
    (∀ c, stackReal 0 c =
      commutatorReal (sourceIndex 0) c (rowIndex 0) (columnIndex 0)) ∧
    (∀ c, stackImag 0 c =
      commutatorImag (sourceIndex 0) c (rowIndex 0) (columnIndex 0)) := by
  decide +kernel

/-- Stack row 1 for the stated finite source data. -/
private theorem stack_row_1 :
    (∀ c, stackReal 1 c =
      commutatorReal (sourceIndex 1) c (rowIndex 1) (columnIndex 1)) ∧
    (∀ c, stackImag 1 c =
      commutatorImag (sourceIndex 1) c (rowIndex 1) (columnIndex 1)) := by
  decide +kernel

/-- Stack row 2 for the stated finite source data. -/
private theorem stack_row_2 :
    (∀ c, stackReal 2 c =
      commutatorReal (sourceIndex 2) c (rowIndex 2) (columnIndex 2)) ∧
    (∀ c, stackImag 2 c =
      commutatorImag (sourceIndex 2) c (rowIndex 2) (columnIndex 2)) := by
  decide +kernel

/-- Stack row 3 for the stated finite source data. -/
private theorem stack_row_3 :
    (∀ c, stackReal 3 c =
      commutatorReal (sourceIndex 3) c (rowIndex 3) (columnIndex 3)) ∧
    (∀ c, stackImag 3 c =
      commutatorImag (sourceIndex 3) c (rowIndex 3) (columnIndex 3)) := by
  decide +kernel

/-- Stack row 4 for the stated finite source data. -/
private theorem stack_row_4 :
    (∀ c, stackReal 4 c =
      commutatorReal (sourceIndex 4) c (rowIndex 4) (columnIndex 4)) ∧
    (∀ c, stackImag 4 c =
      commutatorImag (sourceIndex 4) c (rowIndex 4) (columnIndex 4)) := by
  decide +kernel

/-- Stack row 5 for the stated finite source data. -/
private theorem stack_row_5 :
    (∀ c, stackReal 5 c =
      commutatorReal (sourceIndex 5) c (rowIndex 5) (columnIndex 5)) ∧
    (∀ c, stackImag 5 c =
      commutatorImag (sourceIndex 5) c (rowIndex 5) (columnIndex 5)) := by
  decide +kernel

/-- Stack row 6 for the stated finite source data. -/
private theorem stack_row_6 :
    (∀ c, stackReal 6 c =
      commutatorReal (sourceIndex 6) c (rowIndex 6) (columnIndex 6)) ∧
    (∀ c, stackImag 6 c =
      commutatorImag (sourceIndex 6) c (rowIndex 6) (columnIndex 6)) := by
  decide +kernel

/-- Stack row 7 for the stated finite source data. -/
private theorem stack_row_7 :
    (∀ c, stackReal 7 c =
      commutatorReal (sourceIndex 7) c (rowIndex 7) (columnIndex 7)) ∧
    (∀ c, stackImag 7 c =
      commutatorImag (sourceIndex 7) c (rowIndex 7) (columnIndex 7)) := by
  decide +kernel

/-- Stack row 8 for the stated finite source data. -/
private theorem stack_row_8 :
    (∀ c, stackReal 8 c =
      commutatorReal (sourceIndex 8) c (rowIndex 8) (columnIndex 8)) ∧
    (∀ c, stackImag 8 c =
      commutatorImag (sourceIndex 8) c (rowIndex 8) (columnIndex 8)) := by
  decide +kernel

/-- Stack row 9 for the stated finite source data. -/
private theorem stack_row_9 :
    (∀ c, stackReal 9 c =
      commutatorReal (sourceIndex 9) c (rowIndex 9) (columnIndex 9)) ∧
    (∀ c, stackImag 9 c =
      commutatorImag (sourceIndex 9) c (rowIndex 9) (columnIndex 9)) := by
  decide +kernel

/-- Stack row 10 for the stated finite source data. -/
private theorem stack_row_10 :
    (∀ c, stackReal 10 c =
      commutatorReal (sourceIndex 10) c (rowIndex 10) (columnIndex 10)) ∧
    (∀ c, stackImag 10 c =
      commutatorImag (sourceIndex 10) c (rowIndex 10) (columnIndex 10)) := by
  decide +kernel

/-- Stack row 11 for the stated finite source data. -/
private theorem stack_row_11 :
    (∀ c, stackReal 11 c =
      commutatorReal (sourceIndex 11) c (rowIndex 11) (columnIndex 11)) ∧
    (∀ c, stackImag 11 c =
      commutatorImag (sourceIndex 11) c (rowIndex 11) (columnIndex 11)) := by
  decide +kernel

/-- Stack row 12 for the stated finite source data. -/
private theorem stack_row_12 :
    (∀ c, stackReal 12 c =
      commutatorReal (sourceIndex 12) c (rowIndex 12) (columnIndex 12)) ∧
    (∀ c, stackImag 12 c =
      commutatorImag (sourceIndex 12) c (rowIndex 12) (columnIndex 12)) := by
  decide +kernel

/-- Stack row 13 for the stated finite source data. -/
private theorem stack_row_13 :
    (∀ c, stackReal 13 c =
      commutatorReal (sourceIndex 13) c (rowIndex 13) (columnIndex 13)) ∧
    (∀ c, stackImag 13 c =
      commutatorImag (sourceIndex 13) c (rowIndex 13) (columnIndex 13)) := by
  decide +kernel

/-- Stack row 14 for the stated finite source data. -/
private theorem stack_row_14 :
    (∀ c, stackReal 14 c =
      commutatorReal (sourceIndex 14) c (rowIndex 14) (columnIndex 14)) ∧
    (∀ c, stackImag 14 c =
      commutatorImag (sourceIndex 14) c (rowIndex 14) (columnIndex 14)) := by
  decide +kernel

/-- Stack row 15 for the stated finite source data. -/
private theorem stack_row_15 :
    (∀ c, stackReal 15 c =
      commutatorReal (sourceIndex 15) c (rowIndex 15) (columnIndex 15)) ∧
    (∀ c, stackImag 15 c =
      commutatorImag (sourceIndex 15) c (rowIndex 15) (columnIndex 15)) := by
  decide +kernel

/-- Stack row 16 for the stated finite source data. -/
private theorem stack_row_16 :
    (∀ c, stackReal 16 c =
      commutatorReal (sourceIndex 16) c (rowIndex 16) (columnIndex 16)) ∧
    (∀ c, stackImag 16 c =
      commutatorImag (sourceIndex 16) c (rowIndex 16) (columnIndex 16)) := by
  decide +kernel

/-- Stack row 17 for the stated finite source data. -/
private theorem stack_row_17 :
    (∀ c, stackReal 17 c =
      commutatorReal (sourceIndex 17) c (rowIndex 17) (columnIndex 17)) ∧
    (∀ c, stackImag 17 c =
      commutatorImag (sourceIndex 17) c (rowIndex 17) (columnIndex 17)) := by
  decide +kernel

/-- Stack row 18 for the stated finite source data. -/
private theorem stack_row_18 :
    (∀ c, stackReal 18 c =
      commutatorReal (sourceIndex 18) c (rowIndex 18) (columnIndex 18)) ∧
    (∀ c, stackImag 18 c =
      commutatorImag (sourceIndex 18) c (rowIndex 18) (columnIndex 18)) := by
  decide +kernel

/-- Stack row 19 for the stated finite source data. -/
private theorem stack_row_19 :
    (∀ c, stackReal 19 c =
      commutatorReal (sourceIndex 19) c (rowIndex 19) (columnIndex 19)) ∧
    (∀ c, stackImag 19 c =
      commutatorImag (sourceIndex 19) c (rowIndex 19) (columnIndex 19)) := by
  decide +kernel

/-- Stack row 20 for the stated finite source data. -/
private theorem stack_row_20 :
    (∀ c, stackReal 20 c =
      commutatorReal (sourceIndex 20) c (rowIndex 20) (columnIndex 20)) ∧
    (∀ c, stackImag 20 c =
      commutatorImag (sourceIndex 20) c (rowIndex 20) (columnIndex 20)) := by
  decide +kernel

/-- Stack row 21 for the stated finite source data. -/
private theorem stack_row_21 :
    (∀ c, stackReal 21 c =
      commutatorReal (sourceIndex 21) c (rowIndex 21) (columnIndex 21)) ∧
    (∀ c, stackImag 21 c =
      commutatorImag (sourceIndex 21) c (rowIndex 21) (columnIndex 21)) := by
  decide +kernel

/-- Stack row 22 for the stated finite source data. -/
private theorem stack_row_22 :
    (∀ c, stackReal 22 c =
      commutatorReal (sourceIndex 22) c (rowIndex 22) (columnIndex 22)) ∧
    (∀ c, stackImag 22 c =
      commutatorImag (sourceIndex 22) c (rowIndex 22) (columnIndex 22)) := by
  decide +kernel

/-- Stack row 23 for the stated finite source data. -/
private theorem stack_row_23 :
    (∀ c, stackReal 23 c =
      commutatorReal (sourceIndex 23) c (rowIndex 23) (columnIndex 23)) ∧
    (∀ c, stackImag 23 c =
      commutatorImag (sourceIndex 23) c (rowIndex 23) (columnIndex 23)) := by
  decide +kernel

/-- Stack row 24 for the stated finite source data. -/
private theorem stack_row_24 :
    (∀ c, stackReal 24 c =
      commutatorReal (sourceIndex 24) c (rowIndex 24) (columnIndex 24)) ∧
    (∀ c, stackImag 24 c =
      commutatorImag (sourceIndex 24) c (rowIndex 24) (columnIndex 24)) := by
  decide +kernel

/-- Stack row 25 for the stated finite source data. -/
private theorem stack_row_25 :
    (∀ c, stackReal 25 c =
      commutatorReal (sourceIndex 25) c (rowIndex 25) (columnIndex 25)) ∧
    (∀ c, stackImag 25 c =
      commutatorImag (sourceIndex 25) c (rowIndex 25) (columnIndex 25)) := by
  decide +kernel

/-- Stack row 26 for the stated finite source data. -/
private theorem stack_row_26 :
    (∀ c, stackReal 26 c =
      commutatorReal (sourceIndex 26) c (rowIndex 26) (columnIndex 26)) ∧
    (∀ c, stackImag 26 c =
      commutatorImag (sourceIndex 26) c (rowIndex 26) (columnIndex 26)) := by
  decide +kernel

/-- Stack row 27 for the stated finite source data. -/
private theorem stack_row_27 :
    (∀ c, stackReal 27 c =
      commutatorReal (sourceIndex 27) c (rowIndex 27) (columnIndex 27)) ∧
    (∀ c, stackImag 27 c =
      commutatorImag (sourceIndex 27) c (rowIndex 27) (columnIndex 27)) := by
  decide +kernel

/-- Stack row 28 for the stated finite source data. -/
private theorem stack_row_28 :
    (∀ c, stackReal 28 c =
      commutatorReal (sourceIndex 28) c (rowIndex 28) (columnIndex 28)) ∧
    (∀ c, stackImag 28 c =
      commutatorImag (sourceIndex 28) c (rowIndex 28) (columnIndex 28)) := by
  decide +kernel

/-- Stack row 29 for the stated finite source data. -/
private theorem stack_row_29 :
    (∀ c, stackReal 29 c =
      commutatorReal (sourceIndex 29) c (rowIndex 29) (columnIndex 29)) ∧
    (∀ c, stackImag 29 c =
      commutatorImag (sourceIndex 29) c (rowIndex 29) (columnIndex 29)) := by
  decide +kernel

/-- Stack row 30 for the stated finite source data. -/
private theorem stack_row_30 :
    (∀ c, stackReal 30 c =
      commutatorReal (sourceIndex 30) c (rowIndex 30) (columnIndex 30)) ∧
    (∀ c, stackImag 30 c =
      commutatorImag (sourceIndex 30) c (rowIndex 30) (columnIndex 30)) := by
  decide +kernel

/-- Stack row 31 for the stated finite source data. -/
private theorem stack_row_31 :
    (∀ c, stackReal 31 c =
      commutatorReal (sourceIndex 31) c (rowIndex 31) (columnIndex 31)) ∧
    (∀ c, stackImag 31 c =
      commutatorImag (sourceIndex 31) c (rowIndex 31) (columnIndex 31)) := by
  decide +kernel

/-- Stack row 32 for the stated finite source data. -/
private theorem stack_row_32 :
    (∀ c, stackReal 32 c =
      commutatorReal (sourceIndex 32) c (rowIndex 32) (columnIndex 32)) ∧
    (∀ c, stackImag 32 c =
      commutatorImag (sourceIndex 32) c (rowIndex 32) (columnIndex 32)) := by
  decide +kernel

/-- Stack row 33 for the stated finite source data. -/
private theorem stack_row_33 :
    (∀ c, stackReal 33 c =
      commutatorReal (sourceIndex 33) c (rowIndex 33) (columnIndex 33)) ∧
    (∀ c, stackImag 33 c =
      commutatorImag (sourceIndex 33) c (rowIndex 33) (columnIndex 33)) := by
  decide +kernel

/-- Stack row 34 for the stated finite source data. -/
private theorem stack_row_34 :
    (∀ c, stackReal 34 c =
      commutatorReal (sourceIndex 34) c (rowIndex 34) (columnIndex 34)) ∧
    (∀ c, stackImag 34 c =
      commutatorImag (sourceIndex 34) c (rowIndex 34) (columnIndex 34)) := by
  decide +kernel

/-- Stack row 35 for the stated finite source data. -/
private theorem stack_row_35 :
    (∀ c, stackReal 35 c =
      commutatorReal (sourceIndex 35) c (rowIndex 35) (columnIndex 35)) ∧
    (∀ c, stackImag 35 c =
      commutatorImag (sourceIndex 35) c (rowIndex 35) (columnIndex 35)) := by
  decide +kernel

/-- Stack row 36 for the stated finite source data. -/
private theorem stack_row_36 :
    (∀ c, stackReal 36 c =
      commutatorReal (sourceIndex 36) c (rowIndex 36) (columnIndex 36)) ∧
    (∀ c, stackImag 36 c =
      commutatorImag (sourceIndex 36) c (rowIndex 36) (columnIndex 36)) := by
  decide +kernel

/-- Stack row 37 for the stated finite source data. -/
private theorem stack_row_37 :
    (∀ c, stackReal 37 c =
      commutatorReal (sourceIndex 37) c (rowIndex 37) (columnIndex 37)) ∧
    (∀ c, stackImag 37 c =
      commutatorImag (sourceIndex 37) c (rowIndex 37) (columnIndex 37)) := by
  decide +kernel

/-- Stack row 38 for the stated finite source data. -/
private theorem stack_row_38 :
    (∀ c, stackReal 38 c =
      commutatorReal (sourceIndex 38) c (rowIndex 38) (columnIndex 38)) ∧
    (∀ c, stackImag 38 c =
      commutatorImag (sourceIndex 38) c (rowIndex 38) (columnIndex 38)) := by
  decide +kernel

/-- Stack row 39 for the stated finite source data. -/
private theorem stack_row_39 :
    (∀ c, stackReal 39 c =
      commutatorReal (sourceIndex 39) c (rowIndex 39) (columnIndex 39)) ∧
    (∀ c, stackImag 39 c =
      commutatorImag (sourceIndex 39) c (rowIndex 39) (columnIndex 39)) := by
  decide +kernel

/-- Stack row 40 for the stated finite source data. -/
private theorem stack_row_40 :
    (∀ c, stackReal 40 c =
      commutatorReal (sourceIndex 40) c (rowIndex 40) (columnIndex 40)) ∧
    (∀ c, stackImag 40 c =
      commutatorImag (sourceIndex 40) c (rowIndex 40) (columnIndex 40)) := by
  decide +kernel

/-- Stack row 41 for the stated finite source data. -/
private theorem stack_row_41 :
    (∀ c, stackReal 41 c =
      commutatorReal (sourceIndex 41) c (rowIndex 41) (columnIndex 41)) ∧
    (∀ c, stackImag 41 c =
      commutatorImag (sourceIndex 41) c (rowIndex 41) (columnIndex 41)) := by
  decide +kernel

/-- Stack row 42 for the stated finite source data. -/
private theorem stack_row_42 :
    (∀ c, stackReal 42 c =
      commutatorReal (sourceIndex 42) c (rowIndex 42) (columnIndex 42)) ∧
    (∀ c, stackImag 42 c =
      commutatorImag (sourceIndex 42) c (rowIndex 42) (columnIndex 42)) := by
  decide +kernel

/-- Stack row 43 for the stated finite source data. -/
private theorem stack_row_43 :
    (∀ c, stackReal 43 c =
      commutatorReal (sourceIndex 43) c (rowIndex 43) (columnIndex 43)) ∧
    (∀ c, stackImag 43 c =
      commutatorImag (sourceIndex 43) c (rowIndex 43) (columnIndex 43)) := by
  decide +kernel

/-- Stack row 44 for the stated finite source data. -/
private theorem stack_row_44 :
    (∀ c, stackReal 44 c =
      commutatorReal (sourceIndex 44) c (rowIndex 44) (columnIndex 44)) ∧
    (∀ c, stackImag 44 c =
      commutatorImag (sourceIndex 44) c (rowIndex 44) (columnIndex 44)) := by
  decide +kernel

/-- Stack row 45 for the stated finite source data. -/
private theorem stack_row_45 :
    (∀ c, stackReal 45 c =
      commutatorReal (sourceIndex 45) c (rowIndex 45) (columnIndex 45)) ∧
    (∀ c, stackImag 45 c =
      commutatorImag (sourceIndex 45) c (rowIndex 45) (columnIndex 45)) := by
  decide +kernel

/-- Stack row 46 for the stated finite source data. -/
private theorem stack_row_46 :
    (∀ c, stackReal 46 c =
      commutatorReal (sourceIndex 46) c (rowIndex 46) (columnIndex 46)) ∧
    (∀ c, stackImag 46 c =
      commutatorImag (sourceIndex 46) c (rowIndex 46) (columnIndex 46)) := by
  decide +kernel

/-- Stack row 47 for the stated finite source data. -/
private theorem stack_row_47 :
    (∀ c, stackReal 47 c =
      commutatorReal (sourceIndex 47) c (rowIndex 47) (columnIndex 47)) ∧
    (∀ c, stackImag 47 c =
      commutatorImag (sourceIndex 47) c (rowIndex 47) (columnIndex 47)) := by
  decide +kernel

/-- Stack row 48 for the stated finite source data. -/
private theorem stack_row_48 :
    (∀ c, stackReal 48 c =
      commutatorReal (sourceIndex 48) c (rowIndex 48) (columnIndex 48)) ∧
    (∀ c, stackImag 48 c =
      commutatorImag (sourceIndex 48) c (rowIndex 48) (columnIndex 48)) := by
  decide +kernel

/-- Stack row 49 for the stated finite source data. -/
private theorem stack_row_49 :
    (∀ c, stackReal 49 c =
      commutatorReal (sourceIndex 49) c (rowIndex 49) (columnIndex 49)) ∧
    (∀ c, stackImag 49 c =
      commutatorImag (sourceIndex 49) c (rowIndex 49) (columnIndex 49)) := by
  decide +kernel

/-- Stack row 50 for the stated finite source data. -/
private theorem stack_row_50 :
    (∀ c, stackReal 50 c =
      commutatorReal (sourceIndex 50) c (rowIndex 50) (columnIndex 50)) ∧
    (∀ c, stackImag 50 c =
      commutatorImag (sourceIndex 50) c (rowIndex 50) (columnIndex 50)) := by
  decide +kernel

/-- Stack row 51 for the stated finite source data. -/
private theorem stack_row_51 :
    (∀ c, stackReal 51 c =
      commutatorReal (sourceIndex 51) c (rowIndex 51) (columnIndex 51)) ∧
    (∀ c, stackImag 51 c =
      commutatorImag (sourceIndex 51) c (rowIndex 51) (columnIndex 51)) := by
  decide +kernel

/-- Stack row 52 for the stated finite source data. -/
private theorem stack_row_52 :
    (∀ c, stackReal 52 c =
      commutatorReal (sourceIndex 52) c (rowIndex 52) (columnIndex 52)) ∧
    (∀ c, stackImag 52 c =
      commutatorImag (sourceIndex 52) c (rowIndex 52) (columnIndex 52)) := by
  decide +kernel

/-- Stack row 53 for the stated finite source data. -/
private theorem stack_row_53 :
    (∀ c, stackReal 53 c =
      commutatorReal (sourceIndex 53) c (rowIndex 53) (columnIndex 53)) ∧
    (∀ c, stackImag 53 c =
      commutatorImag (sourceIndex 53) c (rowIndex 53) (columnIndex 53)) := by
  decide +kernel

/-- Stack row 54 for the stated finite source data. -/
private theorem stack_row_54 :
    (∀ c, stackReal 54 c =
      commutatorReal (sourceIndex 54) c (rowIndex 54) (columnIndex 54)) ∧
    (∀ c, stackImag 54 c =
      commutatorImag (sourceIndex 54) c (rowIndex 54) (columnIndex 54)) := by
  decide +kernel

/-- Stack row 55 for the stated finite source data. -/
private theorem stack_row_55 :
    (∀ c, stackReal 55 c =
      commutatorReal (sourceIndex 55) c (rowIndex 55) (columnIndex 55)) ∧
    (∀ c, stackImag 55 c =
      commutatorImag (sourceIndex 55) c (rowIndex 55) (columnIndex 55)) := by
  decide +kernel

/-- Stack row 56 for the stated finite source data. -/
private theorem stack_row_56 :
    (∀ c, stackReal 56 c =
      commutatorReal (sourceIndex 56) c (rowIndex 56) (columnIndex 56)) ∧
    (∀ c, stackImag 56 c =
      commutatorImag (sourceIndex 56) c (rowIndex 56) (columnIndex 56)) := by
  decide +kernel

/-- Stack row 57 for the stated finite source data. -/
private theorem stack_row_57 :
    (∀ c, stackReal 57 c =
      commutatorReal (sourceIndex 57) c (rowIndex 57) (columnIndex 57)) ∧
    (∀ c, stackImag 57 c =
      commutatorImag (sourceIndex 57) c (rowIndex 57) (columnIndex 57)) := by
  decide +kernel

/-- Stack row 58 for the stated finite source data. -/
private theorem stack_row_58 :
    (∀ c, stackReal 58 c =
      commutatorReal (sourceIndex 58) c (rowIndex 58) (columnIndex 58)) ∧
    (∀ c, stackImag 58 c =
      commutatorImag (sourceIndex 58) c (rowIndex 58) (columnIndex 58)) := by
  decide +kernel

/-- Stack row 59 for the stated finite source data. -/
private theorem stack_row_59 :
    (∀ c, stackReal 59 c =
      commutatorReal (sourceIndex 59) c (rowIndex 59) (columnIndex 59)) ∧
    (∀ c, stackImag 59 c =
      commutatorImag (sourceIndex 59) c (rowIndex 59) (columnIndex 59)) := by
  decide +kernel

/-- Stack row 60 for the stated finite source data. -/
private theorem stack_row_60 :
    (∀ c, stackReal 60 c =
      commutatorReal (sourceIndex 60) c (rowIndex 60) (columnIndex 60)) ∧
    (∀ c, stackImag 60 c =
      commutatorImag (sourceIndex 60) c (rowIndex 60) (columnIndex 60)) := by
  decide +kernel

/-- Stack row 61 for the stated finite source data. -/
private theorem stack_row_61 :
    (∀ c, stackReal 61 c =
      commutatorReal (sourceIndex 61) c (rowIndex 61) (columnIndex 61)) ∧
    (∀ c, stackImag 61 c =
      commutatorImag (sourceIndex 61) c (rowIndex 61) (columnIndex 61)) := by
  decide +kernel

/-- Stack row 62 for the stated finite source data. -/
private theorem stack_row_62 :
    (∀ c, stackReal 62 c =
      commutatorReal (sourceIndex 62) c (rowIndex 62) (columnIndex 62)) ∧
    (∀ c, stackImag 62 c =
      commutatorImag (sourceIndex 62) c (rowIndex 62) (columnIndex 62)) := by
  decide +kernel

/-- Stack row 63 for the stated finite source data. -/
private theorem stack_row_63 :
    (∀ c, stackReal 63 c =
      commutatorReal (sourceIndex 63) c (rowIndex 63) (columnIndex 63)) ∧
    (∀ c, stackImag 63 c =
      commutatorImag (sourceIndex 63) c (rowIndex 63) (columnIndex 63)) := by
  decide +kernel

/-- Stack row 64 for the stated finite source data. -/
private theorem stack_row_64 :
    (∀ c, stackReal 64 c =
      commutatorReal (sourceIndex 64) c (rowIndex 64) (columnIndex 64)) ∧
    (∀ c, stackImag 64 c =
      commutatorImag (sourceIndex 64) c (rowIndex 64) (columnIndex 64)) := by
  decide +kernel

/-- Stack row 65 for the stated finite source data. -/
private theorem stack_row_65 :
    (∀ c, stackReal 65 c =
      commutatorReal (sourceIndex 65) c (rowIndex 65) (columnIndex 65)) ∧
    (∀ c, stackImag 65 c =
      commutatorImag (sourceIndex 65) c (rowIndex 65) (columnIndex 65)) := by
  decide +kernel

/-- Stack row 66 for the stated finite source data. -/
private theorem stack_row_66 :
    (∀ c, stackReal 66 c =
      commutatorReal (sourceIndex 66) c (rowIndex 66) (columnIndex 66)) ∧
    (∀ c, stackImag 66 c =
      commutatorImag (sourceIndex 66) c (rowIndex 66) (columnIndex 66)) := by
  decide +kernel

/-- Stack row 67 for the stated finite source data. -/
private theorem stack_row_67 :
    (∀ c, stackReal 67 c =
      commutatorReal (sourceIndex 67) c (rowIndex 67) (columnIndex 67)) ∧
    (∀ c, stackImag 67 c =
      commutatorImag (sourceIndex 67) c (rowIndex 67) (columnIndex 67)) := by
  decide +kernel

/-- Stack row 68 for the stated finite source data. -/
private theorem stack_row_68 :
    (∀ c, stackReal 68 c =
      commutatorReal (sourceIndex 68) c (rowIndex 68) (columnIndex 68)) ∧
    (∀ c, stackImag 68 c =
      commutatorImag (sourceIndex 68) c (rowIndex 68) (columnIndex 68)) := by
  decide +kernel

/-- Stack row 69 for the stated finite source data. -/
private theorem stack_row_69 :
    (∀ c, stackReal 69 c =
      commutatorReal (sourceIndex 69) c (rowIndex 69) (columnIndex 69)) ∧
    (∀ c, stackImag 69 c =
      commutatorImag (sourceIndex 69) c (rowIndex 69) (columnIndex 69)) := by
  decide +kernel

/-- Stack row 70 for the stated finite source data. -/
private theorem stack_row_70 :
    (∀ c, stackReal 70 c =
      commutatorReal (sourceIndex 70) c (rowIndex 70) (columnIndex 70)) ∧
    (∀ c, stackImag 70 c =
      commutatorImag (sourceIndex 70) c (rowIndex 70) (columnIndex 70)) := by
  decide +kernel

/-- Stack row 71 for the stated finite source data. -/
private theorem stack_row_71 :
    (∀ c, stackReal 71 c =
      commutatorReal (sourceIndex 71) c (rowIndex 71) (columnIndex 71)) ∧
    (∀ c, stackImag 71 c =
      commutatorImag (sourceIndex 71) c (rowIndex 71) (columnIndex 71)) := by
  decide +kernel

/-- Stack row 72 for the stated finite source data. -/
private theorem stack_row_72 :
    (∀ c, stackReal 72 c =
      commutatorReal (sourceIndex 72) c (rowIndex 72) (columnIndex 72)) ∧
    (∀ c, stackImag 72 c =
      commutatorImag (sourceIndex 72) c (rowIndex 72) (columnIndex 72)) := by
  decide +kernel

/-- Stack row 73 for the stated finite source data. -/
private theorem stack_row_73 :
    (∀ c, stackReal 73 c =
      commutatorReal (sourceIndex 73) c (rowIndex 73) (columnIndex 73)) ∧
    (∀ c, stackImag 73 c =
      commutatorImag (sourceIndex 73) c (rowIndex 73) (columnIndex 73)) := by
  decide +kernel

/-- Stack row 74 for the stated finite source data. -/
private theorem stack_row_74 :
    (∀ c, stackReal 74 c =
      commutatorReal (sourceIndex 74) c (rowIndex 74) (columnIndex 74)) ∧
    (∀ c, stackImag 74 c =
      commutatorImag (sourceIndex 74) c (rowIndex 74) (columnIndex 74)) := by
  decide +kernel

/-- Stack row 75 for the stated finite source data. -/
private theorem stack_row_75 :
    (∀ c, stackReal 75 c =
      commutatorReal (sourceIndex 75) c (rowIndex 75) (columnIndex 75)) ∧
    (∀ c, stackImag 75 c =
      commutatorImag (sourceIndex 75) c (rowIndex 75) (columnIndex 75)) := by
  decide +kernel

/-- Stack row 76 for the stated finite source data. -/
private theorem stack_row_76 :
    (∀ c, stackReal 76 c =
      commutatorReal (sourceIndex 76) c (rowIndex 76) (columnIndex 76)) ∧
    (∀ c, stackImag 76 c =
      commutatorImag (sourceIndex 76) c (rowIndex 76) (columnIndex 76)) := by
  decide +kernel

/-- Stack row 77 for the stated finite source data. -/
private theorem stack_row_77 :
    (∀ c, stackReal 77 c =
      commutatorReal (sourceIndex 77) c (rowIndex 77) (columnIndex 77)) ∧
    (∀ c, stackImag 77 c =
      commutatorImag (sourceIndex 77) c (rowIndex 77) (columnIndex 77)) := by
  decide +kernel

/-- Stack row 78 for the stated finite source data. -/
private theorem stack_row_78 :
    (∀ c, stackReal 78 c =
      commutatorReal (sourceIndex 78) c (rowIndex 78) (columnIndex 78)) ∧
    (∀ c, stackImag 78 c =
      commutatorImag (sourceIndex 78) c (rowIndex 78) (columnIndex 78)) := by
  decide +kernel

/-- Stack row 79 for the stated finite source data. -/
private theorem stack_row_79 :
    (∀ c, stackReal 79 c =
      commutatorReal (sourceIndex 79) c (rowIndex 79) (columnIndex 79)) ∧
    (∀ c, stackImag 79 c =
      commutatorImag (sourceIndex 79) c (rowIndex 79) (columnIndex 79)) := by
  decide +kernel

/-- Stack row 80 for the stated finite source data. -/
private theorem stack_row_80 :
    (∀ c, stackReal 80 c =
      commutatorReal (sourceIndex 80) c (rowIndex 80) (columnIndex 80)) ∧
    (∀ c, stackImag 80 c =
      commutatorImag (sourceIndex 80) c (rowIndex 80) (columnIndex 80)) := by
  decide +kernel

/-- Stack row 81 for the stated finite source data. -/
private theorem stack_row_81 :
    (∀ c, stackReal 81 c =
      commutatorReal (sourceIndex 81) c (rowIndex 81) (columnIndex 81)) ∧
    (∀ c, stackImag 81 c =
      commutatorImag (sourceIndex 81) c (rowIndex 81) (columnIndex 81)) := by
  decide +kernel

/-- Stack row 82 for the stated finite source data. -/
private theorem stack_row_82 :
    (∀ c, stackReal 82 c =
      commutatorReal (sourceIndex 82) c (rowIndex 82) (columnIndex 82)) ∧
    (∀ c, stackImag 82 c =
      commutatorImag (sourceIndex 82) c (rowIndex 82) (columnIndex 82)) := by
  decide +kernel

/-- Stack row 83 for the stated finite source data. -/
private theorem stack_row_83 :
    (∀ c, stackReal 83 c =
      commutatorReal (sourceIndex 83) c (rowIndex 83) (columnIndex 83)) ∧
    (∀ c, stackImag 83 c =
      commutatorImag (sourceIndex 83) c (rowIndex 83) (columnIndex 83)) := by
  decide +kernel

/-- Stack row 84 for the stated finite source data. -/
private theorem stack_row_84 :
    (∀ c, stackReal 84 c =
      commutatorReal (sourceIndex 84) c (rowIndex 84) (columnIndex 84)) ∧
    (∀ c, stackImag 84 c =
      commutatorImag (sourceIndex 84) c (rowIndex 84) (columnIndex 84)) := by
  decide +kernel

/-- Stack row 85 for the stated finite source data. -/
private theorem stack_row_85 :
    (∀ c, stackReal 85 c =
      commutatorReal (sourceIndex 85) c (rowIndex 85) (columnIndex 85)) ∧
    (∀ c, stackImag 85 c =
      commutatorImag (sourceIndex 85) c (rowIndex 85) (columnIndex 85)) := by
  decide +kernel

/-- Stack row 86 for the stated finite source data. -/
private theorem stack_row_86 :
    (∀ c, stackReal 86 c =
      commutatorReal (sourceIndex 86) c (rowIndex 86) (columnIndex 86)) ∧
    (∀ c, stackImag 86 c =
      commutatorImag (sourceIndex 86) c (rowIndex 86) (columnIndex 86)) := by
  decide +kernel

/-- Stack row 87 for the stated finite source data. -/
private theorem stack_row_87 :
    (∀ c, stackReal 87 c =
      commutatorReal (sourceIndex 87) c (rowIndex 87) (columnIndex 87)) ∧
    (∀ c, stackImag 87 c =
      commutatorImag (sourceIndex 87) c (rowIndex 87) (columnIndex 87)) := by
  decide +kernel

/-- Stack row 88 for the stated finite source data. -/
private theorem stack_row_88 :
    (∀ c, stackReal 88 c =
      commutatorReal (sourceIndex 88) c (rowIndex 88) (columnIndex 88)) ∧
    (∀ c, stackImag 88 c =
      commutatorImag (sourceIndex 88) c (rowIndex 88) (columnIndex 88)) := by
  decide +kernel

/-- Stack row 89 for the stated finite source data. -/
private theorem stack_row_89 :
    (∀ c, stackReal 89 c =
      commutatorReal (sourceIndex 89) c (rowIndex 89) (columnIndex 89)) ∧
    (∀ c, stackImag 89 c =
      commutatorImag (sourceIndex 89) c (rowIndex 89) (columnIndex 89)) := by
  decide +kernel

/-- Stack row 90 for the stated finite source data. -/
private theorem stack_row_90 :
    (∀ c, stackReal 90 c =
      commutatorReal (sourceIndex 90) c (rowIndex 90) (columnIndex 90)) ∧
    (∀ c, stackImag 90 c =
      commutatorImag (sourceIndex 90) c (rowIndex 90) (columnIndex 90)) := by
  decide +kernel

/-- Stack row 91 for the stated finite source data. -/
private theorem stack_row_91 :
    (∀ c, stackReal 91 c =
      commutatorReal (sourceIndex 91) c (rowIndex 91) (columnIndex 91)) ∧
    (∀ c, stackImag 91 c =
      commutatorImag (sourceIndex 91) c (rowIndex 91) (columnIndex 91)) := by
  decide +kernel

/-- Stack row 92 for the stated finite source data. -/
private theorem stack_row_92 :
    (∀ c, stackReal 92 c =
      commutatorReal (sourceIndex 92) c (rowIndex 92) (columnIndex 92)) ∧
    (∀ c, stackImag 92 c =
      commutatorImag (sourceIndex 92) c (rowIndex 92) (columnIndex 92)) := by
  decide +kernel

/-- Stack row 93 for the stated finite source data. -/
private theorem stack_row_93 :
    (∀ c, stackReal 93 c =
      commutatorReal (sourceIndex 93) c (rowIndex 93) (columnIndex 93)) ∧
    (∀ c, stackImag 93 c =
      commutatorImag (sourceIndex 93) c (rowIndex 93) (columnIndex 93)) := by
  decide +kernel

/-- Stack row 94 for the stated finite source data. -/
private theorem stack_row_94 :
    (∀ c, stackReal 94 c =
      commutatorReal (sourceIndex 94) c (rowIndex 94) (columnIndex 94)) ∧
    (∀ c, stackImag 94 c =
      commutatorImag (sourceIndex 94) c (rowIndex 94) (columnIndex 94)) := by
  decide +kernel

/-- Stack row 95 for the stated finite source data. -/
private theorem stack_row_95 :
    (∀ c, stackReal 95 c =
      commutatorReal (sourceIndex 95) c (rowIndex 95) (columnIndex 95)) ∧
    (∀ c, stackImag 95 c =
      commutatorImag (sourceIndex 95) c (rowIndex 95) (columnIndex 95)) := by
  decide +kernel

/-- All 1,440 complex source-column entries agree with the literal commutators. -/
theorem stack_parts_match_commutators :
    (∀ a c, stackReal a c =
      commutatorReal (sourceIndex a) c (rowIndex a) (columnIndex a)) ∧
    (∀ a c, stackImag a c =
      commutatorImag (sourceIndex a) c (rowIndex a) (columnIndex a)) := by
  constructor
  · intro a c
    fin_cases a

    · exact stack_row_0.1 c
    · exact stack_row_1.1 c
    · exact stack_row_2.1 c
    · exact stack_row_3.1 c
    · exact stack_row_4.1 c
    · exact stack_row_5.1 c
    · exact stack_row_6.1 c
    · exact stack_row_7.1 c
    · exact stack_row_8.1 c
    · exact stack_row_9.1 c
    · exact stack_row_10.1 c
    · exact stack_row_11.1 c
    · exact stack_row_12.1 c
    · exact stack_row_13.1 c
    · exact stack_row_14.1 c
    · exact stack_row_15.1 c
    · exact stack_row_16.1 c
    · exact stack_row_17.1 c
    · exact stack_row_18.1 c
    · exact stack_row_19.1 c
    · exact stack_row_20.1 c
    · exact stack_row_21.1 c
    · exact stack_row_22.1 c
    · exact stack_row_23.1 c
    · exact stack_row_24.1 c
    · exact stack_row_25.1 c
    · exact stack_row_26.1 c
    · exact stack_row_27.1 c
    · exact stack_row_28.1 c
    · exact stack_row_29.1 c
    · exact stack_row_30.1 c
    · exact stack_row_31.1 c
    · exact stack_row_32.1 c
    · exact stack_row_33.1 c
    · exact stack_row_34.1 c
    · exact stack_row_35.1 c
    · exact stack_row_36.1 c
    · exact stack_row_37.1 c
    · exact stack_row_38.1 c
    · exact stack_row_39.1 c
    · exact stack_row_40.1 c
    · exact stack_row_41.1 c
    · exact stack_row_42.1 c
    · exact stack_row_43.1 c
    · exact stack_row_44.1 c
    · exact stack_row_45.1 c
    · exact stack_row_46.1 c
    · exact stack_row_47.1 c
    · exact stack_row_48.1 c
    · exact stack_row_49.1 c
    · exact stack_row_50.1 c
    · exact stack_row_51.1 c
    · exact stack_row_52.1 c
    · exact stack_row_53.1 c
    · exact stack_row_54.1 c
    · exact stack_row_55.1 c
    · exact stack_row_56.1 c
    · exact stack_row_57.1 c
    · exact stack_row_58.1 c
    · exact stack_row_59.1 c
    · exact stack_row_60.1 c
    · exact stack_row_61.1 c
    · exact stack_row_62.1 c
    · exact stack_row_63.1 c
    · exact stack_row_64.1 c
    · exact stack_row_65.1 c
    · exact stack_row_66.1 c
    · exact stack_row_67.1 c
    · exact stack_row_68.1 c
    · exact stack_row_69.1 c
    · exact stack_row_70.1 c
    · exact stack_row_71.1 c
    · exact stack_row_72.1 c
    · exact stack_row_73.1 c
    · exact stack_row_74.1 c
    · exact stack_row_75.1 c
    · exact stack_row_76.1 c
    · exact stack_row_77.1 c
    · exact stack_row_78.1 c
    · exact stack_row_79.1 c
    · exact stack_row_80.1 c
    · exact stack_row_81.1 c
    · exact stack_row_82.1 c
    · exact stack_row_83.1 c
    · exact stack_row_84.1 c
    · exact stack_row_85.1 c
    · exact stack_row_86.1 c
    · exact stack_row_87.1 c
    · exact stack_row_88.1 c
    · exact stack_row_89.1 c
    · exact stack_row_90.1 c
    · exact stack_row_91.1 c
    · exact stack_row_92.1 c
    · exact stack_row_93.1 c
    · exact stack_row_94.1 c
    · exact stack_row_95.1 c

  · intro a c
    fin_cases a

    · exact stack_row_0.2 c
    · exact stack_row_1.2 c
    · exact stack_row_2.2 c
    · exact stack_row_3.2 c
    · exact stack_row_4.2 c
    · exact stack_row_5.2 c
    · exact stack_row_6.2 c
    · exact stack_row_7.2 c
    · exact stack_row_8.2 c
    · exact stack_row_9.2 c
    · exact stack_row_10.2 c
    · exact stack_row_11.2 c
    · exact stack_row_12.2 c
    · exact stack_row_13.2 c
    · exact stack_row_14.2 c
    · exact stack_row_15.2 c
    · exact stack_row_16.2 c
    · exact stack_row_17.2 c
    · exact stack_row_18.2 c
    · exact stack_row_19.2 c
    · exact stack_row_20.2 c
    · exact stack_row_21.2 c
    · exact stack_row_22.2 c
    · exact stack_row_23.2 c
    · exact stack_row_24.2 c
    · exact stack_row_25.2 c
    · exact stack_row_26.2 c
    · exact stack_row_27.2 c
    · exact stack_row_28.2 c
    · exact stack_row_29.2 c
    · exact stack_row_30.2 c
    · exact stack_row_31.2 c
    · exact stack_row_32.2 c
    · exact stack_row_33.2 c
    · exact stack_row_34.2 c
    · exact stack_row_35.2 c
    · exact stack_row_36.2 c
    · exact stack_row_37.2 c
    · exact stack_row_38.2 c
    · exact stack_row_39.2 c
    · exact stack_row_40.2 c
    · exact stack_row_41.2 c
    · exact stack_row_42.2 c
    · exact stack_row_43.2 c
    · exact stack_row_44.2 c
    · exact stack_row_45.2 c
    · exact stack_row_46.2 c
    · exact stack_row_47.2 c
    · exact stack_row_48.2 c
    · exact stack_row_49.2 c
    · exact stack_row_50.2 c
    · exact stack_row_51.2 c
    · exact stack_row_52.2 c
    · exact stack_row_53.2 c
    · exact stack_row_54.2 c
    · exact stack_row_55.2 c
    · exact stack_row_56.2 c
    · exact stack_row_57.2 c
    · exact stack_row_58.2 c
    · exact stack_row_59.2 c
    · exact stack_row_60.2 c
    · exact stack_row_61.2 c
    · exact stack_row_62.2 c
    · exact stack_row_63.2 c
    · exact stack_row_64.2 c
    · exact stack_row_65.2 c
    · exact stack_row_66.2 c
    · exact stack_row_67.2 c
    · exact stack_row_68.2 c
    · exact stack_row_69.2 c
    · exact stack_row_70.2 c
    · exact stack_row_71.2 c
    · exact stack_row_72.2 c
    · exact stack_row_73.2 c
    · exact stack_row_74.2 c
    · exact stack_row_75.2 c
    · exact stack_row_76.2 c
    · exact stack_row_77.2 c
    · exact stack_row_78.2 c
    · exact stack_row_79.2 c
    · exact stack_row_80.2 c
    · exact stack_row_81.2 c
    · exact stack_row_82.2 c
    · exact stack_row_83.2 c
    · exact stack_row_84.2 c
    · exact stack_row_85.2 c
    · exact stack_row_86.2 c
    · exact stack_row_87.2 c
    · exact stack_row_88.2 c
    · exact stack_row_89.2 c
    · exact stack_row_90.2 c
    · exact stack_row_91.2 c
    · exact stack_row_92.2 c
    · exact stack_row_93.2 c
    · exact stack_row_94.2 c
    · exact stack_row_95.2 c

/-- This independently binds the lower-right metric block to the supplied F columns. -/
theorem metric_parts_match_fast_basis :
    (∀ i j, metricReal i j =
      if i.val < 2 ∨ j.val < 2 then (if i = j then 1 else 0)
      else ∑ k, (inputReal k i * inputReal k j + inputImag k i * inputImag k j)) ∧
    (∀ i j, metricImag i j =
      if i.val < 2 ∨ j.val < 2 then 0
      else ∑ k, (inputReal k i * inputImag k j - inputImag k i * inputReal k j)) := by
  decide +kernel

def gramReal : Matrix (Fin 15) (Fin 15) ℚ :=
  stackReal.transpose * stackReal + stackImag.transpose * stackImag

def gramImag : Matrix (Fin 15) (Fin 15) ℚ :=
  stackReal.transpose * stackImag - stackImag.transpose * stackReal

/-- Coefficient row 0 for the stated finite source data. -/
private theorem coefficient_row_0 :
    (∀ j, gramReal 0 j - metricReal 0 j = (1/1458 : ℚ) * primitive521Real 0 j) ∧
    (∀ j, gramImag 0 j - metricImag 0 j = (1/1458 : ℚ) * primitive521Imag 0 j) ∧
    (∀ j, (34 : ℚ) * metricReal 0 j - gramReal 0 j = (1/729 : ℚ) * primitive878Real 0 j) ∧
    (∀ j, (34 : ℚ) * metricImag 0 j - gramImag 0 j = (1/729 : ℚ) * primitive878Imag 0 j) := by
  decide +kernel

/-- Coefficient row 1 for the stated finite source data. -/
private theorem coefficient_row_1 :
    (∀ j, gramReal 1 j - metricReal 1 j = (1/1458 : ℚ) * primitive521Real 1 j) ∧
    (∀ j, gramImag 1 j - metricImag 1 j = (1/1458 : ℚ) * primitive521Imag 1 j) ∧
    (∀ j, (34 : ℚ) * metricReal 1 j - gramReal 1 j = (1/729 : ℚ) * primitive878Real 1 j) ∧
    (∀ j, (34 : ℚ) * metricImag 1 j - gramImag 1 j = (1/729 : ℚ) * primitive878Imag 1 j) := by
  decide +kernel

/-- Coefficient row 2 for the stated finite source data. -/
private theorem coefficient_row_2 :
    (∀ j, gramReal 2 j - metricReal 2 j = (1/1458 : ℚ) * primitive521Real 2 j) ∧
    (∀ j, gramImag 2 j - metricImag 2 j = (1/1458 : ℚ) * primitive521Imag 2 j) ∧
    (∀ j, (34 : ℚ) * metricReal 2 j - gramReal 2 j = (1/729 : ℚ) * primitive878Real 2 j) ∧
    (∀ j, (34 : ℚ) * metricImag 2 j - gramImag 2 j = (1/729 : ℚ) * primitive878Imag 2 j) := by
  decide +kernel

/-- Coefficient row 3 for the stated finite source data. -/
private theorem coefficient_row_3 :
    (∀ j, gramReal 3 j - metricReal 3 j = (1/1458 : ℚ) * primitive521Real 3 j) ∧
    (∀ j, gramImag 3 j - metricImag 3 j = (1/1458 : ℚ) * primitive521Imag 3 j) ∧
    (∀ j, (34 : ℚ) * metricReal 3 j - gramReal 3 j = (1/729 : ℚ) * primitive878Real 3 j) ∧
    (∀ j, (34 : ℚ) * metricImag 3 j - gramImag 3 j = (1/729 : ℚ) * primitive878Imag 3 j) := by
  decide +kernel

/-- Coefficient row 4 for the stated finite source data. -/
private theorem coefficient_row_4 :
    (∀ j, gramReal 4 j - metricReal 4 j = (1/1458 : ℚ) * primitive521Real 4 j) ∧
    (∀ j, gramImag 4 j - metricImag 4 j = (1/1458 : ℚ) * primitive521Imag 4 j) ∧
    (∀ j, (34 : ℚ) * metricReal 4 j - gramReal 4 j = (1/729 : ℚ) * primitive878Real 4 j) ∧
    (∀ j, (34 : ℚ) * metricImag 4 j - gramImag 4 j = (1/729 : ℚ) * primitive878Imag 4 j) := by
  decide +kernel

/-- Coefficient row 5 for the stated finite source data. -/
private theorem coefficient_row_5 :
    (∀ j, gramReal 5 j - metricReal 5 j = (1/1458 : ℚ) * primitive521Real 5 j) ∧
    (∀ j, gramImag 5 j - metricImag 5 j = (1/1458 : ℚ) * primitive521Imag 5 j) ∧
    (∀ j, (34 : ℚ) * metricReal 5 j - gramReal 5 j = (1/729 : ℚ) * primitive878Real 5 j) ∧
    (∀ j, (34 : ℚ) * metricImag 5 j - gramImag 5 j = (1/729 : ℚ) * primitive878Imag 5 j) := by
  decide +kernel

/-- Coefficient row 6 for the stated finite source data. -/
private theorem coefficient_row_6 :
    (∀ j, gramReal 6 j - metricReal 6 j = (1/1458 : ℚ) * primitive521Real 6 j) ∧
    (∀ j, gramImag 6 j - metricImag 6 j = (1/1458 : ℚ) * primitive521Imag 6 j) ∧
    (∀ j, (34 : ℚ) * metricReal 6 j - gramReal 6 j = (1/729 : ℚ) * primitive878Real 6 j) ∧
    (∀ j, (34 : ℚ) * metricImag 6 j - gramImag 6 j = (1/729 : ℚ) * primitive878Imag 6 j) := by
  decide +kernel

/-- Coefficient row 7 for the stated finite source data. -/
private theorem coefficient_row_7 :
    (∀ j, gramReal 7 j - metricReal 7 j = (1/1458 : ℚ) * primitive521Real 7 j) ∧
    (∀ j, gramImag 7 j - metricImag 7 j = (1/1458 : ℚ) * primitive521Imag 7 j) ∧
    (∀ j, (34 : ℚ) * metricReal 7 j - gramReal 7 j = (1/729 : ℚ) * primitive878Real 7 j) ∧
    (∀ j, (34 : ℚ) * metricImag 7 j - gramImag 7 j = (1/729 : ℚ) * primitive878Imag 7 j) := by
  decide +kernel

/-- Coefficient row 8 for the stated finite source data. -/
private theorem coefficient_row_8 :
    (∀ j, gramReal 8 j - metricReal 8 j = (1/1458 : ℚ) * primitive521Real 8 j) ∧
    (∀ j, gramImag 8 j - metricImag 8 j = (1/1458 : ℚ) * primitive521Imag 8 j) ∧
    (∀ j, (34 : ℚ) * metricReal 8 j - gramReal 8 j = (1/729 : ℚ) * primitive878Real 8 j) ∧
    (∀ j, (34 : ℚ) * metricImag 8 j - gramImag 8 j = (1/729 : ℚ) * primitive878Imag 8 j) := by
  decide +kernel

/-- Coefficient row 9 for the stated finite source data. -/
private theorem coefficient_row_9 :
    (∀ j, gramReal 9 j - metricReal 9 j = (1/1458 : ℚ) * primitive521Real 9 j) ∧
    (∀ j, gramImag 9 j - metricImag 9 j = (1/1458 : ℚ) * primitive521Imag 9 j) ∧
    (∀ j, (34 : ℚ) * metricReal 9 j - gramReal 9 j = (1/729 : ℚ) * primitive878Real 9 j) ∧
    (∀ j, (34 : ℚ) * metricImag 9 j - gramImag 9 j = (1/729 : ℚ) * primitive878Imag 9 j) := by
  decide +kernel

/-- Coefficient row 10 for the stated finite source data. -/
private theorem coefficient_row_10 :
    (∀ j, gramReal 10 j - metricReal 10 j = (1/1458 : ℚ) * primitive521Real 10 j) ∧
    (∀ j, gramImag 10 j - metricImag 10 j = (1/1458 : ℚ) * primitive521Imag 10 j) ∧
    (∀ j, (34 : ℚ) * metricReal 10 j - gramReal 10 j = (1/729 : ℚ) * primitive878Real 10 j) ∧
    (∀ j, (34 : ℚ) * metricImag 10 j - gramImag 10 j = (1/729 : ℚ) * primitive878Imag 10 j) := by
  decide +kernel

/-- Coefficient row 11 for the stated finite source data. -/
private theorem coefficient_row_11 :
    (∀ j, gramReal 11 j - metricReal 11 j = (1/1458 : ℚ) * primitive521Real 11 j) ∧
    (∀ j, gramImag 11 j - metricImag 11 j = (1/1458 : ℚ) * primitive521Imag 11 j) ∧
    (∀ j, (34 : ℚ) * metricReal 11 j - gramReal 11 j = (1/729 : ℚ) * primitive878Real 11 j) ∧
    (∀ j, (34 : ℚ) * metricImag 11 j - gramImag 11 j = (1/729 : ℚ) * primitive878Imag 11 j) := by
  decide +kernel

/-- Coefficient row 12 for the stated finite source data. -/
private theorem coefficient_row_12 :
    (∀ j, gramReal 12 j - metricReal 12 j = (1/1458 : ℚ) * primitive521Real 12 j) ∧
    (∀ j, gramImag 12 j - metricImag 12 j = (1/1458 : ℚ) * primitive521Imag 12 j) ∧
    (∀ j, (34 : ℚ) * metricReal 12 j - gramReal 12 j = (1/729 : ℚ) * primitive878Real 12 j) ∧
    (∀ j, (34 : ℚ) * metricImag 12 j - gramImag 12 j = (1/729 : ℚ) * primitive878Imag 12 j) := by
  decide +kernel

/-- Coefficient row 13 for the stated finite source data. -/
private theorem coefficient_row_13 :
    (∀ j, gramReal 13 j - metricReal 13 j = (1/1458 : ℚ) * primitive521Real 13 j) ∧
    (∀ j, gramImag 13 j - metricImag 13 j = (1/1458 : ℚ) * primitive521Imag 13 j) ∧
    (∀ j, (34 : ℚ) * metricReal 13 j - gramReal 13 j = (1/729 : ℚ) * primitive878Real 13 j) ∧
    (∀ j, (34 : ℚ) * metricImag 13 j - gramImag 13 j = (1/729 : ℚ) * primitive878Imag 13 j) := by
  decide +kernel

/-- Coefficient row 14 for the stated finite source data. -/
private theorem coefficient_row_14 :
    (∀ j, gramReal 14 j - metricReal 14 j = (1/1458 : ℚ) * primitive521Real 14 j) ∧
    (∀ j, gramImag 14 j - metricImag 14 j = (1/1458 : ℚ) * primitive521Imag 14 j) ∧
    (∀ j, (34 : ℚ) * metricReal 14 j - gramReal 14 j = (1/729 : ℚ) * primitive878Real 14 j) ∧
    (∀ j, (34 : ℚ) * metricImag 14 j - gramImag 14 j = (1/729 : ℚ) * primitive878Imag 14 j) := by
  decide +kernel

/-- Lower coefficient parts for the stated finite source data. -/
theorem lower_coefficient_parts :
    gramReal - metricReal = (1/1458 : ℚ) • primitive521Real ∧
    gramImag - metricImag = (1/1458 : ℚ) • primitive521Imag := by
  constructor
  · ext i j
    fin_cases i

    · exact coefficient_row_0.1 j
    · exact coefficient_row_1.1 j
    · exact coefficient_row_2.1 j
    · exact coefficient_row_3.1 j
    · exact coefficient_row_4.1 j
    · exact coefficient_row_5.1 j
    · exact coefficient_row_6.1 j
    · exact coefficient_row_7.1 j
    · exact coefficient_row_8.1 j
    · exact coefficient_row_9.1 j
    · exact coefficient_row_10.1 j
    · exact coefficient_row_11.1 j
    · exact coefficient_row_12.1 j
    · exact coefficient_row_13.1 j
    · exact coefficient_row_14.1 j

  · ext i j
    fin_cases i

    · exact coefficient_row_0.2.1 j
    · exact coefficient_row_1.2.1 j
    · exact coefficient_row_2.2.1 j
    · exact coefficient_row_3.2.1 j
    · exact coefficient_row_4.2.1 j
    · exact coefficient_row_5.2.1 j
    · exact coefficient_row_6.2.1 j
    · exact coefficient_row_7.2.1 j
    · exact coefficient_row_8.2.1 j
    · exact coefficient_row_9.2.1 j
    · exact coefficient_row_10.2.1 j
    · exact coefficient_row_11.2.1 j
    · exact coefficient_row_12.2.1 j
    · exact coefficient_row_13.2.1 j
    · exact coefficient_row_14.2.1 j

/-- Upper coefficient parts for the stated finite source data. -/
theorem upper_coefficient_parts :
    (34 : ℚ) • metricReal - gramReal = (1/729 : ℚ) • primitive878Real ∧
    (34 : ℚ) • metricImag - gramImag = (1/729 : ℚ) • primitive878Imag := by
  constructor
  · ext i j
    fin_cases i

    · exact coefficient_row_0.2.2.1 j
    · exact coefficient_row_1.2.2.1 j
    · exact coefficient_row_2.2.2.1 j
    · exact coefficient_row_3.2.2.1 j
    · exact coefficient_row_4.2.2.1 j
    · exact coefficient_row_5.2.2.1 j
    · exact coefficient_row_6.2.2.1 j
    · exact coefficient_row_7.2.2.1 j
    · exact coefficient_row_8.2.2.1 j
    · exact coefficient_row_9.2.2.1 j
    · exact coefficient_row_10.2.2.1 j
    · exact coefficient_row_11.2.2.1 j
    · exact coefficient_row_12.2.2.1 j
    · exact coefficient_row_13.2.2.1 j
    · exact coefficient_row_14.2.2.1 j

  · ext i j
    fin_cases i

    · exact coefficient_row_0.2.2.2 j
    · exact coefficient_row_1.2.2.2 j
    · exact coefficient_row_2.2.2.2 j
    · exact coefficient_row_3.2.2.2 j
    · exact coefficient_row_4.2.2.2 j
    · exact coefficient_row_5.2.2.2 j
    · exact coefficient_row_6.2.2.2 j
    · exact coefficient_row_7.2.2.2 j
    · exact coefficient_row_8.2.2.2 j
    · exact coefficient_row_9.2.2.2 j
    · exact coefficient_row_10.2.2.2 j
    · exact coefficient_row_11.2.2.2 j
    · exact coefficient_row_12.2.2.2 j
    · exact coefficient_row_13.2.2.2 j
    · exact coefficient_row_14.2.2.2 j

noncomputable def cornerStack : Matrix (Fin 96) (Fin 15) ℂ :=
  fromParts stackReal stackImag

noncomputable def cornerMetric : Matrix (Fin 15) (Fin 15) ℂ :=
  fromParts metricReal metricImag

noncomputable def cornerGram : Matrix (Fin 15) (Fin 15) ℂ :=
  cornerStack.conjTranspose * cornerStack

/-- Corner Gram eq parts for the stated finite source data. -/
theorem cornerGram_eq_parts : cornerGram = fromParts gramReal gramImag :=
  fromParts_gram stackReal stackImag

/-- Corner Gram lower identity for the stated finite source data. -/
theorem cornerGram_lower_identity :
    cornerGram - cornerMetric = (1/1458 : ℝ) • primitive521 := by
  rw [cornerGram_eq_parts]
  change fromParts gramReal gramImag - fromParts metricReal metricImag = _
  rw [← fromParts_sub, lower_coefficient_parts.1, lower_coefficient_parts.2]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using!
    fromParts_rat_smul (1/1458 : ℚ) primitive521Real primitive521Imag

/-- Corner Gram upper identity for the stated finite source data. -/
theorem cornerGram_upper_identity :
    (34 : ℝ) • cornerMetric - cornerGram = (1/729 : ℝ) • primitive878 := by
  rw [cornerGram_eq_parts]
  have hs : (34 : ℝ) • cornerMetric =
      fromParts ((34 : ℚ) • metricReal) ((34 : ℚ) • metricImag) := by
    simpa only [Rat.cast_ofNat] using!
      (fromParts_rat_smul (34 : ℚ) metricReal metricImag).symm
  rw [hs, ← fromParts_sub, upper_coefficient_parts.1, upper_coefficient_parts.2]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using!
    fromParts_rat_smul (1/729 : ℚ) primitive878Real primitive878Imag

/-- Corner Gram lower pos Semidef for the stated finite source data. -/
theorem cornerGram_lower_posSemidef : (cornerGram - cornerMetric).PosSemidef := by
  rw [cornerGram_lower_identity]
  exact primitive521_posSemidef.smul (by norm_num : (0 : ℝ) ≤ 1/1458)

/-- Corner Gram upper pos Semidef for the stated finite source data. -/
theorem cornerGram_upper_posSemidef : ((34 : ℝ) • cornerMetric - cornerGram).PosSemidef := by
  rw [cornerGram_upper_identity]
  exact primitive878_posSemidef.smul (by norm_num : (0 : ℝ) ≤ 1/729)

/-- Corner Gram sandwich for the stated finite source data. -/
theorem cornerGram_sandwich :
    (cornerGram - cornerMetric).PosSemidef ∧
      ((34 : ℝ) • cornerMetric - cornerGram).PosSemidef :=
  ⟨cornerGram_lower_posSemidef, cornerGram_upper_posSemidef⟩


noncomputable def literalSource (a : Fin 6) : Matrix (Fin 4) (Fin 4) ℂ :=
  fromParts (sourceReal a) (sourceImag a)

noncomputable def literalInput (c : Fin 15) : Matrix (Fin 4) (Fin 4) ℂ :=
  fromParts (inputMatrixReal c) (inputMatrixImag c)

/-- Literal Source eq source for the stated finite source data. -/
theorem literalSource_eq_source (a : Fin 6) : literalSource a = ThreeLevelWordDual.source a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [literalSource, fromParts, sourceReal, sourceImag, ThreeLevelWordDual.source,
      ThreeLevelWordDual.sourceLabel, ExchangeCell.proposals]

/-- Literal Input zero for the stated finite source data. -/
theorem literalInput_zero : literalInput 0 = ThreeLevelWordDual.pOne + ThreeLevelWordDual.pTwo := by
  rw [ThreeLevelWordDual.pTwo_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [literalInput, fromParts, inputMatrixReal, inputMatrixImag,
      inputReal, inputImag, flatIndex, ThreeLevelWordDual.pOne] <;> ring

/-- Literal Input one for the stated finite source data. -/
theorem literalInput_one : literalInput 1 = ThreeLevelWordDual.pTwo := by
  rw [ThreeLevelWordDual.pTwo_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [literalInput, fromParts, inputMatrixReal, inputMatrixImag,
      inputReal, inputImag, flatIndex] <;> ring

/-- Parts mul for the stated finite source data. -/
theorem parts_mul {m n p : ℕ} (R I : Matrix (Fin m) (Fin n) ℚ)
    (S T : Matrix (Fin n) (Fin p) ℚ) :
    fromParts R I * fromParts S T =
      fromParts (R * S - I * T) (R * T + I * S) := by
  ext i j : 2
  apply Complex.ext <;>
    simp [fromParts, Matrix.mul_apply, Complex.mul_re, Complex.mul_im,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]


/-- Literal commutator parts for the stated finite source data. -/
theorem literal_commutator_parts (a : Fin 6) (c : Fin 15) :
    literalSource a * literalInput c - literalInput c * literalSource a =
      fromParts (commutatorReal a c) (commutatorImag a c) := by
  unfold literalSource literalInput
  rw [parts_mul, parts_mul, ← fromParts_sub]
  rfl

/-- From Parts commutator apply for the stated finite source data. -/
theorem fromParts_commutator_apply (SR SI : Matrix (Fin 96) (Fin 15) ℚ)
    (hR : ∀ a c, SR a c = commutatorReal (sourceIndex a) c (rowIndex a) (columnIndex a))
    (hI : ∀ a c, SI a c = commutatorImag (sourceIndex a) c (rowIndex a) (columnIndex a))
    (a : Fin 96) (c : Fin 15) :
    fromParts SR SI a c =
      (ThreeLevelWordDual.source (sourceIndex a) * literalInput c -
        literalInput c * ThreeLevelWordDual.source (sourceIndex a))
          (rowIndex a) (columnIndex a) := by
  rw [← literalSource_eq_source, literal_commutator_parts]
  simp only [fromParts, hR, hI]

/-- From Parts actual Gradient apply for the stated finite source data. -/
theorem fromParts_actualGradient_apply (SR SI : Matrix (Fin 96) (Fin 15) ℚ)
    (hR : ∀ a c, SR a c = commutatorReal (sourceIndex a) c (rowIndex a) (columnIndex a))
    (hI : ∀ a c, SI a c = commutatorImag (sourceIndex a) c (rowIndex a) (columnIndex a))
    (σ : ThreeLevelCluster.Perm) (a : Fin 96) (c : Fin 15) :
    fromParts SR SI a c =
      ThreeLevelCluster.actualGradient σ (fun _ => 0) (sourceIndex a) (literalInput c)
        (rowIndex a) (columnIndex a) := by
  rw [ThreeLevelCluster.actualGradient_zero_energies]
  exact fromParts_commutator_apply SR SI hR hI a c

noncomputable def literalCombination (z : Fin 15 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ c, z c • literalInput c

/-- From Parts actual Gradient mul Vec for the stated finite source data. -/
theorem fromParts_actualGradient_mulVec (SR SI : Matrix (Fin 96) (Fin 15) ℚ)
    (hR : ∀ a c, SR a c = commutatorReal (sourceIndex a) c (rowIndex a) (columnIndex a))
    (hI : ∀ a c, SI a c = commutatorImag (sourceIndex a) c (rowIndex a) (columnIndex a))
    (σ : ThreeLevelCluster.Perm) (a : Fin 96) (z : Fin 15 → ℂ) :
    ((fromParts SR SI) *ᵥ z) a =
      ThreeLevelCluster.actualGradient σ (fun _ => 0) (sourceIndex a) (literalCombination z)
        (rowIndex a) (columnIndex a) := by
  rw [ThreeLevelCluster.actualGradient_zero_energies]
  simp only [Matrix.mulVec, dotProduct, literalCombination, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
    fromParts_commutator_apply SR SI hR hI]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Corner Stack eq actual Gradient for the stated finite source data. -/
theorem cornerStack_eq_actualGradient (σ : ThreeLevelCluster.Perm)
    (a : Fin 96) (c : Fin 15) :
    cornerStack a c =
      ThreeLevelCluster.actualGradient σ (fun _ => 0) (sourceIndex a) (literalInput c)
        (rowIndex a) (columnIndex a) :=
  fromParts_actualGradient_apply stackReal stackImag
    stack_parts_match_commutators.1 stack_parts_match_commutators.2 σ a c

/-- Corner Stack mul Vec eq actual Gradient for the stated finite source data. -/
theorem cornerStack_mulVec_eq_actualGradient (σ : ThreeLevelCluster.Perm)
    (a : Fin 96) (z : Fin 15 → ℂ) :
    (cornerStack *ᵥ z) a =
      ThreeLevelCluster.actualGradient σ (fun _ => 0) (sourceIndex a) (literalCombination z)
        (rowIndex a) (columnIndex a) :=
  fromParts_actualGradient_mulVec stackReal stackImag
    stack_parts_match_commutators.1 stack_parts_match_commutators.2 σ a z


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelGramCertificateCorner
