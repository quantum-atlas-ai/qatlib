/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.Order120LowGram.Population
public import Qatlib.Papers.GibbsSampl26.FiniteModels.Order120LowGram.OperatorRow0
public import Qatlib.Papers.GibbsSampl26.FiniteModels.Order120LowGram.OperatorTail0
public import Qatlib.Papers.GibbsSampl26.FiniteModels.Order120LowGram.OperatorRow1
public import Qatlib.Papers.GibbsSampl26.FiniteModels.Order120LowGram.OperatorTail1
public import Qatlib.Papers.GibbsSampl26.FiniteModels.Order120LowGram.OperatorRow2
public import Qatlib.Papers.GibbsSampl26.FiniteModels.Order120LowGram.OperatorTail2
public import Qatlib.Papers.GibbsSampl26.FiniteModels.Order120LowGram.OperatorRow3

@[expose] public section


/-!
# Complete balanced Gram certificate for the order120 low collision face

Table equality is checked in Order120LowGram.BalancedTables. The imported
certificates follow the population coordinates and the leading and trailing
coordinates of each operator row in the fast chart. This entry assembles the
unchanged full-source row interface.
-/

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowCoefficientTables
open Matrix
set_option autoImplicit false
set_option warningAsError true

/-- All twelve original complete-source Gram identities hold on every row. -/
theorem certified_gram_row (i : Fin 15) :
    (∀ j, gramBBReal i j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) i j) ∧
    (∀ j, gramBBImag i j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) i j) ∧
    (∀ j, gramBUReal i j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) i j) ∧
    (∀ j, gramBUImag i j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) i j) ∧
    (∀ j, gramBVReal i j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) i j) ∧
    (∀ j, gramBVImag i j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) i j) ∧
    (∀ j, gramUUReal i j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) i j) ∧
    (∀ j, gramUUImag i j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) i j) ∧
    (∀ j, gramUVReal i j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) i j) ∧
    (∀ j, gramUVImag i j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) i j) ∧
    (∀ j, gramVVReal i j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) i j) ∧
    (∀ j, gramVVImag i j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) i j) := by
  fin_cases i
  · exact Balanced.populationRows 0 (by decide)
  · exact Balanced.populationRows 1 (by decide)
  · exact Balanced.operatorRow0 2 (by decide)
  · exact Balanced.operatorRow0 3 (by decide)
  · exact Balanced.operatorTail0 4 (by decide)
  · exact Balanced.operatorRow1 5 (by decide)
  · exact Balanced.operatorRow1 6 (by decide)
  · exact Balanced.operatorTail1 7 (by decide)
  · exact Balanced.operatorTail1 8 (by decide)
  · exact Balanced.operatorRow2 9 (by decide)
  · exact Balanced.operatorRow2 10 (by decide)
  · exact Balanced.operatorTail2 11 (by decide)
  · exact Balanced.operatorTail2 12 (by decide)
  · exact Balanced.operatorRow3 13 (by decide)
  · exact Balanced.operatorRow3 14 (by decide)

end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowCoefficientTables
