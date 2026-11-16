/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PPTCompose26.Composition.Main
public import Qatlib.Papers.PPTCompose26.Composition.AtLeast
public import Qatlib.Papers.PPTCompose26.Composition.ChoiBridge
public import Qatlib.Papers.PPTCompose26.Composition.NonTrivial
public import Qatlib.Papers.PPTCompose26.Composition.Counterexample

@[expose] public section


/-!
# PPT composition results and boundary checks

The finite complex-matrix definitions and supporting decompositions live in
`Qatlib.Foundations.PPTMatrix.OperatorCones`. This paper import cone includes:

* `Main`: the `2 j`-map theorem, Schmidt-number descent, and index bounds;
* `AtLeast`: compositions of at least `2 j` PPT maps;
* `ChoiBridge`: Choi criteria for complete positivity, PPT, and entanglement breaking;
* `NonTrivial`: an entangled positive input and the non-entanglement-breaking identity;
* `Counterexample`: complete copositivity of transpose without complete positivity.
-/
