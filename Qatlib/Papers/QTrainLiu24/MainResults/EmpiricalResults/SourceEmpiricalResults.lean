/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QTrainLiu24.MainResults.EmpiricalResults

Paper: Chen-Yu Liu et al., *Quantum-Train: Rethinking Hybrid Quantum-Classical
Machine Learning in the Model Compression Perspective*, fixed arXiv:2405.11304v2.

Claim c003: the empirical classification results of §III–IV and Tables I–III
(p.12). These are *observations* on MNIST, FashionMNIST and CIFAR-10; the claim
explicitly does **not** register them as worst-case accuracy, generalisation, or
complexity-separation guarantees.

This module records the reported numbers as data and proves only arithmetic
facts about them:

* `EmpiricalRecord` bundles the classical parameter count `M`, the QT
  trainable-parameter count, and the two observed test accuracies (in percent).
* `mnistRecord`, `fashionRecord`, `cifarRecord` copy Tables I–III.
* For each dataset the trainable-parameter count is strictly smaller than the
  classical count and the observed test accuracy shows only a slight decrease
  (`*_params_lt`, `*_acc_le`, `*_accuracy_gap`).
* Parameter-ratio upper bounds match the text's "24.3% / 27.2% / 8.1%" remarks
  (reported as safe decimal ceilings).

Nothing here asserts a bound on unseen-data error.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QTrainLiu24.MainResults.EmpiricalResults

/-- An empirical QT-vs-classical record: parameter sizes and observed test
accuracies (in percent), exactly as tabulated in Tables I–III (p.12). -/
structure EmpiricalRecord where
  /-- Classical-network parameter count `M` (Eq. (1)). -/
  classicalParams : ℕ
  /-- QT trainable-parameter count (QNN + mapping model). -/
  qtParams : ℕ
  /-- Classical test accuracy, in percent. -/
  classicalAcc : ℚ
  /-- QT test accuracy, in percent. -/
  qtAcc : ℚ

/-- Table I (MNIST), classical CNN `M = 6690`, QT-106 with `1627` parameters,
classical accuracy `98.45%`, QT accuracy `93.81%`. -/
def mnistRecord : EmpiricalRecord :=
  { classicalParams := 6690, qtParams := 1627,
    classicalAcc := 9845 / 100, qtAcc := 9381 / 100 }

/-- Table II (FashionMNIST), classical CNN `M = 6690`, QT-121 with `1822`
parameters, classical `88.14%`, QT `80.74%`. -/
def fashionRecord : EmpiricalRecord :=
  { classicalParams := 6690, qtParams := 1822,
    classicalAcc := 8814 / 100, qtAcc := 8074 / 100 }

/-- Table III (CIFAR-10), classical CNN `M = 285226`, QT-323 with `23258`
parameters, classical `62.50%`, QT `60.69%`. -/
def cifarRecord : EmpiricalRecord :=
  { classicalParams := 285226, qtParams := 23258,
    classicalAcc := 6250 / 100, qtAcc := 6069 / 100 }

/-! ## MNIST (Table I) -/

/-- Table I: QT-106 uses strictly fewer trainable parameters than the classical
network. -/
theorem mnist_params_lt : mnistRecord.qtParams < mnistRecord.classicalParams := by
  norm_num [mnistRecord]

/-- Table I: the observed MNIST test accuracy does not exceed the classical one
(slight decrease). -/
theorem mnist_acc_le : mnistRecord.qtAcc ≤ mnistRecord.classicalAcc := by
  norm_num [mnistRecord]

/-- Table I: the MNIST accuracy decrease is at most 5 percentage points. -/
theorem mnist_accuracy_gap : mnistRecord.classicalAcc - mnistRecord.qtAcc ≤ 5 := by
  norm_num [mnistRecord]

/-- Table I and p.6: QT uses under 24.4% of the classical MNIST parameters
(the text rounds this to 24.3%). -/
theorem mnist_param_ratio :
    1000 * mnistRecord.qtParams ≤ 244 * mnistRecord.classicalParams := by
  norm_num [mnistRecord]

/-! ## FashionMNIST (Table II) -/

/-- Table II: QT-121 uses strictly fewer trainable parameters. -/
theorem fashion_params_lt : fashionRecord.qtParams < fashionRecord.classicalParams := by
  norm_num [fashionRecord]

/-- Table II: observed FashionMNIST accuracy does not exceed the classical one. -/
theorem fashion_acc_le : fashionRecord.qtAcc ≤ fashionRecord.classicalAcc := by
  norm_num [fashionRecord]

/-- Table II: the FashionMNIST accuracy decrease is at most 8 percentage points. -/
theorem fashion_accuracy_gap :
    fashionRecord.classicalAcc - fashionRecord.qtAcc ≤ 8 := by
  norm_num [fashionRecord]

/-- Table II and p.6: QT uses under 27.3% of the classical FashionMNIST
parameters (the text rounds this to 27.2%). -/
theorem fashion_param_ratio :
    1000 * fashionRecord.qtParams ≤ 273 * fashionRecord.classicalParams := by
  norm_num [fashionRecord]

/-! ## CIFAR-10 (Table III) -/

/-- Table III: QT-323 uses strictly fewer trainable parameters. -/
theorem cifar_params_lt : cifarRecord.qtParams < cifarRecord.classicalParams := by
  norm_num [cifarRecord]

/-- Table III: observed CIFAR-10 accuracy does not exceed the classical one. -/
theorem cifar_acc_le : cifarRecord.qtAcc ≤ cifarRecord.classicalAcc := by
  norm_num [cifarRecord]

/-- Table III: the CIFAR-10 accuracy decrease is at most 2 percentage points. -/
theorem cifar_accuracy_gap : cifarRecord.classicalAcc - cifarRecord.qtAcc ≤ 2 := by
  norm_num [cifarRecord]

/-- Table III and p.6: QT uses under 8.2% of the classical CIFAR-10 parameters
(the text quotes 8.1%). -/
theorem cifar_param_ratio :
    1000 * cifarRecord.qtParams ≤ 82 * cifarRecord.classicalParams := by
  norm_num [cifarRecord]

/-! ## Combined empirical statement -/

/-- All three datasets show strict parameter reduction with a slight empirical
accuracy decrease. This is an empirical observation only — no worst-case
accuracy, generalisation, or separation claim (claim c003 boundary). -/
theorem all_datasets_reduction :
    mnistRecord.qtParams < mnistRecord.classicalParams ∧
    fashionRecord.qtParams < fashionRecord.classicalParams ∧
    cifarRecord.qtParams < cifarRecord.classicalParams ∧
    mnistRecord.qtAcc ≤ mnistRecord.classicalAcc ∧
    fashionRecord.qtAcc ≤ fashionRecord.classicalAcc ∧
    cifarRecord.qtAcc ≤ cifarRecord.classicalAcc :=
  ⟨mnist_params_lt, fashion_params_lt, cifar_params_lt,
    mnist_acc_le, fashion_acc_le, cifar_acc_le⟩

end Qatlib.Papers.QTrainLiu24.MainResults.EmpiricalResults
