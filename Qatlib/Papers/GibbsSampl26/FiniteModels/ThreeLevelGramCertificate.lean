/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Kernel-checked literal Gram certificates

The two complete 15 by 15 Hermitian matrices are the scalar-corner primitive
coefficients of the frozen three-level uniform Gram certificate. A rational
LDL identity is checked by ordinary kernel reduction, then transported to the
literal complex matrix through a proved diagonal phase congruence.

The external generator supplies data only. Neither external computation,
hashes nor positive-matrix hypotheses are premises of the concrete results.
The symbolic physical-stack and continuum coefficient identities are separate
obligations; this module alone does not discharge ScaledStackBounds.
-/


namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelGramCertificate
open Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
-- Let computable finite predicates unfold the matrix/function abbreviations
-- during instance synthesis, as in the pre-4.35 elaborator.
set_option backward.isDefEq.respectTransparency false

noncomputable def complexify {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin n) ℂ := M.map (Rat.castHom ℂ)

/-- Complexify mul for the stated finite source data. -/
theorem complexify_mul {m n p : ℕ} (M : Matrix (Fin m) (Fin n) ℚ)
    (N : Matrix (Fin n) (Fin p) ℚ) :
    complexify (M * N) = complexify M * complexify N := by
  exact Matrix.map_mul

/-- Complexify transpose for the stated finite source data. -/
theorem complexify_transpose {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) :
    complexify M.transpose = (complexify M).conjTranspose := by
  ext i j
  simp [complexify, Matrix.conjTranspose_apply]

/-- Complexify diagonal for the stated finite source data. -/
theorem complexify_diagonal {n : ℕ} (d : Fin n → ℚ) :
    complexify (Matrix.diagonal d) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  by_cases h : i = j <;> simp [complexify, Matrix.diagonal, h]

/-- Complexify pos Semidef of ldl for the stated finite source data. -/
theorem complexify_posSemidef_of_ldl {n : ℕ}
    (M L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (hfactor : M = L * Matrix.diagonal d * L.transpose)
    (hdiag : ∀ i, 0 ≤ d i) :
    (complexify M).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => (d i : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change 0 ≤ (d i : ℝ) ∧ (0 : ℝ) = 0
    exact ⟨Rat.cast_nonneg.mpr (hdiag i), rfl⟩
  rw [hfactor, complexify_mul, complexify_mul, complexify_diagonal, complexify_transpose]
  exact hd.mul_mul_conjTranspose_same (complexify L)

def checkLDL {n : ℕ} (M L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) : Bool :=
  decide ((∀ i j, M i j = ∑ k, L i k * d k * L j k) ∧ ∀ i, 0 ≤ d i)

/-- Check LDL sound for the stated finite source data. -/
theorem checkLDL_sound {n : ℕ}
    (M L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (h : checkLDL M L d = true) : (complexify M).PosSemidef := by
  have hc : (∀ i j, M i j = ∑ k, L i k * d k * L j k) ∧ ∀ i, 0 ≤ d i :=
    of_decide_eq_true h
  have hf : M = L * Matrix.diagonal d * L.transpose := by
    ext i j
    change M i j = ∑ k, (L * Matrix.diagonal d) i k * L j k
    simp only [Matrix.mul_diagonal]
    exact hc.1 i j
  exact complexify_posSemidef_of_ldl M L d hf hc.2


def rational521 : Matrix (Fin 15) (Fin 15) ℚ :=
  !![16542, 9576, 2592, 1296, 0, (-2592), (-192), 1056, 240, (-1296), 1056, (-2496), 480, 0, (-240);
    9576, 11358, 2592, 1296, 0, (-2592), 1536, 1272, 24, (-1296), 1272, (-444), 48, 0, (-24);
    2592, 2592, 16038, 0, 0, 0, 864, (-864), 864, 0, (-864), (-432), (-4104), 0, (-864);
    1296, 1296, 0, 16038, 0, 0, 432, (-432), (-5400), 0, (-432), (-216), 864, 0, (-432);
    0, 0, 0, 0, 21870, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-2592), (-2592), 0, 0, 0, 16038, (-864), 864, (-864), 0, 864, 432, (-1728), 0, 864;
    (-192), 1536, 864, 432, 0, (-864), 7520, 1300, (-868), (-432), 1300, (-2032), (-1736), 0, 868;
    1056, 1272, (-864), (-432), 0, 864, 1300, 19850, 1588, 432, (-2020), (-434), 3176, 0, (-1588);
    240, 24, 864, (-5400), 0, (-864), (-868), 1588, 14882, (-432), 1588, 218, (-2312), 0, 1156;
    (-1296), (-1296), 0, 0, 0, 0, (-432), 432, (-432), 16038, 432, 216, (-864), 0, (-5400);
    1056, 1272, (-864), (-432), 0, 864, 1300, (-2020), 1588, 432, 19850, (-434), 3176, 0, (-1588);
    (-2496), (-444), (-432), (-216), 0, 432, (-2032), (-434), 218, 216, (-434), 8171, 436, 0, (-218);
    480, 48, (-4104), 864, 0, (-1728), (-1736), 3176, (-2312), (-864), 3176, 436, 11414, 0, 2312;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21870, 0;
    (-240), (-24), (-864), (-432), 0, 864, 868, (-1588), 1156, (-5400), (-1588), (-218), 2312, 0, 14882]

def lower521 : Matrix (Fin 15) (Fin 15) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (532/919), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (144/919), (688/3665), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (72/919), (344/3665), (-768/38779), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-144/919), (-688/3665), (1536/38779), (768/38395), 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-32/2757), (9344/32985), (13232/349011), (6616/345555), 0, (-13232/331731), 1, 0, 0, 0, 0, 0, 0, 0, 0;
    (176/2757), (3748/32985), (-26096/349011), (-1864/49365), 0, (26096/331731), (1257935/7165672), 1, 0, 0, 0, 0, 0, 0, 0;
    (40/2757), (-652/32985), (19184/349011), (-1290532/3801105), 0, (-183376/3649041), (-811355/7165672), (4043719/47396801), 1, 0, 0, 0, 0, 0, 0;
    (-72/919), (-344/3665), (768/38779), (384/38395), 0, (-768/36859), (-81873/1791418), (1688148/47396801), (-5933686/151739739), 1, 0, 0, 0, 0, 0;
    (176/2757), (3748/32985), (-26096/349011), (-1864/49365), 0, (26096/331731), (1257935/7165672), (-6345739/47396801), (44480909/303479478), (537346/9973661), 1, 0, 0, 0, 0;
    (-416/2757), (5678/32985), (-5176/349011), (-2588/345555), 0, (5176/331731), (-594857/1791418), (-51392/47396801), (-36784/151739739), (12320/9973661), (-352/269609), 1, 0, 0, 0;
    (80/2757), (-1304/32985), (-596/2223), (183376/3801105), 0, (-366752/3649041), (-811355/3582836), (8087438/47396801), (-28298129/151739739), (-7551964/109710271), (2/9), 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    (-40/2757), (652/32985), (-19184/349011), (-9592/345555), 0, (19184/331731), (930443/7165672), (-4657591/47396801), (10871179/101159826), (-36118662/109710271), (-1/9), 0, (2/5), 0, 1]

def diagonal521 : Fin 15 → ℚ :=
  ![16542, (5343570/919), (56539782/3665), (615779010/38779), 21870, (591144642/38395), (257964192/36859), (34552267929/1791418), (6637096183860/521364811), (266595958530/16859971), (185734988145/9973661), (1844739603/269609), (85050/11), 21870, (122472/11)]

/-- Certificate521 for the stated finite source data. -/
theorem certificate521 : checkLDL rational521 lower521 diagonal521 = true := by
  decide +kernel

/-- Rational521 pos Semidef for the stated finite source data. -/
theorem rational521_posSemidef : (complexify rational521).PosSemidef :=
  checkLDL_sound rational521 lower521 diagonal521 certificate521

def rational878 : Matrix (Fin 15) (Fin 15) ℚ :=
  !![15786, (-4788), (-1296), (-648), 0, 1296, 96, (-528), (-120), 648, (-528), 1248, (-240), 0, 120;
    (-4788), 18378, (-1296), (-648), 0, 1296, (-768), (-636), (-12), 648, (-636), 222, (-24), 0, 12;
    (-1296), (-1296), 16038, 0, 0, 0, (-432), 432, (-432), 0, 432, 216, 2052, 0, 432;
    (-648), (-648), 0, 16038, 0, 0, (-216), 216, 2700, 0, 216, 108, (-432), 0, 216;
    0, 0, 0, 0, 13122, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1296, 1296, 0, 0, 0, 16038, 432, (-432), 432, 0, (-432), (-216), 864, 0, (-432);
    96, (-768), (-432), (-216), 0, 432, 10496, 1132, (-1348), 216, 1132, (-6112), (-2696), 0, 1348;
    (-528), (-636), 432, 216, 0, (-432), 1132, 12350, 988, (-216), (-772), (-674), 1976, 0, (-988);
    (-120), (-12), (-432), 2700, 0, 432, (-1348), 988, 14834, 216, 988, 782, (-2408), 0, 1204;
    648, 648, 0, 0, 0, 0, 216, (-216), 216, 16038, (-216), (-108), 432, 0, 2700;
    (-528), (-636), 432, 216, 0, (-432), 1132, (-772), 988, (-216), 12350, (-674), 1976, 0, (-988);
    1248, 222, 216, 108, 0, (-216), (-6112), (-674), 782, (-108), (-674), 11507, 1564, 0, (-782);
    (-240), (-24), 2052, (-432), 0, 864, (-2696), 1976, (-2408), 432, 1976, 1564, 11222, 0, 2408;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13122, 0;
    120, 12, 432, 216, 0, (-432), 1348, (-988), 1204, 2700, (-988), (-782), 2408, 0, 14834]

def lower878 : Matrix (Fin 15) (Fin 15) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-266/877), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-72/877), (-1016/10181), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-36/877), (-508/10181), (-960/110071), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (72/877), (1016/10181), (1920/110071), (960/109591), 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (16/2631), (-4000/91629), (-31288/990639), (-15644/986319), 0, (31288/969039), 1, 0, 0, 0, 0, 0, 0, 0, 0;
    (-88/2631), (-4310/91629), (19432/990639), (9716/986319), 0, (-19432/969039), (3358493/31185688), 1, 0, 0, 0, 0, 0, 0, 0;
    (-20/2631), (-262/91629), (-28072/990639), (1826882/10849509), 0, (291512/10659429), (-3992075/31185688), (11939233/130047413), 1, 0, 0, 0, 0, 0, 0;
    (36/877), (508/10181), (960/110071), (480/109591), 0, (-960/107671), (387189/15592844), (-2017950/130047413), (14704679/767611302), 1, 0, 0, 0, 0, 0;
    (-88/2631), (-4310/91629), (19432/990639), (9716/986319), 0, (-19432/969039), (3358493/31185688), (-10288183/130047413), (131331563/1535222604), (-1205549/84832676), 1, 0, 0, 0, 0;
    (208/2631), (3251/91629), (23780/990639), (410/34011), 0, (-23780/969039), (-4535555/7796422), (344080/130047413), (4235/22576803), (-60775/21208169), (748/264733), 1, 0, 0, 0;
    (-40/2631), (-524/91629), (9778/76203), (-291512/10849509), 0, (583024/10659429), (-3992075/15592844), (23878466/130047413), (-155393765/767611302), (17378257/466579718), (2/9), 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    (20/2631), (262/91629), (28072/990639), (484/34011), 0, (-28072/969039), (4132871/31185688), (-12306133/130047413), (53580307/511740868), (152287095/933159436), (-1/9), 0, (2/5), 0, 1]

def diagonal878 : Fin 15 → ℚ :=
  ![15786, (14843898/877), (160483518/10181), (1757620458/110071), 13122, (1726827498/109591), (1122684768/107671), (94804564077/7796422), (20145191009688/1430521543), (2040819686532/127935217), (1016094229605/84832676), (2074714317/264733), (94770/11), 13122, (682344/55)]

/-- Certificate878 for the stated finite source data. -/
theorem certificate878 : checkLDL rational878 lower878 diagonal878 = true := by
  decide +kernel

/-- Rational878 pos Semidef for the stated finite source data. -/
theorem rational878_posSemidef : (complexify rational878).PosSemidef :=
  checkLDL_sound rational878 lower878 diagonal878 certificate878


noncomputable def fromParts {m n : ℕ}
    (R I : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => (R i j : ℂ) + (I i j : ℂ) * Complex.I

def phaseReal : Fin 15 → ℚ :=
  ![1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0]

def phaseImag : Fin 15 → ℚ :=
  ![0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1]

noncomputable def phases : Fin 15 → ℂ :=
  fun i => (phaseReal i : ℂ) + (phaseImag i : ℂ) * Complex.I

noncomputable def phaseGauge (M : Matrix (Fin 15) (Fin 15) ℚ) :
    Matrix (Fin 15) (Fin 15) ℂ :=
  fun i j => phases i * (M i j : ℂ) * star (phases j)

/-- Phase Gauge eq congruence for the stated finite source data. -/
theorem phaseGauge_eq_congruence (M : Matrix (Fin 15) (Fin 15) ℚ) :
    phaseGauge M =
      Matrix.diagonal phases * complexify M * (Matrix.diagonal phases).conjTranspose := by
  ext i j
  simp [phaseGauge, complexify, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- Phase Gauge pos Semidef for the stated finite source data. -/
theorem phaseGauge_posSemidef (M : Matrix (Fin 15) (Fin 15) ℚ)
    (h : (complexify M).PosSemidef) : (phaseGauge M).PosSemidef := by
  rw [phaseGauge_eq_congruence]
  exact h.mul_mul_conjTranspose_same (Matrix.diagonal phases)

/-- From Parts eq phase Gauge for the stated finite source data. -/
theorem fromParts_eq_phaseGauge (M R I : Matrix (Fin 15) (Fin 15) ℚ)
    (hr : ∀ i j, R i j =
      (phaseReal i * phaseReal j + phaseImag i * phaseImag j) * M i j)
    (hi : ∀ i j, I i j =
      (phaseImag i * phaseReal j - phaseReal i * phaseImag j) * M i j) :
    fromParts R I = phaseGauge M := by
  ext i j
  apply Complex.ext <;>
    simp [fromParts, phaseGauge, phases, hr, hi, Complex.mul_re, Complex.mul_im] <;> ring


/-- Literal real part of primitive coefficient 521. -/
def primitive521Real : Matrix (Fin 15) (Fin 15) ℚ :=
  !![16542, 9576, 0, 0, 0, 0, (-192), 1056, 0, 0, 1056, (-2496), 0, 0, 0;
    9576, 11358, 0, 0, 0, 0, 1536, 1272, 0, 0, 1272, (-444), 0, 0, 0;
    0, 0, 16038, 0, 0, 0, 0, 0, 864, 0, 0, 0, (-4104), 0, (-864);
    0, 0, 0, 16038, 0, 0, 0, 0, (-5400), 0, 0, 0, 864, 0, (-432);
    0, 0, 0, 0, 21870, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 16038, 0, 0, (-864), 0, 0, 0, (-1728), 0, 864;
    (-192), 1536, 0, 0, 0, 0, 7520, 1300, 0, 0, 1300, (-2032), 0, 0, 0;
    1056, 1272, 0, 0, 0, 0, 1300, 19850, 0, 0, (-2020), (-434), 0, 0, 0;
    0, 0, 864, (-5400), 0, (-864), 0, 0, 14882, (-432), 0, 0, (-2312), 0, 1156;
    0, 0, 0, 0, 0, 0, 0, 0, (-432), 16038, 0, 0, (-864), 0, (-5400);
    1056, 1272, 0, 0, 0, 0, 1300, (-2020), 0, 0, 19850, (-434), 0, 0, 0;
    (-2496), (-444), 0, 0, 0, 0, (-2032), (-434), 0, 0, (-434), 8171, 0, 0, 0;
    0, 0, (-4104), 864, 0, (-1728), 0, 0, (-2312), (-864), 0, 0, 11414, 0, 2312;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21870, 0;
    0, 0, (-864), (-432), 0, 864, 0, 0, 1156, (-5400), 0, 0, 2312, 0, 14882]

/-- Literal imag part of primitive coefficient 521. -/
def primitive521Imag : Matrix (Fin 15) (Fin 15) ℚ :=
  !![0, 0, (-2592), (-1296), 0, 2592, 0, 0, (-240), 1296, 0, 0, (-480), 0, 240;
    0, 0, (-2592), (-1296), 0, 2592, 0, 0, (-24), 1296, 0, 0, (-48), 0, 24;
    2592, 2592, 0, 0, 0, 0, 864, (-864), 0, 0, (-864), (-432), 0, 0, 0;
    1296, 1296, 0, 0, 0, 0, 432, (-432), 0, 0, (-432), (-216), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-2592), (-2592), 0, 0, 0, 0, (-864), 864, 0, 0, 864, 432, 0, 0, 0;
    0, 0, (-864), (-432), 0, 864, 0, 0, 868, 432, 0, 0, 1736, 0, (-868);
    0, 0, 864, 432, 0, (-864), 0, 0, (-1588), (-432), 0, 0, (-3176), 0, 1588;
    240, 24, 0, 0, 0, 0, (-868), 1588, 0, 0, 1588, 218, 0, 0, 0;
    (-1296), (-1296), 0, 0, 0, 0, (-432), 432, 0, 0, 432, 216, 0, 0, 0;
    0, 0, 864, 432, 0, (-864), 0, 0, (-1588), (-432), 0, 0, (-3176), 0, 1588;
    0, 0, 432, 216, 0, (-432), 0, 0, (-218), (-216), 0, 0, (-436), 0, 218;
    480, 48, 0, 0, 0, 0, (-1736), 3176, 0, 0, 3176, 436, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    (-240), (-24), 0, 0, 0, 0, 868, (-1588), 0, 0, (-1588), (-218), 0, 0, 0]

noncomputable def primitive521 : Matrix (Fin 15) (Fin 15) ℂ :=
  fromParts primitive521Real primitive521Imag

/-- Primitive521 parts for the stated finite source data. -/
theorem primitive521_parts :
    (∀ i j, primitive521Real i j =
      (phaseReal i * phaseReal j + phaseImag i * phaseImag j) * rational521 i j) ∧
    (∀ i j, primitive521Imag i j =
      (phaseImag i * phaseReal j - phaseReal i * phaseImag j) * rational521 i j) := by
  decide +kernel

/-- Primitive521 eq phase Gauge for the stated finite source data. -/
theorem primitive521_eq_phaseGauge : primitive521 = phaseGauge rational521 :=
  fromParts_eq_phaseGauge rational521 primitive521Real primitive521Imag
    primitive521_parts.1 primitive521_parts.2

/-- Primitive521 pos Semidef for the stated finite source data. -/
theorem primitive521_posSemidef : primitive521.PosSemidef := by
  rw [primitive521_eq_phaseGauge]
  exact phaseGauge_posSemidef rational521 rational521_posSemidef

/-- Primitive521 quadratic nonneg for the stated finite source data. -/
theorem primitive521_quadratic_nonneg (z : Fin 15 → ℂ) :
    0 ≤ star z ⬝ᵥ (primitive521 *ᵥ z) :=
  primitive521_posSemidef.dotProduct_mulVec_nonneg z

/-- Literal real part of primitive coefficient 878. -/
def primitive878Real : Matrix (Fin 15) (Fin 15) ℚ :=
  !![15786, (-4788), 0, 0, 0, 0, 96, (-528), 0, 0, (-528), 1248, 0, 0, 0;
    (-4788), 18378, 0, 0, 0, 0, (-768), (-636), 0, 0, (-636), 222, 0, 0, 0;
    0, 0, 16038, 0, 0, 0, 0, 0, (-432), 0, 0, 0, 2052, 0, 432;
    0, 0, 0, 16038, 0, 0, 0, 0, 2700, 0, 0, 0, (-432), 0, 216;
    0, 0, 0, 0, 13122, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 16038, 0, 0, 432, 0, 0, 0, 864, 0, (-432);
    96, (-768), 0, 0, 0, 0, 10496, 1132, 0, 0, 1132, (-6112), 0, 0, 0;
    (-528), (-636), 0, 0, 0, 0, 1132, 12350, 0, 0, (-772), (-674), 0, 0, 0;
    0, 0, (-432), 2700, 0, 432, 0, 0, 14834, 216, 0, 0, (-2408), 0, 1204;
    0, 0, 0, 0, 0, 0, 0, 0, 216, 16038, 0, 0, 432, 0, 2700;
    (-528), (-636), 0, 0, 0, 0, 1132, (-772), 0, 0, 12350, (-674), 0, 0, 0;
    1248, 222, 0, 0, 0, 0, (-6112), (-674), 0, 0, (-674), 11507, 0, 0, 0;
    0, 0, 2052, (-432), 0, 864, 0, 0, (-2408), 432, 0, 0, 11222, 0, 2408;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13122, 0;
    0, 0, 432, 216, 0, (-432), 0, 0, 1204, 2700, 0, 0, 2408, 0, 14834]

/-- Literal imag part of primitive coefficient 878. -/
def primitive878Imag : Matrix (Fin 15) (Fin 15) ℚ :=
  !![0, 0, 1296, 648, 0, (-1296), 0, 0, 120, (-648), 0, 0, 240, 0, (-120);
    0, 0, 1296, 648, 0, (-1296), 0, 0, 12, (-648), 0, 0, 24, 0, (-12);
    (-1296), (-1296), 0, 0, 0, 0, (-432), 432, 0, 0, 432, 216, 0, 0, 0;
    (-648), (-648), 0, 0, 0, 0, (-216), 216, 0, 0, 216, 108, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1296, 1296, 0, 0, 0, 0, 432, (-432), 0, 0, (-432), (-216), 0, 0, 0;
    0, 0, 432, 216, 0, (-432), 0, 0, 1348, (-216), 0, 0, 2696, 0, (-1348);
    0, 0, (-432), (-216), 0, 432, 0, 0, (-988), 216, 0, 0, (-1976), 0, 988;
    (-120), (-12), 0, 0, 0, 0, (-1348), 988, 0, 0, 988, 782, 0, 0, 0;
    648, 648, 0, 0, 0, 0, 216, (-216), 0, 0, (-216), (-108), 0, 0, 0;
    0, 0, (-432), (-216), 0, 432, 0, 0, (-988), 216, 0, 0, (-1976), 0, 988;
    0, 0, (-216), (-108), 0, 216, 0, 0, (-782), 108, 0, 0, (-1564), 0, 782;
    (-240), (-24), 0, 0, 0, 0, (-2696), 1976, 0, 0, 1976, 1564, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    120, 12, 0, 0, 0, 0, 1348, (-988), 0, 0, (-988), (-782), 0, 0, 0]

noncomputable def primitive878 : Matrix (Fin 15) (Fin 15) ℂ :=
  fromParts primitive878Real primitive878Imag

/-- Primitive878 parts for the stated finite source data. -/
theorem primitive878_parts :
    (∀ i j, primitive878Real i j =
      (phaseReal i * phaseReal j + phaseImag i * phaseImag j) * rational878 i j) ∧
    (∀ i j, primitive878Imag i j =
      (phaseImag i * phaseReal j - phaseReal i * phaseImag j) * rational878 i j) := by
  decide +kernel

/-- Primitive878 eq phase Gauge for the stated finite source data. -/
theorem primitive878_eq_phaseGauge : primitive878 = phaseGauge rational878 :=
  fromParts_eq_phaseGauge rational878 primitive878Real primitive878Imag
    primitive878_parts.1 primitive878_parts.2

/-- Primitive878 pos Semidef for the stated finite source data. -/
theorem primitive878_posSemidef : primitive878.PosSemidef := by
  rw [primitive878_eq_phaseGauge]
  exact phaseGauge_posSemidef rational878 rational878_posSemidef

/-- Primitive878 quadratic nonneg for the stated finite source data. -/
theorem primitive878_quadratic_nonneg (z : Fin 15 → ℂ) :
    0 ≤ star z ⬝ᵥ (primitive878 *ᵥ z) :=
  primitive878_posSemidef.dotProduct_mulVec_nonneg z
/-- From Parts gram for the stated finite source data. -/
theorem fromParts_gram {m n : ℕ} (R I : Matrix (Fin m) (Fin n) ℚ) :
    (fromParts R I).conjTranspose * fromParts R I =
      fromParts (R.transpose * R + I.transpose * I)
        (R.transpose * I - I.transpose * R) := by
  ext i j : 2
  apply Complex.ext <;>
    simp [fromParts, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib, sub_eq_add_neg]


/-- The checker also rejects an altered matrix entry. -/
theorem rejects_changed_entry :
    checkLDL (fun i j => if i = 0 ∧ j = 0 then rational521 i j + 1
      else rational521 i j) lower521 diagonal521 = false := by
  decide +kernel

/-- A negative first diagonal weight is not accepted. -/
theorem rejects_negative_weight :
    checkLDL rational521 lower521
      (fun i => if i = 0 then -diagonal521 i else diagonal521 i) = false := by
  decide +kernel

/-- Deleting a factor column changes the whole-matrix identity. -/
theorem rejects_deleted_column :
    checkLDL rational878 (fun i j => if j = 0 then 0 else lower878 i j)
      diagonal878 = false := by
  decide +kernel

/-- From Parts sub for the stated finite source data. -/
theorem fromParts_sub {m n : ℕ} (R I S T : Matrix (Fin m) (Fin n) ℚ) :
    fromParts (R - S) (I - T) = fromParts R I - fromParts S T := by
  ext i j
  simp [fromParts]
  ring

/-- From Parts rat smul for the stated finite source data. -/
theorem fromParts_rat_smul {m n : ℕ} (c : ℚ) (R I : Matrix (Fin m) (Fin n) ℚ) :
    fromParts (c • R) (c • I) = (c : ℝ) • fromParts R I := by
  ext i j
  simp [fromParts, Complex.real_smul]
  ring


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelGramCertificate
