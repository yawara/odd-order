/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import OddOrder.Isaacs.Ch03_SplitExtensions.Problems3F

/-!
# Isaacs §3F の演習 — `SL(2,3)` (書籍 pp. 110-111, Problems 3F.4 / 3F.5)

`S = SL(2,3)` (3 元体上の行列式 1 の 2×2 行列群) についての演習。

* **3F.4** `card_specialLinearTwoThree` (`|S| = 24`) +
  `exists_normal_sylow_two_mulEquiv_quaternion` (正規 Sylow 2-部分群 `≅ Q_8`)。

⚠ **配置の理由**: 行列群の import (`Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`) と
`decide` による具体計算はここだけの話題なので, §3F の一般論 (`Problems3F.lean`) とは
別 leaf にしてある。

⚠ **`decide` の使用について**: `SL(2,3)` は 24 元, `Matrix (Fin 2) (Fin 2) (ZMod 3)` は
81 元で `DecidableEq` + `Fintype` があるため, 位数計算・準同型性 (64 通り)・単射性・
正規性 (24×8 通り) はすべて kernel で決定できる (合計 ~6s)。
**`native_decide` は使わない** (`ofReduceBool` 公理が入り axiom-clean が壊れる)。
-/

namespace OddOrder.Isaacs.Ch03

open Matrix QuaternionGroup

section /- 3F.4: SL(2,3) -/

/-- `SL(2,3)` = `ZMod 3` 上の行列式 1 の 2×2 行列群 (書籍 3F.4/3F.5 の `S`)。 -/
abbrev SpecialLinearTwoThree := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

/-- **Isaacs Problem 3F.4 (前半)** (書籍 p. 110): `|SL(2,3)| = 24`。 -/
theorem card_specialLinearTwoThree : Nat.card SpecialLinearTwoThree = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- `SL(2,3)` の中の四元数 `i = [[0,-1],[1,0]]` (`i² = -I`)。 -/
def slQuaternionI : SpecialLinearTwoThree := ⟨!![0, -1; 1, 0], by decide⟩

/-- `SL(2,3)` の中の四元数 `j = [[1,1],[1,-1]]` (`j² = -I`, `j⁻¹ i j = i⁻¹`)。 -/
def slQuaternionJ : SpecialLinearTwoThree := ⟨!![1, 1; 1, -1], by decide⟩

/-- `Q_8 → SL(2,3)` の台写像: `a k ↦ i ^ k`, `xa k ↦ j * i ^ k`。

`QuaternionGroup 2` の生成元関係 (`a 1` の位数 4, `x² = a 2`, `x⁻¹ a x = a⁻¹`) が
`i`, `j` で成り立つので準同型になる。 -/
def quaternionToSL23Fun : QuaternionGroup 2 → SpecialLinearTwoThree
  | .a i => slQuaternionI ^ i.val
  | .xa i => slQuaternionJ * slQuaternionI ^ i.val

/-- `Q_8 → SL(2,3)` の準同型 (`map_mul` は 64 通りを `decide`)。 -/
def quaternionToSL23 : QuaternionGroup 2 →* SpecialLinearTwoThree :=
  MonoidHom.mk' quaternionToSL23Fun (by decide)

theorem quaternionToSL23_injective : Function.Injective quaternionToSL23 := by decide

/-- `SL(2,3)` の Sylow 2-部分群 = `Q_8` の像 `{±I, ±i, ±j, ±k}`。 -/
def sylowTwoSL23 : Subgroup SpecialLinearTwoThree := quaternionToSL23.range

theorem sylowTwoSL23_conj_mem : ∀ n ∈ quaternionToSL23.range,
    ∀ g : SpecialLinearTwoThree, g * n * g⁻¹ ∈ quaternionToSL23.range := by decide

instance sylowTwoSL23_normal : sylowTwoSL23.Normal := ⟨sylowTwoSL23_conj_mem⟩

/-- `Q_8 ≃ SL(2,3)` の Sylow 2-部分群。 -/
noncomputable def quaternionMulEquivSylowTwoSL23 : QuaternionGroup 2 ≃* ↥sylowTwoSL23 :=
  MonoidHom.ofInjective quaternionToSL23_injective

theorem card_sylowTwoSL23 : Nat.card ↥sylowTwoSL23 = 8 := by
  rw [← Nat.card_congr quaternionMulEquivSylowTwoSL23.toEquiv, Nat.card_eq_fintype_card,
    QuaternionGroup.card]

/-- **Isaacs Problem 3F.4** (書籍 p. 110): `SL(2,3)` は位数 24 で, その Sylow
2-部分群は正規かつ `Q_8` と同型。

具体的には `{±I, ±i, ±j, ±k}` (`i = [[0,-1],[1,0]]`, `j = [[1,1],[1,-1]]`) が
その Sylow 2-部分群。 -/
theorem exists_normal_sylow_two_mulEquiv_quaternion :
    ∃ P : Sylow 2 SpecialLinearTwoThree, (P : Subgroup SpecialLinearTwoThree).Normal ∧
      Nonempty (↥(P : Subgroup SpecialLinearTwoThree) ≃* QuaternionGroup 2) := by
  have h24 : (24 : ℕ).factorization 2 = 3 := by
    have hd : (2 : ℕ) ^ 3 ∣ 24 := by norm_num
    have hnd : ¬ (2 : ℕ) ^ 4 ∣ 24 := by norm_num
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).mp hd
    have hlt : ¬ 4 ≤ (24 : ℕ).factorization 2 := fun h =>
      hnd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).mpr h)
    omega
  have hfac : Nat.card ↥sylowTwoSL23
      = 2 ^ (Nat.card SpecialLinearTwoThree).factorization 2 := by
    rw [card_sylowTwoSL23, card_specialLinearTwoThree, h24]
    norm_num
  refine ⟨Sylow.ofCard sylowTwoSL23 hfac, ?_, ?_⟩
  · rw [Sylow.coe_ofCard]
    exact sylowTwoSL23_normal
  · rw [Sylow.coe_ofCard]
    exact ⟨quaternionMulEquivSylowTwoSL23.symm⟩

end -- 3F.4

end OddOrder.Isaacs.Ch03
