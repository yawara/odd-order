---
id: 1000
slug: classsum-omega-integrality
title: "centralCharacterOfRep の代数的整数性 ω(C_s) ∈ algInt"
created: 2026-05-30
---

# centralCharacterOfRep の代数的整数性 ω(C_s) ∈ algInt

## 背景

`OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean` で class-sum 代数と中心指標
`ω_ρ : Z(ℂ[G]) →ₐ[ℂ] ℂ` (`centralCharacterOfRep`, Isaacs §3 p.35 / Peterfalvi (6.7.2) の
`ClassSumAlgebraHom`) を sorry-free で実装した。残るのは **`ω_ρ(C_s)` が代数的整数** (over ℤ)
であること。Peterfalvi (6.7.3) の `ψ(z) ≡ ψ(1) (mod |P|)` 合同で本質的に使う。

## やること

- [x] 次の定理を sorry-free で証明 (**完了 2026-05-30**, commit は worktree 履歴参照):
  ```lean
  theorem centralCharacterOfRep_classSum_isIntegral
      {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      [DecidableEq (ConjClasses G)]
      (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] (C : ConjClasses G) :
      IsIntegral ℤ (centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩)
  ```
  実際の署名は `classSum` が `∑ g : G` を使う都合で `[Finite G]` ではなく `[Fintype G]` を採る
  (本ファイルの既存 convention と一致).

## 完了メモ (2026-05-30)

`OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean` に実装。3 定理を AxiomsCheck 登録済
(unconditional = propext/Classical.choice/Quot.sound のみ):
- `classSum_mul` (PREREQ 1, 正しい per-element 係数形; read-only plan の `/|C_s|` 形は誤りで不採用),
  補助 `classSum_mul_apply_conj` (係数の class-function 性) / `classSum_mul_apply_out`。
- `centralCharacterOfRep_classSum_mul` (`ω_ρ(C_i)·ω_ρ(C_j) = ∑_s m_s·ω_ρ(C_s)`, ℕ 係数)。
- `centralCharacterOfRep_classSum_isIntegral` (本体)。Route A (module-finite ℤ-subalgebra of ℂ):
  `{ω_ρ(C_s)}∪{1}` 生成の `Submodule.span ℤ` が乗法閉 (product rule) かつ f.g. ⟹ `Submodule.toSubalgebra`
  ⟹ `IsIntegral.of_mem_of_fg`。行列固有値論法 (Route B) は不要だった。

## 後続 (2026-05-30): 指標値形の系

keystone `centralCharacterOfRep_classSum_isIntegral` の上に **指標値の明示形**
`isIntegral_card_mul_character_div` を追加 (同ファイル `CharacterIntegrality` section):

```lean
theorem isIntegral_card_mul_character_div (ρ : Representation ℂ G V) [IsIrreducible ρ]
    (C : ConjClasses G) {g : G} (hg : ConjClasses.mk g = C) :
    IsIntegral ℤ
      ((Nat.card { x : G // ConjClasses.mk x = C } : ℂ) * ρ.character g / ρ.character 1)
```

すなわち **`|C| · χ_ρ(g) / χ_ρ(1)` が代数的整数** (Isaacs (3.7))。証明は
`centralCharacterOfRep_classSum` + `sum_character_eq_card_mul` + `ρ.char_one` で `ω_ρ(C)` に書き換え、
keystone を適用するだけ。`[Finite G]` で取り `Fintype.ofFinite` を内部で使い型に余分な instance を残さない。
AxiomsCheck 登録済 (unconditional)。(6.7.3) や古典的 `χ(1) ∣ |G|` がこの形を直接消費する。

## 後続 (2026-05-30 第 2 波): 指標整数性チェーン + χ(1) ∣ |G|

同ファイルに古典的指標整数性の 3 連結ピースを追加 (新 section `CharacterValuesIntegral` /
`CharacterDegreeDvd` / `CharacterDegreeDvdMain`)。すべて AxiomsCheck 登録済 (unconditional):

- `character_isIntegral (ρ) [Finite G] (g) : IsIntegral ℤ (ρ.character g)` — 指標値は代数的整数。
  `ρ g` は有限位数 (`g^|G|=1 ⟹ (ρ g)^|G|=1`)、ℂ 上 charpoly は分解、trace = 根の和、各根 μ は
  固有値で `μ^|G|=1` ⟹ `X^|G|-1` の根 ⟹ 整。補助 `isIntegral_of_pow_eq_one`,
  `pow_eq_one_of_isRoot_charpoly_of_pow_eq_one` (mathlib
  `Module.End.trace_eq_sum_roots_charpoly_of_splits` + `hasEigenvalue_iff_isRoot_charpoly`
  + `HasEigenvector.pow_apply`)。
- `isIntegral_rat_imp_int {q : ℚ} (IsIntegral ℤ (q:ℂ)) : ∃ n : ℤ, (q:ℂ) = n` — 有理代数的整数は整数。
  ℤ integrally closed (UFD ⟹ `IsIntegrallyClosed ℤ`、import `RingTheory.Polynomial.RationalRoot`)、
  `isIntegral_algebraMap_iff` で `ℚ ↪ ℂ` を降りて `IsIntegrallyClosed.isIntegral_iff` (分数体 ℚ)。
- `finrank_dvd_card (ρ) [Finite G] [IsIrreducible ρ] : finrank ℂ V ∣ Nat.card G` — **Isaacs Thm 3.11**。
  第一直交関係 (`Representation.char_orthonormal`, `ρ≅ρ` で `∑_g χ(g)χ(g⁻¹)=|G|`) を共役類で再編成し
  `|G|/χ(1) = ∑_C ω_ρ(C)·χ((g_C)⁻¹)` (補助 `sum_centralCharacter_mul_character_inv_mul_character_one`,
  `sum_eq_sum_conjClasses_of_isClassFun`) — 代数的整数の積和 ⟹ 有理代数的整数 ⟹ 整数 (上記)。
  古典 `χ(1) ∣ |G|` を mathlib に無い形で供給 (round-2 #1 unlock)。

## 後続 (2026-05-30 第 3 波): characterDegree ↔ finrank 橋渡し (S03 層への接続)

第 2 波の `finrank_dvd_card` は `Representation.character`/`finrank` レベルに留まり、S03 の
`characterDegree`/`ClassFunction` 層へ流れていなかった (Peterfalvi の degree 文が消費できない)。
`OddOrder/GroupTheory/RepresentationTheory/ZIrr.lean` に橋を 2 本追加 (AxiomsCheck 登録済,
unconditional = propext/Classical.choice/Quot.sound のみ):

- `IsIrreducibleCharacter.exists_finrank_charValue_one {φ} (hφ) :`
  `∃ V .., Nonempty V ∧ φ 1 = (finrank ℂ V : ℂ)` — 既約指標 `φ` の `φ 1` は任意 witness 表現の次元。
  `IsIrreducibleCharacter` の存在 witness を unpack → 仮説 `Representation.IsIrreducible ρ`
  (= `IsSimpleOrder (Subrepresentation ρ)`, class) を `haveI` で instance 化 → `ρ.char_one`。`[Finite G]` 不要。
- `IsIrreducibleCharacter.exists_natDegree_charValue_one_dvd_card [Finite G] {φ} (hφ) :`
  `∃ n:ℕ, 0<n ∧ φ 1 = (n:ℂ) ∧ n ∣ Nat.card G` — Isaacs Thm 3.11 の `ClassFunction` 層版。
  `finrank_dvd_card ρ` を直接適用。

消費経路: `characterDegree φ = φ 1` は `characterDegree_def` (`rfl`/`@[simp]`, S03) なので、S03 側で
`rw [characterDegree_def]` 後に上記を当てれば `characterDegree φ ∣ |G|` が ℕ 上で出る。`ZIrr` は
`ClassSumAlgebra` を新規 import (sibling, `ClassFunction` 経由で acyclic)。`characterDegree` 自身は
S03 = downstream のため `ZIrr` からは参照せず `φ 1` 形で橋渡しした (上方 import によるサイクル回避)。

## 完了条件

上記 `IsIntegral ℤ (ω_ρ(C_s))` が sorry/admit/axiom 無しで証明され `lake build OddOrder` が通る。

## 参照

- 既存実装: `OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean`
  (`centralCharacterOfRep`, `classSum_mul_apply`, `classSumCoeff`)
- Peterfalvi (6.7.2)/(6.7.3); Isaacs *Character Theory* §3 (p.35), (3.7) 系
- `notes/peterfalvi/s08_coherence_theorems.md` (`AlgInt.cong` も併せて要)

## 証明方針 (structure-constant 行列論法)

標準的な「構造定数の整数行列の固有値」論法:

1. 固定した `C_i` に対し、左乗 `x ↦ C_i · x` は class-sum の ℤ-span を保つ。
   その表現行列 `M_i = (κ)_{j,s}` は **整数係数** (κ は `classSum_mul_apply` の
   per-element 係数 = 因子分解の個数; 整数)。注意: class-sum 基底に関する係数は
   `classSumCoeff Ci Cj Cs / |C_s|` ではなく `classSum_mul_apply` が与える per-element 個数
   (これは同一類上で定数)。`classSum_mul` (class-sum の線型結合形) を正しい係数
   `κ_s := (classSum Ci * classSum Cj) w` (w ∈ C_s 代表) で先に確立する必要がある。
2. `ω_ρ` は環準同型なので `ω_ρ(C_j) · ω_ρ(C_i) = ∑_s κ_s ω_ρ(C_s)`、つまり
   ベクトル `(ω_ρ(C_s))_s` は固有値 `ω_ρ(C_i)` の `M_i` の固有ベクトル。
3. 整数行列 `M_i` の固有値は monic ℤ-係数特性多項式の根 ⟹ `IsIntegral ℤ`。

mathlib 補助: `IsIntegral`, `Matrix.charpoly`/`Matrix.isIntegral_of_...`、固有値の整数性。
代替 (より直接): `RingHom` の像が整閉包に入ることを `Subring.closure` 帰納で示す
(`classSum` 全体が生成する ℤ-部分環が ℤ 上有限生成 = 整) — こちらの方が行列論法を回避できる
可能性あり (要検討)。

## 注意 (read-only plan の誤り)

事前調査 plan の `classSum_mul : C_i C_j = ∑_s (classSumCoeff Ci Cj s : ℂ) • classSum s` は
**`|C_s|` 倍ずれており数学的に誤り** (class-sum `C_s` の係数は `a_{ijs}/|C_s|`)。本実装では
誤った形を証明せず、正しい per-element 係数 `classSum_mul_apply` を採用した。整理した
`classSum_mul` (正しい係数版) が本 issue の前提として必要。
