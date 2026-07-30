---
id: 9215
slug: dihedral-automorphism-group
title: "shared infra claim: OddOrder/GroupTheory/DihedralAut.lean (Aut(D_{2n}) の構造と n 奇数での completeness)"
created: 2026-07-29
---

# shared infra claim: OddOrder/GroupTheory/DihedralAut.lean

## 背景

Isaacs Problem 9B.4 (書籍 p. 285: `G` = 位数 `2n` の二面体群, `n` 奇数のとき
automorphism tower は高々 2 種類の群しか含まない) の本体が
**`Aut(D_{2n})` が complete** であること。

repo にも mathlib にも `Aut(DihedralGroup n)` の記述は無い (検索済:
`grep -rn "MulAut (DihedralGroup" .lake/packages/mathlib/` は 0 hit、
repo 側の DihedralGroup 利用 15 file はいずれも Aut を扱わない)。

## claim (lane a, 2026-07-29)

**新設ファイル**: `OddOrder/GroupTheory/DihedralAut.lean` (汎用群論なので
`OddOrder/GroupTheory/` 配下; consumer は当面
`Isaacs/Ch09_MoreSubnormality/Problems9B.lean` のみ)。

## 中身 (設計)

`n` 奇数のとき `Aut(D_{2n}) ≅ Hol(ℤ/n) = ℤ/n ⋊ (ℤ/n)ˣ`。**抽象的な半直積を経由せず**
座標を直接扱う:

* `dihedralAut (a : ZMod n) (u : (ZMod n)ˣ) : MulAut (DihedralGroup n)` —
  `r i ↦ r (u i)`, `sr i ↦ sr (u i + a)`。
* 合成則 `dihedralAut a u * dihedralAut b v = dihedralAut (a + u b) (u v)`
  (= holomorph の積)。
* 座標抽出 `transCoord` / `rotCoord` (`ψ (sr 0)` / `ψ (r 1)` を読むだけ、choice 不要)
  で単射性。
* **全射性** (`n` 奇数): 回転部分群 `= {x | x ^ n = 1}` が characteristic
  (`dihedral_pow_eq_one_iff_exists_r`, Problems9B.lean に landing 済) →
  `Aut(ℤ/n) = (ℤ/n)ˣ` (`ZMod.AddAutEquivUnits` の `f x = f 1 * x` の筋を再利用)。

**completeness の鍵** ⭐: `n` 奇数のとき
**`[Aut(D_{2n}), Aut(D_{2n})] = N`** (`N = {dihedralAut a 1}` = 平行移動部分群)。
`(ℤ/n)ˣ` が可換なので `≤`、`⁅dihedralAut 0 (-1), dihedralAut b 1⁆ = dihedralAut (-2b) 1`
と `2` の可逆性で `≥`。⟹ `N` は commutator なので **characteristic が無料** で出る
(mathlib `commutator_characteristic`)。

⚠ これは 2026-07-29 の issue 1055 メモの見立て
(「`Inn(D_{2n})` は characteristic でないので 9B.2 は使えない」) の**代替経路**。
9B.2 を使わず、`N` の characteristic 性から直接組み立てる。

completeness の残り:
1. `Z(Aut(D_{2n})) = 1` (`u b = b ∀b ⟹ u = 1`; `a = v a ∀v` に `v = -1` と `2` 可逆)。
2. `Φ ∈ Aut(Aut(D_{2n}))` は `N` を保つ → `Φ|_N` は `ℤ/n` の加法自己同型 = 単元 `w` 倍
   → `conj (dihedralAut 0 w)` で割って `Ψ` は `N` を各点固定。
3. `Ψ (dihedralAut 0 u) = dihedralAut (a_u) u` (共役関係から unit 成分が決まる) で
   `a_{uv} = a_u + u a_v` (1-cocycle)。
4. `u = -1` と可換性から `2 a_u = (1 - u) a_{-1}` ⟹ `a_u = (1 - u) c`, `c = a_{-1}/2`
   ⟹ `Ψ = conj (dihedralAut c 1)` ⟹ `Φ` は内部。

## 完了条件

- [x] `dihedralAut` とその API (合成則・単射・全射) が landing
- [x] `commutator_eq_transSubgroup` (`n` 奇数)
- [x] `IsCompleteGroup (MulAut (DihedralGroup n))` (`n` 奇数)
- [x] Problems9B.lean 側で 9B.4 の statement が閉じる
- [x] `OddOrder.lean` に import 配線

## 完了記録 (2026-07-29)

全項目 landing。`#print axioms` は 4 本とも `[propext, Classical.choice, Quot.sound]`
(`exists_dihedralAut` / `commutator_eq_transSubgroup` / `center_mulAut_dihedral_eq_bot` /
`mulAut_conj_surjective`)。`DihedralAut.lean` = 516 行, lint --strict clean。

設計どおりに回ったが、実装で分かった追加の注意点:

* **`n ≠ 1` は不要**だった。`n = 1` では `D₂ ≅ ℤ/2` で `Aut` が自明群になり
  `center = ⊥` / `innAut = ⊤` が両方自明に成立する。書籍が `n ≠ 1` を要するのは
  "Observe that `Z(G) = 1`" の側だけ (mathlib
  `DihedralGroup.center_eq_bot_of_odd_ne_one`)。
* `2` の可逆性は `ZMod.unitOfCoprime` を経由せず **`n = 2k+1` から `2(k+1) = n+1 ≡ 1`**
  で初等的に取れる (`exists_two_mul_eq_one`)。⚠ `rw [hk]` で `n` 自体を書き換えると
  `ZMod n` の依存で motive が壊れるので、ℕ の等式を `omega` で作りキャスト内だけ
  書き換える。
* 座標抽出 (`rCoord` / `srCoord`) を素の `match` で作れば **choice 不要**で
  `rotAddHom` / `transAddHom` を `def` にできる (`Classical.choice` を実際に使うのは
  `choose A hA using hunit` の 1 箇所だけ)。
* 副産物として `mulEquivMulAutOfIsCompleteGroup` (complete ⟹ `H ≃* Aut(H)`) を
  Problems9B.lean に追加 — 9B.2 / 9B.3 / 9B.4 に共通の
  "contains at most two different groups" の内容を取り出す形。

## 参照

* [issues/1055-isaacs-problems-campaign.md](1055-isaacs-problems-campaign.md) — 9B.4 の実状調査
* `OddOrder/GroupTheory/DihedralAut.lean` — 本体 (`dihedral_pow_eq_one_iff_exists_r` は
  Problems9B.lean から移設)
* `OddOrder/Isaacs/Ch09_MoreSubnormality/Problems9B.lean` —
  `isCompleteGroup_mulAut_dihedralGroup` (9B.4 の statement)
* mathlib `Mathlib/Data/ZMod/Aut.lean` — `ZMod.AddAutEquivUnits`
* 書籍ページ画像 `references/isaacs/pages/isaacs-p285-298.png` — 9B.4 の原文
