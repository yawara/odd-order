---
id: 40
slug: peterfalvi-2-6-dade-map-construction
title: "Peterfalvi (2.6.b)/(2.8)-(2.10) Dade 写像の構成 (inclusion-exclusion)"
created: 2026-05-27
---

# Peterfalvi (2.6.b)/(2.8)-(2.10) Dade 写像の構成 (inclusion-exclusion)

## 背景

§4 The Dade Isometry のうち、**(2.7) adjoint formula は issue 0039 で完成**
(`OddOrder/Peterfalvi/S04_DadeIsometry.lean`, sorry-free).  残るのは

- **(2.6.b)** Dade 写像 τ が virtual character を virtual character に写すこと
- **(2.8)-(2.10)** その証明に使う構造補題 + inclusion-exclusion 公式

で、これらは合わせて **Dade 写像 τ の明示的構成** に相当する.

現状 S04 は (2.6) を `DadeIsometryData` / `FullDadeIsometryData` の
**インターフェース (仮定束)** として扱い、構成は保留している.  §5-§8 は
このインターフェース + (2.7) adjoint formula を使うので、本 issue は §4 の
完成度を上げるものだが §5-§8 の前提ではない (優先度は中).

## 証明構造 (教科書 `04.4_pp_10_14_The_Dade_Isometry.mmd` L56-124)

- **(2.8)** 非空 `B ⊆ A` に対し `H(B) = ⋂_{a∈B} H(a)`, `N_L(B)` = `B` の L-正規化群,
  `M(B) = H(B)·N_L(B)`.  このとき `M(B) = H(B) ⋊ N_L(B)`
  (H(B) ◁ M(B), H(B) ∩ N_L(B) = 1).  `card_centralizer_eq` 同様の積構造.
- **(2.9)** Notation: `α ∈ CF(L,A)` と非空 `B` に対し `α_B ∈ CF(M(B))` を
  `α_B(hx) = α(x)` (h∈H(B), x∈N_L(B)) で定義.  = `α ∘ f_B`,
  `f_B : M(B) → L` は核 `H(B)` の商準同型.  α が virtual char ⟹ α_B も virtual char.
- **(2.10)** **核心の inclusion-exclusion**: ℬ = 非空部分集合の L-共役類代表系 として
  `α^τ = -∑_{B∈ℬ} (-1)^|B| Ind_{M(B)}^G α_B`.
  右辺は誘導指標の交代和なので virtual character ⟹ (2.6.b).
  - **(2.10.1)** `x∈L`, 非空 `B` に対する Ind 値の式 (g の共役での寄与).
  - **(2.10.2)** `C_{H(B)}(a) = H(B∪{a})` (a∈A).
  - **(2.10.3)** `g ∉ ⋃_a (aH(a))^G` なら `(Ind_{M(B)}^G α_B)(g) = 0`;
    `g ∈ (aH(a))^G` なら値の明示式.
  - 証明: γ := -∑(-1)^|B| Ind α_B とおき、γ(g) を場合分け.  項が 2 つずつ相殺
    (B と B∪{a} のペア, (2.10.2) 経由) し `B={a}` の項だけ残る.
    `𝒜(g, H(a)a) = x·C_G(a)` (= issue 0039 の `card_conj_fiber` の中身) を使い
    `γ(g) = α(a)·|C_G(a)|/(|C_L(a)||H(a)|) = α(a) = α^τ(g)`.
- **(2.6)** (a) (2.7) から従う (β^τ が aH(a) 上定数). (b) (2.10) から.
- **(2.11)** `A₁ ⊆ A` が L-正規化されるとき (2.2) が A₁ で成立し、τ₁ は τ の
  CF(L,A₁) への制限.  (現 S04 の `restrict` インターフェースを実 τ で正当化.)

## 必要インフラ

- 誘導指標: `OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`
  (`induce`, `induceSum`, 加法性, support) は存在.  **誘導指標値公式
  (Frobenius reciprocity / Ind の明示値)** が追加で要りそう ((2.10.1)/(2.10.3)).
- 商準同型 `f_B : M(B) → L` と `α_B = α ∘ f_B` の virtual-char 保存.
- 非空部分集合の L-共役類代表系 ℬ と Möbius 型相殺の組合せ論.
- issue 0039 で作った `card_conj_fiber`, `card_centralizer_eq` を再利用.

## やること

- [ ] (2.8) `M(B) = H(B) ⋊ N_L(B)` の構造補題 (H(B), N_L(B), M(B) を定義)
- [ ] (2.9) `α_B` を商準同型 `f_B` 経由で定義、virtual char 保存
- [ ] 誘導指標値公式 (必要なら InducedCharacter.lean に追加)
- [ ] (2.10.1)-(2.10.3) sub-lemmas
- [ ] (2.10) inclusion-exclusion 本体 (Möbius 相殺)
- [ ] (2.6.b) を (2.10) から、(2.6.a) を (2.7) から; Dade 写像 τ の明示構成と
      `FullDadeIsometryData` への接続
- [ ] (2.11) restriction 互換性

## 完了条件

Dade 写像 τ が `IsDadeMap` + isometry + virtual-char 保存を満たすものとして
**構成** され (インターフェース仮定でなく)、(2.8)-(2.11) が形式化される.
規模が大きいので sub-issue 分割可.

## 参照

- 教科書: `references/peterfalvi/04.4_pp_10_14_The_Dade_Isometry.mmd` (2.6),(2.8)-(2.11)
- (2.7) 完成: issue 0040 の前提 = issues/closed/0039-*, commits 40211fe..0d8307e
- ミニロードマップ: `notes/peterfalvi/s04_dade_isometry.md`
- インフラ: `OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`
