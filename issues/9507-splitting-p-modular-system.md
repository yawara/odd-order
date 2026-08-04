---
id: 9507
slug: splitting-p-modular-system
title: "分裂 p-modular system の構成 (段 94 以降の gate)"
created: 2026-08-04
---

# 分裂 `p`-modular system の構成

**claim**: hub / main session (9500 band) / **状態**: 調査済・未着手 (2026-08-04)

## なぜ要るか

[issue 9506](9506-modular-p-modular-system.md) の段 94 (Cartan 行列 `C = DᵀD`) 以降は
**`Irr(G)` を添字集合として持つ**必要がある。`D` の行添字が `Irr(G)` だからで、さらに
Navarro (6.13) の `Irr(B₀) = Irr(G/O_{p'}(G))` と BS 本証明の
`Irr(B₀) = {1_G = χ₀, …, χ_r}` の枚挙も同じものを要求する。

`Irr(G)` を `k`-側と同じ設計 (Wedderburn 分解の添字) で持つには、
**`K = Frac(𝒪)` が `K[G]` を分裂させる**必要がある。

## ⚠ 現行の `StandardSystem` では足りない (2026-08-04 実測)

`StandardSystem p = 𝕎(𝔽̄_p)` の商体 `K = Frac(𝕎(𝔽̄_p))` は **`ℚ_p` の最大不分岐拡大の完備化**。

* `p'`-乗根はすべて含む (だから Brauer 指標側は足りている)。
* **`ζ_p` を含まない** — `ℚ_p(ζ_p)/ℚ_p` は次数 `p−1` の**完全分岐**拡大。`p = 2` なら `i ∉ K`。
* `exp G` の `p`-部分に対応する乗根が指標値に出るので、**一般に分裂体でない**。

`StandardSystem.lean` の docstring が主張しているのは**剰余体側**の 2 条件だけ
(`k` が群環を分裂させる = 代数閉、`k` が `|G|_{p'}` 乗根を持つ) で、`K` の分裂には触れていない。
段 93 までは剰余体側しか使っていなかったので表面化しなかった。

## 数学的には何が要るか

* **Schur 指数は障害にならない**: `K` は完備離散付値体で剰余体が代数閉 ⟹ Lang の定理により
  **quasi-algebraically closed (C₁)** ⟹ Brauer 群が自明 ⟹ Schur 指数はすべて 1。
  したがって**指標値を含めれば分裂する**。
* ⟹ 必要なのは **`ζ_{exp G}` を添加するだけ**。標準構成は
  **`𝒪' = 𝕎(𝔽̄_p)[ζ_{p^a}]`** (`p^a = |G|_p`)。完備 DVR の**完全分岐**有限拡大で、
  剰余体は `𝔽̄_p` のまま ⟹ 同じ `p`-modular system の枠に収まる。

## ⚠⚠ Lean 側の障害 (2026-08-04 実測、これが本 issue の実質)

mathlib に**必要な拡大論が無い**:

* `Mathlib/RingTheory/DiscreteValuationRing/` は `Basic.lean` と `TFAE.lean` のみ。
  **DVR の有限拡大が DVR である**という定理は無い (grep 0 件)。
* `HenselianLocalRing` の instance は **(i) 体、(ii) `IsAdicComplete` から**の 2 つだけ。
  **「Henselian の有限拡大は Henselian」は無い**。
* **C₁ 体 / Lang の定理 / Brauer 群の自明性**も無い (grep 0 件)。

⟹ `𝕎(𝔽̄_p)[ζ_{p^a}]` を作って「完備 DVR で剰余体 `𝔽̄_p`」を示すには、
**mathlib レベルの拡大論を自前で建てる**ことになる。

## 選択肢 (未決定)

1. **完備 DVR の有限拡大論を建てる** — `𝕎(𝔽̄_p)[ζ_{p^a}]` が Henselian 局所 Noetherian
   であることまで。正攻法だが mathlib 規模。
   ⚠ `IsPModularSystem` は DVR を要求していない (Henselian 局所 + charZero + 剰余体 char p)。
   DVR が要るのは `BrauerLinearIndependence` の Nakayama で、そこは
   **Noetherian + `jacobson_eq_maximalIdeal`** があれば足りるはず — 要求を弱められる可能性あり
   (未検証、着手時に確認する)。
2. **古典的な設定に寄せる** — `R = ℤ[ζ_{|G|}]` の `p` 上の極大イデアルでの局所化 `R_M`。
   DVR (Dedekind の局所化) で `K = ℚ(ζ_{|G|})` は分裂体。
   ⚠ ただし **Henselian でない**ので `RootsOfUnityLift.lean` の
   `rootsOfUnityEquivResidue` (Hensel を使う) が効かない。`p'`-乗根の還元が単射・全射で
   あることを別途示す必要がある (可能なはずだが別ルート)。
3. **大域的な分裂を要求しない設計を続ける** — 段 93 では絶対既約性を**加群ごと**の仮説に
   することで回避した。段 94 で同じ手が使えるかは未検討 (`C = DᵀD` は `Irr(G)` 全体を
   要求するので、そのままでは苦しい)。

## 着手前にやること

- [ ] 選択肢 1 の「DVR でなく Noetherian で足りる」を実測で確認
      (`BrauerLinearIndependence` と `DecompositionNumber` の
      `IsDiscreteValuationRing` 使用箇所を trace)
- [ ] 選択肢 2 の Hensel 迂回が本当に書けるか、`RootsOfUnityLift.lean` の依存を見て判断
- [ ] そのうえで route を確定して着手

## 完了条件

`K = Frac(𝒪)` が `K[G]` を分裂させる `p`-modular system の **instance が具体構成で存在**し
(CLAUDE.md「carrier の構成可能性」)、段 94 の `Irr(G)` 添字化が乗る。

## 参照

- 親: [9506](9506-modular-p-modular-system.md) (段 94 の gate)
- 祖父: [0147](0147-q8-modular-char-theory-frozen.md) (Q₈ Brauer–Suzuki)
- 現行 system: `OddOrder/GroupTheory/RepresentationTheory/Modular/StandardSystem.lean`
