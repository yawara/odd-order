---
id: 9504
slug: quadratic-frobenius-subfield
title: "𝔽_{q²}/𝔽_q: q 乗 Frobenius・位数 q の部分体・自己同型の延長"
created: 2026-07-30
---

# `𝔽_{q²} / 𝔽_q` の周辺体論 (shared infra)

## 背景 — なぜ必要か

[0167](0167-pf-part2-ch3-s3-model.md) の Peterfalvi Part II Ch. III §3 (p. 120) は
`E = 𝔽_{q²}` に **bar 作用 `x ↦ x̄ = x^q`** を置き、`F = 𝔽_q` をその固定体として扱う。
Proposition の各条件 (`W₁ ≤ {x : x^{1+q} = 1}`, `σ|_F = θ`, `x^σ = x^{-1}` on `W₁`,
`φ(x,y) = λ₁ x y^σ + λ₁‾ x̄ ȳ^σ`) はすべてこの言葉で書かれているので、段 (2) 以降に
入る前に `E` / `F` / bar の関係を repo の言葉で確立しておく必要がある。

段 (1) (0167, 2026-07-30 landing) が吐く体 `E` は `End_{𝔽₂[KW]}(S/Q₀)` という
**抽象体** (位数 `q²`、標数 2) なので、`GaloisField 2 (2n)` 固有の補題ではなく
「位数 `q²` の任意の有限体」に対する形が要る。

## やったこと (2026-07-30)

`OddOrder/Algebra/QuadraticFrobenius.lean` (新 leaf) に landing:

| 宣言 | 内容 |
|---|---|
| `qFrobenius E p n` | `x ↦ x^{pⁿ}` を `RingAut E` として (有限体は perfect ゆえ全単射) |
| `qFrobenius_sq` | `\|E\| = q²` なら `σ₀² = 1` (`x^{q²} = x`) |
| `qFrobenius_ne_one` | `σ₀ ≠ 1`。`σ₀ = 1` だと全単元が `x^{q-1} = 1` を満たし、巡回群 `E^×` の指数 `q²−1` が `q−1` を割ることになる |
| `orderOf_qFrobenius` | `orderOf σ₀ = 2` |
| `fixedSet_qFrobenius` | `Fix(⟨σ₀⟩) = {x : x^q = x}` |
| `frobFixedSubfield E p n` | その `Subfield E` 版 (= `F`) |
| `mem_frobFixedSubfield` | `x ∈ F ↔ x^q = x` |
| `natCard_fixedSet_qFrobenius` / `natCard_frobFixedSubfield` | `\|F\| = q`。Artin の補題 (`OddOrder.RingAut.finrank_fixedSet`) を `⟨σ₀⟩` (位数 2) に当てて `[E : F] = 2` ⟹ `\|F\|² = q²` |
| `qFrobenius_eq_inv_of_pow_succ_eq_one` / `qFrobenius_mul_self_eq_one` | `x^{q+1} = 1 ⟹ x^q = x⁻¹`。書籍の `x^{1+σ} = 1` (`x ∈ W₁`) |

既存部品の再利用: `OddOrder/Algebra/FixedPointsGalois.lean` の Artin 補題
(`finrank_fixedSet`, `fixedSet_eq_subfield`) がそのまま効いた。**新規に Galois 理論を
作る必要は無かった**。

⟹ **`θ = 1` 分岐の段 (2) はこれで揃った**: `σ := qFrobenius` は `F` 上恒等 (= `θ`) で
`W₁` を反転する。

## やること (残り)

- [ ] **自己同型の延長** (段 (2) の `θ ≠ 1` 分岐の前提): 任意の `θ ∈ Aut(F)` は `E` の
  自己同型に延長でき、延長はちょうど 2 個 (`σ` と `σ σ₀`)。書籍は暗黙に使っている。
  経路 = `E/𝔽_p` は Galois (有限体の有限拡大) なので中間体への制限
  `Gal(E/𝔽_p) → Gal(F/𝔽_p)` は全射 (`AlgEquiv.restrictNormalHom_surjective`)、
  `RingAut ≃* AlgEquiv over ZMod p` は `SemilinearFieldAut.lean` の
  `Huppert.ringAutMulEquivAlgAut` で橋渡し。核が `⟨σ₀⟩` (位数 2) なのは
  `RingAut.fixer_fixedSet` から。
  ⚠ instance plumbing: `[Algebra (ZMod p) E]` は global instance ではない
  (`ZMod.algebra` を `letI` で入れる; `SemilinearFieldAut.lean` は仮説として持っている)。
- [ ] 延長が入れば `{σ, σ σ₀}` の 2 択から `ω^{1+σ} = 1` を満たす方を選ぶ、という
  書籍の「必要なら `σ` を `σ̄` に取り替える」が形式化できる。

## 完了条件

`E` を位数 `q²` の有限体とするとき、bar 作用・固定部分体 `F` (位数 `q`)・
`Aut(E) → Aut(F)` の全射性と核 `⟨σ₀⟩` がすべて sorry-free で揃う。

## 参照

* 消費者 = [0167](0167-pf-part2-ch3-s3-model.md) 段 (2)–(3)
* 原文 = `references/peterfalvi/pages/peterfalvi-p{120,121}.png` (書き起こしは 0167 に転記済)
* 既存部品 = `OddOrder/Algebra/FixedPointsGalois.lean`,
  `OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldAut.lean`
