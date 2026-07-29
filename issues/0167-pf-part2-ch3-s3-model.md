---
id: 167
slug: pf-part2-ch3-s3-model
title: "Peterfalvi Part II, Ch. III §3 本体: S ⋊ KW の標準モデル S₁ ⋊ K₁W₁ (pp. 119-121)"
created: 2026-07-29
---

# Peterfalvi Part II, Ch. III §3 本体: `S ⋊ KW ≅ S₁ ⋊ K₁W₁`

## 背景

[0165](closed/0165-pf-part2-ch3-s2-order-five.md) で §2 の Proposition、
[0166](closed/0166-pf-part2-ch3-s3-case-ab-conclusion.md) で §3 冒頭
(`SecondCaseHypothesis.theoremAConclusion_or_caseC2`) が landing した。
以後は **(C2)** だけを仮定してよい:

> **(C2)** `S` is a Suzuki 2-group of type B, `st` has order 3 and `W ≠ 1`.

残るのが §3 本体 (pp. 119–121) の Proposition。これは `S ⋊ KW` を
**E = 𝔽_{q²} 上の明示モデルに正規化する**構造定理で、Ch. IV (PSU(3,q) の
特徴付け) が全面的に依存する。

正本ページ = `references/peterfalvi/pages/peterfalvi-p{119,120,121}.png`
(text は数式が壊れているので式はページ画像で確定すること)。

## 書籍の設定 (p. 119 末)

`F = 𝔽_q`, `E = 𝔽_{q²}`。`S = B(n, θ, ε)` (`θ` は `F` の奇位数自己同型)。
Appendix III Definition 3 により `S` は中心拡大

    F → S → F × F,   χ(a,b) = a^{1+θ} + ε a b^θ + b^{1+θ}

で、`ε` は `χ(a,b) = 0 ⟹ a = b = 0` (anisotropic)。さらに `K ≅ F^×` で

    (a,b)^x = (xa, xb),   c^x = x^{1+θ} c   (x ∈ F^×, (a,b) ∈ F×F, c ∈ F)。

## 主張 (p. 120)

`S ⋊ KW ≅ S₁ ⋊ K₁W₁` (`S ↦ S₁`, `K ↦ K₁`, `s ↦ (0,1)`) で

* **`S₁`** = `{(x, y) : x, y ∈ E}` のうち、`θ ≠ 1` なら `y ∈ F`、
  `θ = 1` なら `y + y^q = x^{1+q}` を満たすもの。演算は
  `(x,z)(y,u) = (x+y, z+u+φ(x,y))`。
* **`φ`**: `θ = 1` なら `φ(x,y) = x y^q`。そうでなければ `φ : E × E → F` は双加法的で
  `φ(ax, by) = a b^θ φ(x,y)` (`a,b ∈ F`)、かつ `x ≠ 0 ⟹ φ(x,x) ≠ 0`。
* **`K₁W₁ ≤ E^×`**、`K₁ = F^×`、`W₁` は `{x ∈ E^× : x^{1+q} = 1}` の非自明部分群。
* **`σ`**: `E` の自己同型で `F` 上 `θ` に一致し、`W₁` 上 `x^σ = x⁻¹`。
* 作用: `(x,y)^a = (ax, a^{1+σ} y)` (`a ∈ K₁W₁`)。

## 証明の段 (書籍 pp. 120–121)

1. **`(S/Q₀) ⋊ KW` と `E ⋊ K₁W₁` の同一視**
   Ch. I §3 Lemma 5 (`W` は `q+1` を割る位数の巡回群で `S/Q₀` の `K`-部分群上
   固定点自由)。`w` を `W` の生成元とすると `w` は `S/Q₀ = F × F` の `F`-線形自己同型。
   * `θ = 1` のとき: Appendix III Prop 1 で `S/Q₀ ≅ E` (F-空間として)、
     Prop 2 で `ω ∈ E^×` と `E` の自己同型 `τ` があって `x^w = ω x^τ`。
     `w` は `Q₀` 上自明なので `ω ω^τ = 1` かつ `x^τ = x` or `x^τ = x^q`。
     後者だと `w` が偶位数になるので `x^w = ω x`。
   * `θ ≠ 1` のとき: `w` の特性多項式は既約 (`w` は `S/Q₀` の 1 次元部分空間を
     安定化しない) ⟹ `S/Q₀ ≅ F[T]/(P) = E`、`w` は `ω` 倍。
2. **`σ` の存在** — Appendix III Lemma 2(c) を使う。`χ(x) = Σ λ_{μν} x^{μ+ν}`
   (和は `Aut(E)` の濃度 1 or 2 の部分集合)。`λ₁ ≠ 0` なら `ω^{1+σ} = 1`、
   `λ₂ ≠ 0` なら `ω^{q+σ} = 1`。`ω^q ≠ ω` から `λ₂ = 0` かつ `ω^{1+σ} = 1`
   (必要なら `σ` を `σ̄` に取り替える)。
3. **`S` と `S₁` の同一視** — `φ(x,y) = x y^q` (θ=1) / `λ₁ x y^σ + …` (θ≠1)
   と置き、Appendix III Lemma 1(c) で拡大の同値を出す。
4. **`K₁W₁` の `S₁` への作用** — `U` = `Z(S₁)` と `S₁/Z(S₁)` に自明に作用する
   自己同型群 とすると `U ⊴ Aut(S₁)` で `B ⊆ UA`。`U` は 2 群 (Appendix III Lemma 1(d))
   なので **Zassenhaus ([H] I.18.3)** で `u ∈ U`, `A^u = B`。
5. **結論** — `K` は `Q₀^#` 上推移的なので内部自己同型で `s ↦ (0,1)` に正規化。

## repo 側の既存部品 (2026-07-29 実測)

| 必要なもの | 所在 | 状態 |
|---|---|---|
| type B モデル `B(n,θ,ε)` | `Suzuki2Groups/Types.lean` `TypeBData` / `TypeBModel` / `typeBQuadraticMap` / `IsTypeBEpsilon` | ✅ |
| Appendix III Lemma 1(b) (twisted product) | `Suzuki2Groups/QuadraticExtensions.lean` | ✅ |
| Appendix III Prop 2 (`B(n,1)` の自己同型) | `Suzuki2Groups/AutomorphismClassification.lean` | ✅ |
| Ch. I §3 Lemma 5 | `StructureOfH/*` `lemmaFive_of_orderThree` | ✅ |
| (C2) の供給 | `CaseABConclusion.lean` `theoremAConclusion_or_caseC2` (0166) | ✅ |
| Appendix III Prop 1 (`θ=1` の体モデル) | `Suzuki2Groups/FieldModel.lean` | ✅ |
| Appendix III Lemma 1(a)(b) | `Suzuki2Groups/QuadraticExtensions.lean` | ✅ |
| Appendix III Lemma 1(c) (拡大の同値) / 1(d) (`U` は 2 群) | `GroupTheory/CentralExtensionAutomorphisms.lean` | ✅ |
| Appendix III Lemma 2(a)(b)(c) | `GroupTheory/RepresentationTheory/SemilinearFieldAut.lean` + `Algebra/QuadraticMapCoordinates.lean` (issue 0148) | ✅ |
| Zassenhaus [H] I.18.3 (補群の共役性) | `OddOrder/Mathlib/SchurZassenhausConj.lean` | ✅ |

**⟹ 必要な Appendix III の道具はすべて repo に在る**。§3 本体は
「既存部品を (C2) の `S` に当てて標準形へ移す」作業で、新規の外部理論は要らない。

## やること (段ごとに leaf を切る想定)

- [x] 上表の ❓ を実測 (2026-07-29: 全部 ✅ だった)
- [ ] 段 (1): `S/Q₀ ≅ E` と `w` のスカラー化
- [ ] 段 (2): `σ` の存在
- [ ] 段 (3): `S ≅ S₁`
- [ ] 段 (4): 作用の共役化 (Zassenhaus)
- [ ] 段 (5): `s ↦ (0,1)` の正規化
- [ ] Proposition 本体の statement + AxiomsCheck 登録

## 完了条件

(C2) の下で `S ⋊ KW ≅ S₁ ⋊ K₁W₁` (上の 5 条件込み) が sorry-free で landing。

## 参照

* pp. 119–121 = `references/peterfalvi/pages/peterfalvi-p{119,120,121}.png`
* 上流 = [0165](closed/0165-pf-part2-ch3-s2-order-five.md) / [0166](closed/0166-pf-part2-ch3-s3-case-ab-conclusion.md)
* 下流 = Ch. IV「Characterization of PSU(3,q)」(pp. 122–134)

## 進捗 (2026-07-29 その 2)

段 (1) の**数え上げ核**を先に landing:

`OddOrder/Algebra/PowSubOneDvd.lean`
* `OddOrder.Nat.pow_sub_one_dvd_pow_sub_one_iff` — `a^m − 1 ∣ a^n − 1 ↔ m ∣ n` (`2 ≤ a`, `m ≠ 0`)
* `OddOrder.Nat.eq_zero_or_eq_or_eq_two_mul_of_two_pow_sub_one_dvd` —
  `2^n − 1 ∣ 2^j − 1` かつ `j ≤ 2n` ⟹ `j ∈ {0, n, 2n}`

これで「`S/Q₀` (位数 `q² = 2^{2n}`) の `K`-不変部分群の位数は `1`, `q`, `q²` のいずれか」が出る
(`K` は位数 `q−1` で自由に作用 ⟹ `FreeActionOrbitCount.dvd_card_sub_one_of_free_off_unique_fixed`
で `q−1 ∣ |U| − 1`)。よって**真の非自明 `K`-不変部分群 = 書籍の「`K`-部分群」(位数 `q`)** となり、
`W` がその上で固定点自由 (Ch. I §3 Lemma 5 の内部事実 `hprojfree`) ならば `KW` は既約に作用する。

### 段 (1) の残り (次の一手)

1. **`KW` の `S/Q₀` 上の既約性** — 上の数え上げ + `W` の固定点自由性。
   ⚠ `hprojfree` は `WCyclicDivides.lean` の `isCyclic_W_and_card_dvd_of_orderThree` 内部の
   `have` (l.246) に埋まっている。`Q/Z(Q) ≃ 𝔽_q × 𝔽_q` の設定ごと**再利用可能な補題に切り出す**
   のが次の作業。
2. `Huppert.exists_field_of_irreducible` を `T := KW`, `E := S/Q₀` に当てて
   **`E = 𝔽_{q²}`** と `S/Q₀` の 1 次元性を得る (= 書籍の `S/Q₀ ≅ E`)。
3. `K ↦ F^×`, `W ↦ W₁ ≤ {x : x^{1+q} = 1}` の同定。
