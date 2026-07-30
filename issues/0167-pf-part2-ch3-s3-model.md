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
- [x] 段 (1): `S/Q₀ ≅ E` と `w` のスカラー化 (2026-07-30, `QuotientKWField.lean`)
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

## 進捗 (2026-07-30) — 段 (1) 完了、書籍の場合分けは不要だった

`OddOrder/Peterfalvi/Appendices/Suzuki/QuotientKWField.lean` (新 leaf)。

**設計上の発見**: 書籍は `θ = 1` / `θ ≠ 1` で場合分けし、Appendix III Prop 1/2 で
`ω ∈ E^×` を作る。しかし **`KW` 全体の既約性**を先に出すと、Appendix I Prop 2
(`Huppert.exists_field_semilinear_with_scalar`) が一発で体 `E` (位数 `q²`) を吐き、
`ω = μ (1, w)` として自動的に得られる。**`θ` の場合分けは要らない**。

* `Hypothesis.quotientKHom` / `quotientWHom` — 中心商 `Q ⧸ Z(Q)` 上の `K` / `W` 作用
  (どちらも `quotientMulAutHom`; 中心は characteristic なので誘導は無条件)。
  `@[reducible]` にしてあるのは `LemmaFiveSetup` の各フィールドと moved-summand engine が
  生の `quotientMulAutHom` で書かれているため (書換なしで unify させる)。
* `Hypothesis.quotientKWHom` — `MonoidHom.noncommCoprod` による `K × W` の結合作用。
  **直積**を取るのが要点: `W = C_V(K)` ゆえ 2 つの作用は可換
  (`commute_quotientKHom_quotientWHom`) で、直積なら群自体が可換 = Appendix I Prop 2 の
  `[CommGroup T]` を満たす (`MulAut` 内での積を取ると可換性が言えない)。
* `Hypothesis.isAInvariant_quotientKW_eq_bot_or_top` — **既約性**。`KW`-不変 ⟹ `K`-不変 ⟹
  位数は `q` の冪 (`card_invariant_eq_pow_of_fixedPointFree`) ⟹ `|S/Q₀| = q²` から
  `1`, `q`, `q²` のいずれか ⟹ 中間の `q = |Z(Q)|` は moved-summand engine
  (`map_quotientCongr_ne_of_fixedPoints_le`) が `W ∋ w ≠ 1` で潰す。
* `Hypothesis.exists_field_quotient_of_orderThree` — 体 `E`, `|E| = q²`,
  座標 `α : Additive (S/Q₀) ≃+ E` (書籍 p.119 の `α`)、`μ : K × W →* E^×` で
  作用が `E` 内の乗算になる。

### 副産物 (一般化 / dedup)

* `card_dvd_card_sub_one_of_fixedPointFree` と `card_invariant_eq_pow_of_fixedPointFree`
  (`Higman/.../XiLengthFromCard.lean`) を **`K : Subgroup (MulAut P)` から任意の
  `φ : A →* MulAut P` へ一般化**。商 `P ⧸ Z` 上の actor は誘導準同型で subgroup 包含では
  ないので、これが無いと当てられなかった。
* `dvd_of_two_pow_sub_one_dvd` (同ファイル、35 行の自己完結証明) を
  `OddOrder.Nat.pow_sub_one_dvd_pow_sub_one_iff` の base-2 特殊化に置換 (dedup)。
* `Huppert.exists_addEquiv_of_finrank_eq_one` — 「1 次元空間はその係数体そのもの」の
  座標化ステップを切り出し、`exists_field_coordinate_realization` と新規
  `exists_field_coordinate_of_irreducible` の両方で共有。
* `Huppert.exists_field_coordinate_of_irreducible` — 既存の
  `exists_field_coordinate_realization` (作用が regular = `|T| = |E| − 1` を要求) の
  **既約版**。`|KW| = (q−1)|W|` は `|W| ∣ q+1` しか分からないので regular 版は使えない。

### `K₁ = F^×` / `W₁ ≤ {x : x^{1+q} = 1}` も同 leaf に landing (2026-07-30 その 2)

`exists_field_quotient_of_orderThree` の結論に 3 つの連言を追加:

* `((μ (k,1) : E)) ^ q = (μ (k,1) : E)` — `|K| = q−1` ゆえ `μ(K)` は Frobenius
  `x ↦ x^q` の固定体 = 部分体 `F = 𝔽_q` に入る (書籍の `K₁ = F^×` の「⊆」)。
* `Function.Injective (fun k => μ (k,1))` — `s.freeQuotient` から。これで像の位数が
  ちょうど `q−1`、すなわち巡回群 `E^×` の唯一の位数 `q−1` 部分群 = `F^×` に**一致**する。
* `μ (1,v) ^ (q+1) = 1` — Lemma 5 の `|W| ∣ q+1` から (書籍の `W₁ ≤ {x : x^{1+q} = 1}`)。

### 段 (1) の残り → 段 (2) へ

* `μ` 全体の単射性 (= `K ∩ W = 1` の像版) は `W` の商上の忠実性が必要で、
  monolith 内の `hfaith` (`WCyclicDivides.lean`) を切り出す作業になる。下流が要求したら着手。
* 段 (2) `σ` の存在は Appendix III Lemma 2(c) +
  `SemilinearFieldAut` / `QuadraticMapCoordinates` (issue 0148) を `E` に当てる。
  ⚠ `exists_field_semilinear_with_scalar` の**第 4 連言 (semilinearity)** を今は捨てている
  (`- ` で潰した) が、段 (2) の `σ` はまさにこれ — `t` による共役が `KW` の作用を
  正規化するので、`σ : E ≃+* E` が出る。段 (2) では捨てずに受け取ること。
