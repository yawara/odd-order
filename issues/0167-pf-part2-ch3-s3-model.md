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
- [x] 段 (2): `σ` の存在 — **完了** (2026-07-30, `exists_sigma_inverting_W1`)。`θ = 1` 分岐は `QuotientFieldModel.bar_mu_K`/`bar_mu_W`、一般の場合は 5 段計画 (下記) を全部通した
- [x] 段 (3): `S ≅ S₁` — **本体完了** (2026-07-30, `ModelIsomorphism.lean`)。残るのは
  書籍の**明示 cocycle `φ`** の構成のみ (下記「段 (3) の残り」)。Appendix III Lemma 1(c) =
  `GroupExtension.exists_mulEquiv_of_comp_squareMap_eq` (`CentralExtensionAutomorphisms.lean`)
  が中身。必要な入力と現状:
  * 中心拡大 `Z(Q) → Q → Q/Z(Q)`: `GroupExtension.ofNormalSubgroupCoordinates`
    (`CentralElementaryExtension.lean`) で組める。
  * モデル側 `S₁`: `Suzuki2Groups.QuadraticExtension χ basis` (Lemma 1(b)) に χ を食わせる。
  * 商の同型 `f`: 段 (1) の `M.coord`。
  * **核の同型 `g`**: ✅ `exists_center_coordinate_equiv` (2026-07-30) —
    step 1 の `ι` は単射 `→+` だったので、値が部分体 `F` に落ちること + 両側とも `q` 元
    から全単射に格上げして `Additive Z(Q) ≃+ ↥F` にした。Lemma 1(c) が要求する形。
  * `g ∘ q = q' ∘ f` (二次写像の整合): χ の構成 (step 2) がまさにこれ。
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

さらに `(2 : E) = 0` (標数 2) も結論に入れた — 以降の段はすべて `E` の `q` 乗
Frobenius `x ↦ x^q` (書籍の `x ↦ x̄`) で書かれるので標数が必要。

### 構造化 + 段 (2) の `θ = 1` 分岐 (2026-07-30 その 3)

結論が 8 連言まで膨らんだので **`Hypothesis.QuotientFieldModel hyp m` 構造体**に束ねた
(`LemmaFiveSetup` / `Suzuki2Groups.TypeBData` と同じ流儀; 段 (3)–(5) が `σ`・`λ₁`・`φ` を
同じ体の上に足していくので、伸ばせる場所が要る)。フィールド = `E` (`Field`/`Finite`/`CharP 2`
は instance フィールド), `card`, `mu`, `coord` (書籍の `α`), `coord_act`,
`mu_K_frobFixed`, `mu_K_injective`, `mu_W_normOne`。
供給定理は `nonempty_quotientFieldModel_of_orderThree`。

**段 (2) の `θ = 1` 分岐が landing**:
* `QuotientFieldModel.bar` — 書籍の bar 作用 `x ↦ x̄ = x^q` (= `FiniteField.qFrobenius M.E 2 m`)
* `bar_mu_K` — `K₁` は bar の固定体 `F` に入る
* `bar_mu_W` — bar は `W₁` を反転する (書籍 p.120 の `x^σ = x^{-1}` for `x ∈ W₁`)

⟹ `θ = 1` なら `σ := bar` が Proposition の要求 (`σ|_F = θ = id`, `W₁` 反転) を満たす。

支える体論は [9504](closed/9504-quadratic-frobenius-subfield.md) (closed) に切り出した:
`E = 𝔽_{q²}` の bar 作用・位数 `q` の固定部分体 `F`・`Aut(F) → Aut(E)` の延長
(存在 + ちょうど 2 個)。

### p.120 冒頭の設定の `Q₀` 側 (2026-07-30 その 4)

`Hypothesis.exists_Q0_field_coordinate` (`StructureOfH/FieldRealizationK.lean`) —
書籍 p.120 冒頭の

> `K` can be identified with `F^*` in such a way that the actions of `K` on `S/Q₀`
> and on `Q₀` ... are given by `(a,b)^x = (xa,xb)` and `c^x = x^{1+θ} c`

の **`Q₀` 側**: `K` は `Q₀ ∖ {1}` 上自由かつ `|K| = |Q₀| − 1` なので regular、
Appendix I Prop 2 の regular 版 (`exists_field_coordinate_realization`) で
`Q₀` が位数 `q` の体 `F` になり `K` は乗算で作用する。座標 `α : Additive Q₀ ≃+ F`
と `γ : K ≃* F^×` が出る。既存の `exists_field_realization_K` と違い `W = 1` を要求しない
(捻り `σ` だけがその仮説を使っていた)。

`S/Q₀` 側は段 (1) の `QuotientFieldModel` (`coord` / `mu`) が担う。
**残る接着 = この 2 つの体 (`F` と `frobFixedSubfield M.E`) を同一視すること** (下記)。

### 段 (1) の残り → 段 (2) の `θ ≠ 1` 分岐へ

* `μ` 全体の単射性 (= `K ∩ W = 1` の像版) は `W` の商上の忠実性が必要で、
  monolith 内の `hfaith` (`WCyclicDivides.lean`) を切り出す作業になる。下流が要求したら着手。
* **`θ ≠ 1` 分岐の設計上の要点 (次セッションの起点)**: Appendix III Lemma 2(c) は
  **repo に完備している** — `GroupTheory/RepresentationTheory/SemilinearFieldAut.lean` の
  `autMulQuadraticMap` / `autMulQuadratic_coeff_symm` / `autMulQuadratic_diag_eq_zero`
  (独立性) + `span_autMulQuadraticMap_eq_top` (生成) で
  `χ(x) = Σ λ_{στ} σ(x) τ(x)` の一意展開が得られる。さらに
  `exists_smul_algAut_of_norm_intertwiner` はノルム形の intertwiner が単一の半線形写像
  `λ·σ` になることを言っており、Appendix III Prop 2 相当の内容。
  ⚠ **本当の障害は Lemma 2(c) ではなく「担体の位置合わせ」**: 段 (1) が吐く `E` は
  `End_{𝔽₂[KW]}(S/Q₀)` という抽象体で、type-B データ (`TypeBData`) の体 `F` と `θ` は
  別の抽象体の上にある。`χ(ax) = a^{1+θ} χ(x)` を使うには
  「`Q₀ ≅ F`」「`K ≅ F^×`」(既存: `FieldRealizationK` / `exists_field_scalar_realization`) と
  「`μ(K) = frobFixedSubfield E ^×`」(段 (1) の `mu_K_frobFixed` + `mu_K_injective`) を
  **同じ `K` 上で突き合わせて**、`F ≅ frobFixedSubfield E` の**体同型**を作る必要がある。
  単元群の群同型だけでは体同型にならないので、`K`-同変性を使って `θ` を移送する設計が要る。
  ここが本 §3 の最大の行間。

  **2026-07-30 に詰めた分析 — `TypeBData` は要らない (段 (1) と同じく書籍の入力を回避できる)**。

  接着の中身は数値的な指数 `d` に落ちる。`Q₀` 側の座標
  (`exists_Q0_field_coordinate`) で `K` は `γ : K ≅ F^×` として乗算で作用し、
  `S/Q₀` 側 (段 (1)) では `μ|_K : K ≅ (frobFixedSubfield M.E)^×`。どちらも位数 `q−1` の
  巡回群への同型なので、体同型 `F ≅ frobFixedSubfield M.E` を 1 つ選べば
  `γ'(k) = μ(k)^d` の `d` (`gcd(d, q−1) = 1`) が定まる。

  当初「書籍の `θ` = type-B パラメータを `TypeBData` から取り出す必要がある」と書いたが
  **それは誤り**。理由:

  1. χ (= `centralSquare`) の Lemma 2(c) 展開 + `K`-同変性 + 係数の一意性から
     「`λ_{στ} ≠ 0 ⟹ σ(a) τ(a) = a^d` (`a ∈ F^×`)」。`Aut(F)` は Frobenius の冪
     (`FiniteField.exists_pow_eq_of_ringAut`, 9504) なので `d ≡ 2^i + 2^{i'} (mod q−1)`
     (`i, i' < m`)。
  2. **`d` は 2 の冪倍の分しか決まらない**: `Q₀` 座標を `Frob^i ∘ α₀` に取り替えると
     `d ↦ 2^i d`。よって `2^m ≡ 1 (mod q−1)` を使って
     `2^{m−i} d ≡ 1 + 2^{(i'−i) mod m}` と**正規化できる**。
  3. ⟹ 座標を選び直せば `d = 1 + 2^j` とでき、`θ := Frob^j` (on `F`)、
     `σ := qFrobenius E 2 j` (延長は `exists_ringAut_extending_frobFixedSubfield`) と
     **intrinsic に定義できる**。Proposition の主張は `θ` を含む形で自己完結しているので、
     type-B パラメータとの一致は label 合わせ (χ の比較) にすぎない。

  ### 段 (2) `θ ≠ 1` 分岐: step 1 の前半 landing (2026-07-30 その 5)

  `Appendices/Suzuki/CenterFieldExponent.lean` (新 leaf):
  * `isElementaryAbelian_center_of_lemmaFiveSetup` — `Z(Q)` は指数 2 の初等アーベル
    (中心ゆえ可換 + `s.centerSq`)。
  * `centerKHom` — `Z(Q)` (characteristic) 上の `K`-作用。
  * `actualKActor_free_on_center` — **`K` は `Z(Q) ∖ {1}` 上自由**。`s.transCenter` の
    推移性 + `s.cardActorCenter` (`|K| = |Z(Q)| − 1`) から、軌道写像が有限同数集合間の
    全射 ⟹ 単射 ⟹ 固定化群自明。

  ⚠ 途中で `IsAInvariant.toMulAutHom` (Isaacs Ch04 `Main/ThreeSubgroups.lean`) の
  **名前の欠陥**を発見・修正: `_root_.` を欠いた宣言だったため実名が
  `OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom` になっており、
  `OddOrder.Isaacs.Ch04` 名前空間の外から参照できなかった (既存 call site は全て
  その名前空間内だったので露見していなかった)。`_root_.` を付与して修正済 (call site 不変)。

  ### 段 (2) `θ ≠ 1` 分岐の実装計画 (次の一手)

  1. ✅ **`Z(Q)` 座標を `M.E` の中へ — 2026-07-30 完了**
     (`exists_center_coordinate_exponent`)。以下は当初の計画メモ:
     `Huppert.exists_field_coordinate_realization` を `Z(Q)` + `centerKHom` に当てて
     位数 `q` の体 `F` を得る。`F` を
     `FiniteField.ringEquivOfCardEq` (Algebra instance 不要) で
     `frobFixedSubfield M.E` に移す。`s.centerEqQ0` で `Z(Q) ↔ Q₀` を渡す。
     出力 = `ι : Additive ↥(Z(Q)) ≃+ ↥(frobFixedSubfield M.E)` と
     `ι (k • z) = μ(k)^d * ι z`。
     ⚠ **残る道具**だった「巡回群の与位数の部分群は一意」は **repo に既存**だった:
     `OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq`
     (`GroupTheory/CyclicSubgroupUniqueness.lean`, issue 9161 の dedup 産物)。
     `ν` (= `Q₀` 側 `γ` を `E^×` へ送ったもの) と `μ'` (= 段 (1) の `μ|_K`) はどちらも単射
     なので像は同位数の部分群 ⟹ 一致。`K` の生成元 `k₀` で `ν k₀ = (μ' k₀)^d` を取り、
     `k = k₀^t` で全 `k` へ伝播 (`MonoidHom.map_cyclic` は使わずに済んだ)。
  2. ✅ **χ を `E` 座標へ — 2026-07-30 完了**
     (`exists_quadraticMap_of_lemmaFiveSetup`)。`χ : QuadraticMap (ZMod 2) E E` で
     anisotropic (`s.invMem`: `x² = 1 ⟹ x ∈ Z(Q)`)、値は部分体 `F` 内、
     スケーリング `χ (a x) = a^d χ x` (`a ∈ K₁ = μ(K)`)。
     `K`-同変性の核は `centralSquare_quotientKHom` (共役と二乗が可換 = `map_pow`)。
     ⚠ `Algebra (ZMod 2) E` は instance search で出ない (`ZMod.algebra` は意図的に `def`)
     ので `QuotientFieldModel.instAlgebraZModTwo` として登録した — これが
     `QuadraticMap (ZMod 2) E E` を statement に書けるようにする鍵。
     以下は当初の計画メモ: `Suzuki2Groups.centralSquareQuadraticMap`
     (Appendix III Lemma 1(a)、`Additive (Q ⧸ Z(Q)) → Additive ↥(Z(Q))` の
     `QuadraticMap (ZMod 2)`) を `M.coord` と `ι` で移して `χ_E : E → E`。
     anisotropic は `s.invMem` (`x² = 1 ⟹ x ∈ Z(Q)`) から。
  3. ✅ **Lemma 2(c) 展開 — 2026-07-30 完了** (`exists_scalingPair_of_lemmaFiveSetup`)。
     **設計上の要点**: 汎用エンジン
     `RepresentationTheory.exists_algAut_pair_scaling_of_ne_zero` として切り出した —
     「`χ ≠ 0` なら**単一の**自己同型対 `(σ,τ)` があって、χ の**あらゆる**スケーリング関係
     `χ(ax) = b χ(x)` が `σ(a)τ(a) = b` を強制する」。
     ⚠ **対が関係ごとでなく 1 つであることが本質** — 書籍が同じ係数 `λ₁` から
     `{σ|_F, τ|_F} = {1_F, θ}` と `ω^{1+σ} = 1` の**両方**を読むため。
     これで step 5 (`χ(ωx) = χ(x)`) は同じ対への 2 度目の適用で済む。
     証明: 展開の係数 `c` に対しスケーリングは
     `c_{σσ}(σ(a)²+b) = 0` と `(c_{στ}+c_{τσ})(σ(a)τ(a)+b) = 0` を与える
     (独立性側)。`c` が対称かつ対角ゼロなら swap involution + 標数 2 で χ = 0 に
     なるので、そうでない場所を 1 つ選べばよい。
     以下は当初の計画メモ: `SemilinearFieldAut.span_autMulQuadraticMap_eq_top` で
     `χ_E = Σ λ_{στ} • autMulQuadraticMap σ τ`、`autMulQuadratic_coeff_symm` /
     `autMulQuadratic_diag_eq_zero` で係数一意。`K`-同変性から `d ≡ 2^i + 2^{i'}`。
  4-5. ✅ **正規化 + `ω^{1+σ} = 1` — 2026-07-30 完了** (`exists_sigma_inverting_W1`)。
     実装は当初計画より短くなった:
     * `χ(ωx) = χ(x)` は `centralSquare_quotientWHom` (= `w` は `Q₀` 上自明かつ
       二乗は既に `Q₀` に居る) から出て、step 3 と**同じ対** `(σ,τ)` に 2 度目の
       適用をするだけで `σ(ω)τ(ω) = 1` になる。
     * `σ`, `τ` は有限体の自己同型ゆえ Frobenius の冪 (9504 の
       `exists_pow_eq_of_ringAut`)。よって関係は `ω^{2^i} ω^{2^{i'}} = 1` という
       **純粋な指数計算**に落ちる。
     * `FiniteField.exists_qFrobenius_normalized_index` — `Frob^{N-i}` を両辺に当てると
       (`Frob^N = 1` ゆえ) 第 1 因子が `ω` になり `ω · ω^{2^j} = 1` を得る。
       これが書籍の「必要なら `σ` を `σ̄` に取り替える」の正体。
     ⚠ 書籍の `λ₂` を `ω^q ≠ ω` で落とす議論は**不要だった** — 対称形
       `σ(ω)τ(ω) = 1` から直接正規化できるため。

### 段 (3) 完了 — `S ≅ S₁` (2026-07-30 その 6)

`OddOrder/Peterfalvi/Appendices/Suzuki/ModelIsomorphism.lean` (新 leaf)。

**設計上の発見: Lemma 1(c) の `q`/`q'` は「関数」で足りる**。
`GroupExtension.exists_mulEquiv_of_comp_squareMap_eq` の square map 引数は
`(q : V → W) (q' : V' → W')` という**素の関数**なので、`F` 値版の χ を
`QuadraticMap` として作り直す必要は無い…と当初は考えたが、`φ` の側 (`BilinMap`) を
書くには結局 `F` 値の対象が要るので、χ 自体を `F` 値の `QuadraticMap` として作った
(`ι` が既に `F` 値なので `gL.compQuadraticMap` 一発で、証明の重複はゼロ)。

* `centreQuadraticMap` — `χ : E → F` を `𝔽₂`-二次写像として。段 (1) の `M.coord` と
  段 (3) 準備の `ι : Additive Z(Q) ≃+ ↥F` で、降下した二乗写像 (Appendix III Lemma 1(a))
  を移送しただけ。`E` 値の `exists_quadraticMap_of_lemmaFiveSetup` (段 (2) 用) との違いは
  値域だけ。
* `toMul_symm_centreQuadraticMap` — Lemma 1(c) の `hsqS`: `e²` を `ι` 越しに読むと `χ`。
* `centreQuadraticMap_anisotropic` — `χ x = 0 → x = 0` (`s.invMem`)。
* `exists_mulEquiv_bilinearTwistedProduct` — **段 (3) 本体**。`φ x x = χ x` を満たす
  **任意の**双線形 `φ` に対し `Q ≃* (E ×_φ F)`、しかも**両座標と整合**
  (中心 → 核座標が `ι`、商 → `M.coord`)。書籍が「`φ` を書き下して対角が `χ` であることを
  確認する」という使い方をするので、この形が正しい一般性。
* `exists_mulEquiv_quadraticExtension` — 基底による標準リフト `χ.toBilin basis` を入れた
  無条件版 (モデルの存在)。

副産物 (`Suzuki2Groups/QuadraticExtensions.lean`):
`BilinearTwistedProduct.sq_eq_inl_diag` — **twisted product の二乗写像は cocycle の対角
にしか依らない**。これが「書籍の明示 `φ` と基底リフトが交換可能」の根拠。既存の
`QuadraticExtension.sq_eq_inl_q` はこの特殊化に置換 (dedup、private `add_self_eq_zero` は
公開の `zmodTwo_add_self` に一本化)。

### 段 (3) の残り — 書籍の明示 cocycle `φ` (2026-07-30 その 7 で分解 + 部品 2 つ landing)

Proposition の主張は `φ` に **`φ(ax, by) = a b^θ φ(x,y)` (`a,b ∈ F`)** を要求する
(基底リフトはこれを満たさない)。書籍の `φ(x,y) = λ₁ x y^σ + λ̄₁ x̄ ȳ^σ` を作るには
Lemma 2(c) 展開の**係数 `λ₁` 自体**を露出させる必要がある — 現在の
`exists_scalingPair_of_lemmaFiveSetup` は対 `(σ, τ)` しか返していない。必要な追加は

**⚠ 設計上の発見: `λ₂ = 0` は要らない**。Proposition が `φ` に要求するのは
(i) 双加法性、(ii) `φ(ax,by) = a b^θ φ(x,y)` (`a,b ∈ F`)、(iii) `x ≠ 0 ⟹ φ(x,x) ≠ 0`
の 3 つだけ。書籍の 4 項 `λ₁ x y^σ + λ̄₁ x̄ ȳ^σ + λ₂ x̄ y^σ + λ̄₂ x ȳ^σ` は
**`λ₂` 項も (ii) を満たす** (`bar|_F = id` ゆえ `bar` を第 1 変数に置いた項も
`a ↦ a` で作用する)。よって `λ₂ = 0` (書籍が `ω^q ≠ ω` で出す) は**主張には不要**で、
必要なのは「生き残る対 `(σ,τ)` の `F` 制限が `{1_F, θ}` である」ことだけ。

分解 (P1-P5):

* **P1 ✅ 楔正規化した展開** (2026-07-30, `SemilinearFieldAut.lean`)。
  `exists_scaling_pinned_expansion` — Lemma 2(c) 展開を「非順序対ごとに代表 1 つ」へ
  折り畳むと、**生き残る係数がすべて** scaling relation に pin される
  (`c στ ≠ 0 → σ(a) τ(a) = b`)。生の展開は対称・対角ゼロな族を足す自由度があり
  (`sum_autMulQuadratic_eq_zero_of_symm`、既存 `hzeroOfSym` を抽出して dedup)、
  独立性側もその分しか効かないので、この正規化が必須。
  既存 `exists_algAut_pair_scaling_of_ne_zero` (対を **1 つ**取る、段 (2) 用) の強化版。
* **P2 ✅ 指数の帳簿** (2026-07-30, `Algebra/FrobeniusExponentPairs.lean` +
  `two_pow_pair_sum_eq`)。`frobIndex_pair_eq_of_pow_mul_eq` — `a^{2^i} a^{2^j} =
  a^{2^k} a^{2^l}` が全 `a` で成り立てば `{i,j} = {k,l} (mod n)`。`(k,l) = (0,t)` で
  「`{σ|_F, τ|_F} = {1_F, θ}`」になる。
* **P3 (半分 ✅) 生き残る対の `F` 制限が全部同じであること + `α = id` への正規化**。
  * ✅ **並べ替えた双線形持ち上げ** (2026-07-30,
    `RepresentationTheory/SemilinearBilinearLift.lean`)。
    `exists_bilinear_lift_of_pinned_restriction`: 展開の生き残る対が全て
    スカラー集合 `A` 上で非順序対 `{α, β}` に制限されるなら、各対を `(α, β)` の
    順に並べ替えて足した `φ(x,y) = Σ c_{στ} ρ₁(x) ρ₂(y)` は双線形で、対角が `χ`
    (両順序は対角上で一致するので並べ替えは見えない)、かつ
    `φ(ax, by) = α(a) β(b) φ(x,y)` (`a, b ∈ A`)。`A = F^×`, `α = 1`, `β = θ` で
    書籍の cocycle 条件そのもの。**純粋に代数的** — 数論は仮説に出してある。
  * ⏳ **残り**: その仮説 (`hres`) を pin から出すこと。必要なのは
    (i) `E` の自己同型は Frobenius 冪 (既存 `exists_pow_eq_of_ringAut`)、
    (ii) `a ∈ F ⟹ a^{2^i} = a^{2^{i mod m}}` (`F` 上 `Frob^m = 1`)、
    (iii) 2 つの生き残る対を `frobIndex_pair_eq_of_pow_mul_eq` (P2) で比較。
  * ⏳ **`α = id` への正規化**: `Frob_E^{-i₀}` を全体に当てる (χ は
    `Frob^{-i₀} ∘ χ` に、これは座標 `ι' := Frob^{-i₀} ∘ ι` に対する χ)。
  以下は当初の分析メモ:
  **⚠ ここで書籍より短くなる**: `d` を先に `1 + 2^t` へ正規化する必要は無い。
  生き残る対を 1 つ (`(σ₀,τ₀)`) 取れば、他の全ての生き残る対 `(σ,τ)` は
  `a^{2^{i'}+2^{j'}} = a^d = a^{2^{i₀'}+2^{j₀'}}` (`' = mod m`) を満たすので、
  **P2 を 2 つの対の比較に使うだけで** `{σ|_F, τ|_F} = {σ₀|_F, τ₀|_F} =: {α, θ'}`
  が全対で共通と分かる (`d` の形は不要)。順序を `σ|_F = α`, `τ|_F = θ'` に揃えると
  `φ(ax,by) = α(a) θ'(b) φ(x,y)`。
  そのうえで **`φ̃ := α⁻¹ ∘ φ`** を取れば `φ̃(ax,by) = a · (α⁻¹θ')(b) · φ̃(x,y)` で
  書籍の形になり、`φ̃` の対角は `α⁻¹ ∘ χ` = **座標 `ι' := α⁻¹ ∘ ι` に対する χ**。
  ⟹ `centreQuadraticMap` は `ι` を引数に取るので、**`(ι', φ̃)` を組で吐けばよい**
  (`θ := α⁻¹ θ'` を intrinsic に**定義**する)。座標変換を Z(Q) 側へ押し戻す必要なし。
* **P4 ✅ `φ` が `F` 値であること — 係数の bar 対称性は要らない** (2026-07-30,
  `Algebra/QuadraticTraceCorrection.lean`)。`exists_bilinear_frobFixed_of_diag`:
  対角が `F` 値な双線形形式は、**対角を変えずに**全値を `F` に補正できる。
  明示式 `ψ = φ + u·(Tr ∘ φ)` (`Tr u = 1`) も結論に入れてあるので、消費側は
  半双線形性の継承を自分で出せる (`a b^θ ∈ F` は `Tr` を素通りする)。
  支える trace 論 = `frobTrace` (`z ↦ z + z^q`) / 核が `F` / 像が `F` /
  `Tr u = 1` なる `u` の存在 (`Tr ≡ 0` なら `E = F` で位数矛盾)。
  以下は当初の分析メモ:
  当初は `λ_{μ̄ν̄} = λ̄_{μν}` が要ると考えたが、**trace で補正すれば済む**:
  * `Tr : E → F`, `Tr z = z + z̄`。標数 2 で `E/F` は 2 次なので `ker Tr = F`
    (位数勘定; `z ∈ F ⟺ z + z̄ = 0`)。
  * `T := Tr ∘ φ` は双線形で、対角は `Tr(χ x) = 0` (χ は `F` 値) ⟹ **交代形式**。
  * `Tr e = 1` なる `e ∈ E` を取り `A(x,y) := e · T(x,y)` と置くと `A` は交代的で
    `Tr ∘ A = T` (`T` は `F` 値ゆえ `Tr(e T) = (e + ē) T = T`)。
  * ⟹ `φ + A` は対角が同じ `χ` のまま `Tr ∘ (φ + A) = 0`、すなわち **`F` 値**。
  * しかも `a, b ∈ F` に対する半双線形性を**保つ**: `A(ax,by) = e Tr(a b^θ φ) =
    a b^θ e Tr(φ) = a b^θ A(x,y)` (`a, b` は bar 不変)。
  ⟹ 一般補題「対角が `F` 値な双線形持ち上げは、同じ対角のまま `F` 値に補正でき、
  `F`-半双線形性を保つ」(~40 行) で片付く。
* **P5 ⏳ 組み立て**: `φ(x,y) := Σ c_{στ} σ(x) τ(y)` (P1 の正規化係数) → P3 で順序を
  揃えて半双線形性 → P4 で `F` 値に補正 → corestrict して
  `exists_mulEquiv_bilinearTwistedProduct` に食わせて完了。

### 段 (2) 完了 (2026-07-30)

`exists_sigma_inverting_W1`: `∃ j`, 全ての `v ∈ W` で
`μ(1,v) · Frob^j(μ(1,v)) = 1`。すなわち `σ := Frob^j` が `W₁` を反転する。
`σ|_F` が書籍の `θ` (本 repo では intrinsic に**定義**する側なので追加の整合は不要)。

## 📖 p.120–121 の proof 全文の書き起こし (2026-07-30, ページ画像から)

⚠ **これが正本**。Peterfalvi の text レイヤは数式が壊れているので、以下は
`references/peterfalvi/pages/peterfalvi-p{120,121}.png` を直接読んで転記したもの。
次セッションはページ画像を再読しなくてよい。

### p.120 冒頭 (Proposition の直前の設定)

`ε ∈ F` は `χ(a,b) = 0 ⟹ a = b = 0` を満たす。さらに `K` は `F^*` と同一視でき、
`S/Q₀ ≅ F × F` と `Q₀ ≅ F` 上の `K` の作用は

    (a,b)^x = (xa, xb),  c^x = x^{1+θ} c   (x ∈ F^*, (a,b) ∈ F × F, c ∈ F)

で与えられる。`x ∈ E` に対し `x̄ = x^q` と置く。

### Proposition (p.120)

`S ⋊ KW → S₁ ⋊ K₁W₁` の同型があり、`S ↦ S₁`, `K ↦ K₁`, `s ↦ (0,1)`。ここで

* `S₁` = 全ての対 `(x,y)` (`x,y ∈ E`) のうち、**`θ ≠ 1` なら `y ∈ F`**、
  **`θ = 1` なら `y + y^q = x^{1+q}`** を満たすもの。演算は
  `(x,z)(y,u) = (x+y, z+u+φ(x,y))`。
* `θ = 1` なら `φ(x,y) = x y^q`。そうでなければ `φ : E × E → F` は双加法的で
  `φ(ax,by) = a b^θ φ(x,y)` (`a,b ∈ F`)、かつ `x ≠ 0 ⟹ φ(x,x) ≠ 0`。
* `K₁W₁ ≤ E^*` で `K₁ = F^*`、`W₁` は `{x ∈ E^* | x^{1+q} = 1}` の非自明部分群。
  **`E` の自己同型 `σ` があって `σ|_F = θ` かつ `x ∈ W₁ ⟹ x^σ = x^{-1}`**。
  `K₁W₁` の `S₁` への作用は `(x,y)^a = (ax, a^{1+σ} y)` (`a ∈ K₁W₁`)。

### 証明 (1) `(S/Q₀) ⋊ KW` と `E ⋊ K₁W₁` の同一視

Ch. I §3 Lemma 5 で `W` は位数が `q+1` を割る巡回群で、**`S/Q₀` の `K`-部分群全体の上に
固定点自由に作用する**。`w` を `W` の生成元とすると `w` は `S/Q₀ ≅ F × F` の
`F`-線形自己同型。

* `θ = 1`: Appendix III Prop 1 で `S/Q₀` を `E` と (`F`-空間構造と両立する形で) 同一視し、
  中心拡大 `F → S → E` に付随する二次写像が `χ(x) = x x̄` になるようにする。
  Appendix III Prop 2 より `ω ∈ E^*` と `E` の自己同型 `τ` があって、`x ∈ S/Q₀ ≅ E` に対し
  `x^w = ω x^τ`、`y ∈ Q₀ ≅ F` に対し `y^w = ω ω̄ y^τ`。`w` は `Q₀` 上自明ゆえ
  `ω ω̄ = 1` かつ `x^τ = x` または `x^τ = x̄`。後者だと `w` は偶位数になるので
  `x^w = ω x`。
* `θ ≠ 1`: `w` の (`S/Q₀` の `F`-自己同型としての) 特性多項式 `P(T)` は既約
  (`w` は `S/Q₀` の 1 次元部分空間を安定化しない)。よって `S/Q₀` は `F`-線形に
  `F[T]/(P) ≅ E` と同一視でき、`w` の作用は `P(ω) = 0` なる `ω ∈ E` の乗算になる。

⟹ **本 repo の段 (1) はこの場合分けを回避した** (`KW` 全体の既約性 → Appendix I Prop 2)。
書籍の `ω` は `μ (1, w)` に対応する。

### 証明 (2) `σ` の存在  ← **次の作業**

`θ = 1` なら `x^σ = x^q` (`q` 乗 Frobenius) と置けば `σ|_F = θ` (= 恒等) かつ
`x ∈ W₁ ⟹ x^σ = x^{-1}` (`x^{1+q} = 1` ゆえ)。**この分岐は段 (1) の結論から即出る**
(結論の第 4・第 6 連言がまさに `σ(μ(k,1)) = μ(k,1)` と `σ(μ(1,v)) = μ(1,v)⁻¹`)。

`θ ≠ 1` を仮定する。`χ : E → F` を中心拡大 `F → S → E` に付随する二次写像とする。
Appendix III Lemma 2(c) により `λ_{μν} ∈ E` を取って

    χ(x) = Σ λ_{μν} x^μ x^ν     (和は Aut(E) の濃度 1 or 2 の部分集合 {μ,ν} 全体)

と書ける。`χ(x) = χ(x)‾` (= `χ` は `F` 値) と、`a ∈ F`, `x ∈ E` に対し
`χ(ax) = a^{1+θ} χ(x)` に注意して同 lemma を適用すると

* `λ_{μ̄,ν̄} = λ_{μν}‾`  (ここで `μ̄(x) = μ(x)‾`)
* `λ_{μν} ≠ 0 ⟹ a^μ a^ν = a a^θ` (`a ∈ F`)、ゆえに `{μ|_F, ν|_F} = {1_F, θ}`

が出る。よって `σ` が `θ` を延長する `E` の自己同型なら

    χ(x) = λ₁ x^{1+σ} + λ₁‾ x̄^{1+σ} + λ₂ x^{q+σ} + λ₂‾ x̄^{q+σ}

で `λ₁, λ₂ ∈ E` は両方 0 でない。`w` は `Q₀` 上自明ゆえ `χ(ωx) = χ(x)`、
同 lemma より **`λ₁ ≠ 0 ⟹ ω^{1+σ} = 1`**、**`λ₂ ≠ 0 ⟹ ω^{q+σ} = 1`**。
`ω^q ≠ ω` だから `λ₂ = 0` かつ `ω^{1+σ} = 1` (必要なら `σ` を `σ̄` に取り替える)。

⟹ `ω^{1+σ} = 1` は `σ ω = ω⁻¹` と同値で、`W₁ = ⟨ω⟩` なので Proposition の
「`x ∈ W₁ ⟹ x^σ = x^{-1}`」が出る (この橋渡しは 3 行)。

### 証明 (3) `S` と `S₁` の同一視

    φ(x,y) = x y^q                    (θ = 1)
    φ(x,y) = λ₁ x y^σ + λ₁‾ x̄ ȳ^σ     (θ ≠ 1)

と置く。statement の演算で `S₁` が群になり、`F ↪ S₁ ↠ E`
(`ι(y) = (0,y)`, `π(x,y) = x`) が二次写像 `χ` を持つ中心拡大になることを確認する。
Appendix III Lemma 1(c) より、この拡大は `F → S → E` と同値。

### 証明 (4) `K₁W₁` の `S₁` への作用

`A` = `KW` の `Aut(S₁)` における像 (`KW` は `S ≅ S₁` 上共役で作用)。
statement の式が `K₁W₁` の `S₁` への作用を定めることを確認し、`B` = その作用による
`K₁W₁` の `Aut(S₁)` における像とする。`U` = `Z(S₁)` 上と `S₁/Z(S₁)` 上で恒等を誘導する
`S₁` の自己同型群。すると `U ⊴ Aut(S₁)` で、(1) より `B ⊆ UA`。`U` は 2 群
(Appendix III Lemma 1(d)) なので Zassenhaus ([H] Kapitel I, Hauptsatz 18.3) より
`u ∈ U` があって `A^u = B`、この `u` が `S₁ ⋊ A → S₁ ⋊ B` の同型を誘導する。

### 証明 (5) 結論

`K` は `Q₀^#` 上推移的なので、同型 `S ⋊ KW → S₁ ⋊ K₁W₁` に `S₁ ⋊ K₁W₁` の内部自己同型を
合成して `s` を `(0,1)` に送れる。∎
