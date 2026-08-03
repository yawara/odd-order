---
id: 9506
slug: modular-p-modular-system
title: "modular 表現論の底: p-modular system と Brauer 指標 (0147 の bottom-up 第 1 段, hub claim)"
created: 2026-08-03
---

# modular 表現論の底: p-modular system と Brauer 指標

**claim**: hub / main session (9500 band) / **状態**: 着手 (2026-08-03)

## 位置づけ

[issue 0147](0147-q8-modular-char-theory-frozen.md) (Q₈ Brauer–Suzuki, spine = Navarro 1998
Ch.1–7 / Z\*-定理) の **bottom-up 第 1 段**。project spec =
`notes/meta/q8_modular_char_theory_frozen_project.md` §3 の (1)(2)。

3 冊 (Isaacs / BG / Peterfalvi) の残り唯一の実 `sorry` が
`Peterfalvi/Appendices/RankOneAffineModel.lean` の `brauerSuzuki_quaternionSylow_q8` であり、
その根には mathlib にも本リポジトリにも**一切存在しない** modular 表現論がある (下記実測)。

## 着手前検索の結果 (2026-08-03 実測)

* **mathlib に無い**: `BrauerCharacter` / `decompositionMatrix` / block 論 / `defectGroup` は
  0 件 (`CartanMatrix` はルート系のもので別物)。mathlib の表現論は char 0 の ordinary のみ。
* **本リポジトリにも無い**: `OddOrder/GroupTheory/RepresentationTheory/` は 114 leaf あるが
  すべて ordinary。`pRegular` / `IsPRegular` / `IsDiscreteValuationRing` / `ResidueField` の
  grep はいずれも 0 件。
* 使える土台: mathlib の `IsDiscreteValuationRing` / `IsLocalRing.ResidueField` /
  `IsAdicComplete`、および本リポジトリの ordinary 指標一式
  (`ClassFunction` / `IrreducibleCharacter` / 誘導指標 / 直交関係)。

## 設計方針 (この issue で決める分岐)

Brauer 指標の定義には 2 つの流儀がある:

1. **p-modular system 経由** (Navarro Ch.1–2 の流儀): 完備 DVR `𝒪` (剰余体 `k` が char `p`,
   商体 `K` が char 0) を固定し、`p'`-位数の 1 の冪根の群 `U ⊆ K^×` と `k^×` の間の同型を通す。
2. **代数閉体 `k` だけで定義**: `k^×` の `p'`-部分と `ℂ^×` の `p'`-部分の間の単射を固定する。

**採用 = 1 (p-modular system)**。理由: block 論 (Brauer 対応・defect group、Navarro Ch.3–6) が
`𝒪` 上の冪等元の持ち上げを本質的に使うので後段で必ず必要になる。2 から始めると block 論の
段で作り直しになる。

⚠ **carrier の構成可能性 (CLAUDE.md「進捗の測り方」)**: `IsPModularSystem` を仮説クラスとして
置くだけでは doneness にならない。任意の `p` と `n` に対して「`n` 乗根を含む分裂 p-modular
system」を**実際に構成する**ところまでを本 issue のスコープに含める
(`ℤ[ζ_n]` の `p` 上の極大イデアルでの局所化 → 完備化)。これが無いと最終定理が空虚になる。

## やること (bottom-up)

- [x] **`p`-正則元の API** = `OddOrder/GroupTheory/PRegularElement.lean` (2026-08-03)。
      `IsPElement` / `IsPRegular` / `pPart` / `pRegularPart` と分解
      `g = g_{p'} · g_p`・**一意性** (`eq_pPart_of_commute`)・共役同変性。
      mathlib は群の元 1 個の `p`/`p'` 分解を持たない (実測)。
      ⚠ `(ordCompl[p] n : ℤ)` は **ℤ の除算**で elaborate される罠あり (docstring に明記)。
- [x] **根の持ち上げ** = `.../Modular/RootsOfUnityLift.lean` (2026-08-03)。
      Henselian 局所環 `𝒪` で `n` が単元なら還元は同型 `μ_n(𝒪) ≃* μ_n(k)` を誘導
      (`rootsOfUnityEquivResidue`)。一意性は `X^n - 1` の 1 次 Taylor 展開
      (`Polynomial.binomExpansion`) で `f'(b) = n b^{n-1}` が単元、
      存在は `HenselianLocalRing.is_henselian`。
      ⟹ **これが p-modular system の技術的核**。`𝒪` に完備 DVR を要求せず
      Henselian だけで足りることが分かったので、束ねの仮説はこれに合わせる。
- [x] **束ね** = `.../Modular/PModularSystem.lean` (2026-08-03)。
      `IsPModularSystem p 𝒪` = 「Henselian 局所環 `𝒪` が char 0、剰余体が char `p`」。
      `isUnit_natCast_of_not_dvd` (`p ∤ n` ⟹ `n` は `𝒪` の単元) と
      `rootsOfUnityEquivResidue_of_not_dvd` (`p ∤ n` で `μ_n(𝒪) ≃* μ_n(k)`)。
      ⚠ **非空虚性**: `ℤ_[p]` が instance (`instIsPModularSystemPadicInt`)。
      そのために `henselianLocalRing_of_isAdicComplete` (完備局所環は Henselian) を
      補った — mathlib は `HenselianRing R I` 版しか持たない (実測)。
- [x] **分裂 p-modular system の具体構成** (2026-08-03)。**不分岐拡大 = Witt ベクトル**を採用。
      2 leaf:
      * `.../Modular/WittVectorSystem.lean` — `k` が標数 `p` の完全体なら `𝕎 k` は
        `p`-modular system で **剰余体が `k` 自身** (`wittVectorResidueFieldEquiv`)。
        mathlib の `WittVector.quotientPEquiv` (`𝕎 k ⧸ (p) ≃+* k`) +
        `isAdicCompleteIdealSpanP` + `isDiscreteValuationRing` から
        `maximalIdeal (𝕎 k) = (p)` → Henselian を組む。`CharZero (𝕎 k)` は
        `n = p^a · m` 分解 + `p`-torsion freeness + 定数項が単元、で自前。
      * `.../Modular/SplittingSystem.lean` — **`SplittingSystem p n = 𝕎 (GF(p^φ(n)))`**。
        Euler (`p^φ(n) ≡ 1 mod n`) で `n ∣ |GF| − 1` ⟹ 有限体が `μ_n` を全部持つ ⟹
        剰余体経由で `HasEnoughRootsOfUnity (SplittingSystem p n) n`
        (**`rootsOfUnityEquivResidue_of_not_dvd` で `𝒪` 自身へ持ち上げ**)。
        非空虚性の決定打 = `natCard_rootsOfUnity_splittingSystem : Nat.card μ_n(𝒪) = n`。
      ⚠ 「分裂」を新クラスにはしない — 条件は mathlib の
      `HasEnoughRootsOfUnity (ResidueField 𝒪) n` そのものなので、下流は
      `[HasEnoughRootsOfUnity (ResidueField 𝒪) n]` と書く (ラッパー方針)。
- [x] **対角化可能性** = `OddOrder/Algebra/EigenspaceDecomposition.lean` (2026-08-03)。
      分裂した無平方零化多項式 `∏_{ζ ∈ s}(X - ζ)` で消える自己準同型は固有空間で張られる
      (`iSup_eigenspace_eq_top_of_aeval_prod_eq_zero`、証明 = Lagrange 補間)。
      系: `A^m = 1` + 原始 `m` 乗根 ⟹ 分解 + 内部直和 + `∑_ζ dim V_ζ = dim V`。
      ⚠ mathlib の `IsSemisimple.iSup_eigenspace_eq_top` は `IsAlgClosed` 前提で**使えない**
      (modular では係数体は「ちょうど足りる有限体」なので代数閉にできない)。
- [x] **Brauer 指標** = `.../Modular/BrauerCharacter.lean` (2026-08-03)。
      `rootLift n : k → 𝒪` (全域関数化した持ち上げ、`Finset k` 上の和で使うため) と
      `brauerCharacter n ρ g = ∑_{ζ ∈ μ_n(k)} dim_k V_ζ · ζ̂`。
      `brauerCharacter_one` (= `dim_k V`) / `brauerCharacter_conj` (類関数) /
      **`residue_brauerCharacter` (剰余 = 通常のトレース)** が定義の正当性を固定する。
- [ ] `|IBr G| = p`-regular 類の個数 (次の段。既約 `kG`-加群の枚数を数える必要があり、
      `kG` の Jacobson radical / 半単純商の議論が要る)

以降 (別 issue に分割予定): 分解行列 `D` / Cartan 行列 `C = DᵀD` / block / Brauer 対応 /
2nd・3rd main theorem / Z\*-定理 → Q₈ bridge。

## PDF gate について

0147 の pickup 手順 step 1「Navarro Ch.5–7 を精読して Ch.1–4 の slice を絞る」は **PDF 待ち**
(ユーザー購入手配中)。ただし step 2 の**最初の段 (p-modular system / Brauer 指標) は
標準的な内容で slice 絞りに依存しない**ので、そこから着手する。
PDF が入り次第 Ch.5–7 を読んで以降の段の範囲を確定する。

## 完了条件

上記チェックボックスが全て埋まり、**具体構成による instance が存在**し、
build green + AxiomsCheck 登録 + sorry 非退行。

## 参照

- 親: [0147](0147-q8-modular-char-theory-frozen.md)
- spec: `notes/meta/q8_modular_char_theory_frozen_project.md`
- 前提調査: `notes/peterfalvi/appendixC_prop1_q8_brauer_suzuki.md`
