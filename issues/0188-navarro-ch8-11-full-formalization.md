---
id: 188
slug: navarro-ch8-11-full-formalization
title: "Navarro Ch.8-11 の完全形式化 (Brauer 指標 Clifford 理論 / block と正規部分群 / p-可解群 / 位数 p の Sylow)"
created: 2026-08-21
---

# Navarro Ch.8-11 の完全形式化

**ユーザー裁定 (2026-08-21)**: 「Navarro の残りをターゲットにします。書籍に faithful に
したいですが、**より一般的な形で定理を述べられるのであればそうしてください**。」

⟹ Navarro 1998 *Characters and Blocks of Finite Groups* (LMS LNS 250) の posture が
「行間参照のみ・独立の形式化対象ではない」から **形式化対象**へ変わる (CLAUDE.md 更新済)。

## スコープ — 番号付き結果 100 件

`references/navarro/characters-and-blocks.pdftotext.txt` を機械 census した実測値
(OCR が `T H E O R E M` と字間を空けるので、字間許容の正規表現で拾う)。**欠番なし**。

| 章 | 題 | 書籍 pp. | 件数 | 内容 |
|---|---|---|---|---|
| **8** | Brauer Characters as Characters | 150–191 | **34** | Brauer 指標の誘導 (Brauer–Nesbitt)、Clifford 理論・Clifford 対応、Green/Dade の拡張、射影表現と factor set、modular character triple、Swan、Passman、正規 q-補群への応用 |
| **9** | Blocks and Normal Subgroups | 192–221 | **29** | block の covering、Passman の判定、拡張第一主定理、Fong–Reynolds、Fong の高さ 0 定理、Reynolds、Knörr、Harris–Knörr、Alperin–Broué |
| **10** | Characters and Blocks in `p`-Solvable Groups | 222–242 | **23** | **Fong–Swan**、Wolf、Isaacs の `p`-rational lift、Huppert、Fong 指標と次元公式、Fong の block 定理、高さの評価、Kiyota–Okuyama |
| **11** | Groups with Sylow `p`-Subgroups of Order `p` | 243–272 | **14** | 位数 `p` の Sylow をもつ群の `p`-block の完全記述 (Brauer tree の原型)、`M₁₁` の指標表、`ℚ_n` の整数論的準備 |

依存 (書籍 preface より): **Ch.8 → Ch.9 → Ch.10**、Ch.11 は Ch.8/9 の上。
⟹ 着手順は CLAUDE.md の「上流優先 + 文書順」でそのまま **8 → 9 → 10 → 11**。

## 現状 — 100 件すべて未形式化 (実測)

- Lean docstring の `Navarro (N.M)` ラベル分布: Ch.2=51 / Ch.3=64 / Ch.4=78 / Ch.5=147 /
  Ch.6=65 / Ch.7=148、**Ch.8–11 = 0**。
- 番号 grep だけでは証拠にならない ([[textbook-coverage-audit-failure-modes]]) ので概念名でも
  確認: `fongSwan` / `brauerNesbitt` / `cliffordCorrespondence` / `swan_theorem` /
  `modularCharacterTriple` / `projectiveRepresentation` — 環境ダンプ (352,597 定数) に**全て 0 件**。
- ⚠ **`OddOrder/GroupTheory/RepresentationTheory/FongSwan.lean` は Navarro (10.1) ではない** —
  BG Lemma 2.3 (可解群の絶対既約加群で `dim ∣ |G|`) で、ファイル自身が
  「**not** the modular Fong–Swan theorem via Brauer lifting」と明記している。
  (10.1) を実装するときは名前衝突を避けること。

## 土台 (既存インフラ)

Ch.1–7 の形式化で `OddOrder/GroupTheory/RepresentationTheory/Modular/**` に **151 leaf**。
Ch.8 が直接乗るもの:

- `Modular.brauerCharacter` (`BrauerCharacter.lean`) — `p`-modular system `𝒪` 上の Brauer 指標
- `Modular.irreducibleBrauerCharacter` (`IrreducibleBrauerCharacter.lean`) — `IBr(G)` は
  Wedderburn 分解 `π` の添字 `ι` + `blockRepresentation π i` で表現される
- block 側 (`blockOfIrr` / `inducedBlock` / `blockDefect` / `cartanMatrix` /
  `decompositionNumber` / `generalizedDecompositionNumber` …)

## 方針

- **faithful を既定、一般化できるならする** (ユーザー裁定)。CLAUDE.md の特殊化債務ポリシー
  ([[feedback-generalize-specialized-fully]]) と同じ向き。書籍が `F` を代数閉と仮定していても
  分裂体で十分なら分裂体で述べる、`p`-solvable を仮定していても不要なら落とす、等。
  一般化した場合は docstring に**書籍の主張との差**を明記する。
- 番号は docstring の `**Navarro (8.2)**` 形式のみ (識別子には入れない)。
- leaf は新規ディレクトリ `OddOrder/GroupTheory/RepresentationTheory/Modular/` 配下に
  トピック別で切り、**同じ commit で `OddOrder.lean` に配線**する。
- 各 leaf は `bin/check-doc-names` / `bin/check-links` green を維持 ([issue 0187](closed/0187-corpus-doc-hygiene-audit.md))。

## やること

### Ch.8 Brauer Characters as Characters (34)

- [x] **(8.1) DEF 誘導 `α^G`** — `ClassFunction.induceCoset` (`InducedCosetSum.lean`) で
      **除算なしの左剰余類和**として定義。書籍より一般 (任意の可換環 `k`; `|H|` の可逆性・
      体・標数 0 のいずれも不要) — Brauer 指標が値をとる `p`-modular system の付値環 `𝒪` では
      `p ∣ |H|` のとき `|H|` が可逆でないので、既存の正規化済 `ClassFunction.induce` は使えない。
      well-definedness (`induceTerm_mul_mem`)・類関数性・正規化ブリッジ
      (`card_filter_mk_eq` / `card_smul_induceCoset` / `induceCoset_eq_induce`) まで完了。
      ⟹ **(8.1) 完了**。
- [~] (8.2) Brauer–Nesbitt / (8.3) Cor — 誘導表現まわりの土台が landing 済。
      mathlib の `Representation.ind` は coinvariants `(k[H] ⊗ A)_G` で固有値計算に
      不向きなので、coinduced の具体形 `{f : G → W | f(hx) = ρ(h) f(x)}` に右移動作用
      `(g·f)(x) = f(xg)` を入れたモデルを採用 (選択を含まないので `Representation`
      構造が clean)。

      **完了分** (`InducedRepresentation.lean`):
      - `indSubmodule` / `indRep` — 誘導表現の構成
      - `indCoordEquiv` — 座標同型 `≃ₗ[k] (H \ G) → W` (`coordShift` = 右剰余類代表に
        対する `H`-成分)。これで `Module.finrank` が届く
      - `finrank_indSubmodule` — 次数公式 `[G : H] * finrank W`
        (書籍の `θ^G(1) = [G:H]·θ(1)` の加群レベルの出所)
      - `cosetRightMul` / `cosetRightMul_mk_eq_iff` — 右剰余類への `g` の右移動と、
        固定判定 `⟦xg⟧ = ⟦x⟧ ↔ x g x⁻¹ ∈ H` (`induceCoset` の項を切り出す条件)
      - `indSupport` / `indSupport_invariant` — `g`-安定な余類集合が切り出す `⟨g⟩`-部分加群
      - `indRep_apply_of_conj_mem` — **固定余類の寄与** `(g·f)(x) = ρ(x g x⁻¹) (f x)`

      **完了分** (`OddOrder/Algebra/EigenvalueScaling.lean`) — 消滅側の線形代数核:
      可逆な `S` が `S (T v) = ω • T (S v)` で `T` を絡めるなら、`S` は `ζ`-固有空間を
      `ω⁻¹ζ`-固有空間の上へ同型に写す (`map_eigenspace_of_intertwine`)、よって重複度が
      `ω` 倍で不変 (`finrank_eigenspace_eq_of_intertwine`)。体上の任意の作用素についての
      主張で、この応用に固有の仮定は無い。

      **残 (次の着手点、この順)**:
      1. `rootLift` の乗法性 `rootLift n (ω*ζ) = rootLift n ω * rootLift n ζ`
         (現状 `rootLift_mul` は無い。`rootsOfUnityEquivResidue` の逆写像なので成立するはず)
      2. **消滅補題**: 重複度が `ω` 倍で不変 (`ω ∈ μ_n`, `ω ≠ 1`) なら
         `brauerCharacter n ρ g = 0`。1 と `finrank_eigenspace_eq_of_intertwine` から
         `ω̂ · b = b` を経由し、`𝒪` が整域・`ω̂ ≠ 1` で結論
      3. 長さ `ℓ` の軌道に対する**ブロック傾斜作用素** `S` の構成 (第 `i` ブロックを
         `ω^i` 倍) と、`indRep g` を `ω` 倍に絡めることの検証
      4. 軌道分解 (`indSupport` の内部直和) + `brauerCharacter_quotient_add_subrepresentation`
         の加法性で組み立て、`induceCoset` と一致させる

      証明の骨格: `g` を `p`-正則とし `Ind ↓⟨g⟩` を `⟨g⟩` の `H \ G` 上の軌道で分解。
      固定余類 `x` (`x g x⁻¹ ∈ H`) は `α(x g x⁻¹)` を寄与し、長さ `ℓ > 1` の軌道は
      重複度が `ω` 倍で不変になるので 0。
- [ ] (8.4) Nakayama / (8.5) Clifford / (8.6) / (8.7) (8.8) Cor
- [ ] (8.9) Clifford 対応 / (8.10)
- [ ] (8.11) Green / (8.12) 巡回商 / (8.13) Dade (coprime 拡張)
- [ ] (8.14)–(8.18) 射影表現・factor set・Jacobson density
- [ ] (8.19) (8.20) Cor / (8.21) 直積 / (8.22) Swan / (8.23) (8.24)
- [ ] (8.25)–(8.28) modular character triple
- [ ] (8.29) 素点ごとの拡張判定 / (8.30) Dade
- [ ] (8.31) (8.32) Passman / (8.33) (8.34) 正規 `q`-補群

### Ch.9 Blocks and Normal Subgroups (29)

- [ ] (9.1)–(9.6) covering の基本 + Passman 判定
- [ ] (9.7) 拡張第一主定理 / (9.8)–(9.11)
- [ ] (9.12) (9.13) Laradji / (9.14) Fong–Reynolds
- [ ] (9.15)–(9.18) Fong (高さ 0)
- [ ] (9.19)–(9.22) regular block / (9.23) Reynolds
- [ ] (9.24)–(9.26) Knörr / (9.27) (9.28) Harris–Knörr / (9.29) Alperin–Broué

### Ch.10 Characters and Blocks in `p`-Solvable Groups (23)

- [ ] (10.1) **Fong–Swan** / (10.2) (10.3) Wolf
- [ ] (10.4) (10.5) Cor / (10.6) (10.7) (10.8) Isaacs (`p`-rational)
- [ ] (10.9)–(10.12) Huppert / (10.13) (10.14) Fong 指標・次元公式
- [ ] (10.15)–(10.19) Fong 指標の特徴づけ
- [ ] (10.20) Fong の block 定理 / (10.21) (10.22) 高さ / (10.23) Kiyota–Okuyama

### Ch.11 Groups with Sylow `p`-Subgroups of Order `p` (14)

- [ ] (11.1) (11.2) `M₁₁` / (11.3) `p = 2` / (11.4) Brauer
- [ ] (11.5)–(11.10) `ℚ_n` の素イデアル (Notation (11.6) 込み)
- [ ] (11.11) / (11.12) Notation / (11.13) 主定理 / (11.14) Cor

## 完了条件

- Ch.8–11 の 100 件が形式化され、docstring に `**Navarro (N.M)**` ラベルが付く
- `lake build OddOrder` green / 非 sorry 警告 0 / AxiomsCheck OK
- 一般化した箇所は書籍との差が docstring に明記されている

## 参照

- `references/navarro/characters-and-blocks.pdf` (⚠ **PDF ページ = 書籍ページ + 10**、数式は OCR 崩れ大 ⟹ 式の確定はページ画像で)
- 切り出したページ画像は `references/navarro/pages/` に残す (2026-07-26 規約)
- 直前の Navarro 成果: [0147](closed/0147-q8-modular-char-theory-frozen.md) (Q₈ Brauer–Suzuki) / [0186](closed/0186-glauberman-zstar-theorem.md) (Z\*-定理)
