---
id: 151
slug: appc-lemma-c3-abstract-hypothesis-b
title: "BG Lemma C.3 を抽象 Hypothesis (B) から導く (現状 S16 経由のみ)"
created: 2026-07-26
---

# BG Lemma C.3 を抽象 Hypothesis (B) から導く (現状 S16 経由のみ)

## 背景

2026-07-26 に BG App.C の `p, q`-抽象化が二段階進んだ:

1. `theoremC_abstract` (commit `62e84cf0f`) — Theorem C の結論 `p ≤ q` を、S16 設定なしに
   「条件 (A) + 生成関係 `hrel : ∀ a ∈ E, N(2a − 1) = 1`」から導く形。
2. `HypothesisBAbstract` + `hypothesisBAbstract_sl2` (本 issue の直前の commit) — 書籍の
   Hypothesis (B) を `p, q, G` で抽象化した structure と、**Remark (II)** の
   `p = 2, G = SL(2, 2^q)` witness。

この 2 つの間に残っている穴が本 issue:

> **抽象 Hypothesis (B) ⟹ `hrel`** (= BG Lemma C.3 の群論的内容)

現状この含意は **Peterfalvi §16 の設定を通してのみ**存在する
(`S16.FieldNormalizerData.appC_normSet_generator_relation`、sorry-free で証明済)。
`OddOrder/BG/AppC_FinalContradiction.lean` の `lemmaC3_inverse_closed` はその S16 版を
呼ぶだけなので、抽象 `HypothesisBAbstract` からは Theorem C を回せない。

これは**書籍の gap ではなく repo 側の特殊化債務** ([[repo-stronger-hypothesis-is-specialization-not-gap]])。
書籍 Lemma C.3 は Hypothesis (B) だけから Step 1–4 を回している (BG pp. 148–152)。

## やること

- [ ] `HypothesisBAbstract p q G` から Lemma C.3 の Step 1–4 を再構成し、
      `hrel : ∀ a ∈ NormSet.normSetE p q, NormSet.normN p q (2 * a - 1) = 1` を導く。
      素材は既に `p, q` で抽象な形で在る:
      - Step 1 = `NormSet.normOneFrobenius_exists_inr_primeLine_inr` (`AppC_NormSetBasic.lean`)
      - Step 2 = `NormSet.normOneFrobenius_generatorRelation_step2_primeLine` (同)
      - Step 3 = `NormSet.normOneFrobeniusSubspaceGroup_eq_top_of_ne_bot` (同)
      - Step 4 尾部 = `NormSet.normOneFrobenius_normN_two_mul_sub_one_of_first_k_three_decomposition`,
        `NormSet.inv_mem_of_twistedInv_step` (同)
      S16 版の組み立ては `OddOrder/Peterfalvi/S16_CoreBounds.lean` /
      `S16_CoreSetup.lean` / `S16_NonExistenceGCore.lean` にある — どこで `S16.Hypothesis`
      固有の情報 (Q の elementary abelian 性、`hyp.base` の各種構造) を使っているかを
      trace して、抽象 (B) の 4 条件 (σ 単射 / Q 有限可換 p'-群 / σ(P₀) が Q を正規化 /
      σ(P₀)^y が σ(U) を正規化) だけに落とす。
- [ ] 落ちたら `theoremC_of_hypothesisBAbstract : HypothesisBAbstract p q G → conditionA p q → p ≤ q`
      を書き、既存の S16 経路 (`theoremC`) をその特殊化として通す
      (薄いラッパーは作らない — `theoremC` の中身を差し替える)。
- [ ] `AxiomsCheck` に追加。

## 完了条件

`HypothesisBAbstract p q G` + `conditionA p q` から `p ≤ q` が sorry-free で出て、
`OddOrder.BG.AppC.final_contradiction` が非退行 (build green + AxiomsCheck OK)。

## 参照

- 書籍: BG App.C §3 Lemma C.3 (pp. 148–152)、Hypothesis (B) は p. 145
- `OddOrder/BG/AppC_FinalContradiction.lean` (`HypothesisBAbstract`, `theoremC_abstract`,
  `lemmaC3_inverse_closed`)
- `OddOrder/BG/AppC_SL2Example.lean` (Remark (II) witness)
- `OddOrder/BG/AppC_NormSetBasic.lean` (Step 1–4 の `p, q`-抽象な部品)
- `OddOrder/Peterfalvi/S16_NonExistenceGCore.lean` (現行の S16 経由の組み立て)
- survey: `notes/meta/three_books_full_survey_2026_07_16.md` 「2026-07-26 終了時点の frontier」

---

## 📐 2026-07-26 実測 — 依存の全数調査 (着手前)

C.3 chain (`S16_AppendixC3` / `S16_CoreSetupBasic` / `S16_CoreSetup` / `S16_CoreBounds` /
`S16_NonExistenceGCore`、合計 ~3,900 行) が `hyp : S16.Hypothesis` から**実際に何を使っているか**
を全数 grep で確定した。結論: **抽象 (B) を超える依存は無い**。

### `hyp.base` の使用フィールド (全数)

| フィールド | 出現数 |
|---|---|
| `p` | 233 |
| `U` | 108 |
| `P` | 71 |
| `q` | 52 |
| `Q` | 22 |
| `W2` | 17 |
| `p_prime` | 14 |
| `q_prime` | 4 |

**これだけ**。`S15.Hypothesis` の他の ~40 フィールド (S, T, W1, W, V, C, D, 極大性, type
predicates, (8.8) case-B, `q < p`, `p_odd`/`q_odd`, …) は**一切使われていない**。
`hG : IsMinimalSimpleOdd G` も chain のどの補題も取らない。使う instance は `[Finite G]` のみ。

### `hyp` を丸ごと渡す先 (全数)

`fieldNormalizerFrobeniusGroup` / `fieldNormalizerPrimeLineElement` /
`fieldNormalizerNormOneUnits` / `fieldNormalizerPrimeLineGenerator` /
`fieldNormalizerFrobeniusHom` / `exists_fieldNormalizerNormOneUnit_ne_one` /
`appCNormSetGeneratorRelation` / `appCNormSetTwistedNormOneStep` /
`FieldNormalizerData` — **すべて `(p, q)` だけの関数**であり、`hyp` は `hyp.base.p`,
`hyp.base.q` を渡すための syntactic な容器にすぎない。

### `FieldNormalizerData` の非-(B) フィールド

* `sigma_P_eq_P` — 使用 2 箇所 (`S16_AppendixC3:338,341`)。抽象版では `P := σ(P)` を
  定義にすれば `rfl` になる (同様に `sigma_U_eq_U` / `sigma_P0_eq_W2`)。
* `Q_elementaryAbelian` — **使用 1 箇所のみ** (`S16_NonExistenceGCore:213`)、しかも
  `.comm` (可換性) を取り出すだけ。⟹ **書籍の「finite abelian `p'`-subgroup」で足りる**。
  elementary abelian への強化は不要 = `HypothesisBAbstract.Q_commutative` で置換可能。
* `cyclotomic_coprime` — 条件 (A)。書籍でも Theorem C の別仮説なので分離して渡す。
* `P1 := MulAut.conj y • W2` (`S16_CoreBounds:73`)、`t := MulAut.conj y s` — どちらも
  抽象 (B) の `MulAut.conj y • σ(P₀)` そのもの。

### ⟹ 実施プラン (再パラメータ化、証明の書き直しではない)

1. `p, q, G` で index された slim record を新設 (実質 `HypothesisBAbstract` + 条件 (A))。
   ambient な `P`/`U`/`W2` は σ の像として**定義**し、現 `sigma_*_eq_*` フィールドを消す。
2. C.3 chain を `hyp.base.X` → slim record の対応フィールドへ**機械置換**
   ([[lean-systematic-refactor-script]] の Python 一括方式; 連鎖 Edit は空白を潰すので不可)。
   `hyp.base.p`/`hyp.base.q` → `p`/`q` (section variable)。
3. `S16.FieldNormalizerData hyp` → slim record への adapter を書き、既存 S16 経路
   (`theoremC`, `final_contradiction`) を無変更で通す (statement 不変)。
4. `hypothesisBAbstract_sl2` (Remark (II)) から `hrel` が出るようになるので、
   `theoremC_abstract` と繋いで `p ≤ q` を回せることを確認 (p=2 なので結論は自明だが、
   経路が閉じていることの検証になる)。
5. AxiomsCheck に追加。フルビルド + `--strict` gate。

⚠ 規模: ~3,900 行の機械置換 + adapter。**multi-session だがコストは着手判断基準でない**
([[feedback-cost-scope-not-a-criterion]])。分割 commit で進める。
