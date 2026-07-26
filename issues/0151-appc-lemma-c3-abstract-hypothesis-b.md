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

### 配置 (import DAG) の実測 — step 1 の置き場所は確定

* C.3 chain の入口 `S16_CoreLemmas` の BG 側 import は **`OddOrder.BG.AppC_NormSet` だけ**。
* chain が使う `fieldNormalizer*` は全部そこから作れる:
  - `fieldNormalizerPrimeLine hyp` = `normOneFrobeniusSubspaceKernel p q (span (ZMod p) {1})`
    = 今日新設した `AppC.primeLine p q` と**同一式**。
  - `fieldNormalizerKernel` / `fieldNormalizerComplement` = `inl.range` / `inr.range` を**直書き**
    (`AppC_NormOneInduce` の `normOneFrobeniusKernel`/`normOneFrobeniusComplement` と同一式の重複)。
* ⟹ slim record は **`OddOrder.BG.AppC_NormSet` だけを import する新 leaf**
  (`OddOrder/BG/AppC_HypothesisB.lean`) に置ける。`HypothesisBAbstract` と `primeLine` は
  現在 `AppC_FinalContradiction.lean` (= chain の**下流**) に在るので、そこへ**移設**する。
* 同時に `normOneFrobeniusKernel` / `normOneFrobeniusComplement` を
  `AppC_NormOneInduce` (Peterfalvi S08 を import する下流 leaf) から
  `AppC_NormSetBasic` へ**上流移動**し、`fieldNormalizerKernel`/`fieldNormalizerComplement` の
  直書き重複を解消する (3 行 def、依存追加なし)。

### step 1 の作業単位 (次 iteration)

1. `normOneFrobeniusKernel` / `normOneFrobeniusComplement` を `AppC_NormSetBasic` へ移動。
2. 新 leaf `AppC_HypothesisB.lean` を作り、`primeLine` + `HypothesisBAbstract` を移設
   (`AppC_FinalContradiction` / `AppC_SL2Example` は import 追加のみ)。`OddOrder.lean` へ配線。
3. `fieldNormalizerKernel`/`fieldNormalizerComplement`/`fieldNormalizerPrimeLine` を
   移動先の名前へ差し替え (statement 不変)。

---

## ✅ step 1 完了 (2026-07-26)

1. `NormSet.normOneFrobeniusKernel` / `normOneFrobeniusComplement` を
   `AppC_NormOneInduce.lean` (Peterfalvi S08 を import する下流 leaf) から
   `AppC_NormSetBasic.lean` へ**上流移動**。
2. 新 leaf **`OddOrder/BG/AppC_HypothesisB.lean`** を作成 (`AppC_NormSet` のみ import)。
   `conditionA` / `primeLine` / `HypothesisBAbstract` を `AppC_FinalContradiction.lean`
   (= C.3 chain の下流) から移設。`OddOrder.lean` に配線済。
3. `S16.fieldNormalizer{Kernel,Complement,PrimeLine}` の本体を移動先の名前へ差し替え
   (`inl.range`/`inr.range`/span 式の直書き重複を解消)。unfold に依存していた 8 箇所
   (`S16_CoreLemmas` 5、`S16_NonExistenceG/SubgroupL` 3) に新名を simp/rw 引数として追加。
4. **重複していた第 3 の (B) encoding を削除**: `AppC.HypothesisB` +
   `hypothesisB{FrobeniusGroup,PrimeLine,Complement}` は consumer ゼロで、
   フィールドが `S16.FieldNormalizerData` と完全に重複していた (S16 版は `fieldNormalizer*`
   を使うので、`hypothesisB*` は同じ式の別名にすぎない)。削除して module docstring に
   「(B) の抽象形 = `HypothesisBAbstract`、S16 instance = `S16.FieldNormalizerData`」を明記。

⟹ **これで C.3 chain の入口 (`S16_CoreLemmas`) から `AppC.primeLine` /
`NormSet.normOneFrobenius{Kernel,Complement}` が見えており、step 2 の機械置換の
置き換え先が全部揃った。**

### step 2 の残り (次 iteration)

`FieldNormalizerData` を `(p, q, G)` で index された slim record に置き換える。実測済の
置換対応:

| 現 | 置換先 |
|---|---|
| `hyp.base.p`, `hyp.base.q` | section variable `p`, `q` |
| `hyp.base.p_prime` | `[Fact p.Prime]` |
| `hyp.base.q_prime` | `(hq : q.Prime)` |
| `hyp.base.P` | `(NormSet.normOneFrobeniusKernel p q).map data.sigma` |
| `hyp.base.U` | `(NormSet.normOneFrobeniusComplement p q).map data.sigma` |
| `hyp.base.W2` | `(primeLine p q).map data.sigma` |
| `hyp.base.Q` | `data.Q` |
| `data.Q_elementaryAbelian.comm` | `data.Q_commutative` |
| `fieldNormalizerFrobeniusGroup hyp` | `NormSet.normOneFrobeniusGroup p q` |
| `fieldNormalizerKernel/Complement/PrimeLine hyp` | 上流の同名 (step 1 で差し替え済) |

## ✅ step 2a 完了 — 忠実性ブリッジ (2026-07-26)

`S16.FieldNormalizerData.toHypothesisBAbstract` を追加。**Peterfalvi §16 の field-normalizer
構成が書籍 p. 145 の抽象仮説 (B) の instance になっている**ことの証明:

| (B) の要求 | S16 側の供給元 |
|---|---|
| `σ : H → G` 単射 | `data.sigma` / `data.sigma_injective` |
| `Q` 有限 | `[Finite G]` |
| `Q` 可換 | `data.Q_elementaryAbelian.comm` |
| `Q` は `p'`-群 | `|Q| = q^n` (`IsPGroup.exists_card_eq`) + `q < p` ⟹ `p ≠ q` |
| `y ∈ Q` | `data.y` / `data.y_mem_Q` |
| `σ(P₀)` が `Q` を正規化 | `sigma_P0_eq_W2` ▸ `W2_normalizes_Q` |
| `σ(P₀)^y` が `σ(U)` を正規化 | `sigma_P0_eq_W2` + `sigma_U_eq_U` ▸ `W2_conj_y_normalizes_U` |

⟹ **`HypothesisBAbstract` が「spine が実際に作る配置の忠実な抽象化」であることが機械検証された**
(別形の仮説にすり替わっていない = [[scaffold-sorry-free-not-done]] の carrier 構成可能性チェック)。
これで step 2b (chain 本体の再パラメータ化) を進めても、抽象側が空虚でないことが保証される。

### step 2b (次)

chain 本体を `data : FieldNormalizerData hyp` から `data : HypothesisBAbstract p q G`
(+ `hq : q.Prime` + `hA : conditionA p q`) へ機械置換する。上の置換表に従い、
`HypothesisBAbstract.{P, U, W2}` を σ の像として def 化してから file 単位で移行する。

## 🏗 step 2b の設計確定 (2026-07-26) — フィールド名を保存する再パラメータ化

当初は「chain を `HypothesisBAbstract` のフィールド名へ書き換える」つもりだったが、それだと
`data.W2_normalizes_Q` → `data.primeLine_normalizes_Q` のような**証明本体の全書き換え**が要る。
代わりに **`FieldNormalizerData` 自体を `(p, q, G)` で index し直し、フィールド名を全部保存する**
方が diff がはるかに小さい:

```lean
structure FieldNormalizerData (p q : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    extends OddOrder.BG.AppC.HypothesisBAbstract p q G where
  P : Subgroup G
  U : Subgroup G
  W2 : Subgroup G
  sigma_P_eq_P  : (NormSet.normOneFrobeniusKernel p q).map sigma = P
  sigma_U_eq_U  : (NormSet.normOneFrobeniusComplement p q).map sigma = U
  sigma_P0_eq_W2 : (primeLine p q).map sigma = W2
  q_prime : q.Prime
  cyclotomic_coprime : conditionA p q
```

* `extends` にすることで `data.sigma` / `data.Q` / `data.y` / `data.y_mem_Q` は**そのまま**動く。
* 追加フィールド `P`/`U`/`W2` は像に名前を付けるだけの packaging で、
  `HypothesisBAbstract → FieldNormalizerData` は **全域の構成** (P := 像、eq := `rfl`) ゆえ
  隠れた強化が無いことが型で保証される。
* `W2_normalizes_Q` / `W2_conj_y_normalizes_U` は `sigma_P0_eq_W2` / `sigma_U_eq_U` 経由で
  `primeLine_normalizes_Q` / `primeLine_conj_normalizes_U` から**導出**する (フィールドでなく補題に)。

### 残る置換 (証明本体はほぼ無傷)

| 現 | 置換先 | 出現行数 |
|---|---|---|
| `{hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)` | `{p q : ℕ} [Fact p.Prime] (data : FieldNormalizerData p q G)` | 208 (宣言) |
| `hyp.base.p` / `hyp.base.q` | `p` / `q` | — |
| `hyp.base.P/U/W2/Q` | `data.P/U/W2/Q` | — |
| `hyp.base.p_prime` / `hyp.base.q_prime` | `Fact.out` / `data.q_prime` | — |
| `fieldNormalizerXxx hyp` | `xxx p q` (step 1 で上流化済) | — |

`hyp.base.` を含む行数: CoreLemmas 313 / CoreBounds 222 / CoreSetup 148 /
NonExistenceGCore 75 / AppendixC3 72 / CoreSetupBasic 62 = **計 892 行**。
`FieldNormalizerData` 参照は 208 箇所。⟹ 当初見積の「3,900 行の書き換え」ではなく
**~900 行の機械置換**。

### chain の内部 import 順 (migration はこの順)

`S16_CoreLemmas` → `S16_CoreBounds` → `S16_AppendixC3` → `S16_CoreSetupBasic` →
`S16_CoreSetup` → `S16_NonExistenceGCore`

⚠ 各 file は C.3 以外の §16 材料とも混在しているので、**file 丸ごと移動ではなく
`FieldNormalizerData` を取る宣言だけを抜き出して BG 側へ移す**。移した分は S16 側から削除し、
S16 spine は `toHypothesisBAbstract` (step 2a) 経由で繋ぎ直す。

## 🧱 受け皿の完成 (2026-07-26)

`AppC_HypothesisB.lean` に step 2b の置換先を全部揃えた:

* `conditionA` / `primeLine` / `primeLineElement` / `primeLineGenerator` — `(p, q)`-level。
* `HypothesisBAbstract p q G` — 書籍 (B)。
* `FieldNormalizerData p q G` (`extends HypothesisBAbstract`) — (B)+(A) に `P`/`U`/`W₂` の
  名前を付けただけの packaging。`HypothesisBAbstract.toFieldNormalizerData` が全域構成
  (3 本の定義等式は `rfl`) なので強化でないことが型で保証される。
* `W2_normalizes_Q` / `W2_conj_y_normalizes_U` は導出補題として用意済 (chain の呼び名を保存)。

⚠ **S16 側の定義本体を BG の新名へ差し替えるのは無駄**と判明 (試して revert):
`fieldNormalizerPrimeLineElement` 等を BG 名へ向けると、それを `dsimp`/`rw` で展開していた
10 箇所が壊れる。しかし step 2b では S16 側の定義自体が消えて **呼び出し側が**
`AppC.primeLineElement p q c` に置換されるので、S16 の body を先に差し替える必要は無い。
必要なのは「BG 側に名前が存在すること」だけで、それは完了した。
(subgroup 3 本 = `fieldNormalizer{Kernel,Complement,PrimeLine}` は step 1 で差し替え済。
そちらは unfold 依存が 8 箇所で済んだので実施した。)

### step 2b 実行の残り

`S16_CoreLemmas` の 630--1265 行 (= `FieldNormalizerData` namespace、31 宣言) から始めて
chain の import 順に、`{hyp} (data : FieldNormalizerData hyp)` を
`{p q} [Fact p.Prime] (data : AppC.FieldNormalizerData p q G)` へ機械置換し、
宣言を BG 側 leaf へ移す。S16 spine は `toHypothesisBAbstract` +
`HypothesisBAbstract.toFieldNormalizerData` 経由で繋ぎ直す。
