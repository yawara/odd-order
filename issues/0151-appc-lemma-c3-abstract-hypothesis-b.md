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

## ⚠ step 2b は file 単位で刻めない (2026-07-26、設計上の制約)

先に書いた「chain の import 順に file 単位で移行する」は**実行不能**と判明した。理由:

* `S16.FieldNormalizerData hyp` を `AppC.FieldNormalizerData hyp.base.p hyp.base.q G` の
  `abbrev` にすれば、下流の `data.s` / `data.W2_le_P` 等の**ドット記法は型の head symbol で
  解決される**ので、移行済み宣言をそのまま拾える (ここまでは OK)。
* しかし移行した補題の**statement は `data.P` / `data.U` / `data.W2` / `data.Q` で書かれる**のに、
  未移行の下流は `hyp.base.P` 等で書かれている。構成サイトで `P := hyp.base.P` と取るので
  両者は**等しいが定義的には等しくない** (structure field ゆえ opaque)。
* ⟹ 移行済みと未移行が混在した瞬間、境界で `data.P = hyp.base.P` の書き換えが必要になり、
  218 箇所 (`P` 71 + `U` 108 + `W2` 17 + `Q` 22) に橋渡しが要る。

⟹ **step 2b は 6 file を 1 パスで置換する all-or-nothing**。~900 行の機械置換 (Python 一括、
[[lean-systematic-refactor-script]]) を 1 commit で行い、build error で収束させる。
revert は `git checkout <6 files>` で即座なので、リスクは制御可能。

### 1 パスで行う置換 (最終形)

1. `S16_CoreLemmas` の `structure FieldNormalizerData` を削除し、
   `abbrev FieldNormalizerData (hyp) := AppC.FieldNormalizerData hyp.base.p hyp.base.q G` に。
2. 6 file 全体で `hyp.base.P/U/W2/Q` → `data.P/U/W2/Q`、
   `hyp.base.p/q` → `p`/`q`、`hyp.base.p_prime` → `Fact.out`、`hyp.base.q_prime` → `data.q_prime`。
3. `fieldNormalizerXxx hyp` → `AppC.xxx p q` (BG 側に全部存在済)。
4. 宣言ヘッダ `{hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)` →
   `{p q : ℕ} [Fact p.Prime] {G : Type*} [Group G] (data : AppC.FieldNormalizerData p q G)`。
5. 構成サイト (`S16_NonExistenceG/SubgroupL.lean`) で `Q_elementaryAbelian` を
   `Q_finite`/`Q_commutative`/`Q_pPrime` に差し替え (導出は step 2a の
   `toHypothesisBAbstract` で実証済)。
6. `data` を取らない `hyp`-only helper (7 件) も `(p, q)` 化。

## ❗ 実測の訂正 (2026-07-26) — 最初の census は 6 file 中 4 file しか見ていなかった

上の「`hyp.base` の使用フィールドは 8 つだけ」は **`S16_CoreLemmas` と `S16_CoreBounds` を
含めずに数えていた**。6 file 全部の census:

| フィールド | 出現数 | 抽象 (B) から出るか |
|---|---|---|
| `p` / `q` | 541 / 206 | パラメータ |
| `U` / `P` / `Q` / `W2` | 194 / 146 / 88 / 76 | `data` のフィールド |
| `p_prime` / `q_prime` | 94 / 30 | instance / フィールド |
| **`p_eq_card_W2`** | **12** | ⭕ 導出可 — `P₀ ≅ 𝔽_p` かつ σ 単射ゆえ `|σ(P₀)| = p` |
| **`p_odd` / `q_odd` / `three_le_q` / `p_ne_two`** | **7 / 4 / 3 / 1** | ⭕ 書籍 Remark (V) の還元 (条件 (A) の下で p, q は奇と仮定してよい = `le_of_conditionA_of_not_odd` で形式化済) |
| `m` / `m_gt_49_hundredths_...` | 1 / 1 | ❓ §14 の数値パラメータ。`S16_CoreLemmas` の C.3 **以外**の部分 (要確認) |

⟹ 「抽象 (B) を超える依存は無い」は**言い過ぎだった**。正しくは:
**追加依存は 3 種で、いずれも (A)+(B)+「p,q 奇」から導出可能** (= 書籍が実際に使っている仮定):
1. `|W₂| = p` — σ の単射性から出す小補題を書く。
2. 奇性 — 書籍 Remark (V) の還元を使う (repo に `le_of_conditionA_of_not_odd` として在る)。
3. `m` 系 2 箇所 — C.3 chain 外かどうか確認する。

## 🧪 step 2b 試行の結果 (revert 済、知見のみ保持)

1 パス置換を実際に試した:
* `hyp.base.{P,U,W2,Q}` → `data.{P,U,W2,Q}` は **490 箇所**、
  「`data` binder を持たない宣言でこれらを使うものはゼロ」を script で確認済ゆえ安全。
* `S16.FieldNormalizerData` を BG record の `abbrev` にすると
  **`Fact hyp.base.p.Prime` が statement 側で合成できず 103 error**。
  `instance factHypothesisPPrime (hyp) : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩` を
  足すと **12 error まで落ちる** — これが正しい足場。
* 残 12 の内訳: (a) 孤立 docstring 1、(b) `(_data : ...)` の underscore binder 1、
  (c) `hyp.base.p_eq_card_W2` を使う rw が `data.W2` と噛み合わない 5〜6 箇所
  (= 上の追加依存 1 番)、(d) motive not type correct 1。

⟹ **次の試行では `instance factHypothesisPPrime` を最初に置き、`|W₂| = p` の小補題を
先に用意してから 1 パス置換する**。この 2 点で残 error はほぼ消える見込み。

## 🔬 step 2b 第 2 試行 (2026-07-26) — 数学的な障害はゼロと確定

`instance factHypothesisPPrime` を **`Hypothesis` の直後**に置く (ファイル末尾では手遅れ) のが
正しい足場と判明し、`S16_CoreLemmas` は **error 0** まで到達した (残りは long-line 警告のみ)。
続く `S16_CoreBounds` で残っていた `Q_elementaryAbelian` 依存 5 箇所を精査した結果:

| 使用箇所 | 必要なもの | 書籍 (B) で足りるか |
|---|---|---|
| `Q_mul_comm` | `.comm` | ⭕ `Q_commutative` (mathlib `mul_comm_of_mem_isMulCommutative`) |
| `W2_card_coprime_Q_card` | `|Q| = q^k` | ⭕ `Q_pPrime` + `|W₂| = p` + p 素数 (`Nat.Prime.coprime_iff_not_dvd`) |
| `Q_pow_q_eq_one` → `P_inf_Q_eq_bot` | `x^q = 1` | ⭕ **不要**。両 consumer は「`Q` の `p`-元は自明」しか使っておらず、これは `Q_pPrime` から出る |
| `Q_pow_q_eq_one` → `W2_inf_Q_eq_bot` | 同上 | ⭕ 同上 |

⟹ **`Q` が elementary abelian である必要はどこにも無い**。書籍どおり「有限可換 `p'`-群」で足りる。
`AppC.FieldNormalizerData.eq_one_of_mem_Q_of_pow_p_eq_one` (Lagrange + `Q_pPrime`) を BG 側に
追加して commit 済 — これが `Q_pow_q_eq_one` の唯一の役割を代替する。

⟹ **step 2b に残るのは機械作業だけ** (数学的障害はゼロ):
1. `instance factHypothesisPPrime` を `Hypothesis` 直後に置く。
2. `hyp.base.{P,U,W2,Q}` → `data.{P,U,W2,Q}` (490 箇所)。
3. `hyp.base.p_eq_card_W2` → `data.card_W2` (rewrite 方向に注意: `card_W2 : |W₂| = p`)。
4. `fieldNormalizer{Kernel,Complement,PrimeLine} hyp` → BG の対応名 (`rw` の syntactic 一致に必要)。
5. `Q_elementaryAbelian` の 5 箇所を上表どおり置換し、`Q_pow_q_eq_one` を削除
   (AxiomsCheck の同名エントリも削除)。
6. `(_data : FieldNormalizerData hyp)` の underscore binder を `data` に (2 箇所以上)。
7. 長すぎる行 (完全修飾名で 100 字超) を折り返す。

⚠ 第 2 試行で 1 つミスした: `Q_pow_q_eq_one` を消すときに範囲を広く取りすぎて
`W2_pow_p_eq_one` まで削除してしまった。**宣言単位で正確に切ること**。

## 🚧 step 2b 第 3 試行 (2026-07-26) — 境界 file が最後の障害、解法も確定

recipe どおり一括置換したところ、**C.3 chain 6 file は全て error 0 に到達**した
(`Q_elementaryAbelian` 5 箇所も `Q_commutative`/`Q_pPrime`/`eq_one_of_mem_Q_of_pow_p_eq_one`
で置換完了、構成サイトも更新済)。mathlib の API 名も確定:

* 可換性は `setLike_mul_comm (s := data.Q) ha hb`
  (`Subgroup.mul_comm_of_mem_isMulCommutative` は deprecated、`(A := _)` でなく `(s := _)`)。
* `CommGroup ↥data.Q` を作る箇所は
  `mul_comm := fun a b => Subtype.ext (setLike_mul_comm (s := data.Q) a.2 b.2)`。
* `← data.card_W2` の rw は **motive not type correct** になる (`p` が `data` の型に出るため)。
  常に順方向 `data.card_W2` を使い、goal 側を `p` に寄せること。

**残った唯一の障害 = 境界 file**。`S16_G0Coprime.lean` は `data.P` と、S16 仮説の事実
`hyp.base.S_deriv_eq_PU : derivedInG S = hyp.base.P ⊔ hyp.base.U` を**同じ証明の中で混ぜる**。
`data.P` と `hyp.base.P` は構成サイトで等しいが定義的には等しくないので `rw` が噛み合わない。
(`SubgroupL.lean` も同様で、17 宣言が `data` 無しで `hyp.base.P` を使う。)

### ⟹ 解法 (次回これで通る見込み)

S16 側を `abbrev` でなく **pin 付き structure** にする:

```lean
structure FieldNormalizerData (hyp : Hypothesis (G := G)) extends
    OddOrder.BG.AppC.FieldNormalizerData hyp.base.p hyp.base.q G where
  P_eq : toFieldNormalizerData.P = hyp.base.P
  U_eq : toFieldNormalizerData.U = hyp.base.U
  W2_eq : toFieldNormalizerData.W2 = hyp.base.W2
  Q_eq : toFieldNormalizerData.Q = hyp.base.Q
```

* chain 側 (6 file) は `data.P` 等で書かれたまま動く (親フィールドへの dot 記法)。
* 境界 file (`S16_G0Coprime`, `SubgroupL`) は `data.P_eq` 等 4 本で橋渡しできる。
* 構成サイトは `P_eq := rfl` 等。
* 抽象側から使うときは親を取り出すだけ (pin は S16 専用の付加情報で、
  `HypothesisBAbstract.toFieldNormalizerData` 経由の抽象利用には現れない)。

⚠ 試行は revert 済、tree は green。

### ✅ pin 付き structure の前提を Lean で検証済 (2026-07-26)

解法の唯一の未確認点だった「`extends` 越しの dot 記法」を最小例で確認した:

```lean
structure Parent (n : Nat) where
  a : Nat
  h : a = n
namespace Parent
theorem lem {n : Nat} (p : Parent n) : p.a = n := p.h
end Parent
structure Child (m : Nat) extends Parent m where
  b : Nat
  b_eq : a = b            -- ⭕ 親フィールドを裸の名前で参照できる
example (c : Child 5) : c.a = 5 := c.lem   -- ⭕ 親の *定理* にも dot 記法が届く
```

⟹ pin 付き structure にしても **chain 側 (6 file) の `data.s` / `data.W2_le_P` /
`data.card_W2` 等はすべてそのまま動く**。境界 file だけが `data.P_eq` を使う。
step 2b の設計は全部品が検証済で、残るは 1 パスの実行のみ。

## ✅ step 2b 完了 + ❗ commit message の訂正 (2026-07-26)

commit `6518e7859` は **「C.3 chain を §16 の設定から切り離し抽象仮説の上で回るようにした」**
と書いたが、これは**言い過ぎ**。実測 (migration 後):

| 残っている `hyp.base` 依存 | 件数 |
|---|---|
| `p` / `q` | 530 / 192 |
| `p_prime` / `q_prime` | 89 / 24 |
| `p_odd` / `q_odd` / `three_le_q` / `p_ne_two` | 7 / 4 / 3 / 1 |
| `m` / `m_gt_49_hundredths_...` | 1 / 1 |
| `P` / `U` / `W2` / `Q` | 各 1 (= structure の pin 宣言のみ) |

**`{hyp : Hypothesis (G := G)}` を束縛したままの宣言が 203 件**残っている。

### 実際に達成されたこと (これは本物)

* **構造的依存の除去**: chain は `hyp.base.{P,U,W2,Q}` を**もう使わない**
  (490 箇所 → 0; 残 4 は pin 宣言そのもの)。部分群はすべて `data` から来る。
* **強化仮説 2 つの除去**: `Q_elementaryAbelian` と `p_eq_card_W2` が chain から消え、
  書籍どおりの「有限可換 `p'`-部分群」+ 導出された `|W₂| = p` で回る。
* pin 付き structure という載せ替えの器と、その全部品の検証。

### 残り (step 2c)

`{hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)` を
`{p q : ℕ} [Fact p.Prime] (data : AppC.FieldNormalizerData p q G)` に置換する (203 宣言)。
同時に:

* `hyp.base.p`/`q` → `p`/`q` (722 箇所)、`hyp.base.p_prime` → `Fact.out`、
  `hyp.base.q_prime` → `data.q_prime`。
* 奇性 4 種 (15 箇所) は書籍 Remark (V) の還元で扱う
  (`le_of_conditionA_of_not_odd` が既に在る) か、`FieldNormalizerData` に
  `p_odd`/`q_odd` フィールドを足す (書籍 Theorem C も (V) で奇性を仮定してよいとしているので
  後者でも faithful)。
* `m` 系 2 箇所は C.3 chain 外かどうか確認して切り離す。

これが済んで初めて `appC_normSet_generator_relation` が `S16.Hypothesis` 抜きで述べられ、
`hypothesisBAbstract_sl2` (Remark (II)) から `theoremC_abstract` を回せるようになる。
