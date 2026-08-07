# Peterfalvi 完全形式化 — カバレッジ census (2026-08-07 起点)

> **これは live な scope 文書**。[issue 0172](../../issues/0172-peterfalvi-full-formalization.md) の
> キャンペーン正本。章の監査が終わるたびに更新する。
>
> ⚠ **2026-07-16 の 3 冊 survey は使わない**。hub 裁定 9154 で降格済で、さらに 3 週間分 stale
> (Isaacs の章ラベルが全面的に誤っていた前例あり)。着手前は必ず実測する
> ([[verify-port-state-by-number-not-coq-name]])。

## 0. なぜ今これをやるか

2026-08-07 に Q₈ Brauer–Suzuki が閉じて **repo 全体の実 `sorry` が 0** になった。
しかし **sorry 0 ≠ 3 冊完了** — 未形式化の結果は `sorry` を生まないので、sorry カウントは
残スコープについて何も言わない。ユーザー裁定により Peterfalvi の完全形式化を次フロンティアに
定めた。測る対象は「書籍の番号付き結果を書籍強度で被覆したか」。

## 1. Part I の番号 census (機械抽出、2026-08-07 実測)

### 手順 (再現可能)

⚠ **この census は「番号が docstring に出るか」しか測っていない**。§1 の逐条監査 (§3.5) で、
番号 grep が **0 hit でも形式化済**という例が 2 件出た ((1.7)(c) は別番号で誤ラベル、(1.8) は
消費点の番号でラベル)。逆に cite ありでも中身が engine 止まり・特殊化のことがある。
**着手前に必ず結論の形でも検索すること**。

1. `references/peterfalvi/pdftotext/*.txt` の各章から正規表現 `\((ch)\.(\d+)\)` で番号を抽出。
2. 各章 `1..max` が**欠番なしで連続**することを確認 (全 14 章で連続 — 抽出漏れが無い傍証)。
3. repo 側は `OddOrder/**/*.lean` の docstring から `(N.M)` および sub-part `(N.M.x)` を grep。

⚠ 最初に `**Peterfalvi …(N.M)**` 形だけで grep すると 11 件を誤って「未 cite」と判定する。
repo は **`(1.5.d)` のような sub-part 形でしか cite していない結果**が多い。必ず
`\(N\.M(\.[a-z0-9]+)?\)` で取ること。

### 結果 — 書籍 169 件中 168 件が cite あり (残り 1 = (8.9) は 2026-08-07 に形式化済)

| 書籍番号 | 件数 | repo | 章 (書籍ページ) | 状態 |
|---|---|---|---|---|
| (1.1)–(1.10) | 10 | `S03` | §3 Preliminary Results from Character Theory (pp.5-9) | cite 全数あり |
| (2.1)–(2.11) | 11 | `S04` | §4 The Dade Isometry (pp.10-14) | cite 全数あり |
| (3.1)–(3.9) | 9 | `S05` | §5 TI-Subsets with Cyclic Normalizers (pp.15-20) | cite 全数あり |
| (4.1)–(4.10) | 10 | `S06` | §6 The Dade Isometry for a Certain Type of Subgroup (pp.21-24) | cite 全数あり |
| (5.1)–(5.9) | 9 | `S07` | §7 Coherence (pp.25-29) | cite 全数あり |
| (6.1)–(6.8) | 8 | `S08` | §8 Some Coherence Theorems (pp.30-37) | cite 全数あり |
| (7.1)–(7.11) | 11 | `S09` | §9 Non-existence of a Certain Type of Group (pp.38-43) | cite 全数あり |
| (8.1)–(8.18) | 18 | `S10` | §10 Structure of a Minimal Simple Group of Odd Order (pp.44-49) | ✅ (8.9) 形式化済 (2026-08-07) |
| (9.1)–(9.11) | 11 | `S11` | §11 Maximal Subgroups of Types II, III, IV (pp.50-57) | cite 全数あり |
| (10.1)–(10.11) | 11 | `S12` | §12 Maximal Subgroups of Types III, IV, V (pp.58-63) | cite 全数あり |
| (11.1)–(11.9) | 9 | `S13` | §13 Maximal Subgroups of Types III and IV (pp.64-68) | cite 全数あり |
| (12.1)–(12.17) | 17 | `S14` | §14 Maximal Subgroups of Type I (pp.69-74) | cite 全数あり |
| (13.1)–(13.19) | 19 | `S15` | §15 The Subgroups S and T (pp.75-86) | cite 全数あり |
| (14.1)–(14.16) | 16 | `S16` | §16 Non-existence of G (pp.87-92) | cite 全数あり |
| **合計** | **169** | | | **cite 169 / cite ゼロ 0** (2026-08-07 時点) |

⚠ **repo モジュール番号 = 書籍 result 章番号 + 2** (`S10` ↔ (8.x))。この off-by-2 は
frontier 誤診の常習犯なので、番号で話すときは必ずどちらの体系か明示する。

## 2. ⚠ この census が測っていないもの (ここが本体)

**「cite あり」= その番号が docstring に現れる**、それだけである。書籍強度の statement が
存在することを意味しない。番号 grep では原理的に検出できない残債が 3 種ある:

1. **特殊化債務** — 書籍より狭い仮説で述べている。2026-07-16 時点で Peterfalvi に 26 件と
   記録されたが、その後の一般化キャンペーンで大半が解消した可能性が高く**未実測**。
2. **部分被覆** — (a)(b)(c) のうち一部だけ形式化。とくに **bundled statement が条項を
   運搬していない**型が危険 (BG 15.7 で (b)(e) が `∃ X` decoupling により準恒真だった
   実例 = issue 3022。定理自体は真で unsound ではないが、書籍 content として数えてはいけない)。
3. **言及のみ** — 「(8.5) は §14 で使う」のような散文 cite があるだけで statement が無い。

⟹ **キャンペーンの本体は「番号を埋める」ことではなく、1 件ずつ statement を書籍と逐条照合する
監査**。上流優先 + 文書順で (1.1) から当たる。

## 3. 唯一の cite ゼロ — Peterfalvi (8.9) ✅ **2026-08-07 解消**

**形式化済** (commit `39bfc2831`、`OddOrder/Peterfalvi/S10_Theorem88CaseB.lean`):

| Lean 名 | 書籍 | 状態 |
|---|---|---|
| `Theorem88CaseBData.derivedInG_inf_centralizer_W1_eq` | (8.9) 内在形 `C_{S'}(W₁) = W₂` | axiom-clean |
| `Theorem88CaseBData.typePData_W2_eq` | (8.9) 書籍そのままの形 | axiom-clean |

**採用した形**: 下記「どちらの形を採るか」の問いに対する答えは **書籍の `W₂` 同定** (Coq の
witness 抽出形ではない)。理由は消費点が `TypePData S` を既に持っており、必要なのは
「その `.W2` が (8.8) の `W₂` と一致する」という同定だけだったため。

**副産物**: `Theorem88CaseBData` を `S12_MaximalIII_IV_V` から新 leaf `S10_Theorem88CaseB` へ
移設したうえで、書籍 p.46 と逐条照合して**欠けていた 6 条項を補充**した (旧版は (b1) の半分と
(b2)(b3) しか持たず、(8.9) が要求する (8.4.e)・`S ∩ T = W`・直積性・非自明性・(b4) を欠いていた)。
生産側 2 箇所 (`S14.theorem88_dichotomy` / `FeitThompsonSection16Core`) を実データで充足済 —
**仮説への hoist ではない**。

**(8.4.e) の供給経路**: BG Thm 14.7 の `IsTISubset (zTilde K K*) (K ⊔ K*)` 連言から直接出る。
これは書籍 (8.5.c)「V is a TI-subset of G with normalizer W」そのもので、抽象化した
`IsTISubset.set_normalizer_eq_of_subset_of_commute` (可換 host 内の TI-subset は任意の空でない
部分集合の正規化群を host に固定) を `GroupTheory/TISubset.lean` に置いた。
⚠ この経路は双対極大部分群の同定も型 `P₂` 性も要らない (TypePData 経由の重い版より真に弱い仮説)。

以下は着手時の調査記録 (保持)。

書籍 p.46 (`04.10_pp_44_49_...txt`):

> **(8.9)** Suppose that case (b) of Theorem (8.8) holds. Then the group denoted by `W₂` in
> Theorem (8.8) coincides with the group denoted by `W₂` in (8.4.d) with `M = S`.

**証明** (書籍 pp.46–47、全文):

> In the notation of Theorem (8.8), `W₂ ⊆ W ⊆ S`. Since `W` is cyclic, `|W₁|` and `|W₂|` are
> relatively prime, and so `W₂ ⊆ S'`, the commutator subgroup of `S`. Thus `W₂ ⊆ C_{S'}(W₁)`.
> By (8.4.d) with `M = S`, `W₁C_{S'}(W₁)` is abelian, and so `C_{S'}(W₁) ⊆ C(W)`. As `W`
> satisfies (8.4.e), `C_{S'}(W₁) ⊆ W`, whence `C_{S'}(W₁) = W₂`.

**検証** (着手時): `grep -rE "\(8\.9(\.[a-z0-9]+)?\)" --include=*.lean OddOrder/` = 0 hit。
内容 grep (`W2.*coincide` / `centralizer.*W1.*eq.*W2` 等) でも該当なし。

**Coq 対応**: `typeP_pairW` (`coq/theories/PFsection8.v:466`)。Coq は Peterfalvi Definition (8.4)
の Skolem 化である `of_typeP` 述語で述べており、

```coq
Lemma typeP_pairW S T W W1 W2 (defW : W1 \x W2 = W) :
  typeP_pair S T defW -> exists U : {group gT}, of_typeP S U defW.
```

すなわち「type-`P` pair から `of_typeP` の witness `U` が取れる」形に畳んでいる (`W₂` の同定は
その証明内部 `defW2xy : W2x :^ y = 'C_S'(W1)` として現れる)。(8.8)+(8.9) の合成が同ファイル
:712 の `FTtypeP_pair_witness`。

⟹ **決着 (2026-08-07)**: 書籍の `W₂` 同定を採った (上記)。

## 3.5. 逐条監査ログ (ステップ 3) — 文書順に進める

⚠ **「cite あり」は監査済を意味しない**。ここに行が在るものだけが実際に書籍と逐条照合済。
判定は **書籍のページ画像**を読んで条項ごとに突合すること (text は数式が OCR 崩れ)。

### §1 = repo `S03` (書籍 pp.5-9、`pages/peterfalvi-p005..p009.png`)

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (1.1) | ✅ 実証明 | `not_isReal_of_ne_trivial_of_odd_card'`、`BrauerPermutationUnconditional` に pointwise 版 |
| (1.2) | ✅ 実証明・仮説忠実 | `irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot` が `H` normal + `H ⊄ Ker χ` を正しく要求 |
| (1.3) | ✅ **2026-08-07 に補充** | 旧状態は **engine 止まり**の部分被覆 → `S03_InductionRestriction.lean` で (a) の同値と (b) 両結論を追加。詳細下記 |
| (1.4) | ✅ 実証明 | `isometry_difference_pair_structure` (`IsometryDifferencePair.lean`)。符号一様性・pairwise distinct まで込み |
| (1.5) | ✅ 実証明 (a)-(e) 全条項 | (a)(b) `restrict_induce_eq_norm_smul_sum` 系 / (c) `induce_eq_induce_iff_conj` (書籍より強い **iff**) + `inner_induce_eq_zero_of_not_conj` / (d) `InducedIrreducible.lean:327` / (e) `CliffordDecomposition.lean:433` |
| (1.6) | ✅ **2026-08-07 に補充** | (a) 両半分は在ったが**同値そのものが無かった** → `subsetCharacterKernel_induce_iff` で束ねた。(b) は **自明指標 `θ = 1` の場合だけ**だった (`induce_one_eq_compHom_induce_one_of_le`、docstring も "(1.6.b)" と引用符付きで自認) → 一般 `θ` 版 `induce_eq_compHom_induce_of_inflation` を証明し、自明版をその特殊化に置換 (重複 ~63 行削除) |
| (1.7)(a) | ✅ 実証明・verbatim | `induce_eq_sum_smul_induce_of_inertia_eq`。既約性・pairwise distinct・分解式の 3 結論すべて。coprime 性も `T/H` 可換性も不要な一般形 |
| (1.7)(b) | ❌ **未形式化** | 「`T/H` 可換 ⟹ `Ind_H^G θ = e ∑ χᵢ`, `n = \|T:H\|/e²`, `χᵢ(1) = \|G:T\|eθ(1)`」。repo が持つのは **coprime 版** (`induce_eq_sum_mul_linearClassFunction`, Gallagher) だけで、`GallagherDecomposition.lean:229` が「**general** Peterfalvi (1.7.b)」を未達目標と明記。必要な前提 = 可換 inertia 商への拡張定理 (`CyclicCharacterExtension` の巡回版は済、「合成列に沿って反復」が未実施 = 旧 issue 9002 の残り) |
| (1.7)(c) | ✅ **既に形式化されていた (2026-08-07 に書籍形も追加)** | ⚠ **前回の「未形式化」判定は誤り**。`CliffordDecomposition.exists_extension_induce_eq_sum_distinct_irreducible` が実体で、`S.card = [T:H]`・重複度 1 の相異なる既約指標の和・次数 `[L:T]·θ(1)` の 3 結論すべてを持つ。**ただし docstring が (1.7)(b) と誤ラベル**していたため grep で (1.7)(c) が 0 hit になり、別ファイル `GallagherDecomposition.lean:229` の「**general** (1.7.b) は未達」というコメントを (1.7)(c) の話と取り違えた。対処: (i) 誤ラベルを訂正、(ii) 書籍自身の仮説 `gcd(\|H\|, [T:H]) = 1` 版 `exists_induce_eq_sum_distinct_irreducible_of_coprime_card` を追加 (既存版は `gcd([T:H], o(θ)·d) = 1` 形)、そのための橋 `coprime_relIndex_orderOf_determinant_mul_of_coprime_card` も追加 (既存の橋は `H` が Hall という強い仮定だった) |
| (1.8) | ✅ **既に形式化されていた (2026-08-07 に番号ラベル追加)** | ⚠ また番号 grep が空振りした型。実体は `S08_YsetInner/CharacterBreaks.theta_degree_le_index_mul_sqrt_index` で、**消費点の番号 (6.2) でラベルされていて (1.8) と書かれていなかった**。結論は書籍と厳密に一致: `[K:C]·√[C:D] = \|K\|/√(\|C\|·\|D\|)` (∵ `\|D\| = \|C\|/[C:D]`)。仮説 (`N ◁ C`, `N ≤ D ≤ C`, `N ⊆ Ker(Res_C θ)`, `D/N ≤ Z(C/N)`) も書籍どおり。docstring に (1.8) を明記した |
| (1.9) | ✅ 実証明 (a)(b) 両方 | `CyclotomicGaloisAction.lean`: (a) = `exists_complexRingEquiv_pow_and_fixed` (CRT 形)、(b) = `exists_complexRingEquiv_mapRingEquiv_eq_pow`。`ℚ_n` の自己同型でなく `ℂ ≃+* ℂ` のレベルで実現している (docstring に明記) |
| (1.10) | ✅ 実証明 | `CyclotomicCharacterCongruence.lean:269` に (a)+(b) の合成系。(12.16)/(13.5) が消費 |

**§1 監査完了 (2026-08-07)**: 全 10 件のうち **未形式化は (1.7)(b) の 1 件のみ**
(重複度 `e` 付き一般形。可換 inertia 商への拡張定理が前提で、`CyclicCharacterExtension` の
巡回版は済・合成列に沿う反復が未実施)。補充したのは (1.3) と (1.6)、番号ラベルを直したのは
(1.7)(c) と (1.8)。

⚠ **本監査で最も重要な発見**: 「番号 grep が 0 hit」は**未形式化の証拠にならない**。
(1.7)(c) は (1.7)(b) と誤ラベルされ、(1.8) は消費点の番号 (6.2) でラベルされていたため、
どちらも番号では見つからなかった。**必ず結論の形 (conclusion shape) でも検索すること**
— (1.8) は `Real.sqrt` + index の積という形で探して見つかった。

**(1.3) で見つかった型 (再発を探すべきパターン)**: engine (証明の中核となる補題) は在るが、
**教科書の statement そのものが無い**。しかも engine の docstring が
"the `Res μ − Σ dᵢχᵢ` bookkeeping of the textbook statement is **left to the consumers**"
と自認していた。番号 grep では 100% 検出できない。
⟹ **監査時は「その番号の docstring を持つ宣言の *結論* が書籍の結論と一致するか」を見る**。
"engine" / "core" / "-style" / "left to the consumers" / "abstracted" は赤信号。

**(1.6) で見つかった第 2 の型 — 特殊化**: 番号を cite する宣言は在るが、**書籍より狭い場合しか
述べていない** ((1.6.b) は `θ = 1` のみ)。docstring が番号を**引用符付き** `"(1.6.b)"` で書くのは
書き手が自認している合図なので、grep で `"(N.M` (引用符つき番号) を探すと拾える。
処理は「一般版を証明 → 旧版をその特殊化に置換」(コンパイラが同値性を検証してくれる)。

**監査で使った検出クエリ** (次章でも同じ手順を踏むこと):
1. `grep -rn "(N\.M\(\.[a-z]\)\?)" --include=*.lean OddOrder/ | grep -v AxiomsCheck` で cite 箇所を列挙
2. 各 hit の**宣言の結論**を書籍のページ画像と条項ごとに突合 (docstring の主張を信用しない)
3. 赤信号語 + 引用符付き番号 + 「TODO」「まだ」「left as」を本文検索

### §2 = repo `S04` (書籍 pp.10-14、`pages/peterfalvi-p010..p014.png`)

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (2.1) | ✅ 実証明 | `GroupTheory/CoprimeConjugacy.coset_eq_cosetConjImage`。BG §13 Lemma 13.7 も消費 |
| (2.2) | ✅ 構造体として忠実 | `S04.Hypothesis` が (a)(b)(c) 全条項をフィールドで持つ ((b) の半直積は `centralizer_eq_sup` + `centralizer_disjoint` + `H_normalized` の 3 本に分解) |
| (2.3) | ✅ **2026-08-07 に補充** | 両半分 (`isTISubset_of_forall_H_eq_bot` / `H_eq_bot_of_isTISubset` + `of_isTISubset`) は在ったが **書籍の同値そのものが無く**、さらに「TI-subset **with normalizer L**」の `N_G(A) = L` 節が欠けていた (docstring が「`L` を明示的な normalizer-bound として保持する」と自認)。`isTISubset_iff_forall_H_eq_bot` と `normalizer_eq_of_isTISubset` を追加 (後者の汎用核 `IsTISubset.set_normalizer_eq_of_nonempty_of_normalizes` は `TISubset.lean`) |
| (2.4) | ✅ 実証明 (a)(b)(c) 全条項 | `S04_DadeIsometryBasic`: (a) `:470` / (b) `:319` / (c) `:579` |
| (2.5) | ✅ 定義 + 整合性 | `S04_DadeIsometry`: 明示 Dade 写像 `:236`、well-definedness `:203`、uniqueness `:97`、defining equations `:303` |
| (2.6) | ✅ **本体が実構成** | `S04_DadeIsometry`: (a) 等長性 `:755` / (b) 仮想指標保存 `:960` / 束ね `Hypothesis.fullDadeIsometryData :996`。**仮説 (2.2) だけから構成**されており interface assumption ではない ((2.10) の包除原理が (b) を閉じている) |
| (2.7) | ✅ **2026-08-07 に補充** | 一般形 `adjoint_formula` は在ったが、書籍の **"In particular" 節**「`χ` が各 `aH(a)` 上で定数 ⟹ `(α^τ,χ)_G = (α, Res_L^G χ)_L`」が無かった (repo には `χ = τβ` の特殊化 `adjointAverageFun_dadeMap_eq` のみ)。`adjoint_formula_restrict` を追加 |
| (2.8) | ✅ 実証明 | `S04_DadeIsometryBasic` に 5 分割 (`H(B)` `:800` / `N_L(B)` `:854` / normality `:916` / disjointness `:947` / `M(B)` `:965` / 位数等式 `:980`) |
| (2.9) | ✅ 実証明 | `f_B` `:1057` / `α_B` `:1099` / 仮想指標保存 `:1106` / 定義式 `:1147` |
| (2.10) | ✅ 実証明 | pointwise identity `S04_DadeIsometry:846`、sub-part (2.10.1) 13 箇所 / (2.10.2) 5 / (2.10.3) 15 |
| (2.11) | ✅ 実証明 | `S04_DadeIsometry:311` (restriction compatibility) + `:329` (pointwise form) |

⚠ **番号衝突に注意**: `(2.5)` `(2.6)` `(2.7)` は BG・Isaacs にも同じ番号があり、repo 全体 grep では
無関係ファイル (`BG/Ch1_Preliminary/S02_*`, `GroupTheory/RepresentationTheory/*` 等) が大量に混ざる。
Peterfalvi §2 の監査では **`OddOrder/Peterfalvi/S04_*.lean` に絞って** grep すること。

### §3 = repo `S05` (書籍 pp.15-20、`pages/peterfalvi-p015..p020.png`) — **監査途中**

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (3.1) Hypothesis | ✅ 構造体 | `TICyclicHypothesis` (cite 10 箇所) |
| (3.2) | ✅ (a)-(d) 全条項 + 等長性 + 仮想指標保存 | capstone `TICyclicHypothesis.exists_sigma` (`S05_SigmaIsometry:399`) が 6 連言すべてを持つ。個別も (a) `:164`/`:218` (b) `:152` (c) `S05_IntegralSigma:72` (d) `:353` |
| (3.3) (3.4) (3.5) | ✅ 実証明 | ω-grid `S05_OmegaGrid:62`、`α_{ij}` 基底 `S05_NormThree:134`、(3.5.1)-(3.5.5) の sub-part も密 (計 71 cite) |
| (3.6) Hypothesis | ✅ 定義として忠実 | `sigmaCoeff` (係数 `a_{ij} = ⟨ψ, ω_{ij}^σ⟩`) + `sigmaNC` (`NC(ψ)`) |
| (3.7) | ✅ **2026-08-07 に補充** | 格子恒等式 `a_{ij} + a_{i'j'} = a_{ij'} + a_{i'j}` は `sigmaCoeff_add_eq` として在ったが、書籍の **"In particular" 節** `a_{ij} = a_{i0} + a_{0j} − a_{00}` が無かった → `sigmaCoeff_eq_add_sub` を追加。(1.3)(b) / (2.7) に続く 3 例目の「In particular 欠落」 |
| (3.8) | ✅ 内容は在る (packaging 差あり) | `S05_SigmaTrichotomy.sigmaCoeff_trichotomy` が三分岐を係数形で持つ。⚠ 書籍は結論に **`NC(ψ) = w₁` / `= w₂`** を含め、`ψ = a·Σω^σ + β` の形で述べる。repo は係数形 (「列 `j₀` が定数 `c ≠ 0`、他は 0」) で、NC 値は導けるが**述べられていない**。数学的内容は同値だが packaging が違う — 低優先の繰延項目 |
| (3.9) | ✅ 実証明 (a)(b)(c) 全条項 + (a) の "In particular" 節 | `S05_SigmaIsometry`: (a) `:830` / (a) の "in particular" (σ が係数体自己同型と可換) `:902` / (b) `:949` / (c) `:1270`。(3.9.b) の Galois 推移性補題 (`:1023` `:1101`) も有 |

**§3 監査完了 (2026-08-07)**: 全 9 件のうち**未形式化ゼロ**。補充したのは (3.2)(d) の書籍 literal 形と
(3.7) の "In particular" 節の 2 件。繰延 1 件 = (3.8) の packaging 差 (上記)。

✅ **(3.2)(d) の書籍 literal 形を 2026-08-07 に補充**。従来は直交形 (「`σ(Irr W)` の全てと直交する
類関数は `V` 上で消える」) だけで、書籍の「**σ の像に入らない**既約指標は消える」は
docstring が「in particular 直交する」と**散文で主張**していただけだった。
`apply_eq_zero_of_mem_V_of_not_mem_range_sigma` (`PrimeTIResidue.lean`) として証明。
橋渡しは既存の `dirr` 抽出 (`ω^σ = δ·μ`, `δ = ±1`, `μ ∈ Irr G`)。
⟹ **教訓: docstring の「in particular ～」「so this is the stated form of ～」は赤信号**
(証明でなく主張)。

### §4 = repo `S06` (書籍 pp.21-24、`pages/peterfalvi-p021..p024.png`) — **監査途中**

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (4.1) | ✅ 実証明・書籍と逐条一致 | `InducedIrreducible.pairwise_inner_eq_zero_of_orthogonal_signedDifference` (+ 核 `inner_eq_zero_of_orthogonal_signedDifference`)。仮説 4 本 (`α,β,γ,δ` が norm-1 の `ZIrr` 元 / `(α,β)=(γ,δ)=0` / `(α−β, uγ−vδ)=0` / 両差が `1` で消える、`u,v` は非零実数) と結論 (4 つの交差内積すべて 0) が書籍どおり。⚠ **前回「要確認」としたのは誤り** — grep を `S06_*.lean` に絞ったせいで見落とした。§4 の結果が `GroupTheory/RepresentationTheory/` に在る例で、(1.8) と同型の教訓 |
| (4.2) Hypothesis | ✅ 構造体 | certain-type hypothesis ((a) `L = K ⋊ W₁`、(b) `C_K(x) = W₂`、(c) `W` 奇位数) |
| (4.3)(a) | ✅ 実証明 (両半分) | TI part `S06_DadeIsometryCertain:237` + Hypothesis (3.1) 成立 `:408`、centralizer form `:190` |
| (4.3)(b) | ✅ 実証明 | `columnFamily` (`S06_MuColumnBridge`)。`μ_{ij}` の pairwise distinct と `Ind_W^L(ω_{ij} − ω_{0j}) = δ_j(μ_{ij} − μ_{0j})` |
| (4.3)(c) | ✅ **両文とも実証明** | 第 1 文 (値の同定) `S06_CertainTypeCharacters:1006`、**第 2 文 (completeness、`μ_{ij}` でない既約は `W − W₂` 上で消える)** `:1048`。⚠ (3.2)(d) と同じ形なので確認したが、こちらは在った |
| (4.3)(d) | ✅ 実証明 | 次数合同 `μ_{ij}(1) ≡ δ_j (mod w₁)` `S06_CertainTypeCharacters:1065` |
| (4.4) | ✅ 実証明 (全条項) | `S06_CertainTypeCharacters`: 完全特徴づけ `:1309` (「`μ_{i0}` = 核が `K` を含む `L` の既約指標」) + 両方向 (`:1191` `:1277`) + アンカー `δ₀ = 1`, `μ₀₀ = 1_L` `:1149` |
| (4.5)(a) | ✅ 実証明 (3 主張とも) | `S06_CertainTypeClifford`: `i` に依らない `:614` / `χ_j ∈ Irr(K)` `:747` / `Ind_K^L χ_j = μ_j` `:758` |
| (4.5)(b) | ✅ 実証明 (**"Moreover" 節込み** 3 主張とも) | 第 1 文 `:970` / `Ind_K^L χ ≠ μ_{ij}` `:983` / 網羅性 (`L` の既約は `μ_{ij}` か `Ind_K^L χ`) `:1005`。⚠ "Moreover" 型なので重点確認したが揃っていた |
| (4.6) Hypothesis | ✅ 構造体 (a)-(e) | `S06_CertainHypothesis46`。(a) `L` が (4.2) を満たす / (b) `G, W` が (3.1) / (c) `H ⊴ L`, `W₂ ⊆ H ⊆ K` / (d) 被覆条件 `⋃_{h∈H^#} C_K(h)^# ⊆ A ⊆ K^#` と `A₀ = A ∪ V^L` / (e) 記号と `τ` |
| (4.7) | ✅ 実証明 (**5 主張とも**) | `S06_CertainTypeSupport`: (i) `Supp χ ⊆ A∪{1}` `:91`/`:110` / (ii) `Supp Ind_K^L χ ⊆ A∪{1}` `:130` / (iii) `j≥1 ⟹ H ⊄ Ker χ_j` `:185`/`:358` / (iv) `Supp χ_j ⊆ A∪{1}` `:394` / (v) `Supp μ_j ⊆ A∪{1}` `S06_CertainTypeCoherence:285`。構造形 `:43` は Dade 等長性に依らない一般版 |
| (4.8) | ✅ 実証明 (**3 結論とも**) | 結論(1) `Supp(μ_ij − μ_ik) ⊆ A₀` (`FeitThompsonCharacterData:299` = `muS_diff_support`、engine は `S06_CertainTypeStructure:37`) / 結論(2) `δ_j = δ_k` (`certainType_columnSign_eq`, `S06_CertainTypeCoherence:332`) / 結論(3) 等長性同一式 (`S05_SigmaTrichotomy:267` + AxiomsCheck 2456)。⚠ **`FeitThompsonSection16Core` の構造体フィールド `mu_diff_support` は posited ではない** — `FeitThompson.lean:110` が `Section16CharacterData.muS_diff_support` から**実供給**しているのを確認した |
| (4.9)(a) | ✅ 実証明 (主要主張) / ⚠ 1 節が未確認 | `S06_CertainTypeConjugation`: 共役 bridge `:200` / `μ̄_{ij} = μ_{i'j'}` `:223` / `μ̄_j = μ_{j'}` (列和形) `:249` / `μ̄_k ≠ μ_k` `:298`。`0 ≠` の部分は `certainType_nonzero` (`S06_CertainTypeCoherence:524`)。✅ **`ℤ[T, L^#] = ℤ[T, A]` の等式は 2026-08-07 に補充** (`S07.zSupportedSpan_ne_one_eq`、§5 の (5.2)(b) 橋渡しと共通)。当初「見つからない」と記録したもの — (4.7)(v) (`Supp μ_j ⊆ A ∪ {1}`) から従うはずで、repo は `IsCoherent` を最初から `ℤ[T,A]` 相対で述べるので不要になっている。`S10_SubcoherentTypeP:72,297` が下流でこの等式に言及し「(4.7) から得る」と書いている。**低優先の要確認** |
| (4.9)(b) | ✅ 実証明 (全条項) | `certainType_isCoherent` (`S06_CertainTypeCoherence:554`) が書籍の (b) を丸ごと束ねる: 拡張 `ν : μ_{ij} ↦ δ_j ω_{ij}^σ` が `ℤ[𝒯]` 上で等長 (`:249`)、`ℤ[𝒯,A]` 上で `τ` と一致 (`:486`)、`ℤ[Irr G]` に着地 (`:206`)、かつ `ℤ[𝒯,A] ≠ 0`。生成系の補題 (`ℤ[𝒯,A]` は差 `μ_j − μ_k` で生成、`:416`) も書籍の証明どおり |
| (4.10) | ✅ 実証明 (書籍の式そのもの) | `fourCorner_dade_eq` (`S06_CertainTypeFourCorner:432`): `(δ_j μ_{ij} − δ_j μ_{0j} − μ_{i0} + μ_{00})^τ = ω_{ij}^σ − ω_{0j}^σ − ω_{i0}^σ + ω_{00}^σ`。piece (a) `:38` (L 側 = 誘導)、piece (b) `:98` (W 側は `V` 上に台)、crux (c) `:389`、crux (d) `:303` から組み上げ |

**§4 監査完了 (2026-08-07)**: 全 10 件のうち**未形式化ゼロ**。補充ゼロ (§4 は元から完全被覆)。
⚠ 要確認 1 件 = (4.9)(a) の `ℤ[T,L^#] = ℤ[T,A]` 節 (上記、低優先)。
⚠ 途中で (4.1) を「要確認」と誤判定した — grep を `S06_*.lean` に絞ったため。教訓は memory
[[textbook-coverage-audit-failure-modes]] に記録済。

### §5 = repo `S07` (書籍 pp.25-29、`pages/peterfalvi-p025..p029.png`) — **監査途中 ((5.1)(5.2) 済)**

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (5.1) Definition | ✅ 条項対応が忠実 | `S07.IsCoherent` (`S07_Coherence/NormInequalities:484`)。`nonzero` = `ℤ[S,A] ≠ 0` / `extension` + `extension_inner_eq` (on `zSpan S`) = 「`ℤ[S] → ℤ[Irr G]` の線形等長」/ `extends_on_supported` = 「`ℤ[S,A]` 上で `τ` と一致」/ `extension_mem_ZIrr` = 終域が `ℤ[Irr G]`。書籍が 1 文で言う「等長 `ℤ[S] → ℤ[Irr G]`」を内積保存 + 終域の 2 フィールドに割っただけで内容は同じ |
| (5.2)(d) | ✅ 実証明 + **存在構成あり** | `OrthonormalCharacterImageFamily` (`DifferenceImage:835`) が書籍の `R(χ)` そのもの (`(χ − χ̄)^τ = Σ_{α∈R(χ)} α`、`R(χ)` は `ℤ[Irr G]` の正規直交部分集合)。2 元版 `CharacterDifferenceImage` は**かつて constructor 無しの posited 構造体**だったが、`characterDifferenceImageOfIsometry` (`:1132`) が §3 (1.4) keystone から**実構成**するようになっている (docstring に経緯あり) |
| (5.2)(e) | ✅ 実証明 | disjoint-pair 直交 `DifferenceImage:898`、同一定義域版 `:730` ((4.1) 経由)。§9 レベルの形も `AxiomsCheck:12508` |
| (5.2)(a)(b)(c) | ✅ **束ねた構造体が在り、書籍忠実** | `S07.GeneralHypothesis` (`S07_Coherence/NormInequalities:603`) が (a)-(e) 全 5 条項をフィールドに持ち、各フィールドの docstring が書籍の条項番号を明示。(a) = `conjugate_closed` + `no_real_characters` / (b) = `tau` + `tau_isometry_diff` / (c) = `pairwise_orthogonal` |
| **(5.2) 全体の重要注記** | ⚠ 2 つの carrier があり **旧 `Hypothesis` は特殊化債務**だった | `S07.Hypothesis` は `difference_image` を **2 元版** (`CharacterDifferenceImage`) で持つため、ノルムを取ると `‖τ(χ−χ̄)‖² = 2` と (5.2.b) 等長性から `‖χ−χ̄‖² = 2‖χ‖²` が出て **`S` の全メンバーの既約性を暗黙に強制**する。書籍はそれを課さない (可約メンバーは `‖χ‖² > 1`, `\|R(χ)\| = 2‖χ‖²`)。これが **(5.7) を書籍強度で証明できなくしていた** (issue 0157)。→ 書籍忠実な `GeneralHypothesis` (R(χ) が**任意サイズ**) が導入され、`Hypothesis.toGeneralHypothesis` で旧版が特殊化として繋がっている。**私の監査分類でいう「特殊化」型が、過去に発見・解消された実例** |
| **(5.2)(b) の `L^#` vs `A`** | ✅ **2026-08-07 に橋渡しを補充** | 書籍は `τ : ℤ[S, L^#] → ℤ[Irr G, G^#]` の等長。repo は **`ℤ[S,A]` 相対**。docstring が理由を明記: FT の Dade 写像には**大域的な等長は存在しない** (`dim CF(L) > dim CF(G)`)、かつ pre-0099 の全メンバー差分形は混合次数の族で**偽**。書籍の `L^#` 版と一致するのは **`ℤ[S,L^#] = ℤ[S,A]`** (= (4.7) 由来) による。⟹ この等式 `zSupportedSpan_ne_one_eq` を `S07_Coherence/DifferenceImage.lean` に追加した (仮説「各メンバーの台が `A ∪ {1}`」は (4.7) が供給)。従来は必要な個別の台評価 (`inducedNonKernelFamily_conjDiff_support` 等) だけが在り**格子の等式そのものは無かった**。ambient 版の台伝播補題 `support_subset_of_mem_zSpan` も併せて追加 (既存版は subgroup 相対専用)。⟹ **(4.9)(a) の繰延項目もこれで解消** |
| (5.3)(b) | ✅ 族は書籍忠実 / ⚠ docstring の引用を訂正 | 族 `S10.inducedNonKernelFamily` が書籍どおり (`θ : Irr ↥K`、フィルタ `¬(H.subgroupOf K ⊆ characterKernel θ)`、像 `Ind_K^L θ`)。producer は `inducedNonKernelFamily_subcoherent` (= (5.3.b) verbatim)。証明は可約性で 2 分岐 (既約 → (5.3)(a) の 2 元 `R(χ)` / 可約 → (4.4)+(4.5) で源が certain-type 列と判り (4.9) が `2w₁` 元の `R(μ_j)` を供給)。⚠ **`S06_CertainTypeSubcoherent:17` の書籍引用が `{Ind_H^L θ \| θ ∈ Irr H, …}` と誤転記されていた** (書籍 p.25 は `Ind_K^L`, `θ ∈ Irr K`。`W₂ ⊆ H ⊆ K` なので別物) → 2026-08-07 訂正。Lean 側は元から正しかった。書籍の末尾節「`φ ∈ 𝒮 ∩ Irr L` なら `R(φ) ⊥ ω^σ`」も引用に補った |
| (5.3)(a) | ✅ 実証明・書籍の証明どおり | `nonempty_characterDifferenceImage_of_irreducible` = 「任意の `τ` に対する (5.3.a)」: 既約・非実な `χ` で `‖τ(χ−χ̄)‖² = 2` ⟹ 相異なる既約の符号付き対 (`dirr_small_norm`)、`1` で評価すると ((5.2.b) の終域 `ℤ[Irr G, G^#]`) **符号が逆**に強制され 2 元 `R(χ)` になる。`InducedFamilyTauData.hypothesis` が (5.2) 全体を供給し、**(5.2.e) は (4.1) から *導出*** (転送ではない) — **書籍の (5.3.a) の証明どおり** |
| (5.4) | ✅ 実証明 (a)(b) とも・書籍と一致 | 仮説束ね `NormInequalities:28` (`CharacterPsiDecomposition`)、(a) `inner_self_chi_re_le_inner_self_X` `:309`、(b) `:387` (`‖X‖² = ‖χ‖²`, `‖Y‖² = ‖ψ‖²`, `X = ∑_{α∈E} α`)。書籍 p.26 と条項一致 |
| (5.5) | ✅ 実証明・書籍の証明どおり | `NormInequalities:442`。書籍と同じく **(5.4) を `ψ = 0` で適用** し、`‖Y‖² ≥ ‖ψ‖² = 0` が自動成立するので `Y = 0`、`χ^{τ₁} = X = ∑_{α∈E} α`。⚠ 前回 `S12_TypeIIColumnPin` を実体と記録したのは誤り — あれは §12 の**応用**で、一般形は S07 に在る (「節のディレクトリに絞らない」の再確認) |
| (5.6) | ✅ **全体組み立てが在る (UNCONDITIONAL)** | ⚠ **前ターンの「全体定理が見当たらない」は誤り**。実体は `S07.retarget_isCoherent` (`S07_RetargetScaled:367`) = 「**MAIN coherence-union assembly (general (5.6), UNCONDITIONAL)**: `IsCoherent (S₁ ∪ {χ,χ̄}) A`」。拡張 `τ₂ := retarget τ₁ χ χ̄ X X̄` を**構成**し、`ℤ[S₁∪{χ,χ̄}]` 上の格子等長を証明、`extends_on_supported` を 3 本の差分生成元で discharge。**special-position 制限なし**。さらに仮説側も posited でなく構成される: `{X,X̄}` は `retargetTargetPair` が (5.5) 分解から**構成** (既約 `χ` では target pair は強制される)、`himg` は `image_eq_of_decomposition` が構成。(6.6)/(6.8) の `coherentPairChain` が呼ぶ単一エントリ (`IsCoherent τ S₁ A → IsCoherent τ (S₁∪{χ,χ̄}) A`) も在る。私が先に見つけた `isCoherent_union_pair_of_bridge` は §9 レベルの**別ルート** (bridge 経由) だった。⬜ 残る narrow な問い: 書籍の仮説 (b) `χ₁(1) \| χ(1)` と (c) 次数不等式が、repo では「分解 `D₀`/`Da` の存在」に置き換わっている。(b)(c) ⟹ 分解存在 の橋渡しが statement として在るかは未確認 |
| (5.7) | ✅ **書籍強度で実証明** | `coherent_of_constant_degree_general` (issue 0157)。**メンバーの既約性を仮定しない**書籍どおりの形で `GeneralHypothesis` 上に述べられている。旧 `coherent_of_constant_degree` (2 元 carrier) は `m = 1` の特殊化。base case `\|𝒮\| = 2` は `R(χ)` を `m = ‖χ‖²` で二分する構成 (`isCoherent_pair_of_orthonormalImage`) |
| (5.8) | ✅ 実証明 (二分律 + 一意性 rider) | 二分律 `S12.certainTypeR_subsum_dichotomy` — Hypothesis (4.6) 一般に抽象化済 (issue 0161、型-II 特殊化 `typeII_nu_tau2_dichotomy` の ~430 行が抽象版へ移動)。「`ψ` が (4.9) 列像族 `R(μ_j)` の濃度 `w₁` 部分和で `V` 上消えるなら符号付きの完全 σ-grid 列」。**一意性 rider** (書籍 p.29) `S06.subsum_eq_column_of_third_column` も別途 |
| (5.9) | ✅ (a)(b) とも実証明 | (a) `S07_CoherenceGalois:94` (Dade 状況で `𝒮 ⊆ Irr L`, `\|𝒮\| ≥ 2`, 共役閉)。**(b)** `DifferenceImage:1256` = 「`τ` が複素共役と可換なときの差分像の共役対応」(`CharacterDifferenceImage.nu_eq_mu_conj`)、§14 の (12.3) bar-trick が消費。書籍 p.29 と未突合 |

**§5 監査完了 (2026-08-07)**: 全 9 件で**未形式化ゼロ・補充ゼロ**。§4 に続いて元から完全被覆だった。
⬜ narrow な残問 1 件: (5.6) の書籍仮説 (b) `χ₁(1) \| χ(1)` / (c) 次数不等式が repo では
「分解 `D₀`/`Da` の存在」に置き換わっている。(b)(c) ⟹ 分解存在 の橋渡しの有無は未確認 (低優先)。

⚠ **§5 の監査で私は 3 回「実体が無い」と誤判定しかけた** ((4.1)/(5.5)/(5.6))。いずれも検索範囲を
節の repo ディレクトリに絞ったのが原因。**`AxiomsCheck.lean` の番号コメント検索を最初に打つ**のが
最も確実 (「何がどこまで証明されたか」が番号付きで記録されている)。正本 = memory
[[textbook-coverage-audit-failure-modes]]。

⚠ **既知の罠**: (5.3)(b) の族の条件は `θ ≠ 1_K` **ではなく** `H ⊄ Ker θ`
(memory [[read-book-hypothesis-before-adding-side-condition]] — 過去に取り違えて 1 session 誤診した)。

### §6 = repo `S08` (書籍 pp.30-37、`pages/peterfalvi-p030..p037.png` 切り出し済) — **監査完了 (2026-08-07)**

全 8 件 ((6.1)-(6.8)) を書籍ページ (p.30/31/32/33) と逐条突合した。**未形式化ゼロ**。
補充 3 件 = (6.7) の第 1 結論 `ψ(z) ∈ ℤ` / (6.8)(b) の `τ = Ind_L^G` / (6.8)(b) の格子 `ℤ[𝒮,L^#] = ℤ[𝒮,H^#]`。

| 書籍 | AxiomsCheck が記録する到達点 |
|---|---|
| (6.1) | Hypothesis。「assume that Hypothesis (5.2) holds」と読む (`:4076`)。一般核の族 `S(X) = {Ind_K^L θ \| θ ∈ Irr K, θ ≠ 1, X ⊆ Ker θ}` (issue 2022)。standalone 版は `K` 可解 / `H ≤ K` 冪零 / `K ≠ H` (`:3976`) |
| (6.2) (6.3) | **oracle 無し**で一般核 (`six_two_of_imageData` / `six_three_of_imageData`、issues 0153/0154)。(6.3.b) は「`K/X` 可換なら `𝒮(X)` coherent」を任意の可解正規 `K` で (`:4113`) |
| (6.4) | **Hypothesis** (定理でない)。書籍 p.31 と条項一致: (a) (6.1) + `\|L\|` 奇 / (b) `M ⊴ L`, `M ⊆ K`, **`K/M` 冪零** / (c) `H₁/M = [K/M,K/M]` かつ `L/H₁` が核 `K/H₁` の Frobenius 群 |
| (6.5) | ⚠ **特殊化債務を確認** (2026-08-07、書籍 p.31 と突合)。書籍は「(6.4) を仮定し `𝒮(M)` が **coherent でない**」下で (a) `K/H₁` が `L` の chief factor かつ `\|K:H₁\| ≤ 4\|L:K\|²+1` / (b) ある素数 `p` で **`K/M` が非可換 `p`-群** / (c) `\|L:K\| ∤ p−1`。repo は (a) `relIndex_le_of_not_isCoherent` + `isChiefFactor_of_not_isCoherent` / (b) `exists_prime_isPGroup_of_not_isCoherent` / (c) `not_dvd_sub_one_of_not_isCoherent`。**⚠ repo は `K` 自体の冪零性を要求するが書籍 (6.4)(b) は `K/M` の冪零性**。✅ **2026-08-07 に書籍形へ一般化済** ([issue 0173](../../issues/closed/0173-peterfalvi-65-generalize-nilpotent.md) closed)。診断: 過剰仮説は **wrapper の宣言だけ**で、engine `six_three_of_six_two_oracle` は元から書籍形 `[Group.IsNilpotent (↥H ⧸ M.subgroupOf H)]` を取っていた (=「threading されている ≠ 依存している」)。(6.3) wrapper と (6.5)(a) の 2 定理を書籍形へ。(6.5)(b),(c) の section は変数に `M` が無く書籍の `M = 1` の場合なので**債務ではない**と判定 (`K/M = K` ゆえ `[Group.IsNilpotent ↥K]` が書籍 (6.4)(b) そのもの) |
| (6.6) | ✅ **2 結論とも在る**。書籍 p.31: 「(6.4) が `M = 1` で成立、`Z ⊴ L`, `1 ≠ Z ⊆ Z(K)`, `𝒳 = 𝒮 − 𝒮(Z) ⊆ Irr L` ⟹ **`𝒳 = {χ ∈ Irr L \| Z ⊄ Ker χ}`** かつ **`𝒳` は coherent**」。repo は一貫性半分 `xSet_isCoherent_of_irreducible_X` (一般核 + **任意の `τ`**、Dade datum 不要、issue 0155) と `X`-特徴づけ (`:4335`) の両方。書籍 p.32 の証明どおり ((5.7) で最小次数ブロック → 次数順に (5.6) で 1 対ずつ追加)。⚠ **書籍自身が `M = 1` を置く**ので (6.5) の特殊化債務の影響を受けない |
| (6.1) 突合 | ✅ **忠実 + 一般化**。書籍 p.30 の 3 条項 = 「Hypothesis (5.2) が成立」「`K` は `L` の可解正規部分群」「`𝒮 = {Ind_K^L θ \| θ ∈ Irr K, θ ≠ 1_K}`」+ `𝒮(A)` の定義。repo の `InducedFamilyImageData` は (5.2.b) の `τ` (+ 終域 `ℤ[Irr G]` + `τφ(1) = 0`) と (5.2.d)/(5.2.e) を**データ**として持ち、(5.2.a)(5.2.c) は族の形から**証明**される (`S08_SixTwoGeneral`)。⚠ 書籍の等長は `ℤ[𝒮, L^#]` 上、repo は任意の `A₀` (`K^# ⊆ A₀`, `1 ∉ A₀`) 上 ⟹ **より弱い仮説 = より強い定理**。`inducedKernelFamily K X` は `{Ind_K^L θ \| θ ≠ 1_K, X ∩ K ⊆ Ker θ}` で書籍どおり |
| (6.2) 突合 | ✅ **忠実 + 書籍の statement を修理**。結論 `\|K:A\| − 1 ≤ 2\|L:C\|√\|C:D\|` / 仮説 (a)(b) は一致。**⚠ repo の `hBK : B < K` は (6.2.a)(b) から従わない**: `B = K` では `D = C = K`・`D/B = 1 ⊆ Z(C/B)` で (a) が成立し、`𝒮(K) = ∅` は書籍 (5.1) の `ℤ[𝒮,A] ≠ 0` 条項ゆえ **coherent でない** ので (b) も成立する — が結論 `\|K:A\| ≤ 2\|L:K\|+1` は偽 (例: `A = 1` で `𝒮` coherent)。書籍の証明は breaking pair `𝒮₂ = {ψ,ψ̄} ⊆ 𝒮(B)` を取るので `𝒮(B) ≠ ∅` (= `B < K`) が必要。**書籍 statement の implicit 仮定**であり repo 側の特殊化債務ではない (docstring に明記した)。mathcomp `coherent_seqIndD_bound` が `B \proper K` 無しで通るのは、そちらの `coherent` が `ℤ[𝒮,A] ≠ 0` 条項を落として空族を coherent にしているため。repo は `C`/`D` の `L`-正規性を要求せず `D` は `D ⊓ C` 経由でしか入らない (= 書籍より弱い仮説) |
| (6.3) 突合 | ✅ **忠実** (issue 0173 の一般化後)。書籍 p.30: `M ⊆ H₁ ⊆ H ⊆ K` 正規 + (a) `H/M` 冪零 (b) `𝒮(H₁)` coherent (c) `\|H:H₁\| > 4\|L:K\|²+1` ⟹ `𝒮(M)` coherent。repo binder = `[Group.IsNilpotent (↥H ⧸ M.subgroupOf H)]` で (a) そのもの。`hH₁H : H₁ < H` は狭いが (c) が `\|H:H₁\| ≥ 5` を強制するので損失なし。⚠ **`six_three_of_imageData` の docstring に残っていた「repo は `H` 冪零を取る」という特殊化注記は stale だった** → 2026-08-07 訂正 (engine は元から書籍形) |
| (6.7) | ⚠ **第 1 結論が欠けていた → 2026-08-07 補充**。書籍 p.32 の結論は **2 つ**: `z ∈ Z^#` に対し **(i) `ψ(z) ∈ ℤ`** と **(ii) `ψ(z) ≡ ψ(1) (mod \|P\|)`**。repo は (ii) のみ (`peterfalvi_67_of_odd`、`[ALGMOD \|P\|]`) で、(i) は「consumers upgrade to a ℤ-congruence where they separately know `ψ(z) ∈ ℤ`」と**下流に委ねられていた** (file docstring が自認)。⟹ `exists_int_character_of_constant_on_nonidentity` を追加 (`SylowTICongruence.lean`): `Z^#` 上定数な指標は `ψ(1) + (\|Z\|−1)ψ(z) = ∑_{w∈Z} ψ(w) = \|Z\|·dim V^Z` (`sum_character_eq_card_mul_finrank_invariants`) で有理数と判り、代数的整数ゆえ整数 — **TI/Sylow/奇数位数を一切使わない**書籍の証明冒頭そのまま。併せて `peterfalvi_67_int_dvd_of_odd` (両結論 + `\|P\| ∣ ψ(z)−ψ(1)` の ℤ 整除形) と AlgInt の逆向き橋 `int_dvd_of_cong_intCast` (`Cong.of_int` の converse) を追加。**番号 grep では検出できない「部分被覆」型の実例 2 件目** |
| (6.7.1)(6.7.2)(6.7.3) | ✅ 在る。(6.7.1) = `fixedPointFree_classPair_of_isTISubset` + `card_dvd_classSumCoeff_of_fixedPointFree` (`\|P\| ∣ a_{ijs}\|C_s\|`、書籍 p.32 の `Ω = {(u,v) ∈ C_i×C_j \| uv ∈ C_s}` への固定点自由作用)。(6.7.2)/(6.7.3) = `centralCharacterOfRep_classSum_mul_cong_collapse_of_isTISubset` + `peterfalvi_673_combine`/`peterfalvi_673_cancel` (`\|C₁\|` が `p` と互いに素ゆえ消去)。`a₁₁₀ = 0` は `RealClassTISubset` が無仮説で供給 (書籍「Since `\|L\|` is odd, `z⁻¹` is not conjugate to `z`」) |
| (6.8) | ✅ **capstone は無条件・carrier は書籍忠実 (2 点を 2026-08-07 補充)**。書籍 p.33 の (a)(b)(c1)(c2) ⟹ `𝒮` coherent。repo = `sibleySetup_is_coherent : hyp.CoherenceTarget` (`hyp : SibleyDadeHypothesis G L H` のみを取る = 追加仮説ゼロ)。carrier の条項対応: (a) = `H_ne_bot`/`H_normal`/`H_nilpotent`/`split (L = H ⋊ W₁)`/`card_L_odd`/`H_sharp_ti` (⚠ `IsTISubset A L` + `A ≠ ∅` + `L`-不変性 ⟹ `N_G(A) = L` が `set_normalizer_eq_of_nonempty_of_normalizes` で出るので書籍の「with normalizer `L`」と同値) / (b) = `S`/`S_eq` + `dade`/`dade_H_eq_bot` / (c) = `cases` (Frobenius ∨ `Hypothesis46` + `w₂` 素数 + `W₂ ⊆ [H,H]`)。**補充 (b) 2 件**: 書籍は「`τ` は `Ind_L^G` の `ℤ[𝒮,L^#]` への制限」と言うのに repo の `tau` は §4 Dade 写像で、`CoherenceTarget` の `A` も `H^#` だった ⟹ `tau_apply_eq_induce` (TI ⟹ 局所部分群自明 ⟹ 両者は同じ点ごとの規則; §15 の (13.2.e) `H_sharp_tau_eq_induce` の §8 版) と `zSupportedSpan_ne_one_eq_sharp` (`Ind_H^L θ` は正規な `H` の外で消える) を追加し、`CoherenceTarget.toBookForm` で capstone を書籍形 `IsCoherent hyp.tau hyp.S L^#` へ移送。**冗長だが導出可能な 2 フィールド** (債務ではない): `W1_nontrivial` は (c1) `IsFrobeniusGroup.ne_bot_complement` / (c2) `h46.W1_nontrivial` から、`cases` の c2 側 `Nat.Coprime (Nat.card ↥H) (Nat.card W1)` は (4.2.a) Hall 条項 `h46.card_coprime` から出る。carrier の**構成可能性**は `S09_FrobeniusSibley` / `S12_TypeVSibley.typeVSibleyDadeHypothesis` が担保 (posited でない) |

**§6 監査完了 (2026-08-07)**: 全 8 件で**未形式化ゼロ**。補充 3 件・stale 注記訂正 2 件。

得られた一般的教訓 (memory [[textbook-coverage-audit-failure-modes]] に追記すべき型):

1. **「結論が 2 つある定理」は 1 つだけ形式化されがち** — (6.7) は `ψ(z) ∈ ℤ` と合同の 2 結論で、
   番号 cite も AxiomsCheck の headline も合同側だけ見て「(6.7) 済」に見えていた。しかも file
   docstring が「(i) は consumer 側で別途知っている」と**自認**していた ⟹ **docstring の
   "consumers supply X" / "separately known" は部分被覆のシグナル**として読むこと。
2. **`τ` と `A` の同定は statement の一部** — coherence は `(𝒮, A, τ)` の 3 つ組の性質なので、
   「`τ` が書籍の写像か」「`A` が書籍の台集合か」を確認しないと定理の意味が変わる。§5 の
   (5.2.b) `L^#` vs `A` と同型の論点が §6 の (6.8)(b) で再発した (格子側は同じ補題
   `zSupportedSpan_ne_one_eq` で閉じた)。**書籍 p.34 ((6.8) の証明冒頭) が両方を明言している**:
   > By the definition of `𝒮`, `ℤ[𝒮, L^#] = ℤ[𝒮, H^#]`.  Since `H^#` is a TI-subset with
   > normalizer `L`, (5.2.b) holds by [Is], Lemma 7.7.  Moreover, (2.3), Definition (2.5) and
   > [Is], Lemma 7.7, show that `τ` coincides with the Dade isometry relative to `(A, L, G)`.

   ⟹ repo が暗黙にしていた 2 点は、書籍が**明示的な 2 文**として書いていたもの。
   **「書籍の証明の冒頭数文」は statement の一部として読むこと** (仮説の言い換え・同定はそこに置かれる)。
3. **書籍 statement 自体の implicit 仮定** — (6.2) は `B = K` で偽。repo が `B < K` を持つのは
   修理であって債務ではない。**mathcomp が同じ仮説を持たない**ときは、定義 (ここでは
   `coherent` に `ℤ[𝒮,A] ≠ 0` を含めるか) の差を疑う。

### §7 = repo `S09` (書籍 pp.38-43、`pages/peterfalvi-p038..p043.png` 切り出し済) — **監査完了 (2026-08-07)**

全 11 件 ((7.1)-(7.11)) を書籍と逐条突合。**未形式化ゼロ・補充ゼロ**。§4/§5 に続いて元から完全被覆。

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (7.1) Hypothesis | ✅ 忠実 | `S09.Hypothesis71` = (2.2) 仮説 + Dade 写像 `τ` + `IsDadeMap` ((2.5) の方程式)。`χ^ρ` = `chiRho` (`(1/\|H(a)\|)∑_{x∈H(a)} χ(ax)`、`A` 外は 0)、`A^τ` = `hyp.dadeSupport`。TI からの構成 `of_isTISubset` あり。⚠ 書籍は「τ は **Dade isometry**」と言い、repo は等長性を個別定理の仮説 `hiso : IsDadeIsometry` で受ける — 書籍 (2.6) が等長性を与えるので導出可能な仮説 (要確認: (2.6) の形式化を repo が持つか) |
| (7.2)(a) | ✅ 実証明 | `α^{τρ} = α` (pointwise は `chiRho_apply_eq_of_forall_coset` 系、`chiRhoCF_dadeImage_eq`) |
| (7.2)(b) | ✅ **不等式 + 等号条件の両方** | `chiRho_norm_sq_le` (`‖χ^ρ‖² ≤ ‖χ‖²`) と `chiRho_norm_sq_eq_iff_mem_range` (等号 ⟺ `χ ∈ im τ`)。書籍の rider が落ちていない |
| (7.3) | ✅ **不等式 + 等号条件の両方** | `chiRho_integral_inequality` (`(1/\|G\|)∑_{g∈A^τ}\|χ(g)\|² ≥ ‖χ^ρ‖²`) と `chiRho_integral_eq_iff_constant_on_hCoset` (等号 ⟺ 各 `aH(a)` 上で `χ` が定数) |
| (7.4) Hypothesis | ✅ 忠実 | `FamilyHypothesis71`: `L_i`/`A_i` + 各 `i` の (7.1) + `pairwise_disjoint` (`A_i^{τ_i}` が互いに素) + `G0 = G − ⋃_i A_i^{τ_i}` |
| (7.5) | ✅ **実証明 + 一般化** | `family_inequality` = 書籍の displayed 不等式そのまま。⚠ 書籍は `χ ∈ Irr G` だが repo は `‖χ‖² = 1` だけを仮定 (証明が使うのはそれだけ) = **一般化** |
| (7.6) Hypothesis | ✅ 忠実 + **構成可能** | `Hypothesis76`: (7.1) + 等長 + `H ⊴ L` + `A = H^#` + 族 `ζ : Fin (n+1) → CF(L)` + 次数比 `d` + `zeta_induced` (各 `ζ_i` は `Ind_H^L θ`) + `zeta_injective` (相異なる) + `zeta_family_cover` (**全ての** `θ ∈ Irr H` が現れる = 書籍の `T = {Ind θ \| θ ∈ Irr H}` の網羅性)。網羅性を持つのが重要 — (7.7.a) の証明が `CF(L,A)` の基底性を使うため |
| (7.7)(a) | ✅ **実証明** (carrier field だが producer が discharge) | `Hypothesis76.chiRho_decomp` は field だが、`hypothesis76OfFamily` / `hypothesis76OfDade` が **(7.1) データ + `H ⊴ L` + `A = H^#` だけから** 構成し `chiRho_decomp_induced` で証明している (docstring: *"with **no certificate assumed**"*)。名前付き定理 `chiRho_explicit_formula` もある。⟹ posited data ではない |
| (7.7)(b) | ✅ 実証明 | `Hypothesis76.chiRho_norm_sq_double_sum` = 書籍の二重和恒等式そのまま (`(ζ_i,ζ_j) − ζ_i(1)ζ_j(1)/(eh)`; repo は `/(Nat.card L)` = `eh` と同じ)。直交性で潰した形 `chiRho_norm_sq_collapse` も別途 |
| (7.8) 仮説部 | ✅ 忠実 + **構成可能** | `Hypothesis78` (`QuadraticTerm.lean:62`) = (7.6) + `ind1H` (`Ind 1_H` の添字) + `zetaDistinct` (`ζ ∈ 𝒮 ∩ Irr L`, `ζ(1) = e`) + `nu` + `nu_isometry` (書籍の「`ν` は `τ` の `ℤ[𝒮] → ℤ[Irr G]` 等長への拡張」) + **(7.8.c.i) 証明書 field** `chiRho_eq_inner_beta`。⚠ その field は **posited でない**: `hypothesis78OfDade` (`S09_CertificateBasic:101`) が (7.1)+等長 + `H ⊴ L` + `A = H^#` + 誘導族 + `ν` の等長/`τ` 一致 だけから構成し `chiRho_eq_inner_beta_induced` で証明 (docstring: *"with no certificate assumed"*) |
| (7.8)(a) | ✅ 実証明 | `BetaDecomp` (`QuadraticTerm:915`) = 書籍の条項そのまま (`a : ℤ` / `Gamma` / `Gamma_orth_nu` / `Gamma_orth_one` / `orth_one` = `𝒮^ν ⊥ 1_G` / `beta_eq` = displayed 分解 `β = 1_G − ζ^ν + a·weightedNuSum + Γ`)。**構成**は抽象エンジン `betaDecompOfFacts` + Frobenius 実例 `hypothesis78_betaDecomp` (`S09_FrobeniusConjIndex:565`)。各条項の個別証明は `S09_BetaDecompOrthogonality` |
| (7.8)(b) | ✅ 実証明 | `NormEstimates` (`CoherenceFormula:73`) = 2 条項 (`H78.smallIndex` = `2e+1 ≤ h` ⟺ 書籍の `e ≤ (h−1)/2` 下で `1 − e/h ≤ ‖ζ^{νρ}‖²` と `‖Γ‖² ≤ e−1`)。producer = 一般エンジン `normEstimates_of_source_orthogonal` / `normEstimates_of_irreducible_source_data` (源側の直交性・既約性から)。§16 でも `TypeICoherent78Data.normEstimates` が構成 |
| (7.8)(c) | ✅ **(i)(ii) 両方** | (i) `chiRho_eq_inner_beta_on_A` (`CoherenceFormula:1046`) = `χ^ρ(x) = star(β,χ)` for `x ∈ A`。(ii) `chiRho_norm_sq_eq_card_ratio_mul` (`:1064`) = `‖χ^ρ‖² = (\|A\|/\|L\|)·(β,χ)·star(β,χ)` (書籍の `(β,χ)²`; repo の `z·z̄` 形が正しい)。(7.10) が使う帰結 (good-index 界 `(h_j−1)/(e_j h_j) ≤ ‖χ^{ρ_j}‖²`) は `distinguishedNuAt_chiRhoNormSq_ge_of_reverseCoefficient_ne` |
| (7.9) | ✅ 実証明・書籍と一致 | 一般エンジン `conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity` + Frobenius 実例 `hypothesis79_conclusion` (`S09_FrobeniusParity:103`)。結論 = 書籍 p.42 の `(β₁,ζ₂^{ν₂}) ≠ 0 or (β₂,ζ₁^{ν₁}) ≠ 0` そのまま (パリティ経路 `⟨Δ_i,Δ_j⟩` 偶数も含む) |
| (7.10) | ✅ **書籍の displayed 不等式そのまま** | `card_G0_lower_bound` (`S09_FrobeniusCardG0LowerBound:129`): `(\|G₀\|−1)/\|G\| ≥ (e−1)((h−2e−1)/(eh) + 2/(h(h+2)))`。仮説 = `FrobeniusFamily G k` ((a) 各 `L_i` が核 `H_i` の Frobenius 群 / (b) `H_i^#` TI with normalizer `L_i` / (c) `i ≠ j` で `h_i`, `h_j` 互いに素 / (d) `G₀`)。⚠ 書籍は Thompson で `H_i` 冪零を得るが repo も**仮定でなく導出** |
| (7.11) | ✅ 実証明 | `not_trivial_G0` (`:148`): `G₀ = {1}` は矛盾 |

**§7 監査完了 (2026-08-07)**: 全 11 件で**未形式化ゼロ・補充ゼロ**。

- **(7.1) の `IsDadeIsometry` は導出可能**と確認: 書籍 (2.6) は `S04.Hypothesis.fullDadeIsometryData`
  として **(2.2) だけから構成**済 (docstring: *"no longer an interface assumption"*)。個別定理が
  `hiso` を仮説で受けるのは呼び出し規約の問題で、債務ではない。
- **証明書 field は 3 つとも producer が discharge している** ((7.7.a) `chiRho_decomp` /
  (7.8.c.i) `chiRho_eq_inner_beta` / (7.8.a) `BetaDecomp` / (7.8.b) `NormEstimates`)。
  §6 で確立した「carrier field を見たら producer を探す」手順が効いた。
- **§6 で見つけた「結論が 2 つある定理の片方だけ」型は §7 では発生していない** —
  (7.2)(b)/(7.3) の等号条件、(7.8)(c) の (i)(ii) がいずれも揃っている。

### §8 = repo `S10` (書籍 pp.44-49、`pages/peterfalvi-p044..p049.png` 切り出し済) — **監査完了 (2026-08-07、残 1 件 = (8.13)(c3))**

書籍 §8 は番号付き結果 **18 件 ((8.1)-(8.18))**。うち多くは「型」の定義で、監査の問いは
「repo の定義が書籍の条項を全部持っているか」。

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (8.1) 型 `𝓕` の定義 | ✅ 条項一致 | `GroupTheory.TypeFData` (`MaximalSubgroupType.lean:82`)。(a) `H = M_F ≠ 1`・`U ≠ 1`・`M = H ⋊ U` = `H_eq`/`H_nontrivial`/`U_nontrivial`/`complement` / (b) `U₁ ⊴ U` 可換・`C_U(x) ⊆ U₁` (`x ∈ H^#`) = `U1_normal`/`U1_commutative`/`centralizer_le_U1` / (c) `U₀ ≤ U`, `exp U₀ = exp U`, `HU₀` が核 `H` の Frobenius = `U0_le`/`exponent_eq`/`frobenius_HU0` |
| (8.2)(a) | ✅ 実証明 | `S10.typeF_card_U0_eq_exponent` (`\|U₀\| = exp(U)`; [BG] Prop 3.9 経由の Z-群 ⟹ `exp = card`) |
| (8.2)(b) | ⚠ **片側だけだった → 2026-08-07 に同値を補充** | 書籍は「`M` が核 `H` の Frobenius **⟺** `U` の Sylow 部分群が巡回」。repo は `⟸` 側のみ (`typeF_frobenius_of_card_eq_exponent` = `\|U\| = exp(U)` 版、および S14 にあった `IsZGroup` 版)。⟹ `S10.typeF_frobenius_iff_isZGroup` を追加 (`⟹` 側 = 奇数位数 Frobenius 補元は Z-群 [BG] Prop 3.9)。併せて `⟸` 側の一般形を `S10.typeF_frobenius_of_isZGroup` として §8 に置き、**S14 にあった同証明の重複を削除** |
| (8.2)(c) | ✅ 実証明 | `S14.typeF_inertia_inf_le_U1` (`I(θ) ⊓ U ≤ U₁` for `θ ∈ Irr H ∖ {1}`) |
| (8.3) Type I の定義 | ✅ 条項一致 | `TypeIData` = `typeF` + 3 択 (`H^#` TI / `H` 可換 rank 2 / 全ての `p \| \|H\|` で `exp U \| p−1` かつ ある `p` で `O_{p'}(M)` 巡回) |
| (8.4) 型 `𝒫` の定義 | ✅ 条項一致 (2 点の設計差は導出可能) | `TypePData`。(a) `M = M' ⋊ W₁`, `W₁ ≠ 1` 巡回 = `M_complement`/`W1_nontrivial`/`W1_cyclic` — ⚠ **書籍の「Hall」条項は field でない**。代わりに `W_cyclic` (= `W = W₁W₂` 巡回) を持つ (Hall の帰結)。Hall 性は極小単純奇の設定で `S12.typePData_W1_isHallSubgroup_kappa` が**定理として証明**している / (b) `U ≤ M'` 冪零・`W₁` が正規化・`M' = H ⋊ U` = `U_le`/`U_nilpotent`/`W1_normalizes_U`/`derived_complement` / (c) `H` 非巡回・`M'' ⊆ HC_M(H) = F(M) ⊆ M'` = `H_noncyclic`/`secondDerived_le_fitting`/`fitting_eq` (⚠ `fitting_eq` は **(8.5)(a) の形** `F(M) = H·C_U(H)` で持つ — 書籍の (8.4.c) と (8.4.b) から同値。⟹ (8.5)(a) は projection で、producer が discharge) / (d) `W₂ ≠ 1` 巡回 `≤ H ⊓ M''`・`C_{M'}(x) = W₂` (`x ∈ W₁^#`) = `W2_*`/`centralizer_W1` / (e) `W = W₁W₂`, `V = W ∖ (W₁∪W₂)`, 任意の空でない `X ⊆ V` で `N_G(X) = W` = `W_eq`/`normalizer_V` |
| (8.5) | ✅ (a) は carrier field 化 / (b)(c) は要確認 | (a) `F(M) = HC_U(H)` = `TypePData.fitting_eq` (上記)。(b) `[U,U]` は `H` を中心化・`U ≠ 1` なら `U` は `H` を中心化しない / (c) `V` は正規化群 `W` の TI-subset = `normalizer_V` + TI。⬜ (b) の 2 条項と (c) の TI 部分の突合は次回 |
| (8.6) Type II/III/IV の定義 | ✅ 条項被覆 (TI 条項の所在が違う) | `TypeIIData`/`TypeIIIData`/`TypeIVData` = `typeP` + `TypePNontrivialCore` + 型別条項。(b II) `U` 可換・`N_G(U) ⊄ M`・`M'` が型 `𝓕` で `(M')_F = H` = `U_commutative`/`normalizer_not_le`/`derived_typeF`/`derived_fitting_eq` ✓ / (b III)(b IV) ✓。⚠ **(8.6)(a) の TI 条項の読み替え**: 書籍は「`F(M)^#` が `G` の TI-subset」だが `TypePNontrivialCore` は「`M_F^#` が TI」を持つ (Dade base が使う形)。**書籍の形は別に定理として在る** — `S13.fittingIsTI_of_isTypeNonI` が `FittingIsTI M = IsTISubset (F(M)^#) (N_G(F(M)))` を**全ての非 Type-I 極大部分群**について証明 (BG Thm 15.7(a) / type-`P₂` 経路)。⟹ 被覆済 (carrier の `M_F^#` 版は書籍にない**追加**条項で、producer が discharge) |
| (8.7) Type V の定義 | ✅ 条項一致 | `TypeVData` = `typeP` + `U = ⊥` + 3 択 ((a) `H^#` TI / (b) `\|W₁\| \| p−1` かつ `O_{p'}(H)` 巡回 / (c) `\|O_p(H)\| = p³`, `\|W₁\| \| p+1`, `O_{p'}(H)` 巡回) |
| (8.8) | ✅ 実証明 (BG Thm I 経由) | `S10.maximalSubgroup_type_dichotomy` (型言語) + `S14.theorem88_dichotomy` (W/S/T データ込み)。(b1)-(b4) の条項は BG Theorem I から |
| (8.9) | ✅ **2026-08-07 に形式化** (本キャンペーンのステップ 1) | `S10_Theorem88CaseB.Theorem88CaseBData.typePData_W2_eq` + 内在形 `derivedInG_inf_centralizer_W1_eq`。副産物として (8.8.b) の carrier に 6 条項を補充 |

**(8.10)-(8.16) の突合 (2026-08-07、続き)**:

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (8.10) 記法 | ✅ 対応あり (⚠ `A(M)` の型別読み替えに注意) | `M_s` = `mainSubgroup M tau` (type I/II/V で `M_F`、III/IV で `M'`)、`A₁(M) = M_s^#` = `sharpSubgroup`、`A(M)`/`A₀(M)` = `typePA`/`typePA0` (III/IV/V) と `centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)` (type II)。⚠ **repo の `typePA M` は `M^#` 上の和で定義**され `= (M')^#` に潰れる (`typePA_eq_sharpSubgroup_derivedInG`) — これは書籍の `A(M) = ⋃_{x∈M_s^#} C_{M'}(x)^#` と **types III/IV/V でのみ一致** (そこでは `M_s = M'`)。**type II では書籍どおりの honest な形**を `S12_TypeIIDadeBase` が別に使う |
| (8.11) | ✅ 2 条項とも | `N_G(P) ⊆ M` (`S10_StructureSetup:691`) と `M_F`/`M_s` が `G` の Hall (`hall_maxNilpotentNormalHall_and_mainSubgroup`、BG Prop 16.1 + Thm A(1) 経由) |
| (8.12)(a) | ✅ BG Theorem B(1) 経由 | `theoremB_U_sylow_abelian_rank_le_two` (proved)。type-I 極小反例への適用は `counterexample_P0_K_structure` |
| (8.12)(b) | ✅ 忠実形 + 型一律形 | `S10_StructureSetup:796` (faithful) / `S10_MinimalSimpleStructure:589` (type-uniform: 任意の極大 `T`) |
| (8.12)(c) | ✅ BG Theorem B(5) | `A(M) − M_σ` が TI = `S16.theoremB_A_minus_Msigma_isTISubset` |
| (8.13)(a)(b)(c1)(c2) | ✅ (a) は台別・(b)(c2) は型一律 | (a) `V^M`-台 / `σ`-sharp 台 / type-`P₁` `A₀` 台の 3 形 (`S10_MinimalSimpleBasic:560,593,731`)。(b) `S10.escapingCentralizers_control` + 型一律 `escaping_typeA_mem_A1`。(c1) の一意極大は同 control 内、(c2) は `coprime_FT_signalizer_centralizerIn_typeA` (型一律) |
| (8.13)(c4) | ✅ 前半 + 後半とも | 前半「`L` は Type I か II」= `escapingCentralizers_control`。後半「`L` が Type II なら `M` は核 `M_F` の Frobenius 群」= BG Theorem II packaging (`S16_MainResults/TamelyImbedded:141` / `TheoremIIPackaging:393` の `FrobeniusTypeIWithNonTIFitting M`) |
| (8.13) の `X` の範囲 | ✅ 3 型すべて | 書籍は `X = A(M)`/`A₀(M)` を任意の型で許す。repo は `A₁(M)` (全型) + type-`P₁` の `A₀(M)` (`escapingCentralizers_control`) + type I の `A(M)` (`escaping_typeIA_mem_A1`) + **type II は退化** (2026-08-07 補充): (8.16) より `A(S)`/`A₀(S)` は TI ゆえ `D = ∅` — `A(S)` 級は既存の `typeII_centralizer_le_of_mem_centralizerSupport`、`A₀(S)` 級を `S12.typeII_centralizer_le_of_mem_A0` として追加 |
| **(8.13)(c3)** | ⬜ **§8 唯一の未形式化** → [issue 0174](../../issues/0174-peterfalvi-813-c3-support-membership.md) | `x ∈ A(L) − A₁(L)` (`x ∈ D`, `C_G(x) ⊆ L`)。書籍は (8.18)(a) をこれ経由で導くが、repo の型一律 (8.18)(a) は σ-disjointness + (8.12.b) 一意性で直接証明しているので **consumer 0**。BG Theorem D(4) の rich predicate に相当成分が在るかの確認が入口 |
| (8.14) 記法 | ✅ | `supportKernel` (`R(x)`: escaping 集合上は BG Theorem-D signalizer、外は `1`) と `thickenedSupport` (`⋃_{x∈X}(xR(x))^G`) |
| (8.15) | ✅ 3 claim とも | claim 1 = `M = N_G(A)` + (2.2) 成立 (`DadeSupportHypothesisData`、`A = A₁(M)` は全型)、claim 2 = type `𝒫` の (4.6) 成立 (`S12.Hypothesis.toHypothesis46` — `Hypothesis46` の**初の実例**)、claim 3 = subcoherence (`inducedKernelFamily_subcoherent` / 型一律 `inducedNonKernelFamily_subcoherent`) |
| (8.16) | ✅ **type II の 3 集合とも** | `typeII_centralizerSupport_isTISubset` (`A(S)` の TI、書籍の honest な `A(S) = ⋃_{x∈S_σ^#} C_{S'}(x)^#`)、`typeII_A0_isTISubset` (`A₀(S)`)、`A₁(S) = S_F^#` は carrier の (8.6.a) kernel TI 条項。⚠ **`S10_StructureSetup:910` の「(8.16) RETIRED — false-as-stated」注記は、`A(M) = (M')^#` と誤読した版についてのもの** ((8.10) より `A(M) = (M')^#` は types III/IV/V のみ)。書籍の (8.16) 自体は type II の honest な `A(S)` で成立し、上記のとおり証明済 — **注記だけを見て「(8.16) は無い」と誤診しないこと** |

**(8.17)/(8.18) の突合 (2026-08-07)**:

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (8.17) | ✅ (a)(b)(c) とも | `BGTheoremECoverData` (`S10_MinimalSimpleStructure:958`) が (a) `π(G)` の被覆+互いに素 (`primeFactors_cover`/`primeFactors_disjoint`) と (b) 濃度公式 `\|𝒞_G(M̃ᵢ)\| = (\|(Mᵢ)_s\|−1)·\|G:Mᵢ\|` (`cover_card`) を持ち、(c) は `BGTheoremETypeICovering` ((8.8.a) の場合) と `BGTheoremENonTypeICovering` ((8.8.b) の場合、例外集合 `Ẑ = zTilde K K*` 付き)。⚠ **faithful 化の履歴**: 旧 `thickenedA1 (Mᵢ) (Mᵢ)` は `(Mᵢ)_F` 基準の kernel を使い (8.14) の per-`x` signalizer `(N[x])_F` と食い違うため、BG Lemma 14.5 の `𝒞_G(M̃ᵢ)` に置換済 (issue 8021) |
| (8.18)(a) | ✅ **書籍そのまま・型一律** | `escaping_supported_of_A1_conj_mem_typeA` (`:664`): 非共役な極大 `S`,`T` に型仮定なしで「`x ∈ A₁(S)` かつ ある共役 `g·x·g⁻¹ ∈ A(T)` ⟹ `x` は `A(S)` の escaping 点かつ `C_G(x) ≤ g⁻¹Tg`」。証明は σ-disjointness ((8.17.a)) + (8.12.b) 型一律版 |
| (8.18)(b) | ✅ 型一律 | `:753` (+ type-I pair 特殊化 `:856`) |
| (8.18)(c) | ✅ 型一律 | `:873` (mixed `Ã₁ ∩ Ã` disjointness、+ type-I pair `:932`) |

⬜ **§8 の残り = (8.13)(c3) の 1 件のみ** ([issue 0174](../../issues/0174-peterfalvi-813-c3-support-membership.md))。

### §9 = repo `S11` (書籍 pp.50-57、`pages/peterfalvi-p050..p057.png` 切り出し済) — **監査完了 (2026-08-07、残 1 件 = (9.11) の type-free 化)**

書籍 §9 = **(9.1)-(9.11)** + (9.11) の sub-part (9.11.1)-(9.11.8)。型 II/III/IV の極大部分群の
構造解析で、repo は `S11_MaximalII_III_IV/**` + `S13_CoreStructure` + 共有 infra
(`GroupTheory/WielandtFixedPoint.lean` ほか) に分散。

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (9.1) | ✅ **本体 + "In particular" 2 条項とも** | `GroupTheory.wielandt_fixedPoint_frobenius`: `\|C_H(UE)\|^{\|E\|}·\|H\| = \|C_H(E)\|^{\|E\|}·\|C_H(U)\|` (**指数 `\|E\|` が正しく入っている** — pdftotext は上付きを落とすので実害が出やすい箇所、memory [[pdftotext-drops-superscripts]])。第 1 corollary `wielandt_fixedPoint_trivial_E_fixed` (`C_H(E) = 1 ⟹ C_H(U) = H`)、第 2 corollary `wielandt_fixedPoint_trivial_U_fixed` (`C_H(U) = 1 ⟹ \|H\| = \|C_H(E)\|^{\|E\|}`)。証明は chief series 帰納 + 各 chief factor 上の次元恒等式で**無条件** (Wielandt の不動点定理を FT なしで使う書籍の注意も守られている) |
| (9.2) Hypothesis | ✅ carrier あり | 型 II/III/IV の極大 `M` と (8.4) の `H`,`U`,`W₁`,`W₂`,`q = \|W₁\|` — `S11_MaximalII_III_IV` の setup データ (`WielandtSetupBasic` の `data`) |
| (9.3) | ✅ **2 分岐とも書籍そのまま** | `typeII_III_IV_order_relations` (`WielandtSetupBasic:649`): type II で `C_H(U) = 1` ∧ `\|H\| = \|W₂\|^q`、type III/IV で `∃ p` 素数 `\|W₂\| = p` ∧ `C_H(UW₁) = 1` ∧ `\|H\| = p^q·\|C_H(U)\|` |
| (9.4) | ✅ carrier が条項一致 | `ChiefFactorData` (`WielandtSetup:738`): `H₀ < H` + `M ≤ N(H₀)` + `H̄ = H/H₀` が elementary abelian `p` (`quotient_elementaryAbelian`) + chief factor (`quotient_chiefFactor`) + `\|H\| = p^q·\|H₀\|` (`quotient_order`) + `U` が `H̄` を中心化しない。type II で `p = \|W₂\|` かつ `H₀ = 1` は `typeII_chiefFactor_H0_trivial` |
| (9.5) Hypothesis | ✅ 記法が揃う | `H̄`/`C = C_U(H̄)`/`Ū = U/C`/`u = \|Ū\|`/`W̄₂ = C_H̄(W₁)`/`U' = [U,U]`/`C' = [C,C]`、`τ` = (A(M),M,G) の Dade 等長、`𝒳 = {χ ∈ Irr HU \| H ⊄ Ker χ}`/`𝒮 = Ind_{HU}^M 𝒳` と `𝒳(Y)`/`𝒮(Y)` — `S11_MaximalII_III_IV` の `chars` データと `sOf` 系 |
| (9.6) | ✅ 4 条項とも | `U ≠ C` / `H̄` が chief factor / `\|W̄₂\| = p` / `\|H̄\| = p^q`。算術段は `GroupTheory.coprimeFrobeniusAction_card_eq_prime_pow` ((9.1) 系から `\|H̄\| = \|C_H̄(W₁)\|^q` と `\|W̄₂\| ∣ p` で確定) |
| (9.7) | ✅ **二分律 + 両ケースのデータ** | `S11.clifford_dichotomy` + carrier `CliffordCaseAData`/`CliffordCaseBData`。case (a) = `q` 個の位数 `p` 因子 (`exists_supIndep_aInvariant_family_of_iSup`) + `a ∣ p−1` (`aInvariantRestrictAut_range_card_dvd`)。case (b) = `U` 既約 + Galois 体モデル (`S11_GaloisFieldModel`: `F ≅ GF(p^q)`、`U* ≤ F*`、`η : W₁ ↪ Aut F` と twist 恒等式) + **書籍の "Furthermore" 3 条項** (`Ubar_cyclic` / `u_coprime_p_sub_one` / `u_dvd_norm_quotient` = `u ∣ (p^q−1)/(p−1)`) |
| (9.8) | ✅ (a)(b)(c)(d) とも | (a) `a ∣ χ(1)` on `𝒳(H₀)` (`S11_SingleFactorCentralizer:319`、member 版 `:1129`) / (b) 可約メンバーの分類と次数 `qu` (`S12_HcBound:237,419,548`) / (c) `𝒮(H₀C)` の次数 `qu` 既約メンバー (`S15_CharacterDegreeSupply:129`、`HC` の線型指標から誘導) / (d) 次数 `qa` 既約が `(p−1)/a · \|U\|/(a\|U'\|)` 個以上 (`S11_SingleFactorCentralizer:478,554` の `a²\|U'\| ∣ (p−1)\|U\|` と exact count) |
| (9.9) | ✅ (a)(b)(c) とも | (a) `u ∣ χ(1)` on `𝒳(H₀)` と `𝒳(H₀C′)` 上の一様次数 `χ(1) = u` (`S13_CoreStructure:716` の `caseB_degree_qu`、Clifford 対応の次数は `CliffordSingleOrbit:594`) / (b) `𝒮(H₀)`・`𝒮(H₀C)` がちょうど `p−1` 個の可約メンバーを持ち次数 `qu` (`S11.reducible_count_sOf_H0supC` + `S12_HcBound:237`) / (c) 「`𝒮(H₀C′)` に既約が無い ⟹ `C = 1`」= `caseB_no_irreducible_forces_C_bot` (`CaseBXi:817`)、`u = (p^q−1)/(p−1)` は (9.10) の結論に含まれる |
| (9.10) | ✅ **4 結論とも + case (b) の導出込み** | `S11.exceptional_case_frobenius_realization_of_trigger` (`ThetaCountAssembly:1151`): 「`𝒮(H₀C′)` に次数 `qu` の既約が無い」だけを仮定して (i) `H̄Ū` の固定点自由性 (= `H̄U` が核 `H̄` の Frobenius) (ii) `u = (p^q−1)/(p−1)` (iii) `IsCyclic U` (iv) **type II なら `HU` が核 `H` の Frobenius** を返す。書籍の「Then case (9.7.b) holds」は定理内部で**導出** ((9.8.c) の次数 `qu` 既約が case (a) を否定) |
| (9.11) | ⚠ **types III/IV は閉、type-free 版は case (a) の 2 仮説が残る** → [issue 0175](../../issues/0175-pf-911-section9-casea-descent.md) | 書籍は Hypothesis (9.5) (= type II/III/IV) の下で `𝒮(H₀C′)` coherent。repo: **types III/IV は `S13.coherent_sOf_H0Cprime` で閉じている** (FT の live path)。type-free の §9 版 `S11.sOf_nineEleven_coherent` は二分律の両枝を通すが case (a) 側で `h2` (degree-`qa` base coherence) と `hrefuteEq` (maximality refuter) を仮説で受ける。[closed issue 1045](../../issues/closed/1045-pf-9-11-section9-level.md) の消化記録が「開いた carrier はちょうど 1 本 = `CaseASevenEightRefutation`」と結論し、§13 側の対応物が sorry-free で証明済・type 依存点は 4 箇所で**すべて type-free counterpart が在る**ので **descent 作業であって未解決数学ではない**。case (b) 側は無条件 (`sOf_caseB_coherent` / `caseB_coherent_sOf_cprime`) |
| (9.11.1)-(9.11.8) | ✅ 8 件すべて repo に実体 | cite 数 40-130/件。(9.11) case (a) の内部段 (TI witness・inertia 入力・count 入力・norm bound ほか) で、上記 descent の材料 |

⚠ **AxiomsCheck の (9.11) block のコメントが stale**: 「the remaining item of issue 1045」と
書いてあるが issue 1045 は closed。issue 0175 で更新する。

⚠ **書籍の (9.8)(b) を pdftotext で読むと `μ_j ∉ 𝒮(H₀C)` に見える** (実際は `μ_j ∈ 𝒮(H₀C)`)。
ページ画像 p053 で確認した — 否定の有無が反転する OCR 崩れは危険なので、条項の突合は必ず画像で。

## 4. 未着手の census

- **Part II (Suzuki の定理 A、書籍 pp.97-134)** — `Proposition N` / `Lemma N` の**章内リセット
  番号**なので Part I の機械 census が効かない。repo 側は `Appendices/Suzuki/` に
  Ch.I–IV + FirstCase step 1-17 + PSU3 が実装済で、`theoremA` / `theoremB` は 2026-08-07 に
  axiom-clean で `AxiomsCheck` 登録済。**逐条 census は未実施**。
- **補章** — Huppert (pp.135-136) / On Near-Fields (pp.137-138) / On Suzuki 2-Groups
  (pp.139-143) / The Feit–Sibley Theorem (pp.144-150)。repo に対応実装あり、逐条 census 未実施。

## 5. 参照

- 書籍テキスト: `references/peterfalvi/pdftotext/*.txt`
  ⚠ **表示数式は OCR レイヤが壊れており復元不能** — 式・添字の確定は `references/peterfalvi/pages/*.png`
  (無ければ `pdftoppm` で切り出して**残す**)。
- Coq 併読: `coq/theories/PFsection<N>.v` (N = 書籍 result 章番号、`S10` ではなく `8`)。
