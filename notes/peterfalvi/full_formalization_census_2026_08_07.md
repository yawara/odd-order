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

### §10 = repo `S12` (書籍 pp.58-63、`pages/peterfalvi-p058..p063.png` 切り出し済) — **監査完了 (2026-08-07、未形式化ゼロ)**

書籍 §10 =「Maximal Subgroups of Types III, IV and V」= **(10.1)-(10.11)** + (10.10) の
sub-part **(10.10.1)-(10.10.4)** の計 15 件。repo は `S12_*` 系に分散。
**全 15 件に書籍強度の実体あり**。うち 2 件は本監査で書籍の形へ補充した (下表 ⭐)。

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (10.1) Hypothesis | ✅ carrier が条項一致 | `S12.Hypothesis` (`S12_MaximalIII_IV_V_Core/Hypothesis.lean:349`): `maximal` + `typeP : TypePData M` ((8.4) の `M'`,`M''`,`W₁`,`W₂`,`V`) + `type_alt : III ∨ IV ∨ V` + `dadeData` ((8.15) の `A₀(M)` Dade 支持データ)。`τ`/`𝒮`/`A₀`/`w₁`/`w₂` は**すべて honest projection** (free field でない): `tau = dadeIntegralCharacterMap dadeData.dade`、`Sset = inducedFamily M = {Ind_{M'}^M θ ∣ θ ∈ Irr M', θ ≠ 1}`。「(8.15) により (4.6) が `L=M`, `H=K=M'` で成立」= `Hypothesis.toHypothesis46`。⚠ **設計差**: 同じ文の「(5.2) も成立」は独立 carrier を持たず Dade datum 経由 (`S07.coherentEqualDegree_fromDade` / `S06.CertainTypeSubcoherent` (5.3.b)) で実現 — (5.2) が供給する対象 (`ℤ[𝒮,A₀]` 上の等長 `τ`・メンバーの直交性) はすべて `hyp.tau` + `inducedFamily` 直交性から出る |
| (10.2) | ✅ 3 条項とも | `exists_zeta_in_inducedFamily_degree_w1`: `∃ ζ`, `ζ ∈ inducedFamily M` ∧ `IsIrreducibleCharacter ζ` ∧ `ζ(1) = \|W₁\|`。`Hypothesis` 版は `exists_zeta_degree_w1` |
| (10.3) | ✅ 5 条項とも | `w2_prime_and_parameter_independence`: `w₂` 素数 / `1 < d` / `∀ i j ≠ 0, μ_{ij}(1) = d` (**`i` と `j` の両方**に独立) / `∀ j j' ≠ 0, δ_j = δ_{j'}` / `n·w₁ = d − δ` (`n : ℕ` なので `n = (d−δ)/w₁ ∈ ℕ`)。`w₂` 素数の単体は `Hypothesis.w2_prime` — 書籍どおり (8.8)→(8.6.a) 経由で、**(10.10) を経由しない非循環ルート** |
| (10.4) Hypothesis | ✅ (a)(b) とも | (a) = `CharacterParameters` (`ζ,d,δ,n` + (10.3) の恒等式群)、(b) = `CoherentHypothesis` = `S07.IsCoherent hyp.tau hyp.Sset hyp.A0` で `τ₁ = coherent.extension` (`ℤ[𝒮]` 上の等長 + `ℤ[𝒮,A₀]` 上で `τ` と一致)。**2026-08-07 の清掃**: 未消費の opaque `Prop` データフィールド 2 本 (`typeV_parameter_formula` / `typeV_coherence_formula`、3 producer が `True` を入れるだけ) を削除 |
| (10.5) | ✅ 2 条項とも | 支持半分 = `alpha_support` (`CharacterParameters.alpha_support` フィールドでもあり、producer が `muGrid_alpha_support` で discharge)、Dade 像半分 = `alpha_tau_image` (`α_{ij}^τ = δ(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`)。7 つの pin (`hmu`/`hos`/`hzS`/`hz1`/`hzconj`/`hδpm`/`hδj`) は `exists_charParameters_full` が全部 discharge |
| (10.6) | ✅ (a) の 2 恒等式 + (b) | (a) 第 1 = `muColumn_tau1_pin` (= `tau1_values_and_norm_bound` 第 1 連言、`μ_j^{τ₁} = δ∑_i ω_{ij}^σ`)、(a) 第 2 (書籍 "Also") = **`tau_muColumnZero_sub_zeta_eq`** (`(μ_0 − ζ)^τ = ∑_i ω_{i0}^σ − ζ^{τ₁}`、書籍と同じ `∑_i α_{ij} = (μ_j − dζ) − δ(μ_0 − ζ)` 経由)、(b) = `zeta_tau1_norm_ge_one` (**書籍より強い**: `g ∉ Ã(M)` かつ `ord g` が `w₁` と互いに素なら `ζ^{τ₁}(g)` は**奇整数**、ゆえに `\|·\| ≥ 1`)。⚠ (a) 第 2 の docstring が「(10.6)(b) reduction identity」と誤ラベルだったので訂正 (書籍では (10.6)(a) の第 2 文; (10.6)(b) 証明の STEP 1 でもある) |
| (10.7) | ✅ | `typeII_HU_frobenius_of_coherent'`: Hypothesis (10.4) の下で type-II 極大 `S` の `[S,S]` は核 `S_F` の Frobenius 群 (`IsFrobeniusGroup ↥(derivedInG S) (H.subgroupOf _) (U.subgroupOf _)`、`H = S_F`)。⚠ **packaging 差**: `S` 側を `data : TypesIIIIIIVSetup S` で受けるが、これは `typesIIIIIIVSetup_of_isTypeII hM hSII` により `maximal + IsTypeII` から構成可能 (実際 `S12_Noncoherence:125` は inline で構成している) |
| (10.8) Theorem | ✅ | `S_not_coherent_unconditional`: Hypothesis (10.1) の下で `¬ Nonempty (S07.IsCoherent hyp.tau hyp.Sset hyp.A0)` |
| (10.9) | ⭐ **2026-08-07 に書籍の形へ補充** | 従来 repo にあったのは**直交条項だけ** (`residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2`、(11.9.b) 消費側の形) と、**coherence を仮定した**特殊化 (`orthogonality_of_w1_lt_w2`、`χ = ζ^{τ₁}` まで同定)。書籍 (10.9) は Hypothesis (10.1) だけの下で `(μ_0 − ζ)^τ = ∑_i ω_{i0}^σ − χ`, `χ ∈ ℤ[Irr G]`, `χ ⊥ (Irr W)^σ`, `‖χ‖² = 1` の **3 条項** ⟹ **`exists_residual_of_w1_lt_w2`** を新設 (coherence-free、axiom-clean)。`‖χ‖² = 1` は `‖(μ_0−ζ)^τ‖² = ‖μ_0−ζ‖² = w₁+1` (Dade 等長) と σ-grid 正規直交性から `w₁ − w₁ − w₁ + (w₁+1)`。coherence-free であることが (10.8) で `𝒮` が非 coherent な (11.9.b) で使える理由 |
| (10.10) Theorem | ✅ | `no_typeV_maximal_unconditional` |
| (10.10.1) | ✅ 2 条項とも | `typeV_param_arithmetic`: `p = 2w₁ − 1 ∧ w₁ < p` (純算術。入力は `w₁ ∣ p+1` と (6.5.a) の `p² ≤ 4w₁²+1`)。`w₁ < w₂` は `p = w₂` から |
| (10.10.2) | ⭐ **2026-08-07 に個数を書籍の形へ補充** | `d = p` (`muGrid_degree_eq_prime_of_card_eq_prime_cube`) / `δ = −1` (`delta_eq_neg_one`) / `n = 2` (`n_eq_two`) / `𝒮 = 𝒮₁ ∪ {μ_j}` (`mem_SHCSet_or_eq_muGrid_columnSum_of_card_eq_prime_cube`) / `μ_j(1) = d·w₁` (`muColumn_apply_one`) / `W₂ = H′ = M″` (`W2_eq_secondDerivedInAmbient_of_card_eq_prime_cube`)。**`\|𝒮₁\|` は従来 statement に `8 ≤ \|𝒮₁\|` しか出ておらず**、書籍の `\|𝒮₁\| = (p²−1)/w₁` は証明内部の `hcardeq` に埋もれていた ⟹ `w1_mul_SHCcount_add_one_eq_of_card_eq_prime_cube` (`w₁·\|𝒮₁\| + 1 = p²` = 書籍の除算を払った形) と `SHCcount_eq_of_card_eq_prime_cube` (`\|𝒮₁\| = 4(w₁−1)`) を新設し、`eight_le_…` をその数値系に降格 |
| (10.10.3) | ✅ 3 条項とも | `τ₁` の存在 = `SHC_isCoherent` ((5.7) equal-degree 経由)、支持 = `muGrid_alpha_support`、Dade 像 = `SHC_tau_muGridAlpha_eq_of_eight_le_SHCcount` (`α_{ij}^τ = δ(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`、`ζ ∈ 𝒮₁`) |
| (10.10.4) | ✅ | `typeV_caseC_coherence_engine : S07.IsCoherent hyp.tau hyp.Sset hyp.A0` |
| (10.11) | ✅ 第 1・第 2 主張とも | 第 1 = `theorem88_caseB_prime_orders` (case (b) で `\|W₁\|`,`\|W₂\|` 素数)、第 2 = `S11.typeII_sSet_coherent` ((a) `p = \|W₂\|` ∧ `\|H\| = p^q` ∧ `H` 基本可換、(b) Hypothesis (9.5) の `𝒮` が coherent) |

⚠ **OCR 注意**: §10 は pdftotext の崩れが激しい ((10.5) の `α_{ij} = μ_{ij} − δμ_{i0} − nζ` は
`OL{J= fi>ij—Sfi>io — n(.` になる)。全条項をページ画像 p058-p063 で確定した。

📎 **副産物 (ファイル粒度)**: 補充で `S12_TypeVCaseC.lean` が 1515 行になったので
`S12_TypeVColumnCoherence.lean` (985 行、(10.10.3)/(10.10.4) の列指標 + coherence engine) と
`S12_TypeVCaseC.lean` (549 行、(10.10.2) の `p³` 構造パッケージ) に prefix-split し、
`OddOrder.lean` に配線した。

### §11 = repo `S13` (書籍 pp.64-68、`pages/peterfalvi-p064..p068.png` 切り出し済) — **監査完了 (2026-08-07、未形式化ゼロ)**

書籍 §11 =「Maximal Subgroups of Types III and IV」= **(11.1)-(11.9)** + (11.8) の sub-part
**(11.8.1)-(11.8.6)** の計 15 件。**全 15 件に実体あり**。本監査の補充は「書籍は Hypothesis (11.2)
だけの下で述べるのに repo は (11.3) の非coherence をパラメータで受けていた」6 件の無条件化。

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (11.1) | ✅ | `prime_pow_gt_four_mul_sq_add_one`: `p ≠ q` 奇素数 ⟹ `4q² + 1 < p^q` (純算術、`3^x > 4x²+1` の帰納) |
| (11.2) Hypothesis | ✅ carrier が条項一致 | `S13.Hypothesis` (`S13_MaximalIII_IVBasic.lean`): `base` = (10.1) / `type_alt` = III ∨ IV / `chief` = (9.4) を満たす `H₀` (`chief.H0`) / `C` + `C_eq_centralizer` = `C_U(H)` / `Hprime`,`Uprime` = `H'`,`U'` / `SOf` = `𝒮(X)` (`S08.inducedKernelFamily` に pin、`SOf ⊥ = base.Sset`) / `p = \|W₂\|`,`q = \|W₁\|` は projection。**2026-08-07 の清掃**: 未消費の opaque `Prop` フィールド 3 本 (`notOrthogonalFormula` / `finalOrthogonalityFormula` / `caseB_of_97`、producer が `True` を入れるだけ) を削除し、構造 docstring を書籍の条項列挙に差し替え |
| (11.3) | ✅ **無条件** | `S_H0C_not_coherent_unconditional`: `𝒮(H₀C)` は coherent でない。書籍どおり (6.3) → (10.8) 経由 |
| (11.4) | ⭐ **2026-08-07 に無条件化** | `coherent_quotient_bound` (`S13_NonGaloisExclusion`): `H₁ ⊴ M`, `H₁ < M'`, `𝒮(H₁)` coherent ⟹ `\|M' : H₁\| ≤ 2q\|U : C\| + 1` (書籍の `2q\|U/C\| ≥ \|M'/H₁\| − 1` を減算なしで)。旧 `coherent_quotient_bound_of_noncoherent` は `hnc` 受け |
| (11.5) | ⭐ **2026-08-07 に無条件化** | `secondDerived_eq_HC`: `M'' = HC` |
| (11.6) | ⭐ **2026-08-07 に無条件化、4 条項とも** | `core_structure_unconditional`: `H` が `p`-群 ∧ `U` が `H₀` を中心化 ∧ `H₀ = H'` ∧ `C = U'`。第 2 条項は元から無条件 ((9.6)/(9.1) 経由の `U_centralizes_H0`) |
| (11.7) | ⭐ **2026-08-07 に無条件化、3 条項とも** | `H_elementaryAbelian_unconditional`: `H` は基本可換 `p`-群 ∧ `\|H\| = p^q` ∧ `H₀ = 1` |
| (11.8) | ⭐ **2026-08-07 に無条件化** | `zeta_residual_not_orthogonal_unconditional`: 書籍の `∀ ζ ∈ 𝒮(HC)` 形。`𝒮(HC)` = 次数 `q = w₁` の既約メンバー (= repo の `SHCSet`) で、**列**-`0` 残差 `(μ₀ − ζ)^τ − ∑_{0≤i<q} ω_{i0}^σ` が `(Irr W)^σ` に直交**しない**。旧 `zeta_residual_not_orthogonal_H0C_of_refuter` は (11.5)/(11.7)/(11.3) を 3 つとも仮説で受けていた |
| (11.8.1) | ✅ 3 条項とも | `charParam_d_eq_u` (`d = u`) / `charParam_delta_eq_one` (`δ = 1`) / `card_SHCSet_filter_eq_charParam_n` (`\|𝒮₁\| = n = (u−1)/q`; 一般形の軌道数え `card_abelianization_derived_eq_w1_mul_card_SHCSet_add_one` は §10 (10.10.2) と共有) |
| (11.8.2) | ✅ | `muGridAlpha_tau_residual_norm` + `muGridAlpha_tau_proj_a_mem` (`a ∈ {0,1,2}`) + `charParam_a_mem_of_norm_ineq` (`\|𝒮₁\|a² − 2an ≤ 2` の算術) |
| (11.8.3) | ✅ 2 条項とも | `beta_row_eq` / `beta_column_eq_zeroRow` (`i`,`j` 非依存) + `beta_isReal` (実性) |
| (11.8.4) | ✅ 二分律つき | `tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal` (書籍の「we may assume」= 分岐 2 で `τ₁` を共役スワップ `SHC_swap` に置換) + `exists_coherent_extension_h114_of_orthogonal` (両分岐を `∃ ν` に畳んだ消費側インタフェース) |
| (11.8.5) | ✅ | `charParam_a_eq_zero_of_residualEq` (`a = 0`)。書籍の「`β` 実 ⟹ `a` 偶」は `even_inner_of_conjPerm_symmetric` |
| (11.8.6) | ✅ | (11.8) 本体の結び (`zeta_residual_not_orthogonal_H0C_of_refuter` の narrow `𝒮(H₀C)` capstone) |
| (11.9) | ✅ (a)(b)(c) とも | (a) ⭐ **2026-08-07 に無条件化** = `inner_tau_muColumnZero_sub_zeta_rowZero_unconditional` (**行**-`0` 残差は直交 — σ 係数が行-`0` 指示関数 `δ_{i0}`; (11.8) の列-`0` と対照的) / (b) = `w2_lt_w1_of_hypothesis_H0C_unconditional` (`q > p`、既に無条件) / (c) = `not_cliffordCaseA_of_hypothesis` ((9.7) の case (b) が成立) + `isTypeIII_of_hypothesis` (`M` は type III) + 全称形 `no_typeIV_maximal` |

⚠ **層順に注意**: 無条件の (11.3) は Theorem (10.8) 経由なので、(11.5)-(11.7) を証明する
`S13_CoreStructure` / `S13_Lemmas113To115` より**下流**に居る。無条件形は両側を import する
`S13_NonGaloisExclusion` の末尾にまとめた。循環はない — (11.3) の証明は `𝒮(H₀C)` への
Theorem (6.3) + (10.8) で、(11.5)-(11.9) を一切使わない。

### §12 = repo `S14_MaximalI/**` (書籍 pp.69-74、`pages/peterfalvi-p069..p074.png` 切り出し済) — **監査完了 (2026-08-07、未形式化ゼロ)**

書籍 §12 =「Maximal Subgroups of Type I」= **(12.1)-(12.17)** の 17 件 (sub-part なし)。
**全 17 件に実体あり**。補充 1 件 (⭐) + 清掃 2 件。

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (12.1) Hypothesis | ✅ | `S14.Hypothesis` (`S14_MaximalI/Hypothesis.lean`): `L` type-I 極大 / `H = L_F` / `𝒮 = {Ind_H^L θ ∣ θ ∈ Irr H, θ ≠ 1_H}` / `τ` = `(A(L), L, G)` の Dade 等長 |
| (12.2) | ✅ (a)(b) とも | (a) = `character_decomposition_and_dade_domain` (`CharacterDecompositionData`: `χ = ∑_{φ∈S(χ)} φ`、`φ(1)` が `φ` に非依存、`τ` の定義域が `ℤ[⋃S(χ), L^#]`) / (b) = Hypothesis (5.2) + `R₁(φ)` (`ℤ[Irr G]` の濃度 2 正規直交部分集合) と `R(χ) = ⋃_{φ∈S(χ)} R₁(φ)` |
| (12.3) | ✅ | `nonconjugate_typeI_R_orthogonal` (`RhoConstancyDecomposition:640`): 非共役 type-I 極大 `L₁`,`L₂` に対し `R(χ₁) ⊥ R(χ₂)` |
| (12.4) | ✅ | `orthogonal_character_constant_on_coset` (`RhoConstancy:947`): `ψ ⊥ R(χ) ∀χ ∈ 𝒮` ⟹ `x ∈ L − H` 上 `ψ` は `xH` で定数 |
| (12.5) | ✅ | `ψ^ρ` が `H − H'` 上定数 (`PairCoherence:727` の constancy composition; `ρ` = Hypothesis (7.1) の `A = A(L)` 版) |
| (12.6) | ✅ 2 条項とも | `Sset_isIrreducibleCharacter` (`𝒮 ⊆ Irr L`) + `witness_L_coherent` (`𝒮` coherent) |
| (12.7) Theorem | ⭐ **2026-08-07 に書籍の形へ補充** | `typeI_isFrobenius_kernel_maxNilpotentNormalHall` (`NormPackage`): `∃ E, IsFrobeniusGroup ↥M ((maxNilpotentNormalHall M).subgroupOf M) E` — **無条件**かつ**核を名指し**。旧 `typeI_frobenius` は (i) Type-V 排除 `hnoV` を仮説で受け (書籍に無い; (10.10) `no_typeV_maximal_unconditional` で discharge 可、`S12_Noncoherence` が import する S14 側は葉 `CentralizerContainment` のみゆえ循環なし)、(ii) 結論の第 2 連言が `Prop` 値データフィールド `data.kernel_eq_MF` で、その producer は `True` を入れていた (別 producer `WitnessFrobenius` は本物の `typeF.H = M_F` を入れており**強度が producer 依存**) |
| (12.8) Hypothesis | ✅ | `InPi` + `CounterexampleHypothesis` (`WitnessSylowBasic`): `π`・最小元 `p`・`M`・`K = M_F`・`K' = [K,K]`・`P₀` |
| (12.9) | ✅ 3 条項とも | `WitnessSylowCyclic:276` が `IsMulCommutative ↥ctr.P0 ∧ rank ↥ctr.P0 = 2 ∧ Nonempty (RankTwoWitnessData ctr)` を束ねる。`RankTwoWitnessData` は `L`・`P₀ ≤ L_s`・`x ∈ Ω₁(P₀)^#` と `C_K(x) ⊄ K'` / `N_G(⟨x⟩) ≤ M` / `C_G(x) ⊄ L` を**全部 field で**持つ |
| (12.10) | ✅ | `witness_L_frobenius` (`L` は核 `H = L_F` の Frobenius 群) |
| (12.11) | ✅ 2 条項とも | `card_M_le` (`\|M\| ≤ \|K\|·\|H\|` = 補群性の帰結) + `M ∩ L ⊆ H` (`MinimalCounterexample`) |
| (12.12) | ✅ 2 条項とも | `complement_cyclic_order_dvd`: `IsCyclic E ∧ (e ∣ p−1 ∨ e ∣ p+1)` |
| (12.13) Notation | ✅ | `DadeNotation` (`DadeContradiction:21`): `e` / `τ₁` / `χ ∈ 𝒮` with `χ(1) = e` / `ψ = χ^{τ₁}`。**2026-08-07 の清掃**: 未消費の `Prop` 値フィールド 3 本 (`e_eq_index` / `rhoFormula` / `rhoMFormula`; 後 2 者は `True`) を削除 — 本物の `e = [L:H]` は `witness_value_norm_package` の `he_eq` 引数で明示的に threading されている |
| (12.14) | ✅ | `psi_constant_on_xK` (`ψ(xg) = ψ(x)` for `g ∈ K`) + `witness_dade_psi_apply_x_eq_chi` (`ψ^ρ(x) = χ(x)`) |
| (12.15) | ✅ 3 条項とも | 第 1 = `counterexample_chiRho_eval_of_mem_K_sharp` / `counterexample_chiRhoA1_eval_of_mem_K_sharp` (`ψ^{ρ_M}(g) = ψ(g)` on `K^#`) / 第 2 = `counterexample_psi_constant_on_K_sub_Kprime` / 第 3 = `counterexample_psi_int_on_K_sub_Kprime` (`ψ(g) ∈ ℤ`) |
| (12.16) | ✅ | `counterexample_contradiction` + `pi_empty` ((12.7) の証明本体)。**2026-08-07 の訂正**: `witness_value_norm_package` の docstring にあった「**Genuinely still-missing**: ρ-machinery norm estimates …」は **stale** — 7 連言すべてが名前つき補題で discharge 済で axiom-clean |
| (12.17) | ✅ | `not_all_maximal_typeI` + `theorem88_caseB_holds` (Theorem (8.8) の case (b) が成立) |

⚠ **設計差 (被覆済)**: `S14` の多くの補題が Type-V 排除 `hnoV` を仮説で受けたままだが、これは
`no_typeV_maximal_unconditional` で常に discharge されている (書籍 §12 の証明も (10.10) を cite
するので、内部段としては忠実)。headline (12.7) のみ無条件形に直した。

### §13 = repo `S15_*` (書籍 pp.75-86、`pages/peterfalvi-p075..p086.png` 切り出し済) — **監査完了 (2026-08-08、未形式化ゼロ)**

書籍 §13 =「The Subgroups S and T」= **(13.1)-(13.19)** + (13.10) の sub-part
**(13.10.1)-(13.10.3)** の計 **22 件**。repo は `S15_*` 系 (最大のクラスタ)。
番号 grep では全 22 件に実体あり。逐条突合は下記から。

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (13.1) Hypothesis | ✅ carrier が条項一致 | `S15.Hypothesis` (`S15_SAndT_Setup/SubcoherenceInputs.lean:76`)。(a) `S`,`T` 極大 + (8.8.b) (`theorem88_caseB`) + `W = S ⊓ T = W₁ ⊔ W₂` cyclic + `q = \|W₁\|`,`p = \|W₂\|` / (b) `P = S_F`,`Q = T_F`,`S' = PU`,`T' = QV`,`C = C_U(P)`,`D = C_V(Q)`,`\|U\| = uc`,`\|V\| = vd`,`W₁` が `U` を正規化 / (c) `Sset`,`Tset`,`tauS`,`tauT` / (d) `eta_eq_tau_omega` (`η_{ij} = ω_{ij}^σ`) / (e) `mu_definition` (`Ind_W^S(ω_{ij} − ω_{0j}) = δ_j(μ_{ij} − μ_{0j})`) + `delta_pm_one` + `mu_irreducible`/`mu_orthonormal`。書籍に無い追加 field も本物の群論事実 (`Q_inf_V_eq_bot`, `W2_isComplement_T_deriv`, `Sdata_W2_eq` = closed issue 3001 の橋渡し) |
| (13.2) | ⭐ **(e) を 2026-08-07 に書籍の形へ補充; (a)-(d) は被覆** | (a) `isTypeII_or_isTypeIII_of_isTypeNonI` + `isTypeII_of_q_lt_p` + `typeP_uW1_frobenius` (`UW₁` Frobenius, 核 `U` 可換 = `S_U_commutative`) / (b) `P_elementaryAbelian` (**ungated**) + `card_P_eq` (`\|P\| = p^q`、`Sdata_W2_eq` 経由で無条件) / (c) `u_le_cyclotomicQuotient` / (d) coherence = `S15_CaseACoherence`/`CaseBReducibleCoherence` 系 / **(e) ⭐** = **`Hypothesis.A0S_normedTI`** を新設 — 書籍の 2 条項 (`A₀(S)` が正規化群 `S` の TI-部分集合 ∧ `τ = Ind_S^G`) を束ね、Type-V 排除を (10.10) で discharge。**従来は carrier の `Prop` 値フィールド `A0S_TI`/`tauS_eq_induction` しか無く、producer が `True` を入れていた** (headline `basic_structure` の結論の最終連言が空だった) — `basic_structure` の結論も本物の `IsTISubset` へ差し替え |
| (13.3) | ✅ (a)(b)(c) とも | (a) `Hypothesis.mu_j_isIndPC` (`μ_j = Ind_{PC}^S θ`、`θ` 線型) + `mu_j_isIndPC_not_ker` (`P ⊄ Ker θ` の guard = (13.5) 消費側が threading する条件) と次数 `μ_j(1) = uq` / (b) `LambdaWitness hyp` の二分律 (`T_caseB_facts_unconditional` がこれで case-split; no-λ 枝が (9.7.b)+`C = 1`+`u = (p^q−1)/(p−1)`) / (c) `δ_j = δ'_i = 1` (`S15_CharacterDegreeEnginesSSide:515` ほか) + `μ_j^{τ₁} = ∑_i η_{ij}` の列公式 (`S15_CaseACoherence:904` `mu_column_formula`、`p = 3` の符号反転枝込み) |
| (13.4) | ✅ | `lambda_forces_T_caseB_core`: λ-cluster (`LambdaClusterData` = 次数 `uq` で `PC` の線型指標から誘導される既約が `𝒮` に在る) ⟹ `D = ⊥ ∧ v = (q^p−1)/(q−1) ∧ \|Q\| = q^p`。⚠ **packaging 差**: 書籍の「case (9.7.b) holds for `M = T`」という**定性的**条項は結論に出ず、その数値的署名 (`D = 1`、`v` の Singer 上限飽和) で表現されている。定性形自体は `clifford_dichotomy (mkSection11CharacterDataT …)` として存在し、証明はそれで case-split している。carrier `core : CharacterDegreeCore` は `characterDegreeCore_nonempty` で構成可、`pins : NuGridSupplyData` は FT spine の `Section16Inputs` から実現される (posited でない) |
| (13.5) | ✅ (a)(b)(c) とも、**χ 抽象の一般形で** | (a) 点公式 `χ(x) = (a/‖ζ₁‖²)ζ₁(x) + α(x)` on `H^#` = `H_sharp_point_formula` (+ `α` の `P`-核性 = `H_sharp_alphaFun_const_on_P` / `H_sharp_alphaFun_eq_zero_of_not_mem` / `H_sharp_alphaCF_*`) / (b) ノルム分解 = **`sum_normSq_sharp_chi_decomp`** (`ζ, α, χ, κ` すべて抽象) / (c) inflation `(\|P\|−1)α(1)² ≤ ∑_{H^#}\|α\|²` = `H_sharp_alphaFun_inflation` (+ `_finset` 版)。書籍が (13.5) を使う 3 つの `χ` ((13.6) の `λ^{τ₁}`、(13.7) の `η₁₀`、(13.8) の `η₀₁`) はそれぞれ `exists_caseB_data_*_core` が (a)(c) のデータを供給し、side-independent エンジン `caseB_{lambda,eta,eta01}_norm_bound` が (b) を通す |
| (13.6) | ✅ | `CharacterDegreeCore.lambda_tau1_sharp_norm_lower_core`: `\|S\| − (uq)² ≤ ∑_{x∈H^#} ‖λ^{τ₁}(x)‖²` (λ(1) = uq なので書籍そのまま) |
| (13.7) | ✅ | `CharacterDegreeCore.eta10_Hsharp_norm_lower_core`: `\|H\| − 1 ≤ ∑_{x∈H^#} ‖η₁₀(x)‖²` (= `\|H^#\|`) |
| (13.8) | ✅ **書籍そのままの S-side** | `Hypothesis.eta01_Hsharp_norm_lower_core` (`Eta01Correction:790`, issue 1041): `\|S'\| − u² ≤ ∑_{x∈H^#} ‖η₀₁(x)‖²`。T-side ミラー `eta10_Qsharp_norm_lower_core` もあり (docstring が「(13.8) applied to `T`」と明記) 。⚠ pdftotext だと `η₀₁` が `\Voi` に崩れて `ν₀₁` に見える — ページ画像 p079 で確定 |
| (13.9) | ✅ (a)(b) とも | (a) `CharacterDegreeCore.G0_nonvanishing_dichotomy_core`: `∀ x ∈ G₀, λ^{τ₁}(x) ≠ 0 ∨ η₁₀(x) ≠ 0` (`G₀ = G^# − ((H^#)^G ∪ (Q^#)^G)`) / (b) `analyticEstimate_galois_core` (`\|G₀\|/\|G\| ≤` 二つの正規化 norm 和。[Is] Lemma 3.14 の core は `NormEstimates:84`) |
| (13.10) | ⭐ **2026-08-07 に書籍の仮説へ揃えた** | `Hypothesis.analytic_inequality_of_lambdaCluster`: λ-cluster だけを仮説にして `u/c > m·p^{q−1}/q` (`m` は `m_eq` で書籍の式)。従来の Core endpoint `analytic_inequality_of_caseB_facts` は、書籍では**λ から導かれる** 3 入力 (`hD`/`hv` = (13.4)、`hQcomm` = (13.2.b)-at-`T`) を仮説で受けていた |
| (13.10.1) | ✅ | `CharacterDegreeCore.analyticEstimate_lambda_core` (書籍の証明中の display 番号式) |
| (13.10.2) | ✅ | `CharacterDegreeCore.analyticEstimate_eta_core` |
| (13.10.3) | ✅ | `Hypothesis.analyticCounting_disjointCover_of_caseB_facts` (`G = {1} ⊔ G₀ ⊔ (H^#)^G ⊔ (Q^#)^G` の 4 分割カウント) |
| (13.11) | ⭐ **2026-08-07 に書籍の仮説へ揃えた、3 条項とも** | `Hypothesis.numeric_bounds_of_lambdaCluster`: (a) `q ≥ 7 → m > 8/10` / (b) `q ≥ 5 → m > 7/10` / (c) `q = 3 → m > 49/100 ∧ u/c > (p²−1)/6`。Core 形は `numeric_bounds_of_caseB_facts` |
| (13.12) | ✅ | `Hypothesis.c_eq_one_of_lambda_dichotomy`: `c = 1` (無条件、`pins` のみ)。λ の有無で二分し、λ 無しの Galois 枝は `C = ⊥` を直接与える |
| (13.13) | ✅ 2 条項とも | `Hypothesis.caseA_parameters_of_clifford_caseA`: case (9.7.a) が `M = S` で成立 ⟹ `q = 3 ∧ u = (p−1)²/4` |
| (13.14) | ✅ 4 条項とも | `cyclotomic_divisor_facts`: `(p^q−1)/(p−1)` が奇 ∧ (`p ≡ 1 mod q` → `q ∣ …`) ∧ (`p ≢ 1 mod q` → `(p^q−1)/(p−1)` と `p−1` が互いに素 ∧ 約数 `x` は `x ≡ 1 mod q`) |
| (13.15) | ✅ | `T_caseB_v_eq_full_of_swapped_lambda_dichotomy` ほか (swap 経由で Singer パラメータの完全位数)。書籍の 2 分岐 (`p ≢ 1` / `p ≡ 1 mod q`) は (13.14) の場合分けとして扱われる |
| (13.16) | ✅ **2 条項とも** | `normalizer_W1_of_D_eq_bot`: `N_G(W₁) = C_G(W₁) ∧ C_G(W₁) = Q ⊔ W₂`。S-side ミラー `normalizer_W2_of_c_eq_one` (`C_G(W₂) = P ⊔ W₁`)。⚠ 設計差: `hTTypeII`/`hDbot` を仮説で受ける (それぞれ (14.9)/(13.4) から discharge 可能) |
| (13.17) | ✅ carrier が条項一致 | `TypeIOverNormalizerData`: `L` 極大 / `H = L_F` / `N_G(U) ≤ L` / `TypeIFrobeniusData L` / `U ≤ H` / `\|complement\| = pq` / `∃ y ∈ Q, W₂^y ≤ complement` — (13.17)(a)(b)(c) の全条項が genuine field |
| (13.18) | ✅ | `S15_BridgeCharacterBasic` の `β_j`/`Γ_j` carrier (`β_j = Ind_{PW₁}^S 1 − 1_S − μ_{0j}`)。docstring が「de-opacified (W3 §15)、issue 3003 の訂正後は Peterfalvi (13.18) に忠実」と明記 |
| (13.19) | ✅ **書籍の全条項が `TypeIOrthogonalityGridData` に在る** | `S15_SAndTGrid.lean:134` の `TypeIOrthogonalityGridData`: `e_eq_index` (本物の等式) / `betaL_eq` (**`β_L` を Dade 像 `(Ind_H^L 1_H − φ)^{τ₁}` に pin**) / `Ltau_orthogonal_eta` / `betaL_eta0_row_constant`+`col_constant` ((c) 第 1 条項 = `(β_L^τ, η_{0j})` の `j` 非依存) / `caseC`, `caseC_dual` (**(c1) = `(β_S^τ, φ^{τ₁}) ≡ 1 (mod 2)` ∧ `(\|H\|−1)/e ≤ (u−1)/q`、(c2) = `η_{0j}` odd-parity ∧ `p ≤ e`** の**両条項とも**)。producer `typeIOrthogonalityGridData_of_coherent78_of_c_eq_one_and_d_eq_one` は axiom-clean |
| — | ⚠ **設計差 (§16 向け lossy adapter)** | 同ファイル `:36` の**旧** carrier `TypeIOrthogonalityData` は opaque `Prop` を **case ラベル**として持ち (`e_eq_index`/`disjoint_support`/`Ltau_orthogonal_eta`/`betaL_eta_independent`/`caseC1`/`caseC2`/duals)、implication field は (c1) の**次数評価だけ** (`caseC1_bound`)・(c2) の**parity だけ** (`caseC2_eta0j_odd`) を投影する。`betaL` も自由フィールドで pin が無い。producer `typeI_orthogonality_dichotomy_of_c_eq_one_and_d_eq_one` は grid 版から**本物の命題を入れて**いるので**証明としては忠実**だが、`∃ data, data.disjoint_support ∧ …` という statement 単体では (c1) の parity 条項・(c2) の `p ≤ e`・`β_L` の同定が読めない (issue 0172 §2 の失敗様式 2「`∃ X` decoupling」に近い形)。**書籍強度の (13.19) は grid 版**なので被覆漏れではない — §16 側 (`S16_NonExistenceG/BetaVanishing`) がこの adapter 経由で消費している |

✅ **§13 監査完了 (2026-08-08)** — 全 22 件に書籍強度の実体あり。補充 3 件 ((13.2)(e) /
(13.10) / (13.11))、清掃・訂正 1 件 (closed issue 3001 への stale 参照)。
番号 → 主な repo ファイルの対応 (grep 実測):
(13.1)(13.2) `S15_SAndT_Setup/{PairStructure,SubcoherenceInputs,TSideDegrees}` /
(13.3)(13.5) `S15_CaseBEndgameSupply/HSharpChosenBase`, `S15_CharacterDegreeEnginesSSide` /
(13.4) `S15_CharacterDegreeSupply` / (13.6)-(13.9) `S15_CaseBEndgameSupply/{AnalyticRelayer,Eta10HCorrection}`,
`S15_CharacterDegreeEngines`, `S15_SAndT_Setup/CaseBOrder` /
(13.10)(13.10.1-3) `S15_SAndT_Setup/DegreesFirstSplit`, `GroupTheory/TISubsetCounting`,
`Algebra/GaloisRationalInteger` / (13.11)(13.12) `S15_CaseBEndgameSupply/OrderRelayerCore`,
`S16_CoreLemmas`, `RepresentationTheory/SingerLineBound` / (13.13)(13.15) `S15_CaseAContradiction`,
`RepresentationTheory/TypePGaloisUBound`, `S15_CharacterDegreeSupply` /
(13.14) `S15_SAndT_Setup/CaseBOrder` / (13.16) `BG/Ch1_Preliminary/OperatorMaschke`,
`GroupTheory/WielandtFixedPoint` / (13.17) `S15_SAndTDefs` / (13.18) `S15_SAndTGrid`,
`S10_TypePSupportA0`。

### §14 = repo `S16_*` (書籍 pp.87-92、`pages/peterfalvi-p087..p092.png` 切り出し済) — **監査完了 (2026-08-08、未形式化ゼロ・補充ゼロ)**

書籍 §14 =「Non-existence of G」= **(14.1)-(14.16)** + (14.11) の sub-part
**(14.11.1)-(14.11.4)** の計 **20 件**。Part I の最終章で、(14.2) の証明完了が FT 定理の完成。
番号 grep では全 20 件に実体あり。

| 書籍 | 判定 | repo の実体 / 備考 |
|---|---|---|
| (14.1) Hypothesis | ✅ | `q < p` — `S16.Hypothesis` の field `q_lt_p` (`S16_CoreLemmas:46`) |
| (14.2) Theorem | ✅ **(a)(b) とも carrier が条項一致** | `S16.FieldNormalizerData` (`S16_CoreLemmas:572`) が `BG.AppC.FieldNormalizerData p q G` を extend: **(a)** `σ` 単射準同型 + `sigma_P_eq_P` (`P` = 加法群 `F = 𝔽_{p^q}` の像) + `sigma_U_eq_U` (`U` = ノルム 1 補群 `U*`、位数 `(p^q−1)/(p−1)` の像) + `sigma_P0_eq_W2` (`W₂` = 素体直線 `𝔽_p` の像) + `cyclotomic_coprime` = condition (A) = 「`(p^q−1)/(p−1)` は `p−1` と互いに素」 / **(b)** `Q` の可換性・`p'` 性と `primeLine_normalizes_Q` (`W₂` が `Q` を正規化) ほか。書籍の「(a)(b) は BG App.C Theorem C により `p ≤ q` を導き (14.1) に矛盾」は `BG.AppC.theoremC` + `S16.nonexistence_of_G` + `BG.AppC.final_contradiction` の連鎖で、`feitThompson` まで axiom-clean |

| (14.3) Hypothesis | ✅ | `S16.LHypothesis` (`S16_NonExistenceG/SubgroupL:38`): `L` 極大 ⊇ `N_G(U)` / `H = L_F` / `ℒ` / `τ`,`τ₁` / 次数 `\|L:H\|` の `φ`。(b) の `β_S`,`β_T`,`β_L` は `S15_BridgeCharacterBasic` の carrier |
| (14.4) | ✅ | `T_side_caseB_facts` ((13.13)+(13.15) 経由で `v = (q^p−1)/(q−1)`、case (9.7.b) at `T`) |
| (14.5) | ✅ | `exists_y_L_structure`: `∃ y ∈ Q`, `L = H ⋊ (W₁W₂^y)` (repo では `W₂^y ≤` Frobenius 補群の形)。`S15_SAndT:927` に「(14.5) 小補群の排除」節 |
| (14.6) | ✅ | `S15_SSideGaloisFieldModel:217` 「S-side case (9.7.b) with explicit sharp parameters」+ `S15_CaseAOmegaFixedPointFree` (`W₂^y` が `Ω₁(Z(R))` 上 fpf という書籍の矛盾論法) |
| (14.7) | ✅ | `field_normalizer_of_U_characteristic`: `U` が `H` で characteristic ⟹ `Nonempty (FieldNormalizerData hyp)` (= Theorem (14.2) が成立)。**`sorry` なし** |
| (14.8) | ✅ (a)(b) とも | (a) `q_pow_gt_p_pow`: `q^{p+1} > p^{q+1}` (`Hypothesis` 版もあり) / (b) `cyclotomic_ratio_gt_of_q_lt_p`: `((q^p−1)/(q−1) − 1)/p > ((p^q−1)/(p−1) − 1)/q` (書籍の `(v−1)/p > (u−1)/q` を (14.4) の `v` と (13.2.c) の `u` 上界で表した形) |
| (14.9) | ✅ | `T` は type II — `S16_NonExistenceG/TSideTypeP` の type-III 排除群 + `S13.no_typeIV_maximal`/(10.10) |
| (14.10) Hypothesis | ✅ | `S16.MHypothesis` (`S16_NonExistenceG/SubgroupMCore`): `M` 極大 ⊇ `N_G(V)`。`exists_MHypothesis` が producer |
| (14.11) | ✅ | `K = V` と `\|M : K\| = pq` — `SubgroupMCore` の `K_eq_MF`/`e_eq_index` (`e = pq`) |
| (14.11.1)-(14.11.4) | ✅ 4 件とも | (1) `k > 2pv` 系 (`S15_SAndTDefs:980`, `KeyInequality`) / (2) `e = pq` と `β` の η-grid 展開 (`CoherentEtaOrthogonality:330`) / (3) 一般元集合の被覆 (`S16_G0Coprime`, `S15_SAndTDefs:1013`) / (4) 結論 = norm cascade の矛盾 (`KeyInequality:179`) |
| (14.12) | ✅ | `field_normalizer_of_L_conj_M`: `L` が `M` に共役 ⟹ Theorem (14.2) が成立 |
| (14.13) Hypothesis | ✅ | `NonConjugateHypothesis` (`L` は `M` に非共役、`h = \|H\|`) |
| (14.14) | ✅ 2 分岐とも | `(β_L^τ, ψ^{τ₁}) = 0` / `≠ 0` の二分律 (`S15_BridgeCharacterBasic:78` ほか、case (b) は `CaseBContradictionData`) |
| (14.15) | ✅ | `q_eq_three_of_p_pow_q_sub_two_lt_q_sq` + `p_eq_seven_of_q_eq_three_modEq_one_and_lt_q_sq` (`S16_CoreLemmas`) |
| (14.16) | ✅ | `H_eq_U` (`ComparingLM:533`): `H = U`。`U_characteristic_of_H_eq_U` で (14.7) の分岐仮定に矛盾 |

🏁 **§14 の総組み立て** `S16.field_normalizer_structure` (`ComparingLM:1036`) が書籍の結び
「By (14.12), (14.16) and (14.7), the proof of Theorem (14.2) is complete」を**そのまま**写す:
(14.3) `exists_LHypothesis` → `U` characteristic か否かで分岐 → yes なら (14.7)、no なら
(14.10) `exists_MHypothesis` → `L ~ M` か否かで分岐 → yes なら (14.12)、no なら
(14.13)-(14.16) `H_eq_U` + `U_characteristic_of_H_eq_U` で分岐仮定に矛盾。
`field_normalizer_structure` / `H_eq_U` / `feitThompson` はいずれも axiom-clean。
番号 → 主な repo ファイル (grep 実測): (14.3)-(14.7) `S16_NonExistenceG/{SubgroupL,TSideTypeP,BetaVanishing}`,
`S15_SAndT` / (14.8) `S16_NonExistenceG/KeyInequalityArithmetic` / (14.9) `S15_SAndTGrid`,
`Isaacs/Ch06_FrobeniusActions/FrobeniusGroupQuotient` / (14.10)(14.11) `S16_NonExistenceG/SubgroupMCore`,
`S15_ComplementStructure` / (14.11.1)-(14.11.4) `S16_NonExistenceG/{BetaVanishing,CoherentEtaOrthogonality,KeyInequality}`,
`S16_G0Coprime` / (14.12)(14.13) `S16_NonExistenceG/ComparingLM`, `S16_PairingCoherence` /
(14.14) `S15_BridgeCharacterBasic` / (14.15)(14.16) `S16_CoreLemmas`。

## 4. Part II + 補章の番号 census (ステップ 2) — **2026-08-08 実施**

### 4.0 番号体系 — Part I とまったく違う

Part I が「章番号.通し番号」の 1 系列 ((1.1)…(14.16)) なのに対し、**Part II は 3 系統が混在**する:

1. **章をまたぐ固有名**: `Theorem A` (Introduction, p.97) / `Theorem B` (Ch.II, p.108) /
   `Theorem C` (Ch.III, p.115)。
2. **節ごとにリセットする `Proposition N` / `Lemma N`** — Ch.I だけがこれを使う。
   同じ「Proposition 1」が Ch.I §1・§2・§3 に**3 つ別々に存在する**ので、`§` を落とした引用は
   一意でない。しかも §2 / §3 は**無番号の `Proposition.` / `Lemma.` / `Corollary.`** も混ぜる。
3. **証明内の連番ステップ `(N)`** — Ch.II の (1)-(17)、Ch.III 各節の (1)-(7)、
   Ch.IV §2 の (1)-(20) 等。書籍はこれを本文から `(11) により` と参照するので、**実質的に
   番号付き結果**であり repo も 1 ステップ = 1 定理 (しばしば 1 ファイル) で形式化している。

⟹ **Part I の機械 census (番号 grep) は原理的に効かない**。本節は書籍テキストを節境界つきで
走査して結果を列挙し (`scratchpad/census.py` 相当)、repo 側は**概念名 + 節つき引用**の
両方で突合した。

### 4.1 書籍側の全結果 (機械抽出 + ページ画像確認)

| 単位 | 書籍 pp. | 結果 | 件数 |
|---|---|---|---|
| Part II Introduction | 97-98 | 仮説 (A1)(A2)(A3)、帰納法仮説、**Theorem A** | 1 |
| Ch.I §1 Consequences of (A1) | 100-103 | Prop 1(a)-(e) / Prop 2(a)-(d) / Prop 3 / Prop 4(a)-(c) / **Lemma** (無番号, p.102, (a)(b)) / Prop 5 / Prop 6(a)-(c) | 7 |
| Ch.I §2 Structure of Q and K | 103-104 | Prop 1(a)-(c) / Prop 2 / **Corollary** (Prop 2 の系) / Prop 3 | 4 |
| Ch.I §3 Induction Hypothesis | 104-107 | Lemma 1 / Prop 1(a)-(c) / Prop 2 / Lemma 2 / Lemma 3 / Lemma 4 / Lemma 5 | 7 |
| Ch.II The First Case | 108-114 | 仮説 (B1)(B2)、**Theorem B**、ステップ (1)-(17) | 18 |
| Ch.III §1 The Structure of Q | 115-118 | 仮説 (C1)、**Theorem C**、**Proposition** (3 分岐 (a)(b)(c)) | 2 |
| Ch.III §2 `st` の位数 5 | 118-119 | **Proposition**、ステップ (1)-(7) | 8 |
| Ch.III §3 `KW` の `S` への作用 | 119-121 | **Proposition**、ステップ (1)-(5) | 6 |
| Ch.IV §1 The Mappings f, g, h | 122-123 | 恒等式 **(H1)-(H6)**、**Lemma** | 7 |
| Ch.IV §2 Preliminary Calculation | 123-129 | ステップ (1)-(20)、**Proposition** (p.129) | 21 |
| Ch.IV §3 Determination of f | 129-132 | **Proposition**、ステップ (1)-(5)、**Corollary 1**、**Corollary 2** | 8 |
| Ch.IV §4 The Case V ≠ W | 132-134 | ステップ (1)-(10) | 10 |
| App.I A Special Case of Huppert | 135-136 | Prop 1 / **Lemma** (無番号) / Prop 2(a)(b) | 3 |
| App.II On Near-Fields | 137-138 | Prop 1 / Prop 2 | 2 |
| App.III On Suzuki 2-Groups | 139-143 | Lemma 1(a)(b) / Lemma 2 / Def 1 / Def 2 / Def 3 / **Theorem** / Prop 1 / Prop 2 | 8 |
| App.IV The Feit–Sibley Theorem | 144-150 | Lemma 1(a)(b) / Lemma 2(a)(b)(c) / **Theorem** | 3 |
| **合計** | | | **115** |

### 4.2 repo 側の cite 突合 — **111 / 111 に cite あり**

全 115 件について repo 内に引用が存在する (**cite ゼロは無し**)。Part I の 169/169 と同じ状況で、
⚠ 初版の件数 111 は 2 箇所が誤りだった (どちらも 2026-08-08 にページ画像で判明):
**(a)** Ch.I §2 に数えた「無番号 Lemma」は存在しない (§2 の `Lemma` 3 箇所はすべて §1 の
Lemma への参照)。**(b)** Ch.IV §4 のステップは (1)-(5) でなく **(1)-(10)** — 素の
`^\(N\)` grep が表示式内の (6)-(9) を取りこぼしていた。差引 111 − 1 + 5 = **115**。

⟹ **本命はここでも「番号を埋める」ことでなく §2 の 3 種の残債を 1 件ずつ潰す逐条監査**。

⚠ **初回の機械 census は 11 件を偽の「cite ゼロ」と誤判定した** — すべて repo 側の引用表記が
自分の正規表現と違っただけだった。記録しておく (同型の誤判定を繰り返さないため):

| 偽陰性だった項目 | 実際の repo 表記 |
|---|---|
| Ch.III §1 ステップ (1)(2)(3) | `Ch. III §1, Proposition, case (3): st has order 3` (ステップでなく **case** と呼ぶ) |
| Ch.III §2 Proposition | `Ch. III §2, p. 118.` (**ページ番号**で指す) |
| Ch.IV §2 Proposition | `PSU3StepTwenty.lean:396` / `PSU3BarOrbit.lean:400` に**書籍文そのまま引用** |
| Ch.IV §3 ステップ (1)-(5) | `Ch. IV §3 (3), p. 130` (`step` の語を挟まない) |
| Ch.IV §4 ステップ (4)(5) | `Ch. IV §4: the linear equation (4)` 等 |
| App.I Lemma | `Peterfalvi Appendix B, Lemma, part (1)` (**Appendix B** 表記, 下記 4.3) |
| App.II Prop 2 | `Appendix II (Near-Fields), Proposition 2 — irreducibility` |

### 4.3 ⚠ 補章のラベルが repo 内で不統一だった (2026-08-08 に統一)

書籍の補章は **Appendix I / II / III / IV** (ローマ数字) だが、repo は一部で BG の補章letter
(`Appendix A`-`E`) を流用していた:

| 書籍 | 旧 repo 表記 | 実体 |
|---|---|---|
| Appendix I (Huppert, pp.135-136) | **Appendix B** | `Appendices/Huppert.lean` |
| Appendix II (Near-Fields, pp.137-138) | **Appendix C** | `Appendices/NearFields.lean` |
| Appendix III (Suzuki 2-Groups) | Appendix III ✅ | `Appendices/Suzuki2Groups.lean` |
| Appendix IV (Feit–Sibley) | **Appendix E** (見出しのみ; 本文は IV) | `Appendices/FeitSibley.lean` |

`Appendix B`/`C`/`D`/`E` は **BG の補章**を指す語として repo 全体で 200+ 箇所使われているので、
Peterfalvi 側がこれを流用すると grep が混線する (現に上表の偽陰性 2 件を生んだ)。
2026-08-08 に Peterfalvi 側の見出しを書籍どおりのローマ数字へ統一した。

### 4.4 逐条監査 (ステップ 3 の Part II 版)

上流優先 + 文書順 ⟹ **Ch.I §1 から**。ページ画像は `references/peterfalvi/pages/` に
**pp.5-92 / 97-150 が全て揃った** (2026-08-08 に pp.97-114, 135-143 を追加)。

#### Part II Ch.I §1 (書籍 pp.100-103) — **監査完了 (2026-08-08)**

7 件 (Prop 1-6 + 無番号 Lemma) すべてに書籍強度の実体あり。**補充 2 件**:

| 書籍 | repo | 判定 |
|---|---|---|
| Prop 1 (a) | `HypothesisA1.exists_mem_H_conj_inf_eq_D` + `odd_card_conj_inf` | 2 条項とも ✅ |
| Prop 1 (b) | `normalizer_le_H_of_le_Q` (部分**群** X) + `centralizer_le_H_of_mem_Q` | ✅ 書籍は部分**集合** `X ⊂ Q` だが `N_G(X) ≤ N_G(⟨X⟩)` で同値 |
| Prop 1 (c)(d) | `exists_sylow_two_le_Q` / `normalizer_Q_eq_H` + `normalizer_H_eq_H` | ✅ |
| Prop 1 (e) | `Hypothesis.oPiCore_two_compl_eq_normalCore` | ✅ (書籍も 2-rank を明示仮説にする唯一の §1 条項ゆえ `Hypothesis` 側に残す) |
| Prop 2 (a)-(d) | `odd_orderOf_mul_involution` / `isConj_of_involutions` / `bijOn_conj_of_involution_mem_Q` / `ncard_involutions_map_conj_eq_card_involutions_H` | ✅ 4 条項とも |
| Prop 3 | `ncard_KSet_eq` + `image_conj_KSet_eq_involutions_H` | ✅ 2 条項とも |
| Prop 4 (a)(b) | `CanonicalForm.*` / `existsUnique_distinguishedInvolution` | ✅ |
| **Prop 4 (c)** | 旧: `normalCore_H_eq_bot` 等 (**(A2) で恒真**) | ⚠ **特殊化債務 → 一般形へ補充** |
| Prop 5 | `V_eq_centralizer_distinguishedInvolution` + `W_eq_centralizer_involutions_H` | ✅ 2 条項とも |
| Prop 6 (a)(b)(c) | `exists_mem_centralizer_smul_pair` + `cQ_mul_cD_eq_cH` / `even_card_cQ` / `exists_conj_mem_D_map_le_V` | ✅ |
| **Lemma (a)** | 旧: `invertedProdEquiv` (**`yz` だけ**) | ⚠ **第 2 全単射 `zy` を補充** |
| Lemma (b) | `closure_invertedBy_subgroupOf_normal` | ✅ |

**補充 1 — Prop 4(c) の特殊化債務 (失敗様式 2 = 部分被覆)**。書籍の §1 は **(A1) だけ**を仮定する
(p. 100「We assume in this section that `G` satisfies hypothesis (A1)」)。(A2)(A3) が入るのは
§2 から (p. 103)。repo の `Hypothesis` が 3 つを束ねていたので、Prop 4(c)

> `N = ⋂_x H^x = C_D(Q) ⊂ C_D(t)`。`Ḡ = G/N` は `Ω` 上 (A1) を満たし、`Q̄ ≅ Q`、`|s̄t̄| = |st|`。

が **`N = 1` で恒真**に潰れていた (旧 docstring 自身が「all three subgroups equal to `1`」と自認)。
これは飾りでなく、書籍は一般形を §3 で 2 度使う — Prop 1(a) の証明「The statement concerning
`𝒩(L)` has been seen in §1, Proposition 4(c)」、Prop 1(c) の証明「By §1, Proposition 4(c), the
order of `st` is equal to the order of `s̄t̄` in `L̄`」。`L = C_G(X)` の `Ω_X` 上の作用は一般に
忠実でない (Prop 1(a) はその核を計算するのが仕事)。実際 repo も §3 で
`normalCore_cH_eq_centralizer_cQ` を**独立に再証明**していた。

修正 = `Hypothesis extends HypothesisA1` に変更 + §1 全体を `HypothesisA1` へ移送 + 5 条項を
一般形で証明 (`mem_normalCore_H_iff` / `normalCore_H_le_D` / `normalCore_H_eq_centralizer_Q` /
`normalCore_H_le_V` / `quotientOfKernel` / `quotientQEquiv` / `orderOf_mk_distinguished_mul_t`)。
⚠ **(A2)/(A3) を実際に使っていたのは §1 全体で 2 箇所だけ**だった (Prop 1(e) とこの Prop 4(c))
ので、証明本体は一切変えずに済んだ — memory `generalize-by-measuring-which-carrier-fields-are-used`
の実例。

**補充 2 — §1 Lemma (a) の第 2 全単射**。書籍は「The mappings `(y,z) ↦ yz` **and**
`(y,z) ↦ zy` are bijections from `Y × Z` to `X`」と両方を主張するが repo は `yz` 側だけを持ち、
§3 Prop 1(b) (`N_D(X) = N_K(X) N_V(X)` — **反転因子 `K` が先**) は `d⁻¹` に `yz` 版を当てて
反転する回り道をしていた。`invertedProdEquiv'` を追加。

#### Part II Ch.I §2 (書籍 pp.103-104) — **監査完了 (2026-08-08、補充ゼロ)**

§2 冒頭に「We assume from this point onwards that `G` satisfies (A1), (A2) and (A3)」と明記
(§1 の (A1)-only との対比が §1 の Prop 4(c) 債務の根拠)。4 件すべてに書籍強度の実体あり。

| 書籍 | repo |
|---|---|
| Prop 1 (a) `x ∈ K−{1} ⟹ C_Q(x)=1` | `QStructure.centralizer_Q_eq_bot_of_mem_K` 系 (`QStructure.lean:102`) |
| Prop 1 (b) `Q` 冪零 | `QStructure.isNilpotent_Q` (`:169`) |
| Prop 1 (c) `H∩I ⊆ Z(Q)` + `(H∩I)∪{1}` は初等アーベル 2-群 | `involutions_H_subset_centralizer_Q` / `Q0` を**部分群として定義**(`:293`) + `sq_eq_one_of_mem_Q0` + `commute_of_mem_Q0` |
| Prop 2 `K` は `D` の巡回正規部分群 | `KCyclic.K_isCyclic` + `K_normal` |
| Corollary `S` はアーベルか Suzuki 2-群 | `SylowTwo.sylowTwo_isMulCommutative_or_isSuzuki2Group` |
| Prop 3 `Q₀ ⋊ (D/W) ≅ 𝓛(F_q,A)` + `V/W` 巡回 | `SemilinearRealization.exists_semilinear_equiv` |

Prop 3 は非常に忠実: `semilinearGroup F A = (F₊ ⋊ Fˣ) ⋊ A` が書籍の `𝓛(F,A) = (F ⋊ F*) ⋊ A`
そのもので、同型 `Q₀ ⋊ D̄ ≃* semilinearGroup F A` に加えて 3 つの同定 (`Q₀ ↔ F₊` / `K̄ ↔ Fˣ` /
`V̄ ↔ A`) と `IsCyclic V̄` (書籍の "In particular, `V/W` is cyclic") を全部持つ。
書籍が `K` と書く因子は repo では `fitting D̄` で、`SemilinearIdentification.Kbar_eq_fitting`
が両者を同定する (これは §2 Prop 2 の証明そのもの)。

#### Part II Ch.I §3 (書籍 pp.104-107) — **監査完了 (2026-08-08、補充ゼロ)**

7 件すべてに書籍強度の実体あり。

| 書籍 | repo |
|---|---|
| Lemma 1 (Theorem A の結論 ⟹ `Q` は 2-群、`L = O^{2'}(G) = ⟨Qˣ⟩`) | `TheoremAConclusion.Q_and_residual` (**束ねた書籍形**; 3 分岐は `Q_and_residual_of_{psl2,suzuki,psu3}_target`)、核は `simple_normal_oddIndex_Q_core` |
| Prop 1 (a) `C_G(X)` は `Ω_X` 上 (A1)、`𝒩(L) = C_{L∩D}(L∩Q) ⊂ L∩V` | `centralizerHypothesisA1` + `normalCore_cH_eq_centralizer_cQ` + `normalCore_cH_le_cV` (⟵ §1 Prop 4(c) の一般形の適用先) |
| Prop 1 (b) `N_G(X) = C_G(X)N_V(X)` | `CentralizerNormalizer.normalizer_eq_centralizer_mul_normalizer_inf_V` |
| Prop 1 (c) 三分岐 + `C_{Q₁}(X)=1` + `𝒩(L)∩F = Z(F)` | `centralizer_trichotomy_of_induction` → `CentralizerTrichotomyData` (`common` に前 2 条項、`branch` に (i)(ii)(iii)) |
| Prop 2 (`G` 非単純 ⟹ Theorem A の結論) | `InductionNonSimple.theoremAConclusion_of_not_simple` |
| Lemma 2 (`V` の部分集合が `G`-共役 ⟹ `V`-共役) | `ConjugacyInV.lean:176` |
| Lemma 3 (強実で `x²≠1` ⟹ `ut` (`u ∈ Q₀^#`) に共役 **かつ** `|C_G(x)|` 奇) | `stronglyReal_normalForm_and_centralizer_odd` (**2 条項を束ねた形**) |
| Lemma 4 (`\|st\|=3`, `V≠1` ⟹ `⟨Q₀,K,t⟩ = Q₀K ∪ Q₀KtQ₀ ≅ PSL(2,q)`) | `OrderThreePSL` / `OrderThreePSLInduction` |
| Lemma 5 (`W` 巡回 **かつ** `\|W\| ∣ q+1` **かつ** `W≠1 ⟹ Q` は type B) | `WCyclicDivides.lemmaFive_of_orderThree` (**3 条項を束ねた形**) |

設計差の記録: §3 は書籍が「帰納法仮説を標準仮定にする」節なので、repo は
`TheoremAInductionBelow` を明示パラメータで受ける (axiom でも carrier field でもない)。
Lemma 1 は書籍が外部引用 ([HB] Ch.XI Ex 1.3a/Thm 3.3、[H] Kap.II Satz 10.12 等) で済ませる
「`|Ω|−1` が 2 冪」「`L` 単純」を、repo は 3 つの標準モデルから**導出**している。

#### Part II Ch.II The First Case (書籍 pp.108-114) — **監査完了 (2026-08-08、補充 1 件)**

18 件 (仮説 (B1)(B2) + Theorem B + ステップ (1)-(17))。**全ステップにファイルが存在**
(`FirstCase/Step{One..Seventeen}*.lean`、補助分割込みで 29 file)。突合済は以下:

| 書籍 | repo | 判定 |
|---|---|---|
| (B1) | `FirstCaseHypothesis extends Hypothesis` の `P`/`p`/`p_prime`/`P_le_V`/`card_P`/`twoRank_centralizer_le_one` | ✅ 条項一致 |
| (B2) | 仮説として持たず、`theoremB` 内部の二分岐で処理 | ✅ 書籍も背理法の仮定として置くだけ (`p ∣ \|G^ab\|` なら Ch.I §3 Prop 2、さもなくば (B2) で step (1)-(17) が矛盾) |
| **Theorem B** | `FirstCaseHypothesis.theoremB (ind : TheoremAInductionBelow G Ω) : Nonempty (TheoremAConclusion G Ω)` | ✅ 書籍そのまま |
| (1) `V = W ⋊ P`、`\|Q₀\| = 2^p`、`N_G(P) = C_G(P)`、`C_D(P) = C_W(P) × P` | `exists_decomp_of_mem_V` + `P_inf_W_eq_bot` / `card_Q0_eq_two_pow` / `normalizer_P_eq_centralizer` / `D_inf_centralizer_eq_W_inf_centralizer_join_P` | ✅ 4 条項とも (半直積は分解 + 交わり自明の 2 本で表現) |
| (2)(a) `C_G(P)` は `Ω_P` 上 (A1)、核は `N = C_D(C_Q(P)) ∩ C_G(P)` | `rankOneQuotient` (faithful 商上の `RankOneHypothesis`) + 核の同定は §3 Prop 1(a) `normalCore_cH_eq_centralizer_cQ` | ✅ 書籍も核を §3 から引く |
| (2)(b) `C_G(P)/N ≅ (F ⋊ C_Q(P)) ⋊ Σ`、`C_Q(P) ≅ F*`、`Σ = C_W(P)` が `F` の自己同型群 | `exists_affineNearFieldModel` → `AffineNearFieldModel` が `emb`/`isComplement` (半直積)、`qEquiv : Q ≃* Fˣ`、`dAut : D → Aut F` (単射・乗法的・共役実現) を**全部フィールドとして持つ** | ✅ 3 つの同定条項とも |

ステップ (3)-(17) も全件に実体あり (突合 2026-08-08):

| 書籍 | repo |
|---|---|
| (3) `\|Q₁\|` の各素因数 `r` に `r ≡ 2^i (mod 2^p−1)` (`0 ≤ i ≤ p−1`) | `StepThree` 末尾の packaged 定理 (Clifford 二分岐経由) |
| (4) `\|Q\| = \|C_Q(P)\|^p = \|F*\|^p` | `StepFour` (Wielandt 不動点定理; 第 2 等号は step (2)(b) の `qEquiv` から) |
| (5) `F` が体でない ⟹ `F ≅ F_{9,2}` かつ `Q₁ = 1` | `StepFive` (2 条項とも) |
| (6) `Q₁ = 1` のとき `F ≅ F_{9,2} ⟹ \|Σ\| ∈ {1,3}`、さもなくば `\|F\| ∈ {f,9}` かつ `Σ = 1` | `card_field_and_D_of_Q1_eq_bot` (2 分岐とも) |
| (7) `N = P` かつ `Σ ≅ C_W(P)` | `N_eq_P_and_sigma_mulEquiv_centralizer_W` (2 条項を束ねた形) |
| (8) `Q₁ ≠ 1`、`ℓ = \|Σ\| ≠ 1` ⟹ `ℓ` 素数かつ `F` は位数 `3^ℓ/5^ℓ/9^ℓ` の体 | `StepEight` 末尾 |
| (9) `p = f` | `char_eq_p` (`p ∣ \|Q\|+1` の transfer 半分 + 算術仕上げ) |
| (10) `\|F\| = p^m` のとき (10.1) `p ∤ \|Σ\|` かつ `\|G\|_p = p^{m+2}` / (10.2) `p = \|Σ\| = 3`, `F ≅ F_{9,2}`, `W` 巡回 (位数 3 か 9), `\|G\|_3 = 3⁴\|W\|` | `factorization_card_G_eq` + `StepTen` の (10.1)/(10.2) |
| (11) `R = T × P`、`T` は `C_Q(P)C_W(P)` で正規化、**`T ⋊ C_Q(P) ≅ F ⋊ F*`**、`C_Q(P)` は `𝒜 − {P}` に正則 | `StepEleven` + `StepElevenComplement` (⚠ **1 条項が言及のみ**、下記) |
| (12) case (10.2) が成立 | `StepTwelve*` |
| (13) `C_G(Z₁)` は Z-群 | `StepThirteen` |
| (14) `Z(RΣ) = Z₁P`、3-部分群 `R₁` の存在 | `StepFourteen*` |
| (15) 位数 9 の巡回部分群 `L ≤ P₁` の存在 | `StepFifteen*` |
| (16) `Z₁PΣ ⊆ Z₂(P₁)` 等 | `StepSixteen` |
| (17) Conclusion (最終矛盾) | `StepSeventeen*` の `false_of_transfer_control` |

**補充 1 件 (2026-08-08 に landing) — step (11) の `T ⋊ C_Q(P) ≅ F ⋊ F*`** (§2 の失敗様式 3
=「言及のみ」の実例)。
`StepEleven.lean` の file docstring が 3 条項を散文で列挙するが、この半直積同型だけ**定理が無い**
(`sInvertedT` に関する `MulEquiv` は repo 全体にゼロ)。他の 3 条項 —
`R = T × P` (`coe_invImageF_eq_sInvertedT_mul_P` + `sInvertedT_spec` の `⊔`/`⊓`)、
`T` の正規化 (`conj_mem_sInvertedT_of_mem_*`)、正則性 (`ncard_prime_order_not_le_sInvertedT` +
`index_normalizer_P_subgroupOf_normalizer_invImageF`) — は在る。下流 (`StepTwelve`〜`StepFifteen`)
はこの同型を消費していない (使うのは `T` の可換性・位数・`sInvertedT_spec` だけ) ので
**証明の健全性には影響しない**が、書籍の条項なので補充対象。

補充の中身 (新 leaf `FirstCase/StepElevenSemidirect.lean`、全て axiom-clean):

  fieldCoord            座標写像 `T → (F,+)` = 「`C_G(P)/N` 上で `x` が誘導する平行移動」
  emb_fieldCoord        定義性質 `emb (fieldCoord x) = [x]`
  fieldCoord_injective  単射 (`[x] = 1 ⟹ x ∈ N = P` (step (7)) かつ `T ⊓ P = ⊥`)
  sInvertedTEquivField  `T ≃* (F,+)` (全射は `|T| = |F|` = `card_sInvertedT` から)
  fieldCoord_conj       `C_Q(P)` 同変性 — 共役が `qEquiv q⁻¹` 倍に対応 (model の `qEquiv_conj`)

最後の 2 本が合わせて書籍の `T ⋊ C_Q(P) ≅ F ⋊ F*` そのもの (`T` が `(F,+)`、`C_Q(P)` が
`F*` で、作用が一致)。stale docstring 2 件も訂正 (`StepElevenComplement` の「in subsequent
commits, issue 2053」= 実際は landing 済 / `StepEleven` の散文列挙に定理名を追記)。

清掃 1 件: `AxiomsCheck` の「`char_eq_p` は model の `sorry` (9318) を継承するので未登録」注記が
stale だった (Q₈ は 2026-08-07 に閉了) → 訂正し `char_eq_p` を登録 (axiom-clean 確認)。

#### Part II Ch.III The Structure of H (書籍 pp.115-121) — **監査完了 (2026-08-08、補充ゼロ)**

16 件 (Theorem C + §1/§2/§3 の各 Proposition + 各節のステップ)。全件に書籍強度の実体あり。
仮説 (C1) (p.115: `V ≠ 1` かつ素数位数の `P ≤ V` すべてに `C_Q(P)` の 2-rank ≥ 2) は
`SecondCaseHypothesis`、(C2) (p.119: 「`S` は type B の Suzuki 2-群、`st` の位数 3、`W ≠ 1`」
= §1 Proposition の case (c) を §3 以降の標準仮定に昇格したもの) は
`theoremAConclusion_or_caseC2` の右分岐 + 各条項をパラメータで受ける形。

| 書籍 | repo |
|---|---|
| **Theorem C** (`Q` は 2-群) | `SecondCaseHypothesis.isPGroup_two_Q` (**書籍そのままの形**; 内訳の step 1-3 は `StructureOfH/{Basic,FeitSibleyInput,CoherenceContradiction}`) |
| **§1 Proposition** (3 分岐 (a)(b)(c)) | `WNeBot.trichotomy` (**3 分岐を束ねた形**; 書籍より強く case (b)(c) に `\|Q\| = \|Q₀\|²`/`\|Q₀\|³` も付く) |
| **§2 Proposition** (case (b) ⟹ `(SK) ∪ (SKtS)` は部分群) | `CaseBStructure.typeASubgroup` (`Subgroup G` として構成 = 「部分群である」の内容そのもの) + `coe_typeASubgroup` で carrier 一致 |
| §2 ステップ (1)-(7) | `OrderFivePairing` / `OrderFiveOrbits` / `OrderFiveSubgroup` (`h(x) ∈ K`、`K`-軌道代表系、構造方程式の帰結) |
| **§3 Proposition** (`S ⋊ KW ≅ S₁ ⋊ K₁W₁` + 明示モデル) | `ModelAction.exists_standardModel` (**書籍の全条項**: `φ` の双加法性・scaling 則 `φ(ax,by) = ab^θφ(x,y)`・anisotropy `x≠0 ⟹ φ(x,x)≠0`・`K₁W₁ ≤ E^×` の作用 `(x,y)^a = (ax, a^{1+σ}y)`) |
| §3 ステップ (1)-(5) | `ModelIsomorphism` の step (3)/(5)、`CenterFieldExponent` の step (2)、`QuotientKWField` 等 |

設計差の記録: §3 の全 endpoint は `V = W` を要求するが、これは Ch.IV §4 が `U = O^{2'}(C_G(P))`
に対して §2/§3 を適用する場面では商側で自動的に得られない。repo は標準 `PSU(3,ℓ)` モデル側
(`StandardModelHypothesis`) で `V = W` を**定理として**証明し、結論を
`CentralizerPSUData.residualQuotientEquiv` で戻す構成にしている (書籍の "relative to `U`,
`U ∩ H` and `t`" の Lean 化)。

#### Part II Ch.IV Characterization of PSU(3,q) (書籍 pp.122-134) — **監査完了 (2026-08-08、補充ゼロ)**

**46 件** (§1 = 7 / §2 = 21 / §3 = 8 / §4 = 10)。全件に書籍強度の実体あり。

| 書籍 | repo |
|---|---|
| §1 恒等式 **(H1)-(H6)** | `GroupTheory/RankOneBNPair.lean` の `hOne`/`hTwo`/`hThree`/`hFive`/`hSix` (各定理が書籍の条項 + `g`-companion を束ねた形) |
| §1 **Lemma** (`L` 忠実 ⟹ `⟨Qˣ⟩` と `L` は `Q`,`f` (resp. `M`,`f`) で同型を除き決まる) | `GroupTheory/RankOneBNPairRigidity.lean` |
| §2 ステップ (1)-(20) | `PSU3Preliminary` / `PSU3OrbitCount` / `PSU3Sequence` / `PSU3FieldArithmetic` / `PSU3StepFifteen` / `PSU3StepSeventeen` / `PSU3StepEighteen` / `PSU3PairComparison` / `PSU3StepTwenty` |
| §2 末尾 **Proposition** (`D` が `(Q/Q₀)^#` に不動点なく作用 ⟹ ∃`i`, `f(ω) = (ω⁻¹)^ζ`, `h(ω) ∈ W`) | `PSU3StepTwenty.lean:396` / `PSU3BarOrbit.lean:400` (**書籍文そのまま引用**) |
| §3 **Proposition** (`θ = 1` かつ `f(ρ) = (ρ̄/y, 1/y)`) | `PSU3Proposition.proposition_inverseFormula_of_ne_one` (+ `Q^#` 全体版) |
| §3 ステップ (1)-(5) | `PSU3SectionThree` |
| §3 **Corollary 1** (`O^{2'}(G) ≅ PSU(3,q)`) | `PSU3CorollaryOne.exists_mulEquiv_standardPermGroup` + `TheoremAConclusion` インスタンス |
| §3 **Corollary 2** | `PSU3CorollaryTwo` |
| §4 ステップ **(1)-(10)** | `PSU3SectionFourSetup` / `PSU3SectionFourCorollaryTwo` / `PSU3SectionFourCoordinate` (= (4)) / `PSU3SectionFourEquations` / `PSU3SectionFourArithmetic` ((6)-(9)) / `PSU3SectionFourEndgameCore` ((10) + `λ = 1` + `μ = 1 ⟹ η ∈ W`) |

⚠ **(H3)/(H4)/(H6) の指数は `a^t` / `a^{-t}` / `h(y)^t` であって `a^{-1}` 等ではない**。
pdftotext はこれを完全に潰す (`(H3) /(*") =/(*)"' foraeD.`) ので、本セッションでは 200dpi
ページ画像を**さらに拡大クロップして**確定した (repo 側は元から正しい)。
memory `pdftotext-drops-superscripts` の典型例。

⚠ **§4 のステップ数は (1)-(10)** — 素の `^\(N\)` grep は表示式の中に置かれた (6)-(9) を
取りこぼす。census の Ch.IV は 41 → **46** に訂正。

#### Part II 補章 4 本 (書籍 pp.135-150) — **監査完了 (2026-08-08、補充 1 件)**

16 件 (App.I = 3 / II = 2 / III = 8 / IV = 3)。全件に書籍強度の実体あり。

| 書籍 | repo |
|---|---|
| **App.I Prop 1** (`F(D)` 巡回・不動点自由、`D/F(D)` 可換) | `Huppert.fitting_cyclic_fixedPointFree` (3 条項とも) ⚠ **補充 = `[IsSolvable D]` 削除**、下記 |
| **App.I Lemma** (`\|P_a\|` 一定 ⟹ `P` 巡回・不動点自由) | `Huppert.pGroup_cyclic_fixedPointFree` |
| **App.I Prop 2 (a)(b)** (`F = 𝔽_p[T]` は体、`E` は 1 次元、`U` は半線形) | `SemilinearField.exists_field_semilinear` 系 |
| **App.II Prop 1** (2-rank 1 の階数 1 群 ⟹ near-field affine model) | `NearFields.rankOne_affine_nearField` (Q₈ 込みで axiom-clean) |
| **App.II Prop 2** (`F*` が指数 2 の巡回部分群を持つ near-field の分類) | `cyclic_index_two_nearField_classification` (⚠ 旧版は `∃ classification : Prop` の opaque だったが 2026-07 に実分類へ差し替え済) |
| **App.III Def 1-3 / Lemma 1(a)-(d) / Lemma 2(a)-(c) / Theorem (a)-(e) / Prop 1 / Prop 2** | hub `Suzuki2Groups.lean` の被覆表のとおり全件。書籍は Theorem を [Hi] 引用で済ませるが **repo は Higman の分類を証明済** (`OddOrder.Higman.Suzuki2Groups`) |
| **App.IV Lemma 1(a)(b) / Lemma 2(a)(b)(c) / Theorem** | hub `FeitSibley.lean` の per-result 表のとおり全件 proved (2026-07-18 の de-opacification で opaque `Prop` フィールドを全廃済) |

**補充 — App.I Prop 1 の `[IsSolvable D]` を削除**。書籍は「`D` be a group of **odd order**」
としか仮定しないが repo は `[IsSolvable D]` も要求していた。奇数位数 ⟹ 可解は **Feit–Thompson**
で、それは本リポジトリが証明済 (`feitThompson`、2026-07-15 に axiom-clean)。
`OddOrder.FeitThompson` を import して内部で `haveI : IsSolvable D := feitThompson hD_odd`
とし、仮説を書籍どおりに戻した (import cycle なし — `FeitThompson.lean` は `Appendices/` を
一切 import しない)。下流 (`KCyclic.fitting_Dbar_cyclic_fpf_abelian`) は呼び出し側無変更。

stale docstring 訂正 1 件: App.III hub が「Theorem **(e) forward direction**」とだけ書いていたが、
逆向き (`isTypeB_of_isomorphicOrderQModuleSplit_of_card_eq_cube`、Ch.I §3 Lemma 5 が消費する側) も
`Higman/Suzuki2Groups/HigmanLemmaTwelve/TypeBRecognition.lean` に在る。

⟹ **Part II 全体 (Ch.I-IV + 補章 4 本) の逐条監査完了**。

## 4.6 Part II 監査の総括 (2026-08-08)

| 単位 | 件数 | 補充 |
|---|---|---|
| Ch.I §1 | 7 | **2** (Prop 4(c) の (A1) 一般形 / Lemma (a) の第 2 全単射) |
| Ch.I §2 / §3 | 4 / 7 | 0 |
| Ch.II | 18 | **1** (step (11) の `T ⋊ C_Q(P) ≅ F ⋊ F*`) |
| Ch.III | 16 | 0 |
| Ch.IV | 46 | 0 |
| 補章 I-IV | 16 | **1** (App.I Prop 1 の `[IsSolvable D]` 削除) |
| **合計** | **114** | **4** |

(Introduction の Theorem A を足して 115。)

**未形式化ゼロ** — Part II には Part I の (1.7)(b) に相当する残件が無い。
補充 4 件はすべて axiom-clean で landing 済。

**監査の教訓 (Part I の失敗様式リストに追加すべきもの)**:
- **失敗様式 7 = 書籍が暗黙にしている定理を repo が仮説で受ける**。App.I Prop 1 の
  `[IsSolvable D]` がこれ。「書籍が書いていない仮説がある」は特殊化債務のサインだが、
  それが**本リポジトリの既証明定理**で消せる場合がある (ここでは FT 本体)。
- **失敗様式 8 = file docstring の散文が定理の代わりをしている**。Ch.II step (11) の
  半直積同型、App.III Theorem (e) の逆向き (こちらは実在したが docstring が言及漏れ)。
  **hub/file docstring の被覆リストは grep 対象にならないので、必ず定理名まで確認する**。

### 4.5 ページ画像

`references/peterfalvi/pages/` に **pp.5-92 / pp.97-150 が全て揃った** (2026-08-08 に
pp.97-114 と pp.135-143 を `pdftoppm -png -r 200` で追加)。以後の Part II 監査で
再レンダリングは不要。

## 5. 参照

- 書籍テキスト: `references/peterfalvi/pdftotext/*.txt`
  ⚠ **表示数式は OCR レイヤが壊れており復元不能** — 式・添字の確定は `references/peterfalvi/pages/*.png`
  (無ければ `pdftoppm` で切り出して**残す**)。
- Coq 併読: `coq/theories/PFsection<N>.v` (N = 書籍 result 章番号、`S10` ではなく `8`)。
