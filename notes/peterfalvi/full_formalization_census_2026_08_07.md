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
| (4.9)(a) | ✅ 実証明 (主要主張) / ⚠ 1 節が未確認 | `S06_CertainTypeConjugation`: 共役 bridge `:200` / `μ̄_{ij} = μ_{i'j'}` `:223` / `μ̄_j = μ_{j'}` (列和形) `:249` / `μ̄_k ≠ μ_k` `:298`。`0 ≠` の部分は `certainType_nonzero` (`S06_CertainTypeCoherence:524`)。⚠ **`ℤ[T, L^#] = ℤ[T, A]` の等式そのものは statement として見つからない** — (4.7)(v) (`Supp μ_j ⊆ A ∪ {1}`) から従うはずで、repo は `IsCoherent` を最初から `ℤ[T,A]` 相対で述べるので不要になっている。`S10_SubcoherentTypeP:72,297` が下流でこの等式に言及し「(4.7) から得る」と書いている。**低優先の要確認** |
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
| **(5.2)(b) の `L^#` vs `A`** | ⚠ **繰延項目と直結** | 書籍は `τ : ℤ[S, L^#] → ℤ[Irr G, G^#]` の等長。repo は **`ℤ[S,A]` 相対**。docstring が理由を明記: FT の Dade 写像には**大域的な等長は存在しない** (`dim CF(L) > dim CF(G)`)、かつ pre-0099 の全メンバー差分形は混合次数の族で**偽**。書籍の `L^#` 版と一致するのは **`ℤ[S,L^#] = ℤ[S,A]`** (= (4.7) 由来) による。⟹ **繰延項目「(4.9)(a) の `ℤ[T,L^#] = ℤ[T,A]` 等式」は §5 にも効く橋渡し**で、当初思ったより load-bearing。優先度を上げて扱うこと |
| (5.3)(a)(b) | ⬜ **未監査** | (b) は `S06_CertainTypeSubcoherent` に集中 (`:17` に書籍原文引用、`:53` `:77` `:132` `:238`)。`AxiomsCheck:13719`/`:13736` が「**(5.3)(b) at book strength**」(issue 0159 second pass) と記録。⚠ 「`R(φ)` は全ての `ω ∈ Irr(W)` に対し `ω^σ` と直交」の節も確認 |
| (5.4)-(5.9) | ⬜ **未監査** | 書籍 pp.26-29 未読 |

⚠ **既知の罠**: (5.3)(b) の族の条件は `θ ≠ 1_K` **ではなく** `H ⊄ Ker θ`
(memory [[read-book-hypothesis-before-adding-side-condition]] — 過去に取り違えて 1 session 誤診した)。

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
