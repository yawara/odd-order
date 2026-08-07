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
