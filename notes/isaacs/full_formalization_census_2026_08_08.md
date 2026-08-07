# Isaacs 完全形式化 — 番号 census と逐条監査 (2026-08-08 開始)

tracker = [issue 0176](../../issues/0176-isaacs-full-formalization.md)。
前身 = [issue 0172](../../issues/closed/0172-peterfalvi-full-formalization.md) (Peterfalvi 全 284 件、完了)。

## 1. 書籍側の番号 census

`references/isaacs/finite-group-theory.pdftotext.txt` から機械抽出。

⚠ **OCR が文字も数字も分解する** (`T h e o r e m` / `2 . 1 4 .`)。素朴な
`^\d+\.\d+\.\s*(Theorem|Lemma|Corollary)` では **29 件取りこぼす**。空白許容の正規表現:

```python
def sp(w): return r'\s*'.join(w)
kinds = "|".join(sp(w) for w in ["Theorem","Lemma","Corollary","Definition","Example","Notation"])
pat = re.compile(r'^\s*(\d(?:\s*\d)?)\s*\.\s*(\d(?:\s*\d)?)\s*\.\s*(' + kinds + r')\b', re.M)
```

| 章 | 件数 | 欠番 |
|---|---|---|
| Ch.1 Sylow | 46 | なし |
| Ch.2 Subnormality | 20 | なし |
| Ch.3 Split Extensions | 36 | なし |
| Ch.4 Commutators | 38 | なし |
| Ch.5 Transfer | 30 | なし |
| Ch.6 Frobenius Actions | 24 | なし |
| Ch.7 Thompson Subgroup | 8 | なし |
| Ch.8 Permutation Groups | 44 | なし |
| Ch.9 More on Subnormality | 31 | なし |
| Ch.10 More Transfer | 28 | なし |
| **合計** | **305** | **各章 1..max が連続** |

種別は全件 Theorem (135) / Lemma (105) / Corollary (65)。

## 2. ⚠ Isaacs 特有の第 4 の残債型 — 「mathlib 被覆の未記録」

Peterfalvi には無かった型。書籍の結果が **mathlib にそのまま在る**とき、repo に実体が無くても
被覆済だが、対応が記録されていないと監査で「未形式化」に誤分類される。

Isaacs Ch.1/Ch.8 のような**標準的な有限群論**では**これが主役**になる。Peterfalvi で効いた
3 型 (番号表記の揺れ / assembly を endpoint と誤認 / stale な自己注記) に加えて、
**「mathlib に在るか」を必ず確認する**。

⟹ 対処は CLAUDE.md のラッパー方針どおり: **薄いラッパーを書かず、対応を記録する**
(section docstring か `notes/` の対応表)。

## 3. 逐条監査

### Ch.8 = 先行実施 (ステップ 1、cite ゼロ 13 件)

正本 = [`ch08_permutation.md`](ch08_permutation.md) の対応表。
**12 件が mathlib 被覆 / 1 件 (8.28) が真の未形式化 → 2026-08-08 に形式化済**
(`Ch08.normal_perm_eq_bot_or_alternating_or_top` + 支持補題 `Ch08.center_perm_eq_bot`;
⚠ `Z(Sym Ω) = 1` も mathlib に無かった)。
⭐ 8.20 は mathlib のほうが一般 / ⚠ 8.21 は mathlib のほうが狭い (translate 限定)。

### Ch.1 (46 件、書籍 pp.1-30) — **進行中**

repo の cite は **46/46 に存在**。うち **docstring のアンカー位置** (`**Isaacs Thm 1.N**`) に
cite があるのは 37 件で、残り 9 件 (**1.1, 1.5, 1.6, 1.7, 1.10, 1.11, 1.17, 1.24, 1.25**) は
アンカー cite なし。実体を確認した結果、**9 件すべて mathlib 被覆**:

| Isaacs | 書籍の主張 | mathlib |
|---|---|---|
| **1.1** | `H ≤ G`、`Ω` = 右剰余類 ⟹ `G/core_G(H) ↪ Sym(Ω)`; `[G:H] = n` なら `↪ Sₙ` | `Subgroup.normalCore_eq_ker` (`Index.lean:818`) + 第 1 同型定理。系の `[G : core] ∣ n!` は repo の `Ch01.normalCore_index_dvd_factorial` |
| **1.5** | 共役類の大きさ `\|K\| = [G : C_G(x)]` | `MulAction.orbitEquivQuotientStabilizer` (`GroupAction/Quotient.lean:174`) を共役作用に適用 |
| **1.6** | `H` の共役の個数 = `[G : N_G(H)]` | 同上 (部分集合への共役作用; Sylow 版は `Sylow.card_eq_index_normalizer`) |
| **1.7** | **Sylow E** — Sylow `p`-部分群の存在 | `Sylow.exists_subgroup_card_pow_prime` (`Sylow.lean:671`) / `Sylow p G` の `Nonempty` |
| **1.10** | `K char N ⊴ G ⟹ K ⊴ G` | `ConjAct.normal_of_characteristic_of_normal` (`ConjAct.lean:270`) — repo も既に使用中 |
| **1.11** | 任意の `p`-部分群 `P` は或る Sylow の共役に含まれる | `IsPGroup.exists_le_sylow` (`Sylow.lean:167`) |
| **1.17** | `n_p(G) ≡ 1 (mod p)` | `card_sylow_modEq_one` (`Sylow.lean:344`) |
| **1.24** | 位数 `p^a` の `p`-群は各 `0 ≤ b ≤ a` で位数 `p^b` の**正規**部分群 `L ⊴ P` を持つ | ⚠ **部分被覆だった** → **2026-08-08 に補充** `Ch01.IsPGroup.exists_normal_card_eq_pow` |
| **1.25** | `p^b ∣ \|G\|` ⟹ 位数 `p^b` の部分群が在る | `Sylow.exists_subgroup_card_pow_prime` (`Sylow.lean:671`) |

✅ **1.24 の「正規」条項を確定 (2026-08-08、書籍 p.24 のページ画像)** — 書籍は `L ⊴ P` を
主張するが mathlib の `Sylow.exists_subgroup_card_pow_prime_of_le_card` は**存在だけ**を返し
**正規性を返さない** ⟹ **部分被覆**だった。repo の該当注記も自ら「弱形」と自認していた。
⟹ 書籍強度の `Ch01.IsPGroup.exists_normal_card_eq_pow` を補充 (証明は書籍と同じ `b` の帰納法で
Lemma 1.23 = `exists_normal_index_eq_prime` を `M = ⊤` に適用)。

⚠ **この判別は pdftotext では不可能** — `⊲` が `<` に落ちるので `L ⊴ P` と `L < P` が
区別できない ([[mmd-collapses-subnormal-symbol]] と同型の罠)。**ページ画像が必須**。
使用したページ画像は `references/isaacs/pages/isaacs-p015..p024.png` に保存済。

対照的に **1.25** は書籍自身が正規性を主張しない (同ページで確認) ので mathlib がそのまま
書籍強度。⟹ **「隣接する 2 つの系のうち片方だけが正規性を主張する」** ような差は、
番号 grep でも cite 数でも絶対に検出できない。ページ画像での逐条確認だけが効く。

### Ch.1 §1B-§1D の突合 (2026-08-08、書籍 pp.15-24 のページ画像)

| Isaacs | 書籍 | repo / mathlib | 判定 |
|---|---|---|---|
| 1.12 | Sylow C (共役) | mathlib `Sylow` は共役類 1 個 (`Sylow p G` の推移的作用) | ✅ |
| 1.13 | **Frattini argument** `N ⊴ G`, `P ∈ Syl_p(N)` ⟹ `G = N_G(P)N` | mathlib `Sylow.normalizer_sup_eq_top` (`Sylow.lean:498,514`) | ✅ |
| 1.14 | **Sylow D** — `p`-部分群は或る Sylow に含まれる | mathlib `IsPGroup.exists_le_sylow` | ✅ |
| 1.15 | `n_p(G) = [G : N_G(S)]` | mathlib `Sylow.card_eq_index_normalizer` (`Sylow.lean:424`) | ✅ |
| 1.18 | `P ∈ Syl_p(G)`、`Q ≤ N_G(P)` が `p`-部分群 ⟹ `Q ≤ P` | mathlib `IsPGroup.inf_normalizer_sylow` (`Sylow.lean:301`) | ✅ |
| 1.19 | `P` 有限 `p`-群、`1 ≠ N ⊴ P` ⟹ `N ∩ Z(P) ≠ 1` | `Ch01.IsPGroup.normal_inf_center_nontrivial` | ✅ 実証明 |
| 1.20 / 1.21 | 冪零 ⟺ NormalizerCondition / `Z_c(G) = G` | mathlib (`isNilpotent_of_finite_tfae` / `upperCentralSeries_nilpotencyClass`) | ✅ |
| 1.22 | **冪零 (有限とは限らない)** `G`、`H < G` ⟹ `H < N_G(H)` | `Ch01.lt_normalizer_of_isNilpotent_of_lt_top` | ✅ statement は `[Finite G]` を取らず書籍強度。⚠ **docstring が「有限冪零群」と書いていた** = statement より狭い記述 → 2026-08-08 訂正 |
| 1.23 | `N < M` が `P` の正規部分群 ⟹ `N ⊆ L ⊆ M`、`L ⊴ P`、`\|L:N\| = p` | `Ch01.IsPGroup.exists_normal_index_eq_prime` | ✅ 実証明 |

⚠ **file-header の進捗表が stale だった** — 1A が「着手中」、1B/1C/1D/1E/1G が「TODO」の
ままで、章が広範に形式化された後も放置されていた。2026-08-08 に更新
(`OddOrder/Isaacs/Ch01_Sylow/Basic.lean` 冒頭)。**この種の自己注記を監査の一次証拠にしない**。

### Ch.1 §1D-§1E の突合 (2026-08-08)

| Isaacs | 書籍 | repo / mathlib | 判定 |
|---|---|---|---|
| 1.26 | 冪零の TFAE **5 条項** ((1) 冪零 (2) `N_G(H) > H` (3) 極大部分群は正規 (4) Sylow は正規 (5) Sylow の内部直積) | mathlib `Group.isNilpotent_of_finite_tfae` | ✅ **5 条項が同順で完全一致** |
| 1.27 | 位数が対ごとに互いに素な有限正規部分群の族の積は直積 | `Ch01.iSupIndep_of_coprime_card_of_normal` | ✅ |
| 1.28 | `F(G)` は **(i) 正規 (ii) 冪零 (iii) 正規冪零部分群をすべて含む** | `Ch01.fitting.normal` (:833) / `fitting.isNilpotent` (:1149) / `nilpotent_normal_le_fitting` (:1004) | ✅ **3 条項とも** |
| 1.29 | 正規冪零 `K, L` ⟹ `KL` 冪零 | `Ch01.sup_isNilpotent_of_normal_nilpotent` | ✅ |
| 1.30 | `\|G\| = pq` (`q < p` 素数) ⟹ **(i) Sylow `p` は正規** かつ **(ii) `q ∤ p−1` なら `G` は巡回** | (i) `Ch01.sylow_normal_of_card_eq_mul_prime_lt` / (ii) `Ch01.isCyclic_of_card_eq_mul_prime_lt_of_not_dvd` (:1358) | ✅ **2 条項とも** (AxiomsCheck 未登録だったので 2026-08-08 に登録) |
| 1.31 | `\|G\| = p²q` ⟹ Sylow `p` か Sylow `q` が正規 | `Ch01.sylow_normal_of_card_eq_sq_mul_prime_lt` | ✅ |
| 1.32 | `\|G\| = p³q` ⟹ 同上 (`\|G\| = 24` を除く) | `Ch01.sylow_normal_of_card_eq_cube_mul_prime` | ✅ |
| 1.33 | `\|G\| = 24`、`n₂ > 1`、`n₃ > 1` ⟹ `G ≅ S₄` | `Ch01.mulEquiv_perm_fin_four_of_card_twenty_four` | ✅ |
| 1.34 | 「奇に作用する」元があれば指数 2 の正規部分群 | `Ch01.normalSubgroup_index_two_of_actsOddly` | ✅ |
| 1.35 | `\|G\| = 2n` (`n` 奇) ⟹ 指数 2 の正規部分群 | `Ch01.normalSubgroup_index_two_of_card_two_mul_odd` | ✅ |
| 1.36 | `\|G\| = p^a q` ⟹ 非単純 | `Ch01.exists_normal_ne_bot_ne_top_of_card_eq_pow_mul_prime` | ✅ |

### 🚨 誤判定の実例 — 「前半」を「後半が無い」と読んだ (2026-08-08)

**一度 1.30 (ii) を「部分被覆」と誤判定した**。`sylow_p_subsingleton_of_card_eq_mul_prime_lt` の
docstring が「**前半**, uniqueness form」と書いているのを見て、そこで打ち切ったため。実際には
**すぐ次の宣言**として `isCyclic_of_card_eq_mul_prime_lt_of_not_dvd` (:1358) が書籍そのままの
statement で在り、docstring も「**後半**」と明記していた。

⟹ **「前半」「弱形」「uniqueness form」等の自認語は部分被覆の指標にならない**。repo では
**対で書く慣習**があり (`Problem 3F.3 前半/後半`、`Problem 3C.5 前半/後半`、`Thm 3.11 の前半` …)、
「前半」は「この宣言が前半だ」の意であって「後半が無い」ではない。

**正しい手順**: 自認語を見つけたら**その前後 ±5 宣言を必ず読む**。1 宣言だけ見て結論しない
(Peterfalvi 監査の「assembly を endpoint と誤認」型と同根 — 本キャンペーン通算 10 件目)。

⚠ ただし **1.24 は本物の部分被覆**だった (mathlib 側に正規条項が無い)。自認語が当たる場合も
外れる場合もあるので、**判定は常に statement を読むこと**。

### Ch.1 §1A-§1B・§1F-§1G の突合 (2026-08-08) — **Ch.1 監査完了**

| Isaacs | 書籍 | repo / mathlib | 判定 |
|---|---|---|---|
| 1.2 | `[G:H] = n` ⟹ `N ⊴ G`, `N ≤ H`, `[G:N] ∣ n!` の **3 条項** | `Ch01.normalCore_index_dvd_factorial` | ✅ 3 条項とも |
| 1.3 | 単純群が指数 `n > 1` の部分群を持つ ⟹ `\|G\| ∣ n!` | `Ch01.card_dvd_factorial_of_simple_subgroup_index` | ✅ |
| 1.4 | **Fundamental Counting Principle** — 剰余類 `↔` 軌道の全単射 `Hg ↦ a*g`、特に `\|O\| = [G:G_a]` | mathlib `MulAction.orbitEquivQuotientStabilizer` | ✅ 全単射そのもの |
| 1.8 | `C(p^a·m, p^a) ≡ m (mod p)` | mathlib `Nat.choose_pow_mul_pow_mul_modEq_choose_nat` (`Choose/Lucas.lean:130`) | ✅ |
| 1.9 | Cauchy | `Ch01.cauchy` (mathlib `exists_prime_orderOf_dvd_card'` の再述) | ✅ |
| 1.16 | `n_p > 1`、`\|S ∩ T\|` 最大 ⟹ `n_p ≡ 1 (mod [S : S∩T])` | `Ch01.card_sylow_modEq_one_of_max_inter` | ✅ |
| 1.37 | **Brodkey** — Sylow `p` が可換 ⟹ `∃ S,T`, `S ∩ T = O_p(G)` | `Ch01.exists_pair_inf_eq_opCore_of_abelian` | ✅ |
| 1.38 | `S ∩ T` が極小 ⟹ `O_p(G) = S ∩ T` | `Ch01.opCore_eq_inf_of_minimal_sylow_inter` | ✅ |
| 1.39 | `P` 可換 ⟹ `[G : O_p(G)] ≤ [G:P]²` | `Ch01.index_opCore_le_index_sylow_sq` | ✅ |
| **1.40** | `P` 可換, `\|P\| > \|G\|^{1/2}` ⟹ **(i) `O_p(G) > 1`** かつ **(ii) `\|G\| ≠ p` なら `G` 非単純** | (i) `Ch01.opCore_ne_bot_of_card_sylow_sq_gt` | ⚠ **(ii) が欠けていた → 2026-08-08 に補充** `Ch01.not_isSimpleGroup_of_card_sylow_sq_gt` |
| 1.41-1.46 | Chermak-Delgado | `OddOrder/GroupTheory/ChermakDelgado.lean` (条項ごとの対応は `Ch01_Sylow/Main.lean` 末尾の docstring が正本) | ✅ 1.44(a)(b)(c) / 1.45 の 4 条項も個別に名前がある |

⚠ **1.40(ii) は本物の部分被覆**だった。1.30 で「次の宣言に在った」誤判定を出した直後なので、
今回は **repo 全体を grep して実体が無いことを確認**してから補充した。

⟹ **Ch.1 全 46 件の逐条監査完了**。補充 2 件 (**1.24 の正規条項** / **1.40(ii)**)、
誤判定 1 件 (1.30(ii)、撤回済)。

### Ch.2 Subnormality (20 件、書籍 pp.45-64) — **監査完了 (2026-08-08)**、補充 1 件

| Isaacs | 書籍 | repo | 判定 |
|---|---|---|---|
| 2.1 | 有限 `G` 冪零 **⟺** 全部分群が subnormal | `Ch02.isNilpotent_iff_all_isSubnormal` (:131) | ✅ iff |
| 2.2 | `H ≤ F(G)` **⟺** `H` 冪零かつ subnormal | `Ch02.le_fitting_iff_isNilpotent_and_isSubnormal` | ✅ iff |
| 2.3 | `S ⊴⊴ G`, `K ≤ G` ⟹ `S ∩ K ⊴⊴ K` | `Ch02.inf_isSubnormal_subgroupOf` | ✅ |
| **2.4** | `S, T ⊴⊴ G` ⟹ `S ∩ T ⊴⊴ G` | ⚠ **未形式化だった → 2026-08-08 補充** `Ch02.inf_isSubnormal` | ⚠ |
| 2.5 | **Wielandt** `S, T ⊴⊴ G` ⟹ `⟨S,T⟩ ⊴⊴ G` | `Ch02.isSubnormal_sup_of_isSubnormal` | ✅ |
| 2.6 | `S ⊴⊴ G`、`M` 極小正規 ⟹ `M ≤ N_G(S)` | `Ch02.isMinimalNormal_le_normalizer_of_isSubnormal` | ✅ |
| 2.7 | `M, N ⊴ G`、`M ∩ N = 1` ⟹ 元同士が可換 | `Ch02.commute_of_disjoint_normal` | ✅ |
| 2.8 | `S·S^x = S^x·S` (∀`x`) ⟹ `S ⊴⊴ G` | `Ch02.isSubnormal_of_permutable_with_conjugates` | ✅ |
| 2.9 | **Zipper Lemma** | `Ch02.zipper_lemma` | ✅ |
| 2.10 | `H·H^x = G` ⟹ `H = G` | `Ch02.eq_top_of_set_mul_conj_eq_top` | ✅ |
| 2.11 | **Wielandt** `A` 可換、`∀ H ⊇ A`: `[H:A]² ≤ [H:Z(H)]` ⟹ `A ≤ F(G)` | `Ch02.subset_fitting_of_index_sq_le_index_center` (`Theorem211Wielandt.lean:422`) | ✅ |
| 2.12 | **Baer** `H ≤ F(G)` **⟺** `⟨H, H^x⟩` が全 `x` で冪零 | `Ch02.le_fitting_iff_baer_sup_conj_isNilpotent` (:580) | ✅ iff (両方向 :440 / :569) |
| 2.13 | **Matsuyama** `t` 対合、`t ∉ O₂(G)` ⟹ ∃ 奇素数位数 `x`, `x^t = x⁻¹` | `Ch02.matsuyama` (`Theorem211Wielandt.lean:768`) | ✅ 書籍そのまま |
| 2.14 | 二面体型の補題 (a)(b) | `DihedralBasics.lean` の 12 宣言 | ✅ |
| 2.15 | 奇素数 `p` の `p`-local が全て正規 Sylow 2 ⟹ `G` も | `Ch02.normal_sylow_two_of_odd_pLocal_normal_sylow_two` | ✅ |
| 2.16 | 商群の `p`-local | `Ch02.isPLocal_of_quotient` | ✅ |
| 2.17 | `p ∤ \|N\|` での `p`-部分群の持ち上げ | `Ch02.map_ne_bot_of_coprime_kernel` | ✅ |
| 2.18 | **Zenkov** | `Ch02.zenkov_minimal_le_fitting` (unconditional) | ✅ |
| 2.19 | `A` 可換、`\|A\| ≥ [G:A]` ⟹ `A ∩ F(G) > 1` | `Ch02.inf_fitting_ne_bot_of_abelian_card_ge_index` | ✅ |
| 2.20 | **Lucchini** `[A:K] < [G:A]`、特に `\|A\| > [G:A]` なら `K > 1` | `lucchini_index_normalCore_lt_index` (⚠ **`Ch04_Commutators/ForwardFromCh02.lean:1084`**) | ✅ |

⚠ **2.4 の検出経路** — file-header 一覧が `Subgroup.IsSubnormal.inf` という**実在しない補題名**を
挙げていた。番号 grep では「cite あり」になるので検出できない型。
⟹ 監査手順に「**注記の挙げる補題名は実在確認する**」を追加。

⚠ **2.20 は Ch.2 のディレクトリに無い** — Main.lean には「structural reduction のみ」という
注記しかなく、本体は owner chapter 規則で **Ch04** に置かれている。章ディレクトリだけ見ると
部分被覆と誤判定する。

### Ch.3 Split Extensions (36 件、書籍 pp.65-100) — **監査中**

**アンカー cite は 36/36 に存在** (2026-08-08)。うち 5 件 (3.5, 3.8, 3.9, 3.10, 3.12) は
アンカーが無かったが、`Ch03_SplitExtensions/Basic.lean` の **§3B 対応表**に記録されており
実体を確認できた:

| Isaacs | 書籍 | 実体 | 判定 |
|---|---|---|---|
| 3.5 | 可換 `N` の Schur-Zassenhaus (存在 + 共役) | mathlib `Subgroup.exists_right_complement'_of_coprime` + 共役は 3.12 | ✅ |
| 3.8 | **Schur-Zassenhaus** 一般 (存在) | mathlib `Subgroup.exists_right_complement'_of_coprime` | ✅ |
| 3.9 | `G` 可解 **⟺** `G^{(m)} = 1` | mathlib `isSolvable_def` | ✅ iff |
| 3.10 | 可解群の基本 (部分群/商/拡大) | mathlib の `IsSolvable` instance 群 | ✅ |
| 3.11 | 可解な極小正規部分群は可換、有限なら基本可換 `p`-群 | `Ch03.solvable_minimal_normal_isAbelian` (:172、有限性不要) + `..._isElementaryAbelian` (:194) | ✅ 2 条項とも |
| 3.12 | 補元の共役性 (`N` か `G/N` が可解) | `Subgroup.IsComplement'.exists_conj_of_coprime` (**`OddOrder/Mathlib/SchurZassenhausConj.lean:1292`**) | ✅ 共役元が `N` に取れるところまで |
| 3.23 | **coprime action**: (a) `A`-不変 Sylow の存在 (b) `C_G(A)` で共役 | `exists_aInvariant_sylow` (:445) / `aInvariant_sylow_conj` (:498) — **`Ch04_Commutators/ForwardFromCh03.lean`** | ✅ 2 条項とも |
| 3.24 | Glauberman fixed-point lemma (a)(b) | `glauberman_fixed_point_exists` (:187) / `glauberman_fixed_points_conj` (:337) — 同ファイル | ✅ |

⚠ **stale な自己注記を 3 件訂正 (2026-08-08)** — Ch.3 だけで:

1. `Basic.lean:37` の進捗表「✅ **3.11 まで**」 → 実際は 3.12 まで全件。
2. `Basic.lean` §3B 対応表の 3.11「mathlib に**あるか要確認 (TODO)**」「**新規実装候補**」
   → 実装済 (同ファイル :194)。3.12 も「`IsConj` 系 + `SchurZassenhaus`」と曖昧なままだった。
3. `Main.lean` の 3.23/3.24「**placeholder**」「**~8-12 週の大規模**」 → **全 4 条項実装済**。

⟹ **Ch.1 の進捗表・Ch.2 の実在しない補題名と合わせて、stale な自己注記はこの repo で
最も頻出する誤判定源**。監査では**注記を読んだら必ず実体を grep する**。

**残り 3.13-3.22 / 3.25-3.36 も全件被覆を確認 (2026-08-08)**:

| Isaacs | 実体 |
|---|---|
| 3.13 **Hall-E** / 3.14 **Hall-C** | `Ch03` `Basic.lean:630` / `:1007` (⚠ アンカー正規表現が 3.14 を無関係な docstring に誤マッチしていた) |
| 3.15 (Hall E の逆) | ⚠ **`Ch07_ThompsonSubgroup/ForwardFromCh03.lean:34`** (owner chapter 規則で他章) |
| 3.16 / 3.17 (Wielandt) | `Theorem315.lean:33` / `:194` |
| 3.18-3.22 (π-separable / Hall–Higman 1.2.3) | `Ch03/Main.lean:28,273,521,620` |
| 3.25-3.33 (coprime action) | `Ch04_Commutators/ForwardFromCh03.lean` ほか |
| 3.34 | `exists_orbit_card_mul_of_coprime_orbit_card` (`HartleyTurull.lean:1126`) — **一般形**。abelian case (:1034) と Step 2 (:847) はその内部段 |
| 3.35 / 3.36 | `CyclicExtensions.lean:39` / `:185` |

⟹ **Ch.3 全 36 件被覆・補充ゼロ**。訂正は stale な自己注記 3 件のみ。

⚠ **3.34 で危うく誤判定しかけた** — 先に目に入ったのが「Step 2 の τ-論法」「abelian case」
だったため。ファイル冒頭の対応表 (`| Thm 3.34 | exists_orbit_card_mul_of_coprime_orbit_card | ✅ |`)
と末尾の `theorem` 一覧を見て一般形の存在を確認した。**内部段の名前が先に当たっても、
その file の endpoint を必ず確認する**。

### Ch.4-Ch.7, Ch.9-Ch.10 — 未着手 (次の入口 = Ch.4 Commutators、38 件)
