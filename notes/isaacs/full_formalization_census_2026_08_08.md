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

### Ch.2-Ch.7, Ch.9-Ch.10 — 未着手 (次の入口 = Ch.2 Subnormality、20 件)
