# Isaacs Ch.2: Subnormality — mini-roadmap

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.2 (pp. 45-64).
形式化先: [`OddOrder/Isaacs/Ch02_Subnormality.lean`](../../OddOrder/Isaacs/Ch02_Subnormality.lean).
原典抽出: `references/isaacs/finite-group-theory.mmd` lines 952-2123.

## 進捗 (2026-05-22)

§2A 完成 (Thm 2.11 のみ axiom). §2B 完成 (Lemma 2.14 は Matsuyama 用の焦点形式).
**§2D**: Cor 2.19 完成 (2026-05-22). Thm 2.18 Zenkov + Thm 2.20 Lucchini は依然 axiom.
§2C は依然 TODO.

### 補助補題 (mathlib 未収載)

* **`card_set_mul_card_inf`** (§2A 末尾, 2026-05-22): `|H · K| · |H ∩ K| = |H| · |K|`
  古典 group counting formula. H-action on G/K の orbit-stabilizer 経由で証明.
  Cor 2.19 (Lemma 2.10 contrapositive で計数) と Thm 2.11 (Wielandt 計数) で使用.

| # | 状態 | 実装 |
|---|---|---|
| Def `IsMinimalNormal` | ✅ | mathlib 未収載の新規述語 |
| Thm 2.1 (iff 全体) | ✅ | `isNilpotent_iff_all_isSubnormal` + 両方向 |
| Thm 2.3 | ✅ | `inf_isSubnormal_subgroupOf` (mathlib `inf_subgroupOf_right` + `IsSubnormal.subgroupOf`) |
| Thm 2.4 | ✅ (wrapper 不要) | mathlib `Subgroup.IsSubnormal.inf` を直接呼ぶ ([feedback_no_mathlib_wrapper](../../CLAUDE.md#mathlib-ラッパー方針)) |
| Lemma 2.7 | ✅ | `commute_of_disjoint_normal` (mathlib `commute_of_normal_of_disjoint` の **適応版**; instance + implicit M N) |
| **Thm 2.6** ⭐ | ✅ (2026-05-21) | **`isMinimalNormal_le_normalizer_of_isSubnormal`**. Isaacs p.46 の `|G|`-induction を直訳. socle インフラ含めて +316 行 |
| `socle` インフラ | ✅ | `def socle`, `socle.normal`, `socle.characteristic`, `IsMinimalNormal.map_equiv`, `exists_isMinimalNormal_le_of_normal`, `socle_ne_bot_of_nontrivial` |
| **Thm 2.2** | ✅ (2026-05-22) | `le_fitting_iff_isNilpotent_and_isSubnormal`. Ch.1 `fitting.characteristic` を追加して `K ⊴ G ⇒ (fitting K).map K.subtype ⊴ G` 経由で `|G|`-induction. 補助 `le_fitting_aux` 含む |
| Thm 2.5 Wielandt 結合 | ✅ | Thm 2.6 経由の `|G|`-induction |
| **Thm 2.8** | ✅ (2026-05-22) | `isSubnormal_of_permutable_with_conjugates`. |G|-induction + Zipper Lemma + normal closure. IH transfer via `Subgroup.conj_smul_subgroupOf` + `H.subtype` injective image |
| Thm 2.9 (Zipper) | ✅ | `zipper_lemma`. `S.index` 強 induction. Case A (K で S normal) と Case B (chain で T = S ⊔ S^x を構成) |
| Thm 2.10 | ✅ | `eq_top_of_set_mul_conj_eq_top`. 集合等式 `H · H^x = G` ⇒ `H = G`. `Subgroup.conj_smul_eq_self_of_mem` 経由 |
| **Thm 2.11** | ✅ (2026-05-22) | `subset_fitting_of_index_sq_le_index_center` (Wielandt). `\|G\|`-induction + IH を `K ⊋ A` に部分群対応で transfer (`Subgroup.equivMapOfInjective` + `index_comap_of_surjective` で index / center index を移送) + Zipper Lemma + 計数 (`card_set_mul_card_inf` 経由) で `\|G\|·\|Z(G)\| ≤ \|A\|²` を導出して矛盾. ~250 行 |
| **Thm 2.12 Baer 順方向** | ✅ (2026-05-22) | `baer_sup_conj_isNilpotent_of_le_fitting`. F(G) ⊴ G + 冪零 subgroup 継承の単純証明 |
| **Thm 2.12 Baer 逆方向** | ✅ (2026-05-22) | `le_fitting_of_baer_sup_conj_isNilpotent`. Zipper Lemma + Thm 2.2 経由の `|G|`-induction. IH transfer via `Subgroup.conj_smul_subgroupOf` + sup of subgroupOf + subgroupOfEquivOfLe. `x = 1` で `H` 冪零, 部分正規性は背理法 |
| Thm 2.12 Baer iff | ✅ | `le_fitting_iff_baer_sup_conj_isNilpotent` (順+逆 結合) |
| **Lemma 2.14 essence** | ✅ (2026-05-22) | `inv_by_two_involutions`: `t * z * t = z⁻¹` for `z ∈ ⟨s*t⟩`. `conj_zpow` + `inv_zpow` + involution 自己逆 |
| **Lemma 2.14 structural** | ✅ (2026-05-22) | `mem_zpowers_or_mul_t_mem_of_mem_closure_pair`: `⟨{s, t}⟩` の元は `⟨s*t⟩` か `x*t`. Closure induction 4 mul cases + 2 inv cases. Full Lemma 2.14 (`D ≅ DihedralGroup n`) は deferred |
| **Thm 2.13 Matsuyama** | ✅ (2026-05-22) | `matsuyama`: `t ∉ O_2(G)` ⇒ ∃ x odd prime order, `t*x*t = x⁻¹`. Baer iff + Cauchy + Lemma 2.14 essence + structural |
| Helper `mem_opCore_of_le_fitting_of_isPGroup` | ✅ | `H ≤ F(G)` で `H` が `p`-subgroup ⇒ `H ≤ O_p(G)`. Sylow `p` of nilpotent F(G) が unique で characteristic-in-normal 経由 |
| Helper `exists_odd_prime_dvd_of_not_pow_two` | ✅ | Nat 補助: 2-べきでない正整数は奇素数約数を持つ. 強 induction |
| §2C (Thm 2.15-2.17) | TODO | p-local 部分群. Thm 2.13 を使う |
| **Thm 2.18 Zenkov** | axiom (2026-05-22) | `zenkov_minimal_le_fitting`. minimal `M = A ⊓ B^{g₀}` (A, B abelian) ⇒ `M ≤ F(G)`. 完全証明 ~200 行, 別 commit で fill in |
| **Cor 2.19** | ✅ (2026-05-22) | `inf_fitting_ne_bot_of_abelian_card_ge_index`. `\|A\| ≥ \|G:A\|` ⇒ `A ⊓ F(G) > 1`. Zenkov axiom + Lemma 2.10 + `card_set_mul_card_inf` 計数. A = ⊤ case は G abelian ⇒ G nilpotent ⇒ F(G) = ⊤ |
| **Thm 2.20 Lucchini** | axiom (2026-05-22) | `lucchini_index_normalCore_lt_index`. cyclic 真部分群 A, K = core(A) ⇒ `\|A:K\| < \|G:A\|`. **Ch.3 Horosevskii の必須前提**. 完全証明 ~200-300 行 (Cor 2.19 を利用) |

## 章のセクション分割と全 20 定理

Isaacs Ch.2 は § 2A–2D の 4 節構成。**Isaacs FGT 全体に共通の様式として subsection
には番号のみで説明的タイトルが付かない** (PDF 直接確認済). mmd 抽出では 2A/2D ヘッダは
拾えているが 2B/2C ヘッダは抽出失敗で欠落 — ただし Problems 2A/2B/2C/2D のフッタ位置と
本文内容から境界は確実に同定できる:

| § | 書籍 pp. | 内容 | Isaacs 番号 | 主要結果 |
|---|---|---|---|---|
| 2A | 45-54 | 部分正規性の基本・join 定理・Wielandt の F(G) | 2.1 – 2.11 | Wielandt 結合定理 (2.5), Zipper Lemma (2.9), F(G) 特性化 (2.2, 2.11) |
| 2B | 55-58 | Baer の定理と Matsuyama の involution 定理 | 2.12 – 2.14 | Baer (2.12), Matsuyama (2.13) |
| 2C | 58-61 | p-local 部分群 (Isaacs 自身が「subnormality との直接関連無く脱線」と明言) | 2.15 – 2.17 | p-local 商対応 (2.16, 2.17) |
| 2D | 61-64 | Zenkov (Baer の応用) と Lucchini | 2.18 – 2.20 | Zenkov (2.18), Lucchini (2.20) |

### 全結果一覧 (mmd 行番号付き)

#### § 2A — Subnormality basics + Wielandt's F(G) (lines 952-1107)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 2.1  | Lemma   | G finite: nilpotent ⇔ 全部分群が subnormal | L968 |
| 2.2  | Theorem | H ⊆ F(G) ⇔ H が nilpotent かつ subnormal | L978 |
| 2.3  | Lemma   | S ⊴⊴ G, K ≤ G ⇒ S ∩ K ⊴⊴ K | L986 |
| 2.4  | Corollary | S, T subnormal ⇒ S ∩ T subnormal | L994 |
| 2.5  | Theorem | S, T subnormal ⇒ ⟨S, T⟩ subnormal (**Wielandt 結合**) | L1000 |
| 2.6  | Theorem | S subnormal, M minimal normal ⇒ M ⊆ N_G(S) | L1006 |
| 2.7  | Lemma   | M, N ⊴ G, M ∩ N = 1 ⇒ M と N の元同士は可換 | L1016 |
| 2.8  | Theorem | S S^x = S^x S (∀x) ⇒ S ⊴⊴ G | L1042 |
| 2.9  | Theorem | **Zipper Lemma**: S ⊴ ∀ proper H ⊇ S かつ S 非 subnormal ⇒ S を含む極大部分群は一意 | L1048 |
| 2.10 | Lemma   | H H^x = G ⇒ H = G | L1054 |
| 2.11 | Theorem | A abelian, |H:A|² ≤ |H:Z(H)| (∀ H ⊇ A) ⇒ A ⊆ F(G) | L1094 |

#### § 2B — Baer + Matsuyama (lines 1143-1177)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 2.12 | Theorem | **Baer**: H ⊆ F(G) ⇔ ⟨H, H^x⟩ nilpotent (∀x ∈ G) | L1143 |
| 2.13 | Theorem | **Matsuyama**: t involution, t ∉ O_2(G) ⇒ ∃ x 奇素位数で x^t = x⁻¹ | L1155 |
| 2.14 | Lemma   | ⟨a, b⟩ (a, b involution) が dihedral となる構造補題 | L1163 |

#### § 2C — p-local subgroups (lines 1178-1253)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 2.15 | Theorem | 全 p-local が正規 Sylow 2 ⇒ \|G\| 奇 or O_2(G) ≠ 1 | L1219 |
| 2.16 | Lemma   | G/N の p-local 部分群は G の p-local の像 | L1235 |
| 2.17 | Lemma   | p ∤ \|N\|, P p-subgroup ⇒ N_{G/N}(P̄) = N_G(P)/N | L1237 |

#### § 2D — Zenkov + Lucchini (lines 1254-2123)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 2.18 | Theorem | **Zenkov**: A, B abelian, M minimal in {A ∩ B^g} ⇒ M ⊆ F(G) | L1258 |
| 2.19 | Corollary | A abelian, \|A\| ≥ \|G:A\| ⇒ A ∩ F(G) > 1 | L1270 |
| 2.20 | Theorem | **Lucchini**: A cyclic proper, K = core_G(A) ⇒ \|A:K\| < \|G:A\| | L1280 |

## mathlib カバレッジ

**朗報**: mathlib に `Mathlib/GroupTheory/IsSubnormal.lean` (作者: Capdeboscq, Testa) が
存在し、subnormality の基本理論はかなり整備されている。

### 直接利用できるもの

| Isaacs | mathlib | 備考 |
|---|---|---|
| (def) subnormal | `Subgroup.IsSubnormal` (inductive predicate) | `top` と `step` の 2 case |
| (chain 表示) | `Subgroup.IsSubnormal.isSubnormal_iff` | `∃ n f, …` の形 |
| normal ⇒ subnormal | `Subgroup.Normal.isSubnormal` | |
| bot/top subnormal | `Subgroup.IsSubnormal.bot`, `.top` | |
| **Thm 2.3** (S ∩ K ⊴⊴ K) | 直接対応するものは無いが `IsSubnormal.subgroupOf` で `H.subgroupOf K` を扱える | |
| **Thm 2.4** (inf) | `Subgroup.IsSubnormal.inf` | 直接! |
| **Lemma 2.7** | `Subgroup.commute_of_normal_of_disjoint` | 直接! |
| (transitivity) | `Subgroup.IsSubnormal.trans` | |
| (image/preimage) | `.map`, `.comap`, `.quotient` | |
| (action) | `.smul` | |
| (simple 群の subnormal は normal) | `.normal_of_isSimpleGroup`, `.eq_bot_or_top_of_isSimpleGroup` | |
| 「proper subnormal ⊆ proper normal」 | `.exists_normal_and_le_and_lt_top_of_ne` | Wielandt 風 |

### 新規実装が必要な主要項目

* **Def `Subgroup.IsMinimalNormal`** — mathlib 未収載. Thm 2.6, 2.18 で必須.
  軽量 (3 連 conjunction).
* **Thm 2.1** (nilpotent ⇔ 全部分群 subnormal):
  Ch.1 Thm 1.26 (normalizers grow) と Isaacs の論法を組み合わせる。Ch.1 で 1.26 は ✅ 済.
* **Thm 2.2** (H ⊆ F(G) 特性化): Ch.1 で `Subgroup.fitting` ✅ 済なので、
  「F(G) は subnormal の nilpotent な和」程度の補題群を整える。
* **Thm 2.5 Wielandt 結合定理**: 本章の **キモ**.
  「S, T subnormal ⇒ ⟨S, T⟩ subnormal」. mathlib に無いので新規実装が必要.
  Isaacs の証明戦略は p.48 で明言されている: Wielandt 原論文の二重 induction
  (subnormality の定義から直接) ではなく、**Thm 2.6 (minimal normal が subnormal
  を正規化) を経由して |G| に関する induction** を行う. 流れは: minimal normal M を
  取り `G/M` で帰納仮定 → `⟨S, T⟩M ⊴⊴ G` → 2.6 で `M ≤ N_G(⟨S, T⟩)` → 結論.
  Finite 限定だが「より概念的で技術的負担が軽い」とのこと. ⇒ Lean 化も 2.6 を先に
  実装 → 2.5 はその応用、という順で攻めるのが正解.
* **Thm 2.6** (minimal normal が subnormal を正規化): 下流被引用最多 (Ch.4+ で 4 回).
* **Thm 2.8** (permutability ⇒ subnormality): Wielandt の別準位の判定法.
* **Thm 2.9 Zipper Lemma**: Thm 2.11 の証明に使う. それ以外の被引用は薄い.
* **Thm 2.11** (Wielandt の abelian-in-F(G)): 2.9 を使う.
* **Thm 2.12 Baer**: 2.11 を使う. F(G) の極めて使いやすい特性化.
* **Thm 2.13 Matsuyama**: 2.12 + 2.14 を使う. Feit-Thompson の "2-元素" 系の議論で重要.
* **Thm 2.14** (dihedral 構造補題): 2.13 の前段補助.
* **Thm 2.15-2.17** (p-local): 2.17 は下流被引用 3 回. p-local の取り扱いが標準化される.
* **Thm 2.18 Zenkov**: F(G) の "大きな abelian は当たる" を示す.
  §2D 冒頭で Isaacs 自身が "another application of Baer's theorem" と明言しており、
  **2.12 Baer の応用** として位置付けられている. ⇒ 2.12 完了後すぐ着手可.
* **Thm 2.19** 系: 2.18 直系.
* **Thm 2.20 Lucchini**: cyclic 真部分群の core の下限. Isaacs Ch.10 や BG/Peterfalvi での
  index 比較で使う可能性あり (要確認).

## Ch.2 から下流への被引用 (Isaacs 内)

Ch.4 以降の本文 (mmd) で `Theorem|Lemma 2.X` 形式を grep:

```
4 回: Theorem 2.6  (minimal normal が subnormal を正規化)
3 回: Lemma 2.17   (p-local の商対応)
1 回: Theorem 2.13 (Matsuyama)
1 回: Lemma 2.14   (dihedral)
```

→ Ch.2 結果は意外と Isaacs 章間では引用が少ない. ただし **Thm 2.2 (F(G) 特性化)** や
**Thm 2.12 Baer** は名前を呼ばずに使われている可能性があり, 引用数だけで優先度を
決めるのは早計.

### BG / Peterfalvi での引用について (注意)

Peterfalvi mmd では `[Is], Lemma 2.21`, `Corollary 2.23`, `Lemma 2.27`, `Corollary 2.30`
等の表記が頻出するが、これは **Isaacs *Character Theory of Finite Groups* (1976)** を
指す引用であり、本プロジェクトの Isaacs *FGT* (2008) Ch.2 とは無関係 (Ch.2 の最後の
番号は 2.20).  BG は Gorenstein 1968 (**G** 表記) を引くが、これも FGT とは別物.

⇒ FGT Ch.2 の結果が BG/Peterfalvi で必要かどうかは、引用テキスト名 (Wielandt, Baer,
Matsuyama, Lucchini, Zenkov) で別途調査する必要がある.

## 着手順 (提案)

BG/Peterfalvi 引用調査の結果、Ch.2 結果は FT 経路では名前ベース引用されないが、
Phase 1 完全形式化として全て書く必要はある. 依存と新規実装コストで並べると:

1. **§2A 序盤 (Def `IsMinimalNormal`, Thm 2.1, 2.2, 2.3, 2.4, 2.7)** — mathlib
   `IsSubnormal` + Ch.1 `fitting` / `IsNilpotent` のラッパー仕事が中心.
   `IsMinimalNormal` 述語の自前定義もここで導入.
2. **Thm 2.6** (minimal normal が subnormal を正規化) — 章内で 2.5, 2.11 の証明に
   必要. Isaacs Ch.4+ で下流被引用最多 (4 回).
3. **Thm 2.5 Wielandt 結合定理** — 2.6 を経由した |G|-induction で証明.
4. **Thm 2.10 → 2.8 → 2.9 Zipper Lemma → Thm 2.11** — §2A 後半. 2.9, 2.11 は本章の
   キモの一つ.
5. **§2B (Thm 2.12 Baer, 2.13 Matsuyama, 2.14 dihedral)** — 2.11 から 2.12 への流れは
   そのまま. 2.13/2.14 は dihedral 構造の独立補助.
6. **§2C (Thm 2.15-2.17)** — p-local の準位上げ. mathlib `Subgroup.normalizer` +
   quotient で組める.
7. **§2D (Thm 2.18-2.20)** — Zenkov (Baer 応用) と Lucchini. **BG/Peterfalvi 直引用
   無し**なので最後回し可.

FT クリティカル度 (実引用 + 名前): 低い. Phase 1 完成度のために実装するが、急がない.

## 開発時の注意点

* Isaacs の `S ⊴⊴ G` (subnormal の二重三角) は LaTeX 抽出で
  `\ltimes\!\!\!\triangleleft` のような乱雑な形になっている. mmd grep する際は
  上記の文字列パターンか単語 "subnormal" を使う.
* `O_p(G)` は Ch.1 で `Subgroup.opCore` として実装済 (commit 95e7e62). 2.13 で使う.
* `F(G)` は Ch.1 で `Subgroup.fitting` として実装済 (commit 08012c2). 2.2, 2.11, 2.12, 2.18 で使う.
* dihedral 群 (2.14) は mathlib に `DihedralGroup` があるが、Isaacs の Lemma 2.14 は
  「⟨a, b⟩ の構造から dihedral と判定する」方向. mathlib の `DihedralGroup` は
  プレゼンテーションからの構成なので、橋渡し補題を別途書くことになる可能性あり.

## 解決済みの確認

### PDF 直接確認 (2026-05-21)

* ~~§2B/2C ヘッダ欠落~~ → Isaacs FGT 全体に共通する様式として **subsection には
  番号のみで説明的タイトルが付かない**. mmd の 2B/2C ヘッダ欠落は Nougat の偶発
  抽出失敗で、本来の本にはタイトル文字列は無い. 境界は問題なく同定可能.
* ~~Thm 2.5 の証明戦略~~ → Isaacs は **2.6 経由で minimal normal M による induction
  on |G|** (p.48 で明言). Wielandt 原論文の二重 induction は不採用. ⇒ 2.6 → 2.5
  の順で攻める.

### BG/Peterfalvi 引用調査 (2026-05-21)

BG/Peterfalvi の mmd 全体を Ch.2 主要結果の **名前** で grep:

| 名前 | BG | Peterfalvi |
|---|---|---|
| Zenkov | 0 件 | 0 件 |
| Lucchini | 0 件 | 0 件 |
| Baer | 0 件 | 0 件 |
| Matsuyama | 1 件 (索引のみ, "Matsuyama, H., 74") | 0 件 |
| Wielandt | 2 件 (BG §3 Frobenius の proof 帰属, p.18 bib — **どちらも Thm 2.5 join 定理ではない**) | 0 件 ("Wielandt's fixed point theorem" は [HB] からの別物) |

⇒ **Isaacs Ch.2 の名前付き定理 (Wielandt join, Baer, Matsuyama, Zenkov, Lucchini)
は BG/Peterfalvi の proof で直接引用されない**. BG は独自の §1 "Elementary Properties
of Solvable Groups" (P. Hall の `C_G(F(G)) ⊆ F(G)` (Prop 1.3), Lemma 1.1 "minimal
normal solvable ⇒ ⊆ Z(F(G)) かつ elementary abelian", Prop 1.4 等) で必要な F(G)
理論を自前構築している. ⇒ **§2B/§2D は FT 経路としてのクリティカル度は低い**.
**§2C** (p-local) は名前無しで標準論法として使われる可能性は残るが、これは mathlib
の Subgroup.normalizer + Quotient で直接対処可.

Phase 1 完全形式化として Ch.2 は全て書く必要があるが、**着手順としては §2A 基盤
→ §2C → §2B → §2D** が FT 本筋への寄与を最大化する順. ただし §2A 内では Isaacs
の証明依存により 2.6 → 2.5 → 2.9 → 2.11 → ... の章内順は維持.

### mathlib `IsSubnormal` 使い勝手プロトタイプ (2026-05-21)

`/tmp/test_subnormal.lean` で全 6 ケース型チェック通過 (Thm 2.6 のみ意図的 sorry):

1. ✅ `IsSubnormal.bot`, `.top`, `.inf`, `.subgroupOf` がそのまま使える
2. ✅ `isSubnormal_iff` で Isaacs chain 表記に戻せる
3. ✅ **inductive recursor `induction hS with | top | step` が綺麗**. step ケースの
   引数は `(H K : Subgroup G) (h_le : H ≤ K) (hSubn : K.IsSubnormal) (hN : (H.subgroupOf K).Normal) (ih : P K)` で
   Thm 2.5 等の |G|-induction にそのまま流せる
4. ⚠ `Subgroup.normalizer : Set G → Subgroup G` 型なので `S.normalizer` field
   notation が失敗. `Subgroup.normalizer (S : Set G)` 明示で OK
5. ✗ **mathlib に `Subgroup.IsMinimalNormal` 述語が無い**. `IsAtom` は subgroup
   lattice 全体に対するもので normal lattice ではないので不可.
   ⇒ Ch.2 内で自前定義が必要:
   ```lean
   def Subgroup.IsMinimalNormal (M : Subgroup G) : Prop :=
     M.Normal ∧ M ≠ ⊥ ∧ ∀ N : Subgroup G, N.Normal → N ≤ M → N = ⊥ ∨ N = M
   ```
   これは Thm 2.6 でも 2.18 Zenkov でも使う. 軽量だが Ch.2 冒頭で出す.
