# Isaacs Ch.6: Frobenius Actions — mini-roadmap

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.6 (pp. 177-200).
形式化先: `OddOrder/Isaacs/Ch06_FrobeniusActions/Main.lean`.
原典抽出: `references/isaacs/finite-group-theory.mmd` lines 3313-3712.
ROADMAP 上の位置: **第 4 波 (Ch.4 → Ch.5 → Ch.6 シーケンス)** — Ch.6 → Ch.7 (Thompson, ZJ) と Ch.10 (More Transfer) への分岐点で **Phase 1 の山場の入口**. 前提は Ch.3 (Hall + coprime action, 特に Thm 3.23 A-invariant Sylow) + Ch.4 + Ch.5 (Thm 5.26 Frobenius normal p-complement).

## TL;DR — **Phase 1 の核**、mathlib カバレッジは薄い、BG/Peterfalvi 両者で多用

**FT 経路で本書最重要章のひとつ**. BG §3 "Actions of Frobenius Groups" は本章を直接前提し (BG L799-1329 で Frobenius 群を多用), Peterfalvi §10-§14 でも "Frobenius group with kernel" が maximal subgroup 分類の中核語彙として現れる ((9.1) Wielandt 作用, (10.7) [S,S] が Frobenius など).

**mathlib カバレッジは Ch.5 と対照的に薄い**:
- `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean` (DihedralGroup n)・`Quaternion.lean` (QuaternionGroup n; 一般化四元数, 位数 4n) は具体群として実装済
- **`FrobeniusGroup` 定義は mathlib 完全未収載** — `grep "FrobeniusGroup\|isFrobenius"` 全マッチ 0 件
- 半二面体 `SemiDihedral` も mathlib 未収載
- ⇒ **Frobenius 群の定義と基本性質 (6.1-6.7) は新規実装が必要な大きな山**

**章内最重要**: Thm 6.7 (G = NA で N の非単位元中心化群が N に入る ⇔ G が Frobenius), Thm 6.17 (Frobenius complement のSylow は cyclic or quaternion), Thm 6.22-6.24 (**Frobenius kernel nilpotent**, BG L825 で明示引用). Thm 6.23 (Thompson normal p-complement, p odd) は **Ch.7 J(P), ZJ 章への橋渡し**.

## 章のセクション分割と全 24 結果

mmd で `### Problems 6a` (L3406), `### Problems 6B` (L3627), `### Problems 6c` (L3702) が捕捉済. §6B 本文の `**6b**` (L3469) と §6C の `**6C**` (L3662) はインライン text marker で `###` ヘッダ無し:

| § | mmd 行 | 内容 | Isaacs 番号 | 主要結果 |
|---|---|---|---|---|
| 6A | 3315-3405 | Frobenius action の定義と equivalence | 6.1 – 6.7 | order coprime (6.1), quotient 保存 (6.2), even ⇒ 唯一 involution + N abelian (6.3), Frobenius 群の等価条件 (6.4), counting (6.5, 6.6), **6.7 C_G(n) ⊆ N ∀n ⇒ Frobenius** |
| 6B | 3469-3626 | Frobenius complement の Sylow 構造 (partition + p-group classification) | 6.8 – 6.21 | partition counting (6.8), **6.9 elementary abelian p^2 不可・solvable Frobenius 不可**, ≤1 subgroup of order p (6.10), **6.11 ⇒ cyclic or quaternion**, 6.12 normal-abelian-cyclic ⇒ classification, 6.13 cyclic index 2 nonab 2-group ⇒ D/Q/SD, **6.17 Frobenius complement: 各 Sylow が cyclic or quaternion**, 6.18 odd order ⇒ A', A/A' cyclic + coprime, 6.19 odd order ⇒ unique subgroup of order p, 6.20-6.21 abelian coprime action + ⟨C_N(a)⟩ |
| 6C | 3662-3701 | Frobenius kernel nilpotent + Thompson normal p-complement | 6.22 – 6.24 | **6.22 solvable Frobenius kernel ⇒ nilpotent (G. Higman)**, **6.23 Thompson normal p-complement (p odd, char subgroup 版)**, **6.24 Frobenius kernel ⇒ nilpotent (Thompson)** |

mmd 抽出失敗は無し (MISSING_PAGE marker ゼロ, ヘッダ欠落は §6B/§6C の `### ` 形式のみで `**...**` text marker は健在).

### § 6A — Frobenius action basics (lines 3315-3405)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 6.1 | Lemma     | Frobenius action ⇒ \|N\| ≡ 1 mod \|A\|, つまり \|A\|, \|N\| coprime | L3321 |
| 6.2 | Corollary | A-invariant 正規 M ⇒ A の N/M 作用も Frobenius | L3325 |
| 6.3 | Theorem   | \|A\| even, N ≠ 1 ⇒ A は唯一の involution を持ち N abelian | L3337 |
| 6.4 | Theorem   | G = NA, A complement: A の N 作用 Frobenius ⇔ A ∩ A^g = 1 ∀g ∉ A ⇔ A は自己正規化 + 共役間で disjoint | L3369 |
| 6.5 | Lemma     | A ∩ A^g = 1 ∀g ∉ A, X = {A の非単位元 と非共役な元} ⇒ \|X\| = \|G\|/\|A\| (counting) | L3378 |
| 6.6 | Corollary | 上記設定で X = N ちょうど (= A non-trivial 共役以外の和集合) | L3382 |
| 6.7 | Theorem   | **N ◁ G, C_G(n) ⊆ N ∀ 非単位元 n ∈ N ⇒ N は補集合を持ち, 1<N<G なら G が Frobenius 群 (kernel N)** | L3402 |

### § 6B — Frobenius complement Sylow structure (lines 3469-3626)

`**6b**` text marker (L3469) で section 開始. partition の概念 (= 自明な intersections + cover) を導入し, Frobenius complement の Sylow が cyclic か一般化四元数に分類される.

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 6.8  | Lemma     | **partition counting**: Π が A の partition, A が abelian U に作用, U に order ∤ \|Π\|−1 の元 ⇒ ∃ X ∈ Π, C_U(X) > 1 | L3477 |
| 6.9  | Theorem   | **Frobenius complement A ⇒ (i) elementary abelian p^2 を含まない, (ii) 可解 Frobenius 群 部分群を含まない, (iii) 位数 pq 部分群は cyclic** | L3491 |
| 6.10 | Corollary | P ∈ Syl_p(Frobenius complement) ⇒ P は位数 p の部分群を **高々 1 つ** | L3501 |
| 6.11 | Theorem   | **p-group が位数 p の部分群 ≤ 1 つ ⇒ cyclic, または p=2 で一般化四元数** | L3509 |
| 6.12 | Theorem   | p-group で全 normal abelian 部分群が cyclic ⇒ cyclic / p=2 dihedral / generalized quaternion / semidihedral | L3515 |
| 6.13 | Lemma     | 非可換 2-group P が index 2 cyclic 部分群を持ち c^a = c^{-1} (or zc^{-1}) ⇒ dihedral / Q / SD | L3523 |
| 6.14 | Corollary | 位数 8 非可換 ⇒ D_8 または Q_8 | L3529 |
| 6.15 | Lemma     | p-group T, \|T:Z(T)\| = p^2, cyclic Z(T) < C < T, \|T\| ≠ 8 ⇒ T は特性的 elementary abelian 部分群 (位数 p^2) を持つ | L3533 |
| 6.16 | Lemma     | i^p ≡ 1 mod p^e に対する i mod p^e の構造分類 (p 冪剰余) | L3545 |
| 6.17 | Corollary | **Frobenius complement A ⇒ A の各 Sylow は cyclic または一般化四元数** | L3579 |
| 6.18 | Corollary | **odd order Frobenius complement A ⇒ A', A/A' は cyclic で coprime orders** | L3585 |
| 6.19 | Theorem   | odd order Frobenius complement A ⇒ 各 p ∣ \|A\| について A は位数 p の部分群を一意持つ | L3591 |
| 6.20 | Lemma     | abelian A 忠実 coprime, 全 proper A-invariant 部分群への作用が自明 ⇒ A cyclic | L3603 |
| 6.21 | Theorem   | **abelian A coprime, A not cyclic ⇒ N = ⟨C_N(a) ∣ 1 ≠ a ∈ A⟩** (Ch.7 で使用) | L3607 |

### § 6C — Frobenius kernel nilpotent + Thompson (lines 3662-3701)

`**6C**` text marker (L3662) で section 開始. Thompson の Ph.D. 論文の結果 (Frobenius kernel nilpotent) を G. Higman の可解版 (6.22) → Thompson 一般 (6.24) の順で示し, 中継として Thompson normal p-complement (6.23) を **証明無しで引用** (Ch.7 §7 で別経路の改良版を証明).

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 6.22 | Theorem | **solvable Frobenius kernel N ⇒ N nilpotent (G. Higman 1957)** | L3666 |
| 6.23 | Theorem | **Thompson normal p-complement** (p ≠ 2, P ∈ Syl_p, N_G(X) has normal p-comp ∀ 非単位 char X ⊆ P ⇒ G has normal p-comp). **本章では証明なし, Ch.7 で改良版を証明** | L3684 |
| 6.24 | Theorem | **Frobenius kernel N ⇒ N nilpotent (Thompson, 一般版)** — 6.22 + 6.23 から | L3694 |

## mathlib カバレッジ

**Ch.6 主要結果のうち直接利用可は具体群レベルのみ**. Frobenius 群そのものは未収載で **Phase 1 の主要新規実装**.

### 直接利用できるもの

| Isaacs | mathlib | 備考 |
|---|---|---|
| DihedralGroup (Thm 6.13, 6.14) | `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean` `DihedralGroup n` | r, sr 生成元と関係, 位数 2n |
| 一般化四元数 (Thm 6.11, 6.13, 6.14, 6.17) | `Mathlib/GroupTheory/SpecificGroups/Quaternion.lean` `QuaternionGroup n` | a, xa 生成元, 位数 4n, `quaternionGroup_one_isCyclic` 等 |
| Q_8 | `QuaternionGroup 2` (位数 8) | |
| D_8 | `DihedralGroup 4` (位数 8) | |
| Cor 6.14 D_8 / Q_8 一意性 | mathlib **未収載** だが `Dihedral` と `Quaternion` の cardinality 8 case を計算するだけ | 構成可能 |
| 6.16 i^p ≡ 1 mod p^e 分類 | mathlib `ZMod.pow_eq_one_iff` 系で部分対応, 完全分類は **未収載** | 中 |
| Thm 6.23 (Thompson p-comp) | mathlib **未収載** (Thompson の改良版である Ch.7 全体が未収載) | 大 |

### 新規実装が必要な主要項目

| Isaacs | 状況 | コスト見積もり |
|---|---|---|
| **`FrobeniusGroup`, `FrobeniusAction` 定義** | mathlib 完全未収載. 中核 def | **大** (Phase 1 の主要設計判断: TI-subset / disjoint conjugates / fixed-point free 等のいくつかの等価定義をどう選ぶか) |
| 6.1 \|N\| ≡ 1 mod \|A\| | 新規 (def 依存) | 短 (counting 経由) |
| 6.2 quotient Frobenius | ✅ `IsFrobeniusAction.quotient` (Cor 3.28 経由) | 完了 |
| 6.3 even ⇒ involution + N abelian | 新規 (counting + involution 引数) | 中 |
| **6.4 Frobenius 群の等価条件** | 中核補題 — 4 通りの等価定義. mathlib 未収載. **TI** 概念とも接続 | 大 |
| 6.5, 6.6 counting (X = G − ⋃A^g) | 新規 (Burnside counting 流) | 中 |
| **6.7 C_G(n) ⊆ N ⇒ Frobenius** | 章の入口の主要定理. 5.26 / Frobenius normal p-complement と関連 | 大 |
| 6.8 partition counting | 新規. abelian U 上の \|Π\|-1 引数 | 中 |
| **6.9 Frobenius complement banned structures** | 6.8 を使い elementary abelian / solvable Frobenius を排除. Thompson 流の核心引数 | 大 |
| 6.10 ≤1 subgroup of order p | 新規 (6.9 系) | 短 |
| **6.11 p-group ≤1 subgroup p ⇒ cyclic or quaternion** | **古典的 p-群分類定理**. mathlib 未収載. Q_8 構造判定 + induction | 大 |
| 6.12 normal abelian cyclic ⇒ cyclic / D / Q / SD | **半二面体群 (`SemiDihedral`) の新規定義** + 構造判定 | 大 |
| 6.13 cyclic index 2 ⇒ D / Q / SD | 6.12 補助. 直接行列演算 | 中 |
| 6.14 \|P\|=8 非可換 ⇒ D_8 or Q_8 | 6.13 系 | 短 |
| 6.15 \|T:Z(T)\|=p^2, T≠8 ⇒ char elementary abelian p^2 | p-group 構造補題 | 中 |
| 6.16 i^p ≡ 1 mod p^e 分類 | 数論補題. mathlib `ZMod` API 上に直接書ける | 中 |
| **6.17 Frobenius complement: 各 Sylow cyclic or quaternion** | **6.9 + 6.10 + 6.11 + 6.16 を結合**. 章のハイライト | 中 (他結果に依存) |
| 6.18 odd order ⇒ A', A/A' cyclic + coprime | 6.17 + Z-group 経由 (`IsZGroup.coprime_commutator_index` 借用可) | 中 |
| 6.19 odd order ⇒ unique p-subgroup | 6.17 + cyclic Sylow | 短 |
| 6.20 abelian faithful coprime + proper A-inv trivial ⇒ A cyclic | coprime action + Frobenius 定義 (6.4) 経由 | 中 |
| **6.21 ⟨C_N(a)⟩ = N** | **Ch.7 J(P), ZJ で頻用**. 短い induction だが構造美しい | 中 |
| **6.22 solvable Frobenius kernel nilpotent** | **古典 Higman 1957**. 章の主結果. mathlib `IsNilpotent` ベースで induct + Sylow + minimal normal | 中 (Frobenius def + 6.8 で機械的) |
| **6.23 Thompson normal p-complement (char-X 版)** | **Ch.7 で改良版を証明する都合**で Ch.6 では statement のみ提示 (証明 skip). Ch.6 内では使わないので **statement だけ書いて Ch.7 に sorry / `axiom` 一時的に置く案も可** | (Ch.7 範疇) |
| **6.24 Frobenius kernel nilpotent (Thompson)** | **6.22 + 6.23** から導出. 6.23 を Ch.7 完了後に閉じる | 中 |

### mathlib カバレッジ概観

| 種別 | 数 | 比率 |
|---|---|---|
| 直接利用可 (Dihedral, Quaternion specific groups) | 2 / 24 | 8% |
| 同等概念有り、変換必要 | ~3 / 24 | 13% |
| 新規実装が必要 | ~19 / 24 | **79%** |

Ch.5 (mathlib カバー厚) と対照的に **Ch.6 は新規実装中心**. Phase 1 内で Ch.1, Ch.7 と並ぶ「重い章」.

## 下流被引用 (Isaacs Ch.7+, BG, Peterfalvi)

### Isaacs Ch.7-10 内 (mmd L3713-末尾を grep)

```
2 Theorem 6.11   ← p-group ≤1 subgroup p ⇒ cyclic/quaternion
1 Theorem 6.20   ← abelian faithful coprime trivial proper ⇒ cyclic
1 Theorem 6.23   ← Thompson normal p-complement (Ch.7 で改良版証明時に引用)
1 Lemma 6.20     ← 同上
```

Ch.6 は Isaacs 内では **Ch.7 (Thompson J(P), ZJ) への入口**として機能. 直接被引用数は控えめだが Frobenius 群定義 (6.4) と Frobenius kernel nilpotent (6.24) は Ch.7 で **概念的に前提**.

### BG での引用 (`references/bg/local-analysis.mmd`)

**BG §3 "Actions of Frobenius Groups" は Ch.6 を全面的に前提**. BG の本章引用は Isaacs ナンバリングではなく `**G**` (Gorenstein 1968) ないし BG 内 独自再述. 主要引用:

| BG 箇所 | Isaacs Ch.6 対応 | 概要 |
|---|---|---|
| **L799** | 6.4 / 6.7 | "G is a Frobenius group with Frobenius complement R and Frobenius kernel K" 定義導入 |
| **L814** | 6.4 | `G, Theorem 2.7.7, p.39` = "G が Frobenius ⇔ A ∩ A^g = 1 + A self-normalizing" (Isaacs 6.4 の Gorenstein 版) |
| **L820 Lemma 3.2** | 6.2 + 6.7 結合 | "G = KR Frobenius, N ◁ G, K ⊄ N ⇒ G/N も Frobenius" (Isaacs 6.2 の精緻化) |
| **L825 Note** | **6.24** | "Thompson's Thesis (G, Theorem 10.2.1) implies kernel nilpotent (G, Theorem 10.3.1(iii))" = Isaacs 6.24 |
| **L845 Lemma 3.3** | 表現論的拡張 | "G = KR Frobenius が V 上に作用, char ∤ \|K\| ⇒ K nontrivial ⇒ C_V(R) ≠ 0" (Ch.6 にはない. mathlib に近い結果あるかも) |
| **L903 Thm 3.5** | Ch.6 + 表現論 | "G = KR solvable Frobenius, cyclic R prime, dim C_V(R) = 1 ⇒ K' ⊆ C_K(V)" |
| **L1267 Thm 3.10** | Ch.6 + Hall | "G = KR solvable Frobenius が nilpotent M 上に作用" — 構造詳細 |

⇒ **BG §3 全体が Isaacs Ch.6 の表現論的拡張**. Phase 1 で Ch.6 が完成すれば Phase 2a §3 は **BG 流の追加結果 (3.3-3.10 等) を Ch.6 ベースで Frobenius action 一般から記述** する形に進む.

### Peterfalvi での引用 (Frobenius は中心語彙)

| Peterfalvi 箇所 | 用法 | Isaacs Ch.6 対応 |
|---|---|---|
| 04.10:15 (10.X) | "HU_0 is a Frobenius group with kernel H" | 6.4 / 6.7 (定義) |
| 04.10:23 (10.X) | "M is a Frobenius group with kernel H iff Sylow subgroups of U are cyclic" | **6.17** (Frobenius complement Sylow cyclic) |
| 04.10:27 | "**[BG], Proposition 3.9** ⇒ Frobenius complement of odd order has cyclic Sylow" | **6.17 を BG 経由で参照** |
| 04.11:5 (9.1) | "U ⋊ E Frobenius with kernel U が solvable H に coprime に作用" → Wielandt | 6.4 + Ch.3 |
| 04.11:11 | "**[HB] Chapter XI, Theorem 12.4** = Wielandt's fixed point theorem" | (Ch.6 外, Huppert/Blackburn) |
| 04.11:105 | "**[Is] Theorem 6.34** = Frobenius group irreducible character classification" | **注: Isaacs 別書** (Character Theory of Finite Groups, AMS GSM 359). FGT Ch.6 とは別の参照 |
| 04.12:13, 69, 71 (10.7) | "M^{prime} ⋊ W_1 / [S,S] / HU/ M_F が Frobenius group with kernel X" 多用 | 6.4 / 6.7 |

⇒ Peterfalvi 本体 §10-§14 は **maximal subgroup 分類で Frobenius という言葉を中核語彙として使用**. Ch.6 は Phase 2b に進む前提として必須.

注: Peterfalvi の `[Is]` 引用は **Isaacs *Character Theory of Finite Groups* (AMS GSM 359, 2006)** であって本プロジェクトの一次参照 (FGT) とは別書. Ch.6 character-theoretic 拡張 (Frobenius group の irreducible character 分類) は CT 本側に属し, FGT Ch.6 (本ノート対象) には含まれない.

## 章内依存 (Ch.6 内で 6.X が引用される頻度)

`awk` で Ch.6 本文 (L3313-3712) を切り出し grep:

```
最頻 被引用 (証明本文中):
- 6.8  (partition counting)               — 6.9, 6.22 の核
- 6.7  (C_G(n) ⊆ N Frobenius 判定)        — 6.22, 6.24 の核
- 6.2  (quotient Frobenius)                — 6.22, 6.24 の induction step
- 6.11 (p-group ≤1 subgroup p classification) — 6.17 の核
- 6.4  (Frobenius equivalent definitions)  — §6B-§6C 全般
- 6.16 (i^p ≡ 1 mod p^e)                  — 6.17 odd Frobenius complement 構造
- 6.22 (solvable Frobenius kernel nilpotent) — 6.24 の base case
- 6.23 (Thompson char-X p-complement)      — 6.24 inductive step (Ch.7 で改良版証明)
```

**章内ハブ**:
- §6A: 6.1 → 6.2 → 6.3, 6.4 → 6.5, 6.6 → **6.7** (章の入口)
- §6B 前半 (Frobenius complement 構造): **6.8** → **6.9** → 6.10 → **6.11**
- §6B 後半 (p-group 分類): 6.12 → 6.13 → 6.14, 6.15, **6.16** → **6.17** → (6.18, 6.19)
- §6B 末: **6.21 ⇒ 6.20 (one-way)** — mmd L3625 で 6.20 が 6.21 の corollary (2026-05-22 audit 訂正; 元 "相互参照" は誤り)
- §6C: **6.22** + **6.23 (axiom)** → **6.24** (Thompson)

## 着手順 (提案)

FT クリティカル度 + 章内依存で並べる:

1. **`FrobeniusGroup` / `FrobeniusAction` 定義** — 最重要設計判断. TI (`MulAction.IsTrivialIntersection`) 概念 (mathlib `Mathlib/GroupTheory/GroupAction/Blocks.lean` 周辺), `IsSemiregular`, `IsRegular` 等の既存 API との組合せで形成.
2. **§6A 全 (6.1-6.7)** — 定義 + 6.4 等価条件が肝. **6.7 が章の入口主要定理**.
3. **6.16 (i^p ≡ 1 mod p^e)** — 数論補題, mathlib `ZMod` 上の純粋計算. 早めに片付ける.
4. **6.13, 6.14 (cyclic index 2 + 位数 8 非可換 分類)** — mathlib `DihedralGroup`, `QuaternionGroup` を直接利用.
5. **6.12 + `SemiDihedral` 定義** — 半二面体群を `OddOrder/GroupTheory/SemiDihedral.lean` (将来 mathlib upstream) として新規実装. **6.12 を 6.11 より先**: mmd L3519 で 6.11 は 6.12 の corollary と明示 (2026-05-22 audit 訂正; 旧記載は順序逆).
6. **6.11 (p-group ≤1 subgroup p ⇒ cyclic or quaternion)** — 6.12 から 5-10 行の系として導出.
7. **6.8, 6.9, 6.10** — partition + Frobenius complement の禁止構造. 6.7 の応用.
8. **6.17 + 6.18 + 6.19** — Frobenius complement Sylow 分類の主結果. **FT クリティカル**.
9. **6.20, 6.21** — Ch.7 J(P), ZJ への前提結果. 比較的短い.
10. **6.22 (solvable Frobenius kernel nilpotent)** — G. Higman 1957. 6.8 + 6.2 + Sylow.
11. **6.23 を statement のみ** (`section axiomatized` / `sorry` / `theorem ... := by ...`) — Ch.7 で証明完了.
12. **6.24 (Frobenius kernel nilpotent, Thompson)** — 6.22 + 6.23 から.

優先度 (FT クリティカル度): **6.7 (Frobenius 定義), 6.17 (Sylow cyclic/quaternion), 6.22-6.24 (kernel nilpotent)** ≫ 6.4, 6.11 (具体群構造) > 6.18, 6.19, 6.21 (Ch.7 接続) > その他.

## 進捗 (2026-05-23 開始)

ファイル: [`OddOrder/Isaacs/Ch06_FrobeniusActions/Main.lean`](../../OddOrder/Isaacs/Ch06_FrobeniusActions/Main.lean) 新規作成.

**完成済 (no preceding-chapter dep)**:
- `IsFrobeniusAction A N : Prop` — action ベース定義 (Isaacs p.177).
- 構造補題: `orbit_one`, `stabilizer_eq_bot`, `fixedBy_eq_singleton_one`.
- **Lem 6.1** `card_modEq_one`: `|N| ≡ 1 mod |A|`. Burnside 経由.
- Cor `coprime_card`: |A|, |N| coprime.
- **Thm 6.3 (commute part)** `commute_of_card_even`: 2 ∣ |A| ⇒ N abelian.
- **Thm 6.3 (uniqueness part)** `unique_involution`: + Nontrivial N ⇒ unique involution.
- Thm 6.3 用 helper: `fixedPointFree_toMulAut`, `involutive_toMulAut_of_sq_eq_one`,
  `involution_smul_eq_inv`. mathlib `MonoidHom.FixedPointFree` (Mathlib/GroupTheory/
  FixedPointFree.lean, Browning 2024) 経由で大半 reduce.
- **Lem 6.16** `pow_prime_modEq_one_cases` (§6B 数論補題, 先行章依存ゼロ):
  i^p ≡ 1 [ZMOD p^e] ⇒ 3 cases. p odd は LTE (mathlib `Int.emultiplicity_pow_sub_pow`),
  p=2 は (i-1)(i+1) 因数分解 + 奇数因子の IsCoprime で powers of 2 を相殺. ~172 LOC.
  §6B Cor 6.17 (Frobenius complement Sylow 構造) で本補題が要件.
- **Thm 6.4 部分 (cyclic equivalence)** + **`IsFrobeniusGroup G N A`** structure (~215 LOC):
  - Defn: `IsFrobeniusGroup` = `N.Normal` + `IsComplement' N A` + 両者 `≠ ⊥` + `conj_frobenius`
    (Isaacs condition (1) ベース).
  - `of_centralizer_complement_le` (Thm 6.4 (3) ⇒ IsFrobeniusGroup)
  - `of_centralizer_kernel_le` (Thm 6.4 (4) ⇒ IsFrobeniusGroup)
  - `trivialIntersection` (Thm 6.4 (1) ⇒ (2)): A ∩ A^g = ⊥ for g ∉ A, [b, n] 経由
  - `centralizer_complement_le` (Thm 6.4 (2) ⇒ (3))
  - 部分 TFAE: (1) ⇔ (2) ⇔ (3) + (4) ⇒ (1) 完成. **(1) ⇒ (4) は Cor 6.6 待ち.**
- **Lem 6.5** `card_notConjugateSet_eq_index` (~250 LOC):
  TI 条件下で X = "non-A-conjugate 元集合" は `|X| = A.index`. Isaacs p.179 直訳.
  - private `normalizer_eq_self_of_TI`: TI + A ≠ ⊥ ⇒ N_G(A) = A.
  - private `TI_conjugate`: 異なる conjugate は trivial intersection.
  - bijection `G ⧸ A ≃ conjugates A` 経由で |conjugates| = A.index.
  - `|X| = |G| - A.index × (|A| - 1) = A.index` (Lagrange + omega).
  - ConjAct typeclass 回避のため `MulAut.conj g · A` 直接パラメトライズ.
- **Cor 6.6** `IsFrobeniusGroup.kernel_eq_notConjugateSet` (~30 LOC):
  Frobenius 群で N = notConjugateSet A (set 等式). N ⊆ X は normality + Disjoint,
  逆向きは Lem 6.5 cardinality (|N| = A.index = |X|) で `Set.eq_of_subset_of_ncard_le`.
- **Thm 6.4 (1) ⇒ (4)** `IsFrobeniusGroup.centralizer_kernel_le` (~50 LOC):
  Cor 6.6 経由で `c ∉ N` ⇒ c is A-conjugate ⇒ `m := g⁻¹ n g ∈ N, m ≠ 1` で
  `a * m * a⁻¹ = m` を導出, conj_frobenius と矛盾.
- **Thm 6.4 完全 TFAE 達成**: (1) ⇔ (2) ⇔ (3) ⇔ (4) all closed.
  Constructor 形 (`of_centralizer_*_le`) + projection 形 (`trivialIntersection`,
  `centralizer_complement_le`, `centralizer_kernel_le`) 揃った.
- **action/subgroup-pair bridge**: `IsFrobeniusGroup.toFrobeniusAction`,
  `IsFrobeniusGroup.card_kernel_modEq_one`, `IsFrobeniusGroup.coprime_card_kernel_complement`.
  BG/Peterfalvi 側で subgroup-pair 形を使いつつ, Isaacs 6.1 の action 版 counting を再利用できる.
- **Cor 6.2** `IsFrobeniusAction.quotient`: A-invariant normal quotient `N/M` への誘導作用を
  `QuotientGroup.map` で構成し, `⟨a⟩` に制限して Ch.4 forward の
  `coprime_fixedPoints_quotient` を適用. sorry-free.
- **§6B infra: `OddOrder.GroupTheory.SemiDihedral` 新規** (~221 LOC):
  半二面体群 `SemiDihedralGroup n` (位数 `2^(n+1)`). mathlib `QuaternionGroup` template.
  constructors `c i` / `ca i` with twist `r := 2^(n-1) - 1` (n=0,1 override). Group + Fintype.
  Lem 6.13 / 6.14 / 6.17 の前提.
- **Lem 6.13 D/Q/SD recognition 部分**:
  `dihedralOrQuaternion_of_invertingConjugation` と
  `semiDihedral_of_twistConjugation` が sorry-free. cyclic index-2 2-group の主要 split case は
  既存 recognizer に落とせる状態.
- **Cor 6.14** `dihedralOrQuaternion_of_card_eight`: 位数 8 非可換群は
  `DihedralGroup 4` または `QuaternionGroup 2`. sorry-free.
- **Lem 6.15** center-index `p^2` characteristic elementary-abelian subgroup:
  odd `p` branch (`exists_characteristic_isElementaryAbelian_of_center_index_prime_sq_odd`) と
  `p=2` branch (`exists_characteristic_isElementaryAbelian_four_of_center_index_four`) が
  sorry-free. `T/T'` lift, order-8 noncyclic extraction, D/Q 判定まで Ch.6 本体に接続済み.
- **§6B shared helper surface** (`OddOrder.GroupTheory.ElementaryAbelian`):
  `IsElementaryAbelian.isPGroup`, subgroup restriction, order `p^2` non-cyclicity,
  order `p^2` subgroup extraction, order-`p` line 2 本の抽出, および
  「order `p` subgroup が一意なら elementary abelian `p^2` subgroup は存在しない」
  (`Subgroup.not_exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_unique`) を追加.
  6.9 → 6.10 と 6.11 abelian branch の接続で使う.
- **§6B / 6.20 abelian Z-group bridge**:
  `isCyclic_of_sylow_isCyclic` と
  `exists_prime_sylow_not_isCyclic_of_not_isCyclic` を追加. Cor 6.17 で Sylow cyclic
  が得られた後, abelian Frobenius complement を cyclic と結論するための Lean bridge.

**設計判断**:
- **action ベース** (`IsFrobeniusAction A N` on `MulDistribMulAction A N`) を採用. subgroup-pair
  版 `IsFrobeniusGroup G N A` も導入済みで, `toFrobeniusAction` で action 版に接続する.
- mathlib `FixedPointFree` モジュールが involution → invert + commute 部分の machinery を
  全部持っているため, Thm 6.3 は実質 30-40 行で完成.

**現在の残タスク候補**:
- 6.7 centralizer-kernel criterion: Schur-Zassenhaus / Ch.5 normal p-complement 周辺が main に入ったので,
  statement 形から再設計する価値あり.
- 6.8-6.10 partition counting → Frobenius complement 禁止構造.
- 6.11/6.12 p-group classification: 6.13/6.14/6.15 と elementary-abelian line helpers を
  使って大枠へ進める.
- 6.17-6.21 Frobenius complement / coprime abelian action: Ch.7 の 6.20 使用箇所に向けた中期目標.

## 開発時の注意点

### Frobenius 群の定義候補

複数の等価定義が Thm 6.4 で証明される. Lean 実装の選択肢:

1. **action による定義**: `def FrobeniusAction (A : Type) [Group A] (N : Type) [Group N] [MulAction A N] : Prop := A ↷ N ≠ trivial ∧ ∀ a ∈ A, a ≠ 1 → ∀ n ∈ N, n ≠ 1 → a • n ≠ n` (固定点無し)
2. **subgroup pair による定義**: `def IsFrobeniusGroup (G : Type) [Group G] (A N : Subgroup G) : Prop := N.Normal ∧ IsComplement N A ∧ ∀ g ∈ A, g ≠ 1 → centralizer (Set.singleton g : Set G) ⊓ N = ⊥`
3. **TI**: A ∩ A^g = 1 ∀g ∈ G − A (Thm 6.4 (2))
4. **Frobenius kernel** から定義: `C_G(n) ⊆ N ∀n` (Thm 6.7 入口)

mathlib `MulAction.IsTrivialIntersection` 周辺 (Blocks.lean) との整合性を見ると, **action ベース** (#1) で `FrobeniusAction A N` を中核に置き, subgroup 版 (#2) を `def IsFrobeniusGroup ... := FrobeniusAction A (conjugation on N)` で導出する形が自然.

将来 BG §3 / Peterfalvi §10 で "G = KR is a Frobenius group with kernel K and complement R" 形をよく使うので, **subgroup-pair 形を主, action 形を補助** にする選択もあり.

### partition 概念

`def Partition (G : Type) [Group G] (Π : Set (Subgroup G)) : Prop :=
  (∀ X ∈ Π, X ≠ ⊥ ∧ X ≠ ⊤) ∧
  (⋃ X ∈ Π, (X : Set G)) = Set.univ ∧
  (∀ X Y, X ∈ Π → Y ∈ Π → X ≠ Y → X ⊓ Y = ⊥)`

Thm 6.8 はこの上で counting. mathlib に group partition の概念 (代数的) は無さそう. **新規実装**.

注意: mathlib `MulAction.IsBlock` の partition は **集合の partition** であって本書の **subgroup の partition** とは異なる. 混同しないように.

### 一般化四元数の整合性

mathlib `QuaternionGroup n` の n の意味: `Fintype.card (QuaternionGroup n) = 4 * n` (Quaternion.lean L175). 例えば `QuaternionGroup 2` が位数 8 の Q_8. Isaacs の "generalized quaternion of order 2^{n+1}" 記法とは n がずれる. wrapper 補題で対応:

```lean
abbrev GeneralizedQuaternionGroup (n : ℕ) := QuaternionGroup (2 ^ (n - 1))
-- |GeneralizedQuaternionGroup n| = 2^{n+1}
```

または Isaacs の n に合わせて `QuaternionGroup (2^{n-1})` を `Iso.GeneralizedQuaternion n` 等で wrap. ただし [[feedback_no_mathlib_wrapper]] 政策に沿うなら, abbrev のみで thin wrapper は書かず, **section docstring で対応表だけ示す** のが推奨.

### Thm 6.23 (Thompson char-X) の扱い

Isaacs 本文 (L3682-3683) で "we present and prove in Chapter 7" と明示. ⇒ Ch.6 では:

```lean
/-- **Isaacs Thm 6.23** (Thompson). p ≠ 2, P ∈ Syl_p(G), 全 非単位 char X ⊆ P で N_G(X) が
    normal p-complement を持つ ⇒ G が normal p-complement を持つ.
    本書 Ch.7 で改良版を証明する都合で本章では statement のみ. -/
theorem thompsonNormalPComplement_charSubgroupVersion : ... := by
  -- proved in OddOrder.Isaacs.Ch07
  sorry
```

として Ch.7 完了時に置き換える. または `axiom` を一時的に置く. Phase 1 全体の完成度を保つには **後者 (axiom + Ch.7 完了で `axiom` を `theorem` に書き換え)** が clean.

### BG / Peterfalvi 橋渡し名

Phase 2a / 2b で頻繁に Frobenius を引用する:

- **BG L799 setup**: `IsFrobeniusGroup G K R` を section docstring で `OddOrder.BG.Ch1.S03` 冒頭に明記
- **BG Lemma 3.2 (quotient Frobenius)**: Isaacs 6.2 を直接利用
- **BG Lemma 3.3 (Frobenius act on V)**: Isaacs 範疇外, 表現論を別途追加
- **Peterfalvi (10.7) [S,S] Frobenius**: Isaacs 6.4 / 6.7 を直接利用
- **Peterfalvi [BG] Proposition 3.9 ≡ Isaacs 6.17**: BG が自前で再述する Isaacs 6.17. BG 形式化時に対応関係を明記

## 未解決の疑問

- ~~**Frobenius 群定義の最適な Lean 形**~~ → 解決:
  action 版 `IsFrobeniusAction` と subgroup-pair 版 `IsFrobeniusGroup` を併用し,
  `IsFrobeniusGroup.toFrobeniusAction` で接続する.
- **6.11, 6.12 の証明スキーマ** — Isaacs の証明 (induction + 中心化群分析) を Lean で写す難度. mathlib `Quaternion.lean` の lemma 群との接続でどこまで短く書けるか実装時調査.
- ~~**`SemiDihedral` 新規定義**~~ → 解決:
  `OddOrder.GroupTheory.SemiDihedral` に `SemiDihedralGroup n` を追加済み.
- ~~**6.16 (i^p ≡ 1 mod p^e) の存在感**~~ → 解決:
  `pow_prime_modEq_one_cases` として Ch.6 file 内に sorry-free 実装済み.
- ~~**6.21 (⟨C_N(a)⟩ = N) は Ch.7 で何回使われるか**~~ → **解決 (2026-05-22 audit)**: Ch.7 で **6.20 のみ使用** (Thm 7.6 Step 5). 6.21 は Ch.7 内で proof body 引用無し. (元 mmd grep ヒットは 6.20 の prose mention 内で 6.21 を comparison 引用していたためのノイズ.)
- **Thm 6.23 の Ch.6 内での扱い** — `axiom` か `sorry` 経由のステートメントか, あるいは Ch.6 では skip して 6.24 だけ Ch.7 で 6.23 と一緒に証明する形にするか. 章間の依存最小化を考えると Ch.6 全部一度書いて 6.23 を Ch.7 完了時に書き換える運用が clean.

## 第 5 波 (Ch.7, Ch.10) との接続

ROADMAP は Ch.6 完了後の第 5 波として Ch.7 (Thompson, ZJ) と Ch.10 (More Transfer) を並列可と注記. Ch.6 から両者への流れ:

- **Ch.7 (Thompson J(P), ZJ)**: 6.20, 6.21 (abelian coprime action 補題), 6.23 (改良版を証明), 6.24 (kernel nilpotent) を継承. **クリティカルパス**.
- **Ch.10 (More Transfer)**: Ch.5 (Transfer) + Ch.6 (Frobenius) の融合. BG App.A 周辺で使う Hall-Higman 1.2.3 強化版 (Isaacs 10.X) が中心. 直接被引用は Ch.7 経由が多い.

⇒ Phase 1 完成への道筋: **Ch.5 → Ch.6 → Ch.7 → Ch.10** がクリティカルパス. Ch.6 は前 2 章のラッパー仕事と後 2 章の重い新規実装を結ぶ要.
