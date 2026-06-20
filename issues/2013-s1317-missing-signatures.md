---
id: 2013
slug: s1317-missing-signatures
title: "(13.17) gate3/4 未記載 signature 特定 + lane 分担 + stale 文書訂正"
created: 2026-06-20
---

# (13.17) gate3/4 未記載 signature 特定 + lane 分担 + stale 文書訂正

## 背景

POLE-2 の (13.17) `exists_typeI_maximal_overNormalizer_U`（`Peterfalvi/S15_SAndT.lean`、Pf 13.17.a/b）は
4 gate を持つ。gate 2 (L~S) の**構造論コアは sorry-free 化済**（commit `4357cc7d`、`normalizer_le_of_isHall_subgroupOf_of_conj`）。

その過程で、notes/issue 2009/LAUNCH が gate 3/4 を一括で「**cite待ち / sorried cite**」と書いていたのは
**不正確**と判明した。「cite待ち」には 2 種あり、混同していた:

- **(A) signature 存在・producer が sorried** → 今すぐ cite 可（gated-endpoint skeleton、stable signature）。
- **(B) signature 自体が未記載** → cite 不可。**まず statement を書く形式化労力**が要り、その先で (A) や proof に bottom-out。

gate 3/4 は (A) と (B) の**混合**で、純粋な skeleton ではない。本 issue は (B)（未記載 signature）を特定し、
追加すべき lane を提案し、stale 文書の訂正案を出す。

## 現状の正確な仕分け（gate ごと）

`exists_typeI_maximal_overNormalizer_U` の 4 gate（[S15_SAndT.lean](OddOrder/Peterfalvi/S15_SAndT.lean) 内）:

| gate | 必要な事実 | signature 状態 | 種別 |
|---|---|---|---|
| 1 hdisj | `P ⊓ U = ⊥` | carrier に無い | **F-ask**（issue 2009、carrier enrich） |
| 2 L~S | `Coprime |U| [S:U]` ← `[S:M']=|W₁|`（W₁=κ 同定） | carrier に無い | **F-ask**（issue 2009）。構造論コアは ✅ DONE |
| 3 L~T | (13.2.a) `basic_structure.UW1_frobenius` | ✅ **存在**（S15_SAndT、sorried producer） | (A) cite 可 |
| 3 L~T | **`|L_F|=q^p`**（T-side Fitting 位数 / 「L_F は q-群 ⊇ W₁」） | ❌ **未記載** | **(B) 要 statement** |
| 4 U⊆L_F | (9.1) Wielandt FPF `wielandt_fixedPoint_frobenius` | ✅ **存在**（[CoprimeAction.lean:156](OddOrder/GroupTheory/CoprimeAction.lean:156)、sorried） | (A) cite 可 |
| 4 U⊆L_F | **(8.17.a) `|L_F| coprime to pq`** | ⚠ **直接 lemma 無し**（構造体 + producer は存在） | **(B) 要 derivation lemma** |

### (B) 未記載 signature の詳細

**(B1) gate 3 — T-side Fitting 位数 `|hyp.Q| = q^p`（= `|T_F|=q^p`、転送で `|L_F|=q^p`）**
- なぜ無い: `basic_structure`（[S15_SAndT:236](OddOrder/Peterfalvi/S15_SAndT.lean:236)、`BasicStructureData`）は **`hyp.S` 専用**で
  `|P|=|S_F|=p^q` のみ供給。S↔T 対称版（`|Q|=|T_F|=q^p`）は無い。Hypothesis は S,T 非対称（`one_typeII` 等）ゆえ
  単純な swap で出ない。
- gate 3 が実際に要するのは「`L_F` は q-群で `W₁ ⊆ L_F`」（→ `U` が `L_F` 正規化 + `Coprime |U| q`[既存 Frobenius] で
  `[U,W₁]⊆L_F∩U=1` → (13.2.a) 矛盾）。最小形は `T_F` が q-群（位数 q^p）であること。

**(B2) gate 4 — (8.17.a) `|L_F| coprime to pq`（type-I L、S/T 非共役）**
- 構造体 `BGTheoremECoverData`（[S10_MinimalSimpleStructure:287](OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean:287)）
  + producer `bgTheoremE_cover_data`（[S10:365](OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean:365)、**sorried**、
  「deliberately does not prove BG Theorem E」）は**存在**。
- だが **「`|L_F| coprime to pq`」の専用 lemma は未記載**。`primeFactors_disjoint`（π((M_i)_s) 互いに素）から
  **derive 可能**だが、(a) derivation lemma を書く + (b) `bgTheoremE_cover_data`（sorried）を cite、の 2 段が要る。
  ＝ 純 cite ではない。

## やること（提案 — lane 分担）

- [ ] **(B1) gate 3 T-side 位数を H が statement 化**: `card_Q_eq` 相当（`Nat.card ↥hyp.Q = hyp.q ^ hyp.p` または
  「`hyp.Q` は q-群」）を S15_SAndT に新規宣言。**owner = H**（§13 構造 producer の領域、basic_structure の対称版）。
  proof は basic_structure と同じ §13 機構に gate（当面 sorried producer でよい）。これで gate 3 の構造論コアを
  gate 2 と同パターンで sorry-free 化でき、残差を `|T_F|=q^p` 1 本に隔離できる。
- [ ] **(B2) gate 4 (8.17.a) derivation lemma を H が statement 化**: `card_LF_coprime_pq`（type-I L 非共役 ⟹
  `Coprime |L_F| (p*q)`）を、既存 `bgTheoremE_cover_data` producer（**owner = F**、BG Theorem E = BG §14-16 依存）を
  cite して derive。**derivation = H、deep producer = F**。これで gate 4 の構造論（FPF→L_F=1 矛盾）を
  `wielandt_fixedPoint_*`（既存）と組んで sorry-free 化でき、残差を (8.17.a)+producer に隔離。
- [ ] **(stale 文書訂正)** 下記 3 文書の「cite待ち / sorried cite」表現を (A)/(B) で分けて訂正:
  - `notes/peterfalvi/s13_17_structural_program.md`「leaf 分類」table + 「Phase 2 cont.」: gate 3/4 行を
    「(A) cite 可（13.2.a/9.1）」と「(B) 未記載（|T_F|=q^p / 8.17.a）」に分割。
  - `issues/pending/2009-s16-field-normalizer-pole2.md`: 「残り obligation の状態」の gate 3/4 を同様訂正。
  - `LAUNCH.md`（git-excluded）: gate 3/4 行を訂正（H が statement 化すべき (B) を明示）。

## 完了条件

- (B1)(B2) の未記載 signature が S15_SAndT（および必要なら S10）に宣言され、gate 3/4 の**構造論コアが
  それらを仮説/cite として sorry-free 化**できる状態（gate 2 と同じ「構造論コア + 隔離された (B) 残差」形）。
- 3 文書の stale 表現が訂正される。
- 注: (B1)(B2) の signature の **proof** 完成は本 issue のスコープ外（gate 3 は §13 機構、gate 4 は BG Theorem E に gate）。
  本 issue は「未記載 signature の特定 + statement 追加 + 文書訂正」まで。

## 参照

- issue 2009（POLE-2、gate 1/2 の F-ask）
- commit `4357cc7d`（gate 2 構造論コア sorry-free）、`b845e439`（notes/issue 更新）
- `notes/peterfalvi/s13_17_structural_program.md`「Phase 2 cont. (2026-06-20²)」
- memory `typep-w1-kappa-carrier-not-derivable`（W₁=κ は carrier-level の関連事実）
- 原文 Pf (13.17) = `references/peterfalvi/04.15_..._S_and_T.mmd` L286-290
