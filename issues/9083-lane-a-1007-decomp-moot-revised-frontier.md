---
id: 9083
slug: lane-a-1007-decomp-moot-revised-frontier
title: "HUB: (10.7) 3 分解は pair で完了済と判明 (9082 承認 plan の moot 化) — 改訂 frontier 提案"
created: 2026-07-11
---

# HUB: (10.7) 3 分解は pair で完了済と判明 (9082 承認 plan の moot 化) — 改訂 frontier 提案

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 経緯

9082 の hub 承認 (③→①→②) の**直後の precision survey で前提が覆った**:
`exists_typeIICrossIsometryData_at_pair` (S12_TypeIICrossIsometryPair:1345) が
③①② を**全て sorry-free で実装済み**。critical path
(S_not_coherent_unconditional → typeII_HU_frobenius_of_coherent' → at_pair) は
これを消費 (S_not_coherent_unconditional の axiom-clean assert 通過と整合)。
base 非交差は (8.13.c4) not-Frobenius でなく **σ-route**
(typeP_pair_core_order_coprime → sigma_disjoint_of_nonconjugate)。

⟹ **9082 承認 plan は対象消滅 (moot)**。S10 additive 条件・9079/② 注意は
該当作業ごと不要に。

## hub への cleanup 裁定依頼 (急がない)

superseded sorry 3 兄弟の keep/delete/退役方式:
- S12_TypeIIFrobenius:1221 `exists_typeIICrossIsometryData` (dead consumer:
  typeII_derived_frobenius 経由 docstring 参照のみ)。退役案 =
  TypeIICrossIsometryData の MulAut.conj 移送 lemma (near-definitional) で
  pair 版から導出、or 宣言ごと削除。
- S12_MaximalBasic:1257 (「DO NOT fill」注記済) / S12_MaximalIII_IV_V:1659
  (typeV 原本、superseded 注記済)。

## 改訂 frontier (lane a、着手宣言)

**`coherent_Sset_diff_SHCSet`** (S12_MaximalIII_IV_V:1548-1559) の honest 化:
(9.11) の SOf-difference 形再 port + (11.7) collapse。文書順で現 open 作業の
最上流 ((9.11) < (10.x) < (11.x))。docstring の「§14/lane-b 協調」注記は
S11/SOf 世界橋の設計点を指す — lane b の 2022 (S07/S08 coherence infra) とも
c の S16 とも対象非重複の見込み。**本 issue をもって claim** (重複あれば hub 指示を)。
次 iteration: 対象の依存 survey (mkSection11CharacterData の ∅-support 問題 /
SOf-difference の正しい statement / (11.7) collapse の所在) から。
