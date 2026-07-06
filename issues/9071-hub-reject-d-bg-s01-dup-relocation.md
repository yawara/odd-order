---
id: 9071
slug: hub-reject-d-bg-s01-dup-relocation
title: "HUB REJECT: d の 9068-9070 = BG S01 既存補題 5 件の重複 relocation (full-build break)"
created: 2026-07-07
---

# HUB REJECT: d の 9068-9070 = BG S01 既存補題の重複 relocation

## 裁定 (hub autonomous, 2026-07-07 tick)

lane d の 3 commits (`d386f142` 9068 / `995e1134` 9069 / `7ded7966` 9070) は
`OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean` に 5 theorem を追加するが、
**5 件すべてが既存の `BG/Ch1_Preliminary/S01_Solvable.lean` の逐語コピー**:

| d の新 decl (ForwardFromCh03) | 既存 (BG S01) |
|---|---|
| `coprime_actsTrivially_of_normal_and_quotient` | S01:1771 |
| `coprime_stabilizes_chain_trivial` | S01:1803 |
| `coprime_nilpotent_acts_trivially_of_centralizer_self` | S01:1895 |
| `burnside_operator` | S01:1720 |
| `mulAut_eq_one_of_coprime_orderOf_of_frattini` | S01:1735 |

statement・証明とも S01 版と同一 (namespace 修飾のみ差)。d の意図は claim issue の
"**Move** ... to Isaacs Ch04" どおり **relocation** だが、**追加のみで S01 原本を削除せず・
caller を rewire せず** → `S04e_GorThm37.lean:183` で名前衝突 (`open ...Isaacs.Ch04`
=53 と `open ...S01 (coprime_actsTrivially_of_normal_and_quotient)`=58 の二重可視化) →
**full build FAIL** (`Ambiguous term`)。

## REJECT 理由

1. **churn であって progress でない** (CLAUDE.md「進捗の測り方」): 既存の proven 補題を
   ファイル間で移すだけで新しい数学はゼロ・sorry も減らない。lane d が明示的に警告されている
   "make-work / chore-churn busywork" に該当。
2. **claim-before-build 違反** (「既存を再構築しない」): d の 9068-9070「重複確認」は
   "allowed area scan: 未存在" と記すが、**scan が frozen BG を除外**していたため S01 の
   既存 5 件を見落とした。
3. **build-breaking incomplete refactor**: relocation を追加半分だけ実施 + **leaf build のみ**
   (`lake build ...ForwardFromCh03`) で検証 → 下流 (S04e_GorThm37) の衝突を full build しないと
   検出できず素通り。

## d への必要アクション

- branch `d` から 3 commits (`d386f142` / `995e1134` / `7ded7966`) を **drop** する
  (`git rebase` で除去 or `git reset --hard 949d5e27` で 9067 直後まで戻す — 949d5e27 は
  前 tick で main へ合流済みの最後の commit)。5 補題は BG S01 に既存ゆえ、消費側は S01 版を
  そのまま cite すればよい (何も失われない)。
- 起票済み closed issue 9068/9069/9070 は本 REJECT を追記して無効化 (d 側で annotate)。

## d の process 修正 (再発防止)

- **重複 scan は repo 全体で decl 名を grep** する (`grep -rn '^theorem <name>' OddOrder/`)。
  "allowed area" (Isaacs/GroupTheory/Mathlib/Algebra) に限定すると frozen BG の既存を見落とす。
- **shared-infra 追加は commit 前に full build** (`lake build OddOrder`)。leaf build は
  下流の名前衝突・ambiguity を検出できない。

## 補足 — relocation 自体の是非

BG S01 の coprime-action ブロックを Isaacs Ch04 へ移す layering 改善には一定の理があるが
(S01 版 docstring も "no-wrapper policy 例外" と注記)、それは **hub 承認付きの正式 refactor**
(S01 原本削除 + 全 caller 移行 + `open` 更新、frozen BG 編集) であって、silent な additive dup
ではない。かつ **FT-math payoff ゼロの churn** ゆえ優先度は最低。当面は S01 現状維持。

## 参照

- build error: `OddOrder/BG/Ch1_Preliminary/S04e_GorThm37.lean:183` Ambiguous term
- d claim issues: `issues/closed/9068-*`, `9069-*`, `9070-*` (d branch)
- [[verify-port-state-by-number-not-coq-name]] [[hub-arbitrates-cross-lane-autonomously]]
