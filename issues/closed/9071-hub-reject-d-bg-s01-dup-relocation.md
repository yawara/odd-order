---
id: 9071
slug: hub-reject-d-bg-s01-dup-relocation
title: "HUB REJECT: d の 9068-9070 = BG S01 既存補題 5 件の重複 relocation (full-build break)"
created: 2026-07-07
---

# HUB REJECT: d の 9068-9070 = BG S01 既存補題の重複 relocation

## 裁定 (hub autonomous, 2026-07-07 tick)

lane d の unmerged commits (tick 中に `d386f142`/`995e1134`/`7ded7966` の 3 →
main-merge `b8931593` + `6e5a7ca3`/`86e4684b` を加え **6 commit** に進行) は
`OddOrder/Isaacs/Ch04_Commutators/{ForwardFromCh03,Main}.lean` に 6 theorem を追加するが、
**うち 5 件が既存の `BG/Ch1_Preliminary/S01_Solvable.lean` の逐語コピー**:

| d の新 decl | 既存 (BG S01) | 判定 |
|---|---|---|
| `coprime_actsTrivially_of_normal_and_quotient` | S01:1771 | ❌ dup |
| `coprime_stabilizes_chain_trivial` | S01:1803 | ❌ dup |
| `coprime_nilpotent_acts_trivially_of_centralizer_self` | S01:1895 | ❌ dup |
| `burnside_operator` | S01:1720 | ❌ dup |
| `mulAut_eq_one_of_coprime_orderOf_of_frattini` | S01:1735 | ❌ dup |
| `coprime_pgroup_acts_trivially_of_order_p_fixed_centralizer` | (同名は repo に無し) | ⚠ 要検証 (genuine の可能性) |

dup 5 件は statement・証明とも S01 版と同一 (namespace 修飾のみ差)。d の意図は claim issue の
"**Move** ... to Isaacs Ch04" どおり **relocation** だが、**追加のみで S01 原本を削除せず・
caller を rewire せず** → `S04e_GorThm37.lean:183` で名前衝突 (`open ...Isaacs.Ch04`
=53 と `open ...S01 (coprime_actsTrivially_of_normal_and_quotient)`=58 の二重可視化) →
**full build FAIL** (`Ambiguous term`)。**⚠ d は本 REJECT (main commit 15b12f57) を pull する前に
`b8931593` で main を merge 済 → 現 d branch は S01 原本と dup が共存 (full build すれば FAIL)。**

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

## d への必要アクション (dup と genuine の混在ゆえ blanket-drop でなく選別)

- **確定 dup 5 件を除去** (`ForwardFromCh03.lean`/`Main.lean` から削除)。BG S01 に既存ゆえ
  消費側は S01 版をそのまま cite すればよい (何も失われない)。dup を drop すれば
  `S04e_GorThm37:183` の ambiguity も解消。
- **`coprime_pgroup_acts_trivially_of_order_p_fixed_centralizer` (86e4684b) は genuine 可能性**
  ゆえ **軌道修正で保全**: (i) S01 に**別名で同内容が無いか**を content で確認 (名前だけでなく
  statement/証明で grep)。真に新規なら **keep**、ただし依存する coprime-action 補題は
  d の local dup でなく **BG S01 版を cite** するよう rewire。(ii) S01 に同内容があれば drop。
- **技術的な戻し方の目安**: unmerged 群の base は `e21db660` (= 前 tick で main 合流済みの
  d tip、`d386f142^`)。全 dup を捨てて genuine 1 件だけ残すなら、`e21db660` から
  `git merge main` (本 9071 込み) → S01 を cite する p-group 補題のみ 1 commit で再作成、が最短。
  (⚠ base は `949d5e27` ではない — あれは前 tick 7-commit batch の中間 commit。)
- 起票済み closed issue 9068/9069/9070 (+ nilpotent/p-group 分) は本 REJECT を追記して無効化。
- **⚠ d は live で churn 継続中** (本 tick 中に 3→6 commit)。次の shared-infra 追加の前に
  必ず本 9071 を読み、下記 process 修正を適用すること。

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


## ✅ HUB CLOSE (2026-07-08 監視 tick): lane d 退役で moot

9071 は lane d の 9068-9070 (BG S01 既存補題 5 件の verbatim 重複 relocation、net Lean diff = 0) を REJECT した pure coordination record。genuine FT math は含まない (重複ゆえ)。rejected work は main に未マージ、lane d は 2026-07-07 退役 (branch/worktree 削除済) ゆえ本 issue は moot (merge_monitor.md 記録)。process guardrail は merge_monitor.md に保全済。pending action 0。close。
