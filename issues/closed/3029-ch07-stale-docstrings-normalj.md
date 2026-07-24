---
id: 3029
slug: ch07-stale-docstrings-normalj
title: "Isaacs Ch07 stale docstrings 3 件 (normal_J 周り) — lane a 申し送り"
created: 2026-07-21
---

# Isaacs Ch07 stale docstrings 3 件 (normal_J 周り) — lane a 申し送り

## 背景

issue 3024 (Gorenstein Ch.8 §2 / Glauberman ZJ) の調査中 (2026-07-21, lane c) に
Isaacs/Ch07 で stale docstring 3 件を検出した。Ch07 は lane a territory ゆえ
lane c では直さず申し送り (3024 close に伴い独立 issue 化)。
stale 前提記述は frontier 誤診の元 ([[feedback-fix-stale-docstrings-on-sight]])。

## やること

- [ ] `S7B2_NormalJ_PComplement.lean:1421-1424` (`normal_J`) — 「Remaining local
      axioms: `step4_5_normal_J_hypotheses` … `step8_normal_J_closure`」は**すべて
      誤り**。前者は `private theorem` (:864)、`step8_normal_J_closure` は
      **存在しない**。`normal_J` は AxiomsCheck:1548 で axiom-clean 宣言済、
      Ch07 は sorry-free。記述を現状に合わせて修正。
- [ ] `S7B2_NormalJ_PComplement.lean:1300-1307` — 同じ「Step 4-5 axiom」
      「Step 8 axiom」表現の修正。
- [ ] `S7B1_NormalJ.lean:1616-1621` + header :22-37 — 「Step 7 の結論を
      axiomatize する」は stale (`omega1ZCenterOpCore_relIndex_inter_A_le` として
      landed、tracking issue 0036 も closed)。修正。

## 完了条件

上記 3 箇所の docstring が実装の現状 (sorry-free / axiom-clean) を正しく記述する。

## 参照

- issue 3024 (検出元、closed) / issue 0036 (closed; S7B1 Step 7 の landed 記録)。
- 行番号は 2026-07-21 時点 (lint wave コミットでずれている可能性 — 記述内容で grep
  し直すこと)。

---

## ✅ 2026-07-24 close (hub、issue 監査 tick で on-sight 修正)

3 サイトとも実状態 (全 8 step 実証明済・`normal_J` axiom-clean・0036 closed) に合わせて修正:
- `S7B2_NormalJ_PComplement.lean` `thompsonJ_le_opCore_of_normal_J_hypotheses` docstring —
  「Step 4-5 axiom / Step 8 axiom (`step8_normal_J_closure`)」→ 実際の proved theorem 名
  (`step8a_PBar_normal_GBar` / `step8b_pullback_normal_P`) に置換、存在しない名前への参照 0 化。
- 同 `normal_J` docstring — 「Remaining local axioms」段落を「全 step proved・axiom-clean」に。
- `S7B1_NormalJ.lean` 末尾コメント + header — 「axiomatize the Step 7 conclusion」
  「conditional version / still pending」→ landed 済の記述へ。
longLine 非導入を codepoint で確認。close。
