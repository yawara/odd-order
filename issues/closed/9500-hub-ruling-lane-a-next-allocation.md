---
id: 9500
slug: hub-ruling-lane-a-next-allocation
title: "HUB 裁定: レーン a の次の割当 (9163 Option B′ 確定 → Pf type-II 拡張)"
created: 2026-07-19
---

# HUB 裁定: レーン a の次の割当 (9163 Option B′ 確定 → Pf type-II 拡張)

lane a の照会 (9303 → **9203 へ改番**、「担当 2 領域が完済、次の割当を求む」) への hub 回答。

## 結論 — **reallocation は不要。9163 を裁定したので同じ territory で即座に再開できる**

lane a の担当 (Isaacs 全域 + Peterfalvi 本文) は変更しない。**枯渇ではなく gate だった**ので、
gate を外すのが正しい対処:

### ① 最優先: issue 9163 を **Option B′ で裁定済** (同 issue に全文)

`typePA` の 346 hit / 38 rw 箇所 / BG Ch4 の他レーン consumer への波及を実測した結果、
Option A (typePA 自体の訂正) は却下。書籍忠実な `A(M)` は **既に稼働中の
`honestTypeP2ASet`** を `typePACore` へ改名・`S10_StructureSetup` へ昇格して正本にする
(新 def は作らない)。橋渡し `IsTypeP1 → typePACore = typePA` で既存 P₁ consumer は無変更。

⟹ **lane a の次の着手先 = 9163 §3 の 4 項目**を上流優先 + 文書順で:

1. (8.15) type-II instance (issue 1042 着手順 3)
2. (8.18) の一般化 + `cross_zero` の導出化
3. (9.11) M 側 type-II 拡張 (§12 `type_alt` の作り直し)
4. packaging 層の辞書同一視 (`htype`/`hncH0C`) の整理

### ② 演習問題 (Isaacs Problems) は **スコープ外のまま**

CLAUDE.md のスコープは 3 冊の「**全番号付き結果**」。演習は番号付き結果でないので、
被覆測定に含めない現行の運用が正しい。**方針変更が要るならユーザー判断**であって、
lane が空いたから埋める対象ではない。

### ③ 他レーン territory への越境割当は行わない

a の候補案にあった「Pf Appendices 非 Suzuki 系 (c 所管)」「Suzuki チェーン (b 所管)」
「BG 残 (c 所管)」は、**b/c とも稼働中で実 sorry を現に削っている** (本日: c が BG App.D
D.1/D.2 完全証明で sorry 22→20、b が Higman Lemma 5/6 + Neumann 位数 3 定理)。
territory 分割は coordination のためにあるので、a の gate が外れた今わざわざ割る理由がない。

⚠ ただし **shared infra の新設は従来どおり in-scope** (CLAUDE.md (B)(C))。a が type-II 拡張の
途上で未所有 leaf を要したら、**自バンド `--base 9200`** で claim-before-build すること。

## 付随: 採番の是正

- a が起票した `9303-lane-a-scope-complete-reallocation.md` は **b のバンド (9300-9399) を侵している**。
  a のバンドは **9200-9299** なので **9203 へ改番**すること (main 側で hub が実施済なら追随不要)。
- `--base 9000` は 2026-07-19 に**凍結** (`bin/new-issue` がエラーで拒否)。理由 = 幅 1000 ゆえ
  レンジ [9000,10000) がサブバンドを飲み込むため。詳細は issues/closed/0130。

## ⚠ 状態: lane a は 22:46 に**自分で loop を停止**している (再開はユーザー操作)

a は 9303 を起票した直後、`ScheduleWakeup({stop: true})` で loop を明示停止し
PushNotification でユーザーに通知した。理由 (transcript): 「territory 内で取れる行動は
hub issue の起票が最後。hub 裁定を待って空転するか、他レーンの仕事を一方的に取るかに
なるので止める」。**issue 0131 の「黙って止まる」障害とは別物** (これは理由つきの意図的停止で、
通知も出している)。

⟹ 本裁定 (9163 + 本 issue) が main に landing した今、**a を再開すれば即座に着手できる**。
再開時の指示は「main を同期して issue 9163 の hub 裁定節と issue 9500 を読み、
9163 §3 の項目 1 から始める」で足りる。

## 完了条件

- lane a が 9163 §3 の項目 1 に着手し、`typePACore` の昇格が main に landing すること。
- 本 issue は a が着手を開始した時点で close (割当の記録が目的)。

## 参照

- `issues/9163-typepa-mssharp-rescope-for-815-typeii.md` (裁定本体、hub 裁定節)
- `issues/9203-lane-a-scope-complete-reallocation.md` (a の照会、改番後)
- `issues/1042-pf-8-15-dade-hypothesis-instances.md` (着手順 3)
- `notes/isaacs/frontier_measured_2026_07_19.md` / `notes/peterfalvi/frontier_measured_2026_07_19.md`
- `issues/closed/0130-*` (採番サブバンド化)
