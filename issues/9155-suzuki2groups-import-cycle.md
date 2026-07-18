---
id: 9155
slug: suzuki2groups-import-cycle
title: "STOP: b の import cycle で main build が落ちた — Suzuki ⇄ Suzuki2Groups"
created: 2026-07-19
owner: lane b
---

# STOP: b の import cycle で main build が落ちた — Suzuki ⇄ Suzuki2Groups

2026-07-19 の合流 tick で **b を合流した main のフルビルドが `build cycle detected` で失敗**した。
hub は プロトコルどおり **b の合流を差し戻し** (c と hub の分割作業は保持)、本 issue で b に戻す。
**b のブランチ上の成果は一切失っていない** — 差し戻したのは main への合流のみ。

## 循環の実体

```
OddOrder/Peterfalvi/Appendices/Suzuki/SylowTwo.lean:7
    import OddOrder.Peterfalvi.Appendices.Suzuki2Groups          ← hub を import
  → OddOrder/Peterfalvi/Appendices/Suzuki2Groups.lean:9
        import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.ActualQuotientAction
  → OddOrder/Peterfalvi/Appendices/Suzuki2Groups/ActualQuotientAction.lean:6
        import OddOrder.Peterfalvi.Appendices.Suzuki.ActualKActor
  → OddOrder/Peterfalvi/Appendices/Suzuki/ActualKActor.lean:6
        import OddOrder.Peterfalvi.Appendices.Suzuki.SylowTwo     ← 一周
```

lake の出力: `error: build cycle detected:` (`Suzuki.SylowTwo:leanArts` → … → 同左)。
これに引きずられて `OddOrder.lean` / `AxiomsCheck.lean` が `bad import` を大量に出し、
Suzuki 系 10 module 前後が芋づるで失敗した (根本原因はこの 1 循環のみ)。

## なぜ起きたか — 「実体入り hub」の罠

`Suzuki2Groups.lean` は **pure re-export hub ではない**。102 行のうち 10 宣言を持ち、
**`IsSuzuki2Group` の定義そのものが :72 に置かれている**。そのため
`SylowTwo` が `IsSuzuki2Group` を使うだけで **hub 全体 (= 5 leaf 全部) を import せざるを得ず**、
新しく hub に加わった `ActualQuotientAction` の依存が逆流して循環した。

CLAUDE.md「ファイル粒度」が pure re-export hub を*意図的な逸脱*として許容しているのは
「hub が import 行だけを持つ」場合であって、**基底定義を抱えた hub は今回の形で破綻する**。

## 修正案 (b が判断すること。hub は実装しない)

**A. 基底定義を leaf へ切り出す (推奨)**
`IsSuzuki2Group` と同 file の基底宣言群を `Suzuki2Groups/Defs.lean` (新規) へ移し、
`Suzuki2Groups.lean` は pure re-export hub にする。`SylowTwo.lean` は
`import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Defs` に差し替える。
module 名は不変ゆえ他の下流は無変更。

**B. `ActualQuotientAction` を hub から外す**
`Suzuki2Groups.lean` の :9 を落とし、必要な consumer が leaf を直接 import する。
ただし hub の re-export 性が崩れるので A の方が筋が良い。

⚠ **どちらを採るにせよ、`lake build OddOrder`(フル) ではなく
`lake build OddOrder.Peterfalvi.Appendices.Suzuki2Groups OddOrder.Peterfalvi.Appendices.Suzuki`
の leaf build で循環解消を確認すること**。import cycle は leaf build でも即座に出る
(BFS で「循環が消えた」と目視確認するのは不十分 — [[relayer-verify-with-build-not-bfs]])。

## やること

- [ ] b が上記 A (または B) で循環を解消する
- [ ] leaf build で `build cycle detected` が消えることを確認
- [ ] hub が次の tick で b を再合流し、フルビルドで green を確認 → 本 issue を close

## 完了条件

b を合流した main のフルビルドが green。

## 参照

- 差し戻した合流: `3473eb15a Merge 'b'` (reset 済、b のブランチは無傷)
- b の該当 commit: `5caac5480` (transitive invariant leaf) / `b270220ba` (K action 降下)
- CLAUDE.md「ファイル粒度」pure re-export hub の項
