---
id: 9158
slug: interim-realloc-a-down
title: "暫定: lane a 停止中の Pf 本文の扱い — c へ暫定移管 (a 復帰で自動失効)"
created: 2026-07-19
owner: hub
status: CLOSED (a 復帰により失効, 2026-07-19)
---

# 暫定: lane a 停止中の Pf 本文の扱い — c へ暫定移管

## 事実

**lane a は 2026-07-19 05:36 を最後に停止**している (本 issue 起票時点で 2 時間 20 分)。
セッションログの末尾は

> 「このイテレーションを終える。次は Thm 6.22 の書籍形との差を確認するところから (60 秒後に再開)」

で、**予約した 60 秒後の wakeup が発火しないままセッションが終了**した。codex 側にも
a の worktree (`/home/ywr/odd-order-a`) を見ているセッションは無い。

- a は `ahead 0 / dirty 0` で **成果の損失はゼロ**。main から 62 commit 遅れ。
- レーンのセッション起動は hub からは行えない (ユーザー操作が要る)。

## 問題

裁定 9154 で **Peterfalvi 本文 `OddOrder/Peterfalvi/S*` を a に移管**したが、a が停止したため
**3 冊で残量最大の Pf 本文 (63〜65 件、L:10 XL:6) が誰の担当でもない状態**になった。
territorial ルールにより c は触らない。b は Suzuki 系で手一杯。⟹ 実質的に凍結。

## 暫定裁定 (hub)

**Pf 本文 `OddOrder/Peterfalvi/S*` を暫定的に c 所有へ戻す。**

- これは 9154 の恒久的な取り消しではない。**a が復帰した時点で自動的に 9154 の配分へ戻す**
  (= Pf 本文は a、c は BG 残 + Pf Appendices)。a の worktree / branch は削除しない。
- 根拠: 「担当が空いたまま最大クラスタが凍結する」損失 > 「配分が一時的に偏る」損失。
  c は BG §6 が Thm 6.4 のみになり、直近も Pf に隣接する shared infra
  (`FittingHeredity` / `SolvablePrimeIndex` 周辺) を扱っているため接続コストが低い。
- c は**自分の frontier 判断で**着手可否を決めてよい (BG を優先しても差し支えない)。
  本裁定は「c が Pf 本文に着手しても範囲逸脱でない」ことを保証するもので、着手義務ではない。

### 暫定の所有 regex (step 1.5)

```
a_re='^OddOrder/Isaacs/'                       # a 復帰までは Isaacs のみ (完了済ゆえ実質 dormant)
b_re='^OddOrder/Peterfalvi/Appendices/(Suzuki|Suzuki2Groups)'
c_re='^OddOrder/BG/|^OddOrder/Peterfalvi/S|^OddOrder/Peterfalvi/Appendices/(NearFields|Huppert|SemilinearField|FeitSibley)'
```

## やること

- [x] hub: 監視 cron のプロンプトを暫定 regex に更新
- [x] **a が復帰したら本 issue を close し、9154 の配分 (Pf 本文 = a) へ戻す**
      — a は起動時の `git merge main` で本 issue を読むこと

## 完了条件

lane a が復帰し、9154 の配分に戻ったとき。

## 参照

- issue 9154 (恒久裁定。本 issue はその暫定的な上書き)
- a の最終 commit: `6275a76fd docs(survey): Isaacs 特殊化債務 4.6 / 4.16 / 9.8 も stale だった`

## 失効 (2026-07-19, lane a 復帰)

lane a が復帰し `git merge main` で本 issue を読んだ。**9154 の恒久配分へ戻す**:

```
a_re='^OddOrder/Isaacs/|^OddOrder/Peterfalvi/S'
b_re='^OddOrder/Peterfalvi/Appendices/(Suzuki|Suzuki2Groups)'
c_re='^OddOrder/BG/|^OddOrder/Peterfalvi/Appendices/(NearFields|Huppert|SemilinearField|FeitSibley)'
```

### 暫定期間中の c の Pf 本文作業 — 境界は clean

c は暫定裁定下で Pf §3 に着手し、`e5a223ce7 feat(pf §3): Clifford 対応 (1.7)(a) の
distinctness を形式化 — Pf §3 完了 (10/10)` で**節を完了させて commit 済**。
未コミットの引き継ぎ対象は無く、a は §3 を避けた最上流から入ればよい
(9154 の「c が着手済みの未コミット作業は破棄せず a へ引き継ぐ」条項は発動不要)。

⚠ c がこの後さらに Pf 本文へ commit していた場合は、本 issue でなく通常の
territory 調整として hub が裁定する (a は merge 時に検出して申告する)。

### a の着手順 (9154 準拠)

1. **residue: Isaacs Thm 6.23 の standalone 化** (hub 裁定 §0、S サイズ、Pf 着手の前)
2. Pf 本文を上流優先 + 文書順で自律進行 (§3 は c が完了済ゆえスキップ)
