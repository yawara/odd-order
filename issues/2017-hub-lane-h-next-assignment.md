---
id: 2017
slug: hub-lane-h-next-assignment
title: "HUB: lane-h next assignment — ungated work exhausted, all residuals cross-lane"
created: 2026-06-23
---

# HUB: lane-h next assignment — ungated work exhausted, all residuals cross-lane

## 判断を仰ぐ内容 (HUB へ)

lane-h (Pf §14_MaximalI + §15 S&T) は **自セグメント内の ungated closable Lean work を出し尽くした**。
残る S14/S15 の sorry は全て cross-lane。lane-h の次の割当を判断してほしい (read-only 監査 +
必要ならユーザーへ AskUserQuestion)。lane-h 自身では cross-lane ゆえ独断しない。

## lane-h 現状 (2026-06-23 resume¹²)

- **landed (this session)**: BG Lemma 3.2 完全版 (K⊄N 枝, `S03_FrobeniusActions.lean`, main 合流済
  `b9bb6b9d`) + (12.9) gated-endpoint skeleton (proven BG Theorem B(1) を wire, commit `96c793b0`)。
- §9 Wielandt chain / (12.9) centralizer core / (12.12) rep-theory cores はすべて DONE・axiom-clean。
- FT-path sorry = 124。build green。

## 残 sorry は全て cross-lane

| 結果 | gate | 担当レーン |
|---|---|---|
| (12.9) `counterexample_P0_K_structure` | `(κ∪σ)ᶜ`-Hall 複体 = **Prop 16.1** (issue 2016) | **lane-f** (BG §16) |
| (12.11) `intersection_complement_structure` | (8.13.c1) | lane-f (BG §16) |
| (12.2-5),(12.13-16),(13.3-15) char-grid | character theory | lane-b |
| (13.16) full `normalizer_W1` | card_Q_eq + T-side + §13 structural (残 5 obligation) | cross-lane |

## 選択肢 (HUB が判断 / 必要ならユーザーへ)

- **(a) lane-h を lane-f Prop 16.1 支援へ** — 最高レバレッジ: Prop 16.1 が (12.9) [issue 2016] +
  §16 の多くを unblock。ただし lane-f が active frontier ゆえ衝突調整要 (所有境界 / 分担)。
- **(b) lane-h を lane-b char 支援へ** — §12/§13 char-grid。lane-b はユーザー直接管理ゆえ衝突注意。
- **(c) lane-h stand by** — cross-lane prerequisite (Prop 16.1 / lane-b char) landing 待ち、
  landing 時に機会的 close (driver 化)。
- **(d) lane-h を別セグメントへ再配置** — 例: 別の §8-free infra / BG §3 周辺の reusable 群論。

## 参照

- `notes/peterfalvi/s14_maximalI.md` 「(12.9) status (resume¹²)」
- issue 2016 (12.9 ← Prop 16.1)
- [[ft-endgame-two-poles]] (lane-f frontier = Prop 16.1) / [[peterfalvi-work-in-worktree]] (lane layout)
