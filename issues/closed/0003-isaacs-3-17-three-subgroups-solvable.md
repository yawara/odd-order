---
id: 3
slug: isaacs-3-17-three-subgroups-solvable
title: "Isaacs Thm 3.17 Wielandt 3 部分群 solvability 実装"
created: 2026-05-24
---

# Isaacs Thm 3.17 Wielandt 3 部分群 solvability 実装

## 背景

Isaacs Thm 3.17 (Wielandt 1971): `H, K, L ≤ G` の 3 部分群が pairwise coprime index
(`gcd(|G:H|, |G:K|) = gcd(|G:H|, |G:L|) = gcd(|G:K|, |G:L|) = 1`) + 各々 solvable
⇒ G solvable.

owner chapter 規則で Ch.7 (Burnside) ディレクトリの placeholder ファイル
[`OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean`](../OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean)
に statement と証明戦略を記載済 (中身は空 namespace のみ).

証明戦略 (Isaacs p.85): `|G|`-induction. 最小反例 G, minimal normal M.
G/M は IH で solvable. M も `(H ∩ M)`, `(K ∩ M)`, `(L ∩ M)` 経由で IH より solvable.
G simple 場合 (M = G) に Burnside `pᵃqᵇ` 必須.

## やること

- [ ] Ch.7 Burnside `pᵃqᵇ` 定理の実装完了を待つ
- [ ] `OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean` に
      `solvable_of_three_subgroups` (仮名) を実装
- [ ] `|G|`-induction の各ケースを展開
- [ ] G simple 場合に Burnside 適用

## 完了条件

- `Ch07_ThompsonSubgroup/ForwardFromCh03.lean` 内に Thm 3.17 が sorry-free theorem として実装される
- `lake build` が通る

## 参照

- [OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean](../OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean) (placeholder)
- [notes/isaacs/ch03_split.md](../notes/isaacs/ch03_split.md) §3C
- [notes/meta/forward_dep_policy.md](../notes/meta/forward_dep_policy.md)
- Isaacs FGT p.85 (Thm 3.17)
- 関連 issue: 0002 (Thm 3.15, 同じく Burnside 依存)

> 🧾 (2026-07-02 hub 全体レビュー): trigger (Burnside p^aq^b = `burnside_p_pow_q_pow`, axiom-clean) は **fired 済** — ただし本 issue は off-FT-path につき coverage phase まで park 継続。

## 2026-07-17 close

`isSolvable_of_pairwise_coprime_index` (Ch03_SplitExtensions/Theorem315.lean) として sorry-free 実装済み (2026-07-17 Ch.3 survey-gap 一掃; Burnside 不要と判明). 完了条件充足につき close.
