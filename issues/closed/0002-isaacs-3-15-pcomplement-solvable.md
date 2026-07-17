---
id: 2
slug: isaacs-3-15-pcomplement-solvable
title: "Isaacs Thm 3.15 (∀p に p-complement ⇒ solvable) 実装"
created: 2026-05-24
---

# Isaacs Thm 3.15 (∀p に p-complement ⇒ solvable) 実装

## 背景

Isaacs Thm 3.15 (Hall's converse): 有限群 `G` が任意の素数 `p` について
p-complement (= `{p}'`-Hall) を持つならば `G` は solvable.

Isaacs p.84 で「Thm 3.15 in full generality は Burnside `pᵃqᵇ` を仮定すれば容易」と明言.
owner chapter 規則で Ch.7 (Burnside) ディレクトリの placeholder ファイル
[`OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean`](../OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean)
に statement と証明戦略を記載済 (中身は空 namespace のみ).

## やること

- [ ] Ch.7 Burnside `pᵃqᵇ` 定理の実装完了を待つ
- [ ] `OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean` に
      `solvable_of_pcomplement_exists` (仮名) を実装
- [ ] `|G|`-induction. p, q 相異なる素数で H_p (p-complement), H_q (q-complement) を取り
      H_p ∩ H_q が `{p,q}'`-Hall に相当することと, 商・部分群の solvability を組み合わせる
- [ ] G simple 場合に Burnside 適用

## 完了条件

- `Ch07_ThompsonSubgroup/ForwardFromCh03.lean` 内に Thm 3.15 が sorry-free theorem として実装される
- `lake build` が通る
- AxiomsCheck flagship に追加可能であれば追加

## 参照

- [OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean](../OddOrder/Isaacs/Ch07_ThompsonSubgroup/ForwardFromCh03.lean) (placeholder)
- [notes/isaacs/ch03_split.md](../notes/isaacs/ch03_split.md) §3C
- [notes/meta/forward_dep_policy.md](../notes/meta/forward_dep_policy.md)
- Isaacs FGT p.84 (Thm 3.15)
- 関連 issue: 0003 (Thm 3.17, 同じく Burnside 依存)

> 🧾 (2026-07-02 hub 全体レビュー): trigger (Burnside p^aq^b = `burnside_p_pow_q_pow`, axiom-clean) は **fired 済** — ただし本 issue は off-FT-path につき coverage phase まで park 継続。

## 2026-07-17 close

`isSolvable_of_pcomplement_exists` (Ch07_ThompsonSubgroup/ForwardFromCh03.lean, Burnside + 3.17 経由) として sorry-free 実装済み (2026-07-17 Ch.3 survey-gap 一掃, AxiomsCheck 登録済). 完了条件充足につき close.
