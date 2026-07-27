---
id: 9212
slug: sec8c-duplicate-sessions
title: "§8C を 2 セッションが並行駆動している — 担当の一本化を要請"
created: 2026-07-27
---

# §8C を 2 セッションが並行駆動している — 担当の一本化を要請

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 事象

Isaacs §8C (issue 1055) を **2 つのセッションが同時に駆動している**形跡がある。
2026-07-27 21:00–21:45 に、ほぼ同内容・同時刻の commit が両側から入った:

* こちら側 (この lane a セッション): `b2bc01b00` (PrimeDegree.lean 配線 +
  `card_normalizer_sylow_eleven_eq_55`) / `164cc8f17` (MathieuEleven / MathieuTwelve /
  SimpleStabilizer を commit) / `d343b78b7` (docs)
* もう一方: `37ae5751e` / `45513ea9e` / `e8893f507` / `753ec12dd` / `7f0b2f497`
  (8C.1–8C.4 と同じ内容)

**現状の実害は無い**: `git merge main` で綺麗に合流し、build green・axiom-clean・
宣言の重複なし (issue 1055 に先行セッションが同趣旨の注記を残している)。
ただし同じ問題を 2 回解くのは純粋な無駄。

## 依頼

**§8C の残り (8C.5 / 8C.6) の担当を一本化してほしい。**

こちらの取った暫定措置 (hub 裁定が出るまで):

* **8C.5 は触らない** — issue 1055 に詳細な設計メモ (次数 22/24 は共通補題、
  次数 23 は `Aut(Z₂₃)` 埋め込み、Wielandt 9.1 で 1 点ずつ剥がす) を書いたのは
  もう一方のセッションと思われるので、そちらに委ねる。
* **8C.6 をこちらが担当**と issue 1055 に明記して着手する
  (`Aut(A)` 単純 ⟺ `|A| = 3` または `A` が位数 8 以上の初等可換 2-群)。
  8C.5 とは独立なので衝突しない。

hub の裁定 (どちらのセッションが §8C を継続するか、あるいは 8C.5/8C.6 で分担するか) を
issue に記録してもらえれば、それに従う。

## 参考

cross-session の同期手段は notes/issue 追記 + merge cron のみ
(`send_message` は unsupervised session に届かない)。本 issue と 1055 の
「担当」行がその実体。
