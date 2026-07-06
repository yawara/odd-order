---
id: 9037
slug: elementary-abelian-quotient-bot
title: "Public elementary abelian quotient-bot API"
created: 2026-07-06
---

# Public elementary abelian quotient-bot API

## 背景

BG §1 `S01_Solvable.lean` has a private `quotient_bot_isElementaryAbelian`
helper. The fact is a generic transport of elementary abelianness across
`QuotientGroup.quotientBot`.

## やること

- [x] Add public `OddOrder.GroupTheory.IsElementaryAbelian.quotient_bot`.
- [x] Build `OddOrder.GroupTheory.ElementaryAbelian`.

## 完了条件

The lemma is sorry-free, the target leaf build passes, and this issue is moved to
`issues/closed/`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/GroupTheory/ElementaryAbelian.lean`


## 完了メモ

2026-07-06 lane d: added public `IsElementaryAbelian.quotient_bot` via
`QuotientGroup.quotientBot`. Verified by
`lake build OddOrder.GroupTheory.ElementaryAbelian`.
