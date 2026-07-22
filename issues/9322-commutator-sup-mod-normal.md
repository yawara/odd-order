---
id: 9322
slug: commutator-sup-mod-normal
title: "normal quotient 上の commutator-sup API を shared 化"
created: 2026-07-23
---

# normal quotient 上の commutator-sup API を shared 化

## claim

- owner: lane b
- claimed: 2026-07-23
- consumer: Higman Lemma 13 p.92 final Frattini-square contradiction
- shared target: `OddOrder/GroupTheory/CommutatorSup.lean`
- downstream compatibility check:
  `OddOrder/BG/AppE_EigenvalueCombinatorics.lean`

## 背景

normal subgroup `K` modulo で
`⁅A, B⁆ ≤ K` と `⁅A, C⁆ ≤ K` から `⁅A, B ⊔ C⁆ ≤ K` を得る
generic lemma が BG Appendix E leaf 内に埋まっている。Higman Lemma 13 の
factor-cover endpoint でも同じ事実が必要だが、Higman から BG を import するのは
依存方向が逆になる。重複 wrapper は作らず、既存 proof を shared GroupTheory leaf
へ移設し、BG consumer も shared theorem を直接使う。

## やること

- [ ] generic theorem を `OddOrder.GroupTheory` へ移設
- [ ] BG の既存 consumer を shared theorem へ付け替え
- [ ] 新 leaf を `OddOrder.lean` に配線
- [ ] targeted build と warning ratchet
- [ ] issue を closed に移す

## 完了条件

新規 sorry/axiom なし。shared leaf、BG consumer、Higman consumer の targeted build が
green で、warning ratchet が baseline 内。
