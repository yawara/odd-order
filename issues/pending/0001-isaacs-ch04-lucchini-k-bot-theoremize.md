---
id: 1
slug: isaacs-ch04-lucchini-k-bot-theoremize
title: "Isaacs Thm 2.20 Lucchini K=⊥ case を axiom から theorem へ"
created: 2026-05-24
---

# Isaacs Thm 2.20 Lucchini K=⊥ case を axiom から theorem へ

## 背景

Isaacs Thm 2.20 Lucchini (`A` cyclic 真部分群, `K = core_G(A)` ⇒ `|A:K| < |G:A|`) は
owner chapter 規則により Ch.4 dir に物理配置された:

- Ch.2 内: `lucchini_K_pos_reduction` (K > ⊥ structural reduction, subgroup correspondence のみ) ✅
- Ch.4 dir 内 ([Ch04_Commutators/ForwardFromCh02.lean](../OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean)):
  - `lucchini_K_bot_aux` (K = ⊥ case) — **axiom** (現状)
  - `lucchini_aux` + `lucchini_index_normalCore_lt_index` (`|G|`-induction wrapper + 本体 theorem)

K = ⊥ branch の完全証明には Ch.4 §4A-§4B の lower central series 加法性
(`[γᵢ(F), γⱼ(F)] ⊆ γᵢ₊ⱼ(F)`, Isaacs Thm 4.11) と minimal normal `E ⊆ F(G) ⇒ E ⊆ Z(F(G))`
が必要なので, Ch.4 §4A-§4B 完成後に theorem 化する.

下流影響: `OddOrder.Isaacs.Ch03.horosevskii_aut_order_lt` (Thm 3.3) の axioms 閉包に
`lucchini_K_bot_aux` が現れる. theorem 化されると Horosevskii も自動で unconditional になる.

## やること

- [ ] Ch.4 §4A-§4B (lcs 加法性) 完成を待つ
- [ ] `lucchini_K_bot_aux` の body を埋めて `axiom` を `theorem` (or `private theorem`) に置換
- [ ] AxiomsCheck.lean に Thm 2.20 / Thm 3.3 の flagship 追加 (現状はどちらも未登録)
- [ ] `#print axioms OddOrder.Isaacs.Ch03.horosevskii_aut_order_lt` が標準 3 公理のみに依存することを確認

## 完了条件

- `OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean` から `axiom lucchini_K_bot_aux` 行が消える
- `lake build OddOrder.AxiomsCheck` が `lucchini_index_normalCore_lt_index` を flagship として通過

## 参照

- [Ch04_Commutators/ForwardFromCh02.lean:55](../OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean) (axiom 定義)
- [notes/meta/forward_dep_policy.md](../notes/meta/forward_dep_policy.md)
- [notes/isaacs/ch02_subnormality.md](../notes/isaacs/ch02_subnormality.md) §2D
- [notes/isaacs/ch04_commutators.md](../notes/isaacs/ch04_commutators.md) §4A-§4B
- Isaacs FGT pp.62-63 (Lucchini 証明本体)
