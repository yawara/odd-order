---
id: 1037
slug: wielandt-aut-tower-9-10
title: "Theorem 9.10 Wielandt automorphism tower"
created: 2026-07-18
---

# Theorem 9.10 Wielandt automorphism tower

## 背景

Isaacs §9B の capstone (p. 271, mmd L5006)。`Z(G) = 1` ⇒ automorphism tower
`G_1 = G`, `G_{i+1} = Aut(G_i)` は同型を除いて有限種。§9B の解析補題は 2026-07-18 に
全て landed (レーン a):

- 9.11 (`InnerAutomorphisms.lean`): Inn(G) ◁ Aut(G), Z(G)=1 ⇒ C_{Aut}(Inn)=1, Z(Aut)=1。
- 9.12 (`AutTowerBounds.lean` `centralizer_eq_bot_of_chain`): chain の centralizer 消失。
- 9.13 (`OrderBound.lean` `card_le_of_normal_of_centralizer_eq_bot`):
  **S ◁ G**, C_G(S)=1 ⇒ |G| ≤ |Z(S^∞)|·|Aut(S^∞)| (normal 版, divisibility も)。
- 9.14 (`AutTowerBounds.lean`): N ◁ G, C_G(N)≤N ⇒ |G| ∣ |Z(N)||Aut(N)| / |N|!。
- 9.21/9.22 (`Schenkman.lean`): Schenkman **S ◁ G**, C_G(S)=1 ⇒ C_G(S^∞) ≤ S^∞。
- 9.16/9.18 (`NilpotentResidual.lean`/`SubnormalSocle.lean`): **S ◁◁ G** ⇒
  F(G), E(G) ≤ N_G(S^∞) (subnormal 版, F* 経由 bound 用)。

## ⚠ 未解決の設計・数学ギャップ (着手前に要解決)

**normal / subnormal のミスマッチ**: tower では `G_1` は各 `G_i` に **subnormal**
(consecutive normal chain `G_1 ◁ G_2 ◁ ⋯ ◁ G_i`) であって **normal ではない**
(書籍 p.278 が明言: "G is subnormal in each G_i, ... shows why subnormality theory
is relevant")。ところが |G_i| を抑える 9.13 と、その核 9.21 は **S ◁ G (normal) を
本質的に要求**する:
- 9.21 の証明は `G/S` を群として使い、中間 `H ⊇ S` に `S ◁ H` を使う → normal 必須。
- 9.13 の証明は 9.21 を呼ぶ → normal 必須。
- 直接ルート (本 repo の 9.13) も `S^∞ ◁ G` を要求 (subnormal では不成立)。

書籍 (p.282 "Proof of Theorem 9.13" + tower 結論) は「9.13 (S◁G) が tower の
immediate consequence」と書くが、`G_1` subnormal でどう 9.13 を当てるかが行間。
**この橋渡しを PDF 精読 + 必要なら Coq/ChatGPT で確定してから着手する** (CLAUDE.md
「行間で詰まったら原文/最強モデル」)。候補:
1. subnormal S 版の order bound を別途証明 (subnormal-9.21 が要る → 本当に成立するか?)。
2. tower 特有の構造 (各 G_i が centerless + C_{G_i}(G_1)=1) から `F*(G_i)` 経由で
   9.14 を直接当てる経路 (9.16/9.18 は subnormal 版なので F* ≤ N_{G_i}(G_1^∞) は言える;
   隘路は C_{N}(G_1^∞) ≤ G_1^∞ = subnormal-9.21 相当)。
   → `C_{G_i}(G_1^∞) ⊆ G_1^∞` を C_{G_i}(G_1)=1 (9.12) から subnormal でも導けるか要検討。
3. PDF に mmd がドロップした補足がある可能性 (near `[MISSING_PAGE_FAIL:302]`)。

## やること

- [ ] 上記 normal/subnormal ギャップを原文精読で確定 (最優先)。
- [ ] recursive type family `autTowerType : ℕ → Type u` (`0 ↦ G`, `n+1 ↦ MulAut (·)`)
      + 各段の `Group` instance (再帰) + centerless の伝播 (9.11d)。
- [ ] 埋め込み鎖 `G_i ↪ G_{i+1}` (Inn) と subnormality、C_{G_i}(G_1)=1 (9.12 適用)。
- [ ] |G_i| の一様上界 (9.13 または subnormal 版) → `∃ n, ∀ i, Nat.card (autTowerType G i) ≤ n`。
- [ ] leaf 例: `AutTower.lean` (import OrderBound + InnerAutomorphisms)。

## 完了条件

`Theorem 9.10` を sorry-free/axiom-clean で landing (`∃ n, ∀ i, |G_i| ≤ n` 形)。
full build green + AxiomsCheck OK。

## 参照

- notes/isaacs/ch09_more_subnormality.md (§9B 節)
- OddOrder/Isaacs/Ch09_MoreSubnormality/{OrderBound,Schenkman,AutTowerBounds,InnerAutomorphisms}.lean
- references/isaacs/finite-group-theory.mmd L5006–5145 (§9B); PDF p.278–283
