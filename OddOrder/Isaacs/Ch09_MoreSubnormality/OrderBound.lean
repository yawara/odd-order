/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.AutTowerBounds
import OddOrder.Isaacs.Ch09_MoreSubnormality.Schenkman

/-!
# Isaacs Ch. 9 — §9B: Theorem 9.13 (order bound), p. 279–282

Wielandt automorphism tower theorem (Thm 9.10) の最後の一般補題.

- **Theorem 9.13** (`card_dvd_of_normal_of_centralizer_eq_bot` /
  `card_le_of_normal_of_centralizer_eq_bot`): `S ◁ G` (有限群), `C_G(S) = 1` ならば
  `|G| ∣ |Z(S^∞)| · |Aut(S^∞)|`, 特に `|G| ≤ |Z(S^∞)| · |Aut(S^∞)|`
  (`S` の同型型のみで定まる上界).

## 実装ノート

書籍 (p. 282) は `F*(G) = F(G)E(G)` を経由する: 9.16/9.18 で `F*(G) ≤ N_G(S^∞)`,
9.14 で `|N_G(S^∞)| ∣ |Z(S^∞)||Aut(S^∞)|`, 9.8 で `C_G(F*) ≤ F*`, 再び 9.14 で
`|G| ∣ |F*|!` として `|G| ≤ (|Z(S^∞)||Aut(S^∞)|)!` を得る (factorial 上界)。

本ファイルは **より直接的で強い bound** を採る: 仮定が `S ◁ G` (normal) なので
`S^∞ = nilpotentResidual S` も `G` に normal (`nilpotentResidual.normal`)。よって
9.21 (`C_G(S^∞) ≤ S^∞`) と 9.14 第一形 (`card_dvd_card_center_mul_card_mulAut`) を
`G` に直接当てて `|G| ∣ |Z(S^∞)||Aut(S^∞)|` を得る (書籍の factorial 上界より真に強い)。
書籍が `F*` を経由するのは、その手法が (S が subnormal の) automorphism tower の状況
(9.10) に一般化するための布石であり、`S ◁ G` の 9.13 単体には不要。

`F*` 経由の pieces (9.16 `fitting_le_normalizer_nilpotentResidual`, 9.18
`layer_le_normalizer_nilpotentResidual`, 9.8 `centralizer_genFitting_le_genFitting`)
は 9.10 で別途使う。
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

variable {G : Type*} [Group G]

section /- 9B: Theorem 9.13 (order bound, p. 279) -/

/-- **Isaacs Theorem 9.13** (order bound, divisibility 形, p. 279): `S ◁ G` (有限群),
`C_G(S) = 1` ならば `|G| ∣ |Z(S^∞)| · |Aut(S^∞)|`.

`S ◁ G` ゆえ `S^∞ ◁ G` かつ 9.21 で `C_G(S^∞) ≤ S^∞`, これに 9.14 を当てる. -/
theorem card_dvd_of_normal_of_centralizer_eq_bot [Finite G] {S : Subgroup G} [S.Normal]
    (hCS : Subgroup.centralizer (S : Set G) = ⊥) :
    Nat.card G ∣ Nat.card (Subgroup.center ↥(nilpotentResidual S))
      * Nat.card (MulAut ↥(nilpotentResidual S)) :=
  card_dvd_card_center_mul_card_mulAut
    (centralizer_nilpotentResidual_le_of_centralizer_eq_bot hCS)

/-- **Isaacs Theorem 9.13** (order bound, p. 279): `S ◁ G` (有限群), `C_G(S) = 1` ならば
`|G|` は `S` の同型型のみで定まる値 `|Z(S^∞)| · |Aut(S^∞)|` で上から抑えられる. -/
theorem card_le_of_normal_of_centralizer_eq_bot [Finite G] {S : Subgroup G} [S.Normal]
    (hCS : Subgroup.centralizer (S : Set G) = ⊥) :
    Nat.card G ≤ Nat.card (Subgroup.center ↥(nilpotentResidual S))
      * Nat.card (MulAut ↥(nilpotentResidual S)) :=
  Nat.le_of_dvd (Nat.mul_pos Nat.card_pos Nat.card_pos)
    (card_dvd_of_normal_of_centralizer_eq_bot hCS)

end

end OddOrder.Isaacs.Ch09
