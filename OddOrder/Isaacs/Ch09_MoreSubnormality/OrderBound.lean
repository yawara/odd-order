/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.AutTowerBounds
import OddOrder.Isaacs.Ch09_MoreSubnormality.Schenkman
import OddOrder.Isaacs.Ch09_MoreSubnormality.GeneralizedFitting
import OddOrder.Isaacs.Ch09_MoreSubnormality.SubnormalSocle

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

open scoped Nat

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

section /- 9B: Theorem 9.13 — subnormal 版 (書籍 p. 281 の F* 経由ルート) -/

/-- `S ◁◁ G`, `C_G(S) = 1` のとき `|N_G(S^∞)| ≤ |Z(S^∞)| · |Aut(S^∞)|`.

書籍 p. 281 の第一段: `S^∞` は `N = N_G(S^∞)` の中で normal であり, subnormal 版 9.21
(`centralizer_nilpotentResidual_le_of_isSubnormal`) を `↥N` の中の `S.subgroupOf N`
に当てると `C_N(S^∞) ≤ S^∞`. そこへ 9.14 を適用する. -/
theorem card_normalizer_nilpotentResidual_le [Finite G] {S : Subgroup G}
    (hS : S.IsSubnormal) (hCS : Subgroup.centralizer (S : Set G) = ⊥) :
    Nat.card ↥(Subgroup.normalizer (nilpotentResidual S : Set G))
      ≤ Nat.card (Subgroup.center ↥(nilpotentResidual S))
        * Nat.card (MulAut ↥(nilpotentResidual S)) := by
  set N := Subgroup.normalizer (nilpotentResidual S : Set G) with hN
  have hSN : S ≤ N := le_normalizer_nilpotentResidual S
  -- `↥N` の中の `S` の nilpotent residual は `S^∞` を `N` に降ろしたもの
  have hres : nilpotentResidual (S.subgroupOf N) = (nilpotentResidual S).subgroupOf N := by
    refine Subgroup.map_injective N.subtype_injective ?_
    rw [map_subtype_nilpotentResidual_subgroupOf hSN, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (by rw [hN]; exact Subgroup.le_normalizer)]
  haveI hresN : (nilpotentResidual (S.subgroupOf N)).Normal := by
    rw [hres]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (by rw [hN]; exact Subgroup.le_normalizer)).mpr le_rfl
  -- subnormal 版 9.21 を `↥N` で適用
  have h921 := centralizer_nilpotentResidual_le_of_isSubnormal (G := ↥N)
    hS.subgroupOf (centralizer_subgroupOf_eq_bot hSN hCS)
  -- 9.14: `|↥N| ∣ |Z(S^∞)| · |Aut(S^∞)|` (`↥(S^∞ ∩ N) ≃* ↥(S^∞)` で読み替え)
  have hiso : ↥(nilpotentResidual (S.subgroupOf N)) ≃* ↥(nilpotentResidual S) := by
    refine (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective).trans ?_
    exact MulEquiv.subgroupCongr (map_subtype_nilpotentResidual_subgroupOf hSN)
  refine Nat.le_of_dvd (Nat.mul_pos Nat.card_pos Nat.card_pos) ?_
  have hdvd := card_dvd_card_center_mul_card_mulAut (G := ↥N) h921
  rwa [Nat.card_congr (Subgroup.centerCongr hiso).toEquiv,
    Nat.card_congr (mulAutEquivCongr hiso)] at hdvd

/-- **Isaacs Theorem 9.13** (原典どおりの subnormal 版, p. 281): `S ◁◁ G` (有限群),
`C_G(S) = 1` ならば `|G| ≤ (|Z(S^∞)| · |Aut(S^∞)|)!`
(`S` の同型型のみで定まる上界).

書籍 p. 281 の証明:
1. `|N_G(S^∞)| ≤ |Z(S^∞)|·|Aut(S^∞)|` (`card_normalizer_nilpotentResidual_le`).
2. `F*(G) = F(G)E(G) ≤ N_G(S^∞)` — 9.16 / 9.18 の **subnormal 版**.
3. `C_G(F*(G)) ≤ F*(G)` (9.8) に 9.14 の階乗形を当てて `|G| ≤ |F*(G)|!`.

⚠ 仮説は原典どおり **subnormal**. `S ◁ G` の場合はより鋭い階乗なしの bound
(`card_le_of_normal_of_centralizer_eq_bot`) が上にあるのでそちらを使う.
Thm 9.10 (automorphism tower) では `G_1` が `G_i` に subnormal 止まりなので
**本定理が必要**. -/
theorem card_le_factorial_of_isSubnormal [Finite G] {S : Subgroup G}
    (hS : S.IsSubnormal) (hCS : Subgroup.centralizer (S : Set G) = ⊥) :
    Nat.card G ≤ (Nat.card (Subgroup.center ↥(nilpotentResidual S))
      * Nat.card (MulAut ↥(nilpotentResidual S)))! := by
  -- `F*(G) ≤ N_G(S^∞)` (9.16 + 9.18, いずれも subnormal 版)
  have hFstar : genFitting G ≤ Subgroup.normalizer (nilpotentResidual S : Set G) :=
    sup_le (fitting_le_normalizer_nilpotentResidual hS)
      (layer_le_normalizer_nilpotentResidual hS)
  -- `|G| ∣ |F*(G)|!` (9.8 + 9.14 階乗形)
  have hGdvd : Nat.card G ∣ (Nat.card ↥(genFitting G))! :=
    card_dvd_factorial_card_of_centralizer_le centralizer_genFitting_le_genFitting
  -- `|F*(G)| ≤ |N_G(S^∞)| ≤ |Z(S^∞)|·|Aut(S^∞)|`
  have hFcard : Nat.card ↥(genFitting G)
      ≤ Nat.card (Subgroup.center ↥(nilpotentResidual S))
        * Nat.card (MulAut ↥(nilpotentResidual S)) :=
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hFstar)).trans
      (card_normalizer_nilpotentResidual_le hS hCS)
  exact (Nat.le_of_dvd (Nat.factorial_pos _) hGdvd).trans (Nat.factorial_le hFcard)

end

end OddOrder.Isaacs.Ch09
