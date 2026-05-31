/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.BG.Ch1_Preliminary.S04_PGroupsSmallRank

/-!
# BG §4 — Proposition 4.11 (Huppert)

> **本** Bender–Glauberman, *Local Analysis for the Odd Order Theorem* §4,
> Proposition 4.11 (Huppert, *Endliche Gruppen I*, Satz III.11.6).

**Prop 4.11**: `p` 素数, `p > 3`, `R` 有限 `p`-群, `|Ω₁(R)| ≤ p²` ⇒ `R` は metacyclic。

`|R|` 帰納 + 前補題 (Lem 4.9 `card_omega1_quotient_le_prime_sq`, Lem 4.5(b)
`isElementaryAbelian_omega1_of_isCyclic_index_prime`, Lem 4.2, Lem 4.1, agemo `Agemo`)。

S04 本体 (`S04_PGroupsSmallRank.lean`) が肥大しているため、Prop 4.11 とその補助補題は
本 leaf に分離 (S04 を凍結し再ビルドを軽く保つ)。namespace は §4 共通の
`OddOrder.BG.Ch1.S04`。
-/

open scoped commutatorElement

namespace OddOrder.BG.Ch1.S04

open OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- **In a finite `p`-group, a normal subgroup of order `p` is central.**

A nontrivial normal subgroup of a finite `p`-group meets the centre
(`IsPGroup.normal_inf_center_nontrivial`); since `|N| = p` is prime, the nontrivial
subgroup `N ⊓ Z(R)` of `N` must be all of `N`, so `N ≤ Z(R)`.

(BG §4 Prop 4.11 の step 6 で `⟨a,z⟩/⟨aᵖ,z⟩` (位数 `p` の normal) が中心に入ることに使う。) -/
theorem le_center_of_card_eq_prime_of_normal (hR : IsPGroup p R)
    {N : Subgroup R} [N.Normal] (hN : Nat.card N = p) : N ≤ Subgroup.center R := by
  have hp : p.Prime := Fact.out
  haveI hNnt : Nontrivial N :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hN]; exact hp.one_lt)
  have hmeet : Nontrivial ((N ⊓ Subgroup.center R : Subgroup R)) :=
    OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hR hNnt
  have hle : (N ⊓ Subgroup.center R : Subgroup R) ≤ N := inf_le_left
  have hcard_dvd : Nat.card (N ⊓ Subgroup.center R : Subgroup R) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le hle
  have hcard_ne_one : Nat.card (N ⊓ Subgroup.center R : Subgroup R) ≠ 1 :=
    (Finite.one_lt_card_iff_nontrivial.mpr hmeet).ne'
  have hcard_eq : Nat.card (N ⊓ Subgroup.center R : Subgroup R) = p := by
    rcases (Nat.dvd_prime hp).mp (hN ▸ hcard_dvd) with h1 | hp'
    · exact absurd h1 hcard_ne_one
    · exact hp'
  have heq : (N ⊓ Subgroup.center R : Subgroup R) = N :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard_eq, hN])
  calc N = (N ⊓ Subgroup.center R : Subgroup R) := heq.symm
    _ ≤ Subgroup.center R := inf_le_right

end OddOrder.BG.Ch1.S04
