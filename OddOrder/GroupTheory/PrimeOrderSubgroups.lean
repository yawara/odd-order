/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Normal subgroups of prime order in `p`-groups are central

`OddOrder.GroupTheory` shared module: 位数 `p` の部分群まわりの基礎補題。

* `normal_le_center_of_card_eq_prime`: 有限 `p`-群の位数 `p` **正規**部分群は中心に
  含まれる。共役準同型 `P →* MulAut Y` の像は `p`-群だが、`Y` は位数 `p` の巡回群で
  `|MulAut Y| = p - 1` は `p` と互いに素、ゆえに像は自明。

mathlib v4.34.1 時点で未収載 (`Mathlib/GroupTheory/PGroup.lean` / `Nilpotent.lean` を確認,
2026-09-27)。近いのは `Group.IsNilpotent.inf_center_ne_bot_of_normal` (`H ⊓ Z(G) ≠ ⊥`) まで。

かつて同居していた「巡回群の位数 `p` 部分群の一意性」(`subgroup_eq_of_card_eq_prime_of_isCyclic`)
は、mathlib v4.34.0 の `IsCyclic.subgroup_eq_iff_card_eq` (位数が等しい部分群は一致、
素数位数に限らない) に置き換えて削除した (issue 0189)。

## 用途

Isaacs Thm 10.15 (Huppert metacyclic; issue 3007) の「`|P'| = p` ⇒ `P' ≤ Z(P)`」ステップ
(同じ証明の「cyclic `P'` の位数 `p` 部分群の一意性」ステップは mathlib で賄う)。claim = issue 9107。
-/

namespace OddOrder.GroupTheory

variable {p : ℕ} [hp : Fact p.Prime]

/-- A normal subgroup of order `p` in a finite `p`-group is central.

The conjugation homomorphism `P →* MulAut Y` has `p`-group image, while
`MulAut Y` has order `p - 1` (`Y` is cyclic of prime order), so the image is
trivial and `P` centralizes `Y`. -/
theorem normal_le_center_of_card_eq_prime {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) {Y : Subgroup P} [Y.Normal] (hY : Nat.card Y = p) :
    Y ≤ Subgroup.center P := by
  have hp_prime : p.Prime := hp.out
  have : IsCyclic ↥Y := isCyclic_of_prime_card hY
  set φ : P →* MulAut ↥Y := MulAut.conjNormal with hφ_def
  -- the image of the conjugation homomorphism is a `p`-group …
  have hrange : IsPGroup p ↥φ.range :=
    IsPGroup.of_surjective hP φ.rangeRestrict φ.rangeRestrict_surjective
  -- … inside a group of order `p - 1`
  have hcard_aut : Nat.card (MulAut ↥Y) = p - 1 := by
    rw [IsCyclic.card_mulAut, hY, Nat.totient_prime hp_prime]
  have hdvd : Nat.card ↥φ.range ∣ p - 1 := by
    rw [← hcard_aut]
    exact Subgroup.card_subgroup_dvd_card φ.range
  -- hence the image is trivial
  have hrange_bot : φ.range = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hrange
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · exact Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero])
    · exfalso
      have hpdvd : p ∣ p - 1 := dvd_trans (dvd_pow_self p hk1.ne') (hk ▸ hdvd)
      have hp2 : 2 ≤ p := hp_prime.two_le
      have := Nat.le_of_dvd (by omega) hpdvd
      omega
  -- so every element of `Y` commutes with every element of `P`
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro g
  have hφg : φ g = 1 := by
    have hmem : φ g ∈ φ.range := ⟨g, rfl⟩
    rwa [hrange_bot, Subgroup.mem_bot] at hmem
  have hconj : g * y * g⁻¹ = y := by
    have := congrArg (fun ψ : MulAut ↥Y => ((ψ ⟨y, hy⟩ : ↥Y) : P)) hφg
    simpa [hφ_def] using this
  calc g * y = g * y * g⁻¹ * g := by group
    _ = y * g := by rw [hconj]

end OddOrder.GroupTheory
