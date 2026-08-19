/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Solvable

/-!
# Isaacs Problem 3C.6 (書籍 p. 91) — 互いに素な位数の 3 元の積が 1 なら全て 1

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 3C.6 の形式化
(campaign issue 1055)。

**3C.6**: `G` を有限可解群とし, `x, y, z ∈ G` の位数が**対ごとに互いに素**とする。
`xyz = 1` なら `x = y = z = 1`。

## 証明 (書籍 Hint: 導来長に関する帰納)

核となるのは可換化 `G/⁅G,G⁆` での位数勘定 (`mem_commutator_of_mul_eq_one_of_coprime_orders`):
像を `x̄, ȳ, z̄` とすると `x̄ = (ȳ z̄)⁻¹` で, 可換かつ `o(ȳ), o(z̄)` は互いに素だから
`o(x̄) = o(ȳ) · o(z̄)`。一方 `o(x̄) ∣ o(x)` 等より `o(x̄)` は `o(ȳ) · o(z̄)` と互いに素なので
`o(x̄)` は自分自身と互いに素, すなわち `o(x̄) = 1`。ゆえに `x ∈ ⁅G,G⁆`。すると `ȳ z̄ = 1` で
`o(ȳ) = o(z̄)` となり, 互いに素性から両方 1, つまり `y, z ∈ ⁅G,G⁆`。

あとは `⁅G,G⁆` へ降りて帰納する。`G` が非自明可解なら `⁅G,G⁆ < ⊤`
(`Group.IsSolvable.commutator_lt_top_of_nontrivial`) なので `|⁅G,G⁆| < |G|`。書籍の
「導来長に関する帰納」を **`|G|` に関する強帰納**で実装している (導来列が真に減ることを
位数で測るだけなので同値)。

## Main results

- `mem_commutator_of_mul_eq_one_of_coprime_orders` — 可換化での位数勘定 (帰納の 1 段)。
- `eq_one_of_mul_eq_one_of_coprime_orders` — **Problem 3C.6**。
-/

namespace OddOrder.Isaacs.Ch03

universe u

section /- 3C: Problem 3C.6 (p. 91) -/

/-- 3C.6 の帰納 1 段: `xyz = 1` で位数が対ごとに互いに素なら, 3 元とも `⁅G,G⁆` に入る。

可換化 `G/⁅G,G⁆` へ落として位数を数える。像 `x̄` は `(ȳ z̄)⁻¹` で, 可換群なので
`o(ȳz̄) = o(ȳ)·o(z̄)` (互いに素)。`o(x̄)` はこれと互いに素かつこれに等しいので `o(x̄) = 1`。
`x̄ = 1` が出れば `ȳ = z̄⁻¹` で `o(ȳ) = o(z̄)`, 互いに素性から両方 1。

⚠ 有限性は不要 — `orderOf` が `0` (無限位数) でも `Nat.Coprime` の条件がそのまま効く。 -/
theorem mem_commutator_of_mul_eq_one_of_coprime_orders {G : Type u} [Group G] {x y z : G}
    (hxy : Nat.Coprime (orderOf x) (orderOf y))
    (hxz : Nat.Coprime (orderOf x) (orderOf z))
    (hyz : Nat.Coprime (orderOf y) (orderOf z))
    (h : x * y * z = 1) :
    x ∈ commutator G ∧ y ∈ commutator G ∧ z ∈ commutator G := by
  set f : G →* Abelianization G := Abelianization.of with hf
  -- 像の位数は元の位数を割るので, 互いに素性は像へ落ちる
  have hfxy : Nat.Coprime (orderOf (f x)) (orderOf (f y)) :=
    (hxy.coprime_dvd_left (orderOf_map_dvd f x)).coprime_dvd_right (orderOf_map_dvd f y)
  have hfxz : Nat.Coprime (orderOf (f x)) (orderOf (f z)) :=
    (hxz.coprime_dvd_left (orderOf_map_dvd f x)).coprime_dvd_right (orderOf_map_dvd f z)
  have hfyz : Nat.Coprime (orderOf (f y)) (orderOf (f z)) :=
    (hyz.coprime_dvd_left (orderOf_map_dvd f y)).coprime_dvd_right (orderOf_map_dvd f z)
  have hprod : f x * (f y * f z) = 1 := by
    rw [← mul_assoc, ← map_mul, ← map_mul, h, map_one]
  -- `o(x̄) = o(ȳ)·o(z̄)`
  have hordx : orderOf (f x) = orderOf (f y) * orderOf (f z) := by
    rw [eq_inv_of_mul_eq_one_left hprod, orderOf_inv,
      (Commute.all (f y) (f z)).orderOf_mul_eq_mul_orderOf_of_coprime hfyz]
  -- `o(x̄)` は自分自身と互いに素 ⟹ `o(x̄) = 1`
  have hcop : Nat.Coprime (orderOf (f x)) (orderOf (f y) * orderOf (f z)) := hfxy.mul_right hfxz
  rw [← hordx] at hcop
  have hfx1 : f x = 1 := orderOf_eq_one_iff.mp (by rwa [Nat.Coprime, Nat.gcd_self] at hcop)
  -- `ȳ z̄ = 1` から `o(ȳ) = o(z̄)`, 互いに素性で両方 1
  have hyz1 : f y * f z = 1 := by rwa [hfx1, one_mul] at hprod
  have hordy : orderOf (f y) = orderOf (f z) := by
    rw [eq_inv_of_mul_eq_one_left hyz1, orderOf_inv]
  rw [hordy] at hfyz
  have hfz1 : f z = 1 := orderOf_eq_one_iff.mp (by rwa [Nat.Coprime, Nat.gcd_self] at hfyz)
  have hfy1 : f y = 1 := by rwa [hfz1, mul_one] at hyz1
  have hmem : ∀ w : G, f w = 1 → w ∈ commutator G := fun w hw => by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hw
  exact ⟨hmem x hfx1, hmem y hfy1, hmem z hfz1⟩

/-- 3C.6 の帰納本体: `|G| ≤ n` に関する帰納。1 段ごとに `⁅G,G⁆` へ降りる。 -/
private theorem eq_one_aux : ∀ (n : ℕ) {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    (x y z : G), Nat.card G ≤ n →
    Nat.Coprime (orderOf x) (orderOf y) → Nat.Coprime (orderOf x) (orderOf z) →
    Nat.Coprime (orderOf y) (orderOf z) → x * y * z = 1 → x = 1 ∧ y = 1 ∧ z = 1 := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ _ _ _ hcard _ _ _ _
    exact absurd hcard (Nat.not_le.mpr Nat.card_pos)
  | succ n ih =>
    intro G _ _ _ x y z hcard hxy hxz hyz h
    rcases subsingleton_or_nontrivial G with _ | _
    · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    · obtain ⟨hx, hy, hz⟩ := mem_commutator_of_mul_eq_one_of_coprime_orders hxy hxz hyz h
      -- `G` 非自明可解 ⟹ `⁅G,G⁆ < ⊤` ⟹ `|⁅G,G⁆| < |G| ≤ n+1`
      have hlt : commutator G < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial G
      obtain ⟨g, hg⟩ : ∃ g : G, g ∉ commutator G := by
        by_contra hcon
        push Not at hcon
        exact hlt.ne (eq_top_iff.mpr fun a _ => hcon a)
      have hcardlt : Nat.card ↥(commutator G) < Nat.card G :=
        Finite.card_subtype_lt (p := fun a : G => a ∈ commutator G) (x := g) hg
      obtain ⟨hx1, hy1, hz1⟩ :=
        ih (G := ↥(commutator G)) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ (by omega)
          (by rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk])
          (by rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk])
          (by rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk])
          (Subtype.ext h)
      exact ⟨by simpa using Subtype.ext_iff.mp hx1, by simpa using Subtype.ext_iff.mp hy1,
        by simpa using Subtype.ext_iff.mp hz1⟩

/-- **Isaacs Problem 3C.6** (書籍 p. 91)。`G` を有限**可解**群, `x, y, z ∈ G` の位数が
対ごとに互いに素とする。`xyz = 1` なら `x = y = z = 1`。

⚠ 可解性は本質的: `A₅` は位数 2 の `a` と位数 3 の `b` で `ab` が位数 5 になるものをもつ
((2,3,5) 三角群としての表示; 例 `a = (1 2)(3 4)`, `b = (1 3 5)` で `ab` は 5-巡回)。
`c := (ab)⁻¹` とおけば `abc = 1` で位数 `2, 3, 5` は対ごとに互いに素。 -/
theorem eq_one_of_mul_eq_one_of_coprime_orders {G : Type u} [Group G] [Finite G]
    [Group.IsSolvable G] {x y z : G}
    (hxy : Nat.Coprime (orderOf x) (orderOf y))
    (hxz : Nat.Coprime (orderOf x) (orderOf z))
    (hyz : Nat.Coprime (orderOf y) (orderOf z))
    (h : x * y * z = 1) : x = 1 ∧ y = 1 ∧ z = 1 :=
  eq_one_aux (Nat.card G) x y z le_rfl hxy hxz hyz h

end -- Problem 3C.6

end OddOrder.Isaacs.Ch03
