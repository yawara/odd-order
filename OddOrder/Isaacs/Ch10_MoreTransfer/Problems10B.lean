/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.IsMetacyclic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Isaacs, Finite Group Theory — Problems 10B (書籍 p. 312)

> **10B.1.** Given a prime `p` and an integer `n > 0`, let `C = ⟨x⟩` be a cyclic group of
> order `p^n`.  Let `a ∈ Aut(C)` with `x^a = x^{p+1}`, and let `P = C ⋊ ⟨a⟩`.  Show that
> `P` is a metacyclic `p`-group with nilpotence class `n`.  *Hint.* Use Theorem 4.7.

本 leaf は 10B.1 の部品を積む。第一段の「metacyclic」は
`OddOrder.GroupTheory.isMetacyclic_semidirectProduct` (巡回群同士の半直積は metacyclic)。

`p`-群性の核心は **`1 + p` の `(ZMod (p^n))ˣ` での位数が `p` 冪**であること:
`1 + p` は還元写像 `(ZMod (p^n))ˣ → (ZMod p)ˣ` の核に入り, その核の位数は
`φ(p^n) / (p - 1) = p^{n-1}`。

## Main results

* `OddOrder.Isaacs.Ch10.orderOf_dvd_of_unitsMap_eq_one` — 還元の核の元は位数が
  `p^{n-1}` を割る。
* `OddOrder.Isaacs.Ch10.orderOf_one_add_prime_dvd` — `1 + p` の位数は `p^{n-1}` を割る。
-/

set_option autoImplicit false

namespace OddOrder.Isaacs.Ch10

section /- 10B.1: `(ZMod (p^n))ˣ` の `1`-単位群は `p`-群 (p. 312) -/

variable {p n : ℕ}

/-- 還元写像 `(ZMod (p^n))ˣ → (ZMod p)ˣ` の核の位数は `p^{n-1}`. -/
theorem card_ker_unitsMap (hp : p.Prime) (hn : 0 < n) :
    Nat.card ↥(ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n)).ker = p ^ (n - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have hsurj := ZMod.unitsMap_surjective (m := p ^ n) (n := p) (dvd_pow_self p hn.ne')
  have hcard : Nat.card ((ZMod (p ^ n))ˣ) = p ^ (n - 1) * (p - 1) := by
    haveI : Fintype (ZMod (p ^ n)) := ZMod.fintype _
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp hn]
  have hcardp : Nat.card ((ZMod p)ˣ) = p - 1 := by
    haveI : Fintype (ZMod p) := ZMod.fintype _
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hquot : Nat.card ((ZMod (p ^ n))ˣ ⧸
      (ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n)).ker) = p - 1 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv, hcardp]
  have hmul := Subgroup.card_mul_index
    (ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n)).ker
  rw [show (ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n)).ker.index = p - 1 from hquot,
    hcard] at hmul
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  exact Nat.eq_of_mul_eq_mul_right hp1 hmul

/-- 還元が `1` になる単元の位数は `p^{n-1}` を割る. -/
theorem orderOf_dvd_of_unitsMap_eq_one (hp : p.Prime) (hn : 0 < n)
    {u : (ZMod (p ^ n))ˣ}
    (hu : ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n) u = 1) :
    orderOf u ∣ p ^ (n - 1) := by
  have hmem : u ∈ (ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n)).ker :=
    MonoidHom.mem_ker.mpr hu
  have hd := orderOf_dvd_natCard (⟨u, hmem⟩ :
    ↥(ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n)).ker)
  rw [card_ker_unitsMap hp hn] at hd
  simpa using hd

/-- **`1 + p` の `(ZMod (p^n))ˣ` での位数は `p^{n-1}` を割る** (だから `p` 冪). -/
theorem orderOf_one_add_prime_dvd (hp : p.Prime) (hn : 0 < n) {u : (ZMod (p ^ n))ˣ}
    (hu : (u : ZMod (p ^ n)) = 1 + (p : ZMod (p ^ n))) : orderOf u ∣ p ^ (n - 1) := by
  refine orderOf_dvd_of_unitsMap_eq_one hp hn ?_
  refine Units.ext ?_
  rw [ZMod.unitsMap_val, hu]
  change (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) (1 + (p : ZMod (p ^ n))) = 1
  rw [map_add, map_one, map_natCast, ZMod.natCast_self, add_zero]

end

end OddOrder.Isaacs.Ch10
