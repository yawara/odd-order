/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.PRegularElement

/-!
# A `p`-subgroup sees the factorisations `g = x y` only through its centraliser

Fix a prime `p` and `g ∈ C_G(Q)` for a `p`-subgroup `Q ≤ G`, and consider the pairs

`Ω(g) = {(x, y) : x a p-element, y p-regular, x y = g}`.

`Q` acts on `Ω(g)` by simultaneous conjugation — this is where `g ∈ C_G(Q)` is used — and the
fixed points are the pairs with both entries in `C_G(Q)`.  A `p`-group has `p`-power orbits, so

`|Ω(g)| ≡ |Ω(g) ∩ (C_G(Q) × C_G(Q))| (mod p)`.

This is **Navarro, Problem (6.1) (Külshammer)**, the counting step that turns Külshammer's formula
for the principal block idempotent into the third main theorem for `Q C_G(Q) ≤ H ≤ N_G(Q)`.  The
same action applied to `G⁰` itself gives `|G⁰| ≡ |C_G(Q)⁰| (mod p)`
(`card_pRegular_modEq_centralizer`), matching the normalisations on the two sides.

## Main results

* `OddOrder.GroupTheory.card_pFactorPairs_modEq_centralizer` — Navarro, Problem (6.1)
* `OddOrder.GroupTheory.card_pRegular_modEq_centralizer` — `|G⁰| ≡ |C_G(Q)⁰| (mod p)`
-/

namespace OddOrder.GroupTheory

open MulAction

variable {p : ℕ} {G : Type*} [Group G]

/-- The pairs `(x, y)` with `x` a `p`-element, `y` `p`-regular and `x y = g`. -/
abbrev PFactorPairs (p : ℕ) (g : G) : Type _ :=
  {q : G × G // IsPElement p q.1 ∧ IsPRegular p q.2 ∧ q.1 * q.2 = g}

variable {Q : Subgroup G} {g : G}

/-- **`Q` acts on `Ω(g)` by simultaneous conjugation**, provided `g` centralises `Q`. -/
@[reducible] def mulActionPFactorPairs (hg : g ∈ Subgroup.centralizer (Q : Set G)) :
    MulAction ↥Q (PFactorPairs p g) where
  smul u q :=
    ⟨((u : G) * (q : G × G).1 * (u : G)⁻¹, (u : G) * (q : G × G).2 * (u : G)⁻¹),
      q.2.1.conj _, q.2.2.1.conj _, by
        have hprod : (u : G) * (q : G × G).1 * (u : G)⁻¹ * ((u : G) * (q : G × G).2 * (u : G)⁻¹)
            = (u : G) * ((q : G × G).1 * (q : G × G).2) * (u : G)⁻¹ := by group
        rw [hprod, q.2.2.2, (Subgroup.mem_centralizer_iff.mp hg) (u : G) u.2]
        group⟩
  one_smul q := Subtype.ext (Prod.ext
    (by change ((1 : ↥Q) : G) * _ * (((1 : ↥Q) : G))⁻¹ = _; push_cast; group)
    (by change ((1 : ↥Q) : G) * _ * (((1 : ↥Q) : G))⁻¹ = _; push_cast; group))
  mul_smul u v q := Subtype.ext (Prod.ext
    (by change ((u * v : ↥Q) : G) * _ * (((u * v : ↥Q) : G))⁻¹
          = (u : G) * ((v : G) * (q : G × G).1 * (v : G)⁻¹) * (u : G)⁻¹
        push_cast; group)
    (by change ((u * v : ↥Q) : G) * _ * (((u * v : ↥Q) : G))⁻¹
          = (u : G) * ((v : G) * (q : G × G).2 * (v : G)⁻¹) * (u : G)⁻¹
        push_cast; group))

theorem coe_smul_pFactorPairs (hg : g ∈ Subgroup.centralizer (Q : Set G)) (u : ↥Q)
    (q : PFactorPairs p g) :
    letI := mulActionPFactorPairs (p := p) hg
    ((u • q : PFactorPairs p g) : G × G)
      = ((u : G) * (q : G × G).1 * (u : G)⁻¹, (u : G) * (q : G × G).2 * (u : G)⁻¹) := rfl

/-- The fixed points are the pairs whose entries both centralise `Q`. -/
theorem mem_fixedPoints_pFactorPairs_iff (hg : g ∈ Subgroup.centralizer (Q : Set G))
    (q : PFactorPairs p g) :
    letI := mulActionPFactorPairs (p := p) hg
    q ∈ fixedPoints ↥Q (PFactorPairs p g)
      ↔ (q : G × G).1 ∈ Subgroup.centralizer (Q : Set G) ∧
          (q : G × G).2 ∈ Subgroup.centralizer (Q : Set G) := by
  letI := mulActionPFactorPairs (p := p) hg
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    constructor
    · intro u hu
      have hq : u * (q : G × G).1 * u⁻¹ = (q : G × G).1 :=
        congrArg Prod.fst (congrArg Subtype.val (h ⟨u, hu⟩))
      calc u * (q : G × G).1 = u * (q : G × G).1 * u⁻¹ * u := by group
        _ = (q : G × G).1 * u := by rw [hq]
    · intro u hu
      have hq : u * (q : G × G).2 * u⁻¹ = (q : G × G).2 :=
        congrArg Prod.snd (congrArg Subtype.val (h ⟨u, hu⟩))
      calc u * (q : G × G).2 = u * (q : G × G).2 * u⁻¹ * u := by group
        _ = (q : G × G).2 * u := by rw [hq]
  · rintro ⟨h1, h2⟩ u
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change (u : G) * (q : G × G).1 * (u : G)⁻¹ = (q : G × G).1
      rw [h1 (u : G) u.2]
      group
    · change (u : G) * (q : G × G).2 * (u : G)⁻¹ = (q : G × G).2
      rw [h2 (u : G) u.2]
      group

variable (Q g)

/-- **Navarro, Problem (6.1) (Külshammer).**  For `g ∈ C_G(Q)` and `Q` a `p`-subgroup,
`|Ω(g)| ≡ |Ω(g) ∩ (C_G(Q) × C_G(Q))| (mod p)`. -/
theorem card_pFactorPairs_modEq_centralizer [Finite G] (hp : p.Prime) (hQ : IsPGroup p ↥Q)
    (hg : g ∈ Subgroup.centralizer (Q : Set G)) :
    Nat.card (PFactorPairs p g)
      ≡ Nat.card {q : PFactorPairs p g //
          (q : G × G).1 ∈ Subgroup.centralizer (Q : Set G) ∧
            (q : G × G).2 ∈ Subgroup.centralizer (Q : Set G)} [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI := mulActionPFactorPairs (p := p) hg
  have hcard : Nat.card (fixedPoints ↥Q (PFactorPairs p g))
      = Nat.card {q : PFactorPairs p g //
          (q : G × G).1 ∈ Subgroup.centralizer (Q : Set G) ∧
            (q : G × G).2 ∈ Subgroup.centralizer (Q : Set G)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun q => mem_fixedPoints_pFactorPairs_iff hg q)
  rw [← hcard]
  exact hQ.card_modEq_card_fixedPoints _

/-! ### The same count on `G⁰` itself -/

variable {Q}

/-- **`Q` acts on the `p`-regular elements by conjugation.** -/
@[reducible] def mulActionPRegular (p : ℕ) (Q : Subgroup G) :
    MulAction ↥Q {y : G // IsPRegular p y} where
  smul u y := ⟨(u : G) * (y : G) * (u : G)⁻¹, y.2.conj _⟩
  one_smul y := Subtype.ext (by
    change ((1 : ↥Q) : G) * (y : G) * (((1 : ↥Q) : G))⁻¹ = (y : G)
    push_cast
    group)
  mul_smul u v y := Subtype.ext (by
    change ((u * v : ↥Q) : G) * _ * (((u * v : ↥Q) : G))⁻¹
      = (u : G) * ((v : G) * (y : G) * (v : G)⁻¹) * (u : G)⁻¹
    push_cast; group)

/-- The fixed points are the `p`-regular elements of `C_G(Q)`. -/
theorem mem_fixedPoints_pRegular_iff (y : {y : G // IsPRegular p y}) :
    letI := mulActionPRegular p Q
    y ∈ fixedPoints ↥Q {y : G // IsPRegular p y}
      ↔ (y : G) ∈ Subgroup.centralizer (Q : Set G) := by
  letI := mulActionPRegular p Q
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h u hu
    have hy : u * (y : G) * u⁻¹ = (y : G) := congrArg Subtype.val (h ⟨u, hu⟩)
    calc u * (y : G) = u * (y : G) * u⁻¹ * u := by group
      _ = (y : G) * u := by rw [hy]
  · intro h u
    refine Subtype.ext ?_
    change (u : G) * (y : G) * (u : G)⁻¹ = (y : G)
    rw [h (u : G) u.2]
    group

variable (Q)

/-- **`|G⁰| ≡ |C_G(Q)⁰| (mod p)`.**  The `p`-group `Q` acts on the `p`-regular elements by
conjugation and its fixed points are the `p`-regular elements of `C_G(Q)`.  This is the
normalisation matching Navarro, Problem (6.1): both sides of Külshammer's formula are divided by
the number of `p`-regular elements. -/
theorem card_pRegular_modEq_centralizer [Finite G] (hp : p.Prime) (hQ : IsPGroup p ↥Q) :
    Nat.card {y : G // IsPRegular p y}
      ≡ Nat.card {y : {y : G // IsPRegular p y} //
          (y : G) ∈ Subgroup.centralizer (Q : Set G)} [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI := mulActionPRegular p Q
  have hcard : Nat.card (fixedPoints ↥Q {y : G // IsPRegular p y})
      = Nat.card {y : {y : G // IsPRegular p y} //
          (y : G) ∈ Subgroup.centralizer (Q : Set G)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => mem_fixedPoints_pRegular_iff y)
  rw [← hcard]
  exact hQ.card_modEq_card_fixedPoints _

end OddOrder.GroupTheory
