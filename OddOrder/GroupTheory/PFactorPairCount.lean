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
* `OddOrder.GroupTheory.pFactorPairsSubgroupEquiv`, `OddOrder.GroupTheory.pRegularSubgroupEquiv` —
  the same counts taken inside a subgroup
* `OddOrder.GroupTheory.card_pFactorPairsMem_modEq_centralizer`,
  `OddOrder.GroupTheory.card_pRegularMem_modEq_centralizer` — the same two congruences run inside
  an intermediate subgroup `Q C_G(Q) ≤ H`, which is what the third main theorem needs for a
  general `H` rather than only for `H = C_G(Q)`
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

/-! ### Transfer along a subgroup inclusion -/

section Subgroup

variable (p) {H : Subgroup G}

/-- **`Ω_H(g) ≃ Ω_G(g) ∩ (H × H)`**: a factorisation inside `H` is a factorisation in `G` with
both entries in `H`, because orders are unchanged by the inclusion. -/
def pFactorPairsSubgroupEquiv (g : ↥H) :
    PFactorPairs p g
      ≃ {q : PFactorPairs p ((g : G)) // (q : G × G).1 ∈ H ∧ (q : G × G).2 ∈ H} where
  toFun q := ⟨⟨(((q : ↥H × ↥H).1 : G), ((q : ↥H × ↥H).2 : G)),
      isPElement_coe_iff.mpr q.2.1, isPRegular_coe_iff.mpr q.2.2.1,
      congrArg Subtype.val q.2.2.2⟩,
    (q : ↥H × ↥H).1.2, (q : ↥H × ↥H).2.2⟩
  invFun q := ⟨(⟨((q : PFactorPairs p ((g : G))) : G × G).1, q.2.1⟩,
      ⟨((q : PFactorPairs p ((g : G))) : G × G).2, q.2.2⟩),
    (isPElement_coe_iff (H := H)).mp (q : PFactorPairs p ((g : G))).2.1,
    (isPRegular_coe_iff (H := H)).mp (q : PFactorPairs p ((g : G))).2.2.1,
    Subtype.ext (q : PFactorPairs p ((g : G))).2.2.2⟩
  left_inv _ := Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))
  right_inv _ := Subtype.ext (Subtype.ext (Prod.ext rfl rfl))

/-- **`H⁰ ≃ G⁰ ∩ H`**, again because orders are unchanged. -/
def pRegularSubgroupEquiv :
    {y : ↥H // IsPRegular p y} ≃ {y : {y : G // IsPRegular p y} // (y : G) ∈ H} where
  toFun y := ⟨⟨((y : ↥H) : G), isPRegular_coe_iff.mpr y.2⟩, (y : ↥H).2⟩
  invFun y := ⟨⟨((y : {y : G // IsPRegular p y}) : G), y.2⟩,
    (isPRegular_coe_iff (H := H)).mp (y : {y : G // IsPRegular p y}).2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)

end Subgroup

/-! ### The same count taken inside an intermediate subgroup

For `Q C_G(Q) ≤ H` the whole comparison can be run inside `H`: `Q` still acts on the
factorisations with both entries in `H`, and the fixed points are again the pairs in `C_G(Q)`
because `C_G(Q) ≤ H`.  This is what lets Külshammer's route reach the third main theorem for a
general intermediate subgroup, not just for `H = C_G(Q)`. -/

section Intermediate

variable {Q : Subgroup G} {g : G} {H : Subgroup G}

/-- **`Q` acts on the factorisations of `g` with both entries in `H`**, when `Q ≤ H`. -/
@[reducible] def mulActionPFactorPairsMem (hQH : Q ≤ H)
    (hg : g ∈ Subgroup.centralizer (Q : Set G)) :
    MulAction ↥Q {q : PFactorPairs p g // (q : G × G).1 ∈ H ∧ (q : G × G).2 ∈ H} :=
  letI := mulActionPFactorPairs (p := p) hg
  { smul := fun u q => ⟨u • (q : PFactorPairs p g), by
      rw [coe_smul_pFactorPairs]
      exact ⟨H.mul_mem (H.mul_mem (hQH u.2) q.2.1) (H.inv_mem (hQH u.2)),
        H.mul_mem (H.mul_mem (hQH u.2) q.2.2) (H.inv_mem (hQH u.2))⟩⟩
    one_smul := fun q => Subtype.ext (one_smul ↥Q (q : PFactorPairs p g))
    mul_smul := fun u v q => Subtype.ext (mul_smul u v (q : PFactorPairs p g)) }

/-- The fixed points are again the pairs in `C_G(Q)`. -/
theorem mem_fixedPoints_pFactorPairsMem_iff (hQH : Q ≤ H)
    (hg : g ∈ Subgroup.centralizer (Q : Set G))
    (q : {q : PFactorPairs p g // (q : G × G).1 ∈ H ∧ (q : G × G).2 ∈ H}) :
    letI := mulActionPFactorPairsMem (p := p) hQH hg
    q ∈ fixedPoints ↥Q {q : PFactorPairs p g // (q : G × G).1 ∈ H ∧ (q : G × G).2 ∈ H}
      ↔ ((q : PFactorPairs p g) : G × G).1 ∈ Subgroup.centralizer (Q : Set G) ∧
          ((q : PFactorPairs p g) : G × G).2 ∈ Subgroup.centralizer (Q : Set G) := by
  letI := mulActionPFactorPairs (p := p) hg
  letI := mulActionPFactorPairsMem (p := p) hQH hg
  rw [← mem_fixedPoints_pFactorPairs_iff hg]
  exact ⟨fun h u => Subtype.ext_iff.mp (h u), fun h u => Subtype.ext (h u)⟩

/-- **Navarro, Problem (6.1), inside an intermediate subgroup.**  For `Q C_G(Q) ≤ H` and
`g ∈ C_G(Q)`, `|Ω_H(g)| ≡ |Ω_{C_G(Q)}(g)| (mod p)`. -/
theorem card_pFactorPairsMem_modEq_centralizer [Finite G] (hp : p.Prime) (hQ : IsPGroup p ↥Q)
    (hQH : Q ≤ H) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hg : g ∈ Subgroup.centralizer (Q : Set G)) :
    Nat.card {q : PFactorPairs p g // (q : G × G).1 ∈ H ∧ (q : G × G).2 ∈ H}
      ≡ Nat.card {q : PFactorPairs p g //
          (q : G × G).1 ∈ Subgroup.centralizer (Q : Set G) ∧
            (q : G × G).2 ∈ Subgroup.centralizer (Q : Set G)} [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI := mulActionPFactorPairsMem (p := p) hQH hg
  have hcard : Nat.card (fixedPoints ↥Q
        {q : PFactorPairs p g // (q : G × G).1 ∈ H ∧ (q : G × G).2 ∈ H})
      = Nat.card {q : PFactorPairs p g //
          (q : G × G).1 ∈ Subgroup.centralizer (Q : Set G) ∧
            (q : G × G).2 ∈ Subgroup.centralizer (Q : Set G)} :=
    Nat.card_congr
      { toFun := fun z => ⟨(z.1 : PFactorPairs p g),
          (mem_fixedPoints_pFactorPairsMem_iff (p := p) hQH hg z.1).mp z.2⟩
        invFun := fun q => ⟨⟨(q : PFactorPairs p g), hCH q.2.1, hCH q.2.2⟩,
          (mem_fixedPoints_pFactorPairsMem_iff (p := p) hQH hg _).mpr q.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← hcard]
  exact hQ.card_modEq_card_fixedPoints _

/-- **`Q` acts on the `p`-regular elements of `H`**, when `Q ≤ H`. -/
@[reducible] def mulActionPRegularMem (p : ℕ) (Q H : Subgroup G) (hQH : Q ≤ H) :
    MulAction ↥Q {y : {y : G // IsPRegular p y} // (y : G) ∈ H} :=
  letI := mulActionPRegular p Q
  { smul := fun u y => ⟨u • (y : {y : G // IsPRegular p y}),
      H.mul_mem (H.mul_mem (hQH u.2) y.2) (H.inv_mem (hQH u.2))⟩
    one_smul := fun y => Subtype.ext (one_smul ↥Q (y : {y : G // IsPRegular p y}))
    mul_smul := fun u v y => Subtype.ext (mul_smul u v (y : {y : G // IsPRegular p y})) }

/-- **`|H⁰| ≡ |C_G(Q)⁰| (mod p)`** for `Q C_G(Q) ≤ H`: the normalisation matching
`card_pFactorPairsMem_modEq_centralizer`. -/
theorem card_pRegularMem_modEq_centralizer [Finite G] (hp : p.Prime) (hQ : IsPGroup p ↥Q)
    (hQH : Q ≤ H) (hCH : Subgroup.centralizer (Q : Set G) ≤ H) :
    Nat.card {y : {y : G // IsPRegular p y} // (y : G) ∈ H}
      ≡ Nat.card {y : {y : G // IsPRegular p y} //
          (y : G) ∈ Subgroup.centralizer (Q : Set G)} [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI := mulActionPRegular p Q
  letI := mulActionPRegularMem p Q H hQH
  have hfix : ∀ y : {y : {y : G // IsPRegular p y} // (y : G) ∈ H},
      y ∈ fixedPoints ↥Q {y : {y : G // IsPRegular p y} // (y : G) ∈ H}
        ↔ ((y : {y : G // IsPRegular p y}) : G) ∈ Subgroup.centralizer (Q : Set G) := by
    intro y
    rw [← mem_fixedPoints_pRegular_iff (p := p) (Q := Q) (y : {y : G // IsPRegular p y})]
    exact ⟨fun h u => Subtype.ext_iff.mp (h u), fun h u => Subtype.ext (h u)⟩
  have hcard : Nat.card (fixedPoints ↥Q {y : {y : G // IsPRegular p y} // (y : G) ∈ H})
      = Nat.card {y : {y : G // IsPRegular p y} //
          (y : G) ∈ Subgroup.centralizer (Q : Set G)} :=
    Nat.card_congr
      { toFun := fun z => ⟨(z.1 : {y : G // IsPRegular p y}), (hfix z.1).mp z.2⟩
        invFun := fun y => ⟨⟨(y : {y : G // IsPRegular p y}), hCH y.2⟩, (hfix _).mpr y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← hcard]
  exact hQ.card_modEq_card_fixedPoints _

end Intermediate

end OddOrder.GroupTheory
