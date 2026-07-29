/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.SquareRootFibres
import OddOrder.Peterfalvi.Appendices.Suzuki.ActualCenter
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.TwoSummandSplit
import OddOrder.BG.Ch1_Preliminary.OperatorMaschke

/-!
# The two `K`-subgroups of `S` of order `q²`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III, §1, p. 117 (case (3)) and Appendix III, Higman
theorem (d), p. 141.

Case (3) of the Ch. III §1 Proposition works with `K`-subgroups `X`, `Y` of `S`
of order `q²`.  Higman's clause (d) produces them: for a Suzuki `2`-group of
order `q³`, the central quotient `S ⧸ Z(S)` is the direct sum of two invariant
subgroups of order `q` (`center_payload_of_card_eq_cube`), and their preimages
in `S` are `K`-subgroups of order `q²`.

That statement lives in the quotient `↥Q ⧸ Z(↥Q)` with the `IsAInvariant`
vocabulary of Isaacs Ch. 3, while the Proposition's argument is carried out in
`G` with plain subgroups.  This file provides the bridge — `liftCentralQuotient`
and its properties — and packages the resulting pair.

## Main results

* `liftCentralQuotient` — the subgroup of `G` between `Q₀` and `Q` attached to a
  subgroup of `↥Q ⧸ Z(↥Q)`, with its order, its `K`-invariance and injectivity.
* `exists_two_kSubgroups_of_card_cube` — **Higman (d) in `G`-language**: if `Q`
  is a Suzuki `2`-group with `|Q| = |Q₀|³`, there are two distinct `K`-invariant
  subgroups `X ≠ Y` with `Q₀ ≤ X, Y ≤ Q` and `|X| = |Y| = |Q₀|²`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Higman.Suzuki2Groups

universe uG uΩ

/-! ## Conjugating a `K`-subgroup by `V` -/

theorem mem_map_conj {G : Type uG} [Group G] {g y : G} {X : Subgroup G} :
    y ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : g⁻¹ * ((MulAut.conj g).toMonoidHom x) * g = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [hx']
  · intro h
    refine ⟨g⁻¹ * y * g, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_conj_injective {G : Type uG} [Group G] (g : G) :
    Function.Injective fun X : Subgroup G => X.map (MulAut.conj g).toMonoidHom :=
  Subgroup.map_injective (MulAut.conj g).injective

namespace Hypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## Lifting subgroups of `Q ⧸ Z(Q)` to `G` -/

/-- The subgroup of `G` attached to a subgroup `U` of the central quotient
`↥Q ⧸ Z(↥Q)`: pull back to `↥Q` and push forward to `G`.  It lies between
`Z(Q)` and `Q`. -/
def liftCentralQuotient (U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)) :
    Subgroup G :=
  (U.comap (QuotientGroup.mk' (Subgroup.center ↥hyp.Q))).map hyp.Q.subtype

variable {hyp}

theorem mem_liftCentralQuotient_iff
    {U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)} {x : G} :
    x ∈ hyp.liftCentralQuotient U ↔
      ∃ hx : x ∈ hyp.Q,
        QuotientGroup.mk' (Subgroup.center ↥hyp.Q) ⟨x, hx⟩ ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem liftCentralQuotient_le_Q
    (U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)) :
    hyp.liftCentralQuotient U ≤ hyp.Q := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- Every lift contains `Q₀`, once the center of `Q` has been identified with
`Q₀`. -/
theorem Q0_le_liftCentralQuotient
    (hZ : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)) :
    hyp.Q0 ≤ hyp.liftCentralQuotient U := by
  intro c hc
  refine mem_liftCentralQuotient_iff.mpr ⟨hyp.Q0_le_Q hc, ?_⟩
  have hmem : (⟨c, hyp.Q0_le_Q hc⟩ : ↥hyp.Q) ∈ Subgroup.center ↥hyp.Q := by
    rw [hZ]
    exact Subgroup.mem_subgroupOf.mpr hc
  have h1 : QuotientGroup.mk' (Subgroup.center ↥hyp.Q)
      (⟨c, hyp.Q0_le_Q hc⟩ : ↥hyp.Q) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hmem
  rw [h1]
  exact U.one_mem

/-- The lift multiplies the order by `|Z(Q)|`. -/
theorem card_liftCentralQuotient
    (U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)) :
    Nat.card ↥(hyp.liftCentralQuotient U)
      = Nat.card ↥U * Nat.card ↥(Subgroup.center ↥hyp.Q) := by
  classical
  set Z : Subgroup ↥hyp.Q := Subgroup.center ↥hyp.Q with hZdef
  set π := QuotientGroup.mk' Z with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hmapcard : Nat.card ↥(hyp.liftCentralQuotient U)
      = Nat.card ↥(U.comap π) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective (U.comap π) hyp.Q.subtype
      (Subgroup.subtype_injective _)).toEquiv).symm
  have hindex : (U.comap π).index = U.index :=
    U.index_comap_of_surjective hπsurj
  have h1 : Nat.card ↥(U.comap π) * U.index = Nat.card ↥hyp.Q := by
    rw [← hindex]; exact Subgroup.card_mul_index _
  have h2 : Nat.card ↥U * U.index = Nat.card (↥hyp.Q ⧸ Z) :=
    Subgroup.card_mul_index _
  have h3 : Nat.card (↥hyp.Q ⧸ Z) * Nat.card ↥Z = Nat.card ↥hyp.Q :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
  have hpos : 0 < U.index := Nat.pos_of_ne_zero (by
    intro h
    rw [h, mul_zero] at h2
    exact (Nat.card_pos (α := ↥hyp.Q ⧸ Z)).ne h2)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [hmapcard, h1, ← h3, ← h2]
  ring

/-- Distinct subgroups of the central quotient have distinct lifts. -/
theorem liftCentralQuotient_injective :
    Function.Injective hyp.liftCentralQuotient := by
  intro U₁ U₂ h
  have h1 : U₁.comap (QuotientGroup.mk' (Subgroup.center ↥hyp.Q))
      = U₂.comap (QuotientGroup.mk' (Subgroup.center ↥hyp.Q)) :=
    Subgroup.map_injective (Subgroup.subtype_injective hyp.Q) h
  exact Subgroup.comap_injective (QuotientGroup.mk'_surjective _) h1

/-- A `K`-invariant subgroup of the central quotient has `K`-invariant lift,
in the elementwise form the Proposition uses. -/
theorem kInvariant_liftCentralQuotient
    {U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)}
    (hUinv : IsAInvariant
      (IsAInvariant.quotientMulAutHom
        (IsAInvariant.of_characteristic hyp.actualKActor.subtype)) U) :
    ∀ k ∈ hyp.K, ∀ y ∈ hyp.liftCentralQuotient U,
      k * y * k⁻¹ ∈ hyp.liftCentralQuotient U := by
  intro k hk y hy
  obtain ⟨hyQ, hyU⟩ := mem_liftCentralQuotient_iff.mp hy
  have hkH : k ∈ hyp.H := hyp.D_le_H (hyp.K_le_D hk)
  have hconjQ : k * y * k⁻¹ ∈ hyp.Q := hyp.Q_normal_in_H k hkH y hyQ
  refine mem_liftCentralQuotient_iff.mpr ⟨hconjQ, ?_⟩
  set a : ↥hyp.actualKActor := ⟨hyp.conjQByK ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩⟩ with hadef
  have hval : (hyp.actualKActor.subtype a) (⟨y, hyQ⟩ : ↥hyp.Q)
      = (⟨k * y * k⁻¹, hconjQ⟩ : ↥hyp.Q) := rfl
  have := hUinv.smul_mem a hyU
  rwa [IsAInvariant.quotientMulAutHom_apply_mk', hval] at this

variable (hyp)

/-- **The `K`-subgroups of `S` of order `q²`** — the objects case (3) of the
Ch. III §1 Proposition works with (p. 117). -/
def IsKSubgroupSquare (X : Subgroup G) : Prop :=
  X ≤ hyp.Q ∧ hyp.Q0 ≤ X ∧ (∀ k ∈ hyp.K, ∀ y ∈ X, k * y * k⁻¹ ∈ X) ∧
    Nat.card ↥X = Nat.card ↥hyp.Q0 ^ 2

variable {hyp}

/-- **`V` permutes the `K`-subgroups of `S` of order `q²`.**

`V ≤ D` normalizes `Q` and `Q₀`, and normalizes `K` because `K ⊴ D`
(Ch. I §2 Proposition 2); conjugation preserves cardinality. -/
theorem isKSubgroupSquare_map_conj {g : G} (hg : g ∈ hyp.V) {X : Subgroup G}
    (hX : hyp.IsKSubgroupSquare X) :
    hyp.IsKSubgroupSquare (X.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hXQ, hQ0X, hXinv, hXcard⟩ := hX
  have hgD : g ∈ hyp.D := hyp.V_le_D hg
  have hgiD : g⁻¹ ∈ hyp.D := hyp.D.inv_mem hgD
  have hgH : g ∈ hyp.H := hyp.D_le_H hgD
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro y hy
    have := hXQ (mem_map_conj.mp hy)
    have hcj := hyp.Q_normal_in_H g hgH _ this
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y from by group] at hcj
  · intro c hc
    refine mem_map_conj.mpr (hQ0X ?_)
    have := hyp.conj_mem_Q0_of_mem_D hgiD hc
    rwa [show g⁻¹ * c * g⁻¹⁻¹ = g⁻¹ * c * g from by group] at this
  · intro k hk y hy
    refine mem_map_conj.mpr ?_
    have hkK : g⁻¹ * k * g ∈ hyp.K := by
      have hmem : (⟨g⁻¹, hgiD⟩ * ⟨k, hyp.K_le_D hk⟩ * ⟨g⁻¹, hgiD⟩⁻¹ : ↥hyp.D)
          ∈ hyp.K.subgroupOf hyp.D :=
        hyp.K_normal.conj_mem _ (Subgroup.mem_subgroupOf.mpr hk) ⟨g⁻¹, hgiD⟩
      have := Subgroup.mem_subgroupOf.mp hmem
      rwa [show ((⟨g⁻¹, hgiD⟩ * ⟨k, hyp.K_le_D hk⟩ * ⟨g⁻¹, hgiD⟩⁻¹ : ↥hyp.D) : G)
          = g⁻¹ * k * g from by push_cast; group] at this
    have hy' := hXinv _ hkK _ (mem_map_conj.mp hy)
    rwa [show (g⁻¹ * k * g) * (g⁻¹ * y * g) * (g⁻¹ * k * g)⁻¹
        = g⁻¹ * (k * y * k⁻¹) * g from by group] at hy'
  · rw [← hXcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective X _
      (MulAut.conj g).injective).toEquiv).symm

/-- **"`P` therefore normalizes `X` and `Y`"** (p. 117, case (3)) when they are
the only two `K`-subgroups of `S` of order `q²`.

`P` has odd order, so it cannot swap a two-element set: if `g` interchanged `X`
and `Y`, then the square root `h` of `g` inside `⟨g⟩` — available because `p` is
odd — would satisfy `X^{h²} = X` either way, contradicting `X^g = Y ≠ X`. -/
theorem map_conj_eq_self_of_unique {g : G} (hg : g ∈ hyp.V) {p : ℕ}
    (hodd : Odd p) (hgp : g ^ p = 1)
    {X Y : Subgroup G} (hX : hyp.IsKSubgroupSquare X) (hne : X ≠ Y)
    (huniq : ∀ Z : Subgroup G, hyp.IsKSubgroupSquare Z → Z = X ∨ Z = Y) :
    X.map (MulAut.conj g).toMonoidHom = X := by
  classical
  -- `p` is odd, so `g` is a square inside `⟨g⟩`
  obtain ⟨j, hj⟩ := hodd
  set h : G := g ^ (j + 1) with hhdef
  have hhV : h ∈ hyp.V := hyp.V.pow_mem hg _
  have hsq : h * h = g := by
    rw [hhdef, ← pow_add, show j + 1 + (j + 1) = p + 1 from by omega, pow_succ,
      hgp, one_mul]
  have hcomp : ∀ Z : Subgroup G,
      (Z.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h).toMonoidHom
        = Z.map (MulAut.conj g).toMonoidHom := by
    intro Z
    ext y
    rw [mem_map_conj, mem_map_conj, mem_map_conj]
    rw [show h⁻¹ * (h⁻¹ * y * h) * h = (h * h)⁻¹ * y * (h * h) from by group, hsq]
  by_contra hXg
  have hXgY : X.map (MulAut.conj g).toMonoidHom = Y :=
    (huniq _ (isKSubgroupSquare_map_conj hg hX)).resolve_left hXg
  have hXh := huniq _ (isKSubgroupSquare_map_conj hhV hX)
  rcases hXh with hXhX | hXhY
  · -- `h` fixes `X`, so `g = h²` does too
    have : X.map (MulAut.conj g).toMonoidHom = X := by
      rw [← hcomp, hXhX, hXhX]
    exact hXg this
  · -- `h` sends `X` to `Y`; then `Y^h = X` by injectivity, so `g = h²` fixes `X`
    have hYh : Y.map (MulAut.conj h).toMonoidHom = X := by
      rcases huniq _ (isKSubgroupSquare_map_conj hhV
        (hXhY ▸ isKSubgroupSquare_map_conj hhV hX)) with hh | hh
      · exact hh
      · exact absurd (map_conj_injective h (hXhY.trans hh.symm)) hne
    have : X.map (MulAut.conj g).toMonoidHom = X := by
      rw [← hcomp, hXhY, hYh]
    exact hXg this

/-- **"`P` therefore normalizes `X` and `Y`"** (p. 117, case (3)), elementwise,
for a subgroup `P ≤ V` of prime order: `p` is odd (`prime_ne_two_of_le_V`), so
each of its elements fixes both members of a two-element set of `K`-subgroups. -/
theorem conj_mem_of_unique_of_le_V {P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hPcard : Nat.card ↥P = p) (hPV : P ≤ hyp.V)
    {X Y : Subgroup G} (hX : hyp.IsKSubgroupSquare X) (hne : X ≠ Y)
    (huniq : ∀ Z : Subgroup G, hyp.IsKSubgroupSquare Z → Z = X ∨ Z = Y) :
    ∀ g ∈ P, ∀ y ∈ X, g * y * g⁻¹ ∈ X := by
  intro g hg y hy
  have hgp : g ^ p = 1 := by
    have hone := pow_card_eq_one' (G := ↥P) (x := ⟨g, hg⟩)
    rw [hPcard] at hone
    simpa using congrArg (Subtype.val (p := fun z => z ∈ P)) hone
  have hodd : Odd p := hp.odd_of_ne_two (hyp.prime_ne_two_of_le_V hPcard hPV)
  have hfix := map_conj_eq_self_of_unique (hPV hg) hodd hgp hX hne huniq
  have hmem : g * y * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := by
    refine mem_map_conj.mpr ?_
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y from by group]
  rwa [hfix] at hmem

/-- **`Ω₁(Q) = Q₀`, as a cardinality**: the elements of `Q` of order dividing `2`
are exactly `Q₀` (`mem_Q0_of_mem_Q_of_sq_eq_one`). -/
theorem natCard_sq_eq_one_eq_natCard_Q0 {G : Type uG} {Ω : Type uΩ} [Group G]
    [MulAction G Ω] [Finite G] (hyp : Hypothesis G Ω) :
    Nat.card {x : ↥hyp.Q // x ^ 2 = 1} = Nat.card ↥hyp.Q0 := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨((x : ↥hyp.Q) : G),
        hyp.mem_Q0_of_mem_Q_of_sq_eq_one (x : ↥hyp.Q).2 ?_⟩
      invFun := fun c => ⟨⟨(c : G), hyp.Q0_le_Q c.2⟩, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · simpa using congrArg (Subtype.val (p := fun z => z ∈ hyp.Q)) x.2
  · exact Subtype.ext (by simpa using hyp.sq_eq_one_of_mem_Q0 c.2)

/-- **The order of `S`** (Peterfalvi Part II, Ch. III §1, p. 117): a Suzuki
`2`-group `Q` has order `|Q₀|²` (the book's case (2)) or `|Q₀|³` (case (3)).

Higman's dichotomy `natCard_eq_sq_or_cube_of_isSuzuki2Group` phrased with
`Ω₁(Q) = Q₀`. -/
theorem natCard_Q_eq_sq_or_cube {G : Type uG} {Ω : Type uΩ} [Group G]
    [MulAction G Ω] [Finite G] (hyp : Hypothesis G Ω)
    (hQsuz : IsSuzuki2Group ↥hyp.Q) :
    Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2 ∨
      Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 3 := by
  have h := natCard_eq_sq_or_cube_of_isSuzuki2Group hQsuz
  rwa [natCard_sq_eq_one_eq_natCard_Q0] at h

/-- Invariance under two operator subgroups gives invariance under their join. -/
theorem conj_mem_sup {G : Type uG} [Group G] {A B N : Subgroup G}
    (hA : ∀ a ∈ A, ∀ y ∈ N, a * y * a⁻¹ ∈ N)
    (hB : ∀ b ∈ B, ∀ y ∈ N, b * y * b⁻¹ ∈ N) :
    ∀ c ∈ A ⊔ B, ∀ y ∈ N, c * y * c⁻¹ ∈ N := by
  have hnorm : ∀ (C : Subgroup G),
      (∀ a ∈ C, ∀ y ∈ N, a * y * a⁻¹ ∈ N) → C ≤ Subgroup.normalizer N := by
    intro C hC a ha
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hC a ha n hn, fun hn => ?_⟩
    have h := hC a⁻¹ (C.inv_mem ha) _ hn
    rwa [show a⁻¹ * (a * n * a⁻¹) * a⁻¹⁻¹ = n from by group] at h
  intro c hc y hy
  exact (Subgroup.mem_normalizer_iff.mp
    (sup_le (hnorm A hA) (hnorm B hB) hc) y).mp hy

/-! ## Conjugation by a subgroup of `H`, and the Maschke complement -/

/-- Conjugation on `Q` by a subgroup `A` of `H`; `Q ⊴ H`.  Generalizes
`conjQByK` and `conjQByW` to an arbitrary operator subgroup. -/
def conjQBy {A : Subgroup G} (hAH : A ≤ hyp.H) : ↥A →* MulAut ↥hyp.Q where
  toFun a :=
    { toFun := fun x => ⟨(a : G) * x * (a : G)⁻¹,
        hyp.Q_normal_in_H a (hAH a.2) x x.2⟩
      invFun := fun x => ⟨(a : G)⁻¹ * x * (a : G), by
        simpa using hyp.Q_normal_in_H (a : G)⁻¹ (inv_mem (hAH a.2)) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by
        change (a : G) * ((x : G) * (y : G)) * (a : G)⁻¹ =
          ((a : G) * x * (a : G)⁻¹) * ((a : G) * y * (a : G)⁻¹)
        group) }
  map_one' := by
    ext x
    change ((1 : ↥A) : G) * (x : G) * ((1 : ↥A) : G)⁻¹ = (x : G)
    simp
  map_mul' a b := by
    ext x
    change (((a : G) * (b : G)) * (x : G) * (((a : G) * (b : G))⁻¹)) =
      (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹
    group

theorem conjQBy_apply {A : Subgroup G} (hAH : A ≤ hyp.H) (a : ↥A) (x : ↥hyp.Q) :
    ((hyp.conjQBy hAH a x : ↥hyp.Q) : G) = (a : G) * (x : G) * (a : G)⁻¹ := rfl

/-- The induced action of `A` on the central quotient of `Q`. -/
noncomputable def conjQuotientBy {A : Subgroup G} (hAH : A ≤ hyp.H) :
    ↥A →* MulAut (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q) :=
  IsAInvariant.quotientMulAutHom
    (IsAInvariant.of_characteristic (hyp.conjQBy hAH))

/-- The lift of an `A`-invariant subgroup of the central quotient is invariant
under conjugation by `A`, elementwise. -/
theorem conj_mem_liftCentralQuotient {A : Subgroup G} (hAH : A ≤ hyp.H)
    {U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)}
    (hUinv : IsAInvariant (hyp.conjQuotientBy hAH) U) :
    ∀ a ∈ A, ∀ y ∈ hyp.liftCentralQuotient U,
      a * y * a⁻¹ ∈ hyp.liftCentralQuotient U := by
  intro a ha y hy
  obtain ⟨hyQ, hyU⟩ := mem_liftCentralQuotient_iff.mp hy
  have hconjQ : a * y * a⁻¹ ∈ hyp.Q := hyp.Q_normal_in_H a (hAH ha) y hyQ
  refine mem_liftCentralQuotient_iff.mpr ⟨hconjQ, ?_⟩
  have hval : (hyp.conjQBy hAH ⟨a, ha⟩) (⟨y, hyQ⟩ : ↥hyp.Q)
      = (⟨a * y * a⁻¹, hconjQ⟩ : ↥hyp.Q) := rfl
  have hmem := hUinv.smul_mem (⟨a, ha⟩ : ↥A) hyU
  rwa [conjQuotientBy, IsAInvariant.quotientMulAutHom_apply_mk', hval] at hmem

/-- The image in the central quotient of a subgroup between `Q₀` and `Q` that is
invariant under conjugation by `A` is `A`-invariant. -/
theorem aInvariant_map_of_conj_mem {A : Subgroup G} (hAH : A ≤ hyp.H)
    {N : Subgroup G} (hNinv : ∀ a ∈ A, ∀ y ∈ N, a * y * a⁻¹ ∈ N) :
    IsAInvariant (hyp.conjQuotientBy hAH)
      ((N.subgroupOf hyp.Q).map
        (QuotientGroup.mk' (Subgroup.center ↥hyp.Q))) := by
  rw [isAInvariant_iff_smul_mem]
  rintro a x ⟨y, hy, rfl⟩
  refine ⟨(hyp.conjQBy hAH a) y, ?_, rfl⟩
  refine Subgroup.mem_subgroupOf.mpr ?_
  have hyN : (y : G) ∈ N := Subgroup.mem_subgroupOf.mp hy
  rw [conjQBy_apply]
  exact hNinv a a.2 _ hyN

/-- **Operator Maschke for `S ⧸ Q₀`** (BG Ch. 1,
`exists_aInvariant_complement_of_isElementaryAbelian`).

A subgroup `N` with `Q₀ ≤ N ≤ S` of order `q²`, invariant under conjugation by
an operator subgroup `A ≤ D` of odd order, has a partner `N'` of the same
description with `N ⊓ N' = Q₀`.  This replaces the book's count of the
`K`-subgroups of `S` of order `q²` (p. 117, case (3)): applied with
`A = K ⊔ P`, one such subgroup produces a second one that `P` also
normalizes. -/
theorem exists_kSubgroupSquare_complement {A : Subgroup G} (hAD : A ≤ hyp.D)
    (hQ2 : IsPGroup 2 ↥hyp.Q)
    (hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hEA : OddOrder.GroupTheory.IsElementaryAbelian 2
      (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q))
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 3)
    {N : Subgroup G} (hNQ : N ≤ hyp.Q) (hQ0N : hyp.Q0 ≤ N)
    (hNinv : ∀ a ∈ A, ∀ y ∈ N, a * y * a⁻¹ ∈ N)
    (hNcard : Nat.card ↥N = Nat.card ↥hyp.Q0 ^ 2) :
    ∃ N' : Subgroup G, N' ≤ hyp.Q ∧ hyp.Q0 ≤ N' ∧
      (∀ a ∈ A, ∀ y ∈ N', a * y * a⁻¹ ∈ N') ∧
      Nat.card ↥N' = Nat.card ↥hyp.Q0 ^ 2 ∧ N ≠ N' := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAH : A ≤ hyp.H := hAD.trans hyp.D_le_H
  set U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q) :=
    (N.subgroupOf hyp.Q).map
      (QuotientGroup.mk' (Subgroup.center ↥hyp.Q)) with hUdef
  -- cardinalities
  have hZcard : Nat.card ↥(Subgroup.center ↥hyp.Q) = Nat.card ↥hyp.Q0 := by
    rw [hZQ0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv]
  have hQ0two : 2 ≤ Nat.card ↥hyp.Q0 := hyp.two_le_card_Q0
  obtain ⟨n, hn⟩ := (hQ2.to_le hyp.Q0_le_Q).exists_card_eq
  have hn1 : n ≠ 0 := by
    intro h
    rw [h, pow_zero] at hn
    omega
  have hEcard : Nat.card (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)
      = Nat.card ↥hyp.Q0 ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥hyp.Q)
    rw [hQcard, hZcard] at h
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥hyp.Q0)) ?_
    rw [← h, pow_succ]
  have hCle : Subgroup.center ↥hyp.Q ≤ N.subgroupOf hyp.Q := by
    intro x hx
    rw [hZQ0] at hx
    exact Subgroup.mem_subgroupOf.mpr (hQ0N (Subgroup.mem_subgroupOf.mp hx))
  have hcomap : U.comap (QuotientGroup.mk' (Subgroup.center ↥hyp.Q))
      = N.subgroupOf hyp.Q := by
    rw [hUdef, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hCle]
  have hliftU : hyp.liftCentralQuotient U = N := by
    rw [liftCentralQuotient, hcomap, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hNQ]
  have hUcard : Nat.card ↥U = Nat.card ↥hyp.Q0 := by
    have h := card_liftCentralQuotient (hyp := hyp) U
    rw [hliftU, hNcard, hZcard, sq] at h
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm
  -- coprimality: `|A|` divides the odd `|D|`, and the quotient is a `2`-group
  have hcop : Nat.Coprime (Nat.card ↥A)
      (Nat.card (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q)) := by
    have hAodd : ¬ 2 ∣ Nat.card ↥A := by
      intro hdvd
      have hdvdD : (2 : ℕ) ∣ Nat.card ↥hyp.D :=
        hdvd.trans (Subgroup.card_dvd_of_le hAD)
      obtain ⟨j, hj⟩ := hyp.D_odd
      obtain ⟨i, hi⟩ := hdvdD
      omega
    have h2 : Nat.card (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q) = 2 ^ (2 * n) := by
      rw [hEcard, hn, ← pow_mul, mul_comm]
    rw [h2]
    exact Nat.Coprime.pow_right _
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hAodd).symm
  have hpE : 2 ∣ Nat.card (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q) := by
    rw [hEcard, hn, ← pow_mul]
    exact dvd_pow_self 2 (by omega)
  -- operator Maschke
  obtain ⟨W, hWinv, hinf, hsup⟩ :=
    OddOrder.BG.Ch1_Preliminary.exists_aInvariant_complement_of_isElementaryAbelian
      hpE (φ := hyp.conjQuotientBy hAH) hcop hEA
      (aInvariant_map_of_conj_mem hAH hNinv)
  have hinf' : U ⊓ W = ⊥ := hinf
  have hsup' : U ⊔ W = ⊤ := hsup
  -- the complement has order `|Q₀|`
  haveI hUnormal : U.Normal :=
    ⟨fun x hx g => by
      rw [hEA.comm g x, mul_assoc, mul_inv_cancel, mul_one]; exact hx⟩
  have hcompl : IsCompl U W := ⟨disjoint_iff.mpr hinf', codisjoint_iff.mpr hsup'⟩
  have hquot := Suzuki2Groups.card_quotient_of_isCompl hcompl
  have hWcard : Nat.card ↥W = Nat.card ↥hyp.Q0 := by
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup U
    rw [hquot, hUcard, hEcard, sq] at hq
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos hq).symm
  refine ⟨hyp.liftCentralQuotient W, liftCentralQuotient_le_Q _,
    Q0_le_liftCentralQuotient hZQ0 _, conj_mem_liftCentralQuotient hAH hWinv,
    by rw [card_liftCentralQuotient, hWcard, hZcard, sq], ?_⟩
  intro heq
  have hUW : U = W := liftCentralQuotient_injective (hliftU.trans heq)
  have hbot : U = ⊥ := by
    have h := hinf'
    rw [← hUW, inf_idem] at h
    exact h
  rw [hbot, Subgroup.card_bot] at hUcard
  omega

/-! ## Higman clause (d) in `G`-language -/

/-- Every `K`-subgroup of `S` of order `q²` comes from a `K`-invariant subgroup
of order `q` of the central quotient — the converse direction of the bridge. -/
theorem exists_eq_liftCentralQuotient_of_isKSubgroupSquare
    (hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {Z : Subgroup G} (hZ : hyp.IsKSubgroupSquare Z) :
    ∃ U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q),
      IsAInvariant (IsAInvariant.quotientMulAutHom
        (IsAInvariant.of_characteristic hyp.actualKActor.subtype)) U ∧
      Nat.card ↥U = Nat.card ↥hyp.Q0 ∧
      hyp.liftCentralQuotient U = Z := by
  classical
  obtain ⟨hZQ, hQ0Z, hZinv, hZcard⟩ := hZ
  have hCle : Subgroup.center ↥hyp.Q ≤ Z.subgroupOf hyp.Q := by
    intro x hx
    rw [hZQ0] at hx
    exact Subgroup.mem_subgroupOf.mpr (hQ0Z (Subgroup.mem_subgroupOf.mp hx))
  refine ⟨(Z.subgroupOf hyp.Q).map
    (QuotientGroup.mk' (Subgroup.center ↥hyp.Q)), ?_, ?_, ?_⟩
  · -- invariance
    rw [isAInvariant_iff_smul_mem]
    rintro a x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨⟨k, hk⟩, hkeq⟩ := a.2
    have hsub : hyp.actualKActor.subtype a = hyp.conjQByK ⟨k, hk⟩ := hkeq.symm
    refine ⟨(hyp.actualKActor.subtype a) y, ?_, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hyZ : (y : G) ∈ Z := Subgroup.mem_subgroupOf.mp hy
    have hval : (((hyp.actualKActor.subtype a) y : ↥hyp.Q) : G)
        = k * (y : G) * k⁻¹ := by rw [hsub]; rfl
    rw [hval]
    exact hZinv k hk _ hyZ
  · -- cardinality
    have hcomap : ((Z.subgroupOf hyp.Q).map
        (QuotientGroup.mk' (Subgroup.center ↥hyp.Q))).comap
        (QuotientGroup.mk' (Subgroup.center ↥hyp.Q)) = Z.subgroupOf hyp.Q := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hCle]
    have hlift : hyp.liftCentralQuotient ((Z.subgroupOf hyp.Q).map
        (QuotientGroup.mk' (Subgroup.center ↥hyp.Q))) = Z := by
      rw [liftCentralQuotient, hcomap, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hZQ]
    have hZcentre : Nat.card ↥(Subgroup.center ↥hyp.Q) = Nat.card ↥hyp.Q0 := by
      rw [hZQ0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv]
    have h := card_liftCentralQuotient (hyp := hyp) ((Z.subgroupOf hyp.Q).map
      (QuotientGroup.mk' (Subgroup.center ↥hyp.Q)))
    rw [hlift, hZcard, hZcentre, sq] at h
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm
  · -- the lift is `Z` again
    have hcomap : ((Z.subgroupOf hyp.Q).map
        (QuotientGroup.mk' (Subgroup.center ↥hyp.Q))).comap
        (QuotientGroup.mk' (Subgroup.center ↥hyp.Q)) = Z.subgroupOf hyp.Q := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hCle]
    rw [liftCentralQuotient, hcomap, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hZQ]

/-- **Types C and D: there are exactly two `K`-subgroups of `S` of order `q²`**
(Peterfalvi Part II, Ch. III §1, p. 117: "It follows that `X` and `Y` are the
only `𝐅₂[K]`-submodules of order `q` in `S/Q₀`").

A third `K`-invariant subgroup of order `q` in `S ⧸ Z(S)` would make the two
summands of Higman's split `K`-equivariantly isomorphic
(`nonempty_kEquivariantMulEquiv_of_third_invariant`), and Appendix III,
Theorem (e) then says `S` is of type B
(`isTypeB_of_isomorphicOrderQModuleSplit_of_card_eq_cube`). -/
theorem exists_two_kSubgroups_unique_of_card_cube
    (hQsuz : IsSuzuki2Group ↥hyp.Q) {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 3)
    (hnotB : ¬ Suzuki2Groups.IsTypeB.{uG, 0} ↥hyp.Q) :
    ∃ X Y : Subgroup G, hyp.IsKSubgroupSquare X ∧ hyp.IsKSubgroupSquare Y ∧
      X ≠ Y ∧ ∀ Z : Subgroup G, hyp.IsKSubgroupSquare Z → Z = X ∨ Z = Y := by
  classical
  have hKcyc : IsCyclic ↥hyp.actualKActor := hyp.actualKActor_isCyclic
  have hreg : ActsRegularlyOnInvolutions hyp.actualKActor :=
    hyp.actualKActor_actsRegularlyOnInvolutions
  have hKKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1 := by
    have h1 : Nat.card ↥hyp.actualKActor = Nat.card ↥hyp.K :=
      Nat.card_congr (MonoidHom.ofInjective hyp.conjQByK_injective).toEquiv.symm
    rw [h1, hyp.card_K_eq_card_Q0_sub_one, hQ0card]
  have hcard : Nat.card ↥hyp.Q = (2 ^ m) ^ 3 := by rw [hcardQ, hQ0card]
  obtain ⟨-, hZsq, ⟨csplit⟩⟩ :=
    center_payload_of_card_eq_cube hQsuz hKcyc hreg hm hKKcard hcard
  have hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q :=
    hyp.center_Q_eq_Q0_subgroupOf_of_sq_eq_one hZsq
  have hZcard : Nat.card ↥(Subgroup.center ↥hyp.Q) = Nat.card ↥hyp.Q0 := by
    rw [hZQ0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv]
  have hcardK' : Nat.card ↥hyp.actualKActor =
      Nat.card ↥(Subgroup.center ↥hyp.Q) - 1 := by
    rw [hZcard, hQ0card, hKKcard]
  have hcardlift : ∀ U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q),
      Nat.card ↥U = Nat.card ↥(Subgroup.center ↥hyp.Q) →
      Nat.card ↥(hyp.liftCentralQuotient U) = Nat.card ↥hyp.Q0 ^ 2 := by
    intro U hU
    rw [card_liftCentralQuotient, hU, hZcard, sq]
  -- fixed-point-freeness on the central quotient
  obtain ⟨hP2, -, -, -⟩ := id hQsuz
  have hfreeP := fixedPointFree_of_actsRegularlyOnInvolutions hP2 hreg
  have hfree : ∀ k : ↥hyp.actualKActor, k ≠ 1 →
      ∀ q : ↥hyp.Q ⧸ Subgroup.center ↥hyp.Q,
        IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic hyp.actualKActor.subtype) k q = q →
          q = 1 := by
    apply Suzuki2Groups.quotient_fixedPointFree_of_fixedPoints_le
      hyp.actualKActor.subtype (Subgroup.center ↥hyp.Q)
      (IsAInvariant.of_characteristic hyp.actualKActor.subtype)
    · exact Suzuki2Groups.card_coprime_of_card_eq_sub_one
        (Subgroup.center ↥hyp.Q) hcardK'
    · intro k hk x hx
      rw [hfreeP k hk x hx]
      exact Subgroup.one_mem _
  -- all subgroups of the (elementary abelian) central quotient are normal
  have hqcomm : ∀ a b : (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q), a * b = b * a :=
    fun a b => csplit.quotientEA.1 a b
  have hnormal : ∀ U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q), U.Normal := by
    intro U
    refine ⟨fun n hn g => ?_⟩
    rw [hqcomm g n, mul_assoc, mul_inv_cancel, mul_one]
    exact hn
  haveI := hnormal csplit.left
  haveI := hnormal csplit.right
  refine ⟨hyp.liftCentralQuotient csplit.left, hyp.liftCentralQuotient csplit.right,
    ⟨liftCentralQuotient_le_Q _, Q0_le_liftCentralQuotient hZQ0 _,
      kInvariant_liftCentralQuotient csplit.leftInvariant,
      hcardlift _ csplit.leftCard⟩,
    ⟨liftCentralQuotient_le_Q _, Q0_le_liftCentralQuotient hZQ0 _,
      kInvariant_liftCentralQuotient csplit.rightInvariant,
      hcardlift _ csplit.rightCard⟩, ?_, ?_⟩
  · -- the two lifts are distinct
    intro heq
    have hLR : csplit.left = csplit.right := liftCentralQuotient_injective heq
    have hdisj := csplit.complementary.disjoint
    rw [hLR, disjoint_self] at hdisj
    have hcardR : Nat.card ↥csplit.right = Nat.card ↥(Subgroup.center ↥hyp.Q) :=
      csplit.rightCard
    rw [hdisj, Subgroup.card_bot, hZcard, hQ0card] at hcardR
    rcases Nat.pow_eq_one.mp hcardR.symm with h | h
    · omega
    · exact hm h
  · -- uniqueness
    intro Z hZ
    obtain ⟨U, hUinv, hUcard, hUlift⟩ :=
      exists_eq_liftCentralQuotient_of_isKSubgroupSquare hZQ0 hZ
    have hUcard' : Nat.card ↥U = Nat.card ↥(Subgroup.center ↥hyp.Q) := by
      rw [hUcard, hZcard]
    by_cases hU1 : U = csplit.left
    · exact Or.inl (by rw [← hUlift, hU1])
    by_cases hU2 : U = csplit.right
    · exact Or.inr (by rw [← hUlift, hU2])
    exfalso
    obtain ⟨e⟩ := Suzuki2Groups.nonempty_kEquivariantMulEquiv_of_third_invariant
      (IsAInvariant.quotientMulAutHom
        (IsAInvariant.of_characteristic hyp.actualKActor.subtype))
      hfree csplit.leftInvariant csplit.rightInvariant hUinv csplit.complementary
      (by rw [hUcard']; exact hcardK')
      (by rw [hUcard']; exact csplit.leftCard)
      (by rw [hUcard']; exact csplit.rightCard)
      hU1 hU2
    exact hnotB (isTypeB_of_isomorphicOrderQModuleSplit_of_card_eq_cube hQsuz
      hKcyc hreg hm hKKcard hcard ⟨csplit, e⟩)

/-- **A `K`-subgroup of `S` of order `q²` containing an element that `P`
centralizes is normalized by `P`.**

Its conjugates are again such subgroups (`isKSubgroupSquare_map_conj`), and two
distinct ones meet in `Q₀` (`inf_eq_Q0_of_ne_of_kInvariant`) — but the common
element lies outside `Q₀`.  This is what makes the book's "`P` centralizes an
element of order `4` in `S`" produce a `P`-invariant `K`-subgroup (p. 117). -/
theorem conj_mem_of_mem_centralizer
    (hQsuz : IsSuzuki2Group ↥hyp.Q)
    {N : Subgroup G} (hN : hyp.IsKSubgroupSquare N)
    {P : Subgroup G} (hPV : P ≤ hyp.V)
    {v : G} (hvN : v ∈ N) (hvQ0 : v ∉ hyp.Q0)
    (hvC : ∀ g ∈ P, g * v = v * g) :
    ∀ g ∈ P, ∀ y ∈ N, g * y * g⁻¹ ∈ N := by
  intro g hg
  have hgV : g ∈ hyp.V := hPV hg
  have hNg : hyp.IsKSubgroupSquare (N.map (MulAut.conj g).toMonoidHom) :=
    isKSubgroupSquare_map_conj hgV hN
  have hcv : g⁻¹ * v * g = v := by
    have h := hvC g hg
    calc g⁻¹ * v * g = g⁻¹ * (v * g) := by group
      _ = g⁻¹ * (g * v) := by rw [← h]
      _ = v := by group
  have hvNg : v ∈ N.map (MulAut.conj g).toMonoidHom := by
    refine mem_map_conj.mpr ?_
    rwa [hcv]
  have heq : N.map (MulAut.conj g).toMonoidHom = N := by
    by_contra hne
    have hinf := hyp.inf_eq_Q0_of_ne_of_kInvariant hQsuz hNg.1 hNg.2.1 hNg.2.2.1
      hNg.2.2.2 hN.2.1 hN.2.2.1 hN.2.2.2 hne
    exact hvQ0 (by rw [← hinf]; exact ⟨hvNg, hvN⟩)
  intro y hy
  have hmem : g * y * g⁻¹ ∈ N.map (MulAut.conj g).toMonoidHom := by
    refine mem_map_conj.mpr ?_
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y from by group]
  rwa [heq] at hmem

/-- **Peterfalvi Appendix III, Higman theorem (d), in the ambient group**
(p. 141), as case (3) of the Ch. III §1 Proposition uses it (p. 117): if `S = Q`
is a Suzuki `2`-group of order `q³` then `S` has two distinct `K`-subgroups of
order `q²`.

`center_payload_of_card_eq_cube` splits `S ⧸ Z(S)` into two complementary
invariant summands of order `q` and identifies `Z(S)` with `Q₀`; the preimages
in `S` are the required subgroups, distinct because the summands are (they are
complementary and both proper). -/
theorem exists_two_kSubgroups_of_card_cube
    (hQsuz : IsSuzuki2Group ↥hyp.Q) {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 3) :
    ∃ X Y : Subgroup G,
      hyp.IsKSubgroupSquare X ∧ hyp.IsKSubgroupSquare Y ∧ X ≠ Y := by
  classical
  have hKcyc : IsCyclic ↥hyp.actualKActor := hyp.actualKActor_isCyclic
  have hreg : ActsRegularlyOnInvolutions hyp.actualKActor :=
    hyp.actualKActor_actsRegularlyOnInvolutions
  have hKKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1 := by
    have h1 : Nat.card ↥hyp.actualKActor = Nat.card ↥hyp.K :=
      Nat.card_congr (MonoidHom.ofInjective hyp.conjQByK_injective).toEquiv.symm
    rw [h1, hyp.card_K_eq_card_Q0_sub_one, hQ0card]
  have hcard : Nat.card ↥hyp.Q = (2 ^ m) ^ 3 := by rw [hcardQ, hQ0card]
  obtain ⟨-, hZsq, ⟨csplit⟩⟩ :=
    center_payload_of_card_eq_cube hQsuz hKcyc hreg hm hKKcard hcard
  have hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q :=
    hyp.center_Q_eq_Q0_subgroupOf_of_sq_eq_one hZsq
  have hZcard : Nat.card ↥(Subgroup.center ↥hyp.Q) = Nat.card ↥hyp.Q0 := by
    rw [hZQ0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv]
  have hcardlift : ∀ U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q),
      Nat.card ↥U = Nat.card ↥(Subgroup.center ↥hyp.Q) →
      Nat.card ↥(hyp.liftCentralQuotient U) = Nat.card ↥hyp.Q0 ^ 2 := by
    intro U hU
    rw [card_liftCentralQuotient, hU, hZcard, sq]
  refine ⟨hyp.liftCentralQuotient csplit.left, hyp.liftCentralQuotient csplit.right,
    ⟨liftCentralQuotient_le_Q _, Q0_le_liftCentralQuotient hZQ0 _,
      kInvariant_liftCentralQuotient csplit.leftInvariant,
      hcardlift _ csplit.leftCard⟩,
    ⟨liftCentralQuotient_le_Q _, Q0_le_liftCentralQuotient hZQ0 _,
      kInvariant_liftCentralQuotient csplit.rightInvariant,
      hcardlift _ csplit.rightCard⟩, ?_⟩
  intro heq
  have hLR : csplit.left = csplit.right := liftCentralQuotient_injective heq
  have hdisj := csplit.complementary.disjoint
  rw [hLR, disjoint_self] at hdisj
  have hcardR : Nat.card ↥csplit.right = Nat.card ↥(Subgroup.center ↥hyp.Q) :=
    csplit.rightCard
  rw [hdisj, Subgroup.card_bot, hZcard, hQ0card] at hcardR
  rcases Nat.pow_eq_one.mp hcardR.symm with h | h
  · omega
  · exact hm h

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (3): the two
`K`-subgroups that `P` normalizes** (p. 117), unconditionally.

The book splits on the type of `S` — for types C and D the two `K`-subgroups of
order `q²` are the only ones, and for type B it counts `q + 1` of them.  The
dichotomy used here is the one that actually drives both halves: are the two
summands of Higman's split `K`-equivariantly isomorphic?

* **No** — then a third invariant subgroup of the summand order cannot exist
  (`nonempty_kEquivariantMulEquiv_of_third_invariant`), so the two lifts are the
  only `K`-subgroups of `S` of order `q²` and the odd-order `P` fixes both
  (`conj_mem_of_unique_of_le_V`).
* **Yes** — then the element `v` of order `4` that `P` centralizes lies in a
  `K`-invariant subgroup of the summand order
  (`exists_invariant_mem_of_kEquivariantMulEquiv`), whose lift `X` is normalized
  by `P` (`conj_mem_of_mem_centralizer`); operator Maschke for `K ⊔ P ≤ D` then
  supplies the partner (`exists_kSubgroupSquare_complement`).  This replaces the
  book's count. -/
theorem exists_two_kSubgroups_invariant_of_card_cube
    (hQsuz : IsSuzuki2Group ↥hyp.Q) {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 3)
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ hyp.V)
    {v : G} (hvQ : v ∈ hyp.Q) (hvQ0 : v ∉ hyp.Q0)
    (hvC : ∀ g ∈ P, g * v = v * g) :
    ∃ X Y : Subgroup G, hyp.IsKSubgroupSquare X ∧ hyp.IsKSubgroupSquare Y ∧
      X ≠ Y ∧ (∀ g ∈ P, ∀ y ∈ X, g * y * g⁻¹ ∈ X) ∧
      (∀ g ∈ P, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) := by
  classical
  have hKcyc : IsCyclic ↥hyp.actualKActor := hyp.actualKActor_isCyclic
  have hreg : ActsRegularlyOnInvolutions hyp.actualKActor :=
    hyp.actualKActor_actsRegularlyOnInvolutions
  have hKKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1 := by
    have h1 : Nat.card ↥hyp.actualKActor = Nat.card ↥hyp.K :=
      Nat.card_congr (MonoidHom.ofInjective hyp.conjQByK_injective).toEquiv.symm
    rw [h1, hyp.card_K_eq_card_Q0_sub_one, hQ0card]
  have hcard : Nat.card ↥hyp.Q = (2 ^ m) ^ 3 := by rw [hcardQ, hQ0card]
  obtain ⟨-, hZsq, ⟨csplit⟩⟩ :=
    center_payload_of_card_eq_cube hQsuz hKcyc hreg hm hKKcard hcard
  have hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q :=
    hyp.center_Q_eq_Q0_subgroupOf_of_sq_eq_one hZsq
  have hZcard : Nat.card ↥(Subgroup.center ↥hyp.Q) = Nat.card ↥hyp.Q0 := by
    rw [hZQ0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv]
  have hcardK' : Nat.card ↥hyp.actualKActor =
      Nat.card ↥(Subgroup.center ↥hyp.Q) - 1 := by
    rw [hZcard, hQ0card, hKKcard]
  have hcardlift : ∀ U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q),
      Nat.card ↥U = Nat.card ↥(Subgroup.center ↥hyp.Q) →
      Nat.card ↥(hyp.liftCentralQuotient U) = Nat.card ↥hyp.Q0 ^ 2 := by
    intro U hU
    rw [card_liftCentralQuotient, hU, hZcard, sq]
  obtain ⟨hP2, -, -, -⟩ := id hQsuz
  have hfreeP := fixedPointFree_of_actsRegularlyOnInvolutions hP2 hreg
  have hfree : ∀ k : ↥hyp.actualKActor, k ≠ 1 →
      ∀ q : ↥hyp.Q ⧸ Subgroup.center ↥hyp.Q,
        IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic hyp.actualKActor.subtype) k q = q →
          q = 1 := by
    apply Suzuki2Groups.quotient_fixedPointFree_of_fixedPoints_le
      hyp.actualKActor.subtype (Subgroup.center ↥hyp.Q)
      (IsAInvariant.of_characteristic hyp.actualKActor.subtype)
    · exact Suzuki2Groups.card_coprime_of_card_eq_sub_one
        (Subgroup.center ↥hyp.Q) hcardK'
    · intro k hk x hx
      rw [hfreeP k hk x hx]
      exact Subgroup.one_mem _
  have hqcomm : ∀ a b : (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q), a * b = b * a :=
    csplit.quotientEA.1
  have hnormal : ∀ U : Subgroup (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q), U.Normal := by
    intro U
    refine ⟨fun x hx g => ?_⟩
    rw [hqcomm g x, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  haveI := hnormal csplit.left
  haveI := hnormal csplit.right
  have hXpack : hyp.IsKSubgroupSquare (hyp.liftCentralQuotient csplit.left) :=
    ⟨liftCentralQuotient_le_Q _, Q0_le_liftCentralQuotient hZQ0 _,
      kInvariant_liftCentralQuotient csplit.leftInvariant,
      hcardlift _ csplit.leftCard⟩
  have hYpack : hyp.IsKSubgroupSquare (hyp.liftCentralQuotient csplit.right) :=
    ⟨liftCentralQuotient_le_Q _, Q0_le_liftCentralQuotient hZQ0 _,
      kInvariant_liftCentralQuotient csplit.rightInvariant,
      hcardlift _ csplit.rightCard⟩
  have hLRne : hyp.liftCentralQuotient csplit.left
      ≠ hyp.liftCentralQuotient csplit.right := by
    intro heq
    have hLR : csplit.left = csplit.right := liftCentralQuotient_injective heq
    have hdisj := csplit.complementary.disjoint
    rw [hLR, disjoint_self] at hdisj
    have hcardR : Nat.card ↥csplit.right = Nat.card ↥(Subgroup.center ↥hyp.Q) :=
      csplit.rightCard
    rw [hdisj, Subgroup.card_bot, hZcard, hQ0card] at hcardR
    rcases Nat.pow_eq_one.mp hcardR.symm with h | h
    · omega
    · exact hm h
  rcases isEmpty_or_nonempty (Suzuki2Groups.KEquivariantMulEquiv
    csplit.leftInvariant.restrict csplit.rightInvariant.restrict) with hno | hyes
  · -- non-isomorphic summands: the two lifts are the only ones
    have huniq : ∀ Z : Subgroup G, hyp.IsKSubgroupSquare Z →
        Z = hyp.liftCentralQuotient csplit.left ∨
        Z = hyp.liftCentralQuotient csplit.right := by
      intro Z hZ
      obtain ⟨U, hUinv, hUcard, hUlift⟩ :=
        exists_eq_liftCentralQuotient_of_isKSubgroupSquare hZQ0 hZ
      have hUcard' : Nat.card ↥U = Nat.card ↥(Subgroup.center ↥hyp.Q) := by
        rw [hUcard, hZcard]
      by_cases hU1 : U = csplit.left
      · exact Or.inl (by rw [← hUlift, hU1])
      by_cases hU2 : U = csplit.right
      · exact Or.inr (by rw [← hUlift, hU2])
      exact absurd (Suzuki2Groups.nonempty_kEquivariantMulEquiv_of_third_invariant
        (IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic hyp.actualKActor.subtype))
        hfree csplit.leftInvariant csplit.rightInvariant hUinv
        csplit.complementary (by rw [hUcard']; exact hcardK')
        (by rw [hUcard']; exact csplit.leftCard)
        (by rw [hUcard']; exact csplit.rightCard) hU1 hU2) (by simpa using hno)
    exact ⟨_, _, hXpack, hYpack, hLRne,
      conj_mem_of_unique_of_le_V hp hPcard hPV hXpack hLRne huniq,
      conj_mem_of_unique_of_le_V hp hPcard hPV hYpack (Ne.symm hLRne)
        (fun Z hZ => (huniq Z hZ).symm)⟩
  · -- isomorphic summands: build a `K`-subgroup through `v`, then Maschke
    obtain ⟨e⟩ := hyes
    have hKAcomm : ∀ a b : ↥hyp.actualKActor, a * b = b * a := fun a b => by
      obtain ⟨g, hg⟩ := hKcyc.exists_generator
      obtain ⟨i, rfl⟩ := hg a
      obtain ⟨j, rfl⟩ := hg b
      rw [← zpow_add, ← zpow_add, add_comm]
    have htrans : ∀ a b : ↥csplit.right, a ≠ 1 → b ≠ 1 →
        ∃ k : ↥hyp.actualKActor, csplit.rightInvariant.restrict k a = b := by
      apply Suzuki2Groups.restrict_transitive_of_fixedPointFree_card
        (IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic hyp.actualKActor.subtype))
        hfree csplit.rightInvariant
      rw [csplit.rightCard]
      exact hcardK'
    obtain ⟨N, hNinv, hNcard, hNmem⟩ :=
      Suzuki2Groups.exists_invariant_mem_of_kEquivariantMulEquiv hKAcomm hqcomm
        csplit.leftInvariant csplit.rightInvariant csplit.complementary e htrans
        (QuotientGroup.mk' (Subgroup.center ↥hyp.Q) ⟨v, hvQ⟩)
    have hNpack : hyp.IsKSubgroupSquare (hyp.liftCentralQuotient N) :=
      ⟨liftCentralQuotient_le_Q _, Q0_le_liftCentralQuotient hZQ0 _,
        kInvariant_liftCentralQuotient hNinv,
        hcardlift _ (hNcard.trans csplit.leftCard)⟩
    have hvX : v ∈ hyp.liftCentralQuotient N :=
      mem_liftCentralQuotient_iff.mpr ⟨hvQ, hNmem⟩
    have hXP := conj_mem_of_mem_centralizer hQsuz hNpack hPV hvX hvQ0 hvC
    have hPD : P ≤ hyp.D := hPV.trans hyp.V_le_D
    have hAD : hyp.K ⊔ P ≤ hyp.D := sup_le hyp.K_le_D hPD
    have hXA : ∀ a ∈ hyp.K ⊔ P, ∀ y ∈ hyp.liftCentralQuotient N,
        a * y * a⁻¹ ∈ hyp.liftCentralQuotient N :=
      conj_mem_sup hNpack.2.2.1 hXP
    obtain ⟨Y, hYQ, hQ0Y, hYA, hYcard, hne⟩ :=
      hyp.exists_kSubgroupSquare_complement hAD hP2 hZQ0 csplit.quotientEA
        hcardQ hNpack.1 hNpack.2.1 hXA hNpack.2.2.2
    exact ⟨_, Y, hNpack,
      ⟨hYQ, hQ0Y, fun k hk => hYA k ((le_sup_left : hyp.K ≤ hyp.K ⊔ P) hk),
        hYcard⟩, hne, hXP,
      fun g hg => hYA g ((le_sup_right : P ≤ hyp.K ⊔ P) hg)⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
