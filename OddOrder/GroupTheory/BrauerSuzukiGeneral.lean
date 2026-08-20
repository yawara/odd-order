/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzuki
import OddOrder.GroupTheory.BrauerSuzukiEndgame
import OddOrder.GroupTheory.BrauerSuzukiQ8

/-!
# Brauer–Suzuki: the theorem for an arbitrary generalized quaternion Sylow `2`-subgroup

The three cases of the Brauer–Suzuki theorem are proved separately in this directory:

* `brauerSuzuki_of_isCyclic_sylowTwo` — cyclic Sylow `2`-subgroup (Burnside normal complement);
* `QuaternionSylowSetup.brauerSuzuki_of_quaternionSylow` — generalized quaternion of order `≥ 16`
  (Gorenstein Ch. 12, ordinary exceptional characters);
* `brauerSuzuki_q8` — the quaternion group of order `8` (Navarro Ch. 1–7, modular characters).

This file assembles them into a **single statement quantified over an arbitrary isomorphism
`↥T ≃* QuaternionGroup m`**, with no side hypothesis on `m`: a Sylow `2`-subgroup of a finite
group has order a power of `2`, so `4m = 2ᵏ` pins `m = 2ᵏ⁻²`, and the three cases are `k = 2`
(where `QuaternionGroup 1 ≅ C₄` is cyclic), `k = 3` and `k ≥ 4`.

The assembly used to live inside `Peterfalvi.Appendices.NearFields.RankOneHypothesis.brauerSuzuki`,
specialized to the rank-one hypothesis of Peterfalvi Appendix II; it is stated here in the general
form the theorem actually has, and that proof now just applies it.

## Main results

* `OddOrder.GroupTheory.brauerSuzuki_of_quaternionSylowTwo` — `G = O_{2'}(G)·C_G(z)`
* `OddOrder.GroupTheory.brauerSuzuki_mk_mem_center` — the same in the quotient form
  `z̄ ∈ Z(G/O_{2'}(G))`, which is how Brauer and Suzuki state it
* `OddOrder.GroupTheory.mk_mem_center_of_sup_centralizer_eq_top` — the converse of
  `oPiCore_sup_centralizer_eq_top_of_mk_mem_center`, so the two forms are interchangeable
* `OddOrder.GroupTheory.oPiCore_ne_two_eq_sSup_normal_odd` — `O_{2'}(G)` is the classical odd
  core `O(G)`, the supremum of the normal subgroups of odd order
* `OddOrder.GroupTheory.brauerSuzuki_mk_mem_center_oddCore` — the theorem in that notation
-/

open OddOrder.Isaacs.Ch03

open scoped Pointwise

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G]

section QuaternionPresentation

open QuaternionGroup

/-- In `QuaternionGroup n`, conjugation by `xa 0` inverts `a 1`: one half of the presentation
`⟨a, b | a^{2n} = 1, b² = aⁿ, bab⁻¹ = a⁻¹⟩`. -/
theorem quaternionGroup_xa_zero_conj_a_one (n : ℕ) :
    (xa 0 : QuaternionGroup n) * a 1 * (xa 0)⁻¹ = (a 1)⁻¹ := by
  have hinv : (xa 0 : QuaternionGroup n)⁻¹ = xa (n : ZMod (2 * n)) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [xa_mul_xa]
    have h0 : ((n : ZMod (2 * n)) + n - 0) = 0 := by
      rw [sub_zero, ← Nat.cast_add, ← two_mul, ZMod.natCast_self]
    rw [h0, a_zero]
  have hainv : (a 1 : QuaternionGroup n)⁻¹ = a (-1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [a_mul_a, add_neg_cancel, a_zero]
  rw [xa_mul_a, hinv, xa_mul_xa, hainv]
  congr 1
  rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]
  simp

/-- `a 1` and `xa 0` generate `QuaternionGroup n`. -/
theorem quaternionGroup_closure_pair (n : ℕ) [NeZero n] :
    Subgroup.closure {(a 1 : QuaternionGroup n), xa 0} = ⊤ := by
  have : NeZero (2 * n) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne n)⟩
  rw [eq_top_iff]
  rintro w -
  have ha_mem : ∀ j : ZMod (2 * n),
      a j ∈ Subgroup.closure {(a 1 : QuaternionGroup n), xa 0} := by
    intro j
    have hj : (a j : QuaternionGroup n) = a 1 ^ j.val := by
      rw [a_one_pow]
      exact congrArg _ (ZMod.natCast_rightInverse j).symm
    rw [hj]
    exact pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) _
  cases w with
  | a i => exact ha_mem i
  | xa i =>
    have hi : (xa i : QuaternionGroup n) = xa 0 * a i := by
      rw [xa_mul_a, zero_add]
    rw [hi]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) (ha_mem i)

end QuaternionPresentation

/-- **Brauer–Suzuki for an arbitrary generalized quaternion Sylow `2`-subgroup**: if a Sylow
`2`-subgroup `T` of the finite group `G` is isomorphic to `QuaternionGroup m` (any `m`; the case
`m = 1` is the cyclic group `C₄`) and `z ∈ T` is an involution, then

`G = O_{2'}(G)·C_G(z)`, stated as `oPiCore {p | p ≠ 2} G ⊔ C_G(z) = ⊤`.

`|T| = 4m` is a power of `2`, so `m = 2ᵏ⁻²` with `k = log₂|T| ≥ 2`, and the proof splits:

* `k = 2`: `QuaternionGroup 1 ≅ C₄` is cyclic — `brauerSuzuki_of_isCyclic_sylowTwo`;
* `k = 3`: `T ≅ Q₈` — `brauerSuzuki_q8` (modular character theory, Navarro Ch. 1–7);
* `k ≥ 4`: transport the presentation to a `QuaternionSylowSetup` with generators
  `x = e⁻¹(a 1)`, `y = e⁻¹(xa 0)` and apply `QuaternionSylowSetup.brauerSuzuki_of_quaternionSylow`;
  `z` is *the* involution of `T` (`eq_one_or_eq_z_of_sq_eq_one`), hence equals the setup's `z`. -/
theorem brauerSuzuki_of_quaternionSylowTwo {m : ℕ} (T : Sylow 2 G)
    (he : Nonempty (↥(T : Subgroup G) ≃* QuaternionGroup m))
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    oPiCore {p | p ≠ 2} G ⊔ Subgroup.centralizer {z} = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz_sq : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz_ne : z ≠ 1 := fun h => by simp [h] at hz
  obtain ⟨e⟩ := he
  -- `|T| = 2 ^ k = 4 * m`, so `m ≠ 0` and `k ≥ 2`.
  obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : Infinite (ZMod (2 * 0)) := ZMod.infinite
    have : Infinite (QuaternionGroup 0) :=
      Infinite.of_injective (QuaternionGroup.a (n := 0)) fun i j h => by injection h
    have h0 := Nat.card_congr e.toEquiv
    rw [hk, Nat.card_eq_zero_of_infinite] at h0
    exact absurd h0 (by positivity)
  have : NeZero m := ⟨hm0⟩
  have hcards : 2 ^ k = 4 * m := by
    rw [← hk]
    calc Nat.card ↥(T : Subgroup G)
        = Nat.card (QuaternionGroup m) := Nat.card_congr e.toEquiv
      _ = 4 * m := by rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hk2 : 2 ≤ k := by
    by_contra hlt
    rw [not_le] at hlt
    have hle : (2 : ℕ) ^ k ≤ 2 :=
      calc (2 : ℕ) ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    omega
  rcases eq_or_lt_of_le hk2 with hk2' | hk3
  · -- `|T| = 4`: `QuaternionGroup 1 = C₄` is cyclic.
    have hm1 : m = 1 := by rw [← hk2'] at hcards; norm_num at hcards; omega
    subst hm1
    have := QuaternionGroup.quaternionGroup_one_isCyclic
    have hcyc : IsCyclic ↥(T : Subgroup G) :=
      isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    exact brauerSuzuki_of_isCyclic_sylowTwo T hcyc z hz_sq hz_ne
  rcases eq_or_lt_of_le (show 3 ≤ k by omega) with hk3' | hk4
  · -- `|T| = 8`: the `Q₈` case.
    have hm2 : m = 2 := by rw [← hk3'] at hcards; norm_num at hcards; omega
    subst hm2
    exact brauerSuzuki_q8 T ⟨e⟩ hzT hz
  · -- `|T| = 2ᵏ ≥ 16`: assemble the Gorenstein setup and identify `z`.
    have hm_pow : m = 2 ^ (k - 2) := by
      have h1 : (2 : ℕ) ^ k = 4 * 2 ^ (k - 2) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      omega
    set s₁ : ↥(T : Subgroup G) := e.symm (QuaternionGroup.a 1) with hs₁
    set s₂ : ↥(T : Subgroup G) := e.symm (QuaternionGroup.xa 0) with hs₂
    have hqconj : s₂ * s₁ * s₂⁻¹ = s₁⁻¹ := by
      rw [hs₁, hs₂, ← map_inv, ← map_mul, ← map_mul, quaternionGroup_xa_zero_conj_a_one, map_inv]
    have hqsq : s₂ ^ 2 = s₁ ^ 2 ^ (k - 2) := by
      rw [hs₁, hs₂, ← map_pow, ← map_pow]
      congr 1
      rw [QuaternionGroup.xa_sq, QuaternionGroup.a_one_pow]
      congr 1
      rw [← hm_pow]
    let Q : QuaternionSylowSetup G :=
      { n := k - 1
        hn := by omega
        S := T
        x := (s₁ : G)
        y := (s₂ : G)
        hxS := s₁.2
        hyS := s₂.2
        hx_order := by
          have h1 : orderOf ((s₁ : G)) = orderOf s₁ :=
            orderOf_injective (T : Subgroup G).subtype Subtype.coe_injective _
          have h2 : orderOf s₁ = orderOf (QuaternionGroup.a 1 : QuaternionGroup m) :=
            orderOf_injective e.symm.toMonoidHom e.symm.injective _
          rw [h1, h2, QuaternionGroup.orderOf_a_one, hm_pow, ← pow_succ']
          congr 1
          omega
        hy_sq := by
          have := congrArg (Subtype.val) hqsq
          rw [SubgroupClass.coe_pow, SubgroupClass.coe_pow] at this
          rw [this]
          congr 2
        hconj := by
          have := congrArg (Subtype.val) hqconj
          rw [InvMemClass.coe_inv] at this
          exact this
        hclosure := by
          have hQtop : Subgroup.closure {(QuaternionGroup.a 1 : QuaternionGroup m),
              QuaternionGroup.xa 0} = ⊤ := quaternionGroup_closure_pair m
          have h1 : (Subgroup.closure {(QuaternionGroup.a 1 : QuaternionGroup m),
                QuaternionGroup.xa 0}).map e.symm.toMonoidHom
              = Subgroup.closure ({s₁, s₂} : Set ↥(T : Subgroup G)) := by
            rw [MonoidHom.map_closure]
            congr 1
            rw [Set.image_pair]
            rfl
          have hTtop : Subgroup.closure ({s₁, s₂} : Set ↥(T : Subgroup G)) = ⊤ := by
            rw [← h1, hQtop, Subgroup.map_top_of_surjective _ e.symm.surjective]
          have h2 : (Subgroup.closure ({s₁, s₂} : Set ↥(T : Subgroup G))).map
              (T : Subgroup G).subtype
              = Subgroup.closure {((s₁ : G)), ((s₂ : G))} := by
            rw [MonoidHom.map_closure]
            congr 1
            rw [Set.image_pair]
            rfl
          rw [← h2, hTtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] }
    have hbs := Q.brauerSuzuki_of_quaternionSylow
    rcases Q.eq_one_or_eq_z_of_sq_eq_one (s := z) hzT hz_sq with h1 | hzeq
    · exact absurd h1 hz_ne
    · rw [hzeq]
      exact hbs

omit [Finite G] in
/-- **Converse of `oPiCore_sup_centralizer_eq_top_of_mk_mem_center`**, for an arbitrary normal
subgroup: if `G = K·C_G(z)` with `K ⊴ G`, then `z̄` is central in `G/K`.

Elementary: writing `g = k·c` with `k ∈ K` and `c ∈ C_G(z)` (legitimate since `K` is normal, so
the join is the product set), `ḡ = c̄` commutes with `z̄`. -/
theorem mk_mem_center_of_sup_centralizer_eq_top {K : Subgroup G} [K.Normal] {z : G}
    (h : K ⊔ Subgroup.centralizer {z} = ⊤) :
    QuotientGroup.mk' K z ∈ Subgroup.center (G ⧸ K) := by
  rw [Subgroup.mem_center_iff]
  intro gg
  induction gg using QuotientGroup.induction_on with
  | H g =>
    -- `g ∈ ⊤ = K ⊔ C_G(z) = K·C_G(z)`
    have hg : g ∈ (↑(K ⊔ Subgroup.centralizer {z}) : Set G) := by
      rw [h]; trivial
    rw [Subgroup.normal_mul] at hg
    obtain ⟨u, hu, c, hc, rfl⟩ := hg
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hmku : QuotientGroup.mk' K u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
    have hmkuc : QuotientGroup.mk' K (u * c) = QuotientGroup.mk' K c := by
      rw [map_mul, hmku, one_mul]
    change QuotientGroup.mk' K (u * c) * QuotientGroup.mk' K z
      = QuotientGroup.mk' K z * QuotientGroup.mk' K (u * c)
    rw [hmkuc, ← map_mul, ← map_mul, hcz]

/-- **Brauer–Suzuki theorem, quotient form** (R. Brauer and M. Suzuki, *On finite groups of even
order whose 2-Sylow group is a quaternion group*, Proc. Nat. Acad. Sci. U.S.A. **45** (1959),
1757–1759): if a Sylow `2`-subgroup `T` of the finite group `G` is generalized quaternion and
`z ∈ T` is an involution, then the image of `z` in `G/O_{2'}(G)` is central.

This is the historically standard phrasing — `z` is an *isolated* involution in the sense of
Glauberman's later `Z*`-theorem, of which this is the prototype.  It is equivalent to the product
form `brauerSuzuki_of_quaternionSylowTwo` via `mk_mem_center_of_sup_centralizer_eq_top` and
`oPiCore_sup_centralizer_eq_top_of_mk_mem_center`. -/
theorem brauerSuzuki_mk_mem_center {m : ℕ} (T : Sylow 2 G)
    (he : Nonempty (↥(T : Subgroup G) ≃* QuaternionGroup m))
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    QuotientGroup.mk' (oPiCore {p | p ≠ 2} G) z
      ∈ Subgroup.center (G ⧸ oPiCore {p | p ≠ 2} G) :=
  mk_mem_center_of_sup_centralizer_eq_top
    (brauerSuzuki_of_quaternionSylowTwo T he hzT hz)

section OddCore

/-! ### The classical odd core `O(G)`

Brauer and Suzuki state the theorem with `O(G)`, the largest normal subgroup of odd order,
defined directly as the supremum of the normal subgroups of odd order.  For a finite group this
is `oPiCore {p | p ≠ 2} G`: a subgroup has odd order exactly when every prime dividing its order
is `≠ 2`. -/

/-- A subgroup of a finite group is a `{p | p ≠ 2}`-group exactly when its order is odd. -/
theorem isPiGroup_ne_two_iff_odd (N : Subgroup G) :
    Subgroup.IsPiGroup {p | p ≠ 2} N ↔ Odd (Nat.card N) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  constructor
  · exact fun h h2 =>
      h 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, Nat.card_pos.ne'⟩) rfl
  · intro h p hp
    rintro rfl
    exact h (Nat.dvd_of_mem_primeFactors hp)

/-- **`O_{2'}(G)` is the odd core `O(G)`**: for a finite group, the largest normal
`{p | p ≠ 2}`-subgroup is the supremum of all normal subgroups of odd order. -/
theorem oPiCore_ne_two_eq_sSup_normal_odd (G : Type*) [Group G] [Finite G] :
    oPiCore {p | p ≠ 2} G = sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)} := by
  refine le_antisymm (iSup_le fun H => le_sSup ⟨H.2.1, (isPiGroup_ne_two_iff_odd _).mp H.2.2⟩)
    (sSup_le fun N hN => ?_)
  have : N.Normal := hN.1
  exact Subgroup.IsPiGroup.le_oPiCore ((isPiGroup_ne_two_iff_odd N).mpr hN.2)

/-- The odd core is normal — the instance that makes `G ⧸ O(G)` a group. -/
instance sSupNormalOdd.normal (G : Type*) [Group G] [Finite G] :
    (sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}).Normal :=
  oPiCore_ne_two_eq_sSup_normal_odd G ▸ oPiCore.normal {p | p ≠ 2} G

/-- **Brauer–Suzuki theorem in the classical `O(G)` notation**: if a Sylow `2`-subgroup of the
finite group `G` is generalized quaternion, the image of an involution of it in `G/O(G)` is
central, where `O(G)` is the largest normal subgroup of odd order. -/
theorem brauerSuzuki_mk_mem_center_oddCore {m : ℕ} (T : Sylow 2 G)
    (he : Nonempty (↥(T : Subgroup G) ≃* QuaternionGroup m))
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    (QuotientGroup.mk z : G ⧸ sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)})
      ∈ Subgroup.center (G ⧸ sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}) := by
  refine mk_mem_center_of_sup_centralizer_eq_top ?_
  rw [← oPiCore_ne_two_eq_sSup_normal_odd G]
  exact brauerSuzuki_of_quaternionSylowTwo T he hzT hz

end OddCore

end OddOrder.GroupTheory
