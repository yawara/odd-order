/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import OddOrder.Isaacs.Ch06_FrobeniusActions.OddComplement
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups
import OddOrder.GroupTheory.ThreeStepGroup
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.GroupTheory.FittingSelfCentralizing
import OddOrder.GroupTheory.NilpotentCoprimeCommute
import OddOrder.GroupTheory.FixedPointFreeConjugation
import OddOrder.GroupTheory.SylowCovering

/-!
# CN-group structure — Gorenstein Lemma 1.2 and Theorem 1.5 Steps 2-3

Gorenstein Ch. 12 §1 Lemma 1.2, Step 2 (`F(G)·A` is Frobenius) and Step 3
(`π(F(G))` is a single prime) of Theorem 1.5.

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
-/


namespace OddOrder.GroupTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-! ## Gorenstein Ch. 12 §1 Lemma 1.2

> Let `P` and `Q` be `S_p`- and `S_q`-subgroups of the CN-group `G`, where `p` and `q` are
> distinct primes.  If an element of `P^*` centralizes an element of `Q^*`, then `P` centralizes
> `Q`.

This is the CN-specific engine of the section (it is used four times in the proof of
Theorem 1.5).  The CN hypothesis is taken here in unfolded form — "every nonidentity element of
`G` has nilpotent centralizer" — which is definitionally `OddOrder.BG.AppD.IsCNGroup G`; taking
it unfolded keeps this general-purpose leaf free of a dependency on `OddOrder.BG`. -/

/-- The centre of a subgroup `H`, transported back to an ambient subgroup of `G`. -/
def centerIn (H : Subgroup G) : Subgroup G := (Subgroup.center ↥H).map H.subtype

theorem centerIn_le (H : Subgroup G) : centerIn H ≤ H := Subgroup.map_subtype_le _

/-- Every element of `H` commutes with every element of the centre of `H`. -/
theorem commute_of_mem_centerIn {H : Subgroup G} {a z : G} (ha : a ∈ H) (hz : z ∈ centerIn H) :
    Commute a z := by
  obtain ⟨⟨w, hw⟩, hwc, rfl⟩ := hz
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc ⟨a, ha⟩)

/-- A nontrivial finite `p`-subgroup has nontrivial centre. -/
theorem centerIn_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : IsPGroup p ↥H) (hne : H ≠ ⊥) : centerIn H ≠ ⊥ := by
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  haveI := hH.center_nontrivial
  obtain ⟨⟨⟨z, hzH⟩, hzc⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥H))
  intro hbot
  apply hz1
  have hmem : z ∈ centerIn H := ⟨⟨z, hzH⟩, hzc, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subtype.ext (Subtype.ext hmem)

/-- In a finite nilpotent group, a `p`-subgroup and a `q`-subgroup with `p ≠ q` commute
elementwise: both lie in normal (hence unique) Sylow subgroups, which are disjoint. -/
theorem commute_of_isNilpotent_of_isPGroup {L : Type*} [Group L] [Finite L]
    [Group.IsNilpotent L] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {H K : Subgroup L} (hH : IsPGroup p ↥H) (hK : IsPGroup q ↥K) :
    ∀ a ∈ H, ∀ b ∈ K, Commute a b := by
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  obtain ⟨Q, hQ⟩ := hK.exists_le_sylow
  intro a ha b hb
  exact Subgroup.commute_of_normal_of_disjoint _ _
    (Ch01.Sylow.normal_of_isNilpotent P) (Ch01.Sylow.normal_of_isNilpotent Q)
    (IsPGroup.disjoint_of_ne p q hpq _ _ P.isPGroup' Q.isPGroup') a b (hP ha) (hQ hb)

/-- Ambient form of `commute_of_isNilpotent_of_isPGroup`: if `H` and `K` are a `p`-subgroup and a
`q`-subgroup (`p ≠ q`) of `G` both contained in a subgroup `N` with `N` nilpotent, then `H` and
`K` commute elementwise in `G`. -/
theorem commute_of_le_nilpotent_of_isPGroup [Finite G] {N : Subgroup G}
    (hN : Group.IsNilpotent ↥N) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {H K : Subgroup G} (hHN : H ≤ N) (hKN : K ≤ N)
    (hH : IsPGroup p ↥H) (hK : IsPGroup q ↥K) :
    ∀ a ∈ H, ∀ b ∈ K, Commute a b := by
  haveI := hN
  have hH' : IsPGroup p ↥(H.subgroupOf N) :=
    hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHN).symm
  have hK' : IsPGroup q ↥(K.subgroupOf N) :=
    hK.of_equiv (Subgroup.subgroupOfEquivOfLe hKN).symm
  intro a ha b hb
  exact congrArg Subtype.val
    (commute_of_isNilpotent_of_isPGroup hpq hH' hK'
      ⟨a, hHN ha⟩ ha ⟨b, hKN hb⟩ hb).eq

/-- **Gorenstein Ch. 12 §1 Lemma 1.2**.

Let `G` be a group in which every nonidentity element has nilpotent centralizer (a *CN-group*),
and let `P`, `Q` be a `p`-subgroup and a `q`-subgroup with `p ≠ q`.  If some nonidentity element
of `P` commutes with some nonidentity element of `Q`, then `P` and `Q` commute elementwise.

The proof is Gorenstein's, in four passes through the CN hypothesis: `C_G(x)` shows `y`
centralizes `Z(P)`; `C_G(x₁)` for `1 ≠ x₁ ∈ Z(P)` shows `P` centralizes `y`; `C_G(y)` shows `P`
centralizes `Z(Q)`; `C_G(y₁)` for `1 ≠ y₁ ∈ Z(Q)` shows `P` centralizes `Q`.

Stated for arbitrary `p`- and `q`-subgroups rather than only Sylow subgroups: the proof uses
nothing beyond the `p`-group property, so this is the general form. -/
theorem commute_of_cn_of_commute_ne_one [Finite G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {P Q : Subgroup G} (hP : IsPGroup p ↥P) (hQ : IsPGroup q ↥Q)
    {x y : G} (hxP : x ∈ P) (hx1 : x ≠ 1) (hyQ : y ∈ Q) (hy1 : y ≠ 1)
    (hxy : Commute x y) :
    ∀ a ∈ P, ∀ b ∈ Q, Commute a b := by
  -- Notation for the two centres and the cyclic subgroup generated by `y`.
  have hZPle : centerIn P ≤ P := centerIn_le P
  have hZQle : centerIn Q ≤ Q := centerIn_le Q
  have hZP : IsPGroup p ↥(centerIn P) := hP.to_le hZPle
  have hZQ : IsPGroup q ↥(centerIn Q) := hQ.to_le hZQle
  have hyzp : Subgroup.zpowers y ≤ Q := Subgroup.zpowers_le.mpr hyQ
  have hyP : IsPGroup q ↥(Subgroup.zpowers y) := hQ.to_le hyzp
  -- Step 1: `y` centralizes `Z(P)`, via the nilpotent centralizer `C_G(x)`.
  have step1 : ∀ z ∈ centerIn P, Commute z y := by
    have hZPc : centerIn P ≤ Subgroup.centralizer ({x} : Set G) := fun z hz =>
      Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_centerIn hxP hz).symm.eq
    have hyc : Subgroup.zpowers y ≤ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm.eq)
    intro z hz
    exact commute_of_le_nilpotent_of_isPGroup (hCN x hx1) hpq hZPc hyc hZP hyP
      z hz y (Subgroup.mem_zpowers y)
  -- Step 2: `P` centralizes `y`, via `C_G(x₁)` for a nonidentity `x₁ ∈ Z(P)`.
  have hPne : P ≠ ⊥ := fun hc => hx1 (by simpa [hc, Subgroup.mem_bot] using hxP)
  obtain ⟨x₁, hx₁mem⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (centerIn_ne_bot hP hPne)
  have hx₁1 : (x₁ : G) ≠ 1 := fun hc => hx₁mem (Subtype.ext hc)
  have step2 : ∀ a ∈ P, Commute a y := by
    have hPc : P ≤ Subgroup.centralizer ({(x₁ : G)} : Set G) := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_mem_centerIn ha x₁.2).eq
    have hyc : Subgroup.zpowers y ≤ Subgroup.centralizer ({(x₁ : G)} : Set G) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr (step1 _ x₁.2).symm.eq)
    intro a ha
    exact commute_of_le_nilpotent_of_isPGroup (hCN _ hx₁1) hpq hPc hyc hP hyP
      a ha y (Subgroup.mem_zpowers y)
  -- Step 3: `P` centralizes `Z(Q)`, via `C_G(y)`.
  have step3 : ∀ a ∈ P, ∀ w ∈ centerIn Q, Commute a w := by
    have hPc : P ≤ Subgroup.centralizer ({y} : Set G) := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (step2 a ha).eq
    have hZQc : centerIn Q ≤ Subgroup.centralizer ({y} : Set G) := fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_centerIn hyQ hw).symm.eq
    exact commute_of_le_nilpotent_of_isPGroup (hCN y hy1) hpq hPc hZQc hP hZQ
  -- Step 4: `P` centralizes `Q`, via `C_G(y₁)` for a nonidentity `y₁ ∈ Z(Q)`.
  have hQne : Q ≠ ⊥ := fun hc => hy1 (by simpa [hc, Subgroup.mem_bot] using hyQ)
  obtain ⟨y₁, hy₁mem⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (centerIn_ne_bot hQ hQne)
  have hy₁1 : (y₁ : G) ≠ 1 := fun hc => hy₁mem (Subtype.ext hc)
  have hPc : P ≤ Subgroup.centralizer ({(y₁ : G)} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (step3 a ha _ y₁.2).eq
  have hQc : Q ≤ Subgroup.centralizer ({(y₁ : G)} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_centerIn hb y₁.2).eq
  exact commute_of_le_nilpotent_of_isPGroup (hCN _ hy₁1) hpq hPc hQc hP hQ

/-! ## Step 2 of Theorem 1.5: `F(G) A` is Frobenius

Gorenstein's Theorem 1.5 begins by setting `F = F(G)`, `π = π(F)`, and taking a Hall
`π'`-subgroup `A` of the solvable group `G`.  Its first substantive claim is that no nonidentity
element of `A` centralizes a nonidentity element of `F`, so that `A` acts regularly on `F` and
`FA` is a Frobenius group.  This is where the CN hypothesis enters, through Lemma 1.2.

The proof uses nothing about `A` beyond `(|A|, |F|) = 1`, so it is stated for a single element
whose order is prime to `|F(G)|`.  That is a genuine generalization of the book's statement, not
a weakening: the Hall `π'`-subgroup version follows by applying it to each element of `A`. -/

/-- The Sylow `p`-subgroup of `F(G)`, pushed back into `G`, lies in `O_p(G)`.

`F(G)` is nilpotent, so its Sylow `p`-subgroup is normal in it and therefore characteristic;
`F(G)` is normal in `G`, so the image is normal in `G`; a normal `p`-subgroup lies in `O_p(G)`. -/
theorem sylow_fitting_map_le_oPiCore [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p ↥(Ch01.fitting G)) :
    (S : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype ≤
      Ch03.oPiCore ({p} : Set ℕ) G := by
  haveI hSn : (S : Subgroup ↥(Ch01.fitting G)).Normal := Ch01.Sylow.normal_of_isNilpotent S
  haveI hSc : (S : Subgroup ↥(Ch01.fitting G)).Characteristic :=
    Sylow.characteristic_of_normal S hSn
  haveI : ((S : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype).Normal :=
    normal_map_subtype_of_characteristic hSc
  exact (Ch04.isPiGroup_singleton_of_isPGroup
    (S.isPGroup'.map (Ch01.fitting G).subtype)).le_oPiCore

/-- The order of an element of a subgroup, computed in the subgroup, is its order in `G`. -/
theorem orderOf_mk_eq {H : Subgroup G} {x : G} (hx : x ∈ H) :
    orderOf (⟨x, hx⟩ : ↥H) = orderOf x :=
  (orderOf_injective H.subtype H.subtype_injective ⟨x, hx⟩).symm

/-- Two elements of `F(G)` whose orders are coprime commute, `F(G)` being nilpotent. -/
theorem commute_of_mem_fitting_of_coprime_orderOf [Finite G] {x f : G}
    (hx : x ∈ Ch01.fitting G) (hf : f ∈ Ch01.fitting G)
    (hcop : Nat.Coprime (orderOf x) (orderOf f)) : Commute x f := by
  exact congrArg Subtype.val
    (commute_of_coprime_orderOf_of_isNilpotent (L := ↥(Ch01.fitting G))
      (x := ⟨x, hx⟩) (y := ⟨f, hf⟩) (by rw [orderOf_mk_eq, orderOf_mk_eq]; exact hcop)).eq

/-- **Gorenstein Ch. 12 §1, Theorem 1.5, step 2.**

In a finite solvable CN-group, an element whose order is prime to `|F(G)|` centralizes no
nonidentity element of `F(G)`.

Gorenstein argues with a `q`-element `y` of a Hall `π(F)'`-subgroup `A` and a `p`-element `x` of
`F`; the four moves are (1) Lemma 1.2 makes `y` centralize a whole Sylow `p`-subgroup of `G`,
hence `O_p(G)`; (2) `C_G(x)` is nilpotent by the CN hypothesis and contains every element of `F`
of order prime to `p`; (3) coprimality of orders inside that nilpotent centralizer makes `y`
centralize all of those; (4) `F` is generated by its Sylow subgroups, so `y` centralizes `F`, and
`C_G(F) ≤ F` puts `y` in `F` — impossible, since `|y|` is prime to `|F|`. -/
theorem not_commute_of_coprime_orderOf_card_fitting [Finite G] [IsSolvable G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    {x y : G} (hxF : x ∈ Ch01.fitting G) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hcop : Nat.Coprime (orderOf y) (Nat.card ↥(Ch01.fitting G))) :
    ¬ Commute x y := by
  classical
  intro hxy
  -- Replace `x` and `y` by elements of prime order `p` and `q` inside `⟨x⟩` and `⟨y⟩`.
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (fun h => hx1 (orderOf_eq_one_iff.mp h))
  obtain ⟨q, hq, hqy⟩ := Nat.exists_prime_and_dvd (fun h => hy1 (orderOf_eq_one_iff.mp h))
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers x)) p
    (by rw [Nat.card_zpowers]; exact hpx)
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers y)) q
    (by rw [Nat.card_zpowers]; exact hqy)
  set x' : G := (x₀ : G) with hx'def
  set y' : G := (y₀ : G) with hy'def
  have hx'ord : orderOf x' = p :=
    (orderOf_injective (Subgroup.zpowers x).subtype
      (Subgroup.zpowers x).subtype_injective x₀).trans hx₀
  have hy'ord : orderOf y' = q :=
    (orderOf_injective (Subgroup.zpowers y).subtype
      (Subgroup.zpowers y).subtype_injective y₀).trans hy₀
  have hx'1 : x' ≠ 1 := fun h => hp.ne_one (by rw [← hx'ord, h, orderOf_one])
  have hy'1 : y' ≠ 1 := fun h => hq.ne_one (by rw [← hy'ord, h, orderOf_one])
  have hx'F : x' ∈ Ch01.fitting G :=
    (Subgroup.zpowers_le.mpr hxF) x₀.2
  -- `x'` and `y'` still commute: each is a power of the original.
  have hcomm' : Commute x' y' := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x₀.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y₀.2
    rw [hx'def, hy'def, ← hj, ← hk]
    exact (hxy.zpow_left j).zpow_right k
  -- `p ∣ |F(G)|` but `q ∤ |F(G)|`; in particular `p ≠ q`.
  have hpF : p ∣ Nat.card ↥(Ch01.fitting G) := by
    rw [← hx'ord, ← orderOf_mk_eq hx'F]
    exact orderOf_dvd_natCard _
  have hqF : ¬ q ∣ Nat.card ↥(Ch01.fitting G) := by
    intro hdvd
    have hqy' : q ∣ orderOf y := hy'ord ▸ orderOf_dvd_of_mem_zpowers y₀.2
    exact hq.ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hqy' hdvd))
  have hpq : p ≠ q := fun h => hqF (h ▸ hpF)
  -- Step 1: Lemma 1.2 makes `y'` commute with a whole Sylow `p`-subgroup, hence with `O_p(G)`.
  have hx'pg : IsPGroup p ↥(Subgroup.zpowers x') :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hx'ord, pow_one]⟩
  have hy'qg : IsPGroup q ↥(Subgroup.zpowers y') :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hy'ord, pow_one]⟩
  obtain ⟨P, hPle⟩ := IsPGroup.exists_le_sylow hx'pg
  have hstep1 : ∀ a ∈ (P : Subgroup G), ∀ b ∈ Subgroup.zpowers y', Commute a b :=
    commute_of_cn_of_commute_ne_one hCN hpq P.isPGroup' hy'qg
      (hPle (Subgroup.mem_zpowers x')) hx'1 (Subgroup.mem_zpowers y') hy'1 hcomm'
  have hOple : Ch03.oPiCore ({p} : Set ℕ) G ≤ (P : Subgroup G) := by
    rw [Ch04.oPiCore_singleton_eq_opCore]
    exact Ch01.opCore_le P
  -- Step 2/3: inside the nilpotent centralizer `C_G(x')`, coprime orders commute.
  haveI hCnil : Group.IsNilpotent ↥(Subgroup.centralizer ({x'} : Set G)) := hCN x' hx'1
  have hy'C : y' ∈ Subgroup.centralizer ({x'} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm'.symm.eq
  -- Step 4: `F(G)` is generated by its Sylow subgroups, and `y'` commutes with each of them.
  have hcentF : ∀ f ∈ Ch01.fitting G, Commute y' f := by
    intro f hf
    have hmem : (⟨f, hf⟩ : ↥(Ch01.fitting G)) ∈
        ⨆ r : (Nat.card ↥(Ch01.fitting G)).primeFactors,
          ((default : Sylow (r : ℕ) ↥(Ch01.fitting G)) : Subgroup ↥(Ch01.fitting G)) := by
      rw [Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥(Ch01.fitting G)]; trivial
    refine Subgroup.iSup_induction _ (C := fun z : ↥(Ch01.fitting G) => Commute y' (z : G))
      hmem ?_ (Commute.one_right _) (fun a b ha hb => ha.mul_right hb)
    rintro ⟨r, hr⟩ z hz
    haveI : Fact (r : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
    have hzF : (z : G) ∈ Ch01.fitting G := z.2
    have hzr : IsPGroup r
        ↥((default : Sylow r ↥(Ch01.fitting G)) : Subgroup ↥(Ch01.fitting G)) :=
      (default : Sylow r ↥(Ch01.fitting G)).isPGroup'
    rcases eq_or_ne r p with rfl | hrp
    · -- `z` lies in the Sylow `p`-subgroup of `F(G)`, hence in `O_p(G) ≤ P`.
      have : (z : G) ∈ Ch03.oPiCore ({r} : Set ℕ) G :=
        sylow_fitting_map_le_oPiCore (default : Sylow r ↥(Ch01.fitting G))
          ⟨z, hz, rfl⟩
      exact (hstep1 (z : G) (hOple this) y' (Subgroup.mem_zpowers y')).symm
    · -- `z` has order prime to `p`, so it lies in `C_G(x')`; there coprimality finishes.
      obtain ⟨n, hn⟩ := hzr.exists_card_eq
      have hzcoe : orderOf (z : G) = orderOf z :=
        orderOf_injective (Ch01.fitting G).subtype (Ch01.fitting G).subtype_injective z
      have hzdvd : orderOf (z : G) ∣ r ^ n := by
        rw [hzcoe, ← orderOf_mk_eq hz, ← hn]
        exact orderOf_dvd_natCard _
      have hzC : (z : G) ∈ Subgroup.centralizer ({x'} : Set G) := by
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        refine (commute_of_mem_fitting_of_coprime_orderOf hx'F hzF ?_).symm.eq
        rw [hx'ord]
        exact Nat.Coprime.coprime_dvd_right hzdvd
          (Nat.Coprime.pow_right n ((Nat.coprime_primes hp Fact.out).mpr (Ne.symm hrp)))
      have hcopzy : Nat.Coprime (orderOf y') (orderOf (z : G)) := by
        rw [hy'ord]
        refine Nat.Coprime.coprime_dvd_right hzdvd (Nat.Coprime.pow_right n ?_)
        refine (Nat.coprime_primes hq Fact.out).mpr ?_
        rintro rfl
        exact hqF (Nat.dvd_of_mem_primeFactors hr)
      exact congrArg Subtype.val
        (commute_of_coprime_orderOf_of_isNilpotent
          (L := ↥(Subgroup.centralizer ({x'} : Set G)))
          (x := ⟨y', hy'C⟩) (y := ⟨(z : G), hzC⟩)
          (by rw [orderOf_mk_eq, orderOf_mk_eq]; exact hcopzy)).eq
  -- `y' ∈ C_G(F(G)) ≤ F(G)`, so `q = |y'|` divides `|F(G)|` — contradiction.
  have hy'F : y' ∈ Ch01.fitting G :=
    centralizer_fitting_le_fitting
      (Subgroup.mem_centralizer_iff.mpr fun f hf => (hcentF f hf).symm.eq)
  refine hqF ?_
  rw [← hy'ord, ← orderOf_mk_eq hy'F]
  exact orderOf_dvd_natCard _

/-! ## Step 3 of Theorem 1.5: `π(F(G))` is a single prime

Once `G ≠ F(G) A`, Gorenstein rules out `|π(F(G))| ≥ 2` by showing that each `p ∈ π(F(G))` with
a nontrivial `p'`-part in `F(G)` already has `O_p(G)` Sylow — so that `F(G)` would be a Hall
`π`-subgroup and `G = F(G) A` after all. -/

/-- A subgroup of a subgroup with nilpotent carrier is nilpotent. -/
theorem isNilpotent_of_le_of_isNilpotent {H K : Subgroup G}
    (hHK : H ≤ K) (hK : Group.IsNilpotent ↥K) : Group.IsNilpotent ↥H := by
  haveI := hK
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHK)

/-- **In a CN-group, a subgroup with nontrivial centre is nilpotent.**

For `1 ≠ z ∈ Z(A)` we have `A ≤ C_G(z)`, and `C_G(z)` is nilpotent by the CN hypothesis.

This is the last move of Gorenstein's argument that the Hall `π(F(G))'`-subgroup `A` of
Theorem 1.5 is nilpotent, and it reduces that claim to `Z(A) ≠ 1`.  Gorenstein gets `Z(A) ≠ 1`
from the Frobenius-complement structure of `A` (his Theorem 10.3.1(iv)/(v)), which is the part
still missing from this repository. -/
theorem isNilpotent_of_centerIn_ne_bot [Finite G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    {A : Subgroup G} (hZ : centerIn A ≠ ⊥) : Group.IsNilpotent ↥A := by
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hz1 : (z : G) ≠ 1 := fun h => hzne (Subtype.ext h)
  refine isNilpotent_of_le_of_isNilpotent (fun a ha => ?_) (hCN (z : G) hz1)
  exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_centerIn ha z.2).eq

/-- **Gorenstein Ch. 12 §1, Theorem 1.5, step 3.**

In a CN-group, if `O_p(G) ≠ 1` and `F(G)` contains a nontrivial normal subgroup `N` of order
prime to `p`, then `O_p(G)` is already a Sylow `p`-subgroup of `G`.

`O_p(G)` centralizes `N` — both lie in the nilpotent `F(G)` and their orders are coprime — so
Lemma 1.2 promotes this to "a whole Sylow `p`-subgroup `P` of `G` centralizes `N`", `N` being
generated by its Sylow subgroups.  Then `P ≤ C := C_G(N)`, which is normal in `G` and nilpotent
(it sits inside the nilpotent `C_G(z)` for any `1 ≠ z ∈ N`); so `P`, a Sylow `p`-subgroup of the
nilpotent `C`, is normal and hence characteristic in `C`, and therefore normal in `G`.  A normal
`p`-subgroup lies in `O_p(G)`, so `P = O_p(G)`.

Gorenstein applies this with `N = O_{p'}(F(G))`, concluding that if every `p ∈ π(F(G))` had a
nontrivial `p'`-part then `F(G)` would be a Hall subgroup and `G = F(G) A`. -/
theorem exists_sylow_eq_oPiCore_of_normal_pPrime_le_fitting
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    (hOpne : Ch03.oPiCore ({p} : Set ℕ) G ≠ ⊥)
    {N : Subgroup G} [N.Normal] (hNbot : N ≠ ⊥) (hNF : N ≤ Ch01.fitting G)
    (hpN : ¬ p ∣ Nat.card ↥N) :
    ∃ P : Sylow p G, (P : Subgroup G) = Ch03.oPiCore ({p} : Set ℕ) G := by
  classical
  have hOpPG : IsPGroup p ↥(Ch03.oPiCore ({p} : Set ℕ) G) :=
    Ch04.isPGroup_of_isPiGroup_singleton (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))
  have hOpF : Ch03.oPiCore ({p} : Set ℕ) G ≤ Ch01.fitting G := by
    haveI : Group.IsNilpotent ↥(Ch03.oPiCore ({p} : Set ℕ) G) := hOpPG.isNilpotent
    exact Ch01.nilpotent_normal_le_fitting
  haveI hNnil : Group.IsNilpotent ↥N := isNilpotent_of_le_of_isNilpotent hNF inferInstance
  -- Step 1: `O_p(G)` centralizes `N`, both lying in the nilpotent `F(G)` with coprime orders.
  have hOpcentN : ∀ a ∈ Ch03.oPiCore ({p} : Set ℕ) G, ∀ n ∈ N, Commute a n := by
    intro a ha n hn
    refine commute_of_mem_fitting_of_coprime_orderOf (hOpF ha) (hNF hn) ?_
    obtain ⟨k, hk⟩ := hOpPG ⟨a, ha⟩
    have hadvd : orderOf a ∣ p ^ k := by
      rw [← orderOf_mk_eq ha]; exact orderOf_dvd_of_pow_eq_one hk
    have hnp : ¬ p ∣ orderOf n := fun hdvd =>
      hpN (hdvd.trans (by rw [← orderOf_mk_eq hn]; exact orderOf_dvd_natCard _))
    exact Nat.Coprime.coprime_dvd_left hadvd
      (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnp))
  -- Step 2: Lemma 1.2 upgrades this to a whole Sylow `p`-subgroup of `G`.
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hOpne
  have hx1 : (x : G) ≠ 1 := fun h => hxne (Subtype.ext h)
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hOpP : Ch03.oPiCore ({p} : Set ℕ) G ≤ (P : Subgroup G) := by
    rw [Ch04.oPiCore_singleton_eq_opCore]; exact Ch01.opCore_le P
  have hPcentN : ∀ a ∈ (P : Subgroup G), ∀ n ∈ N, Commute a n := by
    intro a ha n hn
    have hmem : (⟨n, hn⟩ : ↥N) ∈ ⨆ r : (Nat.card ↥N).primeFactors,
        ((default : Sylow (r : ℕ) ↥N) : Subgroup ↥N) := by
      rw [Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥N]; trivial
    refine Subgroup.iSup_induction _ (C := fun w : ↥N => Commute a (w : G)) hmem ?_
      (Commute.one_right _) (fun u v hu hv => hu.mul_right hv)
    rintro ⟨r, hr⟩ w hw
    haveI : Fact (r : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
    have hrp : (r : ℕ) ≠ p := fun h => hpN (h ▸ Nat.dvd_of_mem_primeFactors hr)
    rcases eq_or_ne (w : G) 1 with hw1 | hw1
    · rw [hw1]; exact Commute.one_right a
    · have hQpg : IsPGroup (r : ℕ)
          ↥(((default : Sylow (r : ℕ) ↥N) : Subgroup ↥N).map N.subtype) :=
        (default : Sylow (r : ℕ) ↥N).isPGroup'.map N.subtype
      have hwQ : (w : G) ∈ ((default : Sylow (r : ℕ) ↥N) : Subgroup ↥N).map N.subtype :=
        ⟨w, hw, rfl⟩
      exact commute_of_cn_of_commute_ne_one hCN (Ne.symm hrp) P.isPGroup' hQpg
        (hOpP x.2) hx1 hwQ hw1 (hOpcentN _ x.2 _ w.2) a ha (w : G) hwQ
  -- Step 3: `C = C_G(N)` is normal and nilpotent, and contains `P`.
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer (N : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun n hn => (hPcentN a ha n hn).symm.eq
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
  have hz1 : (z : G) ≠ 1 := fun h => hzne (Subtype.ext h)
  haveI hCnil : Group.IsNilpotent ↥(Subgroup.centralizer (N : Set G)) :=
    isNilpotent_of_le_of_isNilpotent
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr z.2)) (hCN (z : G) hz1)
  -- Step 4: `P` is Sylow in the nilpotent `C`, hence characteristic there, hence normal in `G`.
  haveI hPn : ((P.subtype hPC : Sylow p ↥(Subgroup.centralizer (N : Set G))) :
      Subgroup ↥(Subgroup.centralizer (N : Set G))).Normal :=
    Ch01.Sylow.normal_of_isNilpotent _
  haveI hPc : ((P.subtype hPC : Sylow p ↥(Subgroup.centralizer (N : Set G))) :
      Subgroup ↥(Subgroup.centralizer (N : Set G))).Characteristic :=
    Sylow.characteristic_of_normal _ hPn
  haveI hPnormal : (P : Subgroup G).Normal := by
    have hmap := normal_map_subtype_of_characteristic hPc
    rwa [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPC] at hmap
  -- Step 5: a normal `p`-subgroup lies in `O_p(G)`, so `P = O_p(G)`.
  exact ⟨P, le_antisymm (Ch04.isPiGroup_singleton_of_isPGroup P.isPGroup').le_oPiCore hOpP⟩


end OddOrder.GroupTheory
