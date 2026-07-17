/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Nilpotent
import OddOrder.Isaacs.Ch05_Transfer.Basic

/-!
# Isaacs Thm 5.24: nilpotent maximal subgroups of simple groups (p. 172)

**Isaacs, _Finite Group Theory_ (AMS GSM 92), §5D, p. 172.**

**Theorem 5.24**: if `G` is a finite simple group and `H ≤ G` is a maximal subgroup that is
nilpotent, then `H` is a `p`-group for some prime `p`.

## Proof outline (the book's proof)

Assume distinct primes `p ≠ q` divide `|H|`.

1. `P ∈ Syl_p(H)` is normal in `H` (nilpotency), nontrivial, and not normal in `G`
   (simplicity), so `H ≤ N_G(P) < G` and maximality forces `H = N_G(P)`.
2. `P ∈ Syl_p(G)` (`exists_sylow_coe_eq_of_normalizer_le`): otherwise `P < S` for a Sylow
   `S` of `G`, and since normalizers grow in `p`-groups some `x ∈ S \ P` normalizes `P`,
   making `S ⊓ H` a `p`-subgroup of `H` strictly above the Sylow subgroup `P` of `H`.
   Steps 1-2 are packaged per prime in `sylowSetup` below.
3. Likewise `H = N_G(Q)` with `Q ∈ Syl_q(G)`.  By **Lemma 5.12**
   (`normalizer_controls_centralizer_fusion`) `H = N_G(Q)` controls `G`-fusion in
   `C_G(Q) ⊇ P` (`P ≤ C_G(Q)` since `P, Q ⊴ H` are disjoint), so `H` controls `G`-fusion
   in `P`.
4. **Cor 5.22** (`APrime_eq_subgroupOf_APrime_of_controlsFusionIn`) gives
   `A^p(H) = H ∩ A^p(G)`.  Since `H` is nilpotent with `p ∣ |H|`, `A^p(H) < H`
   (`APrime_lt_top_of_isNilpotent_of_prime_dvd_card`), so `A^p(G) < G`; simplicity forces
   `A^p(G) = ⊥`, making `|G| = |G : A^p(G)|` a power of `p` — contradicting `q ∣ |G|`.

## Main results

- `OddOrder.Isaacs.Ch05.APrime_lt_top_of_isNilpotent_of_prime_dvd_card`: for finite
  nilpotent `H` with `p ∣ |H|`, `A^p(H) < H`.
- `OddOrder.Isaacs.Ch05.exists_sylow_coe_eq_of_normalizer_le`: a maximal `p`-subgroup of
  `H ≤ G` whose `G`-normalizer lies in `H` is a full Sylow `p`-subgroup of `G`.
- `OddOrder.Isaacs.Ch05.exists_isPGroup_of_isCoatom_of_isNilpotent`: **Isaacs Thm 5.24**.
-/

namespace OddOrder.Isaacs.Ch05

open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 5D: Thm 5.24 (p. 172) -/

/-- For a finite nilpotent group `H` and a prime `p ∣ |H|`, `A^p(H) < H`.

Isaacs p. 172 argues `O^p(H) < H` and that the nontrivial `p`-group `H/O^p(H)` has a
nontrivial abelian image; we instead compose the (nilpotent) direct-product projection of
`H` onto its normal Sylow `p`-subgroup `P` with `P → P/P'`: the kernel is a proper normal
subgroup containing `H'` of `p`-power index, so it bounds `A^p(H)` strictly below `⊤`. -/
theorem APrime_lt_top_of_isNilpotent_of_prime_dvd_card
    {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H]
    {p : ℕ} [hp : Fact p.Prime] (hpH : p ∣ Nat.card H) :
    APrime p H < ⊤ := by
  classical
  have hcard_ne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hp_mem : p ∈ (Nat.card H).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp.out, hpH, hcard_ne⟩
  -- direct-product decomposition into the (normal) Sylow subgroups
  let e := Sylow.directProductOfNormal (G := H) fun {q} _ Q => inferInstance
  set P : Sylow p H := default with hP_def
  -- projection onto the abelianization of the `p`-component
  let π₁ : (∀ q : (Nat.card H).primeFactors, ∀ Q : Sylow (q : ℕ) H, ↥(Q : Subgroup H)) →*
      (∀ Q : Sylow p H, ↥(Q : Subgroup H)) :=
    Pi.evalMonoidHom (fun q : (Nat.card H).primeFactors =>
      ∀ Q : Sylow (q : ℕ) H, ↥(Q : Subgroup H)) ⟨p, hp_mem⟩
  let π₂ : (∀ Q : Sylow p H, ↥(Q : Subgroup H)) →* ↥(P : Subgroup H) :=
    Pi.evalMonoidHom (fun Q : Sylow p H => ↥(Q : Subgroup H)) P
  let f : H →* Abelianization ↥(P : Subgroup H) :=
    (Abelianization.of.comp (π₂.comp π₁)).comp e.symm.toMonoidHom
  -- `f` is surjective: hit the class of `y` from `e (mulSingle (mulSingle y))`
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨y, hy⟩ := Quot.exists_rep x
    set v₂ : ∀ Q : Sylow p H, ↥(Q : Subgroup H) := Pi.mulSingle P y with hv₂
    set v₁ : ∀ q : (Nat.card H).primeFactors, ∀ Q : Sylow (q : ℕ) H, ↥(Q : Subgroup H) :=
      Pi.mulSingle ⟨p, hp_mem⟩ v₂ with hv₁
    refine ⟨e v₁, ?_⟩
    change Abelianization.of (π₂ (π₁ (e.symm (e v₁)))) = x
    rw [MulEquiv.symm_apply_apply]
    change Abelianization.of (v₁ ⟨p, hp_mem⟩ P) = x
    rw [hv₁, Pi.mulSingle_eq_same, hv₂, Pi.mulSingle_eq_same]
    exact (Abelianization.mk_eq_of y).symm.trans hy
  -- commutator ≤ ker (abelian target)
  have hker_comm : commutator H ≤ f.ker := Abelianization.commutator_subset_ker f
  -- `[H : ker f] = |P/P'|`, a `p`-power
  have hindex : f.ker.index = Nat.card (Abelianization ↥(P : Subgroup H)) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf_surj]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  obtain ⟨m, hm⟩ : ∃ m, Nat.card (Abelianization ↥(P : Subgroup H)) = p ^ m := by
    have hdvd : Nat.card (Abelianization ↥(P : Subgroup H)) ∣ Nat.card ↥(P : Subgroup H) :=
      Subgroup.card_quotient_dvd_card _
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hn] at hdvd
    obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    exact ⟨m, hm⟩
  -- `P` is nontrivial (`p ∣ |H|`), so its abelianization is nontrivial (nilpotent group)
  have hab_ne : Nat.card (Abelianization ↥(P : Subgroup H)) ≠ 1 := by
    have hP_card : 1 < Nat.card ↥(P : Subgroup H) := by
      rw [P.card_eq_multiplicity]
      exact Nat.one_lt_pow (hp.out.factorization_pos_of_dvd hcard_ne hpH).ne' hp.out.one_lt
    haveI : Nontrivial ↥(P : Subgroup H) := Finite.one_lt_card_iff_nontrivial.mp hP_card
    haveI : Group.IsNilpotent ↥(P : Subgroup H) := P.isPGroup'.isNilpotent
    have hcomm_lt : commutator ↥(P : Subgroup H) < ⊤ :=
      IsSolvable.commutator_lt_top_of_nontrivial _
    intro hcard1
    have hidx : (commutator ↥(P : Subgroup H)).index = 1 := hcard1
    exact hcomm_lt.ne (Subgroup.index_eq_one.mp hidx)
  -- assemble: `A^p(H) ≤ ker f < ⊤`
  have hker_lt : f.ker < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hab_ne ?_
    rw [← hindex, htop, Subgroup.index_top]
  exact lt_of_le_of_lt (APrime_le inferInstance hker_comm (hindex.trans hm)) hker_lt

/-- **Sylow promotion** (Isaacs p. 172, step of Thm 5.24): let `P ≤ H ≤ G` be a
maximal `p`-subgroup of `H` (in the sense of `hmaxP`), and suppose `N_G(P) ≤ H`.  Then `P`
is a full Sylow `p`-subgroup of `G`.

Otherwise `P < S` for some Sylow `S` of `G`, and since normalizers grow in the `p`-group
`S` (Isaacs Thm 1.22), some `x ∈ S \ P` normalizes `P`; then `x ∈ N_G(P) ≤ H` puts the
`p`-subgroup `S ⊓ H` of `H` strictly above `P`. -/
theorem exists_sylow_coe_eq_of_normalizer_le
    [Finite G] {p : ℕ} [Fact p.Prime] {H P : Subgroup G}
    (hP : IsPGroup p P) (hPH : P ≤ H)
    (hmaxP : ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ H → P ≤ Q → Q = P)
    (hN : Subgroup.normalizer (P : Set G) ≤ H) :
    ∃ S : Sylow p G, (S : Subgroup G) = P := by
  obtain ⟨S, hle⟩ := hP.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : P < (S : Subgroup G) := hle.lt_of_ne fun h => hne h.symm
  -- `P.subgroupOf S` is proper, so its normalizer in the `p`-group `S` grows
  have hlt_top : P.subgroupOf (S : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hlt.not_ge (Subgroup.subgroupOf_eq_top.mp htop)
  haveI : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  obtain ⟨x, hx_norm, hx_not⟩ :=
    SetLike.exists_of_lt (Ch01.lt_normalizer_of_isNilpotent_of_lt_top hlt_top)
  -- `x` normalizes `P` in `G`
  have hxG_norm : (x : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhS : h ∈ (S : Subgroup G) := hle hh
      have hmem : (⟨h, hhS⟩ : ↥(S : Subgroup G)) ∈ P.subgroupOf (S : Subgroup G) :=
        Subgroup.mem_subgroupOf.mpr hh
      exact Subgroup.mem_subgroupOf.mp
        ((Subgroup.mem_normalizer_iff.mp hx_norm ⟨h, hhS⟩).mp hmem)
    · intro hh
      have hconjS : (x : G) * h * (x : G)⁻¹ ∈ (S : Subgroup G) := hle hh
      have hhS : h ∈ (S : Subgroup G) := by
        have heq : h = (x : G)⁻¹ * ((x : G) * h * (x : G)⁻¹) * (x : G) := by group
        rw [heq]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) hconjS) x.2
      have hmem : x * (⟨h, hhS⟩ : ↥(S : Subgroup G)) * x⁻¹ ∈ P.subgroupOf (S : Subgroup G) :=
        Subgroup.mem_subgroupOf.mpr hh
      exact Subgroup.mem_subgroupOf.mp
        ((Subgroup.mem_normalizer_iff.mp hx_norm ⟨h, hhS⟩).mpr hmem)
  -- so `x ∈ H`, and `S ⊓ H` is a `p`-subgroup of `H` strictly above `P`
  have hxH : (x : G) ∈ H := hN hxG_norm
  have hSH_eq : (S : Subgroup G) ⊓ H = P :=
    hmaxP _ (S.isPGroup'.to_le inf_le_left) inf_le_right (le_inf hle hPH)
  exact hx_not (Subgroup.mem_subgroupOf.mpr (hSH_eq ▸ Subgroup.mem_inf.mpr ⟨x.2, hxH⟩))

variable [Finite G]

/-- Per-prime setup for **Isaacs Thm 5.24**: for `H` a nilpotent maximal subgroup of the
finite simple group `G` and a prime `r ∣ |H|`, the image `P` in `G` of a Sylow
`r`-subgroup of `H` is a full Sylow `r`-subgroup of `G` and `H = N_G(P)`. -/
private lemma sylowSetup (hSimp : IsSimpleGroup G) {H : Subgroup G}
    (hmax : IsCoatom H) (hnilp : Group.IsNilpotent ↥H)
    {r : ℕ} [hr : Fact r.Prime] (hrH : r ∣ Nat.card ↥H) (P₀ : Sylow r ↥H) :
    ∃ S : Sylow r G, (S : Subgroup G) = (P₀ : Subgroup ↥H).map H.subtype ∧
      H = Subgroup.normalizer (((P₀ : Subgroup ↥H).map H.subtype : Subgroup G) : Set G) := by
  haveI := hnilp
  set P' : Subgroup G := (P₀ : Subgroup ↥H).map H.subtype with hP'_def
  have hP'_le_H : P' ≤ H := Subgroup.map_subtype_le _
  have hP'_pgroup : IsPGroup r P' := P₀.isPGroup'.map H.subtype
  -- (1) `P' ≠ ⊥` since `r ∣ |H|`
  have hP'_ne_bot : P' ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥P' = Nat.card ↥(P₀ : Subgroup ↥H) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective _ _ H.subtype_injective).toEquiv).symm
    rw [hbot, Subgroup.card_bot, P₀.card_eq_multiplicity] at hcard
    have hpos := hr.out.factorization_pos_of_dvd Nat.card_pos.ne' hrH
    exact absurd hcard.symm (Nat.one_lt_pow hpos.ne' hr.out.one_lt).ne'
  -- (2) `H ≤ N_G(P')` (the Sylow subgroup of the nilpotent `H` is normal in `H`)
  haveI hP₀_norm : (P₀ : Subgroup ↥H).Normal := inferInstance
  have hH_le_N : H ≤ Subgroup.normalizer (P' : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨g₀, hg₀, rfl⟩
      exact ⟨(⟨h, hh⟩ : ↥H) * g₀ * (⟨h, hh⟩ : ↥H)⁻¹, hP₀_norm.conj_mem g₀ hg₀ _, rfl⟩
    · rintro ⟨g₀, hg₀, hg₀eq⟩
      refine ⟨(⟨h, hh⟩ : ↥H)⁻¹ * g₀ * (⟨h, hh⟩ : ↥H), ?_, ?_⟩
      · have := hP₀_norm.conj_mem g₀ hg₀ (⟨h, hh⟩ : ↥H)⁻¹
        rwa [inv_inv] at this
      · have hg₀G : (g₀ : G) = h * g * h⁻¹ := hg₀eq
        change (((⟨h, hh⟩ : ↥H)⁻¹ * g₀ * ⟨h, hh⟩ : ↥H) : G) = g
        simp only [MulMemClass.coe_mul, InvMemClass.coe_inv, hg₀G]
        group
  -- (3) `N_G(P') ≠ ⊤`: else `P'` is normal in the simple `G`, impossible
  have hN_ne_top : Subgroup.normalizer (P' : Set G) ≠ ⊤ := by
    intro htop
    have hnormal : P'.Normal := by
      constructor
      intro n hn g
      have hg : g ∈ Subgroup.normalizer (P' : Set G) := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
    rcases hSimp.eq_bot_or_eq_top_of_normal P' hnormal with hbot | htop'
    · exact hP'_ne_bot hbot
    · exact hmax.1 (top_le_iff.mp (htop' ▸ hP'_le_H))
  -- (4) maximality: `H = N_G(P')`
  have hH_eq_N : H = Subgroup.normalizer (P' : Set G) := by
    rcases hH_le_N.lt_or_eq with hlt | heq
    · exact absurd (hmax.2 _ hlt) hN_ne_top
    · exact heq
  -- (5) `P'` is a maximal `p`-subgroup of `H` (transport `P₀.is_maximal'` along `map`)
  have hmaxP : ∀ Q : Subgroup G, IsPGroup r Q → Q ≤ H → P' ≤ Q → Q = P' := by
    intro Q hQp hQH hPQ
    have h1 : IsPGroup r (Q.subgroupOf H) :=
      hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
    have h2 : (P₀ : Subgroup ↥H) ≤ Q.subgroupOf H := by
      intro y hy
      exact Subgroup.mem_subgroupOf.mpr (hPQ ⟨y, hy, rfl⟩)
    have h3 := P₀.is_maximal' h1 h2
    calc Q = (Q.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hQH).symm
    _ = P' := by rw [h3]
  -- (6) promote to a Sylow subgroup of `G`
  obtain ⟨S, hS⟩ :=
    exists_sylow_coe_eq_of_normalizer_le hP'_pgroup hP'_le_H hmaxP hH_eq_N.ge
  exact ⟨S, hS, hH_eq_N⟩

/-- **Isaacs Thm 5.24** (p. 172): a nilpotent maximal subgroup `H` of a finite simple
group `G` is a `p`-group for some prime `p`. -/
theorem exists_isPGroup_of_isCoatom_of_isNilpotent
    (hSimp : IsSimpleGroup G) {H : Subgroup G}
    (hmax : IsCoatom H) (hnilp : Group.IsNilpotent ↥H) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥H := by
  classical
  haveI := hnilp
  -- key step: two primes dividing `|H|` must coincide
  have hkey : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ Nat.card ↥H → q ∣ Nat.card ↥H → p = q := by
    intro p q hp hq hpH hqH
    by_contra hpq
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨S, hS, hHP⟩ := sylowSetup hSimp hmax hnilp hpH (default : Sylow p ↥H)
    obtain ⟨T, hT, hHQ⟩ := sylowSetup hSimp hmax hnilp hqH (default : Sylow q ↥H)
    set P₀ : Sylow p ↥H := default
    set Q₀ : Sylow q ↥H := default
    -- `P ≤ C_G(Q)`: the disjoint normal subgroups `P₀, Q₀ ⊴ H` commute elementwise
    have hPC : (S : Subgroup G) ≤ Subgroup.centralizer ((T : Subgroup G) : Set G) := by
      rw [hS, hT]
      rintro _ ⟨x₀, hx₀, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y₀, hy₀, rfl⟩
      have hdisj : Disjoint (Q₀ : Subgroup ↥H) (P₀ : Subgroup ↥H) :=
        IsPGroup.disjoint_of_ne q p (Ne.symm hpq) _ _ Q₀.isPGroup' P₀.isPGroup'
      have hcomm :=
        Subgroup.commute_of_normal_of_disjoint _ _ inferInstance inferInstance hdisj
          y₀ x₀ hy₀ hx₀
      exact congrArg Subtype.val hcomm
    -- `H` controls `G`-fusion in `P` (Lemma 5.12 for `Q`, restricted to `P ≤ C_G(Q)`)
    have hFusion : H.ControlsFusionIn (S : Subgroup G) := by
      rintro x y hx hy ⟨g, hg⟩
      obtain ⟨n, hn, hnxy⟩ :=
        normalizer_controls_centralizer_fusion T (hPC hx) (hPC hy) hg
      refine ⟨n, ?_, hnxy⟩
      rw [hHQ, ← hT]
      exact hn
    -- Cor 5.22 + the nilpotent bound force `A^p(G) < G`
    have hS_le_H : (S : Subgroup G) ≤ H := by
      rw [hS]; exact Subgroup.map_subtype_le _
    have h522 := APrime_eq_subgroupOf_APrime_of_controlsFusionIn S hS_le_H hFusion
    have hlt : APrime p ↥H < ⊤ := APrime_lt_top_of_isNilpotent_of_prime_dvd_card hpH
    have hA_ne_top : APrime p G ≠ ⊤ := by
      intro htop
      rw [h522, htop, Subgroup.top_subgroupOf] at hlt
      exact lt_irrefl _ hlt
    -- simplicity: `A^p(G) = ⊥`, so `|G|` is a `p`-power — contradicting `q ∣ |G|`
    rcases hSimp.eq_bot_or_eq_top_of_normal (APrime p G) inferInstance with hbot | htop
    swap
    · exact hA_ne_top htop
    obtain ⟨k, hk⟩ := APrime_index_isPGroup p G
    rw [hbot, Subgroup.index_bot] at hk
    have hqG : q ∣ Nat.card G := hqH.trans (Subgroup.card_subgroup_dvd_card H)
    rw [hk] at hqG
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqG)).symm
  -- conclude: `|H|` is a prime power
  rcases eq_or_ne (Nat.card ↥H) 1 with h1 | h1
  · exact ⟨2, Nat.prime_two, IsPGroup.of_card (by rw [h1, pow_zero])⟩
  · have hp : (Nat.card ↥H).minFac.Prime := Nat.minFac_prime h1
    refine ⟨_, hp, IsPGroup.of_card
      (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdd =>
        hkey d _ hd hp hdd (Nat.minFac_dvd _))⟩

end

end OddOrder.Isaacs.Ch05
