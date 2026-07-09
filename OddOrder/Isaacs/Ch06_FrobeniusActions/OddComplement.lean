/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.GroupTheory.ElementaryAbelian
import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
# Odd Frobenius complements: prime-order subgroups are normal (Huppert V.8.18 b)

This file proves the structural fact used by Peterfalvi (13.17.c):

> **Huppert, *Endliche Gruppen I*, Kapitel V, Satz 8.18 b):** in a Frobenius complement of
> **odd order**, every subgroup of prime order is normal.

We work with the action-based form of a Frobenius complement, `IsFrobeniusAction A U`
(the complement `A` acting fixed-point-freely on the kernel `U`).  The proof is internal
to the complement `A` and uses the Frobenius hypothesis only through the
order-`pq` cyclicity fact `false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime`
(Isaacs Thm 6.9): a Frobenius actor contains no non-cyclic subgroup of order `p q`.

## Proof outline

Let `A` be a finite Frobenius complement of odd order.

1. **`A` is a Z-group** (`isZGroup_of_isFrobeniusAction_of_odd`).  Each Sylow `p`-subgroup
   has a unique subgroup of order `p` (Isaacs Cor 6.10), and `p` is odd, so it is cyclic
   (Isaacs Thm 6.11).  Hence (mathlib `IsZGroup`) `N := commutator A` is cyclic, normal,
   `A ⧸ N` is cyclic, and `(|N|, [A : N]) = 1`.

2. **Centralizing the commutator** (`centralizes_commutator_of_card_prime_coprime`).  If
   `R ≤ A` has prime order `r` with `r ∤ |N|`, then `R` centralizes `N`.  Indeed `R` acts
   coprimely on the cyclic abelian group `N`, so `C_N(R) ⊓ [N, R] = ⊥`.  If `[N, R] ≠ ⊥`,
   its unique subgroup `S` of some prime order `s` is `R`-invariant with `C_S(R) = ⊥`, so
   `R ⊔ S` is a non-cyclic subgroup of `A` of order `r s` — impossible in a Frobenius
   complement.

3. **Uniqueness and normality** (`unique_card_prime_of_isFrobeniusAction_of_odd`,
   `normal_of_card_prime_of_isFrobeniusAction_of_odd`).  `R` is the unique subgroup of
   order `r` in `A`: if `r ∣ |N|` both order-`r` subgroups lie in the cyclic `N`; if
   `r ∤ |N|` both centralize `N` and lie over the unique order-`r` subgroup of the cyclic
   `A ⧸ N`.  A unique subgroup of its order is characteristic, hence normal.
-/

namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative
open scoped commutatorElement
open OddOrder.Isaacs.Ch04

/-- Local copy (below `OddOrder.BG`): if `M` is normal and `T ⊓ M = ⊥`, then
`|T ⊔ M| = |T| · |M|`.  (Standard second-isomorphism counting.) -/
private theorem card_sup_eq_card_mul_card_of_disjoint_normal'
    {G : Type*} [Group G] [Finite G] {T M : Subgroup G} [M.Normal] (h_disj : T ⊓ M = ⊥) :
    Nat.card ↥(T ⊔ M) = Nat.card ↥T * Nat.card ↥M := by
  have hMT_bot : M.subgroupOf T = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, Subgroup.disjoint_def]
    intro x hxM hxT
    have hx : x ∈ T ⊓ M := ⟨hxT, hxM⟩
    rwa [h_disj, Subgroup.mem_bot] at hx
  have hMT_card_one : Nat.card (M.subgroupOf T) = 1 := by rw [hMT_bot]; exact Subgroup.card_bot
  have hT_quot_card : Nat.card T = Nat.card (T ⧸ M.subgroupOf T) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf T)
    rw [hMT_card_one, mul_one] at this; exact this
  have h_iso := QuotientGroup.quotientInfEquivProdNormalQuotient T M
  have h_eq_TM : Nat.card ((T ⊔ M : Subgroup G) ⧸ (M.subgroupOf (T ⊔ M))) = Nat.card T := by
    rw [hT_quot_card]; exact (Nat.card_congr h_iso.toEquiv).symm
  have hM_sub_TM_card : Nat.card (M.subgroupOf (T ⊔ M : Subgroup G)) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : M ≤ T ⊔ M)).toEquiv
  have h_card := Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf (T ⊔ M))
  rw [h_eq_TM, hM_sub_TM_card] at h_card
  exact h_card

/-- Local copy (below `OddOrder.BG`): if `A` normalizes `B` and `A ⊓ B = ⊥`, then
`|A ⊔ B| = |A| · |B|`. -/
private theorem card_sup_eq_mul_of_le_normalizer_of_disjoint'
    {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hdisj : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hAle : A ≤ A ⊔ B := le_sup_left
  have hBle : B ≤ A ⊔ B := le_sup_right
  haveI hBn : (B.subgroupOf (A ⊔ B)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have hdisj' : A.subgroupOf (A ⊔ B) ⊓ B.subgroupOf (A ⊔ B) = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hxA hxB
    have hxAB : (x : G) ∈ A ⊓ B := ⟨hxA, hxB⟩
    rw [hdisj, Subgroup.mem_bot] at hxAB
    rw [Subgroup.mem_bot]; exact Subtype.ext hxAB
  have htop : A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAle hBle, Subgroup.subgroupOf_self]
  have h := card_sup_eq_card_mul_card_of_disjoint_normal'
    (T := A.subgroupOf (A ⊔ B)) (M := B.subgroupOf (A ⊔ B)) hdisj'
  rw [htop, Nat.card_congr (Subgroup.topEquiv).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv] at h
  exact h

/-- In a finite cyclic group, a subgroup of prime order is unique: two subgroups of the same
prime order `q` coincide.  (`H ⊔ K` is elementary abelian of exponent `q` and cyclic, hence of
order dividing `q`, forcing `H = H ⊔ K = K`.)  Local copy for use below `OddOrder.BG`. -/
theorem eq_of_card_eq_prime_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {q : ℕ} (hq : q.Prime) {H K : Subgroup C}
    (hH : Nat.card ↥H = q) (hK : Nat.card ↥K = q) : H = K := by
  haveI : Fact q.Prime := ⟨hq⟩
  letI : CommGroup C := IsCyclic.commGroup
  have hHel : H.IsElementaryAbelian q := Subgroup.IsElementaryAbelian.of_card_prime hH
  have hKel : K.IsElementaryAbelian q := Subgroup.IsElementaryAbelian.of_card_prime hK
  have hcent : H ≤ Subgroup.centralizer (K : Set C) := fun x _ =>
    Subgroup.mem_centralizer_iff.mpr (fun y _ => mul_comm y x)
  have hsupel : (H ⊔ K).IsElementaryAbelian q := hHel.sup_of_le_centralizer hKel hcent
  haveI : IsCyclic ↥(H ⊔ K) := inferInstance
  have hexp : Monoid.exponent ↥(H ⊔ K) ∣ q :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun x => hsupel.2 x)
  have hcarddvd : Nat.card ↥(H ⊔ K) ∣ q := by rwa [IsCyclic.exponent_eq_card] at hexp
  have hcardle : Nat.card ↥(H ⊔ K) ≤ q := Nat.le_of_dvd hq.pos hcarddvd
  have hHK : H = H ⊔ K := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hH]; exact hcardle)
  have hKK : K = H ⊔ K := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hK]; exact hcardle)
  exact hHK.trans hKK.symm

variable {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
  [MulDistribMulAction A U]

/-- **Step 1.** A finite Frobenius complement of odd order is a Z-group: every Sylow subgroup
is cyclic.  Each Sylow `p`-subgroup has a unique subgroup of order `p` (Isaacs Cor 6.10,
`subgroups_card_prime_unique_of_frobeniusAction_sylow`) and `p` is odd, so it is cyclic
(Isaacs Thm 6.11, `isCyclic_of_subgroups_card_prime_unique_of_odd`). -/
theorem isZGroup_of_isFrobeniusAction_of_odd
    (hFrob : IsFrobeniusAction A U) (hodd : Odd (Nat.card A)) :
    IsZGroup A := by
  refine ⟨fun p hp P => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hpA : p ∣ Nat.card A
  · -- `p` is an odd prime dividing `|A|`; the Sylow `p`-subgroup is cyclic.
    have hp_ne_two : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hpA
      obtain ⟨m, hm⟩ := hodd
      omega
    have hp_odd : Odd p := hp.odd_of_ne_two hp_ne_two
    exact isCyclic_of_subgroups_card_prime_unique_of_odd P.isPGroup' hp_odd
      (subgroups_card_prime_unique_of_frobeniusAction_sylow hFrob P)
  · -- `p ∤ |A|` forces the Sylow `p`-subgroup to be trivial, hence cyclic.
    have hcard : Nat.card P = 1 := by
      rcases P.isPGroup'.card_eq_or_dvd with h1 | hd
      · exact h1
      · exact absurd (hd.trans (Subgroup.card_subgroup_dvd_card P.toSubgroup)) hpA
    haveI : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact isCyclic_of_subsingleton

/-- **Step 2.** In a finite Frobenius complement `A` of odd order, a subgroup `R` of prime
order `r` not dividing `|A'|` (`A' = commutator A`) centralizes `A'`.

`A` is a Z-group (Step 1), so `A'` is cyclic and normal.  `R` acts coprimely on the abelian
`A'`, giving `C_{A'}(R) ⊓ [A', R] = ⊥`.  If `R` did **not** centralize `A'`, then `[A', R] ≠ ⊥`
contains a subgroup `S` of some prime order `s` (unique in the cyclic `A'`, hence `R`-invariant)
with `C_S(R) = ⊥`; then `R ⊔ S` is a **non-cyclic** subgroup of `A` of order `r s`, contradicting
Isaacs Thm 6.9 (`false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime`). -/
theorem centralizes_commutator_of_card_prime_coprime
    (hFrob : IsFrobeniusAction A U) (hodd : Odd (Nat.card A))
    {R : Subgroup A} {r : ℕ} (hr : r.Prime) (hRcard : Nat.card ↥R = r)
    (hrN : ¬ r ∣ Nat.card ↥(commutator A)) :
    R ≤ Subgroup.centralizer ((commutator A : Subgroup A) : Set A) := by
  haveI hZ : IsZGroup A := isZGroup_of_isFrobeniusAction_of_odd hFrob hodd
  haveI hNcyc : IsCyclic ↥(commutator A) := IsZGroup.isCyclic_commutator (G := A)
  haveI hNnorm : (commutator A).Normal := inferInstance
  letI : CommGroup ↥(commutator A) := IsCyclic.commGroup
  -- conjugation action of `R` on the cyclic normal commutator subgroup
  set φ : ↥R →* MulAut ↥(commutator A) :=
    (MulAut.conjNormal (H := commutator A)).comp R.subtype with hφ
  have hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥(commutator A)) := by
    rw [hRcard]; exact (Nat.Prime.coprime_iff_not_dvd hr).mpr hrN
  -- it suffices to show `R` acts trivially on `commutator A`
  suffices hac : actionCommutator φ = ⊥ by
    rw [actionCommutator_eq_bot_iff_acts_trivially] at hac
    intro ρ hρ
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := hac ⟨ρ, hρ⟩ ⟨n, hn⟩
    have h2 : ρ * n * ρ⁻¹ = n := by
      have := congrArg (Subgroup.subtype (commutator A)) h1
      simpa [hφ, MulAut.conjNormal_apply] using this
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  by_contra hbot
  have hinf : Subgroup.fixedPointsOfMulAut φ ⊓ actionCommutator φ = ⊥ :=
    fixedPoints_inf_actionCommutator_eq_bot_of_abelian φ hcop
  -- a prime `s ∣ |[A', R]|`
  have hcard_ne : Nat.card ↥(actionCommutator φ) ≠ 1 := fun h1 =>
    hbot (Subgroup.card_eq_one.mp h1)
  obtain ⟨s, hs, hsdvd⟩ := Nat.exists_prime_and_dvd hcard_ne
  haveI : Fact s.Prime := ⟨hs⟩
  haveI : Fintype ↥(actionCommutator φ) := Fintype.ofFinite _
  obtain ⟨y, hy_ord⟩ := exists_prime_orderOf_dvd_card (G := ↥(actionCommutator φ)) s
    (by rwa [Nat.card_eq_fintype_card] at hsdvd)
  -- the order-`s` subgroup `S ≤ commutator A` inside `[A', R]`
  set x : ↥(commutator A) := (actionCommutator φ).subtype y with hxdef
  have hx_ord : orderOf x = s := by
    rw [hxdef, orderOf_injective (actionCommutator φ).subtype Subtype.coe_injective y]; exact hy_ord
  have hx_mem : x ∈ actionCommutator φ := by rw [hxdef]; exact y.2
  set S : Subgroup ↥(commutator A) := Subgroup.zpowers x with hSdef
  have hScard : Nat.card ↥S = s := by rw [hSdef, Nat.card_zpowers, hx_ord]
  have hSle : S ≤ actionCommutator φ := (Subgroup.zpowers_le).mpr hx_mem
  -- `S` is `φ`-invariant (unique order-`s` subgroup of the cyclic `commutator A`)
  have hSinv : ∀ ρ : ↥R, S.map (φ ρ).toMonoidHom = S := by
    intro ρ
    have hmap : S.map (φ ρ).toMonoidHom = Subgroup.zpowers ((φ ρ) x) := by
      rw [hSdef, MonoidHom.map_zpowers]; rfl
    have hord : orderOf ((φ ρ) x) = s := by
      have h := orderOf_injective (φ ρ).toMonoidHom (φ ρ).injective x
      rw [hx_ord] at h; exact h
    rw [hmap]
    refine eq_of_card_eq_prime_of_isCyclic hs ?_ hScard
    rw [Nat.card_zpowers]; exact hord
  -- push `S` to the subgroup `S' ≤ commutator A ≤ A`
  set S' : Subgroup A := S.map (commutator A).subtype with hS'def
  have hS'card : Nat.card ↥S' = s := by
    rw [hS'def,
      Nat.card_congr (Subgroup.equivMapOfInjective S (commutator A).subtype
        Subtype.coe_injective).toEquiv.symm]
    exact hScard
  -- conjugation by `ρ ∈ R` keeps `S'` inside `S'`
  have hconj_mem : ∀ ρ ∈ R, ∀ a ∈ S', ρ * a * ρ⁻¹ ∈ S' := by
    intro ρ hρ a ha
    rw [hS'def, Subgroup.mem_map] at ha ⊢
    obtain ⟨n, hnS, rfl⟩ := ha
    refine ⟨φ ⟨ρ, hρ⟩ n, ?_, ?_⟩
    · have hinv := hSinv ⟨ρ, hρ⟩
      rw [← hinv]; exact Subgroup.mem_map_of_mem _ hnS
    · simp [hφ, MulAut.conjNormal_apply]
  have hRnorm : R ≤ Subgroup.normalizer (S' : Set A) := by
    intro ρ hρ
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hconj_mem ρ hρ a ha, fun ha => ?_⟩
    have hb := hconj_mem ρ⁻¹ (R.inv_mem hρ) (ρ * a * ρ⁻¹) ha
    simpa [mul_assoc] using hb
  -- `R ⊓ S' = ⊥` (distinct prime orders `r ≠ s`)
  have hsN : s ∣ Nat.card ↥(commutator A) :=
    hsdvd.trans (Subgroup.card_subgroup_dvd_card (actionCommutator φ))
  have hrs : r ≠ s := fun h => hrN (h ▸ hsN)
  have hdisj : R ⊓ S' = ⊥ := by
    have hcoprs : Nat.Coprime r s := (Nat.coprime_primes hr hs).mpr hrs
    have hdvdR : Nat.card ↥(R ⊓ S') ∣ r := hRcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hdvdS : Nat.card ↥(R ⊓ S') ∣ s := hS'card ▸ Subgroup.card_dvd_of_le inf_le_right
    have h1 : Nat.card ↥(R ⊓ S') = 1 := Nat.dvd_one.mp (hcoprs ▸ Nat.dvd_gcd hdvdR hdvdS)
    exact Subgroup.card_eq_one.mp h1
  -- `B := R ⊔ S'` is a subgroup of `A` of order `r s`
  set B : Subgroup A := R ⊔ S' with hBdef
  have hBcard : Nat.card ↥B = r * s := by
    rw [hBdef, card_sup_eq_mul_of_le_normalizer_of_disjoint' hRnorm hdisj, hRcard, hS'card]
  -- `B` is not cyclic: cyclicity forces `R` to centralize `S`, but `C_S(R) = ⊥`
  have hBnc : ¬ IsCyclic ↥B := by
    intro hcyc
    letI : CommGroup ↥B := IsCyclic.commGroup
    have hSfix : S ≤ Subgroup.fixedPointsOfMulAut φ := by
      intro n hnS
      rw [Subgroup.mem_fixedPointsOfMulAut]
      intro ρ
      have hnS' : (↑n : A) ∈ S' := by rw [hS'def]; exact Subgroup.mem_map_of_mem _ hnS
      have hρB : (↑ρ : A) ∈ B := hBdef ▸ Subgroup.mem_sup_left ρ.2
      have hnB : (↑n : A) ∈ B := hBdef ▸ Subgroup.mem_sup_right hnS'
      have hcomm : (↑ρ : A) * ↑n = ↑n * ↑ρ := by
        have := mul_comm (⟨↑ρ, hρB⟩ : ↥B) (⟨↑n, hnB⟩ : ↥B)
        exact congrArg (Subgroup.subtype B) this
      apply Subtype.ext
      simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
      rw [hcomm]; group
    have hSbot : S ≤ ⊥ := hinf ▸ le_inf hSfix hSle
    rw [le_bot_iff] at hSbot
    rw [hSbot, Subgroup.card_bot] at hScard
    exact hs.one_lt.ne' hScard.symm
  haveI : Fact r.Prime := ⟨hr⟩
  exact false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime hFrob B hBcard hBnc

/-- **Huppert, *Endliche Gruppen I*, Kapitel V, Satz 8.18 b):** in a Frobenius complement of
odd order, every subgroup of prime order is normal.

The complement `A` is a Z-group (Step 1), so `N := commutator A` is cyclic, normal, with
`A ⧸ N` cyclic and `(|N|, [A : N]) = 1`.  Let `R ≤ A` have prime order `r`.

*If `r ∣ |N|`:* every order-`r` subgroup lies in `N` (its image in the coprime quotient `A ⧸ N`
is trivial), and order-`r` subgroups of the cyclic `N` are unique, so every conjugate of `R`
equals `R`.

*If `r ∤ |N|`:* `R` centralizes `N` (Step 2).  For a conjugate `R^g` and `k = g r₀ g⁻¹ ∈ R^g`
(`r₀ ∈ R`), the element `ν := k r₀⁻¹ = ⁅g, r₀⁆` lies in `N`; as `r₀` centralizes `ν` and
`k^r = 1 = r₀^r`, we get `ν^r = 1`, so `ν = 1` by coprimality and `k = r₀ ∈ R`. -/
theorem normal_of_card_prime_of_isFrobeniusAction_of_odd
    (hFrob : IsFrobeniusAction A U) (hodd : Odd (Nat.card A))
    {R : Subgroup A} {r : ℕ} (hr : r.Prime) (hRcard : Nat.card ↥R = r) :
    R.Normal := by
  haveI hZ : IsZGroup A := isZGroup_of_isFrobeniusAction_of_odd hFrob hodd
  haveI hNcyc : IsCyclic ↥(commutator A) := IsZGroup.isCyclic_commutator (G := A)
  haveI hNnorm : (commutator A).Normal := inferInstance
  refine ⟨fun n hn g => ?_⟩
  -- it suffices to show the conjugate `R^g` is contained in `R`
  suffices hle : R.map (MulAut.conj g).toMonoidHom ≤ R by
    apply hle
    rw [Subgroup.mem_map]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
  set Rg : Subgroup A := R.map (MulAut.conj g).toMonoidHom with hRgdef
  have hRgcard : Nat.card ↥Rg = r := by
    rw [hRgdef, Nat.card_congr (Subgroup.equivMapOfInjective R (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv.symm]
    exact hRcard
  by_cases hrN : r ∣ Nat.card ↥(commutator A)
  · -- `r ∣ |N|`: both subgroups lie in the cyclic `N`, where order-`r` subgroups are unique
    have hcont : ∀ K : Subgroup A, Nat.card ↥K = r → K ≤ commutator A := by
      intro K hK
      have hcop : Nat.Coprime r (commutator A).index :=
        Nat.Coprime.coprime_dvd_left hrN (IsZGroup.coprime_commutator_index A)
      have hdvd1 : Nat.card ↥(K.map (QuotientGroup.mk' (commutator A))) ∣ r := by
        rw [← hK]
        exact @Subgroup.card_map_dvd A (A ⧸ commutator A) _ _ K
          (QuotientGroup.mk' (commutator A))
      have hdvd2 : Nat.card ↥(K.map (QuotientGroup.mk' (commutator A))) ∣ (commutator A).index := by
        have h := Subgroup.card_subgroup_dvd_card (K.map (QuotientGroup.mk' (commutator A)))
        rwa [← Subgroup.index_eq_card] at h
      have h1 : Nat.card ↥(K.map (QuotientGroup.mk' (commutator A))) = 1 :=
        Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd1 hdvd2)
      have hbot : K.map (QuotientGroup.mk' (commutator A)) = ⊥ := Subgroup.card_eq_one.mp h1
      intro x hx
      have hxmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (commutator A)) hx
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxmem
      exact hxmem
    have hRle : R ≤ commutator A := hcont R hRcard
    have hRgle : Rg ≤ commutator A := hcont Rg hRgcard
    have hRsub : Nat.card ↥(R.subgroupOf (commutator A)) = r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv]; exact hRcard
    have hRgsub : Nat.card ↥(Rg.subgroupOf (commutator A)) = r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRgle).toEquiv]; exact hRgcard
    have heq : R.subgroupOf (commutator A) = Rg.subgroupOf (commutator A) :=
      eq_of_card_eq_prime_of_isCyclic hr hRsub hRgsub
    have hRRg : R = Rg := by
      have h := Subgroup.subgroupOf_inj.mp heq
      rwa [inf_of_le_left hRle, inf_of_le_left hRgle] at h
    exact hRRg.ge
  · -- `r ∤ |N|`: `R` centralizes `N`; the commutator/coprimality argument forces `R^g ≤ R`
    have hRcent : R ≤ Subgroup.centralizer ((commutator A : Subgroup A) : Set A) :=
      centralizes_commutator_of_card_prime_coprime hFrob hodd hr hRcard hrN
    have hcoprN : Nat.Coprime r (Nat.card ↥(commutator A)) := (hr.coprime_iff_not_dvd).mpr hrN
    intro k hk
    have hkr : k ^ r = 1 := by
      have h : (⟨k, hk⟩ : ↥Rg) ^ r = 1 := by rw [← hRgcard]; exact pow_card_eq_one'
      have := congrArg (Subgroup.subtype Rg) h
      rwa [map_pow, map_one, Subgroup.coe_subtype] at this
    rw [hRgdef, Subgroup.mem_map] at hk
    obtain ⟨r₀, hr₀, hkval⟩ := hk
    simp [MulAut.conj_apply] at hkval
    have hr₀r : r₀ ^ r = 1 := by
      have h : (⟨r₀, hr₀⟩ : ↥R) ^ r = 1 := by rw [← hRcard]; exact pow_card_eq_one'
      have := congrArg (Subgroup.subtype R) h
      rwa [map_pow, map_one, Subgroup.coe_subtype] at this
    set ν : A := k * r₀⁻¹ with hνdef
    have hνN : ν ∈ commutator A := by
      have hνe : ν = ⁅g, r₀⁆ := by rw [hνdef, ← hkval, commutatorElement_def]
      rw [hνe]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top r₀)
    have hcomm : Commute ν r₀ := by
      have h := hRcent hr₀
      rw [Subgroup.mem_centralizer_iff] at h
      exact h ν hνN
    have hk_eq : k = ν * r₀ := by rw [hνdef]; group
    have hνr : ν ^ r = 1 := by
      have h := hcomm.mul_pow r
      rw [← hk_eq, hkr, hr₀r, mul_one] at h
      exact h.symm
    have hνord_r : orderOf ν ∣ r := orderOf_dvd_of_pow_eq_one hνr
    have hνord_N : orderOf ν ∣ Nat.card ↥(commutator A) := by
      have heq : orderOf ν = orderOf (⟨ν, hνN⟩ : ↥(commutator A)) :=
        orderOf_injective (commutator A).subtype Subtype.coe_injective ⟨ν, hνN⟩
      rw [heq]; exact orderOf_dvd_natCard _
    have hν1 : ν = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcoprN ▸ Nat.dvd_gcd hνord_r hνord_N))
    have : k = r₀ := by rw [hk_eq, hν1, one_mul]
    rw [this]; exact hr₀

/-- **Huppert V.8.18 b), subgroup-pair form.**  In a finite Frobenius group `G = N ⋊ A` whose
complement `A` has **odd order**, every subgroup `R ≤ A` of prime order is normal in `A`. -/
theorem normal_of_card_prime_of_isFrobeniusGroup_of_odd
    {G : Type*} [Group G] [Finite G] {N A : Subgroup G}
    (hFrob : IsFrobeniusGroup G N A) (hodd : Odd (Nat.card ↥A))
    {R : Subgroup ↥A} {r : ℕ} (hr : r.Prime) (hRcard : Nat.card ↥R = r) :
    R.Normal := by
  letI : N.Normal := hFrob.isNormal
  letI : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom ↥N ((MulAut.conjNormal (H := N)).comp A.subtype)
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hFrob.ne_bot_kernel
  exact normal_of_card_prime_of_isFrobeniusAction_of_odd hFrob.toFrobeniusAction hodd hr hRcard

/-- A conjugate `A^g` of the complement of a Frobenius group `G = N ⋊ A` is again a Frobenius
complement (the normal kernel `N` is fixed by conjugation).  Used to choose a complement
containing a prescribed kernel-disjoint subgroup. -/
theorem IsFrobeniusGroup.conjComplement {G : Type*} [Group G] [Finite G] {N A : Subgroup G}
    (h : IsFrobeniusGroup G N A) (g : G) :
    IsFrobeniusGroup G N (A.map (MulAut.conj g).toMonoidHom) := by
  haveI := h.isNormal
  have hAg_card : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv.symm
  -- `x ∈ A^g ↔ g⁻¹ x g ∈ A`.
  have hmem : ∀ x : G, x ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ A := by
    intro x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have : g⁻¹ * (MulAut.conj g).toMonoidHom b * g = b := by simp [MulAut.conj_apply]; group
      rwa [this]
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply]; group⟩
  have hNdisj : N ⊓ A = ⊥ := disjoint_iff.mp h.isComplement.disjoint
  refine ⟨h.isNormal, ?_, h.ne_bot_kernel, ?_, ?_⟩
  · -- `IsComplement' N A^g` via card and disjointness.
    rw [Subgroup.isComplement'_iff_card_mul_and_disjoint]
    refine ⟨by rw [hAg_card]; exact h.isComplement.card_mul, ?_⟩
    rw [Subgroup.disjoint_def]
    intro x hxN hxAg
    rw [hmem] at hxAg
    have hgxg : g⁻¹ * x * g ∈ N ⊓ A :=
      ⟨by simpa using h.isNormal.conj_mem x hxN g⁻¹, hxAg⟩
    rw [hNdisj, Subgroup.mem_bot] at hgxg
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, hgxg]; group
  · -- `A^g ≠ ⊥`.
    intro hbot
    exact h.ne_bot_complement (Subgroup.card_eq_one.mp (by rw [← hAg_card, hbot, Subgroup.card_bot]))
  · -- conjugation Frobenius for `A^g`, transferred along `g`.
    intro a haAg ha1 n hnN hn1 hfix
    rw [hmem] at haAg
    have hmN : g⁻¹ * n * g ∈ N := by simpa using h.isNormal.conj_mem n hnN g⁻¹
    have hb1 : g⁻¹ * a * g ≠ 1 := fun he => ha1 (by
      have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      rw [this, he]; group)
    have hm1 : g⁻¹ * n * g ≠ 1 := fun he => hn1 (by
      have : n = g * (g⁻¹ * n * g) * g⁻¹ := by group
      rw [this, he]; group)
    -- `a n a⁻¹ = n` transfers to `(g⁻¹ a g)(g⁻¹ n g)(g⁻¹ a g)⁻¹ = g⁻¹ n g`.
    have hbm : (g⁻¹ * a * g) * (g⁻¹ * n * g) * (g⁻¹ * a * g)⁻¹ = g⁻¹ * n * g := by
      have : (g⁻¹ * a * g) * (g⁻¹ * n * g) * (g⁻¹ * a * g)⁻¹ = g⁻¹ * (a * n * a⁻¹) * g := by group
      rw [this, hfix]
    exact h.conj_frobenius _ haAg hb1 _ hmN hm1 hbm

/-- **Size condition for an odd-order Frobenius group**: if a finite Frobenius group has kernel `N`
and complement `A` both of **odd** order, with `N ≠ ⊥`, then `2|A| + 1 ≤ |N|` (equivalently
`e ≤ (h-1)/2`).  The complement acts freely on `N#`, so `|A| ∣ |N| - 1` (`card_kernel_modEq_one`,
Isaacs 6.1); as `|N|` is odd, `|N| - 1` is even, and an odd divisor of an even number is at most half
of it, so `|N| - 1 ≥ 2|A|`.  This is the `2e + 1 ≤ h` (`smallIndex`) input to the Peterfalvi §7
`(7.8.b)` norm bound. -/
theorem IsFrobeniusGroup.two_mul_card_complement_add_one_le_card_kernel {G : Type*} [Group G]
    [Finite G] {N A : Subgroup G} (hFrob : IsFrobeniusGroup G N A)
    (hNodd : Odd (Nat.card ↥N)) (hAodd : Odd (Nat.card ↥A)) (hNnt : N ≠ ⊥) :
    2 * Nat.card ↥A + 1 ≤ Nat.card ↥N := by
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNnt
  have hN1 : 1 < Nat.card ↥N := Finite.one_lt_card
  -- `|A| ∣ |N| - 1` from `|N| ≡ 1 [MOD |A|]` (Isaacs 6.1).
  obtain ⟨m, hm⟩ : Nat.card ↥A ∣ Nat.card ↥N - 1 :=
    (Nat.modEq_iff_dvd' hN1.le).mp hFrob.card_kernel_modEq_one.symm
  -- `|N| - 1` is even (`|N|` odd), `|A|` is odd, so the cofactor `m` is even.
  have hNm1_even : Even (Nat.card ↥N - 1) := Nat.Odd.sub_odd hNodd odd_one
  have hm_even : Even m := by
    rcases (Nat.even_mul.mp (hm ▸ hNm1_even)) with hA | hm
    · exact absurd hA (Nat.not_even_iff_odd.mpr hAodd)
    · exact hm
  -- `m ≠ 0` (else `|N| = 1`), so `m ≥ 2`; hence `|N| - 1 = |A|·m ≥ 2|A|`.
  have hApos : 0 < Nat.card ↥A := Nat.card_pos
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hp
    · rw [h0, Nat.mul_zero] at hm; omega
    · exact hp
  have hm2 : 2 ≤ m := Nat.le_of_dvd hm_pos hm_even.two_dvd
  have hge : Nat.card ↥A * 2 ≤ Nat.card ↥A * m := Nat.mul_le_mul_left _ hm2
  omega

end OddOrder.Isaacs.Ch06
