/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_PropE4

/-!
# BG Corollary E.5: the local data `(E.29)`

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 164–166.

Corollary E.5 opens with *"Note that we are in the situation of Corollary 15.9"* and
collects, from that proof, the display

> `(E.29)`  `C_{N_σ}(x) > 1`, `M ∩ N` is a complement to `N_σ` in `N`, `|K₁|` is prime,
> and `R` is contained in an abelian normal complement `U₁` to `K₁` in `M ∩ N`.

This leaf assembles the corollary in stages (issue 3028):

* **`e5_neighbour_data` (this file, WP1)** — the `(E.29)` bundle: replaying the opening of
  the proved Corollary 15.9 (`centralizer_escape_final_local`,
  `OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TaxonomyOutput.lean`) through its public
  ingredients: `signalizer_structure_of_mem_sigmaSharp`, `subgroupESetup_of_complement`,
  `typeP2_matched_kappa_hall_pair_of_esetup`, and `card_kappaHall_prime_of_isTypeP2`.
  `K₁` is BG's Hall `κ(N)`-subgroup of `M ∩ N` and `U₁` its abelian partner Hall
  `(κ(N) ∪ σ(N))'`-subgroup; the `R ≤ U₁` clause of `(E.29)` is deferred to the `(E.30)`
  stage, where `R` is produced.
* Later stages (issue 3028 WP2–WP5): `(E.30)`–`(E.32)`, the `RegularOperatorSetup`
  instantiation for `(O_p(M), K₁, E)`, `(ii) ∧ hdc ⟹ (i)` via Theorem E.3 and the
  corrected Proposition E.4 (`AppE_PropE4.lean`), and the `(E.33)`/`(E.34)` counting.
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S16

variable {G : Type*} [Group G]

/-- **A `p`-element of a nilpotent normal subgroup lies in the `p`-core**: if `W ≤ M` is
nilpotent, `W ⊴ M` (as `subgroupOf`), and `x ∈ W` has order `p`, then `x ∈ O_p(M)`.

The Sylow `p`-subgroup of the nilpotent `W` is normal, hence characteristic, in `W`, so
its image is a normal `p`-subgroup of `M` — and it absorbs `x`.  This is the `(E.30)`
ingredient *"`O_p(M)` is a Sylow `p`-subgroup of `M_σ`"* in the form actually consumed:
`x ∈ M_σ` of order `p` lands in `O_p(M)` (with `W = M_σ`, nilpotent as the kernel of the
Frobenius group `M` from Corollary 15.9). -/
theorem mem_opiCoreInG_singleton_of_nilpotent [Finite G] {p : ℕ} (hp : p.Prime)
    {M W : Subgroup G} (hWM : W ≤ M) (hWnorm : (W.subgroupOf M).Normal)
    (hWnil : Group.IsNilpotent ↥W) {x : G} (hxW : x ∈ W) (hord : orderOf x = p) :
    x ∈ opiCoreInG {p} M := by
  haveI : Fact p.Prime := ⟨hp⟩
  set W' : Subgroup ↥M := W.subgroupOf M with hW'def
  haveI : W'.Normal := hWnorm
  haveI : Group.IsNilpotent ↥W' :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hWM)).mpr hWnil
  have hxM : x ∈ M := hWM hxW
  set ξ : ↥W' := ⟨⟨x, hxM⟩, by rwa [Subgroup.mem_subgroupOf]⟩ with hξdef
  have hordξ : orderOf ξ = p := by
    have h1 := orderOf_injective W'.subtype W'.subtype_injective ξ
    have h2 := orderOf_injective M.subtype M.subtype_injective (W'.subtype ξ)
    rw [← hord]
    rw [← h1, ← h2]
    rfl
  -- `⟨ξ⟩` is a `p`-group; put it inside a Sylow `p`-subgroup of the nilpotent `W'`.
  have hpg : IsPGroup p ↥(Subgroup.zpowers ξ) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hordξ, pow_one])
  obtain ⟨P, hξP⟩ := hpg.exists_le_sylow
  have hPchar : (P : Subgroup ↥W').Characteristic :=
    Sylow.characteristic_of_normal P inferInstance
  -- Its image in `↥M` is a normal `p`-subgroup; push to the ambient group.
  have hQnorm : (((P : Subgroup ↥W').map W'.subtype)).Normal :=
    OddOrder.GroupTheory.normal_map_subtype_of_characteristic hPchar
  obtain ⟨n, hn⟩ := P.2.exists_card_eq
  set Qamb : Subgroup G := ((P : Subgroup ↥W').map W'.subtype).map M.subtype with hQdef
  have hQambM : Qamb ≤ M := Subgroup.map_subtype_le _
  have hQsub : Qamb.subgroupOf M = (P : Subgroup ↥W').map W'.subtype :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hQnorm' : (Qamb.subgroupOf M).Normal := hQsub ▸ hQnorm
  have hQcard : Nat.card ↥Qamb = p ^ n := by
    rw [hQdef, Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective W'.subtype_injective, hn]
  have hQpi : Subgroup.IsPiSubgroup {p} Qamb := by
    intro r hr
    rw [hQcard] at hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrdvd : r ∣ p ^ n := Nat.dvd_of_mem_primeFactors hr
    exact (Nat.prime_dvd_prime_iff_eq hrp hp).mp (hrp.dvd_of_dvd_pow hrdvd)
  refine le_opiCoreInG_of_normal_of_isPiSubgroup hQambM hQnorm' hQpi ?_
  exact ⟨W'.subtype ξ, ⟨ξ, hξP (Subgroup.mem_zpowers ξ), rfl⟩, rfl⟩

/-- **BG `(E.29)`** (p. 165): under Corollary E.5's hypothesis block, the unique maximal
subgroup `N ⊇ C_G(x)` is of type P₂ with `C_{N_σ}(x) ≠ 1` and `M ∩ N` a complement to
`N_σ` in `N`; and `M ∩ N` carries a Hall `κ(N)`-subgroup `K₁` of prime order together
with a nontrivial abelian Hall `(κ(N) ∪ σ(N))'`-subgroup `U₁` normalized by `K₁`.

This is the opening of BG's proof (*"As in the proof of Corollary 15.9, we see that…"*),
replayed through the public pieces of the proved
`OddOrder.BG.Ch4.S16.centralizer_escape_final_local`.  The remaining `(E.29)` clause —
`R ≤ U₁` for the Sylow `p`-subgroup `R` of `M ∩ N` — is produced at the `(E.30)` stage
(issue 3028 WP2), which constructs `R`. -/
theorem e5_neighbour_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N : Subgroup G} {x : G} {p : ℕ}
    (hM : M ∈ maximalSubgroups G) (hp : p.Prime)
    (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hord : orderOf x = p)
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNmem : N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hNnotF : N ∉ OddOrder.BG.Ch4.S14.maximalTypeFFamily G) :
    N ∈ maximalSubgroups G ∧ OddOrder.BG.Ch4.S14.IsTypeP2 N ∧
      Subgroup.centralizer ({x} : Set G) ≤ N ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ ∧
      Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
        ((M ⊓ N).subgroupOf N) ∧
      ∃ K₁ U₁ : Subgroup G,
        K₁ ≤ M ⊓ N ∧ U₁ ≤ M ⊓ N ∧ U₁ ≠ ⊥ ∧
        OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa N)
          (K₁.subgroupOf N) ∧
        OddOrder.Isaacs.Ch03.IsHallSubgroup
          ((OddOrder.BG.Ch4.S14.kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ)
          (U₁.subgroupOf N) ∧
        (Nat.card ↥K₁).Prime ∧
        IsMulCommutative ↥U₁ ∧
        K₁ ≤ Subgroup.normalizer ((U₁ : Subgroup G) : Set G) ∧
        M ⊓ N = K₁ ⊔ U₁ := by
  classical
  have hx1 : x ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hord, h, orderOf_one])
  have hxsharp : x ∈ OddOrder.BG.Ch4.S14.sigmaSharp M := ⟨hxM, hx1⟩
  -- The escape gives `1 < |𝓜_σ(x)|`, exactly as in Corollary 15.9.
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra h
    push Not at h
    exact hesc (centralizer_le_of_maximalSigma_le_one hG hM hxM hx1 h)
  obtain ⟨N', hNstruct, -⟩ := signalizer_structure_of_mem_sigmaSharp hG hM hxsharp hgt
  obtain ⟨hNmax', hCN', hRne', hRhall', hxtau2', hNtype', hforall'⟩ := hNstruct
  have hxN' : x ∈ N' := hCN' (Subgroup.mem_centralizer_iff.mpr
    (fun y hy => by rw [Set.mem_singleton_iff.mp hy]))
  -- Our given `N ⊇ C_G(x)` is that unique neighbour.
  have hNeq : N = N' := Set.mem_singleton_iff.mp
    ((OddOrder.BG.Ch4.S14.maximalContaining_centralizer_eq_singleton_of_tau2_element hG
      hNmax' hxN' hx1 hxtau2' hRne') ▸ hNmem)
  subst hNeq
  -- `N` is type-P₂ (`IsTypeF N ∨ IsTypeP2 N` with `N ∉ ℳ_𝓕`).
  have hP2N : OddOrder.BG.Ch4.S14.IsTypeP2 N :=
    hNtype'.resolve_left fun hF => hNnotF ⟨hNmax', hF⟩
  -- `M ∩ N` complements `N_σ` in `N` (signalizer conjunct at `M' := M`).
  have hMσx : M ∈ OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x := ⟨hM, hxM⟩
  obtain ⟨-, -, hcompl, -⟩ := hforall' M hMσx
  -- Ambient complement form, as in Corollary 15.9.
  have hEleN : M ⊓ N ≤ N := inf_le_right
  have hinf : OddOrder.BG.Ch3.S10.Msigma N ⊓ (M ⊓ N) = ⊥ := by
    have hd : Disjoint (OddOrder.BG.Ch3.S10.Msigma N ⊓ (M ⊓ N)) N := by
      rw [← Subgroup.subgroupOf_eq_bot]
      change (OddOrder.BG.Ch3.S10.Msigma N ⊓ (M ⊓ N)).comap N.subtype = ⊥
      rw [Subgroup.comap_inf]
      exact disjoint_iff.mp hcompl.disjoint
    have hle : OddOrder.BG.Ch3.S10.Msigma N ⊓ (M ⊓ N) ≤ N := inf_le_right.trans inf_le_right
    rw [← inf_of_le_left hle]
    exact disjoint_iff.mp hd
  have hsup : OddOrder.BG.Ch3.S10.Msigma N ⊔ (M ⊓ N) = N := by
    refine le_antisymm (sup_le (OddOrder.BG.Ch3.S10.Msigma_le N) inf_le_right) ?_
    rw [← Subgroup.subgroupOf_eq_top,
      Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le N) inf_le_right]
    exact hcompl.sup_eq_top
  -- The `E`-setup on `N` with `E := M ∩ N`, and its type-P₂ matched Hall pair.
  obtain ⟨E₁, E₂, E₃, hsetup⟩ := subgroupESetup_of_complement hG hNmax' hEleN hinf hsup
  obtain ⟨-, hU0E, hU0ne, hK₀, hU₀, hU₀ab, hK₀NU₀⟩ :=
    typeP2_matched_kappa_hall_pair_of_esetup hG hNmax' hP2N hsetup
  -- `|K₁|` is prime (BG's *"|K₁| is prime"*, from the type-P₂ structure).
  obtain ⟨qk, hqkprime, hcardK⟩ :=
    OddOrder.BG.Ch4.S15.card_kappaHall_prime_of_isTypeP2 hG hNmax' hP2N
      (hsetup.E₁_le.trans hEleN) hK₀
  -- `M ∩ N = K₁ ⊔ U₁`, from `E = E₁ ⊔ E₂ ⊔ E₃`.
  have hsupMN : M ⊓ N = E₁ ⊔ (E₂ ⊔ E₃) := by
    have h := (subgroupE_basic hG hsetup).2.2.2.2.1.1
    rwa [sup_assoc] at h
  exact ⟨hNmax', hP2N, hCN', hRne', hcompl,
    E₁, E₂ ⊔ E₃, hsetup.E₁_le, hU0E, hU0ne, hK₀, hU₀, hcardK ▸ hqkprime, hU₀ab, hK₀NU₀,
    hsupMN⟩

end OddOrder.BG.AppE
