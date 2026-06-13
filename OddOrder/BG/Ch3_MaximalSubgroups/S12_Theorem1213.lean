/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem1212c
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1211
import OddOrder.BG.Ch3_MaximalSubgroups.S10_BetaRadicalCore
import OddOrder.BG.Ch1_Preliminary.S01b_Prop116

/-!
# BG §12: Theorem 12.13 — every nonabelian `p`-subgroup of `G` lies in `𝒰`

**スコープ**: BG Theorem 12.13 (mmd L3347). The first uniqueness result of the `σ(M)`-side,
derived from Proposition 12.4.

**証明** (背理法): 非可換 `p`-部分群 `P` が相異なる極大 `M`, `M*` に含まれると仮定する。
Corollary 12.10(a)(d) で `p ∈ σ(M) ∩ σ(M*)` かつ `N_G(P) ⊆ M ∩ M*`。`P` を `M ∩ M*` の Sylow
`p`-部分群と仮定でき(よって `G` の Sylow `p`-部分群)、Uniqueness Theorem で `r(P) = 2`。
Corollary 10.7(b) で order `p³`・exponent `p` の非可換 `Q ⊆ P`(extraspecial)、`Z = Z(Q) = Q'`
order `p`。`Q/Z` の `K = C_{M_α}(Z)` 上の作用 + Proposition 1.16 + Proposition 12.4(a) で `K ⊆ M*`、
`N_M(Z) ⊆ M*`、`ℳ(N_G(Z)) ≠ {M}`、`M_α ≠ 1`。最後に Proposition 12.4(b) で `A₀, A₀* ∈ ℰ¹(A)−{Z}`
が `M ∩ M*`(⊇ `Q`)内で非共役となり、`Q` の構造に矛盾。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The nilpotent normalizer condition inside a `p`-group `S`: a proper subgroup `X < S` is
strictly contained in `N_G(X) ⊓ S`. (File-local; same statement as the private helper in
`S10_HallStructureCore`, replicated here for the BG 12.13 Sylow reduction.) -/
private theorem lt_inf_normalizer_of_lt_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {X S : Subgroup G} (hXS : X < S) (hS : IsPGroup p ↥S) :
    X < Subgroup.normalizer X ⊓ S := by
  haveI : Group.IsNilpotent ↥S := hS.isNilpotent
  have hNC : NormalizerCondition ↥S := normalizerCondition_of_isNilpotent (G := ↥S)
  have hsub_lt : X.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hXS.ne (le_antisymm hXS.le htop)
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt (hNC _ hsub_lt)
  rw [← Subgroup.subgroupOf_normalizer_eq hXS.le, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  refine lt_of_le_of_ne (le_inf Subgroup.le_normalizer hXS.le) (fun heq => ht_not ?_)
  exact heq ▸ Subgroup.mem_inf.mpr ⟨ht_norm, t.2⟩

/-- **BG 12.13 reduction step**: a Sylow `p`-subgroup `P` of a subgroup `K ≤ G`, whose image
`P̄ := P.map K.subtype` has `N_G(P̄) ≤ K`, is (as `P̄`) a Sylow `p`-subgroup of `G`.

Non-`σ` analogue of `S10.isSylow_sylowMap_of_mem_sigma` (same proof): take a Sylow `S ⊇ P̄` of `G`;
if `P̄ < S`, then `N_G(P̄) ⊓ S` is a `p`-subgroup of `K` (by `N_G(P̄) ≤ K`) strictly above `P̄`
(nilpotent normalizer condition in `S`), contradicting that `P` is Sylow in `↥K`. Used to enlarge
the nonabelian `P` to a Sylow `p`-subgroup of `G` inside `M ∩ M⋆`. -/
theorem exists_sylow_eq_map_of_normalizer_le [Finite G] {K : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥K)
    (hN : Subgroup.normalizer (((P : Subgroup ↥K).map K.subtype) : Set G) ≤ K) :
    ∃ S : Sylow p G, (S : Subgroup G) = (P : Subgroup ↥K).map K.subtype := by
  set Pbar : Subgroup G := (P : Subgroup ↥K).map K.subtype with hPbar
  have hPbar_pg : IsPGroup p ↥Pbar :=
    P.2.of_equiv (Subgroup.equivMapOfInjective _ _ K.subtype_injective)
  have hPbar_subOf : Pbar.subgroupOf K = (P : Subgroup ↥K) := by
    rw [hPbar, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  obtain ⟨S, hPS⟩ := hPbar_pg.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : Pbar < (S : Subgroup G) := lt_of_le_of_ne hPS (Ne.symm hne)
  have hgrow : Pbar < Subgroup.normalizer Pbar ⊓ (S : Subgroup G) :=
    lt_inf_normalizer_of_lt_of_isPGroup hlt S.2
  set Y : Subgroup G := Subgroup.normalizer Pbar ⊓ (S : Subgroup G) with hY
  have hYK : Y ≤ K := le_trans inf_le_left hN
  have hYpg : IsPGroup p ↥Y :=
    S.2.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  have hPle : (P : Subgroup ↥K) ≤ Y.subgroupOf K :=
    hPbar_subOf ▸ Subgroup.comap_mono (f := K.subtype) hgrow.le
  have hYsubK_pg : IsPGroup p ↥(Y.subgroupOf K) :=
    hYpg.of_equiv (Subgroup.subgroupOfEquivOfLe hYK).symm
  have hYeq : Y.subgroupOf K = (P : Subgroup ↥K) := P.3 hYsubK_pg hPle
  have hYP : Y = Pbar := by
    have := congrArg (Subgroup.map K.subtype) hYeq
    rwa [Subgroup.map_subgroupOf_eq_of_le hYK, ← hPbar] at this
  exact absurd hYP hgrow.ne'

/-- A nonabelian `p`-subgroup `P` contained in two distinct maximal subgroups `M`, `M*` of `G`
satisfies `p ∈ σ(M) ∩ σ(M*)` and `N_G(P) ⊆ M ∩ M*` (Corollary 12.10(a),(d)). The membership
`p ∈ σ(M)` is the contrapositive of 12.10(a): a `σ(M)'`-`p`-subgroup is nilpotent, hence abelian.
The normalizer containment is 12.10(d) (nonabelian `⟹` noncyclic). -/
theorem mem_sigma_normalizer_le_of_two_maximals [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {P M : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPnab : ¬ IsMulCommutative ↥P) (hM : M ∈ maximalSubgroups G) (hPM : P ≤ M) :
    p ∈ S10.sigma M ∧ Subgroup.normalizer (P : Set G) ≤ M := by
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  haveI : Group.IsNilpotent ↥P := hPp.isNilpotent
  have hcor := nilpotent_sigmaComplement_abelian hG hsetup
  -- `P` is a `σ(M)'`-`p`-subgroup only if `p ∉ σ(M)`; its primes are all `p`.
  have hPpi : p ∉ S10.sigma M → Subgroup.IsPiSubgroup ((S10.sigma M)ᶜ) P := by
    intro hpσ q hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
    rw [hn] at hqd
    have : q = p := (Nat.prime_dvd_prime_iff_eq hqp Fact.out).mp (hqp.dvd_of_dvd_pow hqd)
    rwa [this]
  have hpσM : p ∈ S10.sigma M := by
    by_contra hpσ
    exact hPnab (hcor.1 P hPM (hPpi hpσ) ‹_›)
  refine ⟨hpσM, ?_⟩
  -- `N_G(P) ⊆ M`: 12.10(d), `P` noncyclic.
  refine hcor.2.2.2.1 p hpσM P hPM hPp ?_
  intro hcyc
  haveI := hcyc
  exact hPnab (IsMulCommutative.of_comm (IsCyclic.commGroup (α := ↥P)).mul_comm)

/-- **Conjugates of a noncentral element cover its central coset** in an exponent-`p` extraspecial
group: for `a₀ ∉ Z(Q)` and any `z ∈ Z(Q)`, there is `q` with `q a₀ q⁻¹ = z · a₀`.

The map `φ : Q → Z(Q)`, `q ↦ ⁅q, a₀⁆`, is a homomorphism (commutators lie in `[Q,Q] = Z(Q)`,
which is central), nontrivial since `a₀ ∉ Z(Q)`, hence surjective onto the order-`p` group `Z(Q)`.
So every `z ∈ Z(Q)` is realized as `⁅q,a₀⁆`, i.e. `q a₀ q⁻¹ = z · a₀`. This is the conjugacy half of
the BG 12.13 Heisenberg line-conjugacy argument. -/
theorem exists_conj_eq_center_mul_of_expPExtraspecial {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : IsExpPExtraspecial p Q) {a₀ : Q} (ha₀ : a₀ ∉ Subgroup.center Q)
    {z : Q} (hz : z ∈ Subgroup.center Q) :
    ∃ q : Q, q * a₀ * q⁻¹ = z * a₀ := by
  classical
  have hes := hQ.isExtraspecial
  have hZcard : Nat.card (Subgroup.center Q) = p := hes.center_card
  have hZcomm : commutator Q = Subgroup.center Q := hes.commutator_eq_center
  -- (1) `⁅q, a₀⁆ ∈ Z(Q)` for all `q`.
  have hmemZ : ∀ q : Q, ⁅q, a₀⁆ ∈ Subgroup.center Q := fun q => by
    rw [← hZcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top q) (Subgroup.mem_top a₀)
  -- (2) `φ : Q →* Z(Q)`, `q ↦ ⁅q, a₀⁆` (homomorphism by centrality of commutators).
  have hcentral : ∀ z : Q, z ∈ Subgroup.center Q → ∀ w : Q, Commute z w :=
    fun z hz w => (Subgroup.mem_center_iff.mp hz w).symm
  let φ : Q →* Subgroup.center Q := MonoidHom.mk'
    (fun q => ⟨⁅q, a₀⁆, hmemZ q⟩) (fun x y => by
      apply Subtype.ext
      show ⁅x * y, a₀⁆ = ⁅x, a₀⁆ * ⁅y, a₀⁆
      have hc := hcentral ⁅y, a₀⁆ (hmemZ y)
      have e1 : ⁅x * y, a₀⁆ = x * ⁅y, a₀⁆ * x⁻¹ * ⁅x, a₀⁆ := by
        simp only [commutatorElement_def]; group
      have e2 : x * ⁅y, a₀⁆ * x⁻¹ = ⁅y, a₀⁆ := by rw [(hc x).symm.eq]; group
      rw [e1, e2, (hc ⁅x, a₀⁆).eq])
  -- (3) `φ` is surjective: its range is a nontrivial subgroup of the order-`p` group `Z(Q)`.
  have hφsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    have hdvd : Nat.card ↥φ.range ∣ p := hZcard ▸ Subgroup.card_subgroup_dvd_card φ.range
    have hne1 : Nat.card ↥φ.range ≠ 1 := by
      rw [ne_eq, Subgroup.card_eq_one]
      intro hbot
      refine ha₀ (Subgroup.mem_center_iff.mpr fun g => ?_)
      have hg1 : φ g = 1 := by rw [← Subgroup.mem_bot, ← hbot]; exact ⟨g, rfl⟩
      have h2 : ⁅g, a₀⁆ = 1 := Subtype.ext_iff.mp hg1
      exact commutatorElement_eq_one_iff_commute.mp h2
    have hcardr : Nat.card ↥φ.range = p :=
      (Nat.dvd_prime Fact.out).mp hdvd |>.resolve_left hne1
    exact Subgroup.eq_top_of_card_eq _ (by rw [hcardr, hZcard])
  -- (4) realize `z` as `⁅q, a₀⁆`, so `q a₀ q⁻¹ = z · a₀`.
  obtain ⟨q, hq⟩ := hφsurj ⟨z, hz⟩
  refine ⟨q, ?_⟩
  have hqz : ⁅q, a₀⁆ = z := Subtype.ext_iff.mp hq
  rw [commutatorElement_def] at hqz
  exact mul_inv_eq_iff_eq_mul.mp hqz

/-- **Non-central lines through a common rank-2 `A` are `Q`-conjugate** in an exp-`p` extraspecial
group `Q`: if `a ∉ Z(Q)`, `b ∉ Z(Q)`, and `b ∈ ⟨a⟩ ⊔ Z(Q)`, then `⟨b⟩ = q⟨a⟩q⁻¹` for some `q`.

Write `b = aⁱ·z` (`z ∈ Z(Q)`); `aⁱ ∉ Z(Q)` forces `p ∤ i`. Choosing `j := i⁻¹` in the field
`ZMod p` gives `i·j ≡ 1 (mod p)`, so (using `z^p = 1`) `z^{ij} = z`. Then
`exists_conj_eq_center_mul_of_expPExtraspecial` provides `q` with `q a q⁻¹ = zʲ·a`, whence
`q aⁱ q⁻¹ = (zʲa)ⁱ = z·aⁱ = b ∈ q⟨a⟩q⁻¹`; both sides have order `p`, so `⟨b⟩ = q⟨a⟩q⁻¹`.
This is the structural input to BG 12.13's final contradiction: the two lines `A₀, A₀⋆ ∈ ℰ¹(A)−{Z}`
are `Q`-conjugate, contradicting `ℳ(N_G(A₀)) = {M} ≠ {M⋆} = ℳ(N_G(A₀⋆))`. -/
theorem exists_conj_smul_zpowers_eq_of_expPExtraspecial {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : IsExpPExtraspecial p Q) {a b : Q} (ha : a ∉ Subgroup.center Q)
    (hb : b ∉ Subgroup.center Q) (hmem : b ∈ Subgroup.zpowers a ⊔ Subgroup.center Q) :
    ∃ q : Q, MulAut.conj q • Subgroup.zpowers a = Subgroup.zpowers b := by
  classical
  have hp : p.Prime := Fact.out
  -- `ord a = ord b = p`.
  have ha1 : a ≠ 1 := fun h => ha (h ▸ one_mem _)
  have hb1 : b ≠ 1 := fun h => hb (h ▸ one_mem _)
  have horda : orderOf a = p :=
    ((Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hQ.pow_eq_one a))).resolve_left
      (fun h => ha1 (orderOf_eq_one_iff.mp h))
  have hordb : orderOf b = p :=
    ((Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hQ.pow_eq_one b))).resolve_left
      (fun h => hb1 (orderOf_eq_one_iff.mp h))
  -- `b = aⁱ · z`, `z ∈ Z(Q)`.
  rw [Subgroup.mem_sup_of_normal_right] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := hmem
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  -- `aⁱ ∉ Z(Q)`, so `p ∤ i`.
  have haiZ : a ^ i ∉ Subgroup.center Q := fun h => hb (hyz ▸ mul_mem h hz)
  have hpi : ¬ (p : ℤ) ∣ i := fun ⟨m, hm⟩ => haiZ (by
    rw [hm, zpow_mul, zpow_natCast, hQ.pow_eq_one, one_zpow]; exact one_mem _)
  -- `z ^ p = 1` (center has order `p`).
  have hzp : z ^ p = 1 := by
    have h1 : (⟨z, hz⟩ : Subgroup.center Q) ^ Nat.card (Subgroup.center Q) = 1 := pow_card_eq_one'
    rw [hQ.isExtraspecial.center_card] at h1
    have h2 := congrArg (Subgroup.subtype (Subgroup.center Q)) h1
    simpa using h2
  -- choose `j` with `i * j ≡ 1 (mod p)`.
  haveI : Fact p.Prime := ⟨hp⟩
  have hi0 : (i : ZMod p) ≠ 0 := fun h => hpi ((ZMod.intCast_zmod_eq_zero_iff_dvd i p).mp h)
  set j : ℤ := (((i : ZMod p)⁻¹).val : ℤ) with hjdef
  have hij1 : (p : ℤ) ∣ (i * j - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [hjdef, ZMod.natCast_val, ZMod.cast_id]
    rw [mul_inv_cancel₀ hi0, sub_self]
  obtain ⟨m, hm⟩ := hij1
  have hijm : i * j = 1 + (p : ℤ) * m := by linarith
  -- `z ^ (i*j) = z`.
  have hzij : z ^ (i * j) = z := by
    rw [hijm, zpow_add, zpow_one, zpow_mul, zpow_natCast, hzp, one_zpow, mul_one]
  -- conjugate `a` to `zʲ·a` and raise to the `i`-th power: `q aⁱ q⁻¹ = b`.
  obtain ⟨q, hq⟩ := exists_conj_eq_center_mul_of_expPExtraspecial hQ ha (zpow_mem hz j)
  have hca : Commute z a := (Subgroup.mem_center_iff.mp hz a).symm
  have hcomm : Commute (z ^ j) a := hca.zpow_left j
  have hconjai : (MulAut.conj q) (a ^ i) = b := by
    rw [map_zpow, MulAut.conj_apply, hq, hcomm.mul_zpow, ← zpow_mul, mul_comm j i, hzij,
      (Subgroup.mem_center_iff.mp hz (a ^ i)).symm]
    exact hyz
  -- `b ∈ q⟨a⟩q⁻¹` and a cardinality count.
  have hbmem : b ∈ MulAut.conj q • Subgroup.zpowers a := by
    rw [mulAut_smul_eq_map]
    exact ⟨a ^ i, zpow_mem (Subgroup.mem_zpowers a) i, hconjai⟩
  have hinj : Function.Injective (MulAut.conj q).toMonoidHom := (MulAut.conj q).injective
  have hcardL : Nat.card (MulAut.conj q • Subgroup.zpowers a : Subgroup Q) = p := by
    have he : Nat.card (MulAut.conj q • Subgroup.zpowers a : Subgroup Q)
        = Nat.card (Subgroup.zpowers a) := by
      rw [mulAut_smul_eq_map]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ hinj).toEquiv).symm
    rw [he, Nat.card_zpowers, horda]
  have hcardR : Nat.card (Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hordb]
  exact ⟨q, (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbmem)
    (le_of_eq (hcardL.trans hcardR.symm))).symm⟩

/-- **`ℳ(N_G(·))`-uniqueness blocks `M`-conjugacy**: if `A₀⋆ = g • A₀` (conjugation by some
`g ∈ M`), `ℳ(N_G(A₀)) = {M}`, and `ℳ(N_G(A₀⋆)) = {M⋆}`, then `M = M⋆`.

Conjugation by `g` commutes with `N_G(·)` (`normalizer_conj_smul`) and preserves coatomicity
(`isCoatom_conj_smul`), so `g • M` is a maximal subgroup containing `N_G(A₀⋆)`, hence the unique
such, namely `M⋆`; but `g ∈ M` fixes `M` (`conj_smul_eq_self_of_mem_normalizer`), whence `M = M⋆`.
This is the engine of the final contradiction in BG 12.13: `A₀` and `A₀⋆` are `Q`-conjugate, yet
their `ℳ(N_G(·))` are the distinct singletons `{M}` and `{M⋆}`. -/
theorem eq_of_conj_of_maximalContaining_normalizer_eq_singleton
    {A₀ A₀star M Mstar : Subgroup G} {g : G} (hgM : g ∈ M)
    (hconj : MulAut.conj g • A₀ = A₀star)
    (hM : maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) = {M})
    (hMstar : maximalSubgroupsContaining (Subgroup.normalizer (A₀star : Set G)) = {Mstar}) :
    M = Mstar := by
  -- `M ∈ ℳ(N_G(A₀))`, so `IsCoatom M` and `N_G(A₀) ≤ M`.
  have hMmem : M ∈ maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) := by
    rw [hM]; exact Set.mem_singleton_iff.mpr rfl
  obtain ⟨hMcoat, hMle⟩ := mem_maximalSubgroupsContaining.mp hMmem
  -- `g • M` is a coatom containing `N_G(A₀⋆)`, hence lies in `ℳ(N_G(A₀⋆)) = {M⋆}`.
  have hle' : Subgroup.normalizer (A₀star : Set G) ≤ MulAut.conj g • M := by
    rw [← hconj, ← normalizer_conj_smul]
    exact conj_smul_mono _ hMle
  have hmem' : MulAut.conj g • M
      ∈ maximalSubgroupsContaining (Subgroup.normalizer (A₀star : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨isCoatom_conj_smul hMcoat, hle'⟩
  rw [hMstar, Set.mem_singleton_iff] at hmem'
  -- `g ∈ M` fixes `M` under conjugation, so `M = M⋆`.
  rwa [conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hgM)] at hmem'

/-- **BG 12.13 reduction**: a nonabelian `p`-subgroup `P` lying in two distinct maximal subgroups
`M ≠ M⋆` yields a subgroup `Q ⊆ M ∩ M⋆` of order `p³` and exponent `p` (extraspecial).

Enlarge `P` to a Sylow `p`-subgroup `S` of `M ∩ M⋆`; since `N_G(S) ⊆ M ∩ M⋆`
(`mem_sigma_normalizer_le_of_two_maximals`, `S ⊇ P` still nonabelian), `S` is a Sylow `p`-subgroup
of `G` (`exists_sylow_eq_map_of_normalizer_le`). If `r(S) ≥ 3` the Uniqueness Theorem forces
`M = M⋆`; so `r(S) ≤ 2`, and `S` nonabelian, whence Corollary 10.7(b) (`sylow_structure`) provides
the extraspecial `Q ⊆ S ⊆ M ∩ M⋆`. -/
theorem exists_expPExtraspecial_le_of_two_maximals [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {P M Mstar : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPnab : ¬ IsMulCommutative ↥P) (hM : M ∈ maximalSubgroups G)
    (hMstar : Mstar ∈ maximalSubgroups G) (hMne : M ≠ Mstar)
    (hPM : P ≤ M) (hPMstar : P ≤ Mstar) :
    ∃ Q : Subgroup G, Q ≤ M ⊓ Mstar ∧ IsExpPExtraspecial p ↥Q ∧ Nat.card ↥Q = p ^ 3 := by
  classical
  set K : Subgroup G := M ⊓ Mstar with hK
  have hPK : P ≤ K := le_inf hPM hPMstar
  -- enlarge `P` to a Sylow `p`-subgroup `Pbar` of `↥K`.
  have hPsubK_pg : IsPGroup p ↥(P.subgroupOf K) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  obtain ⟨SK, hSK⟩ := hPsubK_pg.exists_le_sylow
  set Pbar : Subgroup G := (SK : Subgroup ↥K).map K.subtype with hPbar
  have hPbar_pg : IsPGroup p ↥Pbar :=
    SK.2.of_equiv (Subgroup.equivMapOfInjective _ _ K.subtype_injective)
  have hP_le_Pbar : P ≤ Pbar := by
    have h1 : (P.subgroupOf K).map K.subtype ≤ Pbar := Subgroup.map_mono hSK
    rwa [Subgroup.map_subgroupOf_eq_of_le hPK] at h1
  have hPbar_nab : ¬ IsMulCommutative ↥Pbar := fun h => hPnab (isMulCommutative_of_le h hP_le_Pbar)
  have hPbar_le_K : Pbar ≤ K := Subgroup.map_subtype_le _
  have hPbar_le_M : Pbar ≤ M := hPbar_le_K.trans inf_le_left
  have hPbar_le_Mstar : Pbar ≤ Mstar := hPbar_le_K.trans inf_le_right
  -- `N_G(Pbar) ≤ K`.
  have hN : Subgroup.normalizer (Pbar : Set G) ≤ K := le_inf
    (mem_sigma_normalizer_le_of_two_maximals hG hPbar_pg hPbar_nab hM hPbar_le_M).2
    (mem_sigma_normalizer_le_of_two_maximals hG hPbar_pg hPbar_nab hMstar hPbar_le_Mstar).2
  -- `Pbar` is a Sylow `p`-subgroup of `G`.
  obtain ⟨S, hS⟩ := exists_sylow_eq_map_of_normalizer_le SK (hPbar ▸ hN)
  rw [← hPbar] at hS
  have hSlt : (S : Subgroup G) < ⊤ := by
    rw [hS, lt_top_iff_ne_top]
    exact fun htop => hM.1 (top_le_iff.mp (htop ▸ hPbar_le_M))
  -- `r(S) ≤ 2` (else Uniqueness forces `M = M⋆`).
  have hrank2 : rank ↥(S : Subgroup G) ≤ 2 := by
    by_contra hr
    have huniq := Ch2.S09.uniquenessTheorem hG hSlt (by omega) (Or.inl (by omega : 3 ≤ rank ↥(S : Subgroup G)))
    exact hMne (huniq.2.unique ⟨hM, by rw [hS]; exact hPbar_le_M⟩
      ⟨hMstar, by rw [hS]; exact hPbar_le_Mstar⟩)
  -- `S` nonabelian, so Cor 10.7(b) gives the extraspecial `Q`.
  rcases (S10.sylow_structure hG S).2.1 hrank2 with habel | ⟨Q, _, hQ_le, _, hQ_es, hQ_card, _, _, _⟩
  · exact absurd habel (by rw [hS]; exact hPbar_nab)
  · exact ⟨Q, hQ_le.trans (by rw [hS]; exact hPbar_le_K), hQ_es, hQ_card⟩

/-- **`M_α ≠ 1`** (BG 12.13, mmd L3395): if a Sylow `p`-subgroup `S` of `G` has `N_G(S) ⊆ M ∩ M⋆`
for distinct maximals `M ≠ M⋆`, then `M_α ≠ 1`.

Corollary 10.9(b) (`beta_factorization_of_sylow_normalizer_in_intersection`) gives
`M = (M⋆ ∩ M) ⊔ M_β` and `α(M) = β(M)`, so `M_α = M_β`; were `M_β = 1`, then `M = M⋆ ∩ M ≤ M⋆`
would force `M = M⋆` (both coatoms), contradiction. -/
theorem Malpha_ne_bot_of_sylow_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    (hMne : M ≠ Mstar) {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M ⊓ Mstar) :
    S10.Malpha M ≠ ⊥ := by
  obtain ⟨hfact, hab⟩ := S10.beta_factorization_of_sylow_normalizer_in_intersection hG hM hMstar
    (Ne.symm hMne) S (by rw [inf_comm]; exact hN)
  have hαβ : S10.Malpha M = S10.Mbeta M := by simp only [S10.Malpha, S10.Mbeta, hab]
  rw [hαβ]
  intro hbot
  rw [hbot, sup_bot_eq] at hfact
  have hMle : M ≤ Mstar := by rw [hfact]; exact inf_le_left
  rcases lt_or_eq_of_le hMle with hlt | heq
  · exact (mem_maximalSubgroups.mp hMstar).1 ((mem_maximalSubgroups.mp hM).2 Mstar hlt)
  · exact hMne heq

/-- **`p ∉ α(M)`** when a Sylow `p`-subgroup of `G` has rank `≤ 2`: since `α(M) = {p ∈ π(M) |
r_p(M) ≥ 3}` and `r_p(M) = pRank_p(M) ≤ pRank_p(G) = pRank_p(S) ≤ rank(S) ≤ 2`. In BG 12.13 this
supplies the coprimality `p ∤ |M_α|` (`M_α` is an `α(M)`-group) needed for the Lemma 6.5(b)
factorization of `N_M(Z)`. -/
theorem notMem_alpha_of_rank_sylow_le_two [Finite G] {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hrank2 : rank ↥(S : Subgroup G) ≤ 2) :
    p ∉ S10.alpha M := by
  intro hp
  have h3 : 3 ≤ pRank ↥M p := ((S10.mem_alpha_iff M p).mp hp).2
  have hle : pRank ↥M p ≤ 2 := calc
    pRank ↥M p ≤ pRank G p := pRank_mono_of_le M
    _ = pRank ↥(S : Subgroup G) p := (pRank_sylow_eq S).symm
    _ ≤ rank ↥(S : Subgroup G) := pRank_le_rank p
    _ ≤ 2 := hrank2
  omega

/-- **BG Theorem 12.13** (mmd L3347): every nonabelian `p`-subgroup of `G` (for every prime `p`)
lies in `𝒰`. -/
theorem nonabelian_pgroup_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPnab : ¬ IsMulCommutative ↥P) :
    IsUniquelyMaximal P := by
  classical
  -- `P < ⊤` (else `G` is a `p`-group, hence solvable).
  have hPlt : P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hPtop
    have hGp : IsPGroup p G :=
      (hPtop ▸ hPp : IsPGroup p ↥(⊤ : Subgroup G)).of_equiv Subgroup.topEquiv
    haveI := hGp.isNilpotent
    exact hG.notSolvable IsNilpotent.to_isSolvable
  obtain ⟨M, hMcoatom, hPM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom P).resolve_left hPlt.ne
  refine IsUniquelyMaximal.of_unique_maximal hPlt (mem_maximalSubgroups.mpr hMcoatom) hPM ?_
  intro Mstar hMstar hPMstar
  by_contra hne
  -- `p ∈ σ(M) ∩ σ(M*)` and `N_G(P) ⊆ M ∩ M*`.
  obtain ⟨hpσM, hNM⟩ := mem_sigma_normalizer_le_of_two_maximals hG hPp hPnab
    (mem_maximalSubgroups.mpr hMcoatom) hPM
  obtain ⟨hpσMstar, hNMstar⟩ := mem_sigma_normalizer_le_of_two_maximals hG hPp hPnab hMstar hPMstar
  -- **Hard core** (Z-action via Prop 1.16 + Prop 12.4, non-conjugacy contradiction).
  sorry

end OddOrder.BG.Ch3.S12
