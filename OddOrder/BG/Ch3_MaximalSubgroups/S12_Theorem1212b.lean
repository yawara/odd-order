/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem1212
import OddOrder.BG.Ch3_MaximalSubgroups.S12_ExceptionalBridge

/-!
# BG §12: Theorem 12.12 — Case 3 (abelian Sylow `p`), building blocks

**スコープ**: BG Theorem 12.12 (mmd L3344-3373) の Case 3。`G` の Sylow `p`-部分群が可換で
`τ₂(M) ≠ ∅` のとき、Lemma 12.8 の設定下で `A₀ = E₂` が (a) を満たす。(b) のためには各
`p ∈ τ₂(M)` に対し、`exp(Z) = exp(S)` をもつ cyclic な `N_G(S)`-不変部分群 `Z ≤ S` で
`C_{M_σ}(Ω₁(Z)) = 1` なるものを構成すればよい (`E₀ = E₁E₃·∏Z_p`)。

本ファイルは Case 3 の部品を下から積む。最初の foundational lemma:
**`inf_centralizer_line_eq_bot_of_invariant`** — `N_G(S)`-不変な line `L ≤ S` (`L ∈ ℰ_p¹`) は
自動的に `C_{M_σ}(L) = 1` を満たす (BG L3345-3347 の「key fact」)。`L ≤ Ω₁(S) = A` ゆえ
Cor 12.6(c) が `N_G(L) ⊆ M` を与え、`N_G(S) ≤ N_G(L) ⊆ M` が `N_G(S) ⊄ M` に矛盾。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.Isaacs.Ch06
open scoped Pointwise

variable {G : Type*} [Group G]

/-- The maximality predicate making `S` a Sylow `p`-subgroup *of `M`* as well: any `p`-subgroup
`R` of `M` containing `S` equals `S`. Holds because `S` is already a Sylow `p`-subgroup of `G`. -/
theorem sylow_maximal_in_M_of_le {p : ℕ} [Fact p.Prime] {M : Subgroup G} [Finite G]
    {S : Sylow p G} (hSM : (S : Subgroup G) ≤ M) :
    ∀ R : Subgroup G, (S : Subgroup G) ≤ R → R ≤ M → IsPGroup p ↥R → R = (S : Subgroup G) := by
  intro R hSR _ hRpg
  refine (Subgroup.eq_of_le_of_card_ge hSR ?_).symm
  obtain ⟨k, hk⟩ := hRpg.exists_card_eq
  rw [S.card_eq_multiplicity, hk]
  refine Nat.pow_le_pow_right (Fact.out : p.Prime).pos ?_
  rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne', ← hk]
  exact Subgroup.card_subgroup_dvd_card R

/-- **Theorem 12.12, Case 3 key fact** (BG L3345-3347): since `p ∉ σ(M)` gives `N_G(S) ⊄ M`,
every `N_G(S)`-invariant line `L ≤ S` automatically satisfies `C_{M_σ}(L) = 1`. Indeed `L ≤ A`
(`= Ω₁(S)`, all order-`p` elements), so if `M_σ ⊓ C_G(L) ≠ 1` then Corollary 12.6(c) makes `M`
the unique maximal over `C_G(L)`, forcing `N_G(L) ⊆ M` and hence `N_G(S) ≤ N_G(L) ⊆ M`,
contradicting `N_G(S) ⊄ M`. -/
theorem inf_centralizer_line_eq_bot_of_invariant [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G)) (hSM : (S : Subgroup G) ≤ M)
    {L : Subgroup G} (hL : L ∈ elemAbelianOfRank G p 1) (hLS : L ≤ (S : Subgroup G))
    (hLinv : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G)) :
    S10.Msigma M ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  -- `Ω₁(S) = A` and `N_G(S) ⊄ M` (Theorem 12.5(b) packaging).
  obtain ⟨hΩ, hNS_not_le⟩ := omega1_eq_of_tau2 hG h.mem_maximal hp hA hAM
    S.isPGroup' hAS hSM (sylow_maximal_in_M_of_le hSM)
  -- the line `L ≤ A`: its order-`p` elements lie in `Ω₁(S) = A`.
  have hLA : L ≤ A := by
    rw [hΩ]
    intro g hg
    rw [Subgroup.mem_map]
    have hgS : (g : G) ∈ (S : Subgroup G) := hLS hg
    refine ⟨⟨g, hgS⟩, ?_, rfl⟩
    apply Omega.mem_of_pow_eq_one
    have hgp : (g : G) ^ p = 1 := by
      have h1 := congrArg (Subtype.val : ↥L → G) (hL.1.pow_eq_one ⟨g, hg⟩)
      simpa using h1
    exact Subtype.ext (by simpa using hgp)
  by_contra hne
  -- Corollary 12.6(c): `M` is the unique maximal subgroup over `C_G(L)`.
  have hsingle : maximalSubgroupsContaining (Subgroup.centralizer (L : Set G)) = {M} :=
    maximalContaining_centralizer_line_eq_singleton hG h hp hA hAE hL hLA hne
  -- hence `N_G(L) ⊆ M`.
  have hLne : L ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hL
  have hNL_lt : Subgroup.normalizer (L : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal (hLA.trans hAM) hLne
  have hNL_le_M : Subgroup.normalizer (L : Set G) ≤ M := by
    obtain ⟨Mst, hco, hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNL_lt.ne
    have hmem : Mst ∈ maximalSubgroupsContaining (Subgroup.centralizer (L : Set G)) :=
      mem_maximalSubgroupsContaining.mpr
        ⟨hco, (Subgroup.centralizer_le_normalizer _).trans hle⟩
    rw [hsingle, Set.mem_singleton_iff] at hmem
    exact hmem ▸ hle
  exact hNS_not_le (hLinv.trans hNL_le_M)

/-! ## Cyclic `p`-group: the order-`p` subgroup is the unique minimal one -/

/-- In a finite cyclic `p`-group, a subgroup `L` of order `p` is contained in `⟨a⟩` for every
nonidentity `a` (it is the unique minimal subgroup `Ω₁`). Working in a generator `g`: writing
`a = g^k`, `x = g^s` for `x ∈ L`, one has `gcd(N,k)·ord(a) = N = gcd(N,s)·p`, so `p ∣ ord(a)`
(`a` a nonidentity `p`-element) gives `gcd(N,k) ∣ gcd(N,s) ∣ s`, whence `x = g^s ∈ ⟨g^k⟩ = ⟨a⟩`
by Bézout. -/
theorem line_le_zpowers_in_cyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {p : ℕ} [Fact p.Prime] (hCp : IsPGroup p C) {L : Subgroup C} (hLcard : Nat.card ↥L = p)
    {a : C} (ha1 : a ≠ 1) : L ≤ Subgroup.zpowers a := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  obtain ⟨ka, hka⟩ : ∃ ka : ℕ, g ^ ka = a :=
    (Submonoid.mem_powers_iff a g).mp (mem_powers_iff_mem_zpowers.mpr (hg a))
  -- `p ∣ orderOf a` (a nonidentity `p`-element).
  have hpa : p ∣ orderOf a := by
    obtain ⟨n, hn⟩ := hCp a
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_of_pow_eq_one hn)
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [pow_zero] at hi; exact absurd (orderOf_eq_one_iff.mp hi) ha1
    · rw [hi]; exact dvd_pow_self p hipos.ne'
  intro x hxL
  rcases eq_or_ne x 1 with rfl | hx1
  · exact one_mem _
  obtain ⟨sx, hsx⟩ : ∃ sx : ℕ, g ^ sx = x :=
    (Submonoid.mem_powers_iff x g).mp (mem_powers_iff_mem_zpowers.mpr (hg x))
  -- `orderOf x = p`.
  have hxord : orderOf x = p := by
    have h1 : orderOf x ∣ p := by
      have h2 : orderOf (⟨x, hxL⟩ : ↥L) ∣ Nat.card ↥L := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk, hLcard] at h2
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  -- `gcd(N,ka) ∣ sx`, where `N = orderOf g`.
  have hga : Nat.gcd (orderOf g) ka ∣ orderOf g := Nat.gcd_dvd_left _ _
  have hgs : Nat.gcd (orderOf g) sx ∣ orderOf g := Nat.gcd_dvd_left _ _
  have ea : Nat.gcd (orderOf g) ka * orderOf a = orderOf g := by
    rw [← hka, orderOf_pow]; exact Nat.mul_div_cancel' hga
  have ex : Nat.gcd (orderOf g) sx * p = orderOf g := by
    rw [← hxord, ← hsx, orderOf_pow]; exact Nat.mul_div_cancel' hgs
  obtain ⟨t, ht⟩ := hpa
  have hcancel : Nat.gcd (orderOf g) ka * t = Nat.gcd (orderOf g) sx := by
    have heq : Nat.gcd (orderOf g) ka * t * p = Nat.gcd (orderOf g) sx * p := by
      rw [mul_assoc, mul_comm t p, ← ht, ea, ex]
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos heq
  have hdvd : Nat.gcd (orderOf g) ka ∣ sx := by
    have h1 : Nat.gcd (orderOf g) ka ∣ Nat.gcd (orderOf g) sx := ⟨t, hcancel.symm⟩
    exact dvd_trans h1 (Nat.gcd_dvd_right (orderOf g) sx)
  -- `x = g^sx ∈ ⟨g^ka⟩ = ⟨a⟩` via Bézout.
  rw [← hsx, ← hka, Subgroup.mem_zpowers_iff]
  obtain ⟨w, hw⟩ := hdvd
  refine ⟨Int.gcdA ka (orderOf g) * w, ?_⟩
  have hbez : (Nat.gcd ka (orderOf g) : ℤ)
      = (ka : ℤ) * Int.gcdA ka (orderOf g) + (orderOf g : ℤ) * Int.gcdB ka (orderOf g) :=
    Int.gcd_eq_gcd_ab ka (orderOf g)
  rw [← zpow_natCast g ka, ← zpow_mul, ← zpow_natCast g sx, zpow_eq_zpow_iff_modEq,
    Int.modEq_iff_dvd]
  have hrw : (sx : ℤ) - (ka : ℤ) * (Int.gcdA ka (orderOf g) * w)
      = (orderOf g : ℤ) * (Int.gcdB ka (orderOf g) * w) := by
    have hsxz : (sx : ℤ) = (Nat.gcd ka (orderOf g) : ℤ) * (w : ℤ) := by
      rw [Nat.gcd_comm]; exact_mod_cast hw
    rw [hsxz, hbez]; ring
  rw [hrw]
  exact dvd_mul_right _ _

/-- **Regularity transfer from the line to the whole cyclic group**: if `N` meets the centralizer
of an order-`p` line `L ≤ Z` (cyclic `p`-group) trivially, then it meets `C_G(a)` trivially for
every `a ∈ Z#`. Each such `a` has `L ≤ ⟨a⟩` (unique minimal subgroup), so `C_G(a) ≤ C_G(L)`. -/
theorem inf_centralizer_eq_bot_of_line_le_cyclic [Finite G] {Z L N : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hZp : IsPGroup p ↥Z) [IsCyclic ↥Z] (hLZ : L ≤ Z) (hLcard : Nat.card ↥L = p)
    (hNL : N ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ∀ a ∈ Z, a ≠ 1 → N ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
  intro a ha ha1
  -- `L ≤ ⟨a⟩` via the unique-minimal-subgroup lemma, transported from `↥Z` to `G`.
  have hLza : L ≤ Subgroup.zpowers a := by
    have hcard' : Nat.card ↥(L.subgroupOf Z) = p := by
      rw [← hLcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLZ).toEquiv
    have hane : (⟨a, ha⟩ : ↥Z) ≠ 1 := by
      intro hcon; exact ha1 (by simpa using congrArg Subtype.val hcon)
    have key := line_le_zpowers_in_cyclic (C := ↥Z) hZp hcard' hane
    have h1 := Subgroup.map_mono (f := Z.subtype) key
    rwa [Subgroup.map_subgroupOf_eq_of_le hLZ, MonoidHom.map_zpowers] at h1
  -- `C_G(a) = C_G(⟨a⟩) ≤ C_G(L)`.
  have hCle : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer (L : Set G) := by
    rw [← centralizer_zpowers_eq_singleton]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLza)
  rw [← le_bot_iff, ← hNL]
  exact le_inf inf_le_left (inf_le_right.trans hCle)

/-! ## φ̄ quotient action: a `q`-group `Q ≤ N_G(S)` acting FPF mod `C_Q(S)` on `S` ⟹ cyclic -/

/-- The conjugation action homomorphism `↥Q →* MulAut ↥S` of a subgroup `Q ≤ N_G(S)` on `S`
(restriction of `Subgroup.normalizerMonoidHom S` along `Q ↪ N_G(S)`). -/
def conjActionHom {S Q : Subgroup G} (hQN : Q ≤ Subgroup.normalizer (S : Set G)) :
    ↥Q →* MulAut ↥S :=
  (Subgroup.normalizerMonoidHom S).comp (Subgroup.inclusion hQN)

/-- The kernel of the conjugation action `conjActionHom` is `C_Q(S) = C_G(S) ⊓ Q`
(the elements of `Q` centralizing `S`), via `Subgroup.normalizerMonoidHom_ker`. -/
theorem conjActionHom_ker {S Q : Subgroup G} (hQN : Q ≤ Subgroup.normalizer (S : Set G)) :
    (conjActionHom hQN).ker = (Subgroup.centralizer (S : Set G)).subgroupOf Q := by
  ext a
  simp only [conjActionHom, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  rfl

/-- **φ̄ quotient action wrapper** (Theorem 12.12, Case 3 main branch, BG L3360-3366): a `q`-group
`Q ≤ N_G(S)` acting on the (`p`-group, `p ≠ q`) `S ≠ 1` by conjugation, fixed-point-freely outside
its kernel `C_Q(S)` — i.e. every `x ∈ Q` with `x ∉ C_G(S)` has `S ⊓ C_G(x) = 1` — has cyclic
quotient `Q ⧸ C_Q(S)`. The lifted conjugation hom `φ̄ : Q ⧸ ker → MulAut S` is fixed-point-free
(its `actionFixedBy` of a nonidentity coset is `C_S(x) = 1`), so Proposition 3.9
(`isCyclic_of_coprime_fpf_pgroup_action`) applies. -/
theorem isCyclic_quotient_of_conjugation_fpf [Finite G]
    {S Q : Subgroup G} {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hQN : Q ≤ Subgroup.normalizer (S : Set G))
    (hSp : IsPGroup p ↥S) (hQq : IsPGroup q ↥Q) (hSne : S ≠ ⊥)
    (hq_odd : Odd q) (hpq : p ≠ q)
    (hfpf : ∀ x ∈ Q, x ∉ Subgroup.centralizer (S : Set G) →
      (S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) = ⊥) :
    IsCyclic (↥Q ⧸ (conjActionHom hQN).ker) := by
  classical
  haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  haveI hRq : IsPGroup q (↥Q ⧸ (conjActionHom hQN).ker) := hQq.to_quotient _
  -- coprimality of `|Q/ker|` (a `q`-power) and `|S|` (a `p`-power), `p ≠ q`.
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := q)).mp hRq
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hSp
  have hcop : Nat.Coprime (Nat.card (↥Q ⧸ (conjActionHom hQN).ker)) (Nat.card ↥S) := by
    rw [hm, hn]
    exact ((Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).mpr
      (Ne.symm hpq)).pow m n
  -- apply Proposition 3.9 to the lifted conjugation hom.
  refine isCyclic_of_coprime_fpf_pgroup_action hRq hq_odd hcop
    (QuotientGroup.kerLift (conjActionHom hQN)) ?_
  intro ā hā
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective ā
  -- `a ∉ ker`, i.e. `(a:G) ∉ C_G(S)`.
  have ha_ker : a ∉ (conjActionHom hQN).ker := fun hmem =>
    hā ((QuotientGroup.eq_one_iff a).mpr hmem)
  have ha_cent : (a : G) ∉ Subgroup.centralizer (S : Set G) := by
    rw [conjActionHom_ker, Subgroup.mem_subgroupOf] at ha_ker; exact ha_ker
  -- the fixed subgroup of the coset `mk a` is `⊥` (regularity of `x` on `S`).
  rw [eq_bot_iff]
  intro s hs
  rw [mem_actionFixedBy, QuotientGroup.kerLift_mk] at hs
  have hsval : (a : G) * (s : G) * (a : G)⁻¹ = (s : G) := congrArg Subtype.val hs
  have hcomm : (a : G) * (s : G) = (s : G) * (a : G) := mul_inv_eq_iff_eq_mul.mp hsval
  have hmem : (s : G) ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({(a : G)} : Set G) := by
    rw [Subgroup.mem_inf]
    refine ⟨s.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    exact hcomm
  rw [hfpf (a : G) a.2 ha_cent, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact Subtype.ext hmem

/-! ## Back-half (Z construction): rank-2 abelian split ⟹ factors cyclic -/

/-- In a finite abelian `p`-group `T` (`p` odd) of `p`-rank `≤ 2`, a subgroup `T₀` disjoint from a
*nontrivial* subgroup `T₁` is cyclic. If `T₀` were noncyclic it would contain an elementary abelian
`B₀ ≤ T₀` of order `p²`; with an order-`p` element `y ∈ T₁`, the join `B₀ ⊔ ⟨y⟩` (disjoint since
`T₀ ⊓ T₁ = ⊥`) is elementary abelian of order `p³`, forcing `pRank T ≥ 3`, a contradiction.
Used in Theorem 12.12 Case 3 for `S = C_S(X) × [S,X]`: both factors are cyclic since `r(S) = 2`. -/
theorem isCyclic_of_inf_eq_bot_of_pRank_le_two {T : Type*} [CommGroup T] [Finite T] {p : ℕ}
    [Fact p.Prime] (hTp : IsPGroup p T) (hodd : Odd p) (hrank : pRank T p ≤ 2)
    {T₀ T₁ : Subgroup T} (hdisj : T₀ ⊓ T₁ = ⊥) (hT₁ : T₁ ≠ ⊥) :
    IsCyclic ↥T₀ := by
  classical
  by_contra hnc
  -- noncyclic `T₀` contains an elementary abelian `B₀` of order `p²`.
  obtain ⟨B₀, hB₀ea, hB₀card⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
      (hTp.to_subgroup T₀) hodd hnc
  set B : Subgroup T := B₀.map T₀.subtype with hB_def
  have hBea : B.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.map T₀.subtype_injective hB₀ea
  have hBT₀ : B ≤ T₀ := Subgroup.map_subtype_le B₀
  have hBcard : Nat.card ↥B = p ^ 2 := by
    rw [hB_def, ← hB₀card]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective B₀ T₀.subtype T₀.subtype_injective).symm.toEquiv
  -- an order-`p` element `y ∈ T₁`.
  haveI : Nontrivial ↥T₁ := (Subgroup.nontrivial_iff_ne_bot T₁).mpr hT₁
  have hp_dvd : p ∣ Nat.card ↥T₁ := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).mp (hTp.to_subgroup T₁)
    have h1lt : 1 < Nat.card ↥T₁ := Finite.one_lt_card
    have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; omega
    rw [hk]; exact dvd_pow_self p hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  set y : T := T₁.subtype x with hy_def
  have hyT₁ : y ∈ T₁ := x.2
  have hyord : orderOf y = p := by
    rw [hy_def, orderOf_injective T₁.subtype T₁.subtype_injective x]; exact hx
  -- `⟨y⟩` is elementary abelian of order `p`.
  have hZcard : Nat.card ↥(Subgroup.zpowers y) = p := by rw [Nat.card_zpowers]; exact hyord
  have hZea : (Subgroup.zpowers y).IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.of_card_prime hZcard
  have hZT₁ : Subgroup.zpowers y ≤ T₁ := by rw [Subgroup.zpowers_le]; exact hyT₁
  -- `B ⊓ ⟨y⟩ = ⊥` (both inside the disjoint `T₀`, `T₁`).
  have hBZ_disj : B ⊓ Subgroup.zpowers y = ⊥ := by
    rw [← le_bot_iff, ← hdisj]
    exact le_inf (inf_le_left.trans hBT₀) (inf_le_right.trans hZT₁)
  -- `B ⊔ ⟨y⟩` is elementary abelian of order `p³`, so `pRank T ≥ 3`.
  have hcent : B ≤ Subgroup.centralizer (Subgroup.zpowers y : Set T) :=
    fun b _ => Subgroup.mem_centralizer_iff.mpr (fun g _ => mul_comm g b)
  have hsupea : (B ⊔ Subgroup.zpowers y).IsElementaryAbelian p :=
    isElementaryAbelian_sup_of_le_centralizer hBea hZea hcent
  have hsupcard : Nat.card ↥(B ⊔ Subgroup.zpowers y) = p ^ 3 := by
    rw [OddOrder.BG.Ch1.S01.card_sup_eq_card_mul_card_of_disjoint_normal hBZ_disj, hBcard, hZcard]
    ring
  have hle := le_pRank (B ⊔ Subgroup.zpowers y) hsupea
  rw [hsupcard, Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
  omega

end OddOrder.BG.Ch3.S12
