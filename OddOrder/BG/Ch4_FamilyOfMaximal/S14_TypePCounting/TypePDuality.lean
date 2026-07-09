import OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting.SigmaLengthOne

/-!
# BG Theorem 14.7 — Z = K ⊔ K* internal direct product (duality bedrock)

Split from the former monolithic `OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting` (directory split, issue 0103).
-/
namespace OddOrder.BG.Ch4.S14
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch3.S13
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ## Theorem 14.7 through Lemma 14.13: type-P duality and global counting -/

/-! ### `Z = K ⊔ K*` internal direct product (BG 14.7 bedrock)

For a type-`P` maximal `M`, a Hall `κ(M)`-subgroup `K`, and `K* = C_{M_σ}(K)`, the join
`Z = K ⊔ K*` is the *internal direct product* of `K` and `K*`: their orders are coprime
(`K` a `σ(M)'`-group since `κ(M) ⊆ σ(M)'`, `K* ≤ M_σ` a `σ(M)`-group), and they commute
(`K* ≤ C_G(K)`).  Hence `K ⊓ K* = 1`, `|Z| = |K|·|K*|`, and — once both factors are cyclic
(which the §14 counting collapse forces, BG L4041) — `Z` is cyclic.

These are the *ungated* structural facts underlying the density count of Theorem 14.7(e)
(`|𝒞_G(Ẑ)| = (1 - 1/k - 1/k* + 1/kk*)|G|`, mmd L4031-4045) and the `IsCyclic (K ⊔ K*)`
conjunct (d).  They depend only on `K` being a Hall `κ(M)`-subgroup and `K* = C_{M_σ}(K)`,
not on the type-P duality counting itself. -/

/-- A Hall `κ(M)`-subgroup `K` is a `σ(M)'`-subgroup (since `κ(M) ⊆ σ(M)'`).  Extracted from
the `hK_pi` step internal to `typeP_structure` for reuse in the `Z`-structure lemmas. -/
theorem kappaHall_isPiSubgroup_sigmaCompl {M K : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) :
    Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := by
  intro p hp
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
  exact kappa_subset_sigmaCompl (hK.1 p hp)

/-- `K* = C_{M_σ}(K)` is a `σ(M)`-subgroup (it lies in `M_σ`, a `σ(M)`-group). -/
theorem Kstar_isPiSubgroup_sigma [Finite G] {M K Kstar : Subgroup G}
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Kstar := by
  intro p hp
  have hle : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := hKstar ▸ inf_le_left
  obtain ⟨hpp, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
  refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
    ⟨hpp, hpdvd.trans (Subgroup.card_dvd_of_le hle), Nat.card_pos.ne'⟩)

/-- **BG 14.7, `|K|`, `|K*|` coprime** (mmd L4027): `K` is a `σ(M)'`-group, `K* ≤ M_σ` a
`σ(M)`-group, so no prime divides both. -/
theorem coprime_card_kappaHall_Kstar [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Nat.Coprime (Nat.card ↥K) (Nat.card ↥Kstar) := by
  apply Nat.coprime_of_dvd
  intro p hp hpK hpKstar
  have hpσc : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
    kappaHall_isPiSubgroup_sigmaCompl hKM hK p
      (Nat.mem_primeFactors.mpr ⟨hp, hpK, Nat.card_pos.ne'⟩)
  exact hpσc (Kstar_isPiSubgroup_sigma hKstar p
    (Nat.mem_primeFactors.mpr ⟨hp, hpKstar, Nat.card_pos.ne'⟩))

/-- **BG 14.7, `|K| > 1`**: the κ-Hall factor of a type-`P` maximal subgroup is nontrivial.  Some
prime `p ∈ κ(M)` divides `|K|`: `p` divides `|M|` (it is the order of an elementary abelian
`p`-subgroup of `M`, by the definition of `κ`), and is coprime to the Hall index `[M : K]`, so it
divides the Hall order `|K|`. -/
theorem card_kappaHall_ne_one [Finite G] {M K : Subgroup G} (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) :
    Nat.card ↥K ≠ 1 := by
  obtain ⟨p, hpκ⟩ := hP
  have hpprime : p.Prime := hpκ.1
  obtain ⟨P, hPelem, hPM, -⟩ := hpκ.2.2
  have hpcardP : Nat.card ↥P = p := by obtain ⟨_, hc⟩ := hPelem; rwa [pow_one] at hc
  have hpM : p ∣ Nat.card ↥M := hpcardP ▸ Subgroup.card_dvd_of_le hPM
  have hpK : p ∣ Nat.card ↥K := by
    have hlag : Nat.card ↥K * (K.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact Subgroup.card_mul_index (K.subgroupOf M)
    have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hd =>
      hK.2 p (Nat.mem_primeFactors.mpr ⟨hpprime, hd, Subgroup.index_ne_zero_of_finite⟩) hpκ
    exact (hpprime.dvd_mul.mp (hlag.symm ▸ hpM)).resolve_right hpidx
  exact fun h => hpprime.ne_one (Nat.dvd_one.mp (h ▸ hpK))

/-- **BG 14.7, `|K| ≠ |K*|`**: the two κ-Hall factors of a type-`P` dual pair have distinct orders.
They are coprime (`coprime_card_kappaHall_Kstar`) and `|K| > 1` (`card_kappaHall_ne_one`), so equality
would force `|K| = 1`. -/
theorem card_kappaHall_ne_card_Kstar [Finite G] {M K Kstar : Subgroup G} (hP : IsTypeP M)
    (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Nat.card ↥K ≠ Nat.card ↥Kstar := by
  intro heq
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Kstar) :=
    coprime_card_kappaHall_Kstar hKM hK hKstar
  rw [← heq, Nat.Coprime, Nat.gcd_self] at hcop
  exact card_kappaHall_ne_one hP hKM hK hcop

/-- **BG 14.7, `K ⊓ K* = 1`**: the coprime factors meet trivially. -/
theorem kappaHall_inf_Kstar_eq_bot [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    K ⊓ Kstar = ⊥ :=
  Subgroup.inf_eq_bot_of_coprime (coprime_card_kappaHall_Kstar hKM hK hKstar)

/-- **BG 14.7, `K*` centralizes `K`**: every element of `K` commutes with every element of
`K* = C_{M_σ}(K)` (which lies in `C_G(K)`). -/
theorem commute_kappaHall_Kstar {M K Kstar : Subgroup G}
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    ∀ (a : ↥K) (b : ↥Kstar), Commute (K.subtype a) (Kstar.subtype b) := by
  intro a b
  have hb : (b : G) ∈ Subgroup.centralizer (K : Set G) := by
    have hbmem : (b : G) ∈
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) := by
      rw [← hKstar]; exact b.2
    exact (Subgroup.mem_inf.mp hbmem).2
  exact Subgroup.mem_centralizer_iff.mp hb (a : G) a.2

/-- **BG 14.7, `Z = K × K*` internal direct product iso** `↥K × ↥K* ≃* ↥(K ⊔ K*)`,
`(a, b) ↦ a·b` (well-defined since `K`, `K*` commute, injective since `K ⊓ K* = 1`). -/
noncomputable def kappaHall_prod_Kstar_mulEquiv [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    (↥K × ↥Kstar) ≃* ↥(K ⊔ Kstar) := by
  have hcomm := commute_kappaHall_Kstar hKstar
  have hinj : Function.Injective (MonoidHom.noncommCoprod K.subtype Kstar.subtype hcomm) :=
    (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
      ⟨K.subtype_injective, Kstar.subtype_injective, by
        rw [K.range_subtype, Kstar.range_subtype]
        exact disjoint_iff.mpr (kappaHall_inf_Kstar_eq_bot hKM hK hKstar)⟩
  have hrange : (MonoidHom.noncommCoprod K.subtype Kstar.subtype hcomm).range = K ⊔ Kstar := by
    rw [MonoidHom.noncommCoprod_range, K.range_subtype, Kstar.range_subtype]
  exact (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)

/-- **BG 14.7, `|Z| = |K|·|K*|`** (mmd L4029, `z = k k*`): the internal direct product order. -/
theorem card_kappaHall_sup_Kstar [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Nat.card ↥(K ⊔ Kstar) = Nat.card ↥K * Nat.card ↥Kstar := by
  rw [← Nat.card_congr (kappaHall_prod_Kstar_mulEquiv hKM hK hKstar).toEquiv, Nat.card_prod]

/-- **BG 14.7(d), `Z = K ⊔ K*` cyclic** (mmd L4041): once both factors are cyclic (forced by the
counting collapse `n = 1`, where `r(K) = r(K*) = 1`), the coprime commuting product is cyclic. -/
theorem isCyclic_kappaHall_sup_Kstar_of_cyclic [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    [IsCyclic ↥K] [IsCyclic ↥Kstar] :
    IsCyclic ↥(K ⊔ Kstar) := by
  have hprodcyc : IsCyclic (↥K × ↥Kstar) :=
    Group.isCyclic_prod_iff.mpr
      ⟨inferInstance, inferInstance, coprime_card_kappaHall_Kstar hKM hK hKstar⟩
  exact (kappaHall_prod_Kstar_mulEquiv hKM hK hKstar).isCyclic.mp hprodcyc

/-- **BG 14.7(h), coprimality is free given the complement**: if `M' = [M,M]` complements the
Hall `κ(M)`-subgroup `K` in `M`, then `|M'|` and `|K|` are coprime — `|M'| = [M : K]` (from the
complement) and a Hall subgroup has order coprime to its index.  This reduces Theorem 14.7(h) to its
substantive obligation `IsComplement' M' K` (mmd L4061, which consumes "`K` cyclic" from the
counting collapse); the second conjunct then follows with no further input. -/
theorem coprime_card_derived_kappaHall_of_isComplement' [Finite G] {M K : Subgroup G}
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hc : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M)) :
    Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M)) (Nat.card ↥(K.subgroupOf M)) := by
  have hcop := hK.coprime_index
  rw [hc.index_eq_card] at hcop
  exact hcop.symm

/-- **Counting-bound kernel for Theorem 14.7(e)** (BG mmd L3975, the `8/15 > 1/2` step).
For `k ≥ 3` and `k* ≥ 5`, the saturation density `(1 - 1/k)(1 - 1/k*)` exceeds `1/2`
(minimised at `(1 - 1/3)(1 - 1/5) = 8/15`).  In Theorem 14.7, `k = |K|` and `k* = |K*|` are
coprime odd integers `> 1` (so `{k, k*} ⊇ {3, 5}` in the worst case), and
`|𝒞_G(Ẑ)| = (1 - 1/k)(1 - 1/k*)|G|`; this bound gives `|𝒞_G(Ẑ)| > ½|G|`, forcing every type-P
maximal subgroup to be conjugate to `M` or `M*`.  Pure arithmetic, independent of §13. -/
theorem half_lt_one_sub_inv_mul {k l : ℕ} (hk : 3 ≤ k) (hl : 5 ≤ l) :
    (1 : ℚ) / 2 < (1 - 1 / (k : ℚ)) * (1 - 1 / (l : ℚ)) := by
  have hk3 : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hl5 : (5 : ℚ) ≤ (l : ℚ) := by exact_mod_cast hl
  have hik : 1 / (k : ℚ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hk3
  have hil : 1 / (l : ℚ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hl5
  calc (1 : ℚ) / 2 < (2 / 3) * (4 / 5) := by norm_num
    _ ≤ (1 - 1 / (k : ℚ)) * (1 - 1 / (l : ℚ)) :=
        mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)

/-- **BG Theorem 14.7, partner existence** (§16-independent core, mmd L3975-3991): for a type-`P`
maximal `M` with Hall `κ(M)`-subgroup `K`, `Kstar = C_{M_σ}(K)`, and a line `X ∈ ℰ_p¹(K)`, every
`M* ∈ 𝓜(N_G(X))` (which exists, `N_G(X)` being proper) is type-`P`, nonconjugate to `M`, contains
`K ⊔ Kstar` with `X ≤ M*_σ`, and `π(Kstar) ⊆ κ(M*)`.  This is the nonconjugate partner `M*` of
Theorem 14.7 with its basic neighbour data; cyclicity of `Z`, the TI property, type-`P₂`, and the
§16-gated covering/uniqueness are layered on top.  Built from `typeP_neighbor_embed` +
`typeP_neighbor_kappa` (the §16-independent pre-position, steps 1a/1b). -/
theorem exists_typeP_partner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K) :
    ∃ Mstar : Subgroup G,
      Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ∧
      ¬ IsConjugateSubgroup M Mstar ∧ K ⊔ Kstar ≤ Mstar ∧
      X ≤ OddOrder.BG.Ch3.S10.Msigma Mstar ∧
      (∀ q ∈ (Nat.card ↥Kstar).primeFactors, q ∈ kappa Mstar) ∧ IsTypeP Mstar := by
  classical
  have hKstarne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  -- `C_{M_σ}(X) ⊇ C_{M_σ}(K) = Kstar ≠ 1`.
  have hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
    intro hbot
    refine hKstarne (le_bot_iff.mp ?_)
    rw [hKstar]
    calc OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
        ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) :=
          inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK))
      _ = ⊥ := hbot
  have hXne : X ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hX
  obtain ⟨Mstar, hMstarmax, hMstarge⟩ :=
    OddOrder.BG.Ch2.S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
      hG hM hXne (hXK.trans hKM)
  have hMstarmem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstarmax, hMstarge⟩
  obtain ⟨hnc, hZle, hXMsσ⟩ :=
    typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hMstarmem
  have hκ := typeP_neighbor_kappa hG hM hP hKM hK hKstar hU hX hXK hCX hMstarmem
  haveI : Nontrivial ↥Kstar := (Subgroup.nontrivial_iff_ne_bot _).mpr hKstarne
  obtain ⟨q, hq⟩ : (Nat.card ↥Kstar).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  exact ⟨Mstar, hMstarmem, hnc, hZle, hXMsσ, hκ, ⟨q, hκ q hq⟩⟩

/-- **σ-part lands in the σ-factor of an internal direct product**: in `Ki ⊔ Kistar`, where `Kistar`
centralizes `Ki`, `Kistar ≤ M_σ`, and `Ki ⊓ M_σ = ⊥` (e.g. `Ki` is a `σ(Mi)'`-group), any subgroup
`X ≤ Ki ⊔ Kistar` contained in `M_σ` lies in `Kistar`.  Writing `x = a·b` (`a ∈ Ki`, `b ∈ Kistar`),
the `σ'`-part `a = x·b⁻¹ ∈ M_σ ⊓ Ki = ⊥`, so `x = b ∈ Kistar`.  This is the `σ`-projection used by
the swap argument (BG mmd L3999, "it follows that `X_i ⊆ K_i*`") and the `Z`-decomposition. -/
theorem le_centralizerFactor_of_le_sup_of_le_Msigma [Finite G] {Mi Ki Kistar X : Subgroup G}
    (hKistarC : Kistar ≤ Subgroup.centralizer (Ki : Set G))
    (hKistarMσ : Kistar ≤ OddOrder.BG.Ch3.S10.Msigma Mi)
    (hKiMσ : Ki ⊓ OddOrder.BG.Ch3.S10.Msigma Mi = ⊥)
    (hXsup : X ≤ Ki ⊔ Kistar) (hXMσ : X ≤ OddOrder.BG.Ch3.S10.Msigma Mi) :
    X ≤ Kistar := by
  classical
  -- `Ki` is normal in `Ki ⊔ Kistar` (`Kistar` centralizes it), so elements decompose as `a · b`.
  have hKnorm : Ki ⊔ Kistar ≤ Subgroup.normalizer (Ki : Set G) :=
    sup_le Subgroup.le_normalizer (hKistarC.trans (Subgroup.centralizer_le_normalizer _))
  haveI : ((Ki).subgroupOf (Ki ⊔ Kistar)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKnorm
  have hsuptop : (Ki.subgroupOf (Ki ⊔ Kistar)) ⊔ (Kistar.subgroupOf (Ki ⊔ Kistar)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
    (hsuptop ▸ Subgroup.mem_top (⟨x, hXsup hx⟩ : ↥(Ki ⊔ Kistar)))
  have haKi : (a : G) ∈ Ki := Subgroup.mem_subgroupOf.mp ha
  have hbKistar : (b : G) ∈ Kistar := Subgroup.mem_subgroupOf.mp hb
  have hab' : (a : G) * (b : G) = x := by have := congrArg Subtype.val hab; simpa using this
  have haMσ : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma Mi := by
    have heq : (a : G) = x * (b : G)⁻¹ := by rw [← hab']; group
    rw [heq]
    exact (OddOrder.BG.Ch3.S10.Msigma Mi).mul_mem (hXMσ hx)
      ((OddOrder.BG.Ch3.S10.Msigma Mi).inv_mem (hKistarMσ hbKistar))
  have ha1 : (a : G) = 1 := Subgroup.mem_bot.mp (hKiMσ ▸ Subgroup.mem_inf.mpr ⟨haKi, haMσ⟩)
  rw [← hab', ha1, one_mul]; exact hbKistar

/-- **BG 14.7, neighbour normalizer identity** (Proposition 14.2(b1) packaged for a neighbour,
mmd L3997): for a type-`P` maximal `Mi`, a Hall `κ(Mi)`-subgroup `Ki ≤ Mi`, and a rank-one
`X ≤ Ki`, `N_G(X) ⊓ Mi = Ki ⊔ C_{Mi_σ}(Ki)`.  The Hall `(κ(Mi) ∪ σ(Mi))'`-subgroup that
Proposition 14.2 needs is produced internally via `hall_E_exists` (in the solvable group `↥Mi`),
so the swap argument supplies only `Ki` and `X`.  Applied twice — to `Ki` and to a Hall
`κ(Mi)`-subgroup `Ki' ⊇ K*` — it yields `Ki ⊔ Ki* = N_G(X) ⊓ Mi = Ki' ⊔ Ki'*`, the choice
independence at the heart of the swap. -/
theorem typeP_normalizer_inf_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {Mi Ki : Subgroup G} (hMi : Mi ∈ maximalSubgroups G) (hPi : IsTypeP Mi)
    (hKiMi : Ki ≤ Mi) (hKi : Ch03.IsHallSubgroup (kappa Mi) (Ki.subgroupOf Mi))
    {p : ℕ} (hp : p.Prime) {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXKi : X ≤ Ki) :
    Subgroup.normalizer (X : Set G) ⊓ Mi =
      Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) := by
  classical
  haveI : IsSolvable ↥Mi := hG.solvable_of_mem_maximalSubgroups hMi
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mi)
    ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
  have hUeq : (U'.map Mi.subtype).subgroupOf Mi = U' :=
    Subgroup.comap_map_eq_self_of_injective Mi.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
      ((U'.map Mi.subtype).subgroupOf Mi) := by rw [hUeq]; exact hU'
  obtain ⟨_, _, hb1, _, _, _⟩ := typeP_structure hG hMi hPi hKiMi hKi rfl hU
  exact hb1 p hp X hX hXKi

/-- **BG 14.7, `M ⊇ N_G(X)` from a unique centralizer-maximal** (mmd L3992, "Moreover, `M ⊇
N_G(X)`"): if `M` is the *unique* maximal subgroup containing `C_G(X)` (i.e.
`ℳ(C_G(X)) = {M}`, the conclusion of Proposition 14.2(c)), then `N_G(X) ≤ M`.

For `g ∈ N_G(X)`, conjugation by `g` fixes `C_G(X)` (`g` normalizes `X`), so `Mᵍ` is again a
maximal subgroup containing `C_G(X)`; by uniqueness `Mᵍ = M`, hence `g ∈ N_G(M) = M`
(`M` self-normalizing as a maximal subgroup).  A general fact, independent of §13. -/
theorem normalizer_le_of_maximalSubgroupsContaining_centralizer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M X : Subgroup G}
    (hsing : maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  classical
  have hMmem : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
    rw [hsing]; rfl
  rw [mem_maximalSubgroupsContaining] at hMmem
  obtain ⟨hMcoat, hCXM⟩ := hMmem
  intro g hg
  -- `g` normalizes `X`, hence normalizes `C_G(X)`: `Mᵍ ⊇ C_G(X)ᵍ = C_G(X)`.
  have hgcent : MulAut.conj g • Subgroup.centralizer (X : Set G)
      = Subgroup.centralizer (X : Set G) := by
    have h1 : MulAut.conj g • Subgroup.centralizer (X : Set G)
        = Subgroup.centralizer ((MulAut.conj g • X : Subgroup G) : Set G) :=
      Subgroup.map_centralizer_eq_of_bijective (X : Set G) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).bijective
    rwa [OddOrder.GroupTheory.conj_smul_eq_self_of_mem_normalizer hg] at h1
  -- `Mᵍ` is a maximal subgroup containing `C_G(X)`, so by uniqueness `Mᵍ = M`.
  have hgM_mem : (MulAut.conj g • M) ∈
      maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
    rw [mem_maximalSubgroupsContaining]
    refine ⟨OddOrder.BG.Ch3.S12.isCoatom_conj_smul hMcoat, ?_⟩
    rw [← hgcent]
    exact (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hCXM
  rw [hsing, Set.mem_singleton_iff] at hgM_mem
  -- `Mᵍ = M` gives `g ∈ N_G(M) = M`.
  have hgNM : g ∈ Subgroup.normalizer (M : Set G) :=
    OddOrder.GroupTheory.mem_normalizer_of_conj_smul_eq_self hgM_mem
  rwa [normalizer_eq_self_of_mem_maximalSubgroups hG (mem_maximalSubgroups.mpr hMcoat)] at hgNM

/-- **BG 14.7, swap argument — direction `⊆`** (mmd L3999): with `M` type-`P`, `K* = C_{M_σ}(K)`,
and a neighbour `Mi` containing `Z = K ⊔ K*` with `π(K*) ⊆ κ(Mi)`, for any line `X* ≤ K*` and any
Hall `κ(Mi)`-subgroup `Ki ∋ X*` (with `Ki* = C_{Mi_σ}(Ki)`),
`K ⊔ K* ≤ Ki ⊔ Ki*`.

`K`-part: `K` centralizes `K* ⊇ X*`, so `K ≤ N_G(X*)`, and `K ≤ Mi`; thus `K ≤ N_G(X*) ⊓ Mi =
Ki ⊔ Ki*` (Proposition 14.2(b1) for `Mi`).  `K*`-part (the "swap"): `K*` is a `κ(Mi)`-subgroup, so
it lies in *some* Hall `κ(Mi)`-subgroup `Ki' ⊇ K*`, and `N_G(X*) ⊓ Mi = Ki' ⊔ Ki'*` is the *same*
group as `Ki ⊔ Ki*` (it depends only on `X*`, not on the chosen Hall subgroup), so
`K* ≤ Ki' ≤ Ki ⊔ Ki*`. -/
theorem typeP_swap_Z_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar Mi Ki : Subgroup G}
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hMi : Mi ∈ maximalSubgroups G) (hPi : IsTypeP Mi) (hZMi : K ⊔ Kstar ≤ Mi)
    (hKstarκ : ∀ q ∈ (Nat.card ↥Kstar).primeFactors, q ∈ kappa Mi)
    {p : ℕ} (hp : p.Prime) {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXKstar : X ≤ Kstar)
    (hKiMi : Ki ≤ Mi) (hKi : Ch03.IsHallSubgroup (kappa Mi) (Ki.subgroupOf Mi)) (hXKi : X ≤ Ki) :
    K ⊔ Kstar ≤ Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) := by
  classical
  set Kistar := OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G) with hKistar
  -- `N_G(X) ⊓ Mi = Ki ⊔ Ki*` (Proposition 14.2(b1) for `Mi`, the reference choice of Hall subgroup).
  have hNeq : Subgroup.normalizer (X : Set G) ⊓ Mi = Ki ⊔ Kistar :=
    typeP_normalizer_inf_eq hG hMi hPi hKiMi hKi hp hX hXKi
  -- `K` centralizes `K*` (since `K* ≤ C_G(K)`), hence `K ≤ C_G(X) ≤ N_G(X)`.
  have hKCKstar : K ≤ Subgroup.centralizer (Kstar : Set G) := by
    have hKstarCK : Kstar ≤ Subgroup.centralizer (K : Set G) := hKstar ▸ inf_le_right
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (hKstarCK hs) k hk).symm
  have hKNX : K ≤ Subgroup.normalizer (X : Set G) :=
    (hKCKstar.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXKstar))).trans
      (Subgroup.centralizer_le_normalizer _)
  -- `K ≤ N_G(X) ⊓ Mi = Ki ⊔ Ki*`.
  have hKle : K ≤ Ki ⊔ Kistar := by
    rw [← hNeq]; exact le_inf hKNX (le_sup_left.trans hZMi)
  -- `K* ≤ Ki ⊔ Ki*` via the swap: pick a Hall `κ(Mi)`-subgroup `Ki' ⊇ K*`.
  have hKstarle : Kstar ≤ Ki ⊔ Kistar := by
    have hKstarMi : Kstar ≤ Mi := le_sup_right.trans hZMi
    obtain ⟨Ki', hKi'Mi, hKi', hKstarKi'⟩ :=
      exists_isHallSubgroup_kappa_ge hG hMi hKstarMi hKstarκ
    have hNeq' : Subgroup.normalizer (X : Set G) ⊓ Mi =
        Ki' ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki' : Set G)) :=
      typeP_normalizer_inf_eq hG hMi hPi hKi'Mi hKi' hp hX (hXKstar.trans hKstarKi')
    calc Kstar ≤ Ki' := hKstarKi'
      _ ≤ Ki' ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki' : Set G)) := le_sup_left
      _ = Subgroup.normalizer (X : Set G) ⊓ Mi := hNeq'.symm
      _ = Ki ⊔ Kistar := hNeq
  exact sup_le hKle hKstarle

/-- **BG 14.7, swap argument — the `Z`-coincidence** (mmd L3999-4001): the neighbour `Mi`'s own
direct-product decomposition coincides with `Z`, i.e. `Z = K ⊔ K* = Ki ⊔ Ki*`.

`M`/`K`/`K*` are the type-`P` data, `Mi` a nonconjugate type-`P` neighbour (e.g. the partner
`exists_typeP_partner` from a line `Xi ∈ ℰ¹(K)`) containing `Z` with `π(K*) ⊆ κ(Mi)`,
`Xi ⊆ Mi_σ`; `X* ∈ ℰ¹(K*)` is a line lying in a Hall `κ(Mi)`-subgroup `Ki`, with
`Ki* = C_{Mi_σ}(Ki)`.  Direction `⊆` is `typeP_swap_Z_le`.  Direction `⊇` re-runs the swap with
the roles of `(M, K, X*)` and `(Mi, Ki, Xi)` exchanged, using:
* `M ⊇ N_G(X*)` (`normalizer_le_of_maximalSubgroupsContaining_centralizer` applied to Prop 14.2(c)'s
  `ℳ(C_G(X*)) = {M}`), which gives `Ki ⊔ Ki* = N_G(X*) ⊓ Mi ≤ M`;
* `π(Ki*) ⊆ κ(M)` (`typeP_neighbor_kappa` for `Mi`, since `M` is the partner of `Mi` via `X*`);
* `Xi ⊆ Ki*` (`le_centralizerFactor_of_le_sup_of_le_Msigma`: `Xi`, a `σ(Mi)`-group inside
  `Ki × Ki*`, lands in the `σ`-factor `Ki*`). -/
theorem typeP_swap_Z_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mi Ki : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMimax : Mi ∈ maximalSubgroups G) (hPi : IsTypeP Mi) (hZMi : K ⊔ Kstar ≤ Mi)
    (hKstarκ : ∀ q ∈ (Nat.card ↥Kstar).primeFactors, q ∈ kappa Mi)
    {pstar : ℕ} (hpstar : pstar.Prime) {Xstar : Subgroup G}
    (hXstar : Xstar ∈ elemAbelianOfRank G pstar 1) (hXstarKstar : Xstar ≤ Kstar)
    (hXstarKi : Xstar ≤ Ki)
    {pi : ℕ} (hpi : pi.Prime) {Xi : Subgroup G}
    (hXi : Xi ∈ elemAbelianOfRank G pi 1) (hXiK : Xi ≤ K)
    (hXiMiσ : Xi ≤ OddOrder.BG.Ch3.S10.Msigma Mi)
    (hKiMi : Ki ≤ Mi) (hKi : Ch03.IsHallSubgroup (kappa Mi) (Ki.subgroupOf Mi)) :
    K ⊔ Kstar = Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) := by
  classical
  haveI : Fact pstar.Prime := ⟨hpstar⟩
  -- Direction `⊆` (the original swap).
  have hle1 : K ⊔ Kstar ≤
      Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) :=
    typeP_swap_Z_le hG hKstar hMimax hPi hZMi hKstarκ hpstar hXstar hXstarKstar hKiMi hKi hXstarKi
  -- `ℳ(C_G(X*)) = {M}` (Prop 14.2(c)) and hence `N_G(X*) ≤ M`.
  obtain ⟨_, _, _, _, _, hc, _⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  have hNXstarM : Subgroup.normalizer (Xstar : Set G) ≤ M :=
    normalizer_le_of_maximalSubgroupsContaining_centralizer hG
      (hc pstar hpstar Xstar hXstar hXstarKstar)
  -- `N_G(X*) ⊓ Mi = Ki ⊔ Ki*` (Prop 14.2(b1) for `Mi`).
  have hZiMi : Subgroup.normalizer (Xstar : Set G) ⊓ Mi =
      Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) :=
    typeP_normalizer_inf_eq hG hMimax hPi hKiMi hKi hpstar hXstar hXstarKi
  -- (A) `Ki ⊔ Ki* ≤ M`.
  have hA : Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) ≤ M := by
    rw [← hZiMi]; exact inf_le_left.trans hNXstarM
  -- A Hall `(κ(Mi) ∪ σ(Mi))'`-subgroup of `Mi` (for Proposition 14.2 applied to `Mi`).
  haveI : IsSolvable ↥Mi := hG.solvable_of_mem_maximalSubgroups hMimax
  obtain ⟨Ui', hUi'⟩ := Ch03.hall_E_exists (G := ↥Mi)
    ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
  have hUieq : (Ui'.map Mi.subtype).subgroupOf Mi = Ui' :=
    Subgroup.comap_map_eq_self_of_injective Mi.subtype_injective Ui'
  have hUi : Ch03.IsHallSubgroup ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
      ((Ui'.map Mi.subtype).subgroupOf Mi) := by rw [hUieq]; exact hUi'
  -- (B) `π(Ki*) ⊆ κ(M)`: `M` is the partner of `Mi` via `X*` (`ℳ(N_G(X*)) = {M}`).
  have hKistarne : OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G) ≠ ⊥ :=
    (typeP_structure hG hMimax hPi hKiMi hKi rfl hUi).2.1
  have hCXstarMi : OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Xstar : Set G) ≠ ⊥ :=
    fun hbot => hKistarne (le_bot_iff.mp (hbot ▸ inf_le_inf_left _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXstarKi))))
  have hM_in_NXstar : M ∈ maximalSubgroupsContaining (Subgroup.normalizer (Xstar : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hM, hNXstarM⟩
  have hB : ∀ q ∈ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma Mi ⊓
      Subgroup.centralizer (Ki : Set G))).primeFactors, q ∈ kappa M :=
    typeP_neighbor_kappa hG hMimax hPi hKiMi hKi rfl hUi hXstar hXstarKi hCXstarMi hM_in_NXstar
  -- (C) `Xi ≤ Ki*` (`σ`-part extraction).
  have hXiCXstar : Xi ≤ Subgroup.centralizer (Xstar : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyCK : y ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.mem_inf.mp (hKstar ▸ hXstarKstar hy)).2
    exact (Subgroup.mem_centralizer_iff.mp hyCK a (hXiK ha)).symm
  have hXisup : Xi ≤ Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) := by
    rw [← hZiMi]
    exact le_inf (hXiCXstar.trans (Subgroup.centralizer_le_normalizer _))
      (hXiMiσ.trans (OddOrder.BG.Ch3.S10.Msigma_le Mi))
  have hKiMσbot : Ki ⊓ OddOrder.BG.Ch3.S10.Msigma Mi = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime (coprime_of_forall_prime_not_dvd ?_)
    intro r hr hrKi hrMσ
    exact (kappaHall_isPiSubgroup_sigmaCompl hKiMi hKi r
        (Nat.mem_primeFactors.mpr ⟨hr, hrKi, Nat.card_pos.ne'⟩))
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mi r
        (Nat.mem_primeFactors.mpr ⟨hr, hrMσ, Nat.card_pos.ne'⟩))
  have hC : Xi ≤ OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G) :=
    le_centralizerFactor_of_le_sup_of_le_Msigma inf_le_right inf_le_left hKiMσbot hXisup hXiMiσ
  -- Direction `⊇` (the swap with `(M, K, X*) ↔ (Mi, Ki, Xi)` exchanged).
  have hle2 : Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) ≤
      K ⊔ Kstar := by
    have h := typeP_swap_Z_le hG (rfl :
      OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G) =
        OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G))
      hM hP hA hB hpi hXi hC hKM hK hXiK
    rwa [← hKstar] at h
  exact le_antisymm hle1 hle2

/-- **BG 14.7, Proposition 14.2(c) packaged** (the unique-centralizer clause): for a type-`P`
maximal `M` with Hall `κ(M)`-subgroup `K`, every line `Y ∈ ℰ¹(K*)` (`K* = C_{M_σ}(K)`) satisfies
`ℳ(C_G(Y)) = {M}`.  The Hall `(κ∪σ)'`-subgroup is produced internally, so callers supply only
`Y ≤ M_σ ⊓ C_G(K)`.  Used to show the `K_i*` are pairwise disjoint. -/
theorem typeP_centralizer_singleton [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    {p : ℕ} (hp : p.Prime) {Y : Subgroup G} (hY : Y ∈ elemAbelianOfRank G p 1)
    (hYK : Y ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {M} := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  obtain ⟨_, _, _, _, _, hc, _⟩ := typeP_structure hG hM hP hKM hK rfl hU
  exact hc p hp Y hY hYK

/-- **BG 14.7, distinct neighbours have disjoint `K*`** (mmd L4005, "By Proposition 14.2(c)
applied to each `Mi`, `Ki* ∩ Kj* = 1` for `i ≠ j`"): if `Mi ≠ Mj` are type-`P` maximal
subgroups with Hall `κ`-subgroups `Ki`, `Kj`, then `C_{Mi_σ}(Ki) ⊓ C_{Mj_σ}(Kj) = ⊥`.

A common nonidentity element gives, by Cauchy, a line `Y ∈ ℰ¹(Ki* ⊓ Kj*)`; Proposition 14.2(c)
then forces `{Mi} = ℳ(C_G(Y)) = {Mj}`, i.e. `Mi = Mj`. -/
theorem typeP_neighbor_Kstar_inf_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {Mi Mj Ki Kj : Subgroup G}
    (hMi : Mi ∈ maximalSubgroups G) (hPi : IsTypeP Mi) (hKiMi : Ki ≤ Mi)
    (hKi : Ch03.IsHallSubgroup (kappa Mi) (Ki.subgroupOf Mi))
    (hMj : Mj ∈ maximalSubgroups G) (hPj : IsTypeP Mj) (hKjMj : Kj ≤ Mj)
    (hKj : Ch03.IsHallSubgroup (kappa Mj) (Kj.subgroupOf Mj))
    (hne : Mi ≠ Mj) :
    (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) ⊓
      (OddOrder.BG.Ch3.S10.Msigma Mj ⊓ Subgroup.centralizer (Kj : Set G)) = ⊥ := by
  classical
  by_contra hbot
  set H := (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) ⊓
    (OddOrder.BG.Ch3.S10.Msigma Mj ⊓ Subgroup.centralizer (Kj : Set G)) with hHdef
  -- Cauchy: a prime-order element `z ∈ H`, generating a line `Y ∈ ℰ¹(H)`.
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hbot
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := ↥H)).ne'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hzH : (z : G) ∈ H := z.2
  have hzord : orderOf (z : G) = p := (orderOf_injective H.subtype H.subtype_injective z).trans hz
  have hYcard : Nat.card ↥(Subgroup.zpowers (z : G)) = p := by rw [Nat.card_zpowers, hzord]
  have hY : Subgroup.zpowers (z : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
  have hYH : Subgroup.zpowers (z : G) ≤ H := Subgroup.zpowers_le.mpr hzH
  -- `ℳ(C_G(Y)) = {Mi} = {Mj}`, so `Mi = Mj`, contradiction.
  have hi : maximalSubgroupsContaining (Subgroup.centralizer ((Subgroup.zpowers (z : G)) : Set G))
      = {Mi} := typeP_centralizer_singleton hG hMi hPi hKiMi hKi hp hY (hYH.trans inf_le_left)
  have hj : maximalSubgroupsContaining (Subgroup.centralizer ((Subgroup.zpowers (z : G)) : Set G))
      = {Mj} := typeP_centralizer_singleton hG hMj hPj hKjMj hKj hp hY (hYH.trans inf_le_right)
  exact hne (Set.singleton_eq_singleton_iff.mp (hi.symm.trans hj))

/-- **Inclusion–exclusion for subgroups meeting only at the identity** (BG 14.7 density backbone,
mmd L4031): for a nonempty finite family `{Sᵢ}_{i ∈ s}` of subgroups of `G` with `Sᵢ ⊓ Sⱼ = ⊥`
(`i ≠ j`), `|⋃ᵢ Sᵢ| + |s| = (∑ᵢ |Sᵢ|) + 1`.  Each `Sᵢ` contributes `|Sᵢ| − 1` non-identity
elements, all pairwise disjoint, plus the single shared identity.  In Theorem 14.7 (with `n + 1`
subgroups `Kᵢ*`) this gives `|T| = |Z| + n − ∑ kᵢ*` for `T = Z − ⋃ Kᵢ*`. -/
theorem ncard_biUnion_subgroup_add_card [Finite G] {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) (S : ι → Subgroup G)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → S i ⊓ S j = ⊥) :
    (⋃ i ∈ s, (S i : Set G)).ncard + s.card = (∑ i ∈ s, Nat.card ↥(S i)) + 1 := by
  classical
  have hcard_eq : ∀ i, (S i : Set G).ncard = Nat.card ↥(S i) := fun i =>
    (Nat.card_coe_set_eq (S i : Set G)).symm
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left, Finset.card_singleton,
      Finset.sum_singleton, hcard_eq]
  | cons a t ha htne ih =>
    have hpair_t : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → S i ⊓ S j = ⊥ := fun i hi j hj hij =>
      hpair i (Finset.mem_cons.mpr (Or.inr hi)) j (Finset.mem_cons.mpr (Or.inr hj)) hij
    have ih' := ih hpair_t
    -- `⋃_{cons a t} = S a ∪ ⋃_t`.
    have hunion : (⋃ i ∈ (Finset.cons a t ha), (S i : Set G))
        = (S a : Set G) ∪ ⋃ i ∈ t, (S i : Set G) := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_cons, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨i, rfl | hi, hxi⟩
        · exact Or.inl hxi
        · exact Or.inr ⟨i, hi, hxi⟩
      · rintro (hxa | ⟨i, hi, hxi⟩)
        · exact ⟨a, Or.inl rfl, hxa⟩
        · exact ⟨i, Or.inr hi, hxi⟩
    -- `S a ∩ ⋃_t = {1}` (pairwise meet at the identity, `t` nonempty).
    have hinter : (S a : Set G) ∩ (⋃ i ∈ t, (S i : Set G)) = {1} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
      constructor
      · rintro ⟨hxa, i, hi, hxi⟩
        have hmem : x ∈ S a ⊓ S i := Subgroup.mem_inf.mpr ⟨hxa, hxi⟩
        rwa [hpair a (Finset.mem_cons_self a t) i (Finset.mem_cons.mpr (Or.inr hi))
          (fun h => ha (h ▸ hi)), Subgroup.mem_bot] at hmem
      · rintro rfl
        obtain ⟨i, hi⟩ := htne
        exact ⟨(S a).one_mem, i, hi, (S i).one_mem⟩
    have hunion_card : ((S a : Set G) ∪ ⋃ i ∈ t, (S i : Set G)).ncard + 1 =
        Nat.card ↥(S a) + (⋃ i ∈ t, (S i : Set G)).ncard := by
      have hfin1 : (S a : Set G).Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      have hfin2 : (⋃ i ∈ t, (S i : Set G)).Finite :=
        Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      have h := Set.ncard_union_add_ncard_inter (S a : Set G) (⋃ i ∈ t, (S i : Set G)) hfin1 hfin2
      rw [hinter, Set.ncard_singleton, hcard_eq a] at h
      exact h
    rw [hunion, Finset.card_cons, Finset.sum_cons]
    omega

/-- **BG 14.7, the `T = Z − ⋃ Kᵢ*` density count** (mmd L4031): for a nonempty finite family
`{Sᵢ}_{i ∈ s}` of subgroups of `Z` pairwise meeting at `⊥`,
`|Z − ⋃ Sᵢ| + (∑ |Sᵢ|) + 1 = |Z| + |s|`, i.e. `|T| = |Z| + (|s| − 1) − ∑ |Sᵢ|`.
With `s.card = n + 1` this is BG's `|T| = z + n − ∑ kᵢ*`.  Combines the inclusion–exclusion
count with the complement `|Z − ⋃| + |⋃| = |Z|`. -/
theorem ncard_sdiff_biUnion_subgroup [Finite G] {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (S : ι → Subgroup G) {Z : Subgroup G} (hSZ : ∀ i ∈ s, S i ≤ Z)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → S i ⊓ S j = ⊥) :
    ((Z : Set G) \ ⋃ i ∈ s, (S i : Set G)).ncard + (∑ i ∈ s, Nat.card ↥(S i)) + 1
      = Nat.card ↥Z + s.card := by
  classical
  have hsub : (⋃ i ∈ s, (S i : Set G)) ⊆ (Z : Set G) :=
    Set.iUnion₂_subset (fun i hi => SetLike.coe_subset_coe.mpr (hSZ i hi))
  have hIE := ncard_biUnion_subgroup_add_card hs S hpair
  have hdiff := Set.ncard_diff_add_ncard_of_subset hsub
  have hZcard : Nat.card ↥Z = (Z : Set G).ncard := Nat.card_coe_set_eq (Z : Set G)
  omega

/-- **Internal direct product cardinality** (BG 14.7 `z = ∏ kᵢ*`, mmd L4009): a finite family
`{Hᵢ}` of pairwise-commuting subgroups with pairwise-coprime orders is an internal direct product,
so `|⨆ᵢ Hᵢ| = ∏ᵢ |Hᵢ|`.  (Independence comes from coprimality via
`Subgroup.independent_of_coprime_order`; the `noncommPiCoprod` map is then injective with range
`⨆ Hᵢ`.)  In Theorem 14.7, applied to the `Kᵢ*` (Hall `σ(Mᵢ)`-subgroups of `Z`, pairwise coprime
since the `σ(Mᵢ)` are disjoint) it gives `z = ∏ kᵢ*` and hence `kᵢ = ∏_{j≠i} kⱼ*`. -/
theorem card_iSup_of_pairwise_commute_coprime [Finite G] {ι : Type*} [Fintype ι]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hcoprime : Pairwise fun i j => Nat.Coprime (Nat.card ↥(H i)) (Nat.card ↥(H j))) :
    Nat.card ↥(⨆ i, H i) = ∏ i, Nat.card ↥(H i) := by
  classical
  haveI : ∀ i, Fintype ↥(H i) := fun i => Fintype.ofFinite _
  have hcop' : Pairwise fun i j => Nat.Coprime (Fintype.card ↥(H i)) (Fintype.card ↥(H j)) :=
    fun i j hij => by simpa only [Nat.card_eq_fintype_card] using hcoprime hij
  have hind : iSupIndep H := Subgroup.independent_of_coprime_order hcomm hcop'
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hrange : (Subgroup.noncommPiCoprod hcomm).range = ⨆ i, H i :=
    Subgroup.noncommPiCoprod_range
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]

/-- **BG 14.7, the canonical form of `Kᵢ*`** (mmd L4009): once the swap gives `Z = Kₙ ⊔ Kₙ*`
(`Kₙ* = C_{Nσ}(Kₙ)`), the factor `Kₙ*` is exactly `Z ⊓ Nσ` — the `σ(N)`-part of `Z`.  This
removes the dependence of `Kₙ*` on the chosen Hall `κ(N)`-subgroup `Kₙ`: it is the canonical
`Z ⊓ M_σ(N)`, so the family `{Kᵢ*}` can be defined choice-free as `N ↦ Z ⊓ Nσ`.

`⊆`: `Kₙ* ≤ Z` (a factor) and `Kₙ* ≤ Nσ`.  `⊇`: `Z ⊓ Nσ = (Kₙ ⊔ Kₙ*) ⊓ Nσ` is a `σ(N)`-group
inside the product `Kₙ × Kₙ*`, so the `σ`-projection lands it in `Kₙ*`. -/
theorem typeP_neighbor_Kstar_eq_Z_inf_Msigma [Finite G]
    {N K Kstar KN : Subgroup G} (hKNN : KN ≤ N)
    (hKN : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N))
    (hZeq : K ⊔ Kstar = KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G))) :
    OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
      = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N := by
  classical
  refine le_antisymm (le_inf (hZeq ▸ le_sup_right) inf_le_left) ?_
  rw [hZeq]
  have hKNMσbot : KN ⊓ OddOrder.BG.Ch3.S10.Msigma N = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime (coprime_of_forall_prime_not_dvd ?_)
    intro r hr hrKN hrMσ
    exact (kappaHall_isPiSubgroup_sigmaCompl hKNN hKN r
        (Nat.mem_primeFactors.mpr ⟨hr, hrKN, Nat.card_pos.ne'⟩))
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N r
        (Nat.mem_primeFactors.mpr ⟨hr, hrMσ, Nat.card_pos.ne'⟩))
  exact le_centralizerFactor_of_le_sup_of_le_Msigma inf_le_right inf_le_left hKNMσbot
    inf_le_left inf_le_right

/-- **Base member of the type-`P` family**: `Z ⊓ M_σ = K*` for `M` itself.  Specialises
`typeP_neighbor_Kstar_eq_Z_inf_Msigma` to `N = M`, `K_N = K` (so `K* = M_σ ⊓ C(K)` is the
canonical `σ(M)`-part of `Z = K ⊔ K*`).  This is the base case of the `T = Ẑ` identification:
the exceptional set `T = Z ∖ ⋃_{N} (Z ⊓ N_σ)` removes `K*` (from `N = M`) and `K` (from the
partner), collapsing to `zTilde K K* = Z ∖ (K ∪ K*)`. -/
theorem typeP_Z_inf_Msigma_eq_Kstar [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar := by
  have h := typeP_neighbor_Kstar_eq_Z_inf_Msigma (N := M) (KN := K) (K := K) (Kstar := Kstar)
    hKM hK (by rw [hKstar])
  rw [← h, ← hKstar]

/-- **BG 14.7, per-neighbour swap package** (mmd L3997-4009): for a type-`P` maximal `M` with Hall
data `K`, `K*`, a line `X ∈ ℰ_p¹(K)` (`C_{M_σ}(X) ≠ 1`) and a maximal `N ⊇ N_G(X)`, there is a
Hall `κ(N)`-subgroup `K_N` of `N` realising the swap: `Z = K ⊔ K* = K_N ⊔ K_N*` with the canonical
factor `K_N* = Z ⊓ M_σ(N)`.  This is the per-neighbour foundation that the `M_i` family iterates
over: assembles `typeP_neighbor_embed`/`typeP_neighbor_kappa` (neighbour data), a chosen line
`X* ∈ ℰ¹(K*)` with a Hall `κ(N)`-subgroup `K_N ∋ X*`, `typeP_swap_Z_eq` (the swap) and
`typeP_neighbor_Kstar_eq_Z_inf_Msigma` (the canonical form). -/
theorem exists_neighbor_kappaHall_swap [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {N : Subgroup G} (hN : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
        = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N := by
  classical
  obtain ⟨hnc, hZN, hXNσ⟩ := typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hκ := typeP_neighbor_kappa hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hNmax : N ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hN).1
  have hKstarne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  haveI : Nontrivial ↥Kstar := (Subgroup.nontrivial_iff_ne_bot _).mpr hKstarne
  obtain ⟨q, hq⟩ : (Nat.card ↥Kstar).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  have hqκN : q ∈ kappa N := hκ q hq
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
  -- A line `X* ∈ ℰ¹(K*)` of prime order `q`, inside a Hall `κ(N)`-subgroup `K_N`.
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' q (Nat.dvd_of_mem_primeFactors hq)
  have hx'ord : orderOf (x' : G) = q :=
    (orderOf_injective Kstar.subtype Kstar.subtype_injective x').trans hx'
  have hXstarcard : Nat.card ↥(Subgroup.zpowers (x' : G)) = q := by rw [Nat.card_zpowers, hx'ord]
  have hXstarElem : Subgroup.zpowers (x' : G) ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXstarcard, by rw [hXstarcard, pow_one]⟩
  have hXstarKstar : Subgroup.zpowers (x' : G) ≤ Kstar := Subgroup.zpowers_le.mpr x'.2
  have hXstarκN : ∀ r ∈ (Nat.card ↥(Subgroup.zpowers (x' : G))).primeFactors, r ∈ kappa N := by
    intro r hr
    rw [hXstarcard, (Nat.prime_of_mem_primeFactors hq).primeFactors, Finset.mem_singleton] at hr
    exact hr ▸ hqκN
  obtain ⟨KN, hKNN, hKN, hXstarKN⟩ :=
    exists_isHallSubgroup_kappa_ge hG hNmax (hXstarKstar.trans (le_sup_right.trans hZN)) hXstarκN
  have hswap : K ⊔ Kstar =
      KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) :=
    typeP_swap_Z_eq hG hM hP hKM hK hKstar hU hNmax ⟨q, hqκN⟩ hZN hκ
      (Nat.prime_of_mem_primeFactors hq) hXstarElem hXstarKstar hXstarKN
      Fact.out hX hXK hXNσ hKNN hKN
  exact ⟨KN, hKNN, hKN, hswap, typeP_neighbor_Kstar_eq_Z_inf_Msigma hKNN hKN hswap⟩

/-- **BG 14.7, coverage of `κ(M)`-primes** (mmd L4007): every prime `p ∣ |K|` lies in `σ(N)` for
some nonconjugate type-`P` neighbour `N` containing `Z`.  A line `X ∈ ℰ_p¹(K)` (Cauchy in `K`) has
a partner `N ∈ 𝓜(N_G(X))` (`exists_typeP_partner`) with `X ⊆ M_σ(N)`, so `p ∈ σ(N)`.  Together with
`M` itself (covering `σ(M) ⊇ π(K*)`), this gives the coverage `⋃ σ(Mᵢ) ⊇ π(Z)` that forces
`⨆ Kᵢ* = Z`. -/
theorem exists_typeP_neighbor_mem_sigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card ↥K) :
    ∃ N : Subgroup G, N ∈ maximalSubgroups G ∧ IsTypeP N ∧ ¬ IsConjugateSubgroup M N ∧
      p ∈ OddOrder.BG.Ch3.S10.sigma N ∧ K ⊔ Kstar ≤ N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxord : orderOf (x : G) = p := (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
  have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
  obtain ⟨N, hNmem, hnc, hZN, hXNσ, _, hPN⟩ :=
    exists_typeP_partner hG hM hP hKM hK hKstar hU hXelem hXK
  have hNmax : N ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hNmem).1
  -- `p ∈ σ(N)` since `X ⊆ M_σ(N)` and `p ∣ |X|`.
  have hpσN : p ∈ OddOrder.BG.Ch3.S10.sigma N :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
      ⟨hp, (by rw [hXcard] : p ∣ Nat.card ↥(Subgroup.zpowers (x : G))).trans
        (Subgroup.card_dvd_of_le hXNσ), Nat.card_pos.ne'⟩)
  exact ⟨N, hNmax, hPN, hnc, hpσN, hZN⟩

/-- **Both factors of an internal direct product are normal**: in `A ⊔ B` with `B ≤ C_G(A)`
(so `A`, `B` commute), `A ⊔ B ≤ N_G(A) ⊓ N_G(B)`.  In Theorem 14.7, applied to the swap
`Z = K_N ⊔ K_N*` (`K_N* ≤ C(K_N)`), it makes both `K_N` and `K_N* = Z ⊓ M_σ(N)` normal in `Z` —
the input to pairwise commutativity of the `Kᵢ*` (for `z = ∏ kᵢ*`), to pairwise nonconjugacy of
the `Mᵢ`, and to the `n = 1` collapse (`Kᵢ ◁ Z` is the unique `σ(Mᵢ)'`-Hall). -/
theorem sup_le_normalizer_inf_of_commute {A B : Subgroup G}
    (h : B ≤ Subgroup.centralizer (A : Set G)) :
    A ⊔ B ≤ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) := by
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (h hb) a ha).symm
  exact le_inf
    (sup_le Subgroup.le_normalizer (h.trans (Subgroup.centralizer_le_normalizer _)))
    (sup_le (hAB.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer)

/-- **Internal direct product of two commuting subgroups**: if `H`, `K` commute elementwise and
`H ⊓ K = ⊥`, then `|H ⊔ K| = |H|·|K|`.  (The `noncommCoprod` map `↥H × ↥K → ↥(H ⊔ K)` is an
isomorphism.)  Used by the family argument for `|Kᵢ* ⊔ Kⱼ*| = kᵢ*·kⱼ*` (pairwise nonconjugacy) and
in the `n = 1` collapse. -/
theorem card_sup_of_commute_of_disjoint [Finite G] {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, Commute x y) (hdisj : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  classical
  have hc : ∀ (a : ↥H) (b : ↥K), Commute (H.subtype a) (K.subtype b) :=
    fun a b => hcomm (a : G) a.2 (b : G) b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod H.subtype K.subtype hc) :=
    (MonoidHom.noncommCoprod_injective _ _ hc).mpr
      ⟨H.subtype_injective, K.subtype_injective, by
        rw [H.range_subtype, K.range_subtype]; exact disjoint_iff.mpr hdisj⟩
  have hrange : (MonoidHom.noncommCoprod H.subtype K.subtype hc).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, H.range_subtype, K.range_subtype]
  rw [← Nat.card_congr
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).toEquiv, Nat.card_prod]

/-- **Subgroups normal in a common overgroup, meeting trivially, commute**: if `A, B ≤ Z` with
`Z ≤ N_G(A)`, `Z ≤ N_G(B)` (so `A, B ◁ Z`) and `A ⊓ B = ⊥`, then every element of `A` commutes with
every element of `B`.  (The commutator `[x,y]` lies in `A ⊓ B = ⊥`.)  Used for `|Kᵢ* ⊔ Kⱼ*| =
kᵢ*·kⱼ*` once the `Kᵢ*` are known normal in `Z`. -/
theorem commute_of_le_normalizer_of_disjoint {Z A B : Subgroup G}
    (hAZ : A ≤ Z) (hBZ : B ≤ Z) (hAnorm : Z ≤ Subgroup.normalizer (A : Set G))
    (hBnorm : Z ≤ Subgroup.normalizer (B : Set G)) (hdisj : A ⊓ B = ⊥) :
    ∀ x ∈ A, ∀ y ∈ B, Commute x y := by
  haveI hAn : (A.subgroupOf Z).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAnorm
  haveI hBn : (B.subgroupOf Z).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBnorm
  have hdisjZ : Disjoint (A.subgroupOf Z) (B.subgroupOf Z) := by
    rw [Subgroup.disjoint_def]
    intro g hgA hgB
    have : (g : G) ∈ A ⊓ B :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hgA, Subgroup.mem_subgroupOf.mp hgB⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact OneMemClass.coe_eq_one.mp this
  intro x hx y hy
  have h := Subgroup.commute_of_normal_of_disjoint (A.subgroupOf Z) (B.subgroupOf Z) hAn hBn hdisjZ
    ⟨x, hAZ hx⟩ ⟨y, hBZ hy⟩ (Subgroup.mem_subgroupOf.mpr hx) (Subgroup.mem_subgroupOf.mpr hy)
  exact h.map Z.subtype

/-- **BG 14.7, pairwise nonconjugacy of the family** (mmd L4015, "the `Mᵢ` are pairwise not
conjugate"): if `M₁`, `M₂` are maximal subgroups whose swap factors `Zₖ = M_σ(Mₖ) ⊓ C(Kₖ)` (the
`σ(Mₖ)`-Halls of `Z = K ⊔ K*`, `Kₖ` Hall `κ(Mₖ)`) meet trivially and `Z₂ ≠ ⊥`, then `M₁`, `M₂` are
nonconjugate.

Were they conjugate, `σ(M₁) = σ(M₂) =: τ`, so `Z₁`, `Z₂` are both `τ`-Halls of `Z`, normal
(direct factors) and disjoint.  Then `|Z₁ ⊔ Z₂| = z₁ z₂ ∣ z = k₁ z₁`, giving `z₂ ∣ k₁`; but `z₂` is
a `τ`-number and `k₁` a `τ'`-number, so `z₂ = 1`, contradicting `Z₂ ≠ ⊥`.  Feeds Lemma 14.5(b)
(pairwise disjointness of the `𝒞_G(M̃ᵢ)`). -/
theorem typeP_family_nonconjugate [Finite G]
    {K Kstar M₁ M₂ K₁ K₂ : Subgroup G}
    (hK₁M₁ : K₁ ≤ M₁) (hK₁ : Ch03.IsHallSubgroup (kappa M₁) (K₁.subgroupOf M₁))
    (hsw₁ : K ⊔ Kstar = K₁ ⊔ (OddOrder.BG.Ch3.S10.Msigma M₁ ⊓ Subgroup.centralizer (K₁ : Set G)))
    (hsw₂ : K ⊔ Kstar = K₂ ⊔ (OddOrder.BG.Ch3.S10.Msigma M₂ ⊓ Subgroup.centralizer (K₂ : Set G)))
    (hne₂ : OddOrder.BG.Ch3.S10.Msigma M₂ ⊓ Subgroup.centralizer (K₂ : Set G) ≠ ⊥)
    (hdisj : (OddOrder.BG.Ch3.S10.Msigma M₁ ⊓ Subgroup.centralizer (K₁ : Set G)) ⊓
      (OddOrder.BG.Ch3.S10.Msigma M₂ ⊓ Subgroup.centralizer (K₂ : Set G)) = ⊥) :
    ¬ IsConjugateSubgroup M₁ M₂ := by
  classical
  set Z₁ := OddOrder.BG.Ch3.S10.Msigma M₁ ⊓ Subgroup.centralizer (K₁ : Set G) with hZ₁def
  set Z₂ := OddOrder.BG.Ch3.S10.Msigma M₂ ⊓ Subgroup.centralizer (K₂ : Set G) with hZ₂def
  rintro ⟨g, hg⟩
  have hσ : OddOrder.BG.Ch3.S10.sigma M₂ = OddOrder.BG.Ch3.S10.sigma M₁ := by
    rw [← hg]; exact sigma_conj_smul_eq g M₁
  have hZ₁CK₁ : Z₁ ≤ Subgroup.centralizer (K₁ : Set G) := by rw [hZ₁def]; exact inf_le_right
  have hZ₁Mσ : Z₁ ≤ OddOrder.BG.Ch3.S10.Msigma M₁ := by rw [hZ₁def]; exact inf_le_left
  have hZ₂CK₂ : Z₂ ≤ Subgroup.centralizer (K₂ : Set G) := by rw [hZ₂def]; exact inf_le_right
  have hZ₂Mσ : Z₂ ≤ OddOrder.BG.Ch3.S10.Msigma M₂ := by rw [hZ₂def]; exact inf_le_left
  have hcommK₁Z₁ : ∀ x ∈ K₁, ∀ y ∈ Z₁, Commute x y := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hZ₁CK₁ hy) x hx
  have hdisjK₁Z₁ : K₁ ⊓ Z₁ = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime (coprime_of_forall_prime_not_dvd ?_)
    intro r hr hrK₁ hrZ₁
    exact kappaHall_isPiSubgroup_sigmaCompl hK₁M₁ hK₁ r
        (Nat.mem_primeFactors.mpr ⟨hr, hrK₁, Nat.card_pos.ne'⟩)
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M₁ r (Nat.mem_primeFactors.mpr
        ⟨hr, hrZ₁.trans (Subgroup.card_dvd_of_le hZ₁Mσ), Nat.card_pos.ne'⟩))
  have hzcard : Nat.card ↥(K ⊔ Kstar) = Nat.card ↥K₁ * Nat.card ↥Z₁ := by
    rw [hsw₁]; exact card_sup_of_commute_of_disjoint hcommK₁Z₁ hdisjK₁Z₁
  have hZ₁Z : Z₁ ≤ K ⊔ Kstar := by rw [hsw₁]; exact le_sup_right
  have hZ₂Z : Z₂ ≤ K ⊔ Kstar := by rw [hsw₂]; exact le_sup_right
  have hZ₁norm : K ⊔ Kstar ≤ Subgroup.normalizer (Z₁ : Set G) := by
    rw [hsw₁]; exact (sup_le_normalizer_inf_of_commute hZ₁CK₁).trans inf_le_right
  have hZ₂norm : K ⊔ Kstar ≤ Subgroup.normalizer (Z₂ : Set G) := by
    rw [hsw₂]; exact (sup_le_normalizer_inf_of_commute hZ₂CK₂).trans inf_le_right
  have hz12 : Nat.card ↥(Z₁ ⊔ Z₂) = Nat.card ↥Z₁ * Nat.card ↥Z₂ :=
    card_sup_of_commute_of_disjoint
      (commute_of_le_normalizer_of_disjoint hZ₁Z hZ₂Z hZ₁norm hZ₂norm hdisj) hdisj
  have hdvd : Nat.card ↥(Z₁ ⊔ Z₂) ∣ Nat.card ↥(K ⊔ Kstar) :=
    Subgroup.card_dvd_of_le (sup_le hZ₁Z hZ₂Z)
  rw [hz12, hzcard] at hdvd
  have hZ₂dvdK₁ : Nat.card ↥Z₂ ∣ Nat.card ↥K₁ := by
    rw [mul_comm (Nat.card ↥K₁)] at hdvd
    exact (Nat.mul_dvd_mul_iff_left Nat.card_pos).mp hdvd
  have hcop : Nat.Coprime (Nat.card ↥Z₂) (Nat.card ↥K₁) :=
    coprime_of_forall_prime_not_dvd (fun r hr hrZ₂ hrK₁ =>
      kappaHall_isPiSubgroup_sigmaCompl hK₁M₁ hK₁ r
        (Nat.mem_primeFactors.mpr ⟨hr, hrK₁, Nat.card_pos.ne'⟩)
        (hσ ▸ OddOrder.BG.Ch3.S10.Msigma_isPiGroup M₂ r (Nat.mem_primeFactors.mpr
          ⟨hr, hrZ₂.trans (Subgroup.card_dvd_of_le hZ₂Mσ), Nat.card_pos.ne'⟩)))
  have hZ₂one : Nat.card ↥Z₂ = 1 := (Nat.gcd_eq_left hZ₂dvdK₁).symm.trans hcop
  exact hne₂ (Subgroup.card_eq_one.mp hZ₂one)

/-- **BG 14.7, per-neighbour swap package with normality** (mmd L3997-4015): the per-neighbour
swap `exists_neighbor_kappaHall_swap`, restated with the canonical factor `K_N* = Z ⊓ M_σ(N)`
folded into the swap and augmented with `K_N* ◁ Z` (`Z ≤ N_G(K_N*)`).  This is the exact per-member
data the `M_i` family consumes: the swap `Z = K_N ⊔ K_N*`, the canonical `K_N*`, and its normality
in `Z` (for pairwise commutativity, the `|T|` count, and the `n = 1` collapse). -/
theorem exists_neighbor_kappaHall_swap_normal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {N : Subgroup G} (hN : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ∧
      K ⊔ Kstar ≤ Subgroup.normalizer
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
  obtain ⟨KN, hKNN, hKN, hswap, hcanon⟩ :=
    exists_neighbor_kappaHall_swap hG hM hP hKM hK hKstar hU hX hXK hCX hN
  refine ⟨KN, hKNN, hKN, hswap.trans (by rw [hcanon]), ?_⟩
  rw [← hcanon, hswap]
  exact (sup_le_normalizer_inf_of_commute inf_le_right).trans inf_le_right

/-- **BG 14.7, full per-neighbour data** (mmd L3997-4015): the complete per-member package the
`M_i` family consumes — for a line `X ∈ ℰ_p¹(K)` and a maximal `N ⊇ N_G(X)`, a Hall `κ(N)`-subgroup
`K_N` with the swap `Z = K_N ⊔ K_N*` (canonical `K_N* = Z ⊓ M_σ(N)`), `K_N* ◁ Z`, `N` type-`P`, and
`K_N* ≠ ⊥` (since `X ≤ K_N*`, as `X ≤ K ≤ Z` and `X ⊆ M_σ(N)`).  Builds on
`exists_neighbor_kappaHall_swap_normal` + `typeP_neighbor_embed`/`typeP_neighbor_kappa`. -/
theorem exists_neighbor_full [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {N : Subgroup G} (hN : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ∧
      K ⊔ Kstar ≤ Subgroup.normalizer
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) ∧
      IsTypeP N ∧ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≠ ⊥ := by
  obtain ⟨KN, hKNN, hKN, hswap, hnorm⟩ :=
    exists_neighbor_kappaHall_swap_normal hG hM hP hKM hK hKstar hU hX hXK hCX hN
  obtain ⟨_, _, hXNσ⟩ := typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hκ := typeP_neighbor_kappa hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hKstarne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  haveI : Nontrivial ↥Kstar := (Subgroup.nontrivial_iff_ne_bot _).mpr hKstarne
  obtain ⟨q, hq⟩ : (Nat.card ↥Kstar).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  have hPN : IsTypeP N := ⟨q, hκ q hq⟩
  have hXKstar : X ≤ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    le_inf (hXK.trans le_sup_left) hXNσ
  have hKstarNne : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≠ ⊥ := fun hbot =>
    ne_bot_of_mem_elemAbelianOfRank_one hX (le_bot_iff.mp (hbot ▸ hXKstar))
  exact ⟨KN, hKNN, hKN, hswap, hnorm, hPN, hKstarNne⟩

/-- **BG 14.7, two family members are nonconjugate** (mmd L4015): given two type-`P` maximals
`N₁ ≠ N₂` with Hall `κ`-subgroups and the swaps `Z = Kₖ ⊔ (M_σ(Nₖ) ⊓ C(Kₖ))` (`Z₂* ≠ ⊥`), the
members are nonconjugate.  Combines Proposition 14.2(c) (`typeP_neighbor_Kstar_inf_eq_bot`: the swap
factors meet trivially since the members are distinct) with `typeP_family_nonconjugate`.  This is
the per-pair input to the family's pairwise nonconjugacy (and thence Lemma 14.5(b)). -/
theorem neighbor_pair_nonconjugate [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {K Kstar N₁ N₂ K₁ K₂ : Subgroup G}
    (hN₁ : N₁ ∈ maximalSubgroups G) (hP₁ : IsTypeP N₁) (hK₁N₁ : K₁ ≤ N₁)
    (hK₁ : Ch03.IsHallSubgroup (kappa N₁) (K₁.subgroupOf N₁))
    (hN₂ : N₂ ∈ maximalSubgroups G) (hP₂ : IsTypeP N₂) (hK₂N₂ : K₂ ≤ N₂)
    (hK₂ : Ch03.IsHallSubgroup (kappa N₂) (K₂.subgroupOf N₂))
    (hsw₁ : K ⊔ Kstar = K₁ ⊔ (OddOrder.BG.Ch3.S10.Msigma N₁ ⊓ Subgroup.centralizer (K₁ : Set G)))
    (hsw₂ : K ⊔ Kstar = K₂ ⊔ (OddOrder.BG.Ch3.S10.Msigma N₂ ⊓ Subgroup.centralizer (K₂ : Set G)))
    (hne₂ : OddOrder.BG.Ch3.S10.Msigma N₂ ⊓ Subgroup.centralizer (K₂ : Set G) ≠ ⊥)
    (hne : N₁ ≠ N₂) :
    ¬ IsConjugateSubgroup N₁ N₂ :=
  typeP_family_nonconjugate hK₁N₁ hK₁ hsw₁ hsw₂ hne₂
    (typeP_neighbor_Kstar_inf_eq_bot hG hN₁ hP₁ hK₁N₁ hK₁ hN₂ hP₂ hK₂N₂ hK₂ hne)

/-- **BG 14.7, the base member `M` (`i = 0`)** (mmd L4003, "let `M₀ = M`"): `M`'s own data in the
same canonical shape the family uses.  `K_M* = Z ⊓ M_σ(M)` equals `K* = Kstar`, the swap
`Z = K ⊔ K_M*` is trivial, `K_M* ◁ Z`, and `K_M* ≠ ⊥` (since `Kstar ≠ ⊥`).  Aligns `M` with the
neighbours (`exists_neighbor_full`) so the family `{M} ∪ {neighbours}` has uniform per-member data. -/
theorem typeP_self_member [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar ∧
    K ⊔ Kstar = K ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M) ∧
    K ⊔ Kstar ≤ Subgroup.normalizer
      (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
    (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := by
  have hcanon : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
      = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M :=
    typeP_neighbor_Kstar_eq_Z_inf_Msigma hKM hK (by rw [hKstar])
  have hKstarEq : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar := hcanon.symm.trans hKstar.symm
  refine ⟨hKstarEq, by rw [hKstarEq], ?_, ?_⟩
  · rw [hKstarEq, hKstar]
    exact (sup_le_normalizer_inf_of_commute inf_le_right).trans inf_le_right
  · rw [hKstarEq]; exact (typeP_structure hG hM hP hKM hK hKstar hU).2.1

/-- **A subgroup of order coprime to a normal subgroup's index lies inside it** (BG 14.7 `n = 1`
collapse, mmd L4043): if `N ◁ G` and `|H|` is coprime to `[G : N]`, then `H ≤ N`.  (The image of
`H` in `G/N` has order dividing both `|H|` and `[G : N]`, hence `1`, so `H ≤ ker = N`.)  In the
collapse, applied with `N = Kᵢ` (the normal `σ(Mᵢ)'`-Hall of `Z`, `[Z : Kᵢ] = kᵢ*` a `σ(Mᵢ)`-number)
and `H = Kⱼ*` (a `σ(Mᵢ)'`-group), it gives `Kⱼ* ≤ Kᵢ`; with `|Kᵢ|` prime this forces `Kⱼ* = Kᵢ`. -/
theorem le_of_coprime_index {N H : Subgroup G} [N.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) N.index) : H ≤ N := by
  have hd1 : Nat.card ↥(H.map (QuotientGroup.mk' N)) ∣ Nat.card ↥H :=
    Subgroup.card_map_dvd H (QuotientGroup.mk' N)
  have hd2 : Nat.card ↥(H.map (QuotientGroup.mk' N)) ∣ N.index :=
    Subgroup.card_subgroup_dvd_card _
  have hcard1 : Nat.card ↥(H.map (QuotientGroup.mk' N)) = 1 :=
    Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2)
  have hbot : H.map (QuotientGroup.mk' N) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard1
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

/-- **BG 14.7, unified per-neighbour data** (mmd L3997-4015): the single per-member source for the
family, exposing the **raw** swap factor `K_N* = M_σ(N) ⊓ C(K_N)` (for pairwise nonconjugacy and the
`z = k_N·k_N*` card) together with the **canonical identity** `K_N* = Z ⊓ M_σ(N)` (for the family's
`Kᵢ*`), plus `N` type-`P` and `K_N* ≠ ⊥`.  Resolves the raw/canonical form tension at the source. -/
theorem exists_neighbor_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {N : Subgroup G} (hN : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
        = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ∧
      IsTypeP N ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G) ≠ ⊥ := by
  obtain ⟨KN, hKNN, hKN, hswap, hcanon⟩ :=
    exists_neighbor_kappaHall_swap hG hM hP hKM hK hKstar hU hX hXK hCX hN
  obtain ⟨_, _, hXNσ⟩ := typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hκ := typeP_neighbor_kappa hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hKstarne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  haveI : Nontrivial ↥Kstar := (Subgroup.nontrivial_iff_ne_bot _).mpr hKstarne
  obtain ⟨q, hq⟩ : (Nat.card ↥Kstar).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  have hXcanon : X ≤ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    le_inf (hXK.trans le_sup_left) hXNσ
  exact ⟨KN, hKNN, hKN, hswap, hcanon, ⟨q, hκ q hq⟩, fun hbot =>
    ne_bot_of_mem_elemAbelianOfRank_one hX (le_bot_iff.mp (hbot ▸ hcanon.symm ▸ hXcanon))⟩

/-- **BG 14.7, the family member predicate** (mmd L4003): `N` is a member of the type-`P` family
attached to `Z` — either `N = M`, or `N` is a maximal subgroup over `N_G(X)` for a line
`X ∈ ℰ_p¹(K)`. -/
def IsZFamilyMember (M K N : Subgroup G) : Prop :=
  N = M ∨ ∃ (p : ℕ) (X : Subgroup G), p.Prime ∧ X ∈ elemAbelianOfRank G p 1 ∧ X ≤ K ∧
    N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))

/-- **BG 14.7, uniform per-member data for the family** (mmd L4003-4015): every member `N` of the
type-`P` family is a type-`P` maximal subgroup containing `Z = K ⊔ K*`, with a Hall `κ(N)`-subgroup
`K_N` realising the swap `Z = K_N ⊔ K_N*` (raw `K_N* = M_σ(N) ⊓ C(K_N)`, canonical
`K_N* = Z ⊓ M_σ(N)`, `K_N* ≠ ⊥`).  Case-split on `N = M` (`typeP_self_member`) vs a neighbour
(`exists_neighbor_data`); this is the data the family `Finset` carries. -/
theorem typeP_family_member_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    N ∈ maximalSubgroups G ∧ IsTypeP N ∧ K ⊔ Kstar ≤ N ∧
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
        = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G) ≠ ⊥ := by
  rcases hN with hNM | ⟨p, X, hp, hX, hXK, hN⟩
  · -- `N = M`: base member.
    rw [hNM]
    obtain ⟨hKstarEq, _, _, _⟩ := typeP_self_member hG hM hP hKM hK hKstar hU
    refine ⟨hM, hP, sup_le hKM (hKstar ▸ inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M)),
      K, hKM, hK, by rw [hKstar], (hKstarEq.trans hKstar).symm,
      hKstar ▸ (typeP_structure hG hM hP hKM hK hKstar hU).2.1⟩
  · -- neighbour from a line `X`.
    haveI : Fact p.Prime := ⟨hp⟩
    have hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
      intro hbot
      refine (typeP_structure hG hM hP hKM hK hKstar hU).2.1 (le_bot_iff.mp ?_)
      rw [hKstar]
      calc OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
          ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) :=
            inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK))
        _ = ⊥ := hbot
    obtain ⟨KN, hKNN, hKN, hswap, hcanon, hPN, hne⟩ :=
      exists_neighbor_data hG hM hP hKM hK hKstar hU hX hXK hCX hN
    refine ⟨mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hN).1, hPN,
      hswap ▸ sup_le hKNN (inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le N)),
      KN, hKNN, hKN, hswap, hcanon, hne⟩

/-- **BG 14.7, the family is pairwise nonconjugate** (mmd L4015): any two distinct members of the
type-`P` family are nonconjugate.  Extracts each member's swap data
(`typeP_family_member_data`) and applies `neighbor_pair_nonconjugate`.  Feeds Lemma 14.5(b)
(pairwise disjointness of the `𝒞_G(M̃ᵢ)`). -/
theorem typeP_family_pairwise_nonconjugate [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N₁ N₂ : Subgroup G} (hN₁ : IsZFamilyMember M K N₁) (hN₂ : IsZFamilyMember M K N₂)
    (hne : N₁ ≠ N₂) :
    ¬ IsConjugateSubgroup N₁ N₂ := by
  obtain ⟨hN₁max, hP₁, _, K₁, hK₁N₁, hK₁, hsw₁, _, _⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN₁
  obtain ⟨hN₂max, hP₂, _, K₂, hK₂N₂, hK₂, hsw₂, _, hne₂⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN₂
  exact neighbor_pair_nonconjugate hG hN₁max hP₁ hK₁N₁ hK₁ hN₂max hP₂ hK₂N₂ hK₂ hsw₁ hsw₂ hne₂ hne

/-- **BG 14.7, the family `Kᵢ*` are pairwise disjoint** (mmd L4005): for distinct members
`N₁ ≠ N₂`, the canonical factors `Kᵢ* = Z ⊓ M_σ(Nᵢ)` meet trivially.  Distinct members are
nonconjugate (`typeP_family_pairwise_nonconjugate`), so `σ(N₁)`, `σ(N₂)` are disjoint
(Theorem 13.9), hence `M_σ(N₁) ⊓ M_σ(N₂) = ⊥` (coprime `σ`-groups), and a fortiori the `Kᵢ*` meet
trivially.  This is the pairwise-`⊥` input to the inclusion–exclusion `|T|` count. -/
theorem typeP_family_Kstar_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N₁ N₂ : Subgroup G} (hN₁ : IsZFamilyMember M K N₁) (hN₂ : IsZFamilyMember M K N₂)
    (hne : N₁ ≠ N₂) :
    ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₁) ⊓
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₂) = ⊥ := by
  obtain ⟨hN₁max, _, _, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN₁
  obtain ⟨hN₂max, _, _, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN₂
  have hnc := typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU hN₁ hN₂ hne
  have hσdisj := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hN₁max hN₂max hnc
  have hMσdisj : OddOrder.BG.Ch3.S10.Msigma N₁ ⊓ OddOrder.BG.Ch3.S10.Msigma N₂ = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime (coprime_of_forall_prime_not_dvd ?_)
    intro r hr hr₁ hr₂
    exact Set.disjoint_left.mp hσdisj
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N₁ r
        (Nat.mem_primeFactors.mpr ⟨hr, hr₁, Nat.card_pos.ne'⟩))
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N₂ r
        (Nat.mem_primeFactors.mpr ⟨hr, hr₂, Nat.card_pos.ne'⟩))
  exact le_bot_iff.mp (le_trans (inf_le_inf inf_le_right inf_le_right) (le_of_eq hMσdisj))

/-- **BG 14.7, the family `Kᵢ*` have pairwise coprime order** (mmd L4009): for distinct members
`N₁ ≠ N₂`, `|Kᵢ*| = |Z ⊓ M_σ(Nᵢ)|` are coprime — each `Kᵢ*` is a `σ(Nᵢ)`-group and the `σ(Nᵢ)` are
pairwise disjoint (Theorem 13.9 via `typeP_family_pairwise_nonconjugate`).  This is the
coprime-orders input to `card_iSup_of_pairwise_commute_coprime` for `z = ∏ kᵢ*`. -/
theorem typeP_family_Kstar_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N₁ N₂ : Subgroup G} (hN₁ : IsZFamilyMember M K N₁) (hN₂ : IsZFamilyMember M K N₂)
    (hne : N₁ ≠ N₂) :
    Nat.Coprime (Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₁))
      (Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₂)) := by
  obtain ⟨hN₁max, _, _, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN₁
  obtain ⟨hN₂max, _, _, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN₂
  have hnc := typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU hN₁ hN₂ hne
  have hσdisj := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hN₁max hN₂max hnc
  refine coprime_of_forall_prime_not_dvd ?_
  intro r hr hr₁ hr₂
  exact Set.disjoint_left.mp hσdisj
    (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N₁ r
      (Nat.mem_primeFactors.mpr
        ⟨hr, hr₁.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩))
    (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N₂ r
      (Nat.mem_primeFactors.mpr
        ⟨hr, hr₂.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩))

/-- **BG 14.7, the type-`P` family as a `Finset`** (mmd L4003): `{N | IsZFamilyMember M K N}`
collected as a `Finset` (finite since `Subgroup G` is finite). -/
noncomputable def ZFamilyFinset [Finite G] (M K : Subgroup G) : Finset (Subgroup G) :=
  (Set.toFinite {N | IsZFamilyMember M K N}).toFinset

theorem mem_ZFamilyFinset [Finite G] {M K N : Subgroup G} :
    N ∈ ZFamilyFinset M K ↔ IsZFamilyMember M K N :=
  Set.Finite.mem_toFinset _

theorem ZFamilyFinset_nonempty [Finite G] {M K : Subgroup G} : (ZFamilyFinset M K).Nonempty :=
  ⟨M, mem_ZFamilyFinset.mpr (Or.inl rfl)⟩

/-- **BG 14.7, the `|T|` count for the family** (mmd L4031): with `T = Z − ⋃_{N} (Z ⊓ M_σ(N))`
over the family `ZFamilyFinset`, `|T| + ∑ |Kᵢ*| + 1 = |Z| + |family|` — i.e. `|T| = z + n − ∑ kᵢ*`
(`|family| = n + 1`).  Direct instance of inclusion–exclusion
(`ncard_sdiff_biUnion_subgroup`) with the pairwise disjointness `typeP_family_Kstar_disjoint`. -/
theorem typeP_family_T_count [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G)).ncard
      + (∑ N ∈ ZFamilyFinset M K, Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N)) + 1
      = Nat.card ↥(K ⊔ Kstar) + (ZFamilyFinset M K).card := by
  refine ncard_sdiff_biUnion_subgroup (s := ZFamilyFinset M K) (Z := K ⊔ Kstar)
    (S := fun N => (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N)
    ZFamilyFinset_nonempty (fun _ _ => inf_le_left) ?_
  intro N₁ hN₁ N₂ hN₂ hne
  exact typeP_family_Kstar_disjoint hG hM hP hKM hK hKstar hU
    (mem_ZFamilyFinset.mp hN₁) (mem_ZFamilyFinset.mp hN₂) hne

/-- **BG 14.7, each family factor `Kᵢ* ◁ Z`** (mmd L3995 "`N_{M_i}(X*) = K_i × K_i*`"): every member
`N` of the type-`P` family has its canonical factor `Z ⊓ M_σ(N)` normalised by all of `Z = K ⊔ K*`.
For `N = M` this is `typeP_self_member`; for a neighbour it is the normality clause of
`exists_neighbor_full`.  Feeds the `Z`-stability of `T` (`hstab` for the TI count). -/
theorem typeP_family_member_normal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    K ⊔ Kstar ≤ Subgroup.normalizer
      (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
  rcases hN with hNM | ⟨p, X, hp, hX, hXK, hN⟩
  · rw [hNM]; exact (typeP_self_member hG hM hP hKM hK hKstar hU).2.2.1
  · haveI : Fact p.Prime := ⟨hp⟩
    have hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
      intro hbot
      refine (typeP_structure hG hM hP hKM hK hKstar hU).2.1 (le_bot_iff.mp ?_)
      rw [hKstar]
      calc OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
          ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) :=
            inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK))
        _ = ⊥ := hbot
    obtain ⟨_, _, _, _, hnorm, _, _⟩ :=
      exists_neighbor_full hG hM hP hKM hK hKstar hU hX hXK hCX hN
    exact hnorm

/-- **BG 14.7, the family `Kᵢ*` pairwise commute** (mmd L4009): for distinct members `N₁ ≠ N₂`, the
canonical factors `Z ⊓ M_σ(Nᵢ)` centralise each other — both are normalised by `Z`
(`typeP_family_member_normal`) and meet trivially (`typeP_family_Kstar_disjoint`), so their
commutator lies in their (trivial) intersection.  The commute input to
`card_iSup_of_pairwise_commute_coprime` for `z = ∏ kᵢ*`. -/
theorem typeP_family_Kstar_commute [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N₁ N₂ : Subgroup G} (hN₁ : IsZFamilyMember M K N₁) (hN₂ : IsZFamilyMember M K N₂)
    (hne : N₁ ≠ N₂) :
    ∀ x ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₁,
      ∀ y ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₂, Commute x y :=
  commute_of_le_normalizer_of_disjoint inf_le_left inf_le_left
    (typeP_family_member_normal hG hM hP hKM hK hKstar hU hN₁)
    (typeP_family_member_normal hG hM hP hKM hK hKstar hU hN₂)
    (typeP_family_Kstar_disjoint hG hM hP hKM hK hKstar hU hN₁ hN₂ hne)

/-- **BG 14.7, `Z` normalises `T`** (mmd L4029, "`N_G(T) = Z`" half — the easy `Z ≤ N_G(T)` part):
conjugation by any `l ∈ Z = K ⊔ K*` fixes the set `T = Z − ⋃_{N} (Z ⊓ M_σ(N))`, because `l`
normalises `Z` (self-normalisation) and each canonical factor `Z ⊓ M_σ(N)`
(`typeP_family_member_normal`).  This is the `hstab` hypothesis of
`ncard_conjClassSet_of_isTISubset` once `T` is shown to be a TI-subset. -/
theorem typeP_family_Z_normalizes_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∀ l ∈ K ⊔ Kstar, MulAut.conj l •
        (((K ⊔ Kstar : Subgroup G) : Set G) \
          ⋃ N ∈ ZFamilyFinset M K,
            (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))
      = ((K ⊔ Kstar : Subgroup G) : Set G) \
          ⋃ N ∈ ZFamilyFinset M K,
            (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
  intro l hl
  rw [Set.smul_set_sdiff, Set.smul_set_iUnion₂]
  congr 1
  · rw [← Subgroup.coe_pointwise_smul,
      conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hl)]
  · refine Set.iUnion₂_congr (fun N hN => ?_)
    rw [← Subgroup.coe_pointwise_smul,
      conj_smul_eq_self_of_mem_normalizer
        (typeP_family_member_normal hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN) hl)]

/-- **BG Proposition 14.2(d), second assertion** (mmd L3827): for a type-`P` maximal `M` with Hall
`κ(M)`-subgroup `K` and `K* = C_{M_σ}(K)`, every `g ∈ M − (K ⊔ K*)` satisfies `K ∩ K^g = 1`.

BG: "the second assertion follows easily from (b1) since `K` is a Z-group."  Lean proof: a
nontrivial element of `K ∩ K^g` gives a rank-one `X = ⟨x⟩ ≤ K` of prime order `p` and its conjugate
`Y = ⟨g⁻¹ x g⟩ ≤ K`.  By Proposition 14.2(b1) (`typeP_structure`), `N_G(X) ⊓ M = N_G(Y) ⊓ M = Z`, so
`K` normalises both.  Since `g ∈ M` but `g ∉ Z`, `g ∉ N_G(X)`, hence `MulAut.conj g⁻¹ • X ≠ X`,
i.e. `X ≠ Y`.  Two distinct normal rank-one subgroups of `K` generate an elementary abelian `p²`
inside `M`, forcing `pRank_M(p) ≥ 2` — contradicting `pRank_M(p) = 1` (`p ∈ π(K) ⊆ κ(M) ⊆ τ₁ ∪ τ₃`).
This is the `(d)`-clause the TI-argument of Theorem 14.7 invokes (`g ∈ K_i × K_i*`). -/
theorem typeP_kappaHall_inf_conj_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {g : G} (hgM : g ∈ M) (hgZ : g ∉ K ⊔ Kstar) :
    K ⊓ (MulAut.conj g • K) = ⊥ := by
  classical
  by_contra hne
  -- A prime `p ∣ |K ∩ K^g|` and an order-`p` element `x ∈ K ∩ K^g`.
  have hcard_ne : Nat.card ↥(K ⊓ (MulAut.conj g • K)) ≠ 1 :=
    fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hcard_ne
  haveI : Fact p.Prime := ⟨hp_prime⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  have hxmem : (x : G) ∈ K ⊓ (MulAut.conj g • K) := x.2
  have hxK : (x : G) ∈ K := (Subgroup.mem_inf.mp hxmem).1
  have hxKg : (x : G) ∈ MulAut.conj g • K := (Subgroup.mem_inf.mp hxmem).2
  have hxord' : orderOf (x : G) = p :=
    (orderOf_injective (K ⊓ (MulAut.conj g • K)).subtype
      (K ⊓ (MulAut.conj g • K)).subtype_injective x).trans hxord
  have hxne1 : (x : G) ≠ 1 := fun h => hp_prime.ne_one (by rw [← hxord', h, orderOf_one])
  -- `X = ⟨x⟩ ≤ K`, rank-one.
  set X := Subgroup.zpowers (x : G) with hXdef
  have hXcard : Nat.card ↥X = p := by rw [hXdef, Nat.card_zpowers, hxord']
  have hXea : X ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXleK : X ≤ K := Subgroup.zpowers_le.mpr hxK
  -- `Y = ⟨g⁻¹ x g⟩ ≤ K`, rank-one (`g⁻¹ x g ∈ K` since `x ∈ K^g`).
  have hgxgK : g⁻¹ * (x : G) * g ∈ K := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxKg
    simpa [MulAut.smul_def] using hxKg
  set y₀ := g⁻¹ * (x : G) * g with hy₀def
  have hy₀conj : y₀ = (MulAut.conj g⁻¹).toMonoidHom (x : G) := by
    rw [hy₀def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hy₀ord : orderOf y₀ = p := by
    rw [hy₀conj, orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective]
    exact hxord'
  set Y := Subgroup.zpowers y₀ with hYdef
  have hYcard : Nat.card ↥Y = p := by rw [hYdef, Nat.card_zpowers, hy₀ord]
  have hYea : Y ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
  have hYleK : Y ≤ K := Subgroup.zpowers_le.mpr hgxgK
  -- (b1): `N_G(X) ⊓ M = N_G(Y) ⊓ M = Z`, so `K` normalises both.
  have hb1 := (typeP_structure hG hM hP hKM hK hKstar hU).2.2.1
  have hNX : Subgroup.normalizer (X : Set G) ⊓ M = K ⊔ Kstar := hb1 p hp_prime X hXea hXleK
  have hNY : Subgroup.normalizer (Y : Set G) ⊓ M = K ⊔ Kstar := hb1 p hp_prime Y hYea hYleK
  have hKNX : K ≤ Subgroup.normalizer (X : Set G) :=
    le_trans (le_trans le_sup_left hNX.ge) inf_le_left
  have hKNY : K ≤ Subgroup.normalizer (Y : Set G) :=
    le_trans (le_trans le_sup_left hNY.ge) inf_le_left
  -- `X ≠ Y`: else `MulAut.conj g⁻¹ • X = Y = X`, so `g ∈ N_G(X) ⊓ M = Z`, against `g ∉ Z`.
  have hXneY : X ≠ Y := by
    intro hXeqY
    have hsmulXY : MulAut.conj g⁻¹ • X = Y := by
      rw [hXdef, hYdef, hy₀conj,
        show MulAut.conj g⁻¹ • Subgroup.zpowers (x : G)
          = (Subgroup.zpowers (x : G)).map (MulAut.conj g⁻¹).toMonoidHom from rfl,
        MonoidHom.map_zpowers]
    have hginvNX : g⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
      mem_normalizer_of_conj_smul_eq_self (hsmulXY.trans hXeqY.symm)
    have hgNX : g ∈ Subgroup.normalizer (X : Set G) := by
      simpa using (Subgroup.normalizer (X : Set G)).inv_mem hginvNX
    exact hgZ (hNX ▸ Subgroup.mem_inf.mpr ⟨hgNX, hgM⟩)
  -- `X ⊓ Y = ⊥` (distinct rank-one subgroups of prime order `p`).
  have hXYbot : X ⊓ Y = ⊥ := by
    by_contra hb
    have hdvd : Nat.card ↥(X ⊓ Y) ∣ p := hXcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne1 : Nat.card ↥(X ⊓ Y) ≠ 1 := fun h => hb (Subgroup.eq_bot_of_card_eq _ h)
    have hpeq : Nat.card ↥(X ⊓ Y) = p := ((Nat.dvd_prime hp_prime).mp hdvd).resolve_left hne1
    have hXY_eq_X : X ⊓ Y = X :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (hXcard.le.trans hpeq.ge)
    exact hXneY (Subgroup.eq_of_le_of_card_ge (hXY_eq_X ▸ inf_le_right)
      (hYcard.le.trans hXcard.ge))
  -- `X`, `Y` commute (both normal in `K`, trivial meet), so `X ⊔ Y` is elementary abelian `p²`.
  have hcomm : ∀ a ∈ X, ∀ b ∈ Y, Commute a b :=
    commute_of_le_normalizer_of_disjoint hXleK hYleK hKNX hKNY hXYbot
  have hXcentY : X ≤ Subgroup.centralizer (Y : Set G) := fun a ha =>
    (Subgroup.mem_centralizer_iff).mpr fun b hb => (hcomm a ha b hb).symm
  have hsupea : (X ⊔ Y).IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.sup_of_le_centralizer hXea.1 hYea.1 hXcentY
  have hsupcard : Nat.card ↥(X ⊔ Y) = p ^ 2 := by
    rw [card_sup_of_commute_of_disjoint hcomm hXYbot, hXcard, hYcard]; ring
  -- `X ⊔ Y ≤ M`, witnessing `pRank_M(p) ≥ 2`.
  have hsupM : X ⊔ Y ≤ M := sup_le (hXleK.trans hKM) (hYleK.trans hKM)
  have hsubea : ((X ⊔ Y).subgroupOf M).IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hsupM).symm hsupea
  have hsubcard : Nat.card ↥((X ⊔ Y).subgroupOf M) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsupM).toEquiv, hsupcard]
  have hle := le_pRank ((X ⊔ Y).subgroupOf M) hsubea
  rw [hsubcard, Nat.log_pow hp_prime.one_lt] at hle
  -- but `pRank_M(p) = 1` since `p ∈ π(K) ⊆ κ(M) ⊆ τ₁ ∪ τ₃`.
  have hp_kappa : p ∈ kappa M := by
    apply hK.1 p
    rw [Nat.mem_primeFactors]
    refine ⟨hp_prime, ?_, Nat.card_pos.ne'⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
    exact hp_dvd.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hpRank1 : pRank ↥M p = 1 := by
    rcases kappa_subset_tau1_union_tau3 hp_kappa with h | h
    · exact tau1_pRank_eq_one h
    · exact tau3_pRank_eq_one h
  omega

/-- **BG 14.7, the family `σ(Nᵢ)` cover `π(z)`** (mmd L4007 "each `X ∈ ℰ¹(Z)` lies in some `Kᵢ*`"):
every prime `p ∣ |Z|` lies in `σ(N)` for some family member `N`.  For `p ∣ |K*|` it is the base
member `M` (`K* ≤ M_σ`, `Kstar_isPiSubgroup_sigma`); for `p ∣ |K|` (`p ∈ κ(M)`) a line
`X ∈ ℰ_p¹(K)` has a type-`P` partner `N ∈ 𝓜(N_G(X))` — a family member — with `X ⊆ M_σ(N)`, so
`p ∈ σ(N)`.  This coverage forces `⋂ᵢ Kᵢ = 1`, i.e. the `t = yy'` characterisation of `T`. -/
theorem typeP_family_sigma_covers [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} (hp : p.Prime) (hpZ : p ∣ Nat.card ↥(K ⊔ Kstar)) :
    ∃ N : Subgroup G, IsZFamilyMember M K N ∧ p ∈ OddOrder.BG.Ch3.S10.sigma N := by
  classical
  rw [card_kappaHall_sup_Kstar hKM hK hKstar] at hpZ
  rcases hp.dvd_mul.mp hpZ with hpK | hpKstar
  · -- `p ∣ k`: a line `X ∈ ℰ_p¹(K)` and its type-`P` partner is a family member.
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
    have hxord : orderOf (x : G) = p :=
      (orderOf_injective K.subtype K.subtype_injective x).trans hx
    have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
    have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
    have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
    obtain ⟨N, hNmem, _, _, hXNσ, _, _⟩ :=
      exists_typeP_partner hG hM hP hKM hK hKstar hU hXelem hXK
    refine ⟨N, Or.inr ⟨p, Subgroup.zpowers (x : G), hp, hXelem, hXK, hNmem⟩, ?_⟩
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
      ⟨hp, (by rw [hXcard] : p ∣ Nat.card ↥(Subgroup.zpowers (x : G))).trans
        (Subgroup.card_dvd_of_le hXNσ), Nat.card_pos.ne'⟩)
  · -- `p ∣ k*`: the base member `M` itself, since `K* ≤ M_σ`.
    exact ⟨M, Or.inl rfl, Kstar_isPiSubgroup_sigma hKstar p
      (Nat.mem_primeFactors.mpr ⟨hp, hpKstar, Nat.card_pos.ne'⟩)⟩

/-- **BG 14.7, `Kᵢ*` is the `σ(Nᵢ)`-Hall of `Z`** (mmd L4007): for a family member `N` and a prime
`p ∈ σ(N)`, the full `p`-part of `|Z|` divides `|Kᵢ*| = |Z ⊓ M_σ(N)|`.  From the swap
`|Z| = |K_N|·|Kᵢ*|` (`card_kappaHall_sup_Kstar` on `N`'s data), `K_N` a `σ(N)'`-group
(`kappaHall_isPiSubgroup_sigmaCompl`), so `p ∤ |K_N|` and `pᵏ ∣ |Z|` forces `pᵏ ∣ |Kᵢ*|`.  Feeds
the σ-decomposition `⊔ Kᵢ* = Z`. -/
theorem typeP_family_prime_pow_dvd_Kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) {p k : ℕ} (hp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma N) (hpk : p ^ k ∣ Nat.card ↥(K ⊔ Kstar)) :
    p ^ k ∣ Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
  obtain ⟨_, _, _, KN, hKNN, hKN, hswap, hcanon, _⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  -- `|Z| = |K_N| · |Kᵢ*|`.
  have hZcard : Nat.card ↥(K ⊔ Kstar)
      = Nat.card ↥KN * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    have h := card_kappaHall_sup_Kstar hKNN hKN
      (rfl : OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
        = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G))
    rw [← hswap, hcanon] at h
    exact h
  -- `p ∤ |K_N|` (a `σ(N)'`-group), so `pᵏ` is coprime to `|K_N|`.
  have hpKN : ¬ p ∣ Nat.card ↥KN := fun hd =>
    kappaHall_isPiSubgroup_sigmaCompl hKNN hKN p
      (Nat.mem_primeFactors.mpr ⟨hp, hd, Nat.card_pos.ne'⟩) hpσ
  have hcop : Nat.Coprime (p ^ k) (Nat.card ↥KN) :=
    (hp.coprime_iff_not_dvd.mpr hpKN).pow_left k
  exact hcop.dvd_of_dvd_mul_left (hZcard ▸ hpk)

/-- **BG 14.7, the σ-decomposition `⊔ Kᵢ* = Z`** (mmd L4009): the canonical factors of the family
join to all of `Z`.  `⊔ Kᵢ* ≤ Z` is clear; for `Z ≤ ⊔ Kᵢ*` it suffices that `|Z| ∣ |⊔ Kᵢ*|`, which
holds prime-power-wise: for `pᵏ ∣ |Z|` the prime `p` lies in some `σ(N)`
(`typeP_family_sigma_covers`), and then `pᵏ ∣ |Kᵢ*|` (`typeP_family_prime_pow_dvd_Kstar`) `∣ |⊔ Kᵢ*|`.
With `⊔ Kᵢ* ≤ Z` this gives equality.  The structural heart of the TI-of-`T` step. -/
theorem typeP_family_iSup_Kstar_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ⨆ N ∈ ZFamilyFinset M K, ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) = K ⊔ Kstar := by
  have hsuple : (⨆ N ∈ ZFamilyFinset M K, ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N))
      ≤ K ⊔ Kstar := iSup₂_le fun _ _ => inf_le_left
  have hdvd : Nat.card ↥(K ⊔ Kstar)
      ∣ Nat.card ↥(⨆ N ∈ ZFamilyFinset M K, ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N)) := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    · have hpZ : p ∣ Nat.card ↥(K ⊔ Kstar) := (dvd_pow_self p hkpos.ne').trans hpk
      obtain ⟨N, hN, hpσ⟩ := typeP_family_sigma_covers hG hM hP hKM hK hKstar hU hp hpZ
      exact (typeP_family_prime_pow_dvd_Kstar hG hM hP hKM hK hKstar hU hN hp hpσ hpk).trans
        (Subgroup.card_dvd_of_le
          (le_iSup₂ (f := fun N _ => (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) N
            (mem_ZFamilyFinset.mpr hN)))
  exact Subgroup.eq_of_le_of_card_ge hsuple (Nat.le_of_dvd Nat.card_pos hdvd)

/-- **BG 14.7, `σ(N)`-elements of `Z` lie in `Kᵢ*`** (mmd L4019, the `σ`-part lands in `Kᵢ*`): for a
family member `N`, every `σ(N)`-element `a ∈ Z` lies in `Kᵢ* = Z ⊓ M_σ(N)`.  Since `a ∈ Z ≤ N`, the
cyclic `⟨a⟩` is a `σ(N)`-subgroup of `N`, hence `⟨a⟩ ≤ M_σ(N)`
(`sigma_subgroup_le_Msigma_of_isHall`); combined with `a ∈ Z` this gives `a ∈ Z ⊓ M_σ(N)`.  This
places the `σ(N)`-part of any `t ∈ Z` into `Kᵢ*` — half of the `t = yy'` characterisation of `T`. -/
theorem typeP_family_isPiElement_mem_Kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) {a : G} (haZ : a ∈ K ⊔ Kstar)
    (hapi : IsPiElement (OddOrder.BG.Ch3.S10.sigma N) a) :
    a ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N := by
  obtain ⟨hNmax, _, hZN, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  refine Subgroup.mem_inf.mpr ⟨haZ, ?_⟩
  have hpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma N) (Subgroup.zpowers a) := by
    intro p hp
    rw [Nat.card_zpowers] at hp
    exact hapi p hp
  exact OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hNmax)
    (Subgroup.zpowers_le.mpr (hZN haZ)) hpi (Subgroup.mem_zpowers a)

/-- **An internal direct factor absorbs coprime elements** (BG 14.7, the `σ(N)′`-part lands in
`K_N`): if `Z = A ⊔ B` with `B ≤ C_G(A)` (so `A`, `B` commute), `A` a `πᶜ`-group and `B` a
`π`-group, then every `πᶜ`-element of `Z` lies in `A`.  Proof: `A ◁ Z` (commuting factor) is a Hall
`πᶜ`-subgroup of `Z` (`|Z| = |A|·|B|`, index `= |B|` a `π`-number), so the `πᶜ`-group `⟨b⟩ ≤ Z` lies
in `A` (`isPiGroup_le_of_normal_isHallSubgroup` in `↥Z`).  Applied with `A = K_N` (the `σ(N)′`-Hall
of `Z`), `B = Kᵢ*`, `π = σ(N)`: the `σ(N)′`-part of any `t ∈ Z` lands in `K_N`. -/
theorem isPiElementCompl_mem_left_of_commute [Finite G] {A B Z : Subgroup G} {π : Set ℕ}
    (hswap : Z = A ⊔ B) (hcent : B ≤ Subgroup.centralizer (A : Set G))
    (hAπc : Subgroup.IsPiSubgroup πᶜ A) (hBπ : Subgroup.IsPiSubgroup π B)
    {b : G} (hbZ : b ∈ Z) (hbπc : IsPiElement πᶜ b) : b ∈ A := by
  classical
  have hAZ : A ≤ Z := by rw [hswap]; exact le_sup_left
  have hcomm : ∀ a ∈ A, ∀ c ∈ B, Commute a c := fun a ha c hc =>
    Subgroup.mem_centralizer_iff.mp (hcent hc) a ha
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥B) := by
    apply Nat.coprime_of_dvd
    intro p hp hpA hpB
    exact (hAπc p (Nat.mem_primeFactors.mpr ⟨hp, hpA, Nat.card_pos.ne'⟩))
      (hBπ p (Nat.mem_primeFactors.mpr ⟨hp, hpB, Nat.card_pos.ne'⟩))
  have hdisj : A ⊓ B = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hnorm : Z ≤ Subgroup.normalizer (A : Set G) := by
    rw [hswap]; exact (sup_le_normalizer_inf_of_commute hcent).trans inf_le_left
  haveI hAnZ : (A.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAZ).mpr hnorm
  have hZcard : Nat.card ↥Z = Nat.card ↥A * Nat.card ↥B := by
    rw [hswap]; exact card_sup_of_commute_of_disjoint hcomm hdisj
  have hcardSub : Nat.card ↥(A.subgroupOf Z) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv
  have hidx : (A.subgroupOf Z).index = Nat.card ↥B := by
    have hl := Subgroup.card_mul_index (A.subgroupOf Z)
    rw [hcardSub, hZcard] at hl
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hl
  have hHall : Ch03.IsHallSubgroup πᶜ (A.subgroupOf Z) := by
    refine ⟨fun p hp => ?_, fun p hp hpc => ?_⟩
    · rw [hcardSub] at hp; exact hAπc p hp
    · exact hpc (hBπ p (by rwa [hidx] at hp))
  have hbZsub : (Subgroup.zpowers b).subgroupOf Z ≤ A.subgroupOf Z := by
    refine OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hHall (fun p hp => ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hbZ)).toEquiv, Nat.card_zpowers] at hp
    exact hbπc p hp
  have hbmem : (⟨b, hbZ⟩ : ↥Z) ∈ (Subgroup.zpowers b).subgroupOf Z :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers b)
  exact Subgroup.mem_subgroupOf.mp (hbZsub hbmem)

/-- **BG 14.7, the family member's `(d)`-data bundle** (mmd L3827, both clauses of Prop 14.2(d)):
for a family member `N`, the chosen Hall `κ(N)`-subgroup `K_N` together with the swap
`Z = K_N ⊔ Kᵢ*` and both conjugacy clauses — (d)-first `Kᵢ* ⊓ Nᵍ = 1` (`g ∉ N`) and (d)-second
`K_N ⊓ K_Nᵍ = 1` (`g ∈ N`, `g ∉ Z`).  Builds `N`'s Hall `(κ∪σ)′`-subgroup once
(`hall_E_exists`, `N` solvable) and feeds it to `typeP_structure` (d-first) and
`typeP_kappaHall_inf_conj_eq_bot` (d-second).  The TI-of-`T` proof obtains this once per chosen
member and conjugates the `σ`/`σ′`-parts of `t` through the two clauses to force `g ∈ Z`. -/
theorem typeP_family_member_dData [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ∧
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ≤ Subgroup.centralizer (KN : Set G) ∧
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma N)ᶜ KN ∧
      (∀ g : G, g ∉ N →
        ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ⊓ (MulAut.conj g • N) = ⊥) ∧
      (∀ g : G, g ∈ N → g ∉ K ⊔ Kstar → KN ⊓ (MulAut.conj g • KN) = ⊥) := by
  classical
  obtain ⟨hNmax, hPN, _, KN, hKNN, hKN, hswap, hcanon, _⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  haveI : IsSolvable ↥N := hG.solvable_of_mem_maximalSubgroups hNmax
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥N)
    ((kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ)
  have hUeq : (U'.map N.subtype).subgroupOf N = U' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective U'
  have hUN : Ch03.IsHallSubgroup ((kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ)
      ((U'.map N.subtype).subgroupOf N) := by rw [hUeq]; exact hU'
  refine ⟨KN, hKNN, hKN, hswap.trans (by rw [hcanon]), hcanon ▸ inf_le_right,
    kappaHall_isPiSubgroup_sigmaCompl hKNN hKN, ?_, ?_⟩
  · intro g hgN
    have hd := (typeP_structure hG hNmax hPN hKNN hKN rfl hUN).2.2.2.1
    rw [hcanon] at hd
    exact hd g hgN
  · intro g hgN hgZ
    exact typeP_kappaHall_inf_conj_eq_bot hG hNmax hPN hKNN hKN rfl hUN hgN (hswap ▸ hgZ)

/-- **BG 14.7, every nontrivial `t ∈ Z` has a nontrivial `σ`-part** (mmd L4015, `z = ∏ xᵢ` is the
`σ`-decomposition): for `t ∈ Z`, `t ≠ 1`, some family member `N` has `t` *not* a `σ(N)′`-element
(equivalently its `σ(N)`-part is nontrivial).  Else every prime of `ord(t)` avoids every `σ(N)`,
contradicting the coverage `⋃ σ(Nᵢ) ⊇ π(z)` (`typeP_family_sigma_covers`) since `ord(t) ∣ |Z|`.
This is the half of the `t = yy'` characterisation that finds the splitting member. -/
theorem typeP_family_exists_sigmaPart [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {t : G} (htZ : t ∈ K ⊔ Kstar) (ht1 : t ≠ 1) :
    ∃ N : Subgroup G, IsZFamilyMember M K N ∧
      ¬ IsPiElement (OddOrder.BG.Ch3.S10.sigma N)ᶜ t := by
  by_contra hcon
  push Not at hcon
  -- `ord(t) ≠ 1` has a prime factor `p`, and `p ∣ |Z|`.
  have hordne : orderOf t ≠ 1 := by rw [Ne, orderOf_eq_one_iff]; exact ht1
  obtain ⟨p, hp, hpord⟩ := Nat.exists_prime_and_dvd hordne
  have hpz : p ∣ Nat.card ↥(K ⊔ Kstar) := by
    refine hpord.trans ?_
    have := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr htZ)
    rwa [Nat.card_zpowers] at this
  obtain ⟨N, hN, hpσN⟩ := typeP_family_sigma_covers hG hM hP hKM hK hKstar hU hp hpz
  exact hcon N hN p (Nat.mem_primeFactors.mpr ⟨hp, hpord, (orderOf_pos t).ne'⟩) hpσN

/-- **BG 14.7, `T` is a TI-subset of `G` with normalizer `Z`** (mmd L4027-4029): `T = Z − ⋃ Kᵢ*`
satisfies `IsTISubset T Z`.  Given `t ∈ T` and `g` with `tᵍ ∈ T ⊆ Z`: pick a member `N` whose
`σ(N)`-part of `t` is nontrivial (`typeP_family_exists_sigmaPart`), `π`-decompose `t = y·y'`
(`exists_isPiElement_mul`, `π = σ(N)`) with `y ∈ Kᵢ*` (`…isPiElement_mem_Kstar`) and `y' ∈ K_N`
(`isPiElementCompl_mem_left_of_commute`), both nontrivial (`y` by choice of `N`, `y'` since
`t ∉ Kᵢ*`).  Conjugates `yᵍ, y'ᵍ` are powers of `tᵍ ∈ Z`, so `yᵍ ∈ Kᵢ*`, `y'ᵍ ∈ K_N`; then
`yᵍ ∈ Kᵢ* ∩ Nᵍ` forces `g ∈ N` (Prop 14.2(d)-first) and `y'ᵍ ∈ K_N ∩ K_Nᵍ` forces `g ∈ Z`
(d-second).  The structural core converting `|T|` to `|𝒞_G(T)| = |T|·[G:Z]`. -/
theorem typeP_family_T_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    OddOrder.GroupTheory.IsTISubset
      (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))
      (K ⊔ Kstar) := by
  classical
  rintro g ⟨t, ⟨htZ, htnot⟩, ⟨htgZ, -⟩⟩
  -- `t ∈ Z`, `t ∉ ⋃ Kⱼ*`, `g t g⁻¹ ∈ Z`.
  have htZ' : t ∈ K ⊔ Kstar := htZ
  have htgZ' : g * t * g⁻¹ ∈ K ⊔ Kstar := htgZ
  have ht1 : t ≠ 1 := fun h => htnot
    (Set.mem_biUnion (mem_ZFamilyFinset.mpr (Or.inl rfl)) (h ▸ one_mem _))
  -- Conjugation by `g` keeps powers of `t` inside `Z` and preserves `π`-element-ness.
  have hconjZ : ∀ a : G, a ∈ Subgroup.zpowers t → g * a * g⁻¹ ∈ K ⊔ Kstar := by
    intro a ha
    refine (Subgroup.zpowers_le.mpr htgZ') ?_
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ha
    rw [MonoidHom.map_zpowers] at h1
    simpa [MulAut.conj_apply] using h1
  have hordeq : ∀ a : G, orderOf (g * a * g⁻¹) = orderOf a := fun a => by
    rw [show g * a * g⁻¹ = (MulAut.conj g).toMonoidHom a by simp [MulAut.conj_apply]]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
  have hpiconj : ∀ {π : Set ℕ} {a : G}, IsPiElement π a → IsPiElement π (g * a * g⁻¹) :=
    fun {π a} ha p hp => ha p (by rwa [hordeq a] at hp)
  -- Pick a member `N` with nontrivial `σ(N)`-part, and `π`-decompose `t`.
  obtain ⟨N, hN, hσpart⟩ := typeP_family_exists_sigmaPart hG hM hP hKM hK hKstar hU htZ' ht1
  obtain ⟨y, y', hyy', hcomm, hyπ, hy'π, hyz, hy'z⟩ :=
    exists_isPiElement_mul (OddOrder.BG.Ch3.S10.sigma N) t
  have hyZ : y ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ') hyz
  have hy'Z : y' ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ') hy'z
  obtain ⟨KN, hKNN, _, hswap, hcent, hAπc, hdfirst, hdsecond⟩ :=
    typeP_family_member_dData hG hM hP hKM hK hKstar hU hN
  have hBπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma N)
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
      ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
  -- `y ∈ Kᵢ*`, `y' ∈ K_N`; both nontrivial.
  have hyKstar : y ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    typeP_family_isPiElement_mem_Kstar hG hM hP hKM hK hKstar hU hN hyZ hyπ
  have hy'KN : y' ∈ KN := isPiElementCompl_mem_left_of_commute hswap hcent hAπc hBπ hy'Z hy'π
  have hy1 : y ≠ 1 := by
    rintro rfl; exact hσpart (by rw [show t = y' from by rw [← hyy', one_mul]]; exact hy'π)
  have hy'1 : y' ≠ 1 := by
    rintro rfl
    exact htnot (Set.mem_biUnion (mem_ZFamilyFinset.mpr hN)
      (show t ∈ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) from
        by rw [show t = y from by rw [← hyy', mul_one]]; exact hyKstar))
  -- `yᵍ ∈ Kᵢ*` (a `σ(N)`-element of `Z`), `yᵍ ≠ 1`; force `g ∈ N` via (d)-first.
  have hygZ : g * y * g⁻¹ ∈ K ⊔ Kstar := hconjZ y hyz
  have hygKstar : g * y * g⁻¹ ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    typeP_family_isPiElement_mem_Kstar hG hM hP hKM hK hKstar hU hN hygZ (hpiconj hyπ)
  have hyg1 : g * y * g⁻¹ ≠ 1 := fun h =>
    hy1 ((map_eq_one_iff _ (MulAut.conj g).injective).mp (by rw [MulAut.conj_apply]; exact h))
  have hgN : g ∈ N := by
    by_contra hgnot
    have hbot := hdfirst g hgnot
    have hmem : g * y * g⁻¹ ∈ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ⊓ (MulAut.conj g • N) := by
      refine Subgroup.mem_inf.mpr ⟨hygKstar, ?_⟩
      have hyN : y ∈ N := (inf_le_right.trans (OddOrder.BG.Ch3.S10.Msigma_le N)) hyKstar
      rw [show (MulAut.conj g • N : Subgroup G) = N.map (MulAut.conj g).toMonoidHom from rfl,
        show g * y * g⁻¹ = (MulAut.conj g).toMonoidHom y from by
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]]
      exact Subgroup.mem_map_of_mem _ hyN
    rw [hbot] at hmem
    exact hyg1 (Subgroup.mem_bot.mp hmem)
  -- `y'ᵍ ∈ K_N ∩ K_Nᵍ`, `y'ᵍ ≠ 1`; force `g ∈ Z` via (d)-second.
  have hy'gZ : g * y' * g⁻¹ ∈ K ⊔ Kstar := hconjZ y' hy'z
  have hy'gKN : g * y' * g⁻¹ ∈ KN :=
    isPiElementCompl_mem_left_of_commute hswap hcent hAπc hBπ hy'gZ (hpiconj hy'π)
  have hy'g1 : g * y' * g⁻¹ ≠ 1 := fun h =>
    hy'1 ((map_eq_one_iff _ (MulAut.conj g).injective).mp (by rw [MulAut.conj_apply]; exact h))
  by_contra hgZ
  have hbot := hdsecond g hgN hgZ
  have hmem : g * y' * g⁻¹ ∈ KN ⊓ (MulAut.conj g • KN) := by
    refine Subgroup.mem_inf.mpr ⟨hy'gKN, ?_⟩
    rw [show (MulAut.conj g • KN : Subgroup G) = KN.map (MulAut.conj g).toMonoidHom from rfl,
      show g * y' * g⁻¹ = (MulAut.conj g).toMonoidHom y' from by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]]
    exact Subgroup.mem_map_of_mem _ hy'KN
  rw [hbot] at hmem
  exact hy'g1 (Subgroup.mem_bot.mp hmem)

/-- **BG 14.7, `|𝒞_G(T)| = |T|·[G:Z]`** (mmd L4031): the conjugacy-saturation count of the TI-set
`T = Z − ⋃ Kᵢ*`.  Direct composition of `ncard_conjClassSet_of_isTISubset` with the TI property
(`typeP_family_T_isTI`) and the `Z`-stability `hstab` (`typeP_family_Z_normalizes_T`).  With
`|T| = z + n − ∑ kᵢ*` (`typeP_family_T_count`) this is BG's `(1 + n/z − ∑ 1/kᵢ)|G|`, the left
summand of the density inequality. -/
theorem typeP_family_conjClass_T_count [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (conjClassSet (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))).ncard
      = (((K ⊔ Kstar : Subgroup G) : Set G) \
          ⋃ N ∈ ZFamilyFinset M K,
            (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G)).ncard
        * (K ⊔ Kstar).index :=
  ncard_conjClassSet_of_isTISubset
    (typeP_family_T_isTI hG hM hP hKM hK hKstar hU)
    (typeP_family_Z_normalizes_T hG hM hP hKM hK hKstar hU)

/-- **BG 14.7, `Z ⊊ Mᵢ` (so `|Mᵢ| ≥ 2z`)** (mmd L4033, the `|M_i| ≥ 2z` step): every family member
`N` properly contains `Z = K ⊔ K*`.  The clean argument (NOT self-centralizing — BG's "prime
manner" allows trivial action): the family has `≥ 2` members (`M` plus a neighbour, which exists
since `N_G(X) ⊄ M` for `X ∈ ℰ¹(K)`), all containing `Z`; if `Z = N` then `N ⊆ M'` for some other
member `M' ≠ N`, impossible for distinct maximal subgroups.  Hence `Z ⊊ N`, giving `|N| ≥ 2z`. -/
theorem typeP_family_Z_lt_member [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    K ⊔ Kstar < N := by
  classical
  -- Distinct maximal subgroups form an antichain.
  have hanti : ∀ {A B : Subgroup G}, A ∈ maximalSubgroups G → B ∈ maximalSubgroups G →
      A ≤ B → A = B := fun {A B} hA hB hAB => hAB.lt_or_eq.elim
    (fun hlt => absurd ((mem_maximalSubgroups.mp hA).2 _ hlt) (mem_maximalSubgroups.mp hB).1) id
  -- A prime `p ∣ |K|` (κ(M) ≠ ∅, κ-primes divide |M|, Hall index avoids κ).
  have hP2 := hP
  obtain ⟨p, hpκ⟩ := hP2
  have hpprime : p.Prime := hpκ.1
  obtain ⟨P, hPelem, hPM, -⟩ := hpκ.2.2
  have hpcardP : Nat.card ↥P = p := by obtain ⟨_, hc⟩ := hPelem; rwa [pow_one] at hc
  have hpM : p ∣ Nat.card ↥M := hpcardP ▸ Subgroup.card_dvd_of_le hPM
  have hpK : p ∣ Nat.card ↥K := by
    have hlag : Nat.card ↥K * (K.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact Subgroup.card_mul_index (K.subgroupOf M)
    have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hd =>
      hK.2 p (Nat.mem_primeFactors.mpr ⟨hpprime, hd, Subgroup.index_ne_zero_of_finite⟩) hpκ
    exact (hpprime.dvd_mul.mp (hlag.symm ▸ hpM)).resolve_right hpidx
  -- A neighbour `N₁ ≠ M` containing `Z`.
  obtain ⟨N₁, hN₁max, -, hncM, -, hZN₁⟩ :=
    exists_typeP_neighbor_mem_sigma hG hM hP hKM hK hKstar hU hpprime hpK
  have hN₁neM : N₁ ≠ M := fun h =>
    hncM (h ▸ (⟨1, by rw [map_one, one_smul]⟩ : IsConjugateSubgroup M M))
  obtain ⟨hNmax, -, hZN, -⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  have hZM : K ⊔ Kstar ≤ M :=
    sup_le hKM (hKstar ▸ inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
  refine lt_of_le_of_ne hZN (fun heq => ?_)
  by_cases hNM : N = M
  · exact hN₁neM ((hanti hNmax hN₁max (heq ▸ hZN₁)).symm.trans hNM)
  · exact hNM (hanti hNmax hM (heq ▸ hZM))

/-- **BG 14.7, `|Mᵢ| ≥ 2z`** (mmd L4033): the cardinality form of `Z ⊊ Mᵢ`, the lower bound the
density inequality needs (`|𝒞_G(M̃ᵢ)| ≥ (1/kᵢ − 1/2z)|G|`).  From `Z < N` (proper), `[N : Z] ≥ 2`. -/
theorem typeP_family_two_mul_card_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    2 * Nat.card ↥(K ⊔ Kstar) ≤ Nat.card ↥N := by
  classical
  have hlt := typeP_family_Z_lt_member hG hM hP hKM hK hKstar hU hN
  have hle : K ⊔ Kstar ≤ N := hlt.le
  have hlag : Nat.card ↥(K ⊔ Kstar) * ((K ⊔ Kstar).subgroupOf N).index = Nat.card ↥N := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact Subgroup.card_mul_index ((K ⊔ Kstar).subgroupOf N)
  have hne1 : ((K ⊔ Kstar).subgroupOf N).index ≠ 1 := fun h =>
    hlt.ne (le_antisymm hle (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h)))
  have hidx2 : 2 ≤ ((K ⊔ Kstar).subgroupOf N).index :=
    (Nat.two_le_iff _).mpr ⟨Subgroup.index_ne_zero_of_finite, hne1⟩
  calc 2 * Nat.card ↥(K ⊔ Kstar)
      ≤ ((K ⊔ Kstar).subgroupOf N).index * Nat.card ↥(K ⊔ Kstar) :=
        Nat.mul_le_mul_right _ hidx2
    _ = Nat.card ↥(K ⊔ Kstar) * ((K ⊔ Kstar).subgroupOf N).index := Nat.mul_comm _ _
    _ = Nat.card ↥N := hlag

/-- **`σ`-sharp set is conjugation-equivariant**: `conj g • (M_σ^#) = (M^g)_σ^#`.  From
`Msigma_conj_smul` (`M_σ` equivariant) and `conj g` fixing `1`. -/
theorem sigmaSharp_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    MulAut.conj g • sigmaSharp M = sigmaSharp (MulAut.conj g • M) := by
  rw [sigmaSharp, sigmaSharp, sharpSubgroup, sharpSubgroup, Set.smul_set_sdiff,
    ← Subgroup.coe_pointwise_smul, ← Msigma_conj_smul]
  congr 1
  simp [Set.smul_set_singleton, MulAut.smul_def]

/-- **`M̃` is conjugation-equivariant** (mmd L3908): `conj g • M̃(M) = M̃(Mᵍ)`.  Each product
`x·x'` (`x ∈ M_σ^#`, `x' ∈ R(x)`) conjugates to `(xᵍ)(x'ᵍ)` with `xᵍ ∈ (Mᵍ)_σ^#`
(`sigmaSharp_conj_smul`) and `x'ᵍ ∈ R(xᵍ)` (`Rsub_conj`).  This is what turns the set-level
disjointness 14.5(b) into disjointness of the conjugacy saturations `𝒞_G(M̃ᵢ)`. -/
theorem Mtilde_conj_smul [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) (g : G) (M : Subgroup G) :
    MulAut.conj g • Mtilde hG D M = Mtilde hG D (MulAut.conj g • M) := by
  have hle : ∀ (h : G) (N : Subgroup G),
      MulAut.conj h • Mtilde hG D N ⊆ Mtilde hG D (MulAut.conj h • N) := by
    rintro h N y ⟨z, ⟨x, hx, x', hx', rfl⟩, rfl⟩
    refine ⟨MulAut.conj h • x, ?_, MulAut.conj h • x', ?_, ?_⟩
    · rw [← sigmaSharp_conj_smul]; exact Set.smul_mem_smul_set hx
    · rw [show MulAut.conj h • x = h * x * h⁻¹ from by rw [MulAut.smul_def, MulAut.conj_apply],
        Rsub_conj]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hx'
    · exact smul_mul' _ _ _
  refine Set.Subset.antisymm (hle g M) (fun y hy => ?_)
  have h2 := hle g⁻¹ (MulAut.conj g • M)
  rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h2
  have hmem : MulAut.conj g⁻¹ • y ∈ Mtilde hG D M := h2 (Set.smul_mem_smul_set hy)
  rw [show y = MulAut.conj g • (MulAut.conj g⁻¹ • y) by
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]]
  exact Set.smul_mem_smul_set hmem

/-- **BG 14.7, the `𝒞_G(M̃ᵢ)` are pairwise disjoint** (mmd L4035): for nonconjugate maximal
`M₁`, `M₂`, the conjugacy saturations `𝒞_G(M̃₁)`, `𝒞_G(M̃₂)` are disjoint.  A common element `z`
is `g₁t₁g₁⁻¹ = g₂t₂g₂⁻¹` with `tᵢ ∈ M̃(Mᵢ)`, so `z ∈ M̃(M₁ᵍ¹) ∩ M̃(M₂ᵍ²)` (`Mtilde_conj_smul`);
`M₁ᵍ¹`, `M₂ᵍ²` are nonconjugate (else `M₁ ~ M₂`), so 14.5(b) (`Mtilde_disjoint`) gives a
contradiction.  Pairwise disjointness of the density-inequality summands. -/
theorem conjClassSet_Mtilde_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M₁ M₂ : Subgroup G} (hM₁ : M₁ ∈ maximalSubgroups G)
    (hM₂ : M₂ ∈ maximalSubgroups G) (hnc : ¬ IsConjugateSubgroup M₁ M₂) :
    Disjoint (conjClassSet (Mtilde hG D M₁)) (conjClassSet (Mtilde hG D M₂)) := by
  rw [Set.disjoint_left]
  rintro z ⟨t₁, ht₁, g₁, rfl⟩ ⟨t₂, ht₂, g₂, hz₂⟩
  have hz1 : g₁ * t₁ * g₁⁻¹ ∈ Mtilde hG D (MulAut.conj g₁ • M₁) := by
    rw [show g₁ * t₁ * g₁⁻¹ = MulAut.conj g₁ • t₁ from by rw [MulAut.smul_def, MulAut.conj_apply],
      ← Mtilde_conj_smul]
    exact Set.smul_mem_smul_set ht₁
  have hz2 : g₁ * t₁ * g₁⁻¹ ∈ Mtilde hG D (MulAut.conj g₂ • M₂) := by
    rw [← hz₂, show g₂ * t₂ * g₂⁻¹ = MulAut.conj g₂ • t₂ from by
      rw [MulAut.smul_def, MulAut.conj_apply], ← Mtilde_conj_smul]
    exact Set.smul_mem_smul_set ht₂
  have hc1 : IsConjugateSubgroup M₁ (MulAut.conj g₁ • M₁) := ⟨g₁, rfl⟩
  have hc2 : IsConjugateSubgroup M₂ (MulAut.conj g₂ • M₂) := ⟨g₂, rfl⟩
  have hncc : ¬ IsConjugateSubgroup (MulAut.conj g₁ • M₁) (MulAut.conj g₂ • M₂) := fun h =>
    hnc ((hc1.trans h).trans hc2.symm)
  exact Set.disjoint_left.mp (Mtilde_disjoint hG D
    (mem_maximalSubgroups_of_isConjugateSubgroup hM₁ ⟨g₁, rfl⟩)
    (mem_maximalSubgroups_of_isConjugateSubgroup hM₂ ⟨g₂, rfl⟩) hncc) hz1 hz2

/-- **`M̃`-membership is the `not_type1_of_type2` "type-2 form"**: `g ∈ M̃(M)` (for maximal `M`)
gives `g = x·x'` with `ℓ_σ(x) = 1` and `x' ∈ R(x)`.  The `ℓ_σ(x) = 1` is from `length_one_iff`
(`x ∈ M_σ^#`, so `M ∈ 𝓜_σ(x)`).  Feeds the `𝒞_G(T) ⊥ 𝒞_G(M̃ᵢ)` disjointness via Lemma 14.6. -/
theorem mem_Mtilde_imp_form [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G}
    (hg : g ∈ Mtilde hG D M) :
    ∃ x x' : G, g = x * x' ∧ D.length x = 1 ∧ x' ∈ Rsub hG D x := by
  obtain ⟨x, hx, x', hx', rfl⟩ := hg
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hx
  exact ⟨x, x', rfl, (D.length_one_iff x).mpr ⟨hx.2, ⟨M, hM, hx.1⟩⟩, hx'⟩

/-- **Elements of `M̃` have `σ`-length at most two** (the per-element core of BG Cor 14.10): every
`g ∈ M̃(M) = ⋃_{x ∈ M_σ#} x·R(x)` is a `σ`-cover element `x·x'` (`mem_Mtilde_imp_form`) with
`x ∈ M_σ#` and `x' ∈ R(x)`, so `ℓ_σ(g) ≤ 2`.  In the multi-maximal case `R(x) = N_σ ∩ C_G(x)` for
the neighbour `N` (`exists_neighbor_eq_Rsub`), where `sigmaLength_cover_le_two_signalizer` applies;
in the trivial case `R(x) = 1`, so `g = x` with `ℓ_σ(x) = 1`. -/
theorem sigmaLength_le_two_of_mem_Mtilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G}
    (hg : g ∈ Mtilde hG (genuineSigmaDecomposition hG) M) :
    sigmaLength g ≤ 2 := by
  obtain ⟨x, x', rfl, hlen, hx'⟩ :=
    mem_Mtilde_imp_form hG (genuineSigmaDecomposition hG) hM hg
  have hx1 : x ≠ 1 := (((genuineSigmaDecomposition hG).length_one_iff x).mp hlen).1
  by_cases hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard
  · obtain ⟨M0, hM0⟩ := (((genuineSigmaDecomposition hG).length_one_iff x).mp hlen).2
    obtain ⟨N, hNmax, _, hReq, hxτ2, _⟩ :=
      exists_neighbor_eq_Rsub hG (genuineSigmaDecomposition hG) hlen hgt
    rw [hReq] at hx'
    have hx'N : x' ∈ OddOrder.BG.Ch3.S10.Msigma N := (Subgroup.mem_inf.mp hx').1
    have hcomm : Commute x x' := by
      have h := (Subgroup.mem_inf.mp hx').2
      rw [Subgroup.mem_centralizer_iff] at h
      exact h x (Set.mem_singleton_iff.mpr rfl)
    exact sigmaLength_cover_le_two_signalizer hG hM0.1 hNmax hM0.2 hx1 hxτ2 hx'N hcomm
  · have hRbot : Rsub hG (genuineSigmaDecomposition hG) x = ⊥ := by
      unfold Rsub
      exact dif_neg (fun h => hgt h.2.2)
    rw [hRbot, Subgroup.mem_bot] at hx'
    rw [hx', mul_one]
    have hsl1 : sigmaLength x = 1 := hlen
    omega

/-- **BG 14.7, elements of `T` have the `not_type1_of_type2` "type-1 form"** (mmd L4021): for
`t ∈ T = Z − ⋃ Kᵢ*`, there is a family member `N` and `t = y·y'` with `y ∈ M_σ(N)^#`, `y'` a
nonidentity `κ(N)`-element of `N` centralising `y`.  Extracted exactly as in the TI-of-`T` proof:
the splitting member `N` (`typeP_family_exists_sigmaPart`), `π`-decompose `t = y·y'`
(`exists_isPiElement_mul`), `y ∈ Kᵢ* ≤ M_σ(N)` (`…isPiElement_mem_Kstar`) and `y' ∈ K_N` (a Hall
`κ(N)`-subgroup, `isPiElementCompl_mem_left_of_commute`), both nontrivial.  Feeds Lemma 14.6
(`not_type1_of_type2`) for the `𝒞_G(T) ⊥ 𝒞_G(M̃ᵢ)` disjointness. -/
theorem typeP_family_T_form [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {t : G} (htT : t ∈ ((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G)) :
    ∃ N : Subgroup G, N ∈ maximalSubgroups G ∧ ∃ y y' : G, t = y * y' ∧ Commute y y' ∧
      y ∈ sigmaSharp N ∧ y' ≠ 1 ∧ y' ∈ N ∧ y' ∈ Subgroup.centralizer ({y} : Set G) ∧
      ∀ p ∈ piSet (Subgroup.closure ({y'} : Set G)), p ∈ kappa N := by
  classical
  obtain ⟨htZ, htnot⟩ := htT
  have ht1 : t ≠ 1 := fun h => htnot
    (Set.mem_biUnion (mem_ZFamilyFinset.mpr (Or.inl rfl)) (h ▸ one_mem _))
  obtain ⟨N, hN, hσpart⟩ := typeP_family_exists_sigmaPart hG hM hP hKM hK hKstar hU htZ ht1
  obtain ⟨y, y', hyy', hcomm, hyπ, hy'π, hyz, hy'z⟩ :=
    exists_isPiElement_mul (OddOrder.BG.Ch3.S10.sigma N) t
  have hyZ : y ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ) hyz
  have hy'Z : y' ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ) hy'z
  obtain ⟨KN, hKNN, hKN, hswap, hcent, hAπc, -, -⟩ :=
    typeP_family_member_dData hG hM hP hKM hK hKstar hU hN
  have hBπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma N)
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
      ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
  have hyKstar : y ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    typeP_family_isPiElement_mem_Kstar hG hM hP hKM hK hKstar hU hN hyZ hyπ
  have hy'KN : y' ∈ KN := isPiElementCompl_mem_left_of_commute hswap hcent hAπc hBπ hy'Z hy'π
  have hy1 : y ≠ 1 := fun h =>
    hσpart (by rw [show t = y' from by rw [← hyy', h, one_mul]]; exact hy'π)
  have hy'1 : y' ≠ 1 := fun h => htnot (Set.mem_biUnion (mem_ZFamilyFinset.mpr hN)
    (show t ∈ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) from by
      rw [show t = y from by rw [← hyy', h, mul_one]]; exact hyKstar))
  obtain ⟨hNmax, -, -, -⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  refine ⟨N, hNmax, y, y', hyy'.symm, hcomm, ?_, hy'1, hKNN hy'KN, ?_, ?_⟩
  · rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
    exact ⟨(inf_le_right :
      (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≤ _) hyKstar, hy1⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw; rw [Set.mem_singleton_iff] at hw; subst hw; exact hcomm
  · intro p hp
    simp only [piSet, Set.mem_setOf_eq] at hp
    obtain ⟨hpp, hpdc, -⟩ := Nat.mem_primeFactors.mp hp
    have hpKN : p ∣ Nat.card ↥KN := hpdc.trans (Subgroup.card_dvd_of_le
      (by rw [← Subgroup.zpowers_eq_closure]; exact Subgroup.zpowers_le.mpr hy'KN))
    apply hKN.1 p
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKNN).toEquiv]
    exact Nat.mem_primeFactors.mpr ⟨hpp, hpKN, Nat.card_pos.ne'⟩

/-- **BG 14.7, `𝒞_G(T)` is disjoint from each `𝒞_G(M̃ᵢ)`** (mmd L4025): the TI-set's conjugacy
saturation meets no `𝒞_G(M̃ᵢ)`.  A common `z = g₁tg₁⁻¹ = g₂sg₂⁻¹` (`t ∈ T`, `s ∈ M̃ᵢ`) makes
`t = (g₁⁻¹g₂)·s·(g₁⁻¹g₂)⁻¹` a conjugate of `s ∈ M̃ᵢ`, so `t ∈ M̃(Mᵢ^{g₁⁻¹g₂})` (`Mtilde_conj_smul`)
has the type-2 form (`mem_Mtilde_imp_form`); but `t ∈ T` has the type-1 form
(`typeP_family_T_form`), contradicting Lemma 14.6 (`not_type1_of_type2`).  The last disjointness
needed for the density inequality. -/
theorem conjClassSet_T_Mtilde_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {Mi : Subgroup G} (hMi : Mi ∈ maximalSubgroups G) :
    Disjoint (conjClassSet (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G)))
      (conjClassSet (Mtilde hG D Mi)) := by
  rw [Set.disjoint_left]
  rintro z ⟨t, htT, g₁, rfl⟩ ⟨s, hsM, g₂, hz₂⟩
  obtain ⟨N, hNmax, y, y', hgyy', hcomm, hy, hy'1, hy'N, hy'C, hy'κ⟩ :=
    typeP_family_T_form hG hM hP hKM hK hKstar hU htT
  have heq : t = MulAut.conj (g₁⁻¹ * g₂) • s := by
    rw [MulAut.smul_def, MulAut.conj_apply,
      show (g₁⁻¹ * g₂) * s * (g₁⁻¹ * g₂)⁻¹ = g₁⁻¹ * (g₂ * s * g₂⁻¹) * g₁ from by group, hz₂]
    group
  have htM : t ∈ Mtilde hG D (MulAut.conj (g₁⁻¹ * g₂) • Mi) := by
    rw [← Mtilde_conj_smul, heq]; exact Set.smul_mem_smul_set hsM
  obtain ⟨x, x'', htxx, hlenx, hx''R⟩ := mem_Mtilde_imp_form hG D
    (mem_maximalSubgroups_of_isConjugateSubgroup hMi ⟨g₁⁻¹ * g₂, rfl⟩) htM
  exact not_type1_of_type2 hG D hNmax hy hgyy' hcomm hy'1 hy'N hy'C hy'κ ⟨x, x'', htxx, hlenx, hx''R⟩

/-- **BG 14.7, type-`P₁` Hall complement card** (mmd L4039, "`Kᵢ` complements `M_{iσ}` in `M_i`"):
for a type-`P₁` maximal subgroup `N` with a Hall `κ(N)`-subgroup `K_N ≤ N`, the order factors as
`|N| = |N_σ|·|K_N|`.  For type `P₁`, `κ(N) = π(N) − σ(N)`, so `K_N` is a Hall `σ(N)′`-subgroup
complementing the normal Hall `σ(N)`-subgroup `N_σ` (`Msigma_isHall`).  The proof is the σ-part
uniqueness: with `m = |N_σ|`, `j = [N : N_σ]`, `a = |K_N|`, `j' = [N : K_N]`, one has
`m·j = |N| = a·j'` with `m`, `j'` being `σ`-numbers and `a`, `j` being `σ′`-numbers, so `a = j`.
This is the `[N : N_σ] = kᵢ` identity the density inequality of Theorem 14.7(e) uses to rewrite
`(|N_σ| − 1)·[G : N]` as `(1/kᵢ − 1/|N|)·|G|`. -/
theorem typeP1_card_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {N KN : Subgroup G} (hNmax : N ∈ maximalSubgroups G) (hP1 : IsTypeP1 N)
    (hKN : KN ≤ N) (hKN_hall : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N)) :
    Nat.card ↥N = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * Nat.card ↥KN := by
  classical
  have hMσle : OddOrder.BG.Ch3.S10.Msigma N ≤ N := OddOrder.BG.Ch3.S10.Msigma_le N
  have hMσHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hNmax
  -- card transfers between `subgroupOf N` and the ambient subgroup
  have hcardNσ : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
      = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσle).toEquiv
  have hcardKN : Nat.card ↥(KN.subgroupOf N) = Nat.card ↥KN :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
  -- Lagrange inside `↥N`
  have hlagNσ : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N)
      * ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).index = Nat.card ↥N := by
    rw [← hcardNσ]; exact Subgroup.card_mul_index _
  have hlagKN : Nat.card ↥KN * (KN.subgroupOf N).index = Nat.card ↥N := by
    rw [← hcardKN]; exact Subgroup.card_mul_index _
  set m := Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) with hm
  set j := ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).index with hjdef
  set a := Nat.card ↥KN with ha
  set j' := (KN.subgroupOf N).index with hj'def
  -- `m`'s primes lie in `σ(N)` (`N_σ` is a Hall `σ`-subgroup)
  have hm_sigma : ∀ p, p ∈ m.primeFactors → p ∈ OddOrder.BG.Ch3.S10.sigma N := hMσHall.1
  -- `a`'s primes avoid `σ(N)` (`κ(N) ⊆ σ(N)′`)
  have ha_sigma : ∀ p, p ∈ a.primeFactors → p ∉ OddOrder.BG.Ch3.S10.sigma N := fun p hp =>
    kappa_subset_sigmaCompl (hKN_hall.1 p (by rw [hcardKN]; exact hp))
  -- `j`'s primes avoid `σ(N)` (`j ∣ (N_σ).index`, a Hall index)
  have hj_div : j ∣ (OddOrder.BG.Ch3.S10.Msigma N).index :=
    Subgroup.relIndex_dvd_index_of_le hMσle
  have hj_sigma : ∀ p, p ∈ j.primeFactors → p ∉ OddOrder.BG.Ch3.S10.sigma N := fun p hp =>
    hMσHall.2 p (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,
      (Nat.dvd_of_mem_primeFactors hp).trans hj_div, Subgroup.index_ne_zero_of_finite⟩)
  -- `j'`'s primes lie in `σ(N)` (type `P₁`: `κ(N) = π(N) − σ(N)`)
  have hj'_dvd_N : j' ∣ Nat.card ↥N := Subgroup.index_dvd_card _
  have hj'_sigma : ∀ p, p ∈ j'.primeFactors → p ∈ OddOrder.BG.Ch3.S10.sigma N := by
    intro p hp
    have hpprime := (Nat.mem_primeFactors.mp hp).1
    have hp_dvd_N : p ∣ Nat.card ↥N := (Nat.dvd_of_mem_primeFactors hp).trans hj'_dvd_N
    have hp_notκ : p ∉ kappa N := hKN_hall.2 p hp
    rw [hP1.2] at hp_notκ
    by_contra hpσ
    exact hp_notκ ⟨Nat.mem_primeFactors.mpr ⟨hpprime, hp_dvd_N, Nat.card_pos.ne'⟩, hpσ⟩
  -- coprimalities and the `a = j` matching
  have hcop_am : Nat.Coprime a m := Nat.coprime_of_dvd fun p hp hpa hpm =>
    ha_sigma p (Nat.mem_primeFactors.mpr ⟨hp, hpa, Nat.card_pos.ne'⟩)
      (hm_sigma p (Nat.mem_primeFactors.mpr ⟨hp, hpm, Nat.card_pos.ne'⟩))
  have hcop_jj' : Nat.Coprime j j' := Nat.coprime_of_dvd fun p hp hpj hpj' =>
    hj_sigma p (Nat.mem_primeFactors.mpr ⟨hp, hpj, Subgroup.index_ne_zero_of_finite⟩)
      (hj'_sigma p (Nat.mem_primeFactors.mpr ⟨hp, hpj', Subgroup.index_ne_zero_of_finite⟩))
  have ha_dvd_j : a ∣ j := hcop_am.dvd_of_dvd_mul_left (by rw [hlagNσ]; exact ⟨j', hlagKN.symm⟩)
  have hj_dvd_a : j ∣ a := hcop_jj'.dvd_of_dvd_mul_right (by rw [hlagKN]; exact ⟨m, by
    rw [← hlagNσ]; ring⟩)
  have hja : j = a := Nat.dvd_antisymm hj_dvd_a ha_dvd_j
  rw [← hlagNσ, hja]

/-- **BG 14.7, `1 ∉ M̃`** (mmd L3920): the identity is never a "twisted" product `x·x'`
(`x ∈ M_σ^#`, `x' ∈ R(x)`).  If `x·x' = 1` then `x' = x⁻¹`, which has the same order as the
`σ(N)`-element `x`, so `x'` is a `σ(N)`-element; but `x' ∈ R(x)` is a `σ(N)′`-element
(`isPiElement_sigmaCompl_of_mem_Rsub`), and a nonidentity element cannot be both.  Hence each
`𝒞_G(M̃)` avoids `1` and lies in `G^#`, which the density inequality of Theorem 14.7(e) needs. -/
theorem one_not_mem_Mtilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {N : Subgroup G} (hN : N ∈ maximalSubgroups G) :
    (1 : G) ∉ Mtilde hG D N := by
  rintro ⟨x, hxsharp, x', hx'R, hxx'⟩
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hxsharp
  obtain ⟨hxN, hx1⟩ := hxsharp
  have hx'eq : x' = x⁻¹ := (mul_eq_one_iff_inv_eq.mp hxx'.symm).symm
  have hlen : D.length x = 1 := (D.length_one_iff x).mpr ⟨hx1, ⟨N, hN, hxN⟩⟩
  have hπ : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma N)ᶜ x' :=
    isPiElement_sigmaCompl_of_mem_Rsub hG D hlen ⟨hN, hxN⟩ hx'R
  have hx'1 : x' ≠ 1 := by rw [hx'eq]; exact inv_ne_one.mpr hx1
  have hord : orderOf x' ≠ 1 := fun h => hx'1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord
  have hordeq : orderOf x' = orderOf x := by rw [hx'eq, orderOf_inv]
  refine hπ p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, (orderOf_pos x').ne'⟩)
    (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr ⟨hp,
      (hordeq ▸ hpdvd).trans ((OddOrder.BG.Ch3.S10.Msigma N).orderOf_dvd_natCard hxN),
      Nat.card_pos.ne'⟩))

/-- **BG Corollary 14.9, the `G#` cover under all-type-`F`** (the covering equality of the
`(8.8.a)` type-I case): when every maximal subgroup is of type `F`, the nonidentity elements of
`G` are exactly the union of the faithful covers `𝒞_G(M̃)` over the maximal subgroups.  The `⊆`
direction is `exists_mem_conjClassSet_Mtilde_of_ne_one` (the discharged form of BG Lemma 14.6),
and `⊇` is `one_not_mem_Mtilde` (`1 ∉ M̃`, so `1 ∉ 𝒞_G(M̃)`).  This is the `cover_nonidentity`
field of `BGTheoremETypeICovering`, modulo replacing the union over all maximals by the union over
conjugacy representatives (`conjClassSet (Mtilde …)` depends only on the conjugacy class via
`Mtilde_conj_smul`). -/
theorem sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hall : ∀ M ∈ maximalSubgroups G, IsTypeF M) :
    sharpSubgroup (⊤ : Subgroup G)
      = ⋃ M ∈ maximalSubgroups G,
          conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) M) := by
  set D := genuineSigmaDecomposition hG with hD
  ext g
  simp only [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_top, true_and, Set.mem_iUnion₂]
  constructor
  · intro hg1
    obtain ⟨M, hM, hgM⟩ := exists_mem_conjClassSet_Mtilde_of_ne_one hG hall hg1
    exact ⟨M, hM, hgM⟩
  · rintro ⟨M, hM, t, ht, c, hc⟩ rfl
    exact one_not_mem_Mtilde hG D hM ((mul_eq_left.mp (mul_inv_eq_one.mp hc)) ▸ ht)

/-- **BG 14.7, the per-member `σ`-Hall identity** (mmd L4039): for a type-`P₁` member `N` of the
type-`P` family, `|N_σ|·[G : N] = [G : Z]·kᵢ*` where `kᵢ* = |Z ⊓ N_σ|` is the canonical family
factor.  This is the cancellation crux of the density inequality: it turns each
`|𝒞_G(M̃ᵢ)| = (|N_σ| − 1)·[G : N]` summand into `[G : Z]·kᵢ* − [G : N]`, so the `[G : Z]·kᵢ*`
parts cancel against the `𝒞_G(T)` count.  Proof: multiply by `kᵢ = |K_N|` and use
`|N| = |N_σ|·kᵢ` (type `P₁`, `typeP1_card_eq`), `z = kᵢ·kᵢ*` (the swap,
`card_kappaHall_sup_Kstar`), and Lagrange `|N|·[G:N] = |G| = z·[G:Z]`. -/
theorem typeP1_member_Msigma_index_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) (hP1 : IsTypeP1 N) :
    Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * N.index
      = (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
  classical
  obtain ⟨hNmax, hPN, hZN, KN, hKNN, hKN_hall, hswap, hcanon, hne⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  have hz : Nat.card ↥(K ⊔ Kstar)
      = Nat.card ↥KN * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    have h1 := card_kappaHall_sup_Kstar (M := N) (K := KN)
      (Kstar := OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G))
      hKNN hKN_hall rfl
    rw [← hswap, hcanon] at h1
    exact h1
  have hN_card : Nat.card ↥N
      = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * Nat.card ↥KN :=
    typeP1_card_eq hG hNmax hP1 hKNN hKN_hall
  have hlagN : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
  have hlagZ : Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index = Nat.card G :=
    Subgroup.card_mul_index _
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥KN)) ?_
  calc Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * N.index * Nat.card ↥KN
      = (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * Nat.card ↥KN) * N.index := by ring
    _ = Nat.card ↥N * N.index := by rw [← hN_card]
    _ = Nat.card G := hlagN
    _ = Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index := hlagZ.symm
    _ = (Nat.card ↥KN * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N))
          * (K ⊔ Kstar).index := by rw [hz]
    _ = (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N)
          * Nat.card ↥KN := by ring

/-- **BG 14.7, the per-member index bound** (mmd L4033): each family member `N` has
`2·[G : N] ≤ [G : Z]`, the upper bound on `[G : N]` the density inequality needs (from
`|N| ≥ 2z`, `typeP_family_two_mul_card_le`).  Cancelling `z` from `2z·[G:N] ≤ |N|·[G:N] =
|G| = z·[G:Z]`. -/
theorem typeP_member_two_mul_index_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    2 * N.index ≤ (K ⊔ Kstar).index := by
  have h2z : 2 * Nat.card ↥(K ⊔ Kstar) ≤ Nat.card ↥N :=
    typeP_family_two_mul_card_le hG hM hP hKM hK hKstar hU hN
  have hlagN : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
  have hlagZ : Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index = Nat.card G :=
    Subgroup.card_mul_index _
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.card_pos (α := ↥(K ⊔ Kstar)))
  calc Nat.card ↥(K ⊔ Kstar) * (2 * N.index)
      = (2 * Nat.card ↥(K ⊔ Kstar)) * N.index := by ring
    _ ≤ Nat.card ↥N * N.index := by gcongr
    _ = Nat.card G := hlagN
    _ = Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index := hlagZ.symm

/-- **BG 14.7, the family has `≥ 2` members** (mmd L3993, "`n ≥ 1`"): the type-`P` family
`{M} ∪ {neighbours}` has at least two members — `M` itself and a neighbour `N ∈ 𝓜(N_G(X))` for a
line `X ∈ ℰ_p¹(K)` (`p ∣ |K|`), which is nonconjugate to `M` (`exists_typeP_partner`).  This is
the `n ≥ 1` the density inequality needs for `(n − 1)/2z ≥ 0`. -/
theorem ZFamilyFinset_one_lt_card [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    1 < (ZFamilyFinset M K).card := by
  classical
  have hPe := hP
  obtain ⟨p, hpκ⟩ := hPe
  have hpprime := hpκ.1
  obtain ⟨P, hPelem, hPM, -⟩ := hpκ.2.2
  have hpcardP : Nat.card ↥P = p := by obtain ⟨_, hc⟩ := hPelem; rwa [pow_one] at hc
  have hpK : p ∣ Nat.card ↥K := by
    have hlag : Nat.card ↥K * (K.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact Subgroup.card_mul_index (K.subgroupOf M)
    have hpM : p ∣ Nat.card ↥M := hpcardP ▸ Subgroup.card_dvd_of_le hPM
    have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hd =>
      hK.2 p (Nat.mem_primeFactors.mpr ⟨hpprime, hd, Subgroup.index_ne_zero_of_finite⟩) hpκ
    exact (hpprime.dvd_mul.mp (hlag.symm ▸ hpM)).resolve_right hpidx
  haveI : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxord : orderOf (x : G) = p := (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
  have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
  obtain ⟨N, hNmem, hnc, -, -, -, -⟩ :=
    exists_typeP_partner hG hM hP hKM hK hKstar hU hXelem hXK
  have hNfam : IsZFamilyMember M K N :=
    Or.inr ⟨p, Subgroup.zpowers (x : G), hpprime, hXelem, hXK, hNmem⟩
  have hMN : M ≠ N := fun h => hnc (h ▸ IsConjugateSubgroup.refl M)
  exact Finset.one_lt_card.mpr ⟨M, mem_ZFamilyFinset.mpr (Or.inl rfl), N,
    mem_ZFamilyFinset.mpr hNfam, hMN⟩

/-- The identity is conjugacy-closed: if `1 ∉ A` then `1 ∉ 𝒞_G(A)` (a conjugate `g·t·g⁻¹ = 1`
forces `t = 1`).  Used to place each density piece `𝒞_G(T)`, `𝒞_G(M̃ᵢ)` inside `G^#`. -/
theorem one_not_mem_conjClassSet {A : Set G} (h : (1 : G) ∉ A) :
    (1 : G) ∉ conjClassSet A := by
  rintro ⟨t, ht, g, hg⟩
  rw [(MulAut.conj_apply g t).symm, ← map_one (MulAut.conj g)] at hg
  exact h ((MulAut.conj g).injective hg ▸ ht)

/-- **BG 14.7, the density pieces fit in `G^#`** (mmd L4035): the conjugacy saturations `𝒞_G(T)`
and `{𝒞_G(M̃ᵢ)}_{i}` over the type-`P` family are pairwise disjoint subsets of `G^# = G − {1}`, so
their cardinalities sum to at most `|G| − 1`.  Disjointness: `𝒞_G(T) ⊥ 𝒞_G(M̃ᵢ)`
(`conjClassSet_T_Mtilde_disjoint`, Lemma 14.6) and `𝒞_G(M̃ᵢ) ⊥ 𝒞_G(M̃ⱼ)`
(`conjClassSet_Mtilde_disjoint`, Lemma 14.5(b), via pairwise nonconjugacy of the family).
Membership in `G^#`: `1 ∉ T` (`1 ∈ Kᵢ*`) and `1 ∉ M̃ᵢ` (`one_not_mem_Mtilde`).  This is the
upper bound `∑ |𝒞_G(·)| ≤ |G^#|` of the density inequality of Theorem 14.7(e). -/
theorem density_pieces_ncard_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (conjClassSet (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))).ncard
      + (∑ N ∈ ZFamilyFinset M K, (conjClassSet (Mtilde hG D N)).ncard)
      ≤ Nat.card G - 1 := by
  classical
  set Tset := ((K ⊔ Kstar : Subgroup G) : Set G) \
      ⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) with hTset
  set A := conjClassSet Tset with hA
  set U := ⋃ N ∈ (↑(ZFamilyFinset M K) : Set (Subgroup G)), conjClassSet (Mtilde hG D N) with hU'
  -- `U.ncard = ∑ |𝒞_G(M̃ᵢ)|`
  have hpair : (↑(ZFamilyFinset M K) : Set (Subgroup G)).PairwiseDisjoint
      (fun N => conjClassSet (Mtilde hG D N)) := by
    intro N₁ hN₁ N₂ hN₂ hne
    refine conjClassSet_Mtilde_disjoint hG D
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN₁)).1
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN₂)).1 ?_
    exact typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU
      (mem_ZFamilyFinset.mp hN₁) (mem_ZFamilyFinset.mp hN₂) hne
  have hUcard : U.ncard = ∑ N ∈ ZFamilyFinset M K, (conjClassSet (Mtilde hG D N)).ncard := by
    rw [hU', Set.Finite.ncard_biUnion (ZFamilyFinset M K).finite_toSet
      (fun N _ => Set.toFinite _) hpair, finsum_mem_coe_finset]
  -- all pieces avoid `1`
  have h1T : (1 : G) ∉ Tset := fun h =>
    (Set.mem_sdiff _ |>.mp h).2 (Set.mem_iUnion₂.mpr ⟨M, mem_ZFamilyFinset.mpr (Or.inl rfl),
      SetLike.mem_coe.mpr (Subgroup.one_mem _)⟩)
  have h1A : (1 : G) ∉ A := one_not_mem_conjClassSet h1T
  have h1U : (1 : G) ∉ U := by
    rw [hU', Set.mem_iUnion₂]; rintro ⟨N, hN, hzN⟩
    exact one_not_mem_conjClassSet (one_not_mem_Mtilde hG D
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN)).1) hzN
  -- `A` disjoint from `U`
  have hAU : Disjoint A U := by
    rw [Set.disjoint_left]
    rintro z hzA hzU
    rw [hU', Set.mem_iUnion₂] at hzU
    obtain ⟨N, hN, hzN⟩ := hzU
    exact Set.disjoint_left.mp (conjClassSet_T_Mtilde_disjoint hG D hM hP hKM hK hKstar hU
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN)).1) hzA hzN
  -- `A ∪ U ⊆ G^#`
  have hsub : A ∪ U ⊆ {g : G | g ≠ 1} := by
    rintro z (hz | hz)
    · exact fun h => h1A (h ▸ hz)
    · exact fun h => h1U (h ▸ hz)
  have hWcard : ({g : G | g ≠ 1} : Set G).ncard = Nat.card G - 1 := by
    have hWeq : {g : G | g ≠ 1} = (Set.univ : Set G) \ {1} := by
      ext g; simp [Set.mem_sdiff]
    rw [hWeq, Set.ncard_sdiff (Set.singleton_subset_iff.mpr (Set.mem_univ 1)), Set.ncard_univ,
      Set.ncard_singleton]
  calc A.ncard + ∑ N ∈ ZFamilyFinset M K, (conjClassSet (Mtilde hG D N)).ncard
      = A.ncard + U.ncard := by rw [hUcard]
    _ = (A ∪ U).ncard := (Set.ncard_union_eq hAU).symm
    _ ≤ ({g : G | g ≠ 1} : Set G).ncard := Set.ncard_le_ncard hsub
    _ = Nat.card G - 1 := hWcard

/-- **BG Theorem 14.7, the density inequality** (mmd L4031-4045): some member of the type-`P`
family `{M} ∪ {neighbours}` has type `P₂`.  If every member were type `P₁`, the disjoint conjugacy
pieces `𝒞_G(T)` and `{𝒞_G(M̃ᵢ)}` would already cover `G^#`:
`|G^#| ≥ |𝒞_G(T)| + ∑ |𝒞_G(M̃ᵢ)| = |G| + n·[G:Z] − ∑ [G:Mᵢ] ≥ |G| + (n−1)·[G:Z]/… ≥ |G|`,
contradicting `|G^#| = |G| − 1`.  The `∑ [G:Z]·kᵢ*` parts cancel between the two counts
(`typeP1_member_Msigma_index_eq`); the bound uses `[G:Mᵢ] ≤ [G:Z]/2` (`|Mᵢ| ≥ 2z`) and `n ≥ 1`
(a neighbour exists).  Entirely a `ℕ` computation closed by `omega`. -/
theorem exists_typeP2_member [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∃ N ∈ ZFamilyFinset M K, IsTypeP2 N := by
  classical
  by_contra hcon
  push Not at hcon
  have hallP1 : ∀ N ∈ ZFamilyFinset M K, IsTypeP1 N := fun N hN =>
    (isTypeP_iff_isTypeP1_or_isTypeP2.mp
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN)).2.1).resolve_right
      (hcon N hN)
  -- lemma instances (explicit `T`), then fold `T`
  have hT_count := typeP_family_conjClass_T_count hG hM hP hKM hK hKstar hU
  have hT_card := typeP_family_T_count hG hM hP hKM hK hKstar hU
  have hbound := density_pieces_ncard_le hG D hM hP hKM hK hKstar hU
  have hcardlt := ZFamilyFinset_one_lt_card hG hM hP hKM hK hKstar hU
  set Tset := ((K ⊔ Kstar : Subgroup G) : Set G) \
      ⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) with hTset
  have hzcard : Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index = Nat.card G :=
    Subgroup.card_mul_index _
  -- per-member `M̃` additive identity and its sum
  have hmem_add : ∀ N ∈ ZFamilyFinset M K,
      (conjClassSet (Mtilde hG D N)).ncard + N.index
        = (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    intro N hN
    have hNmax := (typeP_family_member_data hG hM hP hKM hK hKstar hU
      (mem_ZFamilyFinset.mp hN)).1
    have hmem_id := typeP1_member_Msigma_index_eq hG hM hP hKM hK hKstar hU
      (mem_ZFamilyFinset.mp hN) (hallP1 N hN)
    rw [sigmaConjugacySaturation_Mtilde_ncard hG D hNmax, Nat.sub_one_mul]
    have hge : N.index ≤ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * N.index :=
      Nat.le_mul_of_pos_left _ Nat.card_pos
    omega
  have hMtilde_sum : (∑ N ∈ ZFamilyFinset M K, (conjClassSet (Mtilde hG D N)).ncard)
      + (∑ N ∈ ZFamilyFinset M K, N.index)
      = ∑ N ∈ ZFamilyFinset M K,
          (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl hmem_add
  -- `T` additive (multiply the `|T|` count by `[G:Z]`)
  have hmul : Tset.ncard * (K ⊔ Kstar).index
      + (∑ N ∈ ZFamilyFinset M K,
          Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) * (K ⊔ Kstar).index)
      + (K ⊔ Kstar).index
      = Nat.card G + (ZFamilyFinset M K).card * (K ⊔ Kstar).index := by
    have h := congrArg (· * (K ⊔ Kstar).index) hT_card
    simp only [add_mul, one_mul, Finset.sum_mul] at h
    rw [hzcard] at h
    exact h
  have hPcomm : (∑ N ∈ ZFamilyFinset M K,
        (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N))
      = ∑ N ∈ ZFamilyFinset M K,
        Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) * (K ⊔ Kstar).index :=
    Finset.sum_congr rfl (fun N _ => mul_comm _ _)
  -- key inequality `∑ [G:Mᵢ] ≤ (𝓕.card − 1)·[G:Z]`
  have hkey : (∑ N ∈ ZFamilyFinset M K, N.index)
      ≤ ((ZFamilyFinset M K).card - 1) * (K ⊔ Kstar).index := by
    have h2sum : 2 * (∑ N ∈ ZFamilyFinset M K, N.index)
        ≤ (ZFamilyFinset M K).card * (K ⊔ Kstar).index := by
      rw [Finset.mul_sum]
      calc (∑ N ∈ ZFamilyFinset M K, 2 * N.index)
          ≤ ∑ _N ∈ ZFamilyFinset M K, (K ⊔ Kstar).index :=
            Finset.sum_le_sum (fun N hN => typeP_member_two_mul_index_le hG hM hP hKM hK hKstar hU
              (mem_ZFamilyFinset.mp hN))
        _ = (ZFamilyFinset M K).card * (K ⊔ Kstar).index := by
            rw [Finset.sum_const, smul_eq_mul]
    have hc2 : (ZFamilyFinset M K).card ≤ 2 * ((ZFamilyFinset M K).card - 1) := by omega
    have hstep : (ZFamilyFinset M K).card * (K ⊔ Kstar).index
        ≤ 2 * (((ZFamilyFinset M K).card - 1) * (K ⊔ Kstar).index) := by
      rw [← mul_assoc]; exact mul_le_mul_right' hc2 _
    omega
  -- expansion fact relating `𝓕.card·[G:Z]` and `(𝓕.card−1)·[G:Z]`
  have hexp : (ZFamilyFinset M K).card * (K ⊔ Kstar).index
      = ((ZFamilyFinset M K).card - 1) * (K ⊔ Kstar).index + (K ⊔ Kstar).index := by
    have hle : (K ⊔ Kstar).index ≤ (ZFamilyFinset M K).card * (K ⊔ Kstar).index :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [Nat.sub_one_mul]; omega
  have hgpos : 1 ≤ Nat.card G := Nat.card_pos
  omega

/-- **A `πᶜ`-subgroup of an internal direct product `Z = A × B` (`A` a `πᶜ`-group, `B` a
`π`-group) lies in the left factor `A`.**  Subgroup generalisation of
`isPiElementCompl_mem_left_of_commute`: `A.subgroupOf Z` is the normal Hall `πᶜ`-subgroup of `Z`,
so any `πᶜ`-subgroup `L ≤ Z` lies in it (`isPiGroup_le_of_normal_isHallSubgroup`).  In the `n = 1`
collapse of Theorem 14.7, `A = Kᵢ` (the Hall `κ(Mᵢ) ⊆ σ(Mᵢ)′`-subgroup), `B = Kᵢ*` (the
`σ(Mᵢ)`-part), and `L = Kⱼ*` (a `σ(Mᵢ)′`-group since `σ(Mⱼ) ∩ σ(Mᵢ) = ∅`), forcing `Kⱼ* ≤ Kᵢ`. -/
theorem isPiSubgroup_le_left_of_commute [Finite G] {A B Z L : Subgroup G} {π : Set ℕ}
    (hswap : Z = A ⊔ B) (hcent : B ≤ Subgroup.centralizer (A : Set G))
    (hAπc : Subgroup.IsPiSubgroup πᶜ A) (hBπ : Subgroup.IsPiSubgroup π B)
    (hLZ : L ≤ Z) (hLπc : Subgroup.IsPiSubgroup πᶜ L) : L ≤ A := by
  classical
  have hAZ : A ≤ Z := by rw [hswap]; exact le_sup_left
  have hcomm : ∀ a ∈ A, ∀ c ∈ B, Commute a c := fun a ha c hc =>
    Subgroup.mem_centralizer_iff.mp (hcent hc) a ha
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥B) := by
    apply Nat.coprime_of_dvd
    intro p hp hpA hpB
    exact (hAπc p (Nat.mem_primeFactors.mpr ⟨hp, hpA, Nat.card_pos.ne'⟩))
      (hBπ p (Nat.mem_primeFactors.mpr ⟨hp, hpB, Nat.card_pos.ne'⟩))
  have hdisj : A ⊓ B = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hnorm : Z ≤ Subgroup.normalizer (A : Set G) := by
    rw [hswap]; exact (sup_le_normalizer_inf_of_commute hcent).trans inf_le_left
  haveI hAnZ : (A.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAZ).mpr hnorm
  have hZcard : Nat.card ↥Z = Nat.card ↥A * Nat.card ↥B := by
    rw [hswap]; exact card_sup_of_commute_of_disjoint hcomm hdisj
  have hcardSub : Nat.card ↥(A.subgroupOf Z) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv
  have hidx : (A.subgroupOf Z).index = Nat.card ↥B := by
    have hl := Subgroup.card_mul_index (A.subgroupOf Z)
    rw [hcardSub, hZcard] at hl
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hl
  have hHall : Ch03.IsHallSubgroup πᶜ (A.subgroupOf Z) := by
    refine ⟨fun p hp => ?_, fun p hp hpc => ?_⟩
    · rw [hcardSub] at hp; exact hAπc p hp
    · exact hpc (hBπ p (by rwa [hidx] at hp))
  have hLsub : L.subgroupOf Z ≤ A.subgroupOf Z := by
    refine OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hHall (fun p hp => ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLZ).toEquiv] at hp
    exact hLπc p hp
  intro x hx
  have hmem : (⟨x, hLZ hx⟩ : ↥Z) ∈ L.subgroupOf Z := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hLsub hmem)

/-- **BG Theorem 14.7, the `n = 1` collapse** (mmd L4047): the type-`P` family `{M} ∪ {neighbours}`
has exactly two members.  By the density inequality some member `Mᵢ` is type `P₂`, so its Hall
`κ(Mᵢ)`-subgroup `Kᵢ` has prime order `q` (Proposition 14.2(g)).  In the swap `Z = Kᵢ × Kᵢ*`, `Kᵢ`
is the normal Hall `σ(Mᵢ)′`-subgroup; every other member `Mⱼ` has `Kⱼ* = Z ⊓ M_{jσ}` a nontrivial
`σ(Mᵢ)′`-subgroup of `Z` (`σ(Mⱼ) ∩ σ(Mᵢ) = ∅` by Theorem 13.9), hence `Kⱼ* ≤ Kᵢ`
(`isPiSubgroup_le_left_of_commute`), and `Kⱼ* = Kᵢ` since `|Kᵢ| = q` is prime.  But the `Kⱼ*` are
pairwise disjoint (`typeP_family_Kstar_disjoint`), so two distinct neighbours would give
`Kᵢ = Kⱼ* ⊓ Kₗ* = 1`, contradicting `q ≥ 2`.  Thus at most one neighbour, i.e. `|family| = 2`. -/
theorem family_card_eq_two [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (ZFamilyFinset M K).card = 2 := by
  classical
  refine le_antisymm ?_ (ZFamilyFinset_one_lt_card hG hM hP hKM hK hKstar hU)
  obtain ⟨Mi, hMi𝓕, hMiP2⟩ := exists_typeP2_member hG D hM hP hKM hK hKstar hU
  obtain ⟨hMimax, hMiP, hZMi, KNi, hKNiMi, hKNi, hswapi, hcanoni, hnei⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hMi𝓕)
  -- `|KNi| = q` is prime (Proposition 14.2(g))
  haveI : IsSolvable ↥Mi := hG.solvable_of_mem_maximalSubgroups hMimax
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mi)
    ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
  have hUeq : (U'.map Mi.subtype).subgroupOf Mi = U' :=
    Subgroup.comap_map_eq_self_of_injective Mi.subtype_injective U'
  have hUi : Ch03.IsHallSubgroup ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
      ((U'.map Mi.subtype).subgroupOf Mi) := by rw [hUeq]; exact hU'
  obtain ⟨q, hq, hqcard, -⟩ :=
    ((typeP_structure hG hMimax hMiP hKNiMi hKNi rfl hUi).2.2.2.2.1 hMiP2).2
  have hKNine : KNi ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hqcard; exact hq.ne_one hqcard.symm
  -- the `σ(Mᵢ)′`-Hall data of the swap `Z = KNi × Kᵢ*` for `isPiSubgroup_le_left_of_commute`
  have hswapMi : K ⊔ Kstar = KNi ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mi) :=
    hswapi.trans (by rw [hcanoni])
  have hcentMi : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mi
      ≤ Subgroup.centralizer (KNi : Set G) := hcanoni ▸ inf_le_right
  have hAπc : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mi)ᶜ KNi :=
    kappaHall_isPiSubgroup_sigmaCompl hKNiMi hKNi
  have hBπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mi)
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mi) := fun p hp =>
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mi p (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1,
        (Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_dvd_of_le inf_le_right),
        Nat.card_pos.ne'⟩)
  -- every member `≠ Mᵢ` has its canonical factor equal to `KNi`
  have hKstarEq : ∀ N ∈ (ZFamilyFinset M K).erase Mi,
      (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N = KNi := by
    intro N hNe
    have hN𝓕 := Finset.mem_of_mem_erase hNe
    have hNneMi : N ≠ Mi := Finset.ne_of_mem_erase hNe
    obtain ⟨hNmax, hNP, -, KNj, -, -, -, hcanonj, hnej⟩ :=
      typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN𝓕)
    have hnej' : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≠ ⊥ := hcanonj ▸ hnej
    have hdisjσ : Disjoint (OddOrder.BG.Ch3.S10.sigma Mi) (OddOrder.BG.Ch3.S10.sigma N) :=
      sigma_disjoint_of_nonconjugate hG hMimax hNmax
        (typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU
          (mem_ZFamilyFinset.mp hMi𝓕) (mem_ZFamilyFinset.mp hN𝓕) (Ne.symm hNneMi))
    have hLπc : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mi)ᶜ
        ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := fun p hp => by
      have hpσN : p ∈ OddOrder.BG.Ch3.S10.sigma N :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
          ⟨(Nat.mem_primeFactors.mp hp).1,
            (Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_dvd_of_le inf_le_right),
            Nat.card_pos.ne'⟩)
      exact fun hpσMi => Set.disjoint_left.mp hdisjσ hpσMi hpσN
    have hle : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≤ KNi :=
      isPiSubgroup_le_left_of_commute hswapMi hcentMi hAπc hBπ inf_le_left hLπc
    -- prime-order `KNi`: a nontrivial subgroup is all of it
    have hdvd : Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ∣ q := by
      rw [← hqcard]; exact Subgroup.card_dvd_of_le hle
    have hne1 : Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ≠ 1 :=
      fun h => hnej' (Subgroup.eq_bot_of_card_eq _ h)
    have hcardeq : Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) = Nat.card ↥KNi := by
      rw [hqcard]; exact (hq.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
    exact Subgroup.eq_of_le_of_card_ge hle hcardeq.ge
  -- at most one member is `≠ Mᵢ`
  have herase_le : ((ZFamilyFinset M K).erase Mi).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have hdisj := typeP_family_Kstar_disjoint hG hM hP hKM hK hKstar hU
      (mem_ZFamilyFinset.mp (Finset.mem_of_mem_erase ha))
      (mem_ZFamilyFinset.mp (Finset.mem_of_mem_erase hb)) hab
    rw [hKstarEq a ha, hKstarEq b hb, inf_idem] at hdisj
    rw [hdisj, Subgroup.card_bot] at hqcard
    exact hq.ne_one hqcard.symm
  have hcard_erase := Finset.card_erase_of_mem hMi𝓕
  omega

/-- **BG Theorem 14.7, the unique partner `M*`** (mmd L4047): since the type-`P` family has exactly
two members (`family_card_eq_two`) and `M` is one of them, there is a unique other member `M*`, the
nonconjugate partner of Theorem 14.7.  It is a type-`P` maximal subgroup containing `Z = K ⊔ K*`,
nonconjugate to `M`. -/
theorem exists_partner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∃ Mstar : Subgroup G, Mstar ≠ M ∧ IsZFamilyMember M K Mstar ∧
      ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar := by
  classical
  obtain ⟨a, b, hab, hfam⟩ :=
    Finset.card_eq_two.mp (family_card_eq_two hG D hM hP hKM hK hKstar hU)
  have hMfam : M ∈ ZFamilyFinset M K := mem_ZFamilyFinset.mpr (Or.inl rfl)
  rw [hfam, Finset.mem_insert, Finset.mem_singleton] at hMfam
  rcases hMfam with hMa | hMb
  · refine ⟨b, by rw [hMa]; exact Ne.symm hab,
      mem_ZFamilyFinset.mp (by rw [hfam]; simp), fun N hN => ?_⟩
    have hN' : N ∈ ({a, b} : Finset (Subgroup G)) := hfam ▸ mem_ZFamilyFinset.mpr hN
    rw [Finset.mem_insert, Finset.mem_singleton] at hN'
    exact hN'.imp (fun h => h.trans hMa.symm) id
  · refine ⟨a, by rw [hMb]; exact hab,
      mem_ZFamilyFinset.mp (by rw [hfam]; simp), fun N hN => ?_⟩
    have hN' : N ∈ ({a, b} : Finset (Subgroup G)) := hfam ▸ mem_ZFamilyFinset.mpr hN
    rw [Finset.mem_insert, Finset.mem_singleton] at hN'
    exact hN'.elim (fun h => Or.inr h) (fun h => Or.inl (h.trans hMb.symm))

/-- **BG Theorem 14.7(f), the type-`P₂` dichotomy** (mmd L4047): for the partner `M*` (so every
family member is `M` or `M*`), one of `M`, `M*` is type `P₂`.  Immediate from the density
inequality (`exists_typeP2_member`): the type-`P₂` member it produces is `M` or `M*`. -/
theorem isTypeP2_or_isTypeP2_partner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    IsTypeP2 M ∨ IsTypeP2 Mstar := by
  obtain ⟨N, hN𝓕, hNP2⟩ := exists_typeP2_member hG D hM hP hKM hK hKstar hU
  rcases hpart N (mem_ZFamilyFinset.mp hN𝓕) with h | h
  · subst h; exact Or.inl hNP2
  · subst h; exact Or.inr hNP2

/-- **BG Theorem 14.7, `π(K) ⊆ σ(M*)`** (mmd L3987): every prime `p` dividing `|K|` lies in
`σ(M*)`, for the partner `M*`.  For a line `X ∈ ℰ_p¹(K)`, the maximal subgroup over `N_G(X)` is a
type-`P` family member nonconjugate to `M` (`exists_typeP_partner`), hence `= M*` (the only other
member), and `X ≤ M*_σ` gives `p ∈ σ(M*)`.  This is the half forcing `K ≤ M*_σ` in the partner
structure `Z ⊓ M*_σ = K`. -/
theorem kappaHall_primes_subset_sigma_partner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card ↥K) :
    p ∈ OddOrder.BG.Ch3.S10.sigma Mstar := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxord : orderOf (x : G) = p := (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
  have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
  obtain ⟨N, hNmem, hnc, -, hXNσ, -, -⟩ :=
    exists_typeP_partner hG hM hP hKM hK hKstar hU hXelem hXK
  have hNfam : IsZFamilyMember M K N :=
    Or.inr ⟨p, Subgroup.zpowers (x : G), hp, hXelem, hXK, hNmem⟩
  have hNM : N ≠ M :=
    fun h => hnc (h ▸ (⟨1, by rw [map_one, one_smul]⟩ : IsConjugateSubgroup M M))
  have hNMstar : N = Mstar := (hpart N hNfam).resolve_left hNM
  rw [← hNMstar]
  exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
    ⟨hp, (dvd_of_eq hXcard.symm).trans (Subgroup.card_dvd_of_le hXNσ), Nat.card_pos.ne'⟩)

/-- **BG Theorem 14.7, the partner canonical factor** (mmd L3995): `Z ⊓ M*_σ = K`.  In the swap
`Z = M*'s K* × M*'s κ-Hall`, the partner's canonical factor `Z ⊓ M*_σ` equals `K` (the original
`M`'s Hall `κ`-subgroup).  Two inclusions: `Z ⊓ M*_σ` is a `σ(M)′`-subgroup of the direct product
`Z = K × K*` (`σ(M*) ∩ σ(M) = ∅`), so it lies in the `σ(M)′`-Hall factor `K`
(`isPiSubgroup_le_left_of_commute`); conversely `K ≤ M*_σ` because every prime of `K` lies in
`σ(M*)` (`kappaHall_primes_subset_sigma_partner`).  This is the structural fact that turns the
family's `T = Z − ⋃ Kᵢ*` into `Ẑ = Z − (K ∪ K*)`. -/
theorem partner_canonical_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mstar = K := by
  classical
  have hMstarmax : Mstar ∈ maximalSubgroups G :=
    (typeP_family_member_data hG hM hP hKM hK hKstar hU hMstarmem).1
  have hZMstar : K ⊔ Kstar ≤ Mstar :=
    (typeP_family_member_data hG hM hP hKM hK hKstar hU hMstarmem).2.2.1
  have hnc : ¬ IsConjugateSubgroup M Mstar :=
    typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU (Or.inl rfl) hMstarmem
      (Ne.symm hMstarne)
  have hσdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.sigma Mstar) :=
    sigma_disjoint_of_nonconjugate hG hM hMstarmax hnc
  refine le_antisymm ?_ (le_inf le_sup_left ?_)
  · -- `Z ⊓ M*_σ ≤ K`: it is a `σ(M)′`-subgroup of `Z = K × K*`
    refine isPiSubgroup_le_left_of_commute (π := OddOrder.BG.Ch3.S10.sigma M) rfl
      (hKstar ▸ inf_le_right) (kappaHall_isPiSubgroup_sigmaCompl hKM hK) (fun q hq => ?_)
      inf_le_left (fun q hq => ?_)
    · exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hq).1, (Nat.dvd_of_mem_primeFactors hq).trans
          (Subgroup.card_dvd_of_le (hKstar.le.trans inf_le_left)), Nat.card_pos.ne'⟩)
    · have hqσMstar : q ∈ OddOrder.BG.Ch3.S10.sigma Mstar :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mstar q (Nat.mem_primeFactors.mpr
          ⟨(Nat.mem_primeFactors.mp hq).1, (Nat.dvd_of_mem_primeFactors hq).trans
            (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
      exact fun hqσM => Set.disjoint_left.mp hσdisj hqσM hqσMstar
  · -- `K ≤ M*_σ`: every prime of `K` lies in `σ(M*)`
    refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hMstarmax) (le_sup_left.trans hZMstar) (fun q hq => ?_)
    exact kappaHall_primes_subset_sigma_partner hG hM hP hKM hK hKstar hU hpart
      (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)

/-- **BG Theorem 14.7(e), the family `Z ⊓ N_σ` collapse** (mmd L4051): for the type-`P` family
`{M, M*}` (recorded by `hpart`), the union of the canonical factors collapses to `K ∪ K*`,
`⋃_{N ∈ 𝓕} (Z ⊓ N_σ) = K ∪ K*`, since `Z ⊓ M_σ = K*` (`typeP_self_member`) and `Z ⊓ M*_σ = K`
(`partner_canonical_eq`).  Factored out of `typeP_zTilde_isTI`; reused by the `> ½|G|` density
count `typeP_zTilde_conjClass_gt_half`, where it identifies `Ẑ = Z − (K ∪ K*)` with the family
TI-set `T = Z − ⋃_{N} (Z ⊓ N_σ)`. -/
theorem family_inf_msigma_union_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    (⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))
      = ((K : Set G) ∪ (Kstar : Set G)) := by
  classical
  have hcanonM : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar :=
    (typeP_self_member hG hM hP hKM hK hKstar hU).1
  have hcanonMstar : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mstar = K :=
    partner_canonical_eq hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  apply Set.Subset.antisymm
  · rintro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨N, hN, hxN⟩ := hx
    rcases hpart N (mem_ZFamilyFinset.mp hN) with rfl | rfl
    · rw [hcanonM] at hxN; exact Or.inr hxN
    · rw [hcanonMstar] at hxN; exact Or.inl hxN
  · rintro x (hxK | hxKstar)
    · exact Set.mem_iUnion₂.mpr ⟨Mstar, mem_ZFamilyFinset.mpr hMstarmem,
        by rw [hcanonMstar]; exact hxK⟩
    · exact Set.mem_iUnion₂.mpr ⟨M, mem_ZFamilyFinset.mpr (Or.inl rfl),
        by rw [hcanonM]; exact hxKstar⟩

/-- **BG Theorem 14.7(e), `Ẑ` is a TI-subset** (mmd L4051): with the family `{M, M*}`, the
union `⋃_{N} (Z ⊓ N_σ)` collapses to `K ∪ K*` (`family_inf_msigma_union_eq`), so the family TI-set
`T = Z − ⋃ (Z ⊓ N_σ)` equals `Ẑ = Z − (K ∪ K*)`.  Hence `Ẑ` inherits the TI property from
`typeP_family_T_isTI`.  A conjunct of the `∃! Mstar`. -/
theorem typeP_zTilde_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    OddOrder.GroupTheory.IsTISubset (zTilde K Kstar) (K ⊔ Kstar) := by
  classical
  have hunion := family_inf_msigma_union_eq hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  have hzeq : zTilde K Kstar = ((K ⊔ Kstar : Subgroup G) : Set G) \
      ⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
    simp only [zTilde]; rw [hunion]
  rw [hzeq]
  exact typeP_family_T_isTI hG hM hP hKM hK hKstar hU

/-- Pure `ℕ` identity for the `|Ẑ|` count: `k·l − (k + l − 1) = (k − 1)(l − 1)` for `k, l ≥ 1`. -/
private theorem nat_mul_sub_kl_identity {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    k * l - (k + l - 1) = (k - 1) * (l - 1) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hl
  have h1 : (1 + a) * (1 + b) = a * b + a + b + 1 := by ring
  have h2 : (1 + a - 1) * (1 + b - 1) = a * b := by simp
  omega

/-- `1 ∉ Ẑ`: the identity lies in `K ≤ K ⊔ K*`, hence in the removed set `K ∪ K*`.  So
`sharpSubgroup Ẑ = Ẑ` and `𝒞_G(Ẑ^#) ⊆ G^#` — a prerequisite for the NonType-I `G^#` cover. -/
theorem one_not_mem_zTilde (K Kstar : Subgroup G) : (1 : G) ∉ zTilde K Kstar := by
  rw [zTilde, Set.mem_sdiff, not_and_or, not_not]
  exact Or.inr (Set.mem_union_left _ (SetLike.mem_coe.mpr K.one_mem))

/-- **`Ẑ` is symmetric in its two factors**: `zTilde K K* = zTilde K* K` (both `K ⊔ K*` and
`K ∪ K*` are symmetric).  Used for the partner side, where the swap exchanges `K ↔ K*`. -/
theorem zTilde_comm (K Kstar : Subgroup G) : zTilde K Kstar = zTilde Kstar K := by
  rw [zTilde, zTilde, sup_comm, Set.union_comm]

/-- **`Ẑ` is `G`-conjugation equivariant**: `(zTilde K K*)^g = zTilde (K^g) (K*^g)`.  Conjugation is
a set bijection commuting with `\`, `∪`, and `⊔` (`Subgroup.smul_sup`), so it distributes through
the `zTilde = (K ⊔ K*) ∖ (K ∪ K*)` definition.  Lets a `zTilde` of a conjugate type-`P` maximal be
identified (up to `conjClassSet`) with a fixed `Ẑ`. -/
theorem zTilde_conj_smul (g : G) (K Kstar : Subgroup G) :
    MulAut.conj g • zTilde K Kstar
      = zTilde (MulAut.conj g • K) (MulAut.conj g • Kstar) := by
  rw [zTilde, zTilde, Set.smul_set_sdiff, Set.smul_set_union,
    ← Subgroup.coe_pointwise_smul, ← Subgroup.coe_pointwise_smul,
    ← Subgroup.coe_pointwise_smul, Subgroup.smul_sup]

/-- **`𝒞_G` is invariant under conjugating the underlying set**: `𝒞_G(S^g) = 𝒞_G(S)` (conjugation
permutes `G`-conjugacy classes, fixing their union). -/
theorem conjClassSet_conj_smul (g : G) (S : Set G) :
    conjClassSet (MulAut.conj g • S) = conjClassSet S := by
  ext y
  simp only [OddOrder.GroupTheory.mem_conjClassSet]
  constructor
  · rintro ⟨t, ht, b, rfl⟩
    rw [Set.mem_smul_set] at ht
    obtain ⟨s, hs, hst⟩ := ht
    refine ⟨s, hs, b * g, ?_⟩
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]; group
  · rintro ⟨s, hs, b, rfl⟩
    refine ⟨MulAut.conj g • s, Set.smul_mem_smul_set hs, b * g⁻¹, ?_⟩
    rw [MulAut.smul_def, MulAut.conj_apply]; group

/-- **`𝒞_G(Ẑ)` only depends on the `G`-conjugacy class of `(K, K*)`**: conjugating both factors by
`g` leaves `𝒞_G(zTilde K K*)` unchanged.  This is the fix-`W` step — a `zTilde` of a conjugate
type-`P` maximal has the same `conjClassSet` as the reference `Ẑ`. -/
theorem conjClassSet_zTilde_conj_eq (g : G) (K Kstar : Subgroup G) :
    conjClassSet (zTilde (MulAut.conj g • K) (MulAut.conj g • Kstar))
      = conjClassSet (zTilde K Kstar) := by
  rw [← zTilde_conj_smul, conjClassSet_conj_smul]

/-- **Algebraic core of the κ→Ẑ identification** (the final step of BG `mFT_partition` part 2):
a product `y · y'` of a nonidentity `K*`-element `y` and a nonidentity `K`-element `y'` lies in
`Ẑ = (K ⊔ K*) ∖ (K ∪ K*)`, provided `K ⊓ K* = ⊥`.  Membership in `K ⊔ K*` is immediate; `y·y' ∉ K`
because then `y = (y·y')·y'⁻¹ ∈ K ⊓ K* = ⊥` contradicts `y ≠ 1`, and dually `y·y' ∉ K*`.  The deep
part of κ→Ẑ (placing the σ-part `y` in `K* = C_{M_σ}(K)` via `Z = K ⊔ K*` cyclic, and the
`κ`-element `y'` in the Hall `K`) wraps this core. -/
theorem mem_zTilde_of_mul {K Kstar : Subgroup G} (htri : K ⊓ Kstar = ⊥)
    {y y' : G} (hy : y ∈ Kstar) (hy1 : y ≠ 1) (hy' : y' ∈ K) (hy'1 : y' ≠ 1) :
    y * y' ∈ zTilde K Kstar := by
  rw [zTilde, Set.mem_sdiff]
  refine ⟨(K ⊔ Kstar).mul_mem (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left hy'), ?_⟩
  rw [Set.mem_union, not_or]
  refine ⟨fun hmem => hy1 ?_, fun hmem => hy'1 ?_⟩
  · have hyK : y ∈ K := by
      have h := K.mul_mem (SetLike.mem_coe.mp hmem) (K.inv_mem hy')
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h
    have h := Subgroup.mem_inf.mpr ⟨hyK, hy⟩
    rwa [htri, Subgroup.mem_bot] at h
  · have hy'Ks : y' ∈ Kstar := by
      have h := Kstar.mul_mem (Kstar.inv_mem hy) (SetLike.mem_coe.mp hmem)
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h
    have h := Subgroup.mem_inf.mpr ⟨hy', hy'Ks⟩
    rwa [htri, Subgroup.mem_bot] at h

/-- **`y ∈ C_G(K)` from `y ∈ Z = K ⊔ K*` with `Z` cyclic** (the `cKZ` step of κ→Ẑ): since the
join `K ⊔ K*` is cyclic — hence abelian — every element of it centralizes `K`.  Combined with
`y ∈ M_σ`, this places the σ-part `y` in `K* = M_σ ⊓ C_G(K)`. -/
theorem mem_centralizer_of_mem_sup_isCyclic {K Kstar : Subgroup G}
    (hcyc : IsCyclic ↥(K ⊔ Kstar)) {y : G} (hyZ : y ∈ K ⊔ Kstar) :
    y ∈ Subgroup.centralizer (K : Set G) := by
  haveI := hcyc
  letI : CommGroup ↥(K ⊔ Kstar) := IsCyclic.commGroup
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hkZ : k ∈ K ⊔ Kstar := Subgroup.mem_sup_left (SetLike.mem_coe.mp hk)
  have hcomm : (⟨k, hkZ⟩ : ↥(K ⊔ Kstar)) * ⟨y, hyZ⟩ = ⟨y, hyZ⟩ * ⟨k, hkZ⟩ := mul_comm _ _
  have h := congrArg (Subgroup.subtype (K ⊔ Kstar)) hcomm
  simpa using h

/-- **BG Theorem 14.7, `|Ẑ| = (k − 1)(k* − 1)`** (mmd L4051): the TI-set `Ẑ = Z − (K ∪ K*)` has
`(|K| − 1)(|K*| − 1)` elements.  `|Z| = |K|·|K*|` (`card_kappaHall_sup_Kstar`), `K ∩ K* = 1`
(`kappaHall_inf_Kstar_eq_bot`) so `|K ∪ K*| = |K| + |K*| − 1`, and `|Ẑ| = |Z| − |K ∪ K*|`.
This is the cardinality the density bound `|𝒞_G(Ẑ)| = (1 − 1/k)(1 − 1/k*)|G| > ½|G|` rests on. -/
theorem zTilde_ncard_eq [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    (zTilde K Kstar).ncard = (Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1) := by
  classical
  have hsub : ((K : Set G) ∪ (Kstar : Set G)) ⊆ ((K ⊔ Kstar : Subgroup G) : Set G) :=
    Set.union_subset (SetLike.coe_subset_coe.mpr le_sup_left)
      (SetLike.coe_subset_coe.mpr le_sup_right)
  have hZc : ((K ⊔ Kstar : Subgroup G) : Set G).ncard = Nat.card ↥K * Nat.card ↥Kstar := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr (Equiv.refl _)).symm.trans (card_kappaHall_sup_Kstar hKM hK hKstar)
  have hKc : (K : Set G).ncard = Nat.card ↥K := by
    rw [← Nat.card_coe_set_eq]; exact (Nat.card_congr (Equiv.refl _)).symm
  have hKstarc : (Kstar : Set G).ncard = Nat.card ↥Kstar := by
    rw [← Nat.card_coe_set_eq]; exact (Nat.card_congr (Equiv.refl _)).symm
  have hinter : (K : Set G) ∩ (Kstar : Set G) = {1} := by
    rw [← Subgroup.coe_inf, kappaHall_inf_Kstar_eq_bot hKM hK hKstar, Subgroup.coe_bot]
  have hunion : ((K : Set G) ∪ (Kstar : Set G)).ncard = Nat.card ↥K + Nat.card ↥Kstar - 1 := by
    have h := Set.ncard_union_add_ncard_inter (K : Set G) (Kstar : Set G)
    rw [hinter, Set.ncard_singleton, hKc, hKstarc] at h
    omega
  rw [zTilde, Set.ncard_sdiff hsub, hZc, hunion]
  exact nat_mul_sub_kl_identity Nat.card_pos Nat.card_pos

/-- Pure `ℕ` arithmetic for the `8/15 > 1/2` density step: for coprime odd `k, l > 1` one has
`k·l < 2(k−1)(l−1)`.  Equivalently `(k−2)(l−2) > 2`; the only odd pair `≥ 3` failing this is
`k = l = 3`, excluded by coprimality (`gcd 3 3 = 3 ≠ 1`).  Hence one factor is `≥ 5`. -/
private theorem card_kkstar_lt {k l : ℕ} (hk : Odd k) (hl : Odd l)
    (hk1 : k ≠ 1) (hl1 : l ≠ 1) (hcop : Nat.Coprime k l) :
    k * l < 2 * ((k - 1) * (l - 1)) := by
  obtain ⟨a, rfl⟩ := hk
  obtain ⟨b, rfl⟩ := hl
  have ha : 1 ≤ a := by omega
  have hb : 1 ≤ b := by omega
  have hnotboth : ¬ (a = 1 ∧ b = 1) := by
    rintro ⟨rfl, rfl⟩; exact absurd hcop (by decide)
  have hab : 2 ≤ a ∨ 2 ≤ b := by omega
  have key : 2 * a + 2 * b + 1 < 4 * (a * b) := by
    rcases hab with ha2 | hb2
    · have h1 : 2 * b ≤ a * b := Nat.mul_le_mul ha2 (le_refl b)
      have h2 : a ≤ a * b := by simpa using Nat.mul_le_mul (le_refl a) hb
      omega
    · have h1 : 2 * a ≤ a * b := by simpa [mul_comm] using Nat.mul_le_mul (le_refl a) hb2
      have h2 : b ≤ a * b := by simpa [mul_comm] using Nat.mul_le_mul (le_refl b) ha
      omega
  have e1 : 2 * a + 1 - 1 = 2 * a := by omega
  have e2 : 2 * b + 1 - 1 = 2 * b := by omega
  rw [e1, e2]
  nlinarith [key]

/-- **BG Theorem 14.7, the density bound `|𝒞_G(Ẑ)| > ½|G|`** (mmd L3975/L4051): the conjugacy
saturation of the TI-set `Ẑ` covers more than half of `G`.  This is the counting heart of the
`∃! M*` covering — a third nonconjugate type-`P` maximal subgroup would force a *second* `> ½|G|`
saturation piece disjoint from this one, which is impossible.

Proof chain: `Ẑ` is a TI-subset of `Z = K ⊔ K*` (`typeP_zTilde_isTI`) normalised by `Z`
(`typeP_family_Z_normalizes_T`, transported along `Ẑ = T`), so `|𝒞_G(Ẑ)| = |Ẑ|·[G : Z]`; with
`|Ẑ| = (k−1)(k*−1)` (`zTilde_ncard_eq`) and `|G| = |Z|·[G : Z] = k·k*·[G : Z]`
(`card_kappaHall_sup_Kstar`), the bound reduces to the pure inequality `k·k* < 2(k−1)(k*−1)`
(`card_kkstar_lt`) for the coprime (`coprime_card_kappaHall_Kstar`) odd `k = |K|`, `k* = |K*| > 1`
(`K* ≠ 1` is `typeP_structure`'s second conjunct). -/
theorem typeP_zTilde_conjClass_gt_half [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    Nat.card G < 2 * (conjClassSet (zTilde K Kstar)).ncard := by
  classical
  -- `Ẑ = T` (the family TI-set), via the `Z ⊓ N_σ` collapse.
  have hzeq : zTilde K Kstar = ((K ⊔ Kstar : Subgroup G) : Set G) \
      ⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
    simp only [zTilde]
    rw [family_inf_msigma_union_eq hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart]
  -- `Z` normalises `Ẑ` (transported from the family form).
  have hstab : ∀ l ∈ K ⊔ Kstar, MulAut.conj l • (zTilde K Kstar) = zTilde K Kstar := by
    intro l hl
    rw [hzeq]; exact typeP_family_Z_normalizes_T hG hM hP hKM hK hKstar hU l hl
  -- Saturation count `|𝒞_G(Ẑ)| = |Ẑ|·[G : Z]`.
  have hcount : (conjClassSet (zTilde K Kstar)).ncard
      = (zTilde K Kstar).ncard * (K ⊔ Kstar).index :=
    ncard_conjClassSet_of_isTISubset
      (typeP_zTilde_isTI hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart) hstab
  -- `|Ẑ| = (k − 1)(k* − 1)`.
  have hZc : (zTilde K Kstar).ncard = (Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1) :=
    zTilde_ncard_eq hKM hK hKstar
  -- `|G| = |Z|·[G : Z] = k·k*·[G : Z]`.
  have hG_eq : Nat.card G = Nat.card ↥K * Nat.card ↥Kstar * (K ⊔ Kstar).index := by
    rw [← card_kappaHall_sup_Kstar hKM hK hKstar]
    exact (Subgroup.card_mul_index (K ⊔ Kstar)).symm
  have hidx_pos : 0 < (K ⊔ Kstar).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  -- `k, k*` are odd (divisors of `|G|`).
  have hKodd : Odd (Nat.card ↥K) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
  have hKstarodd : Odd (Nat.card ↥Kstar) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Kstar)
  -- `k > 1`: a prime `p ∈ κ(M)` divides `|K|` (`card_kappaHall_ne_one`).
  have hKne1 : Nat.card ↥K ≠ 1 := card_kappaHall_ne_one hP hKM hK
  -- `k* > 1`: `K* ≠ ⊥` (Proposition 14.2's second conjunct).
  have hKstarne1 : Nat.card ↥Kstar ≠ 1 :=
    fun h => (typeP_structure hG hM hP hKM hK hKstar hU).2.1 (Subgroup.eq_bot_of_card_eq _ h)
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Kstar) :=
    coprime_card_kappaHall_Kstar hKM hK hKstar
  have harith : Nat.card ↥K * Nat.card ↥Kstar
      < 2 * ((Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1)) :=
    card_kkstar_lt hKodd hKstarodd hKne1 hKstarne1 hcop
  rw [hcount, hZc, hG_eq]
  calc Nat.card ↥K * Nat.card ↥Kstar * (K ⊔ Kstar).index
      < 2 * ((Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1)) * (K ⊔ Kstar).index :=
        mul_lt_mul_of_pos_right harith hidx_pos
    _ = 2 * ((Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1) * (K ⊔ Kstar).index) :=
        mul_assoc _ _ _

open Classical in
/-- A reusable dummy `SigmaDecompositionData`: `length x = 1` iff `x ≠ 1` and `x` has a maximal
`σ`-subgroup.  The structure axiom `length_one_iff` pins this predicate across *all* carriers, and
the family/density machinery (`family_card_eq_two`, `exists_partner`, …) consumes `D` only through
`D.length x = 1`; so this dummy suffices — no genuine `σ`-decomposition theory is needed. -/
noncomputable def dummySigmaDecomposition (G : Type*) [Group G] : SigmaDecompositionData G where
  length := fun y => if y ≠ 1 ∧ (maximalSigmaSubgroupsOfElement y).Nonempty then 1 else 0
  length_one_iff := by
    intro y
    by_cases h : y ≠ 1 ∧ (maximalSigmaSubgroupsOfElement y).Nonempty <;> simp [h]

/-- Two subsets of a finite group, each covering more than half of it, must intersect. -/
theorem ncard_inter_nonempty_of_two_mul_gt [Finite G] {A B : Set G}
    (hA : Nat.card G < 2 * A.ncard) (hB : Nat.card G < 2 * B.ncard) :
    (A ∩ B).Nonempty := by
  classical
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hunion := Set.ncard_union_add_ncard_inter A B
  rw [hempty, Set.ncard_empty] at hunion
  have hle : (A ∪ B).ncard ≤ Nat.card G := by
    rw [← Set.ncard_univ G]
    exact Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
  omega

/-- **BG Theorem 14.7, the density bound holds for every type-`P` maximal subgroup** (mmd L4053,
"we also have `|𝒞_G(S)| > ½|G|`"): for `H ∈ 𝓜_𝓟` there is a Hall `κ(H)`-subgroup `L` with
`L* = C_{Hσ}(L)` and `|𝒞_G(Ẑ_H)| > ½|G|`.  The same density count (`typeP_zTilde_conjClass_gt_half`)
run for `H`; the partner data for `H` is produced internally (`exists_partner`, fed the dummy
`σ`-decomposition).  Reused in the covering step of `typeP_duality`. -/
theorem exists_zTilde_conjClass_gt_half_of_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {H : Subgroup G}
    (hHmax : H ∈ maximalSubgroups G) (hHP : IsTypeP H) :
    ∃ L Lstar Uu : Subgroup G, L ≤ H ∧ Ch03.IsHallSubgroup (kappa H) (L.subgroupOf H) ∧
      Lstar = OddOrder.BG.Ch3.S10.Msigma H ⊓ Subgroup.centralizer (L : Set G) ∧
      Ch03.IsHallSubgroup ((kappa H ∪ OddOrder.BG.Ch3.S10.sigma H)ᶜ) (Uu.subgroupOf H) ∧
      Nat.card G < 2 * (conjClassSet (zTilde L Lstar)).ncard := by
  classical
  haveI : IsSolvable ↥H := hG.solvable_of_mem_maximalSubgroups hHmax
  -- Hall `κ(H)`-subgroup `L` of `H`.
  obtain ⟨L', hL'⟩ := Ch03.hall_E_exists (G := ↥H) (kappa H)
  have hLeq : (L'.map H.subtype).subgroupOf H = L' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective L'
  have hL : Ch03.IsHallSubgroup (kappa H) ((L'.map H.subtype).subgroupOf H) := by
    rw [hLeq]; exact hL'
  have hLH : L'.map H.subtype ≤ H := Subgroup.map_subtype_le L'
  set L := L'.map H.subtype with hLdef
  set Lstar := OddOrder.BG.Ch3.S10.Msigma H ⊓ Subgroup.centralizer (L : Set G) with hLstar
  -- Hall `(κ(H) ∪ σ(H))'`-subgroup `U` of `H`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥H) ((kappa H ∪ OddOrder.BG.Ch3.S10.sigma H)ᶜ)
  have hUeq : (U'.map H.subtype).subgroupOf H = U' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((kappa H ∪ OddOrder.BG.Ch3.S10.sigma H)ᶜ)
      ((U'.map H.subtype).subgroupOf H) := by rw [hUeq]; exact hU'
  -- Partner data for `H`, then the density bound.
  obtain ⟨Hstar, hHstarne, hHstarmem, hpart⟩ :=
    exists_partner hG (dummySigmaDecomposition G) hHmax hHP hLH hL hLstar hU
  exact ⟨L, Lstar, U'.map H.subtype, hLH, hL, hLstar, hU,
    typeP_zTilde_conjClass_gt_half hG hHmax hHP hLH hL hLstar hU hHstarmem hHstarne hpart⟩

/-- Dual of `isPiElementCompl_mem_left_of_commute`: a `π`-element of `Z = A ⊔ B` (with `A` a
`πᶜ`-group, `B` a `π`-group commuting with `A`) lies in `B`.  (Swap the roles of `A`, `B` and
`π`, `πᶜ`.) -/
theorem isPiElement_mem_right_of_commute [Finite G] {A B Z : Subgroup G} {π : Set ℕ}
    (hswap : Z = A ⊔ B) (hcent : B ≤ Subgroup.centralizer (A : Set G))
    (hAπc : Subgroup.IsPiSubgroup πᶜ A) (hBπ : Subgroup.IsPiSubgroup π B)
    {b : G} (hbZ : b ∈ Z) (hbπ : IsPiElement π b) : b ∈ B := by
  have hAcent : A ≤ Subgroup.centralizer (B : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_iff]
    exact fun c hc => (Subgroup.mem_centralizer_iff.mp (hcent hc) a ha).symm
  exact isPiElementCompl_mem_left_of_commute (A := B) (B := A) (π := πᶜ)
    (by rw [hswap, sup_comm]) hAcent (by rwa [compl_compl]) hAπc hbZ (by rwa [compl_compl])

/-- **BG Theorem 14.7 covering, the `σ`-part matching** (mmd L4053): if `t` lies in both
`Ẑ_M = (K ⊔ K*) − (K ∪ K*)` (with `K` a `σ(M)′`-group, `K*` a `σ(M)`-group commuting with `K`) and
in `L ⊔ L*` but not in `L` (with `L` a `σ(H)′`-group, `L*` a `σ(H)`-group commuting with `L`), then
`L*` meets one of `K`, `K*` nontrivially.  Proof: the `σ(H)`-part `w` of `t` is a nontrivial
element of `L*` (else `t = (σ(H)′-part) ∈ L`), and `w ∈ ⟨t⟩ ⊆ K ⊔ K*`; its `σ(M)`- and
`σ(M)′`-parts are powers of `w` (so in `L*`) lying in `K*` resp. `K`, and at least one is
nontrivial.  This realizes BG's "`T ∩ S ≠ ∅ ⟹ L* ∩ Kᵢ* ≠ 1`". -/
theorem exists_inf_ne_bot_of_mem_zTilde_inter [Finite G] {K Kstar L Lstar : Subgroup G}
    {πM πH : Set ℕ}
    (hKπ : Subgroup.IsPiSubgroup πMᶜ K) (hKstarπ : Subgroup.IsPiSubgroup πM Kstar)
    (hKcent : Kstar ≤ Subgroup.centralizer (K : Set G))
    (hLπ : Subgroup.IsPiSubgroup πHᶜ L) (hLstarπ : Subgroup.IsPiSubgroup πH Lstar)
    (hLcent : Lstar ≤ Subgroup.centralizer (L : Set G))
    {t : G} (htZ : t ∈ K ⊔ Kstar) (htnL : t ∉ L) (htZ' : t ∈ L ⊔ Lstar) :
    Lstar ⊓ K ≠ ⊥ ∨ Lstar ⊓ Kstar ≠ ⊥ := by
  classical
  -- `σ(H)`-decompose `t = w * v`; `v ∈ L`, `w ∈ L*`, and `w ≠ 1`.
  obtain ⟨w, v, hwv, -, hwπ, hvπ, hwz, hvz⟩ := exists_isPiElement_mul πH t
  have hvL : v ∈ L := isPiElementCompl_mem_left_of_commute rfl hLcent hLπ hLstarπ
    ((Subgroup.zpowers_le.mpr htZ') hvz) hvπ
  have hwLstar : w ∈ Lstar := isPiElement_mem_right_of_commute rfl hLcent hLπ hLstarπ
    ((Subgroup.zpowers_le.mpr htZ') hwz) hwπ
  have hw1 : w ≠ 1 := fun hw => htnL (by rw [show t = v by rw [← hwv, hw, one_mul]]; exact hvL)
  -- `σ(M)`-decompose `w = a * b`; `a ∈ K*`, `b ∈ K`, both powers of `w` (so in `L*`).
  have hwZ : w ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ) hwz
  obtain ⟨a, b, hab, -, haπ, hbπ, haz, hbz⟩ := exists_isPiElement_mul πM w
  have haKstar : a ∈ Kstar := isPiElement_mem_right_of_commute rfl hKcent hKπ hKstarπ
    ((Subgroup.zpowers_le.mpr hwZ) haz) haπ
  have hbK : b ∈ K := isPiElementCompl_mem_left_of_commute rfl hKcent hKπ hKstarπ
    ((Subgroup.zpowers_le.mpr hwZ) hbz) hbπ
  have haLstar : a ∈ Lstar := (Subgroup.zpowers_le.mpr hwLstar) haz
  have hbLstar : b ∈ Lstar := (Subgroup.zpowers_le.mpr hwLstar) hbz
  -- `w = a * b ≠ 1`, so one factor is nontrivial.
  have hor : a ≠ 1 ∨ b ≠ 1 := by
    by_contra h; push Not at h
    exact hw1 (by rw [← hab, h.1, h.2, mul_one])
  rcases hor with ha1 | hb1
  · exact Or.inr fun hbot => ha1 (by
      have : a ∈ Lstar ⊓ Kstar := Subgroup.mem_inf.mpr ⟨haLstar, haKstar⟩
      rwa [hbot, Subgroup.mem_bot] at this)
  · exact Or.inl fun hbot => hb1 (by
      have : b ∈ Lstar ⊓ K := Subgroup.mem_inf.mpr ⟨hbLstar, hbK⟩
      rwa [hbot, Subgroup.mem_bot] at this)

/-- **BG Proposition 14.2(f)** (mmd L3838): every `σ(M)`-subgroup `Y < ⊤` of `G` meeting `K*`
nontrivially lies in `M_σ`.  Not among `typeP_structure`'s packaged conjuncts; derived here from
Corollary 12.16 (`Y` is `G`-conjugate into `M_σ`) and Proposition 14.2(d) (the conjugator lies in
`M`, since it fixes a nontrivial element of `K*`).  A step of the partner-symmetry argument of
Theorem 14.7. -/
theorem typeP_sigma_subgroup_le_Msigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {Y : Subgroup G} (hYlt : Y < ⊤)
    (hYpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Y)
    (hYmeet : Y ⊓ Kstar ≠ ⊥) :
    Y ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  have hYne : Y ≠ ⊥ := fun h => hYmeet (by rw [h, bot_inf_eq])
  -- Corollary 12.16: `Y` is `G`-conjugate into `M_σ`.
  obtain ⟨g, hg⟩ := sigma_subgroup_conj_into_Msigma_general hG hM hYne hYlt hYpi
    (fun hN hnc => sigma_disjoint_of_nonconjugate hG hM hN hnc)
  -- A nontrivial common element `y ∈ Y ⊓ K*`.
  obtain ⟨ysub, hysub1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYmeet
  have hy1 : (ysub : G) ≠ 1 := fun h => hysub1 (OneMemClass.coe_eq_one.mp h)
  have hyY : (ysub : G) ∈ Y := (Subgroup.mem_inf.mp ysub.2).1
  have hyKstar : (ysub : G) ∈ Kstar := (Subgroup.mem_inf.mp ysub.2).2
  -- `conj g • y ∈ M_σ ⊆ M`, so `y ∈ conj g⁻¹ • M`.
  have hyMconj : (ysub : G) ∈ MulAut.conj g⁻¹ • M := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      show (MulAut.conj g⁻¹)⁻¹ • (ysub : G) = MulAut.conj g • (ysub : G) by
        rw [← map_inv MulAut.conj g⁻¹, inv_inv]]
    exact OddOrder.BG.Ch3.S10.Msigma_le M
      (hg (Subgroup.smul_mem_pointwise_smul (ysub : G) (MulAut.conj g) Y hyY))
  -- Proposition 14.2(d): `K* ⊓ Mᵍ⁻¹ ≠ 1` forces `g⁻¹ ∈ M`.
  have hginvM : g⁻¹ ∈ M := by
    by_contra hg'
    exact hy1 (Subgroup.mem_bot.mp
      (((typeP_structure hG hM hP hKM hK hKstar hU).2.2.2.1 g⁻¹ hg') ▸
        Subgroup.mem_inf.mpr ⟨hyKstar, hyMconj⟩))
  have hgM : g ∈ M := inv_inv g ▸ M.inv_mem hginvM
  -- `conj g` fixes `M` and `M_σ`; descend `conj g • Y ≤ M_σ` to `Y ≤ M_σ`.
  have hconjM : MulAut.conj g • M = M :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hgM)
  have hgMsigma :
      MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M = OddOrder.BG.Ch3.S10.Msigma M := by
    rw [← Msigma_conj_smul, hconjM]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp (hgMsigma ▸ hg)

/-- **BG Theorem 14.7(2)(3), partner symmetry** (mmd L4061): the partner `M*` carries the dual
Hall structure — `K*` is a Hall `κ(M*)`-subgroup of `M*` and `K = C_{M*_σ}(K*)`.  So the roles of
`(M, K, K*)` and `(M*, K*, K)` are symmetric.

This is short here (not BG's end-of-proof `Hall σ(M)`-subgroup argument) because the family
machinery already produced `M*`'s Hall `κ(M*)`-subgroup `KN` with `Z = KN ⊔ C_{M*_σ}(KN)`
(`typeP_family_member_data`) and `Z ⊓ M*_σ = K` (`partner_canonical_eq`); two applications of
`isPiSubgroup_le_left_of_commute` (with `π = σ(M*)`: `K` is the `σ(M*)`-part of `Z`, while `KN` and
`K*` are both the `σ(M*)′`-part) give `KN = K*`. -/
theorem typeP_partner_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    Mstar ∈ maximalSubgroups G ∧ IsTypeP Mstar ∧ Kstar ≤ Mstar ∧
      Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar) ∧
      K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G) := by
  classical
  obtain ⟨hMstarmax, hMstarP, hZMstar, KN, hKNMstar, hKN_hall, hsw, hcanon, -⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hMstarmem
  -- The partner's canonical factor `C_{M*_σ}(KN) = K`.
  have hcanonK : OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (KN : Set G) = K := by
    rw [hcanon]; exact partner_canonical_eq hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  have hnc : ¬ IsConjugateSubgroup M Mstar :=
    typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU (Or.inl rfl) hMstarmem
      (Ne.symm hMstarne)
  have hσdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.sigma Mstar) :=
    sigma_disjoint_of_nonconjugate hG hM hMstarmax hnc
  -- `π`-subgroup data for `π = σ(M*)`: `K` is `σ(M*)`, `K*`/`KN` are `σ(M*)′`.
  have hK_piMstar : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar) K := fun q hq =>
    kappaHall_primes_subset_sigma_partner hG hM hP hKM hK hKstar hU hpart
      (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
  have hKstar_piMstarc :
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ Kstar := fun q hq =>
    Set.disjoint_left.mp hσdisj (Kstar_isPiSubgroup_sigma hKstar q hq)
  have hKN_piMstarc :
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ KN := fun q hq =>
    kappa_subset_sigmaCompl (hKN_hall.1 q
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKNMstar).toEquiv]; exact hq))
  -- `K` centralizes both `K*` and `KN`.
  have hKcKstar : K ≤ Subgroup.centralizer (Kstar : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hKstar ▸ hs)).2 k hk).symm
  have hKcKN : K ≤ Subgroup.centralizer (KN : Set G) := hcanonK ▸ inf_le_right
  -- `KN = K*`: each lies in the other's `σ(M*)′`-part of `Z`.
  have hKNle : KN ≤ Kstar := isPiSubgroup_le_left_of_commute (π := OddOrder.BG.Ch3.S10.sigma Mstar)
    (by rw [sup_comm]) hKcKstar hKstar_piMstarc hK_piMstar (by rw [hsw]; exact le_sup_left)
    hKN_piMstarc
  have hKstarle : Kstar ≤ KN := isPiSubgroup_le_left_of_commute
    (π := OddOrder.BG.Ch3.S10.sigma Mstar) (hsw.trans (by rw [hcanonK])) hKcKN hKN_piMstarc
    hK_piMstar le_sup_right hKstar_piMstarc
  have hKNeq : KN = Kstar := le_antisymm hKNle hKstarle
  exact ⟨hMstarmax, hMstarP, le_sup_right.trans hZMstar, hKNeq ▸ hKN_hall,
    (hKNeq ▸ hcanonK).symm⟩

/-- **BG Theorem 14.7(1)** (mmd L3964): `ℳ(C_G(Y)) = {M*}` for every `Y ∈ ℰ¹(K)`.  This is
Proposition 14.2(c) applied to the *partner* `M*`: by the partner symmetry
(`typeP_partner_structure`) `K*` is a Hall `κ(M*)`-subgroup of `M*` and `K = C_{M*_σ}(K*)`, i.e.
`K` plays the `K*`-role for `M*`, so `14.2(c)` for `M*` yields the unique-maximal conclusion for
lines of `K`.  The `K`-side companion of Proposition 14.2(c); the covering step of Theorem 14.7
uses it to conjugate a type-`P` subgroup to `M*`. -/
theorem typeP_partner_centralizer_singleton [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {p : ℕ} [Fact p.Prime] {Y : Subgroup G} (hY : Y ∈ elemAbelianOfRank G p 1) (hYK : Y ≤ K) :
    maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {Mstar} := by
  classical
  obtain ⟨hMstarmax, hMstarP, hKstarMstar, hKstar_hall, hK_eq⟩ :=
    typeP_partner_structure hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  haveI : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstarmax
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mstar)
    ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
  have hUeq : (U'.map Mstar.subtype).subgroupOf Mstar = U' :=
    Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective U'
  have hU_Mstar : Ch03.IsHallSubgroup ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
      ((U'.map Mstar.subtype).subgroupOf Mstar) := by rw [hUeq]; exact hU'
  exact (typeP_structure hG hMstarmax hMstarP hKstarMstar hKstar_hall hK_eq hU_Mstar).2.2.2.2.2.1
    p Fact.out Y hY hYK

/-- **BG Theorem 14.7(7), the covering** (mmd L4053): every type-`P` maximal subgroup `H` is
conjugate to `M` or to its partner `M*`.

Proof: both `Ẑ_M` and `Ẑ_H` have conjugacy saturation `> ½|G|`
(`typeP_zTilde_conjClass_gt_half`, `exists_zTilde_conjClass_gt_half_of_isTypeP`), so the
saturations meet (`ncard_inter_nonempty_of_two_mul_gt`); a common element gives `t ∈ Ẑ_M`,
`s ∈ Ẑ_H` with `t = c • s`.  The `σ`-part matching (`exists_inf_ne_bot_of_mem_zTilde_inter`) then
yields a nontrivial `L*ᶜ ⊓ K` or `L*ᶜ ⊓ K*` (here `L*ᶜ = c • L*`); a line `Y` in it satisfies
`ℳ(C_G(Y)) = {M}` (Proposition 14.2(c), `K*`-case) or `{M*}` (`typeP_partner_centralizer_singleton`,
`K`-case), while `c⁻¹ • Y ∈ ℰ¹(L*)` gives `ℳ(C_G(c⁻¹•Y)) = {H}` (Proposition 14.2(c) for `H`).
Transporting by `c` shows `c • H` is a maximal subgroup over `C_G(Y)`, so `c • H = M` or `M*`. -/
theorem typeP_covering [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {H : Subgroup G} (hHmax : H ∈ maximalSubgroups G) (hHP : IsTypeP H) :
    IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar := by
  classical
  have hMbound := typeP_zTilde_conjClass_gt_half hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  obtain ⟨L, Lstar, Uu, hLH, hL_hall, hLstar_eq, hU_H, hHbound⟩ :=
    exists_zTilde_conjClass_gt_half_of_isTypeP hG hHmax hHP
  obtain ⟨u, huM, huH⟩ := ncard_inter_nonempty_of_two_mul_gt hMbound hHbound
  obtain ⟨t, htM, a, hat⟩ := huM
  obtain ⟨s, hsH, b, hbs⟩ := huH
  simp only [zTilde, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or] at htM hsH
  obtain ⟨htZ, htK, htKstar⟩ := htM
  obtain ⟨hsZ, hsL, hsLstar⟩ := hsH
  set c := a⁻¹ * b with hc_def
  -- `t = c • s`.
  have htcs : MulAut.conj c • s = t := by
    have key : b * s * b⁻¹ = a * t * a⁻¹ := hbs.trans hat.symm
    rw [MulAut.smul_def, MulAut.conj_apply, hc_def, mul_inv_rev, inv_inv]
    calc a⁻¹ * b * s * (b⁻¹ * a)
        = a⁻¹ * (b * s * b⁻¹) * a := by group
      _ = a⁻¹ * (a * t * a⁻¹) * a := by rw [key]
      _ = t := by group
  have hcancel1 : ∀ X : Subgroup G, MulAut.conj c⁻¹ • (MulAut.conj c • X) = X := fun X => by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hcancel2 : ∀ X : Subgroup G, MulAut.conj c • (MulAut.conj c⁻¹ • X) = X := fun X => by
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  -- Matching inputs.
  have hcardL : Nat.card ↥(MulAut.conj c • L) = Nat.card ↥L :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hcardLstar : Nat.card ↥(MulAut.conj c • Lstar) = Nat.card ↥Lstar :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hKπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M)ᶜ K :=
    kappaHall_isPiSubgroup_sigmaCompl hKM hK
  have hKstarπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Kstar :=
    Kstar_isPiSubgroup_sigma hKstar
  have hKcent : Kstar ≤ Subgroup.centralizer (K : Set G) := hKstar ▸ inf_le_right
  have hcLπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma H)ᶜ (MulAut.conj c • L) := by
    intro q hq
    rw [hcardL] at hq
    exact kappa_subset_sigmaCompl
      (hL_hall.1 q (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv]))
  have hcLstarπ :
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma H) (MulAut.conj c • Lstar) := by
    intro q hq
    rw [hcardLstar] at hq
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup H q (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hq).1, (Nat.dvd_of_mem_primeFactors hq).trans
        (Subgroup.card_dvd_of_le (hLstar_eq ▸ inf_le_left)), Nat.card_pos.ne'⟩)
  have hcLcent : MulAut.conj c • Lstar ≤ Subgroup.centralizer ((MulAut.conj c • L : Subgroup G)) := by
    rw [← centralizer_conj_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (hLstar_eq ▸ inf_le_right)
  have htnL : t ∉ MulAut.conj c • L := fun ht =>
    hsL (Subgroup.smul_mem_pointwise_smul_iff.mp (htcs.symm ▸ ht))
  have htZ' : t ∈ (MulAut.conj c • L) ⊔ (MulAut.conj c • Lstar) := by
    rw [← htcs, ← Subgroup.smul_sup]
    exact Subgroup.smul_mem_pointwise_smul s (MulAut.conj c) (L ⊔ Lstar) hsZ
  have hmatch := exists_inf_ne_bot_of_mem_zTilde_inter (πM := OddOrder.BG.Ch3.S10.sigma M)
    (πH := OddOrder.BG.Ch3.S10.sigma H) hKπ hKstarπ hKcent hcLπ hcLstarπ hcLcent htZ htnL htZ'
  -- Common tail: a line `Y ≤ c • L*` with `ℳ(C_G(Y)) = {N}` gives `H ~ N`.
  have hfinish : ∀ {N : Subgroup G} {p : ℕ}, p.Prime → ∀ {Y : Subgroup G},
      Y ∈ elemAbelianOfRank G p 1 → Y ≤ MulAut.conj c • Lstar →
      maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {N} →
      IsConjugateSubgroup H N := by
    intro N p hp Y hYea hYcL hN_sing
    have hcY : MulAut.conj c⁻¹ • Y ≤ Lstar := by
      have h1 := Subgroup.pointwise_smul_le_pointwise_smul_iff
        (a := MulAut.conj c⁻¹) |>.mpr hYcL
      rwa [hcancel1 Lstar] at h1
    have hcYea : MulAut.conj c⁻¹ • Y ∈ elemAbelianOfRank G p 1 :=
      conj_smul_mem_elemAbelianOfRank c⁻¹ hYea
    have hH_sing := (typeP_structure hG hHmax hHP hLH hL_hall hLstar_eq hU_H).2.2.2.2.2.1
      p hp _ hcYea hcY
    have hCle : Subgroup.centralizer ((MulAut.conj c⁻¹ • Y : Subgroup G) : Set G) ≤ H :=
      (mem_maximalSubgroupsContaining.mp (hH_sing.symm ▸ Set.mem_singleton H)).2
    have hCYle : Subgroup.centralizer (Y : Set G) ≤ MulAut.conj c • H := by
      have h1 := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj c) |>.mpr hCle
      rwa [centralizer_conj_smul, hcancel2 Y] at h1
    have hcHN : MulAut.conj c • H = N := by
      have hmem : MulAut.conj c • H ∈ maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) :=
        mem_maximalSubgroupsContaining.mpr ⟨isCoatom_conj_smul (mem_maximalSubgroups.mp hHmax), hCYle⟩
      rw [hN_sing] at hmem; exact Set.eq_of_mem_singleton hmem
    exact ⟨c, hcHN⟩
  -- Extract a line `Y` from the nontrivial intersection and finish.
  rcases hmatch with hne | hne
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
      (fun h => hne (Subgroup.eq_bot_of_card_eq _ h))
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hyord' : orderOf (y : G) = p :=
      (orderOf_injective _ (MulAut.conj c • Lstar ⊓ K).subtype_injective y).trans hyord
    have hYcard : Nat.card ↥(Subgroup.zpowers (y : G)) = p := by rw [Nat.card_zpowers, hyord']
    have hYea : Subgroup.zpowers (y : G) ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
    have hYS : Subgroup.zpowers (y : G) ≤ MulAut.conj c • Lstar ⊓ K :=
      Subgroup.zpowers_le.mpr y.2
    exact Or.inr (hfinish hp hYea (hYS.trans inf_le_left)
      (typeP_partner_centralizer_singleton hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
        hYea (hYS.trans inf_le_right)))
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
      (fun h => hne (Subgroup.eq_bot_of_card_eq _ h))
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hyord' : orderOf (y : G) = p :=
      (orderOf_injective _ (MulAut.conj c • Lstar ⊓ Kstar).subtype_injective y).trans hyord
    have hYcard : Nat.card ↥(Subgroup.zpowers (y : G)) = p := by rw [Nat.card_zpowers, hyord']
    have hYea : Subgroup.zpowers (y : G) ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
    have hYS : Subgroup.zpowers (y : G) ≤ MulAut.conj c • Lstar ⊓ Kstar :=
      Subgroup.zpowers_le.mpr y.2
    exact Or.inl (hfinish hp hYea (hYS.trans inf_le_left)
      ((typeP_structure hG hM hP hKM hK hKstar hU).2.2.2.2.2.1 p hp _ hYea (hYS.trans inf_le_right)))

/-- A Hall `κ(N)`-subgroup `K'` of a maximal `N`, lying inside a nilpotent subgroup `W`, is cyclic.
Since `κ(N) ⊆ τ₁(N) ∪ τ₃(N)`, every prime `p ∣ |K'|` has `pRank N p = 1`, so `pRank K' p ≤ 1`
(`= 0` off `π(K')`); and `K' ≤ W` nilpotent makes `K'` nilpotent.  An odd nilpotent group with
`pRank ≤ 1` everywhere is cyclic (`isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one`).  Used to
make both Hall factors of `Z` cyclic in `typeP_Z_isCyclic`. -/
theorem isCyclic_kappaHall_of_le_nilpotent [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {N K' W : Subgroup G} (hK'N : K' ≤ N)
    (hK'_hall : Ch03.IsHallSubgroup (kappa N) (K'.subgroupOf N))
    (hK'W : K' ≤ W) [Group.IsNilpotent ↥W] : IsCyclic ↥K' := by
  haveI : Group.IsNilpotent ↥K' :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK'W)
  have hodd : Odd (Nat.card ↥K') :=
    hG.odd.of_dvd_nat ((Subgroup.card_dvd_of_le hK'N).trans (Subgroup.card_subgroup_dvd_card N))
  refine isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one hodd fun p hp => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hpK : p ∈ (Nat.card ↥K').primeFactors
  · have hpκ : p ∈ kappa N := hK'_hall.1 p (by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'N).toEquiv])
    have hpτ : pRank ↥N p = 1 := hpκ.2.1.elim tau1_pRank_eq_one tau3_pRank_eq_one
    exact le_trans (pRank_le_of_injective (Subgroup.inclusion_injective hK'N)) (le_of_eq hpτ)
  · by_contra hcon
    exact hpK (OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega))

/-- For a type-`P₂` maximal subgroup `M`, the `σ`-core `M_σ` is nilpotent.  Since `κ(M)` always
satisfies `κ(M) ⊆ π(M) ∖ σ(M)` and `IsTypeP2` makes this inclusion *proper*, there is a prime
`p ∈ π(M) ∖ (σ(M) ∪ κ(M))`; a maximal-rank elementary abelian `p`-subgroup `A ≤ M` then meets the
hypotheses of Lemma 14.1 (`msigma_structure_of_notMem_sigma_kappa`: `p ∈ π(M)`, `p ∉ σ(M)`,
`p ∉ κ(M)`, `A ∈ ℰ_p^{r_p(M)}`), whose third conclusion is `IsNilpotent M_σ`.  This drives the
cyclicity of `Z = K ⊔ K*` in `typeP_Z_isCyclic` (BG 14.7(d)). -/
theorem msigma_isNilpotent_of_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M) :
    Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  classical
  -- `κ(M) ⊆ π(M) ∖ σ(M)`: every prime in `κ(M)` divides `|M|` (a rank-one witness `P ≤ M` has
  -- order `p`) and avoids `σ(M)` (`κ ⊆ σ′`).  `IsTypeP2` makes the inclusion proper.
  have hsub : kappa M ⊆ sigmaComplementPrimes M := by
    intro p hp
    obtain ⟨hp_prime, _, P, hPelem, hPM, _⟩ := id hp
    have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
    refine ⟨Nat.mem_primeFactors.mpr ⟨hp_prime, ?_, Nat.card_pos.ne'⟩, kappa_subset_sigmaCompl hp⟩
    rw [← hPcard]; exact Subgroup.card_dvd_of_le hPM
  obtain ⟨p, hpπ, hpκ⟩ := Set.exists_of_ssubset (ssubset_of_subset_of_ne hsub hP2.2)
  obtain ⟨hpM, hpσ⟩ := hpπ
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpM
  haveI : Fact p.Prime := ⟨hp⟩
  -- A maximal-rank elementary abelian `p`-subgroup `A = B.map M.subtype ≤ M`.
  obtain ⟨B, hBea, hBlog⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥M) (p := p)
      (n := pRank ↥M p) (one_le_pRank_of_mem_primeFactors hpM) (le_refl _)
  obtain ⟨j, hj⟩ := hBea.isPGroup.exists_card_eq
  have hjeq : j = pRank ↥M p := by
    have hsq := le_antisymm (le_pRank B hBea) hBlog
    rwa [hj, Nat.log_pow hp.one_lt] at hsq
  have hAmem : B.map M.subtype ∈ elemAbelianOfRank G p (pRank ↥M p) := by
    refine ⟨Subgroup.IsElementaryAbelian.map M.subtype_injective hBea, ?_⟩
    rw [Subgroup.card_map_of_injective M.subtype_injective, hj, hjeq]
  exact (msigma_structure_of_notMem_sigma_kappa hG hM hpM hpσ hpκ hAmem
    (Subgroup.map_subtype_le _)).2.2

/-- **BG Theorem 14.7, cyclicity of `Z = K ⊔ K*`** (mmd L4041, conjunct (d)): for a type-`P`
maximal `M` with its nonconjugate partner `M*` (the unique other member of the `Z`-family), the
group `Z = K ⊔ K*` is cyclic.  By `isTypeP2_or_isTypeP2_partner` one of `M`, `M*` is type-`P₂`;
in either case the Hall `κ`-factor of the `P₂` member has prime order (cyclic, `typeP_structure`
clause (g)), while the other factor is a Hall `κ`-subgroup of the partner lying inside the
*nilpotent* `σ`-core of the `P₂` member (`msigma_isNilpotent_of_isTypeP2` +
`isCyclic_kappaHall_of_le_nilpotent`, whose Hall-witness `N` and nilpotent ambient `W` differ).
Two coprime cyclic factors give `Z` cyclic (`isCyclic_kappaHall_sup_Kstar_of_cyclic`). -/
theorem typeP_Z_isCyclic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    IsCyclic ↥(K ⊔ Kstar) := by
  classical
  -- Partner symmetry: `K*` is Hall `κ(M*)` of `M*`, and `K = C_{M*_σ}(K*)`.
  obtain ⟨hMstarmax, hMstarP, hKstarMstar, hKstar_hall, hKeq⟩ :=
    typeP_partner_structure hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  rcases isTypeP2_or_isTypeP2_partner hG D hM hP hKM hK hKstar hU hpart with hM2 | hMstar2
  · -- `M` is type-`P₂`: `|K|` prime ⟹ `K` cyclic; `K* ≤ M_σ` (nilpotent) ⟹ `K*` cyclic.
    obtain ⟨q, hq, hKq, -⟩ := ((typeP_structure hG hM hP hKM hK hKstar hU).2.2.2.2.1 hM2).2
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : IsCyclic ↥K := isCyclic_of_prime_card hKq
    haveI : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      msigma_isNilpotent_of_isTypeP2 hG hM hM2
    haveI : IsCyclic ↥Kstar :=
      isCyclic_kappaHall_of_le_nilpotent hG hKstarMstar hKstar_hall (hKstar.le.trans inf_le_left)
    exact isCyclic_kappaHall_sup_Kstar_of_cyclic hKM hK hKstar
  · -- `M*` is type-`P₂`: `|K*|` prime ⟹ `K*` cyclic; `K ≤ M*_σ` (nilpotent) ⟹ `K` cyclic.
    haveI : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstarmax
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mstar)
      ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
    have hUeq : (U'.map Mstar.subtype).subgroupOf Mstar = U' :=
      Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective U'
    have hUstar : Ch03.IsHallSubgroup ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
        ((U'.map Mstar.subtype).subgroupOf Mstar) := by rw [hUeq]; exact hU'
    obtain ⟨q, hq, hKstarq, -⟩ :=
      ((typeP_structure hG hMstarmax hMstarP hKstarMstar hKstar_hall hKeq hUstar).2.2.2.2.1
        hMstar2).2
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : IsCyclic ↥Kstar := isCyclic_of_prime_card hKstarq
    haveI : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma Mstar) :=
      msigma_isNilpotent_of_isTypeP2 hG hMstarmax hMstar2
    haveI : IsCyclic ↥K :=
      isCyclic_kappaHall_of_le_nilpotent hG hKM hK (hKeq.le.trans inf_le_left)
    have hcyc : IsCyclic ↥(Kstar ⊔ K) :=
      isCyclic_kappaHall_sup_Kstar_of_cyclic hKstarMstar hKstar_hall hKeq
    rw [sup_comm]; exact hcyc

/-- **BG Theorem 14.7, the unique nonconjugate partner `M*`** (mmd L3962-3971, parts (1)-(7) +
appendix item (4)): for a type-`P` maximal `M`, there is a *unique* maximal subgroup `M*` that is
type-`P`, nonconjugate to `M`, has `K*` as a Hall `κ(M*)`-subgroup with `K = C_{M*_σ}(K*)`, makes
`Z = K ⊔ K*` cyclic with `Ẑ` a TI-set, has one of `M`, `M*` type-`P₂`, and covers every type-`P`
maximal up to conjugacy.

Existence is the canonical partner of `exists_partner`, its data assembled from
`typeP_partner_structure` (maximal/type-P/`K* ≤ M*`/Hall `κ(M*)`/`K = C_{M*_σ}(K*)`),
`typeP_family_pairwise_nonconjugate`, `typeP_Z_isCyclic`, `typeP_zTilde_isTI`,
`isTypeP2_or_isTypeP2_partner`, and `typeP_covering`.

**Uniqueness** turns on the partner-symmetry conjunct `K = C_{M*_σ}(K*)` (BG 14.7(3), appendix (4)):
it makes `K` the `K*`-role subgroup of any competitor `M*'`, so Proposition 14.2(c) for `M*'`
(`typeP_structure`, last conjunct) gives `ℳ(C_G(X)) = {M*'}` for a line `X ∈ ℰ¹(K)`, which also
equals `{M*}` (Theorem 14.7(1), `typeP_partner_centralizer_singleton`), forcing `M*' = M*`.

The partner-symmetry conjunct is *essential*: without it the `∃!` is false, since
`M*' := (M*)ᵈ` for `d ∈ N_{M_σ}(K*) ∖ K*` (which exists when `M_σ` is nilpotent and `K* ⊊ M_σ`,
e.g. `M` type-`P₂`) is nonconjugate to `M*`, still has `K*` Hall `κ(M*')` (as `d` normalizes `K*`),
and satisfies every other conjunct, yet `M*' ≠ M*`. -/
theorem typeP_partner_existsUnique [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∃! Mstar : Subgroup G,
      Mstar ∈ maximalSubgroups G ∧ IsTypeP Mstar ∧ ¬ IsConjugateSubgroup M Mstar ∧
      (Kstar ≤ Mstar ∧ Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar) ∧
        K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G)) ∧
      IsCyclic ↥(K ⊔ Kstar) ∧ IsTISubset (zTilde K Kstar) (K ⊔ Kstar) ∧
      (IsTypeP2 M ∨ IsTypeP2 Mstar) ∧
      (∀ H : Subgroup G, H ∈ maximalSubgroups G → IsTypeP H →
        IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar) := by
  classical
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ := exists_partner hG D hM hP hKM hK hKstar hU
  obtain ⟨hMstarmax, hMstarP, hKstarMstar, hKstar_hall, hKeq⟩ :=
    typeP_partner_structure hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  -- A line `X = ⟨x⟩ ∈ ℰ¹(K)` (needed for both the existence data and the uniqueness pin).
  obtain ⟨p, hpκ⟩ := id hP
  have hp : p.Prime := prime_of_mem_kappa hpκ
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : p ∣ Nat.card ↥K := by
    obtain ⟨_, _, P, hPelem, hPM, _⟩ := id hpκ
    have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
    have hpdvdM : p ∣ Nat.card ↥M := by rw [← hPcard]; exact Subgroup.card_dvd_of_le hPM
    have hsplit : p ∣ Nat.card ↥(K.subgroupOf M) * (K.subgroupOf M).index := by
      rw [Subgroup.card_mul_index]; exact hpdvdM
    have hpKsub : p ∣ Nat.card ↥(K.subgroupOf M) := by
      rcases hp.dvd_mul.mp hsplit with h | h
      · exact h
      · exact absurd hpκ (hK.2 p (Nat.mem_primeFactors.mpr
          ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hpKsub
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxord : orderOf (x : G) = p := (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
  have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
  -- `ℳ(C_G(X)) = {M*}` (Theorem 14.7(1)).
  have h0 : maximalSubgroupsContaining (Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G))
      = {Mstar} :=
    typeP_partner_centralizer_singleton hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart hXelem hXK
  refine ⟨Mstar, ⟨hMstarmax, hMstarP,
    typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU (Or.inl rfl) hMstarmem
      (Ne.symm hMstarne),
    ⟨hKstarMstar, hKstar_hall, hKeq⟩,
    typeP_Z_isCyclic hG D hM hP hKM hK hKstar hU hMstarmem hMstarne hpart,
    typeP_zTilde_isTI hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart,
    isTypeP2_or_isTypeP2_partner hG D hM hP hKM hK hKstar hU hpart,
    fun H hHmax hHP =>
      typeP_covering hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart hHmax hHP⟩, ?_⟩
  -- Uniqueness: any competitor `M*'` satisfies `ℳ(C_G(X)) = {M*'}` via the partner symmetry.
  rintro Mstar' ⟨hMstar'max, hMstar'P, -, ⟨hKstarMstar', hKstar'_hall, hKeq'⟩, -, -, -, -⟩
  haveI : IsSolvable ↥Mstar' := hG.solvable_of_mem_maximalSubgroups hMstar'max
  obtain ⟨U'', hU''⟩ := Ch03.hall_E_exists (G := ↥Mstar')
    ((kappa Mstar' ∪ OddOrder.BG.Ch3.S10.sigma Mstar')ᶜ)
  have hU''eq : (U''.map Mstar'.subtype).subgroupOf Mstar' = U'' :=
    Subgroup.comap_map_eq_self_of_injective Mstar'.subtype_injective U''
  have hUstar' : Ch03.IsHallSubgroup ((kappa Mstar' ∪ OddOrder.BG.Ch3.S10.sigma Mstar')ᶜ)
      ((U''.map Mstar'.subtype).subgroupOf Mstar') := by rw [hU''eq]; exact hU''
  have h' : maximalSubgroupsContaining (Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G))
      = {Mstar'} :=
    (typeP_structure hG hMstar'max hMstar'P hKstarMstar' hKstar'_hall hKeq' hUstar').2.2.2.2.2.1
      p hp _ hXelem hXK
  have hmem : Mstar' ∈ maximalSubgroupsContaining
      (Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G)) := by
    rw [h']; exact Set.mem_singleton _
  rw [h0, Set.mem_singleton_iff] at hmem
  exact hmem

/-- **Derived subgroup via a `σ`-complement** (BG 14.7(h), Proposition 14.2(a) skeleton, mmd L4061):
for any §12 `E`-setup of `M` (so `M = M_σ ⋊ E`), the derived subgroup `M' = [M,M]` equals
`M_σ ⊔ E'` where `E' = [E,E]` is the derived subgroup of the `σ(M)'`-complement.

`⊇` is `Msigma_le_derived` (`M_σ ≤ M'`) plus `commutator_mono` (`E' ≤ M'`).  For `⊆`, an element
`x ∈ M'` decomposes as `x = a·b` (`a ∈ M_σ`, `b ∈ E`) inside `↥M = M_σ ⋊ E`; then `b = a⁻¹x ∈ M'`
(both factors lie in the normal `M'`), so `b ∈ E ⊓ M' ≤ E'` by `inf_derivedInG_le_derivedInG`,
hence `x = a·b ∈ M_σ ⊔ E'`. -/
theorem derivedInG_eq_Msigma_sup_derivedInG_complement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) :
    derivedInG M = OddOrder.BG.Ch3.S10.Msigma M ⊔ derivedInG E := by
  classical
  have hM := h.mem_maximal
  have hMσM' : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  refine le_antisymm (fun x hx => ?_) (sup_le hMσM' ?_)
  · have hxM : x ∈ M := Subgroup.map_subtype_le _ hx
    haveI : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hsuptop : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊔ E.subgroupOf M = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) h.E_le,
        h.E_compl_sup, Subgroup.subgroupOf_self]
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
      (hsuptop ▸ Subgroup.mem_top (⟨x, hxM⟩ : ↥M))
    have hs : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := Subgroup.mem_subgroupOf.mp ha
    have he : (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hb
    have hse : (a : G) * (b : G) = x := by
      have hh := congrArg Subtype.val hab; simpa using hh
    have hbM' : (b : G) ∈ derivedInG M := by
      have hbeq : (b : G) = (a : G)⁻¹ * x := by rw [← hse]; group
      rw [hbeq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hMσM' hs)) hx
    have hbdE : (b : G) ∈ derivedInG E :=
      h.inf_derivedInG_le_derivedInG (Subgroup.mem_inf.mpr ⟨he, hbM'⟩)
    rw [← hse]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hbdE)
  · rw [show derivedInG E = ⁅E, E⁆ from Subgroup.map_subtype_commutator E,
      show derivedInG M = ⁅M, M⁆ from Subgroup.map_subtype_commutator M]
    exact Subgroup.commutator_mono h.E_le h.E_le

/-- **part (h), degenerate case `K = E`** (BG 14.7(8), mmd L4061 with `U = 1`): if the Hall
`κ(M)`-subgroup `K` equals the whole `σ(M)'`-complement `E` (the case `κ(M) ∩ τ₃(M) ≠ ∅` of
Proposition 14.2(a), or `E₂E₃ = 1`), then `E = K` is cyclic, so `E' = 1` and `M' = M_σ`;
the `M_σ ⋊ E` structure makes `K = E` a complement of `M' = M_σ`. -/
theorem typeP_derivedInG_complement_of_eq_complement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ K : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hKE : K = E) [IsCyclic ↥K] :
    Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) := by
  classical
  -- `E = K` is cyclic, hence abelian, so `E' = ⁅E,E⁆ = ⊥`.
  have hEbot : derivedInG E = ⊥ := by
    rw [← hKE, show derivedInG K = ⁅K, K⁆ from Subgroup.map_subtype_commutator K]
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (fun x hx => ?_)
    letI : CommGroup ↥K := IsCyclic.commGroup
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : ↥K) (⟨x, hx⟩ : ↥K))
  -- `M' = M_σ ⊔ E' = M_σ`.
  have hM'eq : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M := by
    rw [derivedInG_eq_Msigma_sup_derivedInG_complement hG h, hEbot, sup_bot_eq]
  rw [hM'eq, hKE]
  exact h.isComplement'_subgroupOf

/-- **BG Theorem 14.7(h) core, `M'` complements `K`** (mmd L4061): for a type-`P` maximal `M`
with Hall `κ(M)`-subgroup `K` *cyclic* (the counting collapse `n = 1` of Theorem 14.7 makes
`Z = K × K*` cyclic, hence `K`), the derived subgroup `M' = [M,M]` is a complement of `K` in `M`.

By Proposition 14.2(a): take a §12 `E`-setup with `K ≤ E`.  If `κ(M) ∩ τ₃(M) ≠ ∅` then `K = E`
(`typeP_derivedInG_complement_of_eq_complement`).  Otherwise `κ(M) ⊆ τ₁(M)`; conjugate so `K = E₁`,
and (when `E₂E₃ = 1`) again `K = E`, or (`E₂E₃ ≠ 1`) `E = K ⋉ U` is Frobenius with `U = E₂E₃ = E'`
(`U = [U,K]` by the coprime regular action `le_commutator_of_coprime_inf_centralizer_eq_bot`), so
`M' = M_σ ⊔ U`; coprimality (`κ` vs `σ ∪ τ₂ ∪ τ₃`) gives `M' ⊓ K = 1`, and `U ⋊ K = E`,
`M_σ ⋊ E = M` give `M' · K = M`. -/
theorem typeP_derivedInG_isComplement_kappaHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) [IsCyclic ↥K] :
    Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) := by
  classical
  -- `K` is a `σ(M)'`-subgroup (a Hall `κ(M)`-subgroup, and `κ(M) ⊆ σ(M)'`).
  have hK_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
    exact kappa_subset_sigmaCompl (hK.1 p hp)
  obtain ⟨E, E₁, E₂, E₃, hsetup, hKE, hE_pi⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hKM hK_pi
  by_cases hτ3 : (kappa M ∩ tau3 M).Nonempty
  · -- Case `κ(M) ∩ τ₃(M) ≠ ∅`: `K = E`.
    obtain ⟨p, hpmem⟩ := hτ3
    rw [Set.mem_inter_iff] at hpmem
    obtain ⟨hpκ, hpτ3⟩ := hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors ((mem_tau3_iff M p).mp hpτ3).2.1
    obtain ⟨hE3ne, hreg⟩ := E3_not_regular_of_mem_kappa_tau3 hG hsetup hp hpκ hpτ3
    obtain ⟨hE1ne, hEeq, hEprime, hEnorm⟩ := E3_not_regular_consequences hG hsetup hE3ne hreg
    obtain ⟨x, hxE3, hxne, hxC⟩ : ∃ x ∈ E₃, x ≠ 1 ∧
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hreg fun y hy hy1 => hcon y hy hy1
    have hEpi : Ch03.Subgroup.IsPiGroup (kappa M) (E.subgroupOf M) := by
      intro q hq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv] at hq
      exact mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hq
    have hEdvdK : Nat.card ↥E ∣ Nat.card ↥K := by
      have hd := hK.card_dvd_of_isPiGroup hEpi
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hd
    have hKEeq : K = E :=
      Subgroup.eq_of_le_of_card_ge hKE (Nat.dvd_antisymm hEdvdK (Subgroup.card_dvd_of_le hKE)).le
    exact typeP_derivedInG_complement_of_eq_complement hG hsetup hKEeq
  · -- Case `κ(M) ⊆ τ₁(M)`: conjugate the setup so its `E₁` is `K`.
    haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hsetup.mem_maximal
    have hκτ1 : ∀ p ∈ kappa M, p ∈ tau1 M := fun p hpκ =>
      (kappa_subset_tau1_union_tau3 hpκ).resolve_right
        (fun hpτ3 => hτ3 ⟨p, Set.mem_inter hpκ hpτ3⟩)
    obtain ⟨p₀, hp₀κ⟩ := hP
    obtain ⟨hE1ne, hE1nonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG hsetup
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG hsetup hE1ne
    have hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥ :=
      Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hE1prime (le_refl E₁) hE1nonreg
    have hE1HallκE : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf E) :=
      ⟨fun p hp => mem_kappa_of_mem_primeFactors_card_E1 hG hsetup hE1prime hCE1
          (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₁_le).toEquiv] at hp),
        fun p hp hpκ => hsetup.E₁_hall.2 p hp (hκτ1 p hpκ)⟩
    have hE1Hallκ : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf M) :=
      hallPiece_isHall_in_M hG hsetup hsetup.E₁_le hE1HallκE kappa_subset_sigmaCompl
    obtain ⟨w, hwM, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hMsolv
      (hsetup.E₁_le.trans hsetup.E_le) hKM hE1Hallκ hK
    have h' := SubgroupESetup.conj' hsetup hwM
    rw [hw] at h'
    set Ebar := MulAut.conj w • E with hEbardef
    set Ebar₂ := MulAut.conj w • E₂ with hEbar₂def
    set Ebar₃ := MulAut.conj w • E₃ with hEbar₃def
    -- `h' : SubgroupESetup M Ebar K Ebar₂ Ebar₃`.
    by_cases hUbot : (Ebar₂ ⊔ Ebar₃ : Subgroup G) = ⊥
    · -- `Ebar = K`, so `M' = M_σ` and `K = Ebar` complements it.
      have hEbarK : K = Ebar := by
        have hsup := h'.eq_sup hG
        rw [sup_assoc, hUbot, sup_bot_eq] at hsup
        exact hsup.symm
      exact typeP_derivedInG_complement_of_eq_complement hG h' hEbarK
    · -- `E = K ⋉ U` is a Frobenius group with `U = Ebar₂ ⊔ Ebar₃ ≠ 1`, and `U = E' = [E,E]`.
      have hUleE : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ≤ Ebar := sup_le h'.E₂_le h'.E₃_le
      have hKleEbar : K ≤ Ebar := h'.E₁_le
      obtain ⟨hKne, hKnonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG h'
        (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
      have hKprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K := E1_actsPrime hG h' hKne
      have hKstar' : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ :=
        Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
      have hfrob := isFrobeniusGroup_E_of_caseTau1 hG h' hKne hKstar' hτ3 hUbot
      have hcompl_Ebar : ((Ebar₂ ⊔ Ebar₃).subgroupOf Ebar).IsComplement' (K.subgroupOf Ebar) :=
        hfrob.isComplement
      -- coprime `|K|`, `|U|` and `U ⊓ C(K) = ⊥` (regular action of `K = E₁` on `U`).
      have hcopKU : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(Ebar₂ ⊔ Ebar₃)) := by
        have hc := (hfrob.coprime_card_kernel_complement).symm
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleEbar).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleE).toEquiv] at hc
      have hCUK : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
        obtain ⟨⟨g₀, hg₀K⟩, hg₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
        have hg₀1 : g₀ ≠ 1 := fun hc => hg₀ne (Subtype.ext hc)
        have hr := actsRegularlyOn_E23_E1_of_caseTau1 hG h' hKne hKstar' hτ3 g₀ hg₀K hg₀1
        rw [fixedByElement_def] at hr
        rw [eq_bot_iff, ← hr]
        exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hg₀K))
      -- `U = [K, U] ≤ E' = derivedInG Ebar`.
      haveI hKsolv : IsSolvable ↥K :=
        solvable_of_solvable_injective (Subgroup.inclusion_injective (hKleEbar.trans h'.E_le))
      have hUleE' : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ≤ derivedInG Ebar := by
        have hUcomm : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ≤ ⁅K, Ebar₂ ⊔ Ebar₃⁆ :=
          OddOrder.BG.Ch2.S08.le_commutator_of_coprime_inf_centralizer_eq_bot
            (hKleEbar.trans (h'.E23_normal hG)) hcopKU hCUK
        have hcomm_le : (⁅K, Ebar₂ ⊔ Ebar₃⁆ : Subgroup G) ≤ ⁅Ebar, Ebar⁆ :=
          Subgroup.commutator_mono hKleEbar hUleE
        exact hUcomm.trans (le_of_le_of_eq hcomm_le (Subgroup.map_subtype_commutator Ebar).symm)
      -- `E' = U`: the abstract `commutator_eq_sup` for `Ebar = K ⋉ U` with `K` cyclic.
      have hcommEbar_eq : (derivedInG Ebar).subgroupOf Ebar = commutator ↥Ebar := by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective Ebar.subtype_injective]
      have hdEbar : derivedInG Ebar = (Ebar₂ ⊔ Ebar₃ : Subgroup G) := by
        haveI hUnorm : ((Ebar₂ ⊔ Ebar₃).subgroupOf Ebar).Normal :=
          Subgroup.normal_subgroupOf_of_le_normalizer (h'.E23_normal hG)
        have hUcommE : (Ebar₂ ⊔ Ebar₃).subgroupOf Ebar ≤ commutator ↥Ebar := by
          rw [← hcommEbar_eq]; exact Subgroup.comap_mono hUleE'
        have hsupcomm := commutator_eq_sup_commutator_of_isComplement' hcompl_Ebar hUcommE
        have hKbarbot : ⁅K.subgroupOf Ebar, K.subgroupOf Ebar⁆ = ⊥ := by
          refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (fun x hx => ?_)
          letI : CommGroup ↥K := IsCyclic.commGroup
          refine Subgroup.mem_centralizer_iff.mpr (fun y hy => Subtype.ext ?_)
          have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
          have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
          have hcm := congrArg Subtype.val (mul_comm (⟨(y : G), hyK⟩ : ↥K) (⟨(x : G), hxK⟩ : ↥K))
          simpa using hcm
        rw [hKbarbot, sup_bot_eq] at hsupcomm
        rw [show derivedInG Ebar = (commutator ↥Ebar).map Ebar.subtype from rfl, hsupcomm,
          Subgroup.map_subgroupOf_eq_of_le hUleE]
      -- `M' = M_σ ⊔ U`.
      have hM'eq : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M ⊔ (Ebar₂ ⊔ Ebar₃) := by
        rw [derivedInG_eq_Msigma_sup_derivedInG_complement hG h', hdEbar]
      have hcommM : (derivedInG M).subgroupOf M = commutator ↥M := by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
      have hdEbarM : derivedInG Ebar ≤ derivedInG M := by
        rw [show derivedInG Ebar = ⁅Ebar, Ebar⁆ from Subgroup.map_subtype_commutator Ebar,
          show derivedInG M = ⁅M, M⁆ from Subgroup.map_subtype_commutator M]
        exact Subgroup.commutator_mono h'.E_le h'.E_le
      have hUleM' : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ≤ derivedInG M := hdEbar ▸ hdEbarM
      -- `M' ⊓ K = ⊥` (coprime `κ` vs `σ ∪ τ₂ ∪ τ₃`, via `M' ⊓ K ≤ E' ⊓ K = U ⊓ K`).
      have hMKbot : derivedInG M ⊓ K = ⊥ := by
        have hle1 : derivedInG M ⊓ K ≤ derivedInG Ebar :=
          (inf_le_inf_left (derivedInG M) hKleEbar).trans
            (by rw [inf_comm]; exact h'.inf_derivedInG_le_derivedInG)
        have hbot2 : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ⊓ K = ⊥ := by
          rw [inf_comm]; exact Subgroup.inf_eq_bot_of_coprime hcopKU
        exact le_bot_iff.mp ((le_inf (hle1.trans hdEbar.le) inf_le_right).trans hbot2.le)
      -- `M' ⊔ K = M` (`U ⊔ K = Ebar`, `M_σ ⊔ Ebar = M`).
      have hUKsup : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ⊔ K = Ebar := by
        have hsup := hcompl_Ebar.sup_eq_top
        rw [← Subgroup.subgroupOf_sup hUleE hKleEbar] at hsup
        exact le_antisymm (sup_le hUleE hKleEbar) (Subgroup.subgroupOf_eq_top.mp hsup)
      have hMKsup : derivedInG M ⊔ K = M := by
        refine le_antisymm (sup_le (Subgroup.map_subtype_le _) hKM) ?_
        calc M = OddOrder.BG.Ch3.S10.Msigma M ⊔ Ebar := h'.E_compl_sup.symm
          _ ≤ derivedInG M ⊔ K := by
              refine sup_le ((OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM).trans le_sup_left) ?_
              rw [← hUKsup]
              exact sup_le (hUleM'.trans le_sup_left) le_sup_right
      -- Assemble the complement: disjoint + product covers `↥M` (`M'` normal).
      have hderM_le : derivedInG M ≤ M := Subgroup.map_subtype_le _
      rw [hcommM]
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · rw [disjoint_iff, ← hcommM,
          show (derivedInG M).subgroupOf M ⊓ K.subgroupOf M
            = (derivedInG M ⊓ K).subgroupOf M from rfl, hMKbot, Subgroup.bot_subgroupOf]
      · have hsuptop : commutator ↥M ⊔ K.subgroupOf M = ⊤ := by
          rw [← hcommM, ← Subgroup.subgroupOf_sup hderM_le hKM, hMKsup, Subgroup.subgroupOf_self]
        rw [← Subgroup.normal_mul, hsuptop, Subgroup.coe_top]

/-- **BG Theorem 14.7** (mmd L3890): type-P duality and the `Z_tilde` TI-set.

For a type-P maximal subgroup `M`, there is a unique nonconjugate type-P partner
`Mstar`.  The two Hall factors `K` and `Kstar` form a cyclic subgroup `Z`,
`Z_tilde` is a TI-set, one of the two partners is type `P2`, and every type-P
maximal subgroup is conjugate to one of the pair.

**Part (h)** (BG 14.7(8), exposed 2026-06-15 for Lane G §15 — issue 8006): `M' = [M,M]` is a
complement of `K` in `M` (`M = K M'`, `K ∩ M' = 1`), with `|M'|`, `|K|` coprime.  BG Cor 15.6
(mmd L4232) and Lemma 15.1 cite this directly; it is surfaced as the two leading conjuncts so
`§15` can apply it without re-deriving κ/τ prime-handling. -/
theorem typeP_duality [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) ∧
    Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M)) (Nat.card ↥(K.subgroupOf M)) ∧
    ∃! Mstar : Subgroup G,
      Mstar ∈ maximalSubgroups G ∧ IsTypeP Mstar ∧ ¬ IsConjugateSubgroup M Mstar ∧
      (Kstar ≤ Mstar ∧ Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar) ∧
        K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G)) ∧
      IsCyclic ↥(K ⊔ Kstar) ∧ IsTISubset (zTilde K Kstar) (K ⊔ Kstar) ∧
      (IsTypeP2 M ∨ IsTypeP2 Mstar) ∧
      (∀ H : Subgroup G, H ∈ maximalSubgroups G → IsTypeP H →
        IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar) := by
  classical
  -- A Hall `(κ(M) ∪ σ(M))'`-subgroup `U` of `M` (Hall's theorem in the solvable `M`).
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- The counting collapse `n = 1` makes `Z = K ⊔ K*` cyclic, hence the Hall `κ`-factor `K`
  -- cyclic (subgroup of a cyclic group); this is what Proposition 14.2(a)/part (h) consumes.
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ :=
    exists_partner hG (dummySigmaDecomposition G) hM hP hKM hK hKstar hU
  haveI hZcyc : IsCyclic ↥(K ⊔ Kstar) :=
    typeP_Z_isCyclic hG (dummySigmaDecomposition G) hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  haveI : IsCyclic ↥K :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ Kstar)).isCyclic.mp inferInstance
  -- Part (h): `M' = [M,M]` complements `K` in `M` (Proposition 14.2(a): `M' = U M_σ`).
  have hparth : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) :=
    typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hK
  exact ⟨hparth, coprime_card_derived_kappaHall_of_isComplement' hK hparth,
    typeP_partner_existsUnique hG (dummySigmaDecomposition G) hM hP hKM hK hKstar hU⟩

/-- **BG `kappaJ`** (conjugation-invariance of `κ`): `κ(M^g) = κ(M)`.  Each defining condition of
`κ` is conjugation-stable: `τ₁(M) ∪ τ₃(M) = {p | p ∉ σ(M) ∧ r_p(M) = 1}` (with `σ`, `pRank`
invariant), and a rank-one witness `P ≤ M` with `M_σ ⊓ C(P) ≠ 1` transports to `P^{g⁻¹}` (via
`M_σ`, centralizer, and `ℰ_p¹` equivariance).  A prerequisite for the type-`P₁`/`P₂`
conjugation-invariance used in BG Cor 14.12 (`typeP2_neighbor_is_typeF`, `sK_FD`). -/
theorem kappa_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    kappa (MulAut.conj g • M) = kappa M := by
  classical
  -- One inclusion for all `a, N` suffices; the reverse follows with `a := g⁻¹`, `N := M^g`.
  suffices h : ∀ (a : G) (N : Subgroup G), kappa (MulAut.conj a • N) ⊆ kappa N by
    refine le_antisymm (h g M) (fun p hp => ?_)
    have hMeq : MulAut.conj g⁻¹ • (MulAut.conj g • M) = M := by
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    exact h g⁻¹ (MulAut.conj g • M) (hMeq.symm ▸ hp)
  intro a N p hp
  obtain ⟨hpp, hτ, P, hPelem, hPN, hPC⟩ := hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hinv : MulAut.conj a⁻¹ • (MulAut.conj a • N) = N := by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  refine ⟨hpp, ?_, MulAut.conj a⁻¹ • P, conj_smul_mem_elemAbelianOfRank a⁻¹ hPelem, ?_, ?_⟩
  · -- `p ∈ τ₁(N) ∪ τ₃(N)`: from `hτ` extract `p ∉ σ ∧ r_p = 1`, transport, rebuild.
    have hcommon : p ∉ OddOrder.BG.Ch3.S10.sigma (MulAut.conj a • N) ∧
        pRank ↥(MulAut.conj a • N) p = 1 := by
      rcases hτ with h1 | h3
      · exact ⟨((mem_tau1_iff _ _).mp h1).1, ((mem_tau1_iff _ _).mp h1).2.2⟩
      · exact ⟨((mem_tau3_iff _ _).mp h3).1, ((mem_tau3_iff _ _).mp h3).2.2⟩
    have hσN : p ∉ OddOrder.BG.Ch3.S10.sigma N := by
      have h1 := hcommon.1; rwa [sigma_conj_smul_eq] at h1
    have hpRankN : pRank ↥N p = 1 := by
      have heq : pRank ↥N p = pRank ↥(MulAut.conj a • N) p :=
        pRank_eq_of_mulEquiv
          (Subgroup.equivMapOfInjective N (MulAut.conj a).toMonoidHom (MulAut.conj a).injective)
      rw [heq]; exact hcommon.2
    by_cases hπ : p ∈ (Nat.card ↥(derivedInG N)).primeFactors
    · exact Or.inr ((mem_tau3_iff _ _).mpr ⟨hσN, hπ, hpRankN⟩)
    · exact Or.inl ((mem_tau1_iff _ _).mpr ⟨hσN, hπ, hpRankN⟩)
  · -- `P^{a⁻¹} ≤ N` (apply `conj a⁻¹` to `P ≤ M^a`).
    rw [← hinv]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPN
  · -- `M_σ(N) ⊓ C(P^{a⁻¹}) ≠ ⊥` (apply `conj a⁻¹` to `M_σ(M^a) ⊓ C(P) ≠ ⊥`).
    have hbot : MulAut.conj a⁻¹ • (OddOrder.BG.Ch3.S10.Msigma (MulAut.conj a • N) ⊓
        Subgroup.centralizer (P : Set G)) ≠ ⊥ := by
      rw [Ne, pointwise_smul_eq_bot_iff]; exact hPC
    rwa [Subgroup.smul_inf, centralizer_pointwise_smul, ← coe_pointwise_smul,
      show MulAut.conj a⁻¹ • OddOrder.BG.Ch3.S10.Msigma (MulAut.conj a • N)
        = OddOrder.BG.Ch3.S10.Msigma N from by rw [← Msigma_conj_smul, hinv]] at hbot

/-- `π(M) ∖ σ(M)` (`sigmaComplementPrimes`) is conjugation-invariant. -/
theorem sigmaComplementPrimes_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    sigmaComplementPrimes (MulAut.conj g • M) = sigmaComplementPrimes M := by
  unfold sigmaComplementPrimes piSet
  rw [card_pointwise_smul, sigma_conj_smul_eq]

/-- **Type-`P` is conjugation-invariant** (`kappa_conj_smul`). -/
theorem isTypeP_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    IsTypeP (MulAut.conj g • M) ↔ IsTypeP M := by
  unfold IsTypeP; rw [kappa_conj_smul]

/-- **Type-`P₁` is conjugation-invariant**. -/
theorem isTypeP1_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    IsTypeP1 (MulAut.conj g • M) ↔ IsTypeP1 M := by
  unfold IsTypeP1
  rw [kappa_conj_smul, sigmaComplementPrimes_conj_smul, isTypeP_conj_smul]

/-- **A normal Hall subgroup is the unique Hall subgroup of its primes** (finite solvable group):
two Hall `π`-subgroups are conjugate (`hall_C`), and a normal one is fixed by conjugation, so they
coincide.  Used to pin the Theorem D normal complement `R(x)` (a normal Hall complement in `C_G(x)`)
to the canonical signalizer `Rsub`. -/
theorem eq_of_isHall_of_normal {K : Type*} [Group K] [Finite K] [IsSolvable K] {π : Set ℕ}
    {H₁ H₂ : Subgroup K} (hH₁ : Ch03.IsHallSubgroup π H₁) (hH₂ : Ch03.IsHallSubgroup π H₂)
    (hN : H₁.Normal) : H₁ = H₂ := by
  haveI := hN
  obtain ⟨g, hg⟩ := Ch03.hall_C hH₁ hH₂
  rw [← hg]
  exact (Subgroup.Normal.conj_smul_eq_self g H₁).symm

/-- **κ-Hall data transfers under conjugation of the ambient maximal**: if `conj g • N = M` and
`KN.subgroupOf N` is a Hall `κ(N)`-subgroup, then `(conj g • KN).subgroupOf M` is a Hall
`κ(M)`-subgroup.  Conjugation by `g` restricts to a `↥N ≃ ↥M` preserving both `Nat.card` and the
index, and `κ` is conjugation-invariant.  This is the fix-`W` data step: it lets a conjugate
type-`P` maximal's `Ẑ` be related to a fixed reference `Ẑ`. -/
theorem isHall_kappa_subgroupOf_conj [Finite G] (g : G) {M N KN : Subgroup G}
    (hg : MulAut.conj g • N = M) (hKNN : KN ≤ N)
    (hKN : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N)) :
    Ch03.IsHallSubgroup (kappa M) ((MulAut.conj g • KN).subgroupOf M) := by
  have hkap : kappa M = kappa N := by rw [← hg, kappa_conj_smul]
  have hle : MulAut.conj g • KN ≤ M := by
    rw [← hg]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKNN
  -- `Nat.card` is conjugation-invariant; the two `subgroupOf`s have equal card (both `= Nat.card KN`).
  have hcardKN : Nat.card ↥(MulAut.conj g • KN) = Nat.card ↥KN := by
    rw [Subgroup.pointwise_smul_def]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv).symm
  have hcardamb : Nat.card ↥(MulAut.conj g • N) = Nat.card ↥N := by
    rw [Subgroup.pointwise_smul_def]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv).symm
  have hcard : Nat.card ↥((MulAut.conj g • KN).subgroupOf M) = Nat.card ↥(KN.subgroupOf N) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKNN).toEquiv, hcardKN]
  -- the indices agree, via `index · card = card ambient` and the card equalities above.
  have hidx : ((MulAut.conj g • KN).subgroupOf M).index = (KN.subgroupOf N).index := by
    have hMrel := ((MulAut.conj g • KN).subgroupOf M).index_mul_card
    have hNrel := (KN.subgroupOf N).index_mul_card
    have hMN : Nat.card ↥M = Nat.card ↥N := by rw [← hg]; exact hcardamb
    rw [hcard, hMN] at hMrel
    rw [← hNrel] at hMrel
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hMrel
  unfold Ch03.IsHallSubgroup at hKN ⊢
  rw [hkap, hcard, hidx]; exact hKN

/-- **fix-`W` threading**: two conjugate type-`P` maximals `N ~ M` carry `Ẑ`'s with the same
`G`-conjugacy-class closure.  Concretely, if `N` and `M` carry Theorem 14.7 data
`(KN, KstarN)` resp. `(K, Kstar)` and `N` is `G`-conjugate to `M`, then
`𝒞_G(zTilde KN KstarN) = 𝒞_G(zTilde K Kstar)`.  The conjugator `g` (`conj g • N = M`) is corrected
by a Hall conjugacy `w ∈ M` so that `conj (w*g)` carries `N`'s data exactly onto `M`'s; the
`conjClassSet` is then conjugation-invariant via `conjClassSet_zTilde_conj_eq`. -/
theorem conjClassSet_zTilde_eq_of_isConjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N K Kstar KN KstarN : Subgroup G}
    (hMmax : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hNmax : N ∈ maximalSubgroups G) (hKNN : KN ≤ N)
    (hKN : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N))
    (hKstarN : KstarN = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G))
    (hconj : IsConjugateSubgroup N M) :
    conjClassSet (zTilde KN KstarN) = conjClassSet (zTilde K Kstar) := by
  obtain ⟨g, hg⟩ := hconj
  have hle : MulAut.conj g • KN ≤ M := by
    rw [← hg]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKNN
  have hHallM : Ch03.IsHallSubgroup (kappa M) ((MulAut.conj g • KN).subgroupOf M) :=
    isHall_kappa_subgroupOf_conj g hg hKNN hKN
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hMmax
  obtain ⟨w, hwM, hw⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hle hKM hHallM hK
  -- `conj (w*g)` carries `N`'s `κ`-Hall and ambient maximal exactly onto `M`'s.
  have hKeq : MulAut.conj (w * g) • KN = K := by rw [map_mul, mul_smul]; exact hw
  have hMN : MulAut.conj (w * g) • N = M := by
    rw [map_mul, mul_smul, hg]
    exact conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hwM)
  -- hence it carries `KstarN = N_σ ∩ C(KN)` onto `Kstar = M_σ ∩ C(K)`.
  have hKstareq : MulAut.conj (w * g) • KstarN = Kstar := by
    rw [hKstarN, Subgroup.smul_inf, centralizer_pointwise_smul, ← coe_pointwise_smul, hKeq, hKstar]
    congr 1
    rw [← Msigma_conj_smul, hMN]
  -- `conjClassSet` is conjugation-invariant on `Ẑ`.
  calc conjClassSet (zTilde KN KstarN)
      = conjClassSet (zTilde (MulAut.conj (w * g) • KN) (MulAut.conj (w * g) • KstarN)) :=
        (conjClassSet_zTilde_conj_eq (w * g) KN KstarN).symm
    _ = conjClassSet (zTilde K Kstar) := by rw [hKeq, hKstareq]

/-- **fix-`W`** (BG Cor 14.8 packaging): for a reference type-`P` maximal `M` (with Theorem 14.7
data `K, K*, U`) and *any* type-`P` maximal `N` (with data `KN, KstarN`), the `Ẑ` of `N` has the
same `G`-conjugacy-class closure as the fixed `Ẑ(M) = zTilde K K*`.  Every type-`P` `N` is
`G`-conjugate to `M` or to its partner `M*` (`typeP_covering`); the `M`-class lands on `W` by
`conjClassSet_zTilde_eq_of_isConjugate`, and the `M*`-class lands on `zTilde K* K = zTilde K K*`
(`typeP_partner_structure` supplies `M*`'s data `(K*, K)`, then `zTilde_comm`). -/
theorem conjClassSet_zTilde_eq_fixed_of_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U N KN KstarN : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hNmax : N ∈ maximalSubgroups G) (hNP : IsTypeP N) (hKNN : KN ≤ N)
    (hKN : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N))
    (hKstarN : KstarN = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) :
    conjClassSet (zTilde KN KstarN) = conjClassSet (zTilde K Kstar) := by
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ :=
    exists_partner hG (genuineSigmaDecomposition hG) hM hP hKM hK hKstar hU
  obtain ⟨hMstarmax, hMstarP, hKstarMstar, hKstar_hall, hKeq⟩ :=
    typeP_partner_structure hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  rcases typeP_covering hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart hNmax hNP with
    hNM | hNMstar
  · exact conjClassSet_zTilde_eq_of_isConjugate hG hM hKM hK hKstar hNmax hKNN hKN hKstarN hNM
  · rw [conjClassSet_zTilde_eq_of_isConjugate hG hMstarmax hKstarMstar hKstar_hall hKeq
      hNmax hKNN hKN hKstarN hNMstar, zTilde_comm]

/-- **Type-`P` data constructor**: every maximal subgroup `M` carries the Theorem 14.7 data — a
Hall `κ(M)`-subgroup `K ≤ M`, the swap `K* = M_σ ∩ C_G(K)`, and a Hall `(κ ∪ σ)ᶜ`-subgroup `U` —
obtained from Hall's theorem in the solvable `↥M`.  This is the missing constructor that lets the
family-level corollaries (14.8) feed `exists_partner` / `typeP_covering` from a bare
`M ∈ maximalTypePFamily`. -/
theorem exists_typeP_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∃ K Kstar U : Subgroup G, K ≤ M ∧
      Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M) ∧
      Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ∧
      Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) := by
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  obtain ⟨HK, hHK⟩ := Ch03.hall_E_exists (G := ↥M) (kappa M)
  obtain ⟨HU, hHU⟩ :=
    Ch03.hall_E_exists (G := ↥M) ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  refine ⟨HK.map M.subtype,
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ((HK.map M.subtype : Subgroup G) : Set G),
    HU.map M.subtype, Subgroup.map_subtype_le _, ?_, rfl, ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hHK
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hHU

/-- **BG Corollary 14.8** (mmd L4065): the type-`P₁` maximal subgroups, if any, are all
conjugate in `G`; and if the type-`P` family is nonempty it consists of exactly two conjugacy
classes of maximal subgroups (`M` and its nonconjugate partner `M*` from Theorem 14.7).

Follows directly from Theorem 14.7(f),(g) (gated on §13 via Prop 14.2 / Theorem 14.7). -/
theorem typeP1_conjugate_and_typeP_twoClasses [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ M ∈ maximalTypeP1Family G, ∀ N ∈ maximalTypeP1Family G, IsConjugateSubgroup M N) ∧
    ((maximalTypePFamily G).Nonempty →
      ∃ M ∈ maximalTypePFamily G, ∃ Mstar ∈ maximalTypePFamily G,
        ¬ IsConjugateSubgroup M Mstar ∧
        ∀ H ∈ maximalTypePFamily G,
          IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar) := by
  refine ⟨fun M hMfam N hNfam => ?_, fun hne => ?_⟩
  · -- **Part 1** (`𝓜_{P₁}` is a single class): two type-`P₁` maximals `M`, `N` are conjugate.
    -- The Theorem 14.7 partner `M*` of `M` is type-`P₂` (`isTypeP2_or_isTypeP2_partner`, since `M`
    -- is type-`P₁` hence not type-`P₂`); the covering puts `N ~ M` or `N ~ M*`, and `N ~ M*` would
    -- make `M*` type-`P₁` (conjugation-invariant), contradicting type-`P₂`.  So `N ~ M`.
    obtain ⟨hMmax, hMP1⟩ := hMfam
    obtain ⟨hNmax, hNP1⟩ := hNfam
    obtain ⟨K, Kstar, U, hKM, hK, hKstar, hU⟩ := exists_typeP_data hG hMmax
    obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ :=
      exists_partner hG (genuineSigmaDecomposition hG) hMmax hMP1.1 hKM hK hKstar hU
    have hMstarP2 : IsTypeP2 Mstar := by
      rcases isTypeP2_or_isTypeP2_partner hG (genuineSigmaDecomposition hG) hMmax hMP1.1 hKM hK
        hKstar hU hpart with hM2 | hMstar2
      · exact absurd ⟨hMP1, hM2⟩ not_isTypeP1_and_isTypeP2
      · exact hMstar2
    rcases typeP_covering hG hMmax hMP1.1 hKM hK hKstar hU hMstarmem hMstarne hpart hNmax hNP1.1
      with hNM | hNMstar
    · exact hNM.symm
    · exfalso
      obtain ⟨a, ha⟩ := hNMstar
      exact not_isTypeP1_and_isTypeP2
        ⟨ha ▸ (isTypeP1_conj_smul a N).mpr hNP1, hMstarP2⟩
  · -- **Part 2** (`𝓜_P` = two conjugacy classes): the partner pair `(M, M*)` of Theorem 14.7,
    -- with `typeP_covering` placing every type-`P` `H` in one of the two classes.
    obtain ⟨M, hMmax, hMP⟩ := hne
    obtain ⟨K, Kstar, U, hKM, hK, hKstar, hU⟩ := exists_typeP_data hG hMmax
    obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ :=
      exists_partner hG (genuineSigmaDecomposition hG) hMmax hMP hKM hK hKstar hU
    obtain ⟨hMstarmax, hMstarP, _⟩ :=
      typeP_family_member_data hG hMmax hMP hKM hK hKstar hU hMstarmem
    refine ⟨M, ⟨hMmax, hMP⟩, Mstar, ⟨hMstarmax, hMstarP⟩, ?_, ?_⟩
    · exact typeP_family_pairwise_nonconjugate hG hMmax hMP hKM hK hKstar hU (Or.inl rfl)
        hMstarmem (Ne.symm hMstarne)
    · rintro H ⟨hHmax, hHP⟩
      exact typeP_covering hG hMmax hMP hKM hK hKstar hU hMstarmem hMstarne hpart hHmax hHP

/-- **BG Corollary 14.9** (mmd L3997): `G^#` is the disjoint union of the conjugacy pieces
`𝒞_G(M̃ᵢ)` over class representatives `Mᵢ ∈ 𝓜` — together with one extra `𝒞_G(Ẑ)` piece when
`𝓜_𝓟` is nonempty.

**Faithfulness note (2026-06-14):** the Lean surface covers by `sigmaConjugacySaturation =
𝒞_G(M_σ^#)` instead of BG's `𝒞_G(M̃)` (see `sigmaSharp`). Because `M_σ^# ⊊ M̃`, covering `G^#`
by the *smaller* pieces is **stronger than — and false relative to — BG**: the `ℓ_σ = 2`
twisted elements `x x'` (`x' ∈ R(x)^#`) lie in some `𝒞_G(M̃ᵢ)` but in no `𝒞_G(M_σ^#ⱼ)`, so the
covering fails for them. A faithful statement needs the (gated) `M̃`; do not prove this
surface as-is. See `notes/bg/s14_typeP_counting.md`. -/
theorem nonidentity_covered_by_sigma_pieces [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ x : G, x ≠ 1 → ∃ M : Subgroup G,
      M ∈ maximalSubgroups G ∧ IsTypeF M ∧ x ∈ sigmaConjugacySaturation M) ∨
    (∃ M Mstar K Kstar : Subgroup G,
      M ∈ maximalSubgroups G ∧ Mstar ∈ maximalSubgroups G ∧
      IsTypeP M ∧ IsTypeP Mstar ∧
      ∀ x : G, x ≠ 1 →
        x ∈ conjClassSet (zTilde K Kstar) ∨
        ∃ H : Subgroup G,
          H ∈ maximalSubgroups G ∧ IsTypeF H ∧ x ∈ sigmaConjugacySaturation H) := by
  sorry

/-- **`Ẑ` elements have `σ`-length at most two** (the type-P exceptional half of BG Cor 14.10).  A
`z ∈ Ẑ = zTilde Kref Kstarref = (Kref ⊔ Kstarref) ∖ (Kref ∪ Kstarref)` factors as `z = k·k*` with
`k* ∈ Kstarref ⊆ M_σ(Mref)#` (a `σ(Mref)`-element, so `ℓ_σ(k*) = 1`) and `k ∈ Kref` a nonidentity
`κ(Mref)`-element; since `Kref` consists of `σ(Mref*)`-elements for the non-conjugate partner `Mref*`
(type-P duality), `sigma_cover_decomposition` gives the two-element `σ`-decomposition `{k, k*}`.

**Proof recipe (verified 2026-07-01, no deep gap — only a mechanical split remains):**
`typeP_duality hG hMref hMPref hKMref hKref hKstarref` supplies the partner `Mstar` with
`hK_eq : Kref = M_σ(Mstar) ⊓ C(Kstar)` (so `Kref ≤ M_σ(Mstar)` by `inf_le_left` — the partner-`σ`
membership is *immediate*, not a residual), `hnc : ¬ IsConjugateSubgroup Mref Mstar`, and `hZcyc`
(`K ⊔ K*` cyclic).  Then `z ∈ Ẑ` splits as `z = k·k*` (`k ∈ Kref ≤ M_σ(Mstar)#`,
`k* ∈ Kstarref ≤ M_σ(Mref)`, commuting, both `≠ 1`), and `sigma_cover_decomposition hG hMstarmax
hMref (·) (Kref ≤ M_σ Mstar applied to k) hk1 (Kstarref ≤ M_σ Mref applied to k*) hcomm` gives
`sigmaDecomposition (k·k*) = insert k ({k*} \ {1})`, of `ncard ≤ 2`.

**Only mechanical gap (`sorry`):** the `k·k*` split — `z ∈ (Kref ⊔ Kstarref)` with `Kstarref`
central there.  `Subgroup.mem_sup` (CommGroup `↥(Kref⊔Kstarref)` via `hZcyc.commGroup`) hit an
instance diamond; redo via `Subgroup.mem_sup_of_normal_left` after establishing
`(Kstarref.subgroupOf (Kref⊔Kstarref)).Normal` from centrality.  The `M̃`-piece
(`sigmaLength_le_two_of_mem_Mtilde`) and the Cor 14.10 cover/conjugation plumbing are sorry-free. -/
theorem sigmaLength_le_two_of_mem_zTilde_of_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {Mref Kref Kstarref Uref : Subgroup G}
    (hMref : Mref ∈ maximalSubgroups G) (hMPref : IsTypeP Mref) (hKMref : Kref ≤ Mref)
    (hKref : Ch03.IsHallSubgroup (kappa Mref) (Kref.subgroupOf Mref))
    (hKstarref : Kstarref = OddOrder.BG.Ch3.S10.Msigma Mref ⊓ Subgroup.centralizer (Kref : Set G))
    (hUref : Ch03.IsHallSubgroup ((kappa Mref ∪ OddOrder.BG.Ch3.S10.sigma Mref)ᶜ)
      (Uref.subgroupOf Mref))
    {z : G} (hz : z ∈ zTilde Kref Kstarref) :
    sigmaLength z ≤ 2 := by
  classical
  -- The dual partner `Mstar` (Theorem 14.7 duality): `K = M*_σ ⊓ C(K*)` (so `K ≤ M*_σ`) and
  -- `M` not conjugate to `M*`.
  obtain ⟨_, _, hExU⟩ := typeP_duality hG hMref hMPref hKMref hKref hKstarref
  obtain ⟨Mstar, ⟨hMstarmax, _, hnc, ⟨_, _, hK_eq⟩, _, _, _, _⟩, _⟩ := hExU
  have hKMsig : Kref ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := hK_eq.trans_le inf_le_left
  have hKstarMsig : Kstarref ≤ OddOrder.BG.Ch3.S10.Msigma Mref := hKstarref.trans_le inf_le_left
  -- Unpack `z ∈ Ẑ = (K ⊔ K*) ∖ (K ∪ K*)`.
  rw [zTilde, Set.mem_sdiff, Set.mem_union] at hz
  obtain ⟨hzW, hznot⟩ := hz
  have hzW' : z ∈ Kref ⊔ Kstarref := SetLike.mem_coe.mp hzW
  -- `K ◁ (K ⊔ K*)` (`K*` centralises `K`), so the split `z = k·k*` exists (no `CommGroup` needed).
  haveI hKrefnorm : (Kref.subgroupOf (Kref ⊔ Kstarref)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer
      (le_trans (hKstarref.trans_le inf_le_right)
        (Subgroup.centralizer_le_normalizer (↑Kref : Set G)))
  have hsplit : (⟨z, hzW'⟩ : ↥(Kref ⊔ Kstarref)) ∈
      (Kref.subgroupOf (Kref ⊔ Kstarref)) ⊔ (Kstarref.subgroupOf (Kref ⊔ Kstarref)) := by
    rw [codisjoint_iff.mp (Subgroup.codisjoint_subgroupOf_sup Kref Kstarref)]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_sup_of_normal_left] at hsplit
  obtain ⟨a, ha, b, hb, hab⟩ := hsplit
  have hkK : (a : G) ∈ Kref := Subgroup.mem_subgroupOf.mp ha
  have hksK : (b : G) ∈ Kstarref := Subgroup.mem_subgroupOf.mp hb
  have hzkk : z = (a : G) * (b : G) := by
    have h := congrArg (Subgroup.subtype (Kref ⊔ Kstarref)) hab
    simpa using h.symm
  have hk1 : (a : G) ≠ 1 := by
    rintro h0
    exact hznot (Or.inr (by rw [hzkk, h0, one_mul]; exact SetLike.mem_coe.mpr hksK))
  have hks1 : (b : G) ≠ 1 := by
    rintro h0
    exact hznot (Or.inl (by rw [hzkk, h0, mul_one]; exact SetLike.mem_coe.mpr hkK))
  have hksC : (b : G) ∈ Subgroup.centralizer (↑Kref : Set G) :=
    (hKstarref.trans_le inf_le_right) hksK
  have hcomm : Commute (a : G) (b : G) :=
    Subgroup.mem_centralizer_iff.mp hksC (a : G) (SetLike.mem_coe.mpr hkK)
  have hMN : ¬ ∃ g : G, MulAut.conj g • Mstar = Mref := fun h => hnc (IsConjugateSubgroup.symm h)
  -- `z = k·k*` with `k ∈ M*_σ#`, `k* ∈ M_σ`, `M*`/`M` non-conjugate: `sigma_cover_decomposition`.
  have hdecomp := sigma_cover_decomposition hG hMstarmax hMref hMN (hKMsig hkK) hk1
    (hKstarMsig hksK) hcomm
  rw [sigmaLength, hzkk, hdecomp]
  have h1 : (({(b : G)} : Set G) \ {1}).ncard ≤ 1 :=
    (Set.ncard_le_ncard Set.sdiff_subset (Set.finite_singleton _)).trans
      (le_of_eq (Set.ncard_singleton _))
  calc (insert (a : G) (({(b : G)} : Set G) \ {1})).ncard
      ≤ (({(b : G)} : Set G) \ {1}).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ 2 := by omega

end OddOrder.BG.Ch4.S14
