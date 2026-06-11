/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Corollary1210

/-!
# BG §12: Lemma 12.11 — τ₂ の `M* ∈ ℳ(N_G(A))` への移送

**スコープ**: BG Lemma 12.11 (mmd L3318) とその前提インフラ。

1. **`exists_subgroupESetup`** (mmd L3025 "Recall our choice of `E`, ...") :
   任意の `M ∈ ℳ` に `SubgroupESetup` データが取れる存在文。Lemma 12.11 以降は
   `M* ∈ ℳ(N_G(A))` に対して §12 の諸結果 (12.5/12.6/12.7/12.10) を **`M*` 側で**
   適用するため、これが必要になる (これまでの §12 の全定理は setup を仮定で受けるだけ)。
2. **Lemma 12.11**: `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `M* ∈ ℳ(N_G(A))` のとき
   (a) `τ₂(M)` の素数は `σ(M*) − β(M*)` に入る; (b) `π(E/C_E(A)) ⊆ τ₁(M*) ∪ τ₂(M*)`;
   (c) `q ∈ π(E/C_E(A)) ∩ π(C_E(A))` なら `q ∈ τ₂(M*)` で `G` のある Sylow `p` が
   `M*` で正規、`M*` は `G` の abelian Sylow `q` を含む。

**`exists_subgroupESetup` の構成**: `M_σ` は `M` の normal Hall `σ(M)`-部分群
(`S10.Msigma_subgroupOf_isHall`) なので Schur–Zassenhaus
(`Subgroup.exists_right_complement'_of_coprime`) で補群 `E` を取る。`E` は solvable
なので Hall `τ₁∪τ₂`-部分群 `K₀` が存在し (`Ch03.hall_E_exists`)、`K₀` の中で Hall
`τ₁`- と Hall `τ₂`-部分群 `H₁, H₂` を取る。`H₁.index` は `τ₂`-数、`H₂.index` は
`τ₁`-数なので互いに素、よって `H₁ ⊔ H₂ = K₀` (`Ch03.sup_eq_top_of_coprime_index`)
— これが `E₁₂_hall` field を満たす鍵。`E₃` は独立な Hall `τ₃`-部分群。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## Hall-in-Hall 移送 -/

/-- Hall-in-Hall: `K` が `G` の Hall `π`-部分群、`H ≤ K` が `K` 内で Hall `ρ`
(`ρ ⊆ π`) なら、`H` は `G` の Hall `ρ`-部分群。index の素因子が
`index_K(H)`-part (`∉ ρ`) と `index_G(K)`-part (`∉ π ⊇ ρ`) に分かれることによる。 -/
theorem isHallSubgroup_of_isHallSubgroup_of_le {G : Type*} [Group G] [Finite G]
    {π ρ : Set ℕ} (hρπ : ρ ⊆ π) {K : Subgroup G} (hK : Ch03.IsHallSubgroup π K)
    {H : Subgroup G} (hHK : H ≤ K) (hH : Ch03.IsHallSubgroup ρ (H.subgroupOf K)) :
    Ch03.IsHallSubgroup ρ H := by
  constructor
  · intro r hr
    apply hH.1 r
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
  · intro r hr hrρ
    obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
    have hchain := Subgroup.relIndex_mul_relIndex (hHK := hHK) (hKL := le_top (a := K))
    rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at hchain
    rw [← hchain] at hr_dvd
    rcases hr_prime.dvd_mul.mp hr_dvd with h1 | h1
    · exact hH.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, h1,
        Subgroup.index_ne_zero_of_finite⟩) hrρ
    · exact hK.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, h1,
        Subgroup.index_ne_zero_of_finite⟩) (hρπ hrρ)

/-! ## `SubgroupESetup` の存在 -/

/-- **`SubgroupESetup` の存在** (BG §12 冒頭, mmd L3025): 任意の `M ∈ ℳ` に対して
`M_σ` の補群 `E` と、`E₁E₂` が部分群になるような Hall `τᵢ(M)`-部分群の組が取れる。
`E₁ ⊔ E₂` の Hall 性は、Hall `τ₁∪τ₂`-部分群 `K₀` の中で `E₁, E₂` を取り、
両者の (`K₀` 内) index が互いに素 (`τ₁`-数 vs `τ₂`-数) であることから
`E₁ ⊔ E₂ = K₀` と同定して得る。 -/
theorem exists_subgroupESetup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∃ E E₁ E₂ E₃ : Subgroup G, SubgroupESetup M E E₁ E₂ E₃ := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- `M ≤ N_G(M_σ)`, hence `M_σ.subgroupOf M` is normal.
  have hM_norm_Mσ : M ≤ Subgroup.normalizer ((S10.Msigma M) : Set G) := by
    rw [S10.Msigma, OddOrder.GroupTheory.opiCoreInG]
    have hle := Subgroup.le_normalizer_map
      (H := Ch03.oPiCore (S10.sigma M) ↥M) M.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hle
  set N : Subgroup ↥M := (S10.Msigma M).subgroupOf M with hNdef
  haveI hN_normal : N.Normal := by
    constructor
    intro n hn g
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    have hgn := (Subgroup.mem_normalizer_iff.mp (hM_norm_Mσ g.2) (n : G)).mp hn
    simpa using hgn
  -- Schur–Zassenhaus complement `E₀` to `M_σ` inside `↥M`.
  have hN_hall : Ch03.IsHallSubgroup (S10.sigma M) N := S10.Msigma_subgroupOf_isHall hG hM
  obtain ⟨E₀, hE₀⟩ := Subgroup.exists_right_complement'_of_coprime hN_hall.coprime_index
  set E : Subgroup G := E₀.map M.subtype with hEdef
  have hE_le : E ≤ M := Subgroup.map_subtype_le _
  have hE₀_eq : E.subgroupOf M = E₀ := by
    rw [hEdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  -- Complement identities at `G` level.
  have hcompl_inf : S10.Msigma M ⊓ E = ⊥ := by
    have hdisj := hE₀.disjoint
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    have hzM : z ∈ M := hE_le hz2
    have hz1' : (⟨z, hzM⟩ : ↥M) ∈ N := by
      rw [hNdef, Subgroup.mem_subgroupOf]
      exact hz1
    have hz2' : (⟨z, hzM⟩ : ↥M) ∈ E₀ := by
      rw [← hE₀_eq, Subgroup.mem_subgroupOf]
      exact hz2
    have hz_bot := hdisj.le_bot (Subgroup.mem_inf.mpr ⟨hz1', hz2'⟩)
    rw [Subgroup.mem_bot] at hz_bot
    have hz1eq : z = 1 := congrArg Subtype.val hz_bot
    simp [hz1eq]
  have hcompl_sup : S10.Msigma M ⊔ E = M := by
    have hsup := hE₀.sup_eq_top
    apply le_antisymm (sup_le (S10.Msigma_le M) hE_le)
    intro m hm
    have hm' : (⟨m, hm⟩ : ↥M) ∈ N ⊔ E₀ := by rw [hsup]; exact Subgroup.mem_top _
    have h1 : ((N ⊔ E₀).map M.subtype : Subgroup G) ≤ S10.Msigma M ⊔ E := by
      rw [Subgroup.map_sup]
      apply sup_le
      · intro u hu
        obtain ⟨u₀, hu₀, rfl⟩ := hu
        have hu₀' : M.subtype u₀ ∈ S10.Msigma M := hu₀
        exact Subgroup.mem_sup_left hu₀'
      · rw [hEdef]
        exact le_sup_right
    exact h1 ⟨⟨m, hm⟩, hm', rfl⟩
  -- `E` is solvable; fix a Hall `τ₁∪τ₂`-subgroup `K₀` and Hall pieces inside it.
  haveI : IsSolvable ↥E :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hE_le)
  obtain ⟨K₀, hK₀⟩ := Ch03.hall_E_exists (G := ↥E) (tau1 M ∪ tau2 M)
  haveI : IsSolvable ↥K₀ :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (le_top (a := K₀)))
  obtain ⟨H₁, hH₁⟩ := Ch03.hall_E_exists (G := ↥K₀) (tau1 M)
  obtain ⟨H₂, hH₂⟩ := Ch03.hall_E_exists (G := ↥K₀) (tau2 M)
  obtain ⟨H₃, hH₃⟩ := Ch03.hall_E_exists (G := ↥E) (tau3 M)
  -- τ₁ and τ₂ are disjoint (rank 1 vs rank 2).
  have hτ_disj : ∀ r : ℕ, r ∈ tau1 M → r ∈ tau2 M → False := by
    intro r h1 h2
    have h12 := h1.2.2
    have h22 := h2.2
    omega
  -- `H₁ ⊔ H₂ = K₀` via coprime indices (`τ₂`-number vs `τ₁`-number).
  have hsupH : H₁ ⊔ H₂ = (⊤ : Subgroup ↥K₀) := by
    apply Ch03.sup_eq_top_of_coprime_index
    apply coprime_of_forall_prime_not_dvd
    intro r hr_prime hr1 hr2
    have hπK : ∀ s : ℕ, s.Prime → s ∣ Nat.card ↥K₀ → s ∈ tau1 M ∪ tau2 M := by
      intro s hs_prime hs_dvd
      exact hK₀.1 s (Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd, Nat.card_pos.ne'⟩)
    have hr1' : r ∈ tau1 M ∪ tau2 M :=
      hπK r hr_prime (hr1.trans (Subgroup.index_dvd_card H₁))
    have hr1'' : r ∉ tau1 M := fun hmem =>
      hH₁.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, hr1,
        Subgroup.index_ne_zero_of_finite⟩) hmem
    have hr2'' : r ∉ tau2 M := fun hmem =>
      hH₂.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, hr2,
        Subgroup.index_ne_zero_of_finite⟩) hmem
    rcases hr1' with h | h
    · exact hr1'' h
    · exact hr2'' h
  -- Assemble the four subgroups at `G` level.
  set E₁ : Subgroup G := (H₁.map K₀.subtype).map E.subtype with hE₁def
  set E₂ : Subgroup G := (H₂.map K₀.subtype).map E.subtype with hE₂def
  set E₃ : Subgroup G := H₃.map E.subtype with hE₃def
  refine ⟨E, E₁, E₂, E₃, ?_⟩
  have hE₁_subOf : E₁.subgroupOf E = H₁.map K₀.subtype := by
    rw [hE₁def, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
  have hE₂_subOf : E₂.subgroupOf E = H₂.map K₀.subtype := by
    rw [hE₂def, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
  have hE₃_subOf : E₃.subgroupOf E = H₃ := by
    rw [hE₃def, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
  have hH₁K : Ch03.IsHallSubgroup (tau1 M) ((H₁.map K₀.subtype).subgroupOf K₀) := by
    rwa [Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective K₀.subtype_injective]
  have hH₂K : Ch03.IsHallSubgroup (tau2 M) ((H₂.map K₀.subtype).subgroupOf K₀) := by
    rwa [Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective K₀.subtype_injective]
  -- `E₁ ⊔ E₂` corresponds to `K₀`.
  have hsup12 : (E₁ ⊔ E₂).subgroupOf E = K₀ := by
    have h1 : E₁ ⊔ E₂ = ((H₁ ⊔ H₂).map K₀.subtype).map E.subtype := by
      rw [hE₁def, hE₂def, ← Subgroup.map_sup, ← Subgroup.map_sup]
    rw [h1, hsupH]
    have h2 : ((⊤ : Subgroup ↥K₀).map K₀.subtype) = K₀ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h2, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
  exact
    { mem_maximal := hM
      E_le := hE_le
      E_compl_inf := hcompl_inf
      E_compl_sup := hcompl_sup
      E₁_le := Subgroup.map_subtype_le _
      E₂_le := Subgroup.map_subtype_le _
      E₃_le := Subgroup.map_subtype_le _
      E₁_hall := by
        rw [hE₁_subOf]
        exact isHallSubgroup_of_isHallSubgroup_of_le Set.subset_union_left hK₀
          (Subgroup.map_subtype_le _) hH₁K
      E₂_hall := by
        rw [hE₂_subOf]
        exact isHallSubgroup_of_isHallSubgroup_of_le Set.subset_union_right hK₀
          (Subgroup.map_subtype_le _) hH₂K
      E₃_hall := by
        rw [hE₃_subOf]
        exact hH₃
      E₁₂_hall := by
        rw [hsup12]
        exact hK₀ }

/-! ## 共役・押し込みの補助部品 -/

/-- 共役は `ℰ_p^n(G)` を保つ。 -/
theorem conj_smul_mem_elemAbelianOfRank {p n : ℕ} {A : Subgroup G} (w : G)
    (hA : A ∈ elemAbelianOfRank G p n) :
    (MulAut.conj w • A : Subgroup G) ∈ elemAbelianOfRank G p n := by
  refine mem_elemAbelianOfRank.mpr ⟨?_, ?_⟩
  · rw [mulAut_smul_eq_map]
    exact Subgroup.IsElementaryAbelian.map (MulAut.conj w).injective hA.1
  · rw [mulAut_smul_eq_map, Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact hA.2

/-- **Hall 断片の `M` 内 Hall 性**: `E` の Hall `π`-部分群 `F` (`π ∩ σ(M) = ∅`) は
`M` の Hall `π`-部分群でもある (Corollary 12.10(e) の内部導出のパラメトリック化)。
`F ≤ E ≤ M` の relIndex 連鎖で、`E` 内の index は `hF` から、`E.relIndex M = |M_σ|` の
素因子は `σ(M)` に入るので `π` と交わらない。 -/
theorem hallPiece_isHall_in_M [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {π : Set ℕ} {F : Subgroup G} (hFE : F ≤ E)
    (hF : Ch03.IsHallSubgroup π (F.subgroupOf E)) (hπσ : π ⊆ (S10.sigma M)ᶜ) :
    Ch03.IsHallSubgroup π (F.subgroupOf M) := by
  have hFM : F ≤ M := hFE.trans h.E_le
  constructor
  · intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv] at hr
    apply hF.1 r
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv]
  · intro r hr hr2
    obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
    have hchain := Subgroup.relIndex_mul_relIndex (hHK := hFE) (hKL := h.E_le)
    have hr_dvd' : r ∣ F.relIndex E * E.relIndex M := by rwa [hchain]
    rcases hr_prime.dvd_mul.mp hr_dvd' with h1 | h1
    · exact hF.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, h1,
        Subgroup.index_ne_zero_of_finite⟩) hr2
    · have hEM : E.relIndex M = Nat.card ↥(S10.Msigma M) := by
        have hcard := card_Msigma_mul_card_E h
        have h2 := Subgroup.card_mul_index (E.subgroupOf M)
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv] at h2
        have h3 : Nat.card ↥E * E.relIndex M
            = Nat.card ↥E * Nat.card ↥(S10.Msigma M) := by
          rw [show E.relIndex M = (E.subgroupOf M).index from rfl, h2, ← hcard]
          ring
        exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
      rw [hEM] at h1
      have hrσ : r ∈ S10.sigma M :=
        (S10.Msigma_isHall hG h.mem_maximal).1 r
          (Nat.mem_primeFactors.mpr ⟨hr_prime, h1, Nat.card_pos.ne'⟩)
      exact hπσ hr2 hrσ

/-- **`π`-部分群の Hall 断片への押し込み** (Corollary 12.10(e) の押し込み機構の
パラメトリック化): `X ≤ M` が `π`-群、`F` が `E` の Hall `π`-部分群 (`π ∩ σ(M) = ∅`)
なら `M` 内の共役で `X` は `F` に入る。 -/
theorem exists_conj_smul_le_hallPiece [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {π : Set ℕ} {F : Subgroup G} (hFE : F ≤ E)
    (hF : Ch03.IsHallSubgroup π (F.subgroupOf E)) (hπσ : π ⊆ (S10.sigma M)ᶜ)
    {X : Subgroup G} (hXM : X ≤ M)
    (hXpi : Ch03.Subgroup.IsPiGroup π (X.subgroupOf M)) :
    ∃ w ∈ M, MulAut.conj w • X ≤ F := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups h.mem_maximal
  obtain ⟨H, hH_hall, -, hX_le_H⟩ :=
    Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (A := Unit) (φ := (1 : Unit →* MulAut ↥M))
      (by rw [Nat.card_unique]; exact Nat.coprime_one_left _)
      hXpi (fun _ => one_smul _ _)
  set HG : Subgroup G := H.map M.subtype with hHGdef
  have hHG_le_M : HG ≤ M := Subgroup.map_subtype_le _
  have hHG_hall : Ch03.IsHallSubgroup π (HG.subgroupOf M) := by
    rwa [hHGdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  obtain ⟨w, hwM, hw⟩ :=
    Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hHG_le_M
      (hFE.trans h.E_le) hHG_hall (hallPiece_isHall_in_M hG h hFE hF hπσ)
  have hXHG : X ≤ HG := by
    intro x hx
    rw [hHGdef]
    exact Subgroup.mem_map.mpr ⟨⟨x, hXM hx⟩,
      hX_le_H (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  exact ⟨w, hwM, (conj_smul_mono (MulAut.conj w) hXHG).trans hw.le⟩

/-- `p ∈ τ₂(M)` (`p` 素数) なら `M` は rank-2 elementary abelian `p`-部分群を含む
(`pRank ↥M p = 2` の witness 化)。 -/
theorem exists_mem_elemAbelianOfRank_two_le_of_tau2 [Finite G]
    {M : Subgroup G} {p : ℕ} (hp_prime : p.Prime) (hp : p ∈ tau2 M) :
    ∃ A ∈ elemAbelianOfRank G p 2, A ≤ M := by
  have hrank : pRank ↥M p = 2 := tau2_pRank_eq_two hp
  obtain ⟨B, hB_ea, hB_log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥M) (p := p)
      (n := 2) two_pos (by omega)
  have hB_card : p ^ 2 ≤ Nat.card ↥B :=
    le_trans (Nat.pow_le_pow_right hp_prime.one_lt.le hB_log)
      (Nat.pow_log_le_self p Nat.card_pos.ne')
  obtain ⟨H, hH_ea, hH_card⟩ :=
    IsElementaryAbelian.exists_subgroup_card_prime_sq hp_prime hB_ea hB_card
  refine ⟨(H.map B.subtype).map M.subtype, mem_elemAbelianOfRank.mpr ⟨?_, ?_⟩,
    Subgroup.map_subtype_le _⟩
  · exact Subgroup.IsElementaryAbelian.map M.subtype_injective
      (Subgroup.IsElementaryAbelian.map B.subtype_injective hH_ea)
  · rw [Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective B.subtype_injective]
    exact hH_card

/-- `p ∈ σ(M')` のとき `M'` 内の elementary abelian `p`-部分群は `M'_σ` に入る
(`M'_σ` の `G` 内 Hall 性 `S10.Msigma_isHall` から)。 -/
theorem le_Msigma_of_mem_elemAbelianOfRank_of_mem_sigma [Finite G]
    (hG : IsMinimalSimpleOdd G) {M' : Subgroup G} (hM' : M' ∈ maximalSubgroups G)
    {p : ℕ} (hp_prime : p.Prime) (hpσ : p ∈ S10.sigma M') {n : ℕ}
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p n) (hAM' : A ≤ M') :
    A ≤ S10.Msigma M' := by
  refine S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hM') hAM' ?_
  intro r hr
  rw [hA.2] at hr
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn, pow_zero] at hr
    simp at hr
  · rw [Nat.primeFactors_pow p hn.ne', Nat.Prime.primeFactors hp_prime] at hr
    rw [Finset.mem_singleton.mp hr]
    exact hpσ

/-! ## Lemma 12.11(a) -/

/-- **Lemma 12.11(a), `p` 自身の部分** (mmd L3322): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`,
`M* ∈ ℳ(N_G(A))` なら `p ∈ σ(M*)`。Lemma 12.2(a) で `p ∈ σ(M*) ∪ τ₂(M*)`;
`τ₂(M*)` 側は `A` を `M*` 内共役で `E₂*` に押し込むと Corollary 12.6(b) の
`N_G(A^w) ⊄ M*` が `N_G(A) ≤ M*` と衝突して不発。 -/
theorem mem_sigma_of_tau2_of_mem_maximalContaining [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G))) :
    p ∈ S10.sigma Mstar := by
  classical
  obtain ⟨hMst_co, hNMst⟩ := mem_maximalSubgroupsContaining.mp hMstar
  have hMst_mem : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMst_co
  have hAM : A ≤ M := hAE.trans h.E_le
  have hAne : A ≠ ⊥ := by
    intro hbot
    have hcard := hA.2
    rw [hbot, Subgroup.card_bot] at hcard
    exact (Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt).ne' hcard.symm
  rcases prime_mem_sigma_or_tau2 hG h.mem_maximal hAM hAne hA.1.isPGroup hMstar with hσ | hτ₂
  · exact hσ
  · exfalso
    obtain ⟨Es, E1s, E2s, E3s, hs⟩ := exists_subgroupESetup hG hMst_mem
    have hAMst : A ≤ Mstar := Subgroup.le_normalizer.trans hNMst
    have hApi : Ch03.Subgroup.IsPiGroup (tau2 Mstar) (A.subgroupOf Mstar) := by
      intro r hr
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAMst).toEquiv, hA.2,
        Nat.primeFactors_pow p two_ne_zero,
        Nat.Prime.primeFactors (Fact.out : p.Prime)] at hr
      rw [Finset.mem_singleton.mp hr]
      exact hτ₂
    obtain ⟨w, hwMst, hwle⟩ := exists_conj_smul_le_hallPiece hG hs hs.E₂_le hs.E₂_hall
      (tau2_subset_sigma_compl Mstar) hAMst hApi
    have hA' := conj_smul_mem_elemAbelianOfRank w hA
    have hA'E : (MulAut.conj w • A : Subgroup G) ≤ Es := hwle.trans hs.E₂_le
    have hnot := (elemAb_normal_in_E_of_tau2 hG hs hτ₂ hA' hA'E).2.1.2.2
    apply hnot
    rw [← normalizer_conj_smul]
    calc MulAut.conj w • Subgroup.normalizer (A : Set G)
        ≤ MulAut.conj w • Mstar := conj_smul_mono _ hNMst
      _ = Mstar := conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hwMst)

/-- **BG Lemma 12.11(a)** (mmd L3318): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `M* ∈ ℳ(N_G(A))`
のとき、`τ₂(M)` の任意の**素数** `q` は `σ(M*) − β(M*)` に入る。

(repo の `tau2` は pRank 条件のみで合成数を排除しないため、原典の
`τ₂(M) ⊆ σ(M*) − β(M*)` は素数に制限して faithful 化する — 12.3/12.10(c) と同型の訂正。)

`q = p` は `mem_sigma_of_tau2_of_mem_maximalContaining`。`q ≠ p` は `A_q ∈ ℰ_q²(E)` を
押し込みで作り、`A` と `A_q` が `E` の coprime normal 部分群 (Corollary 12.6(a)) として
可換なことから `⊥ ≠ A ≤ C_{M*_σ}(A_q)` を得て、`q ∈ τ₂(M*)` なら Theorem 12.5(d) に
矛盾。rank-2 で `τ₁(M*)/τ₃(M*)` も不可、分割 (12.1) で `q ∈ σ(M*)`。
`β` 除外は Lemma 12.1(g) (`q ∉ β(G)`)。 -/
theorem tau2_prime_mem_sigma_diff_beta [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)))
    {q : ℕ} (hq_prime : q.Prime) (hq : q ∈ tau2 M) :
    q ∈ S10.sigma Mstar \ S10.beta Mstar := by
  classical
  obtain ⟨hMst_co, hNMst⟩ := mem_maximalSubgroupsContaining.mp hMstar
  have hMst_mem : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMst_co
  have hEN : E ≤ Subgroup.normalizer (A : Set G) := E_le_normalizer_of_tau2 hG h hp hA hAE
  have hEMst : E ≤ Mstar := hEN.trans hNMst
  -- β 除外: Lemma 12.1(g) — `q ∉ β(G)`、よって `q ∉ β(M*)`。
  obtain ⟨A₁, hA₁, hA₁M⟩ := exists_mem_elemAbelianOfRank_two_le_of_tau2 hq_prime hq
  have hqideal : ¬ S10.idealPrime q G :=
    (isMaximalElementaryAbelian_of_mem_tau2 hG h.mem_maximal hq_prime hq hA₁M hA₁).2
  refine ⟨?_, fun hβ => hqideal hβ.2⟩
  by_cases hqp : q = p
  · subst hqp
    exact mem_sigma_of_tau2_of_mem_maximalContaining hG h hq hA hAE hMstar
  haveI : Fact q.Prime := ⟨hq_prime⟩
  -- `A_q ∈ ℰ_q²(E)` を押し込みで構成。
  obtain ⟨w, hwM, hwle⟩ := exists_conj_smul_le_hallPiece hG h h.E₂_le h.E₂_hall
    (tau2_subset_sigma_compl M) hA₁M (by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁M).toEquiv, hA₁.2,
      Nat.primeFactors_pow q two_ne_zero, Nat.Prime.primeFactors hq_prime] at hr
    rw [Finset.mem_singleton.mp hr]
    exact hq)
  set Aq : Subgroup G := MulAut.conj w • A₁ with hAqdef
  have hAq : Aq ∈ elemAbelianOfRank G q 2 := conj_smul_mem_elemAbelianOfRank w hA₁
  have hAqE : Aq ≤ E := hwle.trans h.E₂_le
  have hAqMst : Aq ≤ Mstar := hAqE.trans hEMst
  -- `p ∈ σ(M*)`、よって `A ≤ M*_σ`。
  have hpσ : p ∈ S10.sigma Mstar :=
    mem_sigma_of_tau2_of_mem_maximalContaining hG h hp hA hAE hMstar
  have hAMσ : A ≤ S10.Msigma Mstar :=
    le_Msigma_of_mem_elemAbelianOfRank_of_mem_sigma hG hMst_mem
      (Fact.out : p.Prime) hpσ hA (Subgroup.le_normalizer.trans hNMst)
  -- `A ⊓ A_q = ⊥` (coprime cards)。
  have hinf : A ⊓ Aq = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(A ⊓ Aq : Subgroup G) ∣ p ^ 2 := by
      rw [← hA.2]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(A ⊓ Aq : Subgroup G) ∣ q ^ 2 := by
      rw [← hAq.2]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hco : Nat.Coprime (p ^ 2) (q ^ 2) :=
      Nat.Coprime.pow 2 2
        ((Nat.coprime_primes (Fact.out : p.Prime) hq_prime).mpr fun hpq => hqp hpq.symm)
    exact (Nat.Coprime.coprime_dvd_left h1 hco).eq_one_of_dvd h2
  -- `A ≤ C_G(A_q)`: `A, A_q ⊴ E` (Corollary 12.6(a)) の coprime 可換性。
  have hENq : E ≤ Subgroup.normalizer (Aq : Set G) :=
    E_le_normalizer_of_tau2 hG h hq hAq hAqE
  have hAcent : A ≤ Subgroup.centralizer (Aq : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← le_bot_iff, ← hinf]
    rw [Subgroup.commutator_le]
    intro a ha t ht
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : t * a⁻¹ * t⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hEN (hAqE ht)) a⁻¹).mp (A.inv_mem ha)
      have h2 : a * (t * a⁻¹ * t⁻¹) ∈ A := A.mul_mem ha h1
      rw [commutatorElement_def]
      simpa [mul_assoc] using h2
    · have h1 : a * t * a⁻¹ ∈ Aq :=
        (Subgroup.mem_normalizer_iff.mp (hENq (hAE ha)) t).mp ht
      have h2 : a * t * a⁻¹ * t⁻¹ ∈ Aq := Aq.mul_mem h1 (Aq.inv_mem ht)
      rwa [commutatorElement_def]
  -- 分割 (12.1) と rank で `q ∈ σ(M*)` 以外を排除。
  by_contra hqσ
  obtain ⟨Es, E1s, E2s, E3s, hs⟩ := exists_subgroupESetup hG hMst_mem
  have hqMst : q ∣ Nat.card ↥Mstar := by
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hAqMst)
    rw [hAq.2]
    exact dvd_pow_self q two_ne_zero
  have hqEs : q ∈ (Nat.card ↥Es).primeFactors := by
    have hsplit := card_Msigma_mul_card_E hs
    have hqdvd : q ∣ Nat.card ↥(S10.Msigma Mstar) * Nat.card ↥Es := by
      rw [hsplit]
      exact hqMst
    rcases hq_prime.dvd_mul.mp hqdvd with hd | hd
    · exact absurd (S10.Msigma_isPiGroup Mstar q
        (Nat.mem_primeFactors.mpr ⟨hq_prime, hd, Nat.card_pos.ne'⟩)) hqσ
    · exact Nat.mem_primeFactors.mpr ⟨hq_prime, hd, Nat.card_pos.ne'⟩
  have hrank2 : 2 ≤ pRank ↥Mstar q := by
    have hle := le_pRank (Aq.subgroupOf Mstar)
      (IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hAqMst).symm hAq.1)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAqMst).toEquiv, hAq.2,
      Nat.log_pow hq_prime.one_lt] at hle
  rcases hs.mem_tau_union_of_mem_primeFactors hG hqEs with (h1 | h2) | h3
  · have := tau1_pRank_eq_one h1
    omega
  · -- `q ∈ τ₂(M*)`: Theorem 12.5(d) で `M*_σ ⊓ C_G(A_q) = ⊥` だが `⊥ ≠ A` が入る。
    have h125d := (Msigma_nilpotent_of_tau2 hG hMst_mem h2 hAq hAqMst).2.2.2.1
    have hAbot : A ≤ (⊥ : Subgroup G) := by
      rw [← h125d]
      exact le_inf hAMσ hAcent
    have hcard := hA.2
    rw [le_bot_iff.mp hAbot, Subgroup.card_bot] at hcard
    exact (Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt).ne' hcard.symm
  · have := tau3_pRank_eq_one h3
    omega

/-! ## Lemma 12.11(b) -/

/-- `derivedInG` の単調性 (S09/S10 の private 補題の再掲; hoist は hub 仕事)。 -/
private theorem derivedInG_eq_commutator (H : Subgroup G) :
    derivedInG H = ⁅H, H⁆ := by
  rw [derivedInG, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

private theorem derivedInG_mono {H K : Subgroup G} (hHK : H ≤ K) :
    derivedInG H ≤ derivedInG K := by
  rw [derivedInG_eq_commutator H, derivedInG_eq_commutator K]
  exact Subgroup.commutator_mono hHK hHK

/-- **BG Lemma 12.11(b)** (mmd L3325): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `M* ∈ ℳ(N_G(A))`
のとき `π(E/C_E(A)) ⊆ τ₁(M*) ∪ τ₂(M*)`。

`r ∈ π(E/C_E(A))` が `σ(M*) ∪ τ₃(M*)` に落ちると仮定すると、`E` の Sylow `r`-部分群
`Q` は (`σ` なら `M*_σ` 経由、`τ₃` なら `E₃*` への押し込み経由で) `M*' = derivedInG M*`
に入る。`p ∉ β(M*)` (12.11(a)) より `M*'` は normal `p`-補群 `K` を持ち (Lemma 10.8(c) =
`isHall_Mbeta` 第 4 成分)、`r ≠ p` から `Q ≤ K`。`A ≤ M*_σ ≤ M*'` と合わせ
`⁅A,Q⁆ ≤ A ⊓ K = ⊥` (各因子が他方を正規化)、よって `Q ≤ C_G(A)` — これは Sylow `r` が
`C_E(A)` に入ることを意味し `r ∣ [E : C_E(A)]` に矛盾。 -/
theorem index_primeFactors_subset_tau1_union_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)))
    {r : ℕ}
    (hr : r ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors) :
    r ∈ tau1 Mstar ∪ tau2 Mstar := by
  classical
  by_contra hr12
  have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
  haveI : Fact r.Prime := ⟨hr_prime⟩
  obtain ⟨hMst_co, hNMst⟩ := mem_maximalSubgroupsContaining.mp hMstar
  have hMst_mem : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMst_co
  have hEN : E ≤ Subgroup.normalizer (A : Set G) := E_le_normalizer_of_tau2 hG h hp hA hAE
  have hEMst : E ≤ Mstar := hEN.trans hNMst
  have hAMst : A ≤ Mstar := Subgroup.le_normalizer.trans hNMst
  -- `r ∈ τ₁(M)` (Corollary 12.10(c)) ⟹ `r ≠ p`。
  have hrτ₁M : r ∈ tau1 M :=
    ((nilpotent_sigmaComplement_abelian hG h).2.2.1 p (Fact.out : p.Prime) hp A hA hAE).2.2 r hr
  have hrp : r ≠ p := by
    intro he
    have h1 := tau1_pRank_eq_one hrτ₁M
    have h2 := tau2_pRank_eq_two hp
    rw [he] at h1
    omega
  -- `p ∈ σ(M*) − β(M*)` (12.11(a)) と `A ≤ M*_σ ≤ M*'`。
  have hpσ : p ∈ S10.sigma Mstar :=
    mem_sigma_of_tau2_of_mem_maximalContaining hG h hp hA hAE hMstar
  have hpβ : p ∉ S10.beta Mstar :=
    (tau2_prime_mem_sigma_diff_beta hG h hp hA hAE hMstar (Fact.out : p.Prime) hp).2
  have hAD : A ≤ derivedInG Mstar :=
    (le_Msigma_of_mem_elemAbelianOfRank_of_mem_sigma hG hMst_mem (Fact.out : p.Prime)
      hpσ hA hAMst).trans (S10.Msigma_le_derived hG hMst_mem)
  -- `E` の Sylow `r`-部分群 `Q` (G レベル)。
  obtain ⟨Q₀⟩ : Nonempty (Sylow r ↥E) := inferInstance
  set Q : Subgroup G := (Q₀ : Subgroup ↥E).map E.subtype with hQdef
  have hQE : Q ≤ E := Subgroup.map_subtype_le _
  have hQMst : Q ≤ Mstar := hQE.trans hEMst
  -- `r ∣ |E|` (index は |E| を割る) ⟹ `r ∣ |Q₀|`。
  have hrE : r ∣ Nat.card ↥E :=
    (Nat.mem_primeFactors.mp hr).2.1.trans
      (Subgroup.index_dvd_card ((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E))
  have hQ₀card : Nat.card ↥(Q₀ : Subgroup ↥E) = r ^ (Nat.card ↥E).factorization r :=
    Sylow.card_eq_multiplicity Q₀
  have hQcard : Nat.card ↥Q = r ^ (Nat.card ↥E).factorization r := by
    rw [hQdef, Subgroup.card_map_of_injective E.subtype_injective]
    exact hQ₀card
  have hfac_pos : (Nat.card ↥E).factorization r ≠ 0 := by
    intro h0
    have h1 : r ^ 1 ∣ Nat.card ↥E := by rwa [pow_one]
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization hr_prime
      (Nat.card_pos (α := ↥E)).ne').mp h1
    omega
  have hQpg : IsPGroup r ↥Q := by
    rw [hQdef]
    exact Q₀.2.map E.subtype
  -- `Q ≤ M*' = derivedInG M*`。
  have hQD : Q ≤ derivedInG Mstar := by
    by_cases hrσ : r ∈ S10.sigma Mstar
    · -- `σ(M*)`: `Q ≤ M*_σ ≤ M*'`。
      refine (S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hMst_mem)
        hQMst ?_).trans (S10.Msigma_le_derived hG hMst_mem)
      intro s hs'
      rw [hQcard] at hs'
      rw [Nat.primeFactors_pow r hfac_pos, Nat.Prime.primeFactors hr_prime] at hs'
      rw [Finset.mem_singleton.mp hs']
      exact hrσ
    · -- `σ` 外: 分割で `r ∈ τ₃(M*)`、`E₃*` へ押し込み。
      obtain ⟨Es, E1s, E2s, E3s, hs⟩ := exists_subgroupESetup hG hMst_mem
      have hrMst : r ∣ Nat.card ↥Mstar := hrE.trans (Subgroup.card_dvd_of_le hEMst)
      have hrEs : r ∈ (Nat.card ↥Es).primeFactors := by
        have hsplit := card_Msigma_mul_card_E hs
        have hrdvd : r ∣ Nat.card ↥(S10.Msigma Mstar) * Nat.card ↥Es := by
          rw [hsplit]
          exact hrMst
        rcases hr_prime.dvd_mul.mp hrdvd with hd | hd
        · exact absurd (S10.Msigma_isPiGroup Mstar r
            (Nat.mem_primeFactors.mpr ⟨hr_prime, hd, Nat.card_pos.ne'⟩)) hrσ
        · exact Nat.mem_primeFactors.mpr ⟨hr_prime, hd, Nat.card_pos.ne'⟩
      have hrτ₃ : r ∈ tau3 Mstar := by
        rcases hs.mem_tau_union_of_mem_primeFactors hG hrEs with (h1 | h2) | h3
        · exact absurd (Or.inl h1) hr12
        · exact absurd (Or.inr h2) hr12
        · exact h3
      have hQpi : Ch03.Subgroup.IsPiGroup (tau3 Mstar) (Q.subgroupOf Mstar) := by
        intro s hs'
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQMst).toEquiv, hQcard,
          Nat.primeFactors_pow r hfac_pos, Nat.Prime.primeFactors hr_prime] at hs'
        rw [Finset.mem_singleton.mp hs']
        exact hrτ₃
      obtain ⟨w, hwMst, hwle⟩ := exists_conj_smul_le_hallPiece hG hs hs.E₃_le hs.E₃_hall
        (tau3_subset_sigma_compl Mstar) hQMst hQpi
      have hE3D : E3s ≤ derivedInG Mstar :=
        (hs.E3_le_derived hG).trans (derivedInG_mono hs.E_le)
      have hconj : MulAut.conj w • Q ≤ derivedInG Mstar := hwle.trans hE3D
      -- `M* ≤ N(M*')` で共役を引き戻す。
      have hw' : MulAut.conj w⁻¹ • derivedInG Mstar = derivedInG Mstar :=
        conj_smul_eq_self_of_mem_normalizer
          (S10.le_normalizer_derivedInG Mstar (Mstar.inv_mem hwMst))
      have hpull : MulAut.conj w⁻¹ • (MulAut.conj w • Q)
          ≤ MulAut.conj w⁻¹ • derivedInG Mstar := conj_smul_mono _ hconj
      rwa [hw', smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at hpull
  -- `p ∈ π(M*)` と Lemma 10.8(c): `M*'` の normal `p`-補群 `K`。
  have hpMst : p ∈ (Nat.card ↥Mstar).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨(Fact.out : p.Prime), ?_, Nat.card_pos.ne'⟩
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hAMst)
    rw [hA.2]
    exact dvd_pow_self p two_ne_zero
  obtain ⟨K, hKnorm, hKcompl⟩ :=
    ((S10.isHall_Mbeta hG hMst_mem).2.2.2 p (Fact.out : p.Prime) hpMst hpβ).1
  haveI : K.Normal := hKnorm
  set KG : Subgroup G := K.map (derivedInG Mstar).subtype with hKGdef
  -- `Q ≤ K_G`: 商 `D/K` は `p`-群、`Q` は `r ≠ p` の `r`-群。
  have hQKG : Q ≤ KG := by
    have hQ'le : Q.subgroupOf (derivedInG Mstar) ≤ K := by
      have himg : (Q.subgroupOf (derivedInG Mstar)).map (QuotientGroup.mk' K) = ⊥ := by
        rw [← Subgroup.card_eq_one]
        obtain ⟨P⟩ : Nonempty (Sylow p ↥(derivedInG Mstar)) := inferInstance
        have hPcard : ∃ n : ℕ, Nat.card ↥(P : Subgroup ↥(derivedInG Mstar)) = p ^ n :=
          IsPGroup.iff_card.mp P.2
        obtain ⟨n, hPn⟩ := hPcard
        have hidx : K.index = p ^ n := by
          rw [(hKcompl P).symm.index_eq_card, hPn]
        have h1 : Nat.card ↥((Q.subgroupOf (derivedInG Mstar)).map
            (QuotientGroup.mk' K)) ∣ p ^ n := by
          rw [← hidx]
          exact Subgroup.card_subgroup_dvd_card _
        have h2 : Nat.card ↥((Q.subgroupOf (derivedInG Mstar)).map
            (QuotientGroup.mk' K)) ∣ r ^ (Nat.card ↥E).factorization r := by
          refine dvd_trans (Subgroup.card_map_dvd _ _) ?_
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQD).toEquiv]
          exact hQcard.dvd
        have hco : Nat.Coprime (r ^ (Nat.card ↥E).factorization r) (p ^ n) :=
          Nat.Coprime.pow _ _ ((Nat.coprime_primes hr_prime (Fact.out : p.Prime)).mpr hrp)
        exact (hco.coprime_dvd_left h2).eq_one_of_dvd h1
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg
    intro x hx
    rw [hKGdef]
    exact Subgroup.mem_map.mpr ⟨⟨x, hQD hx⟩, hQ'le (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  -- `⁅A, Q⁆ ≤ A ⊓ K_G = ⊥` ⟹ `Q ≤ C_G(A)`。
  have hD_norm_KG : derivedInG Mstar ≤ Subgroup.normalizer (KG : Set G) := by
    rw [hKGdef]
    have hle := Subgroup.le_normalizer_map (H := K) (derivedInG Mstar).subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hle
  have hKG_pcompl : ¬ p ∣ Nat.card ↥KG := by
    intro hdvd
    rw [hKGdef, Subgroup.card_map_of_injective (derivedInG Mstar).subtype_injective] at hdvd
    obtain ⟨P⟩ : Nonempty (Sylow p ↥(derivedInG Mstar)) := inferInstance
    have hcm := (hKcompl P).card_mul_card
    have hPmul : Nat.card ↥(P : Subgroup ↥(derivedInG Mstar))
        = p ^ (Nat.card ↥(derivedInG Mstar)).factorization p :=
      Sylow.card_eq_multiplicity P
    have hfull : p ^ ((Nat.card ↥(derivedInG Mstar)).factorization p + 1)
        ∣ Nat.card ↥(derivedInG Mstar) := by
      have h2 : p ^ (Nat.card ↥(derivedInG Mstar)).factorization p * p
          ∣ Nat.card ↥(P : Subgroup ↥(derivedInG Mstar)) * Nat.card ↥K :=
        mul_dvd_mul hPmul.symm.dvd hdvd
      rw [pow_succ]
      calc p ^ (Nat.card ↥(derivedInG Mstar)).factorization p * p
          ∣ Nat.card ↥(P : Subgroup ↥(derivedInG Mstar)) * Nat.card ↥K := h2
        _ = Nat.card ↥K * Nat.card ↥(P : Subgroup ↥(derivedInG Mstar)) := mul_comm _ _
        _ = Nat.card ↥(derivedInG Mstar) := hcm
    have := (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out : p.Prime)
      (Nat.card_pos (α := ↥(derivedInG Mstar))).ne').mp hfull
    omega
  have hAKG_bot : A ⊓ KG = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(A ⊓ KG : Subgroup G) ∣ p ^ 2 := by
      rw [← hA.2]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hnp : ¬ p ∣ Nat.card ↥(A ⊓ KG : Subgroup G) := fun hdvd =>
      hKG_pcompl (hdvd.trans (Subgroup.card_dvd_of_le inf_le_right))
    exact Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right 2
        ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hnp).symm) h1
  -- `⁅A, Q⁆ ≤ A ⊓ K_G = ⊥` (Q ≤ E ≤ N(A)、A ≤ D ≤ N(K_G))。
  have hcomm : ⁅A, Q⁆ ≤ A ⊓ KG := by
    rw [Subgroup.commutator_le]
    intro a ha t ht
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : t * a⁻¹ * t⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hEN (hQE ht)) a⁻¹).mp (A.inv_mem ha)
      have h2 : a * (t * a⁻¹ * t⁻¹) ∈ A := A.mul_mem ha h1
      rw [commutatorElement_def]
      simpa [mul_assoc] using h2
    · have h1 : a * t * a⁻¹ ∈ KG :=
        (Subgroup.mem_normalizer_iff.mp (hD_norm_KG (hAD ha)) t).mp (hQKG ht)
      have h2 : a * t * a⁻¹ * t⁻¹ ∈ KG := KG.mul_mem h1 (KG.inv_mem (hQKG ht))
      rwa [commutatorElement_def]
  have hcomm_bot : ⁅A, Q⁆ = ⊥ := le_bot_iff.mp (hAKG_bot ▸ hcomm)
  have hQC : Q ≤ Subgroup.centralizer (A : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm_bot
  -- Sylow `r` が `C_E(A)` に入る ⟹ `r ∤ [E : C_E(A)]`、`hr` と矛盾。
  have hQ₀le : (Q₀ : Subgroup ↥E) ≤
      (E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨x.2, hQC (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)⟩
  have hr_idx : r ∣ ((Q₀ : Subgroup ↥E)).index :=
    (Nat.mem_primeFactors.mp hr).2.1.trans (Subgroup.index_dvd_of_le hQ₀le)
  have hr_card : r ∣ Nat.card ↥(Q₀ : Subgroup ↥E) := by
    rw [hQ₀card]
    exact dvd_pow_self r hfac_pos
  have hco := Q₀.card_coprime_index
  exact hr_prime.ne_one (Nat.dvd_one.mp (hco ▸ Nat.dvd_gcd hr_card hr_idx))

end OddOrder.BG.Ch3.S12
