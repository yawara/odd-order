/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Corollary1210

/-!
# BG §12: `SubgroupESetup` の存在 (Lemma 12.11 の前提インフラ)

**スコープ**: BG §12 冒頭 (mmd L3025) の "Recall our choice of `E`, `E₁`, `E₂`, `E₃`"
に対応する **存在文** `exists_subgroupESetup`。

Lemma 12.11 (とその先の §12 後半・§13) は `M* ∈ ℳ(N_G(A))` に対して §12 の諸結果
(12.5/12.6/12.7/12.10) を **`M*` 側で**適用するため、任意の maximal subgroup に
`SubgroupESetup` データが取れることが必要になる。これまでの §12 の全定理は setup を
仮定で受けるだけで、存在文は本ファイルが初出。

**構成**: `M_σ` は `M` の normal Hall `σ(M)`-部分群 (`S10.Msigma_subgroupOf_isHall`)
なので Schur–Zassenhaus (`Subgroup.exists_right_complement'_of_coprime`) で補群 `E` を
取る。`E` は solvable なので Hall `τ₁∪τ₂`-部分群 `K₀` が存在し (`Ch03.hall_E_exists`)、
`K₀` の中で Hall `τ₁`- と Hall `τ₂`-部分群 `H₁, H₂` を取る。`H₁.index` は `τ₂`-数、
`H₂.index` は `τ₁`-数なので互いに素、よって `H₁ ⊔ H₂ = K₀`
(`Ch03.sup_eq_top_of_coprime_index`) — これが `E₁₂_hall` field を満たす鍵。
`E₃` は独立な Hall `τ₃`-部分群。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

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

end OddOrder.BG.Ch3.S12
