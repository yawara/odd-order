/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.PGroup
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8D.SubdegreeTwo

/-!
# Isaacs Problem 8D.2 (p. 269) — 次数 8 の原始置換群は 2-transitive

`|Ω| = 8` の原始的で忠実な作用は必ず 2-transitive、すなわち点安定化群は
`Ω ∖ {α}` (7 点) に推移的。

## 証明の流れ

2-transitive でないとすると、`α` 以外に交わらない 2 つの suborbit が取れる。その長さ
`m ≤ k` について:

* `m = 1` (または `k = 1`): `stabilizer_eq_bot_of_ncard_orbit_eq_one` で `G_α = ⊥`,
  すると `|G| = |Ω| = 8` で `G_α = ⊥` は極大 — しかし Cauchy が位数 2 の真部分群を
  与えるので矛盾。
* `m = 2` (または `k = 2`): **8D.1** から `|G_α| = 2` かつ全 suborbit が長さ 2。
  すると `G_α` (位数 2 の `2`-群) の固定点は `α` だけなので
  `|Ω| ≡ |Fix| (mod 2)`, つまり `8 ≡ 1 (mod 2)` で矛盾。
* どちらも `≥ 3`: 3 つ目の suborbit があれば長さ `≥ 3` の交わらない 3 つが 7 点に
  入らない。よって suborbit はちょうど 2 つで `m + k = 7`, すなわち `{m, k} = {3, 4}`。
  互いに素なので **Thm 8.38** (Weiss, `subdegree_eq_one_of_coprime_of_max`) が
  `3 = 1` を強いて矛盾。

## Main results

- `ncard_orbit_stabilizer_eq_of_card_eq_eight` — **Problem 8D.2** 本体。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- Problem 8D.2 -/

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [FaithfulSMul G Ω]

omit [Finite G] [FaithfulSMul G Ω] in
/-- `α` 以外の点の suborbit は `{α}ᶜ` に含まれる。 -/
private lemma orbit_stabilizer_subset_compl {α γ : Ω} (hγ : γ ≠ α) :
    orbit ↥(stabilizer G α) γ ⊆ ({α}ᶜ : Set Ω) := by
  rintro ε ⟨h, rfl⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hc
  refine hγ ?_
  have hc' : (h : G) • γ = α := hc
  have hinv : ((h : G))⁻¹ • α = α :=
    mem_stabilizer_iff.mp ((stabilizer G α).inv_mem h.2)
  calc γ = ((h : G))⁻¹ • ((h : G) • γ) := (inv_smul_smul _ _).symm
    _ = ((h : G))⁻¹ • α := by rw [hc']
    _ = α := hinv

omit [Finite G] [FaithfulSMul G Ω] in
/-- 相異なる suborbit は交わらない。 -/
private lemma orbit_stabilizer_disjoint {α γ δ : Ω}
    (h : δ ∉ orbit ↥(stabilizer G α) γ) :
    Disjoint (orbit ↥(stabilizer G α) γ) (orbit ↥(stabilizer G α) δ) := by
  rw [Set.disjoint_left]
  intro ε hεγ hεδ
  refine h ?_
  have h1 : orbit ↥(stabilizer G α) ε = orbit ↥(stabilizer G α) γ :=
    (orbit_eq_iff (a := ε) (b := γ)).mpr hεγ
  have h2 : orbit ↥(stabilizer G α) ε = orbit ↥(stabilizer G α) δ :=
    (orbit_eq_iff (a := ε) (b := δ)).mpr hεδ
  rw [← h1, h2]
  exact mem_orbit_self δ

/-- **Isaacs Problem 8D.2** (p. 269)。次数 8 の原始置換群は 2-transitive:
点安定化群は `Ω ∖ {α}` (7 点) に推移的で, 各 suborbit の長さは 7。 -/
theorem ncard_orbit_stabilizer_eq_of_card_eq_eight [IsPreprimitive G Ω]
    (hΩ : Nat.card Ω = 8) {α γ : Ω} (hγ : γ ≠ α) :
    Set.ncard (orbit ↥(stabilizer G α) γ) = 7 := by
  classical
  haveI : Finite Ω := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hcompl : ({α}ᶜ : Set Ω).ncard = 7 := by
    have h := Set.ncard_add_ncard_compl ({α} : Set Ω)
    rw [Set.ncard_singleton, hΩ] at h
    omega
  -- 長さ 1 の suborbit は存在しない
  have hne1 : ∀ δ : Ω, δ ≠ α → Set.ncard (orbit ↥(stabilizer G α) δ) ≠ 1 := by
    intro δ hδ h1
    have hbot : stabilizer G α = ⊥ := stabilizer_eq_bot_of_ncard_orbit_eq_one hδ h1
    -- `G_α = ⊥` かつ極大 ⟹ `G` に真の非自明部分群が無い; しかし `|G| = 8`
    have hcard : Nat.card G = 8 := by
      have h := index_stabilizer_of_transitive (G := G) (x := α)
      rw [hbot, Subgroup.index_bot, hΩ] at h
      exact h
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (by rw [hcard]; norm_num)
    have hcoat : IsCoatom (stabilizer G α) :=
      MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) α
    rw [hbot] at hcoat
    have hlt : (⊥ : Subgroup G) < Subgroup.zpowers x := by
      refine lt_of_le_of_ne bot_le (Ne.symm ?_)
      intro hc
      have hx1 : x = 1 := by
        have hmem := Subgroup.mem_zpowers x
        rw [hc, Subgroup.mem_bot] at hmem
        exact hmem
      rw [hx1, orderOf_one] at hx
      omega
    have htop := hcoat.2 _ hlt
    have hzc : Nat.card ↥(Subgroup.zpowers x) = 2 := by rw [Nat.card_zpowers, hx]
    rw [htop, Subgroup.card_top, hcard] at hzc
    omega
  -- 長さ 2 の suborbit も存在しない
  have hne2 : ∀ δ : Ω, δ ≠ α → Set.ncard (orbit ↥(stabilizer G α) δ) ≠ 2 := by
    intro δ hδ h2
    have hstab : Nat.card ↥(stabilizer G α) = 2 :=
      card_stabilizer_eq_two_of_subdegree_eq_two h2
    -- `G_α` の固定点は `α` のみ
    have hfix : (fixedPoints ↥(stabilizer G α) Ω) = {α} := by
      ext ε
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hε
        by_contra hc
        refine hne1 ε hc ?_
        have : orbit ↥(stabilizer G α) ε = {ε} := by
          ext y
          constructor
          · rintro ⟨h, rfl⟩
            exact Set.mem_singleton_iff.mpr (hε h)
          · rintro rfl
            exact mem_orbit_self _
        rw [this, Set.ncard_singleton]
      · rintro rfl
        intro h
        exact h.2
    have hp2 : IsPGroup 2 ↥(stabilizer G α) :=
      IsPGroup.of_card (n := 1) (by rw [hstab, pow_one])
    have hmod := hp2.card_modEq_card_fixedPoints Ω
    rw [hΩ, hfix] at hmod
    have h1 : Nat.card ↥({α} : Set Ω) = 1 := by simp
    rw [h1] at hmod
    unfold Nat.ModEq at hmod
    omega
  -- 2-transitive でないと仮定して矛盾を導く
  by_contra hne7
  have hsubset := orbit_stabilizer_subset_compl (G := G) hγ
  have hlt : Set.ncard (orbit ↥(stabilizer G α) γ) < 7 := by
    have hle : Set.ncard (orbit ↥(stabilizer G α) γ) ≤ 7 :=
      hcompl ▸ Set.ncard_le_ncard hsubset (Set.toFinite _)
    omega
  -- `Ω ∖ ({α} ∪ orbit γ)` に点 `δ` がある
  obtain ⟨δ, hδmem⟩ : (({α}ᶜ : Set Ω) \ orbit ↥(stabilizer G α) γ).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    rw [Set.sdiff_eq_empty] at hc
    have heq : orbit ↥(stabilizer G α) γ = ({α}ᶜ : Set Ω) := Set.Subset.antisymm hsubset hc
    rw [heq, hcompl] at hlt
    omega
  have hδα : δ ≠ α := hδmem.1
  have hδnot : δ ∉ orbit ↥(stabilizer G α) γ := hδmem.2
  have hdisj := orbit_stabilizer_disjoint (G := G) hδnot
  -- 両方の長さは `≥ 3`
  have h3γ : 3 ≤ Set.ncard (orbit ↥(stabilizer G α) γ) := by
    have hpos : 0 < Set.ncard (orbit ↥(stabilizer G α) γ) :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨γ, mem_orbit_self _⟩
    have := hne1 γ hγ
    have := hne2 γ hγ
    omega
  have h3δ : 3 ≤ Set.ncard (orbit ↥(stabilizer G α) δ) := by
    have hpos : 0 < Set.ncard (orbit ↥(stabilizer G α) δ) :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨δ, mem_orbit_self _⟩
    have := hne1 δ hδα
    have := hne2 δ hδα
    omega
  -- 2 つの suborbit で `{α}ᶜ` を尽くす (3 つ目は入らない)
  have hunion : orbit ↥(stabilizer G α) γ ∪ orbit ↥(stabilizer G α) δ = ({α}ᶜ : Set Ω) := by
    refine Set.Subset.antisymm (Set.union_subset hsubset
      (orbit_stabilizer_subset_compl (G := G) hδα)) fun ε hε => ?_
    by_contra hc
    rw [Set.mem_union] at hc
    push Not at hc
    have hεα : ε ≠ α := hε
    have hdisj1 := orbit_stabilizer_disjoint (G := G) (γ := γ) (δ := ε) hc.1
    have hdisj2 := orbit_stabilizer_disjoint (G := G) (γ := δ) (δ := ε) hc.2
    have h3ε : 3 ≤ Set.ncard (orbit ↥(stabilizer G α) ε) := by
      have hpos : 0 < Set.ncard (orbit ↥(stabilizer G α) ε) :=
        (Set.ncard_pos (Set.toFinite _)).mpr ⟨ε, mem_orbit_self _⟩
      have := hne1 ε hεα
      have := hne2 ε hεα
      omega
    have hsub3 : orbit ↥(stabilizer G α) γ ∪ orbit ↥(stabilizer G α) δ ∪
        orbit ↥(stabilizer G α) ε ⊆ ({α}ᶜ : Set Ω) :=
      Set.union_subset (Set.union_subset hsubset (orbit_stabilizer_subset_compl (G := G) hδα))
        (orbit_stabilizer_subset_compl (G := G) hεα)
    have hcard3 : Set.ncard (orbit ↥(stabilizer G α) γ ∪ orbit ↥(stabilizer G α) δ ∪
        orbit ↥(stabilizer G α) ε) =
        Set.ncard (orbit ↥(stabilizer G α) γ) + Set.ncard (orbit ↥(stabilizer G α) δ) +
          Set.ncard (orbit ↥(stabilizer G α) ε) := by
      rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hdisj1, hdisj2⟩)
          (Set.toFinite _) (Set.toFinite _),
        Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    have hle3 := Set.ncard_le_ncard hsub3 (Set.toFinite _)
    rw [hcard3, hcompl] at hle3
    omega
  -- したがって長さの和は 7, `{3, 4}` に限る
  have hsum : Set.ncard (orbit ↥(stabilizer G α) γ) + Set.ncard (orbit ↥(stabilizer G α) δ)
      = 7 := by
    rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hunion, hcompl]
  -- 長さは `{3, 4}` に限られ, 互いに素なので Weiss (Thm 8.38) で矛盾
  have hmax : ∀ ε : Ω, Set.ncard (orbit ↥(stabilizer G α) ε) ≤ 4 := by
    intro ε
    rcases eq_or_ne ε α with rfl | hεα
    · rw [orbit_stabilizer_self, Set.ncard_singleton]
      omega
    · have hmem : ε ∈ ({α}ᶜ : Set Ω) := hεα
      rw [← hunion, Set.mem_union] at hmem
      rcases hmem with h | h
      · rw [(orbit_eq_iff (a := ε) (b := γ)).mpr h]
        omega
      · rw [(orbit_eq_iff (a := ε) (b := δ)).mpr h]
        omega
  rcases (by omega : (Set.ncard (orbit ↥(stabilizer G α) γ) = 3 ∧
      Set.ncard (orbit ↥(stabilizer G α) δ) = 4) ∨
      (Set.ncard (orbit ↥(stabilizer G α) γ) = 4 ∧
        Set.ncard (orbit ↥(stabilizer G α) δ) = 3)) with ⟨hm, hn⟩ | ⟨hn, hm⟩
  · -- `γ` 側が 3, `δ` 側が 4 (最大)
    have hcop : Nat.Coprime (Set.ncard (orbit ↥(stabilizer G α) γ))
        (Set.ncard (orbit ↥(stabilizer G α) δ)) := by rw [hm, hn]; decide
    have h1 := subdegree_eq_one_of_coprime_of_max (G := G) α (β₀ := δ) (γ₀ := γ)
      rfl (fun ε => by rw [hn]; exact hmax ε) rfl hcop
    omega
  · -- `δ` 側が 3, `γ` 側が 4 (最大)
    have hcop : Nat.Coprime (Set.ncard (orbit ↥(stabilizer G α) δ))
        (Set.ncard (orbit ↥(stabilizer G α) γ)) := by rw [hm, hn]; decide
    have h1 := subdegree_eq_one_of_coprime_of_max (G := G) α (β₀ := γ) (γ₀ := δ)
      rfl (fun ε => by rw [hn]; exact hmax ε) rfl hcop
    omega

end -- Problem 8D.2

end OddOrder.Isaacs.Ch08
