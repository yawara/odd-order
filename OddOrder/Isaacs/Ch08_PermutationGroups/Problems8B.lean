/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.GroupAction.Primitive
import OddOrder.Isaacs.Ch02_Subnormality.Basic
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.RegularRepresentations

/-!
# Isaacs, Finite Group Theory — Problems 8B (pp. 248–249)

Isaacs §8B (block と原始性) の章末演習。**block** は mathlib の `MulAction.IsBlock` が
Isaacs の定義 (「`Δ` の translate は `Δ` 自身か, `Δ` と交わらないかのいずれか」) と
そのまま一致する (`IsBlock G B := ∀ g₁ g₂, g₁ • B ≠ g₂ • B → Disjoint (g₁ • B) (g₂ • B)`)。

## Main results

- `blockCore`, `mem_blockCore`, `smul_blockCore_eq_of_mem`, `isBlock_blockCore` —
  **Problem 8B.1**: `α` を含む `X` の translate すべての共通部分は block。
- `exists_smul_mem_and_smul_notMem` — **Problem 8B.2**: 原始群では, 空でない真部分集合 `X`
  と相異なる 2 点 `α ≠ β` に対し `g • α ∈ X` かつ `g • β ∉ X` となる `g` がある。
- `isPretransitive_of_normal_of_isPreprimitive`, `inf_eq_bot_of_isMinimalNormal_of_ne`,
  `inf_stabilizer_eq_bot_of_normal_of_inf_eq_bot`,
  `regular_centralizer_mulEquiv_of_two_isMinimalNormal` — **Problem 8B.3**: 原始置換群の
  相異なる 2 つの極小正規部分群 `M`, `N` は regular で, `C_G(M) = N`, `C_G(N) = M`,
  `M ≅ N`。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problems 8B (pp. 248-249) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-! ### Problem 8B.1 — translate の共通部分は block -/

variable (G) in
/-- **Isaacs Problem 8B.1** (p. 248) の `Δ`: `α` を含む `X` の translate すべての共通部分。 -/
def blockCore (α : Ω) (X : Set Ω) : Set Ω := ⋂ g ∈ {g : G | α ∈ g • X}, g • X

lemma mem_blockCore (α : Ω) (X : Set Ω) : α ∈ blockCore G α X := by
  simp only [blockCore, Set.mem_iInter]
  exact fun _ hg => hg

lemma smul_blockCore (h : G) (α : Ω) (X : Set Ω) :
    h • blockCore G α X = ⋂ g ∈ {g : G | α ∈ g • X}, (h * g) • X := by
  simp only [blockCore, Set.smul_set_iInter, ← mul_smul]

/-- `α ∈ h • Δ` は「`h` が `S = {g | α ∈ g • X}` を左から保つ」ことと同値。 -/
lemma mem_smul_blockCore_iff (h : G) (α : Ω) (X : Set Ω) :
    α ∈ h • blockCore G α X ↔ ∀ g : G, α ∈ g • X → α ∈ (h * g) • X := by
  rw [smul_blockCore]
  simp only [Set.mem_iInter, Set.mem_setOf_eq]

/-- **8B.1 の核心**: `α ∈ h • Δ` なら `h • Δ = Δ`。

`S := {g | α ∈ g • X}` とおくと `α ∈ h • Δ` は `h · S ⊆ S` を意味し, `G` が有限なので
左移動の単射性から `h · S = S`。したがって `h • Δ = ⋂_{g ∈ h·S} g • X = Δ`。 -/
lemma smul_blockCore_eq_of_mem [Finite G] {h : G} {α : Ω} {X : Set Ω}
    (hmem : α ∈ h • blockCore G α X) : h • blockCore G α X = blockCore G α X := by
  have hmaps : Set.MapsTo (fun g : G => h * g) {g : G | α ∈ g • X} {g : G | α ∈ g • X} :=
    fun g hg => (mem_smul_blockCore_iff h α X).mp hmem g hg
  have hbij : Set.BijOn (fun g : G => h * g) {g : G | α ∈ g • X} {g : G | α ∈ g • X} :=
    ((Set.toFinite _).injOn_iff_bijOn_of_mapsTo hmaps).mp
      fun _ _ _ _ hab => mul_left_cancel hab
  rw [smul_blockCore]
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · simp only [blockCore, Set.mem_iInter, Set.mem_setOf_eq] at hx ⊢
    intro g' hg'
    obtain ⟨g, hg, rfl⟩ := hbij.surjOn (show g' ∈ {g : G | α ∈ g • X} from hg')
    exact hx g hg
  · simp only [blockCore, Set.mem_iInter, Set.mem_setOf_eq] at hx ⊢
    exact fun g hg => hx (h * g) (hmaps hg)

/-- **Isaacs Problem 8B.1** (p. 248) 🎉: `G` が `Ω` に推移的なとき, `α` を含む `X` の
translate すべての共通部分 `Δ` は **block**。

`α ∈ h • Δ ⟺ h • Δ = Δ` (`smul_blockCore_eq_of_mem`) から
`G_α ≤ G_{Δ}` かつ `Δ = orbit G_{Δ} α` が従い, 「点安定化群を含む部分群の軌道は block」
(`MulAction.IsBlock.of_orbit`) に帰着する。 -/
theorem isBlock_blockCore [Finite G] [IsPretransitive G Ω] (α : Ω) (X : Set Ω) :
    IsBlock G (blockCore G α X) := by
  have hstab : stabilizer G α ≤ stabilizer G (blockCore G α X) := by
    intro s hs
    refine mem_stabilizer_iff.mpr (smul_blockCore_eq_of_mem ?_)
    have : s • α ∈ s • blockCore G α X :=
      Set.smul_mem_smul_set (mem_blockCore (G := G) α X)
    rwa [mem_stabilizer_iff.mp hs] at this
  have horbit : orbit ↥(stabilizer G (blockCore G α X)) α = blockCore G α X := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨k, rfl⟩
      have hk : (k : G) • blockCore G α X = blockCore G α X := mem_stabilizer_iff.mp k.2
      have : (k : G) • α ∈ (k : G) • blockCore G α X :=
        Set.smul_mem_smul_set (mem_blockCore (G := G) α X)
      rwa [hk] at this
    · intro β hβ
      obtain ⟨k, hk⟩ := exists_smul_eq G α β
      have hmem : α ∈ k⁻¹ • blockCore G α X := by
        refine Set.mem_smul_set.mpr ⟨β, hβ, ?_⟩
        rw [← hk, inv_smul_smul]
      have hkinv : k⁻¹ ∈ stabilizer G (blockCore G α X) :=
        mem_stabilizer_iff.mpr (smul_blockCore_eq_of_mem hmem)
      exact ⟨⟨k, (Subgroup.inv_mem_iff _).mp hkinv⟩, hk⟩
  rw [← horbit]
  exact IsBlock.of_orbit hstab

/-! ### Problem 8B.2 — 原始群は 2 点を分離する translate をもつ -/

/-- **Isaacs Problem 8B.2** (p. 248) 🎉: `G` が `Ω` に原始的で `α ≠ β`, `X` が空でない
真部分集合なら, **`g • α ∈ X` かつ `g • β ∉ X`** となる `g ∈ G` が存在する。

対偶を取ると「すべての `g` で `g • α ∈ X → g • β ∈ X`」。このとき 8B.1 の block
`Δ = ⋂ {g • X : α ∈ g • X}` (`blockCore`) が `α` と `β` を**両方**含む。原始性より
`Δ` は自明な block だが, `α ≠ β` から subsingleton ではないので `Δ = Ω`。ところが
推移性と `X ≠ ∅` から `α ∈ g • X` なる `g` が取れて `Δ ⊆ g • X` なので `g • X = Ω`,
すなわち `X = Ω` となり `X` が真部分集合であることに反する。 -/
theorem exists_smul_mem_and_smul_notMem [Finite G] [IsPreprimitive G Ω]
    {α β : Ω} (hαβ : α ≠ β) {X : Set Ω} (hX : X.Nonempty) (hXne : X ≠ Set.univ) :
    ∃ g : G, g • α ∈ X ∧ g • β ∉ X := by
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ g, g • α ∈ X → g • β ∈ X` から `β ∈ Δ`。
  have hβ : β ∈ blockCore G α X := by
    simp only [blockCore, Set.mem_iInter, Set.mem_setOf_eq]
    intro g hg
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hg ⊢
    exact hcon g⁻¹ hg
  rcases IsPreprimitive.isTrivialBlock_of_isBlock (isBlock_blockCore (G := G) α X) with
    hsub | huniv
  · exact hαβ (hsub (mem_blockCore (G := G) α X) hβ)
  · -- `Δ = Ω` だが `Δ ⊆ g • X`。
    obtain ⟨x, hx⟩ := hX
    obtain ⟨g, hg⟩ := exists_smul_eq G x α
    have hmem : α ∈ (g • X : Set Ω) := ⟨x, hx, hg⟩
    have hsub : blockCore G α X ⊆ (g • X : Set Ω) := by
      simp only [blockCore]
      exact Set.biInter_subset_of_mem (t := fun g : G => (g • X : Set Ω)) hmem
    rw [huniv] at hsub
    refine hXne ?_
    have hgX : (g • X : Set Ω) = Set.univ := Set.eq_univ_of_univ_subset hsub
    have : X = g⁻¹ • (g • X : Set Ω) := (inv_smul_smul g X).symm
    rw [this, hgX]
    simp

/-! ### Problem 8B.3 — 原始群の相異なる 2 つの極小正規部分群 -/

/-- **原始群の自明でない正規部分群は推移的**。

正規部分群の軌道は block (`MulAction.IsBlock.orbit_of_normal`) なので, 原始性より
subsingleton か `Ω` 全体。忠実性から `N ≠ ⊥` は動かす点をもつので前者ではありえない。 -/
theorem isPretransitive_of_normal_of_isPreprimitive [FaithfulSMul G Ω] [IsPreprimitive G Ω]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : IsPretransitive ↥N Ω := by
  obtain ⟨n, hnN, hn1⟩ : ∃ n : G, n ∈ N ∧ n ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hN (le_antisymm (fun x hx => Subgroup.mem_bot.mpr (hc x hx)) bot_le)
  obtain ⟨α, hα⟩ : ∃ α : Ω, n • α ≠ α := by
    by_contra hc
    push Not at hc
    exact hn1 (FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun β => by rw [hc β, one_smul])
  have hnotsub : ¬ (orbit ↥N α).Subsingleton := fun hsub =>
    hα (hsub (mem_orbit α (⟨n, hnN⟩ : ↥N)) (mem_orbit_self α))
  rcases IsPreprimitive.isTrivialBlock_of_isBlock
    (IsBlock.orbit_of_normal (N := N) α) with h | h
  · exact absurd h hnotsub
  · exact (isPretransitive_iff_orbit_eq_univ α).mpr h

/-- 相異なる 2 つの極小正規部分群は交わらない。 -/
lemma inf_eq_bot_of_isMinimalNormal_of_ne {M N : Subgroup G}
    (hM : Ch02.IsMinimalNormal M) (hN : Ch02.IsMinimalNormal N) (hMN : M ≠ N) :
    M ⊓ N = ⊥ := by
  haveI : M.Normal := hM.1
  haveI : N.Normal := hN.1
  rcases hM.2.2 (M ⊓ N) inferInstance inf_le_left with h | h
  · exact h
  · exact absurd ((hN.2.2 M inferInstance (h ▸ inf_le_right)).resolve_left hM.2.1) hMN

/-- 交わらない正規部分群の一方が推移的なら, もう一方は**半正則** (8A.2 の帰結)。 -/
lemma inf_stabilizer_eq_bot_of_normal_of_inf_eq_bot [FaithfulSMul G Ω] {U V : Subgroup G}
    [U.Normal] [V.Normal] [IsPretransitive ↥U Ω] (h : U ⊓ V = ⊥) (α : Ω) :
    V ⊓ stabilizer G α = ⊥ := by
  refine le_antisymm ?_ bot_le
  calc V ⊓ stabilizer G α ≤ Subgroup.centralizer (U : Set G) ⊓ stabilizer G α :=
        inf_le_inf_right _ (le_centralizer_of_normal_of_inf_eq_bot h)
    _ = ⊥ := centralizer_inf_stabilizer_eq_bot (H := U) α

/-- **Isaacs Problem 8B.3** (p. 248) 🎉: 原始置換群 `G` が相異なる極小正規部分群
`M`, `N` をもてば,

* (a) `M`, `N` はともに **regular**,
* (b) `C_G(M) = N` かつ `C_G(N) = M`,
* (c) `M ≅ N`。

`M ⊓ N = ⊥` (極小性) と「原始群の非自明正規部分群は推移的」から `M`, `N` は推移的。
交わらない正規部分群は可換なので `M ≤ C_G(N)` で, `N` が推移的だから 8A.2
(`centralizer_inf_stabilizer_eq_bot`) より `C_G(N)` は半正則, したがって `M` も半正則
= 推移的かつ半正則 = **regular**。あとは 8A.4
(`centralizer_eq_of_regular_of_inf_eq_bot`, `mulEquiv_and_center_eq_bot_of_regular_normal`)
をそのまま当てるだけ (教科書の Hint どおり)。 -/
theorem regular_centralizer_mulEquiv_of_two_isMinimalNormal [FaithfulSMul G Ω]
    [IsPreprimitive G Ω] {M N : Subgroup G} (hM : Ch02.IsMinimalNormal M)
    (hN : Ch02.IsMinimalNormal N) (hMN : M ≠ N) (α : Ω) :
    Function.Bijective (smulBase M α) ∧ Function.Bijective (smulBase N α) ∧
      Subgroup.centralizer (M : Set G) = N ∧ Subgroup.centralizer (N : Set G) = M ∧
      Nonempty (↥M ≃* ↥N) := by
  haveI : M.Normal := hM.1
  haveI : N.Normal := hN.1
  have hinf : M ⊓ N = ⊥ := inf_eq_bot_of_isMinimalNormal_of_ne hM hN hMN
  have hinf' : N ⊓ M = ⊥ := by rw [inf_comm]; exact hinf
  haveI : IsPretransitive ↥M Ω := isPretransitive_of_normal_of_isPreprimitive M hM.2.1
  haveI : IsPretransitive ↥N Ω := isPretransitive_of_normal_of_isPreprimitive N hN.2.1
  -- 半正則性: `M ≤ C_G(N)` と 8A.2。
  have hMreg : Function.Bijective (smulBase M α) :=
    (bijective_smulBase_iff M α).mpr ⟨inferInstance,
      inf_stabilizer_eq_bot_of_normal_of_inf_eq_bot (U := N) (V := M) hinf' α⟩
  have hNreg : Function.Bijective (smulBase N α) :=
    (bijective_smulBase_iff N α).mpr ⟨inferInstance,
      inf_stabilizer_eq_bot_of_normal_of_inf_eq_bot (U := M) (V := N) hinf α⟩
  exact ⟨hMreg, hNreg,
    centralizer_eq_of_regular_of_inf_eq_bot hMreg hNreg hinf,
    centralizer_eq_of_regular_of_inf_eq_bot hNreg hMreg hinf',
    (mulEquiv_and_center_eq_bot_of_regular_normal hMreg hNreg hinf).1⟩

end

end OddOrder.Isaacs.Ch08
