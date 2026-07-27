/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.GroupAction.Primitive
import OddOrder.Isaacs.Ch02_Subnormality.Basic
import OddOrder.Isaacs.Ch03_SplitExtensions.Basic
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.RegularRepresentations
import OddOrder.Isaacs.Ch08_PermutationGroups.Subdegrees
import OddOrder.GroupTheory.CyclicSylowBurnside
import OddOrder.GroupTheory.FixedPointFreeConjugation

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
- `bijective_smulBase_of_normal_of_comm`,
  `prime_pow_card_and_unique_isMinimalNormal_of_solvable` — **Problem 8B.4**: 可解原始
  置換群の次数は素数冪で, 極小正規部分群はただ一つ。
- `prime_card_of_isCoatom_bot`, `stabilizer_eq_bot_and_prime_card_of_fixed_point` —
  **Problem 8B.5**: 点安定化群 `G_α` が `Ω ∖ {α}` に固定点をもてば `G_α = 1` で
  `|G|` は素数。
- `eq_bot_of_normal_le_stabilizer`, `card_stabilizer_eq_two_of_suborbit_ncard_eq_two` —
  **Problem 8B.6 前半**: 点安定化群が `Ω ∖ {α}` に長さ 2 の軌道をもてば `|G_α| = 2`。
  ⚠ 後半 (`G ≅ D₂ₚ`, `p > 2` 素数) は未完。
- `inf_stabilizer_eq_bot_of_card_stabilizer_eq_two`, `odd_card_of_card_stabilizer_eq_two`,
  `exists_regular_normal_of_card_stabilizer_eq_two` — **8B.6 後半への構造定理**:
  `|G_α| = 2` なら相異なる 2 点の安定化群は自明に交わり, `|Ω|` は奇数で, `Ω` に正則に
  作用する正規部分群 `K` (位数 `|Ω|`) がある (Burnside の正規 `p`-補元定理)。
- `prime_card_of_card_stabilizer_eq_two` — **8B.6 の次数部分**: `|G_α| = 2` の原始置換群
  の次数 `|Ω|` は奇素数 (`t` が `K` を反転 ⟹ `K` の部分群はすべて `G` に正規 ⟹ その軌道
  が block ⟹ 原始性で `K` は真の非自明部分群をもたない)。
  ⚠ `G ≅ D₂ₚ` の同型そのものは未形式化。
- `oddCore`, `isPGroup_two_of_oddCore_eq_bot`, `smul_eq_self_of_odd_of_sq_smul_eq`,
  `smul_eq_self_of_odd_of_ncard_le_two` — **Problem 8B.7 への道具**: 奇位数元が生成する
  部分群 (`O²`) と, 奇位数元が高々 2 点の不変集合を各点固定すること。
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

/-! ### Problem 8B.4 — 可解原始群の次数は素数冪, 極小正規部分群は一意 -/

/-- 推移的な**可換**正規部分群は regular: `N ≤ C_G(N)` と 8A.2 から半正則。 -/
lemma bijective_smulBase_of_normal_of_comm [FaithfulSMul G Ω] {N : Subgroup G} [N.Normal]
    [IsPretransitive ↥N Ω] (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (α : Ω) :
    Function.Bijective (smulBase N α) := by
  refine (bijective_smulBase_iff N α).mpr ⟨inferInstance, le_antisymm ?_ bot_le⟩
  calc N ⊓ stabilizer G α ≤ Subgroup.centralizer (N : Set G) ⊓ stabilizer G α :=
        inf_le_inf_right _ fun x hx =>
          Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
    _ = ⊥ := centralizer_inf_stabilizer_eq_bot (H := N) α

/-- **Isaacs Problem 8B.4** (p. 248) 🎉: **可解**な原始置換群 `G` について,
次数 `|Ω|` は**素数冪**であり, `G` の極小正規部分群は**ただ一つ**。

極小正規部分群 `N` は (可解性より) elementary abelian で, 原始性より推移的。可換なので
`N ≤ C_G(N)` となり 8A.2 から半正則, したがって **regular** で `|Ω| = |N| = p^n`。
一意性: もう一つ極小正規 `M ≠ N` があると 8B.3 より `C_G(N) = M` だが, `N` は可換なので
`N ≤ C_G(N) = M`, 一方 `M ⊓ N = ⊥` だから `N = ⊥` となり極小性に反する。 -/
theorem prime_pow_card_and_unique_isMinimalNormal_of_solvable [Finite G] [FaithfulSMul G Ω]
    [IsPreprimitive G Ω] [IsSolvable G] [Nontrivial G] :
    (∃ p n : ℕ, p.Prime ∧ Nat.card Ω = p ^ n) ∧
      ∃! N : Subgroup G, Ch02.IsMinimalNormal N := by
  obtain ⟨N, hN, -⟩ := Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
  haveI : N.Normal := hN.1
  haveI : IsPretransitive ↥N Ω := isPretransitive_of_normal_of_isPreprimitive N hN.2.1
  have habel := Ch03.solvable_minimal_normal_isAbelian hN
  obtain ⟨p, hp, helem⟩ := Ch03.solvable_minimal_normal_isElementaryAbelian hN
  haveI : Nonempty Ω := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    exact hg (FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun β => isEmptyElim β)
  obtain ⟨α⟩ := ‹Nonempty Ω›
  have hcard : Nat.card Ω = Nat.card ↥N :=
    (Nat.card_eq_of_bijective _ (bijective_smulBase_of_normal_of_comm habel α)).symm
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := helem.isPGroup.exists_card_eq
  refine ⟨⟨p, n, hp, by rw [hcard, hn]⟩, N, hN, fun M hM => ?_⟩
  by_contra hMN
  obtain ⟨-, -, -, hcN, -⟩ := regular_centralizer_mulEquiv_of_two_isMinimalNormal hM hN hMN α
  have hNle : N ≤ Subgroup.centralizer (N : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => habel y hy x hx
  have hinf : M ⊓ N = ⊥ := inf_eq_bot_of_isMinimalNormal_of_ne hM hN hMN
  exact hN.2.1 (le_bot_iff.mp (hinf ▸ le_inf (hcN ▸ hNle) le_rfl))

/-! ### Problem 8B.5 — 点安定化群が他の点を固定すれば自明で `|G|` は素数 -/

/-- 部分群が `⊥` と `⊤` しかない有限群は**素数位数**。

`Nat.card G` の素因数 `p` を取り Cauchy で位数 `p` の元 `y` を作ると
`⊥ < ⟨y⟩` なので `⟨y⟩ = ⊤`, すなわち `|G| = orderOf y = p`。 -/
lemma prime_card_of_isCoatom_bot [Finite G] (h : IsCoatom (⊥ : Subgroup G)) :
    (Nat.card G).Prime := by
  classical
  haveI := Fintype.ofFinite G
  have hnt : Nontrivial G := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact h.1 (le_antisymm bot_le fun x _ =>
      Subgroup.mem_bot.mpr (Subsingleton.elim x 1))
  have hcard1 : Nat.card G ≠ 1 := fun hc =>
    (not_nontrivial_iff_subsingleton.mpr (Nat.card_eq_one_iff_unique.mp hc).1) hnt
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := G) p
    (by rwa [← Nat.card_eq_fintype_card])
  have hy1 : y ≠ 1 := fun hc => hp.ne_one (by rw [hc, orderOf_one] at hy; exact hy.symm)
  have htop : Subgroup.zpowers y = ⊤ :=
    h.2 _ (bot_lt_iff_ne_bot.mpr (Subgroup.zpowers_ne_bot.mpr hy1))
  have hcard : Nat.card G = p := by
    rw [← hy, ← Nat.card_zpowers y, htop]
    simp
  rw [hcard]
  exact hp

/-- **Isaacs Problem 8B.5** (p. 249) 🎉: 原始置換群 `G` の点安定化群 `H = G_α` が
`Ω ∖ {α}` に固定点をもてば, **`H = 1` かつ `|G|` は素数**。

原始性より `H` は極大部分群 (`IsCoatom`)。`H ≤ G_β` で `G_β ≠ G` (推移性 + `|Ω| ≥ 2`)
だから `H = G_β`。`g • α = β` なる `g` は `g ∉ H` かつ `g ∈ N_G(H)` なので
`H < N_G(H)`, 極大性から `N_G(H) = G`, すなわち **`H ⊴ G`**。正規かつ `H ≤ G_α` なら
`H` はすべての点を固定するので, 忠実性から `H = 1`。すると `⊥` が極大部分群になり
`|G|` は素数。 -/
theorem stabilizer_eq_bot_and_prime_card_of_fixed_point [Finite G] [FaithfulSMul G Ω]
    [IsPreprimitive G Ω] [Nontrivial Ω] {α β : Ω} (hαβ : α ≠ β)
    (hfix : ∀ h ∈ stabilizer G α, h • β = β) :
    stabilizer G α = ⊥ ∧ (Nat.card G).Prime := by
  have hcoatom : IsCoatom (stabilizer G α) :=
    IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) α
  -- `G_β ≠ G` (さもなくば推移性から `Ω` が 1 点)。
  have hβtop : stabilizer G β ≠ ⊤ := by
    intro hc
    obtain ⟨x, y, hxy⟩ := exists_pair_ne Ω
    have hall : ∀ γ : Ω, γ = β := fun γ => by
      obtain ⟨g, hg⟩ := exists_smul_eq G β γ
      rw [← hg]
      exact mem_stabilizer_iff.mp (hc ▸ Subgroup.mem_top g)
    exact hxy ((hall x).trans (hall y).symm)
  -- 極大性から `G_α = G_β`。
  have hle : stabilizer G α ≤ stabilizer G β := fun h hh => mem_stabilizer_iff.mpr (hfix h hh)
  have heq : stabilizer G α = stabilizer G β :=
    (lt_or_eq_of_le hle).resolve_left fun hlt => hβtop (hcoatom.2 _ hlt)
  -- `g • α = β` なる `g` は `N_G(G_α)` に入るが `G_α` には入らない。
  obtain ⟨g, hg⟩ := exists_smul_eq G α β
  have hgnot : g ∉ stabilizer G α := fun hc => hαβ (by rw [← hg, mem_stabilizer_iff.mp hc])
  have hconj : ∀ h : G, h ∈ stabilizer G α ↔ g⁻¹ * h * g ∈ stabilizer G α := by
    intro h
    refine (Iff.of_eq (by rw [heq])).trans ?_
    rw [← hg]
    simp only [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
  have hgnorm : g ∈ Subgroup.normalizer (stabilizer G α) :=
    Subgroup.mem_normalizer_iff''.mpr hconj
  haveI hnormal : (stabilizer G α).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact hcoatom.2 _ (lt_of_le_of_ne Subgroup.le_normalizer fun hc => hgnot (hc ▸ hgnorm))
  -- 正規な点安定化群はすべての点を固定 ⟹ 忠実性から自明。
  have htriv : ∀ h ∈ stabilizer G α, ∀ γ : Ω, h • γ = γ := by
    intro h hh γ
    obtain ⟨k, hk⟩ := exists_smul_eq G α γ
    have hmem : k⁻¹ * h * k ∈ stabilizer G α := by
      simpa using hnormal.conj_mem h hh k⁻¹
    rw [← hk, ← mul_smul, show h * k = k * (k⁻¹ * h * k) by group, mul_smul,
      mem_stabilizer_iff.mp hmem]
  have hbot : stabilizer G α = ⊥ :=
    le_antisymm (fun h hh => Subgroup.mem_bot.mpr
      (FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun γ => by rw [htriv h hh γ, one_smul])) bot_le
  exact ⟨hbot, prime_card_of_isCoatom_bot (hbot ▸ hcoatom)⟩

/-! ### Problem 8B.6 — 点安定化群が長さ 2 の軌道をもつ場合 -/

/-- 推移的な忠実作用では, 点安定化群に含まれる**正規**部分群は自明。 -/
lemma eq_bot_of_normal_le_stabilizer [FaithfulSMul G Ω] [IsPretransitive G Ω]
    {D : Subgroup G} [hD : D.Normal] {α : Ω} (hle : D ≤ stabilizer G α) : D = ⊥ := by
  refine le_antisymm (fun h hh => Subgroup.mem_bot.mpr ?_) bot_le
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun γ => ?_
  obtain ⟨k, hk⟩ := exists_smul_eq G α γ
  have hmem : k⁻¹ * h * k ∈ D := by simpa using hD.conj_mem h hh k⁻¹
  rw [one_smul, ← hk, ← mul_smul, show h * k = k * (k⁻¹ * h * k) by group, mul_smul,
    mem_stabilizer_iff.mp (hle hmem)]

/-- **Isaacs Problem 8B.6** (p. 249) 前半 🎉: 原始置換群 `G` の点安定化群 `G_α` が
`Ω ∖ {α}` 上に**長さ 2 の軌道**をもてば `|G_α| = 2`。

`D := G_α ⊓ G_β` (`β` はその軌道の点) は `G_α` の中で指数 2 なので `G_α ≤ N(D)`;
推移性から `|G_α| = |G_β|` なので `D` は `G_β` の中でも指数 2 で `G_β ≤ N(D)`。
`G_β ≰ G_α` (指数の勘定) と `G_α` の極大性から `G_α ⊔ G_β = G`, したがって
`N(D) = G` すなわち `D ⊴ G`。点安定化群に含まれる正規部分群は自明なので `D = 1`,
よって `|G_α| = 2 · |D| = 2`。 -/
theorem card_stabilizer_eq_two_of_suborbit_ncard_eq_two [Finite G] [FaithfulSMul G Ω]
    [IsPreprimitive G Ω] [Nontrivial Ω] {α β : Ω}
    (hsub : Set.ncard (orbit ↥(stabilizer G α) β) = 2) :
    Nat.card ↥(stabilizer G α) = 2 := by
  have hcoatom : IsCoatom (stabilizer G α) :=
    IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) α
  have hDα : stabilizer G β ⊓ stabilizer G α ≤ stabilizer G α := inf_le_right
  have hDβ : stabilizer G β ⊓ stabilizer G α ≤ stabilizer G β := inf_le_left
  have hDpos : 0 < Nat.card ↥(stabilizer G β ⊓ stabilizer G α) := Nat.card_pos
  -- `D` は `G_α` の中で指数 2。
  have hidxα : ((stabilizer G β ⊓ stabilizer G α).subgroupOf (stabilizer G α)).index = 2 := by
    rw [Subgroup.inf_subgroupOf_right, ← Subgroup.relIndex, ← ncard_suborbit_eq_relIndex]
    exact hsub
  have hcardD : ∀ K : Subgroup G, (h : stabilizer G β ⊓ stabilizer G α ≤ K) →
      ((stabilizer G β ⊓ stabilizer G α).subgroupOf K).index *
        Nat.card ↥(stabilizer G β ⊓ stabilizer G α) = Nat.card ↥K := by
    intro K h
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
    exact Subgroup.index_mul_card _
  have hcardα : 2 * Nat.card ↥(stabilizer G β ⊓ stabilizer G α) = Nat.card ↥(stabilizer G α) := by
    rw [← hidxα]; exact hcardD _ hDα
  have hcardeq : Nat.card ↥(stabilizer G α) = Nat.card ↥(stabilizer G β) :=
    card_stabilizer_eq α β
  -- `D` は `G_β` の中でも指数 2。
  have hidxβ : ((stabilizer G β ⊓ stabilizer G α).subgroupOf (stabilizer G β)).index = 2 := by
    refine Nat.eq_of_mul_eq_mul_right hDpos ?_
    rw [hcardD _ hDβ, ← hcardeq, ← hcardα]
  -- 両方の点安定化群が `N(D)` に含まれる。
  have hlenα : stabilizer G α ≤ Subgroup.normalizer
      ((stabilizer G β ⊓ stabilizer G α : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDα).mp
      (Subgroup.normal_of_index_eq_two hidxα)
  have hlenβ : stabilizer G β ≤ Subgroup.normalizer
      ((stabilizer G β ⊓ stabilizer G α : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDβ).mp
      (Subgroup.normal_of_index_eq_two hidxβ)
  -- `G_β ≰ G_α` (さもなくば `D = G_β` で位数の勘定が破綻)。
  have hnotle : ¬ stabilizer G β ≤ stabilizer G α := by
    intro hle
    have hDeq : stabilizer G β ⊓ stabilizer G α = stabilizer G β := inf_eq_left.mpr hle
    have hpos : 0 < Nat.card ↥(stabilizer G β) := Nat.card_pos
    rw [hDeq, hcardeq] at hcardα
    omega
  -- 極大性 ⟹ `G_α ⊔ G_β = ⊤` ⟹ `D ⊴ G`。
  haveI : (stabilizer G β ⊓ stabilizer G α).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine eq_top_iff.mpr ?_
    have hjoin : stabilizer G α ⊔ stabilizer G β = ⊤ :=
      hcoatom.2 _ (lt_of_le_of_ne le_sup_left fun hc => hnotle (hc ▸ le_sup_right))
    exact hjoin ▸ sup_le hlenα hlenβ
  have hDbot : stabilizer G β ⊓ stabilizer G α = ⊥ := eq_bot_of_normal_le_stabilizer hDα
  rw [← hcardα, hDbot]
  simp

/-! ### Problem 8B.6 後半への準備 — 正則正規部分群の存在 -/

/-- `|G_α| = 2` の原始置換群では, 相異なる 2 点の安定化群は自明にしか交わらない。 -/
lemma inf_stabilizer_eq_bot_of_card_stabilizer_eq_two [Finite G] [FaithfulSMul G Ω]
    [IsPreprimitive G Ω] [Nontrivial Ω] {α β : Ω} (hαβ : α ≠ β)
    (hcard : Nat.card ↥(stabilizer G α) = 2) :
    stabilizer G α ⊓ stabilizer G β = ⊥ := by
  have hnotle : ¬ stabilizer G α ≤ stabilizer G β := by
    intro hle
    have hbot := (stabilizer_eq_bot_and_prime_card_of_fixed_point hαβ
      fun h hh => mem_stabilizer_iff.mp (hle hh)).1
    rw [hbot] at hcard
    simp at hcard
  obtain ⟨t, htα, htβ⟩ := SetLike.not_le_iff_exists.mp hnotle
  have ht1 : t ≠ 1 := fun hc => htβ (hc ▸ Subgroup.one_mem _)
  refine le_antisymm (fun s hs => Subgroup.mem_bot.mpr ?_) bot_le
  obtain ⟨hsα, hsβ⟩ := Subgroup.mem_inf.mp hs
  by_contra hs1
  refine htβ ?_
  have huniq := (Nat.card_eq_two_iff' (1 : ↥(stabilizer G α))).mp hcard
  have hst : s = t := congrArg Subtype.val
    (huniq.unique (y₁ := ⟨s, hsα⟩) (y₂ := ⟨t, htα⟩)
      (fun hc => hs1 (congrArg Subtype.val hc)) fun hc => ht1 (congrArg Subtype.val hc))
  exact hst ▸ hsβ

/-- `|G_α| = 2` の原始置換群では **`|Ω|` は奇数**。

`G_α` の非自明元は `α` しか固定しないので `Fix(G_α) = {α}`, したがって `2`-群 `G_α` の
固定点公式 `|Ω| ≡ |Fix(G_α)| = 1 (mod 2)` から従う。 -/
lemma odd_card_of_card_stabilizer_eq_two [Finite G] [Finite Ω] [FaithfulSMul G Ω]
    [IsPreprimitive G Ω] [Nontrivial Ω] {α : Ω}
    (hcard : Nat.card ↥(stabilizer G α) = 2) : Odd (Nat.card Ω) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 ↥(stabilizer G α) := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hfix : MulAction.fixedPoints ↥(stabilizer G α) Ω = {α} := by
    ext γ
    simp only [Set.mem_singleton_iff, MulAction.mem_fixedPoints]
    constructor
    · intro hγ
      by_contra hne
      have hbot := (stabilizer_eq_bot_and_prime_card_of_fixed_point (Ne.symm hne)
        fun h hh => hγ ⟨h, hh⟩).1
      rw [hbot] at hcard
      simp at hcard
    · rintro rfl
      exact fun s => mem_stabilizer_iff.mp s.2
  have hmod := hpg.card_modEq_card_fixedPoints (α := Ω)
  rw [hfix] at hmod
  simp only [Nat.card_eq_fintype_card, Set.card_singleton] at hmod
  rcases Nat.even_or_odd (Nat.card Ω) with he | ho
  · exfalso
    obtain ⟨k, hk⟩ := he
    have : Nat.card Ω % 2 = 1 % 2 := hmod
    omega
  · exact ho

/-- **8B.6 の構造定理**: `|G_α| = 2` の原始置換群には `Ω` に**正則**に作用する正規部分群
`K` (位数 `|Ω|`) がある。

`|Ω|` が奇数 (`odd_card_of_card_stabilizer_eq_two`) なので `G_α` (位数 2) は巡回 Sylow
2-部分群で, Burnside の正規 `p`-補元定理
(`exists_normal_complement_of_isCyclic_sylow`) が位数 `|Ω|` の正規補元 `K` を与える。
`|K|` は奇数なので `K ⊓ G_α = 1` で半正則, 位数が `|Ω|` に一致するので正則。 -/
theorem exists_regular_normal_of_card_stabilizer_eq_two [Finite G] [Finite Ω]
    [FaithfulSMul G Ω] [IsPreprimitive G Ω] [Nontrivial Ω] {α : Ω}
    (hcard : Nat.card ↥(stabilizer G α) = 2) :
    ∃ K : Subgroup G, K.Normal ∧ Nat.card ↥K = Nat.card Ω ∧
      K ⊓ stabilizer G α = ⊥ ∧ Function.Bijective (smulBase K α) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card Ω) := odd_card_of_card_stabilizer_eq_two hcard
  have hΩ2 : ¬ (2 ∣ Nat.card Ω) := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hG : Nat.card Ω * 2 = Nat.card G := by
    rw [← hcard, ← index_stabilizer_of_transitive G α]
    exact Subgroup.index_mul_card _
  -- `G_α` は Sylow 2-部分群。
  have hfact : Nat.card ↥(stabilizer G α) = 2 ^ (Nat.card G).factorization 2 := by
    have hΩpos : Nat.card Ω ≠ 0 := Nat.card_pos.ne'
    have hf1 : (Nat.card G).factorization 2 = 1 := by
      rw [← hG, Nat.factorization_mul hΩpos two_ne_zero, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hΩ2, zero_add,
        Nat.Prime.factorization_self Nat.prime_two]
    rw [hcard, hf1, pow_one]
  set P : Sylow 2 G := Sylow.ofCard (stabilizer G α) hfact with hPdef
  have hPcoe : (P : Subgroup G) = stabilizer G α := Sylow.coe_ofCard _ hfact
  have hPcyc : IsCyclic ↥(P : Subgroup G) := by
    rw [hPcoe]
    exact isCyclic_of_prime_card (p := 2) hcard
  obtain ⟨K, hKnormal, hKcard, hKodd⟩ :=
    OddOrder.GroupTheory.exists_normal_complement_of_isCyclic_sylow P hPcyc
      (by rw [hPcoe, hcard, Nat.totient_two]; exact Nat.coprime_one_right _)
  rw [hPcoe, hcard] at hKcard
  haveI := hKnormal
  have hKΩ : Nat.card ↥K = Nat.card Ω := by omega
  -- `|K|` は奇数なので `K ⊓ G_α = 1`。
  have hinf : K ⊓ stabilizer G α = ⊥ := by
    refine le_antisymm (fun x hx => Subgroup.mem_bot.mpr ?_) bot_le
    obtain ⟨hxK, hxα⟩ := Subgroup.mem_inf.mp hx
    by_contra hx1
    have hdvd2 : orderOf x ∣ 2 := by
      rw [← hcard, ← Subgroup.orderOf_mk x hxα]
      exact orderOf_dvd_natCard _
    have hdvdK : orderOf x ∣ Nat.card ↥K := by
      rw [← Subgroup.orderOf_mk x hxK]
      exact orderOf_dvd_natCard _
    have h2 : orderOf x = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    exact hKodd (h2 ▸ hdvdK)
  refine ⟨K, hKnormal, hKΩ, hinf, ?_⟩
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨?_, hKΩ⟩
  exact (injective_smulBase_iff_disjoint_stabilizer K α).mpr hinf

/-- **Isaacs Problem 8B.6** (p. 249) の次数部分 🎉: `|G_α| = 2` の原始置換群の次数
`|Ω|` は**素数** (`odd_card_of_card_stabilizer_eq_two` と合わせて奇素数)。

正則正規部分群 `K` (位数 `|Ω|`) を取る。`G_α` の非自明元 `t` は `α` しか固定しないので
`K` に共役で**固定点なく**作用し, したがって `K` を反転する
(`conj_eq_inv_of_orderTwo_of_fixedPointFree`)。特に `K` は可換で, `K` の任意の部分群
`L` は `K` からも `t` からも正規化される。`K ⊔ G_α = G` (極大性) なので `L ⊴ G`,
すると `L`-軌道は block になり原始性から `L = 1` または `L = K`。よって `K` は真の非自明
部分群をもたず `|K| = |Ω|` は素数。 -/
theorem prime_card_of_card_stabilizer_eq_two [Finite G] [Finite Ω] [FaithfulSMul G Ω]
    [IsPreprimitive G Ω] [Nontrivial Ω] {α : Ω}
    (hcard : Nat.card ↥(stabilizer G α) = 2) : (Nat.card Ω).Prime := by
  classical
  obtain ⟨K, hKnormal, hKΩ, hKinf, -⟩ :=
    exists_regular_normal_of_card_stabilizer_eq_two hcard
  haveI := hKnormal
  have hΩ2 : 2 ≤ Nat.card Ω := by
    have h0 : Nat.card Ω ≠ 0 := Nat.card_pos.ne'
    have h1 : Nat.card Ω ≠ 1 := fun hc =>
      absurd (Nat.card_eq_one_iff_unique.mp hc).1 (not_subsingleton Ω)
    omega
  -- `G_α = {1, t}` と `t² = 1`。
  obtain ⟨⟨t, htα⟩, ht1, htuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(stabilizer G α))).mp hcard
  have ht1' : t ≠ 1 := fun hc => ht1 (Subtype.ext hc)
  have htt : t * t = 1 := by
    have hinvmem : (⟨t, htα⟩ : ↥(stabilizer G α))⁻¹ = ⟨t, htα⟩ := by
      refine htuniq _ fun hc => ht1' ?_
      have hv : t⁻¹ = 1 := congrArg Subtype.val hc
      simpa using hv
    have hinv : t⁻¹ = t := congrArg Subtype.val hinvmem
    nth_rewrite 1 [← hinv]
    rw [inv_mul_cancel]
  have htα' : t • α = α := mem_stabilizer_iff.mp htα
  -- `t` は `α` しか固定しない。
  have htfix : ∀ γ : Ω, t • γ = γ → γ = α := by
    intro γ hγ
    by_contra hne
    have hbot := inf_stabilizer_eq_bot_of_card_stabilizer_eq_two (Ne.symm hne) hcard
    exact ht1' (Subgroup.mem_bot.mp
      (hbot ▸ Subgroup.mem_inf.mpr ⟨htα, mem_stabilizer_iff.mpr hγ⟩))
  -- `t` は `K` に固定点なく作用する。
  have hfpf : ∀ k ∈ K, t * k * t⁻¹ = k → k = 1 := by
    intro k hk hconj
    have hcm : t * k = k * t := by
      conv_rhs => rw [← hconj]
      group
    have hfix : t • (k • α) = k • α := by
      rw [← mul_smul, hcm, mul_smul, htα']
    have hkα : k • α = α := htfix _ hfix
    exact Subgroup.mem_bot.mp
      (hKinf ▸ Subgroup.mem_inf.mpr ⟨hk, mem_stabilizer_iff.mpr hkα⟩)
  -- `t` は `K` を反転し, `K` は可換。
  have htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K := fun k hk => hKnormal.conj_mem k hk t
  have hinvK : ∀ k ∈ K, t * k * t⁻¹ = k⁻¹ := fun k hk =>
    OddOrder.GroupTheory.conj_eq_inv_of_orderTwo_of_fixedPointFree htt htK hfpf hk
  have hcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    intro x hx y hy
    have h1 : t * (x * y) * t⁻¹ = (x * y)⁻¹ := hinvK _ (K.mul_mem hx hy)
    have h2 : t * (x * y) * t⁻¹ = x⁻¹ * y⁻¹ := by
      rw [show t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) from by group,
        hinvK x hx, hinvK y hy]
    rw [h1, mul_inv_rev] at h2
    have h3 : (y⁻¹ * x⁻¹)⁻¹ = (x⁻¹ * y⁻¹)⁻¹ := congrArg (fun z : G => z⁻¹) h2
    simp only [mul_inv_rev, inv_inv] at h3
    exact h3
  -- `K ⊔ G_α = ⊤`。
  have hcoatom : IsCoatom (stabilizer G α) :=
    IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) α
  have hsup : K ⊔ stabilizer G α = ⊤ := by
    refine hcoatom.2 _ (lt_of_le_of_ne le_sup_right fun hc => ?_)
    have hKle : K ≤ stabilizer G α := hc ▸ le_sup_left
    have hKbot : K = ⊥ := le_bot_iff.mp (hKinf ▸ le_inf le_rfl hKle)
    rw [hKbot] at hKΩ
    simp only [Subgroup.card_bot] at hKΩ
    omega
  -- `K` の部分群は `⊥` か `K` のみ。
  have hsubgroup : ∀ L : Subgroup G, L ≤ K → L = ⊥ ∨ L = K := by
    intro L hLK
    haveI : L.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      refine eq_top_iff.mpr (hsup ▸ sup_le (fun x hx => ?_) fun s hs => ?_)
      · rw [Subgroup.mem_normalizer_iff]
        intro h
        constructor
        · intro hh
          rwa [show x * h * x⁻¹ = h from by rw [hcomm x hx h (hLK hh)]; group]
        · intro hh
          have hhK : h ∈ K := by
            rw [show h = x⁻¹ * (x * h * x⁻¹) * x from by group]
            exact K.mul_mem (K.mul_mem (K.inv_mem hx) (hLK hh)) hx
          rwa [show x * h * x⁻¹ = h from by rw [hcomm x hx h hhK]; group] at hh
      · have htnorm : t ∈ Subgroup.normalizer (L : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro h
          constructor
          · intro hh
            rw [hinvK h (hLK hh)]
            exact L.inv_mem hh
          · intro hh
            have hhK : h ∈ K := by
              have hx : t * h * t⁻¹ ∈ K := hLK hh
              have hc := hKnormal.conj_mem _ hx t⁻¹
              rwa [show t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h from by group] at hc
            rw [hinvK h hhK] at hh
            exact (L.inv_mem_iff).mp hh
        rcases eq_or_ne s 1 with rfl | hs1
        · exact Subgroup.one_mem _
        · have hst : s = t := congrArg Subtype.val
            (htuniq ⟨s, hs⟩ fun hc => hs1 (congrArg Subtype.val hc))
          exact hst ▸ htnorm
    rcases IsPreprimitive.isTrivialBlock_of_isBlock (IsBlock.orbit_of_normal (N := L) α) with
      hsubs | huniv
    · left
      refine le_bot_iff.mp (hKinf ▸ le_inf hLK fun x hx => mem_stabilizer_iff.mpr ?_)
      exact hsubs (mem_orbit α (⟨x, hx⟩ : ↥L)) (mem_orbit_self α)
    · right
      have hLinf : L ⊓ stabilizer G α = ⊥ :=
        le_bot_iff.mp (hKinf ▸ inf_le_inf_right _ hLK)
      have hLinj : Function.Injective (smulBase L α) :=
        (injective_smulBase_iff_disjoint_stabilizer L α).mpr hLinf
      have hLsurj : Function.Surjective (smulBase L α) := by
        intro γ
        have : γ ∈ orbit ↥L α := huniv ▸ Set.mem_univ γ
        obtain ⟨l, hl⟩ := this
        exact ⟨l, hl⟩
      have hLcard : Nat.card ↥L = Nat.card Ω :=
        Nat.card_eq_of_bijective _ ⟨hLinj, hLsurj⟩
      refine SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hLK ?_ (Set.toFinite _))
      have h1 : ((K : Set G)).ncard = Nat.card Ω := by
        rw [← Nat.card_coe_set_eq]; exact hKΩ
      have h2 : ((L : Set G)).ncard = Nat.card Ω := by
        rw [← Nat.card_coe_set_eq]; exact hLcard
      omega
  -- 素因数を取り Cauchy。
  have hKne1 : Nat.card ↥K ≠ 1 := by rw [hKΩ]; omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hKne1
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite ↥K
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := ↥K) p
    (by rwa [← Nat.card_eq_fintype_card])
  have hyord : orderOf (y : G) = p := by rw [← hy, Subgroup.orderOf_coe]
  have hy1 : (y : G) ≠ 1 := by
    intro hc
    rw [hc, orderOf_one] at hyord
    exact hp.ne_one hyord.symm
  have hzple : Subgroup.zpowers (y : G) ≤ K := (Subgroup.zpowers_le).mpr y.2
  rcases hsubgroup _ hzple with h | h
  · exact absurd (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers (y : G))) hy1
  · rw [← hKΩ, ← h, Nat.card_zpowers, hyord]
    exact hp

/-! ### Problem 8B.7 — 点安定化群が長さ 3 の軌道をもつ場合 -/

/-- 部分群 `D` の**奇位数元が生成する部分群**。有限群では Isaacs の `O²(D)`
(2-剰余部分群 = `D / N` が 2-群となる最小の正規部分群 `N`) と一致する。 -/
def oddCore (D : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ D ∧ Odd (orderOf x)}

lemma oddCore_le (D : Subgroup G) : oddCore D ≤ D :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

lemma mem_oddCore {D : Subgroup G} {x : G} (hx : x ∈ D) (hodd : Odd (orderOf x)) :
    x ∈ oddCore D :=
  Subgroup.subset_closure ⟨hx, hodd⟩

/-- `D` の奇位数元がすべて自明なら `D` は 2-群。

`g` の位数を `2^a · m` (`m` 奇) と分解すると `g^(2^a)` は奇位数なので
`oddCore D = ⊥` から `1`, したがって `g` の位数は `2` 冪。 -/
lemma isPGroup_two_of_oddCore_eq_bot [Finite G] {D : Subgroup G} (h : oddCore D = ⊥) :
    IsPGroup 2 ↥D := by
  intro g
  have hgne : orderOf (g : G) ≠ 0 := (orderOf_pos (g : G)).ne'
  refine ⟨(orderOf (g : G)).factorization 2, ?_⟩
  have hdvd : 2 ^ (orderOf (g : G)).factorization 2 ∣ orderOf (g : G) :=
    Nat.ordProj_dvd _ 2
  have hord : orderOf ((g : G) ^ (2 ^ (orderOf (g : G)).factorization 2))
      = orderOf (g : G) / 2 ^ (orderOf (g : G)).factorization 2 := by
    rw [orderOf_pow, Nat.gcd_eq_right hdvd]
  have hodd : Odd (orderOf ((g : G) ^ (2 ^ (orderOf (g : G)).factorization 2))) := by
    rw [hord]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hgne))
  have hmem : ((g : G) ^ (2 ^ (orderOf (g : G)).factorization 2)) ∈ oddCore D :=
    mem_oddCore (D.pow_mem g.2 _) hodd
  rw [h, Subgroup.mem_bot] at hmem
  exact Subtype.ext (by push_cast; exact hmem)

/-- 奇位数の元が `γ` を `x²` で固定するなら `x` 自身でも固定する
(`x` は `⟨x²⟩` に属するから)。 -/
lemma smul_eq_self_of_odd_of_sq_smul_eq {x : G} (hodd : Odd (orderOf x)) {γ : Ω}
    (h2 : (x * x) • γ = γ) : x • γ = γ := by
  obtain ⟨m, hm⟩ := hodd
  have hpow : ∀ k : ℕ, ((x * x) ^ k) • γ = γ := by
    intro k
    induction k with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, h2, ih]
  have hx : (x * x) ^ (m + 1) = x := by
    rw [← sq, ← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  calc x • γ = ((x * x) ^ (m + 1)) • γ := by rw [hx]
    _ = γ := hpow _

/-- **8B.7 の鍵**: 奇位数の元 `x` が高々 2 点の集合 `S` を保つなら `S` を各点固定する。

`x • γ ≠ γ` なら `S = {γ, x • γ}` (2 点) で `x² • γ ∈ S` は `γ` でしかありえず,
奇位数から `x • γ = γ` (`smul_eq_self_of_odd_of_sq_smul_eq`) となって矛盾。 -/
lemma smul_eq_self_of_odd_of_ncard_le_two [Finite Ω] {x : G} (hodd : Odd (orderOf x))
    {S : Set Ω}
    (hS : ∀ δ ∈ S, x • δ ∈ S) (hcard : S.ncard ≤ 2) {γ : Ω} (hγ : γ ∈ S) :
    x • γ = γ := by
  classical
  by_contra hne
  have hxγ : x • γ ∈ S := hS γ hγ
  have hsq : (x * x) • γ ∈ S := by rw [mul_smul]; exact hS _ hxγ
  -- `{γ, x • γ} ⊆ S` は 2 点なので `S = {γ, x • γ}`。
  have hsub : ({γ, x • γ} : Set Ω) ⊆ S := by
    intro z hz
    rcases hz with rfl | hz
    · exact hγ
    · rw [Set.mem_singleton_iff] at hz; exact hz ▸ hxγ
  have hpair : ({γ, x • γ} : Set Ω).ncard = 2 := by
    rw [Set.ncard_pair (Ne.symm hne)]
  have hSeq : S = {γ, x • γ} :=
    (Set.eq_of_subset_of_ncard_le hsub (by rw [hpair]; exact hcard) (Set.toFinite _)).symm
  -- `x² • γ` は `γ` か `x • γ`; 後者なら `x • γ = γ`。
  rw [hSeq] at hsq
  rcases hsq with h | h
  · exact hne (smul_eq_self_of_odd_of_sq_smul_eq hodd h)
  · rw [Set.mem_singleton_iff, mul_smul] at h
    exact hne (MulAction.injective x h)

end

end OddOrder.Isaacs.Ch08
