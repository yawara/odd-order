/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Primitive
import OddOrder.Isaacs.Ch08_PermutationGroups.CommonDivisorGraph

/-!
# Isaacs Problem 8D.1 (p. 269) — subdegree 2 をもつ原始群

`1 = m₁ ≤ m₂ ≤ ⋯ ≤ m_r` を rank `r` の**原始的**作用の subdegree とする。`m₂ = 2`
なら `i ≥ 2` の全てで `mᵢ = 2` — つまり `α` 以外の suborbit はすべて長さ 2。

## 証明の流れ

`α → β` が 2-arrow なら `D := G_β ∩ G_α` は `G_α` でも `G_β` でも指数 2, したがって
両方で正規なので `G_α ⊔ G_β ≤ N_G(D)`。原始性から `G_α` は極大 (`IsCoatom`) なので
`G_α ⊔ G_β` は `G_α` か `⊤`。前者だと位数比較で `G_β = G_α`, つまり `D = G_α` となり
指数 2 に反する。よって `D ◁ G` で, 点安定化群に含まれる正規部分群は忠実性から自明。
ゆえに **`|G_α| = 2`**。すると suborbit の長さは `1` か `2` しかなく, 長さ 1 の
suborbit `{γ}` (`γ ≠ α`) があれば `G_γ = G_α`, しかし「点安定化群が一致する点の集合」は
block なので原始性から `Ω` 全体となり `G_α ◁ G`, 再び `G_α = 1` で矛盾。

## Main results

- `isBlock_stabilizer_eq` — `{δ | G_δ = G_α}` は block。
- `eq_bot_of_normal_of_le_stabilizer` — 点安定化群に含まれる正規部分群は自明。
- `card_stabilizer_eq_two_of_subdegree_eq_two` — subdegree 2 があれば `|G_α| = 2`。
- `ncard_orbit_eq_two_of_subdegree_eq_two` — **Problem 8D.1** 本体。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problem 8D.1 -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- 共役と安定化群: `x ∈ G_{g•δ} ↔ g⁻¹ x g ∈ G_δ`。 -/
theorem mem_stabilizer_smul_iff (g : G) (δ : Ω) (x : G) :
    x ∈ stabilizer G (g • δ) ↔ g⁻¹ * x * g ∈ stabilizer G δ := by
  simp only [mem_stabilizer_iff]
  constructor
  · intro h
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · intro h
    have h2 := congrArg (fun y => g • y) h
    simpa [mul_smul, smul_inv_smul] using h2

/-- 点安定化群が一致する点の集合の, 平行移動による特徴づけ。 -/
private lemma stabilizer_smul_eq_iff (g : G) (ε : Ω) (x : G) :
    x ∈ stabilizer G ε ↔ g⁻¹ * x * g ∈ stabilizer G (g⁻¹ • ε) := by
  have h := mem_stabilizer_smul_iff g (g⁻¹ • ε) x
  rwa [smul_inv_smul] at h

/-- **点安定化群が一致する点の集合は block**。

`g • {δ | G_δ = G_α}` は `{ε | G_ε = G_{g•α}}` なので, 交われば一致する。 -/
theorem isBlock_stabilizer_eq (α : Ω) :
    IsBlock G {δ : Ω | stabilizer G δ = stabilizer G α} := by
  rw [isBlock_iff_smul_eq_of_mem]
  intro g a ha hga
  simp only [Set.mem_ofPred_eq] at ha hga
  have hstab : ∀ x : G, x ∈ stabilizer G α ↔ g⁻¹ * x * g ∈ stabilizer G α := by
    intro x
    calc x ∈ stabilizer G α ↔ x ∈ stabilizer G (g • a) := by rw [hga]
      _ ↔ g⁻¹ * x * g ∈ stabilizer G a := mem_stabilizer_smul_iff g a x
      _ ↔ g⁻¹ * x * g ∈ stabilizer G α := by rw [ha]
  ext ε
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    ext x
    rw [stabilizer_smul_eq_iff g ε x, h, ← hstab]
  · intro h
    ext y
    have hy : y ∈ stabilizer G (g⁻¹ • ε) ↔ g * y * g⁻¹ ∈ stabilizer G ε := by
      have h := stabilizer_smul_eq_iff g ε (g * y * g⁻¹)
      rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h
      exact h.symm
    rw [hy, h, hstab (g * y * g⁻¹), show g⁻¹ * (g * y * g⁻¹) * g = y by group]

/-- 忠実・推移的な作用では, 点安定化群に含まれる正規部分群は自明。 -/
theorem eq_bot_of_normal_of_le_stabilizer [FaithfulSMul G Ω] [IsPretransitive G Ω]
    {N : Subgroup G} [hN : N.Normal] {α : Ω} (h : N ≤ stabilizer G α) : N = ⊥ := by
  refine le_antisymm (fun x hx => Subgroup.mem_bot.mpr ?_) bot_le
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun γ => ?_
  obtain ⟨g, rfl⟩ := exists_smul_eq G α γ
  rw [one_smul]
  have hmem : g⁻¹ * x * g ∈ N := by
    have := hN.conj_mem x hx g⁻¹
    simpa using this
  exact (mem_stabilizer_smul_iff g α x).mpr (h hmem)

variable [Finite G] [FaithfulSMul G Ω]

/-- **Isaacs Problem 8D.1** の鍵。原始的作用で長さ 2 の suborbit があれば
点安定化群の位数は **2**。 -/
theorem card_stabilizer_eq_two_of_subdegree_eq_two [Nontrivial Ω] [IsPreprimitive G Ω]
    {α β : Ω} (hβ : Set.ncard (orbit ↥(stabilizer G α) β) = 2) :
    Nat.card ↥(stabilizer G α) = 2 := by
  classical
  set D : Subgroup G := stabilizer G β ⊓ stabilizer G α with hD
  have hDα : D ≤ stabilizer G α := inf_le_right
  have hDβ : D ≤ stabilizer G β := inf_le_left
  -- `|G_α : D| = 2` と, 対称性から `|G_β : D| = 2`
  have hidxα : (D.subgroupOf (stabilizer G α)).index = 2 := by
    rw [← Subgroup.relIndex, hD, Subgroup.inf_relIndex_right, ← ncard_suborbit_eq_relIndex]
    exact hβ
  have hidxβ : (D.subgroupOf (stabilizer G β)).index = 2 := by
    have hsym : Set.ncard (orbit ↥(stabilizer G β) α) = 2 := IsArrow.symm (G := G) hβ
    rw [← Subgroup.relIndex, hD, inf_comm, Subgroup.inf_relIndex_right,
      ← ncard_suborbit_eq_relIndex]
    exact hsym
  -- 指数 2 なので `D` は両方で正規, よって `G_α ⊔ G_β ≤ N_G(D)`
  have hnormα : stabilizer G α ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDα).mp
      (Subgroup.normal_of_index_eq_two hidxα)
  have hnormβ : stabilizer G β ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDβ).mp
      (Subgroup.normal_of_index_eq_two hidxβ)
  -- 原始性: `G_α` は極大
  have hcoat : IsCoatom (stabilizer G α) :=
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) α
  have hsup : stabilizer G α ⊔ stabilizer G β = ⊤ := by
    rcases eq_or_lt_of_le
      (le_sup_left : stabilizer G α ≤ stabilizer G α ⊔ stabilizer G β) with heq | hlt
    · -- `G_β ≤ G_α` なら位数比較で `G_β = G_α`, すると `D = G_α` で指数 1
      exfalso
      have hle : stabilizer G β ≤ stabilizer G α := by
        rw [heq]
        exact le_sup_right
      have heqβ : stabilizer G β = stabilizer G α :=
        Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_stabilizer_eq α β))
      rw [hD, heqβ, inf_idem, Subgroup.subgroupOf_self, Subgroup.index_top] at hidxα
      exact absurd hidxα (by norm_num)
    · exact hcoat.2 _ hlt
  -- したがって `D ◁ G`, 忠実性から `D = ⊥`
  have : D.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le hnormα hnormβ
  have hbot : D = ⊥ := eq_bot_of_normal_of_le_stabilizer hDα
  have hsub : D.subgroupOf (stabilizer G α) = ⊥ := by rw [hbot, Subgroup.bot_subgroupOf]
  have hmul := Subgroup.card_mul_index (D.subgroupOf (stabilizer G α))
  rw [hidxα, hsub] at hmul
  simpa using hmul.symm

/-- 原始的な忠実作用で `γ ≠ α` の suborbit が長さ 1 なら, `G_α = ⊥` (作用は regular)。

長さ 1 は `G_α ≤ G_γ`, 位数比較で `G_α = G_γ` を与える。block `{δ | G_δ = G_α}` は
`α` と `γ` を含むので原始性から `Ω` 全体, つまり全点安定化群が一致して `G_α ◁ G`。 -/
theorem stabilizer_eq_bot_of_ncard_orbit_eq_one [Nontrivial Ω] [IsPreprimitive G Ω]
    {α γ : Ω} (hγ : γ ≠ α) (h1 : Set.ncard (orbit ↥(stabilizer G α) γ) = 1) :
    stabilizer G α = ⊥ := by
  have hle : stabilizer G α ≤ stabilizer G γ := by
    have htop : (stabilizer G γ).subgroupOf (stabilizer G α) = ⊤ := by
      rw [← Subgroup.index_eq_one, ← Subgroup.relIndex, ← ncard_suborbit_eq_relIndex]
      exact h1
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥(stabilizer G α)) ∈
        (stabilizer G γ).subgroupOf (stabilizer G α) := by rw [htop]; trivial
    exact hmem
  have heq : stabilizer G α = stabilizer G γ :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_stabilizer_eq γ α))
  rcases IsPreprimitive.isTrivialBlock_of_isBlock (isBlock_stabilizer_eq (G := G) α) with
    hsub | huniv
  · exact absurd (hsub (Set.mem_ofPred_eq ▸ heq.symm) rfl) hγ
  · have hall : ∀ δ : Ω, stabilizer G δ = stabilizer G α := by
      intro δ
      have hmem : δ ∈ {δ : Ω | stabilizer G δ = stabilizer G α} := huniv ▸ Set.mem_univ δ
      exact hmem
    have : (stabilizer G α).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have h2 : g * x * g⁻¹ ∈ stabilizer G (g • α) := by
        rw [mem_stabilizer_smul_iff]
        simpa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] using hx
      rwa [hall (g • α)] at h2
    exact eq_bot_of_normal_of_le_stabilizer (N := stabilizer G α) (α := α) le_rfl

/-- **Isaacs Problem 8D.1** (p. 269)。原始的作用で長さ 2 の suborbit が現れるなら,
`α` 以外の点の suborbit はすべて長さ 2。 -/
theorem ncard_orbit_eq_two_of_subdegree_eq_two [Nontrivial Ω] [IsPreprimitive G Ω]
    {α β : Ω} (hβ : Set.ncard (orbit ↥(stabilizer G α) β) = 2)
    {γ : Ω} (hγ : γ ≠ α) :
    Set.ncard (orbit ↥(stabilizer G α) γ) = 2 := by
  have hcard : Nat.card ↥(stabilizer G α) = 2 :=
    card_stabilizer_eq_two_of_subdegree_eq_two hβ
  -- suborbit の長さは `|G_α| = 2` を割る
  have hdvd : Set.ncard (orbit ↥(stabilizer G α) γ) ∣ 2 := by
    rw [ncard_suborbit_eq_relIndex, Subgroup.relIndex, ← hcard]
    exact Subgroup.index_dvd_card _
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · -- 長さ 1 なら `G_α = ⊥` だが位数は 2
    exfalso
    rw [stabilizer_eq_bot_of_ncard_orbit_eq_one hγ h1] at hcard
    simp at hcard
  · exact h2

end -- Problem 8D.1

end OddOrder.Isaacs.Ch08
