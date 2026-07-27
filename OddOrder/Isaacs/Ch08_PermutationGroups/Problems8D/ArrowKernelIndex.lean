/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Primitive
import OddOrder.Isaacs.Ch01_Sylow.Problems
import OddOrder.Isaacs.Ch08_PermutationGroups.CommonDivisorGraph

/-!
# Isaacs Problem 8D.4 (p. 269) — `k_m` と `m` の比較

`m` を推移作用の subdegree, `k_m = |K_m(α) : G_α|` (Thm 8.42 直前の定義,
本リポジトリでは `(stabilizer G α).relIndex (arrowKernel G m α)`) とする。

* **(a)** `k_m ≥ m`。
* **(b)** `k_m = m` で `α → β` が `m`-arrow なら `G_α G_β` は部分群 (実際に `K_m(α)`)。
* **(c)** `m > 1` で `G` が原始的なら `k_m > m`。

## 証明の流れ

`A := G_α`, `B := G_β`, `K := K_m(α)` とおくと `A, B ≤ K` なので集合積 `A·B ⊆ K`。
`|A·B| · |A ∩ B| = |A| · |B|` (**Problem 1A.3** `card_mul_card_inf`) と
`|B| = |A ∩ B| · m`, `|K| = |A| · k_m` を合わせると `m ≤ k_m` (a)。等号なら
`|A·B| = |K|` で有限性から `A·B = K` (b)。原始性のもとで `k_m = m` を仮定すると
`A ≤ K` と `A` の極大性から `K = A` (⟹ `A = B` ⟹ `m = 1`) か `K = ⊤`
(⟹ `m = k_m = |Ω|` だが `m`-suborbit は `Ω ∖ {α}` に入る) で, どちらも矛盾 (c)。

## Main results

- `le_relIndex_arrowKernel` — **8D.4 (a)**。
- `mul_stabilizer_eq_arrowKernel` — **8D.4 (b)**。
- `lt_relIndex_arrowKernel` — **8D.4 (c)**。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problem 8D.4 -/

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [IsPretransitive G Ω]

omit [Finite G] [IsPretransitive G Ω] in
/-- `A ≤ K` のとき `|A| · |A : K の相対指数| = |K|`。 -/
private lemma card_mul_relIndex {A K : Subgroup G} (h : A ≤ K) :
    Nat.card ↥A * A.relIndex K = Nat.card ↥K := by
  have hcard := Subgroup.card_mul_index (A.subgroupOf K)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv, ← Subgroup.relIndex] at hcard

omit [Finite G] [IsPretransitive G Ω] in
variable (G) in
/-- `m`-arrow の両端の安定化群は `K_m(α)` に含まれる。 -/
private lemma stabilizer_le_arrowKernel_of_isArrow {m : ℕ} {α β : Ω}
    (h : IsArrow G m α β) :
    stabilizer G β ≤ arrowKernel G m α :=
  stabilizer_le_arrowKernel (mem_arrowComponent_of_isArrow (mem_arrowComponent_self m α) h)

/-- `m`-arrow `α → β` に対する基本等式: `|A| · |B| = |A·B| · |A ∩ B|` と
`|B| = |A ∩ B| · m`, `|K| = |A| · k_m`。 -/
private lemma arrow_card_relations {m : ℕ} {α β : Ω} (h : IsArrow G m α β) :
    Nat.card ↥(stabilizer G β) = Nat.card ↥(stabilizer G α ⊓ stabilizer G β) * m ∧
      Nat.card ↥(arrowKernel G m α) =
        Nat.card ↥(stabilizer G α) * (stabilizer G α).relIndex (arrowKernel G m α) := by
  constructor
  · have hsym : (stabilizer G α).relIndex (stabilizer G β) = m := by
      have h2 : Set.ncard (orbit ↥(stabilizer G β) α) = m := IsArrow.symm (G := G) h
      rwa [ncard_suborbit_eq_relIndex] at h2
    have hcard := card_mul_relIndex (A := stabilizer G α ⊓ stabilizer G β)
      (K := stabilizer G β) inf_le_right
    rw [Subgroup.inf_relIndex_right, hsym] at hcard
    exact hcard.symm
  · exact (card_mul_relIndex (stabilizer_le_arrowKernel_self m α)).symm

/-- **Isaacs Problem 8D.4 (a)** (p. 269)。`m` が subdegree なら `m ≤ k_m`。 -/
theorem le_relIndex_arrowKernel {m : ℕ} {α β : Ω} (h : IsArrow G m α β) :
    m ≤ (stabilizer G α).relIndex (arrowKernel G m α) := by
  classical
  obtain ⟨hB, hK⟩ := arrow_card_relations h
  -- `A·B ⊆ K`
  have hsub : ((stabilizer G α : Set G) * (stabilizer G β : Set G)) ⊆
      (arrowKernel G m α : Set G) := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact (arrowKernel G m α).mul_mem (stabilizer_le_arrowKernel_self m α ha)
      (stabilizer_le_arrowKernel_of_isArrow G h hb)
  have hle : Nat.card ((stabilizer G α : Set G) * (stabilizer G β : Set G)) ≤
      Nat.card ↥(arrowKernel G m α) := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hprod := Ch01.card_mul_card_inf (stabilizer G α) (stabilizer G β)
  have key : (Nat.card ↥(stabilizer G α) * Nat.card ↥(stabilizer G α ⊓ stabilizer G β)) * m ≤
      (Nat.card ↥(stabilizer G α) * Nat.card ↥(stabilizer G α ⊓ stabilizer G β)) *
        (stabilizer G α).relIndex (arrowKernel G m α) :=
    calc (Nat.card ↥(stabilizer G α) * Nat.card ↥(stabilizer G α ⊓ stabilizer G β)) * m
        = Nat.card ↥(stabilizer G α) *
            (Nat.card ↥(stabilizer G α ⊓ stabilizer G β) * m) := by ring
      _ = Nat.card ↥(stabilizer G α) * Nat.card ↥(stabilizer G β) := by rw [← hB]
      _ = Nat.card ((stabilizer G α : Set G) * (stabilizer G β : Set G)) *
            Nat.card ↥(stabilizer G α ⊓ stabilizer G β) := hprod.symm
      _ ≤ Nat.card ↥(arrowKernel G m α) *
            Nat.card ↥(stabilizer G α ⊓ stabilizer G β) := Nat.mul_le_mul_right _ hle
      _ = (Nat.card ↥(stabilizer G α) *
            (stabilizer G α).relIndex (arrowKernel G m α)) *
            Nat.card ↥(stabilizer G α ⊓ stabilizer G β) := by rw [hK]
      _ = (Nat.card ↥(stabilizer G α) * Nat.card ↥(stabilizer G α ⊓ stabilizer G β)) *
            (stabilizer G α).relIndex (arrowKernel G m α) := by ring
  exact Nat.le_of_mul_le_mul_left key (Nat.mul_pos Nat.card_pos Nat.card_pos)

/-- **Isaacs Problem 8D.4 (b)** (p. 269)。`k_m = m` で `α → β` が `m`-arrow なら,
集合積 `G_α G_β` は部分群 `K_m(α)` に一致する。 -/
theorem mul_stabilizer_eq_arrowKernel {m : ℕ} {α β : Ω} (h : IsArrow G m α β)
    (hk : (stabilizer G α).relIndex (arrowKernel G m α) = m) :
    ((stabilizer G α : Set G) * (stabilizer G β : Set G)) = (arrowKernel G m α : Set G) := by
  classical
  obtain ⟨hB, hK⟩ := arrow_card_relations h
  have hsub : ((stabilizer G α : Set G) * (stabilizer G β : Set G)) ⊆
      (arrowKernel G m α : Set G) := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact (arrowKernel G m α).mul_mem (stabilizer_le_arrowKernel_self m α ha)
      (stabilizer_le_arrowKernel_of_isArrow G h hb)
  have hprod := Ch01.card_mul_card_inf (stabilizer G α) (stabilizer G β)
  have hIpos : 0 < Nat.card ↥(stabilizer G α ⊓ stabilizer G β) := Nat.card_pos
  -- `|A·B| = |K|`
  have hcards : Nat.card ((stabilizer G α : Set G) * (stabilizer G β : Set G)) =
      Nat.card ↥(arrowKernel G m α) := by
    rw [hK, hk]
    refine Nat.eq_of_mul_eq_mul_right hIpos ?_
    rw [hprod, hB]
    ring
  exact Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcards.symm) (Set.toFinite _)

end -- 8D.4 (a)(b)

section /- Problem 8D.4 (c) -/

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]

/-- **Isaacs Problem 8D.4 (c)** (p. 269)。`m > 1` で `G` が原始的なら `k_m > m`。

`k_m = m` とすると `A ≤ K_m(α)` と `A` の極大性から `K_m(α) = A` か `⊤`。前者なら
`B ≤ A` で位数比較から `A = B`, つまり `m = 1`。後者なら `k_m = |G : A| = |Ω|` だが
`m`-suborbit は `Ω ∖ {α}` に含まれるので `m < |Ω|`。 -/
theorem lt_relIndex_arrowKernel [Nontrivial Ω] [FaithfulSMul G Ω] [IsPreprimitive G Ω]
    {m : ℕ} {α β : Ω} (h : IsArrow G m α β) (hm : 1 < m) :
    m < (stabilizer G α).relIndex (arrowKernel G m α) := by
  classical
  refine lt_of_le_of_ne (le_relIndex_arrowKernel h) fun hk => ?_
  have hcoat : IsCoatom (stabilizer G α) :=
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) α
  have hAK : stabilizer G α ≤ arrowKernel G m α := stabilizer_le_arrowKernel_self m α
  rcases eq_or_lt_of_le hAK with heq | hlt
  · -- `K_m(α) = G_α` ⟹ `G_β ≤ G_α` ⟹ `G_α = G_β` ⟹ `m = 1`
    have hBA : stabilizer G β ≤ stabilizer G α := by
      rw [heq]
      exact stabilizer_le_arrowKernel_of_isArrow G h
    have hAB : stabilizer G β = stabilizer G α :=
      Subgroup.eq_of_le_of_card_ge hBA (le_of_eq (card_stabilizer_eq α β))
    have hone : Set.ncard (orbit ↥(stabilizer G α) β) = 1 := by
      rw [ncard_suborbit_eq_relIndex, hAB, Subgroup.relIndex_self]
    rw [isArrow_iff, hone] at h
    omega
  · -- `K_m(α) = ⊤` ⟹ `m = k_m = |Ω|`, しかし `m`-suborbit は `Ω ∖ {α}` に入る
    have htop : arrowKernel G m α = ⊤ := hcoat.2 _ hlt
    have hidx : (stabilizer G α).relIndex (arrowKernel G m α) = Nat.card Ω := by
      rw [htop, Subgroup.relIndex_top_right, index_stabilizer_of_transitive]
    rw [hidx] at hk
    -- suborbit は `{α}ᶜ` に含まれるので長さ `< |Ω|`
    have hβα : β ≠ α := by
      intro hc
      rw [isArrow_iff, hc, orbit_stabilizer_self, Set.ncard_singleton] at h
      omega
    have hsub : orbit ↥(stabilizer G α) β ⊆ ({α}ᶜ : Set Ω) := by
      rintro ε ⟨g, rfl⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hc
      refine hβα ?_
      have hc' : (g : G) • β = α := hc
      have hinv : ((g : G))⁻¹ • α = α :=
        mem_stabilizer_iff.mp ((stabilizer G α).inv_mem g.2)
      calc β = ((g : G))⁻¹ • ((g : G) • β) := (inv_smul_smul _ _).symm
        _ = ((g : G))⁻¹ • α := by rw [hc']
        _ = α := hinv
    haveI : Finite Ω := by
      have : Nat.card Ω ≠ 0 := by omega
      exact Nat.finite_of_card_ne_zero this
    have hcompl : ({α}ᶜ : Set Ω).ncard = Nat.card Ω - 1 := by
      have h2 := Set.ncard_add_ncard_compl ({α} : Set Ω)
      rw [Set.ncard_singleton] at h2
      omega
    have hle : Set.ncard (orbit ↥(stabilizer G α) β) ≤ Nat.card Ω - 1 :=
      hcompl ▸ Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [isArrow_iff] at h
    omega

end -- Problem 8D.4 (c)

end OddOrder.Isaacs.Ch08
