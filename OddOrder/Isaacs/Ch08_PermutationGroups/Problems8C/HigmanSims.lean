/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8B.Blocks
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.MathieuEleven
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.SimpleStabilizer

/-!
# Isaacs Problem 8C.4 (p. 257) — 次数 100, 点安定化群が単純で軌道長 22, 77

`G` が 100 点集合 `Ω` に推移的に作用し, 点安定化群 `G_α` が単純で `Ω ∖ {α}` 上に
長さ 22 と 77 の軌道をもつなら, `G` は**原始的**であり, さらに**単純**。

**Note** (Isaacs)。Higman–Sims 群 `HS` がこの条件を満たし, そのとき点安定化群は
Mathieu 群 `M₂₂` に同型。

## 証明の流れ

* **原始性**: `α` を含む block `Δ` は `G_α`-不変なので `Δ ∖ {α}` は軌道の合併,
  つまり `∅ / 22-軌道 / 77-軌道 / 両方` のいずれか。よって `|Δ| ∈ {1, 23, 78, 100}`。
  他方 `|Δ|` は `|Ω| = 100` を割る (`IsBlock.ncard_dvd_card`) ので `1` か `100`。
* **単純性**: `1 ≠ N ◁ G` は原始性から推移的 (**Problem 8B.3**), `G_α` が単純なので
  `N` は regular で `|N| = 100` (`SimpleStabilizer.lean`)。`N` の Sylow `5`-部分群は
  位数 25 で `n₅ ∣ 4`, `n₅ ≡ 1 (mod 5)` から `n₅ = 1`, ゆえに特性的。すると
  `G` の位数 25 の非自明正規部分群ができ, 原始性からそれも推移的でなければならないが
  `100 ∤ 25`。

## Main results

- `isPreprimitive_of_orbits_eq` — **8C.4** 前半 (原始性)。
- `isSimpleGroup_of_orbits_eq` — **8C.4** 後半 (単純性)。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problem 8C.4 -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- 点安定化群の軌道に `α` は入らない (`α` の軌道は `{α}` だけ)。 -/
private lemma notMem_orbit_stabilizer {α δ : Ω} (hδ : δ ≠ α) :
    α ∉ orbit ↥(stabilizer G α) δ := by
  rintro ⟨h, hh⟩
  refine hδ ?_
  have hh' : (h : G) • δ = α := hh
  have h1 : ((h : G))⁻¹ • α = α := mem_stabilizer_iff.mp ((stabilizer G α).inv_mem h.2)
  calc δ = ((h : G))⁻¹ • ((h : G) • δ) := (inv_smul_smul _ _).symm
    _ = ((h : G))⁻¹ • α := by rw [hh']
    _ = α := h1

/-- **Isaacs Problem 8C.4** (p. 257), 前半。`|Ω| = 100` で点安定化群の `Ω ∖ {α}` 上の
軌道が長さ 22 と 77 のちょうど 2 つなら, `G` は原始的。 -/
theorem isPreprimitive_of_orbits_eq [Finite Ω] [IsPretransitive G Ω]
    (hΩ : Nat.card Ω = 100) (α : Ω) {β γ : Ω} (hβ : β ≠ α) (hγ : γ ≠ α)
    (h22 : (orbit ↥(stabilizer G α) β).ncard = 22)
    (h77 : (orbit ↥(stabilizer G α) γ).ncard = 77)
    (hcover : ∀ δ : Ω, δ ≠ α →
      δ ∈ orbit ↥(stabilizer G α) β ∨ δ ∈ orbit ↥(stabilizer G α) γ) :
    IsPreprimitive G Ω := by
  classical
  -- `α` を含む block は `{α}` か `Ω` 全体
  have key : ∀ B : Set Ω, IsBlock G B → α ∈ B → B = {α} ∨ B = Set.univ := by
    intro B hB hαB
    have hsmul : ∀ h : ↥(stabilizer G α), (h : G) • B = B := by
      intro h
      rw [isBlock_iff_smul_eq_of_mem] at hB
      refine hB hαB ?_
      rw [mem_stabilizer_iff.mp h.2]
      exact hαB
    have horb : ∀ δ ∈ B, orbit ↥(stabilizer G α) δ ⊆ B := by
      rintro δ hδ ε ⟨h, rfl⟩
      have hmem : (h : G) • δ ∈ (h : G) • B := Set.smul_mem_smul_set hδ
      rw [hsmul h] at hmem
      exact hmem
    -- `B` が軌道と交われば軌道を丸ごと含む
    have hmeet : ∀ δ : Ω, δ ∈ B → ∀ ε : Ω, δ ∈ orbit ↥(stabilizer G α) ε →
        orbit ↥(stabilizer G α) ε ⊆ B := by
      intro δ hδ ε hδε
      rw [← orbit_eq_iff.mpr hδε]
      exact horb δ hδ
    have hdvd : B.ncard ∣ 100 := hΩ ▸ hB.ncard_dvd_card ⟨α, hαB⟩
    by_cases hb : orbit ↥(stabilizer G α) β ⊆ B <;> by_cases hc : orbit ↥(stabilizer G α) γ ⊆ B
    · -- 両方含む ⟹ 全体
      right
      rw [Set.eq_univ_iff_forall]
      intro δ
      rcases eq_or_ne δ α with rfl | hδ
      · exact hαB
      · exact (hcover δ hδ).elim (fun h => hb h) fun h => hc h
    · -- 22-軌道のみ ⟹ `|B| = 23` だが `23 ∤ 100`
      exfalso
      have hBeq : B = insert α (orbit ↥(stabilizer G α) β) := by
        refine Set.Subset.antisymm (fun δ hδ => ?_) ?_
        · rcases eq_or_ne δ α with rfl | hne
          · exact Set.mem_insert _ _
          · exact (hcover δ hne).elim (fun h => Set.mem_insert_of_mem _ h)
              fun h => absurd (hmeet δ hδ γ h) hc
        · rintro δ hδ
          rcases Set.mem_insert_iff.mp hδ with rfl | hδ
          · exact hαB
          · exact hb hδ
      rw [hBeq, Set.ncard_insert_of_notMem (notMem_orbit_stabilizer hβ) (Set.toFinite _),
        h22] at hdvd
      norm_num at hdvd
    · -- 77-軌道のみ ⟹ `|B| = 78` だが `78 ∤ 100`
      exfalso
      have hBeq : B = insert α (orbit ↥(stabilizer G α) γ) := by
        refine Set.Subset.antisymm (fun δ hδ => ?_) ?_
        · rcases eq_or_ne δ α with rfl | hne
          · exact Set.mem_insert _ _
          · exact (hcover δ hne).elim (fun h => absurd (hmeet δ hδ β h) hb)
              fun h => Set.mem_insert_of_mem _ h
        · rintro δ hδ
          rcases Set.mem_insert_iff.mp hδ with rfl | hδ
          · exact hαB
          · exact hc hδ
      rw [hBeq, Set.ncard_insert_of_notMem (notMem_orbit_stabilizer hγ) (Set.toFinite _),
        h77] at hdvd
      norm_num at hdvd
    · -- どちらも含まない ⟹ `B = {α}`
      left
      refine Set.Subset.antisymm (fun δ hδ => ?_) ?_
      · rcases eq_or_ne δ α with rfl | hne
        · rfl
        · exact (hcover δ hne).elim (fun h => absurd (hmeet δ hδ β h) hb)
            fun h => absurd (hmeet δ hδ γ h) hc
      · rintro δ hδ
        rw [Set.mem_singleton_iff.mp hδ]
        exact hαB
  -- 一般の block は `α` を含む translate に移して判定する
  refine ⟨fun {B} hB => ?_⟩
  rcases Set.eq_empty_or_nonempty B with rfl | ⟨b, hb⟩
  · exact Or.inl Set.subsingleton_empty
  obtain ⟨g, hg⟩ := exists_smul_eq G b α
  have hαgB : α ∈ g • B := hg ▸ Set.smul_mem_smul_set hb
  rcases key (g • B) (hB.translate g) hαgB with h | h
  · left
    have hBeq : B = g⁻¹ • ({α} : Set Ω) := by rw [← h, inv_smul_smul]
    rw [hBeq, Set.smul_set_singleton]
    exact Set.subsingleton_singleton
  · right
    have hBeq : B = g⁻¹ • (Set.univ : Set Ω) := by rw [← h, inv_smul_smul]
    rw [hBeq, Set.smul_set_univ]

/-- **Isaacs Problem 8C.4** (p. 257), 後半。上の仮定のもと `G` は単純。

**Note** (Isaacs)。Higman–Sims 群 `HS` がこの条件を満たし, 点安定化群は `M₂₂`。 -/
theorem isSimpleGroup_of_orbits_eq [Finite G] [FaithfulSMul G Ω] [IsPretransitive G Ω]
    (hΩ : Nat.card Ω = 100) (α : Ω) (hsimple : IsSimpleGroup ↥(stabilizer G α))
    {β γ : Ω} (hβ : β ≠ α) (hγ : γ ≠ α)
    (h22 : (orbit ↥(stabilizer G α) β).ncard = 22)
    (h77 : (orbit ↥(stabilizer G α) γ).ncard = 77)
    (hcover : ∀ δ : Ω, δ ≠ α →
      δ ∈ orbit ↥(stabilizer G α) β ∨ δ ∈ orbit ↥(stabilizer G α) γ) :
    IsSimpleGroup G := by
  haveI : Finite Ω := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : IsPreprimitive G Ω := isPreprimitive_of_orbits_eq hΩ α hβ hγ h22 h77 hcover
  -- `100 ∣ |G|` なので `G` は非自明
  have h100G : (100 : ℕ) ∣ Nat.card G := by
    have h := index_stabilizer_of_transitive (G := G) (x := α)
    rw [hΩ] at h
    exact h ▸ Subgroup.index_dvd_card _
  haveI : Nonempty G := ⟨1⟩
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd Nat.card_pos h100G))
  refine ⟨fun N hN => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hNbot, hNtop⟩ := hcon
  haveI := hN
  haveI : IsPretransitive ↥N Ω := isPretransitive_of_normal_of_isPreprimitive (Ω := Ω) N hNbot
  have hstabN : stabilizer ↥N α = ⊥ :=
    stabilizer_eq_bot_of_normal_of_isSimpleGroup_stabilizer α hsimple hNtop
  have hNcard : Nat.card ↥N = 100 := by
    rw [card_eq_card_of_stabilizer_eq_bot α hstabN, hΩ]
  -- `N` の Sylow 5-部分群は位数 25 で一意 (`n₅ ∣ 4`, `n₅ ≡ 1 mod 5`)
  obtain ⟨P⟩ := Sylow.nonempty (p := 5) (G := ↥N)
  have hPcard : Nat.card (P : Subgroup ↥N) = 25 :=
    card_sylow_eq_pow_of_not_dvd_succ (k := 2) P (by rw [hNcard]; norm_num)
      (by rw [hNcard]; norm_num)
  have hn5 : Nat.card (Sylow 5 ↥N) = 1 := by
    have hidx : (P : Subgroup ↥N).index = 4 := by
      have h := Subgroup.card_mul_index (P : Subgroup ↥N)
      rw [hPcard, hNcard] at h
      omega
    have hdvd : Nat.card (Sylow 5 ↥N) ∣ 4 := hidx ▸ P.card_dvd_index
    have hmod : Nat.card (Sylow 5 ↥N) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 ↥N
    have hcases : ∀ e ∈ Nat.divisors 4, e = 1 ∨ e = 2 ∨ e = 4 := by decide
    have hmem : Nat.card (Sylow 5 ↥N) ∈ Nat.divisors 4 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    unfold Nat.ModEq at hmod
    rcases hcases _ hmem with h | h | h <;> rw [h] at hmod ⊢ <;> omega
  haveI : Subsingleton (Sylow 5 ↥N) := (Nat.card_eq_one_iff_unique.mp hn5).1
  haveI : (P : Subgroup ↥N).Characteristic := Sylow.characteristic_of_subsingleton P
  -- `P` を `G` の部分群として見ると位数 25 の非自明正規部分群
  have hP'card : Nat.card ↥((P : Subgroup ↥N).map N.subtype) = 25 := by
    rw [← hPcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (P : Subgroup ↥N) N.subtype
      (Subgroup.subtype_injective N)).toEquiv).symm
  have hP'bot : (P : Subgroup ↥N).map N.subtype ≠ ⊥ := by
    intro h
    rw [h] at hP'card
    simp at hP'card
  haveI : IsPretransitive ↥((P : Subgroup ↥N).map N.subtype) Ω :=
    isPretransitive_of_normal_of_isPreprimitive (Ω := Ω) _ hP'bot
  -- 推移的なら `100 ∣ 25`
  have h100 : (100 : ℕ) ∣ 25 := by
    have h := index_stabilizer_of_transitive
      (G := ↥((P : Subgroup ↥N).map N.subtype)) (x := α)
    rw [hΩ] at h
    rw [← hP'card]
    exact h ▸ Subgroup.index_dvd_card _
  norm_num at h100

end -- Problem 8C.4

end OddOrder.Isaacs.Ch08
