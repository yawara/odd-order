/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8D.PrimeIndexCore
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8D.SubdegreeTwo

/-!
# Isaacs Problem 8D.6 (p. 269) — 素数の subdegree

原始置換群で素数 `p` が subdegree として現れるなら, 点安定化群の位数は `p²` で割れず,
したがってどの subdegree も `p²` では割れない。

## 証明

`α → β` を `p`-arrow, `D := G_β ∩ G_α` とすると `|G_α : D| = |G_β : D| = p`
(後者は arrow の対称性 `IsArrow.symm` による)。Hint (`PrimeIndexCore.lean`) より
`R := ⟨D の p-元⟩` は `G_α` でも `G_β` でも正規化されるので `G_α ⊔ G_β ≤ N_G(R)`。
原始性から `G_α` は極大なので `G_α ⊔ G_β` は `G_α` か `⊤`。前者なら位数比較で
`G_β = G_α`, つまり `|G_α : D| = 1 ≠ p` で矛盾。よって `R ◁ G` かつ `R ≤ G_α` なので
忠実性から `R = ⊥` (`eq_bot_of_normal_of_le_stabilizer`)。すると `D` は位数 `p` の元を
持たないので Cauchy より `p ∤ |D|`, そして `|G_α| = |D| · p` だから `p² ∤ |G_α|`。

後半は subdegree が `|G_γ : G_δ ∩ G_γ|` の形で `|G_γ| = |G_α|` を割ることから従う。

## Main results

- `not_dvd_sq_card_stabilizer_of_prime_subdegree` — **8D.6 前半**。
- `not_dvd_sq_ncard_suborbit_of_prime_subdegree` — **8D.6 後半**。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- Problem 8D.6 -/

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [FaithfulSMul G Ω]

/-- **Isaacs Problem 8D.6** (前半, p. 269)。原始置換群で素数 `p` が subdegree として
現れるなら, 点安定化群の位数は `p²` で割り切れない。 -/
theorem not_dvd_sq_card_stabilizer_of_prime_subdegree [Nontrivial Ω] [IsPreprimitive G Ω]
    {p : ℕ} (hp : p.Prime) {α β : Ω} (hβ : Set.ncard (orbit ↥(stabilizer G α) β) = p) :
    ¬ p ^ 2 ∣ Nat.card ↥(stabilizer G α) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set D : Subgroup G := stabilizer G β ⊓ stabilizer G α with hD
  have hDα : D ≤ stabilizer G α := inf_le_right
  have hDβ : D ≤ stabilizer G β := inf_le_left
  -- `|G_α : D| = p`, そして arrow の対称性から `|G_β : D| = p`
  have hidxα : (D.subgroupOf (stabilizer G α)).index = p := by
    rw [← Subgroup.relIndex, hD, Subgroup.inf_relIndex_right, ← ncard_suborbit_eq_relIndex]
    exact hβ
  have hidxβ : (D.subgroupOf (stabilizer G β)).index = p := by
    have hsym : Set.ncard (orbit ↥(stabilizer G β) α) = p := IsArrow.symm (G := G) hβ
    rw [← Subgroup.relIndex, hD, inf_comm, Subgroup.inf_relIndex_right,
      ← ncard_suborbit_eq_relIndex]
    exact hsym
  -- Hint: `R := ⟨D の p-元⟩` は `G_α` でも `G_β` でも正規化される
  set R : Subgroup G := Subgroup.closure {g : G | g ∈ D ∧ ∃ k : ℕ, orderOf g = p ^ k} with hR
  have hnormα : stabilizer G α ≤ Subgroup.normalizer (R : Set G) := by
    rw [hR]; exact le_normalizer_closure_primePow hp hDα hidxα
  have hnormβ : stabilizer G β ≤ Subgroup.normalizer (R : Set G) := by
    rw [hR]; exact le_normalizer_closure_primePow hp hDβ hidxβ
  -- 原始性: `G_α` は極大なので `G_α ⊔ G_β = ⊤`
  have hcoat : IsCoatom (stabilizer G α) :=
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) α
  have hsup : stabilizer G α ⊔ stabilizer G β = ⊤ := by
    rcases eq_or_lt_of_le
      (le_sup_left : stabilizer G α ≤ stabilizer G α ⊔ stabilizer G β) with heq | hlt
    · exfalso
      have hle : stabilizer G β ≤ stabilizer G α := by rw [heq]; exact le_sup_right
      have heqβ : stabilizer G β = stabilizer G α :=
        Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_stabilizer_eq α β))
      rw [hD, heqβ, inf_idem, Subgroup.subgroupOf_self, Subgroup.index_top] at hidxα
      have := hp.one_lt
      omega
    · exact hcoat.2 _ hlt
  -- したがって `R ◁ G`, かつ `R ≤ G_α` なので忠実性から `R = ⊥`
  have : R.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le hnormα hnormβ
  have hRle : R ≤ stabilizer G α := by
    rw [hR, Subgroup.closure_le]
    rintro g ⟨hgD, -⟩
    exact hDα hgD
  have hbot : R = ⊥ := eq_bot_of_normal_of_le_stabilizer hRle
  -- `R = ⊥` は「`D` に位数 `p` の元が無い」, つまり Cauchy から `p ∤ |D|`
  have hpD : ¬ p ∣ Nat.card ↥D := by
    intro hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) p hdvd
    have hgmem : (g : G) ∈ R := by
      rw [hR]
      refine Subgroup.subset_closure ⟨g.2, 1, ?_⟩
      rw [pow_one, ← hg]
      exact orderOf_injective D.subtype Subtype.val_injective g
    rw [hbot, Subgroup.mem_bot] at hgmem
    rw [show g = 1 from Subtype.ext hgmem, orderOf_one] at hg
    exact hp.one_lt.ne hg
  -- `|G_α| = |D| · p` なので `p²` は `|G_α|` を割らない
  have hcard : Nat.card ↥D * p = Nat.card ↥(stabilizer G α) := by
    have h := Subgroup.card_mul_index (D.subgroupOf (stabilizer G α))
    rw [hidxα, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDα).toEquiv] at h
    exact h
  intro hsq
  rw [← hcard, pow_two] at hsq
  exact hpD ((Nat.mul_dvd_mul_iff_right hp.pos).mp hsq)

/-- **Isaacs Problem 8D.6** (後半, p. 269)。素数 `p` が subdegree として現れるなら,
どの subdegree も `p²` では割り切れない。

subdegree `|orbit_{G_γ}(δ)| = |G_γ : G_δ ∩ G_γ|` は `|G_γ|` を割り, 推移性から
`|G_γ| = |G_α|` なので前半に帰着する。 -/
theorem not_dvd_sq_ncard_suborbit_of_prime_subdegree [Nontrivial Ω] [IsPreprimitive G Ω]
    {p : ℕ} (hp : p.Prime) {α β : Ω} (hβ : Set.ncard (orbit ↥(stabilizer G α) β) = p)
    (γ δ : Ω) : ¬ p ^ 2 ∣ Set.ncard (orbit ↥(stabilizer G γ) δ) := by
  intro hdvd
  refine not_dvd_sq_card_stabilizer_of_prime_subdegree hp hβ (hdvd.trans ?_)
  rw [ncard_suborbit_eq_relIndex, Subgroup.relIndex, ← card_stabilizer_eq γ α]
  exact Subgroup.index_dvd_card _

end -- Problem 8D.6

end OddOrder.Isaacs.Ch08
