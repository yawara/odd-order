/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.PResidual
import OddOrder.Isaacs.Ch05_Transfer.Problems5D

/-!
# Isaacs Problem 5D.4 — `O^p` と `A^p` の部分群への制限 (書籍 p. 170)

**主張**: `P ∈ Syl_p(G)` と `P ⊆ K ⊆ G` に対し `O^p(K) ⊆ K ∩ O^p(G)` であり,
等号が成り立つなら `A^p(K) = K ∩ A^p(G)` (すなわち `K` が `p`-transfer を制御する)。

**証明**:

* 前半は `↥K ⧸ O^p(G).subgroupOf K` が `G ⧸ O^p(G)` (`p`-群) の部分群に埋まることから
  `O^p` の普遍性で従う。
* 後半は `A^p(K) ≤ K ∩ A^p(G)` (既存の `APrime_le_subgroupOf_APrime_of_sylow_le`) の逆向き。
  `O := O^p(G)`, `B := A^p(K)` を `G` に押し出したものとして
  1. **`K ⊔ O = ⊤`** (`P ≤ K` と `|G:O|` が `p`-冪・`|G:P|` が `p` と素),
  2. **`⁅G,G⁆ ≤ ⁅K,K⁆ ⊔ O`** (1 で `g = k·u` と分解し `O` を法に交換子を比べる),
  3. `A^p(G) ≤ O ⊔ ⁅G,G⁆ ≤ O ⊔ B` (`APrime_le` + 2 + `⁅K,K⁆ ≤ B`),
  4. **Dedekind** `K ⊓ (O ⊔ B) = (K ⊓ O) ⊔ B = B` (仮定 `K ⊓ O = O^p(K) ≤ B`)

  を順に使う。⭐ 仮定 `O^p(K) = K ∩ O^p(G)` は 4 でだけ効く。
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 5D.4: `O^p(K) ⊆ K ∩ O^p(G)` と `A^p` の等式 (p. 170) -/

/-- **Isaacs Problem 5D.4 前半** (p. 170): 任意の部分群 `K` に対し `O^p(K) ≤ K ∩ O^p(G)`。

`↥K ⧸ O^p(G).subgroupOf K` は `G ⧸ O^p(G)` の部分群と同型で, 後者は `p`-群。 -/
theorem pResidualOf_le_inf_pResidual [Finite G] {p : ℕ} [Fact p.Prime] (K : Subgroup G) :
    Ch09.pResidualOf p K ≤ K ⊓ Ch09.pResidual p G := by
  classical
  refine le_inf (Ch09.pResidualOf_le p K) ?_
  set O : Subgroup G := Ch09.pResidual p G with hO
  set f : ↥K →* G ⧸ O := (QuotientGroup.mk' O).comp K.subtype with hf
  have hker : f.ker = O.subgroupOf K := by
    ext x
    simp [hf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : IsPGroup p ↥f.range := by
    intro x
    obtain ⟨k, hk⟩ := (Ch09.isPGroup_quotient_pResidual (G := G) (p := p)) (x : G ⧸ O)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hquot0 : IsPGroup p (↥K ⧸ f.ker) :=
    hrange.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hquot : IsPGroup p (↥K ⧸ O.subgroupOf K) :=
    hquot0.of_equiv (QuotientGroup.quotientMulEquivOfEq hker)
  have hle : Ch09.pResidual p ↥K ≤ O.subgroupOf K :=
    Ch09.pResidual_le_of_isPGroup_quotient hquot
  calc Ch09.pResidualOf p K = (Ch09.pResidual p ↥K).map K.subtype := rfl
    _ ≤ (O.subgroupOf K).map K.subtype := Subgroup.map_mono hle
    _ = O ⊓ K := Subgroup.subgroupOf_map_subtype _ _
    _ ≤ O := inf_le_left

/-- `O^p(H) ≤ A^p(H)`: `H ⧸ A^p(H)` は `p`-冪位数ゆえ `p`-群。 -/
theorem pResidual_le_APrime (p : ℕ) (H : Type*) [Group H] [Finite H] [Fact p.Prime] :
    Ch09.pResidual p H ≤ APrime p H := by
  obtain ⟨k, hk⟩ := APrime_index_isPGroup p H
  refine Ch09.pResidual_le_of_isPGroup_quotient (IsPGroup.of_card (n := k) ?_)
  rw [← Subgroup.index_eq_card, hk]

/-- **Isaacs Problem 5D.4 後半** (p. 170) ⭐: `P ∈ Syl_p(G)`, `P ≤ K ≤ G` で
`O^p(K) = K ∩ O^p(G)` なら `A^p(K) = K ∩ A^p(G)`, すなわち `K` は `p`-transfer を制御する。 -/
theorem APrime_eq_subgroupOf_APrime_of_pResidualOf_eq [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {K : Subgroup G} (hPK : (P : Subgroup G) ≤ K)
    (hres : Ch09.pResidualOf p K = K ⊓ Ch09.pResidual p G) :
    APrime p ↥K = (APrime p G).subgroupOf K := by
  classical
  refine le_antisymm (APrime_le_subgroupOf_APrime_of_sylow_le P hPK) ?_
  set O : Subgroup G := Ch09.pResidual p G with hO
  set B : Subgroup G := (APrime p ↥K).map K.subtype with hB
  have hBK : B ≤ K := Subgroup.map_subtype_le _
  -- `|G : O|` は `p`-冪
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (Ch09.isPGroup_quotient_pResidual (G := G) (p := p))
  have hOidx : O.index = p ^ n := by rw [Subgroup.index_eq_card]; exact hn
  -- (1) `K ⊔ O = ⊤`
  have hKO : K ⊔ O = ⊤ := by
    have hPO : (P : Subgroup G) ⊔ O = ⊤ := by
      rw [← Subgroup.index_eq_one]
      have h1 : ((P : Subgroup G) ⊔ O).index ∣ (P : Subgroup G).index :=
        Subgroup.index_dvd_of_le le_sup_left
      have h2 : ((P : Subgroup G) ⊔ O).index ∣ p ^ n :=
        hOidx ▸ Subgroup.index_dvd_of_le le_sup_right
      by_contra hne
      obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne
      have hrp : r = p :=
        (Nat.prime_dvd_prime_iff_eq hr Fact.out).mp (hr.dvd_of_dvd_pow (hrdvd.trans h2))
      subst hrp
      exact P.not_dvd_index (hrdvd.trans h1)
    exact top_le_iff.mp (hPO.ge.trans (sup_le_sup_right hPK O))
  have hKOset : ((⊤ : Subgroup G) : Set G) = (K : Set G) * (O : Set G) := by
    have h := Subgroup.mul_normal K O
    rw [hKO] at h
    exact h
  -- (2) `⁅G,G⁆ ≤ ⁅K,K⁆ ⊔ O`
  have hcommG : (_root_.commutator G) ≤ ⁅K, K⁆ ⊔ O := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have hain : a ∈ (K : Set G) * (O : Set G) := by rw [← hKOset]; exact Subgroup.mem_top a
    have hbin : b ∈ (K : Set G) * (O : Set G) := by rw [← hKOset]; exact Subgroup.mem_top b
    obtain ⟨k₁, hk₁, u₁, hu₁, rfl⟩ := hain
    obtain ⟨k₂, hk₂, u₂, hu₂, rfl⟩ := hbin
    have hkk : (⁅k₁, k₂⁆ : G) ∈ ⁅K, K⁆ ⊔ O :=
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hk₁ hk₂)
    have hu₁' : (QuotientGroup.mk' O) u₁ = 1 := (QuotientGroup.eq_one_iff u₁).mpr hu₁
    have hu₂' : (QuotientGroup.mk' O) u₂ = 1 := (QuotientGroup.eq_one_iff u₂).mpr hu₂
    have hmk : (QuotientGroup.mk' O) ⁅k₁ * u₁, k₂ * u₂⁆ = (QuotientGroup.mk' O) ⁅k₁, k₂⁆ := by
      rw [map_commutatorElement, map_commutatorElement, map_mul, map_mul,
        hu₁', hu₂', mul_one, mul_one]
    have hdiff : ⁅k₁ * u₁, k₂ * u₂⁆ * (⁅k₁, k₂⁆ : G)⁻¹ ∈ O := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      change (QuotientGroup.mk' O) (⁅k₁ * u₁, k₂ * u₂⁆ * (⁅k₁, k₂⁆ : G)⁻¹) = 1
      rw [map_mul, map_inv, hmk, mul_inv_cancel]
    have hmem := Subgroup.mul_mem (⁅K, K⁆ ⊔ O) (Subgroup.mem_sup_right hdiff) hkk
    rwa [inv_mul_cancel_right] at hmem
  -- (3) `A^p(G) ≤ O ⊔ B`
  have hcommKB : (⁅K, K⁆ : Subgroup G) ≤ B := by
    rw [hB, ← Subgroup.map_subtype_commutator K]
    exact Subgroup.map_mono (commutator_le_APrime p ↥K)
  have hAle : APrime p G ≤ O ⊔ B := by
    have hnorm : (O ⊔ _root_.commutator G).Normal := Subgroup.sup_normal _ _
    have hidx : ∃ k : ℕ, (O ⊔ _root_.commutator G).index = p ^ k := by
      have hdvd : (O ⊔ _root_.commutator G).index ∣ p ^ n :=
        hOidx ▸ Subgroup.index_dvd_of_le le_sup_left
      obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
      exact ⟨j, hj⟩
    obtain ⟨k, hk⟩ := hidx
    refine (APrime_le hnorm le_sup_right hk).trans (sup_le le_sup_left ?_)
    exact hcommG.trans (sup_le (hcommKB.trans le_sup_right) le_sup_left)
  -- (4) Dedekind: `K ⊓ (O ⊔ B) = (K ⊓ O) ⊔ B = B`
  have hRB : K ⊓ O ≤ B := by
    rw [← hres, hB]
    exact Subgroup.map_mono (pResidual_le_APrime p ↥K)
  have hOBset : ((O ⊔ B : Subgroup G) : Set G) = (O : Set G) * (B : Set G) :=
    Subgroup.normal_mul O B
  have hkey : K ⊓ APrime p G ≤ B := by
    intro x hx
    have hxOB : x ∈ (O : Set G) * (B : Set G) := by
      rw [← hOBset]; exact hAle hx.2
    obtain ⟨u, hu, b, hb, rfl⟩ := hxOB
    have hbK : b ∈ K := hBK hb
    have huK : u ∈ K := by
      have : u = (u * b) * b⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hx.1 (Subgroup.inv_mem _ hbK)
    exact Subgroup.mul_mem _ (hRB ⟨huK, hu⟩) hb
  -- 目標へ翻訳
  have hcomap := Subgroup.comap_mono (f := K.subtype) hkey
  have hself : Subgroup.comap K.subtype K = (⊤ : Subgroup ↥K) := Subgroup.subgroupOf_self K
  rw [Subgroup.comap_inf, hself, top_inf_eq, hB,
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective] at hcomap
  exact hcomap

end

end OddOrder.Isaacs.Ch05
