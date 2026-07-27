/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.NormNum.Prime
import OddOrder.Isaacs.Ch05_Transfer.NilpotentPComplement
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8B.Blocks
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8C.PrimeDegree

/-!
# Isaacs Problem 8C.2 (p. 256) — 次数 11, 位数 7920 の置換群は単純

`Ω` を 11 点集合, `G` を `Ω` 上忠実に作用する位数 `7920 = 11·10·9·8` の群とすると
`G` は単純。Isaacs のヒント通り, まず Sylow `11`-部分群 `P` について `|N_G(P)| = 55`
を示すのが鍵。

**Note** (Isaacs)。実際にはそのような `G` は Mathieu 群 `M₁₁` に同型。

## 証明の流れ

1. `|P| = 11` (`11² ∤ 7920`)。`P` は 11 点上 regular (`isPretransitive_of_card_eq_prime`)
   なので `G` は推移的, 素数次数ゆえ**原始的** (`IsPreprimitive.of_prime_card`)。
2. `|N_G(P)| ∣ 11·10 = 110` (`card_normalizer_dvd_of_card_eq_prime`)。Sylow の第三定理
   `n₁₁ ≡ 1 (mod 11)` と合わせて `|N_G(P)| = 55`, `n₁₁ = 144`。
3. `1 ≠ N ◁ G` は原始性から推移的 (**Problem 8B.3**), よって `11 ∣ |N|`。`N` は Sylow
   `11`-部分群を含むので Frattini 論法で `[G:N] ∣ |N_G(P)| = 55`。`11 ∣ |N|` から
   `[G:N] = 5`, `|N| = 1584`。
4. すると `N_N(P) = P` (位数 11) なので **Burnside の正規 `p`-補群定理** (Isaacs Thm 5.13)
   より `N` は位数 144 の正規 11-補群 `K` をもつ。`K` は `N` の特性部分群
   (`map_mulAut_of_normal_pcomplement`) なので `G` で正規, しかし `11 ∤ 144` は
   step 3 (正規部分群は推移的) に反する。

## Main results

- `isSimpleGroup_of_card_eq_7920` — **Problem 8C.2** 本体。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- Problem 8C.2 の補助 (一般の有限群) -/

variable {G : Type*} [Group G] [Finite G]

/-- `p ∣ |G|` かつ `p² ∤ |G|` なら Sylow `p`-部分群の位数はちょうど `p`。 -/
theorem card_sylow_eq_prime_of_not_dvd_sq {p : ℕ} [Fact p.Prime] (Q : Sylow p G)
    (h1 : p ∣ Nat.card G) (h2 : ¬ p ^ 2 ∣ Nat.card G) :
    Nat.card (Q : Subgroup G) = p := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp Q.2
  have hdvd : Nat.card (Q : Subgroup G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  have hn2 : n ≤ 1 := by
    by_contra hc
    exact h2 (dvd_trans (pow_dvd_pow p (by omega)) (hn ▸ hdvd))
  have hn1 : 1 ≤ n := by
    by_contra hc
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hn
    refine Q.not_dvd_index ?_
    have hmul := Subgroup.card_mul_index (Q : Subgroup G)
    rw [hn, one_mul] at hmul
    rw [hmul]
    exact h1
  rw [hn, show n = 1 by omega, pow_one]

omit [Finite G] in
/-- `H.subgroupOf K` の位数は `|H ⊓ K|`。 -/
theorem card_subgroupOf_eq_card_inf (H K : Subgroup G) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ K ≤ K)).toEquiv

omit [Finite G] in
/-- **Frattini 論法の帳尻**: `N ◁ G` で `M ⊔ N = ⊤` なら `[M : M ∩ N] = [G : N]`。

`M → G ⧸ N` は `M ⊔ N = ⊤` から全射で, 核は `N ∩ M`。 -/
theorem index_subgroupOf_eq_index_of_sup_eq_top {N M : Subgroup G} [N.Normal]
    (h : M ⊔ N = ⊤) : (N.subgroupOf M).index = N.index := by
  set f : ↥M →* G ⧸ N := (QuotientGroup.mk' N).comp M.subtype with hf
  have hker : f.ker = N.subgroupOf M := by
    ext x
    simp [hf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : f.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ ((M ⊔ N : Subgroup G) : Set G) := by rw [h]; trivial
    rw [Subgroup.mul_normal M N] at hx
    obtain ⟨m, hm, n, hn, rfl⟩ := hx
    refine ⟨⟨m, hm⟩, ?_⟩
    simp [hf, (QuotientGroup.eq_one_iff n).mpr hn]
  rw [← hker, Subgroup.index_ker, hrange, Subgroup.card_top]
  rfl

end -- 補助

section /- Problem 8C.2 本体 -/

variable {G Ω : Type*} [Group G] [MulAction G Ω] [FaithfulSMul G Ω]

/-- **Isaacs Problem 8C.2** (p. 256)。次数 11, 位数 `7920 = 11·10·9·8` の置換群は単純。

**Note** (Isaacs)。実際にはそのような `G` は Mathieu 群 `M₁₁` に同型。 -/
theorem isSimpleGroup_of_card_eq_7920 (hΩ : Nat.card Ω = 11) (hG : Nat.card G = 7920) :
    IsSimpleGroup G := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Finite Ω := Nat.finite_of_card_ne_zero (by omega)
  haveI hne : Nonempty Ω := (Nat.card_pos_iff.mp (by omega)).1
  -- (1) 各 Sylow 11-部分群の位数は 11
  have hQcard : ∀ Q : Sylow 11 G, Nat.card (Q : Subgroup G) = 11 := fun Q =>
    card_sylow_eq_prime_of_not_dvd_sq Q (by rw [hG]; norm_num) (by rw [hG]; norm_num)
  obtain ⟨P⟩ := Sylow.nonempty (p := 11) (G := G)
  haveI : IsPretransitive ↥(P : Subgroup G) Ω :=
    isPretransitive_of_card_eq_prime (by norm_num) hΩ _ (hQcard P)
  haveI : IsPretransitive G Ω := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨q, hq⟩ := exists_smul_eq ↥(P : Subgroup G) a b
    exact ⟨q, hq⟩
  haveI : IsPreprimitive G Ω := IsPreprimitive.of_prime_card (G := G) (X := Ω)
    (by rw [hΩ]; norm_num)
  -- 原始群の自明でない正規部分群は推移的なので 11 で割れる (Problem 8B.3)
  have h11dvd : ∀ L : Subgroup G, L.Normal → L ≠ ⊥ → (11 : ℕ) ∣ Nat.card ↥L := by
    intro L hL hLbot
    haveI := hL
    haveI := isPretransitive_of_normal_of_isPreprimitive (Ω := Ω) L hLbot
    obtain ⟨ω⟩ := hne
    have h := index_stabilizer_of_transitive (G := ↥L) (x := ω)
    rw [hΩ] at h
    exact h ▸ Subgroup.index_dvd_card _
  -- (2) `|N_G(Q)| = 55`
  have hNcard : ∀ Q : Sylow 11 G,
      Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) = 55 := by
    intro Q
    have hdvd : Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) ∣ 110 := by
      have h := card_normalizer_dvd_of_card_eq_prime (p := 11) (Ω := Ω) (by norm_num) hΩ
        (Q : Subgroup G) (hQcard Q)
      rwa [show (11 : ℕ) * (11 - 1) = 110 from by norm_num] at h
    have hmul := Subgroup.card_mul_index (Subgroup.normalizer ((Q : Subgroup G) : Set G))
    rw [hG] at hmul
    have hmod : Nat.card (Sylow 11 G) ≡ 1 [MOD 11] := card_sylow_modEq_one 11 G
    rw [Q.card_eq_index_normalizer, ← Sylow.coe_coe] at hmod
    have hcases : ∀ e ∈ Nat.divisors 110,
        e = 1 ∨ e = 2 ∨ e = 5 ∨ e = 10 ∨ e = 11 ∨ e = 22 ∨ e = 55 ∨ e = 110 := by decide
    have hmem : Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) ∈ Nat.divisors 110 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    unfold Nat.ModEq at hmod
    rcases hcases _ hmem with h | h | h | h | h | h | h | h <;>
      rw [h] at hmul ⊢ <;> omega
  -- (3) 単純性
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨fun N hN => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hNbot, hNtop⟩ := hcon
  haveI := hN
  -- `N` は Sylow 11-部分群 `Q` を含む
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 11 (h11dvd N hN hNbot)
  have hy : orderOf ((x : G)) = 11 := by rw [Subgroup.orderOf_coe, hx]
  have hRcard : Nat.card ↥(Subgroup.zpowers ((x : G))) = 11 := by
    rw [Nat.card_zpowers, hy]
  obtain ⟨Q, hRQ⟩ :=
    (IsPGroup.of_card (p := 11) (n := 1) (by rw [hRcard, pow_one])).exists_le_sylow
  have hQR : (Q : Subgroup G) = Subgroup.zpowers ((x : G)) :=
    (Subgroup.eq_of_le_of_card_ge hRQ (by rw [hQcard Q, hRcard])).symm
  have hQN : (Q : Subgroup G) ≤ N := by
    rw [hQR]
    exact Subgroup.zpowers_le.mpr x.2
  -- Frattini 論法
  set M := Subgroup.normalizer ((Q : Subgroup G) : Set G) with hM
  have hsup : M ⊔ N = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top' (N := N) Q hQN
    rwa [← Sylow.coe_coe] at h
  have hMcard : Nat.card ↥M = 55 := by rw [hM]; exact hNcard Q
  have hMidx : (N.subgroupOf M).index = N.index :=
    index_subgroupOf_eq_index_of_sup_eq_top hsup
  -- `[G:N] = 5`, `|N| = 1584`
  have hidx55 : N.index ∣ 55 := by
    rw [← hMidx, ← hMcard]
    exact Subgroup.index_dvd_card _
  have hidxne1 : N.index ≠ 1 := fun h => hNtop (Subgroup.index_eq_one.mp h)
  have hNmul := Subgroup.card_mul_index N
  rw [hG] at hNmul
  have hidx0 : N.index ≠ 0 := by rintro h; rw [h, mul_zero] at hNmul; omega
  have h11N := h11dvd N hN hNbot
  have hidx5 : N.index = 5 := by
    have hmem : N.index ∈ Nat.divisors 55 := Nat.mem_divisors.mpr ⟨hidx55, by norm_num⟩
    have hcases : ∀ e ∈ Nat.divisors 55, e = 1 ∨ e = 5 ∨ e = 11 ∨ e = 55 := by decide
    rcases hcases _ hmem with h | h | h | h <;> rw [h] at hNmul hidxne1 ⊢ <;> omega
  have hNcard1584 : Nat.card ↥N = 1584 := by rw [hidx5] at hNmul; omega
  -- `N_N(Q) = Q` (位数 11)
  set Q' := (Q : Subgroup G).subgroupOf N with hQ'
  have hQ'card : Nat.card ↥Q' = 11 := by
    rw [hQ', card_subgroupOf_eq_card_inf, inf_of_le_left hQN, hQcard Q]
  have hMNcard : Nat.card ↥(M.subgroupOf N) = 11 := by
    have h1 : Nat.card ↥(N.subgroupOf M) = 11 := by
      have h := Subgroup.card_mul_index (N.subgroupOf M)
      rw [hMidx, hidx5, hMcard] at h
      omega
    rw [card_subgroupOf_eq_card_inf, inf_comm, ← card_subgroupOf_eq_card_inf]
    exact h1
  have hnormM : Subgroup.normalizer (Q' : Set ↥N) = M.subgroupOf N := by
    rw [hQ', ← Subgroup.subgroupOf_normalizer_eq hQN, hM]
  have hnorm : Subgroup.normalizer (Q' : Set ↥N) = Q' := by
    refine (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer ?_).symm
    rw [hnormM, hMNcard, hQ'card]
  -- Burnside の正規 11-補群
  obtain ⟨S, hQ'S⟩ :=
    (IsPGroup.of_card (p := 11) (n := 1) (by rw [hQ'card, pow_one])).exists_le_sylow
  have hScard : Nat.card (S : Subgroup ↥N) = 11 :=
    card_sylow_eq_prime_of_not_dvd_sq S (by rw [hNcard1584]; norm_num)
      (by rw [hNcard1584]; norm_num)
  have hSQ' : (S : Subgroup ↥N) = Q' :=
    (Subgroup.eq_of_le_of_card_ge hQ'S (by rw [hScard, hQ'card])).symm
  have hburn : Subgroup.normalizer ((S : Subgroup ↥N) : Set ↥N) ≤
      Subgroup.centralizer ((S : Subgroup ↥N) : Set ↥N) := by
    rw [hSQ', hnorm]
    exact le_centralizer_of_card_eq_prime (by norm_num) Q' hQ'card
  obtain ⟨K, hKn, hKc⟩ := Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer S hburn
  haveI := hKn
  have hKcard : Nat.card ↥K = 144 := by
    have h := (hKc S).card_mul
    rw [hScard, hNcard1584] at h
    omega
  haveI hKchar : K.Characteristic :=
    (Subgroup.characteristic_iff_map_eq).mpr fun ψ =>
      Ch05.map_mulAut_of_normal_pcomplement (hKc S) ψ
  -- `K` を `G` の部分群として見ると正規, しかし `11 ∤ 144`
  have hK'card : Nat.card ↥(K.map N.subtype) = 144 := by
    rw [← hKcard]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective K N.subtype (Subgroup.subtype_injective N)).toEquiv).symm
  have hK'bot : K.map N.subtype ≠ ⊥ := by
    intro h
    rw [h] at hK'card
    simp at hK'card
  have h11K := h11dvd (K.map N.subtype) inferInstance hK'bot
  rw [hK'card] at h11K
  norm_num at h11K

end -- Problem 8C.2

end OddOrder.Isaacs.Ch08
