/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.RegularRepresentations
import Mathlib.Tactic.NormNum.Prime

/-!
# 素数次数の置換群 (Isaacs Problems 8C の準備)

素数 `p` 個の点への忠実な作用について, 位数 `p` の部分群 `H` は **regular** であり,
その中心化群は `H` 自身, 正規化群の位数は `p(p-1)` を割る。Isaacs Problem 8C.2
(次数 11 位数 7920 の置換群は単純) の骨格を与える。

## Main results

- `isPretransitive_of_card_eq_prime` — 位数 `p` の部分群は `p` 点上推移的 (regular)。
- `le_centralizer_of_card_eq_prime` — 素数位数の部分群は可換 (自身を中心化)。
- `centralizer_eq_of_card_eq_prime` — `C_G(H) = H` (**Problem 8A.2** の半正則性から)。
- `card_normalizer_dvd_of_card_eq_prime` — `|N_G(H)| ∣ p(p-1)` (`N/C ↪ Aut(H)`,
  `|Aut(Z_p)| = p - 1`)。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

section /- 素数次数の置換群 -/

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [FaithfulSMul G Ω]

/-- 素数 `p` 個の点への忠実な作用では, 位数 `p` の部分群 `H` は推移的 (よって regular)。

`H` の軌道の大きさは `|H| = p` を割るので `1` か `p`。`H ≠ 1` と忠実性からある点は
動くので, その軌道の大きさは `p`, つまり `Ω` 全体。 -/
theorem isPretransitive_of_card_eq_prime {p : ℕ} (hp : p.Prime) (hΩ : Nat.card Ω = p)
    (H : Subgroup G) (hH : Nat.card H = p) :
    IsPretransitive ↥H Ω := by
  haveI : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hΩ]; exact hp.pos.ne')
  haveI : Nontrivial ↥H := Finite.one_lt_card_iff_nontrivial.mp (by rw [hH]; exact hp.one_lt)
  obtain ⟨h, hh1⟩ := exists_ne (1 : ↥H)
  obtain ⟨ω, hω⟩ : ∃ ω : Ω, h • ω ≠ ω := by
    by_contra hc
    push Not at hc
    refine hh1 (Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun β => ?_))
    rw [show ((1 : ↥H) : G) = 1 from rfl, one_smul]
    exact hc β
  have hdvd : (orbit ↥H ω).ncard ∣ p := by
    rw [← hH, ← index_stabilizer]
    exact Subgroup.index_dvd_card _
  have hne1 : (orbit ↥H ω).ncard ≠ 1 := by
    intro h1
    rw [Set.ncard_eq_one] at h1
    obtain ⟨a, ha⟩ := h1
    refine hω ?_
    have h1 : h • ω ∈ ({a} : Set Ω) := ha ▸ mem_orbit ω h
    have h2 : ω ∈ ({a} : Set Ω) := ha ▸ mem_orbit_self ω
    rw [Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  have hcard : (orbit ↥H ω).ncard = p := (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  refine (isPretransitive_iff_orbit_eq_univ ω).mpr ?_
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
  rw [Set.ncard_univ, hΩ, hcard]

omit [Finite G] in
/-- 素数位数の部分群は巡回的, したがって自分自身を中心化する。 -/
theorem le_centralizer_of_card_eq_prime {p : ℕ} (hp : p.Prime) (H : Subgroup G)
    (hH : Nat.card H = p) :
    H ≤ Subgroup.centralizer (H : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic ↥H := isCyclic_of_prime_card hH
  intro a ha
  refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
  exact congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : ↥H) ⟨a, ha⟩)

/-- **Isaacs Problem 8C.2 の鍵 (i)**。素数 `p` 点への忠実な作用で `|H| = p` なら
`C_G(H) = H`。

`H` は推移的 (`isPretransitive_of_card_eq_prime`) なので **Problem 8A.2**
(`centralizer_inf_stabilizer_eq_bot`) より `C_G(H)` は半正則, すなわち `Ω` 上自由に
作用する。よって `|C_G(H)| = |C_G(H) の軌道| ≤ |Ω| = p`。他方 `H ≤ C_G(H)` で
`|H| = p`。 -/
theorem centralizer_eq_of_card_eq_prime {p : ℕ} (hp : p.Prime) (hΩ : Nat.card Ω = p)
    (H : Subgroup G) (hH : Nat.card H = p) :
    Subgroup.centralizer (H : Set G) = H := by
  haveI : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hΩ]; exact hp.pos.ne')
  haveI := isPretransitive_of_card_eq_prime hp hΩ H hH
  haveI : Nonempty Ω := (Nat.card_pos_iff.mp (by rw [hΩ]; exact hp.pos)).1
  obtain ⟨ω⟩ := (inferInstance : Nonempty Ω)
  set C := Subgroup.centralizer (H : Set G) with hC
  -- `C` の `ω` における安定化群は自明 (半正則性)
  have hstab : stabilizer ↥C ω = ⊥ := by
    have hbot : (stabilizer G ω).subgroupOf C = ⊥ :=
      Subgroup.subgroupOf_eq_bot.mpr
        (disjoint_iff.mpr (by rw [inf_comm]; exact centralizer_inf_stabilizer_eq_bot (H := H) ω))
    rw [← hbot]
    ext x
    rfl
  -- したがって `|C| = |C の軌道| ≤ |Ω| = p`
  have hle : Nat.card ↥C ≤ p := by
    have h1 : (orbit ↥C ω).ncard = Nat.card ↥C := by
      rw [← index_stabilizer, hstab, Subgroup.index_bot]
    calc Nat.card ↥C = (orbit ↥C ω).ncard := h1.symm
      _ ≤ (Set.univ : Set Ω).ncard := Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      _ = p := by rw [Set.ncard_univ, hΩ]
  exact (Subgroup.eq_of_le_of_card_ge (le_centralizer_of_card_eq_prime hp H hH)
    (by rw [hH]; exact hle)).symm

/-- **Isaacs Problem 8C.2 の鍵 (ii)**。素数 `p` 点への忠実な作用で `|H| = p` なら
`|N_G(H)| ∣ p(p-1)`。

`N_G(H)/C_G(H) ↪ Aut(H)` (`Subgroup.normalizerMonoidHom`) で `C_G(H) = H` (上),
`|Aut(H)| = φ(p) = p - 1` (`IsCyclic.card_mulAut`)。 -/
theorem card_normalizer_dvd_of_card_eq_prime {p : ℕ} (hp : p.Prime)
    (hΩ : Nat.card Ω = p) (H : Subgroup G) (hH : Nat.card H = p) :
    Nat.card ↥(Subgroup.normalizer (H : Set G)) ∣ p * (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic ↥H := isCyclic_of_prime_card hH
  have hCH : Subgroup.centralizer (H : Set G) = H := centralizer_eq_of_card_eq_prime hp hΩ H hH
  set N := Subgroup.normalizer (H : Set G) with hN
  set K := (Subgroup.centralizer (H : Set G)).subgroupOf N with hK
  have hker : H.normalizerMonoidHom.ker = K := Subgroup.normalizerMonoidHom_ker H
  have hKcard : Nat.card ↥K = p := by
    have hcongr : Nat.card ↥K = Nat.card ↥(Subgroup.centralizer (H : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer (H : Set G))).toEquiv
    rw [hcongr, hCH, hH]
  have hKindex : K.index ∣ p - 1 := by
    rw [← hker, Subgroup.index_ker]
    refine dvd_trans (Subgroup.card_subgroup_dvd_card _) ?_
    rw [IsCyclic.card_mulAut ↥H, hH, Nat.totient_prime hp]
  calc Nat.card ↥N = Nat.card ↥K * K.index := (Subgroup.card_mul_index K).symm
    _ ∣ p * (p - 1) := by rw [hKcard]; exact Nat.mul_dvd_mul_left p hKindex

/-- **Isaacs Problem 8C.2 の Hint** 🎉: 11 点への忠実な作用をもつ位数 7920 の群では
`P ∈ Syl₁₁(G)` について **`|N_G(P)| = 55`**。

`|N_G(P)| ∣ 11·10 = 110` (`card_normalizer_dvd_of_card_eq_prime`) と `11 ∣ |N_G(P)|`
から `|N_G(P)| = 11m` (`m ∣ 10`)。Sylow の `n₁₁ = [G : N_G(P)] ≡ 1 (mod 11)` が
`m = 5` だけを残す。 -/
theorem card_normalizer_sylow_eleven_eq_55 (hΩ : Nat.card Ω = 11)
    (hG : Nat.card G = 7920) (P : Sylow 11 G) :
    Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) = 55 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hfact : (7920 : ℕ).factorization 11 = 1 := by
    rw [show (7920 : ℕ) = 11 * 720 from by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hPcard : Nat.card ↥(P : Subgroup G) = 11 := by
    rw [Sylow.card_eq_multiplicity, hG, hfact, pow_one]
  have hdvd110 : Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) ∣ 11 * 10 :=
    card_normalizer_dvd_of_card_eq_prime (by norm_num) hΩ (P : Subgroup G) hPcard
  have h11 : 11 ∣ Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
    have hdvd : Nat.card ↥(P : Subgroup G) ∣
        Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.le_normalizer (H := (P : Subgroup G)))).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    rwa [hPcard] at hdvd
  have hidx : Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) *
      (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = 7920 := by
    rw [Subgroup.card_mul_index, hG]
  have hmod : (Subgroup.normalizer ((P : Subgroup G) : Set G)).index % 11 = 1 % 11 := by
    have hcard := Sylow.card_eq_index_normalizer P
    have h2 := card_sylow_modEq_one (p := 11) (G := G)
    rw [hcard] at h2
    exact h2
  obtain ⟨m, hm⟩ := h11
  have hm10 : m ∣ 10 := by
    have h : 11 * m ∣ 11 * 10 := by rw [← hm]; exact hdvd110
    exact (mul_dvd_mul_iff_left (by norm_num : (11 : ℕ) ≠ 0)).mp h
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      rw [hm] at hidx
      omega
    · exact h
  have hmle : m ≤ 10 := Nat.le_of_dvd (by norm_num) hm10
  rw [hm] at hidx ⊢
  interval_cases m <;> omega

end -- 素数次数の置換群

end OddOrder.Isaacs.Ch08
