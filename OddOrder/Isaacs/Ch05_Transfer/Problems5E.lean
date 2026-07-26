/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Problems3B
import OddOrder.Isaacs.Ch03_SplitExtensions.ProblemsSupersolvable
import OddOrder.Isaacs.Ch05_Transfer.Problems5D6

/-!
# Isaacs Problem 5E.2 — 真部分群がすべて超可解なら可解 (書籍 p. 175)

**主張**: 有限群 `G` の真部分群がすべて超可解なら `G` は可解。

**証明** (書籍 hint =「極小反例は単純、Problem 3B.10 で最小素因数の正規 `p`-補群」):
`|G|` に関する強帰納法 (極小反例)。

* 非自明な真の正規部分群 `N` があれば, `N` は超可解ゆえ可解, `G/N` の真部分群は `G` の
  真部分群 (`N` を含むもの) の像ゆえ超可解 (`IsSupersolvable.of_surjective`) で帰納法が効き,
  拡大が可解。
* そうでなければ `G` は**単純**。`G` が `p`-群なら可解。そうでないとき
  `p := minFac |G|` に対し, 非自明 `p`-部分群 `X` の正規化群 `N_G(X)` は真部分群
  (`N_G(X) = ⊤` なら単純性で `X = ⊥` か `X = ⊤`, どちらも除外) ゆえ超可解。
  **3B.7(b)** (`index_prime_of_isCoatom_of_isSupersolvable`) で極大部分群の指数が素数になり,
  **3B.8** (`exists_normal_qComplement`, `p` は最小素因数) で `N_G(X)` は正規 `p`-補群をもつ。
  **Frobenius Thm 5.26** (`hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer`)
  で `G` 自身が正規 `p`-補群 `K` をもつが, `p ∣ |G|` から `K ≠ ⊤`, `G` が `p`-群でないことから
  `K ≠ ⊥` — 単純性に矛盾。
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise

section /- 5E.2: 真部分群がすべて超可解なら可解 (p. 175) -/

universe u

/-- **Isaacs Problem 5E.2** (p. 175) ⭐: 有限群の真部分群がすべて超可解なら, その群は可解。 -/
theorem isSolvable_of_forall_proper_isSupersolvable {G : Type u} [Group G] [Finite G]
    (hsub : ∀ K : Subgroup G, K ≠ ⊤ → Ch03.IsSupersolvable ↥K) : IsSolvable G := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ (H : Type u) [Group H] [Finite H], Nat.card H = n →
      (∀ K : Subgroup H, K ≠ ⊤ → Ch03.IsSupersolvable ↥K) → IsSolvable H
  suffices hmain : motive (Nat.card G) from hmain G rfl hsub
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih H _ _ hcard hHsub
  have ih' : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card H →
      (∀ L : Subgroup K, L ≠ ⊤ → Ch03.IsSupersolvable ↥L) → IsSolvable K := by
    intro K _ _ hK hKsub
    exact ih (Nat.card K) (by simpa only [hcard] using hK) K rfl hKsub
  -- 場合分け: 非自明な真の正規部分群があるか
  by_cases hN : ∃ N : Subgroup H, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤
  · obtain ⟨N, hNnormal, hNbot, hNtop⟩ := hN
    haveI := hNnormal
    haveI : IsSolvable ↥N := (hHsub N hNtop).isSolvable
    have hlt : Nat.card (H ⧸ N) < Nat.card H := by
      have hmul : Nat.card ↥N * N.index = Nat.card H := Subgroup.card_mul_index N
      have hidx : N.index = Nat.card (H ⧸ N) := Subgroup.index_eq_card N
      have hNpos := Nat.card_pos (α := ↥N)
      have h1 : 1 < Nat.card ↥N := by
        rcases Nat.lt_or_ge (Nat.card ↥N) 2 with h | h
        · exact absurd (Subgroup.card_eq_one.mp (by omega)) hNbot
        · omega
      have hqpos := Nat.card_pos (α := H ⧸ N)
      rw [hidx] at hmul
      have hstep : 1 * Nat.card (H ⧸ N) < Nat.card ↥N * Nat.card (H ⧸ N) :=
        (Nat.mul_lt_mul_right hqpos).mpr h1
      rw [one_mul] at hstep
      omega
    haveI : IsSolvable (H ⧸ N) := by
      refine ih' (H ⧸ N) hlt (fun L hL => ?_)
      have hcomap : Subgroup.comap (QuotientGroup.mk' N) L ≠ ⊤ := by
        intro htop
        apply hL
        rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) L,
          htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
      refine (hHsub _ hcomap).of_surjective
        (f := ((QuotientGroup.mk' N).restrict (Subgroup.comap (QuotientGroup.mk' N) L)).codRestrict
          L (fun x => x.2)) ?_
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
      exact ⟨⟨x, hy⟩, rfl⟩
    exact solvable_of_ker_le_range (N.subtype) (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', N.range_subtype])
  -- `H` は単純 (または自明)
  push Not at hN
  by_cases htriv : Nat.card H = 1
  · have : Subsingleton H := Nat.card_eq_one_iff_unique.mp htriv |>.1
    exact ⟨⟨0, Subsingleton.elim _ _⟩⟩
  set p : ℕ := (Nat.card H).minFac with hpdef
  have hpprime : p.Prime := Nat.minFac_prime htriv
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hpdvd : p ∣ Nat.card H := Nat.minFac_dvd _
  by_cases hHp : IsPGroup p H
  · haveI := hHp.isNilpotent
    infer_instance
  -- 非自明 `p`-部分群の正規化群は真部分群ゆえ超可解、そこから正規 `p`-補群
  have hlocal : ∀ X : Subgroup H, X ≠ ⊥ → IsPGroup p X →
      HasNormalPComplement p ↥(Subgroup.normalizer (X : Set H)) := by
    intro X hXbot hXp
    have hXtop : X ≠ ⊤ := by
      intro htop
      exact hHp (by
        have := hXp
        rw [htop] at this
        exact this.of_equiv Subgroup.topEquiv)
    have hNXtop : Subgroup.normalizer (X : Set H) ≠ ⊤ := by
      intro htop
      haveI : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases hN X inferInstance hXbot with h
      exact hXtop h
    have hss : Ch03.IsSupersolvable ↥(Subgroup.normalizer (X : Set H)) := hHsub _ hNXtop
    have hmax : ∀ M : Subgroup ↥(Subgroup.normalizer (X : Set H)), IsCoatom M → M.index.Prime :=
      fun M hM => Ch03.index_prime_of_isCoatom_of_isSupersolvable hss hM
    have hsmall : ∀ r ∈ (Nat.card ↥(Subgroup.normalizer (X : Set H))).primeFactors, p ≤ r := by
      intro r hr
      refine Nat.minFac_le_of_dvd (Nat.mem_primeFactors.mp hr).1.two_le ?_
      exact (Nat.mem_primeFactors.mp hr).2.1.trans (Subgroup.card_subgroup_dvd_card _)
    obtain ⟨K, hKnormal, hpK, k, hk⟩ := Ch03.exists_normal_qComplement hpprime hmax hsmall
    haveI := hKnormal
    exact hasNormalPComplement_of_normal_of_index_eq_pow (X := K) (a := k) hpK hk
  have hHcompl : HasNormalPComplement p H :=
    hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer.mpr
      (isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement hlocal)
  -- 正規 `p`-補群 `K` は `⊥` でも `⊤` でもなく単純性に矛盾
  obtain ⟨K, hKnormal, hKcompl⟩ := hHcompl
  haveI := hKnormal
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p H))
  have hpK : ¬ p ∣ Nat.card ↥K := not_dvd_card_of_isComplement'_sylow Q (hKcompl Q)
  have hKtop : K ≠ ⊤ := by
    intro htop
    refine hpK ?_
    rw [htop, Subgroup.card_top]
    exact hpdvd
  have hKbot : K ≠ ⊥ := by
    intro hbot
    refine hHp ?_
    have hidx : K.index = Nat.card ↥(Q : Subgroup H) := (hKcompl Q).symm.index_eq_card
    have hcard : Nat.card H = Nat.card ↥(Q : Subgroup H) := by
      have hmul : Nat.card ↥K * K.index = Nat.card H := Subgroup.card_mul_index K
      have hKone : Nat.card ↥K = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [hKone, one_mul] at hmul
      rw [← hmul]
      exact hidx
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    exact IsPGroup.of_card (n := m) (by rw [hcard, hm])
  exact absurd (hN K inferInstance hKbot) hKtop

end

end OddOrder.Isaacs.Ch05
