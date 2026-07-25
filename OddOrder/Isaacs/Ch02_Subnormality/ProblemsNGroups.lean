/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch02_Subnormality.Theorem211Wielandt

/-!
# Isaacs Chapter 2 — Problems §2C: N-群 (p. 61)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) の章末演習 §2C (Problem 2C.1)。
**N-群** = 全ての local 部分群が可解な有限群 (`IsLocal` の定義は §2C 本文の
`Theorem211Wielandt.lean`)。

- **2C.1(a)** `isSolvable_quotient_of_isNGroup`: N-群の**真の**準同型像は可解。
- **2C.1(b)**: 非可解 N-群は一意な minimal normal subgroup `S` をもち、`S` は非可換単純。

Note (書籍): 非可解 N-群の分類は Thompson の仕事で、有限単純群分類への大きな一歩だった。
minimal simple group (真部分群がすべて可解な非可換有限単純群) は明らかに N-群である。
-/

namespace OddOrder.Isaacs.Ch02

variable {G : Type*} [Group G]

section /- Problems 2C: N-groups (p. 61) -/

/-- **N-群** (Isaacs p. 61): 全ての local 部分群 (`IsLocal`) が可解な群。 -/
def IsNGroup (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, IsLocal H → IsSolvable ↥H

/-- **Isaacs Problem 2C.1(a)**. N-群の**真の**準同型像 (`G ⧸ N`, `N ≠ ⊥`) は可解。

`p ∣ |N|` なる素数を取り `P ∈ Syl_p(N)` (`≠ ⊥`) とすると、Frattini argument
(`Sylow.normalizer_sup_eq_top`) で `N_G(P) ⊔ N = ⊤`。`N_G(P)` は local ゆえ可解で、
`N` が正規だから `↑(N_G(P) ⊔ N) = ↑N_G(P) · ↑N`、すなわち `N_G(P) → G ⧸ N` は全射。
よって `G ⧸ N` は可解群の準同型像で可解 (`solvable_of_surjective`)。 -/
theorem isSolvable_quotient_of_isNGroup [Finite G] (hG : IsNGroup G)
    {N : Subgroup G} [N.Normal] (hNe : N ≠ ⊥) : IsSolvable (G ⧸ N) := by
  classical
  -- `|N| > 1` ゆえ素因子 `p` と位数 `p` の元が取れる
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNe
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := ↥N)).ne'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpdvd
  have hxpg : IsPGroup p ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hxpg.exists_le_sylow
  -- `P` を `G` の部分群として見たものは非自明な `p`-部分群
  set Q : Subgroup G := (P : Subgroup ↥N).map N.subtype with hQ
  have hQne : Q ≠ ⊥ := by
    intro h
    have hPbot : (P : Subgroup ↥N) = ⊥ := by
      have hle := (Subgroup.map_eq_bot_iff _).mp (hQ.symm.trans h)
      rwa [Subgroup.ker_subtype, le_bot_iff] at hle
    have hxb : x ∈ (⊥ : Subgroup ↥N) := hPbot ▸ hP (Subgroup.mem_zpowers x)
    rw [Subgroup.mem_bot] at hxb
    rw [hxb, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hQpg : IsPGroup p ↥Q := by
    obtain ⟨n, hn⟩ := P.2.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [hQ, ← hn]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective _ _ N.subtype_injective).toEquiv).symm
  -- Frattini argument
  have hfr : Subgroup.normalizer (Q : Set G) ⊔ N = ⊤ := Sylow.normalizer_sup_eq_top P
  -- `N_G(Q)` は local ゆえ可解
  haveI : IsSolvable ↥(Subgroup.normalizer (Q : Set G)) :=
    hG _ ⟨p, hp, Q, hQne, hQpg, rfl⟩
  -- `N_G(Q) → G ⧸ N` は全射
  refine solvable_of_surjective (f := (QuotientGroup.mk' N).comp
    (Subgroup.normalizer (Q : Set G)).subtype) ?_
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hg : g ∈ ((Subgroup.normalizer (Q : Set G) ⊔ N : Subgroup G) : Set G) := by
    rw [hfr]; trivial
  rw [Subgroup.mul_normal] at hg
  obtain ⟨a, ha, n, hn, rfl⟩ := hg
  exact ⟨⟨a, ha⟩, (QuotientGroup.mk_mul_of_mem a hn).symm⟩

end

end OddOrder.Isaacs.Ch02
