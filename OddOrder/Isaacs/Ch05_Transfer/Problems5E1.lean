/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Problems5E

/-!
# Isaacs Problem 5E.1 (Itô) — 極小非 `p`-冪零群 (書籍 p. 175)

**主張**: 有限群 `G` の真部分群がすべて正規 `p`-補群をもつが `G` 自身は持たないとする。
このとき `G` は**正規 Sylow `p`-部分群**をもち, `|G|` の `p` 以外の素因数は**ちょうど 1 個**。

**証明** (⭐ 位数に関する帰納法は不要 — 補題 1 を `G` と `G/O_p(G)` の 2 つに使うだけ):

* **補題 1**: Frobenius Thm 5.26 の対偶より `N_G(X)` が正規 `p`-補群を持たない非自明
  `p`-部分群 `X` が存在し, 仮定から `N_G(X) = ⊤` すなわち `X ◁ G` ⟹ `O_p(G) ≠ 1`。
* **補題 2** ⭐: `M ◁ G` で `|G:M| = p` は起こらない。`M` は真部分群ゆえ `p`-冪零で,
  その正規 `p`-補群 `C` は一意性から `M` に characteristic ⟹ `C ◁ G`。
  `p ∤ |C|` かつ `|G:C| = p·|M:C|` が `p`-冪なので `C` が `G` の正規 `p`-補群になり矛盾。
* **補題 3**: `G/O_p(G)` は `p`-冪零。そうでなければ補題 1 が `G/O_p(G)` にも使えて
  `O_p(G)` の最大性に矛盾。
* **(a)**: 補題 3 の正規 `p`-補群の引き戻し `K` は `|G:K|` が `p`-冪。`K ≠ ⊤` なら `G/K` は
  非自明 `p`-群ゆえ指数 `p` の正規部分群をもち補題 2 に矛盾 ⟹ `K = ⊤` ⟹ `G/O_p(G)` は
  `p'`-群 ⟹ `O_p(G)` が正規 Sylow `p`-部分群。
* **(b)**: Schur–Zassenhaus の Hall `p'`-補群 `H` の各 Sylow `S` について `P·S` は真部分群
  ゆえ `p`-冪零で `[P,S] = 1`。`H` は Sylow たちで生成される (`iSup_sylow_eq_top`) ので
  `H ≤ C_G(P)` ⟹ `H` が正規 `p`-補群になり矛盾 ⟹ `|H|` は素数冪。
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise

variable {G : Type*} [Group G]

section /- 5E.1: 極小非 `p`-冪零群 (Itô) (p. 175) -/

/-- 正規 `p`-補群の性質は**全射像**に遺伝する。 -/
theorem hasNormalPComplement_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    {p : ℕ} [Fact p.Prime] {f : A →* B} (hf : Function.Surjective f)
    (hA : HasNormalPComplement p A) : HasNormalPComplement p B := by
  classical
  haveI : Finite B := Finite.of_surjective f hf
  obtain ⟨N, hNnormal, hNcompl⟩ := hA
  haveI := hNnormal
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p A))
  have hpN : ¬ p ∣ Nat.card ↥N := not_dvd_card_of_isComplement'_sylow Q (hNcompl Q)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hNidx : N.index = p ^ a := by rw [(hNcompl Q).symm.index_eq_card, ha]
  haveI : (N.map f).Normal := hNnormal.map _ hf
  have hidxdvd : (N.map f).index ∣ p ^ a := hNidx ▸ N.index_map_dvd hf
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow Fact.out).mp hidxdvd
  refine hasNormalPComplement_of_normal_of_index_eq_pow (X := N.map f) (a := b) ?_ hb
  intro hdvd
  exact hpN (hdvd.trans (Subgroup.card_map_dvd _ _))

/-- 真部分群がすべて正規 `p`-補群をもち `G` 自身は持たないとき, `O_p(G) ≠ 1`。

Frobenius Thm 5.26 の対偶で `N_G(X)` が正規 `p`-補群を持たない非自明 `p`-部分群が取れ,
仮定からそれは `⊤` すなわち `X ◁ G`。 -/
theorem opCore_ne_bot_of_minimal_non_pNilpotent [Finite G] {p : ℕ} [Fact p.Prime]
    (hproper : ∀ H : Subgroup G, H ≠ ⊤ → HasNormalPComplement p ↥H)
    (hG : ¬ HasNormalPComplement p G) :
    Ch01.opCore p G ≠ ⊥ := by
  classical
  intro hbot
  refine hG (hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer.mpr ?_)
  refine isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement ?_
  intro X hXbot hXp
  by_cases htop : Subgroup.normalizer (X : Set G) = ⊤
  · haveI : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    exact absurd (le_bot_iff.mp (hbot ▸ Ch01.normal_pgroup_le_opCore hXp)) hXbot
  · exact hproper _ htop

/-- 真部分群がすべて正規 `p`-補群をもち `G` 自身は持たないとき, 指数 `p` の正規部分群は無い。

⭐ Itô の定理の鍵。真部分群 `M` の正規 `p`-補群は一意性から `M` に characteristic なので
`G` でも正規になり, 指数が `p`-冪ゆえ `G` の正規 `p`-補群になってしまう。 -/
theorem not_exists_normal_index_eq_prime_of_minimal_non_pNilpotent [Finite G] {p : ℕ}
    [Fact p.Prime] (hproper : ∀ H : Subgroup G, H ≠ ⊤ → HasNormalPComplement p ↥H)
    (hG : ¬ HasNormalPComplement p G) :
    ¬ ∃ M : Subgroup G, M.Normal ∧ M.index = p := by
  classical
  rintro ⟨M, hMnormal, hMidx⟩
  haveI := hMnormal
  have hMtop : M ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hMidx
    exact (Fact.out : p.Prime).one_lt.ne hMidx
  obtain ⟨C', hC'normal, hC'compl⟩ := hproper M hMtop
  haveI := hC'normal
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p ↥M))
  haveI : C'.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro ψ
    exact map_mulAut_of_normal_pcomplement (hC'compl S) ψ
  haveI hCnormal : (C'.map M.subtype).Normal := Ch01.characteristic_map_subtype_normal C'
  have hpC : ¬ p ∣ Nat.card ↥(C'.map M.subtype) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective M)]
    exact not_dvd_card_of_isComplement'_sylow S (hC'compl S)
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hrel : (C'.map M.subtype).relIndex M * M.index = (C'.map M.subtype).index :=
    Subgroup.relIndex_mul_index (Subgroup.map_subtype_le _)
  have hrel2 : (C'.map M.subtype).relIndex M = C'.index := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective M)]
  refine hG (hasNormalPComplement_of_normal_of_index_eq_pow
    (X := C'.map M.subtype) (a := c + 1) hpC ?_)
  rw [← hrel, hrel2, (hC'compl S).symm.index_eq_card, hc, hMidx, pow_succ]

end

end OddOrder.Isaacs.Ch05
