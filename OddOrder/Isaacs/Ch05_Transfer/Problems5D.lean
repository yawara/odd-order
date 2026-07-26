/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Problems5C13

/-!
# Isaacs Problems 5D — `A^p(G)` と p-transfer 制御 (書籍 pp. 169-170)

## 5D.1

`P ∈ Syl_p(G)` が可換で `P ⊆ H ⊆ G`, `H` が `G` の `p`-transfer を制御する
(Isaacs の定義: `A^p(H) = H ∩ A^p(G)`) とする。`H` が正規 `p`-補群をもつなら `G` ももつ。

**鍵**: 可換 Sylow `P` に対して

> `G` が正規 `p`-補群をもつ ⟺ `A^p(G) ⊓ P = ⊥`

(`⟸` は focal subgroup 定理 `A^p(G) ⊓ P = Foc_G(P) = G' ⊓ P` と Problem 5C.1、
`⟹` は「商が `P` の像で可換」+ `APrime_le`)。この同値を `H` 側で使って
`A^p(H) ⊓ P = ⊥` を得, 仮説で `A^p(G) ⊓ P = ⊥` に移し, `G` 側で使い直す。
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 5D.1: p-transfer 制御と正規 `p`-補群 (p. 169) -/

/-- 可換 Sylow `p`-部分群をもつ有限群が正規 `p`-補群をもつなら `A^p(G) ⊓ P = ⊥`。

正規 `p`-補群 `N` に対し `G/N` は `P` の像で可換なので `commutator G ≤ N`、
また `|G:N| = |P|` は `p`-冪なので `A^p(G) ≤ N` (`APrime_le`)。
`N` と `P` は補群対ゆえ交わりが自明。 -/
theorem APrime_inf_sylow_eq_bot_of_hasNormalPComplement [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [hPab : IsMulCommutative ↥(P : Subgroup G)]
    (hG : HasNormalPComplement p G) :
    APrime p G ⊓ (P : Subgroup G) = ⊥ := by
  classical
  obtain ⟨N, hNnormal, hNcompl⟩ := hG
  haveI := hNnormal
  have hcompl := hNcompl P
  -- `commutator G ≤ N`: `G = N · P` と `P` 可換から `G/N` は可換
  have hcomm : _root_.commutator G ≤ N := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have hmul : ((N ⊔ (P : Subgroup G) : Subgroup G) : Set G) = (N : Set G) * (P : Subgroup G) :=
      Subgroup.normal_mul N (P : Subgroup G)
    have htop : ((⊤ : Subgroup G) : Set G) = (N : Set G) * (P : Subgroup G) := by
      rw [← hmul, hcompl.sup_eq_top]
    have hain : a ∈ (N : Set G) * ((P : Subgroup G) : Set G) := by
      rw [← htop]; exact Subgroup.mem_top a
    have hbin : b ∈ (N : Set G) * ((P : Subgroup G) : Set G) := by
      rw [← htop]; exact Subgroup.mem_top b
    obtain ⟨n₁, hn₁, x, hx, rfl⟩ := hain
    obtain ⟨n₂, hn₂, y, hy, rfl⟩ := hbin
    have hxy : (⟨x, hx⟩ : ↥(P : Subgroup G)) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
      hPab.is_comm.comm _ _
    have hxycomm : x * y = y * x := congrArg Subtype.val hxy
    have hn₁' : (QuotientGroup.mk' N) n₁ = 1 := (QuotientGroup.eq_one_iff _).mpr hn₁
    have hn₂' : (QuotientGroup.mk' N) n₂ = 1 := (QuotientGroup.eq_one_iff _).mpr hn₂
    have hkey : (QuotientGroup.mk' N) ⁅n₁ * x, n₂ * y⁆ = 1 := by
      rw [map_commutatorElement, map_mul, map_mul, hn₁', hn₂', one_mul, one_mul,
        commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul, hxycomm]
    exact (QuotientGroup.eq_one_iff _).mp hkey
  -- `N.index = |P|` は `p`-冪
  have hidx : ∃ k : ℕ, N.index = p ^ k := by
    refine ⟨(Nat.card G).factorization p, ?_⟩
    rw [hcompl.symm.index_eq_card, P.card_eq_multiplicity]
  obtain ⟨k, hk⟩ := hidx
  have hAle : APrime p G ≤ N := APrime_le hNnormal hcomm hk
  refine le_antisymm ?_ bot_le
  calc APrime p G ⊓ (P : Subgroup G) ≤ N ⊓ (P : Subgroup G) := inf_le_inf hAle le_rfl
    _ = ⊥ := hcompl.disjoint.eq_bot

/-- 可換 Sylow `p`-部分群 `P` に対し `A^p(G) ⊓ P = ⊥` なら `G` は正規 `p`-補群をもつ
(`APrime_inf_sylow_eq_bot_of_hasNormalPComplement` の逆)。

focal subgroup 定理 (`A^p(G) ⊓ P = Foc_G(P) = G' ⊓ P`) で Problem 5C.1 に落とす。 -/
theorem hasNormalPComplement_of_APrime_inf_sylow_eq_bot [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (h : APrime p G ⊓ (P : Subgroup G) = ⊥) :
    HasNormalPComplement p G := by
  refine hasNormalPComplement_of_commutator_inf_sylow_eq_bot P ?_
  rw [Subgroup.commutator_inf_eq_focalSubgroup P, ← APrime_inf_sylow_eq_focalSubgroup P]
  exact h

/-- **Isaacs Problem 5D.1** (p. 169) ⭐: `P ∈ Syl_p(G)` が可換で `P ≤ H ≤ G`,
`H` が `G` の `p`-transfer を制御する (`A^p(H) = H ∩ A^p(G)`) とする。
`H` が正規 `p`-補群をもつなら `G` ももつ。

`p`-transfer 制御の仮説は Isaacs の定義そのまま (`A^p(H) = (A^p G).subgroupOf H`) で述べた。
Cor 5.22 (`APrime_eq_subgroupOf_APrime_of_controlsFusionIn`) はこの仮説の十分条件を与える。 -/
theorem hasNormalPComplement_of_controlsPTransfer [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsMulCommutative ↥(P : Subgroup G)] {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H)
    (hcontrol : APrime p ↥H = (APrime p G).subgroupOf H)
    (hH : HasNormalPComplement p ↥H) :
    HasNormalPComplement p G := by
  classical
  haveI hPHab : IsMulCommutative ↥((P.subtype hPH : Sylow p ↥H) : Subgroup ↥H) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hGeq : (((x : ↥H) : G)) * (((y : ↥H) : G)) = (((y : ↥H) : G)) * (((x : ↥H) : G)) :=
      congrArg Subtype.val
        (‹IsMulCommutative ↥(P : Subgroup G)›.is_comm.comm
          ⟨((x : ↥H) : G), x.2⟩ ⟨((y : ↥H) : G), y.2⟩)
    exact Subtype.ext (Subtype.ext hGeq)
  have hHbot : APrime p ↥H ⊓ ((P.subtype hPH : Sylow p ↥H) : Subgroup ↥H) = ⊥ :=
    APrime_inf_sylow_eq_bot_of_hasNormalPComplement (P.subtype hPH) hH
  rw [hcontrol, Sylow.coe_subtype, Subgroup.subgroupOf, Subgroup.subgroupOf,
    ← Subgroup.comap_inf] at hHbot
  refine hasNormalPComplement_of_APrime_inf_sylow_eq_bot P ?_
  have hle : APrime p G ⊓ (P : Subgroup G) ≤ H := inf_le_right.trans hPH
  refine le_antisymm (fun g hg => ?_) bot_le
  have hgH : g ∈ H := hle hg
  have hmem : (⟨g, hgH⟩ : ↥H) ∈ Subgroup.comap H.subtype (APrime p G ⊓ (P : Subgroup G)) := hg
  rw [hHbot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))

end

end OddOrder.Isaacs.Ch05
