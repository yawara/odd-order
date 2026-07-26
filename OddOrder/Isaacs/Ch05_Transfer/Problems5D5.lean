/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Problems5D3

/-!
# Isaacs Problem 5D.5 — `A^p(G) ∩ P = P'` から Tate 抜きで正規 `p`-補群 (書籍 p. 170)

**主張**: `P ∈ Syl_p(G)`, `A := A^p(G)` が `A ∩ P = P'` を満たし `P' ⊴ A` なら,
(Tate の定理を使わずに) `G` は正規 `p`-補群をもつ。

**証明** (書籍 hint そのまま): `A ⊴ G` なので `A ∩ P` は `A` の Sylow `p`-部分群
(`Ch03.isHallSubgroup_subgroupOf_of_normal`), 仮定からそれは `P'` で `A` に正規。よって
`P'` は `A` の**正規 Hall `p`-部分群**であり, `|G : A|` は `p`-冪 (`APrime_index_isPGroup`)。
あとは 5C.13 で切り出した共通エンジン
`hasNormalPComplement_of_commutator_normalHall_in_normal` — Schur–Zassenhaus で `A` 内の
`P'` の補群 `K` を取り, Frattini 論法で `G = N_G(K) P'`, `P' ⊆ Φ(P)` の非生成性で
`P` が `K` を正規化 — がそのまま結論を与える。

⭐ 書籍 hint の「Schur–Zassenhaus で `A` 内の `P'` の補群 `K` を取り `G = N_G(K)P'` を示し,
`P' ⊆ Φ(P)` から `P` が `K` を正規化する」は 5C.13 の最終段と**完全に同じ論法**なので,
そのエンジンを共有した。
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 5D.5: `A^p(G) ∩ P = P'` かつ `P' ⊴ A^p(G)` (p. 170) -/

/-- **Isaacs Problem 5D.5** (p. 170) ⭐: `P ∈ Syl_p(G)` と `A := A^p(G)` が
`A ∩ P = ⁅P,P⁆` を満たし `⁅P,P⁆` が `A` で正規なら, `G` は正規 `p`-補群をもつ
(Tate の定理は使わない)。 -/
theorem hasNormalPComplement_of_APrime_inf_sylow_eq_commutator [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G)
    (hAP : APrime p G ⊓ (P : Subgroup G) = ⁅(P : Subgroup G), (P : Subgroup G)⁆)
    (hnorm :
      ((⁅(P : Subgroup G), (P : Subgroup G)⁆ : Subgroup G).subgroupOf (APrime p G)).Normal) :
    HasNormalPComplement p G := by
  classical
  -- `⁅P,P⁆ ≤ A` (仮定の `A ⊓ P` 表示から)
  have hLA : (⁅(P : Subgroup G), (P : Subgroup G)⁆ : Subgroup G) ≤ APrime p G := by
    rw [← hAP]
    exact inf_le_left
  -- `⁅P,P⁆.subgroupOf A = P.subgroupOf A` は `A` の Sylow `p`-部分群 ⟹ 指数は `p` と素
  have hsub : (⁅(P : Subgroup G), (P : Subgroup G)⁆ : Subgroup G).subgroupOf (APrime p G)
      = (P : Subgroup G).subgroupOf (APrime p G) := by
    rw [← hAP, Subgroup.inf_subgroupOf_left]
  have hhall : Ch03.IsHallSubgroup ({p} : Set ℕ) ((P : Subgroup G).subgroupOf (APrime p G)) :=
    Ch03.isHallSubgroup_subgroupOf_of_normal (Ch01.sylow_isHallSubgroup_singleton P)
  have hpM : ¬ p ∣ ((⁅(P : Subgroup G), (P : Subgroup G)⁆ : Subgroup G).subgroupOf
      (APrime p G)).index := by
    rw [hsub]
    intro hdvd
    exact hhall.2 p (Nat.mem_primeFactors.mpr
      ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl
  obtain ⟨a, ha⟩ := APrime_index_isPGroup p G
  exact hasNormalPComplement_of_commutator_normalHall_in_normal P hLA hnorm hpM ha

end

end OddOrder.Isaacs.Ch05
