/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.ThompsonPComplement
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7C_SylowMaximal

/-!
# Isaacs Problem 7C.1 — Thompson の normal `p`-complement 判定条件

**主張** (書籍 p. 210, Thompson): `P ∈ Syl_p(G)`, `p ≠ 2` で, `P` の**任意の**
characteristic 部分群 `X` について `N_G(X)/C_G(X)` が `p`-群なら, `G` は
normal `p`-complement をもつ。

本ファイルはまず, 証明の締めに使う道具

* `hasNormalPComplement_of_normal_pi'_of_isPGroup_quotient`:
  `M ⊴ G` が `p'`-群で `G/M` が `p`-群なら `M` は `G` の normal `p`-complement,

を用意する。
-/

namespace OddOrder.Isaacs.Ch07

variable {G : Type*} [Group G]

section /- 7C.1: normal `p`-complement の組み立て道具 (p. 210) -/

/-- 部分群への `IsPGroup` の遺伝 (`⊤` に使う)。 -/
private theorem isPGroup_subgroup {H : Type*} [Group H] {p : ℕ} (hH : IsPGroup p H)
    (K : Subgroup H) : IsPGroup p K := by
  intro g
  obtain ⟨k, hk⟩ := hH (g : H)
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

/-- **`M ⊴ G` が `p'`-群で `G/M` が `p`-群なら, `M` は `G` の normal `p`-complement**。

`G/M` は `p`-群なのでその Sylow `p`-部分群は `⊤` (`hasNormalPComplement_of_sylow_eq_top`),
したがって `G/M` は自明に normal `p`-complement をもち,
`hasNormalPComplement_of_quotient_of_isPiGroup_compl` で `G` に持ち上がる。 -/
theorem hasNormalPComplement_of_normal_pi'_of_isPGroup_quotient
    [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G} [M.Normal]
    (hM : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} M)
    (hQ : IsPGroup p (G ⧸ M)) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  refine hasNormalPComplement_of_quotient_of_isPiGroup_compl hM ?_
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p (G ⧸ M)))
  refine hasNormalPComplement_of_sylow_eq_top Q ?_
  exact (Q.is_maximal' (isPGroup_subgroup hQ ⊤) le_top).symm

end

end OddOrder.Isaacs.Ch07
