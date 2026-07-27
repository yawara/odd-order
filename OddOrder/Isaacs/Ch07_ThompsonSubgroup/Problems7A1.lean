/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.ThompsonPComplement
import OddOrder.Isaacs.Ch05_Transfer.NilpotentPComplement

/-!
# Isaacs Problem 7A.1 — 単純群の冪零な極大部分群は `2`-群 (書籍 p. 209)

**主張**: 単純群 `G` の極大部分群 `M` が冪零なら `M` は `2`-群。

**証明**: 奇素数 `p ∣ |M|` を仮定して矛盾を出す。`P` を `M` の Sylow `p`-部分群 (を `G` の
部分群として見たもの) とすると

* `M` 冪零なので `P ⊴ M`, つまり `M ≤ N_G(P)`。単純性から `N_G(P) ≠ ⊤`
  (`P ≠ ⊥`, `P = ⊤` は `M = ⊤` に矛盾) なので極大性で **`N_G(P) = M`**。
* したがって `P` は `N_G(P)` の中で極大 `p`-部分群なので **`P ∈ Syl_p(G)`**。
* `P` の任意の非自明 characteristic 部分群 `X` について `M ≤ N_G(X)`
  (`P` は `X` を正規化し, `M` の `p`-complement `H` は `⁅P, H⁆ ≤ P ⊓ H = ⊥` で `P` を
  中心化する)。再び単純性 + 極大性で `N_G(X) = M` で, `M` は冪零だから normal
  `p`-complement を持つ。
* **Isaacs Thm 6.23** (`hasNormalPComplement_of_forall_characteristic_normalizer`,
  `p ≠ 2` が必須) より `G` が normal `p`-complement `N` を持つ。単純性で `N = ⊥` なら
  `P = ⊤ ≤ M` で `M ≠ ⊤` に反し, `N = ⊤` なら `P = ⊥` で `p ∣ |M|` に反する。

教科書 Thm 7.1 (`Z(P)` と `J(P)` の 2 つだけを仮定する強い版) は不要で, Thm 6.23 で足りる —
冪零な極大部分群は `P` の characteristic 部分群を**すべて**正規化するから。
-/

namespace OddOrder.Isaacs.Ch07

section /- 7A.1: 単純群の冪零極大部分群 (p. 209) -/

/-- **`N_G(P)` の中で極大な `p`-部分群は `G` の Sylow `p`-部分群**。

`P ≤ S ∈ Syl_p(G)` を取る。`P < S` なら `S` (`p`-群ゆえ冪零) の normalizer condition から
`P` を正規化する `x ∈ S \ P` があり, `P⟨x⟩` は `N_G(P)` 内の `p`-部分群で `P` を真に含むので
極大性に反する。 -/
theorem exists_sylow_eq_of_maximal_pSubgroup_in_normalizer {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p ↥P)
    (hmax : ∀ R : Subgroup G, IsPGroup p ↥R → P ≤ R → R ≤ Subgroup.normalizer P → R = P) :
    ∃ S : Sylow p G, (S : Subgroup G) = P := by
  classical
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  refine ⟨S, le_antisymm ?_ hPS⟩
  by_contra hnot
  -- `P.subgroupOf S ≠ ⊤`
  have hHne : (P.subgroupOf (S : Subgroup G)) ≠ ⊤ := by
    intro htop
    exact hnot (Subgroup.subgroupOf_eq_top.mp htop)
  haveI : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent (G := ↥(S : Subgroup G))
    (P.subgroupOf (S : Subgroup G)) (lt_top_iff_ne_top.mpr hHne)
  obtain ⟨x, hxnorm, hxnot⟩ := SetLike.exists_of_lt hlt
  -- `x` は `P` を (G の中で) 正規化する
  have hxN : ((x : ↥(S : Subgroup G)) : G) ∈ Subgroup.normalizer P := by
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    constructor
    · intro hy
      have hyS : y ∈ (S : Subgroup G) := hPS hy
      have hmem : (⟨y, hyS⟩ : ↥(S : Subgroup G)) ∈ P.subgroupOf (S : Subgroup G) := hy
      have := (Subgroup.mem_normalizer_iff.mp hxnorm ⟨y, hyS⟩).mp hmem
      exact this
    · intro hy
      have hyS : ((x : ↥(S : Subgroup G)) : G) * y * ((x : ↥(S : Subgroup G)) : G)⁻¹
          ∈ (S : Subgroup G) := hPS hy
      have hyS' : y ∈ (S : Subgroup G) := by
        have hx1 : ((x : ↥(S : Subgroup G)) : G) ∈ (S : Subgroup G) := x.2
        have := (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
          ((S : Subgroup G).inv_mem hx1) hyS) hx1
        simpa [mul_assoc] using this
      have hmem : (⟨((x : ↥(S : Subgroup G)) : G) * y * ((x : ↥(S : Subgroup G)) : G)⁻¹, hyS⟩ :
          ↥(S : Subgroup G)) ∈ P.subgroupOf (S : Subgroup G) := hy
      exact (Subgroup.mem_normalizer_iff.mp hxnorm ⟨y, hyS'⟩).mpr hmem
  -- `P ⊔ ⟨x⟩` は `N_G(P)` 内の `p`-部分群
  have hxp : IsPGroup p ↥(Subgroup.zpowers ((x : ↥(S : Subgroup G)) : G)) := by
    refine S.isPGroup'.to_le ?_
    exact Subgroup.zpowers_le.mpr x.2
  have hsup_p : IsPGroup p ↥(P ⊔ Subgroup.zpowers ((x : ↥(S : Subgroup G)) : G)) :=
    hP.to_sup_of_normal_left' hxp (Subgroup.zpowers_le.mpr hxN)
  have hsup_le : P ⊔ Subgroup.zpowers ((x : ↥(S : Subgroup G)) : G) ≤ Subgroup.normalizer P :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxN)
  have heq := hmax _ hsup_p le_sup_left hsup_le
  -- すると `x ∈ P` で矛盾
  refine hxnot ?_
  have hxP : ((x : ↥(S : Subgroup G)) : G) ∈ P := by
    rw [← heq]
    exact (le_sup_right : Subgroup.zpowers _ ≤ _) (Subgroup.mem_zpowers _)
  exact hxP

end

end OddOrder.Isaacs.Ch07
