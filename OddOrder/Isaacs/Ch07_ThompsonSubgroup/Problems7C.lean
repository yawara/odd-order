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

/-! ### 7C.1 の局所条件 -/

/-- **Isaacs 7C.1 の局所条件**: `P` の characteristic 部分群 `X` すべてについて
`N_G(X)/C_G(X)` が `p`-群。

既存の `HasThompsonLocalPComplements` と同じく **ambient `G` の任意の部分群 `P`** に対して
定義する (Sylow に限定しない) — そうしないと部分群・同型への輸送補題が書けないため。

⚠ 商群 `↥N_G(X) ⧸ C_G(X).subgroupOf N_G(X)` ではなく**元ごとの形**
(`g ∈ N_G(X)` なら `g ^ p ^ k ∈ C_G(X)`) を採る: `Normal` インスタンスの証明を避けられ,
部分群への遺伝が「`N_H(X) ≤ N_G(X)` に仮説を当てるだけ」で済む。有限群では両者は同値。 -/
def CharLocalPControl (p : ℕ) (P : Subgroup G) : Prop :=
  ∀ X : Subgroup ↥P, X.Characteristic →
    ∀ g ∈ Subgroup.normalizer ((X.map P.subtype : Subgroup G) : Set G),
      ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer ((X.map P.subtype : Subgroup G) : Set G)

/-- 局所条件は `C_G(X) ≤ N_G(X)` の元については自明 (`k = 0`)。 -/
theorem CharLocalPControl.trivial_on_centralizer {p : ℕ} {P : Subgroup G}
    {X : Subgroup ↥P} {g : G}
    (hg : g ∈ Subgroup.centralizer ((X.map P.subtype : Subgroup G) : Set G)) :
    ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer ((X.map P.subtype : Subgroup G) : Set G) :=
  ⟨0, by simpa using hg⟩

/-! ### characteristic 部分群の同型による輸送 -/

/-- **群同型に沿って characteristic 部分群は characteristic に移る**。

`ϕ : B ≃* B` に対し `ψ := e.trans (ϕ.trans e.symm) : A ≃* A` を取ると
`X.map ψ = X` (characteristic) で, これを `e` で押し出すと `(X.map e).map ϕ = X.map e`。 -/
theorem characteristic_map_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (X : Subgroup A) [hX : X.Characteristic] : (X.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro ϕ
  have hψ : X.map (e.trans (ϕ.trans e.symm)).toMonoidHom = X :=
    Subgroup.characteristic_iff_map_eq.mp hX (e.trans (ϕ.trans e.symm))
  have hcomp : (ϕ.toMonoidHom.comp e.toMonoidHom) =
      e.toMonoidHom.comp (e.trans (ϕ.trans e.symm)).toMonoidHom := by
    ext x
    simp
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hψ]

end

end OddOrder.Isaacs.Ch07
