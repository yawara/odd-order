/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.Group
import OddOrder.Isaacs.Ch09_MoreSubnormality.InnerAutomorphisms

/-!
# Isaacs §9B の演習 (書籍 pp. 284-285)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 9B
(Wielandt の automorphism tower 周辺)。

* **9B.1** `exists_normal_isComplement_of_isCompleteGroup` — `S ⊴ G` で `S` が
  **complete** (中心自明かつ自己同型がすべて内部) なら `G = S × T`。

書籍の statement はページ画像 `references/isaacs/pages/isaacs-p284-297.png` /
`isaacs-p285-298.png` で確定 (⚠ 9B.5 の `A, B ⊲⊲ G` は **subnormal**)。
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

variable {G : Type*} [Group G]

section /- 9B.1: complete な正規部分群は直積因子 (p. 284) -/

/-- **Complete group** (Isaacs p. 278): 中心が自明で, 自己同型がすべて内部。 -/
def IsCompleteGroup (G : Type*) [Group G] : Prop :=
  center G = ⊥ ∧ innAut G = ⊤

/-- `Z(↥N) = 1` なら `N ⊓ C_G(N) = 1` (`N ⊓ C_G(N)` の元は `↥N` の中心元)。 -/
theorem inf_centralizer_eq_bot_of_center_eq_bot {N : Subgroup G} (h : center ↥N = ⊥) :
    N ⊓ Subgroup.centralizer (N : Set G) = ⊥ := by
  refine le_bot_iff.mp fun x hx => ?_
  have hmem : (⟨x, hx.1⟩ : ↥N) ∈ center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 y y.2)
  rw [h, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

/-- **Isaacs Problem 9B.1** (書籍 p. 284) ⭐: `S ⊴ G` で `S` が complete なら
`G = S × T`, ここで `T = C_G(S)`。

**証明**: `T := C_G(S)` は `S ◁ G` ゆえ正規。`S ⊓ T` は `Z(S) = 1` なので自明。
`g ∈ G` に対し `g` が `S` に誘導する自己同型 (`MulAut.conjNormal g`) は内部, つまり
ある `s ∈ S` の共役に等しいので `s⁻¹ g ∈ C_G(S)`, したがって `g ∈ S T`。 -/
theorem exists_normal_isComplement_of_isCompleteGroup {S : Subgroup G} [S.Normal]
    (h : IsCompleteGroup ↥S) :
    ∃ T : Subgroup G, T.Normal ∧ S ⊓ T = ⊥ ∧ S ⊔ T = ⊤ := by
  refine ⟨Subgroup.centralizer (S : Set G), inferInstance,
    inf_centralizer_eq_bot_of_center_eq_bot h.1, ?_⟩
  refine top_le_iff.mp fun g _ => ?_
  -- `g` の誘導する自己同型は内部。
  have hmem : MulAut.conjNormal (H := S) g ∈ innAut ↥S := by
    rw [h.2]
    exact Subgroup.mem_top _
  obtain ⟨s, hs⟩ := hmem
  -- `s⁻¹ g` は `S` を中心化する。
  have hcent : (s : G)⁻¹ * g ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hval : (s : G) * x * (s : G)⁻¹ = g * x * g⁻¹ := by
      have hap := congrArg (fun t : ↥S => (t : G))
        (congrArg (fun f : MulAut ↥S => f ⟨x, hx⟩) hs)
      simpa [MulAut.conjNormal_apply] using hap
    have hyx : ((s : G)⁻¹ * g) * x * ((s : G)⁻¹ * g)⁻¹ = x := by
      rw [mul_inv_rev, inv_inv]
      calc (s : G)⁻¹ * g * x * (g⁻¹ * (s : G))
          = (s : G)⁻¹ * (g * x * g⁻¹) * (s : G) := by group
        _ = (s : G)⁻¹ * ((s : G) * x * (s : G)⁻¹) * (s : G) := by rw [hval]
        _ = x := by group
    calc x * ((s : G)⁻¹ * g)
        = (((s : G)⁻¹ * g) * x * ((s : G)⁻¹ * g)⁻¹) * ((s : G)⁻¹ * g) := by rw [hyx]
      _ = ((s : G)⁻¹ * g) * x := by group
  have hg : g = (s : G) * ((s : G)⁻¹ * g) := by group
  rw [hg]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left s.2) (Subgroup.mem_sup_right hcent)

end -- 9B.1

end OddOrder.Isaacs.Ch09
