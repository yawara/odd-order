/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import OddOrder.Isaacs.Ch09_MoreSubnormality.AutTower

/-!
# Isaacs §9B の演習 (書籍 pp. 284-285)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 9B
(Wielandt の automorphism tower 周辺)。

* **9B.1** `exists_normal_isComplement_of_isCompleteGroup` — `S ⊴ G` で `S` が
  **complete** (中心自明かつ自己同型がすべて内部) なら `G = S × T`。
* **9B.2** `isCompleteGroup_autTowerType_one_of_normal_range` — `Z(G) = 1` で `G` の像が
  `G₃ = Aut(Aut(G))` で正規なら `Aut(G)` は complete (= tower は `G₂` で止まる)。
  ⚠ 書籍の「`i ≤ 2`」はこの形に**再解釈**して形式化した (issue 1055 参照)。

書籍の statement はページ画像 `references/isaacs/pages/isaacs-p284-297.png` /
`isaacs-p285-298.png` で確定 (⚠ 9B.5 の `A, B ⊲⊲ G` は **subnormal**)。
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

open scoped commutatorElement

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

section /- 9B.2: G ⊴ G₃ なら Aut(G) は complete (p. 285) -/

/-- **`C_K(A) = 1` の押し上げ**: `A`, `B` がともに `K` で正規で `C_K(A) ⊓ B = 1`,
`C_K(B) = 1` なら `C_K(A) = 1`。

`C_K(A)` も `B` も `K`-正規なので `⁅C_K(A), B⁆ ≤ C_K(A) ⊓ B = 1`,
すなわち `C_K(A) ≤ C_K(B) = 1`。

9B.2 で `A` = `G` の像, `B` = `Aut(G)` の像, `K = Aut(Aut(G))` として使う。 -/
theorem centralizer_eq_bot_of_inf_eq_bot_of_centralizer_eq_bot {K : Type*} [Group K]
    {A B : Subgroup K} [A.Normal] [B.Normal]
    (hinf : Subgroup.centralizer (A : Set K) ⊓ B = ⊥)
    (hCB : Subgroup.centralizer (B : Set K) = ⊥) :
    Subgroup.centralizer (A : Set K) = ⊥ := by
  have hcomm : ⁅Subgroup.centralizer (A : Set K), B⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hinf]
    exact le_inf (Subgroup.commutator_le_left _ _) (Subgroup.commutator_le_right _ _)
  refine le_bot_iff.mp ?_
  rw [← hCB]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

/-- `A ⊴ K` への共役作用の核は `C_K(A)`。 -/
theorem ker_conjNormal {K : Type*} [Group K] (A : Subgroup K) [A.Normal] :
    (MulAut.conjNormal (H := A)).ker = Subgroup.centralizer (A : Set K) := by
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx a ha
    have h1 : ((MulAut.conjNormal (H := A) x ⟨a, ha⟩ : ↥A) : K)
        = ((1 : MulAut ↥A) ⟨a, ha⟩ : K) := by rw [hx]
    rw [MulAut.conjNormal_apply] at h1
    simp only [MulAut.one_apply] at h1
    calc a * x = (x * a * x⁻¹) * x := by rw [h1]
      _ = x * a := by group
  · intro hx
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    simp only [MulAut.one_apply]
    calc x * (a : K) * x⁻¹ = ((a : K) * x) * x⁻¹ := by rw [hx (a : K) a.2]
      _ = (a : K) := by group

/-- **忠実な共役作用は `K ↪ Aut(A)`**: `A ⊴ K` で `C_K(A) = 1` なら `|K| ≤ |Aut(A)|`。 -/
theorem card_le_card_mulAut_of_centralizer_eq_bot {K : Type*} [Group K] [Finite K]
    {A : Subgroup K} [A.Normal] (h : Subgroup.centralizer (A : Set K) = ⊥) :
    Nat.card K ≤ Nat.card (MulAut ↥A) := by
  refine Nat.card_le_card_of_injective (MulAut.conjNormal (H := A)) ?_
  rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal, h]

/-- 群同型に沿った `Aut` の個数の一致 (`MulAut` の functor 性は mathlib に無いので自前)。 -/
theorem card_mulAut_congr {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    Nat.card (MulAut H) = Nat.card (MulAut K) :=
  Nat.card_congr
    ⟨fun φ => e.symm.trans (φ.trans e), fun ψ => e.trans (ψ.trans e.symm),
      fun φ => MulEquiv.ext fun x => by simp, fun ψ => MulEquiv.ext fun x => by simp⟩

/-- **Isaacs Problem 9B.2** (書籍 p. 285) ⭐ — **再解釈版** (issue 1055 参照):
`Z(G) = 1` で `G` の像が `G₃ = Aut(Aut(G))` で正規なら, `Aut(G)` は **complete**。
すなわち automorphism tower は `G₂ = Aut(G)` で止まり, 相異なる群は高々 2 個。

⚠ 書籍の「`G ⊲ Gᵢ` なら `i ≤ 2`」は tower が定常な場合 (`G` complete 等) には
そのままでは成り立たず, 上の形が実際の内容 (9B.3 / 9B.4 の
"contains at most two different groups" と同じ言い回し)。

**証明**: `A` = `G` の `G₃` での像, `B` = `G₂` の `G₃` での像 (= `Inn(G₂)`) とする。
`C_{G₃}(B) = 1` と `C_{G₃}(A) ⊓ B = 1` (どちらも Lemma 9.11(c)) から
`C_{G₃}(A) = 1`。すると `G₃` は `A ≅ G` に忠実に共役作用するので
`|G₃| ≤ |Aut(G)| = |G₂| = |B|`, 有限性から `B = ⊤`。 -/
theorem isCompleteGroup_autTowerType_one_of_normal_range.{u} {G : Type u} [Group G] [Finite G]
    (hZ : Subgroup.center G = ⊥) (hnormal : ((autTowerEmb G 0 2).range).Normal) :
    IsCompleteGroup (autTowerType G 1) := by
  refine ⟨center_autTowerType_eq_bot hZ 1, ?_⟩
  haveI := hnormal
  -- `B` = `G₂` の像 = `Inn(G₂)`。
  have hCB : Subgroup.centralizer (((autTowerStep G 1).range : Subgroup (autTowerType G 2)) :
      Set (autTowerType G 2)) = ⊥ := by
    rw [range_autTowerStep]
    exact centralizer_innAut_eq_bot (center_autTowerType_eq_bot hZ 1)
  -- `A = (Inn G).map (autTowerStep G 1)`。
  have hA : (autTowerEmb G 0 2).range
      = (innAut G).map (autTowerStep G 1) := by
    rw [autTowerEmb_succ, MonoidHom.range_comp, autTowerEmb_succ, MonoidHom.range_comp,
      autTowerEmb_zero,
      MonoidHom.range_eq_top.mpr Function.surjective_id, ← MonoidHom.range_eq_map,
      range_autTowerStep]
    rfl
  -- `C_{G₃}(A) ⊓ B = 1` (Lemma 9.11(c) を `autTowerStep G 1` で押し出す)。
  have hinf : Subgroup.centralizer (((autTowerEmb G 0 2).range :
        Subgroup (autTowerType G 2)) : Set (autTowerType G 2))
      ⊓ (autTowerStep G 1).range = ⊥ := by
    have hbase : Subgroup.centralizer ((innAut G : Subgroup (MulAut G)) :
        Set (MulAut G)) ⊓ ⊤ = ⊥ := by
      rw [inf_top_eq]
      exact centralizer_innAut_eq_bot hZ
    have hpush := centralizer_map_inf_map_eq_bot (f := autTowerStep G 1)
      (autTowerStep_injective hZ 1) hbase
    rw [hA, MonoidHom.range_eq_map]
    exact hpush
  haveI hBnorm : ((autTowerStep G 1).range : Subgroup (autTowerType G 2)).Normal := by
    rw [range_autTowerStep]
    exact innAut.normal
  have hCA : Subgroup.centralizer (((autTowerEmb G 0 2).range :
      Subgroup (autTowerType G 2)) : Set (autTowerType G 2)) = ⊥ :=
    centralizer_eq_bot_of_inf_eq_bot_of_centralizer_eq_bot hinf hCB
  -- 数え上げ: `|G₃| ≤ |Aut(A)| = |Aut(G)| = |B|`。
  have hAG : G ≃* ↥((autTowerEmb G 0 2).range) :=
    MonoidHom.ofInjective (autTowerEmb_injective hZ 0 2)
  have hle : Nat.card (autTowerType G 2) ≤ Nat.card (autTowerType G 1) := by
    calc Nat.card (autTowerType G 2)
        ≤ Nat.card (MulAut ↥((autTowerEmb G 0 2).range)) :=
          card_le_card_mulAut_of_centralizer_eq_bot hCA
      _ = Nat.card (MulAut G) := (card_mulAut_congr hAG).symm
  have hBcard : Nat.card ↥((autTowerStep G 1).range) = Nat.card (autTowerType G 1) :=
    (Nat.card_congr (MonoidHom.ofInjective (autTowerStep_injective hZ 1)).toEquiv).symm
  have hBtop : ((autTowerStep G 1).range : Subgroup (autTowerType G 2)) = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) ?_)
    rw [hBcard]
    exact hle
  rwa [range_autTowerStep] at hBtop

end -- 9B.2

end OddOrder.Isaacs.Ch09
