/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.Quasisimple
import OddOrder.Isaacs.Ch02_Subnormality.Basic
import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Isaacs Ch. 9 — §9A: semisimple groups と Lemma 9.5 (pp. 274-275)

- `IsSemisimpleGroup`: **semisimple** = nonabelian simple normal subgroups の積 (書籍 p. 274).
- **Lemma 9.5** (分割して形式化):
  - `isMinimalNormal_of_mem_semisimpleFamily`: 族の各メンバーは minimal normal.
  - `iSupIndep_of_semisimpleFamily` + `piEquivOfSemisimpleFamily`: 積は直積
    (mathlib `MonoidHom.noncommPiCoprod` による `(Π S, ↥S) ≃* G`).
  - `center_eq_bot_of_semisimpleFamily`: semisimple 群は centerless.
  - `mem_semisimpleFamily_of_isMinimalNormal`: 族は `G` の全 minimal normal subgroup と一致.
- 下流 (Thm 9.7/9.8) 向け payload:
  - `IsSemisimpleGroup.isSimpleGroup_of_isMinimalNormal`: semisimple 群の minimal normal は
    nonabelian simple.
  - `IsSemisimpleGroup.eq_bot_of_normal_of_isSolvable`: semisimple 群の solvable normal
    subgroup は自明 (Thm 9.7(c) の核心ステップ).

`center_eq_bot` 系は直積構造 (`noncommPiCoprod` の単射性・全射性) を経由するため
`[Finite G]` を仮定する (Isaacs は有限群の本; 族の有限性が本質).
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

section /- 9A: semisimple groups (pp. 274-275) -/

variable {G : Type*} [Group G]

/-- nonabelian simple 群の中心は自明. -/
theorem center_eq_bot_of_isSimpleGroup_not_isMulCommutative (G : Type*) [Group G]
    [IsSimpleGroup G] (h : ¬IsMulCommutative G) : center G = ⊥ := by
  rcases (Subgroup.instNormalCenter (G := G)).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact absurd (IsMulCommutative.of_comm fun a b =>
      Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top b) a) h

/-- 相異なる minimal normal subgroups は交わらない. -/
theorem disjoint_of_isMinimalNormal_of_ne {M N : Subgroup G}
    (hM : Ch02.IsMinimalNormal M) (hN : Ch02.IsMinimalNormal N) (hne : M ≠ N) :
    Disjoint M N := by
  haveI := hM.1
  haveI := hN.1
  rw [disjoint_iff]
  rcases hM.2.2 (M ⊓ N) (Subgroup.normal_inf_normal M N) inf_le_left with h | h
  · exact h
  · -- M ⊓ N = M ⇒ M ≤ N ⇒ (minimality of N) M = N, 矛盾
    have hMN : M ≤ N := h ▸ inf_le_right
    rcases hN.2.2 M hM.1 hMN with hbot | heq
    · exact absurd hbot hM.2.1
    · exact absurd heq hne

/-- **Semisimple group** (Isaacs p. 274): nonabelian simple normal subgroups の
族の積 (`sSup`) が全体. -/
def IsSemisimpleGroup (G : Type*) [Group G] : Prop :=
  ∃ 𝒳 : Set (Subgroup G),
    (∀ S ∈ 𝒳, S.Normal ∧ IsSimpleGroup ↥S ∧ ¬IsMulCommutative ↥S) ∧ sSup 𝒳 = ⊤

variable {𝒳 : Set (Subgroup G)}

/-- **Isaacs Lemma 9.5 (前半)**: nonabelian simple normal subgroup は minimal normal.
(`G`-normal な部分群は `↥S` でも normal で, simple 性から `⊥` か `S`.) -/
theorem isMinimalNormal_of_mem_semisimpleFamily
    (h𝒳 : ∀ S ∈ 𝒳, S.Normal ∧ IsSimpleGroup ↥S ∧ ¬IsMulCommutative ↥S)
    {S : Subgroup G} (hS : S ∈ 𝒳) : Ch02.IsMinimalNormal S := by
  obtain ⟨hnormal, hsimple, -⟩ := h𝒳 S hS
  obtain ⟨hne_bot, hmin⟩ := Subgroup.isSimpleGroup_iff.mp hsimple
  exact ⟨hnormal, hne_bot, fun K hK hKle => hmin K hKle (hK.subgroupOf S)⟩

/-- 族の相異なるメンバーの元は可換 (Lemma 9.5 第 1 段落). -/
theorem commute_of_mem_semisimpleFamily_of_ne
    (h𝒳 : ∀ S ∈ 𝒳, S.Normal ∧ IsSimpleGroup ↥S ∧ ¬IsMulCommutative ↥S)
    {S T : Subgroup G} (hS : S ∈ 𝒳) (hT : T ∈ 𝒳) (hne : S ≠ T)
    {x y : G} (hx : x ∈ S) (hy : y ∈ T) : Commute x y :=
  Subgroup.commute_of_normal_of_disjoint S T (h𝒳 S hS).1 (h𝒳 T hT).1
    (disjoint_of_isMinimalNormal_of_ne (isMinimalNormal_of_mem_semisimpleFamily h𝒳 hS)
      (isMinimalNormal_of_mem_semisimpleFamily h𝒳 hT) hne) x y hx hy

/-- **Isaacs Lemma 9.5 (直積性の核)**: 族は lattice 的に独立
(各メンバーと残り全体の join は交わらない). -/
theorem iSupIndep_of_semisimpleFamily
    (h𝒳 : ∀ S ∈ 𝒳, S.Normal ∧ IsSimpleGroup ↥S ∧ ¬IsMulCommutative ↥S) :
    iSupIndep fun S : ↥𝒳 => (S : Subgroup G) := by
  intro S
  have hle : (⨆ (T : ↥𝒳) (_ : T ≠ S), (T : Subgroup G))
      ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    refine iSup_le fun T => iSup_le fun hne => fun y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (commute_of_mem_semisimpleFamily_of_ne h𝒳 T.2 S.2
      (fun heq => hne (Subtype.ext heq)) hy hx).symm.eq
  rw [disjoint_iff_inf_le]
  intro x hx
  have hxc : (⟨x, hx.1⟩ : ↥(S : Subgroup G)) ∈ center ↥(S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hle hx.2) w w.2)
  haveI := (h𝒳 S S.2).2.1
  rw [center_eq_bot_of_isSimpleGroup_not_isMulCommutative _ (h𝒳 S S.2).2.2,
    Subgroup.mem_bot] at hxc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)

/-- **Isaacs Lemma 9.5 (直積性)**: 族の直積は `G` と同型
(`noncommPiCoprod` が単射 (独立性) かつ全射 (`sSup 𝒳 = ⊤`)). -/
noncomputable def piEquivOfSemisimpleFamily [Fintype ↥𝒳]
    (h𝒳 : ∀ S ∈ 𝒳, S.Normal ∧ IsSimpleGroup ↥S ∧ ¬IsMulCommutative ↥S)
    (hsup : sSup 𝒳 = ⊤) :
    ((S : ↥𝒳) → ↥(S : Subgroup G)) ≃* G := by
  have hcomm : Pairwise fun S T : ↥𝒳 =>
      ∀ (x : ↥(S : Subgroup G)) (y : ↥(T : Subgroup G)),
        Commute ((S : Subgroup G).subtype x) ((T : Subgroup G).subtype y) :=
    fun S T hne x y => commute_of_mem_semisimpleFamily_of_ne h𝒳 S.2 T.2
      (fun heq => hne (Subtype.ext heq)) x.2 y.2
  have hinj : Function.Injective
      (MonoidHom.noncommPiCoprod (fun S : ↥𝒳 => (S : Subgroup G).subtype) hcomm) :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep
      (fun S : ↥𝒳 => (S : Subgroup G).subtype)
      (by simpa only [Subgroup.range_subtype] using iSupIndep_of_semisimpleFamily h𝒳)
      (fun S => (S : Subgroup G).subtype_injective)
  have hsurj : Function.Surjective
      (MonoidHom.noncommPiCoprod (fun S : ↥𝒳 => (S : Subgroup G).subtype) hcomm) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.noncommPiCoprod_range]
    simp only [Subgroup.range_subtype]
    rw [← sSup_eq_iSup', hsup]
  exact MulEquiv.ofBijective _ ⟨hinj, hsurj⟩

/-- 有限直積の中心: 各因子の中心が自明なら全体の中心も自明. -/
theorem center_pi_eq_bot {ι : Type*} {H : ι → Type*} [∀ i, Group (H i)]
    (h : ∀ i, center (H i) = ⊥) : center ((i : ι) → H i) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro f hf
  rw [Subgroup.mem_bot]
  funext i
  have hfi : f i ∈ center (H i) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hcomm := congrFun (Subgroup.mem_center_iff.mp hf (Pi.mulSingle i g)) i
    simpa using hcomm
  rw [h i, Subgroup.mem_bot] at hfi
  simp [hfi]

/-- **Isaacs Lemma 9.5 (centerless)**: semisimple 族をもつ有限群の中心は自明. -/
theorem center_eq_bot_of_semisimpleFamily [Finite G]
    (h𝒳 : ∀ S ∈ 𝒳, S.Normal ∧ IsSimpleGroup ↥S ∧ ¬IsMulCommutative ↥S)
    (hsup : sSup 𝒳 = ⊤) : center G = ⊥ := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  haveI : Fintype ↥𝒳 := Fintype.ofFinite _
  have e := piEquivOfSemisimpleFamily h𝒳 hsup
  have hpi : center ((S : ↥𝒳) → ↥(S : Subgroup G)) = ⊥ :=
    center_pi_eq_bot fun S => by
      haveI := (h𝒳 S S.2).2.1
      exact center_eq_bot_of_isSimpleGroup_not_isMulCommutative _ (h𝒳 S S.2).2.2
  have hmap := map_center_mulEquiv e
  rw [hpi, Subgroup.map_bot] at hmap
  exact hmap.symm

/-- **Isaacs Lemma 9.5 (後半)**: 族は `G` の minimal normal subgroup を全て含む. -/
theorem mem_semisimpleFamily_of_isMinimalNormal [Finite G]
    (h𝒳 : ∀ S ∈ 𝒳, S.Normal ∧ IsSimpleGroup ↥S ∧ ¬IsMulCommutative ↥S)
    (hsup : sSup 𝒳 = ⊤) {N : Subgroup G} (hN : Ch02.IsMinimalNormal N) : N ∈ 𝒳 := by
  by_contra hnotin
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer (N : Set G) := by
    rw [← hsup]
    refine sSup_le fun S hS => fun y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.commute_of_normal_of_disjoint S N (h𝒳 S hS).1 hN.1
      (disjoint_of_isMinimalNormal_of_ne (isMinimalNormal_of_mem_semisimpleFamily h𝒳 hS)
        hN (fun heq => hnotin (heq ▸ hS))) y x hy hx).symm.eq
  have hNZ : N ≤ center G := fun x hx =>
    Subgroup.mem_center_iff.mpr fun g =>
      (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top g)) x hx).symm
  rw [center_eq_bot_of_semisimpleFamily h𝒳 hsup] at hNZ
  exact hN.2.1 (le_bot_iff.mp hNZ)

/-- semisimple 群の中心は自明. -/
theorem IsSemisimpleGroup.center_eq_bot [Finite G] (h : IsSemisimpleGroup G) :
    center G = ⊥ := by
  obtain ⟨𝒳, h𝒳, hsup⟩ := h
  exact center_eq_bot_of_semisimpleFamily h𝒳 hsup

/-- **Isaacs Lemma 9.5 (帰結)**: semisimple 群の minimal normal subgroup は
nonabelian simple. -/
theorem IsSemisimpleGroup.isSimpleGroup_of_isMinimalNormal [Finite G]
    (h : IsSemisimpleGroup G) {N : Subgroup G} (hN : Ch02.IsMinimalNormal N) :
    IsSimpleGroup ↥N ∧ ¬IsMulCommutative ↥N := by
  obtain ⟨𝒳, h𝒳, hsup⟩ := h
  have hmem := mem_semisimpleFamily_of_isMinimalNormal h𝒳 hsup hN
  exact ⟨(h𝒳 N hmem).2.1, (h𝒳 N hmem).2.2⟩

/-- **Thm 9.7(c) 向け payload**: semisimple 群の solvable normal subgroup は自明.
(非自明なら中の minimal normal が nonabelian simple かつ solvable となり矛盾.) -/
theorem IsSemisimpleGroup.eq_bot_of_normal_of_isSolvable [Finite G]
    (h : IsSemisimpleGroup G) {W : Subgroup G} (hW : W.Normal)
    (hsolv : IsSolvable ↥W) : W = ⊥ := by
  by_contra hne
  haveI := hW
  obtain ⟨M, hMmin, hMle⟩ := Ch02.exists_isMinimalNormal_le_of_normal W hne
  obtain ⟨hsimp, hncomm⟩ := h.isSimpleGroup_of_isMinimalNormal hMmin
  -- `M ≤ W` solvable ⇒ `↥M` solvable
  haveI : IsSolvable ↥M :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hMle)
  haveI := hsimp
  haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMmin.2.1
  -- solvable ⇒ commutator proper ⇒ (simple) commutator = ⊥ ⇒ abelian, 矛盾
  have hlt : commutator ↥M < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial ↥M
  have hnorm : (commutator ↥M).Normal := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_normal ⊤ ⊤
  rcases hnorm.eq_bot_or_eq_top with hb | ht
  · exact hncomm (isMulCommutative_of_commutator_eq_bot hb)
  · exact hlt.ne ht

end

end OddOrder.Isaacs.Ch09
