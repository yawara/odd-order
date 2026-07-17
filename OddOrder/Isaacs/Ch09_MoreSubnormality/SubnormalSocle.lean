/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.Layer
import OddOrder.Isaacs.Ch09_MoreSubnormality.NilpotentResidual

/-!
# Isaacs Ch. 9 — §9B: Lemma 9.17 / Corollary 9.18 (p. 281)

- **Lemma 9.17** (`isMinimalNormal_normalClosure_of_isSubnormal`): `S ◁◁ G`,
  `S` nonabelian simple ならば normal closure `S^G` は `G` の minimal normal subgroup.
  帰結 (`le_socle_of_isSubnormal_of_isSimpleGroup`): `S ≤ Soc(G)`.
- **Corollary 9.18** (`layer_le_normalizer_nilpotentResidual`): `S ◁◁ G` ならば
  `E(G) ≤ N_G(S^∞)`.

## 実装ノート

9.17 の証明: `S` の共役はすべて component (`IsComponent.conj`) で, 相異なる共役は
Thm 9.4 で可換 → 各共役は `W := S^G = ⨆ g, S^g` の中で normal. `↥W` は共役族を
semisimple family とする semisimple 群なので, `⊥ ≠ N ≤ W`, `N ◁ G` に対し
`N.subgroupOf W` の中の minimal normal は Lemma 9.5
(`mem_semisimpleFamily_of_isMinimalNormal`) で族のメンバー = ある共役 `S^g ≤ N`.
`N ◁ G` から全共役が `N` に入り `N = W`.

⚠ mmd 抽出 (L5081) は 9.17 の仮定を `S ◁ G` と誤抽出しているが, PDF 原文 (p. 281) は
`S ◁◁ G` (subnormal). 本ファイルは PDF に従う.
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 9B: Lemma 9.17 (p. 281) -/

/-- nonabelian simple 群は quasisimple (`Z(G) = ⊥` かつ `G' = ⊤`). -/
theorem isQuasisimple_of_isSimpleGroup_not_isMulCommutative
    (hs : IsSimpleGroup G) (hnc : ¬IsMulCommutative G) : IsQuasisimple G where
  isPerfect := by
    haveI := hs
    have hnorm : (commutator G).Normal := inferInstance
    refine ⟨hnorm.eq_bot_or_eq_top.resolve_left fun hbot => hnc ?_⟩
    have hcent : (⊤ : Subgroup G) ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    exact IsMulCommutative.of_comm fun x y =>
      (Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_top x)) y
        (Subgroup.mem_top y)).symm
  isSimpleGroup_quotient := by
    haveI := hs
    have hz : center G = ⊥ :=
      center_eq_bot_of_isSimpleGroup_not_isMulCommutative G hnc
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans
      QuotientGroup.quotientBot).isSimpleGroup

/-- 共役全体の join `⨆ g, S^g` は正規. -/
theorem normal_iSup_conj (S : Subgroup G) :
    (⨆ g : G, S.map (MulAut.conj g).toMonoidHom).Normal := by
  constructor
  intro x hx g
  refine Subgroup.iSup_induction _ (C := fun y => g * y * g⁻¹ ∈
    ⨆ h : G, S.map (MulAut.conj h).toMonoidHom) hx ?_ ?_ ?_
  · intro h y hy
    obtain ⟨s, hs, rfl⟩ := hy
    refine le_iSup (fun h : G => S.map (MulAut.conj h).toMonoidHom) (g * h) ⟨s, hs, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · simp
  · intro y z hy hz
    convert Subgroup.mul_mem _ hy hz using 1
    group

/-- normal closure `S^G` は共役全体の join. -/
theorem iSup_conj_eq_normalClosure (S : Subgroup G) :
    (⨆ g : G, S.map (MulAut.conj g).toMonoidHom) = normalClosure (S : Set G) := by
  apply le_antisymm
  · refine iSup_le fun g => ?_
    rintro x ⟨s, hs, rfl⟩
    simpa using normalClosure_normal.conj_mem _ (subset_normalClosure hs) g
  · haveI := normal_iSup_conj S
    refine normalClosure_le_normal fun x hx => ?_
    have h1 : S.map (MulAut.conj (1 : G)).toMonoidHom = S := by
      ext y
      simp [Subgroup.mem_map]
    exact le_iSup (fun g : G => S.map (MulAut.conj g).toMonoidHom) 1 (h1.symm ▸ hx)

/-- **Isaacs Lemma 9.17** (p. 281): `S ◁◁ G`, `S` nonabelian simple ならば normal
closure `S^G` は `G` の minimal normal subgroup. -/
theorem isMinimalNormal_normalClosure_of_isSubnormal [Finite G] {S : Subgroup G}
    (hS : S.IsSubnormal) (hsimp : IsSimpleGroup ↥S) (hnc : ¬IsMulCommutative ↥S) :
    Ch02.IsMinimalNormal (normalClosure (S : Set G)) := by
  haveI := hsimp
  set W := normalClosure (S : Set G) with hW
  have hScomp : IsComponent S :=
    ⟨hS, isQuasisimple_of_isSimpleGroup_not_isMulCommutative hsimp hnc⟩
  have hle : ∀ g : G, S.map (MulAut.conj g).toMonoidHom ≤ W := by
    intro g
    rw [hW, ← iSup_conj_eq_normalClosure]
    exact le_iSup (fun g : G => S.map (MulAut.conj g).toMonoidHom) g
  -- 各共役は `W` の中で normal (相異なる共役は Thm 9.4 で可換)
  have hWnorm : ∀ g : G, W ≤ Subgroup.normalizer
      ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    intro g
    rw [hW, ← iSup_conj_eq_normalClosure]
    refine iSup_le fun h => ?_
    rcases eq_or_ne (S.map (MulAut.conj h).toMonoidHom)
      (S.map (MulAut.conj g).toMonoidHom) with heq | hne
    · rw [heq]
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((hScomp.conj h).commutator_eq_bot_of_ne (hScomp.conj g) hne)).trans
        (Subgroup.centralizer_le_normalizer _)
  -- `↥W` 内の共役族は semisimple family
  have h𝒳 : ∀ T ∈ Set.range (fun g : G =>
      (S.map (MulAut.conj g).toMonoidHom).subgroupOf W),
      T.Normal ∧ IsSimpleGroup ↥T ∧ ¬IsMulCommutative ↥T := by
    rintro _ ⟨g, rfl⟩
    have e : ↥((S.map (MulAut.conj g).toMonoidHom).subgroupOf W) ≃* ↥S :=
      (Subgroup.subgroupOfEquivOfLe (hle g)).trans
        (Subgroup.equivMapOfInjective S (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).symm
    refine ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer (hle g)).mpr (hWnorm g),
      e.isSimpleGroup, fun hcomm => hnc ?_⟩
    haveI := hcomm
    exact isMulCommutative_of_surjective e.toMonoidHom e.surjective
  have hsup : sSup (Set.range fun g : G =>
      (S.map (MulAut.conj g).toMonoidHom).subgroupOf W) = ⊤ := by
    rw [sSup_range]
    apply Subgroup.map_injective W.subtype_injective
    have hcongr : (⨆ g : G,
        ((S.map (MulAut.conj g).toMonoidHom).subgroupOf W).map W.subtype)
        = ⨆ g : G, S.map (MulAut.conj g).toMonoidHom :=
      iSup_congr fun g => by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hle g)]
    rw [Subgroup.map_iSup, hcongr, iSup_conj_eq_normalClosure,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype, hW]
  refine ⟨normalClosure_normal, ?_, ?_⟩
  · -- `W ≠ ⊥` (`S` は simple ゆえ nontrivial)
    intro hbot
    have h1 : S ≤ W := le_normalClosure
    rw [hbot] at h1
    exact (Subgroup.isSimpleGroup_iff.mp hsimp).1 (le_bot_iff.mp h1)
  · -- minimality: `⊥ ≠ N ≤ W`, `N ◁ G` ⇒ `N = W`
    intro N hNnormal hNle
    rcases eq_or_ne N ⊥ with rfl | hNbot
    · exact Or.inl rfl
    refine Or.inr ?_
    haveI := hNnormal
    have hN'ne : N.subgroupOf W ≠ ⊥ := by
      intro hbot
      apply hNbot
      rw [eq_bot_iff]
      intro x hx
      have hmem : (⟨x, hNle hx⟩ : ↥W) ∈ N.subgroupOf W :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hbot, Subgroup.mem_bot] at hmem
      simpa [Subgroup.mem_bot] using congrArg Subtype.val hmem
    haveI : (N.subgroupOf W).Normal := hNnormal.comap W.subtype
    obtain ⟨M', hM'min, hM'le⟩ :=
      Ch02.exists_isMinimalNormal_le_of_normal (N.subgroupOf W) hN'ne
    obtain ⟨g, hg⟩ := mem_semisimpleFamily_of_isMinimalNormal h𝒳 hsup hM'min
    -- `S^g ≤ N`
    have hSgN : S.map (MulAut.conj g).toMonoidHom ≤ N := by
      intro x hx
      have hmem : (⟨x, hle g hx⟩ : ↥W) ∈ M' := hg ▸ Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_subgroupOf.mp (hM'le hmem)
    -- `N ◁ G` から全共役 `≤ N`
    have hall : ∀ h : G, S.map (MulAut.conj h).toMonoidHom ≤ N := by
      intro h
      rintro _ ⟨s, hs, rfl⟩
      have hgs : (MulAut.conj g) s ∈ N := hSgN ⟨s, hs, rfl⟩
      have hconj := hNnormal.conj_mem _ hgs (h * g⁻¹)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hconj ⊢
      convert hconj using 1
      group
    refine le_antisymm hNle ?_
    rw [hW, ← iSup_conj_eq_normalClosure]
    exact iSup_le hall

/-- **Isaacs Lemma 9.17 (帰結)**: `S ◁◁ G`, `S` nonabelian simple ⇒ `S ≤ Soc(G)`. -/
theorem le_socle_of_isSubnormal_of_isSimpleGroup [Finite G] {S : Subgroup G}
    (hS : S.IsSubnormal) (hsimp : IsSimpleGroup ↥S) (hnc : ¬IsMulCommutative ↥S) :
    S ≤ Ch02.socle G :=
  le_normalClosure.trans (Ch02.isMinimalNormal_le_socle
    (isMinimalNormal_normalClosure_of_isSubnormal hS hsimp hnc))

end

end OddOrder.Isaacs.Ch09
