/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.Layer
import OddOrder.Isaacs.Ch09_MoreSubnormality.NilpotentResidual
import OddOrder.GroupTheory.PrimeComplementResidual

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

9.18 の証明 (書籍 p. 281 の道筋, ただし型の取り方のみ変更): `Z := Z(E(G))` で
`Ḡ = G/Z` を作り, `Ē ≤ Soc(Ḡ)` を経由して Thm 2.6 で `Ē` が subnormal な `S̄` を
正規化 → 引き戻して `E(G) ≤ N_G(SZ)` → Lemma 9.15 で `(SZ)^∞ = S^∞`.

⚠ 書籍は `Ē` が semisimple (Thm 9.7(b)) だと言ってから「その simple factor が
Lemma 9.17 で `Soc(Ḡ)` に入る」と進むが, 本ファイルは **`IsSemisimpleGroup` 述語と
`↥E ⧸ Z(↥E)` の型を経由しない**: `Z` を ambient に `layerCenter G = E ⊓ C_G(E)` と
取り (`layerCenter_subgroupOf_component` が component 上で `Z(↥H)` に一致することを
保証), 各 component `H` の像 `H.map (mk' Z)` に Lemma 9.17 を直接当てる
(`map_layer_le_socle`). `E = sSup components` ゆえ像の sSup が `Soc(Ḡ)` に入り,
書籍の「simple factor ごと」の議論と同じ内容を型を跨がずに得る.

⚠ mmd 抽出 (L5081) は 9.17 の仮定を `S ◁ G` と誤抽出しているが, PDF 原文 (p. 281) は
`S ◁◁ G` (subnormal). 本ファイルは PDF に従う (9.18 も同様).
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
    rw [hW, Subgroup.normalClosure_eq_iSup_map_conj]
    exact le_iSup (fun g : G => S.map (MulAut.conj g).toMonoidHom) g
  -- 各共役は `W` の中で normal (相異なる共役は Thm 9.4 で可換)
  have hWnorm : ∀ g : G, W ≤ Subgroup.normalizer
      ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    intro g
    rw [hW, Subgroup.normalClosure_eq_iSup_map_conj]
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
    rw [Subgroup.map_iSup, hcongr, ← Subgroup.normalClosure_eq_iSup_map_conj,
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
    rw [hW, Subgroup.normalClosure_eq_iSup_map_conj]
    exact iSup_le hall

/-- **Isaacs Lemma 9.17 (帰結)**: `S ◁◁ G`, `S` nonabelian simple ⇒ `S ≤ Soc(G)`. -/
theorem le_socle_of_isSubnormal_of_isSimpleGroup [Finite G] {S : Subgroup G}
    (hS : S.IsSubnormal) (hsimp : IsSimpleGroup ↥S) (hnc : ¬IsMulCommutative ↥S) :
    S ≤ Ch02.socle G :=
  le_normalClosure.trans (Ch02.isMinimalNormal_le_socle
    (isMinimalNormal_normalClosure_of_isSubnormal hS hsimp hnc))

end

section /- 9B: Corollary 9.18 (p. 281) -/

variable (G) in
/-- ambient 版の `Z(E(G))`: `E(G) ⊓ C_G(E(G))` (= `Z(↥E)` の `G` 内での像).

Cor 9.18 の `Ḡ = G/Z(E)` を `↥E ⧸ Z(↥E)` の型を経由せずに作るための ambient 表示.
`layerCenter_subgroupOf_component` が「component `H` に制限すると `Z(↥H)`」を保証する. -/
def layerCenter : Subgroup G := layer G ⊓ Subgroup.centralizer (layer G : Set G)

theorem mem_layerCenter_iff {x : G} :
    x ∈ layerCenter G ↔ x ∈ layer G ∧ x ∈ Subgroup.centralizer (layer G : Set G) :=
  Iff.rfl

theorem layerCenter_le_layer : layerCenter G ≤ layer G := inf_le_left

instance layerCenter.normal : (layerCenter G).Normal := by
  unfold layerCenter
  infer_instance

instance layerCenter.isMulCommutative : IsMulCommutative ↥(layerCenter G) :=
  IsMulCommutative.of_comm fun x y => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp (mem_layerCenter_iff.mp y.2).2 (x : G)
      (layerCenter_le_layer x.2))

open scoped IsMulCommutative in
instance layerCenter.isNilpotent : Group.IsNilpotent ↥(layerCenter G) := inferInstance

/-- **`Z(↥H) = H ⊓ Z(E)`** for a component `H` (Thm 9.7 の `Z(H) = H ∩ Z(E)` の ambient 形).

`⊇` は `Z(E) ≤ C_G(E) ≤ C_G(H)`, `⊆` は `mem_centralizer_layer_of_component`
(component を中心化する component の元は layer 全体を中心化する). -/
theorem layerCenter_subgroupOf_component [Finite G] {H : Subgroup G} (hH : IsComponent H) :
    (layerCenter G).subgroupOf H = center ↥H := by
  ext a
  rw [Subgroup.mem_subgroupOf, mem_layerCenter_iff, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, hc⟩ b
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc (b : G) (hH.le_layer b.2))
  · intro ha
    refine ⟨hH.le_layer a.2, mem_centralizer_layer_of_component hH a.2 ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    simpa using congrArg Subtype.val (ha ⟨h, hh⟩)

/-- component `H` の `Ḡ = G/Z(E)` での像は `↥H ⧸ Z(↥H)` と同型
(第一同型定理 + `layerCenter_subgroupOf_component`). -/
noncomputable def componentMapQuotientEquiv [Finite G] {H : Subgroup G} (hH : IsComponent H) :
    ↥(H.map (QuotientGroup.mk' (layerCenter G))) ≃* (↥H ⧸ center ↥H) := by
  set π := QuotientGroup.mk' (layerCenter G)
  have hker : (π.comp H.subtype).ker = center ↥H := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact layerCenter_subgroupOf_component hH
  have hrange : (π.comp H.subtype).range = H.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ((MulEquiv.subgroupCongr hrange).symm.trans
    (QuotientGroup.quotientKerEquivRange (π.comp H.subtype)).symm).trans
    (QuotientGroup.quotientMulEquivOfEq hker)

/-- component の像 `H̄ ≤ Ḡ` は simple (`H̄ ≅ ↥H ⧸ Z(↥H)`, `H` quasisimple). -/
theorem isSimpleGroup_map_component [Finite G] {H : Subgroup G} (hH : IsComponent H) :
    IsSimpleGroup ↥(H.map (QuotientGroup.mk' (layerCenter G))) := by
  haveI := hH.isQuasisimple.isSimpleGroup_quotient
  exact (componentMapQuotientEquiv hH).isSimpleGroup

/-- component の像 `H̄ ≤ Ḡ` は非可換 (Lemma 9.1). -/
theorem not_isMulCommutative_map_component [Finite G] {H : Subgroup G} (hH : IsComponent H) :
    ¬IsMulCommutative ↥(H.map (QuotientGroup.mk' (layerCenter G))) := by
  intro hcomm
  haveI := hcomm
  exact not_isMulCommutative_of_isSimpleGroup_quotient_center
    hH.isQuasisimple.isSimpleGroup_quotient
    (isMulCommutative_of_surjective (componentMapQuotientEquiv hH).toMonoidHom
      (componentMapQuotientEquiv hH).surjective)

/-- **Cor 9.18 の核**: `Ē = E(G) Z(E)/Z(E) ≤ Soc(Ḡ)`.

各 component の像は subnormal かつ nonabelian simple なので Lemma 9.17 の帰結
(`le_socle_of_isSubnormal_of_isSimpleGroup`) が適用でき, `E(G)` は component の
sSup ゆえ像全体が `Soc(Ḡ)` に入る. -/
theorem map_layer_le_socle [Finite G] :
    (layer G).map (QuotientGroup.mk' (layerCenter G))
      ≤ Ch02.socle (G ⧸ layerCenter G) := by
  rw [show layer G = sSup {H : Subgroup G | IsComponent H} from rfl, sSup_eq_iSup',
    Subgroup.map_iSup]
  refine iSup_le fun H => le_socle_of_isSubnormal_of_isSimpleGroup
    (H.2.isSubnormal.map (QuotientGroup.mk'_surjective _))
    (isSimpleGroup_map_component H.2) (not_isMulCommutative_map_component H.2)

/-- **Cor 9.18 の主要ステップ**: `S ◁◁ G` ならば `E(G) ≤ N_G(S Z(E))`.

`Z := Z(E)` は `ker (mk' Z)` なので `(S ⊔ Z)`-bar `= S`-bar は `Ḡ` で subnormal.
`map_layer_le_socle` + Thm 2.6 (`Ch02.isMinimalNormal_le_normalizer_of_isSubnormal`)
で `Ē ≤ Soc(Ḡ) ≤ N_Ḡ(S̄)`, これを `Z ≤ S ⊔ Z` (`comap_map_eq_self`) で引き戻す. -/
theorem layer_le_normalizer_sup_layerCenter [Finite G] {S : Subgroup G}
    (hS : S.IsSubnormal) :
    layer G ≤ Subgroup.normalizer ((S ⊔ layerCenter G : Subgroup G) : Set G) := by
  set Z := layerCenter G with hZ
  set π := QuotientGroup.mk' Z with hπ
  set T := S ⊔ Z with hT
  -- `Z = ker π` ゆえ `T̄ = S̄` (Z の像は自明)
  have hZmap : Z.map π = ⊥ :=
    (Subgroup.map_eq_bot_iff Z).mpr (by rw [hπ, QuotientGroup.ker_mk'])
  have hmapT : T.map π = S.map π := by rw [hT, Subgroup.map_sup, hZmap, sup_bot_eq]
  have hsn : (S.map π).IsSubnormal := hS.map (QuotientGroup.mk'_surjective _)
  -- `Ē ≤ Soc(Ḡ) ≤ N_Ḡ(S̄)` (Thm 2.6)
  have hEnorm : (layer G).map π
      ≤ Subgroup.normalizer ((S.map π : Subgroup (G ⧸ Z)) : Set (G ⧸ Z)) :=
    map_layer_le_socle.trans
      (iSup_le fun M => Ch02.isMinimalNormal_le_normalizer_of_isSubnormal hsn M.2)
  -- `Z ≤ T` ゆえ `T = comap π (T̄)`: 所属を `Ḡ` 側の所属に翻訳できる
  have hTcomap : Subgroup.comap π (T.map π) = T :=
    Subgroup.comap_map_eq_self (by rw [hπ, QuotientGroup.ker_mk', hT]; exact le_sup_right)
  have hmem : ∀ y : G, y ∈ T ↔ π y ∈ S.map π := fun y => by
    rw [← hmapT, ← Subgroup.mem_comap, hTcomap]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hπx := Subgroup.mem_normalizer_iff.mp (hEnorm ⟨x, hx, rfl⟩) (π h)
  rw [hmem h, hmem (x * h * x⁻¹), map_mul, map_mul, map_inv]
  exact hπx

/-- **Isaacs Corollary 9.18** (p. 281): `S ◁◁ G` (有限群) ならば `E(G) ≤ N_G(S^∞)`.

Cor 9.16 (`fitting_le_normalizer_nilpotentResidual`) と合わせて
`F*(G) = F(G) E(G) ≤ N_G(S^∞)` を与える (Thm 9.10 / 9.13 への布石).

証明: `layer_le_normalizer_sup_layerCenter` で `E(G) ≤ N_G(S Z(E))`, 正規化は
nilpotent residual に伝播し (`normalizer_le_normalizer_nilpotentResidual`),
Lemma 9.15 (相対形) で `(S Z(E))^∞ = S^∞` (`Z(E) ◁ G` は可換ゆえ nilpotent). -/
theorem layer_le_normalizer_nilpotentResidual [Finite G] {S : Subgroup G}
    (hS : S.IsSubnormal) :
    layer G ≤ Subgroup.normalizer (nilpotentResidual S : Set G) := by
  have h915 : nilpotentResidual (S ⊔ layerCenter G) = nilpotentResidual S :=
    nilpotentResidual_sup_eq_of_isSubnormal hS
  calc layer G ≤ Subgroup.normalizer ((S ⊔ layerCenter G : Subgroup G) : Set G) :=
        layer_le_normalizer_sup_layerCenter hS
    _ ≤ Subgroup.normalizer (nilpotentResidual (S ⊔ layerCenter G) : Set G) :=
        normalizer_le_normalizer_nilpotentResidual _
    _ = Subgroup.normalizer (nilpotentResidual S : Set G) := by rw [h915]

end

end OddOrder.Isaacs.Ch09
