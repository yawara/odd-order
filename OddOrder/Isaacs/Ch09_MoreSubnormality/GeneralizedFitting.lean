/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.Layer
import OddOrder.Isaacs.Ch01_Sylow.Basic

/-!
# Isaacs Ch. 9 — §9A: generalized Fitting subgroup F*(G) と Thm 9.8 / Cor 9.9 (p. 275)

- `genFitting G` = **generalized Fitting subgroup** `F*(G) = F(G) E(G)` (書籍 p. 275,
  `fitting G ⊔ layer G`). 両因子 normal ゆえ `F*(G) ◁ G`.
- **Theorem 9.8** (Bender, `centralizer_genFitting_le_genFitting`): 任意の有限群で
  `C_G(F*(G)) ≤ F*(G)`.
- **Corollary 9.9** (`fitting_le_genFitting`, `genFitting_eq_fitting_iff`):
  `F*(G) ⊇ F(G)`, かつ等号 ⟺ `F(G) ⊇ C_G(F(G))`.

## 実装ノート

Cor 9.9 の `←` (`F ⊇ C(F) ⇒ F* = F`) は Thm 9.7(c) のみに依る: `F(G)` solvable normal
なので `[E(G), F(G)] = 1`, ゆえ `E(G) ⊆ C_G(F(G)) ⊆ F(G)`, `F* = F(G) E(G) = F(G)`.
`→` は Thm 9.8 (`F* ⊇ C(F*)`) を要する.
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

open scoped IsMulCommutative commutatorElement

variable {G : Type*} [Group G]

section /- 9A: generalized Fitting subgroup (p. 275) -/

/-- **Generalized Fitting subgroup** `F*(G) = F(G) E(G)` (Isaacs p. 275). -/
def genFitting (G : Type*) [Group G] : Subgroup G :=
  Ch01.fitting G ⊔ layer G

/-- `F(G) ≤ F*(G)` (Cor 9.9 の自明な包含). -/
theorem fitting_le_genFitting : Ch01.fitting G ≤ genFitting G := le_sup_left

/-- `E(G) ≤ F*(G)`. -/
theorem layer_le_genFitting : layer G ≤ genFitting G := le_sup_right

/-- **F\*(G) は `G` で正規** (両因子 normal). -/
instance genFitting.normal [Finite G] : (genFitting G).Normal := by
  rw [genFitting]
  infer_instance

end

section /- 9A: Theorem 9.8 (Bender, p. 275) -/

/-- **Isaacs Theorem 9.8** (Bender): 任意の有限群で `C_G(F*(G)) ≤ F*(G)`.

書籍 p. 275 忠実: `C := C_G(F*)`, `Z := C ⊓ F*` とおき, `C ≤ F*` の否定から
`C.map π ≠ ⊥` (`π : G → G/Z`) を得て `G/Z` の minimal normal `M̄ ≤ C.map π` を取る.
`M := π⁻¹(M̄)` は `Z ≤ M ≤ C` で, `C` が `Z ⊆ F*` を中心化するので `Z ⊆ Z(M)`.
Lemma 9.6 で `M̄` は abelian か semisimple:

- **abelian**: `M → M̄` の核 `Z ⊆ Z(M)` で `M̄` nilpotent だから `M` nilpotent
  (`Subgroup.isNilpotent_of_ker_le_center`), よって `M ≤ F(G) ≤ F*` かつ `M ≤ C` で
  `M ≤ Z`, つまり `M̄ = ⊥` — minimal normal に矛盾.
- **semisimple**: `↥M̄` の minimal normal `T̄` は nonabelian simple (Lemma 9.5).
  `S := π⁻¹(T̄)` は `S ⊴ M ⊴ G` subnormal で `Z(S) = Z` (`T̄` centerless ゆえ),
  `S/Z(S) ≅ T̄` simple だから Lemma 9.1 で `S' = ⁅S,S⁆` は quasisimple — すなわち
  `G` の component で `S' ≤ E(G) ≤ F*`. 一方 `S' ≤ S ≤ C` なので `S' ≤ Z`, すると
  `T̄ = π(S)` が可換になり nonabelian simple と矛盾. -/
theorem centralizer_genFitting_le_genFitting [Finite G] :
    Subgroup.centralizer (genFitting G : Set G) ≤ genFitting G := by
  set F := genFitting G with hFdef
  set C := Subgroup.centralizer (F : Set G) with hCdef
  set Z := C ⊓ F with hZdef
  haveI hFnormal : F.Normal := genFitting.normal
  haveI hCnormal : C.Normal := Subgroup.normal_centralizer
  haveI hZnormal : Z.Normal := Subgroup.normal_inf_normal C F
  have hZC : Z ≤ C := hZdef.le.trans inf_le_left
  by_contra hnle
  -- `Z` の元は `C` の元と可換 (`Z ≤ F*` で `C = C_G(F*)`)
  have hcomm : ∀ z ∈ Z, ∀ c ∈ C, z * c = c * z := fun z hz c hc =>
    Subgroup.mem_centralizer_iff.mp hc z (Subgroup.mem_inf.mp hz).2
  set π := QuotientGroup.mk' Z with hπdef
  -- `C̄ ≠ ⊥` (さもなくば `C ≤ Z ≤ F*` で仮定に矛盾)
  have hCbar_ne : C.map π ≠ ⊥ := by
    intro h
    have hle := (Subgroup.map_eq_bot_iff _).mp h
    rw [QuotientGroup.ker_mk'] at hle
    exact hnle fun c hc => (Subgroup.mem_inf.mp (hle hc)).2
  haveI hCbar_normal : (C.map π).Normal :=
    Subgroup.Normal.map hCnormal π (QuotientGroup.mk'_surjective Z)
  obtain ⟨Mbar, hMbar_min, hMbar_leC⟩ :=
    Ch02.exists_isMinimalNormal_le_of_normal (C.map π) hCbar_ne
  haveI := hMbar_min.1
  set M := Mbar.comap π with hMdef
  haveI hMnormal : M.Normal := Subgroup.Normal.comap hMbar_min.1 π
  have hmemM : ∀ x : G, x ∈ M ↔ π x ∈ Mbar := fun _ => Subgroup.mem_comap
  have hMC : M ≤ C := by
    have h1 : M ≤ (C.map π).comap π := Subgroup.comap_mono hMbar_leC
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZC] at h1
  have hMmap : M.map π = Mbar :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) Mbar
  -- `Z ⊆ Z(M)` (`M ≤ C` が `Z ⊆ F*` を中心化)
  have hZcM : Z.subgroupOf M ≤ center ↥M := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (hcomm _ hz _ (hMC m.2)).symm
  rcases isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal hMbar_min with habel | hsemi
  · -- abelian 枝: `M` nilpotent → `M ≤ F(G) ≤ F*` → `M ≤ Z` → `M̄ = ⊥` 矛盾
    haveI := habel
    have hφker : (π.comp M.subtype).ker = Z.subgroupOf M := by
      ext x
      simp [hπdef, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
    have hφrange : (π.comp M.subtype).range = Mbar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact hMmap
    haveI hnilM : Group.IsNilpotent ↥M := by
      haveI : Group.IsNilpotent ↥((π.comp M.subtype).range) :=
        Group.nilpotent_of_mulEquiv (MulEquiv.subgroupCongr hφrange).symm
      exact Subgroup.isNilpotent_of_ker_le_center (π.comp M.subtype).rangeRestrict
        (by rw [MonoidHom.ker_rangeRestrict, hφker]; exact hZcM)
    have hMF : M ≤ Ch01.fitting G := Ch01.nilpotent_normal_le_fitting
    have hMZ : M ≤ Z := le_inf hMC (hMF.trans fitting_le_genFitting)
    exact hMbar_min.2.1 (by
      rw [← hMmap]
      exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact hMZ))
  · -- semisimple 枝: `↥M̄` の minimal normal `T̄` → `S := π⁻¹(T̄)` → `⁅S,S⁆` component
    haveI : Nontrivial ↥Mbar := (Subgroup.nontrivial_iff_ne_bot Mbar).mpr hMbar_min.2.1
    have htop_ne : (⊤ : Subgroup ↥Mbar) ≠ ⊥ := by
      intro h
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥Mbar)
      exact hx (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top x))
    obtain ⟨Tbar, hTbar_min, -⟩ :=
      Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup ↥Mbar) htop_ne
    obtain ⟨hTbar_simple, hTbar_ncomm⟩ := hsemi.isSimpleGroup_of_isMinimalNormal hTbar_min
    haveI := hTbar_simple
    -- `Ḡ = G/Z` へ押し出し
    set T₀ := Tbar.map Mbar.subtype with hT₀def
    have hT₀le : T₀ ≤ Mbar := Subgroup.map_subtype_le Tbar
    have hT₀recover : T₀.subgroupOf Mbar = Tbar :=
      Subgroup.comap_map_eq_self_of_injective Mbar.subtype_injective Tbar
    have hT₀normalM : (T₀.subgroupOf Mbar).Normal := hT₀recover ▸ hTbar_min.1
    have eT : ↥T₀ ≃* ↥Tbar :=
      (Subgroup.equivMapOfInjective Tbar Mbar.subtype Mbar.subtype_injective).symm
    -- `G` へ引き戻し
    set S := T₀.comap π with hSdef
    have hmemS : ∀ x : G, x ∈ S ↔ π x ∈ T₀ := fun _ => Subgroup.mem_comap
    have hSM : S ≤ M := Subgroup.comap_mono hT₀le
    have hSmap : S.map π = T₀ :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) T₀
    -- `S ⊴ M ⊴ G` subnormal
    have hMbar_norm : Mbar ≤ Subgroup.normalizer (T₀ : Set (G ⧸ Z)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀le).mp hT₀normalM
    have hSnormalM : (S.subgroupOf M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hSM]
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hiff := Subgroup.mem_normalizer_iff.mp (hMbar_norm ((hmemM m).mp hm)) (π x)
      constructor
      · intro hx
        refine (hmemS _).mpr ?_
        rw [map_mul, map_mul, map_inv]
        exact hiff.mp ((hmemS x).mp hx)
      · intro hx
        refine (hmemS x).mpr ?_
        have h2 := (hmemS _).mp hx
        rw [map_mul, map_mul, map_inv] at h2
        exact hiff.mpr h2
    have hSsub : S.IsSubnormal :=
      Subgroup.IsSubnormal.trans hSM hSnormalM.isSubnormal hMnormal.isSubnormal
    -- `Z(S) = Z` (⊆: `T̄` centerless; ⊇: `S ≤ M ≤ C` が `Z` を中心化)
    have hT₀centerless : center ↥T₀ = ⊥ := by
      have h1 : center ↥Tbar = ⊥ :=
        center_eq_bot_of_isSimpleGroup_not_isMulCommutative ↥Tbar hTbar_ncomm
      have h2 := map_center_mulEquiv eT
      rw [h1] at h2
      exact (Subgroup.map_eq_bot_iff_of_injective _ eT.injective).mp h2
    have hcentS_le : center ↥S ≤ Z.subgroupOf S := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hπx : π (x : G) ∈ T₀ := (hmemS _).mp x.2
      have hxc : (⟨π (x : G), hπx⟩ : ↥T₀) ∈ center ↥T₀ := by
        rw [Subgroup.mem_center_iff]
        intro t
        obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp
          (show (t : G ⧸ Z) ∈ S.map π by rw [hSmap]; exact t.2)
        have hcomm' : s * (x : G) = (x : G) * s :=
          congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨s, hs⟩)
        refine Subtype.ext ?_
        change (t : G ⧸ Z) * π (x : G) = π (x : G) * (t : G ⧸ Z)
        rw [← hst, ← map_mul π, ← map_mul π, hcomm']
      rw [hT₀centerless, Subgroup.mem_bot] at hxc
      have hπx1 : π (x : G) = 1 := congrArg Subtype.val hxc
      exact (QuotientGroup.eq_one_iff _).mp hπx1
    have hcentS_ge : Z.subgroupOf S ≤ center ↥S := by
      intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      rw [Subgroup.mem_center_iff]
      intro s
      exact Subtype.ext (hcomm _ hz _ (hMC (hSM s.2))).symm
    have hZcS : center ↥S = Z.subgroupOf S := le_antisymm hcentS_le hcentS_ge
    -- `S/Z(S) ≅ T̄` simple → Lemma 9.1 で `⁅S,S⁆` quasisimple
    have hψker : (π.comp S.subtype).ker = Z.subgroupOf S := by
      ext x
      simp [hπdef, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
    have hψrange : (π.comp S.subtype).range = T₀ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact hSmap
    have eS : (↥S ⧸ center ↥S) ≃* ↥Tbar :=
      (QuotientGroup.quotientMulEquivOfEq (hZcS.trans hψker.symm)).trans
        (((QuotientGroup.quotientKerEquivRange _).trans
          (MulEquiv.subgroupCongr hψrange)).trans eT)
    have hsimp : IsSimpleGroup (↥S ⧸ center ↥S) := eS.isSimpleGroup
    have hquasi : IsQuasisimple ↥(commutator ↥S) := isQuasisimple_commutator hsimp
    -- `⁅S,S⁆` は `G` の component
    have hS'map : (commutator ↥S).map S.subtype = ⁅S, S⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hS'quasi : IsQuasisimple ↥(⁅S, S⁆ : Subgroup G) :=
      hquasi.of_mulEquiv ((Subgroup.equivMapOfInjective _ S.subtype S.subtype_injective).trans
        (MulEquiv.subgroupCongr hS'map))
    have hS'le : (⁅S, S⁆ : Subgroup G) ≤ S := hS'map ▸ Subgroup.map_subtype_le _
    have hS'subOf : (⁅S, S⁆ : Subgroup G).subgroupOf S = commutator ↥S := by
      rw [← hS'map]
      exact Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
    have hS'normalS : ((⁅S, S⁆ : Subgroup G).subgroupOf S).Normal := by
      rw [hS'subOf, _root_.commutator_def]
      exact Subgroup.commutator_normal ⊤ ⊤
    have hS'comp : IsComponent (⁅S, S⁆ : Subgroup G) :=
      ⟨Subgroup.IsSubnormal.trans hS'le hS'normalS.isSubnormal hSsub, hS'quasi⟩
    -- `⁅S,S⁆ ≤ C ⊓ F* = Z` → `T̄ = π(S)` 可換 → nonabelian simple に矛盾
    have hS'Z : (⁅S, S⁆ : Subgroup G) ≤ Z :=
      le_inf (hS'le.trans (hSM.trans hMC)) (hS'comp.le_layer.trans layer_le_genFitting)
    have hcommT₀ : ⁅T₀, T₀⁆ = ⊥ := by
      have h1 : (⁅S, S⁆ : Subgroup G).map π = ⊥ :=
        (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact hS'Z)
      rwa [Subgroup.map_commutator, hSmap] at h1
    haveI habelT₀ : IsMulCommutative ↥T₀ := by
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommT₀
      exact IsMulCommutative.of_comm fun a b => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (hle a.2) (b : G ⧸ Z) b.2).symm
    exact hTbar_ncomm (isMulCommutative_of_surjective eT.toMonoidHom eT.surjective)

end

section /- 9A: Corollary 9.9 (`←` は Thm 9.7(c), `→` は Thm 9.8 依存) -/

/-- **Isaacs Cor 9.9 (`←`)**: `F(G) ⊇ C_G(F(G))` なら `F*(G) = F(G)`.
`F(G)` は solvable normal なので Thm 9.7(c) で `[E(G), F(G)] = 1`, よって
`E(G) ≤ C_G(F(G)) ≤ F(G)`, `F* = F(G) ⊔ E(G) = F(G)`. -/
theorem genFitting_eq_fitting_of_centralizer_fitting_le [Finite G]
    (h : Subgroup.centralizer (Ch01.fitting G : Set G) ≤ Ch01.fitting G) :
    genFitting G = Ch01.fitting G := by
  refine le_antisymm ?_ fitting_le_genFitting
  rw [genFitting, sup_le_iff]
  refine ⟨le_rfl, ?_⟩
  -- E(G) ≤ C_G(F(G)) ≤ F(G)
  haveI : IsSolvable ↥(Ch01.fitting G) := by
    haveI := Ch01.fitting.isNilpotent (G := G)
    exact IsNilpotent.to_isSolvable
  have hcomm : ⁅layer G, Ch01.fitting G⁆ = ⊥ :=
    commutator_layer_eq_bot_of_normal_isSolvable inferInstance
  have hle : layer G ≤ Subgroup.centralizer (Ch01.fitting G : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  exact hle.trans h

/-- **Isaacs Cor 9.9 (`→`)**: `F*(G) = F(G)` なら `F(G) ⊇ C_G(F(G))`
(Thm 9.8 で `F*` は自身の中心化群を含む). -/
theorem centralizer_fitting_le_fitting_of_genFitting_eq [Finite G]
    (h : genFitting G = Ch01.fitting G) :
    Subgroup.centralizer (Ch01.fitting G : Set G) ≤ Ch01.fitting G := by
  rw [← h]
  exact centralizer_genFitting_le_genFitting

/-- **Isaacs Cor 9.9 (等号条件)**: `F*(G) = F(G) ⟺ F(G) ⊇ C_G(F(G))`. -/
theorem genFitting_eq_fitting_iff [Finite G] :
    genFitting G = Ch01.fitting G
      ↔ Subgroup.centralizer (Ch01.fitting G : Set G) ≤ Ch01.fitting G :=
  ⟨centralizer_fitting_le_fitting_of_genFitting_eq,
    genFitting_eq_fitting_of_centralizer_fitting_le⟩

end

end OddOrder.Isaacs.Ch09
