/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_SingleFactorCentralizer

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S11_NineElevenCoherence` (2000-line limit, issue 0103 第 2
パス).
-/
namespace OddOrder.Peterfalvi.S11
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)
open scoped Pointwise

variable {G : Type*} [Group G]

section NineElevenTwoInertia
open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

variable [Finite G] {M : Subgroup G}


/-! ### The generic single-factor centralizer `C_U(H_j)` and its index `a`

Mirrors the a-owned `cuSub`/`card_U_eq_a_mul_card_cuSub` chain for the distinguished generator
`S₀`, but for an *arbitrary* Clifford summand `H_j = caseA.Hpart j`.  The crux is orbit symmetry:
`a` is pinned to `|Ū₁| = |range(aInvariantRestrictAut S₀)|`, and since `H_j = φ(orbitRep j) • S₀`
is the automorphic image of `S₀`, conjugation by `w = φ(orbitRep j)` (well-defined on the acting
`U`-group because `U ◁ U W₁` is the Frobenius kernel) carries `ker(restrict on S₀)` to
`ker(restrict on H_j)`, so the two `U`-action images have equal order `a`.  This gives
`[U : C_U(H_j)] = a` for every `j`. -/

/-- **The generic single-factor centralizer `C_U(H_j)`** for an arbitrary Clifford summand
`H_j = caseA.Hpart j`, realized as a subgroup of `G` with `C_U(H_j) ≤ U`.  Mirror of `cuSub`
(which is `C_U(S₀)` for the distinguished generator): the kernel of the restricted `U`-action
`aInvariantRestrictAut (caseA.Hpart_aInvariant j)` on the order-`p` factor `H_j`, pushed into `G`
along `↥(U.subgroupOf (U ⊔ W₁)) ↪ ↥(U ⊔ W₁) ↪ G`.  By orbit symmetry `[U : C_U(H_j)] = a`
(`relIndex_cuSubOf_U_eq_a`), the same index as `C_U(S₀)`. -/
noncomputable def cuSubOf {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) : Subgroup G :=
  ((aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
    (data.typeP.U ⊔ data.typeP.W1).subtype

omit [Finite G] in
theorem cuSubOf_le_U {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) : cuSubOf caseA j ≤ data.U :=
  (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans <| by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left

omit [Finite G] in
/-- `|C_U(H_j)| = |ker(aInvariantRestrictAut H_j)|` (mirrors `card_cuSub_eq_card_ker`). -/
theorem card_cuSubOf_eq_card_ker {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) :
    Nat.card ↥(cuSubOf caseA j)
      = Nat.card ↥(aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker := by
  change Nat.card ↥(((aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
        (data.typeP.U ⊔ data.typeP.W1).subtype)
      = Nat.card ↥(aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv]

/-- **`ker(uActionHom) ≤ ker(aInvariantRestrictAut H_j)`**: an element acting trivially on the
whole chief factor acts trivially on the summand `H_j` (mirrors
`ker_uActionHom_le_ker_aInvariantRestrictAut` for `S₀`, via
`centralizes_all_imp_centralizes_summand`). -/
theorem ker_uActionHom_le_ker_Hpart {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) :
    (uActionHom data chief).ker ≤ (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  exact centralizes_all_imp_centralizes_summand caseA j g hg

/-- **`C = C_U(H̄) ≤ C_U(H_j)`** (`cSub ≤ cuSubOf`, mirrors `cSub_le_cuSub`). -/
theorem cSub_le_cuSubOf {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) : cSub data chief ≤ cuSubOf caseA j :=
  Subgroup.map_mono (Subgroup.map_mono (ker_uActionHom_le_ker_Hpart caseA j))

/-- **Orbit symmetry of the Clifford index `a`.**  For *any* summand `H_j = caseA.Hpart j` the
order of the `U`-action image on `H_j` equals `caseA.a` (`= |Ū₁|`, the image on the distinguished
generator `S₀`).  Since `H_j = φ(orbitRep j) • S₀` is the automorphic image of `S₀` under
`w = φ(orbitRep j)`, conjugation `σ = conjNormal w⁻¹` (well-defined on the acting group because
`U ◁ U W₁` is the Frobenius kernel, `W1_normalizes_U`) is an automorphism of the acting `U`-group
carrying `ker(restrict on S₀)` to `ker(restrict on H_j)`; equal kernels force equal ranges (first
isomorphism `|U| = |range|·|ker|` on both).  This is the crux behind `[U : C_U(H_j)] = a` for a
general summand (`relIndex_cuSubOf_U_eq_a`). -/
theorem caseA_a_eq_card_Hpart_restrictAut_range {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) (j : Fin data.q) :
    caseA.a = Nat.card ↥(aInvariantRestrictAut (caseA.Hpart_aInvariant j)).range := by
  classical
  set L := data.typeP.U ⊔ data.typeP.W1 with hL
  -- `U ◁ L` (Frobenius kernel), so conjugation by `L`-elements permutes the acting group `U`.
  haveI hAnorm : (data.typeP.U.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer data.typeP.W1_normalizes_U)
  set wt : ↥L := caseA.orbitRep j with hwt
  set w : MulAut (↥data.H ⧸ chief.N) := quotientMulAutHom chief.N_aInvariant wt with hw
  set σ : MulAut ↥(data.typeP.U.subgroupOf L) := MulAut.conjNormal (wt⁻¹) with hσ
  have hHj : caseA.Hpart j = w • caseA.S0 := caseA.Hpart_orbit j
  -- Pointwise-fix characterisation of `restrict … = 1`.
  have hchar : ∀ (S : Subgroup (↥data.H ⧸ chief.N))
      (hS : IsAInvariant (uActionHom data chief) S)
      (a : ↥(data.typeP.U.subgroupOf L)),
      aInvariantRestrictAut hS a = 1 ↔ ∀ y ∈ S, (uActionHom data chief) a y = y := by
    intro S hS a
    constructor
    · intro h y hy
      have hcoe := aInvariantRestrictAut_coe hS a ⟨y, hy⟩
      rw [h] at hcoe
      simpa [MulAut.one_apply] using hcoe.symm
    · intro h
      ext z
      rw [MulAut.one_apply, aInvariantRestrictAut_coe]
      exact h _ z.2
  -- `σ`-conjugation of the action: `φ(σ a) x = w⁻¹ (φ a (w x))`.
  have hσφ : ∀ (a : ↥(data.typeP.U.subgroupOf L)) (x : ↥data.H ⧸ chief.N),
      (uActionHom data chief) (σ a) x = w⁻¹ ((uActionHom data chief) a (w x)) := by
    intro a x
    have hval : ((σ a : ↥(data.typeP.U.subgroupOf L)) : ↥L) = wt⁻¹ * (a : ↥L) * wt := by
      rw [hσ, MulAut.conjNormal_apply, inv_inv]
    have h1 : (uActionHom data chief) (σ a)
        = quotientMulAutHom chief.N_aInvariant
            ((σ a : ↥(data.typeP.U.subgroupOf L)) : ↥L) := rfl
    rw [h1, hval, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply]
    rfl
  -- Kernel correspondence `ker(H_j) = ker(S₀).comap σ`.
  have hker : (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker
      = (aInvariantRestrictAut caseA.S0_aInvariant).ker.comap σ.toMonoidHom := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom,
      hchar (caseA.Hpart j) (caseA.Hpart_aInvariant j) a,
      hchar caseA.S0 caseA.S0_aInvariant (σ a)]
    constructor
    · intro h x hx
      rw [hσφ a x]
      have hxHj : w x ∈ caseA.Hpart j := by
        rw [hHj, ← MulAut.smul_def]
        exact Subgroup.smul_mem_pointwise_smul_iff.mpr hx
      rw [h (w x) hxHj, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    · intro h y hy
      rw [hHj] at hy
      have hx : w⁻¹ • y ∈ caseA.S0 := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hy
      have hfix := h (w⁻¹ • y) hx
      rw [hσφ a (w⁻¹ • y), MulAut.smul_def] at hfix
      have hww : w (w⁻¹ y) = y := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      rw [hww] at hfix
      exact w⁻¹.injective hfix
  -- Equal kernel cardinalities (conjugation `σ` is a bijection).
  have hkercard : Nat.card ↥(aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker
      = Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).ker := by
    rw [hker, Subgroup.comap_equiv_eq_map_symm']
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ σ.symm.toMonoidHom
      σ.symm.injective).toEquiv).symm
  -- Equal range cardinalities via the first isomorphism `|U| = |range|·|ker|`.
  have h0 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (aInvariantRestrictAut caseA.S0_aInvariant).ker
  have hj := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
    (aInvariantRestrictAut caseA.S0_aInvariant)).toEquiv] at h0
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
    (aInvariantRestrictAut (caseA.Hpart_aInvariant j))).toEquiv] at hj
  rw [caseA.a_eq_card_restrictAut_range]
  have hcancel := h0.symm.trans hj
  rw [hkercard] at hcancel
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcancel

/-- **`|U| = a · |C_U(H_j)|`** for an arbitrary summand (mirrors `card_U_eq_a_mul_card_cuSub`), via
orbit symmetry `a = |range(aInvariantRestrictAut H_j)|` (`caseA_a_eq_card_Hpart_restrictAut_range`)
and the first isomorphism theorem. -/
theorem card_U_eq_a_mul_card_cuSubOf {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) :
    Nat.card ↥data.U = caseA.a * Nat.card ↥(cuSubOf caseA j) := by
  rw [caseA_a_eq_card_Hpart_restrictAut_range caseA j]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (aInvariantRestrictAut (caseA.Hpart_aInvariant j))).toEquiv,
    ← card_cuSubOf_eq_card_ker caseA j,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).toEquiv] at h
  exact h

/-- **`[U : C_U(H_j)] = a`** for an arbitrary Clifford summand `H_j` (mirrors
`relIndex_cuSub_U_eq_a` for `S₀`): Lagrange `[U:C_U(H_j)]·|C_U(H_j)| = |U| = a·|C_U(H_j)|`
(`card_U_eq_a_mul_card_cuSubOf`), cancelling `|C_U(H_j)| > 0`.  The orbit-symmetric per-summand
inertia index behind Peterfalvi (9.11.2). -/
theorem relIndex_cuSubOf_U_eq_a {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) :
    (cuSubOf caseA j).relIndex data.U = caseA.a := by
  have h1 : (cuSubOf caseA j).relIndex data.U * Nat.card ↥(cuSubOf caseA j)
      = Nat.card ↥data.U := by
    have h := Subgroup.index_mul_card ((cuSubOf caseA j).subgroupOf data.U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cuSubOf_le_U caseA j)).toEquiv] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos
    (h1.trans (card_U_eq_a_mul_card_cuSubOf caseA j))

/-! ### The realized two-summand centralizer `C_U(H_i) ∩ C_U(H_j)` inside `HU` and the (9.11.2)
inertia identity `I(θ₀) = H·(C_U(H_i) ∩ C_U(H_j))`

Lifts the chief-factor-level two-summand inertia (`caseA_inertia_iff_centralizes_two_summands`) to
the `HU`-inertia subgroup of the inflated character `θ₀`.  Mirrors the a-owned
`cuInHu`/`inertia_eq_hcuInHu_of_easy_le` chain for the single generator `S₀`, but the centralizer is
the *pair* intersection `C_U(H_i) ⊓ C_U(H_j)` (realized as `cuSubOf i ⊓ cuSubOf j`), and the
character-side uses the two-summand lemmas `caseA_hu_char_inertia_two_summands` (`⊆`) and
`caseA_centralizes_two_summands_compHom_eq` (`⊇`). -/

/-- **The realized two-summand centralizer `C_U(H_i) ∩ C_U(H_j)` inside `HU`**, as a subgroup of
`↥(huSub data)` (mirrors `cuInHu` for the single generator `S₀`, but with the *pair* intersection
`cuSubOf i ⊓ cuSubOf j` of the two single-factor centralizers). -/
noncomputable def cuInHuPair {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) : Subgroup ↥(huSub data) :=
  ((cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf M).subgroupOf (huSub data)

omit [Finite G] in
/-- `C_U(H_i) ∩ C_U(H_j) ≤ U` realized inside `HU` (mirrors `cuInHu_le_uInHu`). -/
theorem cuInHuPair_le_uInHu {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) : cuInHuPair caseA i j ≤ uInHu data :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _
    (inf_le_left.trans (cuSubOf_le_U caseA i)))

/-- **Realization bridge**: a `U`-element `a` whose realized `G`-image lies in `cuSubOf caseA k`
acts trivially on the summand `H_k` (`a ∈ ker(aInvariantRestrictAut (Hpart_aInvariant k))`).  The
reverse of the membership-building in `inertia_inf_uInHu_le_cuInHu`: `cuSubOf` is the double
`subtype`-image of the kernel, and the double `subtype` is injective, so the extracted kernel
witness equals `a`. -/
theorem mem_ker_of_realized_mem_cuSubOf {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) (k : Fin data.q)
    (a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (h : (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G)
        ∈ cuSubOf caseA k) :
    a ∈ (aInvariantRestrictAut (caseA.Hpart_aInvariant k)).ker := by
  simp only [cuSubOf, Subgroup.mem_map] at h
  obtain ⟨w, ⟨b, hb_ker, hb_w⟩, hw⟩ := h
  have hba : b = a := by
    apply Subgroup.subtype_injective (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
    apply Subgroup.subtype_injective (data.typeP.U ⊔ data.typeP.W1)
    rw [hb_w]; exact hw
  rwa [hba] at hb_ker

/-- **(9.11.2) `⊆` half at the `HU`-inertia level: `I(θ₀) ⊓ U ≤ C_U(H_i) ∩ C_U(H_j)`.**  For the
inflation `θ₀` of a chief-factor character `θbar` regular on the two Clifford summands `H_i`, `H_j`,
a realized `U`-element `g` in the `HU`-inertia of `θ₀` lies in the realized two-summand centralizer
`cuInHuPair`.  Realizes `g` as an abstract `U`-element `a`, unwraps the `conjBy`-fixing to the
`compHom (typeP_conjAction)` form (`conjBy_compHom_hInHuEquivH` + the injective inflation iso),
feeds it to the two-summand char-inertia core `caseA_hu_char_inertia_two_summands` (giving
`aInvariantRestrictAut … a = 1` on both summands), and builds the intersection membership from the
two kernel witnesses.  Mirrors the single-factor `inertia_inf_uInHu_le_cuInHu`. -/
theorem inertia_inf_uInHu_le_cuInHuPair {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hregi : ∃ x ∈ caseA.Hpart i, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
      ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (hregj : ∃ x ∈ caseA.Hpart j, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
      ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cuInHuPair caseA i j := by
  rintro g ⟨hgin, hgu⟩
  have hgU : ((g : ↥M) : G) ∈ data.typeP.U := by
    simp only [uInHu] at hgu; exact hgu
  have hgUW1 : ((g : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hgU
  set a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U :=
    ⟨⟨((g : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  have hag : ((g : ↥M) : G)
      = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  have hfix := ClassFunction.mem_inertia.mp hgin
  rw [conjBy_compHom_hInHuEquivH data
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype a)
    g hag] at hfix
  have hfix1 := ClassFunction.compHom_injective_of_surjective (hInHuEquivH data).surjective hfix
  obtain ⟨hi, hj⟩ := caseA_hu_char_inertia_two_summands caseA hregi hregj a hfix1
  have hkeri : a ∈ (aInvariantRestrictAut (caseA.Hpart_aInvariant i)).ker :=
    MonoidHom.mem_ker.mpr hi
  have hkerj : a ∈ (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker :=
    MonoidHom.mem_ker.mpr hj
  simp only [cuInHuPair, Subgroup.mem_subgroupOf, Subgroup.mem_inf, cuSubOf, Subgroup.mem_map]
  exact ⟨⟨_, ⟨a, hkeri, rfl⟩, rfl⟩, ⟨_, ⟨a, hkerj, rfl⟩, rfl⟩⟩

/-- **(9.11.2) `⊇` half at the `HU`-inertia level: `C_U(H_i) ∩ C_U(H_j) ≤ I(θ₀)`.**  For the
inflation `θ₀` of `θbar = linearIrreducibleCharacter χ` with `χ` a two-summand-supported
linear character (trivial off `i`, `j`, `hsupp`), the realized two-summand centralizer
`cuInHuPair` fixes `θ₀`.  A `cuInHuPair`-element `c` realizes an abstract `U`-element `a`
centralizing both summands (`aInvariantRestrictAut … a = 1` on `i` and `j`, via
`mem_ker_of_realized_mem_cuSubOf`), so `caseA_centralizes_two_summands_compHom_eq` gives
`compHom (uActionHom a) θbar = θbar`; inflating (`conjBy_compHom_hInHuEquivH` +
`compHom_typeP_conjAction_inflation`) then fixes `θ₀`.  Mirrors `cInHu_le_inertia`, replacing
`quotientMulAutHom w = 1` with the two-summand char-fixing. -/
theorem cuInHuPair_le_inertia {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (χ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hsupp : ∀ k, k ≠ i → k ≠ j → ∀ x ∈ caseA.Hpart k, χ x = 1) :
    cuInHuPair caseA i j ≤ ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
  intro c hc
  rw [ClassFunction.mem_inertia]
  have hcinf : ((c : ↥M) : G) ∈ cuSubOf caseA i ⊓ cuSubOf caseA j := by
    simpa only [cuInHuPair, Subgroup.mem_subgroupOf] using hc
  have hgU : ((c : ↥M) : G) ∈ data.typeP.U := cuSubOf_le_U caseA i hcinf.1
  have hgUW1 : ((c : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hgU
  set a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U :=
    ⟨⟨((c : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  have hag : ((c : ↥M) : G)
      = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  have hgi : aInvariantRestrictAut (caseA.Hpart_aInvariant i) a = 1 :=
    MonoidHom.mem_ker.mp (mem_ker_of_realized_mem_cuSubOf caseA i a (hag ▸ hcinf.1))
  have hgj : aInvariantRestrictAut (caseA.Hpart_aInvariant j) a = 1 :=
    MonoidHom.mem_ker.mp (mem_ker_of_realized_mem_cuSubOf caseA j a (hag ▸ hcinf.2))
  have hchar : ClassFunction.compHom (quotientMulAutHom chief.N_aInvariant
        ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a)).toMonoidHom
        (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      = (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) :=
    caseA_centralizes_two_summands_compHom_eq caseA χ hsupp a hgi hgj
  rw [conjBy_compHom_hInHuEquivH data
      ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype a)
      c hag, compHom_typeP_conjAction_inflation, hchar]

/-- **(9.11.2) the `HU`-inertia identity `I(θ₀) = H·(C_U(H_i) ∩ C_U(H_j))`.**  Combining the two
containments (`inertia_inf_uInHu_le_cuInHuPair` for `⊆`, `cuInHuPair_le_inertia` for `⊇`) with
`H ≤ I(θ₀)` (`subgroup_le_inertia`) identifies the `HU`-inertia of the inflated two-summand
character `θ₀` as `hInHu ⊔ cuInHuPair`.  This is the realized `HU`-level lift of Peterfalvi
(9.11.2)'s inertia `I(θ₀) = H·(U₁ ∩ U₁ʷ)`; its index in `HU` is `[U : U₁ ∩ U₁ʷ]` (the
two-summand inertia index).  Mirrors `inertia_eq_hcInHu_of_inf_le` /
`inertia_eq_hcuInHu_of_easy_le`. -/
theorem caseA_inertia_eq_hcuInHuPair {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (χ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hsupp : ∀ k, k ≠ i → k ≠ j → ∀ x ∈ caseA.Hpart k, χ x = 1)
    (hregi : ∃ x ∈ caseA.Hpart i,
      (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (hregj : ∃ x ∈ caseA.Hpart j,
      (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cuInHuPair caseA i j := by
  set θ₀ := ClassFunction.compHom (hInHuEquivH data).toMonoidHom
    (ClassFunction.compHom (QuotientGroup.mk' chief.N)
      (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ)) with hθ₀
  apply le_antisymm
  · intro g hg
    have hgtop : g ∈ hInHu data ⊔ uInHu data :=
      hInHu_sup_uInHu_eq_top data ▸ Subgroup.mem_top g
    rw [Subgroup.mem_sup_of_normal_left] at hgtop
    obtain ⟨h, hh, u, hu, rfl⟩ := hgtop
    have hh_in : h ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
      ClassFunction.subgroup_le_inertia θ₀ hh
    have hu_in : u ∈ ClassFunction.inertia (H := hInHu data) θ₀ := by
      have hmem : h⁻¹ * (h * u) ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
        mul_mem (inv_mem hh_in) hg
      rwa [inv_mul_cancel_left] at hmem
    exact mul_mem (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right (inertia_inf_uInHu_le_cuInHuPair caseA hregi hregj ⟨hu_in, hu⟩))
  · rw [sup_le_iff]
    exact ⟨ClassFunction.subgroup_le_inertia θ₀, cuInHuPair_le_inertia caseA χ hsupp⟩

/-! ### (9.11.2) the inertia **index** `[HU : I(θ₀)] = [U : C_U(H_i) ∩ C_U(H_j)]`

Computes the index of the (9.11.2) two-summand inertia `I(θ₀) = H·(C_U(H_i) ∩ C_U(H_j))`
(`caseA_inertia_eq_hcuInHuPair`) in `HU`.  Mirrors the a-owned single-generator chain
`index_hcuInHu_eq_relindex_cuInHu` + `index_cuInHu_subgroupOf_uInHu_eq_a` (and the all-summand
`hc_index_eq_u`), replacing `cuInHu`/`C_U(S₀)` with the pair `cuInHuPair`/`C_U(H_i) ∩ C_U(H_j)`:
the second-isomorphism step `[HU : H·K] = [U : K]` (`K ◁ U` normal as an intersection of the two
single-factor centralizer kernels) followed by the realization `[uInHu : cuInHuPair] = [U : K]`.
This is Peterfalvi (9.11.2)'s inertia index `[U : U₁ ∩ U₁ʷ]` — the degree of the source character
whose `M`-induction lands in `𝒮(H₀C′)`, feeding the degree dichotomy `[U:U₁∩U₁ʷ] ∈ {u,a}`. -/

omit [Finite G] in
open Subgroup in
/-- **`C_U(H_j) ◁ U`** for a general Clifford summand (mirrors `cuSub_subgroupOf_U_normal` for
`S₀`): the realization `cuSubOf j` is the `G`-image of the kernel `ker(aInvariantRestrictAut H_j)`,
so its `subgroupOf U` is normal (kernels are normal, transported by the realization iso
`↥(U.subgroupOf (U ⊔ W₁)) ≃* ↥U`). -/
theorem cuSubOf_subgroupOf_U_normal {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) (j : Fin data.q) :
    ((cuSubOf caseA j).subgroupOf data.U).Normal := by
  set e := subgroupOfEquivOfLe (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1) with he
  have heq : (cuSubOf caseA j).subgroupOf data.U
      = (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker.map e.toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      simp only [cuSubOf, Subgroup.mem_map] at hx
      obtain ⟨z, ⟨y, hy, hyz⟩, hzx⟩ := hx
      refine ⟨y, hy, ?_⟩
      apply Subtype.ext
      rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe, ← hzx, ← hyz]
      rfl
    · rintro ⟨y, hy, rfl⟩
      simp only [cuSubOf, Subgroup.mem_map]
      refine ⟨_, ⟨y, hy, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe]
      rfl
  rw [heq]
  exact (MonoidHom.normal_ker _).map e.toMonoidHom e.surjective

omit [Finite G] in
/-- **`C_U(H_i) ∩ C_U(H_j) ◁ U`** (the two-summand centralizer is normal in `U`): the intersection
of the two single-factor normal centralizers (`cuSubOf_subgroupOf_U_normal`), via `subgroupOf`
distributing over `⊓` (`Subgroup.comap_inf`) and `⊓` of normals being normal. -/
theorem cuSubOf_pair_subgroupOf_U_normal {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) :
    ((cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf data.U).Normal := by
  have hi := cuSubOf_subgroupOf_U_normal caseA i
  have hj := cuSubOf_subgroupOf_U_normal caseA j
  have hEq : (cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf data.U
      = (cuSubOf caseA i).subgroupOf data.U ⊓ (cuSubOf caseA j).subgroupOf data.U := by
    simp only [Subgroup.subgroupOf, Subgroup.comap_inf]
  rw [hEq]
  refine ⟨fun n hn g => Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
  · exact hi.conj_mem n (Subgroup.mem_inf.mp hn).1 g
  · exact hj.conj_mem n (Subgroup.mem_inf.mp hn).2 g

omit [Finite G] in
/-- `|C_U(H_i) ∩ C_U(H_j)|` realized inside `HU` equals its `G`-cardinality (mirrors
`card_cuInHu_eq`): the double `subgroupOf` realization is an injective image. -/
theorem card_cuInHuPair_eq {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) :
    Nat.card ↥(cuInHuPair caseA i j) = Nat.card ↥(cuSubOf caseA i ⊓ cuSubOf caseA j) := by
  have hKleU : cuSubOf caseA i ⊓ cuSubOf caseA j ≤ data.U := inf_le_left.trans (cuSubOf_le_U caseA i)
  have hCsubM : (cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (hKleU.trans (le_sup_right : data.U ≤ data.H ⊔ data.U))
  have hCleM : cuSubOf caseA i ⊓ cuSubOf caseA j ≤ M := hKleU.trans (U_le_M data)
  calc Nat.card ↥(cuInHuPair caseA i j)
      = Nat.card ↥((cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCsubM).toEquiv
    _ = Nat.card ↥(cuSubOf caseA i ⊓ cuSubOf caseA j) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleM).toEquiv

omit [Finite G] in
open Subgroup in
/-- **`C_U(H_i) ∩ C_U(H_j) ◁ U` realized inside `HU`** (mirrors `cuInHu_normal`):
`cuInHuPair ◁ uInHu`, transported from `(cuSubOf i ⊓ cuSubOf j) ◁ U` along `↥uInHu ≃* ↥U`. -/
theorem cuInHuPair_normal {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) :
    ((cuInHuPair caseA i j).subgroupOf (uInHu data)).Normal := by
  have hUsubM : data.U.subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_sup_right : data.U ≤ data.H ⊔ data.U)
  set f : ↥(uInHu data) ≃* ↥data.U :=
    (subgroupOfEquivOfLe hUsubM).trans (subgroupOfEquivOfLe (U_le_M data)) with hf
  have hgval : ∀ x : ↥(uInHu data), ((f x : ↥data.U) : G) = (((x : ↥(huSub data)) : ↥M) : G) := by
    intro x
    have h1 : (f x : ↥data.U)
        = subgroupOfEquivOfLe (U_le_M data) (subgroupOfEquivOfLe hUsubM x) := by rw [hf]; rfl
    rw [h1, subgroupOfEquivOfLe_apply_coe, subgroupOfEquivOfLe_apply_coe]
  have hcomap : (cuInHuPair caseA i j).subgroupOf (uInHu data)
      = ((cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf data.U).comap f.toMonoidHom := by
    ext x
    simp only [cuInHuPair, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, hgval x]
  rw [hcomap]
  exact (cuSubOf_pair_subgroupOf_U_normal caseA i j).comap f.toMonoidHom

omit [Finite G] in
/-- **`H·(C_U(H_i) ∩ C_U(H_j)) ◁ HU`** (mirrors `hcuInHu_normal`): the (9.11.2) inertia subgroup is
normal.  From `H ◁ HU` (`hInHu_normal`), `C_U(H_i) ∩ C_U(H_j) ◁ U` (`cuInHuPair_normal`), and
`H ⊔ U = ⊤` (`hInHu_sup_uInHu_eq_top`) via `sup_normal_of_normal_left_of_normal_subgroupOf`. -/
theorem hcuInHuPair_normal {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) :
    (hInHu data ⊔ cuInHuPair caseA i j).Normal :=
  haveI := hInHu_normal data
  haveI := cuInHuPair_normal caseA i j
  OddOrder.GroupTheory.sup_normal_of_normal_left_of_normal_subgroupOf
    (cuInHuPair_le_uInHu caseA i j) (hInHu_sup_uInHu_eq_top data)

/-- **`C = C_U(H̄) ≤ C_U(H_i) ∩ C_U(H_j)`** realized (`cInHu ≤ cuInHuPair`): centralizing the whole
chief factor implies centralizing each summand (`cSub_le_cuSubOf`), realized through the double
`subgroupOf`. -/
theorem cInHu_le_cuInHuPair {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) : cInHu data chief ≤ cuInHuPair caseA i j :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _
    (le_inf (cSub_le_cuSubOf caseA i) (cSub_le_cuSubOf caseA j)))

/-- **`U ⊓ H·(C_U(H_i) ∩ C_U(H_j)) = C_U(H_i) ∩ C_U(H_j)`** realized (mirrors
`uInHu_inf_hcuInHu_eq_cuInHu`), the second-iso input for `[HU : H·K] = [U : K]`.  The crux
`hInHu ⊓ uInHu ≤ cuInHuPair` factors through `H ⊓ U ≤ C` (`hInHu_inf_uInHu_le_cInHu`) and
`C ≤ K` (`cInHu_le_cuInHuPair`). -/
theorem uInHu_inf_hcuInHuPair_eq_cuInHuPair {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) (i j : Fin data.q) :
    uInHu data ⊓ (hInHu data ⊔ cuInHuPair caseA i j) = cuInHuPair caseA i j := by
  haveI := hInHu_normal data
  apply le_antisymm
  · rintro x ⟨hxU, hxHC⟩
    obtain ⟨hh, hhmem, cc, ccmem, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxHC
    have hcc_u : cc ∈ uInHu data := cuInHuPair_le_uInHu caseA i j ccmem
    have hh_u : hh ∈ uInHu data := by
      have h1 : hh * cc * cc⁻¹ ∈ uInHu data :=
        (uInHu data).mul_mem hxU ((uInHu data).inv_mem hcc_u)
      rwa [mul_inv_cancel_right] at h1
    have hh_c : hh ∈ cuInHuPair caseA i j :=
      cInHu_le_cuInHuPair caseA i j
        (hInHu_inf_uInHu_le_cInHu data chief (Subgroup.mem_inf.mpr ⟨hhmem, hh_u⟩))
    exact (cuInHuPair caseA i j).mul_mem hh_c ccmem
  · exact le_inf (cuInHuPair_le_uInHu caseA i j) le_sup_right

/-- **Second-iso index step: `[HU : H·(C_U(H_i) ∩ C_U(H_j))] = [U : C_U(H_i) ∩ C_U(H_j)]`**
(realized `(hInHu ⊔ cuInHuPair).index = (cuInHuPair.subgroupOf uInHu).index`).  Mirrors
`index_hcuInHu_eq_relindex_cuInHu`: the second isomorphism theorem for `H·K ◁ HU` with
`uInHu ⊔ H·K = ⊤`, and `uInHu ⊓ H·K = K` (`uInHu_inf_hcuInHuPair_eq_cuInHuPair`). -/
theorem index_hcuInHuPair_eq_relindex_cuInHuPair {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) (i j : Fin data.q) :
    (hInHu data ⊔ cuInHuPair caseA i j).index
      = ((cuInHuPair caseA i j).subgroupOf (uInHu data)).index := by
  haveI : (hInHu data ⊔ cuInHuPair caseA i j).Normal := hcuInHuPair_normal caseA i j
  have htop : uInHu data ⊔ (hInHu data ⊔ cuInHuPair caseA i j) = ⊤ := by
    rw [← sup_assoc, sup_comm (uInHu data) (hInHu data), hInHu_sup_uInHu_eq_top, top_sup_eq]
  have he := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient
    (uInHu data) (hInHu data ⊔ cuInHuPair caseA i j)).toEquiv
  have hsub : (hInHu data ⊔ cuInHuPair caseA i j).subgroupOf (uInHu data)
      = (cuInHuPair caseA i j).subgroupOf (uInHu data) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxin : (x : ↥(huSub data))
          ∈ uInHu data ⊓ (hInHu data ⊔ cuInHuPair caseA i j) :=
        Subgroup.mem_inf.mpr ⟨x.2, hx⟩
      rw [uInHu_inf_hcuInHuPair_eq_cuInHuPair caseA i j] at hxin
      exact hxin
    · intro hx; exact Subgroup.mem_sup_right hx
  rw [hsub] at he
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((hInHu data ⊔ cuInHuPair caseA i j).subgroupOf
      (uInHu data ⊔ (hInHu data ⊔ cuInHuPair caseA i j)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
        (hInHu data ⊔ cuInHuPair caseA i j)
          ≤ uInHu data ⊔ (hInHu data ⊔ cuInHuPair caseA i j))).toEquiv,
    ← he, ← Subgroup.index_eq_card] at hsplit
  have htopcard : Nat.card ↥(uInHu data ⊔ (hInHu data ⊔ cuInHuPair caseA i j))
      = Nat.card ↥(huSub data) := by
    rw [htop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [htopcard] at hsplit
  have hmul := Subgroup.card_mul_index (hInHu data ⊔ cuInHuPair caseA i j)
  rw [hsplit, mul_comm (((cuInHuPair caseA i j).subgroupOf (uInHu data)).index)] at hmul
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

/-- **`[U : C_U(H_i) ∩ C_U(H_j)] = [uInHu : cuInHuPair]`** (realized index equals ambient-`G`
relative index).  Both sides multiply by `|C_U(H_i) ∩ C_U(H_j)|` to `|U|` (Lagrange in the `uInHu`
realization and in `U`), cancelling the positive common factor.  Mirrors the `relIndex_cSub_U_eq_u`
style. -/
theorem index_cuInHuPair_subgroupOf_uInHu_eq_relIndex {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) (i j : Fin data.q) :
    ((cuInHuPair caseA i j).subgroupOf (uInHu data)).index
      = (cuSubOf caseA i ⊓ cuSubOf caseA j).relIndex data.U := by
  have hI : Nat.card ↥(cuSubOf caseA i ⊓ cuSubOf caseA j)
      * ((cuInHuPair caseA i j).subgroupOf (uInHu data)).index = Nat.card ↥data.U := by
    have h := Subgroup.card_mul_index ((cuInHuPair caseA i j).subgroupOf (uInHu data))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cuInHuPair_le_uInHu caseA i j)).toEquiv,
      card_cuInHuPair_eq caseA i j, card_uInHu_eq data] at h
    exact h
  have hII : Nat.card ↥(cuSubOf caseA i ⊓ cuSubOf caseA j)
      * (cuSubOf caseA i ⊓ cuSubOf caseA j).relIndex data.U = Nat.card ↥data.U := by
    have h := Subgroup.card_mul_index ((cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf data.U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans (cuSubOf_le_U caseA i))).toEquiv] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hI.trans hII.symm)

/-- **Peterfalvi (9.11.2), the inertia index `[HU : I(θ₀)] = [U : C_U(H_i) ∩ C_U(H_j)]`.**

For the inflation `θ₀` of the two-summand-supported linear character `linearIrreducibleCharacter χ`
(regular on `H_i`, `H_j`, `hsupp` off them), the index of its `HU`-inertia group equals the
relative index of the realized two-summand centralizer `C_U(H_i) ∩ C_U(H_j)` in `U`.  Combines the
inertia identity `I(θ₀) = H·(C_U(H_i) ∩ C_U(H_j))` (`caseA_inertia_eq_hcuInHuPair`) with the
second-iso step (`index_hcuInHuPair_eq_relindex_cuInHuPair`) and the realization
(`index_cuInHuPair_subgroupOf_uInHu_eq_relIndex`).  This is the genuine geometric
`[U : U₁ ∩ U₁ʷ]` of Peterfalvi (9.11.2): the degree of the source character whose `M`-induction
lands in `𝒮(H₀C′)`, feeding the degree dichotomy `[U : U₁ ∩ U₁ʷ] ∈ {u, a}`. -/
theorem caseA_inertia_index_eq {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (χ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hsupp : ∀ k, k ≠ i → k ≠ j → ∀ x ∈ caseA.Hpart k, χ x = 1)
    (hregi : ∃ x ∈ caseA.Hpart i,
      (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (hregj : ∃ x ∈ caseA.Hpart j,
      (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    (ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))).index
      = (cuSubOf caseA i ⊓ cuSubOf caseA j).relIndex data.U := by
  rw [caseA_inertia_eq_hcuInHuPair caseA χ hsupp hregi hregj,
    index_hcuInHuPair_eq_relindex_cuInHuPair caseA i j,
    index_cuInHuPair_subgroupOf_uInHu_eq_relIndex caseA i j]

end NineElevenTwoInertia

/-- **`[U : K₁ ⊓ K₂] ≤ [U:K₁]·[U:K₂]`** (relative-index form of `Subgroup.index_inf_le`): the
relative index `H.relIndex U = (H.subgroupOf U).index`, and `subgroupOf = comap` distributes over
`⊓` (`Subgroup.comap_inf`), so the ambient `index_inf_le` in `↥U` applies.  The (9.11.2) injectivity
`Ū ↪ (U/U₁)×(U/U₁ʷ)` in relative-index form. -/
theorem relIndex_inf_le {G : Type*} [Group G] {K₁ K₂ U : Subgroup G} :
    (K₁ ⊓ K₂).relIndex U ≤ K₁.relIndex U * K₂.relIndex U := by
  simp only [Subgroup.relIndex, Subgroup.subgroupOf, Subgroup.comap_inf]
  exact Subgroup.index_inf_le

/-- **Peterfalvi (9.11.2), the bound `u ≤ a²`.**  Book (9.11.2): *"The canonical mapping from `Ū` to
`(U/U₁)×(U/U₁ʷ)` is injective, and so `u ≤ a²`."*  Given the inertia identity `C = U₁ ⊓ U₁ʷ` (the
*first* assertion of (9.11.2), the deep character-theoretic input: `U₁ = C_U(H₁)`, `U₁ʷ = C_U(H₂)`,
their intersection is `C = C_U(H̄)`) and the per-summand index `[U:U₁] = [U:U₁ʷ] = a`, the relative
index `u = [U:C]` is bounded by `[U:U₁]·[U:U₁ʷ] = a²` (`relIndex_inf_le`).  Consumed by the (9.11.5)
polynomial bound (`nineElevenFive_refutation`'s `hua2`). -/
theorem nineElevenTwo_u_le_a_sq [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) {K₁ K₂ : Subgroup G}
    (hK₁ : K₁.relIndex data.U = caseA.a) (hK₂ : K₂.relIndex data.U = caseA.a)
    (hCinf : chars.C = K₁ ⊓ K₂) : chars.u ≤ caseA.a * caseA.a := by
  have hu : (K₁ ⊓ K₂).relIndex data.U = chars.u := by
    rw [← hCinf]; exact relIndex_cSub_U_eq_u chars
  rw [← hu]
  calc (K₁ ⊓ K₂).relIndex data.U ≤ K₁.relIndex data.U * K₂.relIndex data.U := relIndex_inf_le
    _ = caseA.a * caseA.a := by rw [hK₁, hK₂]

/-! ### (9.11.5) preamble: the uniform sub-family `sumnS` value

Book (9.11.5) / Coq `lb3S1'` left endpoint: on `𝒮₁'` (the degree-`qa` irreducibles) every member is
norm-one of degree `qa`, so `Snorm ≡ (qa)²` and `sumnS 𝒮₁' = |𝒮₁'|·(qa)²`.  This is the `hs1'`
supplier of `nineElevenOne_configuration` combined with `sumnS_le_of_subset` (`𝒮₁' ⊆ 𝒮₂`). -/

section UniformSubfamily

variable [Finite G] {M : Subgroup G}

/-- **The uniform sub-family `sumnS` value.**  For a finite family `Si` of irreducible characters of
common degree `d`, `sumnS Si = |Si|·d²`: each member is norm-one (`inner_self_eq_one`, so `Snorm =
degree²`) of degree `d`.  The (9.11.5) left endpoint (`sumnS_of_norm_one_constant_degree` fed the
two pointwise facts from irreducibility + the degree). -/
theorem sumnS_irreducible_constant_degree [Fintype ↥M] [Invertible (Nat.card ↥M : ℂ)]
    (Si : Finset (ClassFunction ↥M ℂ)) {d : ℕ}
    (hirr : ∀ ψ ∈ Si, IsIrreducibleCharacter ψ) (hdeg : ∀ ψ ∈ Si, ψ 1 = (d : ℂ)) :
    OddOrder.Peterfalvi.S07.sumnS Si = (Si.card : ℝ) * (d : ℝ) ^ 2 := by
  refine OddOrder.Peterfalvi.S07.sumnS_of_norm_one_constant_degree
    (fun ψ hψ => ?_) (fun ψ hψ => ?_)
  · have h : ClassFunction.inner ψ ψ = 1 := by
      simpa using OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
        (⟨ψ, hirr ψ hψ⟩ : IrreducibleCharacter ↥M) ⟨ψ, hirr ψ hψ⟩
    rw [h, Complex.one_re]
  · rw [hdeg ψ hψ, Complex.natCast_re]

end UniformSubfamily

/-! ### (9.11.5): the exponential-beats-polynomial arithmetic contradiction

Book (9.11.5), final step: assuming `|𝒮₄| ≤ ‖α‖²`, the (9.11.3)/(9.11.4) norm identities and
(9.11.2) give `p^q − 1 ≤ (q+2)a³ + q²a² + 2qa`; with `p = 2a+1` this forces `2^q ≤ q+2`,
contradicting the induction `2^x > x+2` for `x ≥ 3`.  This subsection isolates the pure
`ℕ`-arithmetic core: the binomial lower bound `(2a+1)^q ≥ 2^q a^q + 2q(q−1)a² + 2qa + 1`
(extracting the `k ∈ {0,1,2,q}` terms) composed with the polynomial upper bound is impossible for
`q ≥ 3`, `a ≥ 1`. -/

section FiveArithmetic

/-- **`q + 2 < 2^q` for `q ≥ 3`** (the (9.11.5) endgame `2^x > x+2`, `x ≥ 3`), by induction:
base `3 + 2 = 5 < 8`, step `2·2^q ≥ 2(q+3) ≥ (q+1)+3`. -/
theorem add_two_lt_two_pow {q : ℕ} (hq : 3 ≤ q) : q + 2 < 2 ^ q := by
  induction q with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> simp_all
    · have := ih hn
      rw [pow_succ]
      omega

/-- **`2·(q.choose 2) = q·(q−1)`** (the `k = 2` binomial coefficient in exact form): `q.choose 2 =
q(q−1)/2` and `q(q−1)` is even (consecutive product). -/
theorem two_mul_choose_two (q : ℕ) : 2 * q.choose 2 = q * (q - 1) := by
  rw [Nat.choose_two_right]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · simp [hq]
  · have heven : 2 ∣ q * (q - 1) := by
      rcases Nat.even_or_odd q with h | h
      · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp h) _
      · exact Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd h odd_one)) _
    exact Nat.mul_div_cancel' heven

/-- **The (9.11.5) binomial lower bound** `2^q·a^q + 2q(q−1)·a² + 2q·a + 1 ≤ (2a+1)^q` (`q ≥ 3`):
the sum of the `k ∈ {0,1,2,q}` terms of `(2a+1)^q = ∑ (2a)^k·C(q,k)`, all others being
nonnegative. -/
theorem binomial_lower_bound {q a : ℕ} (hq : 3 ≤ q) :
    2 ^ q * a ^ q + 2 * q * (q - 1) * a ^ 2 + 2 * q * a + 1 ≤ (2 * a + 1) ^ q := by
  have hexp : (2 * a + 1) ^ q = ∑ k ∈ Finset.range (q + 1), (2 * a) ^ k * q.choose k := by
    rw [add_pow]
    exact Finset.sum_congr rfl fun k _ => by rw [one_pow, mul_one, Nat.cast_id]
  rw [hexp]
  have hsub : ({0, 1, 2, q} : Finset ℕ) ⊆ Finset.range (q + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]; omega
  refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
  -- The subset sum over `{0,1,2,q}` equals the four extracted terms.
  have h01 : (0 : ℕ) ∉ ({1, 2, q} : Finset ℕ) := by simp; omega
  have h12 : (1 : ℕ) ∉ ({2, q} : Finset ℕ) := by simp; omega
  have h2q : (2 : ℕ) ∉ ({q} : Finset ℕ) := by simp; omega
  rw [show ({0, 1, 2, q} : Finset ℕ) = insert 0 (insert 1 (insert 2 {q})) from rfl,
    Finset.sum_insert h01, Finset.sum_insert h12, Finset.sum_insert h2q, Finset.sum_singleton]
  -- Evaluate each term.
  have e0 : (2 * a) ^ 0 * q.choose 0 = 1 := by simp
  have e1 : (2 * a) ^ 1 * q.choose 1 = 2 * q * a := by
    rw [pow_one, Nat.choose_one_right]; ring
  have e2 : (2 * a) ^ 2 * q.choose 2 = 2 * q * (q - 1) * a ^ 2 := by
    rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from rfl, mul_comm ((4 : ℕ) * a ^ 2) (q.choose 2),
      ← mul_assoc, show (q.choose 2) * 4 = 2 * (2 * q.choose 2) by ring, two_mul_choose_two]
    ring
  have eq : (2 * a) ^ q * q.choose q = 2 ^ q * a ^ q := by
    rw [Nat.choose_self, mul_one, mul_pow]
  rw [e0, e1, e2, eq]; omega

/-- **Peterfalvi (9.11.5), the arithmetic contradiction.**  For `q ≥ 3` and `a ≥ 1`, the polynomial
bound `(2a+1)^q − 1 ≤ (q+2)a³ + q²a² + 2qa` (from `|𝒮₄| ≤ ‖α‖²` via (9.11.2)-(9.11.4), with
`p = 2a+1`) is impossible: the binomial lower bound forces `2^q·a^q ≤ (q+2)·a³` (the `a²` terms
cancel since `2q(q−1) ≥ q²` for `q ≥ 2`), hence `2^q ≤ q+2` (as `a^q ≥ a³`), contradicting
`add_two_lt_two_pow`. -/
theorem nineElevenFive_arithmetic_contradiction {q a : ℕ} (hq : 3 ≤ q) (ha : 1 ≤ a)
    (hbound : (2 * a + 1) ^ q - 1 ≤ (q + 2) * a ^ 3 + q ^ 2 * a ^ 2 + 2 * q * a) : False := by
  have hlb := binomial_lower_bound (a := a) hq
  -- `2^q a^q + 2q(q−1)a² + 2qa ≤ (2a+1)^q − 1 ≤ (q+2)a³ + q²a² + 2qa`, cancel `2qa`.
  have hchain : 2 ^ q * a ^ q + 2 * q * (q - 1) * a ^ 2
      ≤ (q + 2) * a ^ 3 + q ^ 2 * a ^ 2 := by
    have h1 : 2 ^ q * a ^ q + 2 * q * (q - 1) * a ^ 2 + 2 * q * a
        ≤ (2 * a + 1) ^ q - 1 := by omega
    omega
  -- `q²a² ≤ 2q(q−1)a²` (since `2q(q−1) ≥ q²` for `q ≥ 2`), so `2^q a^q ≤ (q+2)a³`.
  have hq2 : q ^ 2 ≤ 2 * q * (q - 1) := by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ q)]
  have hqaq : 2 ^ q * a ^ q ≤ (q + 2) * a ^ 3 := by nlinarith [Nat.mul_le_mul_right (a ^ 2) hq2]
  -- `a^q ≥ a^3` (as `q ≥ 3`, `a ≥ 1`), so `2^q a³ ≤ (q+2)a³`, giving `2^q ≤ q+2`.
  have haq : a ^ 3 ≤ a ^ q := Nat.pow_le_pow_right ha hq
  have hfinal : 2 ^ q ≤ q + 2 := by
    have ha3 : 0 < a ^ 3 := pow_pos (by omega : (0 : ℕ) < a) 3
    have : 2 ^ q * a ^ 3 ≤ (q + 2) * a ^ 3 :=
      le_trans (Nat.mul_le_mul_left (2 ^ q) haq) hqaq
    exact Nat.le_of_mul_le_mul_right this ha3
  exact absurd hfinal (Nat.not_le.mpr (add_two_lt_two_pow hq))

/-- **Peterfalvi (9.11.3), the `|𝒮₄|` count** (arithmetic core, denominator-cleared).

Book (9.11.3): the sum-of-squares class equation on the quotient `HŪ/(H₀C)` — `n` characters of
degree `u` and `q(p−1)u/a²` of degree `a`, plus the `u` linear characters of `Ū` — gives
`p^q·u = u + n·u² + q(p−1)·u` (`hclass`).  Cancelling one `u` yields `n·u + q(p−1) + 1 = p^q`; with
the conjugate/reducible split `n = q·|𝒮₄| + (p−1)` (`hn`: `(9.8.b)` gives `p−1` of the `n` inducing
reducibly, the rest falling into `W₁`-orbits of size `q`), this rearranges to the cleared count
`|𝒮₄|·qu + (p−1)u + (p−1)q + 1 = p^q` — the `hcount` input of `nineElevenFive_refutation` (with
`p = 2a+1`).  The two group inputs `hclass` (character sum-of-squares) and `hn` (W₁-orbit count) are
the deep (9.11.3) content, supplied separately. -/
theorem nineElevenThree_count {p q u n S4 : ℕ} (hu : 1 ≤ u)
    (hclass : u + n * u ^ 2 + q * (p - 1) * u = p ^ q * u)
    (hn : n = S4 * q + (p - 1)) :
    S4 * (q * u) + (p - 1) * u + (p - 1) * q + 1 = p ^ q := by
  -- Cancel one `u` from the class equation: `n·u + q(p−1) + 1 = p^q`.
  have key : (n * u + q * (p - 1) + 1) * u = p ^ q * u := by
    have hexp : (n * u + q * (p - 1) + 1) * u = u + n * u ^ 2 + q * (p - 1) * u := by ring
    rw [hexp]; exact hclass
  have hnu : n * u + q * (p - 1) + 1 = p ^ q :=
    Nat.eq_of_mul_eq_mul_right (by omega) key
  -- Substitute the `W₁`-orbit split and reassociate.
  rw [hn] at hnu
  have hre : (S4 * q + (p - 1)) * u + q * (p - 1) + 1
      = S4 * (q * u) + (p - 1) * u + (p - 1) * q + 1 := by ring
  rw [← hre]; exact hnu

/-- **Peterfalvi (9.11.5), the full refutation** (`|𝒮₄| ≤ ‖α‖²` is impossible).

The (9.11.5) argument in denominator-cleared `ℕ` form.  Inputs (all `ℕ`, integrality already used):

* `hcount` — (9.11.3) cleared: `|𝒮₄|·qu + (p−1)q + (p−1)u + 1 = p^q`, i.e. with `p = 2a+1`,
  `S₄·qu + 2aq + 2au + 1 = (2a+1)^q`.  (Book: `|𝒮₄| = (p^q−1)/(qu) − (p−1)/u − (p−1)/q`.)
* `hnorm` — (9.11.4) cleared: `‖α‖²·u = (a+1)u + (q−1)a²`.  (Book: `‖α‖² = a+1+(q−1)a²/u`;
  `‖α‖² ∈ ℤ` as a virtual-character norm.)
* `hua2` — (9.11.2): `u ≤ a²`.
* `hle` — the contradiction hypothesis `|𝒮₄| ≤ ‖α‖²`.

From `hle`: `S₄·qu ≤ q·(‖α‖²·u) = (a+1)qu + q(q−1)a²`; substituting into `hcount` and using `u ≤ a²`
to bound the `u`-linear part `(aq+q+2a)u ≤ (aq+q+2a)a²` gives `(2a+1)^q − 1 ≤ (q+2)a³ + q²a² + 2qa`,
refuted by `nineElevenFive_arithmetic_contradiction`.  This is what the (9.11.6)–(9.11.8) coherence
contradiction (or directly the maximality refutation) feeds. -/
theorem nineElevenFive_refutation {q a u S4 N : ℕ} (hq : 3 ≤ q) (ha : 1 ≤ a) (hu : 1 ≤ u)
    (hua2 : u ≤ a * a)
    (hcount : S4 * (q * u) + 2 * a * q + 2 * a * u + 1 = (2 * a + 1) ^ q)
    (hnorm : N * u = (a + 1) * u + (q - 1) * a ^ 2)
    (hle : S4 ≤ N) : False := by
  refine nineElevenFive_arithmetic_contradiction hq ha ?_
  rw [← hcount, Nat.add_sub_cancel]
  -- `S₄·(q·u) ≤ (a+1)·q·u + q·(q−1)·a²`.
  have key1 : S4 * (q * u) ≤ (a + 1) * (q * u) + q * ((q - 1) * a ^ 2) := by
    calc S4 * (q * u) ≤ N * (q * u) := Nat.mul_le_mul_right _ hle
      _ = q * (N * u) := by ring
      _ = q * ((a + 1) * u + (q - 1) * a ^ 2) := by rw [hnorm]
      _ = (a + 1) * (q * u) + q * ((q - 1) * a ^ 2) := by ring
  -- `(a·q + q + 2·a)·u ≤ (a·q + q + 2·a)·a²` from `u ≤ a²`.
  have key2 : (a * q + q + 2 * a) * u ≤ (a * q + q + 2 * a) * (a * a) :=
    Nat.mul_le_mul_left _ hua2
  -- Clear the `q − 1` subtraction (`q ≥ 3`), then combine as a polynomial inequality.
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at key1 ⊢
  nlinarith [key1, key2, ha, hu, sq_nonneg a, Nat.zero_le q']

end FiveArithmetic

/-! ### (9.11.3) preamble: the `𝒳(H₀C)` character sum-of-squares

Book (9.11.3): the class equation `p^q·u = |Ū| + ∑_{χ ∈ 𝒳(H₀C)} χ(1)²` on the quotient `HŪ/(H₀C)`.
Its character-theoretic core — the sum `∑_{χ ∈ 𝒳(H₀C)} χ(1)²` — is the kernel-interval
degree-square sum (`sumDegreeSq_kernelInterval`, `NonInflatedDegreeSqInterval.lean`) at `N = H₀C`,
`K = H`: `𝒳(H₀C)` is exactly `{χ ∈ Irr(HU) | H₀C ⊆ ker χ, H ⊄ ker χ}` (the `xiOf` conditions), so
the sum equals `|HU/(H₀C)| − |HU/(H ⊔ H₀C)| = |HU/(H₀C)| − |HU/HC|`.  The second term
`|HU/HC| = [HU:HC] = u` is resolved here (`index_hcInHu`); the first term `|HU/(H₀C)| = p^q·u` is
the remaining index arithmetic (`|H|/|H₀| = p^q` × `[U:C] = u`), threaded by the (9.11.3)
`nineElevenThree_count`'s `hclass`. -/

section CharacterSumOfSquares

variable [Finite G] {M : Subgroup G}

/-- **Peterfalvi (9.11.3) quotient order**: the realized `H₀C` in `HU` has index `p^q·u`.

`[HU : H₀C] = [HU : HC]·[HC : H₀C] = u·p^q`, where `HC = H·C = hInHu ⊔ cInHu`:
* `[HU : HC] = u` (`index_hcInHu_eq_relindex_cInHu` ∘ `index_cInHu_subgroupOf_uInHu_eq_u`);
* `[HC : H₀C] = p^q` by the second isomorphism `HC/H₀C ≅ H/(H ⊓ H₀C) = H/H₀ = H̄`
  (`relIndex_sup_right` with `HC = H ⊔ H₀C`, and `H ⊓ H₀C = H₀` via
  `hInHu_inf_realizedH0supC_eq_realizedH0`), so `[HC : H₀C] = [H : H₀] = |H|/|H₀| = p^q`
  (`chief.quotient_order`).
This is the first term of the (9.11.3) class equation, folded into `sum_xiOf_H0C_degreeSq`. -/
theorem index_realizedH0supC_eq (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data)
    (chars : Section11CharacterData data chief) :
    Nat.card (↥(huSub data) ⧸
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      = chief.p ^ data.q * chars.u := by
  haveI : (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal :=
    (chiefFactor_H0supC_subgroupOf_normal chief).subgroupOf (huSub data)
  rw [← Subgroup.index_eq_card]
  have hHC : hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)
      = hInHu data ⊔ cInHu data chief := hInHu_sup_realizedH0supC chief
  have hle : ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)
      ≤ hInHu data ⊔ cInHu data chief := by rw [← hHC]; exact le_sup_right
  have hu : (hInHu data ⊔ cInHu data chief).index = chars.u :=
    (index_hcInHu_eq_relindex_cInHu data chief).trans
      (index_cInHu_subgroupOf_uInHu_eq_u data chief chars)
  -- `[HC : H₀C] = [H : H₀] = p^q` via the second isomorphism theorem.
  have hrel : (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).relIndex
      (hInHu data ⊔ cInHu data chief) = chief.p ^ data.q := by
    rw [← hHC, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_left,
      hInHu_inf_realizedH0supC_eq_realizedH0 chief]
    -- `[H : H₀] = |H|/|H₀| = p^q`.
    have hH0le : (chief.H0.subgroupOf M).subgroupOf (huSub data) ≤ hInHu data :=
      Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M chief.H0_lt_H.le)
    have hcard_H0r : Nat.card ↥((chief.H0.subgroupOf M).subgroupOf (huSub data))
        = Nat.card ↥chief.H0 := by
      have hH0M : chief.H0 ≤ M := chief.H0_lt_H.le.trans (H_le_M data)
      have hH0subM : chief.H0.subgroupOf M ≤ huSub data :=
        Subgroup.subgroupOf_mono M (chief.H0_lt_H.le.trans le_sup_left)
      calc Nat.card ↥((chief.H0.subgroupOf M).subgroupOf (huSub data))
          = Nat.card ↥(chief.H0.subgroupOf M) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH0subM).toEquiv
        _ = Nat.card ↥chief.H0 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH0M).toEquiv
    have hlag := Subgroup.index_mul_card
      (((chief.H0.subgroupOf M).subgroupOf (huSub data)).subgroupOf (hInHu data))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH0le).toEquiv, hcard_H0r,
      Nat.card_congr (hInHuEquivH data).toEquiv, chief.quotient_order] at hlag
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hlag
  rw [← Subgroup.relIndex_mul_index hle, hrel, hu]

open scoped Classical in
/-- **Peterfalvi (9.11.3), the `𝒳(H₀C)` character sum-of-squares (fully resolved: `p^q·u − u`).**

The kernel-interval degree-square sum (`sumDegreeSq_kernelInterval`) instantiated at the realized
`N = H₀C`, `K = H` inside `HU`: over `𝒳(H₀C) = {χ ∈ Irr(HU) | H₀C ⊆ ker, H ⊄ ker}`,
`∑ χ(1)² = |HU/(H₀C)| − |HU/(H ⊔ H₀C)|`, and `H ⊔ H₀C = HC` (`hInHu_sup_realizedH0supC`) with
`|HU/HC| = [HU:HC] = u` (`index_hcInHu`) and `|HU/(H₀C)| = p^q·u` (`index_realizedH0supC_eq`).
So `∑ χ(1)² = p^q·u − u`, the (9.11.3) class equation `|Ū| = |HU/H₀C| − ∑ χ(1)²` value fed to
`nineElevenThree_count`'s `hclass`. -/
theorem sum_xiOf_H0C_degreeSq (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data)
    (chars : Section11CharacterData data chief) :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter ↥(huSub data) =>
        (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :
            Set ↥(huSub data)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) ∧
        ¬ ((hInHu data : Set ↥(huSub data)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ))),
        ((χ : ClassFunction ↥(huSub data) ℂ) 1) ^ 2
      = (chief.p ^ data.q * chars.u : ℂ) - (chars.u : ℂ) := by
  haveI : (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal :=
    (chiefFactor_H0supC_subgroupOf_normal chief).subgroupOf (huSub data)
  haveI : (hInHu data).Normal := hInHu_normal data
  rw [OddOrder.RepresentationTheory.sumDegreeSq_kernelInterval
    (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) (hInHu data)]
  have hHC : hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)
      = hInHu data ⊔ cInHu data chief := hInHu_sup_realizedH0supC chief
  have hu : (hInHu data ⊔ cInHu data chief).index = chars.u :=
    (index_hcInHu_eq_relindex_cInHu data chief).trans
      (index_cInHu_subgroupOf_uInHu_eq_u data chief chars)
  -- First term `|HU/(H₀C)| = p^q·u` (`index_realizedH0supC_eq`); second `|HU/HC| = u`.
  congr 1
  · exact_mod_cast index_realizedH0supC_eq data chief chars
  · rw [hHC]; exact_mod_cast hu

end CharacterSumOfSquares

/-! ### (9.11.4): the norm reduction `‖α‖² = ‖γ‖² + 1`

Book (9.11.4): `α = γ − ψ₁` with `γ = Ind_{HU₁}^M 1` and `ψ₁ ∈ 𝒮₁` a norm-one irreducible.  Since
every constituent of the trivial-induced `γ` has `H ⊆ ker` while `ψ₁` does not, `⟨γ, ψ₁⟩ = 0`, and
the virtual-character norm splits `‖α‖² = ‖γ‖² + 1` (Coq `'[alpha] = '[gamma] + 1`,
`PFsection9.v:1905`).  The remaining `‖γ‖²` is the Mackey double-coset count
`(1/q)·Σ_{w∈W₁} |U₁ ∩ U₁ʷ| / |C| = a + (q−1)a²/u`, resolved through the (9.11.2) inertia identity
`U₁ ∩ U₁ʷ = C`; **this subsection isolates the character-side reduction, which is independent of
(9.11.2)**. -/

section NineElevenFour

/-- **Peterfalvi (9.11.4), the norm reduction `‖γ − ψ‖² = ‖γ‖² + 1`** (`cfnormBd`).

For a norm-one irreducible character `ψ` orthogonal to a class function `γ` (`⟨γ, ψ⟩ = 0`), the
difference `α = γ − ψ` has `⟨α, α⟩ = ⟨γ, γ⟩ + 1`: sesquilinearity expands
`⟨γ−ψ, γ−ψ⟩ = ⟨γ,γ⟩ − ⟨γ,ψ⟩ − ⟨ψ,γ⟩ + ⟨ψ,ψ⟩`, with `⟨γ,ψ⟩ = 0` (hypothesis),
`⟨ψ,γ⟩ = conj⟨γ,ψ⟩ = 0` (`inner_conj_symm`), and `⟨ψ,ψ⟩ = 1`
(`IsIrreducibleCharacter.inner_self_eq_one`).  This is the character-side step of (9.11.4): with
`γ = Ind_{HU₁}^M 1` and `ψ = ψ₁ ∈ 𝒮₁` (orthogonal because `H ⊆ ker` of every constituent of `γ`
but not of `ψ₁`), it gives `‖α‖² = ‖γ‖² + 1`; the remaining `‖γ‖²` is the (9.11.2)-gated Mackey
count.  Stated for an arbitrary character `γ` (no coherence/induction hypothesis), so it is reusable
wherever a norm-one irreducible is subtracted off orthogonally. -/
theorem cfnorm_sub_irreducible_orthogonal {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {γ ψ : ClassFunction Γ ℂ}
    (hψ : IsIrreducibleCharacter ψ) (hortho : ClassFunction.inner γ ψ = 0) :
    ClassFunction.inner (γ - ψ) (γ - ψ) = ClassFunction.inner γ γ + 1 := by
  have hψγ : ClassFunction.inner ψ γ = 0 := by
    rw [inner_conj_symm γ ψ, hortho, star_zero]
  have hψψ : ClassFunction.inner ψ ψ = 1 := by
    simpa using irreducibleCharacter_inner_eq_ite
      (⟨ψ, hψ⟩ : IrreducibleCharacter Γ) ⟨ψ, hψ⟩
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    hortho, hψγ, hψψ]
  ring

end NineElevenFour

/-! ### (9.11.2)–(9.11.5): the equality-branch refutation (assembly)

Book (9.11.2)–(9.11.8): under the (9.11.1) equality configuration (`p = 2a+1`, forced by
`nineElevenOne_configuration`'s `2a = p−1`), the coherence bound `|𝒮₄| ≤ ‖α‖²` — the negation of
"some conjugate pair from `𝒮₃` can be adjoined" — is impossible.  This subsection assembles the four
landed steps into one refutation, isolating the three remaining deep group/character inputs as named
hypotheses:

* **(9.11.2)** the inertia identity `C = K₁ ⊓ K₂` with `[U:K₁] = [U:K₂] = a` (`K₁ = C_U(S₀)`,
  `K₂ = C_U(S₀ʷ)`), giving `u ≤ a²` (`nineElevenTwo_u_le_a_sq`). Gated on the two-summand
  `θ`-character
  inertia computation (generalising `hcPsi_inertia_index_eq_u` from all summands to two).
* **(9.11.3)** the `HŪ/(H₀C)` class equation `hclass` (`|Ū| + Σχ(1)² = p^q·u`, its character side
  `sum_xiOf_H0C_degreeSq` landed) and the `W₁`-orbit split `hn` (`n = q·|𝒮₄| + (p−1)`), giving the
  cleared count (`nineElevenThree_count`).
* **(9.11.4)** the Mackey norm `hnorm` (`‖α‖²·u = (a+1)u + (q−1)a²`), whose `‖α‖² = ‖γ‖²+1` reduction
  is `cfnorm_sub_irreducible_orthogonal` and whose `‖γ‖²` is the non-normal-`HU₁` double-coset
  count.

The (9.11.5) exponential-beats-polynomial contradiction (`nineElevenFive_refutation`) closes it. -/

/-- **Peterfalvi (9.11.2)–(9.11.5), the equality-branch refutation.**

In the (9.11.1) equality configuration `p = 2a+1` (`hpeq`), the three deep inputs — the (9.11.2)
inertia identity (`hK₁`/`hK₂`/`hCinf`), the (9.11.3) class equation and `W₁`-orbit split
(`hclass`/`hn`), and the (9.11.4) Mackey norm (`hnorm`) — combine with the coherence bound
`|𝒮₄| ≤ ‖α‖²` (`hle`) to a contradiction.  This is the equality branch of the (9.11) caseA refuter:
`nineElevenOne_configuration` produces `hpeq` (and `C = U′`, `χdeg = u`) from the (9.11.1) squeeze,
and here (9.11.2)/(9.11.3)/(9.11.4) are chained through to `nineElevenFive_refutation`.  Only the
three named group/character inputs remain honest content; the arithmetic is fully discharged. -/
theorem nineElevenCaseA_equality_refutation [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (hq3 : 3 ≤ data.q) (hu : 1 ≤ chars.u) (hpeq : chief.p = 2 * caseA.a + 1)
    {K₁ K₂ : Subgroup G} (hK₁ : K₁.relIndex data.U = caseA.a)
    (hK₂ : K₂.relIndex data.U = caseA.a) (hCinf : chars.C = K₁ ⊓ K₂)
    {n S4 : ℕ}
    (hclass : chars.u + n * chars.u ^ 2 + data.q * (chief.p - 1) * chars.u
      = chief.p ^ data.q * chars.u)
    (hn : n = S4 * data.q + (chief.p - 1))
    {N : ℕ} (hnorm : N * chars.u = (caseA.a + 1) * chars.u + (data.q - 1) * caseA.a ^ 2)
    (hle : S4 ≤ N) : False := by
  have ha : 1 ≤ caseA.a := caseA.a_pos
  -- (9.11.2): `u ≤ a²` from the inertia identity `C = K₁ ⊓ K₂`.
  have hua2 : chars.u ≤ caseA.a * caseA.a := nineElevenTwo_u_le_a_sq caseA hK₁ hK₂ hCinf
  -- (9.11.3): the cleared count `|𝒮₄|·qu + (p−1)u + (p−1)q + 1 = p^q`.
  have hcount0 : S4 * (data.q * chars.u) + (chief.p - 1) * chars.u
      + (chief.p - 1) * data.q + 1 = chief.p ^ data.q := nineElevenThree_count hu hclass hn
  -- Substitute `p = 2a+1` to match `nineElevenFive_refutation`'s `(2a+1)^q` form.
  have hp1 : chief.p - 1 = 2 * caseA.a := by omega
  have hcount : S4 * (data.q * chars.u) + 2 * caseA.a * data.q + 2 * caseA.a * chars.u + 1
      = (2 * caseA.a + 1) ^ data.q := by
    rw [hp1, hpeq] at hcount0; omega
  -- (9.11.5): the exponential-beats-polynomial contradiction.
  exact nineElevenFive_refutation hq3 ha hu hua2 hcount hnorm hle

/-! ### (9.11.3): the `W₁`-orbit count split (issue 9083, Phase C)

Book (9.11.3): *"Let `n` be the number of irreducible characters of `𝒳(H₀C)` which are of degree
`u`.  By (9.11.1) and (9.8.b), `𝒳(H₀C)` contains `n` characters which are of degree `u` and
`q(p−1)u/a²` characters of degree `a`.  Thus `p^q·u = |H̄Ū| = |Ū| + ∑_{χ∈𝒳(H₀C)} χ(1)² =
u + nu² + q(p−1)u`. … By (9.8.b), `p−1` of these characters induce reducible characters of `M`.
Each of the others has `q` conjugates under `W₁`, which proves (9.11.3)."*  (Coq
`PFsection9.v:1791-1863`, `card_S4`.)

This subsection supplies the two deep (9.11.3) inputs of `nineElevenCaseA_equality_refutation` —
the class equation `hclass` and the `W₁`-orbit split `hn` — in one stroke, by proving `hclass`
directly at `n = |𝒮₄|·q + (p−1)` (so `hn` is definitional).  The engine is the Clifford fibration
of `𝒳(H₀C)` over `𝒮(H₀C)` under `Ind_{HU}^M` (`card_filter_induce_eq_index_inertia`): each fibre
is a full `M`-conjugation orbit of size `[M : I_M(χ)]`, and since `[M : HU] = q` is *prime* the
inertia index is `q` (irreducible member — the free `W₁`-orbit) or `1` (reducible member —
`W₁`-invariant source).  In the (9.11.1) equality configuration the three fibre classes carry the
degrees

* reducible members: `p − 1` of them (`reducible_count_sOf_H0C`), source degree `u` ((9.8.b),
  `caseA_reducible_induceHU_apply_one_eq_qu`);
* irreducible members in `𝒮₂`: degree `qa`, hence `q·|𝒮₁′|` sources of degree `a`, with
  `|𝒮₁′|·a² = (p−1)·[U:U′] = (p−1)·u` by the (9.8.d) count equality and `C = U′`
  (`relIndex_cSub_U_eq_u`);
* irreducible members outside `𝒮₂` (= `𝒮₄`): degree `qu`, hence `q·|𝒮₄|` sources of degree `u`;

and the kernel-interval sum `sum_xiOf_H0C_degreeSq` (`∑ χ(1)² = p^q·u − u`) closes the class
equation. -/

section NineElevenThreeOrbitSplit

variable [Finite G] {M : Subgroup G}

omit [Finite G] in
/-- **Kernel conditions are stable under ambient conjugation** (`cfker_conjg` at an invariant
subgroup).  For `N ≤ HU` whose underlying set is carried into itself by every `M`-conjugation
(`conjByMulEquiv`), the kernel condition `N ⊆ Ker χ` is invariant under `χ ↦ χ^g` (`g ∈ M`):
both directions of `subsetCharacterKernel_conjBy_iff`, transported along the invariance.  This is
what makes the `𝒳(H₀C)` filter conjugation-closed — the `hT` input of the (9.11.3) orbit count. -/
theorem subsetCharacterKernel_conjBy_iff_of_invariant (data : TypesIIIIIIVSetup M)
    (N : Subgroup ↥(huSub data))
    (hN : ∀ (w : ↥M) (x : ↥(huSub data)), x ∈ N →
      ClassFunction.conjByMulEquiv (G := ↥M) (H := huSub data) w x ∈ N)
    (g : ↥M) (χ : ClassFunction ↥(huSub data) ℂ) :
    ((N : Set ↥(huSub data)) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.conjBy (G := ↥M) (H := huSub data) g χ))
      ↔ (N : Set ↥(huSub data)) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ := by
  rw [subsetCharacterKernel_conjBy_iff]
  constructor
  · intro h x hx
    have h1 := h _ (hN g⁻¹ x hx)
    have h2 : ClassFunction.conjByMulEquiv (G := ↥M) (H := huSub data) g
        (ClassFunction.conjByMulEquiv (G := ↥M) (H := huSub data) g⁻¹ x) = x := by
      apply Subtype.ext
      rw [ClassFunction.conjByMulEquiv_apply, ClassFunction.conjByMulEquiv_apply]
      group
    rwa [h2] at h1
  · intro h x hx
    exact h (hN g x hx)

omit [Finite G] in
/-- **A realized `M`-normal subgroup of `HU` is `conjByMulEquiv`-stable**: for `Y ≤ G` with
`(Y.subgroupOf M) ◁ M`, the realization `(Y.subgroupOf M).subgroupOf HU` is carried into itself by
every `M`-conjugation of `HU`.  Supplies the invariance input of
`subsetCharacterKernel_conjBy_iff_of_invariant` at `N = H₀C`-realized
(`chiefFactor_H0supC_subgroupOf_normal`) and `N = H`-realized (`hSubgroupOfM_normal`). -/
theorem realized_conjByMulEquiv_mem (data : TypesIIIIIIVSetup M) {Y : Subgroup G}
    (hY : (Y.subgroupOf M).Normal) (w : ↥M) (x : ↥(huSub data))
    (hx : x ∈ (Y.subgroupOf M).subgroupOf (huSub data)) :
    ClassFunction.conjByMulEquiv (G := ↥M) (H := huSub data) w x
      ∈ (Y.subgroupOf M).subgroupOf (huSub data) := by
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have hval : ((ClassFunction.conjByMulEquiv (G := ↥M) (H := huSub data) w x :
      ↥(huSub data)) : ↥M) = w * ((x : ↥(huSub data)) : ↥M) * w⁻¹ :=
    ClassFunction.conjByMulEquiv_apply (G := ↥M) (H := huSub data) w x
  rw [hval]
  exact hY.conj_mem _ hx w

/-- **A source inducing irreducibly has inertia index `q`** (the free `W₁`-orbit of (9.11.3)).
If `Ind_{HU}^M χ` is irreducible then `‖Ind χ‖² = 1`, so `|I_M(χ)| = |HU|`
(`card_mul_inner_self_induce_eq_card_inertia`), and `[M : I_M(χ)]·|I_M(χ)| = |M| = q·|HU|` gives
`[M : I_M(χ)] = q` — the source has exactly `q` distinct `M`-conjugates ("each of the others has
`q` conjugates under `W₁`"). -/
theorem inertia_index_eq_q_of_induce_irreducible (data : TypesIIIIIIVSetup M)
    [Fintype ↥M] [Invertible (Nat.card ↥M : ℂ)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    (θ : IrreducibleCharacter ↥(huSub data))
    (hirr : IsIrreducibleCharacter (ClassFunction.induce (huSub data) θ.toClassFunction)) :
    (IrreducibleCharacter.inertia (G := ↥M) (H := huSub data) θ).index = data.q := by
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  have hone : ClassFunction.inner (ClassFunction.induce (huSub data) θ.toClassFunction)
      (ClassFunction.induce (huSub data) θ.toClassFunction) = 1 := by
    have h := irreducibleCharacter_inner_eq_ite
      (⟨_, hirr⟩ : IrreducibleCharacter ↥M) ⟨_, hirr⟩
    rwa [if_pos rfl] at h
  have hcard := card_mul_inner_self_induce_eq_card_inertia (G := ↥M) (H := huSub data) θ
  rw [hone, mul_one] at hcard
  have hcardN : Nat.card ↥(huSub data)
      = Nat.card ↥(IrreducibleCharacter.inertia (G := ↥M) (H := huSub data) θ) :=
    Nat.cast_inj.mp hcard
  have hchain : (IrreducibleCharacter.inertia (G := ↥M) (H := huSub data) θ).index
      * Nat.card ↥(huSub data) = data.q * Nat.card ↥(huSub data) := by
    calc (IrreducibleCharacter.inertia (G := ↥M) (H := huSub data) θ).index
        * Nat.card ↥(huSub data)
        = (IrreducibleCharacter.inertia (G := ↥M) (H := huSub data) θ).index
          * Nat.card ↥(IrreducibleCharacter.inertia (G := ↥M) (H := huSub data) θ) := by
          rw [← hcardN]
      _ = Nat.card ↥M := Subgroup.index_mul_card _
      _ = (huSub data).index * Nat.card ↥(huSub data) := (Subgroup.index_mul_card _).symm
      _ = data.q * Nat.card ↥(huSub data) := by rw [huSub_index_eq_q]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hchain

/-- **A source inducing reducibly has inertia index `1`** (the `W₁`-invariant sources of
(9.11.3), "`p−1` of these characters induce reducible characters of `M`" — each reducible member
has a *single* source).  `HU ≤ I_M(χ)` always (`subgroup_le_inertia`), so `[M : I_M(χ)]` divides
`[M : HU] = q`; `q` prime leaves `1` or `q`, and index `q` would force `I_M(χ) = HU`, making
`Ind_{HU}^M χ` irreducible (`isIrreducibleCharacter_induce_of_inertia_eq`) — contradiction. -/
theorem inertia_index_eq_one_of_induce_reducible (data : TypesIIIIIIVSetup M)
    [Fintype ↥M] [Invertible (Nat.card ↥M : ℂ)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    (θ : IrreducibleCharacter ↥(huSub data))
    (hred : ¬ IsIrreducibleCharacter (ClassFunction.induce (huSub data) θ.toClassFunction)) :
    (IrreducibleCharacter.inertia (G := ↥M) (H := huSub data) θ).index = 1 := by
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  have hqp : (data.q).Prime := data.nontrivial.2.1
  have hle : huSub data ≤ IrreducibleCharacter.inertia (G := ↥M) (H := huSub data) θ :=
    IrreducibleCharacter.subgroup_le_inertia θ
  have hdvd : (IrreducibleCharacter.inertia (G := ↥M) (H := huSub data) θ).index
      ∣ (huSub data).index := Subgroup.index_dvd_of_le hle
  rw [huSub_index_eq_q] at hdvd
  rcases hqp.eq_one_or_self_of_dvd _ hdvd with h1 | hq'
  · exact h1
  · exfalso
    have hri := Subgroup.relIndex_mul_index hle
    rw [hq', huSub_index_eq_q] at hri
    have h1' : (huSub data).relIndex
        (IrreducibleCharacter.inertia (G := ↥M) (H := huSub data) θ) = 1 :=
      Nat.eq_of_mul_eq_mul_right hqp.pos (by rw [hri, one_mul])
    have heq : IrreducibleCharacter.inertia (G := ↥M) (H := huSub data) θ = huSub data :=
      le_antisymm (Subgroup.relIndex_eq_one.mp h1') hle
    exact hred (isIrreducibleCharacter_induce_of_inertia_eq θ heq)

open scoped Classical in
/-- **Peterfalvi (9.11.3), the `W₁`-orbit count split** (issue 9083 Phase C).

In the (9.11.1) equality configuration — the degree-`qa` subfamily of `𝒮(H₀U′)` inside `𝒮₂`
(`hS₁'sub`), every `𝒮(H₀C)`-member outside `𝒮₂` of degree `qu` (`hS3deg`), every `𝒮₂`-member of
degree `qa` (`hS2deg`, the Phase-E `𝒮₂ = 𝒮₁` extraction), `C = U′` (`hCU`), and the (9.8.d) count
equality (`hcount`) — the `𝒳(H₀C)` class equation holds with the character count `n` already
split into `W₁`-orbits:

`u + (|𝒮₄|·q + (p−1))·u² + q·(p−1)·u = p^q·u`,

where `𝒮₄ = {φ ∈ 𝒮(H₀C) | φ irreducible, φ ∉ 𝒮₂}` (the book's irreducible members of
`𝒮₃ ∩ 𝒮(H₀C)`; `𝒮(H₀C) ⊆ 𝒮(H₀C′)` makes "`∈ 𝒮₃`" the same as "`∉ 𝒮₂`").  This is
`nineElevenCaseA_equality_refutation`'s `hclass` instantiated at `n = |𝒮₄|·q + (p−1)`, so its
`hn` is definitional.

Proof: fibre `𝒳(H₀C)` over `𝒮(H₀C)` under `Ind_{HU}^M`.  Fibres are full `M`-conjugation orbits
(`card_filter_induce_eq_index_inertia`; the filter is conjugation-closed since `H₀C`-realized and
`H`-realized are `M`-normal), of size `1` over reducible members and `q` over irreducible ones
(`inertia_index_eq_one_of_induce_reducible` / `inertia_index_eq_q_of_induce_irreducible`).  The
three member classes have `p − 1` (`reducible_count_sOf_H0C`), `|𝒮₁′|`, and `|𝒮₄|` members with
source degrees `u` ((9.8.b) `caseA_reducible_induceHU_apply_one_eq_qu`), `a`, and `u`
respectively; `|𝒮₁′|·a² = (p−1)·[U:U′] = (p−1)·u` (`hcount`, `relIndex_cSub_U_eq_u` along
`C = U′`); and `∑_{𝒳(H₀C)} χ(1)² = p^q·u − u` (`sum_xiOf_H0C_degreeSq`) closes the ledger. -/
theorem nineElevenThree_orbit_split (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {S₂ : Set (ClassFunction ↥M ℂ)}
    (hS₁'sub : {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
      χ 1 = ((data.q * caseA.a : ℕ) : ℂ)} ⊆ S₂)
    (hS3deg : ∀ χ ∈ sOf data (chief.H0 ⊔ cSub data chief), χ ∉ S₂ →
      χ 1 = ((data.q * chars.u : ℕ) : ℂ))
    (hS2deg : ∀ χ ∈ S₂, χ 1 = ((data.q * caseA.a : ℕ) : ℂ))
    (hCU : cSub data chief = uprimeSub data)
    (hcount : {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
        χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
      = (chief.p - 1) * ((uprimeSub data).relIndex data.U)) :
    chars.u + ({φ ∈ sOf data (chief.H0 ⊔ cSub data chief) |
          IsIrreducibleCharacter φ ∧ φ ∉ S₂}.ncard * data.q + (chief.p - 1)) * chars.u ^ 2
        + data.q * (chief.p - 1) * chars.u
      = chief.p ^ data.q * chars.u := by
  haveI := huSub_normal data
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hqp : (data.q).Prime := data.nontrivial.2.1
  have hq0 : (data.q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hqp.pos.ne'
  -- ── the source family `T = 𝒳(H₀C)`, as the `sum_xiOf_H0C_degreeSq` filter
  set T : Finset (IrreducibleCharacter ↥(huSub data)) :=
    Finset.univ.filter (fun χ : IrreducibleCharacter ↥(huSub data) =>
      (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :
          Set ↥(huSub data)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) ∧
      ¬ ((hInHu data : Set ↥(huSub data)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ)))
    with hT_def
  have hT_mem : ∀ θ : IrreducibleCharacter ↥(huSub data),
      θ ∈ T ↔ θ ∈ xiOf data (chief.H0 ⊔ cSub data chief) := by
    intro θ
    rw [hT_def, Finset.mem_filter]
    constructor
    · rintro ⟨-, hker, hH⟩
      exact ⟨hH, hker⟩
    · rintro ⟨hH, hker⟩
      exact ⟨Finset.mem_univ _, hker, hH⟩
  -- ── `T` is `M`-conjugation-closed (both kernel conditions are `M`-normal)
  have hH0Cnorm : ((chief.H0 ⊔ cSub data chief).subgroupOf M).Normal :=
    chiefFactor_H0supC_subgroupOf_normal chief
  have hTconj : ∀ θ ∈ T, ∀ g : ↥M,
      IrreducibleCharacter.conjBy (G := ↥M) (H := huSub data) g θ ∈ T := by
    intro θ hθ g
    rw [hT_def, Finset.mem_filter] at hθ ⊢
    obtain ⟨-, hker, hH⟩ := hθ
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [IrreducibleCharacter.coe_conjBy]
      exact (subsetCharacterKernel_conjBy_iff_of_invariant data _
        (realized_conjByMulEquiv_mem data hH0Cnorm) g _).mpr hker
    · rw [IrreducibleCharacter.coe_conjBy]
      intro hcon
      exact hH ((subsetCharacterKernel_conjBy_iff_of_invariant data _
        (realized_conjByMulEquiv_mem data (hSubgroupOfM_normal data)) g _).mp hcon)
  -- ── membership dictionary: `T`-sources induce into `𝒮(H₀C)`
  have hmem_sOf : ∀ θ ∈ T, ClassFunction.induce (huSub data) θ.toClassFunction
      ∈ sOf data (chief.H0 ⊔ cSub data chief) := fun θ hθ =>
    ⟨θ, (hT_mem θ).mp hθ, (induceHU_eq_induce data _).symm⟩
  -- ── generic fibre count: a fibre-closed part of `T` with constant inertia index `c`
  --    has cardinality `|image|·c`
  have hfib_card : ∀ (T' : Finset (IrreducibleCharacter ↥(huSub data))) (c : ℕ),
      T' ⊆ T →
      (∀ θ θ₀ : IrreducibleCharacter ↥(huSub data),
        ClassFunction.induce (huSub data) θ.toClassFunction
          = ClassFunction.induce (huSub data) θ₀.toClassFunction →
        θ ∈ T → θ₀ ∈ T' → θ ∈ T') →
      (∀ θ₀ ∈ T', (IrreducibleCharacter.inertia (G := ↥M) (H := huSub data) θ₀).index = c) →
      T'.card = (T'.image
        (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction)).card * c := by
    intro T' c hsub hfibclosed hc
    calc T'.card
        = ∑ φ ∈ T'.image (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction),
            (T'.filter (fun θ =>
              ClassFunction.induce (huSub data) θ.toClassFunction = φ)).card :=
          Finset.card_eq_sum_card_image _ _
      _ = ∑ _φ ∈ T'.image (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction),
            c := by
          refine Finset.sum_congr rfl fun φ hφ => ?_
          obtain ⟨θ₀, hθ₀T', hθ₀eq⟩ := Finset.mem_image.mp hφ
          have hfib : T'.filter (fun θ =>
              ClassFunction.induce (huSub data) θ.toClassFunction = φ)
              = T.filter (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction
                  = ClassFunction.induce (huSub data) θ₀.toClassFunction) := by
            subst hθ₀eq
            ext θ
            rw [Finset.mem_filter, Finset.mem_filter]
            constructor
            · rintro ⟨hθT', heq⟩
              exact ⟨hsub hθT', heq⟩
            · rintro ⟨hθT, heq⟩
              exact ⟨hfibclosed θ θ₀ heq hθT hθ₀T', heq⟩
          rw [hfib, card_filter_induce_eq_index_inertia T hTconj θ₀ (hsub hθ₀T'),
            hc θ₀ hθ₀T']
      _ = (T'.image
            (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction)).card * c := by
          rw [Finset.sum_const, smul_eq_mul]
  -- ── generic image dictionary: the members of a part cut out by a member predicate `Q`
  have himg : ∀ (T' : Finset (IrreducibleCharacter ↥(huSub data)))
      (Q : ClassFunction ↥M ℂ → Prop),
      T' ⊆ T →
      (∀ θ ∈ T, (θ ∈ T' ↔ Q (ClassFunction.induce (huSub data) θ.toClassFunction))) →
      ((T'.image (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction) :
          Finset (ClassFunction ↥M ℂ)) : Set (ClassFunction ↥M ℂ))
        = {φ ∈ sOf data (chief.H0 ⊔ cSub data chief) | Q φ} := by
    intro T' Q hsub hQmem
    ext φ
    constructor
    · intro hφ
      rw [Finset.mem_coe, Finset.mem_image] at hφ
      obtain ⟨θ, hθT', rfl⟩ := hφ
      exact ⟨hmem_sOf θ (hsub hθT'), (hQmem θ (hsub hθT')).mp hθT'⟩
    · rintro ⟨⟨θ, hθxi, hφeq⟩, hQ⟩
      rw [induceHU_eq_induce data] at hφeq
      subst hφeq
      rw [Finset.mem_coe, Finset.mem_image]
      have hθT : θ ∈ T := (hT_mem θ).mpr hθxi
      exact ⟨θ, (hQmem θ hθT).mpr hQ, rfl⟩
  -- ── source degrees from member degrees (`q` cancels)
  have hdeg_of_member : ∀ (θ : IrreducibleCharacter ↥(huSub data)) (d : ℕ),
      ClassFunction.induce (huSub data) θ.toClassFunction 1 = ((data.q * d : ℕ) : ℂ) →
      (θ : ClassFunction ↥(huSub data) ℂ) 1 = (d : ℂ) := by
    intro θ d hmem
    rw [← induceHU_eq_induce data, induceHU_apply_one_eq_q_mul] at hmem
    apply mul_left_cancel₀ hq0
    rw [hmem]
    push_cast
    ring
  -- ── the three parts of `T`
  have hred_of : ∀ θ ∈ T, ¬ IsIrreducibleCharacter
      (ClassFunction.induce (huSub data) θ.toClassFunction) →
      (θ : ClassFunction ↥(huSub data) ℂ) 1 = (chars.u : ℂ) := by
    intro θ hθ hred
    refine hdeg_of_member θ chars.u ?_
    exact caseA_reducible_induceHU_apply_one_eq_qu caseA hG _
      (sOf_antitone data le_sup_left (hmem_sOf θ hθ)) hred
  have hi4_of : ∀ θ ∈ T, ClassFunction.induce (huSub data) θ.toClassFunction ∉ S₂ →
      (θ : ClassFunction ↥(huSub data) ℂ) 1 = (chars.u : ℂ) := by
    intro θ hθ hnot
    exact hdeg_of_member θ chars.u (hS3deg _ (hmem_sOf θ hθ) hnot)
  have hi2_of : ∀ (θ : IrreducibleCharacter ↥(huSub data)),
      ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂ →
      (θ : ClassFunction ↥(huSub data) ℂ) 1 = (caseA.a : ℂ) := by
    intro θ hin
    exact hdeg_of_member θ caseA.a (hS2deg _ hin)
  -- ── the class equation, folded to `T`
  have hsum := sum_xiOf_H0C_degreeSq data chief chars
  rw [← hT_def] at hsum
  -- split `T` by member irreducibility, then the irreducible part by `𝒮₂`-membership
  have hA := Finset.sum_filter_add_sum_filter_not T
    (fun θ => IsIrreducibleCharacter (ClassFunction.induce (huSub data) θ.toClassFunction))
    (fun χ => ((χ : ClassFunction ↥(huSub data) ℂ) 1) ^ 2)
  have hB := Finset.sum_filter_add_sum_filter_not
    (T.filter (fun θ => IsIrreducibleCharacter
      (ClassFunction.induce (huSub data) θ.toClassFunction)))
    (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂)
    (fun χ => ((χ : ClassFunction ↥(huSub data) ℂ) 1) ^ 2)
  -- ── part `𝒳red`: the `p − 1` sources of the reducible members, degree `u`, fibre `1`
  have hcard_red : (T.filter (fun θ => ¬ IsIrreducibleCharacter
      (ClassFunction.induce (huSub data) θ.toClassFunction))).card = chief.p - 1 := by
    have h1 := hfib_card (T.filter (fun θ => ¬ IsIrreducibleCharacter
        (ClassFunction.induce (huSub data) θ.toClassFunction))) 1
      (Finset.filter_subset _ _)
      (fun θ θ₀ heq hθT hθ₀ => by
        rw [Finset.mem_filter] at hθ₀ ⊢
        exact ⟨hθT, by rw [heq]; exact hθ₀.2⟩)
      (fun θ₀ hθ₀ => inertia_index_eq_one_of_induce_reducible data θ₀
        (Finset.mem_filter.mp hθ₀).2)
    rw [mul_one] at h1
    rw [h1, ← Set.ncard_coe_finset,
      himg _ (fun φ => ¬ IsIrreducibleCharacter φ) (Finset.filter_subset _ _)
        (fun θ hθ => by rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hθ, h⟩⟩)]
    have hcnt := reducible_count_sOf_H0C hG chars
    rw [show chars.C = cSub data chief from rfl] at hcnt
    exact hcnt
  have hvred : ∑ χ ∈ T.filter (fun θ => ¬ IsIrreducibleCharacter
      (ClassFunction.induce (huSub data) θ.toClassFunction)),
      ((χ : ClassFunction ↥(huSub data) ℂ) 1) ^ 2
      = ((chief.p - 1 : ℕ) : ℂ) * ((chars.u : ℕ) : ℂ) ^ 2 := by
    rw [show ∑ χ ∈ T.filter (fun θ => ¬ IsIrreducibleCharacter
        (ClassFunction.induce (huSub data) θ.toClassFunction)),
        ((χ : ClassFunction ↥(huSub data) ℂ) 1) ^ 2
        = ∑ _χ ∈ T.filter (fun θ => ¬ IsIrreducibleCharacter
            (ClassFunction.induce (huSub data) θ.toClassFunction)),
          ((chars.u : ℕ) : ℂ) ^ 2 from
      Finset.sum_congr rfl fun θ hθ => by
        rw [Finset.mem_filter] at hθ
        rw [hred_of θ hθ.1 hθ.2]]
    rw [Finset.sum_const, nsmul_eq_mul, hcard_red]
  -- ── part `𝒳₂`: sources of the irreducible `𝒮₂`-members, degree `a`, fibre `q`
  have hcard_i2 : ((T.filter (fun θ => IsIrreducibleCharacter
        (ClassFunction.induce (huSub data) θ.toClassFunction))).filter
      (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂)).card
      = {φ ∈ sOf data (chief.H0 ⊔ cSub data chief) |
          IsIrreducibleCharacter φ ∧ φ ∈ S₂}.ncard * data.q := by
    have hsub : (T.filter (fun θ => IsIrreducibleCharacter
        (ClassFunction.induce (huSub data) θ.toClassFunction))).filter
        (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂) ⊆ T :=
      fun θ hθ => Finset.filter_subset _ _ ((Finset.filter_subset _ _) hθ)
    have hmem' : ∀ θ ∈ T, (θ ∈ (T.filter (fun θ => IsIrreducibleCharacter
        (ClassFunction.induce (huSub data) θ.toClassFunction))).filter
        (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂)
        ↔ (IsIrreducibleCharacter (ClassFunction.induce (huSub data) θ.toClassFunction) ∧
          ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂)) := by
      intro θ hθ
      rw [Finset.mem_filter, Finset.mem_filter]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hθ, h.1⟩, h.2⟩⟩
    have h1 := hfib_card _ data.q hsub
      (fun θ θ₀ heq hθT hθ₀ => by
        rw [hmem' θ hθT]
        have h₀ := (hmem' θ₀ (hsub hθ₀)).mp hθ₀
        rw [heq]
        exact h₀)
      (fun θ₀ hθ₀ => inertia_index_eq_q_of_induce_irreducible data θ₀
        ((hmem' θ₀ (hsub hθ₀)).mp hθ₀).1)
    rw [h1, ← Set.ncard_coe_finset,
      himg _ (fun φ => IsIrreducibleCharacter φ ∧ φ ∈ S₂) hsub hmem']
  have hvi2 : ∑ χ ∈ (T.filter (fun θ => IsIrreducibleCharacter
        (ClassFunction.induce (huSub data) θ.toClassFunction))).filter
      (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂),
      ((χ : ClassFunction ↥(huSub data) ℂ) 1) ^ 2
      = (({φ ∈ sOf data (chief.H0 ⊔ cSub data chief) |
          IsIrreducibleCharacter φ ∧ φ ∈ S₂}.ncard * data.q : ℕ) : ℂ)
        * ((caseA.a : ℕ) : ℂ) ^ 2 := by
    rw [show ∑ χ ∈ (T.filter (fun θ => IsIrreducibleCharacter
        (ClassFunction.induce (huSub data) θ.toClassFunction))).filter
        (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂),
        ((χ : ClassFunction ↥(huSub data) ℂ) 1) ^ 2
        = ∑ _χ ∈ (T.filter (fun θ => IsIrreducibleCharacter
            (ClassFunction.induce (huSub data) θ.toClassFunction))).filter
          (fun θ => ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂),
          ((caseA.a : ℕ) : ℂ) ^ 2 from
      Finset.sum_congr rfl fun θ hθ => by
        rw [Finset.mem_filter] at hθ
        rw [hi2_of θ hθ.2]]
    rw [Finset.sum_const, nsmul_eq_mul, hcard_i2]
  -- ── part `𝒳₄`: sources of the `𝒮₄`-members, degree `u`, fibre `q`
  have hcard_i4 : ((T.filter (fun θ => IsIrreducibleCharacter
        (ClassFunction.induce (huSub data) θ.toClassFunction))).filter
      (fun θ => ¬ ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂)).card
      = {φ ∈ sOf data (chief.H0 ⊔ cSub data chief) |
          IsIrreducibleCharacter φ ∧ φ ∉ S₂}.ncard * data.q := by
    have hsub : (T.filter (fun θ => IsIrreducibleCharacter
        (ClassFunction.induce (huSub data) θ.toClassFunction))).filter
        (fun θ => ¬ ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂) ⊆ T :=
      fun θ hθ => Finset.filter_subset _ _ ((Finset.filter_subset _ _) hθ)
    have hmem' : ∀ θ ∈ T, (θ ∈ (T.filter (fun θ => IsIrreducibleCharacter
        (ClassFunction.induce (huSub data) θ.toClassFunction))).filter
        (fun θ => ¬ ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂)
        ↔ (IsIrreducibleCharacter (ClassFunction.induce (huSub data) θ.toClassFunction) ∧
          ClassFunction.induce (huSub data) θ.toClassFunction ∉ S₂)) := by
      intro θ hθ
      rw [Finset.mem_filter, Finset.mem_filter]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hθ, h.1⟩, h.2⟩⟩
    have h1 := hfib_card _ data.q hsub
      (fun θ θ₀ heq hθT hθ₀ => by
        rw [hmem' θ hθT]
        have h₀ := (hmem' θ₀ (hsub hθ₀)).mp hθ₀
        rw [heq]
        exact h₀)
      (fun θ₀ hθ₀ => inertia_index_eq_q_of_induce_irreducible data θ₀
        ((hmem' θ₀ (hsub hθ₀)).mp hθ₀).1)
    rw [h1, ← Set.ncard_coe_finset,
      himg _ (fun φ => IsIrreducibleCharacter φ ∧ φ ∉ S₂) hsub hmem']
  have hvi4 : ∑ χ ∈ (T.filter (fun θ => IsIrreducibleCharacter
        (ClassFunction.induce (huSub data) θ.toClassFunction))).filter
      (fun θ => ¬ ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂),
      ((χ : ClassFunction ↥(huSub data) ℂ) 1) ^ 2
      = (({φ ∈ sOf data (chief.H0 ⊔ cSub data chief) |
          IsIrreducibleCharacter φ ∧ φ ∉ S₂}.ncard * data.q : ℕ) : ℂ)
        * ((chars.u : ℕ) : ℂ) ^ 2 := by
    rw [show ∑ χ ∈ (T.filter (fun θ => IsIrreducibleCharacter
        (ClassFunction.induce (huSub data) θ.toClassFunction))).filter
        (fun θ => ¬ ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂),
        ((χ : ClassFunction ↥(huSub data) ℂ) 1) ^ 2
        = ∑ _χ ∈ (T.filter (fun θ => IsIrreducibleCharacter
            (ClassFunction.induce (huSub data) θ.toClassFunction))).filter
          (fun θ => ¬ ClassFunction.induce (huSub data) θ.toClassFunction ∈ S₂),
          ((chars.u : ℕ) : ℂ) ^ 2 from
      Finset.sum_congr rfl fun θ hθ => by
        rw [Finset.mem_filter] at hθ
        rw [hi4_of θ (Finset.filter_subset _ _ hθ.1) hθ.2]]
    rw [Finset.sum_const, nsmul_eq_mul, hcard_i4]
  -- ── the (9.8.d) count equality at `C = U′`: `|𝒮₁′|·a² = (p−1)·u`
  have hcount' : {φ ∈ sOf data (chief.H0 ⊔ cSub data chief) |
      IsIrreducibleCharacter φ ∧ φ ∈ S₂}.ncard * (caseA.a * caseA.a)
      = (chief.p - 1) * chars.u := by
    have hfam : sOf data (chief.H0 ⊔ cSub data chief)
        = sOf data (chief.H0 ⊔ uprimeSub data) := by rw [hCU]
    have hset : {φ ∈ sOf data (chief.H0 ⊔ cSub data chief) |
        IsIrreducibleCharacter φ ∧ φ ∈ S₂}
        = {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
            IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)} := by
      ext φ
      constructor
      · rintro ⟨hs, hirr, hS⟩
        exact ⟨hfam ▸ hs, hirr, hS2deg φ hS⟩
      · rintro ⟨hs, hirr, hdeg⟩
        exact ⟨hfam.symm ▸ hs, hirr, hS₁'sub ⟨hs, hirr, hdeg⟩⟩
    rw [hset, hcount, ← hCU, relIndex_cSub_U_eq_u chars]
  -- ── assemble in `ℂ`, then descend to `ℕ`
  have hcC : (({φ ∈ sOf data (chief.H0 ⊔ cSub data chief) |
      IsIrreducibleCharacter φ ∧ φ ∈ S₂}.ncard * (caseA.a * caseA.a) : ℕ) : ℂ)
      = (((chief.p - 1) * chars.u : ℕ) : ℂ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℂ)) hcount'
  have hgoalC : ((chars.u + ({φ ∈ sOf data (chief.H0 ⊔ cSub data chief) |
        IsIrreducibleCharacter φ ∧ φ ∉ S₂}.ncard * data.q + (chief.p - 1)) * chars.u ^ 2
        + data.q * (chief.p - 1) * chars.u : ℕ) : ℂ)
      = ((chief.p ^ data.q * chars.u : ℕ) : ℂ) := by
    push_cast at hsum hA hB hvred hvi2 hvi4 hcC ⊢
    linear_combination hsum + hA + hB - hvi2 - hvi4 - hvred - (data.q : ℂ) * hcC
  exact Nat.cast_inj.mp hgoalC

end NineElevenThreeOrbitSplit

end OddOrder.Peterfalvi.S11

