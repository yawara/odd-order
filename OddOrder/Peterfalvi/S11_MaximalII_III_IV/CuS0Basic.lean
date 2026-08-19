import OddOrder.Peterfalvi.S11_MaximalII_III_IV.InertiaLift

/-!
# Peterfalvi §11 — `C_U(S₀)`: opening layer

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
-/

namespace OddOrder.Peterfalvi.S11
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}



/-! ### (9.9.a) inertia lift: `I_{HU}(θ₀) = HC`

For the (9.9.a) Clifford degree we need the inertia in `HU` of the realized chief-factor character
`θ₀ = compHom (hInHuEquivH) (compHom (mk' N) θ̄)` to be exactly `HC = hInHu ⊔ cInHu`.  The two
inclusions:

* `cInHu ≤ I(θ₀)` (`cInHu_le_inertia`): `C = C_U(H̄)` acts trivially on the chief factor, so it
  fixes
  `θ₀` (the *easy* direction — `compHom_typeP_conjAction_inflation` + `quotientMulAutHom = 1` on the
  kernel `cSub`);
* `I(θ₀) ⊓ uInHu ≤ cInHu` (`inertia_inf_uInHu_le_cInHu`): the *hard* direction, exactly
  `caseB_inertia_realized` (any `U`-element fixing `θ₀` acts trivially on `H̄`).

Together with `H ≤ I(θ₀)` (automatic) and `H ⊔ U = ⊤`, the modular decomposition
`I(θ₀) = H ⊔ (I(θ₀) ⊓ U)` gives `I(θ₀) = HC` (`inertia_eq_hcInHu`). -/

/-- **`C ≤ I_{HU}(θ₀)`**: `C = C_U(H̄)` fixes the realized chief-factor character `θ₀` (it acts
trivially on `H̄`, so `quotientMulAutHom = 1` on `cSub = ker(uActionHom)`, and the inflation is
unchanged).  The easy half of the (9.9.a) inertia lift. -/
theorem cInHu_le_inertia [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)} :
    cInHu data chief ≤ ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
  intro c hc
  rw [ClassFunction.mem_inertia]
  have hcG : ((c : ↥M) : G) ∈ cSub data chief := by
    simp only [cInHu, Subgroup.mem_subgroupOf] at hc; exact hc
  simp only [cSub, Subgroup.mem_map] at hcG
  obtain ⟨w, ⟨ĉ', hĉ', hĉ'w⟩, hwc⟩ := hcG
  have hq1 : quotientMulAutHom chief.N_aInvariant w = 1 := by rw [← hĉ'w]; exact hĉ'
  have hag : ((c : ↥M) : G) = (w : G) := hwc.symm
  rw [conjBy_compHom_hInHuEquivH data w c hag, compHom_typeP_conjAction_inflation, hq1]
  rfl

/-- **`I(θ₀) ⊓ U ≤ C`, parametrized over the realized stabilizer-triviality `hrealized`.**  The
case-agnostic part of the hard inertia direction: any `g ∈ I(θ₀) ⊓ U` realizes as a `U`-element `a`
whose `θ₀`-fixing (`mem_inertia`) feeds `hrealized` to conclude `a ∈ ker(uActionHom) = C`.  Case (b)
supplies `hrealized` as `caseB_inertia_realized`; case (a) via the non-Galois analog. -/
theorem inertia_inf_uInHu_le_cInHu_of_realized [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hrealized : ∀ (a : ↥((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U)) (g : ↥(huSub data)),
        (((g : ↥M) : G) = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G)) →
        ClassFunction.conjBy g (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
            (ClassFunction.compHom (QuotientGroup.mk' chief.N)
              (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
          = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) →
        ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) a = 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cInHu data chief := by
  rintro g ⟨hgin, hgu⟩
  have hgU : ((g : ↥M) : G) ∈ data.typeP.U := by
    simp only [uInHu] at hgu; exact hgu
  have hgUW1 : ((g : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hgU
  set a : ↥((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U) :=
    ⟨⟨((g : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  have hag : ((g : ↥M) : G)
      = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  have hker : a ∈ (uActionHom data chief).ker :=
    hrealized a g hag (ClassFunction.mem_inertia.mp hgin)
  simp only [cInHu, Subgroup.mem_subgroupOf, cSub, Subgroup.mem_map]
  exact ⟨_, ⟨a, hker, rfl⟩, rfl⟩

theorem inertia_inf_uInHu_le_cInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθbar : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cInHu data chief :=
  inertia_inf_uInHu_le_cInHu_of_realized data chief (caseB_inertia_realized hcaseB hθbar)

/-- **Peterfalvi (9.8.d) hard inertia direction: `I(θ₁₀) ⊓ U ≤ C_U(S₀)`.**  For a chief-factor
character `θ₁` nontrivial on the orbit generator `S₀ = H₁` (`hreg` on `caseA.S0`), any `U`-element
in
the inertia of the inflation `θ₁₀` centralizes `S₀`, hence lies in `C_U(S₀) = cuInHu`.  The
single-factor analog of `inertia_inf_uInHu_le_cInHu`: same `conjBy → compHom → mk'`-injective
unwrapping (`conjBy_compHom_hInHuEquivH`, `compHom_typeP_conjAction_inflation`,
`compHom_injective_of_surjective`) as `caseB_inertia_realized_of_charInertia` /
`caseB_char_inertia_inflation_of_core`, but the stabilizer-triviality core is
`chiefFactor_caseA_char_inertia_single` (`aInvariantRestrictAut S₀ a = 1`, i.e. `a ∈ C_U(S₀)`), not
`uActionHom a = 1` (`a ∈ C`).  This is the honest degree-`qa` inertia: `θ₁` is faithful only on the
single summand `S₀`, so its inertia is `H·C_U(S₀)` (index `a`), not `HC` (index `u`). -/
theorem inertia_inf_uInHu_le_cuInHu [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∃ x ∈ caseA.S0,
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cuInHu caseA := by
  rintro g ⟨hgin, hgu⟩
  have hgU : ((g : ↥M) : G) ∈ data.typeP.U := by
    simp only [uInHu] at hgu; exact hgu
  have hgUW1 : ((g : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hgU
  set a : ↥((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U) :=
    ⟨⟨((g : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  have hag : ((g : ↥M) : G)
      = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  -- Unwrap the `conjBy`-fixing to the abstract `uActionHom`-invariance of `θbar` (as in the
  -- case-(b) plumbing), then apply the single-factor core to get `aInvariantRestrictAut S₀ a = 1`.
  have hfix := ClassFunction.mem_inertia.mp hgin
  rw [conjBy_compHom_hInHuEquivH data
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype a)
    g hag] at hfix
  -- strip the `hInHuEquivH` layer (`compHom_injective` on the surjective inflation iso), …
  have hfix1 := ClassFunction.compHom_injective_of_surjective (hInHuEquivH data).surjective hfix
  -- … then the `typeP_conjAction` layer (`mk'` surjective), leaving abstract `φ`-invariance.
  rw [compHom_typeP_conjAction_inflation] at hfix1
  have hfix2 := ClassFunction.compHom_injective_of_surjective
    (QuotientGroup.mk'_surjective chief.N) hfix1
  have hinv : ∀ x, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ((uActionHom data chief) a x)
      = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x := by
    intro x
    exact congrFun (congrArg (fun f : ClassFunction (↥data.H ⧸ chief.N) ℂ =>
      (f : (↥data.H ⧸ chief.N) → ℂ)) hfix2) x
  have hkerAut : aInvariantRestrictAut caseA.S0_aInvariant a = 1 :=
    chiefFactor_caseA_char_inertia_single caseA hreg a hinv
  have hker : a ∈ (aInvariantRestrictAut caseA.S0_aInvariant).ker :=
    MonoidHom.mem_ker.mpr hkerAut
  simp only [cuInHu, cuSub, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  exact ⟨_, ⟨a, hker, rfl⟩, rfl⟩

/-- **Peterfalvi (9.8.d): the `S₀`-summand decomposition `H̄ = S₀ ⊕ W`.**  The abelian chief factor
`H̄ = H/H₀` is an elementary abelian `p`-group on which `U` acts coprimely (`|U| ⟂ |H̄|`), so
operator
Maschke (`exists_aInvariant_complement_of_isElementaryAbelian`) splits the `U`-invariant order-`p`
factor `S₀ = caseA.S0` off: there is a `U`-invariant complement `W` (`= H₂…H_q` in Peterfalvi's
notation) with `S₀ ⊓ W = ⊥`, `S₀ ⊔ W = ⊤`.  This is the *fresh* decomposition (distinct from the
`Hpart` family — the structure does not give `S₀ = Hpart i₀`) required for the (9.8.d) source
character `θ₁ ∈ Irr(H̄/W)` and its easy inertia direction `C_U(S₀) ⊆ I(θ₁)`. -/
theorem chiefFactor_caseA_S0_complement [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ∃ W : Subgroup (↥data.H ⧸ chief.N),
      OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W ∧
        caseA.S0 ⊓ W = ⊥ ∧ caseA.S0 ⊔ W = ⊤ := by
  have := Fact.mk chief.p_prime
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have hpdvd : chief.p ∣ Nat.card (↥data.H ⧸ chief.N) := by
    rw [chiefFactor_quotient_card chief]
    exact dvd_pow_self chief.p data.nontrivial.2.1.pos.ne'
  have hcop : Nat.Coprime
      (Nat.card ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (Nat.card (↥data.H ⧸ chief.N)) :=
    ((typeP_coprime_H_uW1 data.typeP hU).symm.coprime_dvd_left
      (Subgroup.card_subgroup_dvd_card _)).coprime_dvd_right
        (Subgroup.card_quotient_dvd_card chief.N)
  exact OddOrder.BG.Ch1_Preliminary.exists_aInvariant_complement_of_isElementaryAbelian
    hpdvd hcop chief.quotient_elementaryAbelian caseA.S0_aInvariant

/-- **Some Clifford summand's complement `H₂…H_q` misses `S₀`** (Peterfalvi (9.8.d) support
witness):
there is an index `j₀` with the orbit generator `S₀` *not* contained in the join
`⨆_{j ≠ j₀} Hpart j` of the other `q-1` summands.  Because the `Hpart` form an internal direct
product
(`iSupIndep` + spanning, so `Subgroup.noncommPiCoprod` is bijective,
`noncommPiCoprod_bijective_of_card`)
each `H̄`-element has a unique component tuple; a nonzero `x ∈ S₀` (`S₀ ≠ ⊥`) must have some
nontrivial
`j₀`-component, and `⨆_{j≠j₀} Hpart j` lies in the kernel of the `j₀`-component projection.  This
is the
combinatorial seed of the *single-summand* (9.8.d) source character `θ₁` supported on `S₀` and
trivial on
a summand-join complement — the datum that makes `θ₁` **non-regular** and hence its `M`-induction
irreducible (`hIM`). -/
theorem caseA_exists_index_S0_not_le_biSup_compl [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ∃ j₀ : Fin data.q, ¬ caseA.S0 ≤ ⨆ (j) (_ : j ≠ j₀), caseA.Hpart j := by
  classical
  have : IsMulCommutative (↥data.H ⧸ chief.N) :=
    ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  have hcomm : Pairwise fun i j : Fin data.q =>
      ∀ x y : (↥data.H ⧸ chief.N), x ∈ caseA.Hpart i → y ∈ caseA.Hpart j → Commute x y :=
    fun i j _ x y _ _ => chief.quotient_elementaryAbelian.comm x y
  have hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm) :=
    ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep caseA.Hpart_iSupIndep, by
      rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range]; exact caseA.Hpart_iSup⟩
  set e : (∀ j : Fin data.q, ↥(caseA.Hpart j)) ≃* (↥data.H ⧸ chief.N) :=
    MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm) hbij with he
  -- `S₀ ≠ ⊥`: `|S₀| = |Hpart 0| = p ≥ 2`.
  have hS0card : Nat.card ↥caseA.S0 = chief.p := by
    have h := caseA.Hpart_order ⟨0, data.nontrivial.2.1.pos⟩
    rwa [caseA.Hpart_orbit ⟨0, data.nontrivial.2.1.pos⟩, card_pointwise_smul] at h
  have hS0ne : caseA.S0 ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hS0card
    exact chief.p_prime.one_lt.ne' hS0card.symm
  -- The subgroup `Kj j₀ = {x | (e.symm x) j₀ = 1}` (kernel of the `j₀`-component projection); each
  -- other summand `Hpart j` (`j ≠ j₀`) lies inside it.
  let Kj : Fin data.q → Subgroup (↥data.H ⧸ chief.N) := fun j₀ =>
    MonoidHom.ker ((Pi.evalMonoidHom (fun k : Fin data.q => ↥(caseA.Hpart k)) j₀).comp
      e.symm.toMonoidHom)
  have hmemKj : ∀ (j₀ : Fin data.q) (x : ↥data.H ⧸ chief.N),
      x ∈ Kj j₀ ↔ (e.symm x) j₀ = 1 := fun j₀ x => by
    change ((Pi.evalMonoidHom (fun k : Fin data.q => ↥(caseA.Hpart k)) j₀).comp
        e.symm.toMonoidHom) x = 1 ↔ _
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Pi.evalMonoidHom_apply]
  have hker : ∀ j₀ j : Fin data.q, j ≠ j₀ → caseA.Hpart j ≤ Kj j₀ := by
    intro j₀ j hj x hx
    rw [hmemKj]
    have hsymm : e.symm x = Pi.mulSingle j ⟨x, hx⟩ :=
      (MulEquiv.symm_apply_eq e).mpr (by
        rw [he, MulEquiv.ofBijective_apply, Subgroup.noncommPiCoprod_mulSingle])
    rw [congrFun hsymm j₀, Pi.mulSingle_eq_of_ne (Ne.symm hj)]
  -- If `S₀` were `≤` every complement, every `x ∈ S₀` has all-trivial components, so `x = 1`.
  by_contra hcon
  push Not at hcon
  apply hS0ne
  rw [eq_bot_iff]
  intro x hx
  have hcomp : ∀ j₀ : Fin data.q, (e.symm x) j₀ = 1 := by
    intro j₀
    exact (hmemKj j₀ x).mp ((iSup₂_le (hker j₀)) (hcon j₀ hx))
  rw [Subgroup.mem_bot]
  have hsymm1 : e.symm x = 1 := funext hcomp
  have hxe : x = e 1 := (MulEquiv.symm_apply_eq e).mp hsymm1
  rw [hxe, map_one]

/-- **Peterfalvi (9.8.d) summand-join complement `H̄ = S₀ ⊕ (H₂…H_q)`.**  Refining
`chiefFactor_caseA_S0_complement` (an *arbitrary* operator-Maschke complement) to a complement that
is a
*join of Clifford summands*: there is a `U`-invariant `W = ⨆_{j≠j₀} Hpart j` (the "`H₂…H_q`" of
Peterfalvi)
with `S₀ ⊓ W = ⊥`, `S₀ ⊔ W = ⊤`, **and `Hpart j₁ ≤ W` for some `j₁ ≠ j₀`** (`data.q ≥ 2`).  The
extra
`Hpart j₁ ≤ W` is what forces the (9.8.d) source character `θ₁ ∈ Irr(H̄/W)` (trivial on `W`,
nontrivial on
`S₀`) to be **non-regular** — trivial on the summand `Hpart j₁` — hence `I_M(Ind ζ) ≠ M` (`hIM`). 
Built from
the support witness `caseA_exists_index_S0_not_le_biSup_compl` (`¬ S₀ ≤ W`): `W` complements the
order-`p`
summand `Hpart j₀` (`iSupIndep` + spanning ⟹ `[H̄:W]=p`), so `|S₀|·|W| = p·|W| = |H̄|`, and `S₀ ⊓ W
⊊ S₀`
(`¬ S₀ ≤ W`, `|S₀|=p` prime) gives `S₀ ⊓ W = ⊥`, whence `IsComplement' S₀ W`. -/
theorem caseA_exists_summand_join_complement_S0 [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ∃ W : Subgroup (↥data.H ⧸ chief.N),
      OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W ∧
        caseA.S0 ⊓ W = ⊥ ∧ caseA.S0 ⊔ W = ⊤ ∧
        ∃ j₁ : Fin data.q, caseA.Hpart j₁ ≤ W := by
  classical
  let : Fintype (↥data.H ⧸ chief.N) := Fintype.ofFinite _
  let : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.comm }
  obtain ⟨j₀, hj₀⟩ := caseA_exists_index_S0_not_le_biSup_compl caseA
  have hWnorm : (⨆ (j) (_ : j ≠ j₀), caseA.Hpart j).Normal :=
    Subgroup.normal_of_isMulCommutative _
  -- `|S₀| = p`.
  have hS0card : Nat.card ↥caseA.S0 = chief.p := by
    have h := caseA.Hpart_order ⟨0, data.nontrivial.2.1.pos⟩
    rwa [caseA.Hpart_orbit ⟨0, data.nontrivial.2.1.pos⟩, card_pointwise_smul] at h
  -- `Hpart j₀ ⊔ W = ⊤` (`⨆ Hpart = ⊤`) and `Disjoint (Hpart j₀) W` (`iSupIndep`).
  have hHtop : caseA.Hpart j₀ ⊔ (⨆ (j) (_ : j ≠ j₀), caseA.Hpart j) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← caseA.Hpart_iSup]
    refine iSup_le fun j => ?_
    by_cases hj : j = j₀
    · exact hj ▸ le_sup_left
    · exact le_sup_of_le_right (le_iSup₂ (f := fun j (_ : j ≠ j₀) => caseA.Hpart j) j hj)
  have hHdisj : Disjoint (caseA.Hpart j₀) (⨆ (j) (_ : j ≠ j₀), caseA.Hpart j) :=
    (iSupIndep_def.mp caseA.Hpart_iSupIndep) j₀
  -- `|Hpart j₀|·|W| = |H̄|`, i.e. `p·|W| = |H̄|`.
  have hcompl0 : Subgroup.IsComplement' (caseA.Hpart j₀) (⨆ (j) (_ : j ≠ j₀), caseA.Hpart j) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hHdisj
      (by rw [← Subgroup.normal_mul, hHtop, Subgroup.coe_top])
  have hcardW : chief.p * Nat.card ↥(⨆ (j) (_ : j ≠ j₀), caseA.Hpart j)
      = Nat.card (↥data.H ⧸ chief.N) := by
    rw [← caseA.Hpart_order j₀]; exact hcompl0.card_mul_card
  -- `S₀ ⊓ W = ⊥`: proper (`¬ S₀ ≤ W`) subgroup of the order-`p` `S₀`.
  have hinf : caseA.S0 ⊓ (⨆ (j) (_ : j ≠ j₀), caseA.Hpart j) = ⊥ := by
    by_contra hne
    -- `S₀ ⊓ W` is a nontrivial subgroup of `S₀`, so `= S₀` (`|S₀| = p` prime), forcing `S₀ ≤ W`.
    have hle : caseA.S0 ⊓ (⨆ (j) (_ : j ≠ j₀), caseA.Hpart j) ≤ caseA.S0 := inf_le_left
    have hcard_dvd : Nat.card ↥(caseA.S0 ⊓ (⨆ (j) (_ : j ≠ j₀), caseA.Hpart j))
        ∣ Nat.card ↥caseA.S0 :=
      Subgroup.card_dvd_of_le hle
    rw [hS0card] at hcard_dvd
    have hne1 : Nat.card ↥(caseA.S0 ⊓ (⨆ (j) (_ : j ≠ j₀), caseA.Hpart j)) ≠ 1 := by
      rw [Ne, ← Subgroup.eq_bot_iff_card]; exact hne
    have heqp : Nat.card ↥(caseA.S0 ⊓ (⨆ (j) (_ : j ≠ j₀), caseA.Hpart j)) = chief.p :=
      ((chief.p_prime.eq_one_or_self_of_dvd _ hcard_dvd).resolve_left hne1)
    have heqS0 : caseA.S0 ⊓ (⨆ (j) (_ : j ≠ j₀), caseA.Hpart j) = caseA.S0 :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [heqp, hS0card])
    exact hj₀ (le_of_eq_of_le heqS0.symm inf_le_right)
  -- `S₀ ⊔ W = ⊤` from `IsComplement' S₀ W` (`|S₀|·|W| = |H̄|`, `Disjoint S₀ W`).
  have hsup : caseA.S0 ⊔ (⨆ (j) (_ : j ≠ j₀), caseA.Hpart j) = ⊤ :=
    (Subgroup.isComplement'_of_card_mul_and_disjoint (by rw [hS0card]; exact hcardW)
      (disjoint_iff.mpr hinf)).sup_eq_top
  -- `data.q ≥ 2` gives some `j₁ ≠ j₀`; then `Hpart j₁ ≤ W`.
  have hj₁ex : ∃ j₁ : Fin data.q, j₁ ≠ j₀ := by
    have h1 : 1 < Fintype.card (Fin data.q) := by
      rw [Fintype.card_fin]; exact data.nontrivial.2.1.one_lt
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h1
    rcases eq_or_ne a j₀ with rfl | ha
    · exact ⟨b, (Ne.symm hab)⟩
    · exact ⟨a, ha⟩
  obtain ⟨j₁, hj₁⟩ := hj₁ex
  exact ⟨⨆ (j) (_ : j ≠ j₀), caseA.Hpart j,
    OddOrder.Isaacs.Ch03.IsAInvariant.iSup fun j =>
      OddOrder.Isaacs.Ch03.IsAInvariant.iSup fun _ => caseA.Hpart_aInvariant j,
    hinf, hsup, j₁, le_iSup₂ (f := fun j (_ : j ≠ j₀) => caseA.Hpart j) j₁ hj₁⟩

/-- **Peterfalvi (9.8.d) easy inertia direction `C_U(S₀) ⊆ I_{HU}(θ₁₀)`, given an `S₀`-summand
decomposition.**  For a `U`-invariant complement `W` of `S₀` (`S₀ ⊔ W = ⊤`) and a chief-factor
character `θ₁ = θbar` **trivial on `W`**, every `C_U(S₀) = cuInHu`-element fixes the inflation
`θ₁₀`.
The realized easy half of the (9.8.d) inertia lift (mirror of `cInHu_le_inertia`, but where the
`C`-element acts trivially on *all* of `H̄`, here the `C_U(S₀)`-element acts trivially on `S₀` and
merely preserves `W`).  The algebraic heart is `mulAut_fixes_char_of_id_on_summand_triv_complement`:
`c ∈ C_U(S₀)` gives `aInvariantRestrictAut S₀ = 1` (fixes `S₀` pointwise) and `W`-invariance gives
`W`-preservation, so the linear `θ₁` (trivial on `W`) is fixed. -/
theorem cuInHu_le_inertia_of_complement_triv [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {W : Subgroup (↥data.H ⧸ chief.N)}
    (hWinv : OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W)
    (hsup : caseA.S0 ⊔ W = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (htriv : ∀ w ∈ W, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) w
      = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    cuInHu caseA ≤ ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
  have : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  intro c hc
  rw [ClassFunction.mem_inertia]
  -- unwrap `c ∈ cuInHu` to the `U`-element `a'` (in `U.subgroupOf (U ⊔ W₁)`) with
  -- `aInvariantRestrictAut S₀ a' = 1` and `((c:M):G) = subtype a'`.
  have hcG : ((c : ↥M) : G) ∈ cuSub caseA := by
    simp only [cuInHu, Subgroup.mem_subgroupOf] at hc; exact hc
  simp only [cuSub, Subgroup.mem_map] at hcG
  obtain ⟨w, ⟨a', ha', ha'w⟩, hwc⟩ := hcG
  have hkerAut : aInvariantRestrictAut caseA.S0_aInvariant a' = 1 := by
    rw [← MonoidHom.mem_ker]; exact ha'
  have hag : ((c : ↥M) : G) = (w : G) := hwc.symm
  -- `quotientMulAutHom w = uActionHom a'` (defeq); it fixes `S₀` pointwise and preserves `W`.
  have hid : ∀ x ∈ caseA.S0, (uActionHom data chief) a' x = x := by
    intro x hx
    have := aInvariantRestrictAut_coe caseA.S0_aInvariant a' ⟨x, hx⟩
    rw [hkerAut] at this
    simpa using this.symm
  have hWpres : ∀ x ∈ W, (uActionHom data chief) a' x ∈ W := fun x hx => hWinv.smul_mem a' hx
  have hfixθ : ∀ x, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ((uActionHom data chief) a' x)
      = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x :=
    mulAut_fixes_char_of_id_on_summand_triv_complement (uActionHom data chief a') caseA.S0 W
      hsup hid hWpres θbar htriv
  -- `uActionHom a' = quotientMulAutHom w` (`uActionHom = quotientMulAutHom ∘ subtype`;
  -- `subtype a' = w`)
  have huaw : uActionHom data chief a' = quotientMulAutHom chief.N_aInvariant w := by
    rw [show uActionHom data chief a'
        = quotientMulAutHom chief.N_aInvariant
            ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype a') from rfl, ha'w]
  -- `H̄`-level fixing: `compHom (quotientMulAutHom w) θbar = θbar`.
  have hHbar : ClassFunction.compHom (quotientMulAutHom chief.N_aInvariant w).toMonoidHom
        (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) := by
    ext y
    rw [ClassFunction.compHom_apply, ← huaw]
    exact hfixθ y
  -- reduce the `conjBy`-fixing to the just-established `H̄`-level fixing.
  rw [conjBy_compHom_hInHuEquivH data w c hag, compHom_typeP_conjAction_inflation, hHbar]

/-- **Peterfalvi (9.8.d) inertia lift `I_{HU}(θ₁₀) = H·C_U(S₀)`, parametrized over the easy
direction** `C_U(S₀) ≤ I(θ₁₀)`.  The single-factor analog of `inertia_eq_hcInHu_of_inf_le`: `⊆` uses
the proven hard direction `inertia_inf_uInHu_le_cuInHu` (`I(θ₁₀) ⊓ U ≤ C_U(S₀)`, from `θ₁` faithful
on `S₀`), `⊇` from `H ≤ I(θ₁₀)` (`subgroup_le_inertia`) and the supplied `heasy`
(`C_U(S₀) ≤ I(θ₁₀)`).  The easy direction `heasy` holds precisely when `θ₁ ∈ Irr(H̄/(H₂…H_q))` is
trivial on the complementary summands (a `C_U(S₀)`-element acts trivially on `S₀` and preserves each
`Hpart`, so it fixes a character supported on `S₀`); it is isolated as a hypothesis here.  Result:
`I(θ₁₀) = H·C_U(S₀)`, whose index in `HU` is `a` (`index_hcuInHu_eq_caseA_a`), giving the source
degree `a` and character degree `qa`.  Mirrors the `hInHu ⊔ cuInHu` form of the just-landed
`C_U(S₀)` substrate. -/
theorem inertia_eq_hcuInHu_of_easy_le [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∃ x ∈ caseA.S0,
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (heasy : cuInHu caseA ≤ ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cuInHu caseA := by
  set θ₀ := ClassFunction.compHom (hInHuEquivH data).toMonoidHom
    (ClassFunction.compHom (QuotientGroup.mk' chief.N)
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) with hθ₀
  apply le_antisymm
  · intro g hg
    have hgtop : g ∈ hInHu data ⊔ uInHu data := hInHu_sup_uInHu_eq_top data ▸ Subgroup.mem_top g
    rw [Subgroup.mem_sup_of_normal_left] at hgtop
    obtain ⟨h, hh, u, hu, rfl⟩ := hgtop
    have hh_in : h ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
      ClassFunction.subgroup_le_inertia θ₀ hh
    have hu_in : u ∈ ClassFunction.inertia (H := hInHu data) θ₀ := by
      have hmem : h⁻¹ * (h * u) ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
        mul_mem (inv_mem hh_in) hg
      rwa [inv_mul_cancel_left] at hmem
    exact mul_mem (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right (inertia_inf_uInHu_le_cuInHu caseA hreg ⟨hu_in, hu⟩))
  · rw [sup_le_iff]
    exact ⟨ClassFunction.subgroup_le_inertia θ₀, heasy⟩

/-- **Peterfalvi (9.8.d) full inertia lift `I_{HU}(θ₁₀) = H·C_U(S₀)`**, given an `S₀`-summand
decomposition and `θ₁ = θbar` supported on `S₀` (nontrivial on `S₀`, trivial on the complement `W`).
Combines the proven hard direction (`inertia_inf_uInHu_le_cuInHu`) with the easy direction
(`cuInHu_le_inertia_of_complement_triv`) through the assembly `inertia_eq_hcuInHu_of_easy_le`.  The
index of `H·C_U(S₀)` in `HU` is `a` (`index_hcuInHu_eq_caseA_a`), so the source `θ₁·λ` has degree
`a`
and its `M`-induction degree `qa`. -/
theorem inertia_eq_hcuInHu [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    {W : Subgroup (↥data.H ⧸ chief.N)}
    (hWinv : OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W)
    (hsup : caseA.S0 ⊔ W = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∃ x ∈ caseA.S0,
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (htriv : ∀ w ∈ W, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) w
      = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cuInHu caseA :=
  inertia_eq_hcuInHu_of_easy_le caseA hreg
    (cuInHu_le_inertia_of_complement_triv caseA hWinv hsup htriv)

/-- **Peterfalvi (9.8.d) source character `θ₁ ∈ Irr(H̄/W)`**: for an `S₀`-summand decomposition
`H̄ = S₀ ⊕ W`, there is an irreducible (linear) character `θ₁` of the chief factor that is
**nontrivial on `S₀`** (`hreg`) and **trivial on `W`** (`htriv`) — precisely the input feeding
`inertia_eq_hcuInHu`.  This realizes Peterfalvi's `θ₁ ∈ Irr(H̄/(H₂…H_q))`, `θ₁ ≠ 1`.  Construction:
`H̄/W` has order `p` (`W` complements the order-`p` `S₀`), hence is cyclic with a nontrivial
character `χ̄` (`exists_ne_one_hom_of_prime_card`); pulling `χ̄` back along `mk' W` gives `θ₁`,
which
kills `W` and is nontrivial on `S₀` because `S₀` surjects onto `H̄/W` (`S₀ ⊔ W = ⊤`). -/
theorem exists_source_char_caseA [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {W : Subgroup (↥data.H ⧸ chief.N)}
    (hinf : caseA.S0 ⊓ W = ⊥) (hsup : caseA.S0 ⊔ W = ⊤) :
    ∃ θbar : IrreducibleCharacter (↥data.H ⧸ chief.N),
      (∃ x ∈ caseA.S0, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) ∧
      (∀ w ∈ W, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) w
        = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) := by
  have : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  let : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := isMulCommutative_iff.mp inferInstance }
  have := Fact.mk chief.p_prime
  have : W.Normal := Subgroup.normal_of_isMulCommutative W
  let : CommGroup ((↥data.H ⧸ chief.N) ⧸ W) := inferInstance
  -- `|H̄/W| = p`: `S₀` complements `W`, so `[H̄ : W] = |S₀| = p`.
  have hcompl : Subgroup.IsComplement' caseA.S0 W :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
      (by rw [← Subgroup.mul_normal caseA.S0 W, hsup]; rfl)
  have hS0card : Nat.card ↥caseA.S0 = chief.p := by
    have h := caseA.Hpart_order ⟨0, data.nontrivial.2.1.pos⟩
    rwa [caseA.Hpart_orbit ⟨0, data.nontrivial.2.1.pos⟩, card_pointwise_smul] at h
  have hcard : Nat.card ((↥data.H ⧸ chief.N) ⧸ W) = chief.p := by
    rw [← Subgroup.index_eq_card, hcompl.index_eq_card, hS0card]
  -- A nontrivial character `χ̄` of the order-`p` quotient `H̄/W`.
  obtain ⟨χbar, hχbar⟩ := exists_ne_one_hom_of_prime_card (K := (↥data.H ⧸ chief.N) ⧸ W)
    (by rw [hcard]; exact chief.p_prime)
  -- Pull back to `H̄`: `θ = χ̄ ∘ mk' W`.
  set θ : (↥data.H ⧸ chief.N) →* ℂˣ := χbar.comp (QuotientGroup.mk' W) with hθ
  -- `θ` kills `W` (since `mk' W` does).
  have hθW : ∀ w ∈ W, θ w = 1 := by
    intro w hw
    rw [hθ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hw,
      map_one]
  refine ⟨linearIrreducibleCharacter θ, ?_, ?_⟩
  · -- nontrivial on `S₀`: else `θ = 1` on `S₀ ⊔ W = ⊤`, forcing `χ̄ = 1` (`mk' W` surjective).
    by_contra hall
    push Not at hall
    have hθS0 : ∀ s ∈ caseA.S0, θ s = 1 := by
      intro s hs
      have hθs := hall s hs
      rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
        Units.val_one] at hθs
      exact Units.val_injective (by simpa using hθs)
    -- `θ = 1` on all of `H̄` (`S₀ ⊔ W = ⊤`, `θ` trivial on both).
    have hθ1 : θ = 1 := by
      refine MonoidHom.ext fun y => ?_
      have hymem : y ∈ caseA.S0 ⊔ W := hsup ▸ Subgroup.mem_top y
      rw [Subgroup.mem_sup] at hymem
      obtain ⟨s, hs, w, hw, hsw⟩ := hymem
      rw [← hsw, map_mul, hθS0 s hs, hθW w hw, mul_one, MonoidHom.one_apply]
    -- hence `χ̄ = 1` (`θ = χ̄ ∘ mk' W`, `mk' W` surjective), contradiction.
    exact hχbar ((MonoidHom.cancel_right (QuotientGroup.mk'_surjective W)).mp (hθ ▸ hθ1))
  · -- trivial on `W`: `θ` kills `W` (`hθW`).
    intro w hw
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one, Units.val_one,
      hθW w hw, Units.val_one]

/-- **Peterfalvi (9.8.d): existence of a source character with inertia `H·C_U(S₀)`.**  Combining the
`S₀`-summand decomposition (`chiefFactor_caseA_S0_complement`), the source character
(`exists_source_char_caseA`), and the full inertia lift (`inertia_eq_hcuInHu`): there is a
chief-factor character `θ₁ = θbar`, nontrivial on `S₀`, whose inflation `θ₁₀`'s inertia in `HU` is
exactly `H·C_U(S₀)`. Since `[HU : H·C_U(S₀)] = a` (`index_hcuInHu_eq_caseA_a`), the `HU`-induction
of
`θ₁·λ` (for any `λ ∈ Irr(C_U(S₀)/U')`) from `H·C_U(S₀)` is an irreducible source character of degree
`a`, and its `M`-induction has degree `qa` — the (9.8.d) degree-`qa` members of `𝒮(H₀U')`.  This
packages the honest inertia content of (9.8.d); the `θ₁·λ` construction and count consume it. -/
theorem exists_source_char_inertia_eq_hcuInHu_caseA [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ∃ θbar : IrreducibleCharacter (↥data.H ⧸ chief.N),
      (∃ x ∈ caseA.S0, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) ∧
      ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
          (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
            (ClassFunction.compHom (QuotientGroup.mk' chief.N)
              (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA := by
  obtain ⟨W, hWinv, hinf, hsup⟩ := chiefFactor_caseA_S0_complement caseA
  obtain ⟨θbar, hreg, htriv⟩ := exists_source_char_caseA caseA hinf hsup
  exact ⟨θbar, hreg, inertia_eq_hcuInHu caseA hWinv hsup hreg htriv⟩

/-! ### Peterfalvi (9.8.d): the pair character `θ₁·λ` on `H·C_U(S₀)` and the degree-`qa` irreducible

Unlike the (9.8.c)/(9.9.c) `θ`-factor, which is the *inflation* `θ ∘ hcHom` killing the **normal**
`H₀C`, the (9.8.d) `θ`-factor is a genuine **extension** of the `C_U(S₀)`-invariant linear seed `θ₀`
from `H` to `H·C_U(S₀) = H ⋊ C_U(S₀)` (`C_U(S₀)` is *not* normal — only `H` is).  We build the
extension as a homomorphism `hcuThetaHom : H·C_U(S₀) →* ℂˣ` via `SemidirectProduct.lift`: on the
normal factor `H` it is the seed hom `θ ∘ mk'(N) ∘ hInHuEquivH`, on the complement `C_U(S₀)` it is
trivial (the `λ`-factor is added separately as `hcuLambdaHom`).  The `lift` compatibility
`fn(c·h·c⁻¹) = fn(h)` is exactly the `C_U(S₀)`-invariance of `θ₀`
(`cuInHu_le_inertia_of_complement_triv`),
made available at hom level because the codomain `ℂˣ` is abelian.  The pair
`θ₁·λ = hcuThetaHom · (hcuLambdaHom λ)` restricts to `θ₀` on `H` (the `λ`-factor dies there), so the
inertia lift `inertia_eq_hcuInHu` transfers verbatim and `Ind_{H·C_U(S₀)}^{HU}(θ₁·λ)` is irreducible
of degree `[HU : H·C_U(S₀)] = a` (`index_hcuInHu_eq_caseA_a`), whence `Ind_{HU}^M` has degree `qa`.
-/

/-- **`H` and `C_U(S₀)` are complementary inside `H·C_U(S₀)`** (`IsComplement'` of the two
`subgroupOf`-realizations in the join): `H ⊓ C_U(S₀) = ⊥` (`hInHu_inf_cuInHu_eq_bot`) gives
disjointness,
`H ⊔ C_U(S₀)` is the whole ambient by construction.  This is the complement input to
`SemidirectProduct.mulEquivSubgroup`, exhibiting `H·C_U(S₀) ≃* H ⋊[φ] C_U(S₀)`. -/
theorem hInHu_isComplement'_cuInHu_in_hcuInHu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).IsComplement'
      ((cuInHu caseA).subgroupOf (hInHu data ⊔ cuInHu caseA)) := by
  have := hInHu_normal data
  have : ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).Normal :=
    (hInHu_normal data).subgroupOf _
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff]
    change (hInHu data).comap _ ⊓ (cuInHu caseA).comap _ = ⊥
    rw [← Subgroup.comap_inf (hInHu data) (cuInHu caseA)
      (hInHu data ⊔ cuInHu caseA).subtype, hInHu_inf_cuInHu_eq_bot caseA]
    simp
  · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self, Subgroup.coe_top]

/-- The seed hom `θ₀ : H →* ℂˣ` in raw hom form: `θ ∘ mk'(N) ∘ hInHuEquivH`.  Its
`linearClassFunction` is the seed `θ₀` used in the inertia lift `inertia_eq_hcuInHu` (via
`ClassFunction.compHom_linearIrreducibleCharacter`). -/
noncomputable def hcuSeedHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data} (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    ↥(hInHu data) →* ℂˣ :=
  θ.comp ((QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom)


/-- **The `θ₀`-extension hom `hcuThetaHom : H·C_U(S₀) →* ℂˣ`** (Peterfalvi (9.8.d)).  The extension
of the seed hom `θ ∘ mk'(N) ∘ hInHuEquivH` from the normal factor `H` to `H·C_U(S₀)`, trivial on the
complement `C_U(S₀)`.  Built by `SemidirectProduct.lift` (through the complement iso
`hInHu_isComplement'_cuInHu_in_hcuInHu`); the `lift` `φ`-compatibility `fn(φ(c) h) = fn(h)` is the
`C_U(S₀)`-invariance of `θ₀` (`hinv`, supplied by `cuInHu_le_inertia_of_complement_triv`), using
that
the codomain `ℂˣ` is abelian (`MulAut.conj = 1`).  Restricts to `θ₀` on `H`
(`hcuThetaHom_inclusion_hInHu`). -/
noncomputable def hcuThetaHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h) :
    ↥(hInHu data ⊔ cuInHu caseA) →* ℂˣ :=
  haveI := hInHu_normal data
  haveI : ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).Normal :=
    (hInHu_normal data).subgroupOf _
  (SemidirectProduct.lift
      ((hcuSeedHom (chief := chief) θ).comp
        (Subgroup.subgroupOfEquivOfLe
          (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA)).toMonoidHom)
      (1 : ↥((cuInHu caseA).subgroupOf (hInHu data ⊔ cuInHu caseA)) →* ℂˣ)
      (by
        intro c
        ext h
        -- RHS: `(1 : _→*ℂˣ) c = 1`, `MulAut.conj 1 = 1`; LHS: `φ(c) h = c·h·c⁻¹` in the subgroupOf.
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.one_apply, map_one,
          MulAut.one_apply]
        -- transport `c`, `h` from the join-`subgroupOf`s to `↥(cuInHu)`, `↥(hInHu)`.
        set c' := (Subgroup.subgroupOfEquivOfLe
          (le_sup_right : cuInHu caseA ≤ hInHu data ⊔ cuInHu caseA)) c with hc'
        set h' := (Subgroup.subgroupOfEquivOfLe
          (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA)) h with hh'
        -- the two `↥(hInHu data)` arguments agree, so `hcuSeedHom θ` agrees on them.
        have harg : (Subgroup.subgroupOfEquivOfLe
              (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA))
            ((((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).normalizerMonoidHom
              ((Subgroup.inclusion (((hInHu data).subgroupOf
                (hInHu data ⊔ cuInHu caseA)).normalizer_eq_top ▸ le_top)) c)) h)
            = ⟨(c' : ↥(huSub data)) * (h' : ↥(huSub data)) * (c' : ↥(huSub data))⁻¹,
                (hInHu_normal data).conj_mem _ h'.2 (c' : ↥(huSub data))⟩ := by
          apply Subtype.ext
          simp only [hc', hh', Subgroup.subgroupOfEquivOfLe_apply_coe,
            Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
            Subgroup.coe_mul, Subgroup.coe_inv]
        rw [harg]
        exact congrArg (Units.val) (hinv c' h'))).comp
    (SemidirectProduct.mulEquivSubgroup
      (hInHu_isComplement'_cuInHu_in_hcuInHu caseA)).symm.toMonoidHom



end OddOrder.Peterfalvi.S11
