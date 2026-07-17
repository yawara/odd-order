import OddOrder.Peterfalvi.S11_MaximalII_III_IV.InertiaLift

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S11_MaximalII_III_IV.CuS0` (2000-line limit, issue 0103 第 2 パス).
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

* `cInHu ≤ I(θ₀)` (`cInHu_le_inertia`): `C = C_U(H̄)` acts trivially on the chief factor, so it fixes
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
character `θ₁` nontrivial on the orbit generator `S₀ = H₁` (`hreg` on `caseA.S0`), any `U`-element in
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
`H̄ = H/H₀` is an elementary abelian `p`-group on which `U` acts coprimely (`|U| ⟂ |H̄|`), so operator
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
  haveI := Fact.mk chief.p_prime
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
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
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
  letI : Fintype (↥data.H ⧸ chief.N) := Fintype.ofFinite _
  letI : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.comm }
  obtain ⟨j₀, hj₀⟩ := caseA_exists_index_S0_not_le_biSup_compl caseA
  haveI hWnorm : (⨆ (j) (_ : j ≠ j₀), caseA.Hpart j).Normal :=
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
character `θ₁ = θbar` **trivial on `W`**, every `C_U(S₀) = cuInHu`-element fixes the inflation `θ₁₀`.
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
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
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
  -- `uActionHom a' = quotientMulAutHom w` (`uActionHom = quotientMulAutHom ∘ subtype`; `subtype a' = w`)
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

/-- **Peterfalvi (9.8.d) inertia lift `I_{HU}(θ₁₀) = H·C_U(S₀)`, parametrized over the easy direction**
`C_U(S₀) ≤ I(θ₁₀)`.  The single-factor analog of `inertia_eq_hcInHu_of_inf_le`: `⊆` uses the proven
hard direction `inertia_inf_uInHu_le_cuInHu` (`I(θ₁₀) ⊓ U ≤ C_U(S₀)`, from `θ₁` faithful on `S₀`),
`⊇` from `H ≤ I(θ₁₀)` (`subgroup_le_inertia`) and the supplied `heasy` (`C_U(S₀) ≤ I(θ₁₀)`).  The
easy direction `heasy` holds precisely when `θ₁ ∈ Irr(H̄/(H₂…H_q))` is trivial on the complementary
summands (a `C_U(S₀)`-element acts trivially on `S₀` and preserves each `Hpart`, so it fixes a
character supported on `S₀`); it is isolated as a hypothesis here.  Result: `I(θ₁₀) = H·C_U(S₀)`,
whose index in `HU` is `a` (`index_hcuInHu_eq_caseA_a`), giving the source degree `a` and character
degree `qa`.  Mirrors the `hInHu ⊔ cuInHu` form of the just-landed `C_U(S₀)` substrate. -/
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
index of `H·C_U(S₀)` in `HU` is `a` (`index_hcuInHu_eq_caseA_a`), so the source `θ₁·λ` has degree `a`
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
character `χ̄` (`exists_ne_one_hom_of_prime_card`); pulling `χ̄` back along `mk' W` gives `θ₁`, which
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
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  letI : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := isMulCommutative_iff.mp inferInstance }
  haveI := Fact.mk chief.p_prime
  haveI : W.Normal := Subgroup.normal_of_isMulCommutative W
  letI : CommGroup ((↥data.H ⧸ chief.N) ⧸ W) := inferInstance
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
exactly `H·C_U(S₀)`.  Since `[HU : H·C_U(S₀)] = a` (`index_hcuInHu_eq_caseA_a`), the `HU`-induction of
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
`fn(c·h·c⁻¹) = fn(h)` is exactly the `C_U(S₀)`-invariance of `θ₀` (`cuInHu_le_inertia_of_complement_triv`),
made available at hom level because the codomain `ℂˣ` is abelian.  The pair
`θ₁·λ = hcuThetaHom · (hcuLambdaHom λ)` restricts to `θ₀` on `H` (the `λ`-factor dies there), so the
inertia lift `inertia_eq_hcuInHu` transfers verbatim and `Ind_{H·C_U(S₀)}^{HU}(θ₁·λ)` is irreducible
of degree `[HU : H·C_U(S₀)] = a` (`index_hcuInHu_eq_caseA_a`), whence `Ind_{HU}^M` has degree `qa`. -/

/-- **`H` and `C_U(S₀)` are complementary inside `H·C_U(S₀)`** (`IsComplement'` of the two
`subgroupOf`-realizations in the join): `H ⊓ C_U(S₀) = ⊥` (`hInHu_inf_cuInHu_eq_bot`) gives disjointness,
`H ⊔ C_U(S₀)` is the whole ambient by construction.  This is the complement input to
`SemidirectProduct.mulEquivSubgroup`, exhibiting `H·C_U(S₀) ≃* H ⋊[φ] C_U(S₀)`. -/
theorem hInHu_isComplement'_cuInHu_in_hcuInHu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).IsComplement'
      ((cuInHu caseA).subgroupOf (hInHu data ⊔ cuInHu caseA)) := by
  haveI := hInHu_normal data
  haveI : ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).Normal :=
    (hInHu_normal data).subgroupOf _
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff]
    change (hInHu data).comap _ ⊓ (cuInHu caseA).comap _ = ⊥
    rw [← Subgroup.comap_inf (hInHu data) (cuInHu caseA)
      (hInHu data ⊔ cuInHu caseA).subtype, hInHu_inf_cuInHu_eq_bot caseA]
    simp
  · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self, Subgroup.coe_top]

/-- The seed hom `θ₀ : H →* ℂˣ` in raw hom form: `θ ∘ mk'(N) ∘ hInHuEquivH`.  Its `linearClassFunction`
is the seed `θ₀` used in the inertia lift `inertia_eq_hcuInHu` (via
`ClassFunction.compHom_linearIrreducibleCharacter`). -/
noncomputable def hcuSeedHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data} (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    ↥(hInHu data) →* ℂˣ :=
  θ.comp ((QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom)


/-- **The `θ₀`-extension hom `hcuThetaHom : H·C_U(S₀) →* ℂˣ`** (Peterfalvi (9.8.d)).  The extension of
the seed hom `θ ∘ mk'(N) ∘ hInHuEquivH` from the normal factor `H` to `H·C_U(S₀)`, trivial on the
complement `C_U(S₀)`.  Built by `SemidirectProduct.lift` (through the complement iso
`hInHu_isComplement'_cuInHu_in_hcuInHu`); the `lift` `φ`-compatibility `fn(φ(c) h) = fn(h)` is the
`C_U(S₀)`-invariance of `θ₀` (`hinv`, supplied by `cuInHu_le_inertia_of_complement_triv`), using that
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

/-- **`hcuThetaHom` restricts to `θ₀` on `H`**: on the inclusion of `h ∈ H` into `H·C_U(S₀)`, the
extension returns the seed value `hcuSeedHom θ h`.  Via `SemidirectProduct.lift_inl` after
`(mulEquivSubgroup).symm (inclusion h) = inl h` (the complement iso sends the normal factor to `inl`).
This is the single-factor analog of `hcHom_inclusion`, feeding the restriction-inertia argument. -/
theorem hcuThetaHom_inclusion_hInHu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (h : ↥(hInHu data)) :
    hcuThetaHom caseA θ hinv (Subgroup.inclusion
        (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h)
      = hcuSeedHom (chief := chief) θ h := by
  haveI := hInHu_normal data
  haveI : ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).Normal :=
    (hInHu_normal data).subgroupOf _
  -- `(mulEquivSubgroup).symm (inclusion h) = inl ⟨incl h, h ∈ H⟩`.
  have hsymm : (SemidirectProduct.mulEquivSubgroup
      (hInHu_isComplement'_cuInHu_in_hcuInHu caseA)).symm
      (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h)
      = SemidirectProduct.inl
        (⟨Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h,
          Subgroup.mem_subgroupOf.mpr h.2⟩ :
          ↥((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA))) := by
    rw [MulEquiv.symm_apply_eq]
    simp only [SemidirectProduct.mulEquivSubgroup, MulEquiv.ofBijective_apply,
      SemidirectProduct.monoidHomSubgroup_apply, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, OneMemClass.coe_one, mul_one]
  simp only [hcuThetaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hsymm,
    SemidirectProduct.lift_inl]
  congr 1

/-- **The (9.8.d) pair hom `θ₁·λ : H·C_U(S₀) →* ℂˣ`**: the product of the `θ₀`-extension `hcuThetaHom`
(the single-factor analog of the `θ`-inflation, restricting to `θ₀` on `H`) and the `λ`-lift
`hcuLambdaHom λ` (trivial on `H`).  On `H` it agrees with `hcuThetaHom` (= `θ₀`) alone; on `C_U(S₀)` it
is `λ` (the extension is trivial there by construction).  Mirror of `hcPairHom`, single-factor. -/
noncomputable def hcuPairHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ) :
    ↥(hInHu data ⊔ cuInHu caseA) →* ℂˣ :=
  hcuThetaHom caseA θ hinv * hcuLambdaHom caseA lam

/-- **The `H·C_U(S₀)`-linear pair character `ψ_{θ₁,λ}`** of the (9.8.d) construction: the linear
(degree-one) irreducible character with hom `hcuPairHom`.  Mirror of `hcPsiPair`, single-factor. -/
noncomputable def hcuPsiPair [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ) :
    IrreducibleCharacter ↥(hInHu data ⊔ cuInHu caseA) :=
  linearIrreducibleCharacter (hcuPairHom caseA θ hinv lam)

/-- **`ψ_{θ₁,λ}|_hInHu = θ₀`** (pointwise): on the inclusion of `h ∈ H` the pair character equals the
seed's inflation `θ₀`.  The `λ`-factor dies (`hcuLambdaHom_eq_one_of_mem_hInHu`) and the `θ`-factor is
the extension's restriction (`hcuThetaHom_inclusion_hInHu`), which by
`compHom_linearIrreducibleCharacter` is exactly the ClassFunction seed `θ₀`.  Same right-hand side as
the seed of `inertia_eq_hcuInHu`, so the restriction-inertia argument applies to the pair verbatim. -/
theorem hcuPsiPair_apply_inclusion [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ) (h : ↥(hInHu data)) :
    (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
        (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h)
      = (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        h := by
  have hlam1 : hcuLambdaHom caseA lam
      (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h) = 1 :=
    hcuLambdaHom_eq_one_of_mem_hInHu caseA lam (Subgroup.mem_subgroupOf.mpr h.2)
  simp only [hcuPsiPair, hcuPairHom, linearIrreducibleCharacter_apply, MonoidHom.mul_apply,
    hcuThetaHom_inclusion_hInHu, hlam1, mul_one, hcuSeedHom,
    MonoidHom.comp_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply]

/-- **Restriction-inertia `inertia(ψ_{θ₁,λ}) ≤ inertia(θ₀)`** (Peterfalvi (9.8.d)): an element fixing
the pair character also fixes its `H`-restriction `θ₀` (`hcuPsiPair_apply_inclusion`).  Single-factor
mirror of `hcPsiPair_inertia_le` — the `λ`-factor is invisible on the restriction. -/
theorem hcuPsiPair_inertia_le [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [(hInHu data ⊔ cuInHu caseA).Normal] :
    ClassFunction.inertia (hcuPsiPair caseA θ hinv lam : ClassFunction
        ↥(hInHu data ⊔ cuInHu caseA) ℂ)
      ≤ ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
  haveI := hInHu_normal data
  intro g hg
  rw [ClassFunction.mem_inertia] at hg ⊢
  ext h
  have key : (ClassFunction.conjBy g (hcuPsiPair caseA θ hinv lam : ClassFunction
        ↥(hInHu data ⊔ cuInHu caseA) ℂ))
      (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h)
      = (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
        (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h) := by
    rw [hg]
  rw [ClassFunction.conjBy_apply] at key ⊢
  rw [← hcuPsiPair_apply_inclusion caseA θ hinv lam,
    ← hcuPsiPair_apply_inclusion caseA θ hinv lam, ← key]
  congr 1

/-- **`inertia(ψ_{θ₁,λ}) = H·C_U(S₀)`** (Peterfalvi (9.8.d)): with the seed inertia
`inertia(θ₀) = H·C_U(S₀)` (`inertia_eq_hcuInHu` for `θ` nontrivial on `S₀`, trivial on the complement),
the pair character's `HU`-inertia is exactly `H·C_U(S₀)`.  Single-factor mirror of
`hcPsiPair_inertia_eq_hc`.  Feeds `isIrreducibleCharacter_induce_of_inertia_eq` for the degree-`a`
irreducible. -/
theorem hcuPsiPair_inertia_eq_hcu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    ClassFunction.inertia (hcuPsiPair caseA θ hinv lam : ClassFunction
        ↥(hInHu data ⊔ cuInHu caseA) ℂ)
      = hInHu data ⊔ cuInHu caseA := by
  apply le_antisymm ?_ (ClassFunction.subgroup_le_inertia _)
  refine le_trans (hcuPsiPair_inertia_le caseA θ hinv lam) ?_
  rw [hθ₀]

/-- **`ζ_{θ₁,λ} = Ind_{H·C_U(S₀)}^{HU}(ψ_{θ₁,λ})` is irreducible** (Peterfalvi (9.8.d), degree `a`):
direct from `isIrreducibleCharacter_induce_of_inertia_eq` and `inertia(ψ_{θ₁,λ}) = H·C_U(S₀)`
(`hcuPsiPair_inertia_eq_hcu`).  The (9.8.d) irreducible source character over the extension `θ₀`.  Its
degree is `[HU : H·C_U(S₀)] · 1 = a` (`hcuZetaPair_apply_one`). -/
theorem hcuZetaPair_irreducible [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    IsIrreducibleCharacter (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
      (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)) :=
  OddOrder.RepresentationTheory.isIrreducibleCharacter_induce_of_inertia_eq
    (hcuPsiPair caseA θ hinv lam)
    (hcuPsiPair_inertia_eq_hcu caseA θ hinv lam hθ₀)

/-- **`ζ_{θ₁,λ}(1) = a`** (Peterfalvi (9.8.d), source degree): the induced source character has degree
`[HU : H·C_U(S₀)] · ψ(1) = a · 1 = a`, since `ψ_{θ₁,λ}` is linear (`ClassFunction.induce_apply_one` +
`index_hcuInHu_eq_caseA_a`).  The `M`-induction then has degree `q·a` (`hcuZetaPair_induceHU_apply_one`). -/
theorem hcuZetaPair_apply_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)] :
    ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
        (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
        (1 : ↥(huSub data))
      = (caseA.a : ℂ) := by
  rw [ClassFunction.induce_apply_one, index_hcuInHu_eq_caseA_a,
    show (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
        (1 : ↥(hInHu data ⊔ cuInHu caseA)) = 1 from by
      simp [hcuPsiPair], mul_one]

/-- **`Ind_{HU}^M ζ_{θ₁,λ}(1) = q·a`** (Peterfalvi (9.8.d), full degree): `[M:HU]·ζ(1) = q·a`, from
`induceHU_apply_one_eq_q_mul` and the source degree `a` (`hcuZetaPair_apply_one`).  This is the
degree-`qa` claimed by (9.8.d) for the members of `𝒮(H₀U')`. -/
theorem hcuZetaPair_induceHU_apply_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)] :
    induceHU data (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
        (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ) (1 : ↥M)
      = ((data.q * caseA.a : ℕ) : ℂ) := by
  rw [induceHU_apply_one_eq_q_mul, hcuZetaPair_apply_one, Nat.cast_mul]

/-- **`hcuSeedHom`-invariance from the `C_U(S₀)`-inertia of `θ₀`** (Peterfalvi (9.8.d)): the
`ClassFunction`-level invariance `conjBy c θ₀ = θ₀` (available as `cuInHu_le_inertia_of_complement_triv`)
descends to the hom-level invariance `hinv` required by `hcuThetaHom`, because `θ₀` is the
`linearClassFunction` of `hcuSeedHom θ` (via `compHom_linearIrreducibleCharacter`) and the coercion
`ℂˣ → ℂ` is injective.  This bridges the substrate to the extension construction. -/
theorem hcuSeedHom_invariance_of_cuInHu_le_inertia [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hle : cuInHu caseA ≤ ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))) :
    ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h := by
  haveI := hInHu_normal data
  intro c h
  -- `θ₀ = linearClassFunction (hcuSeedHom θ)` and `conjBy (c:huSub) θ₀ = θ₀`.
  have hconj : ClassFunction.conjBy (c : ↥(huSub data))
      (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)) :=
    ClassFunction.mem_inertia.mp (hle c.2)
  -- evaluate both sides at `h`; the seed-ClassFunction is `hcuSeedHom θ`.
  have hval := congrFun (congrArg (fun f : ClassFunction ↥(hInHu data) ℂ => (f : ↥(hInHu data) → ℂ))
    hconj) h
  simp only [ClassFunction.conjBy_apply,
    ClassFunction.compHom_linearIrreducibleCharacter, linearIrreducibleCharacter_apply] at hval
  -- `hval : (θ (mk' N (hInHuEquivH ⟨c·h·c⁻¹⟩)) : ℂ) = (θ (mk' N (hInHuEquivH h)) : ℂ)`.
  refine Units.val_injective ?_
  simpa only [hcuSeedHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hval

/-- **Peterfalvi (9.8.d) source character in hom form**: the hom-level version of
`exists_source_char_caseA`.  There is a homomorphism `θ : H̄ →* ℂˣ` and an `S₀`-summand complement `W`
such that `linearIrreducibleCharacter θ` is nontrivial on `S₀`, trivial on `W`, and `W` is
`U`-invariant with `S₀ ⊔ W = ⊤`.  Same construction as `exists_source_char_caseA` (nontrivial character
of the order-`p` quotient `H̄/W` pulled back along `mk' W`), but returning the underlying hom so the
extension `hcuThetaHom` and the `hcuSeedHom`-invariance can be built. -/
theorem exists_source_char_hom_caseA [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ∃ (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (W : Subgroup (↥data.H ⧸ chief.N)),
      OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W ∧
      caseA.S0 ⊔ W = ⊤ ∧
      (∃ x ∈ caseA.S0, (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) ∧
      (∀ w ∈ W, (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) w
        = (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) := by
  obtain ⟨W, hWinv, hinf, hsup⟩ := chiefFactor_caseA_S0_complement caseA
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  letI : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := isMulCommutative_iff.mp inferInstance }
  haveI := Fact.mk chief.p_prime
  haveI : W.Normal := Subgroup.normal_of_isMulCommutative W
  letI : CommGroup ((↥data.H ⧸ chief.N) ⧸ W) := inferInstance
  have hcompl : Subgroup.IsComplement' caseA.S0 W :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
      (by rw [← Subgroup.mul_normal caseA.S0 W, hsup]; rfl)
  have hS0card : Nat.card ↥caseA.S0 = chief.p := by
    have h := caseA.Hpart_order ⟨0, data.nontrivial.2.1.pos⟩
    rwa [caseA.Hpart_orbit ⟨0, data.nontrivial.2.1.pos⟩, card_pointwise_smul] at h
  have hcard : Nat.card ((↥data.H ⧸ chief.N) ⧸ W) = chief.p := by
    rw [← Subgroup.index_eq_card, hcompl.index_eq_card, hS0card]
  obtain ⟨χbar, hχbar⟩ := exists_ne_one_hom_of_prime_card (K := (↥data.H ⧸ chief.N) ⧸ W)
    (by rw [hcard]; exact chief.p_prime)
  set θ : (↥data.H ⧸ chief.N) →* ℂˣ := χbar.comp (QuotientGroup.mk' W) with hθ
  have hθW : ∀ w ∈ W, θ w = 1 := by
    intro w hw
    rw [hθ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hw,
      map_one]
  refine ⟨θ, W, hWinv, hsup, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hθS0 : ∀ s ∈ caseA.S0, θ s = 1 := by
      intro s hs
      have hθs := hall s hs
      rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
        Units.val_one] at hθs
      exact Units.val_injective (by simpa using hθs)
    have hθ1 : θ = 1 := by
      refine MonoidHom.ext fun y => ?_
      have hymem : y ∈ caseA.S0 ⊔ W := hsup ▸ Subgroup.mem_top y
      rw [Subgroup.mem_sup] at hymem
      obtain ⟨s, hs, w, hw, hsw⟩ := hymem
      rw [← hsw, map_mul, hθS0 s hs, hθW w hw, mul_one, MonoidHom.one_apply]
    exact hχbar ((MonoidHom.cancel_right (QuotientGroup.mk'_surjective W)).mp (hθ ▸ hθ1))
  · intro w hw
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one, Units.val_one,
      hθW w hw, Units.val_one]

/-- **Peterfalvi (9.8.d) source hom, *non-regular* form** (`θ₁ ∈ Irr(H̄/(H₂…H_q))`).  Strengthens
`exists_source_char_hom_caseA` by taking the complement `W` to be the *summand-join* `H₂…H_q`
(`caseA_exists_summand_join_complement_S0`) rather than an arbitrary Maschke complement: the
resulting
hom `θ` (nontrivial on `S₀`, trivial on `W`) is additionally **trivial on a Clifford summand
`Hpart j₁`** (`Hpart j₁ ≤ W`), i.e. `θ.comp (Hpart j₁).subtype = 1` — so `θ` is *not regular*.  That
non-regularity is exactly what makes the (9.8.d) source `ζ = Ind_{HU} ψ_{θ₁,λ}` fail to be
`W₁`-fixed
(`caseA_reducible_theta_regular` contrapositive), giving `I_M(Ind ζ) ≠ M` and the unconditional
irreducibility of `Ind_{HU}^M ζ`. -/
theorem exists_source_char_hom_caseA_nonRegular [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ∃ (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (W : Subgroup (↥data.H ⧸ chief.N)),
      OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W ∧
      caseA.S0 ⊔ W = ⊤ ∧
      (∃ x ∈ caseA.S0, (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) ∧
      (∀ w ∈ W, (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) w
        = (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) ∧
      ∃ j₁ : Fin data.q, θ.comp (caseA.Hpart j₁).subtype = 1 := by
  obtain ⟨W, hWinv, hinf, hsup, j₁, hj₁le⟩ := caseA_exists_summand_join_complement_S0 caseA
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  letI : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := isMulCommutative_iff.mp inferInstance }
  haveI := Fact.mk chief.p_prime
  haveI : W.Normal := Subgroup.normal_of_isMulCommutative W
  letI : CommGroup ((↥data.H ⧸ chief.N) ⧸ W) := inferInstance
  have hcompl : Subgroup.IsComplement' caseA.S0 W :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
      (by rw [← Subgroup.mul_normal caseA.S0 W, hsup]; rfl)
  have hS0card : Nat.card ↥caseA.S0 = chief.p := by
    have h := caseA.Hpart_order ⟨0, data.nontrivial.2.1.pos⟩
    rwa [caseA.Hpart_orbit ⟨0, data.nontrivial.2.1.pos⟩, card_pointwise_smul] at h
  have hcard : Nat.card ((↥data.H ⧸ chief.N) ⧸ W) = chief.p := by
    rw [← Subgroup.index_eq_card, hcompl.index_eq_card, hS0card]
  obtain ⟨χbar, hχbar⟩ := exists_ne_one_hom_of_prime_card (K := (↥data.H ⧸ chief.N) ⧸ W)
    (by rw [hcard]; exact chief.p_prime)
  set θ : (↥data.H ⧸ chief.N) →* ℂˣ := χbar.comp (QuotientGroup.mk' W) with hθ
  have hθW : ∀ w ∈ W, θ w = 1 := by
    intro w hw
    rw [hθ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hw,
      map_one]
  refine ⟨θ, W, hWinv, hsup, ?_, ?_, j₁, ?_⟩
  · by_contra hall
    push Not at hall
    have hθS0 : ∀ s ∈ caseA.S0, θ s = 1 := by
      intro s hs
      have hθs := hall s hs
      rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
        Units.val_one] at hθs
      exact Units.val_injective (by simpa using hθs)
    have hθ1 : θ = 1 := by
      refine MonoidHom.ext fun y => ?_
      have hymem : y ∈ caseA.S0 ⊔ W := hsup ▸ Subgroup.mem_top y
      rw [Subgroup.mem_sup] at hymem
      obtain ⟨s, hs, w, hw, hsw⟩ := hymem
      rw [← hsw, map_mul, hθS0 s hs, hθW w hw, mul_one, MonoidHom.one_apply]
    exact hχbar ((MonoidHom.cancel_right (QuotientGroup.mk'_surjective W)).mp (hθ ▸ hθ1))
  · intro w hw
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one, Units.val_one,
      hθW w hw, Units.val_one]
  · -- `θ` is trivial on `Hpart j₁ ≤ W`.
    refine MonoidHom.ext fun y => ?_
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, MonoidHom.one_apply]
    exact hθW (y : ↥data.H ⧸ chief.N) (hj₁le y.2)

/-- **Peterfalvi (9.8.d): the degree-`qa` irreducible character of `HU`/`M`.**  Fully assembling the
(9.8.d) construction: there is a homomorphism `θ` (nontrivial on `S₀`), an `S₀`-summand complement
`W`, and — for any `λ ∈ Irr(C_U(S₀))` — the pair character `θ₁·λ` on `H·C_U(S₀)` whose `HU`-induction
`ζ_{θ₁,λ}` is **irreducible** of degree `[HU : H·C_U(S₀)] = a` (`hcuZetaPair_irreducible` +
`hcuZetaPair_apply_one`), and whose `M`-induction `Ind_{HU}^M ζ_{θ₁,λ}` has degree `q·a = qa`
(`hcuZetaPair_induceHU_apply_one`).  The inertia hypotheses are discharged from the substrate:
`exists_source_char_hom_caseA` supplies `θ`/`W`, `inertia_eq_hcuInHu` gives
`inertia(θ₀) = H·C_U(S₀)`, and `hcuSeedHom_invariance_of_cuInHu_le_inertia` (via
`cuInHu_le_inertia_of_complement_triv`) gives the extension's compatibility `hinv`.  This packages the
honest source-character content of (9.8.d); the `Ind_{HU}^M`-irreducibility (`W₁`-free-orbit
propagation) and the `𝒮(H₀U')`-membership/count consume it. -/
theorem caseA_exists_irreducible_source_degree_qa [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Fintype ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)] :
    ∃ ζ : ClassFunction ↥(huSub data) ℂ,
      IsIrreducibleCharacter ζ ∧ ζ (1 : ↥(huSub data)) = (caseA.a : ℂ) ∧
      induceHU data ζ (1 : ↥M) = ((data.q * caseA.a : ℕ) : ℂ) := by
  haveI := hcuInHu_normal caseA
  obtain ⟨θ, W, hWinv, hsup, hreg, htriv⟩ := exists_source_char_hom_caseA caseA
  -- the seed inertia `inertia(θ₀) = H·C_U(S₀)` from the full inertia lift
  have hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
      (ClassFunction.compHom (QuotientGroup.mk' chief.N)
        (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cuInHu caseA :=
    inertia_eq_hcuInHu caseA hWinv hsup hreg htriv
  -- the `hcuSeedHom`-invariance from the easy inertia direction
  have hinv := hcuSeedHom_invariance_of_cuInHu_le_inertia caseA θ
    (cuInHu_le_inertia_of_complement_triv caseA hWinv hsup htriv)
  refine ⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
      (hcuPsiPair caseA θ hinv lam), ?_, ?_, ?_⟩
  · exact hcuZetaPair_irreducible caseA θ hinv lam hθ₀
  · exact hcuZetaPair_apply_one caseA θ hinv lam
  · exact hcuZetaPair_induceHU_apply_one caseA θ hinv lam

/-- **Inertia lift `I_{HU}(θ₀) = HC`, parametrized over the hard direction** `I(θ₀) ⊓ U ≤ C`.  The
case-agnostic assembly: `⊇` from `H ≤ I(θ₀)` (`subgroup_le_inertia`) and `cInHu_le_inertia` (both
case-independent), `⊆` by the modular decomposition `g = h·u` (`H ⊔ U = ⊤`, `H ◁ HU`) with the
`U`-part `u ∈ I(θ₀) ⊓ U ≤ C` supplied by `hinf`.  Both Clifford cases instantiate `hinf`: case (b)
via `inertia_inf_uInHu_le_cInHu` (`U`-irreducible), case (a) via the non-Galois `Hpart` analysis. -/
theorem inertia_eq_hcInHu_of_inf_le [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hinf : ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cInHu data chief) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief := by
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
      (Subgroup.mem_sup_right (hinf ⟨hu_in, hu⟩))
  · rw [sup_le_iff]
    exact ⟨ClassFunction.subgroup_le_inertia θ₀, cInHu_le_inertia data chief⟩

/-- **Peterfalvi (9.9.a), the inertia lift: `I_{HU}(θ₀) = HC`.**  The inertia in `HU` of the
realized chief-factor character `θ₀` is exactly the inertia subgroup `HC = hInHu ⊔ cInHu`.  `⊇` from
`H ≤ I(θ₀)` (automatic) and `cInHu_le_inertia`; `⊆` by decomposing `g ∈ I(θ₀)` as `h·u`
(`H ⊔ U = ⊤`, `H ◁ HU`), where `u = h⁻¹ g ∈ I(θ₀) ⊓ U ≤ C` (`inertia_inf_uInHu_le_cInHu`).  With
`HC ◁ HU` (`hcInHu_normal`) this makes `Ind_{HC}^{HU}` of an `HC`-character over `θ₀` irreducible. -/
theorem inertia_eq_hcInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
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
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief :=
  inertia_eq_hcInHu_of_inf_le data chief (inertia_inf_uInHu_le_cInHu data chief hcaseB hθbar)

/-- **Inertia lift `I_{HU}(θ₀) = HC`, generic over the factor family.**  As `inertia_eq_hcInHu_caseA`
but taking the order-`p`, `U`-invariant, spanning family `Hpart` directly (via
`chiefFactor_caseA_char_inertia_gen`), so the `W1`-conjugates `{S₀^w}` — not the producer's
`caseA.Hpart` — drive the inertia lift for the free-`W1`-orbit character of (9.8.c). -/
theorem inertia_eq_hcInHu_gen [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data)
    {ι : Type*} (Hpart : ι → Subgroup (↥data.H ⧸ chief.N))
    (hp_order : ∀ i, Nat.card ↥(Hpart i) = chief.p)
    (hspan : ⨆ i, Hpart i = ⊤)
    (haInv : ∀ i, IsAInvariant (uActionHom data chief) (Hpart i))
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∀ i, ∃ x ∈ Hpart i,
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief :=
  inertia_eq_hcInHu_of_inf_le data chief
    (inertia_inf_uInHu_le_cInHu_of_realized data chief
      (fun a g hag hfix =>
        caseB_inertia_realized_of_charInertia
          (fun g' hfix' =>
            caseB_char_inertia_inflation_of_core
              (fun g'' hinv =>
                chiefFactor_caseA_char_inertia_gen Hpart hp_order hspan haInv hreg g'' hinv)
              g' hfix')
          a g hag hfix))

/-- **Inertia lift `I_{HU}(θ₀) = HC` in Clifford case (a)** — the non-Galois analog of
`inertia_eq_hcInHu`.  For a **regular** chief-factor character `θ̄` (nontrivial on each order-`p`
Clifford summand `Hpart i`), the inertia of its inflation `θ₀` in `HU` is `HC`.  Feeds the proven
case-(a) core `chiefFactor_caseA_char_inertia` through the same case-agnostic plumbing
(`caseB_char_inertia_inflation_of_core` → `caseB_inertia_realized_of_charInertia` →
`inertia_inf_uInHu_le_cInHu_of_realized` → `inertia_eq_hcInHu_of_inf_le`) that case (b) uses with
`chiefFactor_caseB_char_inertia`.  This is the (9.8.b)/(9.8.c) degree input for the reducible
(= regular) characters. -/
theorem inertia_eq_hcInHu_caseA [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∀ i, ∃ x ∈ caseA.Hpart i,
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief :=
  inertia_eq_hcInHu_gen data chief caseA.Hpart caseA.Hpart_order caseA.Hpart_iSup
    caseA.Hpart_aInvariant hreg

/-- **Peterfalvi (9.7) case (b) carrier.**  When `U` acts irreducibly on the chief factor
`H̄ = H/H₀` (Clifford case (b), the left branch of `chiefFactor_clifford_U_dichotomy`), the
field-model divisibilities of `CliffordCaseBData` hold: with `chars.u = |Ū|` (pinned in
`Section11CharacterData.u_eq_card_quotient`), `Coprime |Ū| (p-1)` and `|Ū| ∣ (p^q-1)/(p-1)` are the
unconditional `chiefFactor_caseB_image_coprime` / `chiefFactor_caseB_image_dvd_norm`. -/
noncomputable def clifford_caseB_data [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    CliffordCaseBData chars where
  field_model := True
  field_model_holds := trivial
  Ubar_cyclic := (chiefFactor_caseB_image_cyclic chief hcaseB).1
  u_coprime_p_sub_one := by
    rw [chars.u_eq_card_quotient]; exact chiefFactor_caseB_image_coprime chief hcaseB
  u_dvd_norm_quotient := by
    rw [chars.u_eq_card_quotient]; exact chiefFactor_caseB_image_dvd_norm chief hcaseB
  actsIrreducibly := hcaseB

/-- **Peterfalvi (9.7) case (a) carrier.**  When `H̄` contains a `U`-invariant order-`p` factor `S₀`
(Clifford case (a), the right branch of `chiefFactor_clifford_U_dichotomy`), the chief factor splits
as the internal direct product of `q = |W₁|` order-`p` factors — the `U W₁`-orbit of `S₀`, packaged
as a `Fin q`-family via the `SupIndep` partition of `exists_supIndep_aInvariant_family_of_iSup` — and
the `U`-action on `S₀` has image of order `a ∣ p - 1` (`aInvariantRestrictAut_range_card_dvd`). -/
noncomputable def clifford_caseA_data [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    {S₀ : Subgroup (↥data.H ⧸ chief.N)} (hS₀ne : S₀ ≠ ⊥)
    (hS₀inv : IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) S₀)
    (hS₀card : Nat.card ↥S₀ = chief.p)
    (hirr₀ : ∀ J, IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) J → J ≤ S₀ → J = ⊥ ∨ J = S₀) :
    CliffordCaseAData chars := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  haveI : chief.N.Normal := chief.N_normal
  set act := typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  have hUnorm : act.U.Normal := (typeP_uW1_frobenius data.typeP hU).isNormal
  -- The `U W₁`-orbit of `S₀` spans `H̄` (irreducibility), giving a `SupIndep` family of order-`p`
  -- factors whose count `k` satisfies `|H̄| = |S₀|^k`.
  have hspan : ⨆ a, act.φ a • S₀ = ⊤ :=
    iSup_smul_eq_top_of_irreducible (φ := act.φ) chief.quotient_chiefFactor hS₀ne
  -- (`Exists` cannot be destructured into the `Type`-valued `CliffordCaseAData`; use `choose`.)
  have hexist := exists_supIndep_aInvariant_family_of_iSup
    (φ := φU) (S := fun a => act.φ a • S₀) (n := Nat.card ↥S₀)
    (fun x y => chief.quotient_elementaryAbelian.comm x y) hspan
    (fun a => isAInvariant_comp_subtype_pointwise_smul hUnorm hS₀inv a)
    (fun a J hJinv hJle => forall_aInvariant_le_pointwise_smul hUnorm hirr₀ a J hJinv hJle)
    (fun a _ => card_pointwise_smul act.φ a S₀)
  let t : Finset ↥(data.typeP.U ⊔ data.typeP.W1) := hexist.choose
  have ht_card : Nat.card (↥data.H ⧸ chief.N) = Nat.card ↥S₀ ^ t.card := hexist.choose_spec.2.2.2
  -- `|H̄| = p^t.card` and `|H̄| = p^q`, so `t.card = q`.
  rw [hS₀card, chiefFactor_quotient_card chief] at ht_card
  have ht_card_q : t.card = data.q :=
    (Nat.pow_right_injective chief.p_prime.two_le ht_card).symm
  -- Reindex the `q`-element orbit family by `Fin q`.
  let e : ↥t ≃ Fin data.q := t.equivFin.trans (finCongr ht_card_q)
  refine
    { Hpart := fun j => act.φ ↑(e.symm j) • S₀
      Hpart_order := fun j => (card_pointwise_smul act.φ _ S₀).trans hS₀card
      Hpart_iSup := by
        rw [← hexist.choose_spec.2.2.1]
        refine le_antisymm (iSup_le fun j => le_iSup₂_of_le _ (e.symm j).2 le_rfl) ?_
        exact iSup₂_le fun i hi =>
          le_iSup_of_le (e ⟨i, hi⟩) (le_of_eq (by rw [Equiv.symm_apply_apply]))
      Hpart_aInvariant := fun j =>
        isAInvariant_comp_subtype_pointwise_smul hUnorm hS₀inv ↑(e.symm j)
      Hpart_iSupIndep := hexist.choose_spec.1.independent.comp e.symm.injective
      S0 := S₀
      S0_aInvariant := hS₀inv
      orbitRep := fun j => ↑(e.symm j)
      Hpart_orbit := fun j => rfl
      a := Nat.card ↥(aInvariantRestrictAut hS₀inv).range
      a_pos := Nat.card_pos
      a_dvd_p_sub_one := ?_
      a_eq_card_restrictAut_range := rfl }
  -- `a = |U-image on S₀| ∣ |S₀| - 1 = p - 1` (the order-`p` factor is cyclic, `Aut ≅ (ZMod p)ˣ`).
  have hdvd := aInvariantRestrictAut_range_card_dvd hS₀inv (hS₀card ▸ chief.p_prime)
  rwa [hS₀card] at hdvd

/-- **`|S₀| = p`**: the orbit generator `S₀` (`CliffordCaseAData.S0`) has order `p`.  Each summand
`Hpart j = φ(orbitRep j) • S₀` (`Hpart_orbit`) is an automorphic image of `S₀` under the chief-factor
action `φ = quotientMulAutHom`, hence has the same order (`card_pointwise_smul`), which is `p`
(`Hpart_order`).  A foundational input for the (9.8.c) constant-factor-data construction (`S₀ ≅ ℤ/p`
has exactly `p` characters, `p-1` of them nontrivial). -/
theorem caseA_S0_card [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    Nat.card ↥caseA.S0 = chief.p := by
  have h := caseA.Hpart_order ⟨0, data.nontrivial.2.1.pos⟩
  rwa [caseA.Hpart_orbit ⟨0, data.nontrivial.2.1.pos⟩, card_pointwise_smul] at h

/-! ### Peterfalvi (9.7.a): the free `W₁`-orbit decomposition `H̄ = ⊕_{w∈W₁} S₀^w`

Peterfalvi (9.7.a), case `k = q` of the Clifford dichotomy: the order-`p` `U`-invariant generator
`S₀ = H₁` has `q = |W₁|` distinct `W₁`-conjugates `{S₀^w | w ∈ W₁}`, and they realise `H̄` as their
internal direct product, freely indexed by `W₁`.  The producer `clifford_caseA_data` carries the
summands only as an *arbitrary* `U`-supindep family (`orbitRep : Fin q → U ⊔ W₁` from a choice
function), so this free-`W₁`-orbit structure — needed for the (9.8.d) (γ) `W₁`-injectivity — is
reconstructed here directly from the stored data (`S₀` order `p`, `U`-invariant;
`chief.quotient_chiefFactor` `U W₁`-irreducibility; `|W₁| = q` and the Frobenius `U ⋊ W₁`). -/

/-- The `W₁`-orbit family of `S₀` (indexed by `W₁` realized inside `U ⊔ W₁`), `w ↦ S₀^w`. -/
noncomputable def caseA_wOrbit [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) → Subgroup (↥data.H ⧸ chief.N) :=
  fun w => quotientMulAutHom chief.N_aInvariant ↑w • caseA.S0

/-- `caseA_wOrbit caseA 1 = S₀` (identity element gives the generator). -/
theorem caseA_wOrbit_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    caseA_wOrbit caseA 1 = caseA.S0 := by
  rw [caseA_wOrbit]
  haveI : chief.N.Normal := chief.N_normal
  change quotientMulAutHom chief.N_aInvariant
      ↑(1 : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) • caseA.S0 = caseA.S0
  rw [Subgroup.coe_one, map_one, one_smul]

/-- **The `W₁`-orbit of `S₀` spans `H̄`** (Peterfalvi (9.7.a)): the `U W₁`-orbit of `S₀` (spanning by
`U W₁`-irreducibility `chief.quotient_chiefFactor`) collapses to the `W₁`-orbit
(`iSup_phi_smul_eq_iSup_W_of_normal`, `U`-invariance), which therefore spans. -/
theorem caseA_wOrbit_iSup [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ⨆ w : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)),
      caseA_wOrbit caseA w = ⊤ := by
  haveI : chief.N.Normal := chief.N_normal
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have hS0card : Nat.card ↥caseA.S0 = chief.p := caseA_S0_card caseA
  have hS0ne : caseA.S0 ≠ ⊥ := by
    intro h0; rw [h0, Subgroup.card_bot] at hS0card
    exact chief.p_prime.one_lt.ne' hS0card.symm
  have hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (typeP_uW1_frobenius data.typeP hU).isNormal
  have hS0inv : IsAInvariant
      ((quotientMulAutHom chief.N_aInvariant).comp
        (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype) caseA.S0 :=
    caseA.S0_aInvariant
  have hsup : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      ⊔ (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hspan_amb : ⨆ a : ↥(data.typeP.U ⊔ data.typeP.W1),
      quotientMulAutHom chief.N_aInvariant a • caseA.S0 = ⊤ :=
    iSup_smul_eq_top_of_irreducible chief.quotient_chiefFactor hS0ne
  have hcollapse := iSup_phi_smul_eq_iSup_W_of_normal (φ := quotientMulAutHom chief.N_aInvariant)
    (U := data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
    (W := data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) hUnorm hS0inv
  have hL : ⨆ a : ↥((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
        ⊔ (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))),
      quotientMulAutHom chief.N_aInvariant ↑a • caseA.S0 = ⊤ := by
    have hcongr : ⨆ a : ↥((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
          ⊔ (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))),
        quotientMulAutHom chief.N_aInvariant ↑a • caseA.S0
        = ⨆ a : ↥(data.typeP.U ⊔ data.typeP.W1),
          quotientMulAutHom chief.N_aInvariant a • caseA.S0 :=
      Equiv.iSup_congr (((MulEquiv.subgroupCongr hsup).trans Subgroup.topEquiv).toEquiv)
        (fun a => rfl)
    rw [hcongr, hspan_amb]
  rw [hcollapse] at hL
  exact hL

/-- **Peterfalvi (9.7.a): the `W₁`-orbit of `S₀` is `iSupIndep`** (free internal direct product).
The `q` conjugates `S₀^w` (`w ∈ W₁`), each of order `p`, span `H̄` (`caseA_wOrbit_iSup`) and satisfy
`∏ |S₀^w| = p^q = |H̄|`; so `Subgroup.noncommPiCoprod` is bijective
(`noncommPiCoprod_bijective_of_card`), giving independence
(`iSupIndep_of_noncommPiCoprod_injective_comm`).  This is the free `W₁`-indexing
`{Hᵢ} = {S₀^w | w ∈ W₁}` of Peterfalvi (9.7.a). -/
theorem caseA_wOrbit_iSupIndep [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [Fintype ↥((data.typeP.W1).subgroupOf (data.typeP.U ⊔ data.typeP.W1))] :
    iSupIndep (caseA_wOrbit caseA) := by
  classical
  haveI : chief.N.Normal := chief.N_normal
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  letI : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.comm }
  have hS0card : Nat.card ↥caseA.S0 = chief.p := caseA_S0_card caseA
  have hspanW := caseA_wOrbit_iSup caseA
  have hcardW1 : Fintype.card ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      = data.q := by
    rw [TypesIIIIIIVSetup.q, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_right : data.typeP.W1 ≤ data.typeP.U ⊔ data.typeP.W1)).toEquiv
  have hprodcard : ∏ w : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)),
      Nat.card ↥(caseA_wOrbit caseA w) = Nat.card (↥data.H ⧸ chief.N) := by
    have hval : ∀ w, Nat.card ↥(caseA_wOrbit caseA w) = chief.p := fun w => by
      rw [caseA_wOrbit, card_pointwise_smul, hS0card]
    simp only [hval]
    rw [Finset.prod_const, Finset.card_univ, hcardW1, chiefFactor_quotient_card chief]
  have hcomm : Pairwise fun i j : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) =>
      ∀ x y : (↥data.H ⧸ chief.N), x ∈ caseA_wOrbit caseA i → y ∈ caseA_wOrbit caseA j →
        Commute x y :=
    fun i j _ x y _ _ => chief.quotient_elementaryAbelian.comm x y
  have hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm) :=
    noncommPiCoprod_bijective_of_card hcomm hspanW hprodcard
  exact iSupIndep_of_noncommPiCoprod_injective_comm hcomm hbij.injective

/-- **Peterfalvi (9.7.a) summand-complement `W = ⨆_{w∈W₁#} S₀^w`** (`H₂…H_q` of Peterfalvi): the join
of the nontrivial `W₁`-conjugates of `S₀`.  Complements `S₀` in `H̄` (`caseA_S0_sup_wComplement`,
`caseA_S0_inf_wComplement`) and contains every `S₀^w` with `w ≠ 1` (used for `horbit`). -/
noncomputable def caseA_wComplement [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    Subgroup (↥data.H ⧸ chief.N) :=
  ⨆ (w) (_ : w ≠ 1), caseA_wOrbit caseA w

/-- The summand-complement `W` is `U`-invariant (a join of `U`-invariant conjugates). -/
theorem caseA_wComplement_aInvariant [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    IsAInvariant (uActionHom data chief) (caseA_wComplement caseA) := by
  haveI : chief.N.Normal := chief.N_normal
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (typeP_uW1_frobenius data.typeP hU).isNormal
  refine OddOrder.Isaacs.Ch03.IsAInvariant.iSup
    (fun w => OddOrder.Isaacs.Ch03.IsAInvariant.iSup (fun _ => ?_))
  rw [caseA_wOrbit]
  exact isAInvariant_comp_subtype_pointwise_smul hUnorm caseA.S0_aInvariant ↑w

/-- **`S₀ ⊔ W = ⊤`** (Peterfalvi (9.7.a) spanning): `S₀ = S₀^1` together with the `w ≠ 1`
conjugates gives the full `W₁`-orbit, which spans `H̄` (`caseA_wOrbit_iSup`). -/
theorem caseA_S0_sup_wComplement [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    caseA.S0 ⊔ caseA_wComplement caseA = ⊤ := by
  have hspanW := caseA_wOrbit_iSup caseA
  rw [← caseA_wOrbit_one caseA, caseA_wComplement, ← hspanW]
  refine le_antisymm
    (sup_le (le_iSup (caseA_wOrbit caseA) 1)
      (iSup₂_le fun w _ => le_iSup (caseA_wOrbit caseA) w)) ?_
  refine iSup_le fun w => ?_
  by_cases hw : w = 1
  · rw [hw]; exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂ (f := fun w (_ : w ≠ 1) => caseA_wOrbit caseA w) w hw)

/-- **`S₀ ⊓ W = ⊥`** (Peterfalvi (9.7.a) freeness): from the independence of the `W₁`-orbit
(`caseA_wOrbit_iSupIndep`), the generator `S₀ = S₀^1` is disjoint from the join of the other
conjugates `W = ⨆_{w≠1} S₀^w`.  Together with `caseA_S0_sup_wComplement` this exhibits `H̄ = S₀ ⊕ W`,
`[H̄ : W] = p`. -/
theorem caseA_S0_inf_wComplement [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [Fintype ↥((data.typeP.W1).subgroupOf (data.typeP.U ⊔ data.typeP.W1))] :
    caseA.S0 ⊓ caseA_wComplement caseA = ⊥ := by
  have hdisj : Disjoint (caseA_wOrbit caseA 1) (⨆ (w) (_ : w ≠ 1), caseA_wOrbit caseA w) :=
    (iSupIndep_def.mp (caseA_wOrbit_iSupIndep caseA)) 1
  rw [caseA_wOrbit_one caseA] at hdisj
  exact disjoint_iff.mp hdisj

/-- **Orbit-transport iso** `S₀ ≃* Hpart j`: the chief-factor automorphism `φ(orbitRep j)` maps the
generator `S₀` isomorphically onto the summand `Hpart j = φ(orbitRep j) • S₀` (`Hpart_orbit`).  The
transport used to define the (9.8.c) constant-factor-data characters (assign one `S₀`-character to
every summand). -/
noncomputable def caseA_orbitEquiv [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) (j : Fin data.q) :
    ↥caseA.S0 ≃* ↥(caseA.Hpart j) :=
  (Subgroup.equivMapOfInjective caseA.S0
      (quotientMulAutHom chief.N_aInvariant (caseA.orbitRep j)).toMonoidHom
      (quotientMulAutHom chief.N_aInvariant (caseA.orbitRep j)).injective).trans
    (MulEquiv.subgroupCongr (by rw [caseA.Hpart_orbit j]; rfl))

/-- **Reducible induction ⟹ full inertia** (prime-index Clifford dichotomy): if `Ind_{HU}^M χ` is
reducible for `χ ∈ Irr(HU)`, then `I_M(χ) = ⊤` (`χ` is `M`-invariant).  `HU ◁ M` with `[M:HU] = q`
prime (`huSub_index_eq_q`), so `HU ≤ I_M(χ) ≤ M` forces `I_M(χ) ∈ {HU, M}`
(`eq_of_le_of_prime_index`); reducibility excludes `I_M(χ) = HU` (contrapositive of
`isIrreducibleCharacter_induce_of_inertia_eq`).  The `M`-fixedness feeding the (9.8.c) `Xmu`
injectivity (`induce_injective_of_inertia_stable`) in the surjectivity route to `|Xmu| = p-1`. -/
theorem inertia_eq_top_of_induceHU_not_irreducible [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) [Fintype ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    (χ : IrreducibleCharacter ↥(huSub data))
    (hred : ¬ IsIrreducibleCharacter
      (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ))) :
    ClassFunction.inertia (χ : ClassFunction ↥(huSub data) ℂ) = ⊤ := by
  haveI := huSub_normal data
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hne : ClassFunction.inertia (χ : ClassFunction ↥(huSub data) ℂ) ≠ huSub data :=
    mt (isIrreducibleCharacter_induce_of_inertia_eq χ) hred
  have hle : huSub data ≤ ClassFunction.inertia (χ : ClassFunction ↥(huSub data) ℂ) :=
    ClassFunction.subgroup_le_inertia _
  have hprime : (huSub data).index.Prime := by rw [huSub_index_eq_q]; exact data.nontrivial.2.1
  by_contra hnt
  exact hne (eq_of_le_of_prime_index hle hprime hnt)

/-- **`Ind_{HU}^M` is injective on reducible-inducing characters** (`Xmu` injectivity): if
`Ind_{HU}^M χ` is reducible and `Ind_{HU}^M χ = Ind_{HU}^M ψ`, then `ψ = χ`.  Reducibility makes `χ`
`M`-invariant (`inertia_eq_top_of_induceHU_not_irreducible`), and a full-inertia character is
`Ind`-injective (`induce_injective_of_inertia_stable`, via `induce_eq_induce_iff_conj`).  Combined
with `reducible_count_sOf_H0C` (`|reducibles| = p-1`) this gives `|Xmu| = p-1` for the (9.8.c)
parity dichotomy (`Xmu = {ζ ∈ Xθ | Ind_M ζ reducible}`), the surjectivity route to conjunct (c). -/
theorem caseA_induceHU_inj_of_reducible [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) [Fintype ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    {χ ψ : IrreducibleCharacter ↥(huSub data)}
    (hχred : ¬ IsIrreducibleCharacter
      (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)))
    (h : ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce (huSub data) (ψ : ClassFunction ↥(huSub data) ℂ)) :
    ψ = χ := by
  haveI := huSub_normal data
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hinertia := inertia_eq_top_of_induceHU_not_irreducible data χ hχred
  refine induce_injective_of_inertia_stable (fun g => ?_) h
  apply IrreducibleCharacter.ext
  rw [IrreducibleCharacter.coe_conjBy]
  exact ClassFunction.mem_inertia.mp (by rw [hinertia]; exact Subgroup.mem_top g)

/-- **A nonempty left-translation-closed subset of a group is everything.**  If `T` is nonempty and
closed under left multiplication by *every* group element (`∀ a b, b ∈ T → a·b ∈ T`), then `T = univ`
(any `w = (w·t⁻¹)·t ∈ T`).  The `W₁`-transitivity core of the (9.8.c) surjectivity route: the set of
`W₁`-conjugates `S₀^w` on which a constituent `θ̄₀` is nontrivial is `W₁`-translation-invariant (from
`M`-invariance of the reducible constituent) — so if nonempty (`H ⊄ ker`) it is *all* conjugates,
making `θ̄₀` regular.  Since the `W₁`-conjugates are indexed by `W₁` itself with `W₁` acting by
translation, transitivity is free (no producer `W₁`-permutation is needed). -/
theorem eq_univ_of_nonempty_of_mul_mem_left {W : Type*} [Group W] {T : Set W}
    (hne : T.Nonempty) (hclosed : ∀ a : W, ∀ b ∈ T, a * b ∈ T) : T = Set.univ := by
  obtain ⟨t, ht⟩ := hne
  refine Set.eq_univ_of_forall fun w => ?_
  have := hclosed (w * t⁻¹) t ht
  simpa using this

/-- **`Ū`-invariance of nontriviality on any `U`-invariant subgroup**: for a `U`-invariant subgroup
`K ≤ H̄` (`IsAInvariant (uActionHom data chief) K`), a character `θ` is nontrivial on `K` iff its
`U`-translate `θ ∘ φ_U(a)` is.  Since `φ_U(a)` restricts to a bijection of `K` (`hK`, invertible), the
two restrictions have the same triviality.  Generalises `caseA_uActionHom_comp_subtype_eq_one_iff`
(the `Hpart i` case) to any `U`-invariant `K` — used on the `W₁`-conjugates `q(w) • S₀` (also
`U`-invariant, `U ◁ U W₁`) in the (9.8.c) surjectivity regularity argument. -/
theorem comp_uActionHom_comp_subtype_eq_one_iff_of_aInvariant [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {K : Subgroup (↥data.H ⧸ chief.N)} (hK : IsAInvariant (uActionHom data chief) K)
    (a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    (θ.comp (uActionHom data chief a).toMonoidHom).comp K.subtype = 1
      ↔ θ.comp K.subtype = 1 := by
  constructor
  · intro h
    refine MonoidHom.ext fun y => ?_
    have hval := DFunLike.congr_fun h ⟨_, hK.inv_smul_mem a y.2⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply,
      MulEquiv.coe_toMonoidHom, MulAut.apply_inv_self] at hval ⊢
    exact hval
  · intro h
    refine MonoidHom.ext fun x => ?_
    have hval := DFunLike.congr_fun h ⟨_, hK.smul_mem a x.2⟩
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply,
      MulEquiv.coe_toMonoidHom] using hval

/-- **`Ū`-invariance of the per-factor nontrivial set**: a character `θ` of `H̄` is nontrivial on the
Clifford summand `Hpart i` iff its `U`-translate `θ ∘ φ_U(a)` is.  The `Hpart i` case of
`comp_uActionHom_comp_subtype_eq_one_iff_of_aInvariant` (`Hpart_aInvariant`).  So the set of summands
on which a constituent `θ̄₀` is nontrivial is constant along the `Ū`-orbit of `θ̄₀` — the input
(together with `M`-invariance and `eq_univ_of_nonempty_of_mul_mem_left`) to the (9.8.c) surjectivity
that a reducible constituent is regular. -/
theorem caseA_uActionHom_comp_subtype_eq_one_iff [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    {i : Fin data.q} (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    (θ.comp (uActionHom data chief a).toMonoidHom).comp (caseA.Hpart i).subtype = 1
      ↔ θ.comp (caseA.Hpart i).subtype = 1 :=
  comp_uActionHom_comp_subtype_eq_one_iff_of_aInvariant (caseA.Hpart_aInvariant i) a θ

/-- **A regular character nontrivial on each `W1`-conjugate of `S₀`** (Clifford case (a)).
Instantiates the elementary `(9.7)` decomposition `H̄ = ⊕_{w∈W1} S₀^w` (`wConjugate_coprod_bijective`,
with the chief-factor `U`-action, `act.U ⊔ act.E = ⊤`, `|H̄| = p^{|W1|}`) and feeds the resulting
internal-direct-product bijection to `exists_regular_char_of_bijective`. -/
theorem clifford_caseA_exists_regular_char_on_conjugates [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    {S₀ : Subgroup (↥data.H ⧸ chief.N)} (hS₀ne : S₀ ≠ ⊥)
    (hS₀inv : IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) S₀)
    (hS₀card : Nat.card ↥S₀ = chief.p) :
    ∃ θ : (↥data.H ⧸ chief.N) →* ℂˣ,
      ∀ w : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).E,
        ∃ x ∈ (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).φ ↑w • S₀, θ x ≠ 1 := by
  classical
  letI : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.comm }
  set act := typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant with hact
  haveI : Fintype ↥act.E := Fintype.ofFinite _
  have hUnorm : act.U.Normal := (typeP_uW1_frobenius data.typeP data.nontrivial.1).isNormal
  have hspan0 : ⨆ a, act.φ a • S₀ = ⊤ :=
    iSup_smul_eq_top_of_irreducible (φ := act.φ) chief.quotient_chiefFactor hS₀ne
  have htop : act.U ⊔ act.E = ⊤ := by
    change data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
        ⊔ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) = ⊤
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hspan : ⨆ a : ↥(act.U ⊔ act.E), act.φ ↑a • S₀ = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hspan0]
    exact iSup_le fun b => le_iSup (fun a : ↥(act.U ⊔ act.E) => act.φ ↑a • S₀)
      ⟨b, htop.ge (Subgroup.mem_top b)⟩
  have hEcard : Fintype.card ↥act.E = data.q := by
    rw [Fintype.card_eq_nat_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hKcard : Nat.card (↥data.H ⧸ chief.N) = (Nat.card ↥S₀) ^ (Fintype.card ↥act.E) := by
    rw [hS₀card, hEcard, chiefFactor_quotient_card chief]
  exact exists_regular_char_of_bijective _
    (wConjugate_coprod_bijective hUnorm hS₀inv hspan hKcard)
    (fun w => by rw [card_pointwise_smul, hS₀card]; exact chief.p_prime)

/-- **A regular character not fixed by some `W1`-element** (Clifford case (a)).  As
`clifford_caseA_exists_regular_char_on_conjugates`, but additionally `θ` is *not* fixed by the
`W1`-action `act.φ(w₀)` for some `w₀` — the free-`W1`-orbit character, via
`exists_regular_char_not_fixed` (`τ = act.φ(w₀)` permutes the conjugate factors, `i₀=1 ≠ j₀=w₀`).
Needs `3 ≤ p` (odd order).  This non-`W1`-fixedness supplies `I_M(χ) ≠ M` ⟹ `I_M(χ) = HU` for the
`induceHU`-irreducible character of degree `qu` in (9.8.c). -/
theorem clifford_caseA_exists_regular_char_not_fixed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    {S₀ : Subgroup (↥data.H ⧸ chief.N)} (hS₀ne : S₀ ≠ ⊥)
    (hS₀inv : IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) S₀)
    (hS₀card : Nat.card ↥S₀ = chief.p) (hp3 : 3 ≤ chief.p) :
    ∃ θ : (↥data.H ⧸ chief.N) →* ℂˣ,
      (∀ w : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).E,
        ∃ x ∈ (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).φ ↑w • S₀, θ x ≠ 1) ∧
      ∃ w₀ : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).E,
        θ.comp ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ ↑w₀).toMonoidHom ≠ θ := by
  classical
  letI : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.comm }
  set act := typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant with hact
  haveI : Fintype ↥act.E := Fintype.ofFinite _
  have hUnorm : act.U.Normal := (typeP_uW1_frobenius data.typeP data.nontrivial.1).isNormal
  have hspan0 : ⨆ a, act.φ a • S₀ = ⊤ :=
    iSup_smul_eq_top_of_irreducible (φ := act.φ) chief.quotient_chiefFactor hS₀ne
  have htop : act.U ⊔ act.E = ⊤ := by
    change data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
        ⊔ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) = ⊤
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hspan : ⨆ a : ↥(act.U ⊔ act.E), act.φ ↑a • S₀ = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hspan0]
    exact iSup_le fun b => le_iSup (fun a : ↥(act.U ⊔ act.E) => act.φ ↑a • S₀)
      ⟨b, htop.ge (Subgroup.mem_top b)⟩
  have hEcard : Fintype.card ↥act.E = data.q := by
    rw [Fintype.card_eq_nat_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hKcard : Nat.card (↥data.H ⧸ chief.N) = (Nat.card ↥S₀) ^ (Fintype.card ↥act.E) := by
    rw [hS₀card, hEcard, chiefFactor_quotient_card chief]
  haveI : Nontrivial ↥act.E := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [Nat.card_eq_fintype_card, hEcard]; exact data.nontrivial.2.1.one_lt)
  obtain ⟨w₀, hw₀⟩ := exists_ne (1 : ↥act.E)
  obtain ⟨θ, hreg, hnf⟩ := exists_regular_char_not_fixed
    (S := fun w : ↥act.E => act.φ ↑w • S₀) _
    (wConjugate_coprod_bijective hUnorm hS₀inv hspan hKcard)
    (fun w => by rw [card_pointwise_smul, hS₀card]; exact chief.p_prime)
    (fun w => by rw [card_pointwise_smul, hS₀card]; exact hp3)
    (Ne.symm hw₀) (act.φ ↑w₀)
    (by simp only [Subgroup.coe_one, map_one, one_smul])
  exact ⟨θ, hreg, w₀, hnf⟩

/-- **`I_HU(θ₀) = HC` for a `W1`-conjugate regular character** (Clifford case (a), free orbit).
Applies the generic inertia lift `inertia_eq_hcInHu_gen` to the `W1`-conjugate family
`{act.φ↑w • S₀}_{w∈W1}`: each is `U`-invariant (since `S₀` is and `U ◁ UW1`, so `U` fixes each
conjugate as a subgroup), they span `H̄` by (9.7), and have order `p`.  For a character nontrivial on
each (a regular character), its inflation `θ₀` has inertia `HC` in `HU` — the `I_HU = HC` step toward
the degree-`qu` irreducible of (9.8.c). -/
theorem clifford_caseA_regular_inertia_hc [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    {S₀ : Subgroup (↥data.H ⧸ chief.N)} (hS₀ne : S₀ ≠ ⊥)
    (hS₀inv : IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) S₀)
    (hS₀card : Nat.card ↥S₀ = chief.p)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∀ w : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).E,
      ∃ x ∈ (typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ ↑w • S₀,
        (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
          ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief := by
  set act := typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant with hact
  have hUnorm : act.U.Normal := (typeP_uW1_frobenius data.typeP data.nontrivial.1).isNormal
  have hspan0 : ⨆ a, act.φ a • S₀ = ⊤ :=
    iSup_smul_eq_top_of_irreducible (φ := act.φ) chief.quotient_chiefFactor hS₀ne
  have htop : act.U ⊔ act.E = ⊤ := by
    change data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
        ⊔ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) = ⊤
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hspan : ⨆ a : ↥(act.U ⊔ act.E), act.φ ↑a • S₀ = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hspan0]
    exact iSup_le fun b => le_iSup (fun a : ↥(act.U ⊔ act.E) => act.φ ↑a • S₀)
      ⟨b, htop.ge (Subgroup.mem_top b)⟩
  have hspan_W : ⨆ w : ↥act.E, act.φ ↑w • S₀ = ⊤ :=
    (iSup_phi_smul_eq_iSup_W_of_normal (W := act.E) hUnorm hS₀inv).symm.trans hspan
  exact inertia_eq_hcInHu_gen data chief (fun w : ↥act.E => act.φ ↑w • S₀)
    (fun w => (card_pointwise_smul act.φ ↑w S₀).trans hS₀card)
    hspan_W
    (fun w => isAInvariant_comp_subtype_pointwise_smul hUnorm hS₀inv ↑w)
    hreg

/-- **Regular character with `I_HU = HC`, not `W1`-fixed** (Clifford case (a), the (9.8.c) object).
Packages `clifford_caseA_exists_regular_char_not_fixed` (a regular hom `θ` on `H̄` in a free
`W1`-orbit) into the inertia statement: the inflation of `linearIrreducibleCharacter θ` has inertia
`HC` in `HU` (via `clifford_caseA_regular_inertia_hc`), and `θ` carries the non-`W1`-fixedness datum
`w₀` for the downstream `I_M = HU` step.  This is the existence of the (9.8.c) seed character. -/
theorem clifford_caseA_exists_char_inertia_hc_not_fixed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    {S₀ : Subgroup (↥data.H ⧸ chief.N)} (hS₀ne : S₀ ≠ ⊥)
    (hS₀inv : IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) S₀)
    (hS₀card : Nat.card ↥S₀ = chief.p) (hp3 : 3 ≤ chief.p) :
    ∃ θ : (↥data.H ⧸ chief.N) →* ℂˣ,
      ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
          (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
            (ClassFunction.compHom (QuotientGroup.mk' chief.N)
              (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief ∧
      ∃ w₀ : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).E,
        θ.comp ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ ↑w₀).toMonoidHom ≠ θ := by
  obtain ⟨θ, hreg, w₀, hnf⟩ :=
    clifford_caseA_exists_regular_char_not_fixed chief hS₀ne hS₀inv hS₀card hp3
  refine ⟨θ, ?_, w₀, hnf⟩
  refine clifford_caseA_regular_inertia_hc chief hS₀ne hS₀inv hS₀card
    (θbar := linearIrreducibleCharacter θ) ?_
  intro w
  obtain ⟨x, hx, hxne⟩ := hreg w
  refine ⟨x, hx, ?_⟩
  simp only [linearIrreducibleCharacter_apply]
  exact fun h => hxne ((Units.val_injective h).trans (map_one θ))

/-- **Peterfalvi (9.7)**: the Clifford-theory dichotomy for the action on the chief factor `H/H_0`.

The case split is `chiefFactor_clifford_U_dichotomy`: `U` acts on `H̄ = H/H₀` either irreducibly
(case (b)) or with a `U`-invariant order-`p` factor (case (a)).  Each branch is packaged into its
carrier: `clifford_caseB_data` (the Singer field-model divisibilities `Coprime |Ū| (p-1)`,
`|Ū| ∣ (p^q-1)/(p-1)`, with `chars.u = |Ū|` pinned in `Section11CharacterData.u_eq_card_quotient`)
and `clifford_caseA_data` (the `q` order-`p` Clifford factors and the bound `a ∣ p-1`). -/
theorem clifford_dichotomy [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) :
    Nonempty (CliffordCaseAData chars) ∨ Nonempty (CliffordCaseBData chars) := by
  rcases chiefFactor_clifford_U_dichotomy chief with hcaseB | ⟨S₀, hS₀ne, hS₀inv, hS₀card, hirr₀⟩
  · exact Or.inr ⟨clifford_caseB_data chars hcaseB⟩
  · exact Or.inl ⟨clifford_caseA_data chars hS₀ne hS₀inv hS₀card hirr₀⟩

end OddOrder.Peterfalvi.S11

