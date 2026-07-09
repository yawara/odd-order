import OddOrder.Peterfalvi.S11_MaximalII_III_IV.WielandtSetup

/-!
# ChiefFactorCore

Prefix-split from `OddOrder.Peterfalvi.S11_MaximalII_III_IV.CliffordData` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# Peterfalvi (9.5)-(9.7) — Clifford-theory data over the chief factor

Split from the former monolithic `OddOrder.Peterfalvi.S11_MaximalII_III_IV` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S11
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)
open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}


/-! ## (9.5)--(9.7): Clifford-theory data over the selected chief factor -/

/-! ### The genuine character families `𝒳`, `𝒮` of Peterfalvi (9.5)

We realise Peterfalvi's families honestly (following the `S12.inducedFamily` pattern), so the
formerly free `Section11CharacterData` fields are pinned to genuine constructions.  `HU = H ⊔ U`
is realised inside `↥M` as `(H ⊔ U).subgroupOf M`; then

* `𝒳 = {χ ∈ Irr(HU) | H ⊄ Ker χ}` (`xiSet`),
* `𝒮 = {Ind_{HU}^M χ | χ ∈ 𝒳}` (`sSet`),

with the restricted families `𝒳(Y) = {χ ∈ 𝒳 | Y ⊆ Ker χ}` (`xiOf`) and `𝒮(Y) = Ind 𝒳(Y)` (`sOf`)
for a subgroup `Y` (the cases `Y = H₀, H₀C, H₀C', H₀U'` of (9.8)/(9.9)). -/

/-- `HU = H ⊔ U`, realised as a subgroup of `↥M`. -/
def huSub (data : TypesIIIIIIVSetup M) : Subgroup ↥M :=
  (data.H ⊔ data.U).subgroupOf M

/-- `HU = H ⊔ U` is exactly the derived subgroup `M' = derivedInG M` realised inside `↥M`
(Peterfalvi (9.2): `M' = HU`).  This identifies the §9 induction carrier `huSub data` with the
`(derivedInG M).subgroupOf M` whose `mk'`-image is the `K` of the `M/H₀`-`Hypothesis`
(`chiefFactorQuotientHypothesis`), the bridge from the §9 family to the §6 reducible count
(issue 1012, B2 bijection). -/
theorem huSub_eq_derivedInG_subgroupOf (data : TypesIIIIIIVSetup M) :
    huSub data = (derivedInG M).subgroupOf M := by
  have h : data.H ⊔ data.U = derivedInG M := by
    rw [data.typeP.derivedInG_eq_fitting_sup_U, ← data.typeP.H_eq]; rfl
  rw [huSub, h]

/-- **`HU ◁ M`**: `HU = H ⊔ U = M' = [M,M]` is the derived subgroup realised inside `↥M`, hence
normal.  This is the `H ⊴ G` hypothesis letting the §9 induction `induceHU = Ind_{HU}^M` use the
Clifford fibre/orbit machinery (`induce_eq_induce_iff_conj`: distinct `M`-conjugacy orbits ↔ distinct
inductions) for the `𝒳 ↔ 𝒮` count of Peterfalvi (9.5)/(9.9). -/
instance huSub_normal (data : TypesIIIIIIVSetup M) : (huSub data).Normal := by
  rw [huSub_eq_derivedInG_subgroupOf, show (derivedInG M).subgroupOf M = commutator ↥M by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
  infer_instance

/-- `H`, realised as a subgroup of `HU = H ⊔ U` inside `↥M`.  Used to state the kernel condition
`H ⊄ Ker χ` defining `𝒳`. -/
def hInHu (data : TypesIIIIIIVSetup M) : Subgroup ↥(huSub data) :=
  (data.H.subgroupOf M).subgroupOf (huSub data)

/-- **Peterfalvi (9.5)'s family `𝒳`**: the irreducible characters of `HU = H ⊔ U` (realised inside
`↥M`) that do not contain `H` in their kernel. -/
def xiSet (data : TypesIIIIIIVSetup M) : Set (IrreducibleCharacter ↥(huSub data)) :=
  { χ | ¬ ((hInHu data : Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ)) }

/-- **Peterfalvi (9.5)'s family `𝒳(Y)`**: the members of `𝒳` containing `Y` in their kernel.  For
`Y ≤ HU`, `Y` is realised inside `HU` as `(Y.subgroupOf M).subgroupOf (huSub data)`. -/
def xiOf (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    Set (IrreducibleCharacter ↥(huSub data)) :=
  { χ ∈ xiSet data | ((Y.subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) }

theorem xiOf_subset_xiSet (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    xiOf data Y ⊆ xiSet data :=
  fun _ h => h.1

theorem mem_xiOf {data : TypesIIIIIIVSetup M} {Y : Subgroup G}
    {χ : IrreducibleCharacter ↥(huSub data)} :
    χ ∈ xiOf data Y ↔ χ ∈ xiSet data ∧
      ((Y.subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) :=
  Iff.rfl

/-- `𝒳(Y)` is antitone in `Y`: a larger kernel demand `Y ⊆ Ker χ` selects fewer characters. -/
theorem xiOf_antitone (data : TypesIIIIIIVSetup M) {Y Y' : Subgroup G} (hY : Y ≤ Y') :
    xiOf data Y' ⊆ xiOf data Y := fun _ hχ =>
  ⟨hχ.1, subset_trans (SetLike.coe_subset_coe.mpr
    (Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M hY))) hχ.2⟩

/-- `Ind_{HU}^M χ`, the induction of a class function of `HU = H ⊔ U` to `↥M`.  The required
`Invertible (Nat.card ↥HU : ℂ)` is constructed from `[Finite G]` and baked in here so that `sSet`
and `sOf` share one canonical instance (avoiding the induce-instance desync). -/
noncomputable def induceHU [Finite G] (data : TypesIIIIIIVSetup M)
    (χ : ClassFunction ↥(huSub data) ℂ) : ClassFunction ↥M ℂ :=
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  ClassFunction.induce (huSub data) χ

/-- The induced degree: `(Ind_{HU}^M χ)(1) = [M : HU] · χ(1)` (Peterfalvi's `Ind` raises degrees by
the index `[M : HU]`). -/
theorem induceHU_apply_one [Finite G] (data : TypesIIIIIIVSetup M)
    (χ : ClassFunction ↥(huSub data) ℂ) :
    induceHU data χ (1 : ↥M) = ((huSub data).index : ℂ) * χ (1 : ↥(huSub data)) := by
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact ClassFunction.induce_apply_one (huSub data) χ

/-- **`[M : HU] = q = |W₁|`.**  `HU = H ⊔ U = M' = derivedInG M` (the type-`P` complementarity
`derived_complement`, `derivedInG_eq_fitting_sup_U`), and `W₁` complements `M'` in `M`
(`M_complement`), so `[M : HU] = [M : M'] = |W₁| = q`.  This pins the index that
`induceHU_apply_one` leaves abstract: every `𝒮`-member `Ind_{HU}^M χ` has degree `q · χ(1)`. -/
theorem huSub_index_eq_q [Finite G] (data : TypesIIIIIIVSetup M) :
    (huSub data).index = data.q := by
  have hsup : data.H ⊔ data.U = derivedInG M := by
    simp only [TypesIIIIIIVSetup.H, TypesIIIIIIVSetup.U]
    rw [data.typeP.derivedInG_eq_fitting_sup_U, data.typeP.H_eq]
  have hidx : ((derivedInG M).subgroupOf M).index = data.q := by
    simp only [TypesIIIIIIVSetup.q, TypesIIIIIIVSetup.W1]
    rw [data.typeP.M_complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.W1_le).toEquiv]
  show ((data.H ⊔ data.U).subgroupOf M).index = data.q
  rw [hsup]; exact hidx

/-- The induced degree, with the index resolved: `(Ind_{HU}^M χ)(1) = q · χ(1)` (`q = |W₁|`).  This
is the degree formula the §9 counts (9.8)/(9.9) use directly (`𝒮`-members of source degree `s` have
degree `q·s`, e.g. `qu`, `qa`). -/
theorem induceHU_apply_one_eq_q_mul [Finite G] (data : TypesIIIIIIVSetup M)
    (χ : ClassFunction ↥(huSub data) ℂ) :
    induceHU data χ (1 : ↥M) = (data.q : ℂ) * χ (1 : ↥(huSub data)) := by
  rw [induceHU_apply_one, huSub_index_eq_q]

/-- **Peterfalvi (9.5)'s family `𝒮`**: `{Ind_{HU}^M χ | χ ∈ 𝒳}`. -/
noncomputable def sSet [Finite G] (data : TypesIIIIIIVSetup M) : Set (ClassFunction ↥M ℂ) :=
  { φ | ∃ χ ∈ xiSet data, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) }

/-- **Peterfalvi (9.5)'s family `𝒮(Y)`**: `{Ind_{HU}^M χ | χ ∈ 𝒳(Y)}`. -/
noncomputable def sOf [Finite G] (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    Set (ClassFunction ↥M ℂ) :=
  { φ | ∃ χ ∈ xiOf data Y, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) }

theorem mem_sSet [Finite G] {data : TypesIIIIIIVSetup M} {φ : ClassFunction ↥M ℂ} :
    φ ∈ sSet data ↔ ∃ χ ∈ xiSet data, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) :=
  Iff.rfl

theorem mem_sOf [Finite G] {data : TypesIIIIIIVSetup M} {Y : Subgroup G}
    {φ : ClassFunction ↥M ℂ} :
    φ ∈ sOf data Y ↔ ∃ χ ∈ xiOf data Y, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) :=
  Iff.rfl

/-- `𝒮(Y) ⊆ 𝒮`: every character induced from `𝒳(Y)` is induced from `𝒳` (since `𝒳(Y) ⊆ 𝒳`). -/
theorem sOf_subset_sSet [Finite G] (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    sOf data Y ⊆ sSet data := fun _ ⟨χ, hχ, hφ⟩ =>
  ⟨χ, xiOf_subset_xiSet data Y hχ, hφ⟩

/-- `𝒮(Y)` is antitone in `Y` (inherited from `xiOf_antitone`). -/
theorem sOf_antitone [Finite G] (data : TypesIIIIIIVSetup M) {Y Y' : Subgroup G} (hY : Y ≤ Y') :
    sOf data Y' ⊆ sOf data Y := fun _ ⟨χ, hχ, hφ⟩ =>
  ⟨χ, xiOf_antitone data hY hχ, hφ⟩

/-- Every `𝒮`-member is a genuine virtual character of `M`: `Ind_{HU}^M χ ∈ ℤ[Irr M]` for
`χ ∈ Irr(HU)` (`ClassFunction.induce_mem_ZIrr`).  This is the foundation on which the (9.8)/(9.9)
degree and inner-product counts treat `𝒮`-members as characters. -/
theorem induceHU_mem_ZIrr [Finite G] (data : TypesIIIIIIVSetup M)
    (χ : IrreducibleCharacter ↥(huSub data)) :
    induceHU data (χ : ClassFunction ↥(huSub data) ℂ) ∈ ZIrr ↥M := by
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Fintype ↥(huSub data) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact ClassFunction.induce_mem_ZIrr (huSub data) χ.mem_ZIrr

/-- `𝒮 ⊆ ℤ[Irr M]`: the whole induced family consists of virtual characters of `M`. -/
theorem sSet_subset_ZIrr [Finite G] (data : TypesIIIIIIVSetup M) :
    sSet data ⊆ (ZIrr ↥M : Set (ClassFunction ↥M ℂ)) := by
  rintro _ ⟨χ, -, rfl⟩
  exact induceHU_mem_ZIrr data χ

/-! ### The genuine subgroups `C = C_U(H̄)`, `U' = [U,U]`, `C' = [C,C]` of Peterfalvi (9.5) -/

/-- The `U`-action on the chief factor `H̄ = ↥H ⧸ N` (Peterfalvi (9.5)), as the hom from `U` (realised
inside `U ⊔ W₁`) to `Aut(H̄)`.  Its range has order `u` (`u_eq_card_quotient`); its kernel is
`C = C_U(H̄)`. -/
noncomputable def uActionHom (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :=
  (quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
    (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype

/-- **Peterfalvi's `C = C_U(H̄)`** (9.5): the kernel of the `U`-action on the chief factor `H̄`,
realised as a subgroup of `G` with `C ≤ U`.  By the first isomorphism theorem `|U : C| = u`
(`u_eq_card_quotient`'s range). -/
noncomputable def cSub (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) : Subgroup G :=
  ((uActionHom data chief).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
    (data.typeP.U ⊔ data.typeP.W1).subtype

theorem cSub_le_U (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    cSub data chief ≤ data.U :=
  (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans <| by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left

/-- **Peterfalvi's `U' = [U, U]`** (9.5), realised in `G` as `derivedInG U`. -/
def uprimeSub (data : TypesIIIIIIVSetup M) : Subgroup G := derivedInG data.U

theorem uprimeSub_le_U (data : TypesIIIIIIVSetup M) : uprimeSub data ≤ data.U :=
  Subgroup.map_subtype_le _

/-- **Peterfalvi's `C' = [C, C]`** (9.5), realised in `G` as `derivedInG C`. -/
noncomputable def cprimeSub (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) : Subgroup G :=
  derivedInG (cSub data chief)

theorem cprimeSub_le_C (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    cprimeSub data chief ≤ cSub data chief :=
  Subgroup.map_subtype_le _

open Subgroup in
/-- **`C = C_U(H̄) ◁ U`** (Peterfalvi (9.5)): the kernel of the `U`-action on the chief factor is
normal in `U`.  `cSub` is the `G`-image of `(uActionHom).ker`, which corresponds (via the
realization iso `subgroupOfEquivOfLe : ↥(U.subgroupOf (U ⊔ W₁)) ≃* ↥U`) to a kernel of a
homomorphism out of `↥U`; kernels are normal.  This is the `C ◁ U` input of the (9.9.a) carrier
normality `HC ◁ HU` (`sup_normal_of_normal_left_of_normal_subgroupOf`). -/
theorem cSub_subgroupOf_U_normal (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    ((cSub data chief).subgroupOf data.U).Normal := by
  set e := subgroupOfEquivOfLe (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1) with he
  have heq : (cSub data chief).subgroupOf data.U
      = (uActionHom data chief).ker.map e.toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      simp only [cSub, Subgroup.mem_map] at hx
      obtain ⟨z, ⟨y, hy, hyz⟩, hzx⟩ := hx
      refine ⟨y, hy, ?_⟩
      apply Subtype.ext
      rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe, ← hzx, ← hyz]
      rfl
    · rintro ⟨y, hy, rfl⟩
      simp only [cSub, Subgroup.mem_map]
      refine ⟨_, ⟨y, hy, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe]
      rfl
  rw [heq]
  exact (MonoidHom.normal_ker _).map e.toMonoidHom e.surjective

/-- **`U W₁ ≤ N_G(C)`** (the `W₁`-half of the `H₀C ◁ M` normality, issue 1012): the `U W₁`-action on
the chief factor `H̄ = ↥H ⧸ N` is defined on *all* of `U ⊔ W₁` (`quotientMulAutHom`, built from
`typeP_conjAction : U ⊔ W₁ → MulAut ↥H`), so `C = C_U(H̄)` realises inside `L = ↥(U ⊔ W₁)` as the
intersection `U' ⊓ ker(quotientMulAutHom)` of two `L`-normal subgroups (`U' = U.subgroupOf L` normal
by the Frobenius structure `typeP_uW1_frobenius`, the action kernel normal as a kernel).  A normal
subgroup of `L` is normalized by all of `L = ↑(U ⊔ W₁)` once pushed forward along `L.subtype`
(`le_normalizer_map`, `normalizer_eq_top`).  Unlike the `H`-conjugation (which only gives
`[C, H] ≤ H₀`, i.e. `H ≤ N(H₀C)` not `H ≤ N(C)`), `W₁` normalizes `C` *exactly*. -/
theorem cSub_normalized_by_uW1 [Finite G] (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    data.typeP.U ⊔ data.typeP.W1 ≤ Subgroup.normalizer (cSub data chief : Set G) := by
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  haveI hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (typeP_uW1_frobenius data.typeP hU).isNormal
  haveI hKnorm : (quotientMulAutHom chief.N_aInvariant).ker.Normal := MonoidHom.normal_ker _
  haveI hInfNorm : ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      ⊓ (quotientMulAutHom chief.N_aInvariant).ker).Normal :=
    Subgroup.normal_inf_normal _ _
  -- `C` realised in `L = ↥(U ⊔ W₁)` is `U' ⊓ ker(quotientMulAutHom)`.
  have hinner : (uActionHom data chief).ker.map
        (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype
      = (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
          ⊓ (quotientMulAutHom chief.N_aInvariant).ker := by
    rw [show (uActionHom data chief).ker
          = (quotientMulAutHom chief.N_aInvariant).ker.comap
              (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype from
        (MonoidHom.comap_ker _ _).symm,
      Subgroup.map_comap_eq, Subgroup.range_subtype]
  have hcSub : cSub data chief
      = ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
            ⊓ (quotientMulAutHom chief.N_aInvariant).ker).map
          (data.typeP.U ⊔ data.typeP.W1).subtype := by
    unfold cSub
    rw [hinner]
  rw [hcSub]
  have h1 := Subgroup.le_normalizer_map
    (H := (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      ⊓ (quotientMulAutHom chief.N_aInvariant).ker)
    (data.typeP.U ⊔ data.typeP.W1).subtype
  rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1

open scoped IsMulCommutative in
/-- **`C_U(H) ≤ C = C_U(H̄)`** (`U ∩ centralizer H ≤ cSub`): a `U`-element centralizing `H` (in `G`)
acts trivially on the chief factor quotient `H̄ = H/N`, hence lies in `ker(uActionHom)`, i.e. in
`C = cSub`.  Centralizing `H` pointwise makes conjugation trivial on every coset `hN`, so the induced
automorphism of `H̄` is the identity.  This is the containment `[U,U] ≤ C(H) ⟹ U' ≤ C` behind
Peterfalvi (9.8.d)'s `U' ≤ C_U(S₀)` and the (9.9) `C' = [C,C]` normality inputs. -/
theorem mem_cSub_of_mem_U_of_centralizes [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) {x : G}
    (hxU : x ∈ data.typeP.U) (hxC : x ∈ Subgroup.centralizer (data.typeP.H : Set G)) :
    x ∈ cSub data chief := by
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  have hxUW1 : x ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hxU
  -- the `U`-action element with `G`-coordinate `x`
  set a : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    ⟨⟨x, hxUW1⟩, Subgroup.mem_subgroupOf.mpr hxU⟩ with ha_def
  -- `a ∈ ker(uActionHom)`: conjugation by `x ∈ C(H)` is trivial on `H`, hence on `H̄`.
  have hker : a ∈ (uActionHom data chief).ker := by
    rw [MonoidHom.mem_ker]
    ext q
    induction q using QuotientGroup.induction_on with
    | _ h =>
      rw [uActionHom, MonoidHom.comp_apply,
        OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply,
        MulAut.one_apply]
      -- conjugation by `x` fixes `h` since `x` centralizes `H`
      have hfix : (typeP_conjAction data.typeP
          ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype a) h) = h := by
        apply Subtype.ext
        rw [typeP_conjAction_apply]
        have hcom : (h : G) * x = x * (h : G) :=
          (Subgroup.mem_centralizer_iff.mp hxC) (h : G) h.2
        show x * (h : G) * x⁻¹ = (h : G)
        rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
      rw [hfix]
  simp only [cSub, Subgroup.mem_map]
  exact ⟨_, ⟨a, hker, rfl⟩, rfl⟩

/-- **`U' = [U,U] ≤ C = C_U(H̄)`** (`uprimeSub ≤ cSub`, Peterfalvi (9.5)/(8.5.b)): the derived
subgroup of `U` centralizes `H` (`typeP_commutator_U_centralizes_H`) and lies in `U`
(`uprimeSub_le_U`), so by `mem_cSub_of_mem_U_of_centralizes` it lies in `C`.  Peterfalvi cites this
as "(8.5.b): `U'` centralizes `H`". -/
theorem uprimeSub_le_cSub [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    uprimeSub data ≤ cSub data chief := by
  intro x hx
  refine mem_cSub_of_mem_U_of_centralizes data chief (uprimeSub_le_U data hx) ?_
  have hxUU : x ∈ ⁅data.U, data.U⁆ := by
    rw [uprimeSub, derivedInG, commutator_def, Subgroup.map_commutator] at hx
    simpa only [← data.U.subtype.range_eq_map, Subgroup.range_subtype] using hx
  exact typeP_commutator_U_centralizes_H data.typeP hxUU

/-! ### (9.9.a) realization: `HC ◁ HU` (the inertia subgroup is normal)

For the (9.9.a) Clifford degree `χ(1) = u` we induce from the inertia subgroup `HC` of a chief-factor
character; `isIrreducibleCharacter_induce_of_inertia_eq` requires `HC ◁ HU`.  We realize `U` and
`C = C_U(H̄)` inside `HU = huSub` and apply the abstract
`sup_normal_of_normal_left_of_normal_subgroupOf` (`H ◁ HU` from `hInHu_normal`, `C ◁ U` from
`cSub_subgroupOf_U_normal`, `H ⊔ U = ⊤`). -/

/-- `H ⊴ HU`: the realization `hInHu data = (H.subgroupOf M).subgroupOf HU` of `H = M_F` inside
`HU` is normal (`M_F ◁ M`, descended along the inclusions). -/
instance hInHu_normal {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    (hInHu data).Normal := by
  have h1 : (data.H.subgroupOf M).Normal := by
    rw [show data.H = maxNilpotentNormalHall M from data.typeP.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal M
  exact h1.subgroupOf (huSub data)

theorem U_le_M (data : TypesIIIIIIVSetup M) : data.U ≤ M :=
  data.typeP.U_le.trans (Subgroup.map_subtype_le _)

theorem H_le_M (data : TypesIIIIIIVSetup M) : data.H ≤ M :=
  data.typeP.H_le.trans (Subgroup.map_subtype_le _)

/-- `U`, realized as a subgroup of `HU = H ⊔ U` inside `↥M`. -/
noncomputable def uInHu (data : TypesIIIIIIVSetup M) : Subgroup ↥(huSub data) :=
  (data.U.subgroupOf M).subgroupOf (huSub data)

/-- `C = C_U(H̄)`, realized as a subgroup of `HU` inside `↥M`. -/
noncomputable def cInHu (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    Subgroup ↥(huSub data) :=
  ((cSub data chief).subgroupOf M).subgroupOf (huSub data)

theorem cInHu_le_uInHu (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    cInHu data chief ≤ uInHu data :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (cSub_le_U data chief))

/-- **`H ⊓ C = ⊥` inside `HU`** (realized `hInHu ⊓ cInHu = ⊥`): `C ≤ U` and `H ⊓ U = ⊥`
(`typeP_H_inf_U`), so `H ⊓ C ≤ H ⊓ U = ⊥`.  A foundational input for the second-isomorphism
`HC/H₀C ≅ H̄` behind the (9.8.c) irreducible-character construction. -/
theorem hInHu_inf_cInHu_eq_bot {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) : hInHu data ⊓ cInHu data chief = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxU := cInHu_le_uInHu data chief hxC
  rw [Subgroup.mem_bot]
  have hxH' : x ∈ (data.H.subgroupOf M).subgroupOf (huSub data) := hxH
  have hxU' : x ∈ (data.U.subgroupOf M).subgroupOf (huSub data) := hxU
  have keyH : ((x : ↥M) : G) ∈ data.H :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hxH')
  have keyU : ((x : ↥M) : G) ∈ data.U :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hxU')
  have key : ((x : ↥M) : G) ∈ data.typeP.H ⊓ data.typeP.U := ⟨keyH, keyU⟩
  rw [typeP_H_inf_U data.typeP, Subgroup.mem_bot] at key
  exact Subtype.ext (Subtype.ext key)

open Subgroup in
/-- **`C ◁ U` inside `HU`** (realized form): `cInHu ◁ uInHu`, transported from `cSub ◁ U`
(`cSub_subgroupOf_U_normal`) along the realization iso `↥uInHu ≃* ↥U`.  Comap of a normal subgroup
is normal. -/
theorem cInHu_normal (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    ((cInHu data chief).subgroupOf (uInHu data)).Normal := by
  have hUsubM : data.U.subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_sup_right : data.U ≤ data.H ⊔ data.U)
  set f : ↥(uInHu data) ≃* ↥data.U :=
    (subgroupOfEquivOfLe hUsubM).trans (subgroupOfEquivOfLe (U_le_M data)) with hf
  have hgval : ∀ x : ↥(uInHu data), ((f x : ↥data.U) : G) = (((x : ↥(huSub data)) : ↥M) : G) := by
    intro x
    have h1 : (f x : ↥data.U)
        = subgroupOfEquivOfLe (U_le_M data) (subgroupOfEquivOfLe hUsubM x) := by rw [hf]; rfl
    rw [h1, subgroupOfEquivOfLe_apply_coe, subgroupOfEquivOfLe_apply_coe]
  have hcomap : (cInHu data chief).subgroupOf (uInHu data)
      = ((cSub data chief).subgroupOf data.U).comap f.toMonoidHom := by
    ext x
    simp only [cInHu, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, hgval x]
  rw [hcomap]
  exact (cSub_subgroupOf_U_normal data chief).comap f.toMonoidHom

open Subgroup in
/-- **`H ⊔ U = ⊤` inside `HU`** (realized form): `hInHu ⊔ uInHu = ⊤`, since `HU = H ⊔ U`.  Both
`H.subgroupOf M` and `U.subgroupOf M` lie below `huSub = (H ⊔ U).subgroupOf M`, and `subgroupOf`
distributes over `⊔` for subgroups below the ambient (`subgroupOf_sup`), so the realized join is
`((H ⊔ U).subgroupOf M).subgroupOf (huSub) = huSub.subgroupOf huSub = ⊤`. -/
theorem hInHu_sup_uInHu_eq_top (data : TypesIIIIIIVSetup M) :
    hInHu data ⊔ uInHu data = ⊤ := by
  have hHsub : data.H.subgroupOf M ≤ huSub data := Subgroup.subgroupOf_mono M le_sup_left
  have hUsub : data.U.subgroupOf M ≤ huSub data := Subgroup.subgroupOf_mono M le_sup_right
  unfold hInHu uInHu
  rw [← subgroupOf_sup hHsub hUsub, ← subgroupOf_sup (H_le_M data) (U_le_M data)]
  exact Subgroup.subgroupOf_self _

/-- **Peterfalvi (9.9.a), the inertia subgroup is normal: `HC ◁ HU`.**  Realized as
`hInHu ⊔ cInHu ◁ huSub`, by the abstract `sup_normal_of_normal_left_of_normal_subgroupOf`:
`H ◁ HU` (`hInHu_normal`), `C ◁ U` (`cInHu_normal`), `H ⊔ U = ⊤` (`hInHu_sup_uInHu_eq_top`).  This is
the normality `isIrreducibleCharacter_induce_of_inertia_eq` needs to make `Ind_{HC}^{HU} ψ`
irreducible in the (9.9.a) Clifford-degree argument. -/
theorem hcInHu_normal (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    (hInHu data ⊔ cInHu data chief).Normal :=
  haveI := hInHu_normal data
  haveI := cInHu_normal data chief
  sup_normal_of_normal_left_of_normal_subgroupOf (cInHu_le_uInHu data chief)
    (hInHu_sup_uInHu_eq_top data)

section
open scoped IsMulCommutative

/-- **`H ⊓ U ≤ C = C_U(H̄)`** (realized form `hInHu ⊓ uInHu ≤ cInHu`).  An element lying in both
`H` and `U` centralizes the chief factor `H̄ = H/H₀`: conjugation by an `H`-element descends to an
inner automorphism of the *abelian* `H̄`, hence is trivial, so the element lies in
`C = ker(U → Aut H̄)`.  This is the index input of (9.9.a)'s `[HU : HC] = u`. -/
theorem hInHu_inf_uInHu_le_cInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    hInHu data ⊓ uInHu data ≤ cInHu data chief := by
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  intro x hx
  obtain ⟨hxH, hxU⟩ := hx
  have hgH : (((x : ↥(huSub data)) : ↥M) : G) ∈ data.H := by
    simp only [hInHu, Subgroup.mem_subgroupOf] at hxH; exact hxH
  have hgU : (((x : ↥(huSub data)) : ↥M) : G) ∈ data.typeP.U := by
    simp only [uInHu, Subgroup.mem_subgroupOf] at hxU; exact hxU
  have hgUW1 : (((x : ↥(huSub data)) : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 :=
    Subgroup.mem_sup_left hgU
  -- the `U`-action element with the same `G`-coordinate
  set a : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    ⟨⟨(((x : ↥(huSub data)) : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  -- `a ∈ ker(uActionHom)`: conjugation by an `H`-element is trivial on the abelian `H̄`.
  have hker : a ∈ (uActionHom data chief).ker := by
    rw [MonoidHom.mem_ker]
    ext q
    induction q using QuotientGroup.induction_on with
    | _ h =>
      rw [uActionHom, MonoidHom.comp_apply,
        OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply,
        MulAut.one_apply]
      have hconj : (typeP_conjAction data.typeP
          ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype a) h)
          = (⟨_, hgH⟩ : ↥data.H) * h * (⟨_, hgH⟩ : ↥data.H)⁻¹ := by
        apply Subtype.ext
        rw [typeP_conjAction_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rfl
      rw [hconj]
      simp only [← QuotientGroup.mk'_apply, map_mul, map_inv]
      rw [mul_comm (QuotientGroup.mk' chief.N ⟨_, hgH⟩) (QuotientGroup.mk' chief.N h),
        mul_assoc, mul_inv_cancel, mul_one]
  simp only [cInHu, Subgroup.mem_subgroupOf, cSub, Subgroup.mem_map]
  exact ⟨_, ⟨a, hker, rfl⟩, rfl⟩

end

/-- **`U ⊓ HC = C`** (realized: `uInHu ⊓ (hInHu ⊔ cInHu) = cInHu`).  The `U`-part of the inertia
subgroup `HC` is exactly `C`.  `⊇` is `C ≤ U` and `C ≤ HC`; `⊆` decomposes `x = h·c`
(`H ◁ HU`, `mem_sup_of_normal_left`) with `c ∈ C ≤ U`, so `h = x·c⁻¹ ∈ U`, whence
`h ∈ H ⊓ U ≤ C` (`hInHu_inf_uInHu_le_cInHu`) and `x = h·c ∈ C`.  This is the `[HU:HC] = [U:C]`
input of (9.9.a). -/
theorem uInHu_inf_hcInHu_eq_cInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    uInHu data ⊓ (hInHu data ⊔ cInHu data chief) = cInHu data chief := by
  haveI := hInHu_normal data
  apply le_antisymm
  · rintro x ⟨hxU, hxHC⟩
    obtain ⟨hh, hhmem, cc, ccmem, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxHC
    have hcc_u : cc ∈ uInHu data := cInHu_le_uInHu data chief ccmem
    have hh_u : hh ∈ uInHu data := by
      have h1 : hh * cc * cc⁻¹ ∈ uInHu data :=
        (uInHu data).mul_mem hxU ((uInHu data).inv_mem hcc_u)
      rwa [mul_inv_cancel_right] at h1
    have hh_c : hh ∈ cInHu data chief :=
      hInHu_inf_uInHu_le_cInHu data chief (Subgroup.mem_inf.mpr ⟨hhmem, hh_u⟩)
    exact (cInHu data chief).mul_mem hh_c ccmem
  · exact le_inf (cInHu_le_uInHu data chief) le_sup_right

/-- **(9.9.a) index step (A): `[HU:HC] = [U:C]` realized form `HC.index = (cInHu.subgroupOf uInHu).index`.**
The second isomorphism theorem for `HC ◁ HU` with `uInHu ⊔ HC = ⊤`: `HU ⧸ HC ≃ uInHu ⧸ (uInHu ⊓ HC)`,
and `uInHu ⊓ HC = cInHu` (`uInHu_inf_hcInHu_eq_cInHu`). -/
theorem index_hcInHu_eq_relindex_cInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    (hInHu data ⊔ cInHu data chief).index
      = ((cInHu data chief).subgroupOf (uInHu data)).index := by
  haveI : (hInHu data ⊔ cInHu data chief).Normal := hcInHu_normal data chief
  have htop : uInHu data ⊔ (hInHu data ⊔ cInHu data chief) = ⊤ := by
    rw [← sup_assoc, sup_comm (uInHu data) (hInHu data), hInHu_sup_uInHu_eq_top, top_sup_eq]
  have he := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient
    (uInHu data) (hInHu data ⊔ cInHu data chief)).toEquiv
  -- The iso's source denominator `HC.subgroupOf uInHu = cInHu.subgroupOf uInHu` (by `U ⊓ HC = C`).
  have hsub : (hInHu data ⊔ cInHu data chief).subgroupOf (uInHu data)
      = (cInHu data chief).subgroupOf (uInHu data) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxin : (x : ↥(huSub data)) ∈ uInHu data ⊓ (hInHu data ⊔ cInHu data chief) :=
        Subgroup.mem_inf.mpr ⟨x.2, hx⟩
      rw [uInHu_inf_hcInHu_eq_cInHu data chief] at hxin
      exact hxin
    · intro hx; exact Subgroup.mem_sup_right hx
  rw [hsub] at he
  -- `he : Nat.card (↥uInHu ⧸ cInHu.subgroupOf uInHu)
  --       = Nat.card (↥(uInHu ⊔ HC) ⧸ HC.subgroupOf (uInHu ⊔ HC))`
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((hInHu data ⊔ cInHu data chief).subgroupOf (uInHu data ⊔ (hInHu data ⊔ cInHu data chief)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
        (hInHu data ⊔ cInHu data chief) ≤ uInHu data ⊔ (hInHu data ⊔ cInHu data chief))).toEquiv,
    ← he, ← Subgroup.index_eq_card] at hsplit
  -- `hsplit : Nat.card ↥(uInHu ⊔ HC) = (cInHu.subgroupOf uInHu).index * Nat.card ↥HC`
  have htopcard : Nat.card ↥(uInHu data ⊔ (hInHu data ⊔ cInHu data chief))
      = Nat.card ↥(huSub data) := by
    rw [htop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [htopcard] at hsplit
  -- `hsplit : Nat.card ↥(huSub) = (cInHu.subgroupOf uInHu).index * Nat.card ↥HC`
  have hmul := Subgroup.card_mul_index (hInHu data ⊔ cInHu data chief)
  rw [hsplit, mul_comm (((cInHu data chief).subgroupOf (uInHu data)).index)] at hmul
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

/-- `|uInHu| = |U|` (the realization `uInHu = (U.subgroupOf M).subgroupOf HU`). -/
theorem card_uInHu_eq (data : TypesIIIIIIVSetup M) :
    Nat.card ↥(uInHu data) = Nat.card ↥data.U := by
  have hUsubM : data.U.subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_sup_right : data.U ≤ data.H ⊔ data.U)
  calc Nat.card ↥(uInHu data)
      = Nat.card ↥(data.U.subgroupOf M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUsubM).toEquiv
    _ = Nat.card ↥data.U := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (U_le_M data)).toEquiv

/-- `|cInHu| = |C|` (the realization `cInHu = (cSub.subgroupOf M).subgroupOf HU`). -/
theorem card_cInHu_eq (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    Nat.card ↥(cInHu data chief) = Nat.card ↥(cSub data chief) := by
  have hCsubM : (cSub data chief).subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M
      ((cSub_le_U data chief).trans (le_sup_right : data.U ≤ data.H ⊔ data.U))
  have hCleM : cSub data chief ≤ M := (cSub_le_U data chief).trans (U_le_M data)
  calc Nat.card ↥(cInHu data chief)
      = Nat.card ↥((cSub data chief).subgroupOf M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCsubM).toEquiv
    _ = Nat.card ↥(cSub data chief) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleM).toEquiv

/-- `|C| = |ker(uActionHom)|`: `cSub` is the injective double-image of the kernel. -/
theorem card_cSub_eq_card_ker (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    Nat.card ↥(cSub data chief) = Nat.card ↥(uActionHom data chief).ker := by
  show Nat.card ↥(((uActionHom data chief).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
        (data.typeP.U ⊔ data.typeP.W1).subtype) = Nat.card ↥(uActionHom data chief).ker
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv]

/-- The character-theoretic setup of Peterfalvi (9.5).

`C`, `U'`, and `C'` denote the centralizer, commutator subgroup, and its
intersection with `C` used in the text.  The families of irreducible characters
`X`, `S`, `XOf`, and `SOf` are no longer free carrier fields: they are *genuine*
definitions (`Section11CharacterData.X = xiSet data` etc.), so the (9.8)/(9.9)
counts and (9.11) coherence are stated against Peterfalvi's honest families
`𝒳 = {χ ∈ Irr(HU) | H ⊄ Ker χ}`, `𝒮 = Ind_{HU}^M 𝒳`, `𝒳(Y)`, `𝒮(Y)`. -/
structure Section11CharacterData {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) where
  u : ℕ
  /-- **`u = |Ū|`**, the order of the image `Ū = U/C_U(H̄)` of the `U`-action on the chief factor
  `H̄ = ↥H ⧸ N` (Peterfalvi (9.5)).  This pins the formerly free `u` to the genuine quantity used by
  the Clifford dichotomy (9.7): in case (b) the Singer field model gives `|Ū| ∣ (p^q-1)/(p-1)` and
  `Coprime |Ū| (p-1)`.  Stated `Finite`-freely via `quotientMulAutHom` so the carrier needs no
  `[Finite G]`; it is definitionally the image used by `chiefFactor_caseB_image_*`. -/
  u_eq_card_quotient : u = Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
    (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).range)
  H0CprimeSupport : Set ↥M
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  quotientSemidirectFrobenius : Prop

namespace Section11CharacterData

variable {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}

/-- **Peterfalvi's `C = C_U(H̄)`** (9.5), genuine: the kernel of the `U`-action on the chief
factor (`cSub`), no longer a free field. -/
noncomputable def C (_chars : Section11CharacterData data chief) : Subgroup G := cSub data chief

theorem C_le_U (chars : Section11CharacterData data chief) : chars.C ≤ data.U := cSub_le_U data chief

/-- **Peterfalvi's `U' = [U, U]`** (9.5), genuine (`uprimeSub`). -/
def Uprime (_chars : Section11CharacterData data chief) : Subgroup G := uprimeSub data

theorem Uprime_le_U (chars : Section11CharacterData data chief) : chars.Uprime ≤ data.U :=
  uprimeSub_le_U data

/-- **Peterfalvi's `C' = [C, C]`** (9.5), genuine (`cprimeSub`). -/
noncomputable def Cprime (_chars : Section11CharacterData data chief) : Subgroup G :=
  cprimeSub data chief

theorem Cprime_le_C (chars : Section11CharacterData data chief) : chars.Cprime ≤ chars.C :=
  cprimeSub_le_C data chief

/-- The genuine family `𝒳 = {χ ∈ Irr(HU) | H ⊄ Ker χ}` (Peterfalvi (9.5)), pinned to `xiSet`. -/
def X (_chars : Section11CharacterData data chief) : Set (IrreducibleCharacter ↥(huSub data)) :=
  xiSet data

/-- The genuine family `𝒳(Y) = {χ ∈ 𝒳 | Y ⊆ Ker χ}` (Peterfalvi (9.5)), pinned to `xiOf`. -/
def XOf (_chars : Section11CharacterData data chief) (Y : Subgroup G) :
    Set (IrreducibleCharacter ↥(huSub data)) :=
  xiOf data Y

/-- The genuine family `𝒮 = Ind_{HU}^M 𝒳` (Peterfalvi (9.5)), pinned to `sSet`. -/
noncomputable def S [Finite G] (_chars : Section11CharacterData data chief) :
    Set (ClassFunction ↥M ℂ) :=
  sSet data

/-- The genuine family `𝒮(Y) = Ind_{HU}^M 𝒳(Y)` (Peterfalvi (9.5)), pinned to `sOf`. -/
noncomputable def SOf [Finite G] (_chars : Section11CharacterData data chief) (Y : Subgroup G) :
    Set (ClassFunction ↥M ℂ) :=
  sOf data Y

@[simp] theorem X_eq (chars : Section11CharacterData data chief) : chars.X = xiSet data := rfl
@[simp] theorem XOf_eq (chars : Section11CharacterData data chief) (Y : Subgroup G) :
    chars.XOf Y = xiOf data Y := rfl
@[simp] theorem S_eq [Finite G] (chars : Section11CharacterData data chief) :
    chars.S = sSet data := rfl
@[simp] theorem SOf_eq [Finite G] (chars : Section11CharacterData data chief) (Y : Subgroup G) :
    chars.SOf Y = sOf data Y := rfl

end Section11CharacterData

/-- **A nontrivial character of a prime-order group is faithful.**  `ker χ ≤ K` has order
dividing the prime `|K|`, and `χ ≠ 1` rules out `ker χ = K`, so `ker χ = ⊥`.  The per-factor input
of Peterfalvi (9.8)'s `def_Itheta`: on each order-`p` chief-factor summand a nontrivial linear
character is faithful, so any automorphism fixing it is the identity. -/
theorem injective_of_prime_card_of_ne_one {K : Type*} [Group K] [Finite K]
    (hp : (Nat.card K).Prime) (χ : K →* ℂˣ) (hχ : χ ≠ 1) : Function.Injective χ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hdvd : Nat.card ↥(MonoidHom.ker χ) ∣ Nat.card K := Subgroup.card_subgroup_dvd_card _
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hpeq
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd (MonoidHom.ker_eq_top_iff.mp ((MonoidHom.ker χ).eq_top_of_card_eq hpeq)) hχ

/-- **An automorphism fixing a nontrivial character of a prime-order group is the identity.**
`χ (α x) = χ x` with `χ` faithful (`injective_of_prime_card_of_ne_one`) forces `α x = x`. -/
theorem mulAut_eq_one_of_fixes_ne_one_hom {K : Type*} [Group K] [Finite K]
    (hp : (Nat.card K).Prime) (α : MulAut K) (χ : K →* ℂˣ) (hχ : χ ≠ 1)
    (hfix : ∀ x, χ (α x) = χ x) : α = 1 := by
  ext x
  exact injective_of_prime_card_of_ne_one hp χ hχ (hfix x)

open OddOrder.RepresentationTheory in
/-- **Per-factor stabilizer = centralizer** (Peterfalvi (9.8) `def_Itheta`, character form): for an
abelian prime-order group `K`, an automorphism `α` fixing a nontrivial irreducible character `θ` is
the identity.  `θ` is linear (`exists_linearIrreducibleCharacter_eq_of_isMulCommutative`), so it is a
faithful homomorphism `χ : K →* ℂˣ` (`injective_of_prime_card_of_ne_one`), and `α` fixing `χ` forces
`α = 1`.  Applied per order-`p` chief-factor summand of the non-Galois (9.7) decomposition. -/
theorem mulAut_eq_one_of_fixes_irr_ne_trivial_of_prime_card {K : Type*} [Group K] [Finite K]
    [IsMulCommutative K] (hp : (Nat.card K).Prime) (α : MulAut K)
    (θ : IrreducibleCharacter K)
    (hθnt : (θ : ClassFunction K ℂ) ≠ trivialClassFunction K)
    (hfix : ∀ x, (θ : ClassFunction K ℂ) (α x) = (θ : ClassFunction K ℂ) x) : α = 1 := by
  obtain ⟨χ, hχ⟩ := θ.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  have hχne : χ ≠ 1 := by
    intro h0
    apply hθnt
    rw [← hχ, h0, show (linearIrreducibleCharacter (1 : K →* ℂˣ)) = trivialIrreducibleCharacter K from
      linearIrreducibleCharacter_eq_trivial_iff.mpr rfl]
    rfl
  refine mulAut_eq_one_of_fixes_ne_one_hom hp α χ hχne (fun x => ?_)
  apply Units.val_injective
  have h1 := hfix x
  rw [← hχ] at h1
  simpa only [linearIrreducibleCharacter_apply] using h1

/-- **An automorphism trivial on a spanning family of subgroups is the identity.**  The fixed
points `{x | α x = x}` form a subgroup containing each `K i`, hence `⨆ i, K i = ⊤`; so `α` fixes
everything.  Piece (D) of the non-Galois (9.8) inertia: `φ(g)` trivial on each order-`p` chief-factor
summand `Hpart i` (which span `H̄`) is trivial on `H̄`. -/
theorem mulAut_eq_one_of_eq_id_on_iSup {H : Type*} [Group H] (α : MulAut H)
    {ι : Type*} (K : ι → Subgroup H) (hspan : ⨆ i, K i = ⊤)
    (htriv : ∀ i, ∀ x ∈ K i, α x = x) : α = 1 := by
  set S : Subgroup H :=
    { carrier := {x | α x = x}
      one_mem' := map_one α
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢; rw [map_inv, ha] } with hS
  have htop : S = ⊤ := top_le_iff.mp (hspan ▸ iSup_le (fun i x hx => htriv i x hx))
  ext x
  show α x = x
  exact htop.ge (Subgroup.mem_top x)

open OddOrder.RepresentationTheory in
/-- **Non-Galois (9.8) core, structural form** (Peterfalvi `def_Itheta`): given the chief factor
`H̄` written as the span of order-`p` `φg`-invariant summands `Hpart i`, and a character `θ` that is
nontrivial on each summand (regular), any `φg` fixing `θ` is the identity.  `θ` is linear
(`= χ`), faithful on each order-`p` summand (`injective_of_prime_card_of_ne_one`), so `φg` is the
identity there (per-factor), hence on the spanning `H̄` (`mulAut_eq_one_of_eq_id_on_iSup`). -/
theorem mulAut_eq_one_of_fixes_regular_on_prime_span {Hbar : Type*} [Group Hbar] [Finite Hbar]
    [IsMulCommutative Hbar] (φg : MulAut Hbar) {ι : Type*} (Hpart : ι → Subgroup Hbar)
    (hp : ∀ i, (Nat.card ↥(Hpart i)).Prime)
    (hpreserve : ∀ i, ∀ x ∈ Hpart i, φg x ∈ Hpart i)
    (hspan : ⨆ i, Hpart i = ⊤)
    (θ : IrreducibleCharacter Hbar)
    (hreg : ∀ i, ∃ x ∈ Hpart i,
      (θ : ClassFunction Hbar ℂ) x ≠ (θ : ClassFunction Hbar ℂ) 1)
    (hfix : ∀ x, (θ : ClassFunction Hbar ℂ) (φg x) = (θ : ClassFunction Hbar ℂ) x) :
    φg = 1 := by
  obtain ⟨χ, hχ⟩ := θ.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  have hcoe : ∀ x, (θ : ClassFunction Hbar ℂ) x = (χ x : ℂ) := by
    intro x; rw [← hχ]; exact linearIrreducibleCharacter_apply χ x
  refine mulAut_eq_one_of_eq_id_on_iSup φg Hpart hspan (fun i x hx => ?_)
  set χi : ↥(Hpart i) →* ℂˣ := χ.comp (Hpart i).subtype with hχi
  have hχine : χi ≠ 1 := by
    obtain ⟨y, hy, hyne⟩ := hreg i
    intro h0
    apply hyne
    have hχy : χ y = 1 := by
      have : χi ⟨y, hy⟩ = 1 := by rw [h0]; rfl
      simpa [hχi, MonoidHom.comp_apply] using this
    rw [hcoe, hcoe, hχy]
    simp
  have hinj : Function.Injective χi := injective_of_prime_card_of_ne_one (hp i) χi hχine
  have hval : χi ⟨φg x, hpreserve i x hx⟩ = χi ⟨x, hx⟩ := by
    apply Units.val_injective
    have hcx : (χi ⟨φg x, hpreserve i x hx⟩ : ℂ) = (θ : ClassFunction Hbar ℂ) (φg x) := by
      rw [hcoe]; rfl
    have hcy : (χi ⟨x, hx⟩ : ℂ) = (θ : ClassFunction Hbar ℂ) x := by
      rw [hcoe]; rfl
    rw [hcx, hcy, hfix x]
  exact Subtype.ext_iff.mp (hinj hval)

open OddOrder.RepresentationTheory in
/-- **Single-factor non-Galois (9.8.d) core, structural form** (Peterfalvi (9.8.d)): given a *single*
order-`p`, `φg`-invariant subgroup `S₀` of `H̄` and an irreducible character `θ` nontrivial on `S₀`,
any `φg` fixing `θ` acts as the identity **on `S₀`** (not necessarily on all of `H̄`).  This is the
single-factor analog of `mulAut_eq_one_of_fixes_regular_on_prime_span` (whose conclusion `φg = 1`
needs a *spanning* regular family): here `θ = θ₁` is faithful only on the one summand `S₀ = H₁`
(`injective_of_prime_card_of_ne_one`), so we only conclude `φg|_{S₀} = id`.  This is the algebraic
heart of `I(θ₁) ∩ U = C_U(H₁)` in the degree-`qa` construction of (9.8.d). -/
theorem mulAut_eq_id_on_of_fixes_ne_one_on_prime {Hbar : Type*} [Group Hbar] [Finite Hbar]
    [IsMulCommutative Hbar] (φg : MulAut Hbar) (S₀ : Subgroup Hbar)
    (hp : (Nat.card ↥S₀).Prime)
    (hpreserve : ∀ x ∈ S₀, φg x ∈ S₀)
    (θ : IrreducibleCharacter Hbar)
    (hreg : ∃ x ∈ S₀, (θ : ClassFunction Hbar ℂ) x ≠ (θ : ClassFunction Hbar ℂ) 1)
    (hfix : ∀ x, (θ : ClassFunction Hbar ℂ) (φg x) = (θ : ClassFunction Hbar ℂ) x) :
    ∀ x ∈ S₀, φg x = x := by
  obtain ⟨χ, hχ⟩ := θ.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  have hcoe : ∀ x, (θ : ClassFunction Hbar ℂ) x = (χ x : ℂ) := by
    intro x; rw [← hχ]; exact linearIrreducibleCharacter_apply χ x
  intro x hx
  set χi : ↥S₀ →* ℂˣ := χ.comp S₀.subtype with hχi
  have hχine : χi ≠ 1 := by
    obtain ⟨y, hy, hyne⟩ := hreg
    intro h0
    apply hyne
    have hχy : χ y = 1 := by
      have : χi ⟨y, hy⟩ = 1 := by rw [h0]; rfl
      simpa [hχi, MonoidHom.comp_apply] using this
    rw [hcoe, hcoe, hχy]
    simp
  have hinj : Function.Injective χi := injective_of_prime_card_of_ne_one hp χi hχine
  have hval : χi ⟨φg x, hpreserve x hx⟩ = χi ⟨x, hx⟩ := by
    apply Units.val_injective
    have hcx : (χi ⟨φg x, hpreserve x hx⟩ : ℂ) = (θ : ClassFunction Hbar ℂ) (φg x) := by
      rw [hcoe]; rfl
    have hcy : (χi ⟨x, hx⟩ : ℂ) = (θ : ClassFunction Hbar ℂ) x := by
      rw [hcoe]; rfl
    rw [hcx, hcy, hfix x]
  exact Subtype.ext_iff.mp (hinj hval)

open OddOrder.RepresentationTheory in
/-- **Single-factor easy inertia core (Peterfalvi (9.8.d) `C_U(H₁) ⊆ I(θ₁)`).**  Given a decomposition
`H̄ = S₀ ⊕ W` (internal direct product: `S₀ ⊓ W = ⊥`, `S₀ ⊔ W = ⊤`) of the abelian chief factor, an
automorphism `φg` that fixes `S₀` **pointwise** and preserves `W`, and an irreducible character `θ`
**trivial on `W`**, then `φg` fixes `θ`: `θ (φg x) = θ x` for all `x`.  This is the easy half of the
(9.8.d) inertia lift, complementing the hard `mulAut_eq_id_on_of_fixes_ne_one_on_prime`: a `C_U(H₁)`
element acts trivially on `H₁ = S₀` and preserves the `U`-invariant complement `W = H₂…H_q`, so it
fixes the character `θ₁ ∈ Irr(H̄/W)` supported on `S₀`.  Proof: `θ = χ` is linear, `x = s·w`
(`s ∈ S₀, w ∈ W` from `S₀ ⊔ W = ⊤`), `φg x = s·(φg w)` (fixes `s`), and `χ` is `1` on `W ∋ w, φg w`,
so `χ(φg x) = χ(s) = χ(x)`. -/
theorem mulAut_fixes_char_of_id_on_summand_triv_complement {Hbar : Type*} [Group Hbar] [Finite Hbar]
    [IsMulCommutative Hbar] (φg : MulAut Hbar) (S₀ W : Subgroup Hbar)
    (hsup : S₀ ⊔ W = ⊤)
    (hid : ∀ x ∈ S₀, φg x = x)
    (hWinv : ∀ x ∈ W, φg x ∈ W)
    (θ : IrreducibleCharacter Hbar)
    (htriv : ∀ w ∈ W, (θ : ClassFunction Hbar ℂ) w = (θ : ClassFunction Hbar ℂ) 1) :
    ∀ x, (θ : ClassFunction Hbar ℂ) (φg x) = (θ : ClassFunction Hbar ℂ) x := by
  haveI : IsMulCommutative Hbar := inferInstance
  obtain ⟨χ, hχ⟩ := θ.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  have hcoe : ∀ x, (θ : ClassFunction Hbar ℂ) x = (χ x : ℂ) := by
    intro x; rw [← hχ]; exact linearIrreducibleCharacter_apply χ x
  -- `χ = 1` on `W` (from `θ`'s triviality on `W` and `θ 1 = χ 1 = 1`).
  have hχW : ∀ w ∈ W, χ w = 1 := by
    intro w hw
    apply Units.val_injective
    have h1 := htriv w hw
    rw [hcoe, hcoe] at h1
    rw [h1, map_one, Units.val_one]
  letI : CommGroup Hbar :=
    { (inferInstance : Group Hbar) with mul_comm := isMulCommutative_iff.mp inferInstance }
  intro x
  -- Decompose `x = s * w` with `s ∈ S₀`, `w ∈ W`.
  have hxmem : x ∈ S₀ ⊔ W := hsup ▸ Subgroup.mem_top x
  rw [Subgroup.mem_sup] at hxmem
  obtain ⟨s, hs, w, hw, rfl⟩ := hxmem
  -- `χ (φg (s*w)) = χ (φg s) · χ (φg w) = χ s · 1 = χ s`; `χ (s*w) = χ s · 1 = χ s`.
  have hlhs : χ (φg (s * w)) = χ s := by
    rw [map_mul, map_mul, hid s hs, hχW (φg w) (hWinv w hw), mul_one]
  have hrhs : χ (s * w) = χ s := by rw [map_mul, hχW w hw, mul_one]
  rw [hcoe, hcoe, hlhs, hrhs]

/-- **A prime-order abelian group has a nontrivial linear character.**  `K` is nontrivial
(`|K| = p > 1`), so some `a ≠ 1`, and `ℂ` has enough roots of unity to separate it
(`exists_apply_ne_one_of_hasEnoughRootsOfUnity`).  Per-factor input for the regular-`θ̄`
construction of Peterfalvi (9.8.c): a character nontrivial on each order-`p` Clifford summand. -/
theorem exists_ne_one_hom_of_prime_card {K : Type*} [CommGroup K] [Finite K]
    (hp : (Nat.card K).Prime) : ∃ ψ : K →* ℂˣ, ψ ≠ 1 := by
  haveI : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp hp.one_lt
  obtain ⟨a, ha⟩ := exists_ne (1 : K)
  obtain ⟨ψ, hψa⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G := K) (M := ℂ) ha
  exact ⟨ψ, fun h => hψa (by rw [h]; rfl)⟩

/-- **A nontrivial character avoiding a prescribed precomposition.**  For a prime-order (`≥ 3`)
target `K'`, an iso `α : K ≃* K'`, and any `A : K →* ℂˣ`, some nontrivial `B : K' →* ℂˣ` has
`B ∘ α ≠ A`: the character group `K' →* ℂˣ` has `|K'| ≥ 3` elements
(`card_monoidHom_of_hasEnoughRootsOfUnity`), and only `{1, A ∘ α⁻¹}` are excluded.  Used to make the
free-`W1`-orbit character non-`W1`-fixed: choosing the `w₀`-conjugate factor-char `B` so its
`α`-pullback differs from the identity-conjugate char `A`. -/
theorem exists_ne_one_hom_comp_ne {K K' : Type*} [CommGroup K] [CommGroup K'] [Finite K']
    (hp : 3 ≤ Nat.card K') (α : K ≃* K') (A : K →* ℂˣ) :
    ∃ B : K' →* ℂˣ, B ≠ 1 ∧ B.comp α.toMonoidHom ≠ A := by
  classical
  haveI : Fintype (K' →* ℂˣ) := Fintype.ofFinite _
  set C : K' →* ℂˣ := A.comp α.symm.toMonoidHom with hC
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset (K' →* ℂˣ)) ⊆ {1, C} := by
    intro B _
    rcases eq_or_ne B 1 with h | h
    · simp [h]
    · have hBC : B = C := by
        rw [hC, ← hcon B h]; ext x; simp
      simp [hBC]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_eq_nat_card,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity K' ℂ] at hle
  have hle2 : ({1, C} : Finset (K' →* ℂˣ)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  omega


/-- **`noncommPiCoprod` is bijective from a cardinality count.**  A spanning commuting family of
subgroups whose cardinalities multiply to `|K|` realises `K` as their internal direct product: the
product map `(∀ i, S i) →* K` is surjective (spanning) and its domain has the same cardinality
(`Nat.card_pi`), hence bijective.  The elementary count behind the `(9.7)` decomposition
`H̄ = ⊕_{w} H1^w` (`q` order-`p` `W1`-conjugates spanning order-`p^q`), bypassing character Clifford
theory. -/
theorem noncommPiCoprod_bijective_of_card {K : Type*} [Group K] [Finite K] {ι : Type*} [Fintype ι]
    {S : ι → Subgroup K}
    (hcomm : Pairwise fun i j : ι => ∀ x y : K, x ∈ S i → y ∈ S j → Commute x y)
    (hspan : ⨆ i, S i = ⊤)
    (hcard : ∏ i, Nat.card ↥(S i) = Nat.card K) :
    Function.Bijective (Subgroup.noncommPiCoprod hcomm) := by
  rw [Nat.bijective_iff_surjective_and_card]
  refine ⟨MonoidHom.range_eq_top.mp (by rw [Subgroup.noncommPiCoprod_range]; exact hspan), ?_⟩
  rw [Nat.card_pi]; exact hcard

/-- **`iSupIndep` from an injective `noncommPiCoprod`** (converse of
`Subgroup.injective_noncommPiCoprod_of_iSupIndep`, for a commutative group `K`).  Given a finite
commuting family `S : ι → Subgroup K` whose `noncommPiCoprod` is injective, the family is
`iSupIndep`: for `x ∈ S i ⊓ ⨆_{j≠i} S j`, the two representations of `x` (as `mulSingle i ⟨x⟩` and
as an element of the `{j≠i}`-product) both map to `x`, so injectivity forces `x = 1`.  This lets the
`(9.7.a)` `W₁`-orbit direct product (`noncommPiCoprod` bijective from cardinality) yield the
independence of the summand family. -/
theorem iSupIndep_of_noncommPiCoprod_injective_comm {K : Type*} [CommGroup K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {S : ι → Subgroup K}
    (hcomm : Pairwise fun i j : ι => ∀ x y : K, x ∈ S i → y ∈ S j → Commute x y)
    (hinj : Function.Injective (Subgroup.noncommPiCoprod hcomm)) :
    iSupIndep S := by
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro x hxi hxsup
  have hcomm' : Pairwise fun a b : {j // j ≠ i} => ∀ x y : K, x ∈ S ↑a → y ∈ S ↑b → Commute x y :=
    fun a b hab => hcomm (fun h => hab (Subtype.ext h))
  have hrange : (⨆ (j) (_ : j ≠ i), S j) = (Subgroup.noncommPiCoprod hcomm').range := by
    rw [Subgroup.noncommPiCoprod_range, iSup_subtype]
  rw [hrange] at hxsup
  obtain ⟨f, hf⟩ := hxsup
  classical
  set g : (∀ j : ι, ↥(S j)) := fun j =>
    if h : j = i then 1 else f ⟨j, h⟩ with hg
  have hgi : g i = 1 := by rw [hg]; simp
  have hprodg : Subgroup.noncommPiCoprod hcomm g = x := by
    rw [← hf, Subgroup.noncommPiCoprod_apply, Subgroup.noncommPiCoprod_apply,
      Finset.noncommProd_eq_prod, Finset.noncommProd_eq_prod,
      ← Finset.mul_prod_erase Finset.univ (fun j => (g j : K)) (Finset.mem_univ i), hgi,
      Subgroup.coe_one, one_mul,
      Finset.prod_subtype (p := fun j => j ≠ i) (Finset.univ.erase i)
        (fun j => by simp only [Finset.mem_erase, Finset.mem_univ, and_true]) (fun j => (g j : K))]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    rw [hg]; simp only [a.2, dif_neg, not_false_iff]
  have hsingle : Subgroup.noncommPiCoprod hcomm (Pi.mulSingle i ⟨x, hxi⟩) = x := by
    rw [Subgroup.noncommPiCoprod_mulSingle]
  have hgeq : g = Pi.mulSingle i ⟨x, hxi⟩ := hinj (hprodg.trans hsingle.symm)
  have hgix : g i = ⟨x, hxi⟩ := by rw [hgeq]; simp
  rw [hgi] at hgix
  simpa using congrArg (Subtype.val) hgix.symm

/-- **An intermediate subgroup of prime index is the bottom.**  For `H ≤ I` with `[G:H]` prime,
`[G:I] ∣ [G:H]` is `1` (so `I = ⊤`) or `[G:H]` (so `|I| = |H|`, giving `I = H`).  Used for the
M-level inertia: `HU ≤ I_M(χ) ≤ M` with `[M:HU] = q` prime, so a character not `W1`-fixed
(`I_M(χ) ≠ M`) has `I_M(χ) = HU` — the free-`W1`-orbit ⟹ `induceHU` irreducible step. -/
theorem eq_of_le_of_prime_index {G : Type*} [Group G] [Finite G] {H I : Subgroup G}
    (hHI : H ≤ I) (hprime : (H.index).Prime) (hne : I ≠ ⊤) : I = H := by
  have hdvd : I.index ∣ H.index := Subgroup.index_dvd_of_le hHI
  rcases hprime.eq_one_or_self_of_dvd I.index hdvd with h1 | hp
  · exact absurd (Subgroup.index_eq_one.mp h1) hne
  · have hcard : Nat.card ↥I = Nat.card ↥H := by
      have e1 : I.index * Nat.card ↥I = Nat.card G := Subgroup.index_mul_card I
      have e2 : H.index * Nat.card ↥H = Nat.card G := Subgroup.index_mul_card H
      rw [hp] at e1
      exact Nat.eq_of_mul_eq_mul_left hprime.pos (e1.trans e2.symm)
    exact (Subgroup.eq_of_le_of_card_ge hHI hcard.le).symm

/-- **A permutation-invariant function on a transitive orbit is constant.**  If `σ` acts
transitively (`∀ i j, ∃ k, σ^k i = j`) and `f` is `σ`-invariant (`f (σ i) = f i`), then `f` is
constant.  Contrapositive: a non-constant `f` is not `σ`-invariant — the combinatorial core of the
free-W1-orbit (aperiodic-tuple) construction for the Clifford case-(a) degree, where `W1` permutes
the `q` order-`p` factors as a `q`-cycle and a regular character with non-constant factor-data has
trivial `W1`-stabilizer. -/
theorem constant_of_perm_invariant_of_transitive {ι α : Type*}
    (σ : Equiv.Perm ι) (htrans : ∀ i j : ι, ∃ k : ℕ, (σ ^ k) i = j)
    {f : ι → α} (hinv : ∀ i, f (σ i) = f i) : ∀ i j, f i = f j := by
  have key : ∀ (k : ℕ) (i : ι), f ((σ ^ k) i) = f i := by
    intro k
    induction k with
    | zero => simp
    | succ n ih => intro i; rw [pow_succ', Equiv.Perm.mul_apply, hinv, ih]
  intro i j
  obtain ⟨k, hk⟩ := htrans i j
  rw [← hk, key]

/-- **Regular character from a bijective product map.**  The char-construction core of
`exists_regular_char`, taking the internal-direct-product witness as `noncommPiCoprod` *bijective*
(rather than `iSupIndep` + spanning).  This lets the elementary `(9.7)` count
(`noncommPiCoprod_bijective_of_card`) feed the construction directly, sidestepping the
`iSupIndep`-from-injectivity gap. -/
theorem exists_regular_char_of_bijective {Hbar : Type*} [CommGroup Hbar] [Finite Hbar]
    {ι : Type*} [Fintype ι] {S : ι → Subgroup Hbar}
    (hcomm : Pairwise fun i j : ι => ∀ x y : Hbar, x ∈ S i → y ∈ S j → Commute x y)
    (hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm))
    (hp : ∀ i, (Nat.card ↥(S i)).Prime) :
    ∃ θ : Hbar →* ℂˣ, ∀ i, ∃ x ∈ S i, θ x ≠ 1 := by
  classical
  choose ψ hψ using fun i => exists_ne_one_hom_of_prime_card (hp i)
  let eEquiv : (∀ i : ι, ↥(S i)) ≃* Hbar :=
    MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm) hbij
  refine ⟨(MonoidHom.noncommPiCoprod ψ
      (fun i j _ x y => mul_comm (ψ i x) (ψ j y))).comp eEquiv.symm.toMonoidHom, fun i => ?_⟩
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp (hψ i)
  rw [MonoidHom.one_apply] at hz
  refine ⟨↑z, z.2, ?_⟩
  have hsymm : eEquiv.symm ↑z = Pi.mulSingle i z :=
    eEquiv.symm_apply_eq.mpr (Subgroup.noncommPiCoprod_mulSingle (hcomm := hcomm) i z).symm
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hsymm,
    MonoidHom.noncommPiCoprod_mulSingle]
  exact hz

/-- **A character with prescribed restriction to each factor**, from a bijective product map.
Given per-factor characters `ψ i : S i →* ℂˣ`, the composite `(∏ ψ) ∘ e⁻¹` (with `e` the
internal-direct-product iso) restricts to `ψ i` on `S i`.  The construction underlying
`exists_regular_char_of_bijective`, exposing the restriction `θ ↑x = ψ i x` — used to control the
factor-data for the free-`W1`-orbit (non-`W1`-fixed) character of the `(9.7)` analysis. -/
theorem char_eq_on_factors_of_bijective {Hbar : Type*} [CommGroup Hbar] [Finite Hbar]
    {ι : Type*} [Fintype ι] {S : ι → Subgroup Hbar}
    (hcomm : Pairwise fun i j : ι => ∀ x y : Hbar, x ∈ S i → y ∈ S j → Commute x y)
    (hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm))
    (ψ : ∀ i, ↥(S i) →* ℂˣ) :
    ∃ θ : Hbar →* ℂˣ, ∀ (i : ι) (x : ↥(S i)), θ ↑x = ψ i x := by
  classical
  let eEquiv : (∀ i : ι, ↥(S i)) ≃* Hbar :=
    MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm) hbij
  refine ⟨(MonoidHom.noncommPiCoprod ψ
      (fun i j _ x y => mul_comm (ψ i x) (ψ j y))).comp eEquiv.symm.toMonoidHom, fun i x => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    show eEquiv.symm ↑x = Pi.mulSingle i x from
      eEquiv.symm_apply_eq.mpr (Subgroup.noncommPiCoprod_mulSingle (hcomm := hcomm) i x).symm,
    MonoidHom.noncommPiCoprod_mulSingle]

/-- **Character extensionality on an internal direct product** (Lemma C — uniqueness companion to
`char_eq_on_factors_of_bijective`).  Two characters of `Hbar` that agree on every factor `S i` are
equal: the factors span `Hbar` (`noncommPiCoprod` surjective), so a character is determined by its
per-factor data.  The `⟸` half of the free-`W1`-orbit separation of `(9.8.c)` — per-factor agreement
forces global equality (the `⟹` half, global equality restricting to the factors, is `congr_fun`). -/
theorem char_eq_of_eq_on_factors {Hbar : Type*} [CommGroup Hbar] [Finite Hbar]
    {ι : Type*} [Fintype ι] {S : ι → Subgroup Hbar}
    (hcomm : Pairwise fun i j : ι => ∀ x y : Hbar, x ∈ S i → y ∈ S j → Commute x y)
    (hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm))
    {χ ψ : Hbar →* ℂˣ} (h : ∀ (i : ι) (x : ↥(S i)), χ ↑x = ψ ↑x) : χ = ψ := by
  classical
  let eEquiv : (∀ i : ι, ↥(S i)) ≃* Hbar :=
    MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm) hbij
  have hcomp : χ.comp eEquiv.toMonoidHom = ψ.comp eEquiv.toMonoidHom := by
    refine MonoidHom.functions_ext ℂˣ _ _ (fun i x => ?_)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show eEquiv (Pi.mulSingle i x) = (↑x : Hbar) from
        Subgroup.noncommPiCoprod_mulSingle (hcomm := hcomm) i x]
    exact h i x
  refine MonoidHom.ext fun y => ?_
  have hy := DFunLike.congr_fun hcomp (eEquiv.symm y)
  simpa using hy

/-- **The character-restriction bijection on an internal direct product**:
`(Hbar →* ℂˣ) ≃ (∀ i, ↥(S i) →* ℂˣ)`, sending a character to its tuple of factor-restrictions.
Injective by `char_eq_of_eq_on_factors` (Lemma C, `left_inv`), surjective by
`char_eq_on_factors_of_bijective` (`right_inv`).  This is the counting bridge for Peterfalvi (9.8):
it identifies the regular characters of `H̄` (nontrivial on every factor) with the tuples of nonzero
per-factor characters, giving `|regular chars| = (p-1)^q` (`card_regular_chars`, the `oXtheta`
numerator). -/
noncomputable def charRestrictEquiv {Hbar : Type*} [CommGroup Hbar] [Finite Hbar]
    {ι : Type*} [Fintype ι] {S : ι → Subgroup Hbar}
    (hcomm : Pairwise fun i j : ι => ∀ x y : Hbar, x ∈ S i → y ∈ S j → Commute x y)
    (hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm)) :
    (Hbar →* ℂˣ) ≃ (∀ i, ↥(S i) →* ℂˣ) where
  toFun χ i := χ.comp (S i).subtype
  invFun ψ := (char_eq_on_factors_of_bijective hcomm hbij ψ).choose
  left_inv χ := by
    refine char_eq_of_eq_on_factors hcomm hbij (fun i x => ?_)
    exact (char_eq_on_factors_of_bijective hcomm hbij
      (fun i => χ.comp (S i).subtype)).choose_spec i x
  right_inv ψ := by
    funext i
    exact MonoidHom.ext fun x =>
      (char_eq_on_factors_of_bijective hcomm hbij ψ).choose_spec i x

/-- **The count of regular characters** (Peterfalvi (9.8) `oXtheta` numerator, `card_pffun_on`):
on an internal direct product `Hbar = ⊕ᵢ Sᵢ` of `q = |ι|` factors each of order `p`, the characters
nontrivial on *every* factor number `(p-1)^q`.  Via `charRestrictEquiv` these correspond to tuples of
nonzero per-factor characters; each factor `Sᵢ` (order `p`) has `p` characters
(`card_monoidHom_of_hasEnoughRootsOfUnity`), hence `p-1` nonzero ones, and the product is
`(p-1)^q`. -/
theorem card_regular_chars {Hbar : Type*} [CommGroup Hbar] [Finite Hbar]
    {ι : Type*} [Fintype ι] {S : ι → Subgroup Hbar}
    (hcomm : Pairwise fun i j : ι => ∀ x y : Hbar, x ∈ S i → y ∈ S j → Commute x y)
    (hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm))
    {p : ℕ} (hp : ∀ i, Nat.card ↥(S i) = p) :
    Nat.card {χ : Hbar →* ℂˣ // ∀ i, χ.comp (S i).subtype ≠ 1} = (p - 1) ^ (Fintype.card ι) := by
  classical
  haveI : ∀ i, Fintype (↥(S i) →* ℂˣ) := fun _ => Fintype.ofFinite _
  have e1 : {χ : Hbar →* ℂˣ // ∀ i, χ.comp (S i).subtype ≠ 1} ≃
      {ψ : ∀ i, ↥(S i) →* ℂˣ // ∀ i, ψ i ≠ 1} :=
    (charRestrictEquiv hcomm hbij).subtypeEquiv (fun _ => Iff.rfl)
  rw [Nat.card_congr e1, Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i (ψ : ↥(S i) →* ℂˣ) =>
        ψ ≠ 1)), Nat.card_eq_fintype_card, Fintype.card_pi]
  have hfac : ∀ i, Fintype.card {ψ : ↥(S i) →* ℂˣ // ψ ≠ 1} = p - 1 := by
    intro i
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥(S i) ℂ, hp i]
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const, Finset.card_univ]

/-- **A regular character not fixed by a factor-permuting automorphism.**  Given the internal
direct product `(noncommPiCoprod hbij)` of prime-order (`≥ 3`) factors `S i`, and an automorphism
`τ` mapping factor `S i₀` onto a *different* factor `S j₀`, there is a character nontrivial on every
factor (regular) yet `θ ∘ τ ≠ θ`.  Choose the `j₀`-factor char `B` so its `τ`-pullback differs from
the `i₀`-factor char `A` (`exists_ne_one_hom_comp_ne`), set the data by `Function.update`, and read
off `θ(τ y) = B(α y) ≠ A(y) = θ(y)` via `char_eq_on_factors_of_bijective`.  The free-`W1`-orbit
character of the `(9.7)` analysis (`τ = act.φ(w₀)`, `S i = S₀^{·}`). -/
theorem exists_regular_char_not_fixed {Hbar : Type*} [CommGroup Hbar] [Finite Hbar]
    {ι : Type*} [Fintype ι] {S : ι → Subgroup Hbar}
    (hcomm : Pairwise fun i j : ι => ∀ x y : Hbar, x ∈ S i → y ∈ S j → Commute x y)
    (hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm))
    (hp : ∀ i, (Nat.card ↥(S i)).Prime) (hp3 : ∀ i, 3 ≤ Nat.card ↥(S i))
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀) (τ : MulAut Hbar) (hτ : τ • S i₀ = S j₀) :
    ∃ θ : Hbar →* ℂˣ, (∀ i, ∃ x ∈ S i, θ x ≠ 1) ∧ θ.comp τ.toMonoidHom ≠ θ := by
  classical
  have hmap : (S i₀).map τ.toMonoidHom = S j₀ := hτ
  let α : ↥(S i₀) ≃* ↥(S j₀) :=
    (Subgroup.equivMapOfInjective (S i₀) τ.toMonoidHom τ.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hαcoe : ∀ z : ↥(S i₀), ((α z : ↥(S j₀)) : Hbar) = τ z := fun z => rfl
  obtain ⟨A, hAne⟩ := exists_ne_one_hom_of_prime_card (hp i₀)
  obtain ⟨B, hBne, hBcomp⟩ := exists_ne_one_hom_comp_ne (hp3 j₀) α A
  choose ψ0 hψ0 using fun i => exists_ne_one_hom_of_prime_card (hp i)
  set ψ : ∀ i, ↥(S i) →* ℂˣ := Function.update (Function.update ψ0 i₀ A) j₀ B with hψdef
  have hψi₀ : ψ i₀ = A := by rw [hψdef, Function.update_of_ne hij, Function.update_self]
  have hψj₀ : ψ j₀ = B := by rw [hψdef, Function.update_self]
  obtain ⟨θ, hθ⟩ := char_eq_on_factors_of_bijective hcomm hbij ψ
  refine ⟨θ, fun i => ?_, ?_⟩
  · -- regular: ψ i ≠ 1 ⟹ ∃ x ∈ S i, θ x ≠ 1
    have hψine : ψ i ≠ 1 := by
      rcases eq_or_ne i j₀ with h | h
      · subst h; rw [hψj₀]; exact hBne
      · rw [hψdef, Function.update_of_ne h]
        rcases eq_or_ne i i₀ with h2 | h2
        · subst h2; rw [Function.update_self]; exact hAne
        · rw [Function.update_of_ne h2]; exact hψ0 i
    obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hψine
    rw [MonoidHom.one_apply] at hz
    exact ⟨↑z, z.2, by rw [hθ i z]; exact hz⟩
  · -- not fixed: ∃ y, θ (τ y) ≠ θ y
    rw [DFunLike.ne_iff]
    obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hBcomp
    refine ⟨↑z, ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show τ ↑z = ((α z : ↥(S j₀)) : Hbar) from (hαcoe z).symm,
      hθ j₀ (α z), hθ i₀ z, hψj₀, hψi₀]
    exact hz

/-- **A regular character exists on an internal direct product of prime-order subgroups.**
If `Hbar` is the internal direct product (`iSupIndep` + spanning) of order-`p` subgroups `Hpart i`,
there is a character `θ : Hbar →* ℂˣ` nontrivial on every summand.  Combine per-factor nontrivial
characters (`exists_ne_one_hom_of_prime_card`) through the direct-product isomorphism
`(∀ i, Hpart i) ≃* Hbar` (`Subgroup.noncommPiCoprod`, bijective by independence + spanning).
Supplies the regular `θ̄` for the Clifford case-(a) degree (`inertia_eq_hcInHu_caseA`'s `hreg`). -/
theorem exists_regular_char {Hbar : Type*} [CommGroup Hbar] [Finite Hbar]
    {ι : Type*} [Fintype ι] (Hpart : ι → Subgroup Hbar)
    (hindep : iSupIndep Hpart) (hspan : ⨆ i, Hpart i = ⊤)
    (hp : ∀ i, (Nat.card ↥(Hpart i)).Prime) :
    ∃ θ : Hbar →* ℂˣ, ∀ i, ∃ x ∈ Hpart i, θ x ≠ 1 := by
  have hcomm : Pairwise fun i j : ι => ∀ x y : Hbar, x ∈ Hpart i → y ∈ Hpart j → Commute x y :=
    fun i j _ x y _ _ => mul_comm x y
  refine exists_regular_char_of_bijective hcomm ⟨?_, ?_⟩ hp
  · exact Subgroup.injective_noncommPiCoprod_of_iSupIndep hindep
  · rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range]; exact hspan

/-- **Restriction of a `φ`-invariant action to the invariant subgroup `S`.**  Each `φ a` maps `S`
bijectively onto itself, hence restricts to an automorphism of `↥S`; this is functorial in `a`,
giving a group homomorphism `A →* MulAut ↥S`.  (Used for (9.7) case (a): the `U`-action on an
order-`p` Clifford factor `H₁ ≤ H̄`; its range order is the Clifford integer `a = |Ū₁|`, pinned in
`CliffordCaseAData.a_eq_card_restrictAut_range`.) -/
noncomputable def aInvariantRestrictAut {K A : Type*} [Group K] [Group A] {φ : A →* MulAut K}
    {S : Subgroup K} (hS : IsAInvariant φ S) : A →* MulAut ↥S where
  toFun a := (MulEquiv.subgroupMap (φ a) S).trans
    (MulEquiv.subgroupCongr ((pointwise_mulAut_smul_eq_map (φ a) S).symm.trans (hS a)))
  map_one' := by
    ext x
    simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply,
      map_one, MulAut.one_apply]
  map_mul' a b := by
    ext x
    simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply,
      map_mul, MulAut.mul_apply]

@[simp] theorem aInvariantRestrictAut_coe {K A : Type*} [Group K] [Group A] {φ : A →* MulAut K}
    {S : Subgroup K} (hS : IsAInvariant φ S) (a : A) (x : ↥S) :
    ((aInvariantRestrictAut hS a x : ↥S) : K) = φ a x := by
  simp only [aInvariantRestrictAut, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply]

/-- Case (a) of Peterfalvi (9.7): `H/H_0` splits as a direct product of `q`
order-`p` factors permuted by `W_1`.

The parts `Hpart` live in the chief factor `H̄ = ↥H ⧸ N` itself (not in `G`): an order-`p` piece of
`H̄` pulls back to a subgroup of `G` of order `p·|H₀|`, so the genuine order-`p` factors are
subgroups of `H̄`. -/
structure CliffordCaseAData {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief) where
  Hpart : Fin data.q → Subgroup (↥data.H ⧸ chief.N)
  Hpart_order : ∀ i, Nat.card ↥(Hpart i) = chief.p
  /-- The `q` order-`p` Clifford summands span the chief factor `H̄` (non-opaque (9.7) structure). -/
  Hpart_iSup : ⨆ i, Hpart i = ⊤
  /-- Each Clifford summand is `U`-invariant (non-opaque (9.7) structure). -/
  Hpart_aInvariant : ∀ i, IsAInvariant (uActionHom data chief) (Hpart i)
  /-- The `q` order-`p` Clifford summands are independent (non-opaque (9.7) structure): together
  with `Hpart_iSup` this exhibits `H̄` as their internal direct product. -/
  Hpart_iSupIndep : iSupIndep Hpart
  /-- **Orbit generator** `S₀` (non-opaque (9.7) case-(a) structure): the `q` summands are the
  `U W₁`-translates `Hpart j = φ(orbitRep j) • S₀` of a single order-`p` subgroup `S₀`, where
  `φ = quotientMulAutHom` is the (`Finite`-free) chief-factor action.  Exposing the orbit (rather than
  the opaque `W₁`-transitivity `Prop`) is what lets the (9.8.c) constant-factor-data set `Xmu` be
  constructed and `W₁`-transitivity of the summands proven. -/
  S0 : Subgroup (↥data.H ⧸ chief.N)
  /-- The orbit generator `S₀` is `U`-invariant (the (9.7) case-(a) construction seeds it from a
  single `U`-invariant order-`p` line).  Exposing this (rather than only the per-`Hpart`
  `Hpart_aInvariant`) lets the (9.8.c) surjectivity reduce the `W₁`-twist `q(w)•S₀` of a factor to
  `q(W₁-part)•S₀` (the `U`-part fixes `S₀`), identifying the `Hpart` family with the `W₁`-conjugate
  family and giving its `W₁`-transitivity. -/
  S0_aInvariant : IsAInvariant (uActionHom data chief) S0
  /-- Orbit representatives realising each summand as a translate of `S₀`. -/
  orbitRep : Fin data.q → ↥(data.typeP.U ⊔ data.typeP.W1)
  /-- Each summand is the `orbitRep`-translate of the generator `S₀`. -/
  Hpart_orbit : ∀ j, Hpart j = quotientMulAutHom chief.N_aInvariant (orbitRep j) • S0
  a : ℕ
  a_pos : 0 < a
  a_dvd_p_sub_one : a ∣ chief.p - 1
  /-- **`a = |Ū₁| = |U : C_U(H₁)|`** (Peterfalvi (9.7.a)): the Clifford integer `a` is pinned to the
  order of the image `Ū₁` of the `U`-action on the order-`p` factor `S₀` (`= H₁`).  This is *not*
  opaque data — it is the genuine group-theoretic index `|U : C_U(S₀)|` (first isomorphism theorem,
  `index_cuInHu_subgroupOf_uInHu_eq_a`), which the (9.8.d) degree analysis needs: the source
  character `θ₁·λ` induced from `H·C_U(S₀)` has degree `[HU : H·C_U(S₀)] = |Ū₁| = a`
  (`index_hcuInHu_eq_a`).  Without this pin, `a` would be an unconstrained free field disconnected
  from the character degrees, and the degree-`qa` count (9.8.d) would not be honestly provable. -/
  a_eq_card_restrictAut_range :
    a = Nat.card ↥(aInvariantRestrictAut S0_aInvariant).range

open scoped IsMulCommutative in
/-- **The `(9.8)` regular-character count on the chief factor** (`oXtheta` numerator): the
characters of `H̄ = H/H₀` nontrivial on *every* Clifford summand `caseA.Hpart i` number `(p-1)^q`.
Instantiates the abstract `card_regular_chars` at the internal-direct-product structure carried by
`CliffordCaseAData` (`Hpart_iSupIndep` + `Hpart_iSup` give `noncommPiCoprod` bijective,
`Hpart_order` gives each factor order `p`).  This is the numerator of Peterfalvi's `oXtheta`
(`u·|𝒳(H₀C)| = (p-1)^q`): via inflation (`hcPsi`) and `HU`-induction these regular `H̄`-characters
parametrise the degree-`qu` members of `𝒮(H₀C)` (Coq `PFsection9` `oXtheta`, `card_pffun_on`). -/
theorem card_regular_chars_Hbar [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    Nat.card {χ : (↥data.H ⧸ chief.N) →* ℂˣ // ∀ i, χ.comp (caseA.Hpart i).subtype ≠ 1}
      = (chief.p - 1) ^ data.q := by
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  have hcomm : Pairwise fun i j : Fin data.q =>
      ∀ x y : (↥data.H ⧸ chief.N), x ∈ caseA.Hpart i → y ∈ caseA.Hpart j → Commute x y :=
    fun i j _ x y _ _ => mul_comm x y
  have hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm) :=
    ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep caseA.Hpart_iSupIndep, by
      rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range]; exact caseA.Hpart_iSup⟩
  have h := card_regular_chars hcomm hbij caseA.Hpart_order
  rwa [Fintype.card_fin] at h

/-- Case (b) of Peterfalvi (9.7): `U` acts irreducibly on `H/H_0`, modeled by
the multiplicative group of a field of order `p^q`.

The genuine consequences of this case are supplied by standalone lemmas (which carry the required
`[Finite G]`/`chief.N.Normal` instances that a `structure` field type cannot): the fixed-point-free
Frobenius action `H̄ ⋊ Ū` by `chiefFactor_caseB_action_fpf` (the structural input of Peterfalvi
(9.9)), the Singer cyclicity of `Ū` by `chiefFactor_caseB_image_cyclic`, and the divisibilities
`u_coprime_p_sub_one`/`u_dvd_norm_quotient` carried here. -/
structure CliffordCaseBData {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief) where
  field_model : Prop
  field_model_holds : field_model
  /-- **`Ū` is cyclic** (Singer, non-opaque): the image of the `U`-action on the chief factor `H̄`
  — Peterfalvi's `Ū = U/C_U(H̄)` — is cyclic, as `Ū` embeds in the multiplicative group of the
  field `End_{𝔽ₚ[U]}(H̄)` on which it acts irreducibly (`chiefFactor_caseB_image_cyclic`). -/
  Ubar_cyclic : IsCyclic ↥(uActionHom data chief).range
  u_coprime_p_sub_one : Nat.Coprime chars.u (chief.p - 1)
  u_dvd_norm_quotient : chars.u ∣ (chief.p ^ data.q - 1) / (chief.p - 1)
  /-- The defining property of case (b): `U` acts **irreducibly** on the chief factor `H̄ = H/H_0`,
  i.e. the only `U`-invariant subgroups of `H̄` are `⊥` and `⊤`.  Stated `Finite`-freely via the
  `U`-action hom `uActionHom` (definitionally `(typeP_quotientCoprimeAction …).φ.comp (…).U.subtype`,
  which needs `[Finite G]`).  This is the hypothesis the Clifford degree analysis (9.8.c)/(9.9.a)
  consumes through `inertia_eq_hcInHu` (it computes the inertia group `I_{HU}(θ₀) = HC` of a
  nontrivial chief-factor character). -/
  actsIrreducibly : ∀ J : Subgroup (↥data.H ⧸ chief.N),
      IsAInvariant (uActionHom data chief) J → J = ⊥ ∨ J = ⊤

/-- **Peterfalvi (9.6)**: after choosing `H_0`, the induced `U`-action is non-trivial (`U` does not
centralize `H`), `H̄ = H/H_0` is a chief factor of `M`, `|H̄| = p^q`, and (types III/IV) `|W_2| = p`.

*Faithfulness note.* The printed (9.6) asserts `|W̄_2| = p` for the **image** `W̄_2 = C_{H̄}(W_1)`,
which for type II is strictly smaller than the full `W_2 = C_H(W_1)` (the carrier never pins `|W_2|`,
only `|W_1|` is prime).  The earlier formalization stated the **unconditional** `|W_2| = p`, which is
*false* for type II: `|W_2|^q = |H| = p^q·|H_0|` (by (9.3) + `quotient_order`) gives `|W_2| = p`
only when `H_0 = 1`.  We therefore state the faithful, carrier-provable form: `|W_2| = p` only in
the types III/IV branch (where `|W_2| = p` directly, `typeIII_IV_p_eq_W2`), together with the genuine
order conclusion `|H̄| = p^q` (`quotient_order`).  The image fact `|W̄_2| = p` needs the (non-opaque)
chief-factor structure and is delivered by `typeP_chiefFactor_card`. -/
theorem chiefFactor_basic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    data.U ⊓ Subgroup.centralizer (data.H : Set G) ≠ data.U ∧
      (IsTypeIII M ∨ IsTypeIV M → Nat.card ↥data.W2 = chief.p) ∧
      Nat.card ↥data.H = chief.p ^ data.q * Nat.card ↥chief.H0 := by
  obtain ⟨hII_case, hIIIIV_case⟩ := typeII_III_IV_order_relations hG data
  have hH_ne : data.typeP.H ≠ ⊥ := fun heq => data.typeP.H_noncyclic (heq ▸ inferInstance)
  refine ⟨?_, chief.typeIII_IV_p_eq_W2, chief.quotient_order⟩
  -- `U` does not centralize `H`: else `C_H(U) = H`, contradicting (9.3).
  intro hcentr
  have hUle : data.U ≤ Subgroup.centralizer (data.H : Set G) := inf_eq_left.mp hcentr
  have hHle : data.H ≤ Subgroup.centralizer (data.U : Set G) := Subgroup.le_centralizer_iff.mp hUle
  have hHinf : data.H ⊓ Subgroup.centralizer (data.U : Set G) = data.H := inf_eq_left.mpr hHle
  rcases data.type_alt with hII | hIIIIV
  · -- Type II: (9.3) gives `C_H(U) = ⊥`, but `C_H(U) = H ≠ ⊥`.
    exact hH_ne (hHinf.symm.trans (hII_case hII).1)
  · -- Types III/IV: (9.3) gives `|H| = p^q·|C_H(U)| = p^q·|H|`, forcing `p^q = 1`.
    obtain ⟨p, hp, _hpW2, _hCUW, hHcard⟩ := hIIIIV_case hIIIIV
    rw [hHinf] at hHcard
    have hpq1 : p ^ data.q = 1 := by
      rcases Nat.eq_zero_or_pos (Nat.card ↥data.H) with h0 | hpos
      · exact absurd h0 Nat.card_pos.ne'
      · exact Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact hHcard.symm)
    have hq_ne : data.q ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ≤ p ^ data.q := le_trans hp.two_le (Nat.le_self_pow hq_ne p)
    omega

/-- **Centralizer commutes with a coprime cyclic quotient** (general group theory): for `x : Γ` and
`N ◁ Γ` with `gcd(|⟨x⟩|, |N|) = 1`, the centralizer of `x̄ = x N` in `Γ/N` is the image of the
centralizer of `x` in `Γ`: `C_{Γ/N}(x̄) = (C_Γ(x)).map (mk' N)`.

`⊇` is functoriality of `mk'`.  `⊆` lifts an `x̄`-centralizing element `g N` through the coprime
action of `⟨x⟩` on `Γ` (conjugation): `g N ∈ C(x̄)` means every power of `x` fixes `g` modulo `N`,
so Isaacs Cor 3.28 (`coprime_fixedPoints_quotient_of_coprime_normal`) produces a genuine
`x`-centralizing representative `c ≡ g (mod N)`.  This is the engine of the Peterfalvi (8.4.d)
`centralizer_W̄₂` computation (`Γ = ↥M`, `N = H₀`). -/
theorem centralizer_map_mk'_eq_of_coprime_zpowers {Γ : Type*} [Group Γ] [Finite Γ]
    {N : Subgroup Γ} [N.Normal] (x : Γ)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥N)) :
    Subgroup.centralizer ({(QuotientGroup.mk' N x : Γ ⧸ N)} : Set (Γ ⧸ N))
      = (Subgroup.centralizer ({x} : Set Γ)).map (QuotientGroup.mk' N) := by
  classical
  apply le_antisymm
  · -- `⊆`: coprime lift of an `x̄`-centralizing element to an `x`-centralizing one
    intro gbar hgbar
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gbar
    set φ : ↥(Subgroup.zpowers x) →* MulAut Γ :=
      (MulAut.conj (G := Γ)).comp (Subgroup.zpowers x).subtype with hφ
    have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ N := by
      rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
      intro c n hn
      show (MulAut.conj (c : Γ)) n ∈ N
      rw [MulAut.conj_apply]
      exact (inferInstance : N.Normal).conj_mem n hn (c : Γ)
    haveI : IsCyclic ↥(Subgroup.zpowers x) := Subgroup.isCyclic_zpowers x
    have hcomm : Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N g) :=
      Subgroup.mem_centralizer_iff.mp hgbar _ (Set.mem_singleton _)
    have hg_fix : ∀ c : ↥(Subgroup.zpowers x), ∃ n ∈ N, φ c g = g * n := by
      intro c
      refine ⟨g⁻¹ * φ c g, ?_, by group⟩
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv]
      have hφc : φ c g = (c : Γ) * g * (c : Γ)⁻¹ := by simp [hφ, MulAut.conj_apply]
      have hcc : Commute (QuotientGroup.mk' N (c : Γ)) (QuotientGroup.mk' N g) := by
        obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp c.2
        rw [← hk, map_zpow]
        exact hcomm.zpow_left k
      rw [hφc, map_mul, map_mul, map_inv, hcc.eq]
      group
    obtain ⟨c, hc_fixed, n, hn, hc_eq⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal
        hcop (Or.inl inferInstance) hN_inv hg_fix
    rw [Subgroup.mem_map]
    refine ⟨c, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      have hfix := hc_fixed ⟨x, Subgroup.mem_zpowers x⟩
      rw [hφ] at hfix
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] at hfix
      -- `hfix : x * c * x⁻¹ = c`  ⟹  `x * c = c * x`
      rw [hy]
      exact mul_inv_eq_iff_eq_mul.mp hfix
    · have hn1 : (QuotientGroup.mk' N) n = 1 := by
        rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff n).mpr hn
      rw [hc_eq, map_mul, hn1, mul_one]
  · -- `⊇`: image of the centralizer centralizes `x̄`
    rw [Subgroup.map_le_iff_le_comap]
    intro c hc
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro ybar hybar
    rw [Set.mem_singleton_iff] at hybar; subst hybar
    show QuotientGroup.mk' N x * QuotientGroup.mk' N c = QuotientGroup.mk' N c * QuotientGroup.mk' N x
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc x (Set.mem_singleton _)]

/-- **`H₀ ◁ M`** (the chief-factor kernel is `M`-normal): `H₀.subgroupOf M` is normal in `↥M`, so
the quotient `↥M ⧸ H₀` — the ambient of Peterfalvi (8.4.d)'s certain-type group `L = M/H₀` — is a
group.  Immediate from the `M`-normalization `H0_normalized_by_M` of (9.4) via
`normal_subgroupOf_iff_le_normalizer` (using `H₀ < H ≤ M`).  This is the foundation of the §9
reducible-count `quotient`-Dade framework (issue 1012). -/
theorem chiefFactor_H0_subgroupOf_normal {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    (chief : ChiefFactorData data) : (chief.H0.subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (chief.H0_lt_H.le.trans (H_le_M data))).mpr chief.H0_normalized_by_M

/-- **`W₁ ⊓ H₀ = ⊥` inside `↥M`**: `W₁` complements `M' = [M,M]` (`data.M_complement`) and
`H₀ < H ≤ M'`, so `W₁ ⊓ H₀ ≤ W₁ ⊓ M' = ⊥`.  In `↥M ⧸ H₀` this makes `W̄₁ = W₁ H₀ / H₀ ≅ W₁`
(needed for `W̄₁ ≠ ⊥` and the Hall coprimality of the (8.4.d) certain-type group). -/
theorem chiefFactor_W1_inf_H0_subgroupOf_eq_bot {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (data.W1.subgroupOf M) ⊓ (chief.H0.subgroupOf M) = ⊥ := by
  have hH0M' : (chief.H0.subgroupOf M) ≤ (derivedInG M).subgroupOf M :=
    Subgroup.comap_mono (chief.H0_lt_H.le.trans data.typeP.H_le)
  rw [eq_bot_iff]
  exact le_trans (inf_le_inf_left _ hH0M')
    (disjoint_iff.mp data.typeP.M_complement.disjoint.symm).le

/-- **`gcd(|H₀|, |W₁|) = 1`**: `H₀ < H` and `gcd(|H|, |W₁|) = 1` (`typeP_coprime_H_W1`, the coprime
action of the Hall complement `W₁` on the nilpotent `H = M_F`).  This is the coprimality the
(8.4.d) centralizer computation `C_{M'/H₀}(x̄) = W̄₂` needs (the `x`-fixed points of `M'` lift
across `H₀` by Isaacs Cor 3.28). -/
theorem chiefFactor_coprime_H0_W1 [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    Nat.Coprime (Nat.card ↥chief.H0) (Nat.card ↥data.W1) :=
  (typeP_coprime_H_W1 data.typeP).coprime_dvd_left
    (Subgroup.card_dvd_of_le chief.H0_lt_H.le)

/-- **`(H₀ ⊔ C) ⊓ H = H₀`** (Peterfalvi (9.8.b)/(9.9.b) shared, the Dedekind step) — the unifying
condition `K ∩ H = H₀` that lets the §9↔§6 reducible count `reducible_count_sOf_H0` apply to
`K = H₀C` exactly as to `K = H₀` (Coq `PFsection9` `nb_redM`, instantiated at both `K = H0` and
`K = H0C`).  `C ≤ U` and `H ⊓ U = ⊥` (`typeP_H_inf_U`) kill the `C`-part: writing
`x ∈ H₀ ⊔ C = H₀·C` (`coe_mul_of_right_le_normalizer_left`, since `C ≤ U ≤ M ≤ N(H₀)`) as
`x = h₀·c`, membership `x ∈ H` together with `h₀ ∈ H₀ ≤ H` forces `c ∈ H ⊓ C ≤ H ⊓ U = ⊥`.
Consequently `W₂ ∩ H₀C = W₂ ∩ H ∩ H₀C = W₂ ∩ H₀` (as `W₂ ≤ H`), so the chief-factor image `W̄₂`
keeps order `p` in `M/H₀C` just as in `M/H₀` — this is what makes the `H₀C` reducible count
`reducible_count_sOf_H0C` a parallel of the `H₀` one (issue 1012). -/
theorem chiefFactor_H0supC_inf_H_eq_H0 {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (chief.H0 ⊔ cSub data chief) ⊓ data.H = chief.H0 := by
  refine le_antisymm ?_ (le_inf le_sup_left chief.H0_lt_H.le)
  intro x hx
  obtain ⟨hxHC, hxH⟩ := Subgroup.mem_inf.mp hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left chief.H0 (cSub data chief)
      (((cSub_le_U data chief).trans (U_le_M data)).trans chief.H0_normalized_by_M)] at hxHC
  obtain ⟨h₀, hh₀, c, hc, rfl⟩ := hxHC
  have hcH : c ∈ data.typeP.H := by
    have hcalc : h₀⁻¹ * (h₀ * c) ∈ data.H := mul_mem (inv_mem (chief.H0_lt_H.le hh₀)) hxH
    simpa [inv_mul_cancel_left] using hcalc
  have hc1 : c = 1 := by
    have hmem : c ∈ data.typeP.H ⊓ data.typeP.U :=
      Subgroup.mem_inf.mpr ⟨hcH, cSub_le_U data chief hc⟩
    rwa [typeP_H_inf_U data.typeP, Subgroup.mem_bot] at hmem
  simpa [hc1] using hh₀

/-- **`H ⊓ H₀C = H₀` inside `HU`** (realized form): `hInHu ⊓ (H₀C).subgroupOf = (H₀).subgroupOf`.
Realization of `chiefFactor_H0supC_inf_H_eq_H0` (`(H₀⊔C) ⊓ H = H₀`).  The `H ∩ H₀C = H₀` input of the
second isomorphism `HC/H₀C ≅ H̄` (`HC = H·H₀C`, so `HC/H₀C ≅ H/(H∩H₀C) = H/H₀ = H̄`) behind the
(9.8.c) irreducible-character construction. -/
theorem hInHu_inf_realizedH0supC_eq_realizedH0 {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    hInHu data ⊓ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)
      = (chief.H0.subgroupOf M).subgroupOf (huSub data) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxH, hxHC⟩ := Subgroup.mem_inf.mp hx
    have hxH' : x ∈ (data.H.subgroupOf M).subgroupOf (huSub data) := hxH
    have memH : ((x : ↥M) : G) ∈ data.H :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hxH')
    have memHC : ((x : ↥M) : G) ∈ chief.H0 ⊔ cSub data chief :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hxHC)
    have memH0 : ((x : ↥M) : G) ∈ chief.H0 := by
      have hmem : ((x : ↥M) : G) ∈ (chief.H0 ⊔ cSub data chief) ⊓ data.H := ⟨memHC, memH⟩
      rwa [chiefFactor_H0supC_inf_H_eq_H0] at hmem
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr memH0)
  · intro x hx
    have memH0 : ((x : ↥M) : G) ∈ chief.H0 :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (chief.H0_lt_H.le memH0))
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr
        ((le_sup_left : chief.H0 ≤ chief.H0 ⊔ cSub data chief) memH0))

/-- **realized `H₀C = H₀ ⊔ C` distributes** (realized form): the realized `H₀C` inside `HU` equals
`(realized H₀) ⊔ cInHu`.  Via `Subgroup.subgroupOf_sup` (twice, with `H₀,C ≤ M` and
`H₀.subgroupOf M, C.subgroupOf M ≤ huSub`).  Lets the second isomorphism use `N = realized H₀C`
with `hInHu ⊔ N = HC` (`realized H₀ ≤ hInHu`) and `hInHu ⊓ N = realized H₀` (modular law +
`hInHu_inf_cInHu_eq_bot`), avoiding `⊔`-realization friction in the (9.8.c) construction. -/
theorem realizedH0supC_eq_realizedH0_sup_cInHu {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)
      = (chief.H0.subgroupOf M).subgroupOf (huSub data) ⊔ cInHu data chief := by
  have hH0M : chief.H0 ≤ M := chief.H0_lt_H.le.trans (H_le_M data)
  have hCM : cSub data chief ≤ M := (cSub_le_U data chief).trans (U_le_M data)
  rw [Subgroup.subgroupOf_sup hH0M hCM]
  have hH0sub : (chief.H0.subgroupOf M) ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_trans chief.H0_lt_H.le le_sup_left)
  have hCsub : (cSub data chief).subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_trans (cSub_le_U data chief) le_sup_right)
  rw [Subgroup.subgroupOf_sup hH0sub hCsub]
  rfl

/-- **`hInHu ⊔ H₀C = HC`** (realized): `hInHu ⊔ (realized H₀C) = hInHu ⊔ cInHu` (the inertia
subgroup `HC`).  Via the bridge `realized H₀C = realizedH₀ ⊔ cInHu` and `realizedH₀ ≤ hInHu`.  This
identifies the `H ⊔ N` of the second isomorphism `H/(H∩N) ≅ (H⊔N)/N` (`H = hInHu`, `N = realized
H₀C`) with the inertia subgroup `HC = hInHu ⊔ cInHu` of `clifford_caseA_regular_inertia_hc`. -/
theorem hInHu_sup_realizedH0supC {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)
      = hInHu data ⊔ cInHu data chief := by
  rw [realizedH0supC_eq_realizedH0_sup_cInHu, ← sup_assoc]
  congr 1
  exact sup_eq_left.mpr
    (Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ chief.H0_lt_H.le))

/-- **The `M`-level `HC` is `(H ⊔ C).subgroupOf M`**: the `huSub`-image of the realized inertia
subgroup `HC = hInHu ⊔ realizedH0C` (used as the source subgroup of the (13.3.a) `isIndHC`
witness) is `(data.H ⊔ cSub).subgroupOf M`.  Via `hInHu_sup_realizedH0supC` (`= hInHu ⊔ cInHu`),
`Subgroup.map_sup`, and `subgroupOf_map_subtype` collapsing each `⊓ huSub` (both `H.subgroupOf M`
and `cSub.subgroupOf M` lie below `huSub`).  In the §13 `S`-instantiation this is
`(P ⊔ C).subgroupOf S = (PC).subgroupOf S`, the `Ind_{PC}` target of (13.3.a). -/
theorem hcRealized_map_subtype_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).map
        (huSub data).subtype
      = (data.H ⊔ cSub data chief).subgroupOf M := by
  have hHsub : data.H.subgroupOf M ≤ huSub data := Subgroup.subgroupOf_mono M le_sup_left
  have hCsub : (cSub data chief).subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M ((cSub_le_U data chief).trans le_sup_right)
  rw [hInHu_sup_realizedH0supC, Subgroup.map_sup]
  show (hInHu data).map (huSub data).subtype ⊔ (cInHu data chief).map (huSub data).subtype
      = (data.H ⊔ cSub data chief).subgroupOf M
  rw [hInHu, cInHu, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left hHsub, inf_of_le_left hCsub, ← Subgroup.subgroupOf_sup (H_le_M data)
      ((cSub_le_U data chief).trans (U_le_M data))]

/-- **`H₀C ≤ M' = HU`**: `H₀ ≤ H ≤ M'` (`typeP.H_le`) and `C ≤ U ≤ M'` (`typeP.U_le`).  The second
input (`K ≤ HU`) of the generic reducible-count hypothesis (Coq `PFsection9` `nb_redM`) for the
quotient `M/H₀C`; combined with `chiefFactor_H0supC_inf_H_eq_H0` and `H₀C ◁ M` it makes the §9↔§6
count apply to `K = H₀C` (issue 1012). -/
theorem chiefFactor_H0supC_le_derived {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    chief.H0 ⊔ cSub data chief ≤ derivedInG M :=
  sup_le (chief.H0_lt_H.le.trans data.typeP.H_le)
    ((cSub_le_U data chief).trans data.typeP.U_le)

/-- **`A.map f ⊓ B.map f = (A ⊓ B).map f` when `ker f ≤ B`** (general group theory).  `⊇` is
monotonicity; for `⊆`, `f a = f b` with `b ∈ B` and `ker f ≤ B` forces `a ∈ B`, so `a ∈ A ⊓ B`.
The step (8.4.d) needs to pull `C(x̄) ⊓ K̄` out of the image (`f = mk' H₀`, `ker = H₀ ≤ K = M'`). -/
theorem map_inf_map_of_ker_le {H : Type*} [Group H] {f : G →* H} {A B : Subgroup G}
    (hB : f.ker ≤ B) : A.map f ⊓ B.map f = (A ⊓ B).map f := by
  refine le_antisymm ?_ (le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right))
  intro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨a, ha, rfl⟩ := hy.1
  obtain ⟨b, hb, hab⟩ := hy.2
  have hker : a * b⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  have haB : a ∈ B := by
    have hmem : a * b⁻¹ * b ∈ B := mul_mem (hB hker) hb
    simpa using hmem
  exact ⟨a, ⟨ha, haB⟩, rfl⟩

/-- **Peterfalvi (8.4.d), step 3 — `centralizer_W₁` transported to `↥M`**: for a lift `x` of a
nontrivial `W̄₁`-element, `C_{↥M}(x) ⊓ M' = W₂` (inside `↥M`).  The (8.4) datum
`derivedInG M ⊓ C_G(x) = W₂` (`data.centralizer_W1`) transported across `↥M ↪ G`
(`S03h.centralizer_subgroupOf`). -/
theorem chiefFactor_centralizer_inf_derived {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (x : ↥M) (hx : (x : G) ∈ data.W1) (hx1 : (x : G) ≠ 1) :
    Subgroup.centralizer ({x} : Set ↥M) ⊓ ((derivedInG M).subgroupOf M)
      = data.W2.subgroupOf M := by
  have hamb : Subgroup.centralizer ({(x : G)} : Set G) ⊓ derivedInG M = data.W2 := by
    rw [inf_comm]; exact data.typeP.centralizer_W1 (x : G) hx hx1
  rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf, Set.image_singleton]
  simp only [Subgroup.subgroupOf, ← Subgroup.comap_inf, Subgroup.coe_subtype, hamb]

/-- **Peterfalvi (8.4.d) `centralizer_W̄₂`, generic in the quotient kernel `N'`** (reused for both
`N' = H₀` and `N' = H₀C`): for `N' ◁ ↥M` with `N' ≤ M' = derivedInG M` and `gcd(|W₁|, |N'|) = 1`,
and a nontrivial `x̄ ∈ W̄₁ = W₁ N'/N'`, `C_{↥M/N'}(x̄) ⊓ (M'/N') = W₂ N'/N'`.  Three steps with the
`N'`-dependence isolated to the coprimality and the containment `ker (mk' N') = N' ≤ M'`:
`centralizer_map_mk'_eq_of_coprime_zpowers` (`gcd(|⟨x⟩|,|N'|)=1`), `map_inf_map_of_ker_le`, and the
`N'`-independent `C_{↥M}(x) ⊓ M' = W₂` (`chiefFactor_centralizer_inf_derived`). -/
theorem centralizer_W2bar_quotient [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (N' : Subgroup ↥M) [N'.Normal]
    (hN'le : N' ≤ (derivedInG M).subgroupOf M)
    (hcopW1 : Nat.Coprime (Nat.card ↥data.W1) (Nat.card ↥N'))
    (xbar : ↥M ⧸ N')
    (hxbar : xbar ∈ (data.W1.subgroupOf M).map (QuotientGroup.mk' N'))
    (hxbar1 : xbar ≠ 1) :
    Subgroup.centralizer ({xbar} : Set (↥M ⧸ N'))
        ⊓ ((derivedInG M).subgroupOf M).map (QuotientGroup.mk' N')
      = (data.W2.subgroupOf M).map (QuotientGroup.mk' N') := by
  obtain ⟨x, hx_mem, rfl⟩ := Subgroup.mem_map.mp hxbar
  have hx1 : x ≠ 1 := fun h => hxbar1 (by rw [h]; exact map_one _)
  have hxW1 : ((x : ↥M) : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp hx_mem
  have hxG1 : ((x : ↥M) : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hcardW1 : Nat.card ↥(data.W1.subgroupOf M) = Nat.card ↥data.W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.W1_le).toEquiv
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥N') := by
    refine hcopW1.coprime_dvd_left ?_
    rw [← hcardW1]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx_mem)
  rw [centralizer_map_mk'_eq_of_coprime_zpowers x hcop,
    map_inf_map_of_ker_le (B := (derivedInG M).subgroupOf M) (by
      rw [QuotientGroup.ker_mk']; exact hN'le),
    chiefFactor_centralizer_inf_derived x hxW1 hxG1]

/-- **Peterfalvi (8.4.d), `centralizer_W̄₂`** (the `N' = H₀` instance of `centralizer_W2bar_quotient`):
in `L = ↥M ⧸ H₀`, for a nontrivial `x̄ ∈ W̄₁`, `C_L(x̄) ⊓ K̄ = W̄₂` where `K̄ = M'/H₀` and
`W̄₂ = W₂ H₀/H₀`.  This is the (8.4.d) certain-type `centralizer_W₂` field of `S06.Hypothesis (M/H₀)`. -/
theorem chiefFactor_centralizer_W2bar [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(chief.H0.subgroupOf M).Normal]
    (xbar : ↥M ⧸ (chief.H0.subgroupOf M))
    (hxbar : xbar ∈ (data.W1.subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M)))
    (hxbar1 : xbar ≠ 1) :
    Subgroup.centralizer ({xbar} : Set (↥M ⧸ (chief.H0.subgroupOf M)))
        ⊓ ((derivedInG M).subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M))
      = (data.W2.subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M)) := by
  have hcardH0 : Nat.card ↥(chief.H0.subgroupOf M) = Nat.card ↥chief.H0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (chief.H0_lt_H.le.trans (H_le_M data))).toEquiv
  refine centralizer_W2bar_quotient (chief.H0.subgroupOf M) ?_ ?_ xbar hxbar hxbar1
  · exact Subgroup.comap_mono (chief.H0_lt_H.le.trans data.typeP.H_le)
  · rw [hcardH0]; exact (chiefFactor_coprime_H0_W1 chief).symm

end OddOrder.Peterfalvi.S11
