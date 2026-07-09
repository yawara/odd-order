import OddOrder.Peterfalvi.S11_MaximalII_III_IV.CliffordData

/-!
# Peterfalvi §9 — C_U(S₀) layer and character grid preparation

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


section CuS0
variable {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
  {chars : Section11CharacterData data chief}

/-- **The single-factor centralizer `C_U(S₀)`**, realized as a subgroup of `G` with `C_U(S₀) ≤ U`.
The kernel of the restricted `U`-action `aInvariantRestrictAut caseA.S0_aInvariant` on the order-`p`
factor `S₀`, pushed into `G` along `↥(U.subgroupOf (U ⊔ W₁)) ↪ ↥(U ⊔ W₁) ↪ G` (exactly as `cSub`
pushes `(uActionHom).ker`).  By the first isomorphism theorem `|U : C_U(S₀)| = |Ū₁| = caseA.a`
(`index_cuInHu_subgroupOf_uInHu_eq_a`). -/
noncomputable def cuSub (caseA : CliffordCaseAData chars) : Subgroup G :=
  ((aInvariantRestrictAut caseA.S0_aInvariant).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
    (data.typeP.U ⊔ data.typeP.W1).subtype

theorem cuSub_le_U (caseA : CliffordCaseAData chars) : cuSub caseA ≤ data.U :=
  (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans <| by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left

/-- `|C_U(S₀)| = |ker(aInvariantRestrictAut S₀)|`: the realization is the injective double-image of
the kernel (mirrors `card_cSub_eq_card_ker`). -/
theorem card_cuSub_eq_card_ker (caseA : CliffordCaseAData chars) :
    Nat.card ↥(cuSub caseA) = Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).ker := by
  show Nat.card ↥(((aInvariantRestrictAut caseA.S0_aInvariant).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
        (data.typeP.U ⊔ data.typeP.W1).subtype)
      = Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).ker
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv]

/-- `C_U(S₀)`, realized as a subgroup of `HU` inside `↥M` (mirrors `cInHu` for `C`). -/
noncomputable def cuInHu (caseA : CliffordCaseAData chars) : Subgroup ↥(huSub data) :=
  ((cuSub caseA).subgroupOf M).subgroupOf (huSub data)

theorem cuInHu_le_uInHu (caseA : CliffordCaseAData chars) : cuInHu caseA ≤ uInHu data :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (cuSub_le_U caseA))

/-- `|C_U(S₀)|` realized inside `HU` equals `|C_U(S₀)|` in `G` (mirrors `card_cInHu_eq`). -/
theorem card_cuInHu_eq (caseA : CliffordCaseAData chars) :
    Nat.card ↥(cuInHu caseA) = Nat.card ↥(cuSub caseA) := by
  have hCsubM : (cuSub caseA).subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M
      ((cuSub_le_U caseA).trans (le_sup_right : data.U ≤ data.H ⊔ data.U))
  have hCleM : cuSub caseA ≤ M := (cuSub_le_U caseA).trans (U_le_M data)
  calc Nat.card ↥(cuInHu caseA)
      = Nat.card ↥((cuSub caseA).subgroupOf M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCsubM).toEquiv
    _ = Nat.card ↥(cuSub caseA) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleM).toEquiv

open Subgroup in
/-- **`C_U(S₀) ◁ U`** (mirrors `cSub_subgroupOf_U_normal`): the realization `cuSub` is the `G`-image
of a kernel, so its `subgroupOf U` is normal (kernels are normal, transported by the realization iso
`↥(U.subgroupOf (U ⊔ W₁)) ≃* ↥U`). -/
theorem cuSub_subgroupOf_U_normal (caseA : CliffordCaseAData chars) :
    ((cuSub caseA).subgroupOf data.U).Normal := by
  set e := subgroupOfEquivOfLe (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1) with he
  have heq : (cuSub caseA).subgroupOf data.U
      = (aInvariantRestrictAut caseA.S0_aInvariant).ker.map e.toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      simp only [cuSub, Subgroup.mem_map] at hx
      obtain ⟨z, ⟨y, hy, hyz⟩, hzx⟩ := hx
      refine ⟨y, hy, ?_⟩
      apply Subtype.ext
      rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe, ← hzx, ← hyz]
      rfl
    · rintro ⟨y, hy, rfl⟩
      simp only [cuSub, Subgroup.mem_map]
      refine ⟨_, ⟨y, hy, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe]
      rfl
  rw [heq]
  exact (MonoidHom.normal_ker _).map e.toMonoidHom e.surjective

open Subgroup in
/-- **`C_U(S₀) ◁ U`** realized inside `HU` (mirrors `cInHu_normal`): `cuInHu ◁ uInHu`, transported
from `cuSub ◁ U` along `↥uInHu ≃* ↥U`. -/
theorem cuInHu_normal (caseA : CliffordCaseAData chars) :
    ((cuInHu caseA).subgroupOf (uInHu data)).Normal := by
  have hUsubM : data.U.subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_sup_right : data.U ≤ data.H ⊔ data.U)
  set f : ↥(uInHu data) ≃* ↥data.U :=
    (subgroupOfEquivOfLe hUsubM).trans (subgroupOfEquivOfLe (U_le_M data)) with hf
  have hgval : ∀ x : ↥(uInHu data), ((f x : ↥data.U) : G) = (((x : ↥(huSub data)) : ↥M) : G) := by
    intro x
    have h1 : (f x : ↥data.U)
        = subgroupOfEquivOfLe (U_le_M data) (subgroupOfEquivOfLe hUsubM x) := by rw [hf]; rfl
    rw [h1, subgroupOfEquivOfLe_apply_coe, subgroupOfEquivOfLe_apply_coe]
  have hcomap : (cuInHu caseA).subgroupOf (uInHu data)
      = ((cuSub caseA).subgroupOf data.U).comap f.toMonoidHom := by
    ext x
    simp only [cuInHu, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, hgval x]
  rw [hcomap]
  exact (cuSub_subgroupOf_U_normal caseA).comap f.toMonoidHom

/-- **`H·C_U(S₀) ◁ HU`** (mirrors `hcInHu_normal`): the inertia subgroup of the (9.8.d) source
character is normal, so `Ind_{H·C_U(S₀)}^{HU}` produces an irreducible.  From `H ◁ HU`
(`hInHu_normal`), `C_U(S₀) ◁ U` (`cuInHu_normal`), `H ⊔ U = ⊤` (`hInHu_sup_uInHu_eq_top`). -/
theorem hcuInHu_normal (caseA : CliffordCaseAData chars) :
    (hInHu data ⊔ cuInHu caseA).Normal :=
  haveI := hInHu_normal data
  haveI := cuInHu_normal caseA
  sup_normal_of_normal_left_of_normal_subgroupOf (cuInHu_le_uInHu caseA)
    (hInHu_sup_uInHu_eq_top data)

/-- **`ker(uActionHom) ≤ ker(aInvariantRestrictAut S₀)`**: an element acting trivially on the *whole*
chief factor `H̄` acts trivially on the summand `S₀ ≤ H̄`.  The subgroup inclusion behind
`C = C_U(H̄) ≤ C_U(S₀)`. -/
theorem ker_uActionHom_le_ker_aInvariantRestrictAut (caseA : CliffordCaseAData chars) :
    (uActionHom data chief).ker ≤ (aInvariantRestrictAut caseA.S0_aInvariant).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  ext s
  rw [MulAut.one_apply, aInvariantRestrictAut_coe, hx, MulAut.one_apply]

/-- **`C = C_U(H̄) ≤ C_U(S₀)`** (`cSub ≤ cuSub`): centralizing the whole chief factor implies
centralizing the summand `S₀`.  Both are `G`-images of kernels under the same double-map, and
`ker(uActionHom) ≤ ker(aInvariantRestrictAut S₀)`. -/
theorem cSub_le_cuSub (caseA : CliffordCaseAData chars) : cSub data chief ≤ cuSub caseA :=
  Subgroup.map_mono (Subgroup.map_mono (ker_uActionHom_le_ker_aInvariantRestrictAut caseA))

theorem cInHu_le_cuInHu (caseA : CliffordCaseAData chars) : cInHu data chief ≤ cuInHu caseA :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (cSub_le_cuSub caseA))

/-- **`U' ≤ C_U(S₀)`** (`uprimeSub ≤ cuSub`, Peterfalvi (9.8.d)): the derived subgroup `U' = [U,U]`
lies in the single-factor centralizer `C_U(S₀)`, via `U' ≤ C = C_U(H̄) ≤ C_U(S₀)`
(`uprimeSub_le_cSub` then `cSub_le_cuSub`).  This is the containment behind the (9.8.d) parameter
`λ ∈ Irr(C_U(S₀)/U')` and the `𝒮(H₀U')`-membership of the induced characters. -/
theorem uprimeSub_le_cuSub [Finite G] (caseA : CliffordCaseAData chars) :
    uprimeSub data ≤ cuSub caseA :=
  (uprimeSub_le_cSub data chief).trans (cSub_le_cuSub caseA)

/-- **`U' ≤ C_U(S₀)` realized inside `HU`** (`Uprime`/`uprimeSub` ⟶ `cuInHu`).  The `HU`-realized form
of `uprimeSub_le_cuSub`: `(U'.subgroupOf M).subgroupOf HU ≤ cuInHu`.  Used to identify `λ` trivial on
`U'` as a character of `C_U(S₀)/U'` in the (9.8.d) count. -/
theorem uprimeSub_subgroupOf_le_cuInHu [Finite G] (caseA : CliffordCaseAData chars) :
    ((uprimeSub data).subgroupOf M).subgroupOf (huSub data) ≤ cuInHu caseA :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (uprimeSub_le_cuSub caseA))

/-- **`H ⊓ U ≤ C_U(S₀)`** realized (`hInHu ⊓ uInHu ≤ cuInHu`): an `H ⊓ U` element centralizes the
chief factor `H̄` (`hInHu_inf_uInHu_le_cInHu`), hence `S₀ ≤ H̄` (`cInHu_le_cuInHu`). -/
theorem hInHu_inf_uInHu_le_cuInHu [Finite G] (caseA : CliffordCaseAData chars) :
    hInHu data ⊓ uInHu data ≤ cuInHu caseA :=
  (hInHu_inf_uInHu_le_cInHu data chief).trans (cInHu_le_cuInHu caseA)

/-- **`H ⊓ C_U(S₀) = ⊥`** realized (`hInHu ⊓ cuInHu = ⊥`).  Since `C_U(S₀) ≤ U`, an element of
`hInHu ⊓ cuInHu` has `G`-image in `H ⊓ U = ⊥` (a type-P setup, `typeP_H_inf_U`), so it is trivial.
This is the trivial-intersection input `H ⊓ C_U(S₀) = ⊥` that makes the second isomorphism
`(H·C_U(S₀))/C_U(S₀) ≅ H` (used to build the `θ₁·λ` source character on `H·C_U(S₀)`), mirroring
`hInHu_inf_cInHu_eq_bot` for the (9.8.c) `hcLambdaHom`. -/
theorem hInHu_inf_cuInHu_eq_bot [Finite G] (caseA : CliffordCaseAData chars) :
    hInHu data ⊓ cuInHu caseA = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxU := cuInHu_le_uInHu caseA hxC
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

/-- **`H·C_U(S₀) = C_U(S₀)·H`** (spelling bridge, mirrors `hcRealized_eq_cInHu_sup_hInHu`): the
`sup_comm` reorientation of the (9.8.d) inertia subgroup, used to phrase the `λ`-lift channel
`hcuLambdaHom` via the second isomorphism `(C_U(S₀)·H)/H ≅ C_U(S₀)`. -/
theorem hcuInHu_eq_cuInHu_sup_hInHu (caseA : CliffordCaseAData chars) :
    hInHu data ⊔ cuInHu caseA = cuInHu caseA ⊔ hInHu data :=
  sup_comm _ _

/-- **`|U| = a · |C_U(S₀)|`** (Peterfalvi (9.7.a)): the order of `U` splits as the Clifford index
`a = [U:C_U(S₀)]` times the centralizer order.  Rearranges the first-isomorphism value `|U| = |Ū₁| ·
|C_U(S₀)|` (the `hII` step of `index_cuInHu_subgroupOf_uInHu_eq_a`) using the pin `a = |Ū₁|`
(`a_eq_card_restrictAut_range`).  The arithmetic behind the (9.8.d) domain-count identity
`|U|/(a|U'|) = |C_U(S₀):U'|`. -/
theorem card_U_eq_a_mul_card_cuSub [Finite G] (caseA : CliffordCaseAData chars) :
    Nat.card ↥data.U = caseA.a * Nat.card ↥(cuSub caseA) := by
  rw [caseA.a_eq_card_restrictAut_range]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (aInvariantRestrictAut caseA.S0_aInvariant).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (aInvariantRestrictAut caseA.S0_aInvariant)).toEquiv,
    ← card_cuSub_eq_card_ker caseA,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).toEquiv] at h
  exact h

/-- **`|U|/(a·|U'|) = |C_U(S₀):U'|`** (Peterfalvi (9.8.d) domain-count identity): the count
`((p-1)/a)·(|U|/(a|U'|))` in the (9.8.d) statement equals `((p-1)/a)·|C_U(S₀):U'|`, the number of
`(θ₁,λ)`-pairs divided by the `U`-orbit size `a`.  Since `|U| = a·|C_U(S₀)|`
(`card_U_eq_a_mul_card_cuSub`) and `|U'| ∣ |C_U(S₀)|` (`U' ≤ C_U(S₀)`, `uprimeSub_le_cuSub`), the
`a` cancels: `|U|/(a·|U'|) = a·|C_U(S₀)|/(a·|U'|) = |C_U(S₀)|/|U'| = [C_U(S₀):U']`.  Here
`[C_U(S₀):U'] = (uprimeSub data).relIndex (cuSub caseA)` (the relative index of `U'` in `C_U(S₀)`,
a genuine subgroup index since `U' ≤ C_U(S₀)`). -/
theorem card_U_div_a_mul_card_Uprime_eq_relIndex [Finite G] (caseA : CliffordCaseAData chars) :
    Nat.card ↥data.U / (caseA.a * Nat.card ↥(uprimeSub data))
      = (uprimeSub data).relIndex (cuSub caseA) := by
  have hUprime_le : uprimeSub data ≤ cuSub caseA := uprimeSub_le_cuSub caseA
  -- `[C_U(S₀):U'] · |U'| = |C_U(S₀)|` (via `[K:H]·|H| = |K|` for `H = U'.subgroupOf C_U(S₀)`)
  have hrel : (uprimeSub data).relIndex (cuSub caseA) * Nat.card ↥(uprimeSub data)
      = Nat.card ↥(cuSub caseA) := by
    have h := Subgroup.index_mul_card ((uprimeSub data).subgroupOf (cuSub caseA))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUprime_le).toEquiv] at h
  rw [card_U_eq_a_mul_card_cuSub caseA, ← hrel]
  -- `a·([C_U(S₀):U']·|U'|) / (a·|U'|) = [C_U(S₀):U']`
  rw [show caseA.a * ((uprimeSub data).relIndex (cuSub caseA) * Nat.card ↥(uprimeSub data))
      = ((uprimeSub data).relIndex (cuSub caseA)) * (caseA.a * Nat.card ↥(uprimeSub data)) by ring]
  exact Nat.mul_div_cancel _ (Nat.mul_pos caseA.a_pos Nat.card_pos)

/-- `C_U(S₀) ≤ H·C_U(S₀)` (mirrors `cInHu_le_hcRealized`): `cuInHu` is contained in the inertia
subgroup `hInHu ⊔ cuInHu`. -/
theorem cuInHu_le_hcuInHu (caseA : CliffordCaseAData chars) :
    cuInHu caseA ≤ hInHu data ⊔ cuInHu caseA :=
  le_sup_right

/-- **The `λ`-lift `H·C_U(S₀) →* ℂˣ`** of a linear character `λ : C_U(S₀) →* ℂˣ` (the `C`-factor of
the (9.8.d) pair character `θ₁·λ`): the composite `H·C_U(S₀) → H·C_U(S₀)/H ≅ C_U(S₀)/(C_U(S₀) ⊓ H)
= C_U(S₀) —λ→ ℂˣ`, using the trivial intersection `H ⊓ C_U(S₀) = ⊥` (`hInHu_inf_cuInHu_eq_bot`).
Mirrors the (9.9.c) `hcLambdaHom` rewired from `cInHu` to `cuInHu`; `hInHu` is normal in the sup, so
the quotient map is well-defined.  Kills `H` (`hcuLambdaHom_eq_one_of_mem_hInHu`) and restricts to
`λ` on `C_U(S₀)` (`hcuLambdaHom_inclusion`). -/
noncomputable def hcuLambdaHom [Finite G] (caseA : CliffordCaseAData chars)
    (lam : ↥(cuInHu caseA) →* ℂˣ) :
    ↥(hInHu data ⊔ cuInHu caseA) →* ℂˣ :=
  haveI := hInHu_normal data
  letI : ((hInHu data).subgroupOf (cuInHu caseA ⊔ hInHu data)).Normal :=
    (hInHu_normal data).subgroupOf _
  (QuotientGroup.lift ((hInHu data).subgroupOf (cuInHu caseA)) lam
      (fun x hx => by
        have hx1 : x = 1 := by
          have hmem : (x : ↥(huSub data)) ∈ hInHu data ⊓ cuInHu caseA :=
            ⟨Subgroup.mem_subgroupOf.mp hx, x.2⟩
          rw [hInHu_inf_cuInHu_eq_bot caseA, Subgroup.mem_bot] at hmem
          exact Subtype.ext hmem
        rw [hx1]
        exact lam.ker.one_mem)).comp
    ((QuotientGroup.quotientInfEquivProdNormalQuotient (cuInHu caseA)
        (hInHu data)).symm.toMonoidHom.comp
      ((QuotientGroup.mk' ((hInHu data).subgroupOf (cuInHu caseA ⊔ hInHu data))).comp
        (MulEquiv.subgroupCongr (hcuInHu_eq_cuInHu_sup_hInHu caseA)).toMonoidHom))

/-- **`hcuLambdaHom` kills `H`** (mirrors `hcLambdaHom_eq_one_of_mem_hInHu`): the `λ`-lift is trivial
on the `H`-part of `H·C_U(S₀)` (the quotient map by `hInHu` kills it).  So the pair character
`θ₁·λ` restricts on `hInHu` to the plain seed inflation `θ₀`, and the (9.8.d) inertia lift
`inertia_eq_hcuInHu` applies to the pair unchanged. -/
theorem hcuLambdaHom_eq_one_of_mem_hInHu [Finite G] (caseA : CliffordCaseAData chars)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    {x : ↥(hInHu data ⊔ cuInHu caseA)}
    (hx : x ∈ (hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)) :
    hcuLambdaHom caseA lam x = 1 := by
  haveI := hInHu_normal data
  letI : ((hInHu data).subgroupOf (cuInHu caseA ⊔ hInHu data)).Normal :=
    (hInHu_normal data).subgroupOf _
  simp only [hcuLambdaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply]
  have hmem : (MulEquiv.subgroupCongr (hcuInHu_eq_cuInHu_sup_hInHu caseA)) x
      ∈ (hInHu data).subgroupOf (cuInHu caseA ⊔ hInHu data) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx)
  rw [(QuotientGroup.eq_one_iff _).mpr hmem, map_one, map_one]

/-- **`hcuLambdaHom` restricts to `λ` on `C_U(S₀)`** (mirrors `hcLambdaHom_inclusion`): on the
inclusion of `c ∈ cuInHu` into `H·C_U(S₀)`, the `λ`-lift returns `λ c`.  The second iso sends the
`cuInHu`-class to the `H·C_U(S₀)`-class via inclusion (`hfwd`), so the reversed iso undoes the
quotient map and the lift evaluates `λ`. -/
theorem hcuLambdaHom_inclusion [Finite G] (caseA : CliffordCaseAData chars)
    (lam : ↥(cuInHu caseA) →* ℂˣ) (c : ↥(cuInHu caseA)) :
    hcuLambdaHom caseA lam (Subgroup.inclusion (cuInHu_le_hcuInHu caseA) c) = lam c := by
  haveI := hInHu_normal data
  letI : ((hInHu data).subgroupOf (cuInHu caseA ⊔ hInHu data)).Normal :=
    (hInHu_normal data).subgroupOf _
  have hfwd : (QuotientGroup.quotientInfEquivProdNormalQuotient (cuInHu caseA)
        (hInHu data))
      (QuotientGroup.mk' _ c)
      = QuotientGroup.mk' _ (Subgroup.inclusion le_sup_left c) := by
    simp only [QuotientGroup.quotientInfEquivProdNormalQuotient,
      QuotientGroup.quotientInfEquivProdNormalizerQuotient, MulEquiv.trans_apply,
      QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.quotientKerEquivOfSurjective,
      QuotientGroup.quotientKerEquivOfRightInverse, MulEquiv.coe_mk, MulEquiv.symm_mk,
      MonoidHom.toMulEquiv_apply, QuotientGroup.kerLift_mk]
    rfl
  simp only [hcuLambdaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have hcongr : (MulEquiv.subgroupCongr (hcuInHu_eq_cuInHu_sup_hInHu caseA))
      (Subgroup.inclusion (cuInHu_le_hcuInHu caseA) c)
      = Subgroup.inclusion le_sup_left c := by
    apply Subtype.ext
    rfl
  rw [hcongr, QuotientGroup.mk'_apply, show ((Subgroup.inclusion le_sup_left c :
      ↥(cuInHu caseA ⊔ hInHu data)) : ↥(cuInHu caseA ⊔ hInHu data)
        ⧸ (hInHu data).subgroupOf (cuInHu caseA ⊔ hInHu data))
      = QuotientGroup.mk' _ (Subgroup.inclusion le_sup_left c) from rfl, ← hfwd,
    MulEquiv.symm_apply_apply, QuotientGroup.mk'_apply, QuotientGroup.lift_mk]

/-- **`U ⊓ H·C_U(S₀) = C_U(S₀)`** realized (`uInHu ⊓ (hInHu ⊔ cuInHu) = cuInHu`), the second-iso
input for `[HU : H·C_U(S₀)] = [U : C_U(S₀)]`.  Mirrors `uInHu_inf_hcInHu_eq_cInHu`. -/
theorem uInHu_inf_hcuInHu_eq_cuInHu [Finite G] (caseA : CliffordCaseAData chars) :
    uInHu data ⊓ (hInHu data ⊔ cuInHu caseA) = cuInHu caseA := by
  haveI := hInHu_normal data
  apply le_antisymm
  · rintro x ⟨hxU, hxHC⟩
    obtain ⟨hh, hhmem, cc, ccmem, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxHC
    have hcc_u : cc ∈ uInHu data := cuInHu_le_uInHu caseA ccmem
    have hh_u : hh ∈ uInHu data := by
      have h1 : hh * cc * cc⁻¹ ∈ uInHu data :=
        (uInHu data).mul_mem hxU ((uInHu data).inv_mem hcc_u)
      rwa [mul_inv_cancel_right] at h1
    have hh_c : hh ∈ cuInHu caseA :=
      hInHu_inf_uInHu_le_cuInHu caseA (Subgroup.mem_inf.mpr ⟨hhmem, hh_u⟩)
    exact (cuInHu caseA).mul_mem hh_c ccmem
  · exact le_inf (cuInHu_le_uInHu caseA) le_sup_right

/-- **Second-iso index step: `[HU : H·C_U(S₀)] = [U : C_U(S₀)]`** (realized
`(hInHu ⊔ cuInHu).index = (cuInHu.subgroupOf uInHu).index`).  Mirrors
`index_hcInHu_eq_relindex_cInHu`: the second isomorphism theorem for `H·C_U(S₀) ◁ HU` with
`uInHu ⊔ H·C_U(S₀) = ⊤`, and `uInHu ⊓ H·C_U(S₀) = cuInHu`. -/
theorem index_hcuInHu_eq_relindex_cuInHu [Finite G] (caseA : CliffordCaseAData chars) :
    (hInHu data ⊔ cuInHu caseA).index
      = ((cuInHu caseA).subgroupOf (uInHu data)).index := by
  haveI : (hInHu data ⊔ cuInHu caseA).Normal := hcuInHu_normal caseA
  have htop : uInHu data ⊔ (hInHu data ⊔ cuInHu caseA) = ⊤ := by
    rw [← sup_assoc, sup_comm (uInHu data) (hInHu data), hInHu_sup_uInHu_eq_top, top_sup_eq]
  have he := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient
    (uInHu data) (hInHu data ⊔ cuInHu caseA)).toEquiv
  have hsub : (hInHu data ⊔ cuInHu caseA).subgroupOf (uInHu data)
      = (cuInHu caseA).subgroupOf (uInHu data) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxin : (x : ↥(huSub data)) ∈ uInHu data ⊓ (hInHu data ⊔ cuInHu caseA) :=
        Subgroup.mem_inf.mpr ⟨x.2, hx⟩
      rw [uInHu_inf_hcuInHu_eq_cuInHu caseA] at hxin
      exact hxin
    · intro hx; exact Subgroup.mem_sup_right hx
  rw [hsub] at he
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((hInHu data ⊔ cuInHu caseA).subgroupOf (uInHu data ⊔ (hInHu data ⊔ cuInHu caseA)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
        (hInHu data ⊔ cuInHu caseA) ≤ uInHu data ⊔ (hInHu data ⊔ cuInHu caseA))).toEquiv,
    ← he, ← Subgroup.index_eq_card] at hsplit
  have htopcard : Nat.card ↥(uInHu data ⊔ (hInHu data ⊔ cuInHu caseA))
      = Nat.card ↥(huSub data) := by
    rw [htop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [htopcard] at hsplit
  have hmul := Subgroup.card_mul_index (hInHu data ⊔ cuInHu caseA)
  rw [hsplit, mul_comm (((cuInHu caseA).subgroupOf (uInHu data)).index)] at hmul
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

/-- **`[U : C_U(S₀)] = |Ū₁|`** (realized `(cuInHu.subgroupOf uInHu).index = |range(aInvariantRestrictAut S₀)|`).
Mirrors `index_cInHu_subgroupOf_uInHu_eq_u`: the first isomorphism theorem for the restricted
`U`-action `aInvariantRestrictAut caseA.S0_aInvariant` on `S₀`, whose image `Ū₁` has order the index
`a` of `C_U(S₀)` in `U`.  This is the value `clifford_caseA_data` assigns to `CliffordCaseAData.a`. -/
theorem index_cuInHu_subgroupOf_uInHu_eq_a [Finite G] (caseA : CliffordCaseAData chars) :
    ((cuInHu caseA).subgroupOf (uInHu data)).index
      = Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).range := by
  -- (I): `|C_U(S₀)| · [U:C_U(S₀)] = |U|`.
  have hI : Nat.card ↥(cuSub caseA) * ((cuInHu caseA).subgroupOf (uInHu data)).index
      = Nat.card ↥data.U := by
    have h := Subgroup.card_mul_index ((cuInHu caseA).subgroupOf (uInHu data))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cuInHu_le_uInHu caseA)).toEquiv,
      card_cuInHu_eq caseA, card_uInHu_eq data] at h
    exact h
  -- (II): `|U| = |Ū₁| · |C_U(S₀)|` (first iso for the restricted action hom, domain `≃* ↥U`).
  have hII : Nat.card ↥data.U
      = Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).range * Nat.card ↥(cuSub caseA) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (aInvariantRestrictAut caseA.S0_aInvariant).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
        (aInvariantRestrictAut caseA.S0_aInvariant)).toEquiv,
      ← card_cuSub_eq_card_ker caseA,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).toEquiv] at h
    exact h
  have hcancel : Nat.card ↥(cuSub caseA)
      * ((cuInHu caseA).subgroupOf (uInHu data)).index
      = Nat.card ↥(cuSub caseA) * Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).range := by
    rw [hI, hII, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcancel

/-- **`[HU : H·C_U(S₀)] = |Ū₁| = a`** (Peterfalvi (9.8.d) degree index).  The inertia subgroup of the
degree-`qa` source character `θ₁·λ` has index `a` in `HU`, giving the source degree `a` and (after
`Ind_{HU}^M`) the character degree `qa`.  Combines the second-iso step `[HU:H·C_U(S₀)] = [U:C_U(S₀)]`
(`index_hcuInHu_eq_relindex_cuInHu`) with the first-iso value `[U:C_U(S₀)] = |Ū₁|`
(`index_cuInHu_subgroupOf_uInHu_eq_a`).  Here `|Ū₁| = Nat.card (aInvariantRestrictAut …).range` is the
genuine geometric `a = |U:C_U(H₁)|`, the value `clifford_caseA_data` assigns to `caseA.a`. -/
theorem index_hcuInHu_eq_a [Finite G] (caseA : CliffordCaseAData chars) :
    (hInHu data ⊔ cuInHu caseA).index
      = Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).range :=
  (index_hcuInHu_eq_relindex_cuInHu caseA).trans (index_cuInHu_subgroupOf_uInHu_eq_a caseA)

/-- **`[HU : H·C_U(S₀)] = a`** (Peterfalvi (9.8.d), with `a = CliffordCaseAData.a`).  The genuine
geometric index `[HU : H·C_U(S₀)] = |Ū₁|` (`index_hcuInHu_eq_a`) equals the carrier's `a`, since `a`
is pinned to `|Ū₁|` (`CliffordCaseAData.a_eq_card_restrictAut_range`).  This is the degree of the
(9.8.d) source character `Ind_{H·C_U(S₀)}^{HU}(θ₁·λ)`, whence `Ind_{HU}^M` of it has degree `qa`. -/
theorem index_hcuInHu_eq_caseA_a [Finite G] (caseA : CliffordCaseAData chars) :
    (hInHu data ⊔ cuInHu caseA).index = caseA.a := by
  rw [index_hcuInHu_eq_a caseA, caseA.a_eq_card_restrictAut_range]

end CuS0

/-- **realized `H₀U' = (realized H₀) ⊔ (realized U')`** (Peterfalvi (9.8.d); mirror of
`realizedH0supCprime_eq_realizedH0_sup_cprimeInHu`): the realized `H₀U'` inside `HU` equals the join
of the realized `H₀` and the realized `U'`.  Feeds the `h₀·u'` decomposition of the (9.8.d) pair
character's kernel computation. -/
theorem realizedH0supUprime_eq_realizedH0_sup_uprimeInHu {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ((chief.H0 ⊔ uprimeSub data).subgroupOf M).subgroupOf (huSub data)
      = (chief.H0.subgroupOf M).subgroupOf (huSub data)
          ⊔ ((uprimeSub data).subgroupOf M).subgroupOf (huSub data) := by
  have hH0M : chief.H0 ≤ M := chief.H0_lt_H.le.trans (H_le_M data)
  have hUM : uprimeSub data ≤ M := (uprimeSub_le_U data).trans (U_le_M data)
  rw [Subgroup.subgroupOf_sup hH0M hUM]
  have hH0sub : (chief.H0.subgroupOf M) ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_trans chief.H0_lt_H.le le_sup_left)
  have hUsub : (uprimeSub data).subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_trans (uprimeSub_le_U data) le_sup_right)
  rw [Subgroup.subgroupOf_sup hH0sub hUsub]

/-- **(9.7) Clifford dimension dichotomy** (the arithmetic heart of (9.7)).  Restricting the
`U W₁`-action on the chief factor `H̄ = H/H₀` to `U`, there is a minimal `U`-invariant `S₀ ≠ ⊥` of
order `p^d` with `0 < d` and `d ∣ q`.  Since `q` is prime, `d ∈ {1, q}`: the dichotomy of (9.7),
case (a) (`d = 1`, `U` semisimple into order-`p` pieces) vs case (b) (`d = q`, `U` irreducible).

Assembled from the spanning step (`iSup_smul_eq_top_of_irreducible`, on the `U W₁`-irreducible `H̄`),
the orbit lemmas (each `U W₁`-translate of `S₀` is `U`-irreducible of order `|S₀|`), and the order
step (`card_eq_pow_of_iSup_aInvariant_irreducible`): `|H̄| = |S₀|^k`, while `|H̄| = p^q`, so
`p^q = (p^d)^k`, i.e. `q = d·k`. -/
theorem chiefFactor_clifford_dim_dvd_q [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ∃ (d : ℕ) (S₀ : Subgroup (↥data.H ⧸ chief.N)),
      0 < d ∧ d ∣ data.q ∧ S₀ ≠ ⊥ ∧ Nat.card ↥S₀ = chief.p ^ d ∧
      IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) S₀ ∧
      (∀ J, IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J ≤ S₀ → J = ⊥ ∨ J = S₀) := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  haveI : chief.N.Normal := chief.N_normal
  haveI := Fact.mk chief.p_prime
  -- The descended `U W₁`-action on the chief factor `H̄` and its restriction to the kernel `U`.
  set act := typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  have hUnorm : act.U.Normal := (typeP_uW1_frobenius data.typeP hU).isNormal
  have hKcard : Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q := chiefFactor_quotient_card chief
  have hq_pos : 0 < data.q := Nat.card_pos
  haveI hKnt : Nontrivial (↥data.H ⧸ chief.N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hKcard]; exact Nat.one_lt_pow hq_pos.ne' chief.p_prime.one_lt)
  -- A minimal nonzero `U`-invariant subgroup `S₀` (the `U`-irreducible Clifford piece).
  set T : Set (Subgroup (↥data.H ⧸ chief.N)) := {J | J ≠ ⊥ ∧ IsAInvariant φU J} with hT
  obtain ⟨S₀, ⟨hS₀ne, hS₀inv⟩, hS₀min⟩ :=
    (Set.toFinite T).exists_minimal ⟨⊤, top_ne_bot, IsAInvariant.top _⟩
  have hirr₀ : ∀ J, IsAInvariant φU J → J ≤ S₀ → J = ⊥ ∨ J = S₀ := by
    intro J hJinv hJle
    by_cases hJ0 : J = ⊥
    · exact Or.inl hJ0
    · exact Or.inr (le_antisymm hJle (hS₀min ⟨hJ0, hJinv⟩ hJle))
  -- `|S₀| = p^d` (subgroup of the elementary abelian `p`-group `H̄`).
  obtain ⟨d, hd⟩ := (chief.quotient_elementaryAbelian.to_subgroup S₀).isPGroup.exists_card_eq
  -- Spanning step (full action) + order step (restricted `U`-action) give `|H̄| = |S₀|^k`.
  have hspan : ⨆ a, act.φ a • S₀ = ⊤ :=
    iSup_smul_eq_top_of_irreducible (φ := act.φ) chief.quotient_chiefFactor hS₀ne
  obtain ⟨k, hk⟩ := card_eq_pow_of_iSup_aInvariant_irreducible
    (φ := φU) (S := fun a => act.φ a • S₀) (n := Nat.card ↥S₀)
    (fun x y => chief.quotient_elementaryAbelian.comm x y) hspan
    (fun a => isAInvariant_comp_subtype_pointwise_smul hUnorm hS₀inv a)
    (fun a J hJinv hJle => forall_aInvariant_le_pointwise_smul hUnorm hirr₀ a J hJinv hJle)
    (fun a _ => card_pointwise_smul act.φ a S₀)
  -- Arithmetic: `p^q = (p^d)^k = p^{d·k}`, so `q = d·k`.
  rw [hd, hKcard, ← pow_mul] at hk
  have hdk : data.q = d * k := Nat.pow_right_injective chief.p_prime.two_le hk
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · rw [h0, pow_zero] at hd; exact absurd (Subgroup.card_eq_one.mp hd) hS₀ne
    · exact h
  exact ⟨d, S₀, hdpos, ⟨k, hdk⟩, hS₀ne, hd, hS₀inv, hirr₀⟩

/-- **(9.7) structural dichotomy** (the Clifford case split, read off the chief factor).  With
`q = |W₁|` prime, the chief factor `H̄` is, under the restricted `U`-action, *either*
`U`-irreducible (Clifford case (b): every `U`-invariant subgroup is `⊥` or `⊤`) *or* contains a
`U`-invariant subgroup of order `p` (Clifford case (a)).

This is the arithmetic dichotomy `d ∈ {1, q}` of `chiefFactor_clifford_dim_dvd_q` read through the
primality of `q`: the minimal nonzero `U`-invariant piece `S₀` has order `p^d` with `d ∣ q`, so
either `d = q` (`|S₀| = p^q = |H̄|`, hence `S₀ = ⊤`, and minimality forces `U`-irreducibility)
or `d = 1` (`|S₀| = p`).  Packaging the two cases into the carriers `CliffordCaseAData` /
`CliffordCaseBData` (the order-`p` factor pullback / the `End_{𝔽ₚ[U]}(H̄)` field model) is the
remaining work of `clifford_dichotomy`. -/
theorem chiefFactor_clifford_U_dichotomy [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) ∨
    (∃ S₀ : Subgroup (↥data.H ⧸ chief.N), S₀ ≠ ⊥ ∧
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) S₀ ∧ Nat.card ↥S₀ = chief.p ∧
        ∀ J, IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J ≤ S₀ → J = ⊥ ∨ J = S₀) := by
  obtain ⟨d, S₀, _hdpos, hdq, hS₀ne, hcard, hS₀inv, hirr₀⟩ :=
    chiefFactor_clifford_dim_dvd_q chief
  -- `q = |W₁|` is prime and `d ∣ q`, so `d = 1` or `d = q`.
  have hq_prime : (data.q).Prime := data.nontrivial.2.1
  rcases hq_prime.eq_one_or_self_of_dvd d hdq with hd1 | hdq2
  · -- `d = 1`: a `U`-invariant subgroup of order `p`.  Clifford case (a).
    exact Or.inr ⟨S₀, hS₀ne, hS₀inv, by rw [hcard, hd1, pow_one], hirr₀⟩
  · -- `d = q`: `|S₀| = p^q = |H̄|` ⟹ `S₀ = ⊤`; minimality ⟹ `U`-irreducible.  Case (b).
    have hS₀top : S₀ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcard, hdq2, chiefFactor_quotient_card chief])
    refine Or.inl fun J hJinv => ?_
    by_cases hJ : J = ⊥
    · exact Or.inl hJ
    · exact Or.inr
        (((hirr₀ J hJinv (le_top.trans_eq hS₀top.symm)).resolve_left hJ).trans hS₀top)

open OddOrder.RepresentationTheory Representation in
open scoped commutatorElement IsMulCommutative in
/-- **Peterfalvi (9.7) case (b), chief-factor Singer conclusion.**  When `U` acts irreducibly on
the chief factor `H̄ = H/H₀` (Clifford case (b) — the left branch of
`chiefFactor_clifford_U_dichotomy`), its image `Ū = φ_U(U) ≤ Aut(H̄)` is *cyclic*, of order
dividing `p^q - 1`.

`Ū` is abelian because `[U, U]` centralizes `H` (Peterfalvi (8.5.b),
`typeP_commutator_U_centralizes_H`): a commutator `⁅a, b⁆ ∈ [U, U]` acts trivially on `H̄`, so
`φ_U ⁅a, b⁆ = 1` and the image is commutative.  Faithfulness of the inclusion `Ū ↪ Aut(H̄)` and the
irreducibility transferred from the case-(b) hypothesis feed the canonical module-level Singer
mechanism `isCyclic_and_card_dvd_of_faithful_irreducible_comm` (shared `SingerField` leaf) through
the thin adapter `elabRepresentation_isSimpleModule_and_faithful`, with `H̄` the elementary abelian
`p`-group of order `p^q` (`chiefFactor_quotient_card`).  This is the structural core behind the
`Coprime u (p-1)` / `u ∣ (p^q-1)/(p-1)` divisibilities of `CliffordCaseBData` (which additionally
pin `u = |Ū|` and use the `W₁`-fixed-point-free refinement). -/
theorem chiefFactor_caseB_image_cyclic [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    IsCyclic ↥(((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype).range) ∧
      Nat.card ↥(((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype).range) ∣ chief.p ^ data.q - 1 := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  haveI : chief.N.Normal := chief.N_normal
  haveI : NeZero chief.p := ⟨chief.p_prime.pos.ne'⟩
  set act := typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  -- `H̄ = ↥H ⧸ N` is finite elementary abelian `p`, nontrivial, of order `p^q`.
  have hKcard : Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q := chiefFactor_quotient_card chief
  have hq_pos : 0 < data.q := Nat.card_pos
  haveI hKnt : Nontrivial (↥data.H ⧸ chief.N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hKcard]; exact Nat.one_lt_pow hq_pos.ne' chief.p_prime.one_lt)
  -- Module instances for the Singer mechanism, from `chief.quotient_elementaryAbelian`.
  letI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  letI : CommGroup (↥data.H ⧸ chief.N) := inferInstance
  letI : Module (ZMod chief.p) (Additive (↥data.H ⧸ chief.N)) :=
    chief.quotient_elementaryAbelian.zmodModule
  -- An element of `U W₁` centralizing `H` acts trivially on `H̄`.
  have hcentral_triv : ∀ g : ↥(data.typeP.U ⊔ data.typeP.W1),
      (g : G) ∈ Subgroup.centralizer (data.typeP.H : Set G) → act.φ g = 1 := by
    intro g hg
    have hfix : ∀ x : ↥data.typeP.H, (typeP_conjAction data.typeP g) x = x := by
      intro x
      apply Subtype.ext
      rw [typeP_conjAction_apply]
      have hcom : (x : G) * (g : G) = (g : G) * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp hg) (x : G) x.2
      rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
    ext y
    refine QuotientGroup.induction_on y ?_
    intro x
    show (act.φ g) (QuotientGroup.mk' chief.N x) = QuotientGroup.mk' chief.N x
    have hstep : (act.φ g) (QuotientGroup.mk' chief.N x)
        = QuotientGroup.mk' chief.N ((typeP_conjAction data.typeP g) x) := rfl
    rw [hstep, hfix x]
  -- `Ū = φU.range` is abelian: `φU ⁅a, b⁆ = 1` since `⁅a, b⁆` maps into `[U, U] ⊆ C(H)`.
  have hComm : ∀ a b : ↥act.U, Commute (φU a) (φU b) := by
    intro a b
    refine commutatorElement_eq_one_iff_commute.mp ?_
    rw [← map_commutatorElement φU a b]
    show act.φ (act.U.subtype ⁅a, b⁆) = 1
    apply hcentral_triv
    change ((data.typeP.U ⊔ data.typeP.W1).subtype.comp act.U.subtype) ⁅a, b⁆
        ∈ Subgroup.centralizer (data.typeP.H : Set G)
    rw [map_commutatorElement]
    exact typeP_commutator_U_centralizes_H data.typeP
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2))
  -- Package the data for the Singer mechanism.
  have hAcomm : ∀ s t : ↥(φU.range), s * t = t * s := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext (hComm a b)
  have hirr : ∀ J : Subgroup (↥data.H ⧸ chief.N),
      IsAInvariant (φU.range).subtype J → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    apply hcaseB
    intro a
    exact hJ ⟨φU a, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have hfaith : ∀ a : ↥(φU.range),
      (∀ x : (↥data.H ⧸ chief.N), ((φU.range).subtype a) x = x) → a = 1 := by
    intro a ha
    have hone : (a : MulAut (↥data.H ⧸ chief.N)) = 1 := by
      ext x
      simpa using ha x
    exact Subtype.ext hone
  -- Thin adapter into the canonical module-level Singer lemma (shared leaf, issue 9000).
  obtain ⟨hcyc, hdvd⟩ := singerAdapter_isCyclic_card_dvd
    (A := ↥(φU.range)) (K := ↥data.H ⧸ chief.N) (p := chief.p)
    (φ := (φU.range).subtype) hAcomm hKnt hirr hfaith
  exact ⟨hcyc, by rwa [hKcard] at hdvd⟩

open OddOrder.RepresentationTheory Representation in
open scoped commutatorElement IsMulCommutative in
/-- **Peterfalvi (9.7) case (b), the fixed-point-free coprimality `Coprime |Ū| (p-1)`.**  When `U`
acts irreducibly on the chief factor `H̄ = H/H₀` (Clifford case (b)), the image `Ū = φ_U(U)` has
order coprime to `p - 1`.

This discharges the hard `coprime` hypothesis of `chiefFactor_caseB_image_dvd_norm` from the
Frobenius structure of `U W₁`: a nonidentity `w₀ ∈ W₁` acts on `Ū` fixed-point-freely.  Indeed if
`act.φ(w₀)` commutes with `φ_U(u)` then `⁅w₀, u⁆` acts trivially on `H̄`, so `u` lies in a
`w₀`-fixed coset of `C_U(H̄)`; Isaacs Cor 3.28 (`coprime_fixedPoints_quotient`) extracts a `w₀`-fixed
representative `c ∈ u·C_U(H̄)`, and `c ∈ C_U(w₀) = 1` by the Frobenius condition
(`centralizer_complement_le`, `U ⊓ W₁ = ⊥`), forcing `u ∈ C_U(H̄)`, i.e. `φ_U(u) = 1`.  The
canonical module-level `coprime_card_sub_one_of_faithful_irreducible_comm_fpf` (shared
`SingerField` leaf, via `elabRepresentation_isSimpleModule_and_faithful` +
`exists_addEquiv_asModule_fpf`) then gives the coprimality. -/
theorem chiefFactor_caseB_image_coprime [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    Nat.Coprime (Nat.card ↥(((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype).range)) (chief.p - 1) := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  haveI : chief.N.Normal := chief.N_normal
  haveI : NeZero chief.p := ⟨chief.p_prime.pos.ne'⟩
  haveI : Fact chief.p.Prime := ⟨chief.p_prime⟩
  set act := typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  haveI hUnorm : act.U.Normal := (typeP_uW1_frobenius data.typeP hU).isNormal
  have hKcard : Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q := chiefFactor_quotient_card chief
  have hq_pos : 0 < data.q := Nat.card_pos
  haveI hKnt : Nontrivial (↥data.H ⧸ chief.N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hKcard]; exact Nat.one_lt_pow hq_pos.ne' chief.p_prime.one_lt)
  letI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  letI : CommGroup (↥data.H ⧸ chief.N) := inferInstance
  letI : Module (ZMod chief.p) (Additive (↥data.H ⧸ chief.N)) :=
    chief.quotient_elementaryAbelian.zmodModule
  -- Abelianness, irreducibility, faithfulness of `Ū = φU.range` (as in `chiefFactor_caseB_image_cyclic`).
  have hcentral_triv : ∀ g : ↥(data.typeP.U ⊔ data.typeP.W1),
      (g : G) ∈ Subgroup.centralizer (data.typeP.H : Set G) → act.φ g = 1 := by
    intro g hg
    have hfix : ∀ x : ↥data.typeP.H, (typeP_conjAction data.typeP g) x = x := by
      intro x
      apply Subtype.ext
      rw [typeP_conjAction_apply]
      have hcom : (x : G) * (g : G) = (g : G) * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp hg) (x : G) x.2
      rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
    ext y
    refine QuotientGroup.induction_on y ?_
    intro x
    show (act.φ g) (QuotientGroup.mk' chief.N x) = QuotientGroup.mk' chief.N x
    have hstep : (act.φ g) (QuotientGroup.mk' chief.N x)
        = QuotientGroup.mk' chief.N ((typeP_conjAction data.typeP g) x) := rfl
    rw [hstep, hfix x]
  have hComm : ∀ a b : ↥act.U, Commute (φU a) (φU b) := by
    intro a b
    refine commutatorElement_eq_one_iff_commute.mp ?_
    rw [← map_commutatorElement φU a b]
    show act.φ (act.U.subtype ⁅a, b⁆) = 1
    apply hcentral_triv
    change ((data.typeP.U ⊔ data.typeP.W1).subtype.comp act.U.subtype) ⁅a, b⁆
        ∈ Subgroup.centralizer (data.typeP.H : Set G)
    rw [map_commutatorElement]
    exact typeP_commutator_U_centralizes_H data.typeP
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2))
  have hAcomm : ∀ s t : ↥(φU.range), s * t = t * s := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext (hComm a b)
  have hirr : ∀ J : Subgroup (↥data.H ⧸ chief.N),
      IsAInvariant (φU.range).subtype J → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    apply hcaseB
    intro a
    exact hJ ⟨φU a, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have hfaith : ∀ a : ↥(φU.range),
      (∀ x : (↥data.H ⧸ chief.N), ((φU.range).subtype a) x = x) → a = 1 := by
    intro a ha
    have hone : (a : MulAut (↥data.H ⧸ chief.N)) = 1 := by
      ext x
      simpa using ha x
    exact Subtype.ext hone
  -- The fixed-point-free witness: a nonidentity `w₀ ∈ W₁` inside `↥(U ⊔ W₁)`.
  obtain ⟨w, hwW1, hwne⟩ :=
    (data.typeP.W1.bot_or_exists_ne_one).resolve_left data.typeP.W1_nontrivial
  have hwUW1 : w ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_right hwW1
  set w₀ : ↥(data.typeP.U ⊔ data.typeP.W1) := ⟨w, hwUW1⟩ with hw₀def
  have hw₀E : w₀ ∈ act.E := by
    show (⟨w, hwUW1⟩ : ↥(data.typeP.U ⊔ data.typeP.W1)) ∈
      data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
    rw [Subgroup.mem_subgroupOf]; exact hwW1
  have hw₀ne : w₀ ≠ 1 := fun h => hwne (Subtype.ext_iff.mp h)
  -- Conjugation action `ψ` of `U W₁` on the kernel `act.U`, and how `φU` transforms under it.
  set ψ : ↥(data.typeP.U ⊔ data.typeP.W1) →* MulAut ↥act.U := MulAut.conjNormal with hψdef
  have hψcoe : ∀ (g : ↥(data.typeP.U ⊔ data.typeP.W1)) (y : ↥act.U),
      (act.U.subtype (ψ g y) : ↥(data.typeP.U ⊔ data.typeP.W1)) =
        (g : ↥(data.typeP.U ⊔ data.typeP.W1)) * act.U.subtype y * g⁻¹ :=
    fun g y => MulAut.conjNormal_apply g y
  have hφUconj : ∀ (g : ↥(data.typeP.U ⊔ data.typeP.W1)) (y : ↥act.U),
      φU (ψ g y) = act.φ g * φU y * (act.φ g)⁻¹ := by
    intro g y
    have he : φU (ψ g y) = act.φ ((g : ↥(data.typeP.U ⊔ data.typeP.W1)) * act.U.subtype y * g⁻¹) := by
      show act.φ (act.U.subtype (ψ g y)) = _
      rw [hψcoe]
    rw [he, map_mul, map_mul, map_inv]; rfl
  -- The kernel `N = C_U(H̄)` of `φU`, and its `ψ`-invariance.
  set N : Subgroup ↥act.U := φU.ker with hNdef
  have hN_inv : IsAInvariant (ψ.comp (Subgroup.zpowers w₀).subtype) N := by
    rw [isAInvariant_iff_smul_mem]
    intro a y hy
    rw [hNdef, MonoidHom.mem_ker] at hy ⊢
    show φU (ψ ((Subgroup.zpowers w₀).subtype a) y) = 1
    rw [hφUconj, hy, mul_one, mul_inv_cancel]
  -- Coprimality and solvability inputs for Isaacs Cor 3.28.
  have hCop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers w₀)) (Nat.card ↥act.U) := by
    have hkc : Nat.Coprime (Nat.card ↥act.U) (Nat.card ↥act.E) :=
      (typeP_uW1_frobenius data.typeP hU).coprime_card_kernel_complement
    exact Nat.Coprime.coprime_dvd_left
      (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hw₀E)) hkc.symm
  have hSolv : IsSolvable ↥(Subgroup.zpowers w₀) ∨ IsSolvable ↥act.U :=
    Or.inl (isSolvable_of_comm fun a b => by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]; group))
  -- The fixed-point-free hypothesis for `σ = act.φ w₀`, in subgroup terms.
  have hfpfσ : ∀ a : ↥(φU.range),
      (∀ x : ↥data.H ⧸ chief.N,
        (act.φ w₀) (((φU.range).subtype a) x) = ((φU.range).subtype a) ((act.φ w₀) x)) →
      a = 1 := by
    intro a ha
    obtain ⟨u₀, hu₀⟩ := a.2
    -- `↑a = φU u₀ = act.φ u₀'`, and `act.φ w₀` commutes with it.
    have ha1 : ((φU.range).subtype a : MulAut (↥data.H ⧸ chief.N)) = act.φ (act.U.subtype u₀) :=
      hu₀.symm
    have hCm : Commute (act.φ w₀) (act.φ (act.U.subtype u₀)) := by
      show act.φ w₀ * act.φ (act.U.subtype u₀) = act.φ (act.U.subtype u₀) * act.φ w₀
      apply MulEquiv.ext
      intro x
      rw [MulAut.mul_apply, MulAut.mul_apply, ← ha1]
      exact ha x
    -- `hg_fix`: each `w₀^k`-conjugate of `u₀` lands in `u₀ · N`.
    have hg_fix : ∀ aa : ↥(Subgroup.zpowers w₀),
        ∃ n ∈ N, (ψ.comp (Subgroup.zpowers w₀).subtype) aa u₀ = u₀ * n := by
      intro aa
      refine ⟨u₀⁻¹ * (ψ ((Subgroup.zpowers w₀).subtype aa) u₀), ?_, ?_⟩
      · rw [hNdef, MonoidHom.mem_ker, map_mul, map_inv, hφUconj]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp aa.2
        have hcaφ : act.φ ((Subgroup.zpowers w₀).subtype aa) = (act.φ w₀) ^ k := by
          rw [show (Subgroup.zpowers w₀).subtype aa = w₀ ^ k from hk.symm, map_zpow]
        have hcomm_k : Commute (act.φ ((Subgroup.zpowers w₀).subtype aa)) (φU u₀) := by
          rw [hcaφ]; exact hCm.zpow_left k
        rw [show act.φ ((Subgroup.zpowers w₀).subtype aa) * φU u₀ *
              (act.φ ((Subgroup.zpowers w₀).subtype aa))⁻¹ = φU u₀ by
          rw [hcomm_k.eq, mul_assoc, mul_inv_cancel, mul_one], inv_mul_cancel]
      · rw [MonoidHom.comp_apply, mul_inv_cancel_left]
    -- Isaacs Cor 3.28: a `w₀`-fixed representative `c ∈ u₀ · N`.
    obtain ⟨c, hc_fix, n, hn, hc_eq⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient
        (φ := ψ.comp (Subgroup.zpowers w₀).subtype) hCop hSolv hN_inv hg_fix
    -- `c` commutes with `w₀`, so `c ∈ C_U(w₀) ⊆ W₁`; as `c ∈ U`, `c = 1`.
    have hc_w₀ : ψ w₀ c = c := by
      have := hc_fix ⟨w₀, Subgroup.mem_zpowers w₀⟩
      rwa [MonoidHom.comp_apply] at this
    have hc_comm : (act.U.subtype c : ↥(data.typeP.U ⊔ data.typeP.W1)) * w₀ =
        w₀ * act.U.subtype c := by
      have h := congrArg act.U.subtype hc_w₀
      rw [hψcoe] at h
      -- `h : w₀ * subtype c * w₀⁻¹ = subtype c`
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    have hc_in_E : (act.U.subtype c : ↥(data.typeP.U ⊔ data.typeP.W1)) ∈ act.E := by
      refine (typeP_uW1_frobenius data.typeP hU).centralizer_complement_le w₀ hw₀E hw₀ne ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc_comm
    have hc_in_U : (act.U.subtype c : ↥(data.typeP.U ⊔ data.typeP.W1)) ∈ act.U := c.2
    have hc1 : (act.U.subtype c : ↥(data.typeP.U ⊔ data.typeP.W1)) = 1 :=
      Subgroup.disjoint_def.mp (typeP_uW1_frobenius data.typeP hU).isComplement.disjoint
        hc_in_U hc_in_E
    have hc0 : c = 1 := act.U.subtype_injective (by rw [hc1, map_one])
    -- `1 = c = u₀ · n` ⟹ `u₀ ∈ N` ⟹ `φU u₀ = 1` ⟹ `a = 1`.
    rw [hc0] at hc_eq
    have hu₀N : u₀ ∈ N := by
      have : u₀ = n⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← hc_eq]
      rw [this]; exact N.inv_mem hn
    apply Subtype.ext
    rw [← hu₀, Subgroup.coe_one]
    exact (MonoidHom.mem_ker (f := φU)).mp hu₀N
  -- Thin adapter into the canonical module-level Singer FPF-coprimality (shared leaf, issue 9000).
  exact singerAdapter_coprime_fpf
    (A := ↥(φU.range)) (K := ↥data.H ⧸ chief.N) (p := chief.p) (φ := (φU.range).subtype)
    hAcomm hKnt hirr hfaith (act.φ w₀) hfpfσ

open OddOrder.RepresentationTheory Representation in
open scoped commutatorElement IsMulCommutative in
/-- **Peterfalvi (9.7) case (b), the `u ∣ (p^q-1)/(p-1)` divisibility** (unconditional).

The Singer divisibility `|Ū| ∣ p^q-1` (`chiefFactor_caseB_image_cyclic`) upgrades to
`|Ū| ∣ (p^q-1)/(p-1)` via the fixed-point-free coprimality `Coprime |Ū| (p-1)`
(`chiefFactor_caseB_image_coprime`): since `(p-1) ∣ (p^q-1)` and `|Ū|` is coprime to `p-1`,
`|Ū|·(p-1) ∣ p^q-1`, hence `|Ū| ∣ (p^q-1)/(p-1)`.  This is the second case-(b) divisibility of
`CliffordCaseBData`, now established without any external coprimality hypothesis. -/
theorem chiefFactor_caseB_image_dvd_norm [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    Nat.card ↥(((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype).range) ∣ (chief.p ^ data.q - 1) / (chief.p - 1) := by
  have hcop := chiefFactor_caseB_image_coprime chief hcaseB
  obtain ⟨_, hdvd⟩ := chiefFactor_caseB_image_cyclic chief hcaseB
  -- The arithmetic core is the shared `SingerLineBound` lemma (issue 9000 dedup).
  exact dvd_div_of_coprime_of_dvd_sub_one chief.p_prime.pos hdvd hcop

open scoped commutatorElement in
/-- **Peterfalvi (9.7) case (b): the `U`-action on `H̄` is fixed-point-free off `C = C_U(H̄)`.**
When `U` acts irreducibly on the chief factor `H̄ = H/H₀` (Clifford case (b)), any `g ∈ U` whose
image `φ_U(g)` is nontrivial (i.e. `g ∉ C`) acts fixed-point-freely on `H̄`: `φ_U(g)·x = x → x = 1`.

This is the structural heart of Peterfalvi (9.9) — `H̄ ⋊ Ū` is a Frobenius group, so a nontrivial
character `θ` of `H̄` has inertia `I(θ) ∩ U = C`, giving the degree `u = |U:C|` of the irreducible
characters of `HU` in `𝒳(H₀C')`.  The proof is pure Clifford theory: the image `Ū = φ_U(U)` is
abelian (`hComm`: `⁅a,b⁆ ∈ [U,U] ⊆ C_M(H)`) and acts irreducibly (`hcaseB`), so
`fixedPointFree_of_aInvariant_irreducible_comm` applies; the Singer field model is *not* needed. -/
theorem chiefFactor_caseB_action_fpf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hg : ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) g ≠ 1)
    (x : ↥data.H ⧸ chief.N)
    (hx : ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) g x = x) : x = 1 := by
  classical
  haveI : chief.N.Normal := chief.N_normal
  set act := typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  -- An element of `U W₁` centralizing `H` acts trivially on `H̄`.
  have hcentral_triv : ∀ c : ↥(data.typeP.U ⊔ data.typeP.W1),
      (c : G) ∈ Subgroup.centralizer (data.typeP.H : Set G) → act.φ c = 1 := by
    intro c hc
    have hfix : ∀ z : ↥data.typeP.H, (typeP_conjAction data.typeP c) z = z := by
      intro z
      apply Subtype.ext
      rw [typeP_conjAction_apply]
      have hcom : (z : G) * (c : G) = (c : G) * (z : G) :=
        (Subgroup.mem_centralizer_iff.mp hc) (z : G) z.2
      rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
    ext y
    refine QuotientGroup.induction_on y ?_
    intro z
    show (act.φ c) (QuotientGroup.mk' chief.N z) = QuotientGroup.mk' chief.N z
    have hstep : (act.φ c) (QuotientGroup.mk' chief.N z)
        = QuotientGroup.mk' chief.N ((typeP_conjAction data.typeP c) z) := rfl
    rw [hstep, hfix z]
  -- `Ū = φU(U)` is abelian: `φU ⁅a, b⁆ = 1` since `⁅a, b⁆` maps into `[U, U] ⊆ C(H)`.
  have hComm : ∀ a b : ↥act.U, Commute (φU a) (φU b) := by
    intro a b
    refine commutatorElement_eq_one_iff_commute.mp ?_
    rw [← map_commutatorElement φU a b]
    show act.φ (act.U.subtype ⁅a, b⁆) = 1
    apply hcentral_triv
    change ((data.typeP.U ⊔ data.typeP.W1).subtype.comp act.U.subtype) ⁅a, b⁆
        ∈ Subgroup.centralizer (data.typeP.H : Set G)
    rw [map_commutatorElement]
    exact typeP_commutator_U_centralizes_H data.typeP
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2))
  exact fixedPointFree_of_aInvariant_irreducible_comm hComm hcaseB _ hg x hx

/-- **Peterfalvi (9.9): the `U`-action on `Irr(H̄)` is fixed-point-free off `C`.**  In Clifford
case (b), if a nontrivial irreducible character `θ` of the chief factor `H̄ = ↥H ⧸ N` is invariant
under the `U`-action `φ_U(g)`, then `g` acts trivially (`φ_U(g) = 1`, i.e. `g ∈ C = C_U(H̄)`).

This is the **character-side inertia** `I_U(θ) ⊆ C` of Peterfalvi (9.9.a), proven *realization-free*:
the abelian `Irr ↔ Hom` bridge (`exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative`)
turns `θ` into a linear character `θ̂`, and a `φ_U(g)`-invariant `θ̂` with `φ_U(g)` fixed-point-free
(`chiefFactor_caseB_action_fpf`, valid for `g ∉ C`) is trivial
(`eq_one_of_invariant_of_fixedPointFree`), contradicting `θ` nontrivial.  No realization of `H̄` as
a subgroup is needed; it works on the abstract quotient `↥H ⧸ N` with the abstract action `φ_U`. -/
theorem chiefFactor_caseB_char_inertia [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θ : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθ : (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hinv : ∀ x, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)
        (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) g x)
          = (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype) g
        = 1 := by
  classical
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  by_contra hne
  have hfpf : MonoidHom.FixedPointFree
      (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
        (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) g) :=
    chiefFactor_caseB_action_fpf chief hcaseB g hne
  obtain ⟨θhom, hθhom⟩ :=
    exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative θ.isIrreducible
  have hinvhom : ∀ x, θhom (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).U.subtype) g x) = θhom x := fun x =>
    Units.ext (by rw [hθhom, hθhom]; exact hinv x)
  have h1 : θhom = 1 := eq_one_of_invariant_of_fixedPointFree hfpf hinvhom
  apply hθ
  ext x
  have hx := hθhom x
  rw [h1] at hx
  simpa using hx.symm

/-- **Non-Galois (9.8) core, generic over the factor family.**  As `chiefFactor_caseA_char_inertia`
but taking the order-`p`, `U`-invariant, spanning factor family `Hpart` directly (rather than from
`CliffordCaseAData`), so the `W1`-conjugates `{S₀^w}` — which have the same properties but are not
the producer's `caseA.Hpart` family — can drive the inertia argument for the free-`W1`-orbit
character of (9.8.c). -/
theorem chiefFactor_caseA_char_inertia_gen [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {ι : Type*} (Hpart : ι → Subgroup (↥data.H ⧸ chief.N))
    (hp_order : ∀ i, Nat.card ↥(Hpart i) = chief.p)
    (hspan : ⨆ i, Hpart i = ⊤)
    (haInv : ∀ i, IsAInvariant (uActionHom data chief) (Hpart i))
    {θ : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∀ i, ∃ x ∈ Hpart i,
      (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hinv : ∀ x, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) ((uActionHom data chief) g x)
        = (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) :
    (uActionHom data chief) g = 1 := by
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  refine mulAut_eq_one_of_fixes_regular_on_prime_span ((uActionHom data chief) g) Hpart
    (fun i => ?_) (fun i x hx => ?_) hspan θ hreg hinv
  · rw [hp_order i]; exact chief.p_prime
  · exact (haInv i).smul_mem g hx

/-- **Peterfalvi (9.8), case (a) non-Galois core**: the case-(a) analog of
`chiefFactor_caseB_char_inertia`.  When `U` acts on `H̄ = H/N` with a `U`-invariant order-`p` factor
(case (a) of (9.7), packaged as `CliffordCaseAData`), a character `θ` that is **regular** (nontrivial
on each of the `q` order-`p` Clifford summands `Hpart i`) and fixed by `φ_U(g)` forces `φ_U(g) = 1`.

This is the `def_Itheta` computation `I_{HU}(θ̄) = HC` for the *reducible* (= regular) characters in
case (a): `θ̄` linear and faithful on each order-`p` summand
(`mulAut_eq_one_of_fixes_regular_on_prime_span`), with the summand data supplied non-opaquely by
`CliffordCaseAData.Hpart_order`/`Hpart_iSup`/`Hpart_aInvariant`. -/
theorem chiefFactor_caseA_char_inertia [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {θ : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∀ i, ∃ x ∈ caseA.Hpart i,
      (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hinv : ∀ x, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) ((uActionHom data chief) g x)
        = (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) :
    (uActionHom data chief) g = 1 := by
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  refine mulAut_eq_one_of_fixes_regular_on_prime_span ((uActionHom data chief) g) caseA.Hpart
    (fun i => ?_) (fun i x hx => ?_) caseA.Hpart_iSup θ hreg hinv
  · rw [caseA.Hpart_order i]; exact chief.p_prime
  · exact (caseA.Hpart_aInvariant i).smul_mem g hx

/-- **Peterfalvi (9.8.d) single-factor char-inertia core**: the single-factor analog of
`chiefFactor_caseA_char_inertia`.  For a character `θ₁` nontrivial on the order-`p` orbit generator
`S₀ = H₁` (`hreg` on `caseA.S0`), a `U`-element `g` fixing `θ₁` acts *trivially on `S₀`*, i.e.
`aInvariantRestrictAut caseA.S0_aInvariant g = 1`.  This — not `uActionHom g = 1` — is the correct
conclusion for (9.8.d): `θ₁` need only be faithful on the *single* summand `S₀`, so the fixing
element centralizes `S₀` (lands in `C_U(S₀)`), not necessarily all of `H̄`.  The pure-algebra heart
is `mulAut_eq_id_on_of_fixes_ne_one_on_prime` (`θ₁` faithful on the prime-order `S₀`), lifted through
`aInvariantRestrictAut_coe` (which identifies the restricted action with `uActionHom` on `S₀`).  This
gives `I(θ₁) ∩ U ⊆ C_U(S₀)` in the degree-`qa` inertia lift. -/
theorem chiefFactor_caseA_char_inertia_single [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {θ : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∃ x ∈ caseA.S0,
      (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hinv : ∀ x, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) ((uActionHom data chief) g x)
        = (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) :
    aInvariantRestrictAut caseA.S0_aInvariant g = 1 := by
  haveI : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  -- `φg = uActionHom g` acts as the identity on the prime-order summand `S₀` (single-factor core).
  have hS0card : Nat.card ↥caseA.S0 = chief.p := by
    have h := caseA.Hpart_order ⟨0, data.nontrivial.2.1.pos⟩
    rwa [caseA.Hpart_orbit ⟨0, data.nontrivial.2.1.pos⟩, card_pointwise_smul] at h
  have hid : ∀ x ∈ caseA.S0, (uActionHom data chief) g x = x :=
    mulAut_eq_id_on_of_fixes_ne_one_on_prime ((uActionHom data chief) g) caseA.S0
      (by rw [hS0card]; exact chief.p_prime)
      (fun x hx => caseA.S0_aInvariant.smul_mem g hx) θ hreg hinv
  -- Lift to `aInvariantRestrictAut … g = 1` via the coercion `(restrict g x : H̄) = uActionHom g x`.
  ext x
  rw [MulAut.one_apply, aInvariantRestrictAut_coe, hid x x.2]

/-- **Inflation equivariance for the chief-factor action.**  The inflation map
`compHom (mk' N) : ClassFunction (↥H/N) → ClassFunction ↥H` intertwines the conjugation action
`typeP_conjAction a` on `↥H` (upstairs) with the descended action `quotientMulAutHom a` on the
chief factor `↥H/N` (downstairs): inflating `θ̄` and acting by `a` upstairs equals acting by `a`
downstairs and then inflating.  Immediate from `quotientMulAutHom_apply_mk'`
(`mk' N (a · h) = a · (mk' N h)`).

This is the algebraic core that turns the *concrete* conjugation invariance of an inflated
character into the *abstract* `φ_U`-invariance consumed by `chiefFactor_caseB_char_inertia`,
without realizing `H̄` as a subgroup. -/
theorem compHom_typeP_conjAction_inflation [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (a : ↥(data.typeP.U ⊔ data.typeP.W1))
    (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) :
    ClassFunction.compHom (typeP_conjAction data.typeP a).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N) θbar)
      = ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (ClassFunction.compHom (quotientMulAutHom chief.N_aInvariant a).toMonoidHom θbar) :=
  rfl

/-- **Char-inertia inflation, parametrized over the core stabilizer-triviality `hcore`.**
Strips the inflation (`compHom_typeP_conjAction_inflation`, `mk'` injective) from the `compHom`-fixing
hypothesis to feed the per-element action-invariance to `hcore`.  Case (b) supplies `hcore` as
`chiefFactor_caseB_char_inertia` (`U`-irreducible); case (a) via the non-Galois `Hpart` analysis. -/
theorem caseB_char_inertia_inflation_of_core [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hcore : ∀ (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U),
        (∀ x, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
            (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
              (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype) g x)
              = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) →
        ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) g = 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hfix : ClassFunction.compHom (typeP_conjAction data.typeP
              ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype g)).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))
            = ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) g = 1 := by
  rw [compHom_typeP_conjAction_inflation] at hfix
  have hfix2 := ClassFunction.compHom_injective_of_surjective
    (QuotientGroup.mk'_surjective chief.N) hfix
  apply hcore g
  intro x
  rw [show ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) g
      = quotientMulAutHom chief.N_aInvariant
          ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype g) from rfl]
  exact congrFun (congrArg (fun f : ClassFunction (↥data.H ⧸ chief.N) ℂ =>
    (f : (↥data.H ⧸ chief.N) → ℂ)) hfix2) x

theorem caseB_char_inertia_inflation [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθbar : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hfix : ClassFunction.compHom (typeP_conjAction data.typeP
              ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype g)).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))
            = ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) g = 1 :=
  caseB_char_inertia_inflation_of_core (chiefFactor_caseB_char_inertia hcaseB hθbar) g hfix

/-! ### (9.9.a) realization: concrete `HU`-conjugation ↔ abstract `typeP_conjAction`

The (9.9.a) inertia of a constituent of `Res^{HU}_H χ` is computed by `ClassFunction.conjBy` in
`HU = (H ⊔ U).subgroupOf M`, with `H` realized as `hInHu data = (H.subgroupOf M).subgroupOf HU`.
The realization iso `hInHuEquivH : ↥(hInHu) ≃* ↥H` (composite of two `subgroupOfEquivOfLe`)
preserves the underlying `G`-element, so it intertwines `conjBy g` (for `g ∈ HU`) with the
abstract `typeP_conjAction a` (for `a ∈ U W₁` with the same `G`-image).  This is the last
realization step of (9.9.a)'s `I_U(θ) ⊆ C`: it turns a concrete `HU`-inertia hypothesis into the
`typeP_conjAction`-invariance consumed by `caseB_char_inertia_inflation`. -/

/-- The realization iso `↥(H-in-HU) ≃* ↥H`: `H` realized inside `HU = H ⊔ U` is `H`, via the
composite of `subgroupOfEquivOfLe (H.subgroupOf M ≤ HU)` and `subgroupOfEquivOfLe (H ≤ M)`. -/
noncomputable def hInHuEquivH {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    ↥(hInHu data) ≃* ↥data.H :=
  (Subgroup.subgroupOfEquivOfLe
      (Subgroup.subgroupOf_mono M (le_sup_left : data.H ≤ data.H ⊔ data.U))).trans
    (Subgroup.subgroupOfEquivOfLe (data.typeP.H_le.trans (derivedInG_le_self M)))

/-- The realization iso preserves the underlying `G`-element. -/
theorem hInHuEquivH_coe {M : Subgroup G} (data : TypesIIIIIIVSetup M) (h : ↥(hInHu data)) :
    ((hInHuEquivH data h : ↥data.H) : G) = (((h : ↥(huSub data)) : ↥M) : G) := rfl

/-- **(9.9.a) realization, conjugation equivariance.**  Under the iso
`hInHuEquivH : ↥(hInHu) ≃* ↥H`, the concrete conjugation `conjBy g` in `HU` (for `g ∈ HU`)
corresponds to the abstract conjugation `typeP_conjAction a` on `↥H` (for `a ∈ U W₁` with the same
`G`-image `↑g = ↑a`).  Both are conjugation by the same `G`-element, so the equality reduces to
`g·h·g⁻¹ = a·h·a⁻¹` in `G`. -/
theorem conjBy_compHom_hInHuEquivH {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (a : ↥(data.typeP.U ⊔ data.typeP.W1)) (g : ↥(huSub data))
    (hag : ((g : ↥M) : G) = (a : G)) (θ : ClassFunction ↥data.H ℂ) :
    ClassFunction.conjBy g (ClassFunction.compHom (hInHuEquivH data).toMonoidHom θ)
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (typeP_conjAction data.typeP a).toMonoidHom θ) := by
  ext h
  rw [ClassFunction.conjBy_apply, ClassFunction.compHom_apply, ClassFunction.compHom_apply,
    ClassFunction.compHom_apply]
  refine congrArg _ (Subtype.ext ?_)
  simp only [MulEquiv.coe_toMonoidHom, hInHuEquivH_coe, typeP_conjAction_apply,
    Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hag]

/-- **Realized stabilizer-triviality, parametrized over the char-inertia core `hcharInertia`.**
The case-agnostic transport: a `U`-element `a` realized by `g ∈ HU` fixing `θ₀` (`conjBy` form) is
turned into the `compHom (typeP_conjAction)` form (`conjBy_compHom_hInHuEquivH`, injective inflation)
and fed to `hcharInertia` to conclude `φ a = 1`.  Case (b) supplies `hcharInertia` as
`caseB_char_inertia_inflation`; case (a) via the non-Galois analog. -/
theorem caseB_inertia_realized_of_charInertia [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hcharInertia : ∀ (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U),
        ClassFunction.compHom (typeP_conjAction data.typeP
              ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype g)).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))
            = ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) →
        ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) g = 1)
    (a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (g : ↥(huSub data))
    (hag : ((g : ↥M) : G) =
      (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G))
    (hfix : ClassFunction.conjBy g
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) a = 1 := by
  rw [conjBy_compHom_hInHuEquivH data
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype a)
    g hag] at hfix
  exact hcharInertia a
    (ClassFunction.compHom_injective_of_surjective (hInHuEquivH data).surjective hfix)

theorem caseB_inertia_realized [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθbar : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _)
    (a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (g : ↥(huSub data))
    (hag : ((g : ↥M) : G) =
      (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G))
    (hfix : ClassFunction.conjBy g
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) a = 1 :=
  caseB_inertia_realized_of_charInertia (caseB_char_inertia_inflation hcaseB hθbar) a g hag hfix

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
    show ((Pi.evalMonoidHom (fun k : Fin data.q => ↥(caseA.Hpart k)) j₀).comp
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
  haveI : W.Normal := Subgroup.normal_of_comm W
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
    show (hInHu data).comap _ ⊓ (cuInHu caseA).comap _ = ⊥
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
    Units.val_mul, hcuThetaHom_inclusion_hInHu, hlam1, Units.val_one, mul_one, hcuSeedHom,
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
      simp [hcuPsiPair, linearIrreducibleCharacter_apply_one], mul_one]

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
  simp only [ClassFunction.conjBy_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
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
  haveI : W.Normal := Subgroup.normal_of_comm W
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
  haveI : W.Normal := Subgroup.normal_of_comm W
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
  show quotientMulAutHom chief.N_aInvariant
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
    show data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
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
    show data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
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
    show data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
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
