/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_MaximalIII_IV_V_Core
import OddOrder.Peterfalvi.S08_SixTwoGeneral
import OddOrder.GroupTheory.PiElementDecomposition

/-!
# Peterfalvi (11.8.1): the §9 counts for the §10 grid

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 12, pp. 58--63 — the (11.8.1) step of the (11.8)
non-orthogonality argument.

The §9 (repo `S11`) character analysis applied to the §10 `Hypothesis` (10.1)
on a type-III/IV maximal subgroup:

* the `Hypothesis → TypesIIIIIIVSetup → Section11CharacterData` bridge
  (`toTypesIIIIIIVSetup`, `mkSection11CharacterData`);
* the identification of the §10 μ-grid column sums `μ_k = ∑_i μ_{ik}`
  (`0 < k`) with the reducible members of the §9 family `𝒮(H₀)`
  (`muGrid_column_sum_mem_sOf_H0_and_reducible` — Coq `PFsection11`
  `memSred`, by counting);
* the Frobenius congruences `|U| ≡ 1 (mod q)` (`card_U_modEq_one`) and
  `|Ū| ≡ 1 (mod q)` (`mkSection11CharacterData_u_modEq_one`);
* the resulting (11.8.1) parameter facts: the residue `d ≡ 1 (mod q)`
  (`charParam_d_modEq_one`, via the degree `d = |Ū|`) and the column sign
  `δ = 1` (`charParam_delta_eq_one`).

The `|𝒮(HC)| = n` count (`card_SHCSet_filter_eq_charParam_n`) is the
remaining (11.8.1) obligation.
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## The `Hypothesis (10.1)` → §9 bridge -/

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **Construct the §9 `Section11CharacterData` from the §10 `Hypothesis`** (the key unblocker for
the (11.8.1) §9 counts).  Given the §9 setup `data` (`toTypesIIIIIIVSetup`) and a chief factor
`chief` (`exists_chiefFactorData`), the §9 character datum's *character* fields are all derived from
`data`/`chief` (the families `𝒳 = xiSet`, `𝒮 = Ind_{HU}^M 𝒳`, `𝒮(Y)`); the only genuine fields are
`u = |Ū|` (pinned to the `U`-action image on the chief factor, `rfl`) and the degree-irrelevant
`tau`/`H0CprimeSupport`/`quotientSemidirectFrobenius` (used only by the (9.11) coherence, not by the
degree fact `caseB_degree_qu`).  So the §9 *degree* analysis — `clifford_dichotomy` (9.7) and the
`μ_j(1) = qu` of (9.8)/(9.9) — becomes available on the §10 `Hypothesis`.  (`tau := hyp.tau` records
the genuine Dade map for the coherence use; the support/`Prop` are placeholders for the count use.) -/
noncomputable def Hypothesis.mkSection11CharacterData [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData data) :
    OddOrder.Peterfalvi.S11.Section11CharacterData data chief where
  u := Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).range)
  u_eq_card_quotient := rfl
  H0CprimeSupport := ∅
  tau := hyp.tau
  quotientSemidirectFrobenius := True

open OddOrder.Peterfalvi.S11 in
/-- **§9 degree `qu` on the §10 `Hypothesis`, case (b) branch** (validating `mkSection11CharacterData`
end-to-end).  Via the constructed `Section11CharacterData`, the (9.7) Clifford dichotomy
(`clifford_dichotomy`, proven) splits into case (a)/(b); in case (b), `caseB_degree_qu` gives that
every member of the §9 family `𝒮(H₀C')` has degree `q·u = q·|Ū|`.  This is the §9 half of the
(11.8.1) degree `d = |Ū|` (the μ-grid column `μ_j = ∑_i μ_{ij}` has degree `qu`, so `μ_{ij}(1) = u`);
combined with the μ-grid ↔ §9-family correspondence (`huSub = M'`, `chars.S ⊆ inducedFamily`) it
gives `d = |Ū|`.  The case (a) branch (reducible-induction degree, `caseA_reducible_*`) is the
remaining case. -/
theorem Hypothesis.forall_sOf_H0Cprime_degree_qu_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data)
    (caseB : CliffordCaseBData (hyp.mkSection11CharacterData data chief)) :
    ∀ φ ∈ (hyp.mkSection11CharacterData data chief).SOf
        (chief.H0 ⊔ (hyp.mkSection11CharacterData data chief).Cprime),
      φ 1 = ((data.q * (hyp.mkSection11CharacterData data chief).u : ℕ) : ℂ) :=
  caseB_degree_qu hG (hyp.mkSection11CharacterData data chief) caseB

/-- **Bridge to the §9 (repo S11) character analysis.**  A §10 type-III/IV `Hypothesis` yields the
§9 `TypesIIIIIIVSetup` on the same `M`, sharing the type-`P` structure `(H, U, W₁, W₂)`.  This is the
`Hypothesis` → `Section11CharacterData` bridge the (11.8.1) §9 counts need: with it,
`exists_chiefFactorData` produces the chief factor `H̄ = H/H₀`, and the §9 results (`caseB_degree_qu`
for `μ_j(1) = qu`, `coherent_H0C_commutator` for the (9.11) `S(H₀C')` coherence) apply to the §10
character parameters.  `type_alt` restricts to III/IV (type V is eliminated separately by
`no_typeV_maximal`); the `nontrivial` core (`U ≠ ⊥`, `|W₁|` prime, the `M_F`-TI condition) is the §8
structural input, threaded as `hnt` (obtainable from the type data via
`typePNontrivialCore_of_isTypeIIIorIV`). -/
def Hypothesis.toTypesIIIIIIVSetup [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP) :
    OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M where
  maximal := hyp.maximal
  typeP := hyp.typeP
  nontrivial := hnt
  type_alt := htype.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))

/-- **Peterfalvi (11.8.1), the Frobenius congruence `|U| ≡ 1 (mod q)`.**  The type-`P` group
`U ⋊ W₁` is a Frobenius group with kernel `U` (`typeP_uW1_frobenius`, `U ≠ ⊥` from the type-`P`
`U_nontrivial`), so by Isaacs Lemma 6.1 (`card_kernel_modEq_one`) `|U| ≡ 1 (mod |W₁| = q)`.  This is
the group-theoretic half of (11.8.1)'s `δ = 1`: with the (9.8)/(9.9) degree `d = μ_{ij}(1) = |Ū|`
and the `U/C_U(H̄)`-quotient of this congruence `|Ū| ≡ 1 (mod q)`, the index relation `n·q = d − δ`
(`δ = ±1`) forces `d ≡ 1 (mod q)`, i.e. `δ = 1`. -/
theorem Hypothesis.card_U_modEq_one [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (hU : hyp.typeP.U ≠ ⊥) :
    Nat.card ↥hyp.typeP.U ≡ 1 [MOD hyp.w1] := by
  have h := (OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.typeP hU).card_kernel_modEq_one
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at h
  exact h

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **Peterfalvi (11.8.1), the chief-factor image congruence `|Ū| ≡ 1 (mod q)`.**  The genuine `u`
field of the constructed §9 character datum, `u = |Ū| = |U/C_U(H̄)|` (the image of `U` in
`Aut(H̄)`, `mkSection11CharacterData.u`), satisfies `|Ū| ≡ 1 (mod w₁ = q)`.

This is the `U/C_U(H̄)`-quotient of the Frobenius congruence `|U| ≡ 1 (mod q)` (`card_U_modEq_one`):
`W₁` acts fixed-point-freely on `U` (`typeP_uW1_frobenius`) and this descends to the chief-factor
image `Ū` — a homomorphic image of `U` under the `U W₁`-equivariant action map `quotientMulAutHom` —
by the general Frobenius-group image congruence
`IsFrobeniusGroup.card_range_comp_subtype_modEq_one` (Isaacs Cor 6.2 + Lemma 6.1).  Together with the
μ-grid degree `d = |Ū|` (from `caseB_degree_qu`, the μ-grid ↔ §9-family correspondence) this is the
§9 half of `charParam_d_modEq_one`. -/
theorem Hypothesis.mkSection11CharacterData_u_modEq_one [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData data) (hU : data.typeP.U ≠ ⊥) :
    (hyp.mkSection11CharacterData data chief).u ≡ 1 [MOD Nat.card ↥data.typeP.W1] := by
  have hgen := (OddOrder.Peterfalvi.S11.typeP_uW1_frobenius data.typeP hU).card_range_comp_subtype_modEq_one
    (quotientMulAutHom (N := chief.N) chief.N_aInvariant)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at hgen

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (11.8.1), the index identification `u = |U : C|`** (`C = U ⊓ C_G(H)`), under the
(11.7) collapse `H₀ = 1` (i.e. the chief-factor kernel `chief.N = ⊥`).

The genuine `u` field is `u = |Ū| = |range φ|`, where `φ : ↥(U.subgroupOf(U ⊔ W₁)) →* Aut(H̄)`
is the `U`-action on the chief factor `H̄ = ↥H ⧸ chief.N`.  By the first isomorphism theorem
`|range φ| = [dom : ker φ]`.  With `chief.N = ⊥` the quotient `H̄ = ↥H ⧸ ⊥` *is* `↥H`, so `φ` is the
conjugation action of `U ⊔ W₁` on `↥H` (`typeP_conjAction`); an element `v ∈ U` acts trivially iff
it centralizes `H`, i.e. `ker φ ≅ (C = U ⊓ C_G(H))` inside `U`.  Transporting the index along
`↥(U.subgroupOf(U ⊔ W₁)) ≃* ↥U` gives `[dom : ker φ] = C.relIndex U = |U : C|`.

This is the (11.7) `H₀ = 1` half of the (11.8.1) chain `|M'{}^{ab}| = |U : C| = u = d` feeding the
`|𝒮(HC)| = n` count (`card_SHCSet_filter_eq_charParam_n`); the `|M'{}^{ab}| = |U : C|` structural
half is `typePData_card_abelianization_derived_eq_relIndex_C` and `u = d` is `charParam_d_eq_u`. -/
theorem Hypothesis.u_eq_relIndex_C [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData data)
    (hN : chief.N = ⊥) :
    (hyp.mkSection11CharacterData data chief).u
      = (data.typeP.U ⊓ Subgroup.centralizer (data.typeP.H : Set G)).relIndex data.typeP.U := by
  classical
  set L := data.typeP.U ⊔ data.typeP.W1 with hL
  set C := data.typeP.U ⊓ Subgroup.centralizer (data.typeP.H : Set G) with hC
  -- The `U`-action map on `H̄`, restricted to `U` via the inclusion `↥U →* ↥L`.
  set φ := quotientMulAutHom (N := chief.N) chief.N_aInvariant with hφ
  set θ := φ.comp (Subgroup.inclusion (le_sup_left : data.typeP.U ≤ L)) with hθ
  -- (A) `u = |range φ_sub| = |range θ|`: the two restrictions of `φ` (to `U.subgroupOf L` and via
  -- the inclusion from `↥U`) have equal range, since both restriction domains sit as `U` in `L`.
  have hrange : ((φ.comp (data.typeP.U.subgroupOf L).subtype)).range = θ.range := by
    rw [hθ, MonoidHom.range_comp, MonoidHom.range_comp]
    congr 1
    -- `(U.subgroupOf L).subtype.range = (inclusion le_sup_left).range` (both are `U` inside `L`).
    rw [Subgroup.range_subtype, Subgroup.inclusion_range]
  have huθ : (hyp.mkSection11CharacterData data chief).u = Nat.card ↥θ.range := by
    change Nat.card ↥((φ.comp (data.typeP.U.subgroupOf L).subtype)).range = _
    rw [hrange]
  -- (B) `ker θ = C.subgroupOf U`: with `chief.N = ⊥`, `v ∈ U` acts trivially on `H̄ = ↥H` iff `↑v`
  -- centralizes `H`, i.e. `↑v ∈ C`.
  have hker : θ.ker = C.subgroupOf data.typeP.U := by
    ext v
    rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, hC,
      Subgroup.mem_inf]
    constructor
    · intro hv
      refine ⟨v.property, Subgroup.mem_centralizer_iff.mpr (fun g hg => ?_)⟩
      -- `φ (incl v) = 1` ⇒ conjugation by `↑v` fixes every `⟨g, hg⟩ : ↥H`.
      have happ : φ (Subgroup.inclusion (le_sup_left : data.typeP.U ≤ L) v)
          ((⟨g, hg⟩ : ↥data.typeP.H) : ↥data.typeP.H ⧸ chief.N)
          = ((⟨g, hg⟩ : ↥data.typeP.H) : ↥data.typeP.H ⧸ chief.N) := by
        rw [hv]; rfl
      rw [hφ, OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply,
        QuotientGroup.eq, hN] at happ
      have hmem : (typeP_conjAction data.typeP
          (Subgroup.inclusion (le_sup_left : data.typeP.U ≤ L) v)
          ⟨g, hg⟩)⁻¹ * ⟨g, hg⟩ ∈ (⊥ : Subgroup ↥data.typeP.H) := happ
      rw [Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have hconj : (v : G) * g * (v : G)⁻¹ = g := by
        have := Subtype.ext_iff.mp hmem
        rwa [typeP_conjAction_apply, Subgroup.coe_inclusion] at this
      -- `↑v * g * ↑v⁻¹ = g` ⇒ `g * ↑v = ↑v * g`.
      exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
    · rintro ⟨-, hvC⟩
      -- `↑v ∈ C_G(H)` ⇒ `φ (incl v) = 1` (conjugation by `↑v` fixes `↥H`, hence all of `H̄`).
      apply MulEquiv.ext
      intro y
      refine QuotientGroup.induction_on y (fun g => ?_)
      rw [hφ, OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply]
      change ((typeP_conjAction data.typeP
        (Subgroup.inclusion (le_sup_left : data.typeP.U ≤ L) v) g : ↥data.typeP.H)
        : ↥data.typeP.H ⧸ chief.N) = _
      congr 1
      apply Subtype.ext
      rw [typeP_conjAction_apply, Subgroup.coe_inclusion]
      -- `↑v * ↑g * ↑v⁻¹ = ↑g` from `↑v ∈ C_G(H)`.
      have hgH : (g : G) ∈ (data.typeP.H : Set G) := g.property
      have hcomm : (g : G) * (v : G) = (v : G) * (g : G) :=
        Subgroup.mem_centralizer_iff.mp hvC (g : G) hgH
      rw [← hcomm, mul_inv_cancel_right]
  -- (C) `|range θ| = [dom : ker θ] = C.relIndex U`.
  rw [huθ, Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).symm.toEquiv, hker]
  rfl

/-! ## (11.8.1): the μ-columns are the reducible `𝒮(H₀)`-members -/

open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (9.8.b)/(9.9.b), unified degree**: in either Clifford case, every reducible member
of `𝒮(H₀)` has degree `qu`.  Case (a) is `caseA_reducible_induceHU_apply_one_eq_qu`; case (b)
combines the cardinality membership `reducible_mem_sOf_H0C` with the `𝒮(H₀C)` degree
`forall_mem_sOf_H0C_apply_one_eq_qu`.  This is the degree input the (11.8.1) `d = |Ū|`
identification consumes, dichotomy-free for the caller. -/
theorem reducible_mem_sOf_H0_apply_one_eq_qu [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (φ : ClassFunction ↥M ℂ) (hφ : φ ∈ sOf data chief.H0)
    (hred : ¬ IsIrreducibleCharacter φ) :
    φ (1 : ↥M) = ((data.q * chars.u : ℕ) : ℂ) := by
  rcases clifford_dichotomy hG chars with ⟨⟨caseA⟩⟩ | ⟨⟨caseB⟩⟩
  · exact caseA_reducible_induceHU_apply_one_eq_qu caseA hG φ hφ hred
  · refine forall_mem_sOf_H0C_apply_one_eq_qu hG chars caseB φ ?_
    rw [Section11CharacterData.SOf_eq]
    exact reducible_mem_sOf_H0C hG chars φ hφ hred

open scoped FiniteInduce in
open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (11.8.1), the μ-columns are the reducible `𝒮(H₀)`-members** (Coq `PFsection11`
`memSred`): for `k ≠ 0`, the §10 column sum `μ_k = ∑_i μ_{ik}` lies in the §9 family `𝒮(H₀)` and is
reducible.

By counting: the reducible `𝒮(H₀)`-members number `p − 1` (`reducible_count_sOf_H0`, proven); each
one is a §6 column induction `Ind_{M'}^M χ_j` by the Clifford characterization
(`induce_not_isIrreducible_iff`), with the trivial column excluded by the `𝒳`-kernel condition
`H ⊄ Ker` (`chiRestrict_one_eq_trivial`) — hence lies among the `w₂ − 1 = p − 1` pairwise-distinct
column sums `μ_k`, `k ≠ 0` (`chief.typeIII_IV_p_eq_W2`).  Equal finite cardinalities force the two
sets equal (`Set.eq_of_subset_of_ncard_le`), so *every* `μ_k` (`k ≠ 0`) is a reducible
`𝒮(H₀)`-member.  This sharpens the `inducedFamily`-membership
(`muGrid_column_sum_mem_inducedFamily`) to the `𝒮(H₀)`-membership that the (9.8)/(9.9) degree
analysis (`reducible_mem_sOf_H0_apply_one_eq_qu`) consumes. -/
theorem Hypothesis.muGrid_column_sum_mem_sOf_H0_and_reducible [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    (k : Fin hyp.w2) (hk : k ≠ 0) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k)
        ∈ sOf (hyp.toTypesIIIIIIVSetup htype hnt) chief.H0 ∧
      ¬ IsIrreducibleCharacter (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hG.odd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Fintype ↥h.K := Fintype.ofFinite _
  letI : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- (4.5.a): the column sum at `j` is the induction of the column character `χ_j`
  have hFk : ∀ j : Fin hyp.w2, (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      = ClassFunction.induce h.K
          ((h.chiRestrict (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)))
            : ClassFunction ↥h.K ℂ) := by
    intro j
    rw [h.coe_chiRestrict, h.induce_restrict_certainType_eq, ← Equiv.sum_comp (finCongr hcardW1.symm)
      (fun i' => ((h.columnFamily
        (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu i' : ClassFunction ↥M ℂ))]
    exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)
  -- every column sum induces reducibly ((4.5.b))
  have hredF : ∀ j : Fin hyp.w2,
      ¬ IsIrreducibleCharacter (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) := by
    intro j
    rw [hFk j]
    exact h.induce_chiRestrict_not_isIrreducible _
  -- the column sums are pairwise distinct
  have hFinj : Function.Injective
      (fun j : Fin hyp.w2 => ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) := by
    intro j j' heq
    have heq' : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
        = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j' := heq
    rw [hFk j, hFk j'] at heq'
    have h1 := h.induce_injective_on_reducible
      (h.induce_chiRestrict_not_isIrreducible _) heq'
    have h2 := h.chiRestrict_injective h1
    have h3 := (finCardEquivCharacterGroup _).injective h2
    exact (finCongr hcardW2sub.symm).injective h3
  -- `|A| = p − 1 = w₂ − 1` (the §9 count and the (9.6) `p = |W₂|`)
  have hAcard : {φ ∈ sOf (hyp.toTypesIIIIIIVSetup htype hnt) chief.H0 |
      ¬ IsIrreducibleCharacter φ}.ncard = hyp.w2 - 1 := by
    rw [reducible_count_sOf_H0 hG chief, ← chief.typeIII_IV_p_eq_W2 htype]
    rfl
  -- `|B| = w₂ − 1` (distinct column sums over `k ≠ 0`)
  have hBcard : (((fun j : Fin hyp.w2 => ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)) ''
      {j : Fin hyp.w2 | j ≠ 0}).ncard = hyp.w2 - 1 := by
    rw [Set.ncard_image_of_injective _ hFinj,
      show {j : Fin hyp.w2 | j ≠ 0} = (Set.univ \ {0} : Set (Fin hyp.w2)) by ext j; simp,
      Set.ncard_sdiff (Set.subset_univ _), Set.ncard_univ, Set.ncard_singleton]
    simp [Nat.card_eq_fintype_card]
  -- `A ⊆ B`: a reducible `𝒮(H₀)`-member is a nonzero column sum
  have hAB : {φ ∈ sOf (hyp.toTypesIIIIIIVSetup htype hnt) chief.H0 |
      ¬ IsIrreducibleCharacter φ}
      ⊆ ((fun j : Fin hyp.w2 => ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)) ''
        {j : Fin hyp.w2 | j ≠ 0} := by
    rintro φ ⟨hφS, hφred⟩
    obtain ⟨χ, hχxi, rfl⟩ := hφS
    have hKeq : huSub (hyp.toTypesIIIIIIVSetup htype hnt) = (derivedInG M).subgroupOf M :=
      huSub_eq_derivedInG_subgroupOf _
    -- transport the source along `HU = M' = K`
    have hχKirr : IsIrreducibleCharacter
        (ClassFunction.compHom (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom
          (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ)) :=
      IsIrreducibleCharacter.compHom_of_surjective
        (MulEquiv.surjective _) χ.isIrreducible
    have hind : ClassFunction.induce ((derivedInG M).subgroupOf M)
        (ClassFunction.compHom (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom
          (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ))
        = induceHU (hyp.toTypesIIIIIIVSetup htype hnt)
            (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ) :=
      induce_compHom_subgroupCongr hKeq.symm _
    -- the reducible transported source is a §6 column `χ_j`
    obtain ⟨χ₂', hχ₂'⟩ := (h.induce_not_isIrreducible_iff ⟨_, hχKirr⟩).mp (by
      show ¬ IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
        (ClassFunction.compHom (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom
          (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ)))
      rw [hind]
      exact hφred)
    -- the trivial column is excluded by the `𝒳`-kernel condition `H ⊄ Ker χ`
    have hχ₂'ne : χ₂' ≠ 1 := by
      rintro rfl
      rw [h.chiRestrict_one_eq_trivial] at hχ₂'
      refine hχxi.1 ?_
      have hval : ∀ y : ↥((derivedInG M).subgroupOf M),
          (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ)
            ((MulEquiv.subgroupCongr hKeq.symm) y) = 1 := by
        intro y
        have hcoe := congrArg
          (fun c : IrreducibleCharacter ↥h.K => (c : ClassFunction ↥h.K ℂ) y) hχ₂'
        simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
          ClassFunction.compHom_apply] using hcoe.symm
      intro x _hx
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def]
      have hx1 := hval ((MulEquiv.subgroupCongr hKeq.symm).symm x)
      have hone := hval ((MulEquiv.subgroupCongr hKeq.symm).symm 1)
      rw [MulEquiv.apply_symm_apply] at hx1 hone
      rw [hx1, hone]
    -- identify the column index `k' ≠ 0` and conclude `φ = μ_{k'}`
    refine ⟨finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂'), ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      intro h0
      apply hχ₂'ne
      have hs0 : (finCardEquivCharacterGroup
          ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))).symm χ₂' = 0 := by
        have := congrArg (finCongr hcardW2sub.symm) h0
        simpa using this
      calc χ₂' = finCardEquivCharacterGroup _
            ((finCardEquivCharacterGroup _).symm χ₂') := (Equiv.apply_symm_apply _ _).symm
        _ = finCardEquivCharacterGroup _ 0 := by rw [hs0]
        _ = 1 := finCardEquivCharacterGroup_zero _
    · show (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i
          (finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂')))
        = induceHU (hyp.toTypesIIIIIIVSetup htype hnt)
            (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ)
      rw [hFk, show finCongr hcardW2sub.symm
          (finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂'))
          = (finCardEquivCharacterGroup _).symm χ₂' from by simp,
        Equiv.apply_symm_apply, hχ₂']
      exact hind
  -- equal counts force `A = B`; conclude for the given `k`
  have hBfin : (((fun j : Fin hyp.w2 => ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)) ''
      {j : Fin hyp.w2 | j ≠ 0}).Finite :=
    (Set.toFinite _).image _
  have hAeqB := Set.eq_of_subset_of_ncard_le hAB (le_of_eq (hBcard.trans hAcard.symm)) hBfin
  have hmemB : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k)
      ∈ ((fun j : Fin hyp.w2 => ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)) ''
        {j : Fin hyp.w2 | j ≠ 0} := ⟨k, hk, rfl⟩
  rw [← hAeqB] at hmemB
  exact ⟨hmemB.1, hmemB.2⟩

open scoped FiniteInduce in
open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (9.8.a-b), reducible-member classification**: every *reducible* member of
`𝒮(H₀)` is a nonzero μ-grid column sum `μ_k = ∑_i μ_{ik}` (`k ≠ 0`).

Public extraction of the `A ⊆ B` step inside `muGrid_column_sum_mem_sOf_H0_and_reducible`
(the reducible transported source is a §6 column `χ_j` by (4.5.b) `induce_not_isIrreducible_iff`,
the trivial column being excluded by the `𝒳`-kernel condition); shared preamble duplicated.
This is the ψ-column identification the (5.2.d) reducible-break datum consumes (issue 2022). -/
theorem Hypothesis.reducible_mem_sOf_H0_eq_muGrid_columnSum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    {φ : ClassFunction ↥M ℂ}
    (hφS : φ ∈ sOf (hyp.toTypesIIIIIIVSetup htype hnt) chief.H0)
    (hφred : ¬ IsIrreducibleCharacter φ) :
    ∃ k : Fin hyp.w2, k ≠ 0 ∧ φ = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hG.odd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Fintype ↥h.K := Fintype.ofFinite _
  letI : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hFk : ∀ j : Fin hyp.w2, (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      = ClassFunction.induce h.K
          ((h.chiRestrict (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)))
            : ClassFunction ↥h.K ℂ) := by
    intro j
    rw [h.coe_chiRestrict, h.induce_restrict_certainType_eq,
      ← Equiv.sum_comp (finCongr hcardW1.symm)
      (fun i' => ((h.columnFamily
        (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu i'
          : ClassFunction ↥M ℂ))]
    exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)
  obtain ⟨χ, hχxi, rfl⟩ := hφS
  have hKeq : huSub (hyp.toTypesIIIIIIVSetup htype hnt) = (derivedInG M).subgroupOf M :=
    huSub_eq_derivedInG_subgroupOf _
  have hχKirr : IsIrreducibleCharacter
      (ClassFunction.compHom (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom
        (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ)) :=
    IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.surjective _) χ.isIrreducible
  have hind : ClassFunction.induce ((derivedInG M).subgroupOf M)
      (ClassFunction.compHom (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom
        (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ))
      = induceHU (hyp.toTypesIIIIIIVSetup htype hnt)
          (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ) :=
    induce_compHom_subgroupCongr hKeq.symm _
  obtain ⟨χ₂', hχ₂'⟩ := (h.induce_not_isIrreducible_iff ⟨_, hχKirr⟩).mp (by
    show ¬ IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
      (ClassFunction.compHom (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom
        (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ)))
    rw [hind]
    exact hφred)
  have hχ₂'ne : χ₂' ≠ 1 := by
    rintro rfl
    rw [h.chiRestrict_one_eq_trivial] at hχ₂'
    refine hχxi.1 ?_
    have hval : ∀ y : ↥((derivedInG M).subgroupOf M),
        (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ)
          ((MulEquiv.subgroupCongr hKeq.symm) y) = 1 := by
      intro y
      have hcoe := congrArg
        (fun c : IrreducibleCharacter ↥h.K => (c : ClassFunction ↥h.K ℂ) y) hχ₂'
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        ClassFunction.compHom_apply] using hcoe.symm
    intro x _hx
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def]
    have hx1 := hval ((MulEquiv.subgroupCongr hKeq.symm).symm x)
    have hone := hval ((MulEquiv.subgroupCongr hKeq.symm).symm 1)
    rw [MulEquiv.apply_symm_apply] at hx1 hone
    rw [hx1, hone]
  refine ⟨finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂'), ?_, ?_⟩
  · intro h0
    apply hχ₂'ne
    have hs0 : (finCardEquivCharacterGroup
        ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))).symm χ₂' = 0 := by
      have := congrArg (finCongr hcardW2sub.symm) h0
      simpa using this
    calc χ₂' = finCardEquivCharacterGroup _
          ((finCardEquivCharacterGroup _).symm χ₂') := (Equiv.apply_symm_apply _ _).symm
      _ = finCardEquivCharacterGroup _ 0 := by rw [hs0]
      _ = 1 := finCardEquivCharacterGroup_zero _
  · rw [hFk, show finCongr hcardW2sub.symm
        (finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂'))
        = (finCardEquivCharacterGroup _).symm χ₂' from by simp,
      Equiv.apply_symm_apply, hχ₂']
    exact hind.symm

open OddOrder.Peterfalvi.S11 in
/-- **Reducible count of the full family** (`reducible_count_sOf_K` at `K = ⊥`): the full §9
family `𝒮 = 𝒮(⊥)` has exactly `p − 1` reducible members. -/
theorem reducible_count_sOf_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (htype : IsTypeIII M ∨ IsTypeIV M)
    (chief : ChiefFactorData data) :
    {φ ∈ sOf data (⊥ : Subgroup G) | ¬ IsIrreducibleCharacter φ}.ncard = chief.p - 1 := by
  classical
  haveI : ((⊥ : Subgroup G).subgroupOf M).Normal := by
    rw [Subgroup.bot_subgroupOf]; infer_instance
  have hW2leM : data.W2 ≤ M := (data.typeP.W2_le.trans inf_le_left).trans (H_le_M data)
  have hcardW2tr : Nat.card ↥(data.W2.subgroupOf M) = chief.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2leM).toEquiv]
    exact chief.typeIII_IV_p_eq_W2 htype
  have hmkinj : Function.Injective
      (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf M)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', Subgroup.bot_subgroupOf]
  refine reducible_count_sOf_K hG chief ⊥ (by rw [Subgroup.bot_subgroupOf]; exact bot_le)
    (by rw [Subgroup.bot_subgroupOf, inf_bot_eq]) ?_ ?_
  · intro hle
    rw [Subgroup.bot_subgroupOf, le_bot_iff] at hle
    have h1 : Nat.card ↥(data.W2.subgroupOf M) = 1 := by
      rw [hle, Nat.card_eq_one_iff_unique]
      exact ⟨inferInstance, ⟨1, rfl⟩⟩
    rw [hcardW2tr] at h1
    exact chief.p_prime.one_lt.ne' h1
  · rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _ hmkinj).symm.toEquiv]
    exact hcardW2tr

open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (9.8.a), membership**: every *reducible* member of the full family
`𝒮 = 𝒮(⊥)` already lies in `𝒮(H₀)`.

Cardinality mirror of `reducible_mem_sOf_H0C`: `𝒮(H₀) ⊆ 𝒮(⊥)` (`sOf_antitone`), the reducibles
of both number `p − 1` (`reducible_count_sOf_K` at `K = ⊥` — the trace is trivially normal, the
`W`-conditions degenerate, and `|W̄₂| = |W₂| = p` by (9.6) — resp. `reducible_count_sOf_H0`), so
the two reducible sets coincide. -/
theorem reducible_mem_sOf_bot_mem_sOf_H0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (htype : IsTypeIII M ∨ IsTypeIV M)
    (chief : ChiefFactorData data) :
    ∀ φ ∈ sOf data (⊥ : Subgroup G), ¬ IsIrreducibleCharacter φ →
      φ ∈ sOf data chief.H0 := by
  classical
  intro φ hφ hred
  have hBA : {ψ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter ψ}
      ⊆ {ψ ∈ sOf data (⊥ : Subgroup G) | ¬ IsIrreducibleCharacter ψ} := by
    rintro ψ ⟨hψS, hψr⟩
    exact ⟨sOf_antitone data bot_le hψS, hψr⟩
  have hAfin : {ψ ∈ sOf data (⊥ : Subgroup G) | ¬ IsIrreducibleCharacter ψ}.Finite := by
    refine Set.finite_of_ncard_ne_zero ?_
    rw [reducible_count_sOf_bot hG htype chief]
    exact Nat.sub_ne_zero_of_lt chief.p_prime.one_lt
  have hAB : {ψ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter ψ}
      = {ψ ∈ sOf data (⊥ : Subgroup G) | ¬ IsIrreducibleCharacter ψ} :=
    Set.eq_of_subset_of_ncard_le hBA (by
      rw [reducible_count_sOf_bot hG htype chief, reducible_count_sOf_H0 hG chief]) hAfin
  have hmem : φ ∈ {ψ ∈ sOf data (⊥ : Subgroup G) | ¬ IsIrreducibleCharacter ψ} := ⟨hφ, hred⟩
  rw [← hAB] at hmem
  exact hmem.1

open scoped FiniteInduce in
open OddOrder.Peterfalvi.S11 in
/-- **(9.8) classification at the bridge family**: a *reducible* member of the general
kernel-filter family `inducedKernelFamily M'-trace B` (any `B`) is a nonzero μ-grid column sum.

Unlike the `𝒮(H₀)`-route, the trivial column is excluded directly by the family's `θ ≠ 1`
condition (`chiRestrict_one_eq_trivial`), so no `𝒳`-kernel condition is needed — this covers
the h56 break members (issue 2022, the U-side case being impossible for *reducible* members
precisely because the trivial column is the only `H`-trivial one among the `χ_j`). -/
theorem Hypothesis.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    {B : Subgroup ↥M} {ψ : ClassFunction ↥M ℂ}
    (hψ : ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) B)
    (hred : ¬ IsIrreducibleCharacter ψ) :
    ∃ k : Fin hyp.w2, k ≠ 0 ∧ ψ = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, hθne, hθker, rfl⟩ := hψ
  let h := (hyp.toCertainTypeHypothesis hG hG.odd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Fintype ↥h.K := Fintype.ofFinite _
  letI : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hFk : ∀ j : Fin hyp.w2, (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      = ClassFunction.induce h.K
          ((h.chiRestrict (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)))
            : ClassFunction ↥h.K ℂ) := by
    intro j
    rw [h.coe_chiRestrict, h.induce_restrict_certainType_eq,
      ← Equiv.sum_comp (finCongr hcardW1.symm)
      (fun i' => ((h.columnFamily
        (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu i'
          : ClassFunction ↥M ℂ))]
    exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)
  -- the reducible source is a §6 column
  obtain ⟨χ₂', hχ₂'⟩ := (h.induce_not_isIrreducible_iff θ).mp hred
  have hχ₂'ne : χ₂' ≠ 1 := by
    rintro rfl
    rw [h.chiRestrict_one_eq_trivial] at hχ₂'
    exact hθne hχ₂'.symm
  refine ⟨finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂'), ?_, ?_⟩
  · intro h0
    apply hχ₂'ne
    have hs0 : (finCardEquivCharacterGroup
        ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))).symm χ₂' = 0 := by
      have := congrArg (finCongr hcardW2sub.symm) h0
      simpa using this
    calc χ₂' = finCardEquivCharacterGroup _
          ((finCardEquivCharacterGroup _).symm χ₂') := (Equiv.apply_symm_apply _ _).symm
      _ = finCardEquivCharacterGroup _ 0 := by rw [hs0]
      _ = 1 := finCardEquivCharacterGroup_zero _
  · rw [hFk, show finCongr hcardW2sub.symm
        (finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂'))
        = (finCardEquivCharacterGroup _).symm χ₂' from by simp,
      Equiv.apply_symm_apply, hχ₂']
    exact rfl

/-! ## (11.8.1): `d = u`, `d ≡ 1 (mod q)` and `δ = 1` -/

open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (11.8.1), the degree identification `d = u = |Ū|`** (Coq `Dd`).  The column sum
`μ_1 = ∑_i μ_{i1}` is a reducible member of the §9 family `𝒮(H₀)`
(`muGrid_column_sum_mem_sOf_H0_and_reducible`), so it has degree `q·u = q·|Ū|` by (9.8.b)/(9.9.b)
(`reducible_mem_sOf_H0_apply_one_eq_qu`, both Clifford cases); its degree is also `w₁·d` by the
(10.3) grid (`degree_independent`, via `hmu`).  Cancelling `q = w₁` gives `d = |Ū|`.  This is
the `d`-identification consumed by the residue `d ≡ 1 (mod q)` (`charParam_d_modEq_one`) and by
the `|S(HC)| = n = (d−1)/q` count. -/
theorem Hypothesis.charParam_d_eq_u [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt)) :
    params.d = (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u := by
  haveI := hyp.finiteG
  classical
  -- the nonzero column `k = 1` (`w₂ ≥ 3`: `w₂` is an odd prime)
  have hw2odd : Odd hyp.w2 := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W2)
  have hw2_3 : 3 ≤ hyp.w2 := by
    have h2 := params.w2_prime.two_le
    obtain ⟨m, hm⟩ := hw2odd
    omega
  set k : Fin hyp.w2 := ⟨1, by omega⟩ with hk_def
  have hk0 : k ≠ 0 := by
    intro h0
    have := congrArg Fin.val h0
    simp [hk_def] at this
  obtain ⟨hmem, hred⟩ :=
    hyp.muGrid_column_sum_mem_sOf_H0_and_reducible hG htype hnt chief k hk0
  -- degree `q·u` from the §9 counts (both Clifford cases)
  have hqu := reducible_mem_sOf_H0_apply_one_eq_qu hG
    (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief) _ hmem hred
  -- degree `w₁·d` from the (10.3) grid
  have hdeg : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) (1 : ↥M)
      = (hyp.w1 : ℂ) * (params.d : ℂ) := by
    have hcoe : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) (1 : ↥M)
        = ∑ i : Fin hyp.w1, (hyp.muGrid hG hG.odd i k) (1 : ↥M) := by
      rw [show ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k : ClassFunction ↥M ℂ) : ↥M → ℂ)
          = ∑ i : Fin hyp.w1, ((hyp.muGrid hG hG.odd i k : ClassFunction ↥M ℂ) : ↥M → ℂ) from
        AddSubmonoidClass.coe_finsetSum _ _]
      rw [Finset.sum_apply]
    have hterm : ∀ i : Fin hyp.w1, (hyp.muGrid hG hG.odd i k) (1 : ↥M) = (params.d : ℂ) := by
      intro i
      rw [← hmu]
      exact params.degree_independent i k hk0
    calc (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) (1 : ↥M)
        = ∑ i : Fin hyp.w1, (hyp.muGrid hG hG.odd i k) (1 : ↥M) := hcoe
      _ = ∑ _i : Fin hyp.w1, (params.d : ℂ) := Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (hyp.w1 : ℂ) * (params.d : ℂ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- cancel `q = w₁`
  have hq : (hyp.toTypesIIIIIIVSetup htype hnt).q = hyp.w1 := rfl
  have hqu' : (hyp.w1 : ℂ) * (params.d : ℂ)
      = (((hyp.toTypesIIIIIIVSetup htype hnt).q
          * (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u : ℕ) : ℂ) := by
    rw [← hdeg]; exact hqu
  rw [hq] at hqu'
  push_cast at hqu'
  have hw1ne : (hyp.w1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  exact_mod_cast mul_left_cancel₀ hw1ne hqu'

open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (11.8.1), the residue `d ≡ 1 (mod q)`** (§9 count, named obligation).  `d = |Ū|`
(`charParam_d_eq_u`), and `|Ū| ≡ 1 (mod q)` is the chief-factor image of the Frobenius congruence
(`mkSection11CharacterData_u_modEq_one`). -/
theorem Hypothesis.charParam_d_modEq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd) :
    params.d ≡ 1 [MOD hyp.w1] := by
  haveI := hyp.finiteG
  classical
  have hnt : TypePNontrivialCore M hyp.typeP :=
    typePNontrivialCore_of_isTypeIIIorIV htype hyp.typeP
  obtain ⟨chief, -⟩ := exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetup htype hnt)
  rw [hyp.charParam_d_eq_u hG htype params hmu hnt chief]
  exact hyp.mkSection11CharacterData_u_modEq_one (hyp.toTypesIIIIIIVSetup htype hnt) chief hnt.1

open scoped Classical in
/-- **Integral Bessel bound over an orthonormal `ℤIrr` triple**: if `T ∈ ℤ[Irr G]` has
`⟨T,T⟩ = 2` and `ω₁, ω₂, ω₃` are pairwise-orthogonal orthonormal `ℤIrr` elements with equal
`T`-coefficients, that coefficient is `0` (`3c² ≤ 2` in `ℤ`). -/
theorem inner_eq_zero_of_three_equal_coeff [Fintype G] [Invertible (Nat.card G : ℂ)]
    {T ω₁ ω₂ ω₃ : ClassFunction G ℂ} (hT : T ∈ ZIrr G) (hT2 : ClassFunction.inner T T = 2)
    (hω : ∀ ω ∈ ({ω₁, ω₂, ω₃} : Finset (ClassFunction G ℂ)), ω ∈ ZIrr G)
    (horth : ∀ α ∈ ({ω₁, ω₂, ω₃} : Finset (ClassFunction G ℂ)),
      ∀ β ∈ ({ω₁, ω₂, ω₃} : Finset (ClassFunction G ℂ)),
      ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (h12 : ω₁ ≠ ω₂) (h13 : ω₁ ≠ ω₃) (h23 : ω₂ ≠ ω₃)
    (hequal : ClassFunction.inner T ω₁ = ClassFunction.inner T ω₂ ∧
      ClassFunction.inner T ω₂ = ClassFunction.inner T ω₃) :
    ClassFunction.inner T ω₁ = 0 := by
  classical
  obtain ⟨c, Y, hc, hdecomp, hY⟩ :=
    OddOrder.RepresentationTheory.ClassFunction.exists_intProjection_of_orthonormal_ZIrr hT hω horth
  set R : Finset (ClassFunction G ℂ) := {ω₁, ω₂, ω₃} with hR
  -- expand `⟨T,T⟩ = ∑ |c|² + ⟨Y,Y⟩`
  have hYS : ClassFunction.inner Y (∑ α ∈ R, (c α : ℂ) • α) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    refine Finset.sum_eq_zero fun α hα => ?_
    rw [ClassFunction.inner_smul_right, hY α hα, mul_zero]
  have hSY : ClassFunction.inner (∑ α ∈ R, (c α : ℂ) • α) Y = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hYS, star_zero]
  have hSS : ClassFunction.inner (∑ α ∈ R, (c α : ℂ) • α) (∑ α ∈ R, (c α : ℂ) • α)
      = ∑ α ∈ R, (c α : ℂ) * star (c α : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_single α]
    · rw [ClassFunction.inner_smul_right, horth α hα α hα, if_pos rfl, mul_one]
    · intro β hβ hne
      rw [ClassFunction.inner_smul_right, horth α hα β hβ,
        if_neg (fun h => hne h.symm)]
      ring
    · intro habs
      exact absurd hα habs
  have hexp : ClassFunction.inner T T
      = (∑ α ∈ R, (c α : ℂ) * star (c α : ℂ)) + ClassFunction.inner Y Y := by
    conv_lhs => rw [hdecomp]
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, hSS, hYS, hSY]
    ring
  have hmem1 : ω₁ ∈ R := by simp [hR]
  have hmem2 : ω₂ ∈ R := by simp [hR]
  have hmem3 : ω₃ ∈ R := by simp [hR]
  have hc1 := hc ω₁ hmem1
  have hc2 := hc ω₂ hmem2
  have hc3 := hc ω₃ hmem3
  have hceq12 : c ω₁ = c ω₂ := by
    have h := hequal.1
    rw [hc1, hc2] at h
    exact_mod_cast h
  have hceq23 : c ω₂ = c ω₃ := by
    have h := hequal.2
    rw [hc2, hc3] at h
    exact_mod_cast h
  have hterm : ∀ α, (c α : ℂ) * star (c α : ℂ) = ((c α ^ 2 : ℤ) : ℂ) := fun α => by
    rw [star_intCast]
    push_cast
    ring
  have hsum3 : (∑ α ∈ R, (c α : ℂ) * star (c α : ℂ))
      = ((3 * (c ω₁) ^ 2 : ℤ) : ℂ) := by
    rw [hR, Finset.sum_insert (by simp [h12, h13]),
      Finset.sum_insert (by simp [h23]), Finset.sum_singleton,
      hterm, hterm, hterm, ← hceq12, ← (hceq12.trans hceq23)]
    push_cast
    ring
  have hYnn := OddOrder.RepresentationTheory.inner_self_re_nonneg Y
  have h := congrArg Complex.re hexp
  rw [hT2, hsum3, Complex.add_re, Complex.intCast_re] at h
  have h2c : (2 : ℂ).re = 2 := by norm_num
  rw [h2c] at h
  have hineq : ((3 * (c ω₁) ^ 2 : ℤ) : ℝ) ≤ 2 := by linarith
  have hc0 : c ω₁ = 0 := by
    by_contra hne
    have h1 : (1 : ℤ) ≤ (c ω₁) ^ 2 := by
      rcases lt_or_gt_of_ne hne with h | h <;> nlinarith
    have hint : (3 * (c ω₁) ^ 2 : ℤ) ≤ 2 := by exact_mod_cast hineq
    nlinarith
  rw [hc1, hc0]
  norm_num

open scoped FiniteInduce in
open OddOrder.Peterfalvi.S11 in
/-- **Irreducible family members are orthogonal to every μ-grid entry** (degree separation
mod `q`): an irreducible member has degree `w₁·θ(1) ≡ 0 (mod w₁)` while the grid degree is
`d ≡ 1 (mod w₁)` ((11.8.1), `charParam_d_modEq_one`), so they are distinct irreducibles.
This is the (5.2.e)-hypothesis feeder for member-vs-column `R`-orthogonality (issue 2022). -/
theorem Hypothesis.muGrid_inner_irr_member_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd)
    {X : Subgroup ↥M} {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) X)
    (hχirr : IsIrreducibleCharacter χ)
    (i : Fin hyp.w1) {k : Fin hyp.w2} (hk0 : k ≠ 0) :
    ClassFunction.inner (hyp.muGrid hG hG.odd i k) χ = 0 := by
  haveI := hyp.finiteG
  refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hG.odd i k hχirr ?_
  obtain ⟨θ, -, -, hχ1⟩ := OddOrder.Peterfalvi.S08.inducedKernelFamily_apply_one hχ
  have hd : hyp.muGrid hG hG.odd i k 1 = (params.d : ℂ) := by
    rw [← hmu]
    exact params.degree_independent i k hk0
  have hdmod := hyp.charParam_d_modEq_one hG htype params hmu
  have hidx : ((derivedInG M).subgroupOf M).index = hyp.w1 :=
    hyp.typeP.card_W1_eq_derived_index.symm
  obtain ⟨nθ, -, hnθ, -⟩ := θ.isIrreducible.exists_natDegree_charValue_one_dvd_card
  rw [hd, hχ1, hidx, hnθ]
  intro he
  have hnat : params.d = hyp.w1 * nθ := by exact_mod_cast he
  have hnt : TypePNontrivialCore M hyp.typeP :=
    typePNontrivialCore_of_isTypeIIIorIV htype hyp.typeP
  have hw1 : 2 ≤ hyp.w1 := by
    have hprime : (Nat.card ↥hyp.typeP.W1).Prime := hnt.2.1
    have heq : Nat.card ↥hyp.typeP.W1 = hyp.w1 := rfl
    have := hprime.two_le
    omega
  have h0 : params.d % hyp.w1 = 0 := by
    rw [hnat]
    exact Nat.mul_mod_right _ _
  have h1 : params.d % hyp.w1 = 1 % hyp.w1 := hdmod
  rw [Nat.one_mod_eq_one.mpr (by omega)] at h1
  omega

/-- **Peterfalvi (11.8.1), `δ = 1`**.  The (10.3) column sign `δ ∈ {±1}` equals `1`.  From the index
relation `n·w₁ = d − δ` (`n_formula`), `w₁ ∣ d − δ`; from the (11.8.1) residue `d ≡ 1 (mod w₁)`
(`charParam_d_modEq_one`), `w₁ ∣ 1 − d`; adding, `w₁ ∣ 1 − δ`.  With `δ = −1` this forces `w₁ ∣ 2`,
impossible for the odd `w₁ = |W₁| ≥ 3`.  Hence `δ = 1`.  (This is the pure arithmetic of (11.8.1);
the §9/Frobenius content is isolated in `charParam_d_modEq_one`.) -/
theorem Hypothesis.charParam_delta_eq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1) : params.delta = 1 := by
  have hw1odd : Odd hyp.w1 := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W1)
  have hw1gt : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hw1 : 3 ≤ hyp.w1 := by obtain ⟨k, hk⟩ := hw1odd; omega
  have hddelta : (hyp.w1 : ℤ) ∣ (params.d : ℤ) - params.delta :=
    ⟨params.n, by rw [mul_comm]; exact params.n_formula.symm⟩
  have hd1 : (hyp.w1 : ℤ) ∣ (1 : ℤ) - (params.d : ℤ) :=
    Nat.modEq_iff_dvd.mp (hyp.charParam_d_modEq_one hG htype params hmu)
  have hkey : (hyp.w1 : ℤ) ∣ (1 : ℤ) - params.delta := by
    have hcomb : (1 : ℤ) - params.delta = ((params.d : ℤ) - params.delta) + (1 - (params.d : ℤ)) := by
      ring
    rw [hcomb]; exact dvd_add hddelta hd1
  rcases hδpm with h1 | hm1
  · exact h1
  · exfalso
    rw [hm1] at hkey
    have h2 : (hyp.w1 : ℤ) ∣ 2 := by simpa using hkey
    have hle := Int.le_of_dvd (by norm_num) h2
    have hw1Z : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast hw1
    omega

/-! ## (11.8.1) `|𝒮(HC)| = n`: linear sources and the orbit count -/

/-- `M' = (derivedInG M).subgroupOf M` is normal in `↥M` (it is `commutator ↥M` under
`comap_map_eq_self`). -/
instance {M : Subgroup G} : ((derivedInG M).subgroupOf M).Normal := by
  rw [derivedInG, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  infer_instance

/-- **Nonidentity `↥K`-elements commuting with a nonidentity `W₁`-element lie in
`commutator ↥K`** — the `hfix` translation of Peterfalvi (8.4.d): such an element lands in
`M' ⊓ C_G(w) = W₂` (`TypePData.centralizer_W1`) and `W₂ ≤ M''` (`W2_le`), and `M''` pulls back
to `commutator ↥K` across `↥K ≃* ↥M'`. -/
theorem Hypothesis.mem_commutator_of_commute_W1 [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    {v : ↥M} (hv : v ∈ hyp.W1.subgroupOf M) (hvne : v ≠ 1)
    {x : ↥((derivedInG M).subgroupOf M)}
    (hcomm : (v : ↥M) * (x : ↥M) = (x : ↥M) * (v : ↥M)) :
    x ∈ commutator ↥((derivedInG M).subgroupOf M) := by
  -- `(x:G)` commutes with `(v:G)`, so lies in `M' ⊓ C_G(v) = W₂ ≤ M''`.
  have hvG : ((v : ↥M) : G) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp hv
  have hvGne : ((v : ↥M) : G) ≠ 1 := fun h => hvne (by ext; exact h)
  have hxG : ((x : ↥M) : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp x.2
  have hxcen : ((x : ↥M) : G) ∈ Subgroup.centralizer ({((v : ↥M) : G)} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have := congrArg (fun m : ↥M => (m : G)) hcomm
    simpa using this.symm
  have hxW2 : ((x : ↥M) : G) ∈ hyp.typeP.W2 := by
    rw [← hyp.typeP.centralizer_W1 _ hvG hvGne]
    exact ⟨hxG, hxcen⟩
  have hxM'' : ((x : ↥M) : G) ∈ secondDerivedInAmbient M := (hyp.typeP.W2_le hxW2).2
  -- pull `M'' = derivedInG M'` back to `commutator ↥K` across `e : ↥K ≃* ↥M'`.
  rw [secondDerivedInAmbient, derivedInG] at hxM''
  obtain ⟨c, hc, hcx⟩ := hxM''
  set e := Subgroup.subgroupOfEquivOfLe
    (Subgroup.map_subtype_le (commutator ↥M) : derivedInG M ≤ M) with he
  have hex : e x = c := by
    ext
    exact hcx.symm
  have hcmem : e.symm c ∈ commutator ↥((derivedInG M).subgroupOf M) := by
    have hmap : (commutator ↥(derivedInG M)).map e.symm.toMonoidHom
        ≤ commutator ↥((derivedInG M).subgroupOf M) := by
      have h1 : (commutator ↥(derivedInG M)).map e.symm.toMonoidHom
          = ⁅(⊤ : Subgroup ↥(derivedInG M)).map e.symm.toMonoidHom,
              (⊤ : Subgroup ↥(derivedInG M)).map e.symm.toMonoidHom⁆ :=
        Subgroup.map_commutator ⊤ ⊤ _
      rw [h1]
      exact Subgroup.commutator_mono le_top le_top
    exact hmap (Subgroup.mem_map_of_mem _ hc)
  rw [← hex, MulEquiv.symm_apply_apply] at hcmem
  exact hcmem

/-- **A nontrivial linear character of `M'` has inertia group exactly `M'`** — Peterfalvi's
(8.4.d) at the character level, the heart of the h56 anchor.

If some `w ∈ M ∖ M'` fixed `θ`, its `W₁`-component `v ≠ 1` (through `M = M' ⋊ W₁`,
`M_complement`; the `M'`-component is absorbed by `ClassFunction.subgroup_le_inertia`) would fix
`θ` too.  The
`W₁`-conjugation action on `M'/M''` is fixed-point-free (`quotient_of_fixedPoints_le`, from
`(|W₁|, |M'|) = 1` (`coprime_card_W1_derived`) and `C_{M'}(v) = W₂ ≤ M''`
(`mem_commutator_of_commute_W1`)), so `x ↦ (v•x)·x⁻¹` is injective, hence *surjective* on the
finite `M'/M''`.  Every `y ∈ M'` is then `(v•x)·x⁻¹` mod `M''`; a `v`-fixed multiplicative `θ`
(trivial on `M''` by multiplicativity) evaluates to `θ(v•x)·θ(x)⁻¹ = 1` on it — so `θ = 1`,
a contradiction. -/
theorem Hypothesis.inertia_eq_derived_of_linear [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M)}
    (hθne : θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M))
    (hθdeg : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1) :
    ClassFunction.inertia (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)
      = (derivedInG M).subgroupOf M := by
  classical
  haveI : Fintype G := Fintype.ofFinite _
  refine le_antisymm ?_ (ClassFunction.subgroup_le_inertia _)
  intro w hw
  by_contra hwK
  -- decompose `w = k · v` through the complement `M = M' ⋊ W₁`; `v ≠ 1` since `w ∉ M'`.
  obtain ⟨⟨k, v⟩, hkv, -⟩ := hyp.typeP.M_complement.existsUnique (w : ↥M)
  have hvI : (v : ↥M) ∈ ClassFunction.inertia
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) := by
    have hkI : (k : ↥M) ∈ ClassFunction.inertia
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) :=
      ClassFunction.subgroup_le_inertia _ k.2
    have hveq : (v : ↥M) = (k : ↥M)⁻¹ * w := by
      rw [← hkv]; group
    rw [hveq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hkI) hw
  have hvne : (v : ↥M) ≠ 1 := by
    intro hv1
    refine hwK ?_
    have hwk : w = (k : ↥M) := by rw [← hkv, hv1, mul_one]
    rw [hwk]; exact k.2
  have hvfix : ClassFunction.conjBy (v : ↥M)
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)
      = (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) := hvI
  -- rebind the complement component as a subgroup-subtype element for the action.
  have hvW1s : (v : ↥M) ∈ hyp.W1.subgroupOf M := v.2
  -- the `W₁`-conjugation action on `↥M'` and its fixed-point-free quotient action mod `M''`.
  letI act : MulDistribMulAction ↥(hyp.W1.subgroupOf M) ↥((derivedInG M).subgroupOf M) :=
    MulDistribMulAction.compHom _
      ((MulAut.conjNormal (H := (derivedInG M).subgroupOf M)).comp
        (hyp.W1.subgroupOf M).subtype)
  have hsmul : ∀ (a : ↥(hyp.W1.subgroupOf M)) (x : ↥((derivedInG M).subgroupOf M)),
      ((a • x : ↥((derivedInG M).subgroupOf M)) : ↥M)
      = (a : ↥M) * (x : ↥M) * (a : ↥M)⁻¹ := by
    intro a x
    change ((MulAut.conjNormal (H := (derivedInG M).subgroupOf M)
      ((hyp.W1.subgroupOf M).subtype a)) x : ↥M) = _
    rw [MulAut.conjNormal_apply]; rfl
  have hMinv : ∀ a : ↥(hyp.W1.subgroupOf M),
      ∀ m ∈ commutator ↥((derivedInG M).subgroupOf M),
      a • m ∈ commutator ↥((derivedInG M).subgroupOf M) := by
    intro a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (commutator ↥((derivedInG M).subgroupOf M)).Characteristic)
      (MulDistribMulAction.toMulAut _ _ a)
    have hmem : (MulDistribMulAction.toMulAut _ _ a).toMonoidHom m
        ∈ commutator ↥((derivedInG M).subgroupOf M) := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  have hfixle : ∀ a : ↥(hyp.W1.subgroupOf M), a ≠ 1 →
      ∀ x : ↥((derivedInG M).subgroupOf M), a • x = x →
      x ∈ commutator ↥((derivedInG M).subgroupOf M) := by
    intro a ha x hax
    have haMne : (a : ↥M) ≠ 1 := fun h => ha (Subtype.ext h)
    refine hyp.mem_commutator_of_commute_W1 a.2 haMne (x := x) ?_
    have h1 := hsmul a x
    rw [hax] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1.symm
  have hCop : Nat.Coprime (Nat.card ↥(hyp.W1.subgroupOf M))
      (Nat.card ↥((derivedInG M).subgroupOf M)) := by
    have h1 : Nat.card ↥(hyp.W1.subgroupOf M) = Nat.card ↥hyp.W1 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.typeP.W1_le).toEquiv
    have h2 : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.map_subtype_le (commutator ↥M) : derivedInG M ≤ M)).toEquiv
    rw [h1, h2]
    exact (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP).symm
  have hFrob := OddOrder.Isaacs.Ch06.IsFrobeniusAction.quotient_of_fixedPoints_le
    hCop (commutator ↥((derivedInG M).subgroupOf M)) hMinv hfixle
  letI actQ := OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction
    (N := ↥((derivedInG M).subgroupOf M)) (commutator ↥((derivedInG M).subgroupOf M)) hMinv
  -- `x ↦ (v•x)·x⁻¹` is injective mod `M''` (fixed-point-freeness), hence surjective.
  set v' : ↥(hyp.W1.subgroupOf M) := ⟨(v : ↥M), hvW1s⟩ with hv'
  have hvne' : v' ≠ 1 := fun h => hvne (congrArg Subtype.val h)
  have hinj : Function.Injective
      (fun q : (↥((derivedInG M).subgroupOf M)
        ⧸ commutator ↥((derivedInG M).subgroupOf M)) => (v' • q) * q⁻¹) := by
    intro q₁ q₂ h12
    simp only at h12
    have hstep : v' • (q₂⁻¹ * q₁) = q₂⁻¹ * q₁ := by
      have h2 := mul_inv_eq_iff_eq_mul.mp h12
      rw [smul_mul', smul_inv']
      have h3 : v' • q₁ = (v' • q₂) * q₂⁻¹ * q₁ := by rw [← h2]
      rw [h3]
      group
    by_contra hne
    refine hFrob v' hvne' (q₂⁻¹ * q₁) (fun h => hne ?_) hstep
    have h4 : q₁ = q₂ * (q₂⁻¹ * q₁) := by group
    rw [h4, h, mul_one]
  have hsurj := Finite.surjective_of_injective hinj
  -- `θ` is multiplicative, trivial on `M''`, and `v`-conjugation-invariant.
  have hmul := θ.isIrreducible.map_mul_of_apply_one_eq_one hθdeg
  have hinv : ∀ x : ↥((derivedInG M).subgroupOf M),
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x⁻¹
      = ((θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x)⁻¹ := by
    intro x
    have h1 : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x
        * (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x⁻¹ = 1 := by
      rw [← hmul, mul_inv_cancel]; exact hθdeg
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)
  have hval_ne : ∀ x : ↥((derivedInG M).subgroupOf M),
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x ≠ 0 := by
    intro x h0
    have h1 : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x
        * (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x⁻¹ = 1 := by
      rw [← hmul, mul_inv_cancel]; exact hθdeg
    rw [h0, zero_mul] at h1
    exact one_ne_zero h1.symm
  have hN1 : ∀ n ∈ commutator ↥((derivedInG M).subgroupOf M),
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) n = 1 := by
    intro n hn
    rw [commutator_eq_closure] at hn
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨a, b, rfl⟩ := hx
        change (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) (a * b * a⁻¹ * b⁻¹) = 1
        rw [hmul, hmul, hmul, hinv, hinv]
        field_simp [hval_ne a, hval_ne b]
    | one => exact hθdeg
    | mul x y _ _ hx hy => rw [hmul, hx, hy, one_mul]
    | inv x _ hx => rw [hinv, hx, inv_one]
  -- every `y ∈ M'` is `(v•x)·x⁻¹ · n`, so `θ y = θ(v•x)·θ(x)⁻¹ = 1`.
  have hall : ∀ y : ↥((derivedInG M).subgroupOf M),
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) y = 1 := by
    intro y
    obtain ⟨q, hq⟩ := hsurj (QuotientGroup.mk y)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hmk : (QuotientGroup.mk ((v' • x) * x⁻¹) :
        ↥((derivedInG M).subgroupOf M) ⧸ commutator ↥((derivedInG M).subgroupOf M))
        = QuotientGroup.mk y := by
      rw [← hq]; rfl
    have hmem := (QuotientGroup.eq (s := commutator ↥((derivedInG M).subgroupOf M))).mp hmk
    have hyeq : y = (v' • x) * x⁻¹ * (((v' • x) * x⁻¹)⁻¹ * y) := by group
    have hθvsx : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) (v' • x)
        = (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x := by
      have hcoe : ((v' • x : ↥((derivedInG M).subgroupOf M)) : ↥M)
          = (v : ↥M) * (x : ↥M) * (v : ↥M)⁻¹ := hsmul v' x
      have h5 := congrArg
        (fun f : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ => f x) hvfix
      simp only [ClassFunction.conjBy_apply] at h5
      rw [← h5]
      exact congrArg _ (Subtype.ext hcoe)
    rw [hyeq, hmul, hmul, hθvsx, hinv, hN1 _ hmem]
    field_simp [hval_ne x]
  -- contradiction: `θ` is the trivial character.
  refine hθne (Subtype.ext ?_)
  ext x
  rw [hall x]
  rfl

/-- **Peterfalvi (8.5.a)/(11.2): `C = C_U(H)` is normalized by `M`** (the `C_normalized_by_M`
obligation of the (11.2) setup): `F(M) = H ⊔ C` (`TypePData.fitting_eq`) is `M`-invariant; `H` and
`C` centralize each other with coprime orders (`typeP_coprime_H_uW1`), so the `M`-conjugate of a
`C`-element, decomposed along `F(M) = H·C`, has trivial `H`-part by the uniqueness of the
commuting coprime (`π(H)`, `π(H)'`) decomposition (`isPiElement_mul_unique`). -/
theorem typePData_C_normalized_by_M [Finite G] {M : Subgroup G} (data : TypePData M)
    (hU : data.U ≠ ⊥) :
    M ≤ Subgroup.normalizer
      ((data.U ⊓ Subgroup.centralizer (data.H : Set G) : Subgroup G) : Set G) := by
  classical
  -- `F(M)` mapped to `G` is normalized by all of `M`
  have hFn : M ≤ Subgroup.normalizer
      (((OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype : Subgroup G) : Set G) := by
    have h := Subgroup.le_normalizer_map (H := OddOrder.Isaacs.Ch01.fitting ↥M) M.subtype
    rwa [Subgroup.normalizer_eq_top_iff.mpr inferInstance, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
  -- `C ≤ N(H)` (it centralizes `H`), so `↑(H ⊔ C) = ↑H * ↑C` as sets
  have hCleNH : (data.U ⊓ Subgroup.centralizer (data.H : Set G) : Subgroup G)
      ≤ Subgroup.normalizer (data.H : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer (data.H : Set G))
  have hHC : ((data.H ⊔ (data.U ⊓ Subgroup.centralizer (data.H : Set G)) : Subgroup G) : Set G)
      = (data.H : Set G) * ((data.U ⊓ Subgroup.centralizer (data.H : Set G) : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCleNH
  -- coprimality of `|H|` and `|U|`
  have hcoHU : Nat.Coprime (Nat.card ↥data.H) (Nat.card ↥data.U) :=
    (OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1 data hU).coprime_dvd_right
      (Subgroup.card_dvd_of_le le_sup_left)
  -- orders of `C`-elements are `π(H)'`; orders of `H`-elements are `π(H)`
  set π : Set ℕ := {p : ℕ | p ∣ Nat.card ↥data.H} with hπ_def
  have hPiH : ∀ h ∈ data.H, IsPiElement π h := by
    intro h hh p hp
    have hdvd : orderOf h ∣ Nat.card ↥data.H := by
      have h1 : orderOf ((⟨h, hh⟩ : ↥data.H) : G) = orderOf (⟨h, hh⟩ : ↥data.H) :=
        orderOf_injective data.H.subtype data.H.subtype_injective ⟨h, hh⟩
      rw [show ((⟨h, hh⟩ : ↥data.H) : G) = h from rfl] at h1
      rw [h1]
      exact orderOf_dvd_natCard _
    exact (Nat.dvd_of_mem_primeFactors hp).trans hdvd
  have hPiC : ∀ c ∈ data.U, IsPiElement πᶜ c := by
    intro c hc p hp
    have hdvd : orderOf c ∣ Nat.card ↥data.U := by
      have h1 : orderOf ((⟨c, hc⟩ : ↥data.U) : G) = orderOf (⟨c, hc⟩ : ↥data.U) :=
        orderOf_injective data.U.subtype data.U.subtype_injective ⟨c, hc⟩
      rw [show ((⟨c, hc⟩ : ↥data.U) : G) = c from rfl] at h1
      rw [h1]
      exact orderOf_dvd_natCard _
    intro hpH
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpU : p ∣ Nat.card ↥data.U := (Nat.dvd_of_mem_primeFactors hp).trans hdvd
    have hgcd : p ∣ Nat.gcd (Nat.card ↥data.H) (Nat.card ↥data.U) := Nat.dvd_gcd hpH hpU
    rw [hcoHU] at hgcd
    exact hprime.one_lt.ne' (Nat.dvd_one.mp hgcd)
  -- one-sided conjugation stability suffices
  have key : ∀ g ∈ M, ∀ x ∈ (data.U ⊓ Subgroup.centralizer (data.H : Set G) : Subgroup G),
      g * x * g⁻¹ ∈ (data.U ⊓ Subgroup.centralizer (data.H : Set G) : Subgroup G) := by
    intro g hg x hx
    -- the conjugate lies in `F(M) = H ⊔ C`
    have hxF : x ∈ (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype := by
      rw [data.fitting_eq]
      exact Subgroup.mem_sup_right hx
    have hgxF : g * x * g⁻¹ ∈ (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype :=
      ((Subgroup.mem_normalizer_iff.mp (hFn hg)) x).mp hxF
    rw [data.fitting_eq, ← SetLike.mem_coe, hHC, Set.mem_mul] at hgxF
    obtain ⟨h, hh, c, hc, hhc⟩ := hgxF
    -- `h` and `c` commute (`c` centralizes `H`)
    have hcomm : Commute h c := Subgroup.mem_centralizer_iff.mp hc.2 h hh
    -- the conjugate is a `π'`-element (conjugation preserves order, `x ∈ U`)
    have hgx_pi : IsPiElement πᶜ (g * x * g⁻¹) := by
      intro p hp
      have horder : orderOf (g * x * g⁻¹) = orderOf x := by
        have h1 := orderOf_injective (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective x
        simpa [MulAut.conj_apply] using h1
      rw [horder] at hp
      exact hPiC x hx.1 p hp
    -- uniqueness of the commuting coprime decomposition: the `H`-part is trivial
    obtain ⟨hh1, hceq⟩ := isPiElement_mul_unique (π := π) hhc hcomm
      (hPiH h hh) (hPiC c hc.1)
      (one_mul (g * x * g⁻¹)) (Commute.one_left _) (isPiElement_one π) hgx_pi
    rw [← hhc, hh1, one_mul]
    exact hc
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key g hg x hx
  · intro hx
    have h1 := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using h1

open scoped Classical in
/-- **The linear-character count** (Pontryagin): for a finite group `H`, the number of degree-one
irreducible characters equals `|H^{ab}| = [H : H']`.  Degree-one irreducibles are exactly the
multiplicative characters `H →* ℂˣ` (`linearIrreducibleCharacter`,
`exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one`); those factor through the
abelianization (`Abelianization.lift`), whose dual has the same cardinality (Pontryagin,
`CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`).  This is the
`#(linear sources) = |HU/HC| = |U/C| = u` input of the (11.8.1) `|S(HC)| = n` count
(Coq `size_S1`, `card_Iirr_abelian`). -/
theorem card_filter_degree_one_eq_card_abelianization (H : Type*) [Group H] [Finite H] :
    (Finset.univ.filter fun θ : IrreducibleCharacter H =>
        (θ : ClassFunction H ℂ) 1 = 1).card = Nat.card (Abelianization H) := by
  classical
  have hbij : Function.Bijective (fun ψ : H →* ℂˣ =>
      (⟨linearIrreducibleCharacter ψ, linearIrreducibleCharacter_apply_one ψ⟩ :
        {θ : IrreducibleCharacter H // (θ : ClassFunction H ℂ) 1 = 1})) := by
    constructor
    · intro a b hab
      exact linearIrreducibleCharacter_injective (congrArg Subtype.val hab)
    · rintro ⟨θ, hθ⟩
      obtain ⟨ψ, hψ⟩ := θ.property.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one hθ
      exact ⟨ψ, Subtype.ext (Subtype.ext hψ)⟩
  calc (Finset.univ.filter fun θ : IrreducibleCharacter H =>
          (θ : ClassFunction H ℂ) 1 = 1).card
      = Nat.card {θ : IrreducibleCharacter H // (θ : ClassFunction H ℂ) 1 = 1} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card (H →* ℂˣ) := (Nat.card_eq_of_bijective _ hbij).symm
    _ = Nat.card (Abelianization H →* ℂˣ) := Nat.card_congr Abelianization.lift
    _ = Nat.card (Abelianization H) :=
        Nat.card_congr (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
          (Abelianization H) ℂ).some.toEquiv

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.1), the orbit count `#{nontrivial linear} = w₁ · |S(HC)|`** (Coq `size_S1`
without the (11.5) arithmetic): every nontrivial linear character `θ` of `M'` induces irreducibly
to a degree-`w₁` member of `S = inducedFamily M` (`inertia_eq_derived_of_linear` + [Is] 6.34);
every degree-`w₁` irreducible member arises this way (the degree forces a linear source); and each
such member has exactly `w₁ = [M : M']` sources — its conjugation orbit, free since the inertia
group is `M'` (`card_filter_induce_eq_index_inertia`).  So the nontrivial linear characters of
`M'` are counted with multiplicity `w₁` by the degree-`w₁` irreducible members `S(HC)` of `S`. -/
theorem Hypothesis.card_filter_linear_eq_w1_mul_card_SHCSet_filter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    (Finset.univ.filter fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
        θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
          (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1).card
      = hyp.w1 * (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
          (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
            ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ)).card := by
  haveI := hyp.finiteG
  classical
  have hidx : ((derivedInG M).subgroupOf M).index = hyp.w1 :=
    hyp.typeP.card_W1_eq_derived_index.symm
  have hw1ne : (hyp.w1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  -- a nontrivial linear character of `M'` induces irreducibly
  have hirr : ∀ θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M),
      θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) →
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1 →
      IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)) := fun θ hne hdeg =>
    isIrreducibleCharacter_induce_of_inertia_eq θ (hyp.inertia_eq_derived_of_linear hG hne hdeg)
  -- the nontrivial linear characters are closed under `↥M`-conjugation
  have hTinv : ∀ θ ∈ (Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
            (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1),
      ∀ g : ↥M, IrreducibleCharacter.conjBy g θ ∈ (Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
            (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1) := by
    intro θ hθ g
    rw [Finset.mem_filter] at hθ ⊢
    obtain ⟨-, hne, hdeg⟩ := hθ
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro heq
      refine hne ?_
      have h1 : IrreducibleCharacter.conjBy (g⁻¹ : ↥M) (IrreducibleCharacter.conjBy g θ) = θ := by
        rw [← IrreducibleCharacter.conjBy_mul]
        simp
      rw [heq] at h1
      have h2 : IrreducibleCharacter.conjBy (g⁻¹ : ↥M)
          (trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M))
          = trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) := by
        apply IrreducibleCharacter.ext
        rw [IrreducibleCharacter.coe_conjBy]
        ext x
        simp [ClassFunction.conjBy_apply]
      rw [h2] at h1
      exact h1.symm
    · rw [conjBy_apply_one]
      exact hdeg
  -- fiberwise count over the induction map: each fiber is a free conjugation orbit of size `w₁`
  rw [Finset.card_eq_sum_card_fiberwise (fun θ hθ => Finset.mem_image_of_mem
    (fun θ' : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
      ClassFunction.induce ((derivedInG M).subgroupOf M) θ'.toClassFunction) hθ)]
  have hfib : ∀ φ ∈ (Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
            (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1).image
        (fun θ' : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          ClassFunction.induce ((derivedInG M).subgroupOf M) θ'.toClassFunction),
      ((Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
            (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1).filter
        fun θ => ClassFunction.induce ((derivedInG M).subgroupOf M) θ.toClassFunction = φ).card
        = hyp.w1 := by
    intro φ hφ
    obtain ⟨θ₀, hθ₀, rfl⟩ := Finset.mem_image.mp hφ
    rw [card_filter_induce_eq_index_inertia _ hTinv θ₀ hθ₀]
    rw [Finset.mem_filter] at hθ₀
    rw [show IrreducibleCharacter.inertia (G := ↥M) θ₀ = (derivedInG M).subgroupOf M from
      hyp.inertia_eq_derived_of_linear hG hθ₀.2.1 hθ₀.2.2]
    exact hidx
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  -- identify the image with the degree-`w₁` irreducible members of `S`
  have himage : (Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
            (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1).image
        (fun θ' : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          ClassFunction.induce ((derivedInG M).subgroupOf M) θ'.toClassFunction)
      = (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
          (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
            ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ)).image
          (fun χ : IrreducibleCharacter ↥M => (χ : ClassFunction ↥M ℂ)) := by
    ext φ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨θ, ⟨hne, hdeg⟩, rfl⟩
      refine ⟨⟨ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ), hirr θ hne hdeg⟩,
        ⟨⟨θ, hne, rfl⟩, ?_⟩, rfl⟩
      change ((ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) :
          ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ)
      rw [ClassFunction.induce_apply_one, hdeg, mul_one, hidx]
    · rintro ⟨χ, ⟨⟨θ, hθne, hχeq⟩, hχdeg⟩, rfl⟩
      have hθdeg : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1 := by
        have h1 := ClassFunction.induce_apply_one ((derivedInG M).subgroupOf M)
          (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)
        rw [← hχeq] at h1
        rw [hχdeg, hidx] at h1
        exact mul_left_cancel₀ hw1ne (h1.symm.trans (mul_one (hyp.w1 : ℂ)).symm)
      exact ⟨θ, ⟨hθne, hθdeg⟩, hχeq.symm⟩
  rw [himage, Finset.card_image_of_injective _
    (fun a b hab => IrreducibleCharacter.ext hab), Nat.mul_comm]

open scoped Classical in
/-- **Peterfalvi (11.8.1), abelianization form of the `S(HC)` count**:
`|M'/M''| = w₁ · |S(HC)| + 1`.  The linear characters of `M'` number `|M'{}^{ab}|`
(`card_filter_degree_one_eq_card_abelianization`); one of them is trivial, and the nontrivial
ones are counted with multiplicity `w₁` by the degree-`w₁` irreducible members of `S`
(`card_filter_linear_eq_w1_mul_card_SHCSet_filter`).  Downstream ((11.5) `M'' = HC`,
`S13.secondDerived_eq_HC`) this becomes `u = w₁·|S(HC)| + 1`, i.e. `|S(HC)| = (u−1)/w₁ = n`. -/
theorem Hypothesis.card_abelianization_derived_eq_w1_mul_card_SHCSet_add_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    Nat.card (Abelianization ↥((derivedInG M).subgroupOf M))
      = hyp.w1 * (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
          (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
            ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ)).card + 1 := by
  haveI := hyp.finiteG
  classical
  rw [← card_filter_degree_one_eq_card_abelianization,
    ← hyp.card_filter_linear_eq_w1_mul_card_SHCSet_filter hG]
  -- the trivial character is the one degree-one character excluded by the nontriviality filter
  have htriv : trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M)
      ∈ (Finset.univ.filter fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have herase : (Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
            (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1)
      = (Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1).erase
        (trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M)) := by
    ext θ
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [herase, Finset.card_erase_of_mem htriv,
    Nat.sub_add_cancel (Finset.card_pos.mpr ⟨_, htriv⟩)]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.1), `|S(HC)| = n` — the arithmetic reduction** (sorry-free).  Given the
abelianization order `|M'{}^{ab}| = |M'/M''| = d`, the count `|S(HC)| = n` follows purely from the
orbit count `|M'{}^{ab}| = w₁·|S(HC)| + 1`
(`card_abelianization_derived_eq_w1_mul_card_SHCSet_add_one`) and the index relation
`n·w₁ = d − δ = d − 1` (`n_formula` at `δ = 1`): `w₁·|S(HC)| = d − 1 = n·w₁`, so `|S(HC)| = n`. -/
theorem Hypothesis.card_SHCSet_filter_eq_charParam_n_of_card_abelianization_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (params : CharacterParameters hyp) (hdelta : params.delta = 1)
    (hab : Nat.card (Abelianization ↥((derivedInG M).subgroupOf M)) = params.d) :
    (Finset.univ.filter (fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ))).card = params.n := by
  haveI := hyp.finiteG
  classical
  -- `d = w₁·|S(HC)| + 1`
  have horbit := hyp.card_abelianization_derived_eq_w1_mul_card_SHCSet_add_one hG
  rw [hab] at horbit
  -- `n·w₁ = d − 1 = w₁·|S(HC)|`
  have hnw : params.n * hyp.w1
      = hyp.w1 * (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
          (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
            ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ)).card := by
    have h := params.n_formula
    rw [hdelta, horbit] at h
    have : (params.n * hyp.w1 : ℤ)
        = (hyp.w1 * (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
            (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
              ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ)).card : ℤ) := by
      push_cast at h ⊢
      linarith
    exact_mod_cast this
  have hw1pos : 0 < hyp.w1 := Nat.pos_of_ne_zero (NeZero.ne hyp.w1)
  rw [mul_comm hyp.w1] at hnw
  exact (Nat.eq_of_mul_eq_mul_right hw1pos hnw).symm


/-- **Structural index identity for the (11.8.1) count**: `|M'|·|C| = |HC|·|U|`, where
`C = U ⊓ C_G(H)` and `HC = H ⊔ C`.  Since `M' = H ⋊ U` (`derived_complement`; `H ⊴ M'`,
`H ⊓ U = ⊥`) we have `|M'| = |H|·|U|`, and `HC = H ⋊ C` (`C ≤ U`, same disjointness) gives
`|HC| = |H|·|C|`.  Rearranged this is `[M' : HC] = [U : C]` — the structural half of
`|M'/M''| = |U/C|` (with (11.5) `M'' = HC`) feeding the count. -/
theorem typePData_card_derived_mul_card_C_eq [Finite G] {M : Subgroup G} (data : TypePData M) :
    Nat.card ↥(derivedInG M)
      * Nat.card ↥(data.U ⊓ Subgroup.centralizer (data.H : Set G))
      = Nat.card ↥(data.H ⊔ (data.U ⊓ Subgroup.centralizer (data.H : Set G)))
        * Nat.card ↥data.U := by
  classical
  set C := data.U ⊓ Subgroup.centralizer (data.H : Set G) with hCdef
  have hCleU : C ≤ data.U := inf_le_left
  have hHleM' : data.H ≤ derivedInG M := data.H_le
  have hCleM' : C ≤ derivedInG M := hCleU.trans data.U_le
  have hM'leM : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `H ⊓ U = ⊥` from the complement `M' = H ⋊ U`
  have hHUbot : data.H ⊓ data.U = ⊥ := by
    have hd : (data.H ⊓ data.U).subgroupOf (derivedInG M) = ⊥ := by
      have h1 : (data.H ⊓ data.U).subgroupOf (derivedInG M)
          = data.H.subgroupOf (derivedInG M) ⊓ data.U.subgroupOf (derivedInG M) :=
        Subgroup.comap_inf _ _ _
      rw [h1]; exact disjoint_iff.mp data.derived_complement.disjoint
    have hle : data.H ⊓ data.U ≤ derivedInG M := inf_le_left.trans data.H_le
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hle] at hd
    exact hd
  -- `C ⊓ H = ⊥`
  have hCHbot : C ⊓ data.H = ⊥ := by
    refine le_bot_iff.mp ?_
    calc C ⊓ data.H ≤ data.U ⊓ data.H := inf_le_inf_right _ hCleU
      _ = data.H ⊓ data.U := inf_comm _ _
      _ = ⊥ := hHUbot
  -- `|M'| = |H|·|U|`
  have hHU : Nat.card ↥data.H * Nat.card ↥data.U = Nat.card ↥(derivedInG M) := by
    have h := data.derived_complement.card_mul
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.U_le).toEquiv] at h
  -- `H ⊴ M'`
  haveI hHn : (data.H.subgroupOf (derivedInG M)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer data.H_le).mpr ?_
    have hnM : M ≤ Subgroup.normalizer (data.H : Set G) := by
      rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M
    exact hM'leM.trans hnM
  -- `|HC| = |H|·|C|`, via disjoint-normal card in `↥M'`
  have hHC : Nat.card ↥(data.H ⊔ C) = Nat.card ↥data.H * Nat.card ↥C := by
    have hdisj : C.subgroupOf (derivedInG M) ⊓ data.H.subgroupOf (derivedInG M) = ⊥ := by
      have h1 : (C ⊓ data.H).subgroupOf (derivedInG M)
          = C.subgroupOf (derivedInG M) ⊓ data.H.subgroupOf (derivedInG M) :=
        Subgroup.comap_inf _ _ _
      rw [← h1, hCHbot, Subgroup.bot_subgroupOf]
    have hcard := OddOrder.BG.Ch1.S01.card_sup_eq_card_mul_card_of_disjoint_normal
      (T := C.subgroupOf (derivedInG M)) (M := data.H.subgroupOf (derivedInG M)) hdisj
    rw [← Subgroup.subgroupOf_sup hCleM' hHleM',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hCleM' hHleM')).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleM').toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleM').toEquiv, sup_comm] at hcard
    rw [hcard, Nat.mul_comm]
  rw [← hHU, hHC]
  ring

/-- **Structural core of the (11.8.1) count `|M'/M''| = |U : C|`** (`C = U ⊓ C_G(H)`).  Given the
(11.5) identity `M'' = HC` — supplied here in the `TypePData`-expressible form
`secondDerivedInAmbient M = H ⊔ C` — the abelianization order `|M'{}^{ab}| = |M' : M''|` equals the
relative index `|U : C|`.

Three steps, all sorry-free group theory: (1) `|M'{}^{ab}| = |M'{}^{ab}|` transports along
`M' = (derivedInG M).subgroupOf M ≃* derivedInG M` (`MulEquiv.abelianizationCongr`); (2)
`|(derivedInG M){}^{ab}| = |M' : M''|` because `Abelianization = quotient by the commutator` and
`M''.subgroupOf M' = commutator ↥M'` (`comap_map_eq_self_of_injective`); (3) `|M' : HC| = |U : C|`
by cancelling the common factor `|H|` in the structural card identity `|M'|·|C| = |HC|·|U|`
(`typePData_card_derived_mul_card_C_eq`), mirroring the S13 `HC_relIndex_derived`.

This isolates the *char-free* half of `card_SHCSet_filter_eq_charParam_n`'s remaining input
`|M'{}^{ab}| = d`: with (11.5) discharged it reduces `d = |M'{}^{ab}|` to `|U : C| = u = d`, whose
`|U : C| = u` half is the (11.7) `H₀ = 1` collapse `C_U(H̄) = C` and whose `u = d` half is
`charParam_d_eq_u`. -/
theorem typePData_card_abelianization_derived_eq_relIndex_C [Finite G] {M : Subgroup G}
    (data : TypePData M)
    (hM2 : secondDerivedInAmbient M
      = data.H ⊔ (data.U ⊓ Subgroup.centralizer (data.H : Set G))) :
    Nat.card (Abelianization ↥((derivedInG M).subgroupOf M))
      = (data.U ⊓ Subgroup.centralizer (data.H : Set G)).relIndex data.U := by
  classical
  set C := data.U ⊓ Subgroup.centralizer (data.H : Set G) with hCdef
  set HC := data.H ⊔ C with hHCdef
  have hCleU : C ≤ data.U := inf_le_left
  have hHCleM' : HC ≤ derivedInG M := sup_le data.H_le (hCleU.trans data.U_le)
  -- (1) transport the abelianization along `↥(M'.subgroupOf M) ≃* ↥M'`
  have hiso : Nat.card (Abelianization ↥((derivedInG M).subgroupOf M))
      = Nat.card (Abelianization ↥(derivedInG M)) :=
    Nat.card_congr (MulEquiv.abelianizationCongr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _))).toEquiv
  -- (2) `M''.subgroupOf M' = commutator ↥M'`, so `|M'{}^{ab}| = |M' : M''|`
  have hcomm : (secondDerivedInAmbient M).subgroupOf (derivedInG M)
      = commutator ↥(derivedInG M) := by
    have hdef : secondDerivedInAmbient M
        = (commutator ↥(derivedInG M)).map (derivedInG M).subtype := rfl
    rw [hdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (derivedInG M).subtype_injective]
  have hab : Nat.card (Abelianization ↥(derivedInG M))
      = (secondDerivedInAmbient M).relIndex (derivedInG M) := by
    rw [Subgroup.relIndex, hcomm]; rfl
  -- (3) `|M' : HC| = |U : C|` by cancelling `|H|·|C|` in `|M'|·|C| = |HC|·|U|`
  have h1 : Nat.card ↥HC * HC.relIndex (derivedInG M) = Nat.card ↥(derivedInG M) := by
    have := Subgroup.card_mul_index (HC.subgroupOf (derivedInG M))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHCleM').toEquiv] at this
  have h2 : Nat.card ↥C * C.relIndex data.U = Nat.card ↥data.U := by
    have := Subgroup.card_mul_index (C.subgroupOf data.U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleU).toEquiv] at this
  have hcardid : Nat.card ↥(derivedInG M) * Nat.card ↥C = Nat.card ↥HC * Nat.card ↥data.U := by
    have h := typePData_card_derived_mul_card_C_eq data
    rw [← hCdef, ← hHCdef] at h
    exact h
  have hkey : Nat.card ↥HC * Nat.card ↥C * HC.relIndex (derivedInG M)
      = Nat.card ↥HC * Nat.card ↥C * C.relIndex data.U := by
    calc Nat.card ↥HC * Nat.card ↥C * HC.relIndex (derivedInG M)
        = Nat.card ↥C * (Nat.card ↥HC * HC.relIndex (derivedInG M)) := by ring
      _ = Nat.card ↥C * Nat.card ↥(derivedInG M) := by rw [h1]
      _ = Nat.card ↥(derivedInG M) * Nat.card ↥C := by ring
      _ = Nat.card ↥HC * Nat.card ↥data.U := hcardid
      _ = Nat.card ↥HC * (Nat.card ↥C * C.relIndex data.U) := by rw [h2]
      _ = Nat.card ↥HC * Nat.card ↥C * C.relIndex data.U := by ring
  have hpos : 0 < Nat.card ↥HC * Nat.card ↥C := Nat.mul_pos Nat.card_pos Nat.card_pos
  rw [hiso, hab, hM2]
  exact Nat.eq_of_mul_eq_mul_left hpos hkey

open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (11.8.1), the abelianization order `|M'{}^{ab}| = d`** — the assembled `|M'/M''| = d`
input to the `|S(HC)| = n` count, given the two structural facts of (11.5)/(11.7): `M'' = HC`
(`hM2`, i.e. `secondDerivedInAmbient M = H ⊔ C`) and `H₀ = 1` (`hN`, i.e. `chief.N = ⊥`).

Chains the three sorry-free pieces: `|M'{}^{ab}| = |U : C|`
(`typePData_card_abelianization_derived_eq_relIndex_C`, given `M'' = HC`), `|U : C| = u`
(`u_eq_relIndex_C`, given `H₀ = 1`), and `u = d` (`charParam_d_eq_u`).  The two hypotheses are
Peterfalvi (11.5) `secondDerived_eq_HC` and (11.7) `H_elementaryAbelian` — proven in `S13`
(downstream of this file), so `card_SHCSet_filter_eq_charParam_n` (below) discharges its
`|M'/M''| = d` obligation by threading them from the `FeitThompson` layer where `S13` is available. -/
theorem Hypothesis.card_abelianization_derived_eq_charParam_d [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hnt : OddOrder.GroupTheory.TypePNontrivialCore M hyp.typeP)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hN : chief.N = ⊥) :
    Nat.card (Abelianization ↥((derivedInG M).subgroupOf M)) = params.d := by
  have h1 : Nat.card (Abelianization ↥((derivedInG M).subgroupOf M))
      = (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)).relIndex hyp.typeP.U :=
    typePData_card_abelianization_derived_eq_relIndex_C hyp.typeP hM2
  have h2 : (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u
      = (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)).relIndex hyp.typeP.U :=
    hyp.u_eq_relIndex_C (hyp.toTypesIIIIIIVSetup htype hnt) chief hN
  have h3 : params.d = (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u :=
    hyp.charParam_d_eq_u hG htype params hmu hnt chief
  rw [h1, ← h2, h3]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.1), `|S(HC)| = n`** (§9 count, named obligation).  The number of degree-`w₁`
irreducible members of `S = inducedFamily M` equals `n = (d − δ)/w₁ = (d − 1)/w₁`.  `S(HC) = S₁`
consists of the `(u − 1)/q` degree-`q = w₁` irreducible constituents of the constant-degree Frobenius
family `(U/C) ⋊ W₁`, so `|S(HC)| = (u − 1)/q = (d − 1)/w₁ = n` by (11.8.1).  This is the cardinality
matching the isometric coherent image (`exists_coherentImage_SHC`, `|R| = |S(HC)|`) to `n`.

The orbit count `|M'{}^{ab}| = w₁·|S(HC)| + 1` and the `n·w₁ = d − 1` arithmetic are discharged by
`card_SHCSet_filter_eq_charParam_n_of_card_abelianization_eq` (sorry-free); the remaining
`|M'/M''| = d` input is assembled by `card_abelianization_derived_eq_charParam_d` from the two (11.5)/
(11.7) structural facts threaded here: `hM2` (`M'' = HC`, Peterfalvi (11.5) `S13.secondDerived_eq_HC`)
and `hHcard` (`|H| = |W₂|^{|W₁|} = p^q`, Peterfalvi (11.7)/(13.2.b) `S13.H_elementaryAbelian`), which
force any chief kernel `N ◁ H` to be trivial (`H/N` has order `p^q = |H|`, so `|N| = 1`).  Both are
`params`-free and expressed in the §12 `Hypothesis`; they are discharged at the `FeitThompson` layer
(where `S13` is available).  See `notes/peterfalvi/s13_11_8_orthogonality.md`. -/
theorem Hypothesis.card_SHCSet_filter_eq_charParam_n [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1) :
    (Finset.univ.filter (fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ))).card = params.n := by
  haveI := hyp.finiteG
  classical
  refine hyp.card_SHCSet_filter_eq_charParam_n_of_card_abelianization_eq hG params
    (hyp.charParam_delta_eq_one hG htype params hmu hδpm) ?_
  -- **The remaining (11.5)/(11.7) gate**: `|M'/M''| = u = d`.  Obtain the §11 chief factor on
  -- `M`, prove its kernel `N = ⊥` from `|H| = |W₂|^{|W₁|}` (any proper chief kernel would make
  -- `|H/N| < |H|`), then assemble `|M'{}^{ab}| = d` via `card_abelianization_derived_eq_charParam_d`.
  have hnt : TypePNontrivialCore M hyp.typeP :=
    typePNontrivialCore_of_isTypeIIIorIV htype hyp.typeP
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
    (hyp.toTypesIIIIIIVSetup htype hnt)
  -- `chief.N = ⊥`: `|H/N| = chief.p ^ q = |W₂|^q = |H|`, so `|N| = 1`.
  have hN : chief.N = ⊥ := by
    haveI := chief.N_normal
    -- `chief.p = |W₂| = w₂` for type III/IV.
    have hpW2 : chief.p = hyp.w2 := (chief.typeIII_IV_p_eq_W2 htype).symm
    -- `data.H = H` and `data.q = w₁` hold by `rfl` through the `TypesIIIIIIVSetup` projections.
    have hHcard' : Nat.card ↥(hyp.toTypesIIIIIIVSetup htype hnt).typeP.H = hyp.w2 ^ hyp.w1 :=
      hHcard
    have hq : (hyp.toTypesIIIIIIVSetup htype hnt).q = hyp.w1 := rfl
    have hquot : Nat.card (↥(hyp.toTypesIIIIIIVSetup htype hnt).typeP.H ⧸ chief.N)
        = hyp.w2 ^ hyp.w1 := by
      rw [OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief, hpW2, hq]
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
    rw [hquot, hHcard'] at hsplit
    have hN1 : Nat.card ↥chief.N = 1 := by
      have hpos : 0 < hyp.w2 ^ hyp.w1 := hHcard' ▸ Nat.card_pos
      nlinarith [Nat.card_pos (α := ↥chief.N), hsplit, hpos]
    exact Subgroup.card_eq_one.mp hN1
  exact hyp.card_abelianization_derived_eq_charParam_d hG htype params hmu hnt chief hM2 hN

/-! ## The §10 μ-grid column ↔ §6 certain-type column identification (issue 1019 update⁶²)

The (9.11) reducible-side coherence lives on the §6 `certainTypeSet`
(`certainTypeSet_isCoherent_A0`), while the §9/§10 family facts
(`reducible_mem_inducedKernelFamily_eq_muGrid_columnSum`) name the reducible members as μ-grid
column sums `∑ᵢ muGrid i j`.  These are the *same* characters: `muGrid` reads column `j` off the
§6 `columnFamily` at the Pontryagin-reindexed `W₂`-dual character.  The next two declarations
extract that dual character (`muColumnChar`) and record the identification
(`muGrid_columnSum_eq_columnSum`), so the two worlds can be joined by `rw`. -/

open scoped FiniteInduce in
/-- **The `Fin w₂`-indexed `W₂`-dual character of the §10 μ-grid**: column `j` of `muGrid` is the
§6 `columnFamily` at this character (`muGrid_columnSum_eq_columnSum`).  Extracted from the `muGrid`
definition (the `finCardEquivCharacterGroup`-reindex of `j`) so the §6 ↔ §10 column identification
can be *stated*. -/
noncomputable def Hypothesis.muColumnChar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (j : Fin hyp.w2) :
    ((hyp.toHypothesis46 hG hodd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hodd).W1 ⊔ (hyp.toHypothesis46 hG hodd).W2)) →* ℂˣ := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  exact finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)

open scoped FiniteInduce in
/-- The §10→§6 bridge's `Hypothesis46` carries the very (4.4) hypothesis of
`toCertainTypeHypothesis` (definitional, structure-literal projection). -/
theorem toHypothesis46_toHypothesis [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    (hyp.toHypothesis46 hG hodd).toHypothesis
      = (hyp.toCertainTypeHypothesis hG hodd).toHypothesis :=
  rfl

open scoped FiniteInduce in
/-- **A nontrivial μ-grid column has a nontrivial `W₂`-dual**: `muColumnChar j ≠ 1` for `j ≠ 0`.
The Pontryagin reindex `finCardEquivCharacterGroup` is normalized to send `0` to the trivial
character (`finCardEquivCharacterGroup_zero`), so by injectivity a nonzero column index gives a
nontrivial dual.  This is the `χ₂ ≠ 1` input of `columnSum_mem_certainTypeSet` for the μ-grid
column sums. -/
theorem Hypothesis.muColumnChar_ne_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {j : Fin hyp.w2} (hj : j ≠ 0) :
    hyp.muColumnChar hG hodd j ≠ 1 := by
  haveI := hyp.finiteG
  classical
  -- rebuild the `muColumnChar` definition chain (instance-defeq trap §5)
  set h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis with hhdef
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  set χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j) with hχ₂def
  have hchar : hyp.muColumnChar hG hodd j = χ₂ := by
    unfold Hypothesis.muColumnChar
    rfl
  rw [hchar, hχ₂def]
  intro heq
  -- `1 = fCECG 0`, so injectivity forces `finCongr … j = 0`, i.e. `j = 0`
  have heq' : finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
      = finCardEquivCharacterGroup (↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) 0 := by
    rw [finCardEquivCharacterGroup_zero]
    exact heq
  have hj0 : finCongr hcardW2sub.symm j = 0 :=
    (finCardEquivCharacterGroup _).injective heq'
  apply hj
  ext
  simpa using congrArg Fin.val hj0

open scoped FiniteInduce in
/-- **§10 μ-grid column sum = §6 certain-type column sum** (the world-joining identification):
`∑ᵢ muGrid i j = columnSum (toHypothesis46 …) (muColumnChar j)`.  Both sides enumerate the same
§6 `columnFamily` column — `muGrid` through the `finCongr` row-reindex (a bijection, so
`Equiv.sum_comp` collapses the sum), `columnSum` directly.  Through this equation the
`certainTypeSet` coherence (`certainTypeSet_isCoherent_A0`) applies to the μ-grid column sums
named by `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum`. -/
theorem Hypothesis.muGrid_columnSum_eq_columnSum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G))
    [NeZero (Nat.card (hyp.toHypothesis46 hG hodd).W1)]
    (j : Fin hyp.w2) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
      = OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hodd)
          (hyp.muColumnChar hG hodd j) := by
  haveI := hyp.finiteG
  classical
  -- rebuild the very `let`/`have` chain of the `muGrid`/`muColumnChar` definitions, so the
  -- entrywise `unfold …; rfl` identifications fire against syntactically matching variables
  set h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis with hhdef
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  set χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j) with hχ₂def
  -- entrywise: `muGrid i j = (h.columnFamily χ₂).mu (finCongr … i)`
  have hstep1 : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
      = ∑ i' : Fin (Nat.card ↥h.W1), ((h.columnFamily χ₂).mu i' : ClassFunction ↥M ℂ) := by
    rw [← Equiv.sum_comp (finCongr hcardW1.symm)
      (fun i' => ((h.columnFamily χ₂).mu i' : ClassFunction ↥M ℂ))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show hyp.muGrid hG hodd i j
      = ((h.columnFamily χ₂).mu ((finCongr hcardW1.symm) i) : ClassFunction ↥M ℂ)
    unfold Hypothesis.muGrid
    rfl
  -- the extracted dual character is the same `χ₂`
  have hchar : hyp.muColumnChar hG hodd j = χ₂ := by
    unfold Hypothesis.muColumnChar
    rfl
  rw [hstep1, OddOrder.Peterfalvi.S06.columnSum_def, hchar]
  with_unfolding_all rfl

open scoped FiniteInduce in
/-- **Cross-column degree constancy at the §6 interface** (Peterfalvi (10.3)): two nontrivial
μ-grid columns have equal column-sum degrees, phrased on the §6 `columnFamily` sums that
`columnSum_mem_certainTypeSet` consumes.  Via `muGrid_columnSum_eq_columnSum` (evaluated at `1`)
this is `∑ᵢ muGrid i j (1) = ∑ᵢ muGrid i k (1)`, which is `muGrid_apply_one_eq` entrywise. -/
theorem Hypothesis.muColumnChar_columnSum_apply_one_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) [NeZero (Nat.card (hyp.toHypothesis46 hG hodd).W1)]
    (hw2 : (hyp.w2).Prime) {j k : Fin hyp.w2} (hj : j ≠ 0) (hk : k ≠ 0) :
    (∑ i, (((hyp.toHypothesis46 hG hodd).columnFamily (hyp.muColumnChar hG hodd j)).mu i
        : ClassFunction ↥M ℂ) 1)
      = (∑ i, (((hyp.toHypothesis46 hG hodd).columnFamily (hyp.muColumnChar hG hodd k)).mu i
        : ClassFunction ↥M ℂ) 1) := by
  haveI := hyp.finiteG
  classical
  rw [← OddOrder.Peterfalvi.S06.columnSum_apply_one, ← OddOrder.Peterfalvi.S06.columnSum_apply_one,
    ← hyp.muGrid_columnSum_eq_columnSum hG hodd j, ← hyp.muGrid_columnSum_eq_columnSum hG hodd k]
  -- `(Σᵢ muGrid i j) 1 = (Σᵢ muGrid i k) 1` — sum-apply + per-entry (10.3)
  have hsum : ∀ j' : Fin hyp.w2, (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j') 1
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j' 1 := fun j' =>
    map_sum (AddMonoidHom.mk' (fun φ : ClassFunction ↥M ℂ => φ (1 : ↥M)) (fun _ _ => rfl))
      (fun i => hyp.muGrid hG hodd i j') Finset.univ
  rw [hsum j, hsum k]
  exact Finset.sum_congr rfl (fun i _ => hyp.muGrid_apply_one_eq hG hodd hw2 i i hj hk)


open scoped FiniteInduce in
/-- **A reducible kernel-filter member lies in the certain-type set** (the all-reducible-corner
membership composite, issue 1019 update⁶³): a reducible member `ψ` of any kernel filtration
`S(B) = inducedKernelFamily M' B` is a nontrivial μ-grid column sum
(`reducible_mem_inducedKernelFamily_eq_muGrid_columnSum`), which under the world-join
`muGrid_columnSum_eq_columnSum` is the §6 `columnSum` at the nontrivial dual
(`muColumnChar_ne_one`) of matching degree (`muColumnChar_columnSum_apply_one_eq`), hence lies in
`certainTypeSet (toHypothesis46 …) (muColumnChar kref)` for any nonzero reference column `kref`.
Feeding `isCoherent_of_subset` on `certainTypeSet_isCoherent_A0`, this closes the reducible side
of the (9.11) family coherence. -/
theorem Hypothesis.reducible_mem_inducedKernelFamily_mem_certainTypeSet [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    (hw2 : (hyp.w2).Prime) {kref : Fin hyp.w2} (hkref : kref ≠ 0)
    {B : Subgroup ↥M} {ψ : ClassFunction ↥M ℂ}
    (hψ : ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) B)
    (hred : ¬ IsIrreducibleCharacter ψ) :
    ψ ∈ OddOrder.Peterfalvi.S06.certainTypeSet (hyp.toHypothesis46 hG hG.odd)
      (hyp.muColumnChar hG hG.odd kref) := by
  haveI := hyp.finiteG
  classical
  obtain ⟨k, hk0, rfl⟩ :=
    hyp.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum hG htype hnt chief hψ hred
  rw [hyp.muGrid_columnSum_eq_columnSum hG hG.odd k]
  exact OddOrder.Peterfalvi.S06.columnSum_mem_certainTypeSet _
    (hyp.muColumnChar_ne_one hG hG.odd hk0)
    (hyp.muColumnChar_columnSum_apply_one_eq hG hG.odd hw2 hk0 hkref)

open scoped FiniteInduce in
/-- **Every nontrivial `W₂`-dual is a μ-grid column dual** (`muColumnChar` is onto the nontrivial
duals): for `χ₂ ≠ 1` there is a nonzero column index `k` with `muColumnChar k = χ₂`.  Inverse of
the Pontryagin reindex (`finCardEquivCharacterGroup`), with `k ≠ 0` from the zero-normalization
(`finCardEquivCharacterGroup_zero`). -/
theorem Hypothesis.exists_muColumnChar_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    {χ₂ : ((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2)) →* ℂˣ}
    (hχ₂ : χ₂ ≠ 1) :
    ∃ k : Fin hyp.w2, k ≠ 0 ∧ hyp.muColumnChar hG hG.odd k = χ₂ := by
  haveI := hyp.finiteG
  classical
  -- instances and the card identification, phrased at the `toHypothesis46` spelling (the type
  -- of `χ₂`), definitionally the `toCertainTypeHypothesis` chain of the `muColumnChar` body
  haveI : IsCyclic ↥((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2) :=
    (hyp.toCertainTypeHypothesis hG hG.odd).toHypothesis.isCyclic_sup
  letI : CommGroup ↥((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2) :=
    IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW2sub : Nat.card ↥((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2))) :=
    ⟨Nat.card_pos.ne'⟩
  refine ⟨finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂), ?_, ?_⟩
  · -- `k ≠ 0`: else `χ₂ = fCECG 0 = 1`
    intro h0
    apply hχ₂
    have hs0 : (finCardEquivCharacterGroup
        ↥((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
          ((hyp.toHypothesis46 hG hG.odd).W1 ⊔
            (hyp.toHypothesis46 hG hG.odd).W2))).symm χ₂ = 0 := by
      have := congrArg (finCongr hcardW2sub.symm) h0
      simpa using this
    rw [← Equiv.apply_symm_apply (finCardEquivCharacterGroup
        ↥((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
          ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2))) χ₂,
      hs0, finCardEquivCharacterGroup_zero]
  · -- `muColumnChar k = χ₂` (definitional chain + `finCongr` round-trip)
    have hchar : hyp.muColumnChar hG hG.odd
        (finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂))
        = finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm
            (finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂))) := by
      unfold Hypothesis.muColumnChar
      with_unfolding_all rfl
    rw [hchar, show finCongr hcardW2sub.symm
        (finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂))
        = (finCardEquivCharacterGroup _).symm χ₂ from by simp]
    exact Equiv.apply_symm_apply _ _

open scoped FiniteInduce in
/-- **A certain-type column sum is orthogonal to every irreducible kernel-filter member**
(the `hμ_S1` input of the (9.11) column-pair adjunction `adjoin_muColumnPair_of_irrFamily`):
`⟨columnSum χ₂, x⟩ = 0` for `χ₂ ≠ 1` and irreducible `x ∈ S(X)`.  Via `exists_muColumnChar_eq`
and the world-join `muGrid_columnSum_eq_columnSum` the column sum is `∑ᵢ muGrid i k` (`k ≠ 0`),
and each grid entry is orthogonal to `x` by the degree separation
`muGrid_inner_irr_member_eq_zero` ((11.8.1) `d ≡ 1 (mod w₁)` vs `x(1) = w₁·n`). -/
theorem Hypothesis.columnSum_inner_irr_member_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    {χ₂ : ((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2)) →* ℂˣ}
    (hχ₂ : χ₂ ≠ 1)
    {X : Subgroup ↥M} {x : ClassFunction ↥M ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) X)
    (hxirr : IsIrreducibleCharacter x) :
    ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂) x = 0 := by
  haveI := hyp.finiteG
  classical
  obtain ⟨k, hk0, hkeq⟩ := hyp.exists_muColumnChar_eq hG hχ₂
  rw [← hkeq, ← hyp.muGrid_columnSum_eq_columnSum hG hG.odd k, inner_sum_left]
  exact Finset.sum_eq_zero (fun i _ =>
    hyp.muGrid_inner_irr_member_eq_zero hG htype params hmu hx hxirr i hk0)

open scoped FiniteInduce in
/-- **The break decomposition `Da` for a certain-type column pair against an irreducible anchor**
(the `Da` input of `adjoin_muColumnPair_of_irrFamily`, at `a = 1`): the (5.4) decomposition
`Da : CharacterPsiDecomposition τ (columnSum χ₂) (1 • χ₁)` produced by
`certainTypeDecompositionDa`.  The §6 support shape `A(M) ∪ (tic.V)^M` is definitionally
`A₀(M)` (`tic.V = typePV M` by the `toHypothesis46` construction, and
`typePA0 = typePA ∪ conjClassSetIn M (typePV M)`), so the caller's `A₀`-support of
`columnSum χ₂ − χ₁` feeds through; the anchor orthogonalities are piece-4
(`columnSum_inner_irr_member_eq_zero`), and the integral image is the Dade
`ZIrr`-preservation on the supported difference. -/
noncomputable def Hypothesis.columnBreakDa [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    {χ₂ : ((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2)) →* ℂˣ}
    (hχ₂ : χ₂ ≠ 1)
    {X : Subgroup ↥M} {χ₁ : ClassFunction ↥M ℂ}
    (hχ₁ : χ₁ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) X)
    (hχ₁irr : IsIrreducibleCharacter χ₁)
    (hdiffsupp : ((OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂
      - χ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.A0)
    (hμZ : OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂ ∈ ZIrr ↥M) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj))
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂)
      ((1 : ℕ) • χ₁) := by
  haveI := hyp.finiteG
  classical
  have hdeg := (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
    (hyp.toHypothesis46 hG hG.odd) χ₂).symm
  have hsupp1 : ((OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂
      - (1 : ℕ) • χ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.A0 := by
    rw [one_smul]; exact hdiffsupp
  have hZ : (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂
      - (1 : ℕ) • χ₁ : ClassFunction ↥M ℂ) ∈ ZIrr ↥M := by
    rw [one_smul]
    exact Submodule.sub_mem _ hμZ hχ₁irr.mem_ZIrr
  have htau1_mema : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂
        - (1 : ℕ) • χ₁) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp.dadeData.dade
      hyp.hconj hsupp1 hZ
  have hχψ : ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂)
      (((1 : ℕ) • χ₁ : ClassFunction ↥M ℂ)) = 0 := by
    rw [one_smul]
    exact hyp.columnSum_inner_irr_member_eq_zero hG htype params hmu hχ₂ hχ₁ hχ₁irr
  have hχbarψ : ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂).conj
      (((1 : ℕ) • χ₁ : ClassFunction ↥M ℂ)) = 0 := by
    rw [one_smul, OddOrder.Peterfalvi.S06.columnSum_conj_eq]
    exact hyp.columnSum_inner_irr_member_eq_zero hG htype params hmu
      (inv_ne_one.mpr hχ₂) hχ₁ hχ₁irr
  exact OddOrder.Peterfalvi.S06.certainTypeDecompositionDa (hyp.toHypothesis46 hG hG.odd)
    hχ₂ hdeg hsupp1 htau1_mema hχψ hχbarψ

open scoped FiniteInduce in
/-- **A certain-type column sum is a virtual character** (`hμZ` input of the (9.11) column-pair
adjunction): `columnSum χ₂ = ∑ᵢ μ_{iχ₂} ∈ ℤ[Irr M]` — a sum of irreducible characters. -/
theorem Hypothesis.columnSum_mem_ZIrr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    (χ₂ : ((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2)) →* ℂˣ) :
    OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂ ∈ ZIrr ↥M := by
  haveI := hyp.finiteG
  classical
  rw [OddOrder.Peterfalvi.S06.columnSum_def]
  exact Submodule.sum_mem _
    (fun i _ => (((hyp.toHypothesis46 hG hG.odd).columnFamily χ₂).mu i).mem_ZIrr)

open scoped FiniteInduce in
/-- **Distinct certain-type column sums are orthogonal** (`⟨μ_j, μ_l⟩ = 0` for `χ₂ ≠ χ₂'`):
off-diagonal of the column Gram `columnFamily_mu_sum_inner`.  The `μ_old ⊥ μ_new` input of the
(9.11) chain fold. -/
theorem Hypothesis.columnSum_inner_columnSum_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    {χ₂ χ₂' : ((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2)) →* ℂˣ}
    (hne : χ₂ ≠ χ₂') :
    ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂)
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂') = 0 := by
  haveI := hyp.finiteG
  classical
  rw [OddOrder.Peterfalvi.S06.columnSum_def, OddOrder.Peterfalvi.S06.columnSum_def,
    OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner]
  exact if_neg hne

open scoped FiniteInduce in
/-- **A nontrivial μ-grid column sum is an induced-family member** (`hdk1`-free form via the
(11.8.1) degree separation): for `k ≠ 0` and `d ≢ 1` (the caseB column degree `d = u > 1`,
supplied as `hdne1` through `params.degree_independent`), the column sum
`∑ᵢ muGrid i k = columnSum (muColumnChar k)` lies in `S = inducedFamily M`.  Feeds the
scaled-difference support machinery of the (9.11) chain fold (`μ_old − χ₁` is `A₀`-supported). -/
theorem Hypothesis.columnSum_muColumnChar_mem_inducedFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hdne1 : ((params.d : ℂ)) ≠ 1)
    {k : Fin hyp.w2} (hk0 : k ≠ 0) :
    OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd)
      (hyp.muColumnChar hG hG.odd k) ∈ inducedFamily M := by
  haveI := hyp.finiteG
  classical
  rw [← hyp.muGrid_columnSum_eq_columnSum hG hG.odd k]
  refine hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd k ?_
  -- `muGrid 0 k (1) = d ≠ 1`
  intro h1
  apply hdne1
  rw [← h1, ← hmu]
  exact (params.degree_independent 0 k hk0).symm

open scoped FiniteInduce in
/-- **Certain-type column sums are injective in the `W₂`-dual** (`columnSum χ₂ = columnSum χ₂' →
χ₂ = χ₂'`): if the sums agree, the Gram `columnFamily_mu_sum_inner` evaluates their inner product
both as `w₁ ≠ 0` (diagonal) and as `0` if `χ₂ ≠ χ₂'` — forcing equality.  Turns the set-level
distinctness `μ_new ∉ pairUnion` into dual-level distinctness for the (9.11) chain fold. -/
theorem Hypothesis.columnSum_injective [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    {χ₂ χ₂' : ((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2)) →* ℂˣ}
    (heq : OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂
      = OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂') :
    χ₂ = χ₂' := by
  haveI := hyp.finiteG
  classical
  by_contra hne
  have h0 := hyp.columnSum_inner_columnSum_eq_zero hG (χ₂ := χ₂) (χ₂' := χ₂') hne
  rw [heq] at h0
  have hw1 : ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂')
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂')
      = (Nat.card (hyp.toHypothesis46 hG hG.odd).W1 : ℂ) := by
    rw [OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl]
  rw [h0] at hw1
  exact Nat.cast_ne_zero.mpr Nat.card_pos.ne' hw1.symm

end OddOrder.Peterfalvi.S12
