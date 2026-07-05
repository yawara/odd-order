/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_MaximalIII_IV_V_Core

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
      Set.ncard_diff (Set.subset_univ _), Set.ncard_univ, Set.ncard_singleton]
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

/-! ## (11.8.1): `d ≡ 1 (mod q)` and `δ = 1` -/

open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (11.8.1), the residue `d ≡ 1 (mod q)`** (§9 count, named obligation).  The common
degree `d = μ_{ij}(1)` of the (10.3) grid is `≡ 1 (mod w₁ = q)`.

The column sum `μ_1 = ∑_i μ_{i1}` is a reducible member of the §9 family `𝒮(H₀)`
(`muGrid_column_sum_mem_sOf_H0_and_reducible`), so it has degree `q·u = q·|Ū|` by (9.8.b)/(9.9.b)
(`reducible_mem_sOf_H0_apply_one_eq_qu`, both Clifford cases); its degree is also `w₁·d` by the
(10.3) grid (`degree_independent`, via `hmu`).  Cancelling `q = w₁` gives `d = |Ū|`, and
`|Ū| ≡ 1 (mod q)` is the chief-factor image of the Frobenius congruence
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
        AddSubmonoidClass.coe_finset_sum _ _]
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
  -- cancel `q = w₁`: `d = |Ū|`
  have hq : (hyp.toTypesIIIIIIVSetup htype hnt).q = hyp.w1 := rfl
  have hdu : params.d
      = (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u := by
    have hqu' : (hyp.w1 : ℂ) * (params.d : ℂ)
        = (((hyp.toTypesIIIIIIVSetup htype hnt).q
            * (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u : ℕ) : ℂ) := by
      rw [← hdeg]; exact hqu
    rw [hq] at hqu'
    push_cast at hqu'
    have hw1ne : (hyp.w1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
    exact_mod_cast mul_left_cancel₀ hw1ne hqu'
  -- `|Ū| ≡ 1 (mod w₁)` (Frobenius image congruence)
  rw [hdu]
  exact hyp.mkSection11CharacterData_u_modEq_one (hyp.toTypesIIIIIIVSetup htype hnt) chief hnt.1

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

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.1), `|S(HC)| = n`** (§9 count, named obligation).  The number of degree-`w₁`
irreducible members of `S = inducedFamily M` equals `n = (d − δ)/w₁ = (d − 1)/w₁`.  `S(HC) = S₁`
consists of the `(u − 1)/q` degree-`q = w₁` irreducible constituents of the constant-degree Frobenius
family `(U/C) ⋊ W₁`, so `|S(HC)| = (u − 1)/q = (d − 1)/w₁ = n` by (11.8.1).  This is the cardinality
matching the isometric coherent image (`exists_coherentImage_SHC`, `|R| = |S(HC)|`) to `n` — the sole
remaining §9-gated input of the `R`-data.  §9-gated: needs the Frobenius constituent count and
`caseB_degree_qu` (via `d = |Ū|`, `charParam_d_modEq_one`). -/
theorem Hypothesis.card_SHCSet_filter_eq_charParam_n [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd) :
    (Finset.univ.filter (fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ))).card = params.n := by
  sorry

end OddOrder.Peterfalvi.S12
