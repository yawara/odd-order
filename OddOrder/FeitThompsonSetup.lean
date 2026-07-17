import OddOrder.FeitThompsonSection16Core

/-!
# Feit–Thompson Section 16 character-grid setup

Peterfalvi §§3–13 (pp. 5–68): alignment API for the canonical type-`P`
maximal pair and its `S`/`T` character grids.
-/

namespace OddOrder

open OddOrder.BG
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.RepresentationTheory
open scoped Pointwise

universe u

section
open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)

/-- `W₁` of `certainTypeS` is `mp.K.subgroupOf mp.S` (the κ-Hall factor of `S`). -/
theorem certainTypeS_W1_eq : (mp.certainTypeS hG).W1 = mp.K.subgroupOf mp.S := by
  unfold Section16MaximalPair.certainTypeS certainTypeHypothesis_of_typeP_kappaHall; rfl

/-- `W₂` of `certainTypeS` is `mp.Kstar.subgroupOf mp.S` (the dual factor of `S`). -/
theorem certainTypeS_W2_eq : (mp.certainTypeS hG).W2 = mp.Kstar.subgroupOf mp.S := by
  unfold Section16MaximalPair.certainTypeS certainTypeHypothesis_of_typeP_kappaHall; rfl

/-- `K` of `certainTypeS` is `(derivedInG mp.S).subgroupOf mp.S` (the (4.2) convention `K = S'`;
same literal field as the `Sdata`-instance `typePData_toS06Hypothesis`, so the two §6 Hypothesis
instances of `S` share `K` on the nose — issue 2038 `hyp46Smp` shortcut). -/
theorem certainTypeS_K_eq :
    (mp.certainTypeS hG).K = (derivedInG mp.S).subgroupOf mp.S := by
  unfold Section16MaximalPair.certainTypeS certainTypeHypothesis_of_typeP_kappaHall; rfl

include hG in
/-- `mp.Kstar ≤ mp.S` (it lies in `S ∩ T = K ⊔ K*`). -/
theorem kstar_le_S : mp.Kstar ≤ mp.S := by
  obtain ⟨hWjoin, -, -, -⟩ := mp.W_structure hG
  have : mp.Kstar ≤ mp.S ⊓ mp.T := by rw [hWjoin]; exact le_sup_right
  exact this.trans inf_le_left

variable (tp : Section16TypePStructure mp)

/-! #### The two §6 Hypothesis instances of `S` share their `W₁`/`W₂` (issue 2038)

The κ-Hall instance `mp.certainTypeS` (grid producer, `muS`) and the `Sdata`-instance
`typePData_toS06Hypothesis tp.Sdata` (the `hypothesis46OfTypePData`/engines side) carry
propositionally equal cyclic factors: `Sdata.W1 = tp.W1 = mp.K` and `Sdata.W2 = tp.W2 =
mp.Kstar`.  These equalities ground the per-`ω` rigidity identification of the two `μ`-grids
(`irreducibleCharacterFamily_eq_of_difference_eq`). -/

/-- `W₁` of the `Sdata`-instance §6 Hypothesis equals `certainTypeS`'s. -/
theorem sdataS06_W1_eq_certainTypeS
    (hHall : Nat.Coprime (Nat.card ↥(OddOrder.GroupTheory.derivedInG mp.S))
      (Nat.card ↥tp.Sdata.W1)) :
    (OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis tp.Sdata hG.odd hHall).W1
      = (mp.certainTypeS hG).W1 := by
  have hlhs : (OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis tp.Sdata hG.odd hHall).W1
      = tp.Sdata.W1.subgroupOf mp.S := by
    unfold OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis; rfl
  rw [hlhs, tp.Sdata_W1_eq, tp.W1_eq_K hG, certainTypeS_W1_eq]

/-- `W₂` of the `Sdata`-instance §6 Hypothesis equals `certainTypeS`'s. -/
theorem sdataS06_W2_eq_certainTypeS
    (hHall : Nat.Coprime (Nat.card ↥(OddOrder.GroupTheory.derivedInG mp.S))
      (Nat.card ↥tp.Sdata.W1)) :
    (OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis tp.Sdata hG.odd hHall).W2
      = (mp.certainTypeS hG).W2 := by
  have hlhs : (OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis tp.Sdata hG.odd hHall).W2
      = tp.Sdata.W2.subgroupOf mp.S := by
    unfold OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis; rfl
  rw [hlhs, tp.Sdata_W2_eq, tp.W2_eq_Kstar hG, certainTypeS_W2_eq]

/-- The joins `W = W₁ ⊔ W₂` of the two §6 Hypothesis instances of `S` coincide. -/
theorem sdataS06_W_join_eq_certainTypeS
    (hHall : Nat.Coprime (Nat.card ↥(OddOrder.GroupTheory.derivedInG mp.S))
      (Nat.card ↥tp.Sdata.W1)) :
    (OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis tp.Sdata hG.odd hHall).W1
        ⊔ (OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis tp.Sdata hG.odd hHall).W2
      = (mp.certainTypeS hG).W1 ⊔ (mp.certainTypeS hG).W2 := by
  rw [sdataS06_W1_eq_certainTypeS hG mp tp hHall, sdataS06_W2_eq_certainTypeS hG mp tp hHall]

/-- `|certainTypeS.W₁| = tp.q` (both are `|mp.K|`). -/
theorem cardCertainTypeS_W1 : Nat.card ↥(mp.certainTypeS hG).W1 = tp.q := by
  rw [certainTypeS_W1_eq hG mp, Nat.card_congr (Subgroup.subgroupOfEquivOfLe mp.K_le_S).toEquiv,
    ← tp.W1_eq_K hG, ← tp.q_eq_card_W1]

/-- `|certainTypeS.W₂| = tp.p` (both are `|mp.Kstar|`). -/
theorem cardCertainTypeS_W2 : Nat.card ↥(mp.certainTypeS hG).W2 = tp.p := by
  rw [certainTypeS_W2_eq hG mp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (kstar_le_S hG mp)).toEquiv,
    ← tp.W2_eq_Kstar hG, ← tp.p_eq_card_W2]

/-! ### T-side mirror of the S-side identification infrastructure (cd `nu_definition`, step D)

The partner `mp.T` carries the `certain-type` Hypothesis `certainTypeT` with the roles of the two
factors swapped (`W₁ = mp.Kstar`, `W₂ = mp.K`).  These lemmas mirror the S-side
(`certainTypeS_W1_eq`, …, `gridEquivE_mem_W2`) and supply the `↥tp.W ≃* ↥(certainTypeT.sdiff.W)`
transport used to express the same `ω`-grid through `certainTypeT` (the S/T-shared-`ω` symmetry). -/

/-- `W₁` of `certainTypeT` is `mp.Kstar.subgroupOf mp.T` (the κ-Hall factor of `T`; the roles of the
two factors swap for the partner). -/
theorem certainTypeT_W1_eq : (mp.certainTypeT hG).W1 = mp.Kstar.subgroupOf mp.T := by
  unfold Section16MaximalPair.certainTypeT certainTypeHypothesis_of_typeP_kappaHall; rfl

/-- `W₂` of `certainTypeT` is `mp.K.subgroupOf mp.T` (the dual factor of `T`). -/
theorem certainTypeT_W2_eq : (mp.certainTypeT hG).W2 = mp.K.subgroupOf mp.T := by
  unfold Section16MaximalPair.certainTypeT certainTypeHypothesis_of_typeP_kappaHall; rfl

/-- `K` of `certainTypeT` is `(derivedInG mp.T).subgroupOf mp.T` (the (4.2) convention
`K = T'`). -/
theorem certainTypeT_K_eq :
    (mp.certainTypeT hG).K = (derivedInG mp.T).subgroupOf mp.T := by
  unfold Section16MaximalPair.certainTypeT certainTypeHypothesis_of_typeP_kappaHall; rfl

include hG in
/-- `mp.K ≤ mp.T` (it lies in `S ∩ T = K ⊔ K*`). -/
theorem k_le_T : mp.K ≤ mp.T := by
  obtain ⟨hWjoin, -, -, -⟩ := mp.W_structure hG
  have : mp.K ≤ mp.S ⊓ mp.T := by rw [hWjoin]; exact le_sup_left
  exact this.trans inf_le_right

/-- `|certainTypeT.W₁| = tp.p` (both are `|mp.Kstar|`). -/
theorem cardCertainTypeT_W1 : Nat.card ↥(mp.certainTypeT hG).W1 = tp.p := by
  rw [certainTypeT_W1_eq hG mp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe mp.Kstar_le_T).toEquiv,
    ← tp.W2_eq_Kstar hG, ← tp.p_eq_card_W2]

/-- `|certainTypeT.W₂| = tp.q` (both are `|mp.K|`). -/
theorem cardCertainTypeT_W2 : Nat.card ↥(mp.certainTypeT hG).W2 = tp.q := by
  rw [certainTypeT_W2_eq hG mp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (k_le_T hG mp)).toEquiv,
    ← tp.W1_eq_K hG, ← tp.q_eq_card_W1]

include hG in
/-- The key subgroup identity (T-side): `tp.W.subgroupOf mp.T = certainTypeT.sdiff.W`.  Both equal
`(mp.Kstar ⊔ mp.K).subgroupOf mp.T` (`tp.W = mp.K ⊔ mp.Kstar` and `certainTypeT.sdiff.W = W₁ ⊔ W₂`). -/
theorem tpW_subgroupOf_T_eq :
    tp.W.subgroupOf mp.T = (mp.certainTypeT hG).sdiffTICyclicHypothesis.W := by
  change tp.W.subgroupOf mp.T = (mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2
  rw [certainTypeT_W1_eq hG mp, certainTypeT_W2_eq hG mp,
    ← Subgroup.subgroupOf_sup mp.Kstar_le_T (k_le_T hG mp), sup_comm, ← tp.W_eq_kappa_join hG]

/-- The `W`-identification equiv (T-side) `↥tp.W ≃* ↥(certainTypeT.sdiff.W)`: `tp.W ≃ tp.W.subgroupOf
mp.T` then transported along `tpW_subgroupOf_T_eq`.  Mirrors `gridEquivE` with `inf_le_right`. -/
noncomputable def gridEquivE_T :
    ↥tp.W ≃* ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W :=
  (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_right)).symm.trans
    (MulEquiv.subgroupCongr (tpW_subgroupOf_T_eq hG mp tp))

/-- **`gridEquivE_T` preserves the underlying `G`-element** (composite of the element-preserving
`subgroupOfEquivOfLe` and `subgroupCongr`). -/
theorem gridEquivE_T_coe (w : ↥tp.W) :
    (((gridEquivE_T hG mp tp w : ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W) :
        ↥mp.T) : G) = (w : G) := rfl

/-- A `tp.W`-element lying in `mp.Kstar` transports under `gridEquivE_T` into `certainTypeT.W1`
(`= mp.Kstar.subgroupOf mp.T`). -/
theorem gridEquivE_T_mem_W1 (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    gridEquivE_T hG mp tp w ∈ ((mp.certainTypeT hG).W1).subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf, certainTypeT_W1_eq hG mp, Subgroup.mem_subgroupOf, gridEquivE_T_coe]
  exact hw

/-- A `tp.W`-element lying in `mp.K` transports under `gridEquivE_T` into `certainTypeT.W2`
(`= mp.K.subgroupOf mp.T`). -/
theorem gridEquivE_T_mem_W2 (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    gridEquivE_T hG mp tp w ∈ ((mp.certainTypeT hG).W2).subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf, certainTypeT_W2_eq hG mp, Subgroup.mem_subgroupOf, gridEquivE_T_coe]
  exact hw

/-- `Fin tp.q ≃ Fin |certainTypeS.W₁|`, fixing `0 ↦ 0` (so the (13.1.e) anchor `⟨0, q_prime.pos⟩`
matches `chiColumn`'s distinguished base index). -/
noncomputable def eqQ : Fin tp.q ≃ Fin (Nat.card ↥(mp.certainTypeS hG).W1) :=
  finCongr (cardCertainTypeS_W1 hG mp tp).symm

/-- The base `W₂`-column enumeration `Fin tp.p ≃ Ŵ₂` (Pontryagin: `|Ŵ₂| = |W₂| = tp.p`).  Stated in
the `sdiffTICyclicHypothesis.W₂/W` forms (defeq to `certainTypeS.W₂` / `W₁ ⊔ W₂`) so that both
`chiColumn` and `card_charGroup_subgroupOf` consume it directly.  An arbitrary bijection; the column-`0`
normalization is applied in `chi2enum`. -/
theorem cardChi2CharGroup :
    Nat.card (((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ) = tp.p := by
  rw [(mp.certainTypeS hG).sdiffTICyclicHypothesis.card_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W]
  exact cardCertainTypeS_W2 hG mp tp

/-- The `W₂`-column enumeration `Fin tp.p ≃ Ŵ₂`, realized as the **power enumeration** `j ↦ γ^j`
of a fixed generator `γ` of the cyclic dual (`S05.isCyclic_charGroup_subgroupOf` +
`cardCertainTypeS_W2`: `|Ŵ₂| = |W₂| = p`), mirroring the `w1CharEquiv` convention: column `0` is
the trivial character (`chi2enum_zero`, the `j = 0` base of the `nu_definition` T-side
difference), and column negation is character inversion (`chi2enum_finNeg`) — the honest (3.9.a)
grid pairing (issue 3002).  The `muS_definition` proof fixes the column `j` and is invariant
under the choice of column enumeration. -/
noncomputable def chi2enum :
    Fin tp.p ≃ (((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ) := by
  haveI := (mp.certainTypeS hG).sdiffTICyclicHypothesis.isCyclic_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W
  exact OddOrder.Peterfalvi.S06.cyclicPowEnum (cardChi2CharGroup hG mp tp)

/-- The normalized column enumeration sends column `0` to the trivial character (Peterfalvi's
column-`0` convention; the `j = 0` base of `nu_definition`). -/
@[simp] theorem chi2enum_zero : chi2enum hG mp tp ⟨0, tp.p_prime.pos⟩ = 1 := by
  haveI := (mp.certainTypeS hG).sdiffTICyclicHypothesis.isCyclic_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W
  rw [chi2enum, OddOrder.Peterfalvi.S06.cyclicPowEnum_apply]
  simp

/-- **Column negation is character inversion** (Peterfalvi (3.5)/(3.9.a) power-grid pairing,
`W₂`-column half): `chi2enum ((p − j) % p) = (chi2enum j)⁻¹`. -/
theorem chi2enum_finNeg (j : Fin tp.p) :
    chi2enum hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
      = (chi2enum hG mp tp j)⁻¹ := by
  haveI := (mp.certainTypeS hG).sdiffTICyclicHypothesis.isCyclic_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W
  rw [chi2enum]
  refine OddOrder.Peterfalvi.S06.cyclicPowEnum_eq_inv_of_add_mod_eq_zero _ ?_
  change ((tp.p - (j : ℕ)) % tp.p + (j : ℕ)) % tp.p = 0
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
  · simp [h0]
  · have hj : (j : ℕ) < tp.p := j.2
    rw [Nat.mod_eq_of_lt (by omega : tp.p - (j : ℕ) < tp.p),
      Nat.sub_add_cancel hj.le, Nat.mod_self]

include hG in
/-- The key subgroup identity: `tp.W.subgroupOf mp.S = certainTypeS.sdiff.W`.  Both equal
`(mp.K ⊔ mp.Kstar).subgroupOf mp.S` (`tp.W = mp.K ⊔ mp.Kstar` and `certainTypeS.sdiff.W = W₁ ⊔ W₂`). -/
theorem tpW_subgroupOf_eq :
    tp.W.subgroupOf mp.S = (mp.certainTypeS hG).sdiffTICyclicHypothesis.W := by
  change tp.W.subgroupOf mp.S = (mp.certainTypeS hG).W1 ⊔ (mp.certainTypeS hG).W2
  rw [certainTypeS_W1_eq hG mp, certainTypeS_W2_eq hG mp,
    ← Subgroup.subgroupOf_sup mp.K_le_S (kstar_le_S hG mp), tp.W_eq_kappa_join hG]

/-- The `W`-identification equiv `↥tp.W ≃* ↥(certainTypeS.sdiff.W)`: `tp.W ≃ tp.W.subgroupOf mp.S`
then transported along `tpW_subgroupOf_eq`.  The `≤` proof is the *same term* as in
`Section16CharacterData.mu_definition`. -/
noncomputable def gridEquivE :
    ↥tp.W ≃* ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W :=
  (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_left)).symm.trans
    (MulEquiv.subgroupCongr (tpW_subgroupOf_eq hG mp tp))

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

/-- S-side `ω`-grid: the `certainTypeS` `chiColumn` transported to `↥tp.W`. -/
noncomputable def omegaS (i : Fin tp.q) (j : Fin tp.p) : ClassFunction ↥tp.W ℂ :=
  ClassFunction.compHom (gridEquivE hG mp tp).toMonoidHom
    ((mp.certainTypeS hG).chiColumn (chi2enum hG mp tp j) (eqQ hG mp tp i) :
      ClassFunction ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W ℂ)

/-- S-side `μ`-grid: the (4.3.b) certain-type characters of `certainTypeS`. -/
noncomputable def muS (i : Fin tp.q) (j : Fin tp.p) : ClassFunction ↥mp.S ℂ :=
  (((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).mu (eqQ hG mp tp i) :
    ClassFunction ↥mp.S ℂ)

/-- S-side signs `δ`. -/
noncomputable def deltaS (j : Fin tp.p) : ℤ :=
  ((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).sign

/-- The `eqQ` reindex fixes the base index `0`. -/
theorem eqQ_zero : eqQ hG mp tp ⟨0, tp.q_prime.pos⟩ = 0 := by
  apply Fin.ext; simp [eqQ]

/-- **The S-side (13.1.e) `mu_definition` identity** — the cd producer's `mu_definition` field for the
S-side grid.  Inducing the transported `ω`-column difference `Ind_W^S(ω_{ij} − ω_{0j})` gives the
signed `μ`-difference `δ_j (μ_{ij} − μ_{0j})`, via `S06.induce_chiColumn_diff_mu_diff` after the
`compHom`/`subgroupCongr` transport collapse. -/
theorem muS_definition (i : Fin tp.q) (j : Fin tp.p) :
    ClassFunction.induce (tp.W.subgroupOf mp.S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_left)).toMonoidHom
          (omegaS hG mp tp i j - omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j))
      = (deltaS hG mp tp j : ℂ) • (muS hG mp tp i j - muS hG mp tp ⟨0, tp.q_prime.pos⟩ j) := by
  have key : ∀ k : Fin tp.q,
      ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_left)).toMonoidHom
          (omegaS hG mp tp k j)
        = ClassFunction.compHom (MulEquiv.subgroupCongr (tpW_subgroupOf_eq hG mp tp)).toMonoidHom
            ((mp.certainTypeS hG).chiColumn (chi2enum hG mp tp j) (eqQ hG mp tp k) :
              ClassFunction ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W ℂ) := by
    intro k
    rw [omegaS, ClassFunction.compHom_comp]
    congr 1
  rw [ClassFunction.compHom_sub, key i, key ⟨0, tp.q_prime.pos⟩, ← ClassFunction.compHom_sub,
    eqQ_zero hG mp tp, induce_compHom_subgroupCongr (tpW_subgroupOf_eq hG mp tp)]
  simp only [deltaS, muS, eqQ_zero hG mp tp, Int.cast_smul_eq_zsmul]
  exact (mp.certainTypeS hG).induce_chiColumn_diff_mu_diff (chi2enum hG mp tp j) (eqQ hG mp tp i)

/-- **Peterfalvi (9.8)/(9.11) reverse dichotomy at the `S`-instance certain-type grid** — the
producer supply for the `mu_reducible_dichotomy` field (issue 9092).  A *reducible* member of the
kernel-filter family `S(X)` over `S' = (derivedInG mp.S).subgroupOf mp.S` (any kernel demand `X`)
is a nonzero `μ`-column sum `∑ᵢ μ_{ij}`, `j ≠ 0`.  Mirrors the M-side
`Hypothesis.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` (`S12_HcBound`) at
`mp.certainTypeS hG`, using the identification `μ = columnFamily.mu` (`muS`) and the §6
reducibility criterion `induce_not_isIrreducible_iff` (the reducible source `θ = Ind_{S'}` is one
of the certain-type columns `χ_{j}`, whose column enumeration `chi2enum` supplies the `j`). -/
theorem muS_reducible_dichotomy {X : Subgroup ↥mp.S} {ψ : ClassFunction ↥mp.S ℂ}
    (hψ : ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG mp.S).subgroupOf mp.S) X)
    (hred : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ) :
    ∃ j : Fin tp.p, j ≠ ⟨0, tp.p_prime.pos⟩ ∧ ψ = ∑ i : Fin tp.q, muS hG mp tp i j := by
  classical
  haveI hcyc : IsCyclic ↥((mp.certainTypeS hG).W1 ⊔ (mp.certainTypeS hG).W2) :=
    (mp.certainTypeS hG).isCyclic_sup
  letI : CommGroup ↥((mp.certainTypeS hG).W1 ⊔ (mp.certainTypeS hG).W2) := IsCyclic.commGroup
  letI : Fintype ↥mp.S := Fintype.ofFinite _
  letI : Fintype ↥(mp.certainTypeS hG).K := Fintype.ofFinite _
  letI : Fintype ↥((mp.certainTypeS hG).W1 ⊔ (mp.certainTypeS hG).W2) := Fintype.ofFinite _
  obtain ⟨θ, hθne, hθker, rfl⟩ := hψ
  -- the μ-column sum is `Ind_{S'} χ_j` (reversing the `mu_colSum_eq_induce` identity)
  have hFk : ∀ j : Fin tp.p, (∑ i : Fin tp.q, muS hG mp tp i j)
      = ClassFunction.induce (mp.certainTypeS hG).K
          (((mp.certainTypeS hG).chiRestrict (chi2enum hG mp tp j) :
            ClassFunction ↥(mp.certainTypeS hG).K ℂ)) := by
    intro j
    rw [(mp.certainTypeS hG).coe_chiRestrict, (mp.certainTypeS hG).induce_restrict_certainType_eq]
    simp only [muS]
    exact Equiv.sum_comp (eqQ hG mp tp)
      (fun i' => (((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).mu i'
        : ClassFunction ↥mp.S ℂ))
  -- the reducible source `θ` is a §6 column `χ_j`
  obtain ⟨χ₂', hχ₂'⟩ := ((mp.certainTypeS hG).induce_not_isIrreducible_iff θ).mp hred
  have hχ₂'ne : χ₂' ≠ 1 := by
    rintro rfl
    rw [(mp.certainTypeS hG).chiRestrict_one_eq_trivial] at hχ₂'
    exact hθne hχ₂'.symm
  refine ⟨(chi2enum hG mp tp).symm χ₂', ?_, ?_⟩
  · intro h0
    apply hχ₂'ne
    calc χ₂' = chi2enum hG mp tp ((chi2enum hG mp tp).symm χ₂') :=
          (Equiv.apply_symm_apply _ _).symm
      _ = chi2enum hG mp tp ⟨0, tp.p_prime.pos⟩ := by rw [h0]
      _ = 1 := chi2enum_zero hG mp tp
  · rw [hFk, Equiv.apply_symm_apply, hχ₂']
    -- `(mp.certainTypeS hG).K` is defeq `(derivedInG mp.S).subgroupOf mp.S` (`certainTypeS_K_eq`)
    exact rfl

/-- **A linear character of `↥tp.W` is determined by its restrictions to `tp.W1` and `tp.W2`.**
Since `tp.W = tp.W1 ⊔ tp.W2` is an internal product of two commuting subgroups, every `w : ↥tp.W`
factors as `w = a * b` with `a ∈ tp.W1`, `b ∈ tp.W2`; two monoid homs agreeing on `tp.W1` and `tp.W2`
therefore agree everywhere.  This is the generating-set half of the S/T-shared-`ω` symmetry. -/
theorem monoidHom_eq_of_eqOn_W1_W2 {χ χ' : ↥tp.W →* ℂˣ}
    (h1 : ∀ w : ↥tp.W, (w : G) ∈ tp.W1 → χ w = χ' w)
    (h2 : ∀ w : ↥tp.W, (w : G) ∈ tp.W2 → χ w = χ' w) :
    χ = χ' := by
  haveI := tp.W_cyclic
  letI : CommGroup ↥tp.W := IsCyclic.commGroup
  have hW1le : tp.W1 ≤ tp.W := by rw [tp.W_eq_join]; exact le_sup_left
  have hW2le : tp.W2 ≤ tp.W := by rw [tp.W_eq_join]; exact le_sup_right
  have htop : (tp.W1.subgroupOf tp.W) ⊔ (tp.W2.subgroupOf tp.W) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← tp.W_eq_join, Subgroup.subgroupOf_self]
  ext w
  have hmem : w ∈ (tp.W1.subgroupOf tp.W) ⊔ (tp.W2.subgroupOf tp.W) := htop ▸ Subgroup.mem_top w
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  rw [← hab, map_mul, map_mul, h1 a (Subgroup.mem_subgroupOf.mp ha),
    h2 b (Subgroup.mem_subgroupOf.mp hb)]

/-- **`gridEquivE` preserves the underlying `G`-element.**  It is the composite of the
element-preserving subgroup equivs `subgroupOfEquivOfLe` and `subgroupCongr`, so transporting
`w : ↥tp.W` into `certainTypeS`'s `W` does not move the ambient group element. -/
theorem gridEquivE_coe (w : ↥tp.W) :
    (((gridEquivE hG mp tp w : ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W) :
        ↥mp.S) : G) = (w : G) := rfl

/-- A `tp.W`-element lying in `mp.K` transports under `gridEquivE` into `certainTypeS.W1`
(`= mp.K.subgroupOf mp.S`). -/
theorem gridEquivE_mem_W1 (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    gridEquivE hG mp tp w ∈ ((mp.certainTypeS hG).W1).subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf, certainTypeS_W1_eq hG mp, Subgroup.mem_subgroupOf, gridEquivE_coe]
  exact hw

/-- A `tp.W`-element lying in `mp.Kstar` transports under `gridEquivE` into `certainTypeS.W2`
(`= mp.Kstar.subgroupOf mp.S`). -/
theorem gridEquivE_mem_W2 (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    gridEquivE hG mp tp w ∈ ((mp.certainTypeS hG).W2).subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf, certainTypeS_W2_eq hG mp, Subgroup.mem_subgroupOf, gridEquivE_coe]
  exact hw

/-- **The S-side (4.3.c) value identity** (Coq `prTIirr_id`, `PFsection4.v:403`) — the cd
producer's `mu_apply_of_not_mem_W2` field: on `W ∖ W₂` the `μ`-grid is the signed `ω`-grid,
`μ_{ij}(w) = δ_j·ω_{ij}(w)`.  The §6 value identity `certainType_apply_eq_of_mem_V` at
`certainTypeS` (Dade-free, base-`Hypothesis` level), with the `sdiff.V`-membership built from
`tpW_subgroupOf_eq`/`certainTypeS_W2_eq` and the `chiColumn`/`omegaS` transport collapsing
along `gridEquivE` (`gridEquivE_coe` is `rfl`). -/
theorem muS_apply_of_not_mem_W2 (i : Fin tp.q) (j : Fin tp.p) (w : G) (hwW : w ∈ tp.W)
    (hwS : w ∈ mp.S) (hw2 : w ∉ (tp.W2 : Set G)) :
    muS hG mp tp i j ⟨w, hwS⟩
      = (deltaS hG mp tp j : ℂ) * omegaS hG mp tp i j ⟨w, hwW⟩ := by
  have hjoin : (⟨w, hwS⟩ : ↥mp.S) ∈ (mp.certainTypeS hG).sdiffTICyclicHypothesis.W := by
    rw [← tpW_subgroupOf_eq hG mp tp]
    exact Subgroup.mem_subgroupOf.mpr hwW
  have hnot : (⟨w, hwS⟩ : ↥mp.S) ∉ ((mp.certainTypeS hG).W2 : Set ↥mp.S) := by
    intro hmem
    apply hw2
    rw [tp.W2_eq_Kstar hG]
    have hks := (certainTypeS_W2_eq hG mp) ▸ hmem
    exact Subgroup.mem_subgroupOf.mp hks
  have hv : (⟨w, hwS⟩ : ↥mp.S) ∈ (mp.certainTypeS hG).sdiffTICyclicHypothesis.V :=
    ⟨SetLike.mem_coe.mpr hjoin, hnot⟩
  have h43c := (mp.certainTypeS hG).certainType_apply_eq_of_mem_V
    (chi2enum hG mp tp j) (eqQ hG mp tp i) hv
  refine (show muS hG mp tp i j ⟨w, hwS⟩
      = (((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).mu (eqQ hG mp tp i) :
          ClassFunction ↥mp.S ℂ) ⟨w, hwS⟩ from rfl).trans (h43c.trans ?_)
  rw [omegaS, ClassFunction.compHom_apply]
  show (((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).sign : ℂ) * _
      = (deltaS hG mp tp j : ℂ) * _
  congr 1

/-- **Value of `certainTypeS`'s product character on a transported `mp.K`-element**: only the
`W₁`-factor `a` survives (`wFst` is the identity, `wSnd` is trivial, on a `W₁`-element).  This is the
`tp.W1`-restriction value used (with its `tp.W2` mirror) to discharge the S/T-shared-`ω` symmetry on
the generators via `monoidHom_eq_of_eqOn_W1_W2`. -/
theorem omegaProdCharS_apply_mem_K
    (a : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE hG mp tp w)
      = a ⟨gridEquivE hG mp tp w, gridEquivE_mem_W1 hG mp tp w hw⟩ := by
  have mem := gridEquivE_mem_W1 hG mp tp w hw
  have hfst : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst (gridEquivE hG mp tp w)
      = ⟨gridEquivE hG mp tp w, mem⟩ :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst_W1_subtype ⟨gridEquivE hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd (gridEquivE hG mp tp w) = 1 :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd_W1_subtype ⟨gridEquivE hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, mul_one]

/-- **Value of `certainTypeS`'s product character on a transported `mp.Kstar`-element**: only the
`W₂`-factor `b` survives.  The `tp.W2`-restriction mirror of `omegaProdCharS_apply_mem_K`. -/
theorem omegaProdCharS_apply_mem_Kstar
    (a : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE hG mp tp w)
      = b ⟨gridEquivE hG mp tp w, gridEquivE_mem_W2 hG mp tp w hw⟩ := by
  have mem := gridEquivE_mem_W2 hG mp tp w hw
  have hfst : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst (gridEquivE hG mp tp w) = 1 :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst_W2_subtype ⟨gridEquivE hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd (gridEquivE hG mp tp w)
      = ⟨gridEquivE hG mp tp w, mem⟩ :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd_W2_subtype ⟨gridEquivE hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, one_mul]

/-- **Value of `certainTypeT`'s product character on a transported `mp.K`-element**: since `mp.K` is
the `W₂`-factor of `T`, only the `W₂`-factor `b` survives.  The T-side mirror of
`omegaProdCharS_apply_mem_Kstar`. -/
theorem omegaProdCharT_apply_mem_K
    (a : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE_T hG mp tp w)
      = b ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W2 hG mp tp w hw⟩ := by
  have mem := gridEquivE_T_mem_W2 hG mp tp w hw
  have hfst : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst (gridEquivE_T hG mp tp w) = 1 :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst_W2_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd (gridEquivE_T hG mp tp w)
      = ⟨gridEquivE_T hG mp tp w, mem⟩ :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd_W2_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, one_mul]

/-- **Value of `certainTypeT`'s product character on a transported `mp.Kstar`-element**: since
`mp.Kstar` is the `W₁`-factor of `T`, only the `W₁`-factor `a` survives.  The T-side mirror of
`omegaProdCharS_apply_mem_K`. -/
theorem omegaProdCharT_apply_mem_Kstar
    (a : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE_T hG mp tp w)
      = a ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W1 hG mp tp w hw⟩ := by
  have mem := gridEquivE_T_mem_W1 hG mp tp w hw
  have hfst : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst (gridEquivE_T hG mp tp w)
      = ⟨gridEquivE_T hG mp tp w, mem⟩ :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst_W1_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd (gridEquivE_T hG mp tp w) = 1 :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd_W1_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, mul_one]

end Section16CharacterData
end
end OddOrder
