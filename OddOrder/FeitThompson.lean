import OddOrder.FeitThompsonSetup
import OddOrder.Peterfalvi.S13_TypeDetermination
import OddOrder.Peterfalvi.S15_HonestTypeP2A0

/-!
# TAIL

Prefix-split from `OddOrder.FeitThompson` (2000-line limit, issue 0103 第 2 パス).
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

variable (tp : Section16TypePStructure mp)

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]


/-! ### S/T-shared-`ω` symmetry: the T-side duals and the column identity (steps C/E/F)

The shared `ω`-grid (`= omegaS`) is re-expressed through `certainTypeT`'s certain-type machinery by
transporting the S-side index characters to the T-side along the `G`-element-preserving
`eTS : ↥certainTypeT.sdiff.W ≃* ↥certainTypeS.sdiff.W`.  The T-side column dual `colT i` (a `W₂_T = K`
character, depending only on `i`) and row dual `rowDualT j` (a `W₁_T = K*` character, depending only on
`j`) are the `W₂_T`/`W₁_T`-restrictions of the transported single-factor product characters; their
values on `mp.K`/`mp.Kstar` elements match the S-side index characters by the round-trip
`eTS (gridEquivE_T w) = gridEquivE w` and the step-B product-character evaluations. -/

/-- The `G`-element-preserving equiv `↥certainTypeT.sdiff.W ≃* ↥certainTypeS.sdiff.W` (via `↥tp.W`). -/
noncomputable def eTS :
    ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W ≃* ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W :=
  (gridEquivE_T hG mp tp).symm.trans (gridEquivE hG mp tp)

/-- The round-trip: `eTS` sends `gridEquivE_T w` back to `gridEquivE w` (same `tp.W`-element `w`). -/
theorem eTS_gridEquivE_T (w : ↥tp.W) :
    eTS hG mp tp (gridEquivE_T hG mp tp w) = gridEquivE hG mp tp w := by
  simp only [eTS, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- **T-side column dual** (`W₂_T = mp.K`): the `W₂_T`-restriction of the transported `i`-th `W₁_S`-dual
(trivial `W₂_S`-part).  Depends only on `i` by construction. -/
noncomputable def colT (i : Fin tp.q) :
    ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ :=
  (((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
        ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) 1).comp (eTS hG mp tp).toMonoidHom).comp
    ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W).subtype

/-- **T-side row dual** (`W₁_T = mp.Kstar`): the `W₁_T`-restriction of the transported `j`-th `W₂_S`-dual
(trivial `W₁_S`-part).  Depends only on `j` by construction. -/
noncomputable def rowDualT (j : Fin tp.p) :
    ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ :=
  (((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar 1 (chi2enum hG mp tp j)).comp
      (eTS hG mp tp).toMonoidHom).comp
    ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W).subtype

/-- `colT i` on a transported `mp.K`-element matches the S-side `W₁_S`-dual `w1CharEquiv (eqQ i)`. -/
theorem colT_apply_mem_K (i : Fin tp.q) (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    colT hG mp tp i ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W2 hG mp tp w hw⟩
      = (mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)
          ⟨gridEquivE hG mp tp w, gridEquivE_mem_W1 hG mp tp w hw⟩ := by
  rw [colT, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
      ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) 1
      (eTS hG mp tp (gridEquivE_T hG mp tp w)) = _
  rw [eTS_gridEquivE_T]
  exact omegaProdCharS_apply_mem_K hG mp tp _ 1 w hw

/-- `rowDualT j` on a transported `mp.Kstar`-element matches the S-side `W₂_S`-dual `chi2enum j`. -/
theorem rowDualT_apply_mem_Kstar (j : Fin tp.p) (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    rowDualT hG mp tp j ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W1 hG mp tp w hw⟩
      = chi2enum hG mp tp j ⟨gridEquivE hG mp tp w, gridEquivE_mem_W2 hG mp tp w hw⟩ := by
  rw [rowDualT, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar 1 (chi2enum hG mp tp j)
      (eTS hG mp tp (gridEquivE_T hG mp tp w)) = _
  rw [eTS_gridEquivE_T]
  exact omegaProdCharS_apply_mem_Kstar hG mp tp 1 _ w hw

/-- The base row dual is trivial (`chi2enum_zero` ⟹ `omegaProdChar 1 1 = 1`).  This is what makes the
`j = 0` column the distinguished trivial base of the T-side `chiColumn`. -/
theorem rowDualT_zero : rowDualT hG mp tp ⟨0, tp.p_prime.pos⟩ = 1 := by
  rw [rowDualT, chi2enum_zero, (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_one,
    MonoidHom.one_comp, MonoidHom.one_comp]

variable [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)]

/-- **T-side row index** (`Fin |certainTypeT.W₁|`): the `w1CharEquiv_T`-preimage of the row dual.  The
T-side `chiColumn` is indexed by `Fin |W₁_T|` with distinguished base `0`; `rowT j` is the index of the
`j`-th `K*`-column. -/
noncomputable def rowT (j : Fin tp.p) : Fin (Nat.card ↥(mp.certainTypeT hG).W1) :=
  (mp.certainTypeT hG).w1CharEquiv.symm (rowDualT hG mp tp j)

/-- The base row index is `0` (`rowDualT_zero` ⟹ `w1CharEquiv_T.symm 1 = 0`).  This makes the `j = 0`
column the distinguished trivial base of the T-side `chiColumn` (so `nu i 0 = (columnFamily _).mu 0`). -/
theorem rowT_zero : rowT hG mp tp ⟨0, tp.p_prime.pos⟩ = 0 := by
  rw [rowT, rowDualT_zero]
  exact (mp.certainTypeT hG).w1CharEquiv.symm_apply_eq.mpr
    ((mp.certainTypeT hG).w1CharEquiv_zero).symm

/-- **T-side `ω`-grid** through `certainTypeT`: the same shared `ω` re-expressed via `certainTypeT`'s
`chiColumn` with column dual `colT i` (`K`) and row index `rowT j` (`K*`).  By `omegaS_eq_omegaT` this
equals the S-side `omegaS`, so the cd `omega` field admits *both* induction identities. -/
noncomputable def omegaT (i : Fin tp.q) (j : Fin tp.p) : ClassFunction ↥tp.W ℂ :=
  ClassFunction.compHom (gridEquivE_T hG mp tp).toMonoidHom
    ((mp.certainTypeT hG).chiColumn (colT hG mp tp i) (rowT hG mp tp j) :
      ClassFunction ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W ℂ)

/-- **The S/T-shared-`ω` symmetry** (cd piece 3 crux): `omegaS i j = omegaT i j`.  Both are the linear
character `ω(Φ)` of `↥tp.W` for the *same* `Φ`: the S-side product character `ω_{ij}^S` and the T-side
product character `ω_{ij}^T` agree on the generating subgroups `tp.W₁ = mp.K` and `tp.W₂ = mp.Kstar`
(by the step-B evaluations and the matching of `colT`/`rowDualT` with the S-side index characters), so
they are equal as monoid homs (`monoidHom_eq_of_eqOn_W1_W2`), hence as linear characters. -/
theorem omegaS_eq_omegaT (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j = omegaT hG mp tp i j := by
  have hrow : (mp.certainTypeT hG).w1CharEquiv (rowT hG mp tp j) = rowDualT hG mp tp j := by
    rw [rowT, Equiv.apply_symm_apply]
  have key : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.omegaProdChar
          (rowDualT hG mp tp j) (colT hG mp tp i)).comp (gridEquivE_T hG mp tp).toMonoidHom
      = ((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
          ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) (chi2enum hG mp tp j)).comp
          (gridEquivE hG mp tp).toMonoidHom := by
    apply monoidHom_eq_of_eqOn_W1_W2
    · intro w hw
      rw [tp.W1_eq_K hG] at hw
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [omegaProdCharT_apply_mem_K hG mp tp _ _ w hw, colT_apply_mem_K hG mp tp i w hw]
      exact (omegaProdCharS_apply_mem_K hG mp tp _ _ w hw).symm
    · intro w hw
      rw [tp.W2_eq_Kstar hG] at hw
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [omegaProdCharT_apply_mem_Kstar hG mp tp _ _ w hw, rowDualT_apply_mem_Kstar hG mp tp j w hw]
      exact (omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hw).symm
  simp only [omegaS, omegaT, Peterfalvi.S06.Hypothesis.chiColumn,
    Peterfalvi.S05.TICyclicHypothesis.omega]
  rw [hrow, ClassFunction.compHom_linearIrreducibleCharacter,
    ClassFunction.compHom_linearIrreducibleCharacter, key]

/-- T-side `ν`-grid: the (4.3.b) certain-type characters of `certainTypeT`, with column dual `colT i`
(the `K`-dual fixed by `i`) and row index `rowT j` (the `K*`-direction). -/
noncomputable def nuT (i : Fin tp.q) (j : Fin tp.p) : ClassFunction ↥mp.T ℂ :=
  (((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).mu (rowT hG mp tp j) :
    ClassFunction ↥mp.T ℂ)

/-- T-side signs `δ'` (depending on `i`, the fixed column). -/
noncomputable def deltaPrimeT (i : Fin tp.q) : ℤ :=
  ((mp.certainTypeT hG).columnFamily (colT hG mp tp i)).sign

/-- **The T-side (13.1.e) `nu_definition` identity** — the cd producer's `nu_definition` field for the
shared `ω`-grid.  Inducing the transported `ω`-row difference `Ind_W^T(ω_{ij} − ω_{i0})` to `T` gives the
signed `ν`-difference `δ'_i (ν_{ij} − ν_{i0})`, via the symmetry `omegaS_eq_omegaT` (which rewrites the
shared `ω` through `certainTypeT`'s `chiColumn`) and `S06.induce_chiColumn_diff_mu_diff` (T-side) after
the `compHom`/`subgroupCongr` transport collapse.  The complete mirror of `muS_definition`. -/
theorem nuT_definition (i : Fin tp.q) (j : Fin tp.p) :
    ClassFunction.induce (tp.W.subgroupOf mp.T)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_right)).toMonoidHom
          (omegaS hG mp tp i j - omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩))
      = (deltaPrimeT hG mp tp i : ℂ) •
          (nuT hG mp tp i j - nuT hG mp tp i ⟨0, tp.p_prime.pos⟩) := by
  have key : ∀ l : Fin tp.p,
      ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_right)).toMonoidHom
          (omegaS hG mp tp i l)
        = ClassFunction.compHom (MulEquiv.subgroupCongr (tpW_subgroupOf_T_eq hG mp tp)).toMonoidHom
            ((mp.certainTypeT hG).chiColumn (colT hG mp tp i) (rowT hG mp tp l) :
              ClassFunction ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W ℂ) := by
    intro l
    rw [omegaS_eq_omegaT hG mp tp i l, omegaT, ClassFunction.compHom_comp]
    congr 1
  rw [ClassFunction.compHom_sub, key j, key ⟨0, tp.p_prime.pos⟩, ← ClassFunction.compHom_sub,
    rowT_zero hG mp tp, induce_compHom_subgroupCongr (tpW_subgroupOf_T_eq hG mp tp)]
  simp only [deltaPrimeT, nuT, rowT_zero hG mp tp, Int.cast_smul_eq_zsmul]
  exact (mp.certainTypeT hG).induce_chiColumn_diff_mu_diff (colT hG mp tp i) (rowT hG mp tp j)

/-! ### `tau3`: the real Dade σ-integral on `W = tp.W` (cd piece 5)

The integral character map `τ₃ : ClassFunction ↥tp.W →ₗ[ℤ] ClassFunction G` is the Peterfalvi (3.2)
σ-isometry of the **G-internal TI-cyclic structure** on `W = S ∩ T = mp.K ⊔ mp.Kstar`, supported on the
regular set `Ẑ = W \ (W₁ ∪ W₂)` (`= S14.zTilde mp.K mp.Kstar`).  It must be the genuine Dade map (not a
formal one): `η := τ₃ ∘ ω` is consumed downstream as a real virtual character (notes 更新¹⁷).  The TI-set
fact is read off the proven `BG §14 typeP_duality` (Theorem 14.7), and the Dade isometry from the
general §4 producer `S04.Hypothesis.fullDadeIsometryData` (all local `H(a) = ⊥`, so `HConjInvariant` is
automatic).  Named `tau3W` to avoid the `Section16CharacterData.tau3` field projection. -/

/-- The **G-internal TI-cyclic structure (3.1)** on `W = S ∩ T = mp.K ⊔ mp.Kstar`, supported on
the regular set `Ẑ = W ∖ (W₁ ∪ W₂)` (`= S14.zTilde mp.K mp.Kstar`); the TI-set fact is the proven
BG §14 `typeP_duality` (Theorem 14.7).  Extracted from `tau3W`'s local `let` as a top-level
definition so the (3.2) σ-isometry property package (`tau3W_isometry` etc., the issue-3002 grid
property supply) can be read off the `S05` lemmas. -/
noncomputable def tiCyclicW : OddOrder.Peterfalvi.S05.TICyclicHypothesis G :=
  { W := tp.W
    W1 := tp.W1
    W2 := tp.W2
    W1_le_W := by rw [tp.W_eq_join]; exact le_sup_left
    W2_le_W := by rw [tp.W_eq_join]; exact le_sup_right
    W1_nontrivial := by
      rw [tp.W1_eq_K hG]
      exact fun h => BG.Ch4.S14.card_kappaHall_ne_one mp.S_typeP mp.K_le_S mp.K_hall
        (Subgroup.card_eq_one.mpr h)
    W2_nontrivial := by
      rw [tp.W2_eq_Kstar hG]
      exact fun h => BG.Ch4.S14.card_kappaHall_ne_one mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
        (Subgroup.card_eq_one.mpr h)
    W_sup := tp.W_eq_join.symm
    W_disjoint := disjoint_iff.mpr tp.W1_inf_W2_eq_bot
    W_card_coprime := by
      rw [← tp.q_eq_card_W1, ← tp.p_eq_card_W2]
      exact (Nat.coprime_primes tp.q_prime tp.p_prime).mpr (ne_of_lt tp.q_lt_p)
    W_card_odd := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card tp.W)
    W_cyclic := tp.W_cyclic
    V := (tp.W : Set G) \ ((tp.W1 : Set G) ∪ (tp.W2 : Set G))
    V_subset_sharp := by
      rintro x hx
      rw [Set.mem_sdiff] at hx
      obtain ⟨_, hxni⟩ := hx
      simp only [Set.mem_union, SetLike.mem_coe, not_or] at hxni
      change x ∈ Set.univ \ ({1} : Set G)
      refine ⟨Set.mem_univ x, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact fun h => hxni.1 (h ▸ one_mem tp.W1)
    V_subset_W := Set.sdiff_subset
    W_normalizes_V := by
      intro w v hv
      have hvW : v ∈ tp.W := hv.1
      haveI := tp.W_cyclic
      letI : CommGroup ↥tp.W := IsCyclic.commGroup
      have hcg : (w : G) * v = v * (w : G) := by
        have h := mul_comm w (⟨v, hvW⟩ : ↥tp.W)
        have := congrArg (Subgroup.subtype tp.W) h
        simpa using this
      have heq : (w : G) * v * (w : G)⁻¹ = v := by rw [hcg]; group
      rw [heq]; exact hv
    V_ti := by
      -- The `Ẑ = zTilde` TI-set fact for the canonical pair (BG Theorem 14.7).
      have hZti : OddOrder.GroupTheory.IsTISubset (BG.Ch4.S14.zTilde mp.K mp.Kstar)
          (mp.K ⊔ mp.Kstar) := by
        obtain ⟨Mst, hMstP⟩ :=
          (BG.Ch4.S14.typeP_duality hG mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall
            mp.Kstar_eq).2.2.exists
        exact hMstP.2.2.2.2.2.1
      rw [tp.W_eq_kappa_join hG, tp.W1_eq_K hG, tp.W2_eq_Kstar hG]
      exact hZti }

/-- The full §4 Dade application for `tiCyclicW` (all local subgroups `H(a) = ⊥`, so
`HConjInvariant` is automatic). -/
noncomputable def tiCyclicWDadeApp :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (tiCyclicW hG mp tp) :=
  OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication.mk
    ((tiCyclicW hG mp tp).toDadeHypothesis.fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)))

/-- **The (3.2) Dade σ-integral on `W = tp.W`** (see the section header above): the σ-isometry of
`tiCyclicW`, re-viewed as an integral character map. -/
noncomputable def tau3W : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥tp.W G :=
  (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp)

/-! #### The (3.2) property package of `tau3W` (issue-3002 grid property supply)

Read off the `S05` σ-isometry lemmas through the extracted `tiCyclicW`/`tiCyclicWDadeApp`;
these discharge the `tau3_*` fields of `Section16CharacterData` (and hence of
`Section16Inputs` / `S15.Hypothesis`). -/

/-- **Peterfalvi (3.2), isometry part**: `tau3W` preserves the class-function inner product. -/
theorem tau3W_isometry :
    OddOrder.Peterfalvi.S07.IsIntegralIsometry (tau3W hG mp tp) :=
  (tiCyclicW hG mp tp).sigmaIntegral_isIntegralIsometry rfl (tiCyclicWDadeApp hG mp tp)

/-- **Peterfalvi (3.2)**: `tau3W` sends the trivial character to the trivial character. -/
theorem tau3W_trivial :
    tau3W hG mp tp (trivialClassFunction ↥tp.W) = trivialClassFunction G :=
  (tiCyclicW hG mp tp).sigmaIntegral_trivial rfl (tiCyclicWDadeApp hG mp tp)

/-- **Peterfalvi (3.2)**: `tau3W` sends virtual characters to virtual characters. -/
theorem tau3W_mem_ZIrr {z : ClassFunction ↥tp.W ℂ} (hz : z ∈ ZIrr ↥tp.W) :
    tau3W hG mp tp z ∈ ZIrr G :=
  (tiCyclicW hG mp tp).sigmaIntegral_mem_ZIrr rfl (tiCyclicWDadeApp hG mp tp) hz

/-- **Peterfalvi (3.2.c)**: on the regular set `W ∖ (W₁ ∪ W₂)` the map `tau3W` is the
identity. -/
theorem tau3W_apply_of_regular (α : ClassFunction ↥tp.W ℂ) (w : G) (hwW : w ∈ tp.W)
    (hnot : w ∉ (tp.W1 : Set G) ∪ (tp.W2 : Set G)) :
    tau3W hG mp tp α w = α ⟨w, hwW⟩ :=
  (tiCyclicW hG mp tp).sigmaIntegral_apply_of_mem_V rfl (tiCyclicWDadeApp hG mp tp) α
    (show w ∈ (tiCyclicW hG mp tp).V from ⟨hwW, hnot⟩)

/-! #### The (3.3)/(3.4) property package of `omegaS` (issue-3002 grid property supply)

The `omegaS` are distinct irreducible linear characters of `↥tp.W` — the `certainTypeS`
`chiColumn`s (S05 `omega ∘ omegaProdChar`, orthonormal by `omega_inner` and the injectivity of
the enumerations) transported along the group isomorphism `gridEquivE` (which preserves the
inner product, `ClassFunction.inner_compHom_mulEquiv`). -/

/-- **Peterfalvi (3.3)/(3.4)**: the S-side `ω`-grid is orthonormal. -/
theorem omegaS_inner (i k : Fin tp.q) (j l : Fin tp.p) :
    ClassFunction.inner (omegaS hG mp tp i j) (omegaS hG mp tp k l)
      = if i = k ∧ j = l then 1 else 0 := by
  rw [omegaS, omegaS, ClassFunction.inner_compHom_mulEquiv (gridEquivE hG mp tp)]
  simp only [Peterfalvi.S06.Hypothesis.chiColumn]
  rw [(mp.certainTypeS hG).sdiffTICyclicHypothesis.omega_inner]
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
  · have hne : (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
        ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) (chi2enum hG mp tp j)
        ≠ (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
          ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp k)) (chi2enum hG mp tp l) := by
      intro hc
      obtain ⟨h1, h2⟩ := (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_inj hc
      exact h ⟨(eqQ hG mp tp).injective ((mp.certainTypeS hG).w1CharEquiv_injective h1),
        (chi2enum hG mp tp).injective h2⟩
    rw [if_neg hne, if_neg h]

/-- **Peterfalvi (4.3.b), full-grid orthonormality of the S-side `μ`-grid** (issues 9076/9014):
`⟨μ_{ij}, μ_{kl}⟩ = [(i,j) = (k,l)]`.  Within a column by the (1.4) family injectivity; across
columns by the certain-type cross-column distinctness `columnFamily_mu_ne`. -/
theorem muS_orthonormal (i k : Fin tp.q) (j l : Fin tp.p) :
    ClassFunction.inner (muS hG mp tp i j) (muS hG mp tp k l)
      = if i = k ∧ j = l then 1 else 0 := by
  simp only [muS]
  rw [irreducibleCharacter_inner_eq_ite]
  by_cases hjl : j = l
  · subst hjl
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
    · rw [if_neg (fun hc => hik ((eqQ hG mp tp).injective
          ((((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).injective) hc))),
        if_neg (by simp [hik])]
  · rw [if_neg ((mp.certainTypeS hG).columnFamily_mu_ne
        (fun hc => hjl ((chi2enum hG mp tp).injective hc)) _ _),
      if_neg (by simp [hjl])]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **The type-`P₂` `Hypothesis46` on the `muS` producer instance** (issue 2038, the shortcut
that avoids the two-instance grid identification): a §6 `Hypothesis46 (A(S)) S` whose
`toHypothesis` is the κ-Hall instance `mp.certainTypeS` — the *same* instance whose
`columnFamily` is the `muS` grid — so the §6 certain-type engines
(`certainType_diff_supp_subset_A0`, `certainType_diff_dade_apply_eq_of_mem_V`) apply to `muS`
directly.  The `tic` reconciliations are the `W₁/W₂/K`-equalities of the two §6 instances
(`sdataS06_*`/`certainTypeS_*_eq`); the Dade data is the honest `'A0(S)`-Dade of
`dadeSupportHypothesisData_honestTypeP2A0Set`; the kernel-family subgroup is `M_σ(S)` with the
`A(S)`-covering of `mem_honestTypeP2ASet` (mirroring `S15.Hypothesis.hyp46S`). -/
noncomputable def hyp46Smp :
    OddOrder.Peterfalvi.S06.Hypothesis46
      (OddOrder.Peterfalvi.S15.honestTypeP2ASet mp.S) mp.S :=
  { toHypothesis := mp.certainTypeS hG
    dade := ((OddOrder.Peterfalvi.S15.dadeSupportHypothesisData_honestTypeP2A0Set hG
          mp.S_maximal mp.S_typeP2 tp.Sdata).some.dade).restrict Set.subset_union_left
        (fun l _ ha => OddOrder.Peterfalvi.S15.honestTypeP2ASet_conj_mem l.2 ha)
    tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis tp.Sdata hG.odd
    tic_W1 := by
      show tp.Sdata.W1 = _
      rw [certainTypeS_W1_eq, Subgroup.map_subgroupOf_eq_of_le mp.K_le_S,
        tp.Sdata_W1_eq, tp.W1_eq_K hG]
    tic_W2 := by
      show tp.Sdata.W2 = _
      rw [certainTypeS_W2_eq, Subgroup.map_subgroupOf_eq_of_le (kstar_le_S hG mp),
        tp.Sdata_W2_eq, tp.W2_eq_Kstar hG]
    tic_V := rfl
    subH := (OddOrder.BG.Ch3.S10.Msigma mp.S).subgroupOf mp.S
    subH_normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    W2_le_subH := by
      rw [certainTypeS_W2_eq, ← tp.W2_eq_Kstar hG, ← tp.Sdata_W2_eq]
      refine Subgroup.subgroupOf_mono mp.S ?_
      have hW2H : tp.Sdata.W2 ≤ tp.Sdata.H := le_trans tp.Sdata.W2_le inf_le_left
      rw [tp.Sdata.H_eq] at hW2H
      exact le_trans hW2H
        (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG mp.S_maximal)
    subH_le_K := by
      rw [certainTypeS_K_eq]
      exact Subgroup.subgroupOf_mono mp.S
        (OddOrder.BG.Ch3.S10.Msigma_le_derived hG mp.S_maximal)
    A_covers := by
      intro hh hhσ hh1 x hx hx1
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxC, hxD⟩ := hx
      rw [certainTypeS_K_eq, Subgroup.mem_subgroupOf] at hxD
      rw [Subgroup.mem_subgroupOf] at hhσ
      rw [Subgroup.mem_centralizer_iff] at hxC
      rw [OddOrder.Peterfalvi.S15.mem_honestTypeP2ASet]
      refine ⟨hxD, ?_, (hh : G), ⟨hhσ, ?_⟩, ?_⟩
      · simpa using hx1
      · simpa using hh1
      · rw [Subgroup.mem_centralizer_iff]
        rintro g rfl
        have hcomm := hxC (hh : ↥mp.S) rfl
        have := congrArg (mp.S.subtype) hcomm
        simpa using this
    dade0 := (OddOrder.Peterfalvi.S15.dadeSupportHypothesisData_honestTypeP2A0Set hG
        mp.S_maximal mp.S_typeP2 tp.Sdata).some.dade
    tau := ((OddOrder.Peterfalvi.S15.dadeSupportHypothesisData_honestTypeP2A0Set hG
          mp.S_maximal mp.S_typeP2 tp.Sdata).some.dade).fullDadeIsometryData
      (OddOrder.Peterfalvi.S15.dadeSupportHypothesisData_honestTypeP2A0Set hG
        mp.S_maximal mp.S_typeP2 tp.Sdata).some.hconj }

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **The Dade-free (4.6) core on the `muS` producer instance** (issue 9081): the structural
fields of `hyp46Smp` — the κ-Hall grid instance, `tic` reconciliations, `M_σ(S)` kernel family,
`A(S)`-covering, and the `L`-conjugation invariance of `A(S)`
(`honestTypeP2ASet_conj_mem`, honest) — **without** the Dade data.  The (4.7)/(4.8)-(1) support
engines (`certainType_diff_supp_subset_A0`) run on this core, so their producer applications
(`muS_diff_support`) stay clear of the `A₀(S)`-Dade existence pin
(`dadeSupportHypothesisData_honestTypeP2A0Set`, currently sorried) that `hyp46Smp` bundles. -/
noncomputable def hyp46SmpCore :
    OddOrder.Peterfalvi.S06.Hypothesis46Core
      (OddOrder.Peterfalvi.S15.honestTypeP2ASet mp.S) mp.S :=
  { toHypothesis := mp.certainTypeS hG
    L_normalizes_A := fun l _ ha => OddOrder.Peterfalvi.S15.honestTypeP2ASet_conj_mem l.2 ha
    tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis tp.Sdata hG.odd
    -- the structural proofs are verbatim copies of the `hyp46Smp` fields: citing the `hyp46Smp`
    -- projections instead would pull its (sorried) `A₀(S)`-Dade pin into this axiom closure.
    tic_W1 := by
      show tp.Sdata.W1 = _
      rw [certainTypeS_W1_eq, Subgroup.map_subgroupOf_eq_of_le mp.K_le_S,
        tp.Sdata_W1_eq, tp.W1_eq_K hG]
    tic_W2 := by
      show tp.Sdata.W2 = _
      rw [certainTypeS_W2_eq, Subgroup.map_subgroupOf_eq_of_le (kstar_le_S hG mp),
        tp.Sdata_W2_eq, tp.W2_eq_Kstar hG]
    tic_V := rfl
    subH := (OddOrder.BG.Ch3.S10.Msigma mp.S).subgroupOf mp.S
    subH_normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    W2_le_subH := by
      rw [certainTypeS_W2_eq, ← tp.W2_eq_Kstar hG, ← tp.Sdata_W2_eq]
      refine Subgroup.subgroupOf_mono mp.S ?_
      have hW2H : tp.Sdata.W2 ≤ tp.Sdata.H := le_trans tp.Sdata.W2_le inf_le_left
      rw [tp.Sdata.H_eq] at hW2H
      exact le_trans hW2H
        (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG mp.S_maximal)
    subH_le_K := by
      rw [certainTypeS_K_eq]
      exact Subgroup.subgroupOf_mono mp.S
        (OddOrder.BG.Ch3.S10.Msigma_le_derived hG mp.S_maximal)
    A_covers := by
      intro hh hhσ hh1 x hx hx1
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxC, hxD⟩ := hx
      rw [certainTypeS_K_eq, Subgroup.mem_subgroupOf] at hxD
      rw [Subgroup.mem_subgroupOf] at hhσ
      rw [Subgroup.mem_centralizer_iff] at hxC
      rw [OddOrder.Peterfalvi.S15.mem_honestTypeP2ASet]
      refine ⟨hxD, ?_, (hh : G), ⟨hhσ, ?_⟩, ?_⟩
      · simpa using hx1
      · simpa using hh1
      · rw [Subgroup.mem_centralizer_iff]
        rintro g rfl
        have hcomm := hxC (hh : ↥mp.S) rfl
        have := congrArg (mp.S.subtype) hcomm
        simpa using this }

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Peterfalvi (4.8) conclusion (1) on the `muS` grid** (Coq `prDade_sub_TIirr_on`; the
`(13.18)` support engine in producer vocabulary): for nontrivial equal-degree columns
`j, k ≠ 0`, the `μ`-column difference `μ_{ij} − μ_{ik}` is supported in
`A₀(S) = A(S) ∪ V^S`.  The §6 support engine `certainType_diff_supp_subset_A0` applied at the
Dade-free `hyp46SmpCore` (issue 9081), whose `toHypothesis` is the `muS` instance
`mp.certainTypeS` — no grid identification needed, and no `A₀(S)`-Dade pin in the closure. -/
theorem muS_diff_support (i : Fin tp.q) {j k : Fin tp.p}
    (hj0 : j ≠ ⟨0, tp.p_prime.pos⟩) (hk0 : k ≠ ⟨0, tp.p_prime.pos⟩)
    (hdeg : muS hG mp tp i j 1 = muS hG mp tp i k 1) :
    (muS hG mp tp i j - muS hG mp tp i k).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S15.honestTypeP2A0Set mp.S tp.Sdata) mp.S := by
  classical
  haveI : NeZero (Nat.card ↥(hyp46SmpCore hG mp tp).W1) :=
    inferInstanceAs (NeZero (Nat.card ↥(mp.certainTypeS hG).W1))
  have hχj : chi2enum hG mp tp j ≠ 1 := by
    intro hc
    exact hj0 ((chi2enum hG mp tp).injective (hc.trans (chi2enum_zero hG mp tp).symm))
  have hχk : chi2enum hG mp tp k ≠ 1 := by
    intro hc
    exact hk0 ((chi2enum hG mp tp).injective (hc.trans (chi2enum_zero hG mp tp).symm))
  intro z hz
  rw [OddOrder.RepresentationTheory.ClassFunction.mem_support] at hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  exact OddOrder.Peterfalvi.S06.certainType_diff_supp_subset_A0 (hyp46SmpCore hG mp tp)
    hχj hχk (eqQ hG mp tp i) hdeg hz

/-- The `omegaS` are linear characters: `ω_{ij}(1) = 1`. -/
theorem omegaS_apply_one (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j 1 = 1 := by
  rw [omegaS, ClassFunction.compHom_apply, map_one]
  exact (mp.certainTypeS hG).chiColumn_apply_one _ _

/-- Each `omegaS i j` is a virtual character of `↥tp.W` (the pullback along `gridEquivE` of an
irreducible character). -/
theorem omegaS_mem_ZIrr (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j ∈ ZIrr ↥tp.W := by
  rw [omegaS]
  exact ClassFunction.compHom_mem_ZIrr _
    ((mp.certainTypeS hG).chiColumn (chi2enum hG mp tp j) (eqQ hG mp tp i)).mem_ZIrr

/-! #### The (3.3) value semantics of `omegaS` (issue-2033 factorization supply)

Each `omegaS i j` is a *linear* character — its values are the monoid-hom values of
`omegaProdChar (w1CharEquiv (eqQ i)) (chi2enum j)` transported along `gridEquivE` — the
column-`0`/row-`0` normalizations are trivial on `W₂`/`W₁`, and the `W₁`- and `W₂`-values
are `q`-th and `p`-th roots of unity.  These five facts are the Peterfalvi (3.3) grid semantics
that the (1.10)-congruence atoms of the §13 norm cascade consume, threaded through the
matching fields of `Peterfalvi.S15.Hypothesis` (issue 2033, the 3002-pattern successor). -/

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.3), linearity** (issue 2033): each `ω_{ij}` is multiplicative — a linear
character of `W`.  Discharges the `omega_mul` field of `Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_mul (i : Fin tp.q) (j : Fin tp.p) (w w' : ↥tp.W) :
    omegaS hG mp tp i j (w * w') = omegaS hG mp tp i j w * omegaS hG mp tp i j w' := by
  simp only [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    map_mul, Units.val_mul]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.3), column-`0` normalization** (issue 2033): the column-`0` grid characters
`ω_{i0}` are trivial on `W₂` (`chi2enum 0 = 1` is the trivial `W₂`-dual).  Discharges the
`omega_col_zero_apply_of_mem_W2` field of `Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_col_zero_apply_of_mem_W2 (i : Fin tp.q) (w : ↥tp.W) (hw : (w : G) ∈ tp.W2) :
    omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩ w = 1 := by
  have hwK : (w : G) ∈ mp.Kstar := tp.W2_eq_Kstar hG ▸ hw
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK, chi2enum_zero]
  exact Units.val_one

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.3), row-`0` normalization** (issue 2033): the row-`0` grid characters
`ω_{0j}` are trivial on `W₁` (`w1CharEquiv 0 = 1` is the trivial `W₁`-dual).  Discharges the
`omega_row_zero_apply_of_mem_W1` field of `Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_row_zero_apply_of_mem_W1 (j : Fin tp.p) (w : ↥tp.W) (hw : (w : G) ∈ tp.W1) :
    omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j w = 1 := by
  have hwK : (w : G) ∈ mp.K := tp.W1_eq_K hG ▸ hw
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK, eqQ_zero hG mp tp,
    (mp.certainTypeS hG).w1CharEquiv_zero]
  exact Units.val_one

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.3), `W₁`-value order** (issue 2033): on `W₁` the grid values are `q`-th
roots of unity — the `W₂`-factor is trivial there and the `W₁`-factor character has order
dividing `|W₁| = q`.  Discharges the `omega_pow_q_of_mem_W1` field of
`Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_pow_q_of_mem_W1 (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ tp.W1) :
    omegaS hG mp tp i j w ^ tp.q = 1 := by
  have hwK : (w : G) ∈ mp.K := tp.W1_eq_K hG ▸ hw
  have mem := gridEquivE_mem_W1 hG mp tp w hwK
  have hcard : Nat.card ↥((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) = tp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W1_le_W).toEquiv]
    exact cardCertainTypeS_W1 hG mp tp
  have hx : (⟨gridEquivE hG mp tp w, mem⟩ :
      ↥((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W)) ^ tp.q = 1 := by
    rw [← hcard]; exact pow_card_eq_one'
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK, ← Units.val_pow_eq_pow_val, ← map_pow,
    hx, map_one, Units.val_one]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.3), `W₂`-value order** (issue 2033): on `W₂` the grid values are `p`-th
roots of unity — the `W₁`-factor is trivial there and the `W₂`-factor character has order
dividing `|W₂| = p`.  Discharges the `omega_pow_p_of_mem_W2` field of
`Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_pow_p_of_mem_W2 (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ tp.W2) :
    omegaS hG mp tp i j w ^ tp.p = 1 := by
  have hwK : (w : G) ∈ mp.Kstar := tp.W2_eq_Kstar hG ▸ hw
  have mem := gridEquivE_mem_W2 hG mp tp w hwK
  have hcard : Nat.card ↥((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) = tp.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W).toEquiv]
    exact cardCertainTypeS_W2 hG mp tp
  have hx : (⟨gridEquivE hG mp tp w, mem⟩ :
      ↥((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W)) ^ tp.p = 1 := by
    rw [← hcard]; exact pow_card_eq_one'
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK, ← Units.val_pow_eq_pow_val, ← map_pow,
    hx, map_one, Units.val_one]

/-! #### The (3.2.d) completeness of the `η`-grid (issue-2034 supply)

The `omegaS`-family is `pq` *distinct* linear characters of the `pq`-element cyclic `↥tp.W`,
hence exhausts them; through `sigma_omega` the `η`-grid `tau3W (omegaS i j)` therefore
enumerates the whole `(3.5)` family `χ_{ab}`, and the S05 completeness
(`eq_zero_of_mem_V_of_inner_chiFam_eq_zero`) transfers: any class function of `G` orthogonal
to the whole `η`-grid vanishes on the regular set `Ŵ`. -/

/-- The underlying linear character of `omegaS i j`, as a monoid hom of `↥tp.W`. -/
noncomputable def omegaSChar (i : Fin tp.q) (j : Fin tp.p) : ↥tp.W →* ℂˣ :=
  ((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
    ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) (chi2enum hG mp tp j)).comp
    (gridEquivE hG mp tp).toMonoidHom

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- `omegaS i j` is the `tiCyclicW`-grid character of its underlying hom. -/
theorem omegaS_eq_omega_omegaSChar (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j
      = ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j)).toClassFunction := by
  ext w
  simp only [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaSChar, MonoidHom.comp_apply]
  rfl

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- The row-axis underlying character is the corresponding power of the first
nonprincipal row character. -/
theorem omegaSChar_row_eq_pow (i : Fin tp.q) :
    omegaSChar hG mp tp i ⟨0, tp.p_prime.pos⟩ =
      omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩ ^ (i : ℕ) := by
  let χ := (mp.certainTypeS hG).w1CharEquiv
    (eqQ hG mp tp ⟨1, tp.q_prime.one_lt⟩)
  have hpow : (mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i) = χ ^ (i : ℕ) := by
    simp [χ, OddOrder.Peterfalvi.S06.Hypothesis.w1CharEquiv,
      OddOrder.Peterfalvi.S06.cyclicPowEnum_apply, eqQ]
  unfold omegaSChar
  rw [chi2enum_zero, hpow, (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_right,
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_right]
  apply MonoidHom.ext
  intro w
  simp only [MonoidHom.comp_apply]
  exact (MonoidHom.pow_apply χ (i : ℕ) _).trans
    (MonoidHom.pow_apply
      ((χ.comp (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst).comp
        (gridEquivE hG mp tp).toMonoidHom)
      (i : ℕ) w).symm

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- The column-axis underlying character is the corresponding power of the first
nonprincipal column character. -/
theorem omegaSChar_column_eq_pow (j : Fin tp.p) :
    omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ j =
      omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩ ^ (j : ℕ) := by
  let χ := chi2enum hG mp tp ⟨1, tp.p_prime.one_lt⟩
  let χ₀ := (mp.certainTypeS hG).w1CharEquiv
    (eqQ hG mp tp ⟨0, tp.q_prime.pos⟩)
  have hpow : chi2enum hG mp tp j = χ ^ (j : ℕ) := by
    simp [χ, chi2enum, OddOrder.Peterfalvi.S06.cyclicPowEnum_apply]
  have hzero : eqQ hG mp tp ⟨0, tp.q_prime.pos⟩ = 0 := by
    apply Fin.ext
    simp [eqQ]
  have hχ₀ : χ₀ = 1 := by
    simp [χ₀, hzero]
  unfold omegaSChar
  rw [hpow]
  apply MonoidHom.ext
  intro w
  simp only [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar,
    MonoidHom.comp_apply, MonoidHom.mul_apply]
  change χ₀ _ * (χ ^ (j : ℕ)) _ =
    (((χ₀.comp (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst *
      χ.comp (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd).comp
        (gridEquivE hG mp tp).toMonoidHom) ^ (j : ℕ)) w
  rw [hχ₀]
  simp only [MonoidHom.one_apply, one_mul, MonoidHom.one_comp]
  exact (MonoidHom.pow_apply χ (j : ℕ) _).trans
    (MonoidHom.pow_apply
      ((χ.comp (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd).comp
        (gridEquivE hG mp tp).toMonoidHom) (j : ℕ) w).symm

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- The concrete Dade-grid member is the S05 sigma image of its underlying
linear character. -/
theorem tau3W_omegaS_eq_sigma_omegaSChar (i : Fin tp.q) (j : Fin tp.p) :
    tau3W hG mp tp (omegaS hG mp tp i j) =
      (tiCyclicW hG mp tp).sigma rfl (tiCyclicWDadeApp hG mp tp)
        ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j) :
          ClassFunction ↥(tiCyclicW hG mp tp).W ℂ) := by
  rw [omegaS_eq_omega_omegaSChar]
  change (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _ = _
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]

omit [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)] [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- The cyclic factor `W = W₁ ⊔ W₂` has order `|W| = q·p` (`W₁ ∩ W₂ = ⊥`, `W₁` normalizes `W₂`
since they commute). -/
theorem cardTPW : Nat.card ↥tp.W = tp.q * tp.p := by
  have hconj : ∀ x ∈ tp.W1, ∀ a ∈ tp.W2, x * a * x⁻¹ ∈ tp.W2 := by
    intro x hx a ha
    have hc : Commute x a := tp.W1_commutes_W2 x hx a ha
    have hxa : x * a * x⁻¹ = a := by rw [hc.eq]; group
    rw [hxa]; exact ha
  have hW1norm : tp.W1 ≤ Subgroup.normalizer (tp.W2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hconj x hx a ha, fun ha => ?_⟩
    have hb := hconj x⁻¹ (tp.W1.inv_mem hx) (x * a * x⁻¹) ha
    simpa [mul_assoc] using hb
  rw [tp.W_eq_join,
    OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hW1norm
      tp.W1_inf_W2_eq_bot,
    ← tp.q_eq_card_W1, ← tp.p_eq_card_W2]

/-- The underlying-character grid is injective: orthonormal grid characters cannot have
the same underlying linear character. -/
theorem omegaSChar_injective :
    Function.Injective
      (fun ij : Fin tp.q × Fin tp.p => omegaSChar hG mp tp ij.1 ij.2) := by
  intro ⟨i, j⟩ ⟨k, l⟩ h
  by_contra hne
  have hCF : omegaS hG mp tp i j = omegaS hG mp tp k l := by
    rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar]
    exact congrArg _ (congrArg _ h)
  have h1 := omegaS_inner hG mp tp i k j l
  rw [hCF] at h1
  have h2 := omegaS_inner hG mp tp k k l l
  rw [h1] at h2
  have hcond : ¬ (i = k ∧ j = l) := fun ⟨h1', h2'⟩ => hne (by rw [h1', h2'])
  rw [if_neg hcond, if_pos (⟨rfl, rfl⟩ : k = k ∧ l = l)] at h2
  exact zero_ne_one h2

/-- **Exhaustion by counting**: every linear character of `↥tp.W` underlies some `omegaS i j` —
the `(i,j) ↦ omegaSChar i j` map is injective (the `omegaS` are orthonormal, hence distinct)
between types of the same cardinality `pq`. -/
theorem exists_omegaS_eq_omega (ξ : ↥tp.W →* ℂˣ) :
    ∃ (i : Fin tp.q) (j : Fin tp.p),
      omegaS hG mp tp i j = ((tiCyclicW hG mp tp).omega ξ).toClassFunction := by
  classical
  haveI : Fintype (↥tp.W →* ℂˣ) := Fintype.ofFinite _
  have hinj := omegaSChar_injective hG mp tp
  -- cardinalities agree: `|Fin q × Fin p| = pq = |W| = |Ŵ|`
  have hcardW : Nat.card ↥tp.W = tp.q * tp.p := cardTPW mp tp
  have hcardHom : Fintype.card (↥tp.W →* ℂˣ) = tp.q * tp.p := by
    haveI := tp.W_cyclic
    letI : CommGroup ↥tp.W := IsCyclic.commGroup
    haveI : NeZero ((Monoid.exponent ↥tp.W : ℂ)) := ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩
    rw [← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥tp.W ℂ]
    exact hcardW
  have hsurj : Function.Surjective
      (fun ij : Fin tp.q × Fin tp.p => omegaSChar hG mp tp ij.1 ij.2) := by
    have hbij := (Fintype.bijective_iff_injective_and_card
      (fun ij : Fin tp.q × Fin tp.p => omegaSChar hG mp tp ij.1 ij.2)).mpr
      ⟨hinj, by simp [hcardHom]⟩
    exact hbij.surjective
  obtain ⟨⟨i, j⟩, hij⟩ := hsurj ξ
  refine ⟨i, j, ?_⟩
  rw [omegaS_eq_omega_omegaSChar]
  exact congrArg _ (congrArg _ hij)

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- **Peterfalvi (3.9.c) for the S-side `η`-grid** (issue-3002 supply): the grid value
`η_{ij}(g) = (τ₃ω)_{ij}(g)` is a rational integer on elements `g` of order prime to `pq`.

The value is `σ(ω(ξ_{ij}))(g)` for the underlying linear character `ξ_{ij} = omegaSChar i j`
(`omegaS_eq_omega_omegaSChar` + `sigmaIntegral_apply`).  Since `ξ_{ij}` is a character of the
cyclic `W` (`|W| = pq`, `cardTPW`), its order divides `pq`, so `Coprime(orderOf g, pq)` gives
`Coprime(orderOf g, orderOf ξ_{ij})`, and the S05 (3.9.c) Galois-integrality
`exists_intCast_sigma_omega_apply` applies. -/
theorem tau3W_omegaS_intCast_of_coprime (i : Fin tp.q) (j : Fin tp.p) {g : G}
    (hg : Nat.Coprime (orderOf g) (tp.p * tp.q)) :
    ∃ n : ℤ, tau3W hG mp tp (omegaS hG mp tp i j) g = (n : ℂ) := by
  classical
  haveI : Fintype ↥tp.W := Fintype.ofFinite _
  -- `orderOf (omegaSChar i j) ∣ pq`: the hom `ξ` satisfies `ξ ^ |W| = 1` and `|W| = pq`.
  have hdvd : orderOf (omegaSChar hG mp tp i j) ∣ tp.p * tp.q := by
    set ξ := omegaSChar hG mp tp i j with hξ
    have hpow : ξ ^ Fintype.card ↥tp.W = 1 := by
      ext w
      rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, pow_card_eq_one, map_one]
    have hcardW : Fintype.card ↥tp.W = tp.p * tp.q := by
      rw [← Nat.card_eq_fintype_card, cardTPW mp tp, Nat.mul_comm]
    rw [← hcardW]
    exact orderOf_dvd_of_pow_eq_one hpow
  have hcop : (orderOf g).Coprime (orderOf (omegaSChar hG mp tp i j)) :=
    hg.coprime_dvd_right hdvd
  obtain ⟨n, hn⟩ := (tiCyclicW hG mp tp).exists_intCast_sigma_omega_apply rfl
    (tiCyclicWDadeApp hG mp tp) (omegaSChar hG mp tp i j) hcop
  refine ⟨n, ?_⟩
  rw [omegaS_eq_omega_omegaSChar]
  show (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _ g = _
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  exact hn

/-- The principal grid character `omegaS ⟨0⟩ ⟨0⟩` is the trivial character of `↥tp.W`:
its underlying hom is `omegaProdChar (w1CharEquiv 0) (chi2enum 0) = omegaProdChar 1 1 = 1`
(`w1CharEquiv_zero`, `chi2enum_zero`), and `omega 1 = trivialClassFunction`. -/
theorem omegaS_principal_eq_trivial :
    omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩
      = trivialClassFunction ↥tp.W := by
  have hchar : omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩ = 1 := by
    have h0 : eqQ hG mp tp ⟨0, tp.q_prime.pos⟩ = 0 := by
      apply Fin.ext; simp [eqQ]
    rw [omegaSChar, h0, (mp.certainTypeS hG).w1CharEquiv_zero, chi2enum_zero]
    apply MonoidHom.ext
    intro w
    show ((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar 1 1
      ((gridEquivE hG mp tp).toMonoidHom w) : ℂˣ) = 1
    rw [(mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_one_one, MonoidHom.one_apply]
  rw [omegaS_eq_omega_omegaSChar, hchar]
  apply ClassFunction.ext
  intro w
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply]
  change ((1 : ↥tp.W →* ℂˣ) w : ℂ) = _
  rw [MonoidHom.one_apply, Units.val_one, trivialClassFunction_apply]

/-- **Peterfalvi (3.9) principal value on generic elements** (issue-3002 supply): the principal
grid value `(τ₃ω)_{00}(g) = 1` for every `g` (the coprimality hypothesis is unused:
`omegaS₀₀` is the trivial character and `τ₃(1_W) = 1_G`). -/
theorem tau3W_omegaS_principal_of_coprime {g : G}
    (_hg : Nat.Coprime (orderOf g) (tp.p * tp.q)) :
    tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩) g = 1 := by
  rw [omegaS_principal_eq_trivial, tau3W_trivial, trivialClassFunction_apply]

/-- **The `eqQ` reindex commutes with index negation**: `eqQ` is a `finCongr` (value-preserving
cast along `|W₁| = q`), so the `S15.finNeg` negation on `Fin tp.q` transports to the explicit
`(w₁ − ·) % w₁` negation on `Fin |W₁|` — the index form of `w1CharEquiv_finNeg`. -/
theorem eqQ_finNeg (i : Fin tp.q) :
    eqQ hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
      = ⟨(Nat.card ↥(mp.certainTypeS hG).W1 - ((eqQ hG mp tp i : Fin _) : ℕ))
            % Nat.card ↥(mp.certainTypeS hG).W1,
          Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩ := by
  apply Fin.ext
  simp only [eqQ, finCongr_apply, Fin.coe_cast, OddOrder.Peterfalvi.S15.finNeg]
  rw [cardCertainTypeS_W1 hG mp tp]

/-- **Index negation is character inversion for the S-side grid characters** (Peterfalvi (3.5):
the grid is indexed by character powers, so `ω_{−i,−j} = ω_{ij}⁻¹`).  Assembled from the two
power-enumeration halves (`w1CharEquiv_finNeg` via the `eqQ` cast, `chi2enum_finNeg`) and the
coordinatewise inversion `omegaProdChar_inv`. -/
theorem omegaSChar_finNeg (i : Fin tp.q) (j : Fin tp.p) :
    omegaSChar hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
      = (omegaSChar hG mp tp i j)⁻¹ := by
  rw [omegaSChar, omegaSChar, eqQ_finNeg hG mp tp i,
    (mp.certainTypeS hG).w1CharEquiv_finNeg (eqQ hG mp tp i),
    chi2enum_finNeg hG mp tp j]
  -- `(ω(χ₁⁻¹, χ₂⁻¹)).comp e = (ω(χ₁, χ₂).comp e)⁻¹`: pointwise, `ℂˣ` values invert
  -- coordinatewise (`omegaProdChar` is the product of the two coordinate pullbacks).
  ext w
  simp only [MonoidHom.comp_apply, MonoidHom.inv_apply,
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    Units.val_mul, Units.val_inv_eq_inv_val, mul_inv]
  -- the row factor's `⁻¹` sits at the (defeq) `W₁ ⊔ W₂`-form hom type, where the `simp`
  -- lemmas do not fire syntactically; close it by definitional unfolding of the pointwise inv.
  congr 1
  exact Units.val_inv_eq_inv_val _

/-- The `eqQ` reindex intertwines row negation (`S15.finNeg`) with the character-inversion
row permutation `rowInv`: both send `i` to the index of the inverse `W₁`-character. -/
theorem eqQ_finNeg_eq_rowInv (i : Fin tp.q) :
    eqQ hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
      = OddOrder.Peterfalvi.S06.rowInv (mp.certainTypeS hG) (eqQ hG mp tp i) := by
  apply (mp.certainTypeS hG).w1CharEquiv.injective
  rw [eqQ_finNeg hG mp tp i, (mp.certainTypeS hG).w1CharEquiv_finNeg,
    OddOrder.Peterfalvi.S06.w1CharEquiv_rowInv]

/-- **CF-level conjugation pairs the `ω`-grid at the negated index** (Peterfalvi (3.9.a),
character half): `ω̄_{ij} = ω_{−i,−j}` — complex conjugation inverts the linear grid character
(`galoisMap_conj_omega`), and index negation is character inversion (`omegaSChar_finNeg`). -/
theorem omegaS_conj (i : Fin tp.q) (j : Fin tp.p) :
    (omegaS hG mp tp i j).conj
      = omegaS hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
          (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j) := by
  have hg2 := congrArg
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(tiCyclicW hG mp tp).W =>
      (χ : ClassFunction ↥(tiCyclicW hG mp tp).W ℂ))
    (OddOrder.Peterfalvi.S06.galoisMap_conj_omega (tiCyclicW hG mp tp)
      (omegaSChar hG mp tp i j))
  simp only [IrreducibleCharacter.galoisMap_apply_coe] at hg2
  rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar, omegaSChar_finNeg,
    ClassFunction.conj_eq_mapRingEquiv_conjAe]
  exact hg2

/-- **CF-level conjugation pairs the `μ`-grid at the negated index** (Peterfalvi (4.9)(a)):
`μ̄_{ij} = μ_{−i,−j}` — the §6 conjugation bridge `certainType_mu_conj_eq` with the two
power-enumeration index bridges (`chi2enum_finNeg`, `eqQ_finNeg_eq_rowInv`). -/
theorem muS_conj (i : Fin tp.q) (j : Fin tp.p) :
    (muS hG mp tp i j).conj
      = muS hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
          (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j) := by
  have hg2 := congrArg
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥mp.S =>
      (χ : ClassFunction ↥mp.S ℂ))
    (OddOrder.Peterfalvi.S06.certainType_mu_conj_eq (mp.certainTypeS hG)
      (chi2enum hG mp tp j) (eqQ hG mp tp i))
  simp only [IrreducibleCharacter.galoisMap_apply_coe] at hg2
  rw [muS, muS, chi2enum_finNeg hG mp tp j, eqQ_finNeg_eq_rowInv hG mp tp i,
    ClassFunction.conj_eq_mapRingEquiv_conjAe]
  exact hg2

/-- **CF-level conjugation pairs the `η = τ₃∘ω` grid at the negated index** (Peterfalvi (3.9.a),
full CF form — strengthening the generic-element `tau3W_omegaS_pair_of_coprime` below):
`(τ₃ω_{ij})̄ = τ₃ω_{−i,−j}`.  `σ` intertwines the coefficientwise Galois action
(`sigma_mapRingEquiv_comm`), and conjugation inverts the grid character
(`galoisMap_conj_omega` + `omegaSChar_finNeg`). -/
theorem tau3W_omegaS_conj (i : Fin tp.q) (j : Fin tp.p) :
    (tau3W hG mp tp (omegaS hG mp tp i j)).conj
      = tau3W hG mp tp (omegaS hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
          (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)) := by
  have hcomm := OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_mapRingEquiv_comm
    (tiCyclicW hG mp tp) rfl (tiCyclicWDadeApp hG mp tp) Complex.conjAe.toRingEquiv
    ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j))
  have hg2 := congrArg
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(tiCyclicW hG mp tp).W =>
      (χ : ClassFunction ↥(tiCyclicW hG mp tp).W ℂ))
    (OddOrder.Peterfalvi.S06.galoisMap_conj_omega (tiCyclicW hG mp tp)
      (omegaSChar hG mp tp i j))
  rw [hg2] at hcomm
  rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar, omegaSChar_finNeg,
    ClassFunction.conj_eq_mapRingEquiv_conjAe]
  exact hcomm

/-- **Peterfalvi (3.9.a) conjugate-pair symmetry on generic elements** (issue-3002 supply):
for `g` of order prime to `pq`, the `η`-grid pairs under the index negation `(i,j) ↦ (−i,−j)`
(`S15.finNeg`), `(τ₃ω)_{−i,−j}(g) = (τ₃ω)_{ij}(g)`.

Peterfalvi's (3.9.a) content: the negated-index grid character is the *inverse* linear character
(`omegaSChar_finNeg` — honest because the enumerations are **power enumerations**, Peterfalvi's
own (3.5) grid indexing), whose `ω` is the complex conjugate (`galoisMap_conj_omega`); `σ`
intertwines coefficientwise Galois action ((3.9.a), `sigma_mapRingEquiv_comm`), so
`η_{−i,−j}(g) = conj (η_{ij}(g))`; and the value `η_{ij}(g)` is a rational **integer** by (3.9.c)
(`exists_intCast_sigma_omega_apply`, `Coprime(ord g, pq)`), hence conjugation-fixed. -/
theorem tau3W_omegaS_pair_of_coprime (i : Fin tp.q) (j : Fin tp.p) {g : G}
    (hg : Nat.Coprime (orderOf g) (tp.p * tp.q)) :
    tau3W hG mp tp (omegaS hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)) g
      = tau3W hG mp tp (omegaS hG mp tp i j) g := by
  classical
  haveI : Fintype ↥tp.W := Fintype.ofFinite _
  -- (3.9.c): the σ-value at the base index is a rational integer.
  have hdvd : orderOf (omegaSChar hG mp tp i j) ∣ tp.p * tp.q := by
    set ξ := omegaSChar hG mp tp i j with hξ
    have hpow : ξ ^ Fintype.card ↥tp.W = 1 := by
      ext w
      rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, pow_card_eq_one, map_one]
    have hcardW : Fintype.card ↥tp.W = tp.p * tp.q := by
      rw [← Nat.card_eq_fintype_card, cardTPW mp tp, Nat.mul_comm]
    rw [← hcardW]
    exact orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨n, hn⟩ := (tiCyclicW hG mp tp).exists_intCast_sigma_omega_apply rfl
    (tiCyclicWDadeApp hG mp tp) (omegaSChar hG mp tp i j) (hg.coprime_dvd_right hdvd)
  -- the negated-index grid character is the Galois conjugate of the base one
  have homega : (tiCyclicW hG mp tp).omega (omegaSChar hG mp tp
        (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j))
      = IrreducibleCharacter.galoisMap Complex.conjAe.toRingEquiv
          ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j)) := by
    rw [OddOrder.Peterfalvi.S06.galoisMap_conj_omega]
    exact congrArg _ (omegaSChar_finNeg hG mp tp i j)
  rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar]
  show (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _ g
    = (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _ g
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply,
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply, homega,
    ← (tiCyclicW hG mp tp).sigma_mapRingEquiv_comm rfl (tiCyclicWDadeApp hG mp tp),
    OddOrder.RepresentationTheory.ClassFunction.mapRingEquiv_apply]
  have hv : (tiCyclicW hG mp tp).sigma rfl (tiCyclicWDadeApp hG mp tp)
      ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j)).toClassFunction g = (n : ℂ) := hn
  rw [hv]
  exact map_intCast _ n

/-- **Peterfalvi (3.2.d), `η`-grid form** (issue-2034 supply): a class function of `G`
orthogonal to the whole grid `tau3W (omegaS i j)` vanishes on the regular set
`Ŵ = W ∖ (W₁ ∪ W₂)`.  Transfer of the S05 completeness
`eq_zero_of_mem_V_of_inner_chiFam_eq_zero` along the exhaustion `exists_omegaS_eq_omega`
and the `σ`-grid identification `sigma_omega`. -/
theorem tau3W_omegaS_complete_vanish (χ : ClassFunction G ℂ)
    (horth : ∀ (i : Fin tp.q) (j : Fin tp.p),
      ClassFunction.inner (tau3W hG mp tp (omegaS hG mp tp i j)) χ = 0)
    {w : G} (hwW : w ∈ tp.W) (hnot : w ∉ (tp.W1 : Set G) ∪ (tp.W2 : Set G)) :
    χ w = 0 := by
  classical
  refine OddOrder.Peterfalvi.S05.TICyclicHypothesis.eq_zero_of_mem_V_of_inner_chiFam_eq_zero
    (tiCyclicW hG mp tp) rfl (tiCyclicWDadeApp hG mp tp) (χ := χ) ?_ (show w ∈ _ from ⟨hwW, hnot⟩)
  intro a b
  obtain ⟨i, j, hij⟩ := exists_omegaS_eq_omega hG mp tp
    ((tiCyclicW hG mp tp).omegaProdChar a b)
  have hchi : (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) (a, b)
      = tau3W hG mp tp (omegaS hG mp tp i j) := by
    have h1 := (tiCyclicW hG mp tp).sigma_omega rfl (tiCyclicWDadeApp hG mp tp)
      ((tiCyclicW hG mp tp).omegaProdChar a b)
    rw [(tiCyclicW hG mp tp).omegaProdEquiv_symm_omegaProdChar a b] at h1
    rw [← h1, ← hij]
    show _ = (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  rw [OddOrder.RepresentationTheory.inner_conj_symm _ χ, hchi, horth i j, star_zero]

/-! #### The (3.4)/(3.5) four-corner relation on the `η`-grid (issue-2036 supply)

`tau3W (omegaS i j)` is the `(3.5)`-family member at the hom-pair of `omegaSChar i j`; the
`(3.5)` defining relation `τ(α_{ab}) = 1 − χ_{a1} − χ_{1b} + χ_{ab}` plus the vanishing of
`τ(α)` off the `V`-saturation gives the four-corner identity
`1 − η_{i0}(x) − η_{0j}(x) + η_{ij}(x) = 0` there. -/

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- Column-independence of the `omegaS`-values on `W₁` (the row character alone survives). -/
theorem omegaS_apply_of_mem_W1_col_eq (i : Fin tp.q) (j j' : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ tp.W1) :
    omegaS hG mp tp i j w = omegaS hG mp tp i j' w := by
  have hwK : (w : G) ∈ mp.K := tp.W1_eq_K hG ▸ hw
  rw [omegaS, omegaS, ClassFunction.compHom_apply, ClassFunction.compHom_apply,
    MulEquiv.coe_toMonoidHom, Peterfalvi.S06.Hypothesis.chiColumn,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- Row-independence of the `omegaS`-values on `W₂` (the column character alone survives). -/
theorem omegaS_apply_of_mem_W2_row_eq (i i' : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ tp.W2) :
    omegaS hG mp tp i j w = omegaS hG mp tp i' j w := by
  have hwK : (w : G) ∈ mp.Kstar := tp.W2_eq_Kstar hG ▸ hw
  rw [omegaS, omegaS, ClassFunction.compHom_apply, ClassFunction.compHom_apply,
    MulEquiv.coe_toMonoidHom, Peterfalvi.S06.Hypothesis.chiColumn,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- Values of `omegaSChar` are the `omegaS`-values. -/
theorem omegaSChar_val (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W) :
    ((omegaSChar hG mp tp i j w : ℂˣ) : ℂ) = omegaS hG mp tp i j w := by
  rw [omegaS_eq_omega_omegaSChar]
  rfl

/-- **Row alignment**: `omegaSChar i 0` is the product character of the first component of
`omegaSChar i j`'s pair with the trivial second component. -/
theorem omegaSChar_row_align (i : Fin tp.q) (j : Fin tp.p) :
    omegaSChar hG mp tp i ⟨0, tp.p_prime.pos⟩
      = (tiCyclicW hG mp tp).omegaProdChar
          ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).1 1 := by
  have hpair : (tiCyclicW hG mp tp).omegaProdChar
      ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).1
      ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).2
      = omegaSChar hG mp tp i j :=
    (tiCyclicW hG mp tp).omegaProdEquiv.apply_symm_apply (omegaSChar hG mp tp i j)
  refine monoidHom_eq_of_eqOn_W1_W2 mp tp ?_ ?_
  · -- on `W₁`: both equal `omegaSChar i j` there
    intro w hw
    have hsnd : (tiCyclicW hG mp tp).wSnd w = 1 :=
      (tiCyclicW hG mp tp).wSnd_eq_one_of_mem_W1
        (Subgroup.mem_subgroupOf.mpr (show (w : G) ∈ (tiCyclicW hG mp tp).W1 from hw))
    have h1 : omegaSChar hG mp tp i ⟨0, tp.p_prime.pos⟩ w = omegaSChar hG mp tp i j w :=
      Units.ext (by
        rw [omegaSChar_val hG mp tp _ _ w,
          omegaS_apply_of_mem_W1_col_eq hG mp tp i ⟨0, tp.p_prime.pos⟩ j w hw,
          ← omegaSChar_val hG mp tp i j w])
    refine h1.trans ((DFunLike.congr_fun hpair w).symm.trans ?_)
    show _ * ((tiCyclicW hG mp tp).omegaProdEquiv.symm
        (omegaSChar hG mp tp i j)).2 ((tiCyclicW hG mp tp).wSnd w)
      = _ * (1 : (tiCyclicW hG mp tp).W2.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
          ((tiCyclicW hG mp tp).wSnd w)
    rw [hsnd, map_one, map_one]
  · -- on `W₂`: both are `1`
    intro w hw
    have hfst : (tiCyclicW hG mp tp).wFst w = 1 :=
      (tiCyclicW hG mp tp).wFst_eq_one_of_mem_W2
        (Subgroup.mem_subgroupOf.mpr (show (w : G) ∈ (tiCyclicW hG mp tp).W2 from hw))
    have h1 : omegaSChar hG mp tp i ⟨0, tp.p_prime.pos⟩ w = 1 :=
      Units.ext (by
        rw [omegaSChar_val hG mp tp _ _ w,
          omegaS_col_zero_apply_of_mem_W2 hG mp tp i w hw, Units.val_one])
    rw [h1]
    show (1 : ℂˣ) = ((tiCyclicW hG mp tp).omegaProdEquiv.symm
        (omegaSChar hG mp tp i j)).1 ((tiCyclicW hG mp tp).wFst w)
      * (1 : (tiCyclicW hG mp tp).W2.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
          ((tiCyclicW hG mp tp).wSnd w)
    rw [hfst, map_one, MonoidHom.one_apply, one_mul]

/-- **Column alignment**: `omegaSChar 0 j` is the product character of the trivial first
component with the second component of `omegaSChar i j`'s pair. -/
theorem omegaSChar_col_align (i : Fin tp.q) (j : Fin tp.p) :
    omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ j
      = (tiCyclicW hG mp tp).omegaProdChar 1
          ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).2 := by
  have hpair : (tiCyclicW hG mp tp).omegaProdChar
      ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).1
      ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).2
      = omegaSChar hG mp tp i j :=
    (tiCyclicW hG mp tp).omegaProdEquiv.apply_symm_apply (omegaSChar hG mp tp i j)
  refine monoidHom_eq_of_eqOn_W1_W2 mp tp ?_ ?_
  · intro w hw
    have hsnd : (tiCyclicW hG mp tp).wSnd w = 1 :=
      (tiCyclicW hG mp tp).wSnd_eq_one_of_mem_W1
        (Subgroup.mem_subgroupOf.mpr (show (w : G) ∈ (tiCyclicW hG mp tp).W1 from hw))
    have h1 : omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ j w = 1 :=
      Units.ext (by
        rw [omegaSChar_val hG mp tp _ _ w,
          omegaS_row_zero_apply_of_mem_W1 hG mp tp j w hw, Units.val_one])
    rw [h1]
    show (1 : ℂˣ) = (1 : (tiCyclicW hG mp tp).W1.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
        ((tiCyclicW hG mp tp).wFst w)
      * ((tiCyclicW hG mp tp).omegaProdEquiv.symm
          (omegaSChar hG mp tp i j)).2 ((tiCyclicW hG mp tp).wSnd w)
    rw [hsnd, map_one, MonoidHom.one_apply, one_mul]
  · intro w hw
    have hfst : (tiCyclicW hG mp tp).wFst w = 1 :=
      (tiCyclicW hG mp tp).wFst_eq_one_of_mem_W2
        (Subgroup.mem_subgroupOf.mpr (show (w : G) ∈ (tiCyclicW hG mp tp).W2 from hw))
    have h1 : omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ j w = omegaSChar hG mp tp i j w :=
      Units.ext (by
        rw [omegaSChar_val hG mp tp _ _ w,
          omegaS_apply_of_mem_W2_row_eq hG mp tp ⟨0, tp.q_prime.pos⟩ i j w hw,
          ← omegaSChar_val hG mp tp i j w])
    refine h1.trans ((DFunLike.congr_fun hpair w).symm.trans ?_)
    show ((tiCyclicW hG mp tp).omegaProdEquiv.symm
        (omegaSChar hG mp tp i j)).1 ((tiCyclicW hG mp tp).wFst w) * _
      = (1 : (tiCyclicW hG mp tp).W1.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
          ((tiCyclicW hG mp tp).wFst w) * _
    rw [hfst, map_one, map_one]

/-- **Peterfalvi (3.4)/(3.5), the four-corner vanishing** (issue-2036 supply): off the
conjugacy saturation of the regular set `V = W ∖ (W₁ ∪ W₂)`,
`1 − η_{i0}(x) − η_{0j}(x) + η_{ij}(x) = 0` for nonzero row and column indices — the `(3.5)`
relation `τ(α_{AB}) = 1_G − χ_{A1} − χ_{1B} + χ_{AB}` evaluated where the `V`-supported
`τ(α)` vanishes, with the `χ`-corners identified with the `η`-grid along the
`omegaSChar`-pair alignments. -/
theorem tau3W_omegaS_fourcorner_vanish (i : Fin tp.q) (j : Fin tp.p)
    (hi : i ≠ ⟨0, tp.q_prime.pos⟩) (hj : j ≠ ⟨0, tp.p_prime.pos⟩) {x : G}
    (hx : x ∉ Group.conjugatesOfSet ((tiCyclicW hG mp tp).V)) :
    (1 : ℂ) - tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) x
      - tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j) x
      + tau3W hG mp tp (omegaS hG mp tp i j) x = 0 := by
  classical
  set A := ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).1 with hAdef
  set B := ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).2 with hBdef
  have hpair : (tiCyclicW hG mp tp).omegaProdChar A B = omegaSChar hG mp tp i j :=
    (tiCyclicW hG mp tp).omegaProdEquiv.apply_symm_apply (omegaSChar hG mp tp i j)
  -- distinctness of the grid forces nontrivial components
  have hdistinct : ∀ (k : Fin tp.q) (l : Fin tp.p), (k, l) ≠ (i, j) →
      omegaSChar hG mp tp k l ≠ omegaSChar hG mp tp i j := by
    intro k l hne heq
    have hCF : omegaS hG mp tp k l = omegaS hG mp tp i j := by
      rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar, heq]
    have h1 := omegaS_inner hG mp tp k i l j
    rw [hCF] at h1
    have h2 := omegaS_inner hG mp tp i i j j
    rw [h1] at h2
    have hcond : ¬ (k = i ∧ l = j) := fun ⟨h1', h2'⟩ => hne (by rw [h1', h2'])
    rw [if_neg hcond, if_pos ⟨rfl, rfl⟩] at h2
    exact zero_ne_one h2
  have hA1 : A ≠ 1 := by
    intro h1
    refine hdistinct ⟨0, tp.q_prime.pos⟩ j (fun hp => hi (congrArg Prod.fst hp).symm) ?_
    rw [omegaSChar_col_align hG mp tp i j, ← hBdef, ← h1, hAdef]
    exact hpair
  have hB1 : B ≠ 1 := by
    intro h1
    refine hdistinct i ⟨0, tp.p_prime.pos⟩ (fun hp => hj (congrArg Prod.snd hp).symm) ?_
    rw [omegaSChar_row_align hG mp tp i j, ← hAdef, ← h1, hBdef]
    exact hpair
  -- the (3.5) relation, evaluated at `x`
  have hrel := ((tiCyclicW hG mp tp).chiFam_spec rfl (tiCyclicWDadeApp hG mp tp)).2.2.2
    A B hA1 hB1
  have hvanish : (tiCyclicWDadeApp hG mp tp).tau.toDadeMap
      ((tiCyclicW hG mp tp).alpha rfl A B) x = 0 :=
    OddOrder.Peterfalvi.S04.map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot
      (tiCyclicWDadeApp hG mp tp).tau.toDadeIsometryData.isDadeMap (fun _ => rfl) _ hx
  -- identify the χ-corners with the η-grid
  have hcorner : ∀ (k : Fin tp.q) (l : Fin tp.p)
      (pr : ((tiCyclicW hG mp tp).W1.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
        × ((tiCyclicW hG mp tp).W2.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)),
      omegaSChar hG mp tp k l = (tiCyclicW hG mp tp).omegaProdChar pr.1 pr.2 →
      (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) pr
        = tau3W hG mp tp (omegaS hG mp tp k l) := by
    intro k l pr hchar
    have h1 := (tiCyclicW hG mp tp).sigma_omega rfl (tiCyclicWDadeApp hG mp tp)
      ((tiCyclicW hG mp tp).omegaProdChar pr.1 pr.2)
    rw [(tiCyclicW hG mp tp).omegaProdEquiv_symm_omegaProdChar pr.1 pr.2] at h1
    rw [← h1, ← hchar, omegaS_eq_omega_omegaSChar]
    show _ = (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  have hc11 := hcorner i j (A, B) hpair.symm
  have hcA1 := hcorner i ⟨0, tp.p_prime.pos⟩ (A, 1) (omegaSChar_row_align hG mp tp i j)
  have hc1B := hcorner ⟨0, tp.q_prime.pos⟩ j (1, B) (omegaSChar_col_align hG mp tp i j)
  have htriv := ((tiCyclicW hG mp tp).chiFam_spec rfl (tiCyclicWDadeApp hG mp tp)).1
  -- evaluate at `x` and rearrange
  have hev := congrArg (fun f : ClassFunction G ℂ => f x) hrel
  rw [hvanish] at hev
  have hev' : (0 : ℂ) = 1 - tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) x
      - tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j) x
      + tau3W hG mp tp (omegaS hG mp tp i j) x := by
    rw [← hcA1, ← hc1B, ← hc11]
    calc (0 : ℂ) = (trivialClassFunction G
          - (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) (A, 1)
          - (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) (1, B)
          + (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) (A, B)) x := hev
      _ = _ := by
        simp only [ClassFunction.add_apply, ClassFunction.sub_apply,
          trivialClassFunction_apply]
  exact hev'.symm

/-- The first nonprincipal row-axis character has the full prime order `q`. -/
theorem orderOf_omegaSChar_row_base :
    orderOf
      (omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩) = tp.q := by
  let ξ := omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩
  have hpow : ξ ^ tp.q = 1 := by
    dsimp [ξ]
    refine monoidHom_eq_of_eqOn_W1_W2 mp tp ?_ ?_ <;>
      intro w hw <;> refine Units.ext ?_
    · rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        omegaSChar_val hG mp tp _ _ w, MonoidHom.one_apply, Units.val_one]
      exact omegaS_pow_q_of_mem_W1 hG mp tp _ _ w hw
    · rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        omegaSChar_val hG mp tp _ _ w, MonoidHom.one_apply, Units.val_one,
        omegaS_col_zero_apply_of_mem_W2 hG mp tp _ w hw, one_pow]
  have hzero :
      omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩ = 1 := by
    simpa using omegaSChar_row_eq_pow hG mp tp ⟨0, tp.q_prime.pos⟩
  have hne : ξ ≠ 1 := by
    intro hξ
    have hξprime : omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩
        ⟨0, tp.p_prime.pos⟩ = 1 := by simpa only [ξ] using hξ
    have hp : ((⟨1, tp.q_prime.one_lt⟩ : Fin tp.q),
        (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) =
        ((⟨0, tp.q_prime.pos⟩ : Fin tp.q),
          (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) :=
      (omegaSChar_injective hG mp tp) (hξprime.trans hzero.symm)
    have hv := congrArg (fun ij : Fin tp.q × Fin tp.p => (ij.1 : ℕ)) hp
    norm_num at hv
  have hdvd : orderOf ξ ∣ tp.q := orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.dvd_prime tp.q_prime).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

/-- The first nonprincipal column-axis character has the full prime order `p`. -/
theorem orderOf_omegaSChar_column_base :
    orderOf
      (omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩) = tp.p := by
  let ξ := omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩
  have hpow : ξ ^ tp.p = 1 := by
    dsimp [ξ]
    refine monoidHom_eq_of_eqOn_W1_W2 mp tp ?_ ?_ <;>
      intro w hw <;> refine Units.ext ?_
    · rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        omegaSChar_val hG mp tp _ _ w, MonoidHom.one_apply, Units.val_one,
        omegaS_row_zero_apply_of_mem_W1 hG mp tp _ w hw, one_pow]
    · rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        omegaSChar_val hG mp tp _ _ w, MonoidHom.one_apply, Units.val_one]
      exact omegaS_pow_p_of_mem_W2 hG mp tp _ _ w hw
  have hzero :
      omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩ = 1 := by
    simpa using omegaSChar_column_eq_pow hG mp tp ⟨0, tp.p_prime.pos⟩
  have hne : ξ ≠ 1 := by
    intro hξ
    have hξprime : omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩
        ⟨1, tp.p_prime.one_lt⟩ = 1 := by simpa only [ξ] using hξ
    have hp : ((⟨0, tp.q_prime.pos⟩ : Fin tp.q),
        (⟨1, tp.p_prime.one_lt⟩ : Fin tp.p)) =
        ((⟨0, tp.q_prime.pos⟩ : Fin tp.q),
          (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) :=
      (omegaSChar_injective hG mp tp) (hξprime.trans hzero.symm)
    have hv := congrArg (fun ij : Fin tp.q × Fin tp.p => (ij.2 : ℕ)) hp
    norm_num at hv
  have hdvd : orderOf ξ ∣ tp.p := orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.dvd_prime tp.p_prime).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

/-- Full Galois orbit of the nonprincipal row-axis `η`-characters. -/
theorem tau3W_omegaS_row_galois_orbit (i : Fin tp.q)
    (hi : i ≠ ⟨0, tp.q_prime.pos⟩) :
    ∃ u : ℂ ≃+* ℂ,
      ClassFunction.mapRingEquiv u
          (tau3W hG mp tp
            (omegaS hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩)) =
        tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) := by
  let ξ := omegaSChar hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩
  have hi0 : (i : ℕ) ≠ 0 := by
    intro h
    apply hi
    apply Fin.ext
    simpa using h
  have hicop : (i : ℕ).Coprime (orderOf ξ) := by
    rw [show orderOf ξ = tp.q by
      simpa [ξ] using orderOf_omegaSChar_row_base hG mp tp]
    exact Nat.coprime_comm.mp (tp.q_prime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hi0) i.isLt))
  obtain ⟨u, hu, -⟩ :=
    (tiCyclicW hG mp tp).exists_mapRingEquiv_sigma_omega_pow rfl
      (tiCyclicWDadeApp hG mp tp) ξ hicop
  refine ⟨u, ?_⟩
  rw [tau3W_omegaS_eq_sigma_omegaSChar, tau3W_omegaS_eq_sigma_omegaSChar]
  rw [omegaSChar_row_eq_pow hG mp tp i]
  convert hu.symm using 1
  all_goals simp [ξ]
  all_goals rfl

/-- Full Galois orbit of the nonprincipal column-axis `η`-characters. -/
theorem tau3W_omegaS_column_galois_orbit (j : Fin tp.p)
    (hj : j ≠ ⟨0, tp.p_prime.pos⟩) :
    ∃ u : ℂ ≃+* ℂ,
      ClassFunction.mapRingEquiv u
          (tau3W hG mp tp
            (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩)) =
        tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j) := by
  let ξ := omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ ⟨1, tp.p_prime.one_lt⟩
  have hj0 : (j : ℕ) ≠ 0 := by
    intro h
    apply hj
    apply Fin.ext
    simpa using h
  have hjcop : (j : ℕ).Coprime (orderOf ξ) := by
    rw [show orderOf ξ = tp.p by
      simpa [ξ] using orderOf_omegaSChar_column_base hG mp tp]
    exact Nat.coprime_comm.mp (tp.p_prime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hj0) j.isLt))
  obtain ⟨u, hu, -⟩ :=
    (tiCyclicW hG mp tp).exists_mapRingEquiv_sigma_omega_pow rfl
      (tiCyclicWDadeApp hG mp tp) ξ hjcop
  refine ⟨u, ?_⟩
  rw [tau3W_omegaS_eq_sigma_omegaSChar, tau3W_omegaS_eq_sigma_omegaSChar]
  rw [omegaSChar_column_eq_pow hG mp tp j]
  convert hu.symm using 1
  all_goals simp [ξ]
  all_goals rfl

/-- **Peterfalvi (3.9.b), vanishing transport along the row** (issue-2036 supply):
if the `η₁₀`-value vanishes at `x`, so do all nonprincipal row-axis values.  This is the
pointwise zero consequence of `tau3W_omegaS_row_galois_orbit`. -/
theorem tau3W_omegaS_row_vanish_of_one_zero {x : G}
    (h0 : tau3W hG mp tp
      (omegaS hG mp tp ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩) x = 0)
    (i : Fin tp.q) (hi : i ≠ ⟨0, tp.q_prime.pos⟩) :
    tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) x = 0 := by
  obtain ⟨u, hu⟩ := tau3W_omegaS_row_galois_orbit hG mp tp i hi
  have hv := congrArg (fun f : ClassFunction G ℂ => f x) hu
  simp only [OddOrder.RepresentationTheory.ClassFunction.mapRingEquiv_apply, h0, map_zero] at hv
  exact hv.symm

end Section16CharacterData

/-- **Peterfalvi §13 coherent Dade-grid producer** (`sorry`-free) — *lane-b*
(Peterfalvi §3–§13 coherent grids).  Given the maximal pair and the type-P
structure, constructs the character grids `ω, μ, ν`, the signs `δ, δ'`, the integral
maps, and the induction identities (13.1.d/e).

The mathematically substantive fields are the genuine §13 grid:
* `omega := omegaS` — the shared `ω`-grid, materialized from the certain-type machinery of
  `mp.S` (`certainTypeS`, indexed by `mp.K`, `mp.Kstar` and aligned to `tp.W₁, tp.W₂` via
  `tp.W1_eq_K`/`W2_eq_Kstar`).  `omegaS_eq_omegaT` proves it equals the T-side reconstruction, so
  the single `ω`-field satisfies *both* induction identities;
* `mu := muS`, `nu := nuT`, `delta := deltaS`, `deltaPrime := deltaPrimeT` — the induced
  exceptional characters and signs read off `certainTypeS`/`certainTypeT`'s `columnFamily`;
* `tau3 := tau3W` — the genuine §3.2 Dade σ-integral of the G-internal TI-cyclic structure on
  `W = S ∩ T`, supported on `Ẑ = W \ (W₁ ∪ W₂)` (built from the proven BG Theorem 14.7 TI fact and
  the general §4 Dade producer; `#print axioms` is `sorryAx`-free);
* `mu_definition := muS_definition`, `nu_definition := nuT_definition` — Peterfalvi (13.1.e),
  proven `sorry`-free.

**Vestigial fields** `Sset, Tset, A0S, A0T, tauS, tauT` carry honest placeholders (`∅`, `0`).
These are *not* consumed on the FT critical path: the §13/§16 contradiction in
`Peterfalvi.S16` (`S16_NonExistenceG`) is routed entirely through `eta = τ₃ ∘ ω` (the W-side
Dade grid), never through the S/T-side maximal-coherent isometries `τ_S, τ_T`.  The only
references to `tauS`/`tauT` are the (currently `sorry`-stubbed, *uncited*) coherence-wiring
lemmas in `S15_SAndT_Setup`, which lie off the FT path.  `Hypothesis` itself places no `Prop`
constraint on these six fields, so the placeholders introduce no unsound dependency — they are
genuine values of the right type for fields the formalized contradiction does not read.  (User
decision 2026-06-24, issue 1004: close the producer on the verified-vestigial finding rather
than build the off-path §7 maximal-coherent Dade theory.) -/
noncomputable def section16CharacterData_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) (tp : Section16TypePStructure mp) :
    Section16CharacterData mp tp := by
  -- The grid building blocks carry `[NeZero |certainType{S,T}.W₁|]` (the prime base-index
  -- normalization); discharge both from `|certainTypeS.W₁| = tp.q`, `|certainTypeT.W₁| = tp.p`.
  haveI : NeZero (Nat.card ↥(mp.certainTypeS hG).W1) :=
    ⟨by rw [Section16CharacterData.cardCertainTypeS_W1 hG mp tp]; exact tp.q_prime.pos.ne'⟩
  haveI : NeZero (Nat.card ↥(mp.certainTypeT hG).W1) :=
    ⟨by rw [Section16CharacterData.cardCertainTypeT_W1 hG mp tp]; exact tp.p_prime.pos.ne'⟩
  exact
    { Sset := ∅
      Tset := ∅
      A0S := ∅
      A0T := ∅
      tauS := 0
      tauT := 0
      omega := Section16CharacterData.omegaS hG mp tp
      mu := Section16CharacterData.muS hG mp tp
      nu := Section16CharacterData.nuT hG mp tp
      delta := Section16CharacterData.deltaS hG mp tp
      deltaPrime := Section16CharacterData.deltaPrimeT hG mp tp
      delta_pm_one :=
        ⟨fun j => ((mp.certainTypeS hG).columnFamily
            (Section16CharacterData.chi2enum hG mp tp j)).sign_eq,
         fun i => ((mp.certainTypeT hG).columnFamily
            (Section16CharacterData.colT hG mp tp i)).sign_eq⟩
      mu_degree_modEq_delta := fun i j => by
        haveI : NeZero (Nat.card ↥(mp.certainTypeS hG).W1) :=
          ⟨by rw [Section16CharacterData.cardCertainTypeS_W1 hG mp tp]; exact tp.q_prime.pos.ne'⟩
        obtain ⟨a, ha⟩ := (mp.certainTypeS hG).certainType_degree_modEq
          (Section16CharacterData.chi2enum hG mp tp j) (Section16CharacterData.eqQ hG mp tp i)
        refine ⟨a, ?_⟩
        have hq : (tp.q : ℂ) = (Nat.card ↥(mp.certainTypeS hG).W1 : ℂ) := by
          rw [Section16CharacterData.cardCertainTypeS_W1 hG mp tp]
        simp only [Section16CharacterData.muS, Section16CharacterData.deltaS, hq]
        exact ha
      delta_zero_eq_one := by
        haveI : NeZero (Nat.card ↥(mp.certainTypeS hG).W1) :=
          ⟨by rw [Section16CharacterData.cardCertainTypeS_W1 hG mp tp]; exact tp.q_prime.pos.ne'⟩
        show Section16CharacterData.deltaS hG mp tp ⟨0, tp.p_prime.pos⟩ = 1
        rw [Section16CharacterData.deltaS, Section16CharacterData.chi2enum_zero]
        exact ((mp.certainTypeS hG).certainType_zero_column_anchor).1
      tau3 := Section16CharacterData.tau3W hG mp tp
      mu_definition := Section16CharacterData.muS_definition hG mp tp
      mu_irreducible := fun i j =>
        (((mp.certainTypeS hG).columnFamily (Section16CharacterData.chi2enum hG mp tp j)).mu
          (Section16CharacterData.eqQ hG mp tp i)).isIrreducible
      mu_col_injective := fun j i i' h =>
        (Section16CharacterData.eqQ hG mp tp).injective
          ((((mp.certainTypeS hG).columnFamily
            (Section16CharacterData.chi2enum hG mp tp j)).injective)
            (OddOrder.RepresentationTheory.IrreducibleCharacter.ext h))
      mu_orthonormal := Section16CharacterData.muS_orthonormal hG mp tp
      mu_diff_support := fun i {j k} hj0 hk0 hdeg =>
        Section16CharacterData.muS_diff_support hG mp tp i hj0 hk0 hdeg
      mu_apply_of_not_mem_W2 := fun i j w hwW hwS hw2 =>
        Section16CharacterData.muS_apply_of_not_mem_W2 hG mp tp i j w hwW hwS hw2
      mu_conj := Section16CharacterData.muS_conj hG mp tp
      tau3_omega_conj := Section16CharacterData.tau3W_omegaS_conj hG mp tp
      mu_colSum_eq_induce := fun j => by
        refine ⟨ClassFunction.restrict ((derivedInG mp.S).subgroupOf mp.S)
            (((mp.certainTypeS hG).columnFamily
              (Section16CharacterData.chi2enum hG mp tp j)).mu 0 : ClassFunction ↥mp.S ℂ),
          ?_, ?_, ?_⟩
        · exact (mp.certainTypeS hG).certainTypeRestrict_isIrreducible _
        · calc (∑ i : Fin tp.q, Section16CharacterData.muS hG mp tp i j)
              = ∑ i' : Fin (Nat.card ↥(mp.certainTypeS hG).W1),
                  (((mp.certainTypeS hG).columnFamily
                    (Section16CharacterData.chi2enum hG mp tp j)).mu i' :
                    ClassFunction ↥mp.S ℂ) := by
                simp only [Section16CharacterData.muS]
                exact Equiv.sum_comp (Section16CharacterData.eqQ hG mp tp)
                  (fun i' => (((mp.certainTypeS hG).columnFamily
                    (Section16CharacterData.chi2enum hG mp tp j)).mu i' :
                    ClassFunction ↥mp.S ℂ))
            _ = _ := ((mp.certainTypeS hG).induce_restrict_certainType_eq _).symm
        · intro hjne hsub
          have hχ₂ne : Section16CharacterData.chi2enum hG mp tp j ≠ 1 := by
            rw [← Section16CharacterData.chi2enum_zero hG mp tp]
            exact fun h => hjne ((Section16CharacterData.chi2enum hG mp tp).injective h)
          refine (mp.certainTypeS hG).not_subset_characterKernel_chiRestrict_of_ne_one
            hχ₂ne ?_
          have hseq : ((tp.W2.subgroupOf mp.S).subgroupOf
                ((derivedInG mp.S).subgroupOf mp.S))
              = (((mp.certainTypeS hG).W2).subgroupOf
                ((derivedInG mp.S).subgroupOf mp.S)) := by
            rw [Section16CharacterData.certainTypeS_W2_eq hG mp, tp.W2_eq_Kstar hG]
          exact hseq ▸ hsub
      mu_reducible_dichotomy := Section16CharacterData.muS_reducible_dichotomy hG mp tp
      nu_definition := Section16CharacterData.nuT_definition hG mp tp
      tau3_isometry := Section16CharacterData.tau3W_isometry hG mp tp
      tau3_trivial := Section16CharacterData.tau3W_trivial hG mp tp
      tau3_apply_of_regular := fun α w hwW hnot =>
        Section16CharacterData.tau3W_apply_of_regular hG mp tp α w hwW hnot
      tau3_mem_ZIrr := fun _ hz => Section16CharacterData.tau3W_mem_ZIrr hG mp tp hz
      omega_orthonormal := Section16CharacterData.omegaS_inner hG mp tp
      omega_apply_one := Section16CharacterData.omegaS_apply_one hG mp tp
      omega_mem_ZIrr := Section16CharacterData.omegaS_mem_ZIrr hG mp tp
      omega_mul := Section16CharacterData.omegaS_mul hG mp tp
      omega_col_zero_apply_of_mem_W2 :=
        Section16CharacterData.omegaS_col_zero_apply_of_mem_W2 hG mp tp
      omega_row_zero_apply_of_mem_W1 :=
        Section16CharacterData.omegaS_row_zero_apply_of_mem_W1 hG mp tp
      omega_pow_q_of_mem_W1 := Section16CharacterData.omegaS_pow_q_of_mem_W1 hG mp tp
      omega_pow_p_of_mem_W2 := Section16CharacterData.omegaS_pow_p_of_mem_W2 hG mp tp
      eta_complete_vanish := fun χ horth w hwW hnot =>
        Section16CharacterData.tau3W_omegaS_complete_vanish hG mp tp χ horth hwW hnot
      eta_fourcorner_vanish := fun i j hi hj x hx =>
        Section16CharacterData.tau3W_omegaS_fourcorner_vanish hG mp tp i j hi hj (by
          intro hmem
          obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hmem
          obtain ⟨c, hc⟩ := isConj_iff.mp hconj
          exact hx (OddOrder.GroupTheory.mem_conjClassSet.mpr ⟨a, ha, c, hc⟩))
      eta_row_vanish_of_one_zero := fun x h0 i hi =>
        Section16CharacterData.tau3W_omegaS_row_vanish_of_one_zero hG mp tp h0 i hi
      eta_row_galois_orbit :=
        Section16CharacterData.tau3W_omegaS_row_galois_orbit hG mp tp
      eta_column_galois_orbit :=
        Section16CharacterData.tau3W_omegaS_column_galois_orbit hG mp tp
      eta_intCast_of_coprime := fun g hg i j =>
        Section16CharacterData.tau3W_omegaS_intCast_of_coprime hG mp tp i j hg
      eta_pair_of_coprime := fun g hg i j =>
        Section16CharacterData.tau3W_omegaS_pair_of_coprime hG mp tp i j hg
      eta_principal_of_coprime := fun g hg =>
        Section16CharacterData.tau3W_omegaS_principal_of_coprime hG mp tp hg }

/-- **Assembly of `Section16Inputs` from the three lane producers** (`sorry`-free).
Each field of `Section16Inputs` is sourced from exactly one of `mp` / `tp` / `cd`;
the character fields unify because `mp.S, mp.T, tp.W, tp.q, tp.p` are the chosen
witnesses. -/
noncomputable def section16Inputs_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) : Section16Inputs G :=
  let mp := section16MaximalPair_of_isMinimalSimpleOdd hG
  let tp := section16TypePStructure_of_isMinimalSimpleOdd hG mp
  let cd := section16CharacterData_of_isMinimalSimpleOdd hG mp tp
  { S := mp.S
    T := mp.T
    W1 := tp.W1
    W2 := tp.W2
    W := tp.W
    U := tp.U
    V := tp.V
    S_maximal := mp.S_maximal
    T_maximal := mp.T_maximal
    S_ne_T := mp.S_ne_T
    S_nonI := mp.S_nonI
    T_nonI := mp.T_nonI
    one_typeII := mp.one_typeII
    S_typeP2 := mp.S_typeP2
    theorem88_caseB := mp.theorem88_caseB
    W_eq_inter := tp.W_eq_inter
    W_eq_join := tp.W_eq_join
    W1_inf_W2_eq_bot := tp.W1_inf_W2_eq_bot
    W1_commutes_W2 := tp.W1_commutes_W2
    W_cyclic := tp.W_cyclic
    S_deriv_eq_PU := tp.S_deriv_eq_PU
    T_deriv_eq_QV := tp.T_deriv_eq_QV
    V_inf_Q_eq_bot := tp.V_inf_Q_eq_bot
    W2_isComplement_T_deriv := tp.W2_isComplement_T_deriv
    W1_normalizes_U := tp.W1_normalizes_U
    W2_normalizes_V := tp.W2_normalizes_V
    q := tp.q
    p := tp.p
    q_prime := tp.q_prime
    p_prime := tp.p_prime
    q_eq_card_W1 := tp.q_eq_card_W1
    p_eq_card_W2 := tp.p_eq_card_W2
    u := tp.u
    v := tp.v
    c := tp.c
    d := tp.d
    c_eq_card_C := tp.c_eq_card_C
    d_eq_card_D := tp.d_eq_card_D
    card_U_eq_uc := tp.card_U_eq_uc
    card_V_eq_vd := tp.card_V_eq_vd
    Sset := cd.Sset
    Tset := cd.Tset
    A0S := cd.A0S
    A0T := cd.A0T
    tauS := cd.tauS
    tauT := cd.tauT
    omega := cd.omega
    mu := cd.mu
    nu := cd.nu
    delta := cd.delta
    deltaPrime := cd.deltaPrime
    delta_pm_one := cd.delta_pm_one
    mu_degree_modEq_delta := cd.mu_degree_modEq_delta
    delta_zero_eq_one := cd.delta_zero_eq_one
    tau3 := cd.tau3
    mu_definition := cd.mu_definition
    mu_irreducible := cd.mu_irreducible
    mu_col_injective := cd.mu_col_injective
    mu_orthonormal := cd.mu_orthonormal
    mu_diff_support := cd.mu_diff_support
    mu_apply_of_not_mem_W2 := cd.mu_apply_of_not_mem_W2
    mu_conj := cd.mu_conj
    tau3_omega_conj := cd.tau3_omega_conj
    mu_colSum_eq_induce := cd.mu_colSum_eq_induce
    mu_reducible_dichotomy := cd.mu_reducible_dichotomy
    nu_definition := cd.nu_definition
    q_lt_p := tp.q_lt_p
    Sdata := tp.Sdata
    Sdata_U_eq := tp.Sdata_U_eq
    Sdata_W1_eq := tp.Sdata_W1_eq
    S_U_commutative := tp.S_U_commutative
    Sdata_W2_eq := tp.Sdata_W2_eq
    tau3_isometry := cd.tau3_isometry
    tau3_trivial := cd.tau3_trivial
    tau3_apply_of_regular := cd.tau3_apply_of_regular
    tau3_mem_ZIrr := cd.tau3_mem_ZIrr
    omega_orthonormal := cd.omega_orthonormal
    omega_apply_one := cd.omega_apply_one
    omega_mem_ZIrr := cd.omega_mem_ZIrr
    omega_mul := cd.omega_mul
    omega_col_zero_apply_of_mem_W2 := cd.omega_col_zero_apply_of_mem_W2
    omega_row_zero_apply_of_mem_W1 := cd.omega_row_zero_apply_of_mem_W1
    omega_pow_q_of_mem_W1 := cd.omega_pow_q_of_mem_W1
    omega_pow_p_of_mem_W2 := cd.omega_pow_p_of_mem_W2
    eta_complete_vanish := cd.eta_complete_vanish
    eta_fourcorner_vanish := cd.eta_fourcorner_vanish
    eta_row_vanish_of_one_zero := cd.eta_row_vanish_of_one_zero
    eta_row_galois_orbit := cd.eta_row_galois_orbit
    eta_column_galois_orbit := cd.eta_column_galois_orbit
    eta_intCast_of_coprime := cd.eta_intCast_of_coprime
    eta_pair_of_coprime := cd.eta_pair_of_coprime
    eta_principal_of_coprime := cd.eta_principal_of_coprime }

/-- **Assembly of the Section 16 configuration from named inputs** (`sorry`-free).

Given the `Section16Inputs` witnesses, this builds `Peterfalvi.S16.Hypothesis`
without any `sorry`.  Beyond carrying the input fields, it *derives* the fields of
`Peterfalvi.S15.Hypothesis` that are not independent data:

* `finiteG` from the ambient `[Finite G]`;
* the Fitting kernels `P := F(S)`, `Q := F(T)` (`maxNilpotentNormalHall`) and the
  centralizer complements `C := U ∩ C_G(P)`, `D := V ∩ C_G(Q)` definitionally, so
  `P_eq_SF`, `Q_eq_TF`, `C_eq`, `D_eq` are `rfl` — they are determined by
  `S, T, U, V`, not separate data;
* `q_odd`, `p_odd` from `Odd |G|` (subgroup orders divide `|G|`);
* `eta := τ₃ ∘ ω`, discharging **Peterfalvi (13.1.d)** `η_{ij} = ω_{ij}^{τ₃}`
  definitionally — `η` is the τ₃-image of the `ω`-grid, not separate data;
* `m` as the **(13.10)/(13.11)** rational formula in `p, q`, with `m_eq` by `rfl`.

These derivations are why `Section16Inputs` is a *strictly smaller* obligation
than `Peterfalvi.S16.Hypothesis`: discharging the menu does not require separately
producing `P, Q, C, D`, `η`, `m`, or the oddness facts. -/
noncomputable def sectionSixteenHypothesis_of_inputs {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (inp : Section16Inputs G) :
    Peterfalvi.S16.Hypothesis (G := G) where
  base :=
    { S := inp.S
      T := inp.T
      W1 := inp.W1
      W2 := inp.W2
      W := inp.W
      P := maxNilpotentNormalHall inp.S
      Q := maxNilpotentNormalHall inp.T
      U := inp.U
      V := inp.V
      C := inp.U ⊓ Subgroup.centralizer (maxNilpotentNormalHall inp.S : Set G)
      D := inp.V ⊓ Subgroup.centralizer (maxNilpotentNormalHall inp.T : Set G)
      S_maximal := inp.S_maximal
      T_maximal := inp.T_maximal
      S_ne_T := inp.S_ne_T
      S_nonI := inp.S_nonI
      T_nonI := inp.T_nonI
      one_typeII := inp.one_typeII
      S_typeP2 := inp.S_typeP2
      theorem88_caseB := inp.theorem88_caseB
      W_eq_inter := inp.W_eq_inter
      W_eq_join := inp.W_eq_join
      W1_inf_W2_eq_bot := inp.W1_inf_W2_eq_bot
      W1_commutes_W2 := inp.W1_commutes_W2
      W_cyclic := inp.W_cyclic
      P_eq_SF := rfl
      Q_eq_TF := rfl
      S_deriv_eq_PU := inp.S_deriv_eq_PU
      T_deriv_eq_QV := inp.T_deriv_eq_QV
      Q_inf_V_eq_bot := inp.V_inf_Q_eq_bot
      W2_isComplement_T_deriv := inp.W2_isComplement_T_deriv
      C_eq := rfl
      D_eq := rfl
      W1_normalizes_U := inp.W1_normalizes_U
      W2_normalizes_V := inp.W2_normalizes_V
      q := inp.q
      p := inp.p
      q_prime := inp.q_prime
      p_prime := inp.p_prime
      q_odd := by
        rw [inp.q_eq_card_W1]
        exact hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card inp.W1)
      p_odd := by
        rw [inp.p_eq_card_W2]
        exact hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card inp.W2)
      q_eq_card_W1 := inp.q_eq_card_W1
      p_eq_card_W2 := inp.p_eq_card_W2
      u := inp.u
      v := inp.v
      c := inp.c
      d := inp.d
      c_eq_card_C := inp.c_eq_card_C
      d_eq_card_D := inp.d_eq_card_D
      card_U_eq_uc := inp.card_U_eq_uc
      card_V_eq_vd := inp.card_V_eq_vd
      Sset := inp.Sset
      Tset := inp.Tset
      A0S := inp.A0S
      A0T := inp.A0T
      tauS := inp.tauS
      tauT := inp.tauT
      omega := inp.omega
      eta := fun i j => inp.tau3 (inp.omega i j)
      mu := inp.mu
      nu := inp.nu
      delta := inp.delta
      deltaPrime := inp.deltaPrime
      delta_pm_one := inp.delta_pm_one
      mu_degree_modEq_delta := inp.mu_degree_modEq_delta
      delta_zero_eq_one := inp.delta_zero_eq_one
      tau3 := inp.tau3
      eta_eq_tau_omega := fun _ _ => rfl
      mu_definition := inp.mu_definition
      mu_irreducible := inp.mu_irreducible
      mu_col_injective := inp.mu_col_injective
      mu_orthonormal := inp.mu_orthonormal
      mu_diff_support := inp.mu_diff_support
      mu_apply_of_not_mem_W2 := inp.mu_apply_of_not_mem_W2
      mu_conj := inp.mu_conj
      eta_conj := inp.tau3_omega_conj
      mu_colSum_eq_induce := inp.mu_colSum_eq_induce
      mu_reducible_dichotomy := inp.mu_reducible_dichotomy
      nu_definition := inp.nu_definition
      m := 1 - 1 / ((inp.q : ℚ) - 1) - ((inp.q : ℚ) - 1) / (inp.q : ℚ) ^ inp.p +
        1 / (((inp.q : ℚ) - 1) * (inp.q : ℚ) ^ inp.p)
      m_eq := rfl
      Sdata := inp.Sdata
      Sdata_U_eq := inp.Sdata_U_eq
      Sdata_W1_eq := inp.Sdata_W1_eq
      S_U_commutative := inp.S_U_commutative
      Sdata_W2_eq := inp.Sdata_W2_eq
      tau3_isometry := inp.tau3_isometry
      tau3_trivial := inp.tau3_trivial
      tau3_apply_of_regular := inp.tau3_apply_of_regular
      tau3_mem_ZIrr := inp.tau3_mem_ZIrr
      omega_orthonormal := inp.omega_orthonormal
      omega_apply_one := inp.omega_apply_one
      omega_mem_ZIrr := inp.omega_mem_ZIrr
      omega_mul := inp.omega_mul
      omega_col_zero_apply_of_mem_W2 := inp.omega_col_zero_apply_of_mem_W2
      omega_row_zero_apply_of_mem_W1 := inp.omega_row_zero_apply_of_mem_W1
      omega_pow_q_of_mem_W1 := inp.omega_pow_q_of_mem_W1
      omega_pow_p_of_mem_W2 := inp.omega_pow_p_of_mem_W2
      eta_complete_vanish := inp.eta_complete_vanish
      eta_fourcorner_vanish := inp.eta_fourcorner_vanish
      eta_row_vanish_of_one_zero := inp.eta_row_vanish_of_one_zero
      eta_row_galois_orbit := inp.eta_row_galois_orbit
      eta_column_galois_orbit := inp.eta_column_galois_orbit
      eta_intCast_of_coprime := inp.eta_intCast_of_coprime
      eta_pair_of_coprime := inp.eta_pair_of_coprime
      eta_principal_of_coprime := inp.eta_principal_of_coprime }
  q_lt_p := inp.q_lt_p

/-- **The one remaining upstream obligation.** From a minimal simple group of odd
order, the Bender–Glauberman local analysis (BG §7–§16) together with Peterfalvi's
character theory (Peterfalvi §3–§16) constructs the Section 16 field-normalizer
configuration of Peterfalvi (14.2).

In gated-endpoint-skeleton form: the `sorry`-free `sectionSixteenHypothesis_of_inputs`
already performs the assembly, so the only thing missing is a `Section16Inputs G`
witness — the explicit menu of §7–§16 obligations.  This single `sorry` is what the
whole remaining project targets.

Everything *downstream* of this point is already formalized:
`noMinimalSimpleOdd_of_section16` feeds the configuration into BG Appendix C, which
contradicts the standing inequality `q < p`. -/
noncomputable def sectionSixteenHypothesis_of_isMinimalSimpleOdd
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) :
    Peterfalvi.S16.Hypothesis (G := G) :=
  sectionSixteenHypothesis_of_inputs hG.odd (section16Inputs_of_isMinimalSimpleOdd hG)

end

/-- **No minimal simple group of odd order exists.** Combining the upstream
construction of the Section 16 configuration
(`sectionSixteenHypothesis_of_isMinimalSimpleOdd`) with the already-formalized
final contradiction (`noMinimalSimpleOdd_of_section16`). -/
theorem noMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) : False :=
  noMinimalSimpleOdd_of_section16 hG (sectionSixteenHypothesis_of_isMinimalSimpleOdd hG)

/-! ## The minimal-counterexample reduction -/

/-- **Minimal-counterexample reduction** (pure group theory, `sorry`-free).

If no minimal simple group of odd order exists, then every finite group of odd
order is solvable.

The proof is strong induction on `Nat.card G`. If `G` were a non-solvable group of
odd order, then — using the induction hypothesis on its (smaller, odd-order) proper
subgroups and proper quotients — every proper subgroup is solvable and `G` is
simple: a proper nontrivial normal subgroup `N` would make `G` an extension of the
solvable group `N` by the solvable group `G ⧸ N`, hence solvable
(`solvable_of_ker_le_range`). Thus `G` would be a minimal simple group of odd
order, contradicting the hypothesis `hno`. -/
theorem feitThompson_of_noMinimalSimpleOdd
    (hno : ∀ (H : Type u) [Group H] [Finite H], IsMinimalSimpleOdd H → False)
    {G : Type u} [Group G] [Finite G] (hodd : Odd (Nat.card G)) :
    IsSolvable G := by
  -- Strong induction on the order, generalized over all groups in this universe.
  suffices key : ∀ (n : ℕ) (K : Type u) [Group K] [Finite K],
      Nat.card K = n → Odd (Nat.card K) → IsSolvable K from key (Nat.card G) G rfl hodd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K _ _ hcard hodd'
    subst hcard
    by_contra hns
    -- `K` is nontrivial: a subsingleton group is solvable.
    have hNT : Nontrivial K := by
      by_contra hc
      rw [not_nontrivial_iff_subsingleton] at hc
      haveI := hc
      exact hns inferInstance
    -- `K` is simple: a proper nontrivial normal subgroup splits `K` as a solvable
    -- extension of a solvable group, making `K` solvable.
    have hsimple : IsSimpleGroup K := by
      refine { toNontrivial := hNT, eq_bot_or_eq_top_of_normal := fun N hN => ?_ }
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨hNbot, hNtop⟩ := hcon
      -- `N` is solvable (proper subgroup of odd order, induction hypothesis).
      have hN_odd : Odd (Nat.card ↥N) :=
        hodd'.of_dvd_nat (Subgroup.card_subgroup_dvd_card N)
      have hNlt : Nat.card ↥N < Nat.card K := by
        have hidx : 1 < N.index := Subgroup.one_lt_index_of_ne_top hNtop
        have h := lt_mul_of_one_lt_right (Nat.card_pos (α := ↥N)) hidx
        rwa [Subgroup.card_mul_index] at h
      haveI : IsSolvable ↥N := ih (Nat.card ↥N) hNlt ↥N rfl hN_odd
      -- `K ⧸ N` is solvable (proper quotient of odd order, induction hypothesis).
      have hQ_odd : Odd (Nat.card (K ⧸ N)) :=
        hodd'.of_dvd_nat (Subgroup.card_quotient_dvd_card N)
      have hQlt : Nat.card (K ⧸ N) < Nat.card K := by
        have hN1 : 1 < Nat.card ↥N :=
          Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot N).mpr hNbot)
        have h := lt_mul_of_one_lt_right (Nat.card_pos (α := K ⧸ N)) hN1
        rwa [← Subgroup.card_eq_card_quotient_mul_card_subgroup] at h
      haveI : IsSolvable (K ⧸ N) := ih (Nat.card (K ⧸ N)) hQlt (K ⧸ N) rfl hQ_odd
      -- Extension of a solvable group by a solvable group is solvable.
      have hfg : (QuotientGroup.mk' N).ker ≤ (N.subtype).range :=
        le_of_eq ((QuotientGroup.ker_mk' N).trans (Subgroup.subtype_range N).symm)
      exact hns (solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) hfg)
    -- Every proper subgroup is solvable (smaller, odd order, induction hypothesis).
    have hproper : ∀ M : Subgroup K, M < ⊤ → IsSolvable ↥M := by
      intro M hM
      have hM_odd : Odd (Nat.card ↥M) :=
        hodd'.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
      have hMlt : Nat.card ↥M < Nat.card K := by
        have hidx : 1 < M.index := Subgroup.one_lt_index_of_ne_top (ne_of_lt hM)
        have h := lt_mul_of_one_lt_right (Nat.card_pos (α := ↥M)) hidx
        rwa [Subgroup.card_mul_index] at h
      exact ih (Nat.card ↥M) hMlt ↥M rfl hM_odd
    -- `K` is then a minimal simple group of odd order — impossible.
    exact hno K ⟨hodd', hsimple, hns, hproper⟩

/-! ## The Feit–Thompson theorem -/

/-- **Feit-Thompson theorem**: every finite group of odd order is solvable.

This combines the `sorry`-free minimal-counterexample reduction
(`feitThompson_of_noMinimalSimpleOdd`) with the non-existence of a minimal simple
group of odd order (`noMinimalSimpleOdd`), the latter currently resting on the
single upstream obligation `sectionSixteenHypothesis_of_isMinimalSimpleOdd`. -/
theorem feitThompson {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) :
    IsSolvable G :=
  feitThompson_of_noMinimalSimpleOdd (fun _ _ _ hG => noMinimalSimpleOdd hG) hodd

end OddOrder
