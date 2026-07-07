/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_NormSet
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroupQuotient
import OddOrder.GroupTheory.RepresentationTheory.OrbitOnIrr
import OddOrder.GroupTheory.RepresentationTheory.SingerField
import OddOrder.Peterfalvi.S15_SAndT
import OddOrder.Peterfalvi.S16_CaseBOrder
import OddOrder.Peterfalvi.S16_NonExistenceGCore
import OddOrder.Peterfalvi.S16_G0Coprime
import OddOrder.Peterfalvi.S16_GridExpansion
import OddOrder.Peterfalvi.S16_PairingBessel

/-!
# Peterfalvi Section 16: Non-existence of G — tail (14.3)--(14.16)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 16, pp. 87--92.

This file holds the tail of Section 16: the subgroup `L` over `N_G(U)`
((14.3)--(14.7)), the case-B character cascade, the orthogonality switch, and
the final field-normalizer structure theorem `field_normalizer_structure`
(Peterfalvi (14.2)) together with `nonexistence_of_G`.  The section hypothesis
`Hypothesis`, the `FieldNormalizerData` structure, and the BG Appendix C
finite-field model machinery live in the frozen upstream core
`OddOrder.Peterfalvi.S16_NonExistenceGCore` (hub prefix-split 2026-06-15).
-/

namespace OddOrder.Peterfalvi.S16
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]

/-! ## (14.3)--(14.7): the subgroup `L` over `N_G(U)` -/

/-- **Peterfalvi (14.3)**: the type-I maximal subgroup `L` containing `N_G(U)`,
its Fitting kernel `H`, the Dade extension, and the three virtual characters
`beta_S`, `beta_T`, and `beta_L`. -/
structure LHypothesis (hyp : Hypothesis (G := G)) where
  L : Subgroup G
  H : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  normalizer_U_le_L : Subgroup.normalizer (hyp.base.U : Set G) ≤ L
  H_eq_LF : H = maxNilpotentNormalHall L
  typeI_data : OddOrder.Peterfalvi.S15.TypeIOverNormalizerData hyp.base
  typeI_data_L_eq : typeI_data.L = L
  typeI_data_H_eq : typeI_data.H = H
  typeI_complement_card_eq_pq :
    Nat.card ↥typeI_data.frobenius.complement = hyp.base.p * hyp.base.q

namespace LHypothesis

/-- The subgroup `L` supplied in **Peterfalvi (14.3)** is type I, as witnessed
by the Frobenius data inherited from (13.17). -/
theorem isTypeI {hyp : Hypothesis (G := G)} (Ldata : LHypothesis hyp) :
    IsTypeI Ldata.L := by
  rw [← Ldata.typeI_data_L_eq]
  exact ⟨Ldata.typeI_data.frobenius.typeI⟩

end LHypothesis

/-! ### (14.9) `calT1` structural foundation

The Coq `FTtypeP_min_typeII` body (PFsection14.v:737--853) opens `calT1 = seqIndD QV T QV Q` with
three purely group-theoretic facts about `QV = T' = derivedInG T` that are *independent* of the
character/coherence/Γ-bridge machinery:

* `QV ◁ T` with `[T : QV] = p` (Coq `index_sdprod defT`, `p = |W2|` via `W2_isComplement_T_deriv`) —
  this is `calT1_1p`'s degree factor.
* `Q ⋊ V = QV` (Coq `defQV`, from `T_deriv_eq_QV` + `Q_inf_V_eq_bot`), giving `QV/Q ≅ V` and hence
  `|QV/Q| = |V|` (Coq `card_isog (sdprod_isog defQV)`) — the source of the abelian-quotient irr count.
* `QV/Q` abelian (Coq `isog_abelian (sdprod_isog defQV)`, `V` abelian) — makes every `QV/Q`-irr
  linear, so `calT1_1p`'s inflated sources have degree one and `Ind_{QV}^T` has degree `[T:QV] = p`.

These are landed below as reusable named helpers (`T_derived_index_eq_p`,
`T_Q_isComplement_V_derived`, `T_card_quot_Q_derived_eq_card_V`).  They feed a future `calT1` build
but do **not** on their own close (14.9); see the blocker map on `T_typeIII_ratio_le`. -/

/-- **The `T`-side derived complement `T = T' ⋊ W₂`, index `[T : T'] = p`** (Coq
`index_sdprod defT`, `p = |W2|`).  From the base `W2_isComplement_T_deriv` (`T' ⋊ W₂ = T`, available
ungated at the §16 construction) and `p = |W2|` (`p_eq_card_W2`).  The degree factor of Coq
`calT1_1p` (`Ind_{QV}^T θ (1) = [T:QV]·θ(1) = p` for linear `θ`). -/
theorem T_derived_index_eq_p (hyp : Hypothesis (G := G)) :
    ((derivedInG hyp.base.T).subgroupOf hyp.base.T).index = hyp.base.p := by
  have hW2_le_T : hyp.base.W2 ≤ hyp.base.T := by
    have h1 : hyp.base.W2 ≤ hyp.base.W := by rw [hyp.base.W_eq_join]; exact le_sup_right
    have h2 : hyp.base.W ≤ hyp.base.T := by rw [hyp.base.W_eq_inter]; exact inf_le_right
    exact h1.trans h2
  rw [hyp.base.W2_isComplement_T_deriv.symm.index_eq_card,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2_le_T).toEquiv, hyp.base.p_eq_card_W2]

/-- **`Q.subgroupOf QV` is normal in `QV = T' = derivedInG T`** (`Q = T_F` normalized by `T ⊇ T'`).
The normality feeding the `QV/Q` quotient (Coq `nsQQV`). -/
theorem T_Q_subgroupOf_derived_normal (hyp : Hypothesis (G := G)) :
    (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).Normal := by
  have hQ_le : hyp.base.Q ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_left
  have hM'_le_T : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hT_le_NQ : hyp.base.T ≤ Subgroup.normalizer (hyp.base.Q : Set G) := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)

/-- **The `T`-side complement `Q ⋊ V = QV = T'`** (Coq `defQV`): `Q` (normal in `T'`, being `T_F`
restricted) and `V` complement inside `derivedInG T`, from `Q ⊔ V = T'` (`T_deriv_eq_QV`) and
`Q ⊓ V = ⊥` (`Q_inf_V_eq_bot`).  The `sdprod` giving `QV/Q ≅ V`.  Mirrors the complement built inside
`S15.coprime_card_V_card_Q_of_disjoint`. -/
theorem T_Q_isComplement_V_derived [Finite G] (hyp : Hypothesis (G := G)) :
    Subgroup.IsComplement' (hyp.base.Q.subgroupOf (derivedInG hyp.base.T))
      (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) := by
  have hQ_le : hyp.base.Q ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.base.V ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right
  haveI := T_Q_subgroupOf_derived_normal hyp
  have hQnVn_inf : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) ⊓
      (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) = ⊥ := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
      OneMemClass.coe_one]
    refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
    have hxQV : x ∈ (hyp.base.Q ⊓ hyp.base.V : Subgroup G) := ⟨hxQ, hxV⟩
    rwa [hyp.base.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
  have hQnVn_sup : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) ⊔
      (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.base.T_deriv_eq_QV.symm,
      Subgroup.subgroupOf_self]
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hQnVn_inf)
  have hmul := Subgroup.normal_mul (hyp.base.Q.subgroupOf (derivedInG hyp.base.T))
    (hyp.base.V.subgroupOf (derivedInG hyp.base.T))
  rw [hQnVn_sup, Subgroup.coe_top] at hmul
  exact hmul.symm

/-- **`|QV/Q| = |V|`** (Coq `card_isog (sdprod_isog defQV)`): the quotient of `QV = T'` by `Q` has
the order of the complement `V`.  The source of the abelian-quotient irreducible count `v − 1`
(nonprincipal `QV/Q`-irreducibles) in Coq `size calT1 = (v.-1) %/ p`. -/
theorem T_card_quot_Q_derived_eq_card_V [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card (↥(derivedInG hyp.base.T) ⧸ (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)))
      = Nat.card ↥hyp.base.V := by
  have hV_le : hyp.base.V ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right
  haveI := T_Q_subgroupOf_derived_normal hyp
  -- `QV/Q ≅ V.subgroupOf QV` via the complement (`Q` normal in the `K`-slot).
  rw [Nat.card_congr (T_Q_isComplement_V_derived hyp).symm.QuotientMulEquiv.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le).toEquiv]

/-- **`(QV = T')` is normal in `↥T` with index `p`** (`T = T' ⋊ W₂`, `p = |W₂|`).  The
`↥T`-side normal subgroup and the `[T:QV] = p` degree/orbit factor consumed by the `calT1` count,
repackaged from `T_derived_index_eq_p` as a statement about `(derivedInG T).subgroupOf T`
(the shape `card_image_induce_eq_div` needs: `H.index` for `H ◁ ↥T`). -/
theorem T_derivedSubgroupOf_normal (hyp : Hypothesis (G := G)) :
    ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal := by
  rw [show (derivedInG hyp.base.T).subgroupOf hyp.base.T = _root_.commutator ↥hyp.base.T by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective hyp.base.T.subtype_injective]]
  infer_instance

open scoped Classical in
/-- **The `calT1` orbit count, ungated engine** — Peterfalvi (14.9), Coq
`PFsection14.v:836--845` `size calT1 = (v.-1) %/ p`, the *cardinality* half.

Given any conjugation-invariant `Finset` `𝒯 ⊆ Irr(QV)` (`QV = T' = derivedInG T`, normal in `↥T`)
whose every member induces irreducibly to `T` (equivalently has inertia `I_T(θ) = QV`), the map
`θ ↦ Ind_{QV}^T θ` is exactly `[T:QV] = p`-to-one onto its image, so

  `|{Ind_{QV}^T θ | θ ∈ 𝒯}| = |𝒯| / p`.

This is the direct §16 specialization of the shared-infra orbit count
`RepresentationTheory.card_image_induce_eq_div` with `G := ↥T`, `H := QV.subgroupOf T`, and the
index `[T:QV] = p` plugged in via `T_derived_index_eq_p`.  It is **ungated** (no `IsTypeII`/`IsTypeP2`
input, no `sorry`): the two facts entering are supplied by the caller as `𝒯`'s
conjugation-invariance and irreducible-induction (inertia `= QV`) hypotheses.  For the `calT1`
assembly `𝒯` is the non-principal inflated `Irr(QV/Q)`-family, `|𝒯| = |V| − 1`
(the `|Irr(QV/Q)| = |QV/Q| = |V|` count, gated on `V` abelian — see the blocker map on
`T_typeIII_ratio_le`), yielding `|calT1| = (|V| − 1)/p`.

The `Fintype`/`Invertible` instances are taken explicitly (satisfiable from `Finite G`) so the
`induce`-image in the statement type-checks, matching the shared-infra convention. -/
theorem calT1_image_induce_card_eq [Finite G] (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T] [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hQVnormal : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal)
    (𝒯 : Finset (OddOrder.RepresentationTheory.IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hconj : ∀ θ ∈ 𝒯, ∀ g : ↥hyp.base.T,
      OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy
        (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) g θ ∈ 𝒯)
    (hinertia : ∀ θ ∈ 𝒯,
      OddOrder.RepresentationTheory.IrreducibleCharacter.inertia
          (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T) :
    (𝒯.image (fun θ => OddOrder.RepresentationTheory.ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)).card
      = 𝒯.card / hyp.base.p := by
  haveI := hQVnormal
  -- The shared-infra orbit count `|image| = |𝒯| / [T:QV]`, with `[T:QV] = p`.
  rw [OddOrder.RepresentationTheory.card_image_induce_eq_div 𝒯 hconj hinertia,
    T_derived_index_eq_p hyp]

/-- **Inflation-through-quotient inertia via a Frobenius quotient** (general reusable brick, the
Coq `irr_induced_Frobenius_ker` ∘ `injm_Frobenius_ker` core, PFsection14.v:757--762).

For `N ◁ G`, `H ◁ G` with `N ≤ H`, if the quotient `G/N` is a **Frobenius group** with kernel
`H/N = H.map (mk' N)` (any complement `A'`), then every *non-principal* `θ̄ ∈ Irr(H/N)` inflates
(along a quotient-corestriction `q : ↥H →* ↥(H/N)`, `(q x : G/N) = mk' N x`) to a character of `H`
whose inertia group in `G` is exactly `H`:

  `I_G(inflate_q θ̄) = H`.

Proof: `inertia_eq_of_frobeniusGroup` gives `I_{G/N}(θ̄) = H/N`; the inertia/inflation bridge
`mem_inertia_compHom_iff` transfers `g ∈ I_G(inflate θ̄) ↔ mk' N g ∈ I_{G/N}(θ̄) = H/N`, and
`comap (mk' N) (H.map (mk' N)) = H` (as `N = ker (mk' N) ≤ H`) closes the membership.

This is the inertia input feeding the `calT1` orbit count (`calT1_image_induce_card_eq`): with
`G := ↥T`, `N := Q.subgroupOf T`, `H := QV.subgroupOf T` (`QV = T'`), and the quotient Frobenius
`T/Q = (QV/Q) ⋊ (W₂Q/Q)` sourced *ungated* from the intrinsic type-III datum's `U ⋊ W₁` Frobenius
(`T_typeIII_UW1_frobenius`), it gives `I_T(inflate θ) = QV` for each non-principal inflated
`θ ∈ Irr(QV/Q)`. -/
theorem inertia_inflate_eq_of_frobeniusQuotient {Γ : Type*} [Group Γ] [Finite Γ]
    {N H : Subgroup Γ} [N.Normal] [H.Normal] (hNH : N ≤ H)
    {A' : Subgroup (Γ ⧸ N)}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (Γ ⧸ N)
      (H.map (QuotientGroup.mk' N)) A')
    (q : ↥H →* ↥(H.map (QuotientGroup.mk' N)))
    (hq : ∀ x : ↥H, ((q x : Γ ⧸ N)) = QuotientGroup.mk' N (x : Γ))
    (hqinj : Function.Injective (OddOrder.RepresentationTheory.ClassFunction.compHom q :
      OddOrder.RepresentationTheory.ClassFunction ↥(H.map (QuotientGroup.mk' N)) ℂ →
        OddOrder.RepresentationTheory.ClassFunction ↥H ℂ))
    (θbar : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(H.map (QuotientGroup.mk' N)))
    (hθne : θbar ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter _) :
    OddOrder.RepresentationTheory.ClassFunction.inertia (G := Γ) (H := H)
        (OddOrder.RepresentationTheory.ClassFunction.compHom q
          (θbar : OddOrder.RepresentationTheory.ClassFunction _ ℂ)) = H := by
  haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  haveI : Fintype ↥(H.map (QuotientGroup.mk' N)) := Fintype.ofFinite _
  -- Frobenius ⟹ `I_{Γ/N}(θ̄) = H/N`.
  have hIbar : OddOrder.RepresentationTheory.ClassFunction.inertia
      (G := Γ ⧸ N) (H := H.map (QuotientGroup.mk' N))
      (θbar : OddOrder.RepresentationTheory.ClassFunction _ ℂ) = H.map (QuotientGroup.mk' N) :=
    OddOrder.RepresentationTheory.inertia_eq_of_frobeniusGroup hfrob hθne
  ext g
  rw [OddOrder.RepresentationTheory.mem_inertia_compHom_iff q hq hqinj
    (θbar : OddOrder.RepresentationTheory.ClassFunction _ ℂ) g, hIbar]
  constructor
  · intro hmem
    have hcm : g ∈ Subgroup.comap (QuotientGroup.mk' N) (H.map (QuotientGroup.mk' N)) := hmem
    rwa [Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hNH)] at hcm
  · intro hg
    exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩

/-- **The intrinsic type-III `U ⋊ W₁` Frobenius** (ungated).  From `hIII : IsTypeIII T` take the
*intrinsic* datum `td = hIII.some : TypeIIIData T`; its `td.typeP.U ⋊ td.typeP.W₁` is a Frobenius
group (Peterfalvi Def (8.4), `S11.typeP_uW1_frobenius` fed the non-triviality `td.common.1`).

Crucially this **avoids** the sorried T-side reconciliation `S15.reconciled_typePData_T` (which is
what gated the abstract-`V`/`W₂` route): the datum `td` comes straight from `IsTypeIII T` with no
reconciliation to the abstract Hypothesis fields `V`/`W₂`.  It is the ungated source of the quotient
Frobenius `T/Q` needed for `inertia_inflate_eq_of_frobeniusQuotient`.  (Coq `frobVW2`.) -/
theorem T_typeIII_UW1_frobenius {M : Subgroup G} (td : OddOrder.GroupTheory.TypeIIIData M) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(td.typeP.U ⊔ td.typeP.W1)
      (td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1))
      (td.typeP.W1.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) :=
  OddOrder.Peterfalvi.S11.typeP_uW1_frobenius td.typeP td.common.1

/-- **The intrinsic type-III cyclic factor has order `p`** (ungated): `|td.typeP.W₁| = [T:T'] = p`.
`td.typeP.W₁` complements `T' = derivedInG T` in `T` (`M_complement`), so `|W₁| = [T:T']`
(`card_W1_eq_derived_index`), and `[T:T'] = p` (`T_derived_index_eq_p`).  This is the orbit-size /
degree factor of `calT1` (Coq `index_sdprod defT`, `p = |W₂|`; note the intrinsic `.W₁` is the
`T'`-complement, matching Coq's `W₂` — the abstract-Hypothesis `W₂` — **not** the abstract `W₁`). -/
theorem T_typeIII_card_W1 [Finite G] (hyp : Hypothesis (G := G))
    (td : OddOrder.GroupTheory.TypeIIIData hyp.base.T) :
    Nat.card ↥td.typeP.W1 = hyp.base.p := by
  rw [td.typeP.card_W1_eq_derived_index, T_derived_index_eq_p hyp]

/-- **The intrinsic type-III complement has order `|V|`** (ungated, canonical): `|td.typeP.U| = |V|`.
`|td.typeP.U| = [T' : M_F]` (`card_U_eq_index`, `M_F = Q`), and `[T' : M_F] = |QV/Q| = |V|`
(`Subgroup.index_eq_card` + `T_card_quot_Q_derived_eq_card_V`).  The equality is **canonical** — both
sides are the intrinsic index `[T':M_F]` — so it needs *no* reconciliation of `td.typeP.U` with the
abstract `V` (the source of `calT1`'s abelian-quotient count `size = (v−1)/p`). -/
theorem T_typeIII_card_U [Finite G] (hyp : Hypothesis (G := G))
    (td : OddOrder.GroupTheory.TypeIIIData hyp.base.T) :
    Nat.card ↥td.typeP.U = Nat.card ↥hyp.base.V := by
  rw [td.typeP.card_U_eq_index, ← hyp.base.Q_eq_TF, Subgroup.index_eq_card]
  exact T_card_quot_Q_derived_eq_card_V hyp

/-- **`Q = M_F` is complemented by the intrinsic `U ⊔ W₁` in `T`** (ungated): `T = Q ⋊ (U ⋊ W₁)`.
The semidirect tower `T = T' ⋊ W₁` (`M_complement`) and `T' = M_F ⋊ U` (`derived_complement`,
`Q = M_F`) compose to a complement of the *normal* `Q` by `U ⊔ W₁`.

* **Disjoint** `Q ⊓ (U ⊔ W₁) = ⊥`: an element lies in `Q ≤ T'`, so in `(U ⊔ W₁) ⊓ T'`, which is `U`
  (decompose in the Frobenius complement `U ⋊ W₁`: the `W₁`-part lands in `W₁ ⊓ T' = ⊥`), and then in
  `Q ⊓ U = M_F ⊓ U = ⊥` (`derived_complement`).
* **Order** `|Q|·|U ⊔ W₁| = |T|`: `|U ⊔ W₁| = |U|·|W₁|` (Frobenius complement), `|M_F|·|U| = |T'|`
  (`derived_complement`), `|T'|·|W₁| = |T|` (`M_complement`).

This is the iso `↥T ⧸ (Q.subgroupOf T) ≃* ↥(U ⊔ W₁)` powering the quotient Frobenius `T/Q` (via
`isFrobeniusGroup_map_equiv` on `T_typeIII_UW1_frobenius`) feeding
`inertia_inflate_eq_of_frobeniusQuotient`. -/
theorem T_typeIII_Q_isComplement_UW1 [Finite G] (hyp : Hypothesis (G := G))
    (td : OddOrder.GroupTheory.TypeIIIData hyp.base.T) :
    Subgroup.IsComplement' (hyp.base.Q.subgroupOf hyp.base.T)
      ((td.typeP.U ⊔ td.typeP.W1).subgroupOf hyp.base.T) := by
  classical
  have hHeqQ : td.typeP.H = hyp.base.Q := by rw [td.typeP.H_eq, hyp.base.Q_eq_TF]
  have hHle : td.typeP.H ≤ derivedInG hyp.base.T := td.typeP.H_le
  have hUleM' : td.typeP.U ≤ derivedInG hyp.base.T := td.typeP.U_le
  have hM'leM : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hQleM : hyp.base.Q ≤ hyp.base.T := hHeqQ ▸ (hHle.trans hM'leM)
  have hW1leM : td.typeP.W1 ≤ hyp.base.T := td.typeP.W1_le
  have hUW1leM : td.typeP.U ⊔ td.typeP.W1 ≤ hyp.base.T := sup_le (hUleM'.trans hM'leM) hW1leM
  -- `W₁ ⊓ T' = ⊥` (from `M_complement`).
  have hW1M' : td.typeP.W1 ⊓ derivedInG hyp.base.T = ⊥ := by
    have hd := td.typeP.M_complement.disjoint; rw [disjoint_iff] at hd
    rw [eq_bot_iff]; intro x hx; rw [Subgroup.mem_inf] at hx
    have hxM : x ∈ hyp.base.T := hM'leM hx.2
    have : (⟨x, hxM⟩ : ↥hyp.base.T) ∈ ((derivedInG hyp.base.T).subgroupOf hyp.base.T) ⊓
        (td.typeP.W1.subgroupOf hyp.base.T) := by
      rw [Subgroup.mem_inf]
      exact ⟨Subgroup.mem_subgroupOf.mpr hx.2, Subgroup.mem_subgroupOf.mpr hx.1⟩
    rw [hd, Subgroup.mem_bot] at this; rw [Subgroup.mem_bot]; exact Subtype.ext_iff.mp this
  -- `M_F ⊓ U = ⊥` (from `derived_complement`).
  have hHU : td.typeP.H ⊓ td.typeP.U = ⊥ := by
    have hd := td.typeP.derived_complement.disjoint; rw [disjoint_iff] at hd
    rw [eq_bot_iff]; intro x hx; rw [Subgroup.mem_inf] at hx
    have hxM' : x ∈ derivedInG hyp.base.T := hHle hx.1
    have : (⟨x, hxM'⟩ : ↥(derivedInG hyp.base.T)) ∈ (td.typeP.H.subgroupOf (derivedInG hyp.base.T)) ⊓
        (td.typeP.U.subgroupOf (derivedInG hyp.base.T)) := by
      rw [Subgroup.mem_inf]
      exact ⟨Subgroup.mem_subgroupOf.mpr hx.1, Subgroup.mem_subgroupOf.mpr hx.2⟩
    rw [hd, Subgroup.mem_bot] at this; rw [Subgroup.mem_bot]; exact Subtype.ext_iff.mp this
  -- `(U ⊔ W₁) ⊓ T' ≤ U` (Frobenius decomposition).
  have hUW1M'_le_U : (td.typeP.U ⊔ td.typeP.W1) ⊓ derivedInG hyp.base.T ≤ td.typeP.U := by
    intro x hx; obtain ⟨hxUW1, hxM'⟩ := hx
    have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius td.typeP td.common.1
    obtain ⟨⟨u, w⟩, hgw⟩ := (hfrob.isComplement.existsUnique ⟨x, hxUW1⟩).exists
    have huU : ((u : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) ∈ td.typeP.U := Subgroup.mem_subgroupOf.mp u.2
    have hwW1 : ((w : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) ∈ td.typeP.W1 :=
      Subgroup.mem_subgroupOf.mp w.2
    have hxeq : x = ((u : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) *
        ((w : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) := by
      have := congrArg (Subtype.val) hgw; simpa using this.symm
    have hwM' : ((w : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) ∈ derivedInG hyp.base.T := by
      have he : ((w : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) =
          ((u : ↥(td.typeP.U ⊔ td.typeP.W1)) : G)⁻¹ * x := by rw [hxeq]; group
      rw [he]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (td.typeP.U_le huU)) hxM'
    have hw1 : ((w : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) = 1 := by
      have : ((w : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) ∈ td.typeP.W1 ⊓ derivedInG hyp.base.T :=
        ⟨hwW1, hwM'⟩
      rw [hW1M', Subgroup.mem_bot] at this; exact this
    rw [hxeq, hw1, mul_one]; exact huU
  -- Disjointness of the two `subgroupOf T`.
  have hdisj : Disjoint (hyp.base.Q.subgroupOf hyp.base.T)
      ((td.typeP.U ⊔ td.typeP.W1).subgroupOf hyp.base.T) := by
    rw [disjoint_iff, eq_bot_iff]; intro x hx; rw [Subgroup.mem_inf] at hx
    have hxQ : (x : G) ∈ hyp.base.Q := Subgroup.mem_subgroupOf.mp hx.1
    have hxUW1 : (x : G) ∈ td.typeP.U ⊔ td.typeP.W1 := Subgroup.mem_subgroupOf.mp hx.2
    have hxM' : (x : G) ∈ derivedInG hyp.base.T := hHle (hHeqQ ▸ hxQ)
    have hxU : (x : G) ∈ td.typeP.U := hUW1M'_le_U ⟨hxUW1, hxM'⟩
    have hmem : (x : G) ∈ td.typeP.H ⊓ td.typeP.U := ⟨hHeqQ ▸ hxQ, hxU⟩
    rw [hHU, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; exact Subtype.ext hmem
  -- Cardinality `|Q|·|U ⊔ W₁| = |T|`.
  have hcardUW1 : Nat.card ↥(td.typeP.U ⊔ td.typeP.W1) =
      Nat.card ↥td.typeP.U * Nat.card ↥td.typeP.W1 := by
    rw [← (OddOrder.Peterfalvi.S11.typeP_uW1_frobenius td.typeP td.common.1).isComplement.card_mul,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
  have hcardM' : Nat.card ↥td.typeP.H * Nat.card ↥td.typeP.U = Nat.card ↥(derivedInG hyp.base.T) := by
    rw [← td.typeP.derived_complement.card_mul,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleM').toEquiv]
  have hcardM : Nat.card ↥(derivedInG hyp.base.T) * Nat.card ↥td.typeP.W1 = Nat.card ↥hyp.base.T := by
    rw [← td.typeP.M_complement.card_mul,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'leM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1leM).toEquiv]
  have hcard : Nat.card ↥(hyp.base.Q.subgroupOf hyp.base.T) *
      Nat.card ↥((td.typeP.U ⊔ td.typeP.W1).subgroupOf hyp.base.T) = Nat.card ↥hyp.base.T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW1leM).toEquiv, hcardUW1, ← hHeqQ,
      ← mul_assoc, hcardM', hcardM]
  exact Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdisj

/-- **The complement-iso `↥T ⧸ Q ≃* ↥(U ⊔ W₁)` sends `U` onto `T'/Q`** (ungated).  The iso
`e := (subgroupOfEquivOfLe).symm.trans (QuotientMulEquiv).symm` built from the `Q`-complement
(`T_typeIII_Q_isComplement_UW1`) satisfies `e x = mk' Q ↑x` (definitionally), and carries the
Frobenius kernel `U.subgroupOf (U ⊔ W₁)` onto `(T'.subgroupOf T).map (mk' Q) = T'/Q`:

* `⊆`: `e x = mk' Q ↑x` with `↑x ∈ U ≤ T'`;
* `⊇`: a coset `mk' Q ↑t'` (`t' ∈ T'`) decomposes `t' = q·u` in `T' = Q ⋊ U`
  (`derived_complement`), so `mk' Q ↑t' = mk' Q ↑u` (`q ∈ Q` killed, `u⁻¹ q u ∈ Q` by normality),
  the image of `u ∈ U`.

This is the kernel identity feeding `isFrobeniusGroup_map_equiv` (on `T_typeIII_UW1_frobenius`) to
produce the quotient Frobenius `T/Q` with kernel `T'/Q` for
`inertia_inflate_eq_of_frobeniusQuotient`. -/
theorem T_typeIII_quotFrobenius_kernel_eq [Finite G] (hyp : Hypothesis (G := G))
    (td : OddOrder.GroupTheory.TypeIIIData hyp.base.T)
    (hQnormal : (hyp.base.Q.subgroupOf hyp.base.T).Normal)
    (hUW1leM : td.typeP.U ⊔ td.typeP.W1 ≤ hyp.base.T) :
    ((td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1)).map
      ((Subgroup.subgroupOfEquivOfLe hUW1leM).symm.trans
        (T_typeIII_Q_isComplement_UW1 hyp td).symm.QuotientMulEquiv.symm).toMonoidHom) =
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T).map
        (QuotientGroup.mk' (hyp.base.Q.subgroupOf hyp.base.T)) := by
  haveI := hQnormal
  have hHeqQ : td.typeP.H = hyp.base.Q := by rw [td.typeP.H_eq, hyp.base.Q_eq_TF]
  have hUleUW1 : td.typeP.U ≤ td.typeP.U ⊔ td.typeP.W1 := le_sup_left
  have hQleT : hyp.base.Q ≤ hyp.base.T := hHeqQ ▸ (td.typeP.H_le.trans (Subgroup.map_subtype_le _))
  set e : ↥(td.typeP.U ⊔ td.typeP.W1) ≃* (↥hyp.base.T ⧸ hyp.base.Q.subgroupOf hyp.base.T) :=
    (Subgroup.subgroupOfEquivOfLe hUW1leM).symm.trans
      (T_typeIII_Q_isComplement_UW1 hyp td).symm.QuotientMulEquiv.symm with he_def
  have he : ∀ x : ↥(td.typeP.U ⊔ td.typeP.W1),
      e x = QuotientGroup.mk' (hyp.base.Q.subgroupOf hyp.base.T)
          (⟨(x : G), hUW1leM x.2⟩ : ↥hyp.base.T) := fun x => rfl
  apply le_antisymm
  · rintro _ ⟨x, hxU, rfl⟩
    show e x ∈ _
    rw [he]
    exact Subgroup.mem_map.mpr ⟨⟨(x : G), hUW1leM x.2⟩,
      Subgroup.mem_subgroupOf.mpr (td.typeP.U_le (Subgroup.mem_subgroupOf.mp hxU)), rfl⟩
  · rintro _ ⟨t', ht', rfl⟩
    have ht'M' : (t' : G) ∈ derivedInG hyp.base.T := Subgroup.mem_subgroupOf.mp ht'
    obtain ⟨⟨qq, uu⟩, hdec⟩ :=
      (td.typeP.derived_complement.existsUnique ⟨(t':G), ht'M'⟩).exists
    have huuU : ((uu : ↥(derivedInG hyp.base.T)) : G) ∈ td.typeP.U :=
      Subgroup.mem_subgroupOf.mp uu.2
    have hqqQ : ((qq : ↥(derivedInG hyp.base.T)) : G) ∈ hyp.base.Q :=
      hHeqQ ▸ Subgroup.mem_subgroupOf.mp qq.2
    have hdecG : (t' : G) = ((qq : ↥(derivedInG hyp.base.T)) : G) *
        ((uu : ↥(derivedInG hyp.base.T)) : G) := by
      have := congrArg (Subtype.val) hdec; simpa using this.symm
    have huuT : ((uu : ↥(derivedInG hyp.base.T)) : G) ∈ hyp.base.T := hUW1leM (hUleUW1 huuU)
    set uUW1 : ↥(td.typeP.U ⊔ td.typeP.W1) := ⟨((uu : ↥(derivedInG hyp.base.T)) : G), hUleUW1 huuU⟩
      with huUW1def
    set uElt : ↥hyp.base.T := ⟨((uu : ↥(derivedInG hyp.base.T)) : G), huuT⟩ with huEltdef
    set qElt : ↥hyp.base.T := ⟨((qq : ↥(derivedInG hyp.base.T)) : G), hQleT hqqQ⟩ with hqEltdef
    have htElt : (⟨(t':G), t'.2⟩ : ↥hyp.base.T) = qElt * uElt := by
      apply Subtype.ext; simpa [hqEltdef, huEltdef] using hdecG
    refine Subgroup.mem_map.mpr ⟨uUW1, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mpr huuU), ?_⟩
    show e uUW1 = _
    rw [he]
    have hgoaleq : (⟨((uUW1 : ↥(td.typeP.U ⊔ td.typeP.W1)) : G), hUW1leM uUW1.2⟩ : ↥hyp.base.T)
        = uElt := rfl
    rw [hgoaleq]
    refine ((QuotientGroup.mk'_eq_mk' (hyp.base.Q.subgroupOf hyp.base.T)).mpr
      ⟨uElt⁻¹ * qElt * uElt, ?_, ?_⟩)
    · have hqQ' : qElt ∈ hyp.base.Q.subgroupOf hyp.base.T := by
        rw [Subgroup.mem_subgroupOf]; exact hqqQ
      have hconj := hQnormal.conj_mem qElt hqQ' uElt⁻¹
      simpa using hconj
    · have hg : uElt * (uElt⁻¹ * qElt * uElt) = qElt * uElt := by group
      rw [hg, ← htElt]

open scoped Classical in
/-- **Peterfalvi (14.9): `|calT1| = (|V| − 1)/p`** (Coq `PFsection14.v:836--845`
`size calT1 = (v.-1) %/ p`, the cardinality half) — **assembly skeleton, ungated**.

`calT1` is realized as the `Ind_{QV}^T`-image of the family `𝒯` of non-principal inflated
`Irr(QV/Q)`-characters (`QV = T' = derivedInG T`, `Q = M_F`).  Given the two remaining *ungated*
transcription facts as hypotheses — packaged so this carries **no `sorry`** and its consumers can
supply them from the intrinsic type-III datum `hIII.some` — the count is closed by the engine
`calT1_image_induce_card_eq` (`|image| = |𝒯|/p`) plus `|𝒯| = |V| − 1`:

* `hcard : 𝒯.card = Nat.card ↥hyp.base.V - 1` — the abelian-quotient count `|Irr(QV/Q)| = |QV/Q| =
  |V|` minus the principal character.  Ungated from `T_typeIII_card_U`
  (`|td.typeP.U| = |V|`, `td.U_commutative` making `QV/Q ≅ U` abelian so
  `card_irreducibleCharacter_eq_card_of_commGroup` applies) — **no** abstract-`V` abelianness / no
  `reconciled_typePData_T`.
* `hconj`/`hinertia` — `𝒯` is `↥T`-conjugation invariant and every member has inertia
  `I_T(inflate θ) = QV`.  The inertia fact is `inertia_inflate_eq_of_frobeniusQuotient` fed the
  quotient Frobenius `T/Q = (QV/Q) ⋊ (W₂Q/Q)`, itself transported (`isFrobeniusGroup_map_equiv`)
  from the intrinsic `U ⋊ W₁` Frobenius `T_typeIII_UW1_frobenius` through `mk' Q` (injective on
  `U ⊔ W₁` since `Q ⊓ (U ⊔ W₁) = ⊥`) — **all ungated** (Coq `frobVW2`/`injm_Frobenius_ker`).

`hp_pos` records `0 < p` (from `hyp.base.p_prime`) to discharge the `/p` division exactness.  This
skeleton is the honest §16 assembly point: it consumes only the verified ungated bricks
(`calT1_image_induce_card_eq`, `T_typeIII_card_U`, `T_typeIII_UW1_frobenius`,
`inertia_inflate_eq_of_frobeniusQuotient`), leaving `hcard`/`hconj`/`hinertia` as the precisely
scoped *transcription* residual (not a gate) — the `Q`-complement iso-transport building `𝒯` and
its two properties.  Its output `(|V| − 1)/p` then feeds the (14.9) Γ-Bessel bound
`T_typeIII_ratio_le` (still gated additionally on the `v = |V|` (13.12) `d=1` substitution + the
S07 coherence package + the S-side `Γ` bridge). -/
theorem T_typeIII_calT1_card_eq [Finite G] (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T] [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hQVnormal : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal)
    (𝒯 : Finset (OddOrder.RepresentationTheory.IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hcard : 𝒯.card = Nat.card ↥hyp.base.V - 1)
    (hconj : ∀ θ ∈ 𝒯, ∀ g : ↥hyp.base.T,
      OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy
        (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) g θ ∈ 𝒯)
    (hinertia : ∀ θ ∈ 𝒯,
      OddOrder.RepresentationTheory.IrreducibleCharacter.inertia
          (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T) :
    (𝒯.image (fun θ => OddOrder.RepresentationTheory.ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)).card
      = (Nat.card ↥hyp.base.V - 1) / hyp.base.p := by
  rw [calT1_image_induce_card_eq hyp hQVnormal 𝒯 hconj hinertia, hcard]

open scoped IsMulCommutative in
open scoped Classical in
/-- **Peterfalvi (14.9): `|calT1| = (|V| − 1)/p`, fully proven** (Coq `PFsection14.v:836--845`
`size calT1 = (v.-1) %/ p`) — the cardinality half of (14.9), **end-to-end and ungated**.

There *exists* a family `𝒯 ⊆ Irr(QV)` (`QV = T' = derivedInG T`) — namely the inflations along the
corestriction `q : ↥QV →* ↥(QV/Q)` of the non-principal `Irr(QV/Q)` — whose `Ind_{QV}^T`-image
`calT1` has `|calT1| = (|V| − 1)/p`.  All three inputs of the orbit-count engine
`calT1_image_induce_card_eq` are discharged from the **intrinsic** type-III datum `td` (no abstract
`V`/`W₂`, no sorried `reconciled_typePData_T`):

* **inertia** `I_T(inflate θ̄) = QV`: `inertia_inflate_eq_of_frobeniusQuotient` fed the quotient
  Frobenius `T/Q`, transported (`isFrobeniusGroup_map_equiv`) from the intrinsic `U ⋊ W₁` Frobenius
  (`T_typeIII_UW1_frobenius`) through the complement iso `↥T/Q ≃* ↥(U ⊔ W₁)`
  (`T_typeIII_Q_isComplement_UW1`), with kernel identified by `T_typeIII_quotFrobenius_kernel_eq`;
* **conjugation-invariance**: `conjBy_compHom_eq_compHom_conjBy` carries conjugates of inflations to
  inflations of conjugates, preserving non-principality;
* **cardinality** `|𝒯| = |V| − 1`: inflation is injective (`compHom_injective_of_surjective`), and
  `|Irr(QV/Q)| = |QV/Q| = |V|` (`QV/Q ≅ U` abelian by `td.U_commutative`,
  `card_irreducibleCharacter_eq_card_of_commGroup`; `|U| = |V|` by `T_typeIII_card_U`), minus the
  principal character.

This closes the **cardinality** obligation of (14.9) with no parameterized hypotheses.  The full
ratio bound `T_typeIII_ratio_le` additionally needs `v = |V|` ((13.12) `d = 1`, lane-b), the T-side
`S07.Hypothesis` coherence package, and the S-side `Γ` bridge. -/
theorem T_typeIII_calT1_card [Finite G] (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T] [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (td : TypeIIIData hyp.base.T) :
    ∃ 𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)),
      (𝒯.image (fun θ => ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)).card
        = (Nat.card ↥hyp.base.V - 1) / hyp.base.p := by
  haveI := hyp.base.finiteG
  haveI hHnormal : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal :=
    T_derivedSubgroupOf_normal hyp
  have hQnormal : (hyp.base.Q.subgroupOf hyp.base.T).Normal := by
    have hQleT : hyp.base.Q ≤ hyp.base.T := by
      rw [hyp.base.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.base.T
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQleT).mpr ?_
    rw [hyp.base.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T
  haveI := hQnormal
  have hUW1leM : td.typeP.U ⊔ td.typeP.W1 ≤ hyp.base.T :=
    sup_le ((td.typeP.U_le).trans (Subgroup.map_subtype_le _)) td.typeP.W1_le
  have hNH : hyp.base.Q.subgroupOf hyp.base.T ≤ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
    intro x hx; rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hyp.base.T_deriv_eq_QV]; exact (le_sup_left : hyp.base.Q ≤ hyp.base.Q ⊔ hyp.base.V) hx
  set mkN := QuotientGroup.mk' (hyp.base.Q.subgroupOf hyp.base.T) with hmkN
  set Hbar := ((derivedInG hyp.base.T).subgroupOf hyp.base.T).map mkN with hHbar
  set q : ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) →* ↥Hbar :=
    (mkN.comp ((derivedInG hyp.base.T).subgroupOf hyp.base.T).subtype).codRestrict Hbar (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩) with hq_def
  have hq : ∀ x : ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T), ((q x : ↥Hbar) : ↥hyp.base.T ⧸ hyp.base.Q.subgroupOf hyp.base.T) = mkN (x : ↥hyp.base.T) := fun x => rfl
  have hq_surj : Function.Surjective q := by
    rintro ⟨z, hz⟩; rw [hHbar, Subgroup.mem_map] at hz
    obtain ⟨x, hxH, hxz⟩ := hz; exact ⟨⟨x, hxH⟩, Subtype.ext hxz⟩
  have hqinj : Function.Injective
      (ClassFunction.compHom q : ClassFunction ↥Hbar ℂ → ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ) :=
    ClassFunction.compHom_injective_of_surjective hq_surj
  -- quotient Frobenius, kernel = Hbar
  set e : ↥(td.typeP.U ⊔ td.typeP.W1) ≃* (↥hyp.base.T ⧸ hyp.base.Q.subgroupOf hyp.base.T) :=
    (Subgroup.subgroupOfEquivOfLe hUW1leM).symm.trans
      (T_typeIII_Q_isComplement_UW1 hyp td).symm.QuotientMulEquiv.symm with he_def
  have hfrobUW1 := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius td.typeP td.common.1
  have hqfrob0 := OddOrder.Isaacs.Ch06.isFrobeniusGroup_map_equiv hfrobUW1 e
  have himg := T_typeIII_quotFrobenius_kernel_eq hyp td hQnormal hUW1leM
  rw [show ((Subgroup.subgroupOfEquivOfLe hUW1leM).symm.trans
      (T_typeIII_Q_isComplement_UW1 hyp td).symm.QuotientMulEquiv.symm) = e from rfl] at himg
  rw [himg] at hqfrob0
  -- the inflation map on irreducibles
  set infl : IrreducibleCharacter ↥Hbar → IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) :=
    fun θbar => ⟨ClassFunction.compHom q (θbar : ClassFunction ↥Hbar ℂ),
      IsIrreducibleCharacter.compHom_of_surjective hq_surj θbar.isIrreducible⟩ with hinfl
  have hinfl_inj : Function.Injective infl := by
    intro a b hab
    have : ClassFunction.compHom q (a : ClassFunction ↥Hbar ℂ) =
        ClassFunction.compHom q (b : ClassFunction ↥Hbar ℂ) := congrArg Subtype.val hab
    exact IrreducibleCharacter.ext (hqinj this)
  -- 𝒯 := image of non-principal Irr(Hbar)
  refine ⟨(Finset.univ.filter (fun θbar : IrreducibleCharacter ↥Hbar =>
      θbar ≠ trivialIrreducibleCharacter ↥Hbar)).image infl, ?_⟩
  -- hconj, hinertia for members, hcard
  set 𝒯 := (Finset.univ.filter (fun θbar : IrreducibleCharacter ↥Hbar =>
      θbar ≠ trivialIrreducibleCharacter ↥Hbar)).image infl with h𝒯
  -- hinertia
  have hinertia : ∀ θ ∈ 𝒯,
      IrreducibleCharacter.inertia (G := ↥hyp.base.T) (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) θ = ((derivedInG hyp.base.T).subgroupOf hyp.base.T) := by
    intro θ hθ
    rw [h𝒯, Finset.mem_image] at hθ
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    rw [Finset.mem_filter] at hθbar
    exact inertia_inflate_eq_of_frobeniusQuotient (N := hyp.base.Q.subgroupOf hyp.base.T)
      (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) hNH hqfrob0 q hq hqinj θbar hθbar.2
  -- hconj
  have hconj : ∀ θ ∈ 𝒯, ∀ g : ↥hyp.base.T,
      IrreducibleCharacter.conjBy (G := ↥hyp.base.T) (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) g θ ∈ 𝒯 := by
    intro θ hθ g
    rw [h𝒯, Finset.mem_image] at hθ ⊢
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    rw [Finset.mem_filter] at hθbar
    -- conjBy (infl θbar) = infl (conjBy (mk g) θbar)
    refine ⟨IrreducibleCharacter.conjBy (G := ↥hyp.base.T ⧸ hyp.base.Q.subgroupOf hyp.base.T)
      (H := Hbar) (mkN g) θbar, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      -- conjBy preserves non-triviality
      intro hcontra
      apply hθbar.2
      -- conjBy (mk g) θbar = triv ⟹ θbar = triv (conjBy invertible)
      have := congrArg (IrreducibleCharacter.conjBy (mkN g)⁻¹) hcontra
      rwa [← IrreducibleCharacter.conjBy_mul, mul_inv_cancel, IrreducibleCharacter.conjBy_one,
        show IrreducibleCharacter.conjBy (mkN g)⁻¹ (trivialIrreducibleCharacter ↥Hbar) =
          trivialIrreducibleCharacter ↥Hbar from ?_] at this
      · apply IrreducibleCharacter.ext
        rw [IrreducibleCharacter.coe_conjBy]; ext x
        simp [ClassFunction.conjBy_apply, trivialIrreducibleCharacter, trivialClassFunction_apply]
    · -- infl (conjBy (mk g) θbar) = conjBy g (infl θbar)
      apply IrreducibleCharacter.ext
      show ClassFunction.compHom q _ = ClassFunction.conjBy g (ClassFunction.compHom q _)
      rw [conjBy_compHom_eq_compHom_conjBy q hq]
      rfl
  -- hcard : 𝒯.card = |V| - 1
  have hcard : 𝒯.card = Nat.card ↥hyp.base.V - 1 := by
    rw [h𝒯, Finset.card_image_of_injective _ hinfl_inj]
    -- |non-principal Irr(Hbar)| = |Irr Hbar| - 1
    -- |Irr Hbar| = |V| (abelian)
    haveI hUcomm : IsMulCommutative ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) :=
      OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (le_sup_left)).symm td.U_commutative
    have hemap : ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) ≃* ↥Hbar :=
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr himg)
    haveI hHbarComm : IsMulCommutative ↥Hbar :=
      OddOrder.GroupTheory.isMulCommutative_of_mulEquiv hemap hUcomm
    have hIrrHbar : Nat.card (IrreducibleCharacter ↥Hbar) = Nat.card ↥hyp.base.V := by
      rw [card_irreducibleCharacter_eq_card_of_commGroup, ← Nat.card_congr hemap.toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv, T_typeIII_card_U hyp td]
    -- |filter (≠triv) univ| = |univ| - 1
    have hfilter : (Finset.univ.filter (fun θbar : IrreducibleCharacter ↥Hbar =>
        θbar ≠ trivialIrreducibleCharacter ↥Hbar)).card = Fintype.card (IrreducibleCharacter ↥Hbar) - 1 := by
      rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [hfilter]
    have : Fintype.card (IrreducibleCharacter ↥Hbar) = Nat.card ↥hyp.base.V := by
      rw [Nat.card_eq_fintype_card] at hIrrHbar; exact hIrrHbar
    rw [this]
  -- wire into calT1_image_induce_card_eq
  rw [← hcard]
  exact calT1_image_induce_card_eq hyp hHnormal 𝒯 hconj hinertia

open scoped IsMulCommutative in
open scoped Classical in
/-- **Peterfalvi (14.9): the full `calT1` family data** (issue 9072, Stage-2 bridge) — the same
inflated `Irr(QV/Q)`-family `𝒯` as `T_typeIII_calT1_card`, but exposing *all* the predicates the
coherence assembler `T_typeIII_calT1_isCoherent` consumes, not just the count.  There *exists* a
`𝒯 ⊆ Irr(QV)` (the inflations of the non-principal `Irr(QV/Q)` along the quotient corestriction `q`)
with, for `θ ∈ 𝒯`:
* `hinertia : I_T(θ) = QV` (via `inertia_inflate_eq_of_frobeniusQuotient`, the quotient Frobenius);
* `hne : θ ≠ 1` (inflation of a non-principal `θ̄`, injective on `Irr`);
* `hlinear : θ(1) = 1` (inflation of a *linear* `θ̄`, since `QV/Q ≅ U` is abelian, `td.U_commutative`);
* `hconj𝒯 : θ̄ ∈ 𝒯` (**complex** conjugate, `compHom` commutes with `star`, and `Irr(QV/Q)` is
  complex-conj-closed with non-principality preserved);
and with the count `|calT1_image| = (|V| − 1)/p`.  This packages the "pure transcription" `𝒯`-build
so the (14.9) coherence carrier `horth` is dischargeable end-to-end. -/
theorem T_typeIII_calT1_family [Finite G] (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T] [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (td : TypeIIIData hyp.base.T) :
    ∃ 𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)),
      (∀ θ ∈ 𝒯,
        IrreducibleCharacter.inertia (G := ↥hyp.base.T)
            (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
          = (derivedInG hyp.base.T).subgroupOf hyp.base.T) ∧
      (∀ θ ∈ 𝒯, θ ≠ trivialIrreducibleCharacter _) ∧
      (∀ θ ∈ 𝒯, (θ.toClassFunction :
        ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1) ∧
      (∀ θ ∈ 𝒯,
        (⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
          θ.isIrreducible.conj⟩ :
          IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) ∈ 𝒯) ∧
      (𝒯.image (fun θ => ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)).card
        = (Nat.card ↥hyp.base.V - 1) / hyp.base.p := by
  haveI := hyp.base.finiteG
  haveI hHnormal : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal :=
    T_derivedSubgroupOf_normal hyp
  have hQnormal : (hyp.base.Q.subgroupOf hyp.base.T).Normal := by
    have hQleT : hyp.base.Q ≤ hyp.base.T := by
      rw [hyp.base.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.base.T
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQleT).mpr ?_
    rw [hyp.base.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T
  haveI := hQnormal
  have hUW1leM : td.typeP.U ⊔ td.typeP.W1 ≤ hyp.base.T :=
    sup_le ((td.typeP.U_le).trans (Subgroup.map_subtype_le _)) td.typeP.W1_le
  have hNH : hyp.base.Q.subgroupOf hyp.base.T ≤ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
    intro x hx; rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hyp.base.T_deriv_eq_QV]; exact (le_sup_left : hyp.base.Q ≤ hyp.base.Q ⊔ hyp.base.V) hx
  set mkN := QuotientGroup.mk' (hyp.base.Q.subgroupOf hyp.base.T) with hmkN
  set Hbar := ((derivedInG hyp.base.T).subgroupOf hyp.base.T).map mkN with hHbar
  set q : ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) →* ↥Hbar :=
    (mkN.comp ((derivedInG hyp.base.T).subgroupOf hyp.base.T).subtype).codRestrict Hbar
      (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩) with hq_def
  have hq : ∀ x : ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T),
      ((q x : ↥Hbar) : ↥hyp.base.T ⧸ hyp.base.Q.subgroupOf hyp.base.T) = mkN (x : ↥hyp.base.T) :=
    fun x => rfl
  have hq_surj : Function.Surjective q := by
    rintro ⟨z, hz⟩; rw [hHbar, Subgroup.mem_map] at hz
    obtain ⟨x, hxH, hxz⟩ := hz; exact ⟨⟨x, hxH⟩, Subtype.ext hxz⟩
  have hqinj : Function.Injective
      (ClassFunction.compHom q :
        ClassFunction ↥Hbar ℂ → ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ) :=
    ClassFunction.compHom_injective_of_surjective hq_surj
  set e : ↥(td.typeP.U ⊔ td.typeP.W1) ≃* (↥hyp.base.T ⧸ hyp.base.Q.subgroupOf hyp.base.T) :=
    (Subgroup.subgroupOfEquivOfLe hUW1leM).symm.trans
      (T_typeIII_Q_isComplement_UW1 hyp td).symm.QuotientMulEquiv.symm with he_def
  have hfrobUW1 := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius td.typeP td.common.1
  have hqfrob0 := OddOrder.Isaacs.Ch06.isFrobeniusGroup_map_equiv hfrobUW1 e
  have himg := T_typeIII_quotFrobenius_kernel_eq hyp td hQnormal hUW1leM
  rw [show ((Subgroup.subgroupOfEquivOfLe hUW1leM).symm.trans
      (T_typeIII_Q_isComplement_UW1 hyp td).symm.QuotientMulEquiv.symm) = e from rfl] at himg
  rw [himg] at hqfrob0
  set infl : IrreducibleCharacter ↥Hbar →
      IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) :=
    fun θbar => ⟨ClassFunction.compHom q (θbar : ClassFunction ↥Hbar ℂ),
      IsIrreducibleCharacter.compHom_of_surjective hq_surj θbar.isIrreducible⟩ with hinfl
  have hinfl_inj : Function.Injective infl := by
    intro a b hab
    have : ClassFunction.compHom q (a : ClassFunction ↥Hbar ℂ) =
        ClassFunction.compHom q (b : ClassFunction ↥Hbar ℂ) := congrArg Subtype.val hab
    exact IrreducibleCharacter.ext (hqinj this)
  set 𝒯 := (Finset.univ.filter (fun θbar : IrreducibleCharacter ↥Hbar =>
      θbar ≠ trivialIrreducibleCharacter ↥Hbar)).image infl with h𝒯
  refine ⟨𝒯, ?_, ?_, ?_, ?_, ?_⟩
  -- hinertia
  · intro θ hθ
    rw [h𝒯, Finset.mem_image] at hθ
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    rw [Finset.mem_filter] at hθbar
    exact inertia_inflate_eq_of_frobeniusQuotient (N := hyp.base.Q.subgroupOf hyp.base.T)
      (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) hNH hqfrob0 q hq hqinj θbar hθbar.2
  -- hne : `infl θbar ≠ 1` since `θbar ≠ 1` and `infl` is injective (`infl 1 = 1`).
  · intro θ hθ
    rw [h𝒯, Finset.mem_image] at hθ
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    rw [Finset.mem_filter] at hθbar
    intro hcontra
    apply hθbar.2
    -- `infl` injective + `infl (triv) = triv`, so `infl θbar = triv ⟹ θbar = triv`.
    apply hinfl_inj
    rw [hcontra]
    -- `infl (triv Hbar) = triv QV`: pointwise `compHom q (triv) x = triv (q x) = 1 = triv x`.
    apply IrreducibleCharacter.ext
    ext x
    simp [hinfl, ClassFunction.compHom_apply, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      trivialClassFunction_apply]
  -- hlinear : `(infl θbar)(1) = θbar (q 1) = θbar 1 = 1` (θbar linear, `Hbar` abelian).
  · intro θ hθ
    rw [h𝒯, Finset.mem_image] at hθ
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    -- `Hbar ≅ U` abelian.
    haveI hUcomm : IsMulCommutative ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) :=
      OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (le_sup_left)).symm td.U_commutative
    have hemap : ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) ≃* ↥Hbar :=
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr himg)
    haveI hHbarComm : IsMulCommutative ↥Hbar :=
      OddOrder.GroupTheory.isMulCommutative_of_mulEquiv hemap hUcomm
    show (ClassFunction.compHom q (θbar : ClassFunction ↥Hbar ℂ) :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1
    rw [ClassFunction.compHom_apply, map_one]
    exact θbar.isIrreducible.apply_one_eq_one_of_isMulCommutative
  -- hconj𝒯 : `(infl θbar).conj = infl (θbar.conj)` and `θbar.conj` non-principal ∈ filter.
  · intro θ hθ
    rw [h𝒯, Finset.mem_image] at hθ ⊢
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    rw [Finset.mem_filter] at hθbar
    refine ⟨⟨(θbar : ClassFunction ↥Hbar ℂ).conj, θbar.isIrreducible.conj⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      -- `θbar̄ ≠ 1`: else `θbar = θbar̄̄ = 1̄ = 1`.
      intro hcontra
      apply hθbar.2
      have hcoe : (θbar : ClassFunction ↥Hbar ℂ).conj = trivialClassFunction ↥Hbar := by
        simpa using congrArg (fun c : IrreducibleCharacter ↥Hbar => (c : ClassFunction ↥Hbar ℂ))
          hcontra
      apply IrreducibleCharacter.ext
      show (θbar : ClassFunction ↥Hbar ℂ) = trivialClassFunction ↥Hbar
      rw [← ClassFunction.conj_conj (θbar : ClassFunction ↥Hbar ℂ), hcoe]
      exact trivialClassFunction_isReal
    · -- `infl (θbar̄) = (infl θbar)^`: pointwise `compHom q θbar̄ x = star (θbar (q x))`.
      apply IrreducibleCharacter.ext
      show ClassFunction.compHom q ((θbar : ClassFunction ↥Hbar ℂ).conj)
        = (ClassFunction.compHom q (θbar : ClassFunction ↥Hbar ℂ)).conj
      ext x
      simp [ClassFunction.compHom_apply, ClassFunction.conj_apply]
  -- hcard : `|calT1_image| = (|V| − 1)/p`.
  · have hinertia : ∀ θ ∈ 𝒯,
        IrreducibleCharacter.inertia (G := ↥hyp.base.T)
            (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) θ
          = ((derivedInG hyp.base.T).subgroupOf hyp.base.T) := by
      intro θ hθ
      rw [h𝒯, Finset.mem_image] at hθ
      obtain ⟨θbar, hθbar, rfl⟩ := hθ
      rw [Finset.mem_filter] at hθbar
      exact inertia_inflate_eq_of_frobeniusQuotient (N := hyp.base.Q.subgroupOf hyp.base.T)
        (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) hNH hqfrob0 q hq hqinj θbar hθbar.2
    have hconj : ∀ θ ∈ 𝒯, ∀ g : ↥hyp.base.T,
        IrreducibleCharacter.conjBy
          (G := ↥hyp.base.T) (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) g θ ∈ 𝒯 := by
      intro θ hθ g
      rw [h𝒯, Finset.mem_image] at hθ ⊢
      obtain ⟨θbar, hθbar, rfl⟩ := hθ
      rw [Finset.mem_filter] at hθbar
      refine ⟨IrreducibleCharacter.conjBy (G := ↥hyp.base.T ⧸ hyp.base.Q.subgroupOf hyp.base.T)
        (H := Hbar) (mkN g) θbar, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hcontra
        apply hθbar.2
        have := congrArg (IrreducibleCharacter.conjBy (mkN g)⁻¹) hcontra
        rwa [← IrreducibleCharacter.conjBy_mul, mul_inv_cancel, IrreducibleCharacter.conjBy_one,
          show IrreducibleCharacter.conjBy (mkN g)⁻¹ (trivialIrreducibleCharacter ↥Hbar) =
            trivialIrreducibleCharacter ↥Hbar from ?_] at this
        · apply IrreducibleCharacter.ext
          rw [IrreducibleCharacter.coe_conjBy]; ext x
          simp [ClassFunction.conjBy_apply, trivialIrreducibleCharacter, trivialClassFunction_apply]
      · apply IrreducibleCharacter.ext
        show ClassFunction.compHom q _ = ClassFunction.conjBy g (ClassFunction.compHom q _)
        rw [conjBy_compHom_eq_compHom_conjBy q hq]
        rfl
    have hcard : 𝒯.card = Nat.card ↥hyp.base.V - 1 := by
      rw [h𝒯, Finset.card_image_of_injective _ hinfl_inj]
      haveI hUcomm : IsMulCommutative ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) :=
        OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe (le_sup_left)).symm td.U_commutative
      have hemap : ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) ≃* ↥Hbar :=
        (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
          (MulEquiv.subgroupCongr himg)
      haveI hHbarComm : IsMulCommutative ↥Hbar :=
        OddOrder.GroupTheory.isMulCommutative_of_mulEquiv hemap hUcomm
      have hIrrHbar : Nat.card (IrreducibleCharacter ↥Hbar) = Nat.card ↥hyp.base.V := by
        rw [card_irreducibleCharacter_eq_card_of_commGroup, ← Nat.card_congr hemap.toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv, T_typeIII_card_U hyp td]
      have hfilter : (Finset.univ.filter (fun θbar : IrreducibleCharacter ↥Hbar =>
          θbar ≠ trivialIrreducibleCharacter ↥Hbar)).card
          = Fintype.card (IrreducibleCharacter ↥Hbar) - 1 := by
        rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      rw [hfilter]
      have : Fintype.card (IrreducibleCharacter ↥Hbar) = Nat.card ↥hyp.base.V := by
        rw [Nat.card_eq_fintype_card] at hIrrHbar; exact hIrrHbar
      rw [this]
    rw [← hcard]
    exact calT1_image_induce_card_eq hyp hHnormal 𝒯 hconj hinertia

/-- **The intrinsic type-III kernel size bound `2p + 1 ≤ |V|`** (ungated, the crude `hcard2` input).
The intrinsic `U ⋊ W₁` Frobenius (`T_typeIII_UW1_frobenius`) has odd kernel `U` (`|U| = |V|`,
`T_typeIII_card_U`) and odd complement `W₁` (`|W₁| = p`, `T_typeIII_card_W1`); the odd-order Frobenius
size condition `IsFrobeniusGroup.two_mul_card_complement_add_one_le_card_kernel` (`|A| ∣ |N|−1`, and
`|N|−1` even with `|A|` odd forces `|N|−1 ≥ 2|A|`) then gives `2p + 1 ≤ |V|`.

This is the **ungated** source of the `calT1` crude size bound `2 ≤ (|V|−1)/p` (`hcard2` in
`T_typeIII_ratio_le`): it needs only oddness (subgroups of the odd `G`) plus the intrinsic Frobenius
index `[T:T'] = p` — **not** the lane-b-gated `|V|`-lower-bound `v = (q^p−1)/(q−1)` (13.15).  (The
`v`-value is still needed for the *exact* count `(v−1)/p`, but the coherence input `hcard2` only needs
`≥ 2`.) -/
theorem T_typeIII_two_p_add_one_le_card_V [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (td : OddOrder.GroupTheory.TypeIIIData hyp.base.T) :
    2 * hyp.base.p + 1 ≤ Nat.card ↥hyp.base.V := by
  haveI := hyp.base.finiteG
  have hfrob := T_typeIII_UW1_frobenius td
  have hVodd : Odd (Nat.card ↥hyp.base.V) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.base.V)
  -- Kernel `|U.subgroupOf| = |U| = |V|`, complement `|W₁.subgroupOf| = |W₁| = p`.
  have hcardN : Nat.card ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1))
      = Nat.card ↥hyp.base.V := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv, T_typeIII_card_U hyp td]
  have hcardA : Nat.card ↥(td.typeP.W1.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) = hyp.base.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv, T_typeIII_card_W1 hyp td]
  have hNodd : Odd (Nat.card ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1))) := by
    rw [hcardN]; exact hVodd
  have hAodd : Odd (Nat.card ↥(td.typeP.W1.subgroupOf (td.typeP.U ⊔ td.typeP.W1))) := by
    rw [hcardA]; exact hyp.base.p_odd
  have h := hfrob.two_mul_card_complement_add_one_le_card_kernel hNodd hAodd hfrob.ne_bot_kernel
  rwa [hcardN, hcardA] at h

/-! ### T-side type-`P` Dade isometry foundation (14.9), issue 9072

The (14.9) coherence carrier `horth` in `T_typeIII_ratio_le` needs a T-side Dade package
`S07.Hypothesis calT1_set A` carrying the isometry `tauT`.  The three lemmas below build that
package's **foundation** — the genuine §10 Dade support datum on `T`, the resulting integral
character map `τ_T`, and its difference-isometry property — from the **ungated** σ-sharp Dade
support builder `S10.dadeSupportHypothesisData_of_subset_sigmaSharp` (issue 9072 hub verdict).

The support set is `A = A₁(T) = T_σ^# = sigmaSharp T` (BG `M̃`-core), which trivially satisfies the
builder's `X ⊆ sigmaSharp T` (reflexivity) and is `T`-conjugation-invariant (`M_σ ⊴ T`), and is
nonempty (`M_σ ≠ ⊥`).  This mirrors the type-I `S14.Hypothesis.tau`/`Sset_tau_isometry_diff`
assembly (built from `S10.dadeSupportHypotheses_typeI`) but is driven by the σ-generic engine so it
does not need a `TypeIData`/`TypePData` witness. -/

/-- **T-side (8.15) Dade support datum on `A₁(T) = T_σ^#`** (issue 9072 foundation, step 1).
The ungated σ-sharp Dade builder `S10.dadeSupportHypothesisData_of_subset_sigmaSharp` applied at
`X = sigmaSharp T`: `hXσ` is reflexivity, `hXne` follows from `M_σ ≠ ⊥`
(`S10.Msigma_ne_bot`), and `hXiff` is `T`-conjugation invariance of `T_σ^#` via
`sharpSubgroup_conj_mem` (`M_σ ⊴ T`, `le_normalizer_opiCoreInG`). -/
theorem tSideDadeSupport_nonempty [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nonempty (OddOrder.Peterfalvi.S10.DadeSupportHypothesisData hyp.base.T
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T)) := by
  haveI := hyp.base.finiteG
  -- `T ≤ N_G(M_σ(T))` (`M_σ = O_{σ}(T)` is normal in `T`), so `M_σ^#` is `T`-conj-invariant.
  have hTnorm : hyp.base.T ≤ Subgroup.normalizer
      ((OddOrder.BG.Ch3.S10.Msigma hyp.base.T : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma hyp.base.T) hyp.base.T
  refine OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_of_subset_sigmaSharp hG
    hyp.base.T_maximal (fun _ h => h) ?_ ?_
  · -- Nonempty: pick a nonidentity element of `M_σ(T) ≠ ⊥`.
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hyp.base.T_maximal)
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    exact ⟨a.1, (Set.mem_diff _).mpr
      ⟨SetLike.mem_coe.mpr a.2, fun h => ha1' (Set.mem_singleton_iff.mp h)⟩⟩
  · -- `T`-conjugation invariance of `T_σ^# = sharpSubgroup (M_σ T)`.
    intro m x hm
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h2 := OddOrder.Peterfalvi.S10.sharpSubgroup_conj_mem
        (H := OddOrder.BG.Ch3.S10.Msigma hyp.base.T) (hTnorm (inv_mem hm)) h
      have h3 : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
      rwa [h3] at h2
    · exact OddOrder.Peterfalvi.S10.sharpSubgroup_conj_mem
        (H := OddOrder.BG.Ch3.S10.Msigma hyp.base.T) (hTnorm hm) h

open scoped Classical in
/-- **T-side type-`P` Dade integral character map `τ_T`** (issue 9072 foundation, step 2).
The genuine §7 integral character map of the (8.15) support datum
(`tSideDadeSupport_nonempty`), pinned exactly as the type-I `S14.Hypothesis.tau`:
`τ_T = dadeIntegralCharacterMap dadeData.dade (dadeData.dade.fullDadeIsometryData dadeData.hconj)`.
This is the `tauT` field of the T-side `S07.Hypothesis calT1_set (sigmaSharp T)` package that
`T_typeIII_calT1_coherent`/`T_typeIII_ratio_le`'s `horth` carrier consumes. -/
noncomputable def tSideDadeMap (hyp : Hypothesis (G := G)) [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥hyp.base.T) G :=
  haveI := hyp.base.finiteG
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (tSideDadeSupport_nonempty hG hyp).some.dade
    ((tSideDadeSupport_nonempty hG hyp).some.dade.fullDadeIsometryData
      (tSideDadeSupport_nonempty hG hyp).some.hconj)

open scoped Classical in
/-- **`τ_T` is a difference-isometry on any `A₁(T)`-supported family** (issue 9072 foundation,
step 3) — the `tau_isometry_diff`/`hiso` input of `S07.irrSubcoherent` (and of
`coherent_of_constant_degree`).  For a family `S` all of whose member-difference class functions
`a − b` (`a, b ∈ S`) are supported in `supportInSubgroup (sigmaSharp T) T = A₁(T)`, the genuine §10
Dade isometry preserves their inner products, via
`S07.dadeIntegralCharacterMap_inner_eq_on_supported_span`.  This mirrors `S14.Sset_tau_isometry_diff`
exactly (both reduce to the same supported-span inner-preservation lemma); the family-supportedness
hypothesis packages the (14.9) fact that `calT1` member differences vanish off `T^#`. -/
theorem tSideDadeMap_isometry_diff (hyp : Hypothesis (G := G)) [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (hSsupp : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction ↥hyp.base.T ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    {a b c d : ClassFunction ↥hyp.base.T ℂ}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    ClassFunction.inner (tSideDadeMap hyp hG (a - b)) (tSideDadeMap hyp hG (c - d))
      = ClassFunction.inner (a - b) (c - d) := by
  haveI := hyp.base.finiteG
  -- Both differences live in the supported subspace `CF(T, A₁(T))`; unfold `τ_T` and apply the
  -- Dade supported-span inner-preservation lemma (the same brick `S14.Sset_tau_isometry_diff` uses).
  have hS : ∀ s ∈ ({a - b, c - d} : Set (ClassFunction ↥hyp.base.T ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hSsupp a ha b hb
    · exact hSsupp c hc d hd
  simp only [tSideDadeMap]
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    (tSideDadeSupport_nonempty hG hyp).some.dade (tSideDadeSupport_nonempty hG hyp).some.hconj
    hS (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

/-- **The T-side Dade support `A₁(T) = T_σ^#` is exactly `(T')^# = QV^#`** (issue 9072, step 3
support identity).  For type-III `T`, the Peterfalvi "main subgroup" `T_s = T'` (`mainSubgroup .III =
derivedInG`), and the support bridge `A1_eq_sigmaSharp` (Peterfalvi (8.10) + `mainSubgroup_eq_Msigma`,
here `T' = M_σ(T)` for the type-`P₁` regime that type-III inhabits) gives
`sigmaSharp T = A₁(T) = (T_s)^# = (T')^#`.  Concretely `sigmaSharp T = (derivedInG T : Set G) \ {1}`.

This is the linchpin making the (14.9) coherence support facts derivable *without* any cross-lane
type-`P` char structure: the induced members `Ind_{QV}^T θ` vanish off the normal `QV = T' =
derivedInG T`, so their differences are automatically supported in `sigmaSharp T = (T')^#` — matching
the Dade domain of `tSideDadeMap`.  (Coq `FTcore_eq_der1`: for `FTtype T > 2`, `T_s = T^{(1)}`; the
member differences `nu_0 − zeta ∈ 'CF(T, QV^#) = 'CF(T, 'A1(T))`, PFsection14.v:785--790.) -/
theorem T_typeIII_sigmaSharp_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T = (derivedInG hyp.base.T : Set G) \ {1} := by
  haveI := hyp.base.finiteG
  -- `A1 T .III = sigmaSharp T` (support bridge), and `A1 T .III = sharpSubgroup (derivedInG T)`
  -- since `mainSubgroup .III = derivedInG`.
  have hA1 : OddOrder.GroupTheory.A1 hyp.base.T OddOrder.GroupTheory.PeterfalviType.III
      = OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T :=
    OddOrder.BG.Ch4.S16.A1_eq_sigmaSharp hG hyp.base.T_maximal hIII
  rw [← hA1]
  rfl

open scoped Classical in
/-- **Peterfalvi (14.9): assembling the T-side `S07.Hypothesis` (`hyp07`)** (issue 9072, steps 2--4)
— the coherence-carrier constructor feeding `T_typeIII_calT1_coherent`.

Given the `calT1` family `𝒯 =` non-principal conjugate-closed `Irr(QV/Q)`-inflated sources (matching
`T_typeIII_calT1_card`/`calT1_image_induce_card_eq`), with:
* `hinertia : I_T(θ) = QV` for each `θ ∈ 𝒯` (⟹ `Ind_{QV}^T θ` irreducible), the same inertia fact
  feeding the count;
* `hne : θ ≠ 1` for each `θ ∈ 𝒯` (non-principal sources);
* `hconj𝒯 : θ ∈ 𝒯 ⟹ ⟨θ̄, θ.isIrreducible.conj⟩ ∈ 𝒯` (`𝒯` conjugate-closed, since `Irr` is);

this constructs the T-side `S07.Hypothesis calT1_set (supportInSubgroup (sigmaSharp T) T)` via the
in-repo assembler `S07.irrSubcoherent`, threading:
* `τ = tSideDadeMap hyp hG` (the genuine §10 Dade integral character map);
* the family predicates `S03.ClosedUnderConjugate`/`HasNoRealCharacters`/`PairwiseOrthogonal`, all
  derived from the induced-irreducible structure alone (Frobenius-analogous to the type-I
  `S14.Sset_*` witnesses): closure via `induce_conj`, no-real via `not_isReal_of_ne_trivial_of_odd_card'`
  (odd `|T|`, `Ind θ ≠ 1`), orthogonality via `irreducibleCharacter_inner_eq_ite`;
* the per-member `CharacterDifferenceImage` via `S07.dadeCharacterDifferenceImageOfDiff` (fed the
  conjugate-difference support `(χ̄ − χ).support ⊆ supportInSubgroup (sigmaSharp T) T`, from the
  member vanishing off `QV = T'` and `sigmaSharp T = (T')^#` = `T_typeIII_sigmaSharp_eq`);
* the isometry `tSideDadeMap_isometry_diff` (fed the family-supportedness `hSsupp`).

Everything here is **ungated**: it needs only the intrinsic type-III support identity
`T_typeIII_sigmaSharp_eq` and the induced-character bricks, no S-side βₛ / (13.12) input.  Its output
is exactly the `hyp07` argument that `T_typeIII_calT1_coherent` consumes to produce coherence. -/
noncomputable def T_typeIII_hyp07 [Finite G] (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hinertia : ∀ θ ∈ 𝒯,
      IrreducibleCharacter.inertia (G := ↥hyp.base.T)
          (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T)
    (hne : ∀ θ ∈ 𝒯, θ ≠ trivialIrreducibleCharacter _)
    (hlinear : ∀ θ ∈ 𝒯, (θ.toClassFunction :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1)
    (hconj𝒯 : ∀ θ ∈ 𝒯,
      (⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
        θ.isIrreducible.conj⟩ :
        IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) ∈ 𝒯)
    (calT1_set : Set (ClassFunction ↥hyp.base.T ℂ))
    (hcalT1 : calT1_set = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.base.T) (G := G) calT1_set
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) := by
  classical
  haveI := hyp.base.finiteG
  -- `T` has odd order (subgroup of the odd `G`).
  have hodd : Odd (Nat.card ↥hyp.base.T) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.base.T)
  -- `K = QV.subgroupOf T` is normal in `T` (`QV = T' = derivedInG T ⊴ T`).
  haveI hKnormal : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal :=
    T_derivedSubgroupOf_normal hyp
  -- The support identity `sigmaSharp T = (derivedInG T)^#`.
  have hAK : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T = (derivedInG hyp.base.T : Set G) \ {1} :=
    T_typeIII_sigmaSharp_eq hG hyp hIII
  -- Membership form: `x ∈ A ↔ x ∈ K ∧ x ≠ 1`.
  have hmemA : ∀ x : ↥hyp.base.T,
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ↔
        (x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T ∧ x ≠ 1) := fun x =>
    OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
      (derivedInG hyp.base.T) hAK x
  -- Each member of `calT1_set` is `Ind_K θ` for a non-principal `θ ∈ 𝒯`.
  have hmem_form : ∀ a ∈ calT1_set, ∃ θ ∈ 𝒯,
      a = ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction := by
    intro a ha
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at ha
    obtain ⟨θ, hθ, rfl⟩ := ha
    exact ⟨θ, hθ, rfl⟩
  -- `Ind_K θ ≠ 1` (else `⟨Ind θ, 1⟩ = 1 ≠ 0 = ⟨Ind θ, 1⟩`), for non-principal `θ`.
  have hInd_ne_triv : ∀ θ (hθ : θ ∈ 𝒯),
      (⟨ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction,
        isIrreducibleCharacter_induce_of_inertia_eq
          (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)⟩ :
        IrreducibleCharacter ↥hyp.base.T) ≠ trivialIrreducibleCharacter _ := by
    intro θ hθ hcontra
    -- `Res_K 1 = 1`, so `⟨Ind_K θ, 1⟩ = ⟨θ, Res 1⟩ = ⟨θ, 1⟩ = 0` (`θ ≠ 1`), contradicting `= 1`.
    have hrestrict : ClassFunction.restrict ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          (trivialIrreducibleCharacter ↥hyp.base.T : ClassFunction ↥hyp.base.T ℂ)
        = (trivialIrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) :
            ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ) := by
      ext x
      simp [ClassFunction.restrict_apply, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        trivialClassFunction_apply]
    have hzero : ClassFunction.inner
        (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          (θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ))
        (trivialIrreducibleCharacter ↥hyp.base.T : ClassFunction ↥hyp.base.T ℂ) = 0 := by
      rw [ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
        irreducibleCharacter_inner_eq_ite, if_neg (hne θ hθ)]
    have hcf : ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          (θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ)
        = (trivialIrreducibleCharacter ↥hyp.base.T : ClassFunction ↥hyp.base.T ℂ) :=
      congrArg (fun c : IrreducibleCharacter ↥hyp.base.T => (c : ClassFunction ↥hyp.base.T ℂ))
        hcontra
    rw [hcf, irreducibleCharacter_inner_eq_ite, if_pos rfl] at hzero
    exact one_ne_zero hzero
  -- (a) `S03.HasNoRealCharacters calT1_set`: each member is a nontrivial irreducible of the odd `T`.
  have hreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters calT1_set := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    exact not_isReal_of_ne_trivial_of_odd_card' (G := ↥hyp.base.T) hodd
      (χ := ⟨ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction,
        isIrreducibleCharacter_induce_of_inertia_eq
          (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)⟩)
      (hInd_ne_triv θ hθ)
  -- (b) `S03.PairwiseOrthogonal calT1_set`: distinct irreducible members are orthogonal.
  have hortho : OddOrder.Peterfalvi.S03.PairwiseOrthogonal calT1_set := by
    intro χ ψ hχ hψ hne'
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    obtain ⟨θ', hθ', rfl⟩ := hmem_form ψ hψ
    have hχirr := isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
    have hψirr := isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ' (hinertia θ' hθ')
    rw [show ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction
          = ((⟨_, hχirr⟩ : IrreducibleCharacter ↥hyp.base.T) : ClassFunction ↥hyp.base.T ℂ) from rfl,
      show ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ'.toClassFunction
          = ((⟨_, hψirr⟩ : IrreducibleCharacter ↥hyp.base.T) : ClassFunction ↥hyp.base.T ℂ) from rfl,
      irreducibleCharacter_inner_eq_ite, if_neg]
    intro h
    exact hne' (congrArg
      (fun c : IrreducibleCharacter ↥hyp.base.T => (c : ClassFunction ↥hyp.base.T ℂ)) h)
  -- (c) `S03.ClosedUnderConjugate calT1_set`: `(Ind_K θ)^ = Ind_K θ̄` and `θ̄ ∈ 𝒯`.
  have hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate calT1_set := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    rw [hcalT1, Finset.mem_coe, Finset.mem_image]
    refine ⟨⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
      θ.isIrreducible.conj⟩, hconj𝒯 θ hθ, ?_⟩
    -- `Ind_K (θ̄) = (Ind_K θ)^`.
    exact (ClassFunction.induce_conj ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
      (θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ)).symm
  -- Support of the conjugate difference `χ̄ − χ` for a member `χ = Ind_K θ`: `⊆ A = (T')^#`.
  have hconjDiff_supp : ∀ χ ∈ calT1_set,
      ((χ : ClassFunction ↥hyp.base.T ℂ).conj - χ).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    intro x hx
    have hx0 : ((ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          θ.toClassFunction).conj
        - ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) x
        ≠ 0 := ClassFunction.mem_support.mp hx
    rw [ClassFunction.sub_apply, ClassFunction.conj_apply] at hx0
    -- Off `K`, `Ind θ` vanishes (normal `K`), so the difference vanishes.
    have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      by_contra h
      apply hx0
      rw [ClassFunction.induce_eq_zero_of_not_mem_normal θ.toClassFunction h]
      simp
    -- At `1`, `Ind θ (1)` is a real (natural) degree, so the conjugate difference vanishes.
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hx0
      obtain ⟨n, -, hn1, -⟩ :=
        (isIrreducibleCharacter_induce_of_inertia_eq
          (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
          (hinertia θ hθ)).exists_natDegree_charValue_one_dvd_card
      rw [hn1, star_natCast, sub_self]
    rw [hmemA x]; exact ⟨hxK, hx1⟩
  -- Support of a member *difference* `a − b`: `⊆ A` (both vanish off `K`, and `a(1) = b(1) = p`).
  have hdiff_supp : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set,
      ((a - b : ClassFunction ↥hyp.base.T ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro a ha b hb
    obtain ⟨θa, hθa, rfl⟩ := hmem_form a ha
    obtain ⟨θb, hθb, rfl⟩ := hmem_form b hb
    intro x hx
    have hx0 : (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          θa.toClassFunction
        - ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θb.toClassFunction) x
        ≠ 0 := ClassFunction.mem_support.mp hx
    rw [ClassFunction.sub_apply] at hx0
    have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      by_contra h
      apply hx0
      rw [ClassFunction.induce_eq_zero_of_not_mem_normal θa.toClassFunction h,
        ClassFunction.induce_eq_zero_of_not_mem_normal θb.toClassFunction h, sub_zero]
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hx0
      -- Both degrees are `[T:K]·θ(1) = [T:K]·1` (linear sources), so the difference vanishes at 1.
      rw [ClassFunction.induce_apply_one, ClassFunction.induce_apply_one,
        hlinear θa hθa, hlinear θb hθb, sub_self]
    rw [hmemA x]; exact ⟨hxK, hx1⟩
  -- Each member is irreducible (packaged from its `Ind_K θ` form).
  have hirr : ∀ χ ∈ calT1_set, IsIrreducibleCharacter χ := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  -- Per-member `CharacterDifferenceImage` from the Dade map (difference-support form).
  have Rdatum : ∀ χ ∈ calT1_set, OddOrder.Peterfalvi.S07.CharacterDifferenceImage
      (L := ↥hyp.base.T) (G := G) (tSideDadeMap hyp hG) χ := fun χ hχ =>
    -- Package `χ` (an irreducible member) as an `IrreducibleCharacter ↥T`; `(ζ : CF) = χ` by `rfl`.
    OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff
      (tSideDadeSupport_nonempty hG hyp).some.dade (tSideDadeSupport_nonempty hG hyp).some.hconj
      ⟨χ, hirr χ hχ⟩ (hreal hχ) (hconjDiff_supp _ hχ)
  -- Assemble via the (5.3)(a) `irrSubcoherent` (0099 form: `hconjsupp` + `zSupportedSpan` isometry,
  -- the latter unconditional from the Dade pair brick).
  exact OddOrder.Peterfalvi.S07.irrSubcoherent (S := calT1_set) (tSideDadeMap hyp hG) _ Rdatum
    hconj hreal hortho
    (fun χ hχ => hdiff_supp χ hχ χ.conj (hconj hχ))
    (fun φ ψ hφ hψ => by
      simp only [tSideDadeMap]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (tSideDadeSupport_nonempty hG hyp).some.dade (tSideDadeSupport_nonempty hG hyp).some.hconj
        hφ.2 hψ.2)

open scoped Classical in
/-- **Peterfalvi (14.9): `calT1` is coherent** (Coq `PFsection14.v:750--751`
`have [tau1T cohT1]: coherent calT1 T^# tauT`, via
`apply/(uniform_degree_coherence scohT1)/(@all_pred1_constant _ p%:R)`) — the **coherence skeleton**
isolating the T-side type-`P` Dade setup as the single deep residual.

`calT1 = {Ind_{QV}^T θ | θ ∈ 𝒯}` (`QV = T' = derivedInG T`, `Q = M_F`, `𝒯 =` non-principal inflated
`Irr(QV/Q)`), realized here as the `Set`-coercion of the `Finset` image (matching
`T_typeIII_calT1_card`/`calT1_image_induce_card_eq`).  Given the **Dade setup** as the input
`hyp07 : S07.Hypothesis calT1_set A` (the Coq `subcoherent calT1 tauT rmR_T` = `FTtypeP_coh_base`,
carrying `tauT` and the seven §5.2 fields), this produces coherence via the proven engine
`S07.coherent_of_constant_degree` (Coq `uniform_degree_coherence`), **proving everything else** from
`calT1`'s structure + the proven count:

* `hirr` — each `ζ = Ind_{QV}^T θ (θ ∈ 𝒯)` is irreducible (`isIrreducibleCharacter_induce_of_inertia_eq`
  fed the inertia fact `hinertia : I_T(θ) = QV`, the same input feeding the count), so `⟨ζ,ζ⟩ = 1`
  (`IsIrreducibleCharacter.inner_self_eq_one`);
* `hconst`/`hdeg0` — each `ζ` has degree `ζ(1) = [T:QV]·θ(1) = p·1 = p ≠ 0`
  (`ClassFunction.induce_apply_one` + `T_derived_index_eq_p` `[T:QV] = p` + linearity
  `hlinear : θ(1) = 1`, since `θ` inflates from the abelian `QV/Q ≅ V`), i.e. Coq's `all_pred1_constant p`;
* `hSfin` — `calT1_set` is the image of a `Finset`, hence finite.

The residual — **the T-side type-`P` Dade isometry construction** (Coq `FTtypeP_coh_base`, a from-scratch
§4/§5 build with **no** existing type-`P` Dade base in the repo) — is precisely the input `hyp07`
together with the three genuinely Dade/support-dependent facts, kept as explicit hypotheses (each
cited from `hyp07`'s concrete Dade map at the call site, exactly as the §14 type-I assembly discharges
them via `dadeIntegralCharacterMap_mem_ZIrr_of_supported` etc.):

* `hZIrr : ∀ a b ∈ calT1_set, hyp07.tau (a − b) ∈ ZIrr G` — the Dade-map integrality on member
  differences (Coq `Ztau1T` from the `subcoherent` datum);
* `h1A : (1 : ↥T) ∉ A` and `hsuppdiff : ∀ a b ∈ calT1_set, (a − b).support ⊆ A` — the support/`A`-facts
  (Coq `A = T^#`, so `1 ∉ A` and every member difference vanishes off `T^#`);
* `hcard2 : 2 ≤ calT1_set.ncard` — the size bound `2 ≤ (|V|−1)/p` (arithmetic on `|V|`, from the proven
  count `T_typeIII_calT1_card`; kept explicit since it needs a `|V|`-lower bound not carried by the
  intrinsic datum here).

This is the honest §16 coherence assembly point for (14.9): it consumes only the verified bricks
(`isIrreducibleCharacter_induce_of_inertia_eq`, `induce_apply_one`, `T_derived_index_eq_p`,
`coherent_of_constant_degree`) and the parameterized Dade setup, leaving the type-`P` Dade base as the
single precisely-scoped deep obligation.  Its output feeds the (14.9) Γ-Bessel bound
`T_typeIII_ratio_le` (Coq `cohT1` consumed at PFsection14.v:769 `have [[Itau1T Ztau1T] Dtau1T] := cohT1`). -/
theorem T_typeIII_calT1_coherent [Finite G] (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hinertia : ∀ θ ∈ 𝒯,
      IrreducibleCharacter.inertia (G := ↥hyp.base.T)
          (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T)
    (hlinear : ∀ θ ∈ 𝒯, (θ.toClassFunction : ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1)
    (A : Set ↥hyp.base.T)
    (calT1_set : Set (ClassFunction ↥hyp.base.T ℂ))
    (hcalT1 : calT1_set = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)))
    (hyp07 : OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.base.T) (G := G) calT1_set A)
    (hZIrr : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set, hyp07.tau (a - b) ∈ ZIrr G)
    (h1A : (1 : ↥hyp.base.T) ∉ A)
    (hsuppdiff : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set, ((a - b : ClassFunction ↥hyp.base.T ℂ)).support ⊆ A)
    (hcard2 : 2 ≤ calT1_set.ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp07.tau calT1_set A) := by
  haveI := hyp.base.finiteG
  -- `calT1_set` is finite (image of a `Finset`).
  have hSfin : calT1_set.Finite := by rw [hcalT1]; exact (Finset.finite_toSet _)
  -- The `[T:QV] = p` index (degree factor) and its positivity.
  have hindex : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).index = hyp.base.p :=
    T_derived_index_eq_p hyp
  have hp_ne : (hyp.base.p : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hyp.base.p_prime.pos.ne'
  -- Each member `ζ = Ind_{QV}^T θ` is irreducible; extract its source `θ ∈ 𝒯` and its degree `= p`.
  have hmem_form : ∀ a ∈ calT1_set, ∃ θ ∈ 𝒯,
      a = ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction := by
    intro a ha
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at ha
    obtain ⟨θ, hθ, rfl⟩ := ha
    exact ⟨θ, hθ, rfl⟩
  have hirr : ∀ ζ ∈ calT1_set, IsIrreducibleCharacter ζ := by
    intro ζ hζ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form ζ hζ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  have hdeg : ∀ ζ ∈ calT1_set, (ζ : ↥hyp.base.T → ℂ) 1 = (hyp.base.p : ℂ) := by
    intro ζ hζ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form ζ hζ
    rw [ClassFunction.induce_apply_one, hindex, hlinear θ hθ, mul_one]
  -- assemble and invoke the equal-degree coherence producer.
  refine OddOrder.Peterfalvi.S07.coherent_of_constant_degree hyp07 hSfin hcard2 ?_ hZIrr ?_ ?_ h1A hsuppdiff
  · exact fun ζ hζ => (hirr ζ hζ).inner_self_eq_one
  · exact fun a ha b hb => by rw [hdeg a ha, hdeg b hb]
  · exact fun a ha => by rw [hdeg a ha]; exact hp_ne

open scoped Classical in
/-- **Peterfalvi (14.9): `calT1` is coherent, end-to-end** (issue 9072, Stage-1 completion) — the
composition `T_typeIII_hyp07` ∘ `T_typeIII_calT1_coherent` that produces the coherent map `τ₁` from
the *intrinsic* family data alone (plus the gated size bound `hcard2`).  The T-side `S07.Hypothesis`
Dade package `hyp07` is now **constructed** (not posited) by `T_typeIII_hyp07`, and its three
support/integrality carriers are discharged here from the induced-character support facts:

* `hZIrr` — `τ_T(a − b) ∈ ZIrr G` via `S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported` (the
  member difference is `A₁(T)`-supported (`hdiff_supp`) and lies in `ℤ[Irr T]`);
* `h1A` — `1 ∉ A₁(T) = supportInSubgroup (sigmaSharp T) T` (`one_not_mem_supportInSubgroup_sharp`);
* `hsuppdiff` — member differences vanish off `A₁(T)` (the same `hdiff_supp`, from the members
  vanishing off `QV = T'` and `sigmaSharp T = (T')^#`).

The only *external* input is `hcard2 : 2 ≤ calT1_set.ncard` (`= (|V|−1)/p ≥ 2`, the size bound needing
a `|V|`-lower bound — kept explicit, as in `T_typeIII_calT1_coherent`).  Output: the coherent
`τ₁ = hyp07.tau = tSideDadeMap hyp hG`-extension whose orthonormal image family feeds the (14.9)
Γ-Bessel bound. -/
theorem T_typeIII_calT1_isCoherent [Finite G] (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hinertia : ∀ θ ∈ 𝒯,
      IrreducibleCharacter.inertia (G := ↥hyp.base.T)
          (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T)
    (hlinear : ∀ θ ∈ 𝒯, (θ.toClassFunction :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1)
    (hne : ∀ θ ∈ 𝒯, θ ≠ trivialIrreducibleCharacter _)
    (hconj𝒯 : ∀ θ ∈ 𝒯,
      (⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
        θ.isIrreducible.conj⟩ :
        IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) ∈ 𝒯)
    (calT1_set : Set (ClassFunction ↥hyp.base.T ℂ))
    (hcalT1 : calT1_set = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)))
    (hcard2 : 2 ≤ calT1_set.ncard) :
    ∃ hyp07 : OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.base.T) (G := G) calT1_set
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T),
      hyp07.tau = tSideDadeMap hyp hG ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp07.tau calT1_set
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)) := by
  classical
  haveI := hyp.base.finiteG
  -- Support identity `sigmaSharp T = (derivedInG T)^#` and the sharp-membership form.
  have hAK : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T = (derivedInG hyp.base.T : Set G) \ {1} :=
    T_typeIII_sigmaSharp_eq hG hyp hIII
  have hmemA : ∀ x : ↥hyp.base.T,
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ↔
        (x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T ∧ x ≠ 1) := fun x =>
    OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
      (derivedInG hyp.base.T) hAK x
  haveI hKnormal : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal :=
    T_derivedSubgroupOf_normal hyp
  have hmem_form : ∀ a ∈ calT1_set, ∃ θ ∈ 𝒯,
      a = ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction := by
    intro a ha
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at ha
    obtain ⟨θ, hθ, rfl⟩ := ha
    exact ⟨θ, hθ, rfl⟩
  have hirr : ∀ χ ∈ calT1_set, IsIrreducibleCharacter χ := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  -- Member-difference support `⊆ A₁(T)` (`= hsuppdiff`).
  have hdiff_supp : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set,
      ((a - b : ClassFunction ↥hyp.base.T ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro a ha b hb
    obtain ⟨θa, hθa, rfl⟩ := hmem_form a ha
    obtain ⟨θb, hθb, rfl⟩ := hmem_form b hb
    intro x hx
    have hx0 : (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          θa.toClassFunction
        - ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θb.toClassFunction) x
        ≠ 0 := ClassFunction.mem_support.mp hx
    rw [ClassFunction.sub_apply] at hx0
    have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      by_contra h
      apply hx0
      rw [ClassFunction.induce_eq_zero_of_not_mem_normal θa.toClassFunction h,
        ClassFunction.induce_eq_zero_of_not_mem_normal θb.toClassFunction h, sub_zero]
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hx0
      rw [ClassFunction.induce_apply_one, ClassFunction.induce_apply_one,
        hlinear θa hθa, hlinear θb hθb, sub_self]
    rw [hmemA x]; exact ⟨hxK, hx1⟩
  -- Build `hyp07` via `T_typeIII_hyp07`; its `.tau = tSideDadeMap hyp hG` (by `rfl`).
  set hyp07 := T_typeIII_hyp07 hyp hG hIII 𝒯 hinertia hne hlinear hconj𝒯 calT1_set hcalT1
    with hhyp07
  have htau : hyp07.tau = tSideDadeMap hyp hG := rfl
  refine ⟨hyp07, htau, ?_⟩
  -- `h1A`: `1 ∉ A₁(T)`.
  have h1A : (1 : ↥hyp.base.T) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    rw [hmemA 1]; rintro ⟨-, h⟩; exact h rfl
  -- `hZIrr`: `τ_T(a − b) ∈ ZIrr G` (member difference `A₁(T)`-supported + in `ℤ[Irr T]`).
  have hZIrr : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set, hyp07.tau (a - b) ∈ ZIrr G := by
    intro a ha b hb
    rw [htau]
    simp only [tSideDadeMap]
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (tSideDadeSupport_nonempty hG hyp).some.dade (tSideDadeSupport_nonempty hG hyp).some.hconj
      (hdiff_supp a ha b hb) ?_
    exact Submodule.sub_mem _ (hirr a ha).mem_ZIrr (hirr b hb).mem_ZIrr
  -- Feed the coherence engine `T_typeIII_calT1_coherent`.
  exact T_typeIII_calT1_coherent hyp 𝒯 hinertia hlinear _ calT1_set hcalT1 hyp07 hZIrr h1A
    hdiff_supp hcard2

open scoped Classical in
/-- **Peterfalvi (14.9), the Γ-Bessel assembly skeleton** — the *proven* structural core of the
character body, isolating the char-cascade carriers as precisely-named hypotheses.  Coq
`FTtypeP_min_typeII` (PFsection14.v:764--853): given the coherent `τ₁`-image family `calT1`
(orthonormal degree-`p` induced characters, whose `|calT1| = (v−1)/p` count is the proven
`T_typeIII_calT1_card` after the (13.12) `d = 1` substitution `v = |V|`) and the `S`-side `βₛ`
bridge gap `Γ`, the parity fact `⟨Γ, τ₁ζ⟩ ≡ 1 (mod 2)` per `ζ` (`S09.cfdot_real_vchar_even`) makes
each integer pairing coefficient `x ζ = ⟨Γ, τ₁ζ⟩` **nonzero**; then the orthogonal-integer Bessel
bridge `S09.sum_rat_weights_le_of_orthogonal_integer_decomposition` (Coq's `orthogonal_split` +
Bessel over `‖Γ‖² ≤ (u−1)/q`) gives `∑_{ζ ∈ calT1} 1 ≤ ⟨Γ,Γ⟩ ≤ (u−1)/q`, i.e.
`|calT1| = (v−1)/p ≤ (u−1)/q`.

This is the **genuinely-available** arithmetic of (14.9): everything downstream of the carriers is
proven here (the orthonormal-family Bessel step with unit weights `m ζ = 1`, the `∑ 1 = |calT1|`
count-collapse, and the `⟨Γ,Γ⟩ ≤ (u−1)/q` chaining).  The four hypotheses package exactly the deep
carriers that the honest §16 build still owes, each cited from its own construction at the
`T_typeIII_ratio_le` call site:

* `hcount : (calT1.card : ℚ) = (v−1)/p` — the coherent count (proven `T_typeIII_calT1_card` in `|V|`
  form) **after** the (13.12) `d = 1` substitution `v = |V|` (`S15.V_inf_centralizer_Q_eq_bot`, lane-b);
* `horth` — orthonormality of the `τ₁`-images (the `calT1` **coherence** carrier, proven skeleton
  `T_typeIII_calT1_coherent` fed a T-side `S07.Hypothesis` Dade package);
* `hdecomp`/`hΓ₁`/`hx` — the `S`-side `βₛ` bridge gap `Γ = ∑ x_ζ·τ₁ζ + Γ₁` (`Γ₁ ⊥ τ₁ζ`), with the
  parity nonzeroness `x_ζ ≠ 0` (Coq `nzT1_Ga` via `cfdot_real_vchar_even`);
* `hnorm : ⟨Γ,Γ⟩.re ≤ (u−1)/q` — the `S`-side norm bound on the bridge gap.

Its output `(v−1)/p ≤ (u−1)/q` is exactly the (14.9) `≤` whose `>` counterpart (14.8)
`key_inequality` contradicts. -/
theorem T_typeIII_ratio_le_of_gamma_bridge [Finite G]
    [Fintype G] [Invertible (Nat.card G : ℂ)] (hyp : Hypothesis (G := G))
    (calT1 : Finset (ClassFunction G ℂ)) (Γ Γ₁ : ClassFunction G ℂ)
    (x : ClassFunction G ℂ → ℤ)
    (hcount : (calT1.card : ℚ) = ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (horth : ∀ a ∈ calT1, ∀ b ∈ calT1,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    (hdecomp : Γ = (∑ a ∈ calT1, (((x a : ℝ) : ℂ) • a)) + Γ₁)
    (hΓ₁ : ∀ a ∈ calT1, ClassFunction.inner Γ₁ a = 0)
    (hx : ∀ a ∈ calT1, x a ≠ 0)
    (hnorm : (ClassFunction.inner Γ Γ).re ≤
      ((((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) : ℚ) : ℝ)) :
    ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
  classical
  -- Bessel over the orthonormal `calT1` (unit weights `m a = 1`, integer coeffs `x a ≠ 0`),
  -- against the norm bound `⟨Γ,Γ⟩ ≤ (u−1)/q`: yields `∑_{a ∈ calT1} 1 ≤ (u−1)/q`.
  have hbessel := OddOrder.Peterfalvi.S09.sum_rat_weights_le_of_orthogonal_integer_decomposition
    (ι := ClassFunction G ℂ) calT1 (fun a => a) x (fun _ => (1 : ℚ)) Γ Γ₁
    (((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ))
    hdecomp
    (fun a ha b hb => by rw [horth a ha b hb]; split <;> simp)
    hΓ₁
    (fun _ _ => zero_le_one)
    hx
    hnorm
  -- `∑_{a ∈ calT1} 1 = |calT1|`, and `|calT1| = (v−1)/p` by the coherent count.
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcount] at hbessel
  exact hbessel

open scoped Classical in
/-- **(14.9) Γ-bridge extraction engine** (issue 0098 item 4, de-serialization skeleton).  Given the
`S`-side gap `Γ` whose inner products against the orthonormal coherent family `calT1` are the integer
coefficients `x_ζ = ⟨Γ, ζ⟩` (each `≠ 0` — the `nzT1_Ga` parity input), plus the norm bound
`⟨Γ,Γ⟩ ≤ (u−1)/q`, the orthogonal projection `Γ₁ := Γ − ∑_ζ x_ζ·ζ` is `calT1`-orthogonal
(`hΓ₁`, from orthonormality), so the proven Bessel skeleton `T_typeIII_ratio_le_of_gamma_bridge`
closes the ratio.

This isolates the **genuine assembly** — the orthogonal split (`hdecomp`/`hΓ₁`) — from the
lane-b-gated `S`-side `βₛ` content (the gap `Γ` with its parity `hx` and norm `hnorm`), which enters
as hypotheses.  `T_typeIII_ratio_le`'s residual then reduces to *just* the `βₛ`-gap existence, ready
to cite once the `S`-side `βₛ` bridge (item 3 / issue 9013) lands. -/
theorem T_typeIII_ratio_le_of_sSide_gap [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis (G := G)) (calT1 : Finset (ClassFunction G ℂ))
    (horth : ∀ a ∈ calT1, ∀ b ∈ calT1,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    (hcount : (calT1.card : ℚ) = ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (Γ : ClassFunction G ℂ) (x : ClassFunction G ℂ → ℤ)
    (hxcoe : ∀ a ∈ calT1, ClassFunction.inner Γ a = ((x a : ℝ) : ℂ))
    (hx : ∀ a ∈ calT1, x a ≠ 0)
    (hnorm : (ClassFunction.inner Γ Γ).re ≤
      ((((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) : ℚ) : ℝ)) :
    ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
  classical
  set Γ₁ : ClassFunction G ℂ := Γ - ∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a with hΓ₁def
  have hdecomp : Γ = (∑ a ∈ calT1, (((x a : ℝ) : ℂ) • a)) + Γ₁ := by rw [hΓ₁def]; abel
  -- `Γ₁` is orthogonal to every member: `⟨Γ₁, b⟩ = ⟨Γ, b⟩ − ∑_a x_a·⟨a,b⟩ = x_b − x_b = 0`
  -- (inner is linear in the first argument, `inner_smul_left : ⟨c•φ,ψ⟩ = c·⟨φ,ψ⟩`).
  have hΓ₁ : ∀ a ∈ calT1, ClassFunction.inner Γ₁ a = 0 := by
    intro b hb
    have hsum_left : ∀ (s : Finset (ClassFunction G ℂ)),
        ClassFunction.inner (∑ a ∈ s, ((x a : ℝ) : ℂ) • a) b
          = ∑ a ∈ s, ClassFunction.inner (((x a : ℝ) : ℂ) • a) b := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert c s hc ih =>
          rw [Finset.sum_insert hc, ClassFunction.inner_add_left, ih, Finset.sum_insert hc]
    rw [hΓ₁def, ClassFunction.inner_sub_left, hsum_left calT1, hxcoe b hb,
      Finset.sum_eq_single b
        (fun a ha hab => by
          rw [ClassFunction.inner_smul_left, horth a ha b hb, if_neg hab, mul_zero])
        (fun hbni => absurd hb hbni),
      ClassFunction.inner_smul_left, horth b hb b hb, if_pos rfl, mul_one, sub_self]
  exact T_typeIII_ratio_le_of_gamma_bridge hyp calT1 Γ Γ₁ x hcount horth hdecomp hΓ₁ hx hnorm

/-- **Peterfalvi (14.9), the character body** — the structural `≤` half of the ratio comparison, the
sole deep obligation of (14.9).  Coq `PFsection14` `FTtypeP_min_typeII`, lines 737--853: assuming `T`
is type III, build `calT1 = seqIndD QV T QV Q` (the degree-`p` induced characters of `T`, from
`T' = Q ⊔ V` via `T_deriv_eq_QV`), coherent by uniform-degree coherence
(`S07.coherent_of_constant_degree` / Coq `uniform_degree_coherence`).  Now **reduced to the proven
Γ-Bessel skeleton** `T_typeIII_ratio_le_of_gamma_bridge` (above), which discharges all the
orthonormal-family Bessel arithmetic; this theorem supplies the skeleton's four precisely-named
char-cascade carriers (`hcount`/`horth`/`hdecomp`+`hΓ₁`+`hx`/`hnorm`), kept jointly as its single
documented residual `sorry`.  Via the `S`-side `βₛ` bridge
gap `Γ`, `⟨Γ, τ₁ ζ⟩ ≡ 1 (mod 2)` for each `ζ ∈ calT1` (Coq `nzT1_Ga`, using
`cfdot_real_vchar_even`), so `|⟨Γ, τ₁ ζ⟩|² ≥ 1`; then `orthogonal_split` + Bessel give
`(v − 1)/p = p · |calT1| ≤ ⟨Γ, Γ⟩ ≤ (u − 1)/q`.

The `|calT1| = (v − 1)/p` step is *structural* (Coq line 836--845: `size calT1 = (v.-1) %/ p` from
`v = |V/Q|` and the degree-`p` induction), so this bound does **not** re-derive the exact `v`-value;
it is exactly the type-III Γ-bridge estimate whose `>` counterpart (14.8) `key_inequality` then
contradicts.  Kept as the single precisely-named character residual of (14.9).

**Blocker map (why this stays sorried; lane-c 2026-07-06).**  The Coq spine needs four missing
pieces, none supplied by the `S16_PairingBessel` M-side template (which inducts from the *full*
`Irr(M')` via a Frobenius `(T, M', C)` and counts fibers with `card_index_mul_sum_induced_family_
degree_sq` — *not* the quotient-restricted `Irr(QV/Q)` family with a `W₁`-orbit count):

1. **`v = |V|`** (Peterfalvi (13.12), `d = 1`, i.e. `D = V ⊓ C_G(Q) = ⊥`).  Coq's `v := |V|` is
   *definitional* (PFsection14.v:66/422) so its `(v−1)/p` bound is literally `(|V|−1)/p`; the Lean
   `Hypothesis.v` is a **free** ℕ with only `card_V_eq_vd : |V| = v·d`, so `v = |V|` iff `d = 1`.
   That is `S15.V_inf_centralizer_Q_eq_bot` — currently **sorried and gated on `IsTypeII T`**, hence
   unavailable in this type-III branch.  Without it, the honest `|calT1| = (|V|−1)/p` cannot be
   identified with the goal's `(v−1)/p`.  (`T_card_quot_Q_derived_eq_card_V` above supplies the
   `|QV/Q| = |V|` half; the `|V| = v` half is the missing (13.12).)
2. **The `calT1` family + its `|calT1| = (v−1)/p` count.**  Needs (a) inflation `Irr(QV/Q) ↪
   {χ ∈ Irr QV | Q ⊆ ker}` (available: `RepresentationTheory.InflationCharacter`), (b)
   `Ind_{QV}^T`-irreducibility for nonprincipal inflated sources via `I_T(θ) = QV` — reduced below to
   two general rep-theory bricks, **both now available as shared infra**, so no longer missing — and
   (c) the `/p` **orbit count**, landed as reusable shared infra
   `RepresentationTheory.card_image_induce_eq_div` (`OrbitOnIrr.lean`):
   `|T.image (Ind_H^G)| = |T| / [G:H]` for a conjugation-invariant `T ⊆ Irr H` with `I_G(θ) = H`
   throughout — the cardinality analogue of the M-side degree-square `sum_div_normSq_induce_image_eq`,
   built from `card_filter_induce_eq_index_inertia`.  With (a)+(c) in hand the count reduces to (b).

   The residual (b) — `I_T(inflate θ) = QV` for nonprincipal `θ ∈ Irr(QV/Q)` (Coq
   `irr_induced_Frobenius_ker` + `injm_Frobenius_ker` through the quotient, PFsection14.v:757--762) —
   is packaged as the reusable brick `inertia_inflate_eq_of_frobeniusQuotient` (this file):
   `I_G(inflate θ̄) = H` from a Frobenius quotient `G/N` with kernel `H/N`, via
   `inertia_eq_of_frobeniusGroup` (⟹ `I_{G/N}(θ̄) = H/N`) + the inertia/inflation bridge
   `mem_inertia_compHom_iff` (`ConjugationBrauer.lean`) + `comap_map_eq_self` (`N ≤ H`).  Its input,
   the quotient Frobenius `T/Q = (QV/Q) ⋊ (W₂Q/Q)`, is transported (`isFrobeniusGroup_map_equiv`)
   from the **intrinsic** `U ⋊ W₁` Frobenius `T_typeIII_UW1_frobenius` through `mk' Q` (injective on
   `U ⊔ W₁` since `Q ⊓ (U ⊔ W₁) = ⊥`) — **ungated**, replacing the earlier abstract-`V ⋊ W₂`
   (`S15.isMulCommutative_V`) route that was gated through the sorried `reconciled_typePData_T`.
   Likewise `U` abelian is the intrinsic `td.U_commutative` (ungated), not the gated abstract-`V`
   abelianness.  See the (now-`UNGATED`) escape-hatch conclusion below.
3. **A full `S07.Hypothesis` (5.2) instance for `calT1`** (the (12.1) T-side Dade `tauT` +
   `difference_image`/`no_real`/`pairwise_orthogonal`/`tau_isometry_diff`), to feed
   `coherent_of_constant_degree`.  This is the T-side coherence package, itself separately gated.
4. **The `S`-side βₛ bridge gap `Γ`** and `⟨Γ, τ₁ζ⟩ ≡ 1 (mod 2)` (Coq `nzT1_Ga`, via
   `S09.cfdot_real_vchar_even`), then `orthogonal_split` + Bessel.  `Γ` needs the full S-side
   (13.x)/(14.x) βₛ construction (cf. the `S16_NonExistenceG` βₛ-grid sorry at ~line 6377).

Escape-hatch conclusion (**revised 2026-07-06, lane-c** — the count is now known **UNGATED**; this
corrects an earlier lane-c note that wrongly called items 2/b "gated behind `IsTypeP2 T`").  The
`IsTypeP2` gate is **bypassed by working with the *intrinsic* type-III datum** `td = hIII.some :
TypeIIIData T` (NOT the abstract Hypothesis `V`/`W₂`, whose reconciliation to `td` is the sorried
`S15.reconciled_typePData_T`).  Its factors `td.typeP.U`/`td.typeP.W₁` supply, **all ungated**:

* `td.U_commutative : IsMulCommutative ↥td.typeP.U` (⟹ `QV/Q ≅ U` abelian ⟹ `|Irr(QV/Q)| = |V|`);
* `T_typeIII_UW1_frobenius` — the `U ⋊ W₁` Frobenius (`S11.typeP_uW1_frobenius td.typeP td.common.1`,
  Coq `frobVW2`), the ungated source of the quotient Frobenius `T/Q` for the inertia fact;
* `T_typeIII_card_W1 : |td.typeP.W₁| = p` and `T_typeIII_card_U : |td.typeP.U| = |V|` — canonical
  (both sides are intrinsic indices `[T:T']`, `[T':M_F]`), so **no** abstract-`V`/`W₂`
  reconciliation.

Landed ungated + green: the group-theoretic foundation (`T_derived_index_eq_p`,
`T_Q_isComplement_V_derived`, `T_card_quot_Q_derived_eq_card_V`, `T_derivedSubgroupOf_normal`), the
orbit-count engine `calT1_image_induce_card_eq` (`|{Ind_{QV}^T θ}| = |𝒯|/p` for conj-invariant
inertia-`QV` `𝒯`), the reusable inflation-quotient inertia brick
`inertia_inflate_eq_of_frobeniusQuotient` (`I_G(inflate θ̄) = H` from a Frobenius quotient `G/N`,
kernel `H/N`), the four intrinsic facts above, and the **no-`sorry` assembly skeleton**
`T_typeIII_calT1_card_eq` producing `|calT1| = (|V|−1)/p` from the count engine + `|𝒯| = |V|−1`.

The remaining `|calT1| = (|V|−1)/p` work is **pure transcription, ungated** (not a gate): discharging
the skeleton's `hcard`/`hconj`/`hinertia` by (i) building `𝒯` = non-principal inflated `Irr(QV/Q)`,
(ii) the `Q`-complement `IsComplement' (Q.subgroupOf T) ((U ⊔ W₁).subgroupOf T)` → iso
`↥T/Q ≅ U ⊔ W₁` → quotient Frobenius `T/Q` via `isFrobeniusGroup_map_equiv` (feeding
`inertia_inflate_eq_of_frobeniusQuotient`), (iii) `|𝒯| = |V|−1` via `inflate_injective` +
`T_typeIII_card_U` + `card_irreducibleCharacter_eq_card_of_commGroup`, (iv) conj-invariance via
`conjBy_compHom_eq_compHom_conjBy`.  All bricks for (i)-(iv) are landed/verified.

Then the *full* (14.9) `T_typeIII_ratio_le` bound still needs, beyond `|calT1| = (|V|−1)/p`:
item 1 (`v = |V|`, i.e. (13.12) `d = 1`, separately lane-b-gated — the `(|V|−1)/p → (v−1)/p`
substitution), item 3 (the T-side coherence package `S07.Hypothesis` feeding
`coherent_of_constant_degree`), and item 4 (the S-side `Γ` bridge + `nzT1_Ga` + `orthogonal_split`
Bessel).  Those remain the documented residual of the character body. -/
theorem T_typeIII_ratio_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
  -- Coq `FTtypeP_min_typeII` body (PFsection14.v:737--853): `calT1`/coherence + Γ-Bessel.
  -- Reduced to the proven Γ-Bessel skeleton `T_typeIII_ratio_le_of_gamma_bridge`; its inputs are
  -- the precisely-named char-cascade carriers, each a genuinely-missing construction kept as a
  -- documented residual `sorry` here (NOT a gate on `T_typeIII_ratio_le`'s honest structure — the
  -- Bessel/orthonormality/count arithmetic is fully proven in the skeleton).
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI := hyp.base.finiteG
  haveI : Fintype ↥hyp.base.T := Fintype.ofFinite _
  haveI : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥hyp.base.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- **Carrier 1 (the coherent `τ₁`-image family, now DISCHARGED from the (14.9) coherence).**
  -- The intrinsic type-III datum builds the degree-`p` `Ind_{QV}^T`-family `calT1_set` with all
  -- coherence inputs (`T_typeIII_calT1_family`); the T-side Dade package + coherence engine
  -- (`T_typeIII_calT1_isCoherent`, i.e. `T_typeIII_hyp07` ∘ `T_typeIII_calT1_coherent`) then produce
  -- the coherent map `τ₁ = hτ.extension`.  Its image `calT1 := τ₁(calT1_set)` is an **orthonormal**
  -- set of `G`-class functions (`horth`), because `τ₁` is an isometry on `ℤ[calT1_set]`
  -- (`IsCoherent.extension_inner_eq`) and the source members are orthonormal irreducibles.
  obtain ⟨𝒯, hinertia, hne, hlinear, hconj𝒯, hcount_V⟩ :=
    T_typeIII_calT1_family hyp hIII.some
  set calT1_set : Set (ClassFunction ↥hyp.base.T ℂ) :=
    ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)) with hcalT1
  -- Members of `calT1_set` are orthonormal irreducibles of `T` (irreducible + pairwise orthogonal
  -- via `T_typeIII_hyp07`'s family predicates), reused below for `horth`.
  have hirr : ∀ χ ∈ calT1_set, IsIrreducibleCharacter χ := by
    intro χ hχ
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at hχ
    obtain ⟨θ, hθ, rfl⟩ := hχ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  -- `hcard2 : 2 ≤ |calT1_set|` — the crude size bound `(|V|−1)/p ≥ 2`, **ungated**: from the
  -- intrinsic `2p + 1 ≤ |V|` (`T_typeIII_two_p_add_one_le_card_V`, odd-order Frobenius `U ⋊ W₁`)
  -- and the count `|calT1_set| = (|V|−1)/p` (`hcount_V`), via `2 ≤ (|V|−1)/p ⟺ 2p ≤ |V|−1`.  The
  -- lane-b `|V|`-lower-bound (`v = (q^p−1)/(q−1)`, 13.15) is only needed for the *exact* count, not
  -- this `≥ 2`.
  have hcard2 : 2 ≤ calT1_set.ncard := by
    have hV := T_typeIII_two_p_add_one_le_card_V hG hyp hIII.some
    have hncard : calT1_set.ncard = (Nat.card ↥hyp.base.V - 1) / hyp.base.p := by
      rw [hcalT1, Set.ncard_coe_finset]; exact hcount_V
    rw [hncard, Nat.le_div_iff_mul_le hyp.base.p_prime.pos]
    omega
  -- The T-side coherence: `τ₁ = hτ.extension`, `IsCoherent (tSideDadeMap) calT1_set A₁(T)`.
  obtain ⟨hyp07, _htau, ⟨hτ⟩⟩ :=
    T_typeIII_calT1_isCoherent hyp hG hIII 𝒯 hinertia hlinear hne hconj𝒯 calT1_set hcalT1 hcard2
  -- `calT1 := τ₁(calT1_set)`, the coherent-image `Finset` in `CF(G)`.
  set calT1 : Finset (ClassFunction G ℂ) :=
    calT1_set.toFinset.image (⇑hτ.extension) with hcalT1img
  -- **`horth`: the coherent images are orthonormal** — the discharged coherence carrier.
  have horth : ∀ a ∈ calT1, ∀ b ∈ calT1,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0 := by
    intro a ha b hb
    rw [hcalT1img, Finset.mem_image] at ha hb
    obtain ⟨ζ, hζT, rfl⟩ := ha
    obtain ⟨ζ', hζ'T, rfl⟩ := hb
    rw [Set.mem_toFinset] at hζT hζ'T
    -- `⟨τ₁ζ, τ₁ζ'⟩ = ⟨ζ, ζ'⟩` (coherent isometry on `ℤ[calT1_set]`).
    have hiso : ClassFunction.inner (hτ.extension ζ) (hτ.extension ζ')
        = ClassFunction.inner ζ ζ' :=
      hτ.extension_inner_eq ζ ζ' (Submodule.subset_span hζT) (Submodule.subset_span hζ'T)
    -- `⟨ζ, ζ'⟩ = if ζ = ζ' then 1 else 0` (orthonormal irreducibles).
    have hsrc : ClassFunction.inner ζ ζ' = if ζ = ζ' then (1 : ℂ) else 0 := by
      by_cases hζζ' : ζ = ζ'
      · subst hζζ'; rw [if_pos rfl]; exact (hirr ζ hζT).inner_self_eq_one
      · rw [if_neg hζζ']; exact hyp07.pairwise_orthogonal hζT hζ'T hζζ'
    rw [hiso, hsrc]
    -- The image equality `τ₁ζ = τ₁ζ'` iff `ζ = ζ'` (injectivity from the isometry).
    by_cases hζζ' : ζ = ζ'
    · rw [if_pos hζζ', if_pos (by rw [hζζ'])]
    · rw [if_neg hζζ', if_neg ?_]
      -- if `τ₁ζ = τ₁ζ'` then `⟨ζ,ζ'⟩ = ⟨τ₁ζ,τ₁ζ⟩ = ⟨ζ,ζ⟩ = 1 ≠ 0 = ⟨ζ,ζ'⟩`, contradiction.
      intro hab
      have h1 : ClassFunction.inner ζ ζ' = ClassFunction.inner ζ ζ := by
        rw [← hiso, ← hab,
          hτ.extension_inner_eq ζ ζ (Submodule.subset_span hζT) (Submodule.subset_span hζT)]
      rw [hsrc, if_neg hζζ', (hirr ζ hζT).inner_self_eq_one] at h1
      exact one_ne_zero h1.symm
  -- **The gated `S`-side `βₛ` bridge content** (one documented residual `sorry`), now reduced by the
  -- `T_typeIII_ratio_le_of_sSide_gap` extraction engine to *just* the `βₛ`-gap facts — the orthogonal
  -- split (`Γ₁`/`hdecomp`/`hΓ₁`) is **no longer** part of the residual (the engine derives it):
  --   • `hcount`  = `|calT1| = (v−1)/p` — the coherent count `hcount_V` (`|calT1_set| = (|V|−1)/p`,
  --     proven, via `T_typeIII_calT1_family`) composed with the (13.12) `d = 1` substitution
  --     `v = |V|` (`S15.V_inf_centralizer_Q_eq_bot`, lane-b);
  --   • `hxcoe`/`hx` = the `S`-side gap coefficients `⟨Γ, ζ⟩ = x_ζ ∈ ℤ` with parity nonzeroness
  --     `x_ζ ≠ 0` (Coq `nzT1_Ga`, via `S09.cfdot_real_vchar_even`);
  --   • `hnorm`   = the `S`-side norm bound `⟨Γ,Γ⟩ ≤ (u−1)/q` on the bridge gap.
  -- (`horth` is discharged from the (14.9) coherence; `hdecomp`/`hΓ₁` from the engine.)
  obtain ⟨Γ, x, hcount, hxcoe, hx, hnorm⟩ :
      ∃ (Γ : ClassFunction G ℂ) (x : ClassFunction G ℂ → ℤ),
        (calT1.card : ℚ) = ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ∧
        (∀ a ∈ calT1, ClassFunction.inner Γ a = ((x a : ℝ) : ℂ)) ∧
        (∀ a ∈ calT1, x a ≠ 0) ∧
        (ClassFunction.inner Γ Γ).re ≤
          ((((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) : ℚ) : ℝ) := by
    sorry
  exact T_typeIII_ratio_le_of_sSide_gap hyp calT1 horth hcount Γ x hxcoe hx hnorm

/-- **Complement-conjugacy transfer of commutativity `V → d.U`** (`T`-side, ungated by (14.9)).
Given that the `κ`-Hall complement `V` of `Q = T_F` in `T' = [T,T]` is abelian, *any* type-`P`
witness `d` on `T` has its own derived complement `d.U` (the `H = M_F` complement in `T'`) abelian
too.  Both `V` and `d.U` complement the *same* normal Hall subgroup `Q = d.H` in `T'` (`Q ⋊ V = T' =
Q ⋊ d.U`), so Schur–Zassenhaus conjugacy inside `↥T'` (`IsComplement'.exists_conj_of_coprime`,
coprimality from `Q` being Hall in `T`) conjugates `V` onto `d.U`, transporting `IsMulCommutative`.

Structurally the mirror of `S15.isMulCommutative_V` (which runs `d.U → V`); the sole difference is
that the `(|Q|, |V|)`-coprimality is sourced from `maxNilpotentNormalHall_isHall` +
`IsHallSubgroup.coprime_index` (with `|V| = [T':Q] ∣ [T:Q]` via the tower law) rather than from a
`TypeIIData`, so it is available for a *generic* `TypePData d`. -/
theorem isMulCommutative_typePData_U_of_V [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (d : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hVcomm : IsMulCommutative ↥hyp.base.V) :
    IsMulCommutative ↥d.U := by
  have hdisj : hyp.base.Q ⊓ hyp.base.V = ⊥ := hyp.base.Q_inf_V_eq_bot
  have hQH : hyp.base.Q = d.H := by rw [hyp.base.Q_eq_TF, d.H_eq]
  have hQ_le : hyp.base.Q ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.base.V ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right
  have hM'_le_T : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hQ_le_T : hyp.base.Q ≤ hyp.base.T := by
    rw [hyp.base.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.base.T
  have hT_le_NQ : hyp.base.T ≤ Subgroup.normalizer (hyp.base.Q : Set G) := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T
  haveI hQn_normal : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  have hVcompl : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).IsComplement'
      (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
        OneMemClass.coe_one]
      refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
      have hxQV : x ∈ (hyp.base.Q ⊓ hyp.base.V : Subgroup G) := ⟨hxQ, hxV⟩
      rwa [hdisj, Subgroup.mem_bot] at hxQV
    · have hsup : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) ⊔
          (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.base.T_deriv_eq_QV.symm,
          Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (hyp.base.Q.subgroupOf (derivedInG hyp.base.T))
        (hyp.base.V.subgroupOf (derivedInG hyp.base.T))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  have hV'compl : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).IsComplement'
      (d.U.subgroupOf (derivedInG hyp.base.T)) := by
    rw [hQH]; exact d.derived_complement
  have hcop : Nat.Coprime (Nat.card ↥(hyp.base.Q.subgroupOf (derivedInG hyp.base.T)))
      ((hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).index) := by
    -- `|Q|` (Hall in `T`) is coprime to `[T:Q]`; and `[T':Q] ∣ [T:Q]` by the tower law
    -- (`Q ≤ T' ≤ T`).  `(Q.subgroupOf T').index = Q.relIndex T' ∣ Q.relIndex T`.
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.base.T
    rw [← hyp.base.Q_eq_TF] at hHall
    have h0 := OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv] at h0
    -- `h0 : Nat.Coprime (Nat.card ↥Q) (Q.relIndex T)`
    have hcard : Nat.card ↥(hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) = Nat.card ↥hyp.base.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv
    have hdvd : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).index ∣
        (hyp.base.Q.subgroupOf hyp.base.T).index := by
      have htower : hyp.base.Q.relIndex (derivedInG hyp.base.T) *
          (derivedInG hyp.base.T).relIndex hyp.base.T = hyp.base.Q.relIndex hyp.base.T :=
        Subgroup.relIndex_mul_relIndex hyp.base.Q (derivedInG hyp.base.T) hyp.base.T hQ_le hM'_le_T
      show hyp.base.Q.relIndex (derivedInG hyp.base.T) ∣ hyp.base.Q.relIndex hyp.base.T
      exact ⟨(derivedInG hyp.base.T).relIndex hyp.base.T, htower.symm⟩
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right hdvd h0
  have hQ_lt_top : hyp.base.Q < ⊤ :=
    lt_of_le_of_lt hQ_le_T (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.base.T_maximal).1)
  haveI hQsolv : IsSolvable ↥hyp.base.Q := hG.solvable_of_lt_top hyp.base.Q hQ_lt_top
  have hsolv : IsSolvable ↥(hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) ∨
      IsSolvable (↥(derivedInG hyp.base.T) ⧸ hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) :=
    Or.inl (solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQ_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ_le).injective)
  obtain ⟨n, _hnQ, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hVcompl hV'compl
  -- `hn : (V.subgroupOf T').map (conj n) = d.U.subgroupOf T'`.  Push `V` commutative forward.
  have hVsub : IsMulCommutative ↥(hyp.base.V.subgroupOf (derivedInG hyp.base.T)) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hV_le).symm hVcomm
  have hmapped : IsMulCommutative
      ↥((hyp.base.V.subgroupOf (derivedInG hyp.base.T)).map (MulAut.conj n).toMonoidHom) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective) hVsub
  rw [hn] at hmapped
  exact OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe d.U_le) hmapped

/-- **Peterfalvi (11.9)/(14.9), the Type-IV exclusion residual** — the genuine deep content of the
type determination.  Coq `FTtype34_structure` (Peterfalvi (11.9), `PFsection11.v:1001`, consumed at
`PFsection14.v:735`) pins a non-type-II type-`P` maximal `T` to Type III (not IV) via the
character/Galois argument `suffices galM : typeP_Galois MtypeP` (`PFsection11.v:1139`) — the
`η`-grid projection computation `a₁₁ = a₁₀ = 0`.  In this formalisation the III/IV discriminator is
`IsMulCommutative U` (`TypeIIIData` carries `U_commutative`, `TypeIVData` its negation), so the
(11.9) content is exactly: *`T`'s derived complement `U`-factor (`= V`) is abelian*.

This is genuine §11 character theory — **not** a σ-structural config fact — and is formalised
nowhere in this repo (the §11/§13 layer `S13_MaximalIII_IV` only ever *posits* `IsTypeIII M ∨
IsTypeIV M`, and there is no universal Type-IV exclusion analogous to the proven Type-V one
`no_typeV_maximal`).  Isolated here as the *single* residual of the (14.9) type determination:
everything else (Type-V exclusion, the III/IV structural wiring incl. `normalizer_le`) is proven in
`T_isTypeIII_of_isTypeP1` below. -/
theorem T_not_isTypeIV_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    ¬ OddOrder.GroupTheory.IsTypeIV hyp.base.T := by
  -- Coq (11.9) `FTtype34_structure` ⟹ `typeP_Galois T` ⟹ (in the `IsMulCommutative U` presentation)
  -- the `U = V` factor is abelian, so `T` is Type III not IV.  The deep character/projection argument
  -- is now isolated to the single residual `hVcomm` (`V` abelian); everything else is the honest
  -- complement-conjugacy transfer `isMulCommutative_typePData_U_of_V`.
  --
  -- EXACT REDUCTION of `IsMulCommutative V` (verified against Coq `PFsection{9,11}.v`, 2026-07-06):
  --   V abelian  ⟸  `cyclic V`  ⟸  `typeP_Galois T`  (the genuine (11.9) content).
  -- Coq chain (`FTtype34_structure`, `PFsection11.v:1139-1144`):
  --   `suffices galM : typeP_Galois MtypeP` (`:1139`); then
  --   `typeP_Galois_P` (`PFsection9.v:501-511`) extracts `cyclic Ubar` (`:1140`), and
  --   `cyclic V` + `nilpotent V` ⟹ `cyclic V` ⟹ `abelian V`
  --   (`cyclic_nilpotent_quo_der1_cyclic`/`cyclic_abelian`, `:1144`).
  -- `typeP_Galois := acts_irreducibly U Hbar 'Q` (`PFsection9.v:323`): `V` acts IRREDUCIBLY on
  -- `Hbar = Q/Φ(Q)`.  Proving THAT is the `η`-grid projection `a₁₁ = a₁₀ = 0` (`PFsection11.v:1041-
  -- 1126`), whose inputs are the FULL §3–§11 apparatus: `S₁`-coherence (`cohS1`), the Dade isometry
  -- (`Dade_isometry`/`Dade_reciprocity`, §4/§5), the cyclic-TI isometry (`cycTIiso`,
  -- `coherent_ortho_cycTIiso`, §3), and prime-TI reducibles (`prTIred`) — via the norm bound
  -- `⟨X,X⟩ ≤ q` and odd-order parity.  So this is genuinely (11.9)-GATED, NOT σ-theory: the §9/§13
  -- σ-engine (`card_le_cyclotomicQuotient_of_faithful_fpf`, `TypePGaloisUBound.lean`) is the (13.2.c)
  -- `u`-bound `|V| ≤ (p^q−1)/(p−1)` which CARRIES `[CommGroup V]` as a hypothesis — it consumes
  -- commutativity, never proves it.
  --
  -- WHY NOT STRUCTURALLY FREE (contrast S-side): the S-side `U` is abelian for free via BG 15.1(b)
  -- (`typeP_hall_derived_eq_and_abelian`, `⁅U,U⁆ ≤ U ⊓ M_σ = ⊥`) BECAUSE `U` is the `(κ∪σ)'`-Hall
  -- of `S`.  For type `P₁` (`IsTypeP1 T ⟺ κ(T) = σ'(T) = π(T) ∖ σ(T)`, `S14.IsTypeP1`), the
  -- `(κ∪σ)'`-Hall is TRIVIAL (`κ ∪ σ = π`) and `V` is instead the κ-Hall complement to `Q = T_F` in
  -- `T' = Q ⋊ V`; with `T_F ⊊ M_σ` (III/IV case) one gets `V ⊓ M_σ ≠ ⊥` (exactly the σ-part that,
  -- at type IV, is where non-commutativity lives), so the `⁅V,V⁆ ≤ V ⊓ M_σ = ⊥` mechanism FAILS.
  -- Structurally `V` is only known to be a nilpotent Frobenius kernel (`Hypothesis.isNilpotent_V`,
  -- `V ⋊ W₂` Frobenius with `C_V(W₂) = ⊥`) — nilpotent ⇏ abelian.  No lane-c-doable sub-part
  -- advances this: even the final `nilpotent + cyclic V/V' ⟹ abelian` step needs `cyclic V`, which
  -- is downstream of `typeP_Galois`.  Missing bridge (Lean): a `typeP_Galois`/`cyclic V` producer,
  -- itself requiring the §5–§11 coherence/Dade layer (S05/S06/S07 Dade + coherence, still sorried).
  have hVcomm : IsMulCommutative ↥hyp.base.V := sorry  -- (11.9)-gated: V (=T's U-factor) abelian ⟸ `cyclic V` ⟸ `typeP_Galois T`
  rintro ⟨d⟩
  exact d.U_not_commutative (isMulCommutative_typePData_U_of_V hG hyp d.typeP hVcomm)

/-- **Peterfalvi (14.9), the type determination** — Coq `PFsection14`
`have [_ _ [Ttype3 _]] := FTtype34_structure maxT TtypeP notTtype2` (line 735): a type-`P` maximal
subgroup that is *not* type II is type III.  In σ-theoretic terms, `IsTypeP1 T` (equivalently
`¬ IsTypeP2 T` given `IsTypeP T`) forces `T` to be structurally Type III.

**Fully reduced to the single (11.9) residual `T_not_isTypeIV_of_isTypeP1`.**  The type dictionary
`proposition_type_classification` (BG Prop 16.1, proven) gives, from `IsTypeP1 T`, either Type III/IV
(if `M_F ≠ M_σ`) or Type V (if `M_F = M_σ`).  **Type V is excluded outright** by Peterfalvi (10.10)
`no_typeV_maximal` (proven — no maximal subgroup of a minimal simple group of odd order is Type V),
so `M_F ≠ M_σ` and `T` is Type III or IV.  Excluding Type IV — the genuine (11.9) Galois/character
content — is the isolated residual `T_not_isTypeIV_of_isTypeP1`.  The Type-V exclusion and the III/IV
structural wiring (incl. the `TypeIIIData.normalizer_le` field, bundled into the clause-(c)
disjunction) are proven here. -/
theorem T_isTypeIII_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    OddOrder.GroupTheory.IsTypeIII hyp.base.T := by
  -- Type dictionary (BG Prop 16.1): `IsTypeP1 T` ⟹ III/IV (`M_F ≠ M_σ`) or V (`M_F = M_σ`).
  obtain ⟨_, _, hcIII_IV, hdV, _, _⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.base.T_maximal
  -- Type V excluded universally by Peterfalvi (10.10) `no_typeV_maximal`, so `M_F ≠ M_σ`.
  have hMF : OddOrder.BG.Ch4.S15.MF hyp.base.T ≠ OddOrder.BG.Ch3.S10.Msigma hyp.base.T := fun h =>
    OddOrder.Peterfalvi.S12.no_typeV_maximal hG ⟨hyp.base.T, hyp.base.T_maximal, hdV.mpr ⟨hP1, h⟩⟩
  -- `T` is Type III or IV; exclude IV by the (11.9) residual.
  exact (hcIII_IV.mpr ⟨hP1, hMF⟩).resolve_right (T_not_isTypeIV_of_isTypeP1 hG hyp hP1)

/-- **Peterfalvi (14.9), reduced to its canonical residual** — the `T`-side dual of the `S`-side
`(13.2.a)` carrier field `S_typeP2`.  `T` is of BG type `P₂` (`κ(T) ≠ σ'(T)`; Coq `PFsection14`
`FTtypeP_min_typeII : FTtype T == 2`).  The `IsTypeP T` conjunct is discharged honestly from `T_nonI`
(`isTypeP_of_isTypeNonI`).

The residual `κ(T) ≠ σ'(T)` is proved by the (14.9) contradiction, following Coq
`FTtypeP_min_typeII` (`apply: contraLR v1p_gt_u1q => notTtype2`): were `κ(T) = σ'(T)` (i.e.
`IsTypeP1 T`), then `T` is Type III (`T_isTypeIII_of_isTypeP1`, the `FTtype34_structure`
determination), whence the character body forces `(v − 1)/p ≤ (u − 1)/q` (`T_typeIII_ratio_le`) —
contradicting (14.8) `key_inequality`'s `(v − 1)/p > (u − 1)/q`.

The two deep pieces are isolated as `T_typeIII_ratio_le` (character body) and
`T_isTypeIII_of_isTypeP1` (type determination), both consumed below.  The `>` half is (14.8);
because the file's `T_typeII` feeds `T_side_caseB_facts` (whose case-(9.7.b) `v`-value is what
`key_inequality`'s `>` rests on), `T_isTypeP2` is strictly upstream of `key_inequality` in this
file's linearization and cannot cite it — so the `>` fact is left as this theorem's single residual,
a documented forward reference to `key_inequality` (proved later in this same file). -/
theorem T_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch4.S14.IsTypeP2 hyp.base.T := by
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.base.T_maximal hyp.base.T_nonI
  refine ⟨hP, ?_⟩
  -- (14.9), by contradiction (Coq `contraLR v1p_gt_u1q => notTtype2`): assume `κ(T) = σ'(T)`.
  intro hκeq
  -- Then `T` is type `P₁`, hence (Coq `FTtype34_structure`) structurally Type III.
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := ⟨hP, hκeq⟩
  have hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T := T_isTypeIII_of_isTypeP1 hG hyp hP1
  -- The character body then gives the type-III Γ-bridge estimate `(v − 1)/p ≤ (u − 1)/q`.
  have hle : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := T_typeIII_ratio_le hG hyp hIII
  -- (14.8) `key_inequality` gives the strict `>`, contradicting `hle`.  `key_inequality` is proved
  -- below in this file but is unreachable here (its `>` rests on the case-(9.7.b) `v`-value, which
  -- flows through `T_side_caseB_facts ← T_typeII ← T_isTypeP2`), so the `>` is this theorem's
  -- single documented forward residual.
  have hgt : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
    -- (14.8) = `(key_inequality hG hyp).2`; forward-referenced.
    sorry
  exact absurd hle (not_le.mpr hgt)

/-- **Peterfalvi (14.9)**: the subgroup `T` is of Type II.  Dual to the `S`-side `(13.2.a)` line
`isTypeII_of_isTypeP2 … S_maximal S_typeP2`: `T` is of type `P₂` (`T_isTypeP2`), and *every* type-`P₂`
maximal subgroup is type II by the proven BG bridge `isTypeII_of_isTypeP2`.  That bridge discharges
the deep `M'`-type-`F` structure — `IsTypeF (derivedInG T)` and `(T')_F = T_F` — internally
(`isTypeF_derivedInG_of_isTypeP2`), so the sole residual of (14.9) is the type-`P₂` fact `T_isTypeP2`.
(Placed ahead of `exists_LHypothesis` so the §14 `T`-side chain — `typeII_overNormalizer_frobenius`
etc. — can cite `IsTypeII T` locally.) -/
theorem T_typeII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    IsTypeII hyp.base.T :=
  OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.base.T_maximal (T_isTypeP2 hG hyp)

/-- **Peterfalvi (14.3)**: a type-I maximal subgroup `L` over `N_G(U)` exists.  Constructed by
citing (13.17) `S15.typeII_overNormalizer_frobenius` for the type-I-over-normalizer Frobenius data
(`S` is type II by `basic_structure` + (14.1) `q < p`); the complement order `|C| = p q` is a field
`complement_card_eq_pq` of that data ((13.17.c)/(14.5)).  The (14.3.b) Dade data is not carried —
it is unused by the §14 non-existence argument, so the carrier holds exactly the structural data the
proof consumes.  Placed here (ahead of the (14.4)--(14.16) lemmas) so the mid-file numeric lemmas
can construct an `LHypothesis` to feed the S-side case-(9.7.b) data `caseB_for_S`. -/
theorem exists_LHypothesis [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (LHypothesis hyp) := by
  obtain ⟨bdata, _⟩ := OddOrder.Peterfalvi.S15.basic_structure _hG hyp.base
  have hSII : IsTypeII hyp.base.S := bdata.q_lt_p_forces_typeII hyp.q_lt_p
  have hTII : IsTypeII hyp.base.T := T_typeII _hG hyp
  obtain ⟨typeI_data, _, _⟩ :=
    OddOrder.Peterfalvi.S15.typeII_overNormalizer_frobenius _hG hyp.base hSII hTII
  exact ⟨⟨typeI_data.L, typeI_data.H, typeI_data.L_maximal, typeI_data.normalizer_U_le_L,
    typeI_data.H_eq_LF, typeI_data, rfl, rfl, typeI_data.complement_card_eq_pq⟩⟩

/-- Carrier for the case-(9.7.b) conclusion applied to `T` in Peterfalvi
(14.4). -/
structure CaseBForTData (hyp : Hypothesis (G := G)) where
  caseB_formula : Prop
  caseB_holds : caseB_formula
  D_eq_bot : hyp.base.D = ⊥
  v_eq : hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1)

namespace CaseBForTData

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
odd. -/
theorem v_odd {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    Odd hyp.base.v := by
  rw [data.v_eq]
  exact hyp.tSide_cyclotomic_quotient_odd

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
positive. -/
theorem v_pos {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    0 < hyp.base.v :=
  Odd.pos data.v_odd

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
nonzero. -/
theorem v_ne_zero {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    hyp.base.v ≠ 0 :=
  ne_of_gt data.v_pos

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
coprime to `q - 1`. -/
theorem v_coprime_q_sub_one {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    Nat.Coprime hyp.base.v (hyp.base.q - 1) := by
  rw [data.v_eq]
  exact hyp.tSide_cyclotomic_quotient_coprime

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, every
positive divisor of `v` is `1 mod p`. -/
theorem divisor_modEq_one {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    ∀ x : ℕ, x ≠ 0 → x ∣ hyp.base.v → x ≡ 1 [MOD hyp.base.p] := by
  intro x hx hxdvd
  apply hyp.tSide_cyclotomic_quotient_divisor_modEq_one x hx
  rw [data.v_eq] at hxdvd
  exact hxdvd

end CaseBForTData

/-- The genuinely character/field-gated inputs of the `T`-side **(13.15)** `v`-value (04.16 p. 87,
"`q ≢ 1 (mod p)`, and so `v = (q^p − 1)/(q − 1)` by (13.15)").  Packaged as an existential over the
cofactor `x` (`v·x = (q^p − 1)/(q − 1)`) and the `T`-side norm parameter `mᵀ`, carrying exactly the
case-(9.7.b) data that Peterfalvi's proof of (13.15) consumes with the roles of `p, q` swapped: the
(13.10)-dual analytic inequality, the (13.11)-dual `mᵀ`-lower bounds, and `v ≠ 1`.

These land once the generic §13 estimates do (issue 9013 案 A → `typeP_Galois`, issue 9000) together
with the `T`-side field model (`TFieldModelData`, issue-9000 sphere).  This is the *single* gated
residue of `T_side_caseB_facts.2`: the proven side-agnostic numeric engine
`S15.caseB_order_u_full_of_not_modEq` (`S16_CaseBOrder`) discharges all the arithmetic from these.
(The `(13.11.c)` bound `h11c` is *not* needed on the `T`-side — it is vacuous since `p ≠ 3`.) -/
theorem tSide_caseB_v_gated_inputs [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ (x : ℕ) (mT : ℚ),
      hyp.base.v * x = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) ∧
        hyp.base.v ≠ 1 ∧ x ≠ 0 ∧
        (5 ≤ hyp.base.p → (7 : ℚ) / 10 < mT) ∧
        (7 ≤ hyp.base.p → (8 : ℚ) / 10 < mT) ∧
        mT < (hyp.base.p : ℚ) * ((hyp.base.q : ℚ) ^ hyp.base.p - 1)
          / ((hyp.base.q : ℚ) ^ (hyp.base.p - 1) * (x : ℚ) * ((hyp.base.q : ℚ) - 1)) := by
  sorry

/-- **Peterfalvi (14.4) `T`-side numeric facts**: in case (9.7.b) for `T` (which holds since
`q < p ⟹ p ≠ 3`, by (13.13) applied to `T`), the dual centralizer parameter vanishes (`D = ⊥`,
dual of (13.12) `c = 1`) and `v` takes its full cyclotomic value (`v = (q^p−1)/(q−1)`, dual of
(13.15)).  The §13 `T`-side obligation feeding (14.4). -/
theorem T_side_caseB_facts [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.D = ⊥ ∧
      hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
  refine ⟨?_, ?_⟩
  · -- **Peterfalvi (13.12) dual** `d = 1`: `D = V ⊓ C_G(Q) = ⊥`, the canonical §15 obligation
    -- `V_inf_centralizer_Q_eq_bot` (`T` type-II from `T_typeII` (14.9)).
    rw [hyp.base.D_eq]
    exact OddOrder.Peterfalvi.S15.V_inf_centralizer_Q_eq_bot _hG hyp.base (T_typeII _hG hyp)
  · -- **Peterfalvi (13.15) dual** via the *proven* side-agnostic numeric engine
    -- `caseB_order_u_full_of_not_modEq` (`S16_CaseBOrder`) with the roles of `p, q` swapped
    -- (`04.16` p. 87 applies (13.15) to `T`).  The ungated arithmetic — primality, oddness, the
    -- branch selector `q ≢ 1 (mod p)`, the vacuous `p = 3` bound, and `¬ p ∣ v` (from the (13.14)-dual
    -- divisor congruence) — is discharged here; the char/field content is the single gated residue
    -- `tSide_caseB_v_gated_inputs`.
    obtain ⟨x, mT, hux, hv1, hx0, hm5, hm7, hanalytic⟩ := tSide_caseB_v_gated_inputs _hG hyp
    have hvdvd : hyp.base.v ∣ (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := ⟨x, hux.symm⟩
    have hpnv : ¬ hyp.base.p ∣ hyp.base.v := by
      intro hpv
      have hpmod : hyp.base.p ≡ 1 [MOD hyp.base.p] :=
        hyp.tSide_cyclotomic_quotient_divisor_modEq_one hyp.base.p
          hyp.base.p_prime.pos.ne' (hpv.trans hvdvd)
      have h1 : (1 : ℕ) < hyp.base.p := hyp.base.p_prime.one_lt
      have hpmod' : hyp.base.p % hyp.base.p = 1 % hyp.base.p := hpmod
      rw [Nat.mod_self, Nat.mod_eq_of_lt h1] at hpmod'
      exact absurd hpmod' (by norm_num)
    exact OddOrder.Peterfalvi.S15.caseB_order_u_full_of_not_modEq
      hyp.base.q_prime hyp.base.p_prime hyp.base.three_le_q
      (by have := hyp.five_le_p; omega) (ne_of_lt hyp.q_lt_p)
      hyp.base.q_odd hyp.base.p_odd hyp.q_not_modEq_one_mod_p
      hux hv1 hpnv hx0 hm5 hm7
      (fun hp3 => absurd hp3 (by have := hyp.five_le_p; omega)) hanalytic

/-- **Peterfalvi (14.4)**: case (9.7.b) holds for `T`, and `v = (q^p - 1) / (q - 1)`.  The numeric
content (`D = ⊥`, `v` full) is the named §13 obligation `T_side_caseB_facts`; the case-(9.7.b)
proposition is carried trivially (no consumer reads it). -/
theorem caseB_for_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧
        hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) :=
  ⟨⟨True, trivial, (T_side_caseB_facts _hG hyp).1, (T_side_caseB_facts _hG hyp).2⟩,
    trivial, (T_side_caseB_facts _hG hyp).2⟩

/-- **Peterfalvi (14.5)**: there is an element `y ∈ Q` such that `L = H ⋊ (W₁ W₂^y)`.
The downstream-relevant content of the split is that the conjugate `W₂^y` lands in the
Frobenius complement of `L` (the complement `W₁W₂^y`); this is the concrete form consumed by
`u_modEq_one_mod_p_of_LHypothesis` (the (14.7) fixed-point-free value argument) and, through it,
the part-(14.2.b) normalizer input `W₂^y ≤ N_G(U)`.  Its proof rules out the alternative
`L = H ⋊ W₁` of (13.17.c) via (13.19.c1)/(13.2.a). -/
theorem exists_y_L_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) :
    ∃ y ∈ hyp.base.Q, (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Ldata.typeI_data.frobenius.complement.map (Ldata.typeI_data.L).subtype :=
  Ldata.typeI_data.exists_y_W2_conj_le_complement

/-- Carrier for the case-(9.7.b) conclusion applied to `S` in Peterfalvi
(14.6). -/
structure CaseBForSData (hyp : Hypothesis (G := G)) where
  caseB_formula : Prop
  caseB_holds : caseB_formula
  order : OddOrder.Peterfalvi.S15.CaseBOrderUData hyp.base caseB_formula
  U_rank_obstruction : Prop
  U_rank_obstruction_holds : U_rank_obstruction

namespace CaseBForSData

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
`p ≡ 1 mod q` branch gives the divided cyclotomic value of `u`. -/
theorem u_eq_of_p_modEq_one {hyp : Hypothesis (G := G)} (data : CaseBForSData hyp) :
    hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1)) :=
  data.order.u_eq_of_p_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
non-`p ≡ 1 mod q` branch gives the full cyclotomic value of `u`. -/
theorem u_eq_of_not_modEq_one {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
  data.order.u_eq_of_not_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, `u` is at
most the full cyclotomic quotient.  The `p ≡ 1 mod q` branch divides that
quotient by the additional factor `q`; the other branch is equality. -/
theorem u_le_full_cyclotomic {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    hyp.base.u ≤ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · rw [data.u_eq_of_p_modEq_one hmod]
    have hp1_pos : 0 < hyp.base.p - 1 := by
      have hp2 : 2 ≤ hyp.base.p := hyp.base.p_prime.two_le
      omega
    have hden_le : hyp.base.p - 1 ≤ hyp.base.q * (hyp.base.p - 1) := by
      have hqpos : 1 ≤ hyp.base.q := hyp.base.q_prime.one_le
      nlinarith [Nat.mul_le_mul_right (hyp.base.p - 1) hqpos]
    exact Nat.div_le_div_left hden_le hp1_pos
  · rw [data.u_eq_of_not_modEq_one hmod]

end CaseBForSData

/-- **Peterfalvi (14.6)**: case (9.7.b) holds for `S`.

Following the opaque-`Prop` convention of this file (see `caseB_for_T`), the qualitative
case-(9.7.b) proposition `caseB_formula` is carried trivially (no consumer reads it — the
downstream cascade reads only the numeric `order` data).  The numeric content — the `u`-order
of (13.15) — is supplied by `S15.caseB_order_u_data` (the §13 obligation, currently a named
upstream `sorry`); citing it wires the S-side `u`-value into the (14.8)/(14.11) cascade exactly
as `caseB_for_T` wires the T-side `D = ⊥`/`v` value via `T_side_caseB_facts`.  The full
group-theoretic (14.6) argument (the rank-2 Sylow contradiction ruling out case (9.7.a), via
(13.13)/(9.7.a)/[BG] 1.16/(13.2.e)/(13.17)) is §13/§9 character/structure theory upstream. -/
theorem caseB_for_S [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_Ldata : LHypothesis hyp) :
    ∃ data : CaseBForSData hyp, data.caseB_formula :=
  ⟨⟨True, trivial,
      OddOrder.Peterfalvi.S15.caseB_order_u_data _hG hyp.base trivial, True, trivial⟩, trivial⟩

/-- Over `ℕ`, the geometric-sum identity `(p − 1) · ∑_{i<q} pⁱ = p^q − 1`. -/
private theorem pred_mul_geomSum (p q : ℕ) (hp : 1 ≤ p) :
    (p - 1) * ∑ i ∈ Finset.range q, p ^ i = p ^ q - 1 := by
  induction q with
  | zero => simp
  | succ n ih =>
      have hpn : 1 ≤ p ^ n := Nat.one_le_pow _ _ (by omega)
      have hle : p ^ n ≤ p ^ n * p := Nat.le_mul_of_pos_right _ (by omega)
      have key : (p - 1) * p ^ n = p ^ n * p - p ^ n := by
        rw [Nat.sub_mul, one_mul, Nat.mul_comm p (p ^ n)]
      rw [Finset.sum_range_succ, mul_add, ih, key, pow_succ]
      omega

/-- The geometric sum `∑_{i<q} pⁱ` is `≡ q (mod d)` whenever `p ≡ 1 (mod d)`,
since every `pⁱ ≡ 1`. -/
private theorem geomSum_modEq_card {p d : ℕ} (hpd : p ≡ 1 [MOD d]) (q : ℕ) :
    ∑ i ∈ Finset.range q, p ^ i ≡ q [MOD d] := by
  induction q with
  | zero => simp [Nat.ModEq]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hpow : p ^ n ≡ 1 [MOD d] := by simpa using hpd.pow n
      exact Nat.ModEq.add ih hpow

/-- **Peterfalvi (14.2)(a)** arithmetic core: when `q ∤ (p − 1)`, the cyclotomic
quotient `(p^q − 1)/(p − 1)` is prime to `p − 1`.  In (14.7) the hypothesis
`q ∤ (p − 1)` is `p ≢ 1 (mod q)`, which holds once `u` takes its full cyclotomic
value.  The quotient equals `∑_{i<q} pⁱ ≡ q (mod p − 1)`, so it is coprime to
`p − 1` exactly when `q` is, and `q` prime with `q ∤ (p − 1)` gives that.  This
discharges the `cyclotomic_coprime` field of `FieldNormalizerData`. -/
theorem cyclotomic_quotient_coprime_of_not_dvd {p q : ℕ} (hp : 2 ≤ p)
    (hq : q.Prime) (hnd : ¬ q ∣ (p - 1)) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) := by
  have hpd : p ≡ 1 [MOD (p - 1)] :=
    ((Nat.modEq_iff_dvd' (by omega : (1 : ℕ) ≤ p)).mpr (dvd_refl (p - 1))).symm
  have hdiv : (p ^ q - 1) / (p - 1) = ∑ i ∈ Finset.range q, p ^ i := by
    rw [← pred_mul_geomSum p q (by omega),
      Nat.mul_div_cancel_left _ (show 0 < p - 1 by omega)]
  have hmod : (∑ i ∈ Finset.range q, p ^ i) % (p - 1) = q % (p - 1) :=
    geomSum_modEq_card hpd q
  have hcoq : Nat.Coprime q (p - 1) := (Nat.Prime.coprime_iff_not_dvd hq).mpr hnd
  have hgcd : Nat.gcd (p - 1) (∑ i ∈ Finset.range q, p ^ i) = Nat.gcd (p - 1) q := by
    rw [Nat.gcd_rec (p - 1) (∑ i ∈ Finset.range q, p ^ i), Nat.gcd_rec (p - 1) q, hmod]
  rw [hdiv]
  have : Nat.gcd (∑ i ∈ Finset.range q, p ^ i) (p - 1) = 1 := by
    rw [Nat.gcd_comm, hgcd, Nat.gcd_comm]; exact hcoq
  exact this

/-! ### (14.7) σ-bridge: transporting the (14.2)(a) field model into `G`

The hard, *ungated* core of `field_normalizer_of_U_characteristic` is to turn the
abstract field isomorphism of Peterfalvi (14.2)(a) — produced by the Singer machinery
`exists_galoisField_repr` once the §13 inputs `Nat.card P = p^q`, `c = 1` are in hand —
into the concrete `FieldNormalizerData`, i.e. an injective `σ : 𝔽_{p^q} ⋊ U* →* G`
matching `P`, `U`, `W₂`.  The construction is a `SemidirectProduct.lift` of two transport
homomorphisms `fN : 𝔽_{p^q} →* G` (the additive kernel) and `fU : U* →* G` (the
norm-one complement), glued by the (14.2)(a) `U`-equivariance.  These pieces take the
isomorphism as *input*, so they are independent of the §13 character theory that supplies
it (`fieldNormalizerData_of_repr` below). -/

/-- **(14.7) σ-bridge, kernel half.**  Given the Peterfalvi (14.2)(a) additive
isomorphism `e : Additive ↥P ≃+ 𝔽_{p^q}`, this is the transport homomorphism
`P = 𝔽_{p^q} →* G` sending a field point `s` to the group element `e⁻¹ s ∈ P ≤ G`.
It is the kernel (`inl`) factor of the field-normalizer embedding `σ`. -/
noncomputable def fieldNormalizerKernelTransport (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q) :
    fieldNormalizerAdditiveGroup hyp →* G :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  { toFun := fun m =>
      ((Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥hyp.base.P) : G)
    map_one' := by simp
    map_mul' := fun m n => by
      simp [toAdd_mul, map_add, toMul_add] }

@[simp] theorem fieldNormalizerKernelTransport_apply (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
    (m : fieldNormalizerAdditiveGroup hyp) :
    fieldNormalizerKernelTransport hyp e m =
      ((Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥hyp.base.P) : G) :=
  rfl

/-- The kernel transport `fN` is injective: it is a coordinate-wise composition of the
bijections `e.symm`, `Additive.toMul` and the (injective) subgroup inclusion `P ↪ G`. -/
theorem fieldNormalizerKernelTransport_injective (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q) :
    Function.Injective (fieldNormalizerKernelTransport hyp e) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro m n hmn
  rw [fieldNormalizerKernelTransport_apply, fieldNormalizerKernelTransport_apply] at hmn
  have h1 : (Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥hyp.base.P) =
      Additive.toMul (e.symm (Multiplicative.toAdd n)) := Subtype.ext hmn
  have h2 : e.symm (Multiplicative.toAdd m) = e.symm (Multiplicative.toAdd n) :=
    Additive.toMul.injective h1
  have h3 : Multiplicative.toAdd m = Multiplicative.toAdd n := e.symm.injective h2
  exact Multiplicative.toAdd.injective h3

/-- The kernel transport `fN` has image exactly Peterfalvi's additive kernel `P`. -/
theorem fieldNormalizerKernelTransport_range (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q) :
    (fieldNormalizerKernelTransport hyp e).range = hyp.base.P := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [fieldNormalizerKernelTransport_apply]
    exact (Additive.toMul (e.symm (Multiplicative.toAdd m))).2
  · intro g hg
    refine ⟨Multiplicative.ofAdd (e (Additive.ofMul (⟨g, hg⟩ : ↥hyp.base.P))), ?_⟩
    rw [fieldNormalizerKernelTransport_apply]
    simp

/-- **(14.7) σ-bridge, complement half.**  Given the Peterfalvi (14.2)(a)
multiplicative character `μ : U →* 𝔽_{p^q}ˣ` realizing `U` as the norm-one units `U*`,
this is the transport homomorphism `U* →* G` inverting `μ` and including back into `G`.
It is the complement (`inr`) factor of the field-normalizer embedding `σ`. -/
noncomputable def fieldNormalizerComplementTransport (hyp : Hypothesis (G := G))
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :
    fieldNormalizerNormOneUnits hyp →* G :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  let μ' : ↥hyp.base.U →* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
    { toFun := fun u => ⟨μ u, hμ_range ▸ MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  let eU : ↥hyp.base.U ≃* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
    MulEquiv.ofBijective μ'
      ⟨fun a b h => hμ_inj (congrArg Subtype.val h),
       fun u => by
         obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (by rw [hμ_range]; exact u.2)
         exact ⟨v, Subtype.ext hv⟩⟩
  hyp.base.U.subtype.comp eU.symm.toMonoidHom

/-- The defining property of the complement transport `fU`: each norm-one unit `u*`
has a preimage `u'' ∈ U` whose field character is `u*` and whose image under `fU` is
exactly `u''`.  This packages everything the `SemidirectProduct.lift` compatibility
needs about `fU`. -/
theorem fieldNormalizerComplementTransport_exists (hyp : Hypothesis (G := G))
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q)
    (u : fieldNormalizerNormOneUnits hyp) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ v : ↥hyp.base.U,
      (μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) = (u : (GaloisField hyp.base.p hyp.base.q)ˣ) ∧
        fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range u = (v : G) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  set μ' : ↥hyp.base.U →* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
    { toFun := fun u => ⟨μ u, hμ_range ▸ MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp } with hμ'def
  set eU : ↥hyp.base.U ≃* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
    MulEquiv.ofBijective μ'
      ⟨fun a b h => hμ_inj (congrArg Subtype.val h),
       fun u => by
         obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (by rw [hμ_range]; exact u.2)
         exact ⟨v, Subtype.ext hv⟩⟩ with heUdef
  refine ⟨eU.symm u, ?_, rfl⟩
  have hval : (eU (eU.symm u) : ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q)) = u :=
    eU.apply_symm_apply u
  have : (μ (eU.symm u) : (GaloisField hyp.base.p hyp.base.q)ˣ) = (u : (GaloisField hyp.base.p hyp.base.q)ˣ) := by
    have h1 : (μ' (eU.symm u) : (GaloisField hyp.base.p hyp.base.q)ˣ) =
        (u : (GaloisField hyp.base.p hyp.base.q)ˣ) := congrArg Subtype.val hval
    simpa [hμ'def] using h1
  exact this

/-- The complement transport `fU` is injective. -/
theorem fieldNormalizerComplementTransport_injective (hyp : Hypothesis (G := G))
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :
    Function.Injective (fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro a b hab
  obtain ⟨va, hva_mu, hva⟩ := fieldNormalizerComplementTransport_exists hyp μ hμ_inj hμ_range a
  obtain ⟨vb, hvb_mu, hvb⟩ := fieldNormalizerComplementTransport_exists hyp μ hμ_inj hμ_range b
  rw [hva, hvb] at hab
  have hvab : va = vb := Subtype.ext hab
  have : (a : (GaloisField hyp.base.p hyp.base.q)ˣ) = (b : (GaloisField hyp.base.p hyp.base.q)ˣ) := by
    rw [← hva_mu, ← hvb_mu, hvab]
  exact Subtype.ext this

/-- The complement transport `fU` has image exactly Peterfalvi's complement `U`. -/
theorem fieldNormalizerComplementTransport_range (hyp : Hypothesis (G := G))
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :
    (fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range).range = hyp.base.U := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    obtain ⟨v, _, hv⟩ := fieldNormalizerComplementTransport_exists hyp μ hμ_inj hμ_range u
    rw [hv]
    exact v.2
  · intro g hg
    set μ' : ↥hyp.base.U →* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
      { toFun := fun u => ⟨μ u, by rw [← hμ_range]; exact MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp } with hμ'def
    set eU : ↥hyp.base.U ≃* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
      MulEquiv.ofBijective μ'
        ⟨fun a b h => hμ_inj (congrArg Subtype.val h),
         fun u => by
           obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (by rw [hμ_range]; exact u.2)
           exact ⟨v, Subtype.ext hv⟩⟩ with heUdef
    refine ⟨eU (⟨g, hg⟩ : ↥hyp.base.U), ?_⟩
    show (hyp.base.U.subtype.comp eU.symm.toMonoidHom) (eU ⟨g, hg⟩) = g
    simp

/-- **(14.7) σ-bridge assembly.**  Given the full Peterfalvi (14.2)(a) field model
(the additive isomorphism `e`, the multiplicative character `μ` realizing `U = U*`, the
`U`-equivariance `hcompat`, the prime-line/`W₂` identification `hW2`), together with the
standing `P ∩ U = 1`, the cyclotomic coprimality, and part (14.2)(b) data, the concrete
`FieldNormalizerData` exists.  The embedding `σ` is the `SemidirectProduct.lift` of the
two transport homomorphisms `fN`, `fU`, glued by (14.2)(a).  Every hypothesis is an
*input* — the §13 character theory (`basic_structure`, `c_eq_one`) that produces them is
not invoked here, so this reduction is the ungated heart of (14.7). -/
theorem fieldNormalizerData_of_repr (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q)
    (hUP : ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
         (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.base.P)
    (hcompat : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
           e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hUP v x⟩ : ↥hyp.base.P))
             = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                 GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x))
    (hW2 : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         (((Submodule.span (ZMod hyp.base.p)
             ({(1 : GaloisField hyp.base.p hyp.base.q)} :
               Set (GaloisField hyp.base.p hyp.base.q))).toAddSubgroup).toSubgroup).map
           (fieldNormalizerKernelTransport hyp e) = hyp.base.W2)
    (hPU_disj : hyp.base.P ⊓ hyp.base.U = ⊥)
    (hcyclotomic :
       Nat.Coprime ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) (hyp.base.p - 1))
    (hQ_elemAb : IsElementaryAbelian hyp.base.q ↥hyp.base.Q)
    (hW2_norm_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G))
    (yQ : G) (hyQ_mem : yQ ∈ hyp.base.Q)
    (hW2_conj_y : MulAut.conj yQ • hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G)) :
    Nonempty (FieldNormalizerData hyp) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  -- the `SemidirectProduct.lift` compatibility: `fN (u • s) = fU u * fN s * (fU u)⁻¹`,
  -- which is exactly the (14.2)(a) `U`-equivariance `hcompat` transported through the iso.
  have hcompatLift : ∀ u : OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q,
      (fieldNormalizerKernelTransport hyp e).comp
          ((OddOrder.BG.AppC.NormSet.normOneMulAction hyp.base.p hyp.base.q u).toMonoidHom)
        = (MulAut.conj (fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range u)).toMonoidHom.comp
          (fieldNormalizerKernelTransport hyp e) := by
    intro u
    ext s
    obtain ⟨v, hμv, hfUv⟩ :=
      fieldNormalizerComplementTransport_exists hyp μ hμ_inj hμ_range u
    show fieldNormalizerKernelTransport hyp e
        ((OddOrder.BG.AppC.NormSet.normOneMulAction hyp.base.p hyp.base.q u) s) =
      fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range u *
        fieldNormalizerKernelTransport hyp e s *
        (fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range u)⁻¹
    rw [hfUv]
    -- compute the action `u • s = ofAdd (↑u * toAdd s)`
    have hact : (OddOrder.BG.AppC.NormSet.normOneMulAction hyp.base.p hyp.base.q u) s =
        Multiplicative.ofAdd (((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q) *
            (Multiplicative.toAdd s : GaloisField hyp.base.p hyp.base.q)) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      conv_lhs => rw [← ofAdd_toAdd s]
      exact OddOrder.BG.AppC.NormSet.normOneMulAction_apply hyp.base.p hyp.base.q u
        (Multiplicative.toAdd s)
    rw [hact, fieldNormalizerKernelTransport_apply, fieldNormalizerKernelTransport_apply,
      toAdd_ofAdd]
    -- both sides are coercions of `↥P` elements; reduce to the conjugate identity
    set t : GaloisField hyp.base.p hyp.base.q := Multiplicative.toAdd s with htdef
    set x : ↥hyp.base.P := Additive.toMul (e.symm t) with hxdef
    have hex : e (Additive.ofMul x) = t := by
      rw [hxdef, ofMul_toMul, e.apply_symm_apply]
    have hkey : Additive.toMul (e.symm (((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
          GaloisField hyp.base.p hyp.base.q) * t)) =
        (⟨(v : G) * (x : G) * (v : G)⁻¹, hUP v x⟩ : ↥hyp.base.P) := by
      have h1 := hcompat v x
      rw [hex] at h1
      have hμvF : ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q) =
          ((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q) := by rw [hμv]
      rw [hμvF] at h1
      have h2 : Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hUP v x⟩ : ↥hyp.base.P) =
          e.symm (((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q) * t) := by
        rw [← h1, e.symm_apply_apply]
      rw [← h2, toMul_ofMul]
    rw [hkey]
  -- the field-normalizer embedding `σ`
  set sigma := SemidirectProduct.lift (fieldNormalizerKernelTransport hyp e)
    (fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range) hcompatLift with hsigma
  -- `σ (inl a) (inr b) = fN a * fU b`
  have hlift_apply : ∀ g : fieldNormalizerFrobeniusGroup hyp,
      sigma g = fieldNormalizerKernelTransport hyp e g.left *
        fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range g.right := by
    intro g
    rw [hsigma]
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
    rw [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  -- `σ` is injective: kernel meets complement trivially (`P ∩ U = 1`)
  have hsigma_inj : Function.Injective sigma := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker, hlift_apply] at hg
    -- `fN g.left = (fU g.right)⁻¹ ∈ P ⊓ U = ⊥`
    have hPmemP : fieldNormalizerKernelTransport hyp e g.left ∈ hyp.base.P := by
      rw [← fieldNormalizerKernelTransport_range hyp e]; exact ⟨g.left, rfl⟩
    have hinv : fieldNormalizerKernelTransport hyp e g.left =
        (fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range g.right)⁻¹ :=
      mul_eq_one_iff_eq_inv.mp hg
    have hUmemU : fieldNormalizerKernelTransport hyp e g.left ∈ hyp.base.U := by
      rw [hinv]
      apply Subgroup.inv_mem
      rw [← fieldNormalizerComplementTransport_range hyp μ hμ_inj hμ_range]
      exact ⟨g.right, rfl⟩
    have hbot : fieldNormalizerKernelTransport hyp e g.left = 1 := by
      have : fieldNormalizerKernelTransport hyp e g.left ∈ hyp.base.P ⊓ hyp.base.U :=
        ⟨hPmemP, hUmemU⟩
      rw [hPU_disj] at this
      simpa using this
    have hleft : g.left = 1 := fieldNormalizerKernelTransport_injective hyp e (by
      rw [hbot, map_one])
    have hfUone : fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range g.right = 1 := by
      have hg' := hg
      rw [hbot, one_mul] at hg'
      exact hg'
    have hright : g.right = 1 :=
      fieldNormalizerComplementTransport_injective hyp μ hμ_inj hμ_range (by
        rw [hfUone, map_one])
    rw [Subgroup.mem_bot]
    exact SemidirectProduct.ext hleft hright
  -- `σ` carries the abstract kernel / complement / prime line onto `P` / `U` / `W₂`
  have hP : (fieldNormalizerKernel hyp).map sigma = hyp.base.P := by
    rw [fieldNormalizerKernel, MonoidHom.range_eq_map, Subgroup.map_map, hsigma,
      SemidirectProduct.lift_comp_inl, ← MonoidHom.range_eq_map,
      fieldNormalizerKernelTransport_range]
  have hU : (fieldNormalizerComplement hyp).map sigma = hyp.base.U := by
    rw [fieldNormalizerComplement, MonoidHom.range_eq_map, Subgroup.map_map, hsigma,
      SemidirectProduct.lift_comp_inr, ← MonoidHom.range_eq_map,
      fieldNormalizerComplementTransport_range]
  have hP0 : (fieldNormalizerPrimeLine hyp).map sigma = hyp.base.W2 := by
    rw [fieldNormalizerPrimeLine, OddOrder.BG.AppC.NormSet.normOneFrobeniusSubspaceKernel,
      Subgroup.map_map, hsigma, SemidirectProduct.lift_comp_inl]
    exact hW2
  exact ⟨{
    sigma := sigma
    sigma_injective := hsigma_inj
    sigma_P_eq_P := hP
    sigma_P0_eq_W2 := hP0
    sigma_U_eq_U := hU
    cyclotomic_coprime := hcyclotomic
    Q_elementaryAbelian := hQ_elemAb
    W2_normalizes_Q := hW2_norm_Q
    y := yQ
    y_mem_Q := hyQ_mem
    W2_conj_y_normalizes_U := hW2_conj_y }⟩

/-! ### (14.7) standing structural inputs (proved by citing the §13 Frobenius data)

These discharge the *structural* hypotheses of `fieldNormalizerData_of_repr` from the
standing Section-15 data — they cite the (sorried) §13 producers `basic_structure`/`c_eq_one`
the same way `u_modEq_one_mod_q` does, so they are proven (their own bodies are `sorry`-free).
The remaining genuine work for (14.7) is the *numeric* input `|U| = (p^q-1)/(p-1)` and the
`𝔽_p[U]`-module construction feeding `exists_galoisField_repr`. -/

/-- `U` normalizes `P`: since `P = F(S)` is normal in `S` and `U ≤ S' = PU ≤ S`. -/
theorem U_le_normalizer_P (hyp : Hypothesis (G := G)) :
    hyp.base.U ≤ Subgroup.normalizer hyp.base.P := by
  have hU_le_deriv : hyp.base.U ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU]; exact le_sup_right
  have hderiv_le_S : derivedInG hyp.base.S ≤ hyp.base.S := Subgroup.map_subtype_le _
  have hS_le_norm : hyp.base.S ≤ Subgroup.normalizer hyp.base.P := by
    rw [hyp.base.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.S
  exact (hU_le_deriv.trans hderiv_le_S).trans hS_le_norm

/-- **(14.7) `hUP` input**: conjugating a point of `P` by an element of `U` stays in `P`. -/
theorem conj_mem_P (hyp : Hypothesis (G := G)) (v : ↥hyp.base.U) (x : ↥hyp.base.P) :
    (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.base.P := by
  have hv : (v : G) ∈ Subgroup.normalizer hyp.base.P := U_le_normalizer_P hyp v.2
  exact (Subgroup.mem_normalizer_iff.mp hv (x : G)).mp x.2

/-- `V` normalizes `Q` (`T`-side dual of `U_le_normalizer_P`): `Q = F(T)` is normal in `T` and
`V ≤ T' = Q V ≤ T` (`T_deriv_eq_QV`). -/
theorem V_le_normalizer_Q (hyp : Hypothesis (G := G)) :
    hyp.base.V ≤ Subgroup.normalizer hyp.base.Q := by
  have hV_le_deriv : hyp.base.V ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right
  have hderiv_le_T : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hT_le_norm : hyp.base.T ≤ Subgroup.normalizer hyp.base.Q := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T
  exact (hV_le_deriv.trans hderiv_le_T).trans hT_le_norm

/-- `T`-side dual of `conj_mem_P`: conjugating a point of `Q` by an element of `V` stays in `Q`. -/
theorem conj_mem_Q (hyp : Hypothesis (G := G)) (v : ↥hyp.base.V) (x : ↥hyp.base.Q) :
    (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.base.Q := by
  have hv : (v : G) ∈ Subgroup.normalizer hyp.base.Q := V_le_normalizer_Q hyp v.2
  exact (Subgroup.mem_normalizer_iff.mp hv (x : G)).mp x.2

/-- **(14.7) `hPU_disj` input**: `P ∩ U = 1`.  Since `P` is elementary abelian it
centralizes itself, so `P ⊓ U ≤ U ⊓ C_G(P) = C = 1` by (13.12) `c = 1`.  Cites the
(sorried) §13 producers `basic_structure` and `c_eq_one`. -/
theorem P_inf_U_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.P ⊓ hyp.base.U = ⊥ := by
  obtain ⟨data, _⟩ := OddOrder.Peterfalvi.S15.basic_structure hG hyp.base
  haveI : IsMulCommutative ↥hyp.base.P :=
    IsMulCommutative.of_comm data.P_elementaryAbelian.comm
  have hP_le_cent : hyp.base.P ≤ Subgroup.centralizer (hyp.base.P : Set G) :=
    Subgroup.le_centralizer (H := hyp.base.P)
  have hC_bot : hyp.base.C = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [← hyp.base.c_eq_card_C, OddOrder.Peterfalvi.S15.c_eq_one hG hyp.base]
  rw [eq_bot_iff, ← hC_bot, hyp.base.C_eq]
  exact le_inf inf_le_right (inf_le_left.trans hP_le_cent)

set_option maxHeartbeats 1000000 in
open scoped IsMulCommutative in
/-- **(14.7)/(14.2)(a) field model from the §13 numeric data.**  When
`|U| = (p^q-1)/(p-1)` (the (14.7) cyclotomic value), the conjugation action of `U` on the
elementary-abelian `P` of order `p^q` makes `Additive ↥P ≅ 𝔽_{p^q}` with `U ↪ 𝔽^×`
(Singer mechanism, `exists_galoisField_repr`).  Cites the §13 producers `basic_structure`
(`|P|=p^q`, `P` elementary abelian) and `c_eq_one` (`U` faithful on `P`). -/
theorem exists_pu_field_repr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hu_full : Nat.card ↥hyp.base.U =
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ (e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
      (μ : ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ),
      Function.Injective μ ∧
      ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
        e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
            ↥hyp.base.P))
          = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  haveI : NeZero hyp.base.p := ⟨hyp.base.p_prime.ne_zero⟩
  obtain ⟨data, _⟩ := OddOrder.Peterfalvi.S15.basic_structure hG hyp.base
  haveI hPcomm : IsMulCommutative ↥hyp.base.P :=
    IsMulCommutative.of_comm data.P_elementaryAbelian.comm
  letI hUcomm : CommGroup ↥hyp.base.U :=
    { (inferInstance : Group ↥hyp.base.U) with
      mul_comm := fun a b => (isMulCommutative_iff.mp data.U_commutative) a b }
  have hpsmul : ∀ x : Additive ↥hyp.base.P, (hyp.base.p : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact data.P_elementaryAbelian.pow_eq_one x.toMul
  haveI hPmod : Module (ZMod hyp.base.p) (Additive ↥hyp.base.P) :=
    AddCommGroup.zmodModule hpsmul
  -- the conjugation representation of `U` on `Additive ↥P`
  let conjHom : ↥hyp.base.U →* MulAut ↥hyp.base.P :=
    (Subgroup.normalizerMonoidHom (H := hyp.base.P)).comp
      (Subgroup.inclusion (U_le_normalizer_P hyp))
  let ρ : Representation (ZMod hyp.base.p) ↥hyp.base.U (Additive ↥hyp.base.P) :=
    (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥hyp.base.P hyp.base.p).comp conjHom
  have hρ_apply : ∀ (c : ↥hyp.base.U) (a : Additive ↥hyp.base.P),
      ρ c a = Additive.ofMul ((conjHom c) (Additive.toMul a)) := fun _ _ => rfl
  -- `Additive ↥P` as an `𝔽_p[U]`-module *directly* (sidesteps the `asModule` synth trap)
  letI hPmodAlg :
      Module (MonoidAlgebra (ZMod hyp.base.p) ↥hyp.base.U) (Additive ↥hyp.base.P) :=
    Module.compHom (Additive ↥hyp.base.P) (ρ.asAlgebraHom).toRingHom
  have hof_smul : ∀ (c : ↥hyp.base.U) (a : Additive ↥hyp.base.P),
      MonoidAlgebra.of (ZMod hyp.base.p) ↥hyp.base.U c • a =
        Additive.ofMul ((conjHom c) (Additive.toMul a)) := by
    intro c a
    have h : MonoidAlgebra.of (ZMod hyp.base.p) ↥hyp.base.U c • a = ρ c a := by
      show (ρ.asAlgebraHom (MonoidAlgebra.of (ZMod hyp.base.p) ↥hyp.base.U c)) a = ρ c a
      rw [Representation.asAlgebraHom_of]
    rw [h, hρ_apply]
  haveI hNeZero : NeZero (Nat.card ↥hyp.base.U : ZMod hyp.base.p) := by
    refine ⟨fun h => ?_⟩
    rw [hu_full] at h
    have hdvd : hyp.base.p ∣ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
      (ZMod.natCast_eq_zero_iff _ _).mp h
    have hmod : (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) ≡ 1 [MOD hyp.base.p] := by
      have hsum_eq : ∑ k ∈ Finset.range hyp.base.q, hyp.base.p ^ k =
          (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
        Nat.geomSum_eq hyp.base.p_prime.two_le _
      rw [← hsum_eq, show hyp.base.q = (hyp.base.q - 1) + 1 by
          have := hyp.base.q_prime.pos; omega, Finset.sum_range_succ']
      have hzero : (∑ k ∈ Finset.range (hyp.base.q - 1), hyp.base.p ^ (k + 1)) ≡ 0
          [MOD hyp.base.p] := by
        rw [Nat.modEq_zero_iff_dvd]
        exact Finset.dvd_sum fun k _ => dvd_pow_self hyp.base.p (Nat.succ_ne_zero k)
      simpa using hzero.add_right 1
    have hdvd1 : hyp.base.p ∣ 1 := by
      have h0 := (Nat.modEq_zero_iff_dvd).mpr hdvd
      have h01 := h0.symm.trans hmod
      rwa [Nat.modEq_iff_dvd', Nat.sub_zero] at h01
      omega
    exact absurd (Nat.le_of_dvd one_pos hdvd1) (by have := hyp.base.p_prime.two_le; omega)
  have hcardM : Nat.card (Additive ↥hyp.base.P) = hyp.base.p ^ hyp.base.q := data.P_order
  have hfaith : ∀ c : ↥hyp.base.U,
      (∀ x : Additive ↥hyp.base.P,
          MonoidAlgebra.of (ZMod hyp.base.p) ↥hyp.base.U c • x = x) → c = 1 := by
    intro c hc
    have hcomm : ∀ y : ↥hyp.base.P, (c : G) * (y : G) = (y : G) * (c : G) := by
      intro y
      have h1 := hc (Additive.ofMul y)
      rw [hof_smul] at h1
      have h2 : (conjHom c) y = y := Additive.ofMul.injective (by simpa using h1)
      have h3 : (c : G) * (y : G) * (c : G)⁻¹ = (y : G) := congrArg Subtype.val h2
      rwa [mul_inv_eq_iff_eq_mul] at h3
    have hmem : (c : G) ∈ hyp.base.C := by
      rw [hyp.base.C_eq]
      exact ⟨c.2, Subgroup.mem_centralizer_iff.mpr (fun y hy => (hcomm ⟨y, hy⟩).symm)⟩
    have hCbot : hyp.base.C = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      rw [← hyp.base.c_eq_card_C, OddOrder.Peterfalvi.S15.c_eq_one hG hyp.base]
    rw [hCbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨e0, μ, hμinj, hcompat0⟩ :=
    OddOrder.RepresentationTheory.exists_galoisField_repr
      (C := ↥hyp.base.U) (M := Additive ↥hyp.base.P)
      hyp.base.q_prime hyp.base.q_odd hcardM hu_full hfaith
  refine ⟨e0, μ, hμinj, ?_⟩
  intro v x
  rw [← hcompat0 v (Additive.ofMul x), hof_smul v (Additive.ofMul x)]
  congr 2

/-- **(14.7) `hμ_range` input**: any injective `μ : U →* 𝔽_{p^q}ˣ` with `|U| = (p^q-1)/(p-1)`
has image exactly the norm-one units `U*`.  Both are subgroups of the cyclic group `𝔽_{p^q}ˣ`
of the same order `d = (p^q-1)/(p-1)`, hence both equal the unique subgroup `{x | x^d = 1}` of
that order (`= ker (powMonoidHom d)`, whose card is `gcd(p^q-1, d) = d`). -/
theorem mu_range_eq_normOneUnits {hyp : Hypothesis (G := G)}
    (hu_full : Nat.card ↥hyp.base.U =
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hinj : Function.Injective μ) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  set d := (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) with hd
  have hq0 : hyp.base.q ≠ 0 := hyp.base.q_prime.ne_zero
  have hGcard : Nat.card (GaloisField hyp.base.p hyp.base.q)ˣ = hyp.base.p ^ hyp.base.q - 1 := by
    rw [Nat.card_units, GaloisField.card hyp.base.p hyp.base.q hq0]
  have hpm1_dvd : (hyp.base.p - 1) ∣ (hyp.base.p ^ hyp.base.q - 1) := by
    have h1 : (1 : ℕ) ≡ hyp.base.p [MOD (hyp.base.p - 1)] :=
      (Nat.modEq_iff_dvd' (by have := hyp.base.p_prime.two_le; omega)).mpr dvd_rfl
    have hq1 : (1 : ℕ) ≡ hyp.base.p ^ hyp.base.q [MOD (hyp.base.p - 1)] := by
      simpa using h1.pow hyp.base.q
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by have := hyp.base.p_prime.two_le; omega))).mp hq1
  have hd_dvd : d ∣ (hyp.base.p ^ hyp.base.q - 1) :=
    ⟨hyp.base.p - 1, (Nat.div_mul_cancel hpm1_dvd).symm⟩
  have hkercard : Nat.card
      (powMonoidHom d :
        (GaloisField hyp.base.p hyp.base.q)ˣ →* (GaloisField hyp.base.p hyp.base.q)ˣ).ker = d := by
    rw [IsCyclic.card_powMonoidHom_ker, hGcard, Nat.gcd_eq_right hd_dvd]
  have hμcard : Nat.card (μ.range) = d := by
    have hcU := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [hu_full] at hcU
    exact hcU
  have hncard :
      Nat.card (OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) = d :=
    OddOrder.BG.AppC.NormSet.normOneUnits_card hyp.base.p hyp.base.q hq0
  have hsub : ∀ (K : Subgroup (GaloisField hyp.base.p hyp.base.q)ˣ), Nat.card K = d →
      K ≤ (powMonoidHom d :
        (GaloisField hyp.base.p hyp.base.q)ˣ →* (GaloisField hyp.base.p hyp.base.q)ˣ).ker := by
    intro K hK x hx
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    have hord : orderOf x ∣ d := by
      have h := orderOf_dvd_natCard (⟨x, hx⟩ : K)
      rw [hK] at h
      rwa [← orderOf_injective K.subtype (Subgroup.subtype_injective K) ⟨x, hx⟩] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hord
  have hμeq : μ.range =
      (powMonoidHom d :
        (GaloisField hyp.base.p hyp.base.q)ˣ →* (GaloisField hyp.base.p hyp.base.q)ˣ).ker :=
    Subgroup.eq_of_le_of_card_ge (hsub _ hμcard) (le_of_eq (hkercard.trans hμcard.symm))
  have hneq : OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q =
      (powMonoidHom d :
        (GaloisField hyp.base.p hyp.base.q)ˣ →* (GaloisField hyp.base.p hyp.base.q)ˣ).ker :=
    Subgroup.eq_of_le_of_card_ge (hsub _ hncard) (le_of_eq (hkercard.trans hncard.symm))
  rw [hμeq, hneq]

/-- **(14.7) prime-line rescaling.**  The field model `e₀` produced by `exists_pu_field_repr`
is canonical only up to a nonzero field scalar — nothing in the Singer construction pins down
where it sends the prime line `W₂`.  Given `W₂ ≤ P` (a §13-structural fact), rescale
`e₀ ↦ c⁻¹ • e₀` by `c := e₀(w₀)` for a nonidentity `w₀ ∈ W₂`.  The rescaled `e` then sends
`w₀ ↦ 1`, hence carries the prime line `⟨1⟩ = (span 𝔽_p {1})` of `𝔽_{p^q}` exactly onto `W₂`
(both are cyclic of prime order `p`).  The `U`-equivariance `hcompat` survives because the
field is commutative (`c⁻¹·(μv·y) = μv·(c⁻¹·y)`).  This produces the `hW2` input of
`fieldNormalizerData_of_repr`; it is pure field algebra, *independent* of the §13 character
theory that produces `e₀` — `W₂ ≤ P` is its only structural input. -/
theorem field_repr_rescale_to_W2 (hyp : Hypothesis (G := G))
    (hW2_le_P : hyp.base.W2 ≤ hyp.base.P)
    (e₀ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hcompat₀ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
           e₀ (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
               ↥hyp.base.P))
             = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                 GaloisField hyp.base.p hyp.base.q) * e₀ (Additive.ofMul x)) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q,
      (∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
          e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
              ↥hyp.base.P))
            = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x)) ∧
      (((Submodule.span (ZMod hyp.base.p)
            ({(1 : GaloisField hyp.base.p hyp.base.q)} :
              Set (GaloisField hyp.base.p hyp.base.q))).toAddSubgroup).toSubgroup).map
          (fieldNormalizerKernelTransport hyp e) = hyp.base.W2 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  haveI : NeZero hyp.base.p := ⟨hyp.base.p_prime.ne_zero⟩
  -- `ZMod p`-linearity reduces to `nsmul` (any module over `ZMod p`)
  have hsmul_red : ∀ (r : ZMod hyp.base.p) (x : GaloisField hyp.base.p hyp.base.q),
      r • x = r.val • x := by
    intro r x
    rw [← Nat.cast_smul_eq_nsmul (ZMod hyp.base.p) r.val x, ZMod.natCast_rightInverse r]
  -- a nonidentity element of the prime line `W₂ ≤ P`
  haveI hW2fin : Finite ↥hyp.base.W2 := Nat.finite_of_card_ne_zero (by
    rw [← hyp.base.p_eq_card_W2]; exact hyp.base.p_prime.ne_zero)
  haveI : Nontrivial ↥hyp.base.W2 := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [← hyp.base.p_eq_card_W2]; exact hyp.base.p_prime.one_lt)
  obtain ⟨w0', hw0'_ne⟩ := exists_ne (1 : ↥hyp.base.W2)
  have hw0G_ne : (w0' : G) ≠ 1 := fun h => hw0'_ne (OneMemClass.coe_eq_one.mp h)
  set w0 : ↥hyp.base.P := ⟨(w0' : G), hW2_le_P w0'.2⟩ with hw0def
  have hw0_ne : w0 ≠ 1 := by
    rw [hw0def, ne_eq, Subtype.ext_iff]; simpa using hw0G_ne
  -- the rescaling scalar `c = e₀ w₀ ≠ 0`
  set c : GaloisField hyp.base.p hyp.base.q := e₀ (Additive.ofMul w0) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, ne_eq, map_eq_zero_iff _ e₀.injective]
    rw [show (0 : Additive ↥hyp.base.P) = Additive.ofMul (1 : ↥hyp.base.P) from rfl,
      EmbeddingLike.apply_eq_iff_eq]
    exact hw0_ne
  -- multiplication by `c⁻¹` is an additive automorphism of the field
  let scale : GaloisField hyp.base.p hyp.base.q ≃+ GaloisField hyp.base.p hyp.base.q :=
    { toFun := fun x => c⁻¹ * x
      invFun := fun x => c * x
      left_inv := fun x => mul_inv_cancel_left₀ hc x
      right_inv := fun x => inv_mul_cancel_left₀ hc x
      map_add' := fun x y => mul_add c⁻¹ x y }
  set e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q := e₀.trans scale with hedef
  have he_apply : ∀ a, e a = c⁻¹ * e₀ a := fun a => rfl
  have he_w0 : e (Additive.ofMul w0) = 1 := by
    rw [he_apply, ← hcdef, inv_mul_cancel₀ hc]
  refine ⟨e, ?_, ?_⟩
  · -- `hcompat` survives rescaling by commutativity
    intro v x
    simp only [he_apply]
    rw [hcompat₀ v x]; ring
  · -- the prime line `span{1}` maps onto `W₂`
    have hSpan : (((Submodule.span (ZMod hyp.base.p)
          ({(1 : GaloisField hyp.base.p hyp.base.q)} :
            Set (GaloisField hyp.base.p hyp.base.q))).toAddSubgroup).toSubgroup)
        = Subgroup.zpowers
            (Multiplicative.ofAdd (1 : GaloisField hyp.base.p hyp.base.q)) := by
      apply le_antisymm
      · intro g hg
        rw [Multiplicative.mem_toSubgroup, Submodule.mem_toAddSubgroup,
          Submodule.mem_span_singleton] at hg
        obtain ⟨r, hr⟩ := hg
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨(r.val : ℤ), ?_⟩
        rw [zpow_natCast, ← ofAdd_nsmul, ← hsmul_red r, hr, ofAdd_toAdd]
      · rw [Subgroup.zpowers_le, Multiplicative.mem_toSubgroup, Submodule.mem_toAddSubgroup]
        exact Submodule.subset_span (by simp)
    rw [hSpan, MonoidHom.map_zpowers]
    have hfN1 : fieldNormalizerKernelTransport hyp e
        (Multiplicative.ofAdd (1 : GaloisField hyp.base.p hyp.base.q)) = (w0' : G) := by
      rw [fieldNormalizerKernelTransport_apply]
      have hsymm : e.symm (1 : GaloisField hyp.base.p hyp.base.q) = Additive.ofMul w0 := by
        rw [← he_w0, e.symm_apply_apply]
      simp [hsymm, hw0def]
    rw [hfN1]
    -- `zpowers (w0' : G) = W₂` since `w0'` has prime order `p`
    have horder : orderOf ((w0' : G)) = hyp.base.p := by
      have hne1 : orderOf ((w0' : G)) ≠ 1 := fun h => hw0G_ne (orderOf_eq_one_iff.mp h)
      have hdvd : orderOf ((w0' : G)) ∣ hyp.base.p := by
        have heq : orderOf ((w0' : G)) = orderOf w0' :=
          orderOf_injective hyp.base.W2.subtype (Subgroup.subtype_injective _) w0'
        rw [heq, hyp.base.p_eq_card_W2]
        exact orderOf_dvd_natCard w0'
      rcases (hyp.base.p_prime.eq_one_or_self_of_dvd _ hdvd) with h | h
      · exact absurd h hne1
      · exact h
    have hle : Subgroup.zpowers ((w0' : G)) ≤ hyp.base.W2 := by
      rw [Subgroup.zpowers_le]; exact w0'.2
    have hcard : Nat.card hyp.base.W2 ≤ Nat.card (Subgroup.zpowers ((w0' : G))) := by
      rw [Nat.card_zpowers, horder, ← hyp.base.p_eq_card_W2]
    exact Subgroup.eq_of_le_of_card_ge hle hcard

/-- **(14.7)/(14.2)(a) field model carrying the prime line to `W₂`.**  Chains the Singer
field model `exists_pu_field_repr` with the prime-line rescaling `field_repr_rescale_to_W2`,
producing the full `(e, μ)` package that `fieldNormalizerData_of_repr` consumes: an additive
isomorphism `e : Additive ↥P ≃+ 𝔽_{p^q}`, an injective character `μ : U →* 𝔽_{p^q}ˣ`, the
`U`-equivariance `hcompat`, and the prime-line/`W₂` identification `hW2`.  Cites the §13
producers `basic_structure` (`|P| = p^q`) and `c_eq_one` (`U` faithful) through
`exists_pu_field_repr`; its extra structural input is `W₂ ≤ P`. -/
theorem exists_pu_field_repr_W2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hu_full : Nat.card ↥hyp.base.U =
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hW2_le_P : hyp.base.W2 ≤ hyp.base.P) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ (e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
      (μ : ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ),
      Function.Injective μ ∧
      (∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
          e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
              ↥hyp.base.P))
            = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x)) ∧
      (((Submodule.span (ZMod hyp.base.p)
            ({(1 : GaloisField hyp.base.p hyp.base.q)} :
              Set (GaloisField hyp.base.p hyp.base.q))).toAddSubgroup).toSubgroup).map
          (fieldNormalizerKernelTransport hyp e) = hyp.base.W2 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  obtain ⟨e₀, μ, hμinj, hcompat₀⟩ := exists_pu_field_repr hG hyp hu_full
  obtain ⟨e, hcompat, hW2⟩ := field_repr_rescale_to_W2 hyp hW2_le_P e₀ μ hcompat₀
  exact ⟨e, μ, hμinj, hcompat, hW2⟩

/-- **(14.7) assembly engine.**  Given the §13/§14-gated structural facts as explicit
hypotheses — the cyclotomic value `|U| = (p^q-1)/(p-1)` (14.7), `U` cyclic (13), `W₂ ≤ P`
(13), the coprimality `gcd((p^q-1)/(p-1), p-1) = 1` (14.7), and part (14.2)(b)
(`Q` elementary abelian, `W₂ ≤ N_G(Q)`, and a `y ∈ Q` with `W₂^y ≤ N_G(U)`) — the concrete
`FieldNormalizerData` exists.  Every step is one of the proven (14.7) producers:
`exists_pu_field_repr_W2` (field model + prime line → `W₂`), `mu_range_eq_normOneUnits`
(`μ` onto `U*`), `conj_mem_P`/`P_inf_U_eq_bot` (the kernel/complement intersection), assembled
by the σ-bridge `fieldNormalizerData_of_repr`.  This engine carries no `sorry`; it is gated only
through the §13 producers `basic_structure`/`c_eq_one` cited inside `exists_pu_field_repr_W2`
and `P_inf_U_eq_bot` (Lane B), so it becomes unconditional exactly when those land. -/
theorem field_normalizer_of_U_characteristic_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hu_full : Nat.card ↥hyp.base.U =
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hW2_le_P : hyp.base.W2 ≤ hyp.base.P)
    (hcyc : Nat.Coprime
      ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) (hyp.base.p - 1))
    (hQ_elemAb : IsElementaryAbelian hyp.base.q ↥hyp.base.Q)
    (hW2_norm_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G))
    (yQ : G) (hyQ_mem : yQ ∈ hyp.base.Q)
    (hW2_conj_y : MulAut.conj yQ • hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G)) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨e, μ, hμinj, hcompat, hW2⟩ := exists_pu_field_repr_W2 hG hyp hu_full hW2_le_P
  exact fieldNormalizerData_of_repr hyp e μ hμinj
    (mu_range_eq_normOneUnits hu_full μ hμinj) (conj_mem_P hyp) hcompat hW2
    (P_inf_U_eq_bot hG hyp) hcyc hQ_elemAb hW2_norm_Q yQ hyQ_mem hW2_conj_y

/-! **Peterfalvi (14.7)** (`field_normalizer_of_U_characteristic`) is assembled **after** the
(14.5)/(13.17) fixed-point-free bridge `u_modEq_one_mod_p_of_LHypothesis` below: it consumes that
bridge (for `u ≡ 1 mod p`), the value-argument engine `field_normalizer_of_U_characteristic_of_fpf`,
and the part-(14.2.b) normalizer lemma `W2conj_le_normalizer_U_of_LHypothesis`.  See it just before
`field_normalizer_of_L_conj_M`. -/

/-! ## (14.8)--(14.9): the key inequality and `T` is type II -/

/-- A small explicit upper bound for `e`, used to keep Peterfalvi (14.8.a)
inside elementary arithmetic/log estimates. -/
private theorem real_exp_one_le_three : Real.exp 1 ≤ 3 := by
  have h :=
    Complex.exp_bound_sq (0 : ℂ) ((1 : ℝ) : ℂ) (by norm_num : ‖((1 : ℝ) : ℂ)‖ ≤ 1)
  rw [Complex.exp_zero] at h
  norm_num at h
  change ‖Complex.exp (((1 : ℝ) : ℂ)) - 1 - 1‖ ≤ (1 : ℝ) at h
  have hsq : ‖Complex.exp (((1 : ℝ) : ℂ)) - 1 - 1‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hsq
  simp [Complex.exp_re, Complex.exp_im] at hsq
  have hupper : Real.exp 1 - 2 ≤ 1 := by nlinarith
  linarith

/-- Taylor's quadratic upper bound for `exp` on `[0,1]`, in the weak form
needed for Peterfalvi (14.8.a). -/
private theorem real_exp_le_quadratic {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have hxnorm : ‖((x : ℝ) : ℂ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have h := Complex.exp_bound_sq (0 : ℂ) ((x : ℝ) : ℂ) hxnorm
  rw [Complex.exp_zero] at h
  have hnorm : ‖Complex.exp (((x : ℝ) : ℂ)) - 1 - ((x : ℝ) : ℂ)‖ ≤ x ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h0, pow_two] using h
  have hre := Complex.re_le_norm (Complex.exp (((x : ℝ) : ℂ)) - 1 - ((x : ℝ) : ℂ))
  have hre_eq :
      (Complex.exp (((x : ℝ) : ℂ)) - 1 - ((x : ℝ) : ℂ)).re = Real.exp x - 1 - x := by
    simp [Complex.exp_re]
  have hdiff : Real.exp x - 1 - x ≤ x ^ 2 := by
    rw [← hre_eq]
    exact hre.trans hnorm
  linarith

private theorem one_add_inv_le_log_of_five_le {q : ℕ} (hq : 5 ≤ q) :
    1 + (1 / (q : ℝ)) ≤ Real.log q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hq)
  rw [Real.le_log_iff_exp_le hqpos]
  have hqge : (5 : ℝ) ≤ q := by exact_mod_cast hq
  calc
    Real.exp (1 + 1 / (q : ℝ)) = Real.exp 1 * Real.exp (1 / (q : ℝ)) := by
      rw [Real.exp_add]
    _ ≤ 3 * (1 + 1 / (q : ℝ) + (1 / (q : ℝ)) ^ 2) := by
      have hsmall : Real.exp (1 / (q : ℝ)) ≤
          1 + 1 / (q : ℝ) + (1 / (q : ℝ)) ^ 2 :=
        real_exp_le_quadratic (by positivity) (by
          field_simp [hqpos.ne']
          exact_mod_cast (le_trans (by norm_num : 1 ≤ 5) hq))
      exact mul_le_mul real_exp_one_le_three hsmall (Real.exp_nonneg _) (by norm_num)
    _ ≤ q := by
      have hs : 0 ≤ (q : ℝ) ^ 2 := sq_nonneg _
      have hcube : 5 * (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by nlinarith [hqge, hs]
      have hquad : 3 * ((q : ℝ) * ((q : ℝ) + 1) + 1) ≤ 5 * (q : ℝ) ^ 2 := by
        nlinarith [hqge, hs]
      field_simp [hqpos.ne']
      nlinarith [hcube, hquad]

private theorem log_div_succ_lt_of_five_le {p q : ℕ} (hq : 5 ≤ q) (hqp : q < p) :
    Real.log (p : ℝ) / ((p : ℝ) + 1) < Real.log (q : ℝ) / ((q : ℝ) + 1) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hq)
  have hppos : (0 : ℝ) < p := hqpos.trans (by exact_mod_cast hqp)
  have hdenp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hdenq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  rw [div_lt_div_iff₀ hdenp hdenq]
  have hratio_pos : (0 : ℝ) < (p : ℝ) / (q : ℝ) := div_pos hppos hqpos
  have hratio_ne : (p : ℝ) / (q : ℝ) ≠ 1 := by
    intro h
    field_simp [hqpos.ne'] at h
    have hpq : p = q := by exact_mod_cast h
    omega
  have hlog_ratio := Real.log_lt_sub_one_of_pos hratio_pos hratio_ne
  have hlog_div := Real.log_div hppos.ne' hqpos.ne'
  have hlogp_bound : Real.log (p : ℝ) < Real.log (q : ℝ) + ((p : ℝ) / (q : ℝ) - 1) := by
    nlinarith [hlog_ratio, hlog_div]
  have hmul := mul_lt_mul_of_pos_right hlogp_bound hdenq
  have hlogq_lower : ((q : ℝ) + 1) / (q : ℝ) ≤ Real.log (q : ℝ) := by
    have h := one_add_inv_le_log_of_five_le hq
    field_simp [hqpos.ne'] at h ⊢
    exact h
  have hupper :
      (Real.log (q : ℝ) + ((p : ℝ) / (q : ℝ) - 1)) * ((q : ℝ) + 1) ≤
        Real.log (q : ℝ) * ((p : ℝ) + 1) := by
    have hpq_nonneg : 0 ≤ (p : ℝ) - (q : ℝ) := by
      have hpqle : (q : ℝ) ≤ p := by exact_mod_cast (le_of_lt hqp)
      linarith
    have hlogq_lower' : (q : ℝ) + 1 ≤ Real.log (q : ℝ) * (q : ℝ) := by
      rwa [div_le_iff₀ hqpos] at hlogq_lower
    have hmul_nonneg :
        ((p : ℝ) - (q : ℝ)) * ((q : ℝ) + 1) ≤
          ((p : ℝ) - (q : ℝ)) * (Real.log (q : ℝ) * (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogq_lower' hpq_nonneg
    field_simp [hqpos.ne']
    nlinarith [hmul_nonneg]
  exact hmul.trans_le hupper

private theorem q_pow_gt_p_pow_of_five_le {p q : ℕ} (hq : 5 ≤ q) (hqp : q < p) :
    p ^ (q + 1) < q ^ (p + 1) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hq)
  have hppos : (0 : ℝ) < p := hqpos.trans (by exact_mod_cast hqp)
  have hdenp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hdenq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hfrac := log_div_succ_lt_of_five_le (p := p) (q := q) hq hqp
  rw [div_lt_div_iff₀ hdenp hdenq] at hfrac
  have hlogpow : Real.log (((p : ℝ) ^ (q + 1))) < Real.log (((q : ℝ) ^ (p + 1))) := by
    rw [Real.log_pow, Real.log_pow]
    norm_num
    nlinarith [hfrac]
  have hreal : ((p : ℝ) ^ (q + 1)) < ((q : ℝ) ^ (p + 1)) :=
    (Real.log_lt_log_iff (pow_pos hppos _) (pow_pos hqpos _)).mp hlogpow
  exact_mod_cast hreal

private theorem fourth_lt_three_pow_succ {p : ℕ} (hp : 5 ≤ p) :
    p ^ 4 < 3 ^ (p + 1) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hstep : (p + 1) ^ 4 < 3 * p ^ 4 := by
        have hpz : (5 : ℤ) ≤ p := by exact_mod_cast hp
        have hz : ((p + 1 : ℤ) ^ 4 < 3 * (p : ℤ) ^ 4) := by
          nlinarith [hpz, sq_nonneg ((p : ℤ) - 5), sq_nonneg ((p : ℤ) - 4),
            sq_nonneg ((p : ℤ) - 3), sq_nonneg ((p : ℤ) - 2),
            sq_nonneg ((p : ℤ) - 1), sq_nonneg (p : ℤ)]
        exact_mod_cast hz
      calc
        (p + 1) ^ 4 < 3 * p ^ 4 := hstep
        _ < 3 * 3 ^ (p + 1) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 3 ^ (p + 2) := by
          rw [show p + 2 = p + 1 + 1 by omega, pow_succ]
          ring

private theorem q_pow_gt_p_pow_of_q_eq_three {p q : ℕ} (hq : q = 3) (hp : 5 ≤ p) :
    p ^ (q + 1) < q ^ (p + 1) := by
  subst q
  simpa using fourth_lt_three_pow_succ hp

/-- **Peterfalvi (14.8.a)**: for odd prime parameters with `q < p`,
`q^(p+1)` strictly dominates `p^(q+1)`. -/
theorem q_pow_gt_p_pow {p q : ℕ} (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q)
    (hqp : q < p) :
    q ^ (p + 1) > p ^ (q + 1) := by
  by_cases hq3 : q = 3
  · have hp5 : 5 ≤ p := by
      have hp4 : p ≠ 4 := by
        intro hp4
        subst p
        rcases hpodd with ⟨k, hk⟩
        omega
      omega
    exact q_pow_gt_p_pow_of_q_eq_three hq3 hp5
  · have hq_ne_two : q ≠ 2 := by
      intro hq2
      subst q
      rcases hqodd with ⟨k, hk⟩
      omega
    have hq_three : 3 ≤ q := by
      have htwo : 2 ≤ q := hq.two_le
      omega
    have hq_ne_four : q ≠ 4 := by
      intro hq4
      subst q
      rcases hqodd with ⟨k, hk⟩
      omega
    have hq5 : 5 ≤ q := by omega
    exact q_pow_gt_p_pow_of_five_le hq5 hqp

namespace Hypothesis

/-- The arithmetic part of **Peterfalvi (14.8)** under the Section 16
hypothesis bundle. -/
theorem q_pow_gt_p_pow (hyp : Hypothesis (G := G)) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) :=
  OddOrder.Peterfalvi.S16.q_pow_gt_p_pow hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p

end Hypothesis

private theorem cyclotomic_quotient_sub_one_ge_pow_pred {q p : ℕ}
    (hq2 : 2 ≤ q) (hp2 : 2 ≤ p) :
    ((q ^ (p - 1) : ℕ) : ℚ) ≤ (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) := by
  have hsum_eq : ∑ k ∈ Finset.range p, q ^ k = (q ^ p - 1) / (q - 1) :=
    Nat.geomSum_eq hq2 p
  have hle_rest : q ^ (p - 1) ≤ ∑ k ∈ Finset.range (p - 1), q ^ (k + 1) := by
    have hlast_mem : p - 2 ∈ Finset.range (p - 1) := by
      simp
      omega
    have hnonneg : ∀ k ∈ Finset.range (p - 1), 0 ≤ q ^ (k + 1) := by
      intro k _hk
      exact Nat.zero_le _
    have hsingle := Finset.single_le_sum hnonneg hlast_mem
    simpa [show p - 2 + 1 = p - 1 by omega] using hsingle
  have hsum_succ : ∑ k ∈ Finset.range p, q ^ k =
      (∑ k ∈ Finset.range (p - 1), q ^ (k + 1)) + 1 := by
    rw [show p = (p - 1) + 1 by omega]
    rw [Finset.sum_range_succ']
    simp
  have hle_sum : q ^ (p - 1) + 1 ≤ ∑ k ∈ Finset.range p, q ^ k := by
    rw [hsum_succ]
    omega
  have hnat : q ^ (p - 1) ≤ (q ^ p - 1) / (q - 1) - 1 := by
    rw [← hsum_eq]
    omega
  exact_mod_cast hnat

private theorem cyclotomic_quotient_modEq_one_mod_base {p q : ℕ}
    (hp2 : 2 ≤ p) (hqpos : 0 < q) :
    (p ^ q - 1) / (p - 1) ≡ 1 [MOD p] := by
  have hsum_eq : ∑ k ∈ Finset.range q, p ^ k = (p ^ q - 1) / (p - 1) :=
    Nat.geomSum_eq hp2 q
  rw [← hsum_eq]
  rw [show q = (q - 1) + 1 by omega]
  rw [Finset.sum_range_succ']
  have hzero : (∑ k ∈ Finset.range (q - 1), p ^ (k + 1)) ≡ 0 [MOD p] := by
    rw [Nat.modEq_zero_iff_dvd]
    refine Finset.dvd_sum fun k _hk => ?_
    exact dvd_pow_self p (Nat.succ_ne_zero k)
  simpa using hzero.add_right 1

/-- **Peterfalvi (14.7) value argument** (arithmetic core).  In case (9.7.b), the
`p ≡ 1 mod q` branch of (13.15) is incompatible with `u ≡ 1 mod p` — the congruence the
fixed-point-free action of `W₂^y` on `U` supplies in (14.7).  In that branch
`q · u = (p^q-1)/(p-1) ≡ 1 mod p` (geometric sum), so `q ≡ q·u ≡ 1 mod p` (using
`u ≡ 1 mod p`), forcing `p ∣ q - 1` against `q < p`.  Hence `u` takes its full cyclotomic
value and `q ∤ (p-1)` (i.e. `¬ p ≡ 1 mod q`).  Reduces the (14.7) value argument to the single
fixed-point-free congruence `u ≡ 1 mod p`; cites the (sorried) case-(b) data `CaseBForSData`. -/
theorem u_eq_full_of_caseB_of_u_modEq_one_mod_p {hyp : Hypothesis (G := G)}
    (Sdata : CaseBForSData hyp) (hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p]) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) ∧
      ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] := by
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · exfalso
    have hqdvd : hyp.base.q ∣ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
      OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one hyp.base.p_prime hmod
    have hu_div : hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) / hyp.base.q := by
      rw [Sdata.u_eq_of_p_modEq_one hmod, Nat.div_div_eq_div_mul,
        Nat.mul_comm (hyp.base.p - 1) hyp.base.q]
    have hqu : hyp.base.q * hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
      rw [hu_div, Nat.mul_div_cancel' hqdvd]
    have hC_mod : (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) ≡ 1 [MOD hyp.base.p] :=
      cyclotomic_quotient_modEq_one_mod_base hyp.base.p_prime.two_le hyp.base.q_prime.pos
    have hqu_mod : hyp.base.q * hyp.base.u ≡ 1 [MOD hyp.base.p] := by rw [hqu]; exact hC_mod
    have hqu_mod2 : hyp.base.q * hyp.base.u ≡ hyp.base.q * 1 [MOD hyp.base.p] :=
      Nat.ModEq.mul_left hyp.base.q hu_mod_p
    have hq_mod : hyp.base.q ≡ 1 [MOD hyp.base.p] := by
      have h := hqu_mod2.symm.trans hqu_mod
      simpa using h
    have hp_dvd : hyp.base.p ∣ hyp.base.q - 1 :=
      (Nat.modEq_iff_dvd' hyp.base.q_prime.one_lt.le).mp hq_mod.symm
    have hqpos : 0 < hyp.base.q - 1 := by have := hyp.base.three_le_q; omega
    have hple : hyp.base.p ≤ hyp.base.q - 1 := Nat.le_of_dvd hqpos hp_dvd
    have hqp : hyp.base.q < hyp.base.p := hyp.q_lt_p
    omega
  · exact ⟨Sdata.u_eq_of_not_modEq_one hmod, hmod⟩

/-- **(14.7) assembly from the fixed-point-free congruence.**  The tightest reduction of (14.7):
given the (14.7) fixed-point-free congruence `u ≡ 1 mod p` (the `W₂^y`-on-`U` input), `U` cyclic,
`W₂ ≤ P`, and part (14.2)(b), the field-normalizer data exists.  The value argument
`u_eq_full_of_caseB_of_u_modEq_one_mod_p` turns `u ≡ 1 mod p` into `u = (p^q-1)/(p-1)` and
`q ∤ (p-1)` (using the case-(b) certificate `caseB_for_S Ldata`), which then feed
`field_normalizer_of_U_characteristic_of_inputs`.  Carries no `sorry`; gated only through the §13
producers (`basic_structure`/`c_eq_one`, via the assembly) and `caseB_for_S` (Lane B). -/
theorem field_normalizer_of_U_characteristic_of_fpf [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp)
    (hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p])
    (hW2_le_P : hyp.base.W2 ≤ hyp.base.P)
    (hQ_elemAb : IsElementaryAbelian hyp.base.q ↥hyp.base.Q)
    (hW2_norm_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G))
    (yQ : G) (hyQ_mem : yQ ∈ hyp.base.Q)
    (hW2_conj_y : MulAut.conj yQ • hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G)) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨Sdata, _⟩ := caseB_for_S hG hyp Ldata
  obtain ⟨hu_full, hnot_mod⟩ := u_eq_full_of_caseB_of_u_modEq_one_mod_p Sdata hu_mod_p
  -- bridge `|U| = u` via (13.12) `c = 1`
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, OddOrder.Peterfalvi.S15.c_eq_one hG hyp.base, mul_one]
  have hcyc : Nat.Coprime
      ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) (hyp.base.p - 1) :=
    OddOrder.Peterfalvi.S15.cyclotomic_quotient_coprime_of_not_modEq_one
      hyp.base.p_prime hyp.base.q_prime hnot_mod
  exact field_normalizer_of_U_characteristic_of_inputs hG hyp (hU_card.trans hu_full)
    hW2_le_P hcyc hQ_elemAb hW2_norm_Q yQ hyQ_mem hW2_conj_y

private theorem cyclotomic_quotient_sub_one_lt_div {p q : ℕ} (hp2 : 2 ≤ p) :
    (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) <
      (p ^ q : ℚ) / (((p - 1 : ℕ) : ℚ)) := by
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num : 0 < 2) hp2
  have hp1_pos_nat : 0 < p - 1 := by omega
  have hden_pos : (0 : ℚ) < (((p - 1 : ℕ) : ℚ)) := by exact_mod_cast hp1_pos_nat
  have hdiv : p - 1 ∣ p ^ q - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow p 1 q
  have hcast_div : (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) =
      ((p ^ q - 1 : ℕ) : ℚ) / (((p - 1 : ℕ) : ℚ)) := by
    exact Nat.cast_div hdiv (ne_of_gt hden_pos)
  have hsub_le : (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) ≤
      (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le ((p ^ q - 1) / (p - 1)) 1
  have hnum_nat : p ^ q - 1 < p ^ q := by
    have hpq_pos : 0 < p ^ q := pow_pos hp_pos q
    omega
  have hnum : ((p ^ q - 1 : ℕ) : ℚ) < (p ^ q : ℚ) := by exact_mod_cast hnum_nat
  have hquot_lt : (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) <
      (p ^ q : ℚ) / (((p - 1 : ℕ) : ℚ)) := by
    rw [hcast_div]
    exact div_lt_div_of_pos_right hnum hden_pos
  exact lt_of_le_of_lt hsub_le hquot_lt

private theorem mul_pred_lt_three_pow_pred {p : ℕ} (hp : 5 ≤ p) :
    p * (p - 1) < 3 ^ (p - 1) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hstep : (p + 1) * p < 3 * (p * (p - 1)) := by
        have hfactor : p + 1 < 3 * (p - 1) := by omega
        have hmul := Nat.mul_lt_mul_of_pos_right hfactor (by omega : 0 < p)
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      calc
        (p + 1) * ((p + 1) - 1) = (p + 1) * p := by rw [Nat.add_sub_cancel_right]
        _ < 3 * (p * (p - 1)) := hstep
        _ < 3 * 3 ^ (p - 1) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 3 ^ p := by
          calc
            3 * 3 ^ (p - 1) = 3 ^ (p - 1) * 3 := by rw [mul_comm]
            _ = 3 ^ ((p - 1) + 1) := by rw [pow_succ]
            _ = 3 ^ p := by rw [show (p - 1) + 1 = p by omega]

private theorem p_mul_q_lt_q_pow_pred_of_five_le {p q : ℕ}
    (hp5 : 5 ≤ p) (hq3 : 3 ≤ q) (hqp : q < p) :
    p * q < q ^ (p - 1) := by
  have hq_le_pred : q ≤ p - 1 := by omega
  have hpq_le : p * q ≤ p * (p - 1) := Nat.mul_le_mul_left p hq_le_pred
  have hpq_lt_three : p * q < 3 ^ (p - 1) :=
    lt_of_le_of_lt hpq_le (mul_pred_lt_three_pow_pred hp5)
  have hthree_le_qpow : 3 ^ (p - 1) ≤ q ^ (p - 1) :=
    Nat.pow_le_pow_left hq3 (p - 1)
  exact lt_of_lt_of_le hpq_lt_three hthree_le_qpow

private theorem two_mul_sq_lt_pow_pred_of_odd_lt {p q : ℕ}
    (hpodd : Odd p) (hqodd : Odd q) (hq3 : 3 ≤ q) (hqp : q < p) :
    2 * q * q < p ^ (q - 1) := by
  by_cases hq_three : q = 3
  · subst q
    have hp_gt_three : 3 < p := by simpa using hqp
    have hp5 : 5 ≤ p := by
      have hp_ne_four : p ≠ 4 := by
        intro hp4
        have hodd : Odd 4 := by simpa [hp4] using hpodd
        rcases hodd with ⟨k, hk⟩
        omega
      omega
    have hpow2 : 2 * 3 * 3 < p ^ 2 := by
      nlinarith
    simpa using hpow2
  · have hq5 : 5 ≤ q := by
      have hq_ne_four : q ≠ 4 := by
        intro hq4
        have hodd : Odd 4 := by simpa [hq4] using hqodd
        rcases hodd with ⟨k, hk⟩
        omega
      omega
    have hq_pos : 0 < q := by omega
    have hq_sq_pos : 0 < q * q := Nat.mul_pos hq_pos hq_pos
    have htwo_lt_qsq : 2 < q * q := by nlinarith
    have hlt_q4 : 2 * (q * q) < (q * q) * (q * q) :=
      Nat.mul_lt_mul_of_pos_right htwo_lt_qsq hq_sq_pos
    have hq4_le_p4 : q ^ 4 ≤ p ^ 4 :=
      Nat.pow_le_pow_left (Nat.le_of_lt hqp) 4
    have hp_pos : 0 < p := by omega
    have hp4_le : p ^ 4 ≤ p ^ (q - 1) :=
      Nat.pow_le_pow_right hp_pos (by omega : 4 ≤ q - 1)
    calc
      2 * q * q = 2 * (q * q) := by ring
      _ < (q * q) * (q * q) := hlt_q4
      _ = q ^ 4 := by ring
      _ ≤ p ^ 4 := hq4_le_p4
      _ ≤ p ^ (q - 1) := hp4_le

namespace CaseBForTData

/-- The T-side case-(9.7.b) cyclotomic value in **Peterfalvi (14.4)** is already
larger than `p q`.  This is the cyclotomic lower consequence consumed by the
norm-cascade contradiction in (14.11.4). -/
theorem pq_lt_v {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    hyp.base.p * hyp.base.q < hyp.base.v := by
  have hpow : hyp.base.p * hyp.base.q < hyp.base.q ^ (hyp.base.p - 1) :=
    p_mul_q_lt_q_pow_pred_of_five_le hyp.five_le_p hyp.base.three_le_q hyp.q_lt_p
  have hleQ := cyclotomic_quotient_sub_one_ge_pow_pred
    (q := hyp.base.q) (p := hyp.base.p) hyp.base.q_prime.two_le hyp.base.p_prime.two_le
  have hle : hyp.base.q ^ (hyp.base.p - 1) ≤
      (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) - 1 := by
    exact_mod_cast hleQ
  rw [data.v_eq]
  exact lt_of_lt_of_le (lt_of_lt_of_le hpow hle)
    (Nat.sub_le ((hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1)) 1)

/-- The T-side case-(9.7.b) lower bound also gives the size hypothesis
`v > 2 p` needed in the (14.11.4) norm cascade. -/
theorem two_p_lt_v {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    2 * hyp.base.p < hyp.base.v := by
  have hq_gt_two : 2 < hyp.base.q := by
    have hq3 : 3 ≤ hyp.base.q := hyp.base.three_le_q
    omega
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hmul : hyp.base.p * 2 < hyp.base.p * hyp.base.q :=
    Nat.mul_lt_mul_of_pos_left hq_gt_two hp_pos
  have h2p_lt_pq : 2 * hyp.base.p < hyp.base.p * hyp.base.q := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  exact lt_trans h2p_lt_pq data.pq_lt_v

end CaseBForTData

namespace CaseBForSData

/-- The S-side case-(9.7.b) cyclotomic value in **Peterfalvi (14.6)** is larger
than `2 q`.  This is the S-side size input consumed by the norm-cascade
contradiction in (14.11.4), including the additional division by `q` in the
`p ≡ 1 mod q` branch. -/
theorem two_q_lt_u {hyp : Hypothesis (G := G)} (data : CaseBForSData hyp) :
    2 * hyp.base.q < hyp.base.u := by
  have hpow_sq :
      2 * hyp.base.q * hyp.base.q < hyp.base.p ^ (hyp.base.q - 1) :=
    two_mul_sq_lt_pow_pred_of_odd_lt hyp.base.p_odd hyp.base.q_odd
      hyp.base.three_le_q hyp.q_lt_p
  have hq_gt_one : 1 < hyp.base.q := hyp.base.q_prime.one_lt
  have htwoq_pos : 0 < 2 * hyp.base.q :=
    Nat.mul_pos (by norm_num) hyp.base.q_prime.pos
  have htwoq_lt_twoqq : 2 * hyp.base.q < 2 * hyp.base.q * hyp.base.q := by
    have hmul := Nat.mul_lt_mul_of_pos_left hq_gt_one htwoq_pos
    simpa [mul_assoc] using hmul
  have hpow : 2 * hyp.base.q < hyp.base.p ^ (hyp.base.q - 1) :=
    lt_trans htwoq_lt_twoqq hpow_sq
  have hleQ := cyclotomic_quotient_sub_one_ge_pow_pred
    (q := hyp.base.p) (p := hyp.base.q) hyp.base.p_prime.two_le hyp.base.q_prime.two_le
  have hle : hyp.base.p ^ (hyp.base.q - 1) ≤
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 := by
    exact_mod_cast hleQ
  have hfull_gt_twoq :
      2 * hyp.base.q < (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
    lt_of_lt_of_le (lt_of_lt_of_le hpow hle)
      (Nat.sub_le ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) 1)
  have hfull_gt_twoqq :
      2 * hyp.base.q * hyp.base.q <
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
    lt_of_lt_of_le (lt_of_lt_of_le hpow_sq hle)
      (Nat.sub_le ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) 1)
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · rw [data.u_eq_of_p_modEq_one hmod]
    have hdvd : hyp.base.q ∣ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
      OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one
        hyp.base.p_prime hmod
    have hlt_div :
        2 * hyp.base.q <
          (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) / hyp.base.q := by
      rw [Nat.lt_div_iff_mul_lt' hdvd]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hfull_gt_twoqq
    rw [show (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1)) =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) / hyp.base.q by
      rw [Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm]]
    exact hlt_div
  · rw [data.u_eq_of_not_modEq_one hmod]
    exact hfull_gt_twoq

end CaseBForSData

/-- Arithmetic bridge for **Peterfalvi (14.8)**: under the Section 16 prime
ordering `q < p`, the T-side full cyclotomic quotient gives a strictly larger
`(v - 1) / p` ratio than the S-side full cyclotomic quotient gives for
`(u - 1) / q`. -/
theorem cyclotomic_ratio_gt_of_q_lt_p {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q) (hqp : q < p) :
    (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) / (p : ℚ) >
      (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) / (q : ℚ) := by
  have hpow : q ^ (p + 1) > p ^ (q + 1) :=
    OddOrder.Peterfalvi.S16.q_pow_gt_p_pow hq hpodd hqodd hqp
  have hq2 : 2 ≤ q := hq.two_le
  have hp2 : 2 ≤ p := hp.two_le
  have hqpos_nat : 0 < q := hq.pos
  have hppos_nat : 0 < p := hp.pos
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hp1_pos_nat : 0 < p - 1 := by omega
  have hp1pos : (0 : ℚ) < (((p - 1 : ℕ) : ℚ)) := by exact_mod_cast hp1_pos_nat
  have hp_pred_ge_q : q ≤ p - 1 := by omega
  have hmain_nat : p ^ (q + 1) < (p - 1) * q ^ p := by
    have hmul : q ^ (p + 1) ≤ (p - 1) * q ^ p := by
      rw [pow_succ, mul_comm (q ^ p) q]
      exact Nat.mul_le_mul_right (q ^ p) hp_pred_ge_q
    exact lt_of_lt_of_le hpow hmul
  have hmain : (p : ℚ) ^ (q + 1) < (((p - 1 : ℕ) : ℚ)) * (q : ℚ) ^ p := by
    exact_mod_cast hmain_nat
  have hmain' : (p ^ q : ℚ) * (p : ℚ) <
      (q ^ (p - 1) : ℚ) * ((q : ℚ) * (((p - 1 : ℕ) : ℚ))) := by
    have hp_pow : (p : ℚ) ^ (q + 1) = (p : ℚ) ^ q * (p : ℚ) := by
      rw [pow_succ]
    have hq_pow : (q : ℚ) ^ p = (q : ℚ) ^ (p - 1) * (q : ℚ) := by
      calc
        (q : ℚ) ^ p = (q : ℚ) ^ ((p - 1) + 1) := by
          exact congrArg (fun n : ℕ => (q : ℚ) ^ n) (by omega : p = (p - 1) + 1)
        _ = (q : ℚ) ^ (p - 1) * (q : ℚ) := by rw [pow_succ]
    norm_num [Nat.cast_pow] at hmain ⊢
    nlinarith
  have hleft_lower := cyclotomic_quotient_sub_one_ge_pow_pred (q := q) (p := p) hq2 hp2
  have hright_upper := cyclotomic_quotient_sub_one_lt_div (p := p) (q := q) hp2
  have hcompare_core : (p ^ q : ℚ) / ((q : ℚ) * (((p - 1 : ℕ) : ℚ))) <
      (q ^ (p - 1) : ℚ) / (p : ℚ) := by
    rw [div_lt_div_iff₀]
    · simpa [Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using hmain'
    · positivity
    · exact hppos
  calc
    (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) / (q : ℚ)
        < ((p ^ q : ℚ) / (((p - 1 : ℕ) : ℚ))) / (q : ℚ) :=
          div_lt_div_of_pos_right hright_upper hqpos
    _ = (p ^ q : ℚ) / ((q : ℚ) * (((p - 1 : ℕ) : ℚ))) := by
          field_simp [hqpos.ne', hp1pos.ne']
    _ < (q ^ (p - 1) : ℚ) / (p : ℚ) := hcompare_core
    _ ≤ (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) / (p : ℚ) := by
          exact div_le_div_of_nonneg_right (by simpa [Nat.cast_pow] using hleft_lower)
            (le_of_lt hppos)

/-- The ratio comparison in **Peterfalvi (14.8)** from the two case-(9.7.b)
cyclotomic order conclusions. -/
theorem key_ratio_inequality_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) :
    (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  have hratio := cyclotomic_ratio_gt_of_q_lt_p
    hyp.base.p_prime hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p
  have hqpos : (0 : ℚ) < hyp.base.q := by exact_mod_cast hyp.base.q_prime.pos
  have hu_sub : ((hyp.base.u - 1 : ℕ) : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le_sub_right Sdata.u_le_full_cyclotomic 1
  have hu_div : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) /
        (hyp.base.q : ℚ) :=
    div_le_div_of_nonneg_right hu_sub (le_of_lt hqpos)
  rw [Tdata.v_eq]
  exact lt_of_le_of_lt hu_div hratio

/-- **Peterfalvi (14.8)** from materialized case-(9.7.b) data on both sides.
This is the proven consumer form of `key_inequality`: once Sections (14.4) and
(14.6) provide the T- and S-side `CaseB` data, the remaining comparison is pure
arithmetic. -/
theorem key_inequality_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  exact ⟨hyp.q_pow_gt_p_pow, key_ratio_inequality_of_caseB_data Tdata Sdata⟩

/-- **Peterfalvi (14.8)** consumer form for the exact output shapes of
`caseB_for_T` and `caseB_for_S`.  This keeps the future proof of
`key_inequality` focused on constructing the structural `CaseB` data. -/
theorem key_inequality_of_caseB_outputs {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  rcases hT with ⟨Tdata, _hTcase, _hv⟩
  rcases hS with ⟨Sdata, _hScase⟩
  exact key_inequality_of_caseB_data Tdata Sdata

/-- **Peterfalvi (14.8)**: the strict exponential inequality and its
character-theoretic corollary comparing `(v - 1) / p` and `(u - 1) / q`. -/
theorem key_inequality [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  -- (14.8) is the proven arithmetic consumer `key_inequality_of_caseB_outputs`
  -- fed by the (14.4) T-side and (14.6) S-side case-(9.7.b) data.  The S-side
  -- data `caseB_for_S` needs an `LHypothesis`, supplied by `exists_LHypothesis`.
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hyp
  exact key_inequality_of_caseB_outputs (caseB_for_T _hG hyp) (caseB_for_S _hG hyp Ldata)

/-! ## (14.10)--(14.11): the subgroup `M` over `N_G(V)` -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.10)**: the type-I maximal subgroup `M` containing
`N_G(V)`, its Fitting kernel `K`, the Dade extension, and `beta_M`. -/
structure MHypothesis (hyp : Hypothesis (G := G)) where
  [finiteG : Finite G]
  M : Subgroup G
  K : Subgroup G
  M_maximal : M ∈ maximalSubgroups G
  normalizer_V_le_M : Subgroup.normalizer (hyp.base.V : Set G) ≤ M
  K_eq_MF : K = maxNilpotentNormalHall M
  /-- **Peterfalvi (12.1) for `M`**: the genuine type-I Dade setup of the maximal subgroup `M`
  over `N_G(V)` — its `TypeIData`, the (8.15) Dade support data for `A(M)`, and the support-kernel
  conjugation invariance.  This is the honest carrier (sorry-free constructible from `IsTypeI M`
  via `S14.exists_typeI_hypothesis`) supplying the concrete `S04.Hypothesis`/`S04.DadeMap` that
  bridge `M` to the §7 ρ-machinery (`S09.Hypothesis71`/`FamilyHypothesis71`/`family_inequality`),
  the common §3/§4 Dade foundation of the (14.11) norm-cascade producers. -/
  typeIHyp : OddOrder.Peterfalvi.S14.Hypothesis M
  /-- **Peterfalvi (7.8) for `M`**: the §7 coherence data (`S09.Hypothesis78`) of the type-I
  maximal subgroup `M` on its Dade support `A(M) = typeIA M`.  Its (7.8.a) `β`-decomposition and
  (7.8.b) norm estimates feed the (14.11) cascade producers (`betaM_expansion_data` via
  `betaMExpansionData_of_hypothesis78`; `normCascadeData` via `family_inequality`).  The genuine
  M-coherence supply (Pf §5–§8 + §13/§14), isolated here as the single honest obligation that
  `exists_MHypothesis` discharges. -/
  h78 : OddOrder.Peterfalvi.S09.Hypothesis78 G
    (OddOrder.GroupTheory.typeIA M typeIHyp.typeI) M
  Mset : Set (ClassFunction ↥M ℂ)
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  psi : ClassFunction ↥M ℂ
  e : ℕ
  k : ℕ
  /-- **Peterfalvi (14.10)**: `e = |M : K|` (the degree of `ψ`).  De-opacified from the former
  opaque `Prop` to the concrete index identity (lane-c §16 char-endpoint, carrier honesty). -/
  e_eq_index : e = (K.subgroupOf M).index
  /-- **Peterfalvi (14.11)**: `e = |M : K| = p q`.  The V-side dual of
  `LHypothesis.typeI_complement_card_eq_pq`: `M` is type I over `N_G(V)` with Frobenius complement
  `W₁ W₂^y` of order `p q` ((13.17.c)/(14.5), dual side).  Carried structurally and supplied by
  `exists_MHypothesis` (from the T/V-side `typeII_overNormalizer_frobenius`), so that the index
  half of (14.11) `K_eq_V_index_pq` is a direct consequence rather than a separate obligation. -/
  complement_card_eq_pq : e = hyp.base.p * hyp.base.q
  k_eq_card_K : k = Nat.card ↥K
  psi_mem : psi ∈ Mset
  psi_degree_eq_e : psi 1 = (e : ℂ)
  betaM : ClassFunction G ℂ
  /-- **Peterfalvi (14.10)**: `betaM` is `β_M^τ`, the image under the Dade isometry `τ` of
  `β_M = Ind_K^M 1_K − ψ`.  Still carried as an opaque `Prop` pending the induce/`Invertible`
  instance plumbing needed to spell `Ind_K^M 1_K` inside a field type (lane-c §16). -/
  betaM_formula : Prop
  betaM_formula_holds : betaM_formula
  /-- **Peterfalvi (7.8.a) for `M`**: `β_M^τ` is the Dade image `β` carried by `h78`. -/
  betaM_eq : betaM = h78.beta
  /-- **Peterfalvi (14.10)/(7.8)**: `ψ^{τ₁}` is the coherent image `ζ^ν` of the distinguished `ζ`. -/
  psi_tau1_eq : tau1 psi = h78.nu (h78.hyp76.zeta h78.zetaDistinct)
  /-- **Peterfalvi (13.1.d)/(3.9)**: the `±1` signs of the `η`-grid expansion of `1_G + Δ`. -/
  betaSigns : Fin hyp.base.q → Fin hyp.base.p → ℤ
  betaSigns_pm : ∀ i j, betaSigns i j = 1 ∨ betaSigns i j = -1
  /-- **Peterfalvi (13.1.d)**: `1_G + Δ = Σ ε_ij η_ij` ties the residual `Δ` of `h78`'s (7.8.a)
  decomposition to the §13 `η`-grid. -/
  betaGrid : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + h78.delta =
    ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (betaSigns i j : ℂ) • hyp.base.eta i j
  G0 : Set G
  /-- **Peterfalvi (14.10)/(7.5)**: the test character `ψ^{τ₁}` has norm one — it is the
  Dade-isometry `τ₁`-image of the unit-norm coherent `ζ`, hence admissible in the family
  inequality (7.5) `S09.family_inequality`.  V-side dual of
  `S12.Hypothesis.inner_tau1_zeta_self_eq_one`; a genuine consequence of `tau1` being an isometry
  on `ℤ[ℳ]` and `ψ ∈ ℳ` irreducible. -/
  psi_tau1_norm_one : ClassFunction.inner (tau1 psi) (tau1 psi) = 1
  /-- **Peterfalvi (14.11.3)/(14.11.4)**: `G₀ ⊆ G − Ã(M)`.  The (14.11.3) set
  `G₀ = G − [Ã(M) ∪ (W#)^G ∪ (P#)^G ∪ (Q#)^G]` lies inside the family `(7.4)` support complement
  `famG₀ = (toFamilyHypothesis71).G0 = G − Ã(M)`, since every `g ∈ G₀` is off the Dade support
  `Ã(M)` of `A(M)` (`typeIHyp.dadeData.dade.dadeSupport`).  This is the inclusion `G₀ ⊆ famG₀`
  used to drop the `G₀`-part of the (7.5) sum in (14.11.4). -/
  G0_off_dadeSupport : ∀ g ∈ G0, g ∉ typeIHyp.dadeData.dade.dadeSupport
  /-- **Peterfalvi (14.11.3)/(14.11.4)**: the complement of `G₀` is covered by the Dade support
  `Ã(M)` and the three orbits `(W − (W₁∪W₂))^G`, `(P#)^G`, `(Q#)^G`.  Concretely, `G₀` is the
  (14.11.3) set `G − [Ã(M) ∪ (W−(W₁∪W₂))^G ∪ (P#)^G ∪ (Q#)^G]`, so any `g` off `Ã(M)` and off `G₀`
  lies in the orbit union.  This is the §8 TI-counting input: `famG₀ ∖ G₀ ⊆ orbits` lets the
  `(7.5)` `G₀`-drop in line 83 (`chiRhoNormSq_psi_le_line83`) be bounded by the orbit cardinalities
  (the genuine §8 structural fact, supplied from the partner type-`P` structure). -/
  G0_orbit_cover : ∀ g : G, g ∉ typeIHyp.dadeData.dade.dadeSupport → g ∉ G0 →
    g ∈ OddOrder.GroupTheory.conjClassSet
          ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
        ∪ OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)
        ∪ OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)
  /-- **Peterfalvi (14.11.3), avoidance half**: the generic set meets none of the three
  singular orbits — no conjugate of the regular Weyl set `W − (W₁∪W₂)`, of `P#`, or of `Q#`.
  Together with `G0_off_dadeSupport` this pins `G₀` inside Peterfalvi's (14.11.3) complement
  `G − [Ã(M) ∪ (W#)^G ∪ (P#)^G ∪ (Q#)^G]`; the support half of (14.11.3) — every `g ∈ G₀`
  has order prime to `pq` — follows through `orderOf_coprime_pq_of_not_mem_conj`
  (`G0_orderOf_coprime` below). -/
  G0_avoid : ∀ g ∈ G0,
    g ∉ OddOrder.GroupTheory.conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
      ∧ g ∉ OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)
      ∧ g ∉ OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)
  /-- **Peterfalvi §13 `normalizer_V` for the `W`-set**: `N_G(X) = W` for every nonempty
  `X ⊆ W − (W₁∪W₂)` (the type-`P` exceptional-set normalizer, from the partner structure).  The
  `hnorm` input to the `W`-orbit TI count (`orbit_sdiff_sup_normSq_term`). -/
  W_normalizer_V : ∀ X : Set G, X.Nonempty →
    X ⊆ (hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)) →
    Subgroup.normalizer X = hyp.base.W
  -- **Peterfalvi (14.11)/(14.11.3)**: `|W| = p q`, `|W₁| + |W₂| = p + q`, and the nonemptiness of
  -- `W − (W₁∪W₂)` are **base-derived** (`S15.card_W_eq_pq`, `S15.card_W1_add_W2`,
  -- `S15.W_sdiff_nonempty`), so they are no longer carried as fields — the `W = W₁ × W₂` cyclic
  -- structure is an elementary consequence of the base `Hypothesis`, not a §13-14 σ-obligation.
  /-- **Peterfalvi §8**: `P` is a TI-subgroup (distinct conjugates meet trivially). -/
  P_isTI : Subgroup.IsTI hyp.base.P
  /-- **Peterfalvi §8**: `Q` is a TI-subgroup. -/
  Q_isTI : Subgroup.IsTI hyp.base.Q
  /-- **Peterfalvi (14.11.4)**: `|N_G(P)| = |P| u q` (the Type-II partner `S = (H ⋊ U) ⋊ W₂`). -/
  card_normalizer_P_eq : Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G))
    = Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q
  /-- **Peterfalvi (14.11.4)**: `|N_G(Q)| = |Q| v p` (the `T`-side partner). -/
  card_normalizer_Q_eq : Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G))
    = Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p
  /-- **Peterfalvi (7.1)/(14.11.4) bridge compatibility.**  The underlying `(7.1)` Dade hypothesis
  of the §7 coherence datum `h78` is the type-I Dade support hypothesis of `M` carried by
  `typeIHyp` (i.e. `h78` is built over the same `(M, A(M))` Dade map that powers the family
  inequality (7.5) via `toFamilyHypothesis71`).  Since `S09.Hypothesis71.chiRho` depends only on
  the support hypothesis `H71.hyp` (the `H(a)`-family), not on the chosen Dade map `τ`, this
  identifies the `ρ`-image of `h78` (used in `zetaNuRho`, (7.8.b)) with the family member's
  `ρ`-image, so the `ρ`-norm `‖ψ^{τ₁ρ}‖²` of (14.11.4) equals `h78.zetaNuRhoNormSq`.  Holds by
  `rfl` for any `h78` built from `typeIHyp.dadeData`; carried so `exists_MHypothesis` supplies a
  compatible `h78`. -/
  h78_hyp_eq : h78.hyp76.hyp71.hyp = typeIHyp.dadeData.dade
  /-- **Peterfalvi (7.6)/(14.10).**  The normal kernel `H` of the §7 coherence datum `h78` is the
  Fitting kernel `K = M_F`.  (For type-I `M`, `A(M) = K^#` is the Dade support; the coherent family
  `T = {Ind_K^M θ}` has kernel `K`.)  Gives `h78.kernelOrder = |K| = k` and
  `h78.complementIndex = |M : K| = e = p q` for the (7.8.b) lower bound. -/
  h78_H_eq : h78.hyp76.H = K
  /-- **Peterfalvi (7.8.b) for `M`** — the coherence-norm lower bound
  `‖ζ^{νρ}‖² ≥ 1 − e/h = 1 − |M:K|/|K|`.  This is
  `S09.Hypothesis78.NormEstimates.zetaNuRho_norm_sq_ge` for the coherent type-I `M`, with the
  small-index hypothesis `smallIndex` (`2·|M:K| + 1 ≤ |K|`, i.e. `2 p q + 1 ≤ k`, a consequence of
  (14.11.1) `k > 2 p v` and `v ≥ q`) discharged.  The genuine §7 Dade content of the (14.11.4)
  lower bound, isolated here as part of the `exists_MHypothesis` obligation. -/
  h78_zetaNuRho_normSq_ge :
    1 - (h78.complementIndex : ℝ) / (h78.kernelOrder : ℝ) ≤ h78.zetaNuRhoNormSq

namespace MHypothesis

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The Peterfalvi (7.4) one-member family `{(M, A(M))}` for the V-side type-I subgroup `M`** —
the §7 input bridging `M` to the family inequality (7.5) `S09.family_inequality`, the common
foundation of the (14.11) norm-cascade producers (`normCascadeData`, …).

Built genuinely from the type-I Dade setup carried by `typeIHyp` (its (8.15) Dade support
`dadeData` for `A(M) = typeIA M` and the conjugation invariance `hconj`), mirroring
`S12.Hypothesis.toFamilyHypothesis71` for type-`P` subgroups — but on the type-I support `typeIA`,
so no `A_0(M) → A(M)` restriction is needed.  The single member's (7.1) data is the restricted Dade
map of `dadeData`, the `IsDadeIsometry` certificate is `FullDadeIsometryData`'s, and
`pairwise_disjoint` is vacuous over `Fin 1`.  **Sorry-free + self-contained** from the genuine
`typeIHyp`. -/
noncomputable def toFamilyHypothesis71 [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) : OddOrder.Peterfalvi.S09.FamilyHypothesis71 G 1 where
  L := fun _ => Mdata.M
  A := fun _ => OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI
  fintypeL := fun _ => inferInstance
  invertibleL := fun _ => inferInstance
  hyp71 := fun _ =>
    { hyp := Mdata.typeIHyp.dadeData.dade
      τ := (Mdata.typeIHyp.dadeData.dade.fullDadeIsometryData Mdata.typeIHyp.hconj).toDadeMap
      isDadeMap :=
        (Mdata.typeIHyp.dadeData.dade.fullDadeIsometryData
          Mdata.typeIHyp.hconj).toDadeIsometryData.isDadeMap
      hConjInvariant := Mdata.typeIHyp.hconj }
  isDadeIsometry := fun _ =>
    (Mdata.typeIHyp.dadeData.dade.fullDadeIsometryData
      Mdata.typeIHyp.hconj).toDadeIsometryData.isDadeIsometry
  pairwise_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij

end MHypothesis

/-- The displayed rational inequality produced by the norm calculation in
**Peterfalvi (14.11.4)**, after substituting `e = p q`.  It is kept concrete so
future character-theoretic producers can target the exact arithmetic consumer
without adding another opaque proposition. -/
def normCascadeBound (hyp : Hypothesis (G := G)) (k : ℕ) : Prop :=
  (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
    ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
      2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
      1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
      1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)

/-- Pure arithmetic estimate used in **Peterfalvi (14.11.4)**.  Once the
norm calculation reduces the error terms to `2 / (p q) + 1 / (u q) + 1 / (v p)`,
the Section 16 size assumptions `u > 2q`, `v > 2p`, and `q < p` bound that error
strictly by `1 / q`. -/
theorem norm_error_terms_lt_inv_q {p q u v : ℕ}
    (hq3 : 3 ≤ q) (hqp : q < p) (hu : 2 * q < u) (hv : 2 * p < v) :
    (2 : ℚ) / ((p * q : ℕ) : ℚ) + 1 / ((u * q : ℕ) : ℚ) +
        1 / ((v * p : ℕ) : ℚ) < 1 / (q : ℚ) := by
  have hqpos_nat : 0 < q := by omega
  have hppos_nat : 0 < p := by omega
  have hupos_nat : 0 < u := by omega
  have hvpos_nat : 0 < v := by omega
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hupos : (0 : ℚ) < u := by exact_mod_cast hupos_nat
  have hvpos : (0 : ℚ) < v := by exact_mod_cast hvpos_nat
  have hq3q : (3 : ℚ) ≤ q := by exact_mod_cast hq3
  have hqpq : (q : ℚ) < p := by exact_mod_cast hqp
  have huq : (2 : ℚ) * q < u := by exact_mod_cast hu
  have hvp : (2 : ℚ) * p < v := by exact_mod_cast hv
  have hterm1 : (2 : ℚ) / ((p * q : ℕ) : ℚ) < 2 / ((q * q : ℕ) : ℚ) := by
    norm_num [Nat.cast_mul]
    exact div_lt_div_of_pos_left (by norm_num) (mul_pos hqpos hqpos)
      (mul_lt_mul_of_pos_right hqpq hqpos)
  have hterm2 : (1 : ℚ) / ((u * q : ℕ) : ℚ) < 1 / ((2 * q * q : ℕ) : ℚ) := by
    have hden : (2 : ℚ) * q * q < u * q := by nlinarith [huq, hqpos]
    have hcore : (1 : ℚ) / (u * q) < 1 / (2 * q * q) :=
      one_div_lt_one_div_of_lt (by positivity : (0 : ℚ) < 2 * q * q) hden
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hterm3 : (1 : ℚ) / ((v * p : ℕ) : ℚ) < 1 / ((2 * q * q : ℕ) : ℚ) := by
    have hsq : (q : ℚ) * q < p * p := by nlinarith [hqpq, hqpos, hppos]
    have hden : (2 : ℚ) * q * q < v * p := by nlinarith [hsq, hvp, hppos]
    have hcore : (1 : ℚ) / (v * p) < 1 / (2 * q * q) :=
      one_div_lt_one_div_of_lt (by positivity : (0 : ℚ) < 2 * q * q) hden
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hsum :
      (2 : ℚ) / ((p * q : ℕ) : ℚ) + 1 / ((u * q : ℕ) : ℚ) +
          1 / ((v * p : ℕ) : ℚ) <
        2 / ((q * q : ℕ) : ℚ) + 1 / ((2 * q * q : ℕ) : ℚ) +
          1 / ((2 * q * q : ℕ) : ℚ) := by
    nlinarith [hterm1, hterm2, hterm3]
  have hsum_eq :
      2 / ((q * q : ℕ) : ℚ) + 1 / ((2 * q * q : ℕ) : ℚ) +
          1 / ((2 * q * q : ℕ) : ℚ) = 3 / ((q * q : ℕ) : ℚ) := by
    norm_num [Nat.cast_mul]
    field_simp [hqpos.ne']
    ring
  have hthree_le : (3 : ℚ) / ((q * q : ℕ) : ℚ) ≤ 1 / (q : ℚ) := by
    norm_num [Nat.cast_mul]
    have hmul_nonneg : 0 ≤ (q : ℚ) * ((q : ℚ) - 3) :=
      mul_nonneg (le_of_lt hqpos) (sub_nonneg.mpr hq3q)
    field_simp [hqpos.ne']
    nlinarith [hmul_nonneg]
  nlinarith [hsum, hsum_eq, hthree_le]

/-- **Peterfalvi (14.11.4), the upper-bound loosening step** (04.16 line 115).  The raw `(7.8.b)`
upper estimate
`1 − 1/p − 1/q + 1/(pq) + (|P|−1)/(|P|uq) + (|Q|−1)/(|Q|vp) + (k−1)/(kpq)`
is loosened to the displayed `NormCascadeData.upper`
`1 − 1/p − 1/q + 2/(pq) + 1/(uq) + 1/(vp)`
via `(|P|−1)/|P| ≤ 1`, `(|Q|−1)/|Q| ≤ 1`, and `(k−1)/k ≤ 1` (so `(k−1)/(kpq) ≤ 1/(pq)`).  Pure `ℝ`
arithmetic; reusable by the `normCascadeData` producer to discharge `NormCascadeData.upper` once the
§8 TI-counting has produced the raw bound. -/
theorem normCascade_upper_loosen {p q u v k cardP cardQ : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v)
    (hk : 0 < k) (hP : 0 < cardP) (hQ : 0 < cardQ) :
    (1 : ℝ) - 1 / (p : ℝ) - 1 / (q : ℝ) + 1 / ((p * q : ℕ) : ℝ)
        + ((cardP : ℝ) - 1) / ((cardP * u * q : ℕ) : ℝ)
        + ((cardQ : ℝ) - 1) / ((cardQ * v * p : ℕ) : ℝ)
        + ((k : ℝ) - 1) / ((k * p * q : ℕ) : ℝ)
      ≤ 1 - 1 / (p : ℝ) - 1 / (q : ℝ) + 2 / ((p * q : ℕ) : ℝ)
        + 1 / ((u * q : ℕ) : ℝ) + 1 / ((v * p : ℕ) : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hPR : (0 : ℝ) < cardP := by exact_mod_cast hP
  have hQR : (0 : ℝ) < cardQ := by exact_mod_cast hQ
  -- `(|P|−1)/(|P|uq) ≤ 1/(uq)`.
  have h1 : ((cardP : ℝ) - 1) / ((cardP * u * q : ℕ) : ℝ) ≤ 1 / ((u * q : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [hPR, huR, hqR, mul_pos huR hqR]
  -- `(|Q|−1)/(|Q|vp) ≤ 1/(vp)`.
  have h2 : ((cardQ : ℝ) - 1) / ((cardQ * v * p : ℕ) : ℝ) ≤ 1 / ((v * p : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [hQR, hvR, hpR, mul_pos hvR hpR]
  -- `(k−1)/(kpq) ≤ 1/(pq)`.
  have h3 : ((k : ℝ) - 1) / ((k * p * q : ℕ) : ℝ) ≤ 1 / ((p * q : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [hkR, hpR, hqR, mul_pos hpR hqR]
  -- `1/(pq) + (k−1)/(kpq) ≤ 2/(pq)`, plus the two complement bounds.
  have hpq2 : (2 : ℝ) / ((p * q : ℕ) : ℝ)
      = 1 / ((p * q : ℕ) : ℝ) + 1 / ((p * q : ℕ) : ℝ) := by ring
  linarith [h1, h2, h3, hpq2]

/-- Arithmetic endpoint for **Peterfalvi (14.11.4)**.  If the norm calculation
has already yielded the displayed bound from the text, then the lower bound
`k > 2 p v` and the cyclotomic lower consequence `p q < v` are contradictory. -/
theorem norm_cascade_contradiction {p q u v k : ℕ}
    (hq3 : 3 ≤ q) (hqp : q < p) (hu : 2 * q < u) (hv : 2 * p < v)
    (hk : 2 * p * v < k) (hvlarge : p * q < v)
    (hbound :
      (1 : ℚ) / (p : ℚ) + 1 / (q : ℚ) ≤
        ((p * q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((p * q : ℕ) : ℚ) +
          1 / ((u * q : ℕ) : ℚ) +
          1 / ((v * p : ℕ) : ℚ)) :
    False := by
  have hqpos_nat : 0 < q := by omega
  have hppos_nat : 0 < p := by omega
  have hvpos_nat : 0 < v := by omega
  have hkpos_nat : 0 < k := by omega
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hkpos : (0 : ℚ) < k := by exact_mod_cast hkpos_nat
  have hsmall := norm_error_terms_lt_inv_q (p := p) (q := q) (u := u) (v := v)
    hq3 hqp hu hv
  have hpinv_lt : (1 : ℚ) / (p : ℚ) < ((p * q : ℕ) : ℚ) / (k : ℚ) := by
    nlinarith [hbound, hsmall]
  have hk_lt : (k : ℚ) < (p : ℚ) * (p : ℚ) * (q : ℚ) := by
    field_simp [Nat.cast_mul, hppos.ne', hqpos.ne', hkpos.ne'] at hpinv_lt
    norm_num [Nat.cast_mul] at hpinv_lt
    nlinarith [hpinv_lt]
  have hk_gt : ((2 * p * v : ℕ) : ℚ) < k := by exact_mod_cast hk
  have hvlargeq : ((p * q : ℕ) : ℚ) < v := by exact_mod_cast hvlarge
  norm_num [Nat.cast_mul] at hk_gt hvlargeq
  nlinarith [hk_lt, hk_gt, hvlargeq, hppos]

/-- **Peterfalvi (14.11.4)** arithmetic consumer with the T-side case-(9.7.b)
data already materialized.  The T-side data supplies both `p q < v` and
`2 p < v`, so the remaining inputs are exactly the S-side lower bound on `u`,
the `k > 2 p v` lower bound, and the displayed norm inequality. -/
theorem norm_cascade_contradiction_of_T_caseB {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (hu : 2 * hyp.base.q < hyp.base.u) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k)
    (hbound :
      (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)) :
    False := by
  exact norm_cascade_contradiction hyp.base.three_le_q hyp.q_lt_p hu
    Tdata.two_p_lt_v hk Tdata.pq_lt_v hbound

/-- **Peterfalvi (14.11.4)** arithmetic consumer with both case-(9.7.b) data
packages materialized.  The S-side data supplies `2 q < u`; the T-side data
supplies `2 p < v` and `p q < v`. -/
theorem norm_cascade_contradiction_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k)
    (hbound :
      (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)) :
    False := by
  exact norm_cascade_contradiction_of_T_caseB Tdata Sdata.two_q_lt_u hk hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact output shapes of
`caseB_for_T` and `caseB_for_S`.  It leaves only the lower bound on `k` and the
concrete displayed norm inequality as inputs. -/
theorem norm_cascade_contradiction_of_caseB_outputs {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k) (hbound : normCascadeBound hyp k) :
    False := by
  rcases hT with ⟨Tdata, _hTcase, _hv⟩
  rcases hS with ⟨Sdata, _hScase⟩
  exact norm_cascade_contradiction_of_caseB_data Tdata Sdata hk hbound

/-- **Peterfalvi (14.11.4)** consumer after the first numerical output of
`main_size_bounds` has supplied `k > 2 p v`.  The remaining non-arithmetic work
is precisely to produce the displayed norm inequality. -/
theorem norm_cascade_contradiction_of_main_size_bound {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v)
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  exact norm_cascade_contradiction_of_caseB_data Tdata Sdata hsize hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact three-part numerical output
of **Peterfalvi (14.11.1)**.  Only the first component, `k > 2 p v`, is needed
by the norm-cascade contradiction; the remaining components stay available to
match the theorem output without weakening its shape. -/
theorem norm_cascade_contradiction_of_caseB_data_main_size_bounds
    {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  exact norm_cascade_contradiction_of_main_size_bound Tdata Sdata Mdata hsize.1 hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact output shapes of
`caseB_for_T`, `caseB_for_S`, and `main_size_bounds`. -/
theorem norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
    {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  rcases hT with ⟨Tdata, _hTcase, _hv⟩
  rcases hS with ⟨Sdata, _hScase⟩
  exact norm_cascade_contradiction_of_caseB_data_main_size_bounds Tdata Sdata Mdata
    hsize hbound

/-- **Fixed-point-free congruence** (the mod-`p` analogue of the `U⋊W₁` Frobenius congruence,
group-theoretic core).  If a subgroup `A` of prime order `p` normalizes a finite group `U` and
acts on it fixed-point-freely by conjugation, then `|U| ≡ 1 (mod p)`.  The conjugation action of
the `p`-group `A` on `U` has `{1}` as its only fixed point, so the `p`-group fixed-point
congruence `Nat.card U ≡ Nat.card (fixedPoints) (mod p)` gives `|U| ≡ 1 (mod p)`. -/
theorem card_modEq_one_of_prime_normalizing_fpf {G : Type*} [Group G] [Finite G]
    {U A : Subgroup G} {p : ℕ} (hp : p.Prime) (hA_card : Nat.card ↥A = p)
    (hA_norm : A ≤ Subgroup.normalizer (U : Set G))
    (hfpf : ∀ a ∈ A, a ≠ 1 → ∀ u ∈ U, u ≠ 1 → (a : G) * u * (a : G)⁻¹ ≠ u) :
    Nat.card ↥U ≡ 1 [MOD p] := by
  letI : MulAction ↥A ↥U := MulAction.compHom ↥U (Subgroup.inclusion hA_norm)
  have hpg : IsPGroup p ↥A := IsPGroup.of_card (by rw [hA_card, pow_one])
  -- the conjugation `smul` is `a • u = a u a⁻¹`
  have hsmul : ∀ (a : ↥A) (u : ↥U), ((a • u : ↥U) : G) = (a : G) * (u : G) * (a : G)⁻¹ := by
    intro a u; rfl
  -- the only fixed point is `1`
  haveI : Nontrivial ↥A :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hA_card]; exact hp.one_lt)
  obtain ⟨a0, ha0⟩ := exists_ne (1 : ↥A)
  have ha0G : (a0 : G) ≠ 1 := fun h => ha0 (Subtype.ext h)
  have hfix_eq : MulAction.fixedPoints ↥A ↥U = {(1 : ↥U)} := by
    ext u
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hu
      by_contra hune
      have huG : (u : G) ≠ 1 := fun h => hune (Subtype.ext h)
      have hfixa : ((a0 • u : ↥U) : G) = (u : G) :=
        congrArg (Subtype.val) (hu a0)
      rw [hsmul] at hfixa
      exact hfpf (a0 : G) a0.2 ha0G (u : G) u.2 huG hfixa
    · rintro rfl
      intro a
      apply Subtype.ext
      rw [hsmul]
      simp
  have hfix_card : Nat.card (MulAction.fixedPoints ↥A ↥U) = 1 := by
    rw [hfix_eq]
    haveI := Set.uniqueSingleton (1 : ↥U)
    exact Nat.card_unique
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hcong := hpg.card_modEq_card_fixedPoints (α := ↥U)
  rwa [hfix_card] at hcong

/-- **A Frobenius complement acts fixed-point-freely on its kernel** (ambient-group form).
If `↥L` is a Frobenius group with kernel `H.subgroupOf L` and complement `compl`, and `H ≤ L`,
then every `a ≠ 1` lying — as a `G`-element — in the complement image `compl.map L.subtype`
conjugates no nontrivial `u ∈ H` to itself: `a * u * a⁻¹ ≠ u`.  This transports
`IsFrobeniusGroup.conj_frobenius` from `↥L` down to `G` through `L.subtype`. -/
theorem isFrobeniusGroup_conj_ne_of_mem_map_complement
    {L H : Subgroup G} {compl : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (H.subgroupOf L) compl)
    (hHL : H ≤ L) {a : G} (ha_mem : a ∈ compl.map L.subtype) (ha_ne : a ≠ 1)
    {u : G} (hu_mem : u ∈ H) (hu_ne : u ≠ 1) :
    a * u * a⁻¹ ≠ u := by
  obtain ⟨a', ha'_compl, ha'_eq⟩ := Subgroup.mem_map.mp ha_mem
  have ha'_ne : a' ≠ 1 := by
    intro h
    rw [h] at ha'_eq
    exact ha_ne (by simpa using ha'_eq.symm)
  have hmemL : u ∈ L := hHL hu_mem
  have hu'_ker : (⟨u, hmemL⟩ : ↥L) ∈ H.subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]; exact hu_mem
  have hu'_ne : (⟨u, hmemL⟩ : ↥L) ≠ 1 := fun h => hu_ne (congrArg Subtype.val h)
  have hconj := hfrob.conj_frobenius a' ha'_compl ha'_ne ⟨u, hmemL⟩ hu'_ker hu'_ne
  intro hcontra
  apply hconj
  apply Subtype.coe_injective
  show ((a' * ⟨u, hmemL⟩ * a'⁻¹ : ↥L) : G) = ((⟨u, hmemL⟩ : ↥L) : G)
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, InvMemClass.coe_inv,
    show ((a' : G)) = a from ha'_eq]
  exact hcontra

/-- If `x ≡ 1 (mod p)` with `p` odd and `≥ 2`, `x` odd and `x ≠ 1`, then `x ≥ 2p + 1`.  This is the
elided "fixed-point-free congruence + oddness" step of Peterfalvi (14.11.1): `x ≡ 1 (mod p)` and
`x ≠ 1` give `x = pm + 1` with `m ≥ 1`, and `x` odd with `p` odd forces `m` even, hence `m ≥ 2`. -/
private theorem two_mul_add_one_le_of_modEq_one_odd {p x : ℕ} (hp : Odd p) (hp2 : 2 ≤ p)
    (hmod : x ≡ 1 [MOD p]) (hodd : Odd x) (hne : x ≠ 1) : 2 * p + 1 ≤ x := by
  have hxmod : x % p = 1 := by
    have h := hmod
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (by omega : 1 < p)] at h
  have hdm := Nat.div_add_mod x p
  set m := x / p with hm_def
  rw [hxmod] at hdm
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h1
    · exfalso; rw [h0, Nat.mul_zero] at hdm; omega
    · exact h1
  have hpm_even : Even (p * m) := by
    rcases hodd with ⟨t, ht⟩; exact ⟨t, by omega⟩
  have hm_even : Even m := by
    by_contra hodd_m
    rw [Nat.not_even_iff_odd] at hodd_m
    exact (Nat.not_odd_iff_even.mpr hpm_even) (Nat.odd_mul.mpr ⟨hp, hodd_m⟩)
  have hm2 : 2 ≤ m := by rcases hm_even with ⟨r, hr⟩; omega
  have hpm : 2 * p ≤ p * m := by
    calc 2 * p = p * 2 := by ring
      _ ≤ p * m := by gcongr
  omega

/-- **Peterfalvi (14.11.1)** structural half: under `K ≠ V`, the Fitting kernel `K = M_F` is large
(`k > 2 p v`) and the Frobenius quotient `(k − 1) / e` dominates `(v − 1) / p`.  The **quotient
bound is now a genuine consequence** of `k > 2 p v` (with `e = pq`, `q < p`): `q(v−1) ≤ qv ≤ 2pv ≤
k−1`, so `(v−1)/p ≤ (k−1)/(pq)` (`div_le_div_iff₀` + `nlinarith`).  The `k > 2 p v` bound is in turn
the arithmetic consequence (`two_mul_add_one_le_of_modEq_one_odd`) of the §13/§15 structural datum
`hstruct` of (14.11.1): by (13.17) the kernel order factors as `k = v·x` with `x` an integer, `x ≠ 1`
(as `K ≠ V`), and `x ≡ 1 (mod p)` (since `W₂` acts fixed-point-freely on `K` and `V`); as `k = |K|`
is odd, `x` is odd, so `x ≥ 2p+1` and `k = vx > 2pv`.  The third inequality of (14.11.1),
`(v − 1) / p > (u − 1) / q`, is `key_ratio_inequality_of_caseB_data` (14.8), discharged in
`main_size_bounds`. -/
theorem main_size_bounds_structural [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) := by
  have hqp : hyp.base.q < hyp.base.p := hyp.q_lt_p
  -- (14.11.1): `k = v·x`, `x ≡ 1 (mod p)` (`W₂` fixed-point-free on `K`, `V`), `x ≠ 1` (`K ≠ V`) —
  -- the §13/§15 structural datum (13.17); `k > 2 p v` is then arithmetic (`x` odd, so `x ≥ 2p+1`).
  have hstruct : ∃ x : ℕ, Mdata.k = hyp.base.v * x ∧ x ≡ 1 [MOD hyp.base.p] ∧ x ≠ 1 := by
    have hMI : IsTypeI Mdata.M := ⟨Mdata.typeIHyp.typeI⟩
    have hTII : IsTypeII hyp.base.T := T_typeII _hG hyp
    -- **(13.17)/(14.11.1)**: `V ≤ K = M_F` (type-I-over-`N_G(V)` Fitting inclusion).
    have hVK : hyp.base.V ≤ Mdata.K := by
      rw [Mdata.K_eq_MF]
      exact OddOrder.Peterfalvi.S15.typeI_overNormalizer_V_le_fitting _hG hyp.base hTII
        Mdata.M_maximal hMI Mdata.normalizer_V_le_M
    -- `|V| = v` (`d = 1` from `D = V ⊓ C_G(Q) = ⊥`, (13.12) dual).
    have hVcard : Nat.card ↥hyp.base.V = hyp.base.v := by
      have hDbot : hyp.base.D = ⊥ := by
        rw [hyp.base.D_eq]
        exact OddOrder.Peterfalvi.S15.V_inf_centralizer_Q_eq_bot _hG hyp.base hTII
      have hd1 : hyp.base.d = 1 := by rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
      rw [hyp.base.card_V_eq_vd, hd1, mul_one]
    -- `v ∣ k` from `V ≤ K`; set `x = k / v`.
    have hvdvdk : hyp.base.v ∣ Mdata.k := by
      rw [Mdata.k_eq_card_K, ← hVcard]
      exact Subgroup.card_dvd_of_le hVK
    obtain ⟨x, hkx⟩ := hvdvdk
    -- **(13.17)**: type-I Frobenius data with `W₂ ≤ complement`, so `W₂` acts fpf on `K = M_F`.
    obtain ⟨frob, _hker, hW2E⟩ := OddOrder.Peterfalvi.S15.exists_typeIFrobeniusData_W2_le
      _hG hyp.base Mdata.M_maximal hMI Mdata.normalizer_V_le_M
    have hKeq : Mdata.K = frob.typeI.typeF.H := by rw [Mdata.K_eq_MF, frob.typeI.typeF.H_eq]
    have hW2card : Nat.card ↥hyp.base.W2 = hyp.base.p := hyp.base.p_eq_card_W2.symm
    have hW2M : hyp.base.W2 ≤ Mdata.M := by
      intro a ha
      obtain ⟨x', _, hx'⟩ := Subgroup.mem_map.mp (hW2E ha)
      rw [← hx']; exact x'.2
    have hW2normK : hyp.base.W2 ≤ Subgroup.normalizer (Mdata.K : Set G) := by
      refine hW2M.trans ?_
      rw [Mdata.K_eq_MF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer Mdata.M
    -- `W₂` acts fixed-point-freely on `K` (Frobenius complement on the kernel).
    have hfpfK : ∀ a ∈ hyp.base.W2, a ≠ 1 → ∀ u ∈ Mdata.K, u ≠ 1 → a * u * a⁻¹ ≠ u := by
      intro a ha ha_ne u hu hu_ne
      refine isFrobeniusGroup_conj_ne_of_mem_map_complement frob.frobenius
        frob.typeI.typeF.H_le (hW2E ha) ha_ne ?_ hu_ne
      rw [← hKeq]; exact hu
    -- `k ≡ 1 (mod p)` and `v ≡ 1 (mod p)` (`W₂` fpf on `K` and on `V ≤ K`).
    have hkmod : Mdata.k ≡ 1 [MOD hyp.base.p] := by
      rw [Mdata.k_eq_card_K]
      exact card_modEq_one_of_prime_normalizing_fpf hyp.base.p_prime hW2card hW2normK hfpfK
    have hvmod : hyp.base.v ≡ 1 [MOD hyp.base.p] := by
      rw [← hVcard]
      refine card_modEq_one_of_prime_normalizing_fpf hyp.base.p_prime hW2card
        hyp.base.W2_normalizes_V ?_
      intro a ha ha_ne u hu hu_ne
      exact hfpfK a ha ha_ne u (hVK hu) hu_ne
    refine ⟨x, hkx, ?_, ?_⟩
    · -- `x ≡ 1 (mod p)`: from `v x = k ≡ 1` and `v ≡ 1`.
      have hvx1 : hyp.base.v * x ≡ 1 [MOD hyp.base.p] := hkx ▸ hkmod
      have hvxx : hyp.base.v * x ≡ x [MOD hyp.base.p] := by simpa using hvmod.mul_right x
      exact hvxx.symm.trans hvx1
    · -- `x ≠ 1`: if `x = 1` then `k = v`, so `|K| = |V|` with `V ≤ K`, forcing `V = K` (⊥ `K ≠ V`).
      intro hx1
      have hkv : Mdata.k = hyp.base.v := by rw [hkx, hx1, Nat.mul_one]
      have hKcardV : Nat.card ↥Mdata.K = Nat.card ↥hyp.base.V := by
        rw [← Mdata.k_eq_card_K, hkv, hVcard]
      exact hne (Subgroup.eq_of_le_of_card_ge hVK (le_of_eq hKcardV)).symm
  have hk : Mdata.k > 2 * hyp.base.p * hyp.base.v := by
    obtain ⟨x, hkx, hxmod, hxne⟩ := hstruct
    have hk_odd : Odd Mdata.k := by
      rw [Mdata.k_eq_card_K]
      exact _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Mdata.K)
    have hvx_odd : Odd (hyp.base.v * x) := hkx ▸ hk_odd
    have hx_odd : Odd x := (Nat.odd_mul.mp hvx_odd).2
    have hv_pos : 0 < hyp.base.v := by rcases (Nat.odd_mul.mp hvx_odd).1 with ⟨r, hr⟩; omega
    have hx_ge : 2 * hyp.base.p + 1 ≤ x :=
      two_mul_add_one_le_of_modEq_one_odd hyp.base.p_odd hyp.base.p_prime.two_le hxmod hx_odd hxne
    have hle : hyp.base.v * (2 * hyp.base.p + 1) ≤ hyp.base.v * x := by gcongr
    have hexpand : hyp.base.v * (2 * hyp.base.p + 1)
        = 2 * hyp.base.p * hyp.base.v + hyp.base.v := by ring
    rw [hkx]; omega
  refine ⟨hk, ?_⟩
  -- The quotient bound `(k−1)/e ≥ (v−1)/p` is pure arithmetic from `k > 2pv`, `q < p`, `e = pq`:
  -- `q(v−1) ≤ qv ≤ 2pv ≤ k−1`, so `(v−1)/p ≤ (k−1)/(pq)`.
  have he : Mdata.e = hyp.base.p * hyp.base.q := Mdata.complement_card_eq_pq
  have hNat : hyp.base.q * (hyp.base.v - 1) ≤ Mdata.k - 1 := by
    have hb : 2 * hyp.base.p * hyp.base.v ≤ Mdata.k - 1 := Nat.le_sub_one_of_lt hk
    have ha : hyp.base.q * (hyp.base.v - 1) ≤ 2 * hyp.base.p * hyp.base.v := by
      calc hyp.base.q * (hyp.base.v - 1) ≤ hyp.base.q * hyp.base.v := by gcongr; omega
        _ ≤ 2 * hyp.base.p * hyp.base.v := by gcongr; omega
    exact le_trans ha hb
  rw [he, ge_iff_le]
  have hppos : (0 : ℚ) < hyp.base.p := by exact_mod_cast hyp.base.p_prime.pos
  have hqpos : (0 : ℚ) < hyp.base.q := by exact_mod_cast hyp.base.q_prime.pos
  have hpqpos : (0 : ℚ) < ((hyp.base.p * hyp.base.q : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos hyp.base.p_prime.pos hyp.base.q_prime.pos
  rw [div_le_div_iff₀ hppos hpqpos]
  have hNatQ : (hyp.base.q : ℚ) * ((hyp.base.v - 1 : ℕ) : ℚ) ≤ ((Mdata.k - 1 : ℕ) : ℚ) := by
    exact_mod_cast hNat
  push_cast
  nlinarith [hNatQ, hppos, hqpos]

/-- **Peterfalvi (14.11.1)**: if `K != V`, then `k` is large and the quotient
bound dominates `(v - 1) / p`.

The third conjunct `(v − 1) / p > (u − 1) / q` is now a genuine proof: it is the arithmetic
ratio comparison `key_ratio_inequality_of_caseB_data` (14.8), fed by the (14.4)/(14.6) case-(9.7.b)
cyclotomic data.  The two structural bounds remain the named §13/§14 obligation
`main_size_bounds_structural`. -/
theorem main_size_bounds [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hyp
  obtain ⟨Tdata, _⟩ := caseB_for_T _hG hyp
  obtain ⟨Sdata, _⟩ := caseB_for_S _hG hyp Ldata
  obtain ⟨hk, hke⟩ := main_size_bounds_structural _hG hyp Mdata hne
  exact ⟨hk, hke, key_ratio_inequality_of_caseB_data Tdata Sdata⟩

/-- **Arithmetic core of Peterfalvi (14.11.2)**: an integer grid of *odd* Dade-isometry
coefficients whose squares sum to at most `e − 1`, with `e ≤ |grid| + 1`, forces `e = |grid| + 1`
and every coefficient `= ±1`.

The Dade parities (13.19.c / 7.8 / 3.7) make each pairing coefficient `a_ij = ⟨β_M^τ, η_ij⟩` an
*odd* integer, so `a_ij² ≥ 1`; the isometry norm bound gives `∑ a_ij² ≤ e − 1`; and `e ≤ pq`
(here `|grid| = pq − 1`, the non-principal η's, so `e ≤ |grid| + 1`).  Sandwiching
`|grid| ≤ ∑ a_ij² ≤ e − 1 ≤ |grid|` collapses every inequality: `e = pq` and each `a_ij² = 1`,
i.e. `a_ij = ±1`.  Stated generically over a `Fintype` (`|grid| = Fintype.card ι`); the η-grid
specialization indexes by the non-principal characters. -/
theorem all_pm_one_and_card_of_odd_sq_sum_le {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (e : ℕ)
    (hodd : ∀ i, Odd (a i))
    (hsq : ∑ i, (a i) ^ 2 ≤ (e : ℤ) - 1)
    (he : (e : ℤ) ≤ (Fintype.card ι : ℤ) + 1) :
    (e : ℤ) = (Fintype.card ι : ℤ) + 1 ∧ ∀ i, a i = 1 ∨ a i = -1 := by
  -- Each `a_i² ≥ 1` (odd ⟹ nonzero).
  have hge1 : ∀ i, (1 : ℤ) ≤ (a i) ^ 2 := by
    intro i
    have h0 : a i ≠ 0 := by rcases hodd i with ⟨m, hm⟩; omega
    nlinarith [Int.one_le_abs h0, sq_abs (a i)]
  -- `card ≤ ∑ a_i²`, so the sandwich `card ≤ ∑ a_i² ≤ e − 1 ≤ card` pins everything.
  have hsum_ge : (Fintype.card ι : ℤ) ≤ ∑ i, (a i) ^ 2 := by
    calc (Fintype.card ι : ℤ) = ∑ _i : ι, (1 : ℤ) := by
          rw [Finset.sum_const, Finset.card_univ]; ring
      _ ≤ ∑ i, (a i) ^ 2 := Finset.sum_le_sum (fun i _ => hge1 i)
  refine ⟨by omega, ?_⟩
  have hsum_eq : ∑ i, (a i) ^ 2 = (Fintype.card ι : ℤ) := by omega
  -- `∑ (a_i² − 1) = 0` with each summand `≥ 0` ⟹ each `a_i² = 1` ⟹ `a_i = ±1`.
  have heach : ∀ i, (a i) ^ 2 = 1 := by
    have hz : ∑ i, ((a i) ^ 2 - 1) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hsum_eq]; ring
    have hnn : ∀ i ∈ (Finset.univ : Finset ι), (0 : ℤ) ≤ (a i) ^ 2 - 1 :=
      fun i _ => by linarith [hge1 i]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz
    intro i; have := hall i (Finset.mem_univ i); linarith
  intro i
  have hfac : (a i - 1) * (a i + 1) = 0 := by nlinarith [heach i]
  rcases mul_eq_zero.mp hfac with h | h
  · left; linarith
  · right; linarith

/-- **Faithful §7/§3 Dade carrier for the `β_M` expansion of Peterfalvi (14.11.2).**

This is the `M`-instance of the (7.8) Dade-coherence decomposition specialised to the `η`-grid,
isolating the genuine character-theoretic content of (14.11.2) away from the pure algebra:

* `betaM_seven_eight` — **Peterfalvi (7.8.a)** for `M`: `β_M^τ = 1_G − χ + Δ`, the Dade-isometry
  image of `β_M = Ind_K^M 1_K − ψ` decomposed against the principal character `1_G` and the removed
  unit-norm coherent image `χ` (`= ψ^{τ₁}` or `−ψ̄^{τ₁}`, recorded only through the
  branch-independent `chi_norm`).  In the `χ = ψ^{τ₁} = ζ^ν` branch this is exactly the `M`-instance
  of `S09.Hypothesis78.beta_eq_constOne_sub_zetaImage_add_delta` (`β = 1_G − ζ^ν + Δ`); see the
  bridge lemma `betaMExpansionData_of_hypothesis78` below.
* `grid_eq` — **Peterfalvi (13.1.d)/(7.8.b)** `η`-grid identification: `1_G + Δ = Σ_{ij} ε_ij η_ij`.
  The principal `η₀₀` carries the `1_G`, the off-principal grid realizes the residual `Δ`, and the
  `±1` signs come from the Dade congruence `a_ij ≡ 1 (mod 2)` (13.19.c / 7.8.c) with
  `Σ a_ij² ≤ e − 1` and `e = p q` (`all_pm_one_and_card_of_odd_sq_sum_le`).

All fields are genuine facts about the type-I maximal subgroup `M` (its Dade isometry and coherent
extension exist by the §3/§4/§5 machinery); their concrete construction is the remaining §3/§4
Dade-isometry obligation.  Cf. `EtaGenericData` for the dual generic-set carrier. -/
structure BetaMExpansionData (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  /-- The residual `Δ` of the (7.8.a) Dade expansion `β_M = 1_G − χ + Δ`. -/
  delta : ClassFunction G ℂ
  /-- The removed unit-norm character `χ` (`= ψ^{τ₁}` or `−ψ̄^{τ₁}`). -/
  chi : ClassFunction G ℂ
  /-- `χ` has the same pointwise absolute value as `ψ^{τ₁}` (holds for both branches, since
  `|z| = |z̄|`) — exactly what (14.11.3) consumes. -/
  chi_norm : ∀ g : G, ‖chi g‖ = ‖(Mdata.tau1 Mdata.psi) g‖
  /-- **Peterfalvi (7.8.a)** for `M`: `β_M^τ = 1_G − χ + Δ`. -/
  betaM_seven_eight :
    Mdata.betaM = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G - chi + delta
  /-- The `±1` signs of the `η`-grid expansion. -/
  signs : Fin hyp.base.q → Fin hyp.base.p → ℤ
  signs_pm_one : ∀ i j, signs i j = 1 ∨ signs i j = -1
  /-- **Peterfalvi (13.1.d)/(7.8.b)** `η`-grid identification: `1_G + Δ = Σ_{ij} ε_ij η_ij`. -/
  grid_eq :
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + delta =
      ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (signs i j : ℂ) • hyp.base.eta i j

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §3/§7 Dade producer for (14.11.2).**  Under `K ≠ V`, the type-I maximal subgroup `M`
carries the (7.8) Dade-coherence decomposition `BetaMExpansionData` of `β_M^τ` against the `η`-grid.
The construction is the §3/§4 Dade-isometry layer (the abstract §16 `τ`/`τ₁`/`betaM` carriers do not
yet pin it); see the bridge lemma `betaMExpansionData_of_hypothesis78`, which reduces this to a
concrete `S09.Hypothesis78` for `M` plus the `η`-grid identification (3.9)/(13.1.d). -/
noncomputable def betaM_expansion_data [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) (_hne : Mdata.K ≠ hyp.base.V) :
    BetaMExpansionData hyp Mdata where
  delta := Mdata.h78.delta
  chi := Mdata.tau1 Mdata.psi
  chi_norm := fun _ => rfl
  betaM_seven_eight := by
    rw [Mdata.betaM_eq, Mdata.h78.beta_eq_constOne_sub_zetaImage_add_delta, Mdata.psi_tau1_eq]
  signs := Mdata.betaSigns
  signs_pm_one := Mdata.betaSigns_pm
  grid_eq := Mdata.betaGrid

/-- **§16 → §7 bridge for the `β_M` (7.8.a) decomposition.**  Given a concrete `S09.Hypothesis78`
for `M` whose Dade image `β` and coherent image `ζ^ν` are identified with the abstract §16 carriers
`β_M` and `ψ^{τ₁}`, the (7.8.a) field of `BetaMExpansionData` is exactly the `M`-instance of
`S09.Hypothesis78.beta_eq_constOne_sub_zetaImage_add_delta` (`β = 1_G − ζ^ν + Δ`).

This reduces the `betaM_expansion_data` obligation to (i) `M` instantiating `S09.Hypothesis78` with
`β_M = β` and `ψ^{τ₁} = ζ^ν`, and (ii) the `η`-grid identification `1_G + Δ = Σ ε_ij η_ij`
(3.9)/(13.1.d) — the genuine §3/§4 Dade content — and certifies that the (7.8.a) rearrangement is a
real S09 consequence, not an independent assumption.  The `χ = ζ^ν = ψ^{τ₁}` branch; `chi_norm` is
then `rfl`.  Axiom-clean. -/
noncomputable def betaMExpansionData_of_hypothesis78 [Finite G]
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    {A : Set G} [Fintype G] [Fintype ↥Mdata.M]
    [Invertible (Nat.card ↥Mdata.M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A Mdata.M)
    (hbeta : Mdata.betaM = H78.beta)
    (hchi : Mdata.tau1 Mdata.psi = H78.nu (H78.hyp76.zeta H78.zetaDistinct))
    (signs : Fin hyp.base.q → Fin hyp.base.p → ℤ)
    (hsigns : ∀ i j, signs i j = 1 ∨ signs i j = -1)
    (hgrid : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + H78.delta =
      ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (signs i j : ℂ) • hyp.base.eta i j) :
    BetaMExpansionData hyp Mdata where
  delta := H78.delta
  chi := Mdata.tau1 Mdata.psi
  chi_norm := fun _ => rfl
  betaM_seven_eight := by
    rw [hbeta, H78.beta_eq_constOne_sub_zetaImage_add_delta, hchi]
  signs := signs
  signs_pm_one := hsigns
  grid_eq := hgrid

/-- **Peterfalvi (14.11.2)**: under `K ≠ V`, `e = p q` and `β_M^τ` is a signed sum of the
`η_ij` grid with one unit-norm character `χ` removed:
`β_M^τ = Σ_{0≤i<q, 0≤j<p} (±η_ij) − χ`, where `χ = ψ^{τ₁}` or `−ψ̄^{τ₁}`.

De-opacified (W4 §16→§7 bridge, lane-h): the `e = p q` half is the structural field
`MHypothesis.complement_card_eq_pq` (Pf (14.11)), and the `η`-grid expansion is the pure-algebra
rearrangement of the faithful `BetaMExpansionData` (7.8.a) decomposition `β_M = 1_G − χ + Δ`
together with the `η`-grid identification `1_G + Δ = Σ ε_ij η_ij`.  The genuine character theory
(the (7.8) Dade decomposition for `M`) is confined to `betaM_expansion_data`. -/
theorem betaM_expansion [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.e = hyp.base.p * hyp.base.q ∧
      ∃ ε : Fin hyp.base.q → Fin hyp.base.p → ℤ,
        (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
        ∃ χ : ClassFunction G ℂ,
          (∀ g : G, ‖χ g‖ = ‖(Mdata.tau1 Mdata.psi) g‖) ∧
          Mdata.betaM =
            (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
              (ε i j : ℂ) • hyp.base.eta i j) - χ := by
  refine ⟨Mdata.complement_card_eq_pq, ?_⟩
  obtain ⟨delta, chi, hchi_norm, hbeta, signs, hsigns, hgrid⟩ :=
    betaM_expansion_data _hG hyp Mdata hne
  refine ⟨signs, hsigns, chi, hchi_norm, ?_⟩
  rw [hbeta, ← hgrid]
  abel

/-- **Parity core of Peterfalvi (3.9)/(14.11.3)**: a `±1`-signed sum of an integer-valued grid
that pairs under a conjugation involution has complex norm `≥ 1`.

Concretely, let `n : ι → ℤ` be constant on the orbits of an involution `ρ` whose *unique* fixed
point `i₀` carries the principal value `n i₀ = 1`, and let `ε : ι → ℤ` take values in `{±1}`.  Then
the signed sum `∑ ε_i n_i` is an **odd** integer — the `ρ`-paired off-principal terms contribute an
even total (`n` is `ρ`-invariant, so each pair sums to `2 n_i`), while the fixed point contributes
`±1` — so its image in `ℂ` has norm `≥ 1`.

This is the arithmetic heart of (14.11.3): on a generic element `g`, the η-grid values `η_ij(g)`
are rational integers (3.9.c) that pair under the conjugation `(i,j) ↦ (−i,−j)` with the single
principal value `η₀₀(g) = 1` (3.9.a); combined with the (14.11.2) expansion
`ψ^{τ₁}(g) = ±∑ ε_ij η_ij(g)` (valid on `G_0`, where `β_M^τ(g) = 0`) this forces
`|ψ^{τ₁}(g)| ≥ 1`.  Stated generically over a `Fintype` so it serves both the (14.11.3) bound and
the dual (14.16) parity contradiction. -/
theorem one_le_norm_signed_paired_sum {ι : Type*} [Fintype ι]
    (n ε : ι → ℤ) (ρ : Equiv.Perm ι) (i₀ : ι)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hρ : Function.Involutive ρ)
    (hfix : ∀ i, ρ i = i ↔ i = i₀)
    (hpair : ∀ i, n (ρ i) = n i)
    (hn0 : n i₀ = 1) :
    1 ≤ ‖(∑ i, (ε i : ℂ) * (n i : ℂ))‖ := by
  classical
  have hcast : (∑ i, (ε i : ℂ) * (n i : ℂ)) = ((∑ i, ε i * n i : ℤ) : ℂ) := by
    push_cast; rfl
  rw [hcast, Complex.norm_intCast]
  -- Off-principal terms sum to an even integer (fixed-point-free involution on `univ ∖ {i₀}`).
  have heven_erase : (2 : ℤ) ∣ ∑ i ∈ Finset.univ.erase i₀, n i := by
    have hz : ((∑ i ∈ Finset.univ.erase i₀, n i : ℤ) : ZMod 2) = 0 := by
      push_cast
      refine Finset.sum_involution (fun a _ => ρ a) ?_ ?_ ?_ ?_
      · intro a _
        rw [hpair a]; exact CharTwo.add_self_eq_zero _
      · intro a ha _ hcontra
        exact (Finset.mem_erase.mp ha).1 ((hfix a).mp hcontra)
      · intro a ha
        rw [Finset.mem_erase] at ha ⊢
        refine ⟨fun hcontra => ha.1 ?_, Finset.mem_univ _⟩
        change ρ a = i₀ at hcontra
        calc a = ρ (ρ a) := (hρ a).symm
          _ = ρ i₀ := by rw [hcontra]
          _ = i₀ := (hfix i₀).mpr rfl
      · intro a _; exact hρ a
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz
  -- Each sign satisfies `ε_i ≡ 1 (mod 2)`, so `∑ ε_i n_i ≡ ∑ n_i (mod 2)`.
  have hdiff : (2 : ℤ) ∣ (∑ i, ε i * n i) - (∑ i, n i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum (fun i _ => ?_)
    have hrw : ε i * n i - n i = (ε i - 1) * n i := by ring
    rw [hrw]
    exact Dvd.dvd.mul_right (by rcases hε i with h | h <;> rw [h] <;> norm_num) (n i)
  have hsum_n : ∑ i, n i = (∑ i ∈ Finset.univ.erase i₀, n i) + n i₀ :=
    (Finset.sum_erase_add Finset.univ n (Finset.mem_univ i₀)).symm
  have hodd_n : Odd (∑ i, n i) := by
    rw [hsum_n, hn0]
    rcases heven_erase with ⟨c, hc⟩
    exact ⟨c, by rw [hc]⟩
  have hodd : Odd (∑ i, ε i * n i) := by
    rcases hdiff with ⟨d, hd⟩
    rcases hodd_n with ⟨m, hm⟩
    refine ⟨d + m, ?_⟩
    have hA : ∑ i, ε i * n i = (∑ i, n i) + 2 * d := by omega
    rw [hA, hm]; ring
  rcases hodd with ⟨m, hm⟩
  rw [hm, ← Int.cast_abs]
  have hh : (1 : ℤ) ≤ |2 * m + 1| := by
    rcases abs_cases (2 * m + 1 : ℤ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> omega
  exact_mod_cast hh

/-- Negation `i ↦ -i ≡ (n − i) (mod n)` on `Fin n`, for `0 < n`.  This is the index map
realizing the conjugation pairing `(i,j) ↦ (−i,−j)` of the Dade `η`-grid in (3.9.a)/(14.11.3). -/
def finNeg {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(n - i.val) % n, Nat.mod_lt _ hn⟩

@[simp] theorem finNeg_val {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (finNeg hn i).val = (n - i.val) % n := rfl

theorem finNeg_involutive {n : ℕ} (hn : 0 < n) : Function.Involutive (finNeg hn) := by
  intro i
  apply Fin.ext
  rw [finNeg_val, finNeg_val]
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
  · have hlt : i.val < n := i.isLt
    have h1 : (n - i.val) % n = n - i.val := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have h2 : n - (n - i.val) = i.val := by omega
    rw [h2, Nat.mod_eq_of_lt hlt]

theorem finNeg_eq_self_iff {n : ℕ} (hn : 0 < n) (hodd : Odd n) (i : Fin n) :
    finNeg hn i = i ↔ i = ⟨0, hn⟩ := by
  rw [Fin.ext_iff, Fin.ext_iff, finNeg_val]
  show (n - i.val) % n = i.val ↔ i.val = 0
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · exact h0
    · have hlt : i.val < n := i.isLt
      have h1 : (n - i.val) % n = n - i.val := Nat.mod_eq_of_lt (by omega)
      rw [h1] at h
      rcases hodd with ⟨k, hk⟩
      omega
  · intro h
    rw [h, Nat.sub_zero, Nat.mod_self]

/-- **Arithmetic core of Peterfalvi (14.11.3), specialised to the `η`-grid.**  An integer-valued
`q × p` grid `n` that pairs under the conjugation `(i,j) ↦ (−i,−j)` (`finNeg`) with principal value
`n₀₀ = 1`, summed against a `±1`-sign grid `ε`, has complex norm `≥ 1`.

This packages the conjugation involution `(i,j) ↦ (−i,−j)` on `Fin q × Fin p` (whose unique fixed
point is `(0,0)`, since `q`, `p` are odd) and feeds it to `one_le_norm_signed_paired_sum`.  It is the
exact arithmetic consumed by `generic_character_bound` (14.11.3) and the dual (14.16) parity
contradiction once the `(3.9)` integrality/pairing facts of the `η`-grid are supplied. -/
theorem one_le_norm_eta_grid_signed_sum {q p : ℕ} (hq : 0 < q) (hp : 0 < p)
    (hqodd : Odd q) (hpodd : Odd p) (n ε : Fin q → Fin p → ℤ)
    (hε : ∀ i j, ε i j = 1 ∨ ε i j = -1)
    (hpair : ∀ i j, n (finNeg hq i) (finNeg hp j) = n i j)
    (h00 : n ⟨0, hq⟩ ⟨0, hp⟩ = 1) :
    1 ≤ ‖(∑ i : Fin q, ∑ j : Fin p, (ε i j : ℂ) * (n i j : ℂ))‖ := by
  classical
  have hinv : Function.Involutive
      (fun x : Fin q × Fin p => (finNeg hq x.1, finNeg hp x.2)) := by
    intro x
    show (finNeg hq (finNeg hq x.1), finNeg hp (finNeg hp x.2)) = x
    rw [finNeg_involutive hq x.1, finNeg_involutive hp x.2]
  have key := one_le_norm_signed_paired_sum
    (fun x : Fin q × Fin p => n x.1 x.2) (fun x => ε x.1 x.2)
    hinv.toPerm (⟨0, hq⟩, ⟨0, hp⟩) (fun x => hε x.1 x.2)
    (by rw [Function.Involutive.coe_toPerm]; exact hinv)
    (by
      intro x
      rw [Function.Involutive.coe_toPerm]
      constructor
      · intro h
        have h1 : finNeg hq x.1 = x.1 := (Prod.ext_iff.mp h).1
        have h2 : finNeg hp x.2 = x.2 := (Prod.ext_iff.mp h).2
        exact Prod.ext ((finNeg_eq_self_iff hq hqodd x.1).mp h1)
          ((finNeg_eq_self_iff hp hpodd x.2).mp h2)
      · intro h
        rw [h]
        exact Prod.ext ((finNeg_eq_self_iff hq hqodd _).mpr rfl)
          ((finNeg_eq_self_iff hp hpodd _).mpr rfl))
    (by intro x; rw [Function.Involutive.coe_toPerm]; exact hpair x.1 x.2)
    h00
  have hsum : (∑ i : Fin q, ∑ j : Fin p, (ε i j : ℂ) * (n i j : ℂ))
      = ∑ x : Fin q × Fin p, (ε x.1 x.2 : ℂ) * (n x.1 x.2 : ℂ) := by
    rw [Fintype.sum_prod_type]
  rw [hsum]
  exact key

/-- Pointwise evaluation of a finite sum of class functions: `(∑ i ∈ s, f i) g = ∑ i ∈ s, f i g`.
General-purpose `ClassFunction` plumbing (hoistable to `ClassFunction.lean`). -/
theorem classFunction_sum_apply {ι : Type*} {k : Type*} [CommRing k]
    (s : Finset ι) (f : ι → ClassFunction G k) (g : G) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, ClassFunction.add_apply, ih, Finset.sum_insert ha]

/-- **Peterfalvi (14.6)+(13.12), the S-side Frobenius kernel** — `C_{S'}(x) ≤ P` for
`x ∈ P#`.  (14.6) puts `S` in case (9.7.b), whose field model (`FieldNormalizerData`) has
Frobenius kernel `P`; the proven transport `FieldNormalizerData.derived_inf_centralizer_le_P`
then gives the containment.  Named §14 obligation: what remains is the (9.7.b) resolution
for `S` — the (14.2.a)-carrier inputs of `field_normalizer_of_U_characteristic_of_inputs`
(§13 producers `basic_structure`/`c_eq_one`, issue 2035/9000 sphere). -/
theorem s_side_frobenius_kernel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ x ∈ sharpSubgroup hyp.base.P,
      derivedInG hyp.base.S ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.base.P := by
  sorry

/-- **Peterfalvi (14.4)+(13.12), the T-side Frobenius kernel** — `C_{T'}(x) ≤ Q` for
`x ∈ Q#` (dual of `s_side_frobenius_kernel`: (14.4) puts `T` in case (9.7.b), and the
T-side field model has Frobenius kernel `Q`).  Discharge path (engine proven,
`S16_G0Coprime`): supply the minimal (14.4) carrier `TFieldModelData` (injective
`σ : F_{q^p} ⋊ V* →* G` with kernel `Q`, complement `V` — the
`T_side_caseB_facts`/issue-9000 sphere) and apply
`TFieldModelData.derived_inf_centralizer_le_Q`. -/
theorem t_side_frobenius_kernel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ x ∈ sharpSubgroup hyp.base.Q,
      derivedInG hyp.base.T ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.base.Q := by
  sorry

/-- **Peterfalvi (14.11.3), support half**: every element of the generic set `G₀` has order
prime to `pq`.  The avoidance fields of `MHypothesis` (`G0_avoid`) feed the proven
(14.11.3) chain `orderOf_coprime_pq_of_not_mem_conj` (W-orbit bridge + per-side
Sylow/TI/(2.1) coset collapse, `S16_G0Coprime`), with the two case-(9.7.b) Frobenius-kernel
inputs supplied by `s_side_frobenius_kernel`/`t_side_frobenius_kernel`. -/
theorem MHypothesis.G0_orderOf_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) {g : G} (hg : g ∈ Mdata.G0) :
    Nat.Coprime (orderOf g) (hyp.base.p * hyp.base.q) := by
  obtain ⟨hreg, hP, hQ⟩ := Mdata.G0_avoid g hg
  exact orderOf_coprime_pq_of_not_mem_conj hG hyp.base (T_typeII hG hyp)
    (s_side_frobenius_kernel hG hyp) (t_side_frobenius_kernel hG hyp) hreg hP hQ

/-- **Peterfalvi (3.9.a,c) for the `η`-grid on the generic set `G₀`** (faithful §3 Dade obligation).
For `g ∈ G₀` (an element of order prime to `pq` lying outside `Ã(M)`):

* (3.9.c) each grid value `η_ij(g)` is a rational integer (`eta_int`);
* (3.9.a) the grid is invariant under the conjugation `(i,j) ↦ (−i,−j)` (`finNeg`), i.e. the values
  pair up (`eta_pair`), with principal value `η₀₀(g) = 1` (`eta_principal`);
* `β_M^τ(g) = 0`, since `g ∉ Ã(M)` (`betaM_vanish`).

These are the Dade-character integrality/symmetry facts of Peterfalvi (3.9) specialised to the
`M`-grid plus the support vanishing of (14.10); their honest construction lives in the §3/§4
Dade-isometry layer (the abstract §16 `ω`/`η`/`tau3` carriers do not yet pin it). -/
structure EtaGenericData (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  eta_int : ∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
    ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ)
  eta_pair : ∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
    hyp.base.eta (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) g
      = hyp.base.eta i j g
  eta_principal : ∀ g ∈ Mdata.G0,
    hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ g = 1
  betaM_vanish : ∀ g ∈ Mdata.G0, Mdata.betaM g = 0

/-- **Peterfalvi (3.9.a/c), the Galois half of the `η`-grid facts** — the genuine §3/§5
obligation still gated on the `τ₃`-Galois-equivariance (issue 3002 follow-up; the carried
grid primitives determine `η` on `W`-regular values but not its Galois behaviour off `W`):
on the generic set `G₀`, the `η`-grid takes integer values (3.9.c) and pairs under the
negation involution (3.9.a). -/
theorem eta_grid_galois_facts_on_G0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) :
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ)) ∧
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      hyp.base.eta (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) g
        = hyp.base.eta i j g) := by
  -- Now **proven** by citing the issue-3002 keystone fields threaded into `S15.Hypothesis`
  -- by lane b (`eta_intCast_of_coprime` = (3.9.c), `eta_pair_of_coprime` = (3.9.a)), which apply
  -- to every `g` of order coprime to `pq` — and `G₀` elements are exactly such
  -- (`MHypothesis.G0_orderOf_coprime`).
  refine ⟨fun g hg i j => ?_, fun g hg i j => ?_⟩
  · exact hyp.base.eta_intCast_of_coprime g (Mdata.G0_orderOf_coprime hG hg) i j
  · exact hyp.base.eta_pair_of_coprime g (Mdata.G0_orderOf_coprime hG hg) i j

/-- **Peterfalvi (3.9.a/c) `η`-grid facts on `G₀`**: on the generic set `G₀`, the `η`-grid
takes integer values (3.9.c), pairs under the negation involution (3.9.a), and has principal
entry `η₀₀ = 1`.  The principal entry is now genuine (`eta_principal_apply_eq_one`, the
issue-2033 grid-semantics payoff, `S16_GridExpansion`); the Galois half remains the named
obligation `eta_grid_galois_facts_on_G0`. -/
theorem eta_grid_facts_on_G0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ)) ∧
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      hyp.base.eta (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) g
        = hyp.base.eta i j g) ∧
    (∀ g ∈ Mdata.G0,
      hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ g = 1) := by
  obtain ⟨hint, hpair⟩ := eta_grid_galois_facts_on_G0 hG hyp Mdata
  exact ⟨hint, hpair, fun g _ => eta_principal_apply_eq_one hyp.base g⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.9)/(14.10) generic-set producer.**  The `η`-grid integrality/symmetry on `G₀`
(`eta_grid_facts_on_G0`, the §3/§5 grid obligation) together with the **now-genuine** support
vanishing `β_M^τ = 0` on `G₀`: `β_M = β` is a Dade image, so its support lies in `Ã(M)`
(`beta_support_subset_dadeSupport`), while `G₀` avoids `Ã(M)` (`G0_off_dadeSupport`). -/
theorem eta_generic_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    EtaGenericData hyp Mdata := by
  obtain ⟨hint, hpair, hprinc⟩ := eta_grid_facts_on_G0 hG hyp Mdata
  refine { eta_int := hint, eta_pair := hpair, eta_principal := hprinc, betaM_vanish := ?_ }
  -- **Peterfalvi (14.11.3)**: `β_M^τ` vanishes off its Dade support `Ã(M)`, and `G₀ ⊆ G ∖ Ã(M)`.
  intro g hg
  rw [Mdata.betaM_eq]
  by_contra hne
  have hmem := Mdata.h78.beta_support_subset_dadeSupport (Function.mem_support.mpr hne)
  rw [Mdata.h78_hyp_eq] at hmem
  exact Mdata.G0_off_dadeSupport g hg hmem

/-- **Peterfalvi (14.11.3)**: on the generic set `G_0`, the extended character `ψ^{τ₁}` has
absolute value at least one: `|ψ^{τ₁}(g)| ≥ 1` for `g ∈ G_0`.

De-opacified (lane-c §16 char-endpoint): the former opaque carrier field
`generic_bound_formula : G → Prop` is replaced by this concrete inequality on the `ℤ`-linear
Dade extension `τ₁` applied to `ψ`.  Proof recipe (Pf p.89): for `g ∈ G_0`, `β_M^τ(g) = 0` (as
`g ∉ Ã(M)`), so by (14.11.2) `ψ^{τ₁}(g) = ±Σ_{i,j}(±η_ij(g))`; `g` has order prime to `pq`, so by
(3.9.c) each `η_ij(g) ∈ ℤ` and by (3.9.a) they pair under conjugation, and `η₀₀(g) = 1`, whence
`Σ(±η_ij(g)) ∈ 2ℤ+1`, giving absolute value `≥ 1`.  Depends on `betaM_expansion` (14.11.2). -/
theorem generic_character_bound [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    ∀ g : G, g ∈ Mdata.G0 → 1 ≤ ‖(Mdata.tau1 Mdata.psi) g‖ := by
  classical
  -- (14.11.2): the signed `η`-grid expansion of `β_M^τ`.
  obtain ⟨_he, ε, hε, χ, hχnorm, hexp⟩ := betaM_expansion _hG hyp Mdata hne
  -- (3.9)/(14.10): the `η`-grid is integral and conjugation-symmetric on `G₀`, and `β_M^τ`
  -- vanishes there.
  have hdata := eta_generic_data _hG hyp Mdata
  intro g hg
  -- (3.9.c) integer values of the `η`-grid at `g`.
  choose n hn using hdata.eta_int g hg
  -- Evaluate the (14.11.2) expansion at `g` pointwise.
  have happ : Mdata.betaM g
      = (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
          (ε i j : ℂ) * (hyp.base.eta i j g)) - χ g := by
    rw [hexp, ClassFunction.sub_apply, classFunction_sum_apply]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [classFunction_sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ClassFunction.smul_apply]
  -- `β_M^τ(g) = 0` gives `χ(g) = Σ ε_ij η_ij(g) = Σ ε_ij (n_ij : ℂ)`.
  have hχ2 : χ g = ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (ε i j : ℂ) * (n i j : ℂ) := by
    have h0 : (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
        (ε i j : ℂ) * (hyp.base.eta i j g)) - χ g = 0 := by
      rw [← happ]; exact hdata.betaM_vanish g hg
    rw [(sub_eq_zero.mp h0).symm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hn i j]
  -- (3.9.a) the integer grid pairs under negation with principal value `1`.
  have hpair : ∀ i j,
      n (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) = n i j := by
    intro i j
    have he := hdata.eta_pair g hg i j
    rw [hn, hn] at he
    exact_mod_cast he
  have h00 : n ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ = 1 := by
    have he := hdata.eta_principal g hg
    rw [hn] at he
    exact_mod_cast he
  -- The signed paired sum has norm `≥ 1` (14.11.3 arithmetic core), and `‖χ‖ = ‖ψ^{τ₁}‖`.
  calc (1 : ℝ)
      ≤ ‖∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (ε i j : ℂ) * (n i j : ℂ)‖ :=
        one_le_norm_eta_grid_signed_sum hyp.base.q_prime.pos hyp.base.p_prime.pos
          hyp.base.q_odd hyp.base.p_odd n ε hε hpair h00
    _ = ‖χ g‖ := by rw [hχ2]
    _ = ‖(Mdata.tau1 Mdata.psi) g‖ := hχnorm g

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), line-83 upper-bound step** — the V-side `M`-analogue of
`S12.Hypothesis.chiRhoNormSq_zeta_le_line83`.  Applying the family inequality (7.5)
`S09.family_inequality` to the norm-one character `ψ^{τ₁}` (`psi_tau1_norm_one`) and dropping the
`G₀`-part of the sum via (14.11.3) `generic_character_bound` (`|ψ^{τ₁}(g)| ≥ 1` on `G₀`) together
with the inclusion `G₀ ⊆ famG₀` (`G0_off_dadeSupport`) gives
`‖ψ^{τ₁ρ}‖² ≤ |A(M)|/|M| + (1/|G|)(|famG₀| − |G₀|)`.

This is the first step of (14.11.4)'s upper bound; the remaining passage to the displayed
`1 − 1/p − 1/q + …` is the `|K#|/|M|` evaluation and the §8 TI-counting of the `(W#)^G`/`(P#)^G`/
`(Q#)^G` contributions, isolated for the cascade producer `normCascadeData`.  `famG₀ =
(toFamilyHypothesis71).G0 = G − Ã(M)` and `G₀ = Mdata.G0`. -/
theorem MHypothesis.chiRhoNormSq_psi_le_line83 [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0
      ≤ (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
          / (Nat.card ↥Mdata.M : ℝ)
        + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
          - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)) := by
  haveI := Mdata.finiteG
  have hA0 : (Mdata.toFamilyHypothesis71).A 0
      = OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI := rfl
  have hL0 : (Mdata.toFamilyHypothesis71).L 0 = Mdata.M := rfl
  -- (7.5) line 81 (single member, `k = 1`).
  have h81 := OddOrder.Peterfalvi.S09.family_inequality (Mdata.toFamilyHypothesis71)
    (Mdata.tau1 Mdata.psi) Mdata.psi_tau1_norm_one
  rw [Fin.sum_univ_one, hA0, hL0] at h81
  -- `G₀ ⊆ famG₀`: every `g ∈ G₀` is off the Dade support `Ã(M)`.
  have hsub : Finset.univ.filter (fun g : G => g ∈ Mdata.G0)
      ⊆ Finset.univ.filter (fun g : G => g ∈ (Mdata.toFamilyHypothesis71).G0) := by
    intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨Finset.mem_univ g, fun _ => Mdata.G0_off_dadeSupport g hg.2⟩
  -- Drop the `G₀`-part: `|G₀| ≤ Σ_{G₀} ‖ψ^{τ₁}‖² ≤ Σ_{famG₀} ‖ψ^{τ₁}‖²`.
  have hge : ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
      ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ Mdata.G0),
          ‖(Mdata.tau1 Mdata.psi : G → ℂ) g‖ ^ 2 := by
    calc ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
        = ∑ _g ∈ Finset.univ.filter (fun g : G => g ∈ Mdata.G0), (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ Mdata.G0),
            ‖(Mdata.tau1 Mdata.psi : G → ℂ) g‖ ^ 2 := by
          refine Finset.sum_le_sum (fun g hg => ?_)
          have hg2 : g ∈ Mdata.G0 := (Finset.mem_filter.mp hg).2
          have h1 := generic_character_bound _hG hyp Mdata hne g hg2
          nlinarith [h1, norm_nonneg ((Mdata.tau1 Mdata.psi : G → ℂ) g)]
  have hdrop : ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
      ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ (Mdata.toFamilyHypothesis71).G0),
          ‖(Mdata.tau1 Mdata.psi : G → ℂ) g‖ ^ 2 :=
    le_trans hge (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => by positivity))
  have hGinv : (0 : ℝ) ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hcS := mul_le_mul_of_nonneg_left hdrop hGinv
  rw [mul_sub] at h81 ⊢
  linarith [h81, hcS]

/-- **`S09.Hypothesis71.chiRho` depends only on the support hypothesis `H71.hyp`.**  Two `(7.1)`
data with the same underlying `S04.Hypothesis` (the same `H(a)`-family) induce the same `ρ`-image
of any `χ`, even if their chosen Dade maps `τ` differ — `chiRho` never mentions `τ`.  Used to
identify the family-inequality `ρ`-norm of (14.11.4) with the (7.8.b) `ρ`-norm of `h78`. -/
theorem chiRhoCF_congr_hyp [Fintype G] {A : Set G} {L : Subgroup G}
    {H71a H71b : OddOrder.Peterfalvi.S09.Hypothesis71 G A L}
    (h : H71a.hyp = H71b.hyp) (χ : ClassFunction G ℂ) :
    H71a.chiRhoCF χ = H71b.chiRhoCF χ := by
  apply ClassFunction.ext
  intro a
  simp only [OddOrder.Peterfalvi.S09.Hypothesis71.chiRhoCF_apply]
  unfold OddOrder.Peterfalvi.S09.Hypothesis71.chiRho
  rw [h]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4) norm bridge.**  The family-inequality `ρ`-norm of `ψ^{τ₁}` (the LHS of
the line-83 bound) equals the (7.8.b) `ρ`-norm `h78.zetaNuRhoNormSq`.  Both are `‖(ψ^{τ₁})^ρ‖²` for
the `(M, A(M))` map `ρ`: `psi_tau1_eq` (`ψ^{τ₁} = ζ^ν`) matches the characters, and `h78_hyp_eq`
(same Dade support hypothesis) plus `chiRhoCF_congr_hyp` (independence of `chiRho` from `τ`) matches
the `ρ`-images.  This is the linchpin tying the (7.5) family-inequality layer to the (7.8.b)
coherence-norm layer of (14.11.4). -/
theorem MHypothesis.chiRhoNormSq_eq_zetaNuRhoNormSq [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0
      = Mdata.h78.zetaNuRhoNormSq := by
  have hcf : ((Mdata.toFamilyHypothesis71).hyp71 0).chiRhoCF (Mdata.tau1 Mdata.psi)
      = Mdata.h78.zetaNuRho := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRho, Mdata.psi_tau1_eq]
    exact chiRhoCF_congr_hyp Mdata.h78_hyp_eq.symm _
  simp only [OddOrder.Peterfalvi.S09.FamilyHypothesis71.chiRhoNormSq,
    OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRhoNormSq, hcf]
  congr 1

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), the lower bound** `1 − pq/k ≤ ‖ψ^{τ₁ρ}‖²` — the genuine (7.8.b)
coherence-norm content of (14.11.4).  Combines the (7.8.b) lower bound for the coherent type-I `M`
(`h78_zetaNuRho_normSq_ge`) with the index identities `h78.kernelOrder = |K| = k` and
`h78.complementIndex = |M:K| = p q` (`h78_H_eq`, `e_eq_index`, `complement_card_eq_pq`) via the norm
bridge `chiRhoNormSq_eq_zetaNuRhoNormSq`.  This is the `lower` field of the `NormCascadeData`
producer `normCascadeData`; the remaining gate is the upper-bound §8 TI-counting. -/
theorem MHypothesis.rhoNormSq_ge_lower [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    1 - ((hyp.base.p * hyp.base.q : ℕ) : ℝ) / (Mdata.k : ℝ)
      ≤ (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0 := by
  rw [Mdata.chiRhoNormSq_eq_zetaNuRhoNormSq]
  -- `K ≤ M` for the index/card bookkeeping.
  have hKleM : Mdata.K ≤ Mdata.M :=
    Mdata.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le Mdata.M
  -- `h78.kernelOrder = |K| = k`.
  have hko : Mdata.h78.kernelOrder = Mdata.k := by
    rw [Mdata.k_eq_card_K]
    show Nat.card ↥(Mdata.h78.hyp76.H) = Nat.card ↥Mdata.K
    rw [Mdata.h78_H_eq]
  -- `h78.complementIndex = |M:K| = p q`.
  have hci : Mdata.h78.complementIndex = hyp.base.p * hyp.base.q := by
    have hmul := Mdata.h78.kernelOrder_mul_complementIndex_eq_card_L
    rw [hko, Mdata.k_eq_card_K] at hmul
    have hcardK : Nat.card ↥(Mdata.K.subgroupOf Mdata.M) = Nat.card ↥Mdata.K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleM).toEquiv
    have hidx : Nat.card ↥Mdata.K * (Mdata.K.subgroupOf Mdata.M).index = Nat.card ↥Mdata.M := by
      rw [← hcardK]; exact Subgroup.card_mul_index _
    have hidxpq : (Mdata.K.subgroupOf Mdata.M).index = hyp.base.p * hyp.base.q := by
      rw [← Mdata.e_eq_index]; exact Mdata.complement_card_eq_pq
    rw [hidxpq] at hidx
    have hKpos : 0 < Nat.card ↥Mdata.K := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hKpos (hmul.trans hidx.symm)
  -- Rewrite the (7.8.b) carrier into `p q`/`k` and conclude.
  have key := Mdata.h78_zetaNuRho_normSq_ge
  rw [hci, hko] at key
  exact key

/-- **The type-I Dade support is the kernel sharp** `A(M) = K#`, the §8 cardinality input
`|A(M)| = |K#| = k − 1` of Peterfalvi (14.11.4) (Coq `PFsection14`: the `Dade_cover_inequality`
support term `#|A| = k.-1`).  For a Frobenius group `M` with kernel `N` (the complement acts
fixed-point-freely on `N#`), the centralizer-support
`centralizerSupport N# M = {y ∈ M : y ≠ 1, ∃ x ∈ N#, [y,x]=1}` is exactly `N#`: the forward
inclusion is the Frobenius FPF property `centralizer_kernel_le` (`C_M(x) ≤ N` for `x ∈ N#`), the
reverse takes `x = y`.  Applied with `N = K = M_F`, this is `typeIA M = K#`. -/
theorem centralizerSupport_sharpSubgroup_eq_of_frobenius [Finite G] {M N : Subgroup G}
    {C : Subgroup ↥M}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (N.subgroupOf M) C) (hNM : N ≤ M) :
    OddOrder.GroupTheory.centralizerSupport (OddOrder.GroupTheory.sharpSubgroup N) M
      = OddOrder.GroupTheory.sharpSubgroup N := by
  ext y
  simp only [OddOrder.GroupTheory.centralizerSupport, OddOrder.GroupTheory.sharpSubgroup,
    Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyM, hy1, x, ⟨hxN, hx1⟩, hyx⟩
    have hxM : x ∈ M := hNM hxN
    have hxMsub : (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M := (Subgroup.mem_subgroupOf).mpr hxN
    have hx1' : (⟨x, hxM⟩ : ↥M) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hycomm : (⟨y, hyM⟩ : ↥M) ∈ Subgroup.centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyx ⊢
      exact Subtype.ext hyx
    have hyN : (⟨y, hyM⟩ : ↥M) ∈ N.subgroupOf M :=
      hfrob.centralizer_kernel_le _ hxMsub hx1' hycomm
    exact ⟨(Subgroup.mem_subgroupOf).mp hyN, hy1⟩
  · rintro ⟨hyN, hy1⟩
    refine ⟨hNM hyN, hy1, y, ⟨hyN, hy1⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]

/-- **Peterfalvi (14.11.4): `|A(M)| = k − 1`** — the §8 cardinality input of the upper bound.  The
type-I Dade support `A(M) = typeIA M` equals `K#` (`centralizerSupport_sharpSubgroup_eq_of_frobenius`
applied to the Frobenius structure of `M` from `typeI_frobenius` (12.7), kernel `K = M_F`), so its
cardinality is `|K| − 1 = k − 1`. -/
theorem MHypothesis.card_typeIA_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) = Mdata.k - 1 := by
  -- Frobenius witness for `M` (kernel `M_F`), from (12.7).
  obtain ⟨fdata, _⟩ :=
    OddOrder.Peterfalvi.S14.typeI_frobenius hG Mdata.M_maximal ⟨Mdata.typeIHyp.typeI⟩
  -- The two kernels both equal `maxNilpotentNormalHall M`.
  have hKf : fdata.typeI.typeF.H = Mdata.typeIHyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, Mdata.typeIHyp.typeI.typeF.H_eq]
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥Mdata.M
      (Mdata.typeIHyp.typeI.typeF.H.subgroupOf Mdata.M) fdata.complement := hKf ▸ fdata.frobenius
  -- `typeIA M = K#` (FPF support identity).
  have hTI : OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup Mdata.typeIHyp.typeI.typeF.H :=
    centralizerSupport_sharpSubgroup_eq_of_frobenius hfrob Mdata.typeIHyp.typeI.typeF.H_le
  -- `typeF.H = K`, so `|K#| = |K| − 1 = k − 1`.
  have hHK : Mdata.typeIHyp.typeI.typeF.H = Mdata.K := by
    rw [Mdata.typeIHyp.typeI.typeF.H_eq, Mdata.K_eq_MF]
  have hc : Nat.card ↥Mdata.K = ((Mdata.K : Set G)).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  rw [hTI, hHK, Mdata.k_eq_card_K, Nat.card_coe_set_eq, OddOrder.GroupTheory.sharpSubgroup,
    Set.ncard_diff (Set.singleton_subset_iff.mpr Mdata.K.one_mem), Set.ncard_singleton, hc]

/-- **Peterfalvi (14.11): `|M| = p q k`** — the order of the type-I maximal `M`, from
`[M : K] = e = pq` (`e_eq_index`, `complement_card_eq_pq`) and `|K| = k` (`k_eq_card_K`) by Lagrange.
The denominator of the §8 cardinality input `|A(M)|/|M| = (k − 1)/(kpq)` of (14.11.4). -/
theorem MHypothesis.card_M_eq {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Nat.card ↥Mdata.M = hyp.base.p * hyp.base.q * Mdata.k := by
  have hKleM : Mdata.K ≤ Mdata.M :=
    Mdata.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le Mdata.M
  have hcardK : Nat.card ↥(Mdata.K.subgroupOf Mdata.M) = Nat.card ↥Mdata.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleM).toEquiv
  have hidx : Nat.card ↥Mdata.K * (Mdata.K.subgroupOf Mdata.M).index = Nat.card ↥Mdata.M := by
    rw [← hcardK]; exact Subgroup.card_mul_index _
  have hidxpq : (Mdata.K.subgroupOf Mdata.M).index = hyp.base.p * hyp.base.q := by
    rw [← Mdata.e_eq_index]; exact Mdata.complement_card_eq_pq
  rw [hidxpq] at hidx
  rw [← hidx, Mdata.k_eq_card_K]; ring

/-- **The exceptional set `W − (W₁ ∪ W₂)` of a cyclic `W = W₁ × W₂` is a TI-subset with
normalizer-bound `W`** — the abstract core of Peterfalvi's `V`-set TI property, generalising
`S12.typePData_V_ti` to take the singleton/subset normalizer fact `N_G(X) = W` (`hnorm`) directly.
Given `g` conjugating some `a` of the set into it, `N_G({a}) = W = N_G({g a g⁻¹})` forces `g` to
normalize `W`, and cyclic-uniqueness (`cyclic_subgroup_eq_of_card_eq`) makes `W₁`, `W₂`
`g`-stable, so `g` normalizes the set, whence `g ∈ N_G(set) = W`.  The `W`-orbit TI input to the
(14.11.4) §8 count (`hnorm` is the genuine §13 structural fact, supplied from the partner type-`P`
structure). -/
theorem isTISubset_sdiff_sup_of_normalizer_eq [Finite G] {W W1 W2 : Subgroup G}
    (hWcyc : IsCyclic ↥W) (hWeq : W = W1 ⊔ W2)
    (hnorm : ∀ X : Set G, X.Nonempty →
      X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W) :
    OddOrder.GroupTheory.IsTISubset ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) W := by
  classical
  set vset : Set G := (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) with hvset
  haveI : IsCyclic ↥W := hWcyc
  have hW1le : W1 ≤ W := hWeq ▸ le_sup_left
  have hW2le : W2 ≤ W := hWeq ▸ le_sup_right
  have mem_norm_sing : ∀ c z : G,
      z ∈ Subgroup.normalizer ({c} : Set G) ↔ z * c * z⁻¹ = c := by
    intro c z
    rw [Subgroup.mem_set_normalizer_iff]
    constructor
    · intro hz; have := (hz c).mp rfl; simpa using this
    · intro hz h
      simp only [Set.mem_singleton_iff]
      refine ⟨fun hrfl => hrfl ▸ hz, fun hh => ?_⟩
      have hcc : z * h * z⁻¹ = z * c * z⁻¹ := by rw [hh, hz]
      exact mul_left_cancel (mul_right_cancel hcc)
  intro g hg
  obtain ⟨a, haV, hbV⟩ := hg
  have hNa : Subgroup.normalizer ({a} : Set G) = W :=
    hnorm {a} (Set.singleton_nonempty a) (Set.singleton_subset_iff.mpr haV)
  have hNb : Subgroup.normalizer ({g * a * g⁻¹} : Set G) = W :=
    hnorm {g * a * g⁻¹} (Set.singleton_nonempty _) (Set.singleton_subset_iff.mpr hbV)
  have hgW : ∀ h, h ∈ W ↔ g * h * g⁻¹ ∈ W := by
    intro h
    have e1 : (h ∈ W) ↔ h * a * h⁻¹ = a := by rw [← hNa, mem_norm_sing]
    have e2 : (g * h * g⁻¹ ∈ W) ↔ h * a * h⁻¹ = a := by
      rw [← hNb, mem_norm_sing]
      have hexp : g * h * g⁻¹ * (g * a * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by
        group
      rw [hexp]
      exact ⟨fun hh => mul_left_cancel (mul_right_cancel hh), fun hh => by rw [hh]⟩
    rw [e1, e2]
  have hstab : ∀ (A : Subgroup G), A ≤ W → ∀ x : G, g * x * g⁻¹ ∈ A ↔ x ∈ A := by
    intro A hAW
    have hmap_le : A.map (MulAut.conj g).toMonoidHom ≤ W := by
      rintro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hzA, rfl⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (hgW z).mp (hAW hzA)
    have hcard : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = Nat.card ↥A :=
      (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv).symm
    have hsubeq : (A.map (MulAut.conj g).toMonoidHom).subgroupOf W = A.subgroupOf W := by
      apply OddOrder.BG.Ch3.S10.cyclic_subgroup_eq_of_card_eq (C := ↥W)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmap_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv, hcard]
    have hmapeq : A.map (MulAut.conj g).toMonoidHom = A := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hmap_le, hsubeq,
        Subgroup.map_subgroupOf_eq_of_le hAW]
    intro x
    constructor
    · intro hx
      have hmem : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := by rw [hmapeq]; exact hx
      rw [Subgroup.mem_map] at hmem
      obtain ⟨z, hzA, hz⟩ := hmem
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hz
      have hzx : z = x := mul_left_cancel (mul_right_cancel hz)
      rwa [hzx] at hzA
    · intro hx
      have hmem : (MulAut.conj g).toMonoidHom x ∈ A.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hmapeq] at hmem
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  rw [← hnorm vset ⟨a, haV⟩ Set.Subset.rfl, Subgroup.mem_set_normalizer_iff]
  intro h
  simp only [hvset, Set.mem_diff, Set.mem_union, SetLike.mem_coe]
  rw [hgW h, hstab W1 hW1le h, hstab W2 hW2le h]

/-- **`W` stabilises its exceptional set `W − (W₁ ∪ W₂)` under conjugation** — the `hstab` input to
the `W`-orbit count `ncard_conjClassSet_of_isTISubset`/`orbit_normSq_term`, generalising
`S12.typePData_W_normalizes_typePV`.  Every `l ∈ W = N_G(set)` (via `hnorm`) normalizes the set. -/
theorem conj_smul_sdiff_sup_eq_of_normalizer_eq [Finite G] {W W1 W2 : Subgroup G}
    (hnorm : ∀ X : Set G, X.Nonempty →
      X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W)
    (hne : ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).Nonempty) :
    ∀ l ∈ W, MulAut.conj l • ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))
      = (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) := by
  intro l hl
  have hlN : l ∈ Subgroup.normalizer ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) := by
    rw [hnorm _ hne Set.Subset.rfl]; exact hl
  rw [Subgroup.mem_set_normalizer_iff] at hlN
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact (hlN v).mp hv
  · intro hx
    refine ⟨l⁻¹ * x * l, (hlN _).mpr ?_, by group⟩
    rw [show l * (l⁻¹ * x * l) * l⁻¹ = x by group]; exact hx

/-- **Orbit measure of a TI-subset** `|𝒞_G(A)|/|G| = |A|/|N|` — the real-valued form of the §8
TI-counting `ncard_conjClassSet_of_isTISubset` (`|𝒞_G(A)| = |A|·[G:N]`).  For a TI-subset `A` with
normalizer-bound `N` stabilizing `A`, the conjugacy-saturation `𝒞_G(A) = A^G` has relative measure
`|A|/|N|` in `G`.  The reusable bridge turning each (14.11.4) orbit `(W#)^G`/`(P#)^G`/`(Q#)^G` into a
`1/|N_G(·)|`-term (Pf 04.16 lines 109–115). -/
theorem orbit_normSq_term [Finite G] {A : Set G} {L : Subgroup G}
    (hTI : OddOrder.GroupTheory.IsTISubset A L)
    (hstab : ∀ l ∈ L, MulAut.conj l • A = A) :
    ((OddOrder.GroupTheory.conjClassSet A).ncard : ℝ) / (Nat.card G : ℝ)
      = (A.ncard : ℝ) / (Nat.card ↥L : ℝ) := by
  rw [OddOrder.BG.Ch4.S14.ncard_conjClassSet_of_isTISubset hTI hstab, ← L.card_mul_index]
  have hidx : (L.index : ℝ) ≠ 0 := by exact_mod_cast Subgroup.index_ne_zero_of_finite
  push_cast
  rw [mul_div_mul_right _ _ hidx]

/-- **`W`-orbit relative measure** `|(W − (W₁ ∪ W₂))^G|/|G| = |W − (W₁ ∪ W₂)|/|W|` — the assembled
`W`-orbit term of Peterfalvi (14.11.4), combining the TI core
(`isTISubset_sdiff_sup_of_normalizer_eq`), the `W`-stability
(`conj_smul_sdiff_sup_eq_of_normalizer_eq`), and the orbit bridge (`orbit_normSq_term`).  Given the
cyclic structure `W = W₁ × W₂` and the singleton/subset normalizer fact `N_G(X) = W` (`hnorm`). -/
theorem orbit_sdiff_sup_normSq_term [Finite G] {W W1 W2 : Subgroup G}
    (hWcyc : IsCyclic ↥W) (hWeq : W = W1 ⊔ W2)
    (hnorm : ∀ X : Set G, X.Nonempty →
      X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W)
    (hne : ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).Nonempty) :
    ((OddOrder.GroupTheory.conjClassSet
        ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))).ncard : ℝ) / (Nat.card G : ℝ)
      = (((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).ncard : ℝ) / (Nat.card ↥W : ℝ) :=
  orbit_normSq_term (isTISubset_sdiff_sup_of_normalizer_eq hWcyc hWeq hnorm)
    (conj_smul_sdiff_sup_eq_of_normalizer_eq hnorm hne)

/-- **The normalizer of `P` stabilises `P# = P ∖ {1}` under conjugation** — the `hstab` input to the
`P#`-orbit count `orbit_normSq_term`.  For `l ∈ N_G(P)`, conjugation by `l` permutes `P` and fixes
`1`, so it permutes `P#`.  (With `IsTI P` — definitionally `IsTISubset (P ∖ {1}) (N_G(P))` — this
gives `|(P#)^G|/|G| = (|P|−1)/|N_G(P)|`, the `P`/`Q` orbit terms of Peterfalvi (14.11.4).) -/
theorem conj_smul_sharpSubgroup_eq_of_mem_normalizer {P : Subgroup G} {l : G}
    (hl : l ∈ Subgroup.normalizer (P : Set G)) :
    MulAut.conj l • (OddOrder.GroupTheory.sharpSubgroup P)
      = OddOrder.GroupTheory.sharpSubgroup P := by
  rw [Subgroup.mem_set_normalizer_iff] at hl
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply,
    OddOrder.GroupTheory.sharpSubgroup, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, ⟨hvP, hv1⟩, rfl⟩
    refine ⟨(hl v).mp hvP, fun h => hv1 ?_⟩
    have : v = l⁻¹ * (l * v * l⁻¹) * l := by group
    rw [this, h]; group
  · rintro ⟨hxP, hx1⟩
    refine ⟨l⁻¹ * x * l, ⟨(hl _).mpr ?_, fun h => hx1 ?_⟩, by group⟩
    · rw [show l * (l⁻¹ * x * l) * l⁻¹ = x by group]; exact hxP
    · rw [show x = l * (l⁻¹ * x * l) * l⁻¹ by group, h]; group

/-- **`P#`-orbit relative measure** `|(P#)^G|/|G| = |P#|/|N_G(P)|` — the `P`/`Q` orbit term of
Peterfalvi (14.11.4), for a TI-subgroup `P` (`Subgroup.IsTI P`, definitionally
`IsTISubset (P ∖ {1}) (N_G(P))`).  Combines the TI property with the `P#`-stability
(`conj_smul_sharpSubgroup_eq_of_mem_normalizer`) via the orbit bridge `orbit_normSq_term`. -/
theorem orbit_sharpSubgroup_normSq_term [Finite G] {P : Subgroup G} (hTI : Subgroup.IsTI P) :
    ((OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup P)).ncard : ℝ)
        / (Nat.card G : ℝ)
      = ((OddOrder.GroupTheory.sharpSubgroup P).ncard : ℝ)
        / (Nat.card ↥(Subgroup.normalizer (P : Set G)) : ℝ) :=
  orbit_normSq_term hTI (fun _ hl => conj_smul_sharpSubgroup_eq_of_mem_normalizer hl)

/-- **`|P#| + 1 = |P|`** — the cardinality of the sharp subgroup (the `|P| − 1` numerator of the
`P`/`Q` orbit term of (14.11.4)), additive form. -/
theorem ncard_sharpSubgroup_add_one {P : Subgroup G} [Finite ↥P] :
    (OddOrder.GroupTheory.sharpSubgroup P).ncard + 1 = Nat.card ↥P := by
  have hc : Nat.card ↥P = (P : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  rw [hc, OddOrder.GroupTheory.sharpSubgroup, ← Set.ncard_singleton (1 : G),
    Set.ncard_diff_add_ncard_of_subset (Set.singleton_subset_iff.mpr P.one_mem)]

/-- **`|W − (W₁ ∪ W₂)| + |W₁| + |W₂| = |W| + 1`** — the cardinality of the exceptional set, by
inclusion–exclusion with `W₁ ∩ W₂ = {1}` (`hdisj`).  The numerator of the `W`-orbit term
`|W − (W₁ ∪ W₂)|/|W|` of Peterfalvi (14.11.4) (additive form, avoiding `ℕ`-truncation). -/
theorem ncard_sdiff_sup_add_eq [Finite G] {W W1 W2 : Subgroup G}
    (hW1le : W1 ≤ W) (hW2le : W2 ≤ W) (hdisj : W1 ⊓ W2 = ⊥) :
    ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).ncard + Nat.card ↥W1 + Nat.card ↥W2
      = Nat.card ↥W + 1 := by
  have hsub : ((W1 : Set G) ∪ (W2 : Set G)) ⊆ (W : Set G) :=
    Set.union_subset (SetLike.coe_subset_coe.mpr hW1le) (SetLike.coe_subset_coe.mpr hW2le)
  have h1 := Set.ncard_diff_add_ncard_of_subset hsub
  have h2 := Set.ncard_union_add_ncard_inter (W1 : Set G) (W2 : Set G)
  have h3 : ((W1 : Set G) ∩ (W2 : Set G)).ncard = 1 := by
    rw [← Subgroup.coe_inf, hdisj, Subgroup.coe_bot, Set.ncard_singleton]
  have hcW : Nat.card ↥W = (W : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  have hcW1 : Nat.card ↥W1 = (W1 : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  have hcW2 : Nat.card ↥W2 = (W2 : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  rw [hcW, hcW1, hcW2]
  omega

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), the `G₀`-drop set reduction** — `|famG₀| − |G₀| ≤ |(W−(W₁∪W₂))^G| +
|(P#)^G| + |(Q#)^G|` (as `ncard`s).  Since `G₀ ⊆ famG₀` (`G0_off_dadeSupport`) and `famG₀ ∖ G₀` is
covered by the three orbits (`G0_orbit_cover`, the (14.11.3) `G₀ = G − [Ã(M) ∪ orbits]`), the
difference is bounded by the orbit cardinalities (`Set.ncard_diff` + `Set.ncard_union_le`).  The
set-theoretic core of the (14.11.4) §8 TI-counting, feeding `orbit_normSq_term` per orbit. -/
theorem MHypothesis.famG0_sub_filter_card_le_orbit_ncard [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    (Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
      ≤ ((OddOrder.GroupTheory.conjClassSet
            ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))).ncard : ℝ)
        + ((OddOrder.GroupTheory.conjClassSet
            (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)).ncard : ℝ)
        + ((OddOrder.GroupTheory.conjClassSet
            (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)).ncard : ℝ) := by
  classical
  haveI := Mdata.finiteG
  set famG0 := (Mdata.toFamilyHypothesis71).G0 with hfamdef
  set Worb := OddOrder.GroupTheory.conjClassSet
    ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
  set Porb := OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)
  set Qorb := OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)
  -- `g ∈ famG₀ ↔ g ∉ Ã(M)` (single-member family).
  have hmemfam : ∀ g : G, g ∈ famG0 ↔ g ∉ Mdata.typeIHyp.dadeData.dade.dadeSupport := by
    intro g
    refine ⟨fun hg => hg 0, fun hg i => ?_⟩
    fin_cases i; exact hg
  -- `G₀ ⊆ famG₀` and `famG₀ ∖ G₀ ⊆ orbits`.
  have hsub : Mdata.G0 ⊆ famG0 := fun g hg => (hmemfam g).mpr (Mdata.G0_off_dadeSupport g hg)
  have hcover : famG0 \ Mdata.G0 ⊆ Worb ∪ Porb ∪ Qorb := by
    rintro g ⟨hgfam, hgG0⟩
    exact Mdata.G0_orbit_cover g ((hmemfam g).mp hgfam) hgG0
  -- ncard reduction.
  have hdiff : (famG0 \ Mdata.G0).ncard ≤ Worb.ncard + Porb.ncard + Qorb.ncard :=
    le_trans (Set.ncard_le_ncard hcover)
      (le_trans (Set.ncard_union_le _ _) (by gcongr; exact Set.ncard_union_le _ _))
  have hdeq : (famG0 \ Mdata.G0).ncard = famG0.ncard - Mdata.G0.ncard := Set.ncard_diff hsub
  have hG0le : Mdata.G0.ncard ≤ famG0.ncard := Set.ncard_le_ncard hsub
  -- `Nat.card famG₀ = famG₀.ncard`, `|filter| = G₀.ncard`.
  have hfamcard : Nat.card famG0 = famG0.ncard := Nat.card_coe_set_eq famG0
  have hfiltcard : (Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card = Mdata.G0.ncard := by
    rw [Set.ncard_eq_toFinset_card']; congr 1; ext g; simp
  rw [hfamcard, hfiltcard]
  have hcast : (famG0.ncard : ℝ) - (Mdata.G0.ncard : ℝ)
      = ((famG0.ncard - Mdata.G0.ncard : ℕ) : ℝ) := (Nat.cast_sub hG0le).symm
  rw [hcast, ← hdeq]
  calc ((famG0 \ Mdata.G0).ncard : ℝ) ≤ ((Worb.ncard + Porb.ncard + Qorb.ncard : ℕ) : ℝ) := by
        exact_mod_cast hdiff
    _ = (Worb.ncard : ℝ) + (Porb.ncard : ℝ) + (Qorb.ncard : ℝ) := by push_cast; ring

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), the upper-bound §8 TI-counting step** (04.16 lines 109–115).  Brings the
line-83 bound `|A(M)|/|M| + (1/|G|)(|famG₀| − |G₀|)` (`chiRhoNormSq_psi_le_line83`, proven) up to
the displayed `NormCascadeData.upper`.  The genuine §8 content: `|A(M)|/|M| = (k−1)/(kpq)`
(`card_typeIA_eq`/`card_M_eq`); the `G₀`-drop `famG0_sub_filter_card_le_orbit_ncard` (set-reduction,
proven) plus the orbit measures (`orbit_sdiff_sup_normSq_term`/`orbit_sharpSubgroup_normSq_term`)
and the structural values (`|W|`/`|N_G(P)|`, `IsTI P`/`IsTI Q`, `normalizer_V`) bound the orbits,
then `normCascade_upper_loosen`.  The remaining §8 structural input is the TI/normalizer data of the
Frobenius pieces `W`, `P`, `Q` (the type-I analogue of S12 (10.8)'s `G₁ ⊆ (H#)^G ∪ V^G`). -/
theorem MHypothesis.line83_le_displayed_upper [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ))
      ≤ 1 - (1 : ℝ) / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
        + 2 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
        + 1 / ((hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + 1 / ((hyp.base.v * hyp.base.p : ℕ) : ℝ) := by
  haveI := Mdata.finiteG
  -- abbreviations
  have hW1le : hyp.base.W1 ≤ hyp.base.W := hyp.base.W_eq_join ▸ le_sup_left
  have hW2le : hyp.base.W2 ≤ hyp.base.W := hyp.base.W_eq_join ▸ le_sup_right
  -- positivity (`p`, `q` prime; `u`, `v` from the faithful normalizer carriers; `k`/cards `> 0`).
  have hp : (0 : ℝ) < hyp.base.p := by exact_mod_cast hyp.base.p_prime.pos
  have hq : (0 : ℝ) < hyp.base.q := by exact_mod_cast hyp.base.q_prime.pos
  have hkpos : 0 < Mdata.k := Mdata.k_eq_card_K ▸ Nat.card_pos
  have hPpos : 0 < Nat.card ↥hyp.base.P := Nat.card_pos
  have hQpos : 0 < Nat.card ↥hyp.base.Q := Nat.card_pos
  have hNPpos : 0 < Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G)) := Nat.card_pos
  have hNQpos : 0 < Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G)) := Nat.card_pos
  have hupos : 0 < hyp.base.u := by
    by_contra hc
    have hu0 : hyp.base.u = 0 := Nat.le_zero.mp (not_lt.mp hc)
    have : Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G)) = 0 := by
      rw [Mdata.card_normalizer_P_eq, hu0, mul_zero, zero_mul]
    omega
  have hvpos : 0 < hyp.base.v := by
    by_contra hc
    have hv0 : hyp.base.v = 0 := Nat.le_zero.mp (not_lt.mp hc)
    have : Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G)) = 0 := by
      rw [Mdata.card_normalizer_Q_eq, hv0, mul_zero, zero_mul]
    omega
  -- orbit measures (equalities).
  have hWm := orbit_sdiff_sup_normSq_term hyp.base.W_cyclic hyp.base.W_eq_join
    Mdata.W_normalizer_V (S15.W_sdiff_nonempty hyp.base)
  have hPm := orbit_sharpSubgroup_normSq_term Mdata.P_isTI
  have hQm := orbit_sharpSubgroup_normSq_term Mdata.Q_isTI
  -- cardinalities of the supports.
  have hWc := ncard_sdiff_sup_add_eq hW1le hW2le hyp.base.W1_inf_W2_eq_bot
  have hPc := ncard_sharpSubgroup_add_one (P := hyp.base.P)
  have hQc := ncard_sharpSubgroup_add_one (P := hyp.base.Q)
  -- `|W-set| = pq + 1 − (p+q)`, `|N_G(P)| = |P| u q`, etc. (`ℕ`-level facts → `ℝ`).
  have hWsetR : (((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))).ncard : ℝ)
      = (hyp.base.p : ℝ) * hyp.base.q + 1 - hyp.base.p - hyp.base.q := by
    have : ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))).ncard
        + (hyp.base.p + hyp.base.q) = hyp.base.p * hyp.base.q + 1 := by
      rw [← S15.card_W1_add_W2 hyp.base,
        ← S15.card_W_eq_pq hyp.base]
      omega
    have hR : (((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))).ncard : ℝ)
        + ((hyp.base.p : ℝ) + hyp.base.q) = (hyp.base.p : ℝ) * hyp.base.q + 1 := by
      exact_mod_cast this
    linarith
  -- the three orbit-term values (equalities).
  have hWterm : (OddOrder.GroupTheory.conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))).ncard
        / (Nat.card G : ℝ)
      = 1 - 1 / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
        + 1 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ) := by
    rw [hWm, hWsetR]
    have hWcardR : (Nat.card ↥hyp.base.W : ℝ) = (hyp.base.p : ℝ) * hyp.base.q := by
      rw [S15.card_W_eq_pq hyp.base]; push_cast; ring
    rw [hWcardR]; push_cast; field_simp; ring
  have hPterm : (OddOrder.GroupTheory.conjClassSet
        (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)).ncard / (Nat.card G : ℝ)
      = ((Nat.card ↥hyp.base.P : ℝ) - 1)
        / ((Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q : ℕ) : ℝ) := by
    rw [hPm]
    have hsharpR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.P).ncard : ℝ)
        = (Nat.card ↥hyp.base.P : ℝ) - 1 := by
      have hR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.P).ncard : ℝ) + 1
          = (Nat.card ↥hyp.base.P : ℝ) := by exact_mod_cast hPc
      linarith
    rw [hsharpR, Mdata.card_normalizer_P_eq]
  have hQterm : (OddOrder.GroupTheory.conjClassSet
        (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)).ncard / (Nat.card G : ℝ)
      = ((Nat.card ↥hyp.base.Q : ℝ) - 1)
        / ((Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p : ℕ) : ℝ) := by
    rw [hQm]
    have hsharpR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.Q).ncard : ℝ)
        = (Nat.card ↥hyp.base.Q : ℝ) - 1 := by
      have hR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.Q).ncard : ℝ) + 1
          = (Nat.card ↥hyp.base.Q : ℝ) := by exact_mod_cast hQc
      linarith
    rw [hsharpR, Mdata.card_normalizer_Q_eq]
  -- `|A(M)|/|M| = (k−1)/(kpq)`.
  have hAterm : (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      = ((Mdata.k : ℝ) - 1) / ((Mdata.k * hyp.base.p * hyp.base.q : ℕ) : ℝ) := by
    rw [Mdata.card_typeIA_eq hG, Mdata.card_M_eq]
    have hkR : ((Mdata.k - 1 : ℕ) : ℝ) = (Mdata.k : ℝ) - 1 := by
      have : 1 ≤ Mdata.k := hkpos
      push_cast [Nat.cast_sub this]; ring
    rw [hkR]; push_cast; ring
  -- the `G₀`-drop, scaled by `1/|G|`.
  have hGinv : (0 : ℝ) ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hdrop := mul_le_mul_of_nonneg_left Mdata.famG0_sub_filter_card_le_orbit_ncard hGinv
  -- `(1/|G|)·Σ ncard = Σ (ncard/|G|) = hWterm + hPterm + hQterm`.
  have hsum : (Nat.card G : ℝ)⁻¹ * (((OddOrder.GroupTheory.conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))).ncard : ℝ)
      + ((OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)).ncard : ℝ)
      + ((OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)).ncard : ℝ))
      = (1 - 1 / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ) + 1 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ))
        + ((Nat.card ↥hyp.base.P : ℝ) - 1)
            / ((Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + ((Nat.card ↥hyp.base.Q : ℝ) - 1)
            / ((Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p : ℕ) : ℝ) := by
    rw [← hWterm, ← hPterm, ← hQterm]; ring
  -- assemble: `line83-RHS ≤ raw bound`.
  have hraw : (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ))
      ≤ 1 - 1 / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
          + 1 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
        + ((Nat.card ↥hyp.base.P : ℝ) - 1)
            / ((Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + ((Nat.card ↥hyp.base.Q : ℝ) - 1)
            / ((Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p : ℕ) : ℝ)
        + ((Mdata.k : ℝ) - 1) / ((Mdata.k * hyp.base.p * hyp.base.q : ℕ) : ℝ) := by
    rw [hAterm]; rw [hsum] at hdrop; linarith
  -- loosen the raw bound to the displayed one.
  exact le_trans hraw (normCascade_upper_loosen hyp.base.p_prime.pos hyp.base.q_prime.pos
    hupos hvpos hkpos hPpos hQpos)

/-- **Faithful §7 carrier for the `ρ`-norm two-sided bound of Peterfalvi (14.11.4).**

The character theory of (14.11.4) reduces to a two-sided bound on `‖ψ^{τ₁ρ}‖²`, where `ρ` is the
Hypothesis (7.1) map for `(M, A(M))` (Pf (14.11.4), p.90):

* `lower` — **(7.8.b)** (Pf 04.16 line 113): the §7 coherence-norm formula `‖ζ^{νρ}‖² ≥ 1 − e/h`
  for the coherent type-I `M` (with `e = |M:K| = pq`, `h = |K| = k`) gives `1 − pq/k ≤ ‖ψ^{τ₁ρ}‖²`.
  **Proven** (`MHypothesis.rhoNormSq_ge_lower`), via the `h78` coherence carrier and the norm bridge
  `chiRhoNormSq_eq_zetaNuRhoNormSq`.
* `upper` — **(7.5) + (14.11.3) + §8 TI-counting**: the (7.5) family inequality applied to the
  norm-one `ψ^{τ₁}`, dropping the `G_0`-part via `|ψ^{τ₁}(g)| ≥ 1` (`generic_character_bound`,
  14.11.3) to line 83 (`chiRhoNormSq_psi_le_line83`), then the §8 TI-counting of the
  `(W#)^G`/`(P#)^G`/`(Q#)^G` orbit contributions giving the raw estimate, loosened by
  `(|P|−1)/|P| ≤ 1`, `(|Q|−1)/|Q| ≤ 1`, `(k−1)/k ≤ 1` (`normCascade_upper_loosen`) to the
  `normCascadeBound` error terms `2/(pq) + 1/(uq) + 1/(vp)`.

The two-sided structure mirrors the textbook's two-step derivation; the `lower` (7.8.b) bound is
proven, and the remaining genuine obligation is the upper §8 TI-counting, isolated in
`normCascadeData`. -/
structure NormCascadeData (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  /-- `‖ψ^{τ₁ρ}‖²`, the squared `L`-norm of the Hypothesis (7.1) `ρ`-image of `ψ^{τ₁}`.
  Real-valued (matching `S09.FamilyHypothesis71.chiRhoNormSq : ℝ`), so the (7.5)/(7.8.b)
  derivation lives in `ℝ`; the passage to the rational `normCascadeBound` is a final cast. -/
  rhoNormSq : ℝ
  /-- **(7.8.b)** lower bound: `1 − pq/k ≤ ‖ψ^{τ₁ρ}‖²`
  (proven, `MHypothesis.rhoNormSq_ge_lower`). -/
  lower :
    (1 : ℝ) - ((hyp.base.p * hyp.base.q : ℕ) : ℝ) / (Mdata.k : ℝ) ≤ rhoNormSq
  /-- **(7.5) + (14.11.3) + §8 TI-counting** upper bound (loosened to the `normCascadeBound`
  error terms). -/
  upper :
    rhoNormSq ≤ 1 - (1 : ℝ) / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
      + 2 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
      + 1 / ((hyp.base.u * hyp.base.q : ℕ) : ℝ)
      + 1 / ((hyp.base.v * hyp.base.p : ℕ) : ℝ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §7 Dade producer for (14.11.4).**  The `ρ`-norm is the concrete family-inequality
norm `(toFamilyHypothesis71).chiRhoNormSq (ψ^{τ₁}) 0` for the `(M, A(M))` map `ρ`.

* `lower` is **proven** (`MHypothesis.rhoNormSq_ge_lower`): the (7.8.b) coherence-norm lower bound
  `1 − pq/k ≤ ‖ψ^{τ₁ρ}‖²` (via the `h78` carrier and the bridge `chiRhoNormSq_eq_zetaNuRhoNormSq`).
* `upper` is the remaining genuine obligation: the **§8 TI-counting** of the `(W#)^G`/`(P#)^G`/
  `(Q#)^G` orbit contributions that turns the line-83 bound (`chiRhoNormSq_psi_le_line83`, proven)
  into the raw estimate, which `normCascade_upper_loosen` (proven) then loosens to the displayed
  `normCascadeBound` error terms.  Both arithmetic ends of `upper` are honest; the gap is the §8
  orbit cardinality `|K#|/|M|`, `|(W#)^G|`/`|(P#)^G|`/`|(Q#)^G|` count. -/
noncomputable def normCascadeData [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    NormCascadeData hyp Mdata where
  rhoNormSq := (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0
  lower := Mdata.rhoNormSq_ge_lower
  -- line-83 (`chiRhoNormSq_psi_le_line83`, proven) chained with the §8 TI-counting step
  -- (`line83_le_displayed_upper`, the single remaining gate).
  upper := le_trans (Mdata.chiRhoNormSq_psi_le_line83 _hG hne) (Mdata.line83_le_displayed_upper _hG)

/-- **Peterfalvi (14.11.4)**: the character-theoretic norm calculation produces the displayed
rational inequality `normCascadeBound hyp k`.

De-opacified (W4 §16→§7 bridge, lane-h): the genuine character theory is the two-sided `ρ`-norm
bound `NormCascadeData` (the (7.5) family inequality + (14.11.3)/(7.8.b) norm estimates); the
passage to `normCascadeBound` is then the pure rational rearrangement
`1 − pq/k ≤ ‖ψ^{τ₁ρ}‖² ≤ 1 − 1/p − 1/q + 2/(pq) + 1/(uq) + 1/(vp)` ⟹
`1/p + 1/q ≤ pq/k + 2/(pq) + 1/(uq) + 1/(vp)` (`linarith`).  Everything downstream of
`normCascadeBound` is the arithmetic cascade already discharged in `norm_cascade_contradiction`. -/
theorem normCascadeBound_of_charData [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    normCascadeBound hyp Mdata.k := by
  obtain ⟨R, hlower, hupper⟩ := normCascadeData _hG hyp Mdata hne
  unfold normCascadeBound
  -- The two-sided `ℝ` bound `1 − pq/k ≤ R ≤ 1 − 1/p − 1/q + 2/(pq) + 1/(uq) + 1/(vp)` gives the
  -- displayed rational inequality; lift the `ℚ` goal to `ℝ` and close by `linarith`.
  rw [← Rat.cast_le (K := ℝ)]
  push_cast at hlower hupper ⊢
  linarith [hlower, hupper]

/-- **Peterfalvi (14.11.4)**: the norm inequality cascade contradicts `K != V`.

This is now a transparent composition rather than an opaque obligation: the
case-(9.7.b) outputs of `caseB_for_T` (14.4) and `caseB_for_S` (14.6) supply the
T-side/S-side cyclotomic size data, `main_size_bounds` (14.11.1) supplies
`k > 2 p v`, and `normCascadeBound_of_charData` (14.11.2)--(14.11.3) supplies the
displayed norm inequality.  The arithmetic consumer
`norm_cascade_contradiction_of_caseB_outputs_main_size_bounds` then closes the
cascade.  The only remaining genuine `sorry`s are the named producers above. -/
theorem contradiction_of_K_ne_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    False :=
  norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
    (caseB_for_T _hG hyp) (caseB_for_S _hG hyp Ldata) Mdata
    (main_size_bounds _hG hyp Mdata hne)
    (normCascadeBound_of_charData _hG hyp Mdata hne)

/-- **Peterfalvi (14.11)**: `K = V` and `|M : K| = p q`.

The `K = V` half is now a genuine consequence of the (14.11.1)--(14.11.4)
contradiction: assuming `K ≠ V` invokes `contradiction_of_K_ne_V`.  The index
computation `|M : K| = p q` (here `Mdata.e = p q`) is the remaining genuine
obligation; note `betaM_expansion`'s `e = p q` is unavailable here because it
is conditioned on `K ≠ V`, so the equal-index value under `K = V` needs the
type-I structure of `M` directly. -/
theorem K_eq_V_index_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp) :
    Mdata.K = hyp.base.V ∧ Mdata.e = hyp.base.p * hyp.base.q := by
  refine ⟨?_, ?_⟩
  · -- (14.11.1)--(14.11.4): `K ≠ V` is contradictory.
    by_contra hne
    exact contradiction_of_K_ne_V _hG hyp Ldata Mdata hne
  · -- `|M : K| = p q` from the type-I structure of `M`, carried by `MHypothesis`
    -- (V-side dual of `LHypothesis.typeI_complement_card_eq_pq`).
    exact Mdata.complement_card_eq_pq

/-! ## (14.12)--(14.16): comparing `L` and `M` -/

/-! **Peterfalvi (14.12)** (`field_normalizer_of_L_conj_M`, the `L ≅ M` case) is assembled
**after** (14.7) `field_normalizer_of_U_characteristic`, which it reduces to: when `L` is conjugate
to `M`, `H` is cyclic, so `U ≤ H` is characteristic and (14.7) applies.  See it just after (14.7). -/

/-- **Peterfalvi (14.13)**: the final comparison case assumes `L` and `M` are
not conjugate and sets `h = |H|`. -/
structure NonConjugateHypothesis (hyp : Hypothesis (G := G)) where
  Ldata : LHypothesis hyp
  Mdata : MHypothesis hyp
  not_conj : ¬ ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M
  h : ℕ
  h_eq_card_H : h = Nat.card ↥Ldata.H

namespace NonConjugateHypothesis

/-- **Peterfalvi (14.13)**: since `h = |H|` and `H` is a subgroup of the
minimal odd-order group, `h` is odd. -/
theorem h_odd [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    Odd nc.h := by
  rw [nc.h_eq_card_H]
  exact _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card nc.Ldata.H)

/-- **Peterfalvi (14.5)** cardinal consequence: `u` divides `h = |H|`.
The subgroup `U` lies in the Fitting kernel `H` of the type-I subgroup over
`N_G(U)`, while (13.12) gives `c = 1`; hence `|U| = u` and `u ∣ |H|`. -/
theorem u_dvd_h [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    hyp.base.u ∣ nc.h := by
  rw [nc.h_eq_card_H]
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, OddOrder.Peterfalvi.S15.c_eq_one _hG hyp.base, mul_one]
  have hU_le_H : hyp.base.U ≤ nc.Ldata.H := by
    rw [← nc.Ldata.typeI_data_H_eq]
    exact nc.Ldata.typeI_data.U_le_H
  have hdvd : Nat.card ↥hyp.base.U ∣ Nat.card ↥nc.Ldata.H :=
    Subgroup.card_dvd_of_le hU_le_H
  simpa [hU_card] using hdvd

/-- **Peterfalvi (14.5)** cardinal congruences for `h = |H|`.  The type-I
Frobenius structure has kernel `M_F = H`; by (14.5) its complement has order
`p q`.  Isaacs Lemma 6.1 gives `|H| ≡ 1 mod |C|`, hence both congruences
modulo `p` and modulo `q`. -/
theorem h_modEq_one_mod_p_and_q [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    nc.h ≡ 1 [MOD hyp.base.p] ∧ nc.h ≡ 1 [MOD hyp.base.q] := by
  let H0 : Subgroup G := nc.Ldata.typeI_data.frobenius.typeI.typeF.H
  have hH0_eq_typeI_H : H0 = nc.Ldata.typeI_data.H := by
    dsimp [H0]
    rw [nc.Ldata.typeI_data.frobenius.typeI.typeF.H_eq,
      nc.Ldata.typeI_data.H_eq_LF]
  have hH0_eq_H : H0 = nc.Ldata.H :=
    hH0_eq_typeI_H.trans nc.Ldata.typeI_data_H_eq
  have hkernel_card :
      Nat.card ↥(H0.subgroupOf nc.Ldata.typeI_data.L) = Nat.card ↥nc.Ldata.H := by
    have hH0_card :
        Nat.card ↥(H0.subgroupOf nc.Ldata.typeI_data.L) = Nat.card ↥H0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
        dsimp [H0]
        exact nc.Ldata.typeI_data.frobenius.typeI.typeF.H_le)).toEquiv
    rw [hH0_card, hH0_eq_H]
  have hmod_pq : nc.h ≡ 1 [MOD hyp.base.p * hyp.base.q] := by
    have hmod := nc.Ldata.typeI_data.frobenius.frobenius.card_kernel_modEq_one
    rw [hkernel_card, nc.Ldata.typeI_complement_card_eq_pq] at hmod
    rwa [nc.h_eq_card_H]
  exact ⟨hmod_pq.of_dvd (dvd_mul_right hyp.base.p hyp.base.q),
    hmod_pq.of_dvd (dvd_mul_left hyp.base.q hyp.base.p)⟩

end NonConjugateHypothesis

namespace Hypothesis

/-- **Peterfalvi (14.5)** fixed-point-free cardinal consequence for `U`:
`u ≡ 1 mod q`.  The Frobenius action of `W₁` on `U` gives
`|U| ≡ 1 mod |W₁|`; using (13.12), `|U| = u`, and the definition
`q = |W₁|` gives the stated congruence. -/
theorem u_modEq_one_mod_q [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.u ≡ 1 [MOD hyp.base.q] := by
  rcases OddOrder.Peterfalvi.S15.basic_structure _hG hyp.base with ⟨data, _hdata⟩
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, OddOrder.Peterfalvi.S15.c_eq_one _hG hyp.base, mul_one]
  have hU_sub_card :
      Nat.card ↥(hyp.base.U.subgroupOf (hyp.base.U ⊔ hyp.base.W1)) =
        Nat.card ↥hyp.base.U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : hyp.base.U ≤ hyp.base.U ⊔ hyp.base.W1)).toEquiv
  have hW1_sub_card :
      Nat.card ↥(hyp.base.W1.subgroupOf (hyp.base.U ⊔ hyp.base.W1)) =
        Nat.card ↥hyp.base.W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_right : hyp.base.W1 ≤ hyp.base.U ⊔ hyp.base.W1)).toEquiv
  have hmod := data.UW1_frobenius.card_kernel_modEq_one
  rwa [hU_sub_card, hW1_sub_card, hU_card, ← hyp.base.q_eq_card_W1] at hmod

/-- **Peterfalvi (14.7)** fixed-point-free congruence for `U` modulo `p`.  The conjugate
`W₂^y` has order `p = |W₂|`; if it acts fixed-point-freely on `U` — as it does in (14.7), since
`W₂^y` lies in the complement of the type-I Frobenius subgroup `L ⊇ N_G(U)` whose kernel
contains `U` — then `|U| ≡ 1 mod p`, hence (using `|U| = u` by (13.12)) `u ≡ 1 mod p`.  This is
the mod-`p` analogue of `u_modEq_one_mod_q`; it discharges the `hu_mod_p` input of the (14.7)
value argument from the fixed-point-free action. -/
theorem u_modEq_one_mod_p_of_fpf [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {y : G}
    (hW2y_norm : (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Subgroup.normalizer (hyp.base.U : Set G))
    (hfpf : ∀ a ∈ (MulAut.conj y • hyp.base.W2 : Subgroup G), a ≠ 1 →
      ∀ u ∈ hyp.base.U, u ≠ 1 → a * u * a⁻¹ ≠ u) :
    hyp.base.u ≡ 1 [MOD hyp.base.p] := by
  have hW2y_card : Nat.card ↥(MulAut.conj y • hyp.base.W2 : Subgroup G) = hyp.base.p := by
    rw [hyp.base.p_eq_card_W2]
    exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj y) hyp.base.W2).toEquiv).symm
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, OddOrder.Peterfalvi.S15.c_eq_one hG hyp.base, mul_one]
  have h := card_modEq_one_of_prime_normalizing_fpf hyp.base.p_prime hW2y_card hW2y_norm hfpf
  rwa [hU_card] at h

end Hypothesis

/-- **Part (14.2.b) normalizer conclusion `W₂^y ≤ N_G(U)`, from the structural carrier.**
The (14.5) complement membership of `W₂^y` already forces `W₂^y ≤ N_G(U)`: each element of `W₂^y`
lies in `L`, normalizes the Fitting kernel `H ◁ L` (`maxNilpotentNormalHall_le_normalizer`), and
`U` is characteristic in `H`, so it normalizes `U`
(`mem_normalizer_map_subtype_of_characteristic`).  Shared by the (14.7) value argument and the
final field-normalizer assembly. -/
theorem W2conj_le_normalizer_U_of_LHypothesis
    {hyp : Hypothesis (G := G)} (Ldata : LHypothesis hyp)
    (hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic)
    {y : G}
    (hW2y_compl : (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Ldata.typeI_data.frobenius.complement.map (Ldata.typeI_data.L).subtype) :
    (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Subgroup.normalizer (hyp.base.U : Set G) := by
  haveI : (hyp.base.U.subgroupOf Ldata.H).Characteristic := hchar
  have hU_le_H : hyp.base.U ≤ Ldata.H := by
    rw [← Ldata.typeI_data_H_eq]; exact Ldata.typeI_data.U_le_H
  intro a ha
  have ha_L : a ∈ Ldata.L := by
    obtain ⟨a', -, ha'eq⟩ := Subgroup.mem_map.mp (hW2y_compl ha)
    rw [← Ldata.typeI_data_L_eq, ← ha'eq]; exact a'.2
  have ha_normH : a ∈ Subgroup.normalizer (Ldata.H : Set G) := by
    have hLnorm := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer Ldata.L ha_L
    rwa [← Ldata.H_eq_LF] at hLnorm
  have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
    (W := Ldata.H) (C := hyp.base.U.subgroupOf Ldata.H) ha_normH
  rwa [Subgroup.map_subgroupOf_eq_of_le hU_le_H] at hmem

/-- **Peterfalvi (14.7) value-argument input, assembled from (14.3)/(13.17)/(14.5).**
With the type-I-over-`N_G(U)` carrier `Ldata` — so `L ⊇ N_G(U)` is a Frobenius group (13.17.a)
with kernel `H ⊇ U` (13.17.b) — and `U` characteristic in `H` (the standing hypothesis of
(14.7)), the element `y ∈ Q` produced by (14.5) places `W₂^y` in the Frobenius complement of `L`.
Then `W₂^y` normalizes `U` (it normalizes `H ◁ L`, and `U` is characteristic in `H`) and acts
fixed-point-freely on `U` (it is a nontrivial complement element acting on the kernel), so by
`Hypothesis.u_modEq_one_mod_p_of_fpf`, `u ≡ 1 (mod p)`.  This discharges the fixed-point-free
input of the (14.7) value argument from the structural carrier, reducing it to the (14.5)
membership `W₂^y ≤ complement`. -/
theorem u_modEq_one_mod_p_of_LHypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp)
    (hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic)
    {y : G}
    (hW2y_compl : (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Ldata.typeI_data.frobenius.complement.map (Ldata.typeI_data.L).subtype) :
    hyp.base.u ≡ 1 [MOD hyp.base.p] := by
  -- `U ≤ H` (13.17.b)
  have hU_le_H : hyp.base.U ≤ Ldata.H := by
    rw [← Ldata.typeI_data_H_eq]; exact Ldata.typeI_data.U_le_H
  -- the Frobenius kernel base `typeI.typeF.H` is `H`
  have hH0_eq_typeIH : Ldata.typeI_data.frobenius.typeI.typeF.H = Ldata.typeI_data.H := by
    rw [Ldata.typeI_data.frobenius.typeI.typeF.H_eq, Ldata.typeI_data.H_eq_LF]
  have hH0_eq_H : Ldata.typeI_data.frobenius.typeI.typeF.H = Ldata.H :=
    hH0_eq_typeIH.trans Ldata.typeI_data_H_eq
  -- `W₂^y ≤ N_G(U)` (part (14.2.b)), shared with the final assembly
  have hW2y_norm := W2conj_le_normalizer_U_of_LHypothesis Ldata hchar hW2y_compl
  -- `W₂^y` acts fixed-point-freely on `U` (Frobenius complement on the kernel)
  have hfpf : ∀ a ∈ (MulAut.conj y • hyp.base.W2 : Subgroup G), a ≠ 1 →
      ∀ u ∈ hyp.base.U, u ≠ 1 → a * u * a⁻¹ ≠ u := by
    intro a ha ha_ne u hu hu_ne
    refine isFrobeniusGroup_conj_ne_of_mem_map_complement
      Ldata.typeI_data.frobenius.frobenius
      Ldata.typeI_data.frobenius.typeI.typeF.H_le (hW2y_compl ha) ha_ne ?_ hu_ne
    rw [hH0_eq_H]; exact hU_le_H hu
  exact Hypothesis.u_modEq_one_mod_p_of_fpf hG hyp hW2y_norm hfpf

/-- **Peterfalvi (13.2.b)/(14.2.a): `W₂ ≤ P`.**  `W₂` is a `p`-group (`|W₂| = p`) inside `S`
(`W₂ ≤ W = S ⊓ T`), while `P = S_F` is a normal Hall `p`-subgroup of `S` (normal by
`maxNilpotentNormalHall_subgroupOf_normal`, Hall by `maxNilpotentNormalHall_isHall`, and a
`p`-group of order `p^q` by `basic_structure`).  Hence `W₂ ≤ P` — the `F_p ⊆ F` identification of
(14.2.a). -/
theorem W2_le_P [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.base.W2 ≤ hyp.base.P :=
  OddOrder.Peterfalvi.S15.W2_le_P _hG hyp.base

/-- **Peterfalvi (13.2.b) for `T`**: `Q` is elementary abelian (13.2.b applied to the dual subgroup
`T`) — the canonical §15 obligation `Q_elementaryAbelian_T` (`T` type-II from `T_typeII` (14.9)). -/
theorem Q_elemAbelian_S [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    IsElementaryAbelian hyp.base.q ↥hyp.base.Q :=
  OddOrder.Peterfalvi.S15.Q_elementaryAbelian_T _hG hyp.base (T_typeII _hG hyp)

/-- **Peterfalvi (13.2) `S`-side structural inputs for the (14.7) field model.**  The field-model
construction (14.2.a) needs two §13 structural facts about the type-`P` subgroup `S`: `W₂ ≤ P`
(the `F_p ⊆ F` identification) and `Q` elementary abelian (13.2.b for `T`).  `W₂ ≤ P` is proved
outright (`W2_le_P`); `Q` elementary abelian is the §15 obligation `Q_elemAbelian_S`.

The field model needs **no** cyclicity of `U`: the Singer representation `exists_pu_field_repr` is
built from `U` **abelian** (Peterfalvi (13.2.a): `UW₁` is Frobenius with abelian kernel `U`; coq
`PFsection14.v` `cUU : abelian U`) via the abelian Singer irreducibility
`isSimpleModule_of_abelian_faithful_card`, and the injection `μ : U ↪ 𝔽_{p^q}^×` into the cyclic unit
group is a *consequence* — never a hypothesis. -/
theorem S_field_model_structural_inputs [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.base.W2 ≤ hyp.base.P ∧
      IsElementaryAbelian hyp.base.q ↥hyp.base.Q :=
  ⟨W2_le_P _hG hyp, Q_elemAbelian_S _hG hyp⟩

/-- **Peterfalvi (14.7)**: if `U` is characteristic in `H`, then the field-normalizer
configuration (14.2) holds.  The value argument is assembled entirely from the structural
carrier: (14.5) `exists_y_L_structure` supplies `y ∈ Q` with `W₂^y` in the Frobenius complement
of `L`; the bridge `u_modEq_one_mod_p_of_LHypothesis` turns that into `u ≡ 1 mod p`; and
`W2conj_le_normalizer_U_of_LHypothesis` supplies `W₂^y ≤ N_G(U)`.  These feed the value-argument
engine `field_normalizer_of_U_characteristic_of_fpf`.  This theorem carries **no `sorry`**: the
remaining §13 structural facts are cited as the named obligation `S_field_model_structural_inputs`
(`U` cyclic / `W₂ ≤ P` / `Q` elementary abelian), while `W₂ ≤ N_G(Q)` is discharged outright
(`W₂ ≤ W ≤ T` and `Q = T_F`). -/
theorem field_normalizer_of_U_characteristic [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp)
    (hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨y, hyQ, hW2y_compl⟩ := exists_y_L_structure hG hyp Ldata
  have hmod := u_modEq_one_mod_p_of_LHypothesis hG Ldata hchar hW2y_compl
  have hW2_conj_y := W2conj_le_normalizer_U_of_LHypothesis Ldata hchar hW2y_compl
  -- §13 structural inputs (13.2.a/b, companion to `basic_structure`; Lane B / §13 group theory)
  obtain ⟨hW2_le_P, hQ_elemAb⟩ := S_field_model_structural_inputs hG hyp
  -- `W₂ ≤ N_G(Q)` is ungated: `W₂ ≤ W ≤ T` and `Q = T_F`
  have hW2_norm_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G) := by
    have hW2_le_W : hyp.base.W2 ≤ hyp.base.W := by
      rw [hyp.base.W_eq_join]; exact le_sup_right
    have hW_le_T : hyp.base.W ≤ hyp.base.T := by
      rw [hyp.base.W_eq_inter]; exact inf_le_right
    rw [hyp.base.Q_eq_TF]
    exact (hW2_le_W.trans hW_le_T).trans
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T)
  exact field_normalizer_of_U_characteristic_of_fpf hG hyp Ldata hmod hW2_le_P
    hQ_elemAb hW2_norm_Q y hyQ hW2_conj_y

/-- **Every subgroup of a finite cyclic group is characteristic.**  A subgroup `K` equals the
`|K|`-torsion `ker (powMonoidHom |K|) = {x | x ^ |K| = 1}`: it is contained in it (Lagrange:
`x ^ |K| = 1` for `x ∈ K`) and has the same cardinality (`|ker| = gcd(|C|, |K|) = |K|` as
`|K| ∣ |C|`).  The torsion is preserved by every automorphism `φ` since `φ x ^ d = φ (x ^ d)`,
so `K` is characteristic.  Used for the (14.12) `L ≅ M` case where `H` is cyclic. -/
theorem characteristic_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (K : Subgroup C) : K.Characteristic := by
  letI : CommGroup C := IsCyclic.commGroup
  have key : ∀ A : Subgroup C, A = (powMonoidHom (Nat.card A) : C →* C).ker := by
    intro A
    have hle : A ≤ (powMonoidHom (Nat.card A) : C →* C).ker := by
      intro a ha
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have h1 : (⟨a, ha⟩ : A) ^ Nat.card A = 1 := pow_card_eq_one'
      have h2 := congrArg (Subtype.val) h1
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
      exact h2
    have hdvd : Nat.card A ∣ Nat.card C := Subgroup.card_subgroup_dvd_card A
    have hcard : Nat.card (powMonoidHom (Nat.card A) : C →* C).ker = Nat.card A := by
      rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hdvd]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
  rw [Subgroup.characteristic_iff_comap_eq]
  intro φ
  have hcard_eq : Nat.card ↥(K.comap φ.toMonoidHom) = Nat.card ↥K :=
    Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv (fun a => Subgroup.mem_comap))
  conv_lhs => rw [key (K.comap φ.toMonoidHom)]
  conv_rhs => rw [key K]
  rw [hcard_eq]

open scoped IsMulCommutative in
/-- **Peterfalvi (13.2.a) for `T`**: the `T`-side complement `V` is cyclic.  `V` is the abelian
Frobenius kernel of the type-I-over-`N_G(V)` configuration.  This is the `T`/`V`-side dual of the
`S`/`U`-side field-model cyclicity (`exists_pv_field_repr`, still to be built): once the dual Singer
representation `μ : V ↪ 𝔽_{q^p}^×` is constructed from `V` abelian via
`isSimpleModule_of_abelian_faithful_card`, `V` cyclic follows.  Used to transport `K = V` (14.11) to
`K` cyclic in `MHypothesis_kernel_cyclic`. -/
theorem V_cyclic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : IsCyclic ↥hyp.base.V := by
  letI : Fact hyp.base.q.Prime := ⟨hyp.base.q_prime⟩
  haveI : NeZero hyp.base.q := ⟨hyp.base.q_prime.ne_zero⟩
  haveI hTII : IsTypeII hyp.base.T := T_typeII hG hyp
  have hQea : IsElementaryAbelian hyp.base.q ↥hyp.base.Q := Q_elemAbelian_S hG hyp
  haveI hQcomm : IsMulCommutative ↥hyp.base.Q := IsMulCommutative.of_comm hQea.comm
  letI hVcomm : CommGroup ↥hyp.base.V :=
    { (inferInstance : Group ↥hyp.base.V) with
      mul_comm := fun a b =>
        (isMulCommutative_iff.mp
          (OddOrder.Peterfalvi.S15.isMulCommutative_V hG hyp.base hTII)) a b }
  -- `|V| = v = (q^p - 1)/(q - 1)`: `d = 1` from `D = V ⊓ C_G(Q) = ⊥` (13.12 dual), plus the
  -- `v`-value (14.4) `T_side_caseB_facts`.
  have hv_full : Nat.card ↥hyp.base.V =
      (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact OddOrder.Peterfalvi.S15.V_inf_centralizer_Q_eq_bot hG hyp.base hTII
    have hd1 : hyp.base.d = 1 := by rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
    rw [hyp.base.card_V_eq_vd, hd1, mul_one]
    exact (T_side_caseB_facts hG hyp).2
  have hqsmul : ∀ x : Additive ↥hyp.base.Q, (hyp.base.q : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hQea.pow_eq_one x.toMul
  haveI hQmod : Module (ZMod hyp.base.q) (Additive ↥hyp.base.Q) :=
    AddCommGroup.zmodModule hqsmul
  -- the conjugation representation of `V` on `Additive ↥Q`
  let conjHom : ↥hyp.base.V →* MulAut ↥hyp.base.Q :=
    (Subgroup.normalizerMonoidHom (H := hyp.base.Q)).comp
      (Subgroup.inclusion (V_le_normalizer_Q hyp))
  let ρ : Representation (ZMod hyp.base.q) ↥hyp.base.V (Additive ↥hyp.base.Q) :=
    (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥hyp.base.Q hyp.base.q).comp conjHom
  have hρ_apply : ∀ (c : ↥hyp.base.V) (a : Additive ↥hyp.base.Q),
      ρ c a = Additive.ofMul ((conjHom c) (Additive.toMul a)) := fun _ _ => rfl
  letI hQmodAlg :
      Module (MonoidAlgebra (ZMod hyp.base.q) ↥hyp.base.V) (Additive ↥hyp.base.Q) :=
    Module.compHom (Additive ↥hyp.base.Q) (ρ.asAlgebraHom).toRingHom
  have hof_smul : ∀ (c : ↥hyp.base.V) (a : Additive ↥hyp.base.Q),
      MonoidAlgebra.of (ZMod hyp.base.q) ↥hyp.base.V c • a =
        Additive.ofMul ((conjHom c) (Additive.toMul a)) := by
    intro c a
    have h : MonoidAlgebra.of (ZMod hyp.base.q) ↥hyp.base.V c • a = ρ c a := by
      show (ρ.asAlgebraHom (MonoidAlgebra.of (ZMod hyp.base.q) ↥hyp.base.V c)) a = ρ c a
      rw [Representation.asAlgebraHom_of]
    rw [h, hρ_apply]
  haveI hNeZero : NeZero (Nat.card ↥hyp.base.V : ZMod hyp.base.q) := by
    refine ⟨fun h => ?_⟩
    rw [hv_full] at h
    have hdvd : hyp.base.q ∣ (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) :=
      (ZMod.natCast_eq_zero_iff _ _).mp h
    have hmod : (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) ≡ 1 [MOD hyp.base.q] := by
      have hsum_eq : ∑ k ∈ Finset.range hyp.base.p, hyp.base.q ^ k =
          (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) :=
        Nat.geomSum_eq hyp.base.q_prime.two_le _
      rw [← hsum_eq, show hyp.base.p = (hyp.base.p - 1) + 1 by
          have := hyp.base.p_prime.pos; omega, Finset.sum_range_succ']
      have hzero : (∑ k ∈ Finset.range (hyp.base.p - 1), hyp.base.q ^ (k + 1)) ≡ 0
          [MOD hyp.base.q] := by
        rw [Nat.modEq_zero_iff_dvd]
        exact Finset.dvd_sum fun k _ => dvd_pow_self hyp.base.q (Nat.succ_ne_zero k)
      simpa using hzero.add_right 1
    have hdvd1 : hyp.base.q ∣ 1 := by
      have h0 := (Nat.modEq_zero_iff_dvd).mpr hdvd
      have h01 := h0.symm.trans hmod
      rwa [Nat.modEq_iff_dvd', Nat.sub_zero] at h01
      omega
    exact absurd (Nat.le_of_dvd one_pos hdvd1) (by have := hyp.base.q_prime.two_le; omega)
  have hcardM : Nat.card (Additive ↥hyp.base.Q) = hyp.base.q ^ hyp.base.p :=
    OddOrder.Peterfalvi.S15.card_Q_eq hG hyp.base hTII
  have hfaith : ∀ c : ↥hyp.base.V,
      (∀ x : Additive ↥hyp.base.Q,
          MonoidAlgebra.of (ZMod hyp.base.q) ↥hyp.base.V c • x = x) → c = 1 := by
    intro c hc
    have hcomm : ∀ y : ↥hyp.base.Q, (c : G) * (y : G) = (y : G) * (c : G) := by
      intro y
      have h1 := hc (Additive.ofMul y)
      rw [hof_smul] at h1
      have h2 : (conjHom c) y = y := Additive.ofMul.injective (by simpa using h1)
      have h3 : (c : G) * (y : G) * (c : G)⁻¹ = (y : G) := congrArg Subtype.val h2
      rwa [mul_inv_eq_iff_eq_mul] at h3
    have hmem : (c : G) ∈ hyp.base.D := by
      rw [hyp.base.D_eq]
      exact ⟨c.2, Subgroup.mem_centralizer_iff.mpr (fun y hy => (hcomm ⟨y, hy⟩).symm)⟩
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact OddOrder.Peterfalvi.S15.V_inf_centralizer_Q_eq_bot hG hyp.base hTII
    rw [hDbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨e0, μ, hμinj, _⟩ :=
    OddOrder.RepresentationTheory.exists_galoisField_repr
      (C := ↥hyp.base.V) (M := Additive ↥hyp.base.Q)
      hyp.base.p_prime hyp.base.p_odd hcardM hv_full hfaith
  -- `μ : V ↪ 𝔽_{q^p}ˣ` is injective and the finite-field unit group is cyclic, so `V` is cyclic.
  exact isCyclic_of_injective μ hμinj

/-- **Peterfalvi (14.11)/(14.4)/(13.12)**: the Fitting kernel `K = M_F` of the type-I maximal
subgroup `M` over `N_G(V)` is cyclic.

This realizes the textbook route directly: by (14.11) `K = V` (`K_eq_V_index_pq`, the
(14.11.1)--(14.11.4) norm cascade), and `V` is cyclic (`V_cyclic`, 13.2.a for `T`), so `K` is
cyclic.  The remaining character-theoretic content is therefore isolated into the two named
obligations `K_eq_V_index_pq` (the (14.11) cascade, whose structural input is
`main_size_bounds_structural` and whose character input is `betaM_expansion` /
`generic_character_bound`) and `V_cyclic` (13.2.a for `T`).  Feeds the (14.12) reduction; the
`L ≅ M` case transports it to `H = L_F` purely structurally (`H_cyclic_of_L_conj_M`). -/
theorem MHypothesis_kernel_cyclic [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) : IsCyclic ↥Mdata.K := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hyp
  rw [(K_eq_V_index_pq _hG hyp Ldata Mdata).1]
  exact V_cyclic _hG hyp

/-- **Peterfalvi (14.12) structural input**: in the `L ≅ M` case, `H = L_F` is cyclic.  Since
`L ≅ M` (a conjugation `MulAut.conj g`), the maximal nilpotent normal Hall subgroup is
automorphism-equivariant (`maxNilpotentNormalHall_pointwise_smul`), so `H = L_F ≅ M_F = K`;
cyclicity of `K` is the §13/§14 obligation `MHypothesis_kernel_cyclic`.  This reduction is
purely structural — the character theory is confined to `MHypothesis_kernel_cyclic`. -/
theorem H_cyclic_of_L_conj_M [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (_hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M) :
    IsCyclic ↥Ldata.H := by
  obtain ⟨g, hg⟩ := _hconj
  haveI := MHypothesis_kernel_cyclic _hG hyp Mdata
  rw [Ldata.H_eq_LF]
  -- `M_F` is the `conj g`-image of `L_F`: `conj g • L_F = (conj g • L)_F = M_F = K`.
  have hmap : (maxNilpotentNormalHall Ldata.L).map ((MulAut.conj g : MulAut G) : G →* G)
      = Mdata.K := by
    rw [← pointwise_mulAut_smul_eq_map, maxNilpotentNormalHall_pointwise_smul, hg, Mdata.K_eq_MF]
  set e : ↥(maxNilpotentNormalHall Ldata.L) ≃* ↥Mdata.K :=
    (MulEquiv.subgroupMap (MulAut.conj g) (maxNilpotentNormalHall Ldata.L)).trans
      (MulEquiv.subgroupCongr hmap) with he
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

/-- **Peterfalvi (14.12)**: if `L` is conjugate to `M`, then the field-normalizer configuration
(14.2) holds.  Textbook reduction: `L ≅ M ⟹ H ≅ K` cyclic (`H_cyclic_of_L_conj_M`), so every
subgroup of `H` — in particular `U` — is characteristic (`characteristic_of_isCyclic`), and (14.7)
`field_normalizer_of_U_characteristic` applies.  Carries **no `sorry`**; gated only through the
named §13/§14 obligation `H_cyclic_of_L_conj_M`. -/
theorem field_normalizer_of_L_conj_M [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M) :
    Nonempty (FieldNormalizerData hyp) := by
  haveI : IsCyclic ↥Ldata.H := H_cyclic_of_L_conj_M hG hyp Ldata Mdata hconj
  exact field_normalizer_of_U_characteristic hG hyp Ldata
    (characteristic_of_isCyclic (hyp.base.U.subgroupOf Ldata.H))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The two alternatives of **Peterfalvi (14.14)**. -/
structure OrthogonalitySwitchData {hyp : Hypothesis (G := G)}
    (nc : NonConjugateHypothesis hyp) where
  caseA : Prop
  caseA_bound :
    caseA →
      (((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ))
  caseB : Prop
  caseB_params : caseB → hyp.base.q = 3 ∧ hyp.base.p = 5
  /-- **Peterfalvi (14.14.b), the case-(b) pairing**: in case (b) the L-side `β` pairs
  nontrivially with the M-side coherent test image — the first branch of the (7.9)
  dichotomy (`pairing_dichotomy`), packaged with its coherence bundles.  This carries
  the "(β_L^τ, ψ^{τ₁}) ≠ 0" half of Pf's case-(b) *definition*, which the `(q,p) = (3,5)`
  conclusion alone cannot recover; the (14.16) contradiction consumes it through
  `caseB_contradiction_data`. -/
  caseB_pairing :
    caseB →
      haveI := hyp.base.finiteG
      ∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G),
      ∃ (dataL : TypeICoherent78Data nc.Ldata.L) (dataM : TypeICoherent78Data nc.Mdata.M),
        ClassFunction.inner
          ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal nc.Mdata.M_maximal
              nc.not_conj).first.beta)
          ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal nc.Mdata.M_maximal
              nc.not_conj).secondZetaImage) ≠ 0

namespace CaseBForSData

/-- **Peterfalvi (14.15)**: the congruence part of the non-full branch.  From
`h = u * x`, the congruence `h ≡ 1 mod p` supplied by (14.5), and the
fixed-point-free congruence `x ≡ 1 mod q`, the divided cyclotomic formula gives
`x ≡ q mod p`; hence `x = q + n p` for some `n`, and then `n ≡ 1 mod q`. -/
theorem exists_x_decomposition_of_nonfull_card_congruences
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (Sdata : CaseBForSData hyp)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    {x : ℕ} (hh_eq : nc.h = hyp.base.u * x)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hx_mod_q : x ≡ 1 [MOD hyp.base.q]) :
    ∃ n : ℕ, x = hyp.base.q + n * hyp.base.p ∧ n ≡ 1 [MOD hyp.base.q] := by
  let C : ℕ := (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)
  have hmod : hyp.base.p ≡ 1 [MOD hyp.base.q] := by
    by_contra hnot_mod
    exact hu_not_full (Sdata.u_eq_of_not_modEq_one hnot_mod)
  have hC_dvd : hyp.base.q ∣ C := by
    dsimp [C]
    exact OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one
      hyp.base.p_prime hmod
  have hu_div : hyp.base.u = C / hyp.base.q := by
    rw [Sdata.u_eq_of_p_modEq_one hmod]
    dsimp [C]
    rw [Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm (hyp.base.p - 1) hyp.base.q]
  have hq_u : hyp.base.q * hyp.base.u = C := by
    rw [hu_div, Nat.mul_comm, Nat.div_mul_cancel hC_dvd]
  have hq_h : hyp.base.q * nc.h = C * x := by
    rw [hh_eq, ← mul_assoc, hq_u]
  have hC_mod_p : C ≡ 1 [MOD hyp.base.p] := by
    dsimp [C]
    exact cyclotomic_quotient_modEq_one_mod_base
      hyp.base.p_prime.two_le hyp.base.q_prime.pos
  have hqh_mod : hyp.base.q * nc.h ≡ hyp.base.q [MOD hyp.base.p] := by
    simpa [mul_one] using hh_mod_p.mul_left hyp.base.q
  rw [hq_h] at hqh_mod
  have hCx_mod : C * x ≡ x [MOD hyp.base.p] := by
    simpa [one_mul] using hC_mod_p.mul_right x
  have hx_mod_p : x ≡ hyp.base.q [MOD hyp.base.p] := hCx_mod.symm.trans hqh_mod
  have hq_le_x : hyp.base.q ≤ x := by
    by_contra hnot
    have hx_lt_q : x < hyp.base.q := Nat.lt_of_not_ge hnot
    have hx_eq_q : x = hyp.base.q :=
      Nat.ModEq.eq_of_lt_of_lt hx_mod_p (lt_trans hx_lt_q hyp.q_lt_p) hyp.q_lt_p
    omega
  rcases (Nat.modEq_iff_exists_eq_add hq_le_x).mp hx_mod_p.symm with
    ⟨n, hx_eq_add⟩
  have hx_eq : x = hyp.base.q + n * hyp.base.p := by
    simpa [mul_comm] using hx_eq_add
  have hnp_mod : n * hyp.base.p ≡ n [MOD hyp.base.q] := by
    simpa [mul_one] using hmod.mul_left n
  have hq_zero : hyp.base.q ≡ 0 [MOD hyp.base.q] := by
    rw [Nat.modEq_zero_iff_dvd]
  have hx_mod_n : x ≡ n [MOD hyp.base.q] := by
    rw [hx_eq]
    simpa using hq_zero.add hnp_mod
  exact ⟨n, hx_eq, hx_mod_n.symm.trans hx_mod_q⟩

/-- **Peterfalvi (14.15)**: in the non-full S-side cyclotomic branch, the
`h = u * x` decomposition and the fixed-point-free congruence estimate give the
lower comparison `p^q < h - 1`.  The proof follows the paragraph
`x > p q`, hence `h > p * (p^q - 1)/(p - 1) > p^q + 1`, with the divided
cyclotomic formula for `u` supplied by **Peterfalvi (13.15)**. -/
theorem p_pow_lt_h_sub_one_of_nonfull_decomposition
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (Sdata : CaseBForSData hyp)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    {x n : ℕ} (hh_eq : nc.h = hyp.base.u * x)
    (hx_eq : x = hyp.base.q + n * hyp.base.p)
    (hn_mod : n ≡ 1 [MOD hyp.base.q]) (hx_odd : Odd x) :
    hyp.base.p ^ hyp.base.q < nc.h - 1 := by
  let C : ℕ := (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)
  have hmod : hyp.base.p ≡ 1 [MOD hyp.base.q] := by
    by_contra hnot_mod
    exact hu_not_full (Sdata.u_eq_of_not_modEq_one hnot_mod)
  have hC_dvd : hyp.base.q ∣ C := by
    dsimp [C]
    exact OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one
      hyp.base.p_prime hmod
  have hu_div : hyp.base.u = C / hyp.base.q := by
    rw [Sdata.u_eq_of_p_modEq_one hmod]
    dsimp [C]
    rw [Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm (hyp.base.p - 1) hyp.base.q]
  have hq_u : hyp.base.q * hyp.base.u = C := by
    rw [hu_div, Nat.mul_comm, Nat.div_mul_cancel hC_dvd]
  have hC_sub_ge : hyp.base.p ^ (hyp.base.q - 1) ≤ C - 1 := by
    have hleQ := cyclotomic_quotient_sub_one_ge_pow_pred
      (q := hyp.base.p) (p := hyp.base.q)
      hyp.base.p_prime.two_le hyp.base.q_prime.two_le
    dsimp [C]
    exact_mod_cast hleQ
  have hpow_pred_pos : 0 < hyp.base.p ^ (hyp.base.q - 1) :=
    pow_pos hyp.base.p_prime.pos _
  have hC_ge : hyp.base.p ^ (hyp.base.q - 1) + 1 ≤ C := by omega
  have hC_pos : 0 < C := by omega
  have hp_mul_C_gt : hyp.base.p ^ hyp.base.q + 1 < hyp.base.p * C := by
    have hq_pos : 0 < hyp.base.q := hyp.base.q_prime.pos
    have hmul_le :
        hyp.base.p * (hyp.base.p ^ (hyp.base.q - 1) + 1) ≤
          hyp.base.p * C :=
      Nat.mul_le_mul_left hyp.base.p hC_ge
    have hpow_mul :
        hyp.base.p * hyp.base.p ^ (hyp.base.q - 1) = hyp.base.p ^ hyp.base.q := by
      calc
        hyp.base.p * hyp.base.p ^ (hyp.base.q - 1) =
            hyp.base.p ^ (hyp.base.q - 1) * hyp.base.p := by rw [mul_comm]
        _ = hyp.base.p ^ ((hyp.base.q - 1) + 1) := by rw [pow_succ]
        _ = hyp.base.p ^ hyp.base.q := by rw [show hyp.base.q - 1 + 1 = hyp.base.q by omega]
    have hle : hyp.base.p ^ hyp.base.q + hyp.base.p ≤ hyp.base.p * C := by
      calc
        hyp.base.p ^ hyp.base.q + hyp.base.p =
            hyp.base.p * (hyp.base.p ^ (hyp.base.q - 1) + 1) := by
          rw [mul_add, mul_one, hpow_mul]
        _ ≤ hyp.base.p * C := hmul_le
    nlinarith [hle, hyp.base.p_prime.one_lt]
  have hx_min : hyp.base.q + (1 + hyp.base.q) * hyp.base.p ≤ x :=
    hyp.x_ge_caseA_min_of_decomposition_modEq_and_odd hx_eq hn_mod hx_odd
  have hx_gt_pq : hyp.base.p * hyp.base.q < x := by
    nlinarith [hx_min, hyp.base.p_prime.pos, hyp.base.q_prime.pos]
  have hq_h : hyp.base.q * nc.h = C * x := by
    rw [hh_eq, ← mul_assoc, hq_u]
  have hpC_lt_h : hyp.base.p * C < nc.h := by
    have hCx_gt : C * (hyp.base.p * hyp.base.q) < C * x :=
      Nat.mul_lt_mul_of_pos_left hx_gt_pq hC_pos
    have hq_lt : hyp.base.q * (hyp.base.p * C) < hyp.base.q * nc.h := by
      calc
        hyp.base.q * (hyp.base.p * C) = C * (hyp.base.p * hyp.base.q) := by ring
        _ < C * x := hCx_gt
        _ = hyp.base.q * nc.h := hq_h.symm
    exact Nat.lt_of_mul_lt_mul_left hq_lt
  have hpq_add_lt_h : hyp.base.p ^ hyp.base.q + 1 < nc.h :=
    lt_trans hp_mul_C_gt hpC_lt_h
  omega

end CaseBForSData

namespace OrthogonalitySwitchData

/-- The exceptional branch in **Peterfalvi (14.14)** is already in the
`q = 3` situation, so the Section 16 `m > 49/100` bound is available for later
use in the final comparison. -/
theorem m_gt_49_hundredths_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (hcaseB : data.caseB) :
    hyp.base.m > (49 / 100 : ℚ) := by
  exact hyp.m_gt_49_hundredths_of_q_eq_three (data.caseB_params hcaseB).1

/-- In the exceptional branch of **Peterfalvi (14.14)**, the S-side congruence
branch `p ≡ 1 mod q` is impossible: the branch has `(q,p) = (3,5)`, and
`5` is not `1 mod 3`. -/
theorem not_p_modEq_one_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (hcaseB : data.caseB) :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] := by
  intro hmod
  have hparams := data.caseB_params hcaseB
  have hmod' : 5 ≡ 1 [MOD 3] := by
    simpa [hparams.1, hparams.2] using hmod
  unfold Nat.ModEq at hmod'
  norm_num at hmod'

/-- In the exceptional branch of **Peterfalvi (14.14)**, the S-side case-(9.7.b)
order data is forced into its full cyclotomic branch.  This is the consumer form
needed for **Peterfalvi (14.15)**. -/
theorem u_eq_full_cyclotomic_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
  Sdata.u_eq_of_not_modEq_one (data.not_p_modEq_one_of_caseB hcaseB)

/-- Numerically, the exceptional branch of **Peterfalvi (14.14)** gives
`u = (5^3 - 1)/(5 - 1) = 31`, once the S-side case-(9.7.b) order data has been
materialized. -/
theorem u_eq_thirty_one_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB) :
    hyp.base.u = 31 := by
  have hparams := data.caseB_params hcaseB
  have hu := data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB
  rw [hparams.1, hparams.2] at hu
  norm_num at hu
  exact hu

/-- Numerically, the exceptional branch of **Peterfalvi (14.14)** gives
`v = (3^5 - 1)/(3 - 1) = 121`, once the T-side case-(9.7.b) order data from
(14.4) has been materialized. -/
theorem v_eq_one_twenty_one_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (Tdata : CaseBForTData hyp) (hcaseB : data.caseB) :
    hyp.base.v = 121 := by
  have hparams := data.caseB_params hcaseB
  rw [Tdata.v_eq, hparams.1, hparams.2]
  norm_num

/-- **Peterfalvi (14.15)**: the case-(a) bound of (14.14) turns a lower
bound `p^q < h - 1` into the key inequality `p^(q - 2) < q^2`. -/
theorem p_pow_q_sub_two_lt_q_sq_of_p_pow_lt_h_sub_one
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseA : data.caseA)
    (hpow_lt_h : hyp.base.p ^ hyp.base.q < nc.h - 1) :
    hyp.base.p ^ (hyp.base.q - 2) < hyp.base.q ^ 2 := by
  have hbound := data.caseA_bound hcaseA
  have hpq_pos_nat : 0 < hyp.base.p * hyp.base.q :=
    Nat.mul_pos hyp.base.p_prime.pos hyp.base.q_prime.pos
  have hpq_posQ : (0 : ℚ) < (hyp.base.p * hyp.base.q : ℚ) := by
    exact_mod_cast hpq_pos_nat
  have hmul := mul_le_mul_of_nonneg_right hbound (le_of_lt hpq_posQ)
  have hleQ : ((nc.h - 1 : ℕ) : ℚ) ≤
      (hyp.base.p * hyp.base.q : ℚ) * ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) := by
    rw [div_mul_cancel₀ _ (ne_of_gt hpq_posQ)] at hmul
    nlinarith [hmul]
  have hsub_ltQ : ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) <
      (hyp.base.p * hyp.base.q : ℚ) := by
    have hsub_lt : hyp.base.p * hyp.base.q - 1 < hyp.base.p * hyp.base.q := by omega
    exact_mod_cast hsub_lt
  have hpow_ltQ : ((hyp.base.p ^ hyp.base.q : ℕ) : ℚ) < ((nc.h - 1 : ℕ) : ℚ) := by
    exact_mod_cast hpow_lt_h
  have hright_lt_sq :
      (hyp.base.p * hyp.base.q : ℚ) * ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) <
        (hyp.base.p * hyp.base.q : ℚ) * (hyp.base.p * hyp.base.q : ℚ) :=
    mul_lt_mul_of_pos_left hsub_ltQ hpq_posQ
  have hpq_sqQ : ((hyp.base.p ^ hyp.base.q : ℕ) : ℚ) <
      ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ^ 2 := by
    calc
      ((hyp.base.p ^ hyp.base.q : ℕ) : ℚ) < ((nc.h - 1 : ℕ) : ℚ) := hpow_ltQ
      _ ≤ (hyp.base.p * hyp.base.q : ℚ) *
          ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) := hleQ
      _ < (hyp.base.p * hyp.base.q : ℚ) * (hyp.base.p * hyp.base.q : ℚ) :=
        hright_lt_sq
      _ = ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ^ 2 := by
        norm_num [Nat.cast_mul, pow_two]
  have hpq_sq_nat : hyp.base.p ^ hyp.base.q < (hyp.base.p * hyp.base.q) ^ 2 := by
    exact_mod_cast hpq_sqQ
  exact p_pow_sub_two_lt_q_sq_of_pow_lt_mul_sq hyp.base.q_prime.two_le hpq_sq_nat

/-- **Peterfalvi (14.15)**: the final numerical contradiction for the
case-(a) branch of (14.14). Once the bound is specialized to `(q,p) = (3,7)`,
it is incompatible with `h ≥ 31 * 19`. -/
theorem caseA_bound_contradiction_of_h_ge_thirty_one_mul_nineteen
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseA : data.caseA)
    (hq3 : hyp.base.q = 3) (hp7 : hyp.base.p = 7) (hh : 31 * 19 ≤ nc.h) :
    False := by
  have hbound := data.caseA_bound hcaseA
  rw [hq3, hp7] at hbound
  norm_num at hbound
  have hleQ : ((nc.h - 1 : ℕ) : ℚ) ≤ 420 := by nlinarith [hbound]
  have hle : nc.h - 1 ≤ 420 := by exact_mod_cast hleQ
  have hge : 588 ≤ nc.h - 1 := by omega
  omega

/-- **Peterfalvi (14.15)**: arithmetic spine of the non-full cyclotomic
case-(a) branch. Once the preceding group-theoretic part of the paragraph has
supplied `p ≡ 1 mod q`, the lower comparison `p^q < h - 1`, and
`h ≥ 31 * 19`, the case-(a) bound forces `q = 3`, then `p = 7`, and finally
the numerical contradiction `31 * 19 - 1 ≤ 20 * 21`. -/
theorem caseA_contradiction_of_p_modEq_one_and_h_bounds
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseA : data.caseA)
    (hmod : hyp.base.p ≡ 1 [MOD hyp.base.q])
    (hpow_lt_h : hyp.base.p ^ hyp.base.q < nc.h - 1)
    (hh : 31 * 19 ≤ nc.h) :
    False := by
  have hpq2 := data.p_pow_q_sub_two_lt_q_sq_of_p_pow_lt_h_sub_one hcaseA hpow_lt_h
  have hq3 := hyp.q_eq_three_of_p_pow_q_sub_two_lt_q_sq hpq2
  have hp_lt_q_sq : hyp.base.p < hyp.base.q ^ 2 := by
    simpa [hq3] using hpq2
  have hp7 :=
    hyp.p_eq_seven_of_q_eq_three_modEq_one_and_lt_q_sq hq3 hmod hp_lt_q_sq
  exact data.caseA_bound_contradiction_of_h_ge_thirty_one_mul_nineteen
    hcaseA hq3 hp7 hh

/-- **Peterfalvi (14.15)**: the non-full cyclotomic branch of the case-(a)
comparison.  If `u` is not the full cyclotomic quotient, then the S-side
case-(9.7.b) order formula puts us in the `p ≡ 1 mod q` branch and gives the
divided cyclotomic value of `u`.  Together with the `h = u * x` decomposition
and the fixed-point-free congruence/parity estimate for `x`, the case-(a) bound
forces `q = 3`, `p = 7`, `u = 19`, `x ≥ 31`, and hence the final numerical
contradiction. -/
theorem caseA_contradiction_of_nonfull_u_data
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    {x n : ℕ} (hh_eq : nc.h = hyp.base.u * x)
    (hx_eq : x = hyp.base.q + n * hyp.base.p)
    (hn_mod : n ≡ 1 [MOD hyp.base.q]) (hx_odd : Odd x) :
    False := by
  have hmod : hyp.base.p ≡ 1 [MOD hyp.base.q] := by
    by_contra hnot_mod
    exact hu_not_full (Sdata.u_eq_of_not_modEq_one hnot_mod)
  have hpow_lt_h :=
    Sdata.p_pow_lt_h_sub_one_of_nonfull_decomposition
      hu_not_full hh_eq hx_eq hn_mod hx_odd
  have hpq2 := data.p_pow_q_sub_two_lt_q_sq_of_p_pow_lt_h_sub_one hcaseA hpow_lt_h
  have hq3 := hyp.q_eq_three_of_p_pow_q_sub_two_lt_q_sq hpq2
  have hp_lt_q_sq : hyp.base.p < hyp.base.q ^ 2 := by
    simpa [hq3] using hpq2
  have hp7 :=
    hyp.p_eq_seven_of_q_eq_three_modEq_one_and_lt_q_sq hq3 hmod hp_lt_q_sq
  have hu19 : hyp.base.u = 19 := by
    have hu := Sdata.u_eq_of_p_modEq_one hmod
    rw [hq3, hp7] at hu
    norm_num at hu
    exact hu
  have hx_min : hyp.base.q + (1 + hyp.base.q) * hyp.base.p ≤ x :=
    hyp.x_ge_caseA_min_of_decomposition_modEq_and_odd hx_eq hn_mod hx_odd
  have hx31 : 31 ≤ x := by
    have hx := hx_min
    rw [hq3, hp7] at hx
    norm_num at hx
    exact hx
  have hh_ge : 31 * 19 ≤ nc.h := by
    rw [hh_eq, hu19]
    nlinarith [hx31]
  exact data.caseA_bound_contradiction_of_h_ge_thirty_one_mul_nineteen
    hcaseA hq3 hp7 hh_ge

/-- **Peterfalvi (14.15)**: consumer form of the non-full case-(a) branch with
only the cardinal/congruence inputs left from (14.5) and the fixed-point-free
`W₁` action.  The congruence theorem above derives `x = q + n p` and
`n ≡ 1 mod q`; the numerical part then closes the case-(a) contradiction. -/
theorem caseA_contradiction_of_nonfull_card_congruences
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    {x : ℕ} (hh_eq : nc.h = hyp.base.u * x)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hx_mod_q : x ≡ 1 [MOD hyp.base.q]) (hx_odd : Odd x) :
    False := by
  rcases Sdata.exists_x_decomposition_of_nonfull_card_congruences
      hu_not_full hh_eq hh_mod_p hx_mod_q with ⟨n, hx_eq, hn_mod⟩
  exact data.caseA_contradiction_of_nonfull_u_data
    Sdata hcaseA hu_not_full hh_eq hx_eq hn_mod hx_odd

/-- **Peterfalvi (14.15)**: quotient form of the non-full case-(a) branch.
Once the group-theoretic part of (14.5) has supplied `u ∣ h`, `h ≡ 1 mod p`,
and the fixed-point-free congruence for the quotient `x = h / u`, the oddness
of `x` is no longer an input: it follows from `h = |H|` in the ambient
odd-order group. -/
theorem caseA_contradiction_of_nonfull_card_divisibility
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hx_mod_q_of_quotient :
      ∀ x : ℕ, nc.h = hyp.base.u * x → x ≡ 1 [MOD hyp.base.q]) :
    False := by
  rcases hu_dvd_h with ⟨x, hh_eq⟩
  have hx_mod_q : x ≡ 1 [MOD hyp.base.q] := hx_mod_q_of_quotient x hh_eq
  have hh_odd : Odd nc.h := nc.h_odd _hG
  have hux_odd : Odd (hyp.base.u * x) := by
    rw [← hh_eq]
    exact hh_odd
  have hx_odd : Odd x := (Nat.odd_mul.mp hux_odd).2
  exact data.caseA_contradiction_of_nonfull_card_congruences
    Sdata hcaseA hu_not_full hh_eq hh_mod_p hx_mod_q hx_odd

/-- **Peterfalvi (14.15)**: fixed-point-free cardinal-congruence form of the
non-full case-(a) branch.  If the `W₁` action gives both `h ≡ 1 mod q` and
`u ≡ 1 mod q`, then for any quotient decomposition `h = u * x` the quotient
itself satisfies `x ≡ 1 mod q`, which is the congruence used in the displayed
`x = q + n p` calculation. -/
theorem caseA_contradiction_of_nonfull_fpf_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q]) :
    False := by
  exact data.caseA_contradiction_of_nonfull_card_divisibility
    _hG Sdata hcaseA hu_not_full hu_dvd_h hh_mod_p (fun x hh_eq => by
      have hux_mod_q : hyp.base.u * x ≡ x [MOD hyp.base.q] := by
        simpa [one_mul] using hu_mod_q.mul_right x
      have hh_mod_x : nc.h ≡ x [MOD hyp.base.q] := by
        rw [hh_eq]
        exact hux_mod_q
      exact hh_mod_x.symm.trans hh_mod_q)

/-- **Peterfalvi (14.16)**: the case-(a) branch cannot occur when `H` is
properly larger than `U`, once (14.15) and the fixed-point-free cardinal
congruences have been materialized.  The proof follows Peterfalvi's paragraph:
`x ≡ 1 mod p q` and odd `x ≠ 1` give `x > 2 p q`; the case-(a) bound then
forces `2 u < p q`, contradicting `u ≡ 1 mod p q` and `u > 2 q`. -/
theorem caseA_contradiction_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_full : hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    False := by
  rcases hu_dvd_h with ⟨x, hh_eq⟩
  have hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p] := by
    rw [hu_full]
    exact cyclotomic_quotient_modEq_one_mod_base
      hyp.base.p_prime.two_le hyp.base.q_prime.pos
  have hx_mod_p : x ≡ 1 [MOD hyp.base.p] := by
    have hux_mod_p : hyp.base.u * x ≡ x [MOD hyp.base.p] := by
      simpa [one_mul] using hu_mod_p.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.p] := by
      rw [hh_eq]
      exact hux_mod_p
    exact hh_mod_x.symm.trans hh_mod_p
  have hx_mod_q : x ≡ 1 [MOD hyp.base.q] := by
    have hux_mod_q : hyp.base.u * x ≡ x [MOD hyp.base.q] := by
      simpa [one_mul] using hu_mod_q.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.q] := by
      rw [hh_eq]
      exact hux_mod_q
    exact hh_mod_x.symm.trans hh_mod_q
  have hh_odd : Odd nc.h := nc.h_odd _hG
  have hux_odd : Odd (hyp.base.u * x) := by
    rw [← hh_eq]
    exact hh_odd
  have hx_odd : Odd x := (Nat.odd_mul.mp hux_odd).2
  have hx_gt : 2 * (hyp.base.p * hyp.base.q) < x :=
    hyp.quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q
      hx_mod_p hx_mod_q hx_odd (hx_ne_one_of_quotient x hh_eq)
  have hu_pos : 0 < hyp.base.u := by
    have h2q := Sdata.two_q_lt_u
    omega
  have h_lower : 2 * (hyp.base.p * hyp.base.q) * hyp.base.u < nc.h := by
    have hmul :
        hyp.base.u * (2 * (hyp.base.p * hyp.base.q)) < hyp.base.u * x :=
      Nat.mul_lt_mul_of_pos_left hx_gt hu_pos
    rw [hh_eq]
    nlinarith
  have hbound := data.caseA_bound hcaseA
  have hpq_pos_nat : 0 < hyp.base.p * hyp.base.q :=
    Nat.mul_pos hyp.base.p_prime.pos hyp.base.q_prime.pos
  have hpq_posQ : (0 : ℚ) < (hyp.base.p * hyp.base.q : ℚ) := by
    exact_mod_cast hpq_pos_nat
  have hmul_bound := mul_le_mul_of_nonneg_right hbound (le_of_lt hpq_posQ)
  have h_upper_Q : ((nc.h - 1 : ℕ) : ℚ) ≤
      (hyp.base.p * hyp.base.q : ℚ) *
        ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) := by
    rw [div_mul_cancel₀ _ (ne_of_gt hpq_posQ)] at hmul_bound
    nlinarith [hmul_bound]
  have h_upper_sub : nc.h - 1 ≤
      (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q - 1) := by
    exact_mod_cast h_upper_Q
  have h_upper : nc.h ≤
      (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q - 1) + 1 := by
    omega
  have htwo_u_lt_pq : 2 * hyp.base.u < hyp.base.p * hyp.base.q := by
    by_contra hnot
    have hpq_le_2u : hyp.base.p * hyp.base.q ≤ 2 * hyp.base.u :=
      Nat.le_of_not_gt hnot
    have hpq_sq_le :
        (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) ≤
          (hyp.base.p * hyp.base.q) * (2 * hyp.base.u) :=
      Nat.mul_le_mul_left (hyp.base.p * hyp.base.q) hpq_le_2u
    have hupper_lt_sq :
        (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q - 1) + 1 <
          (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) := by
      have hpq_gt_one : 1 < hyp.base.p * hyp.base.q := by
        nlinarith [hyp.base.p_prime.one_lt, hyp.base.q_prime.one_lt]
      have hs :
          (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) =
            (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q - 1) +
              (hyp.base.p * hyp.base.q) := by
        rw [← Nat.mul_succ]
        have : (hyp.base.p * hyp.base.q - 1).succ = hyp.base.p * hyp.base.q := by
          omega
        rw [this]
      rw [hs]
      omega
    nlinarith [hpq_sq_le, h_lower, h_upper, hupper_lt_sq]
  have hpq_coprime : Nat.Coprime hyp.base.p hyp.base.q :=
    (Nat.coprime_primes hyp.base.p_prime hyp.base.q_prime).mpr hyp.p_ne_q
  have hu_mod_pq : hyp.base.u ≡ 1 [MOD hyp.base.p * hyp.base.q] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hpq_coprime).mp ⟨hu_mod_p, hu_mod_q⟩
  have hu_gt_one : 1 < hyp.base.u := by
    have h2q := Sdata.two_q_lt_u
    nlinarith [hyp.base.q_prime.one_lt]
  rcases (Nat.modEq_iff_exists_eq_add (le_of_lt hu_gt_one)).mp hu_mod_pq.symm with
    ⟨t, hu_eq⟩
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    rw [ht0, mul_zero, add_zero] at hu_eq
    omega
  have ht_ge_one : 1 ≤ t := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ht_ne_zero)
  have hu_ge_pq_add_one : hyp.base.p * hyp.base.q + 1 ≤ hyp.base.u := by
    rw [hu_eq]
    have hmul := Nat.mul_le_mul_left (hyp.base.p * hyp.base.q) ht_ge_one
    nlinarith
  nlinarith [htwo_u_lt_pq, hu_ge_pq_add_one]

/-- **Peterfalvi (14.16)**: cardinal/congruence lower bound for the proper
`H > U` alternative.  From `h = u x`, the full cyclotomic value for `u`, and
the fixed-point-free congruences, the quotient satisfies `x ≡ 1 mod p q`; if
`x ≠ 1`, oddness forces `x > 2 p q`, hence `h > 2 p q u`. -/
theorem h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (hu_full : hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    2 * (hyp.base.p * hyp.base.q) * hyp.base.u < nc.h := by
  rcases hu_dvd_h with ⟨x, hh_eq⟩
  have hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p] := by
    rw [hu_full]
    exact cyclotomic_quotient_modEq_one_mod_base
      hyp.base.p_prime.two_le hyp.base.q_prime.pos
  have hx_mod_p : x ≡ 1 [MOD hyp.base.p] := by
    have hux_mod_p : hyp.base.u * x ≡ x [MOD hyp.base.p] := by
      simpa [one_mul] using hu_mod_p.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.p] := by
      rw [hh_eq]
      exact hux_mod_p
    exact hh_mod_x.symm.trans hh_mod_p
  have hx_mod_q : x ≡ 1 [MOD hyp.base.q] := by
    have hux_mod_q : hyp.base.u * x ≡ x [MOD hyp.base.q] := by
      simpa [one_mul] using hu_mod_q.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.q] := by
      rw [hh_eq]
      exact hux_mod_q
    exact hh_mod_x.symm.trans hh_mod_q
  have hh_odd : Odd nc.h := nc.h_odd _hG
  have hux_odd : Odd (hyp.base.u * x) := by
    rw [← hh_eq]
    exact hh_odd
  have hx_odd : Odd x := (Nat.odd_mul.mp hux_odd).2
  have hx_gt : 2 * (hyp.base.p * hyp.base.q) < x :=
    hyp.quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q
      hx_mod_p hx_mod_q hx_odd (hx_ne_one_of_quotient x hh_eq)
  have hu_pos : 0 < hyp.base.u := Odd.pos (Nat.odd_mul.mp hux_odd).1
  have hmul :
      hyp.base.u * (2 * (hyp.base.p * hyp.base.q)) < hyp.base.u * x :=
    Nat.mul_lt_mul_of_pos_left hx_gt hu_pos
  rw [hh_eq]
  nlinarith

/-- **Peterfalvi (14.16)**: the numerical gap in the exceptional branch.  If
case-(b) has `(q,p)=(3,5)` and `H > U`, then the lower bound `h > 2 p q u`
gives `(h - 1)/(p q) > (v - 1)/p`; the concrete values `u=31`, `v=121` also
give `(v - 1)/p > (u - 1)/q`. -/
theorem caseB_gap_inequalities_of_h_gt_two_mul_pq_mul_u
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Tdata : CaseBForTData hyp)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB)
    (hh_lower : 2 * (hyp.base.p * hyp.base.q) * hyp.base.u < nc.h) :
    (((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  have hparams := data.caseB_params hcaseB
  have hu31 := data.u_eq_thirty_one_of_caseB Sdata hcaseB
  have hv121 := data.v_eq_one_twenty_one_of_caseB Tdata hcaseB
  have hh930 : 930 < nc.h := by
    have h := hh_lower
    rw [hparams.1, hparams.2, hu31] at h
    norm_num at h
    exact h
  have hh_sub_ge : 930 ≤ nc.h - 1 := by omega
  constructor
  · have hgeQ : (930 : ℚ) ≤ ((nc.h - 1 : ℕ) : ℚ) := by
      exact_mod_cast hh_sub_ge
    have hgt : (24 : ℚ) < ((nc.h - 1 : ℕ) : ℚ) / 15 := by
      nlinarith
    rw [hparams.1, hparams.2, hv121]
    norm_num
    exact hgt
  · rw [hparams.1, hparams.2, hu31, hv121]
    norm_num

/-- **Peterfalvi (14.16)**: the S-side gap in the exceptional branch
excludes case-(c1) of (13.19.c).  After identifying the Type-I kernel with the
current `H` and the complement index with `p q`, the inequality
`(h - 1)/(p q) > (v - 1)/p > (u - 1)/q` is exactly the strict negation of the
case-(c1) bound, so the parity alternative (c2) must hold. -/
theorem typeI_caseC2_of_caseB_sSide_gap
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L)
    (hcases : orth.caseC1 ∨ orth.caseC2)
    (hH : Nat.card ↥orth.typeISetup.H = nc.h)
    (he : orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    orth.caseC2 := by
  apply orth.caseC2_of_gap hcases
  rw [hH, he]
  exact hvu.trans hhv

/-- **Peterfalvi (14.16)**: the T-side gap in the exceptional branch excludes
the dual case-(c1) of (13.19.c).  This is the symmetric input producing the
`eta_i0` parity congruences. -/
theorem typeI_caseC2_of_caseB_tSide_gap
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L)
    (hcases : orth.caseC1_dual ∨ orth.caseC2_dual)
    (hH : Nat.card ↥orth.typeISetup.H = nc.h)
    (he : orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) :
    orth.caseC2_dual := by
  apply orth.caseC2_dual_of_gap hcases
  rw [hH, he]
  exact hhv

/-- **Peterfalvi (14.16)**: the two numerical gaps in case-(b) force both
(13.19.c2) parity alternatives, the S-side one for the `eta_0j` row and the
T-side swapped one for the `eta_i0` column. -/
theorem typeI_caseC2_pair_of_caseB_gap
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L)
    (hcases : orth.caseC1 ∨ orth.caseC2)
    (hcases_dual : orth.caseC1_dual ∨ orth.caseC2_dual)
    (hH : Nat.card ↥orth.typeISetup.H = nc.h)
    (he : orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    orth.caseC2 ∧ orth.caseC2_dual := by
  exact ⟨typeI_caseC2_of_caseB_sSide_gap orth hcases hH he hhv hvu,
    typeI_caseC2_of_caseB_tSide_gap orth hcases_dual hH he hhv⟩

/-- **Peterfalvi (14.16)**: after the case-(b) gaps force both alternatives
(13.19.c2), the usable character output is odd integer pairing on the two
zero-axis families `eta_0j` and `eta_i0`. -/
theorem typeI_eta_axes_odd_of_caseB_gap
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L)
    (hcases : orth.caseC1 ∨ orth.caseC2)
    (hcases_dual : orth.caseC1_dual ∨ orth.caseC2_dual)
    (hH : Nat.card ↥orth.typeISetup.H = nc.h)
    (he : orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    (∀ j : Fin hyp.base.p, (j : ℕ) ≠ 0 →
        OddOrder.Peterfalvi.S15.OddIntegerInner orth.betaL
          (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j)) ∧
      (∀ i : Fin hyp.base.q, (i : ℕ) ≠ 0 →
        OddOrder.Peterfalvi.S15.OddIntegerInner orth.betaL
          (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)) := by
  exact orth.eta_axes_odd_of_caseC2_pair
    (typeI_caseC2_pair_of_caseB_gap orth hcases hcases_dual hH he hhv hvu)

/-- **Peterfalvi (14.16)**: combining the actual (13.19) Type-I
orthogonality output for `L` with the case-(b) numerical gaps gives the two
zero-axis odd pairings needed for the final `eta_ij` expansion.  The remaining
inputs identify the abstract kernel and complement index in the (13.19) data
with the `H` and `p q` already fixed in Section 16. -/
theorem exists_typeI_eta_axes_odd_of_caseB_gap
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (hH_of_orth :
      ∀ orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L,
        Nat.card ↥orth.typeISetup.H = nc.h)
    (he_of_orth :
      ∀ orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L,
        orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    ∃ orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L,
      (∀ j : Fin hyp.base.p, (j : ℕ) ≠ 0 →
          OddOrder.Peterfalvi.S15.OddIntegerInner orth.betaL
            (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j)) ∧
        (∀ i : Fin hyp.base.q, (i : ℕ) ≠ 0 →
          OddOrder.Peterfalvi.S15.OddIntegerInner orth.betaL
            (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)) := by
  rcases OddOrder.Peterfalvi.S15.typeI_orthogonality_dichotomy
      _hG hyp.base nc.Ldata.L_maximal nc.Ldata.isTypeI with
    ⟨orth, horth⟩
  exact ⟨orth, typeI_eta_axes_odd_of_caseB_gap orth horth.2.2.2.1 horth.2.2.2.2
    (hH_of_orth orth) (he_of_orth orth) hhv hvu⟩

/-- Pointwise-in-the-left additivity of the canonical class-function inner product over a finite
sum: `(∑ i ∈ s, f i, ψ) = ∑ i ∈ s, (f i, ψ)`.  General-purpose `ClassFunction.inner` plumbing
(hoistable to `ClassFunction.lean`). -/
theorem inner_finset_sum_left {ι : Type*} [Fintype G]
    [Invertible (Nat.card G : ℂ)] (s : Finset ι)
    (f : ι → ClassFunction G ℂ) (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (∑ i ∈ s, f i) ψ = ∑ i ∈ s, ClassFunction.inner (f i) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, ClassFunction.inner_add_left, ih, Finset.sum_insert ha]

/-- **Faithful §16 carrier for the (14.16) case-(b) contradiction inputs.**

Under case-(b) of (14.14) (`(β_L^τ, ψ^{τ₁}) ≠ 0`, `q = 3`, `p = 5`) and the two strict gap
inequalities, the §16 character theory supplies (Pf (14.16), p.92):

* `betaL_expansion` — the (14.11.2)-style signed `η`-grid expansion `β_L^τ = Σ_{ij} ±η_ij − χ_L`
  (`χ_L = φ^{τ₁}` or `−φ̄^{τ₁}`), derived from `(13.19.c)` applied on both the S- and T-sides
  (`exists_typeI_eta_axes_odd_of_caseB_gap`) plus the vanishing of `β_L^τ` on `W − (W₁ ∪ W₂)`;
* `eta_orthogonal_psi` — `(η_ij, ψ^{τ₁}) = 0`: `ψ^{τ₁}` is the unit-norm component removed from the
  `η`-grid in the M-side expansion (14.11.2), hence orthogonal to the whole grid;
* `chiL_orthogonal_psi` — `(χ_L, ψ^{τ₁}) = 0`: by (4.1), `L^{τ₁}` is orthogonal to `M^{τ₁}`, and
  `χ_L ∈ L^{τ₁}`, `ψ^{τ₁} ∈ M^{τ₁}`;
* `pairing_ne_zero` — `(β_L^τ, ψ^{τ₁}) ≠ 0`, the defining property of case-(b) (14.14.b).

The genuine character theory (the expansion via (14.11.2)/(13.19.c), the orthogonalities via
(14.11.2)/(4.1), and the case-(b) pairing via (14.14)) is isolated here; the contradiction itself
is then the pure inner-product computation `(β_L^τ, ψ^{τ₁}) = 0`. -/
structure CaseBContradictionData {hyp : Hypothesis (G := G)}
    (nc : NonConjugateHypothesis hyp) [Fintype G] [Invertible (Nat.card G : ℂ)] where
  /-- The L-side virtual character `β_L^τ`. -/
  betaL : ClassFunction G ℂ
  /-- The removed unit-norm L-side character `χ_L` (`= φ^{τ₁}` or `−φ̄^{τ₁}`). -/
  chiL : ClassFunction G ℂ
  /-- The M-side test character `ψ^{τ₁}` (the coherent `ν`-image of the distinguished
  `ζ` — carried as a field so the whole datum is bundle-local; the (14.16) contradiction
  is a pure inner-product computation in the four fields and never needs the anchor
  `ψ^{τ₁} = nc.Mdata.tau1 nc.Mdata.psi` itself). -/
  psiImg : ClassFunction G ℂ
  /-- The `±1` signs of the `η`-grid expansion. -/
  signs : Fin hyp.base.q → Fin hyp.base.p → ℤ
  signs_pm_one : ∀ i j, signs i j = 1 ∨ signs i j = -1
  /-- **(14.16)** signed `η`-grid expansion `β_L^τ = Σ_{ij} ε_ij η_ij − χ_L`. -/
  betaL_expansion :
    betaL =
      (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (signs i j : ℂ) • hyp.base.eta i j) - chiL
  /-- **(14.11.2)**: `ψ^{τ₁}` is orthogonal to the `η`-grid. -/
  eta_orthogonal_psi : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
    ClassFunction.inner (hyp.base.eta i j) psiImg = 0
  /-- **(4.1)**: `χ_L ∈ L^{τ₁}` is orthogonal to `ψ^{τ₁} ∈ M^{τ₁}`. -/
  chiL_orthogonal_psi :
    ClassFunction.inner chiL psiImg = 0
  /-- **(14.14.b)**: the case-(b) nonzero pairing `(β_L^τ, ψ^{τ₁}) ≠ 0`. -/
  pairing_ne_zero :
    ClassFunction.inner betaL psiImg ≠ 0

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.b), the M-side `η`-grid orthogonality of `ψ^{τ₁} = ζ_M^ν`.**

The distinguished coherent image `ψ^{τ₁} = ζ_M^ν` (`= (dataM.h78 hG).nu (ζ_{zetaDistinct})`)
is orthogonal to the entire `η`-grid.  This is the sorry-free (3.6)–(3.8)/(13.19.b) engine
`eta_orthogonal_of_norm_one_pair_vanish` (`S16_GridExpansion`) applied to the conjugate pair
`(ζ_M^ν, ζ̄_M^ν)`: the unit norms (`nu_zeta_norm_one`), the conjugate distinctness
`⟨ζ_M^ν, ζ̄_M^ν⟩ = 0` (`nu_zeta_inner_nu_conj_eq_zero`), and the `ℤ[Irr G]` memberships
(`coh.extension_mem_ZIrr` on `ζ ∈ 𝒮`) are all supplied by the `TypeICoherent78Data` coherence
bundle.  The single genuine §13/§14 input is `hDadeAvoid` = **Peterfalvi (13.19.a)**: the M-side
Dade support `Ã(M)` avoids the regular-set saturation `Ŵ^G = (W ∖ (W₁ ∪ W₂))^G`, so the
conjugate difference `ζ_M^ν − ζ̄_M^ν` (supported in `Ã(M)`, `nu_zeta_sub_conj_support_at`)
vanishes on `Ŵ^G`. -/
theorem caseB_eta_orthogonal_psi [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (dataM : TypeICoherent78Data M)
    (hDadeAvoid : ∀ x ∈ conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j)
        ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct)) = 0 := by
  classical
  -- distinctness datum for the distinguished index `zetaDistinct = 0` and its conjugate `i'`
  have hjne : (dataM.h78 hG).zetaDistinct ≠ dataM.ind1H := by
    have h := (dataM.h78 hG).zetaDistinct_ne_ind1H
    rwa [dataM.h78_ind1H_eq] at h
  obtain ⟨i', hi'_ne, hi'⟩ := dataM.exists_conjIndex_at hG hjne
  -- engine inputs from the coherence bundle
  have hpsiZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct)
      ∈ ZIrr G := by
    rw [dataM.h78_nu_eq, dataM.h78_zetaDistinct_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset (Ne.symm dataM.ind1H_ne_zero)))
  have hconjZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta i') ∈ ZIrr G := by
    have hi'ne_data : i' ≠ dataM.ind1H := by rw [← dataM.h78_ind1H_eq]; exact hi'_ne
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hi'ne_data))
  have hpsi1 := dataM.nu_zeta_norm_one hG (dataM.h78 hG).zetaDistinct_ne_ind1H
  have hconj1 := dataM.nu_zeta_norm_one hG hi'_ne
  have hcross := dataM.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hjne hi'_ne hi'
  have hsupp := dataM.nu_zeta_sub_conj_support_at hG hjne hi'_ne hi'
  have hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct)
        - (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta i')) x = 0 := by
    intro x hx
    by_contra hval
    exact hDadeAvoid x hx (hsupp (ClassFunction.mem_support.mpr hval))
  exact eta_orthogonal_of_norm_one_pair_vanish hyp hpsiZ hconjZ hpsi1 hconj1 hcross hvanish

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.b), the `η`-grid orthogonality of *every* coherent image `ζ_k^ν`**
(the Coq `o_tauLeta` for the whole family, not just the distinguished index).  For any family
member `k ≠ ind1H`, the coherent image `ζ_k^ν = (dataM.h78 hG).nu (ζ_k)` is orthogonal to the
entire `η`-grid.  Identical (3.6)–(3.8)/(13.19.b) engine as `caseB_eta_orthogonal_psi`, but with
the distinguished index `zetaDistinct` replaced by an arbitrary `k`: `ζ_k^ν` has unit norm
(`nu_zeta_norm_one`), its conjugate partner `ζ_{k'}^ν` (`exists_conjIndex_at`, generic in the
index) is a distinct unit-norm virtual character (`nu_zeta_inner_nu_conj_eq_zero`), and the
conjugate difference `ζ_k^ν − ζ_{k'}^ν` (supported in `Ã(M)`, `nu_zeta_sub_conj_support_at`,
also generic) vanishes on `Ŵ^G` by the same (13.19.a) Dade-support avoidance `hDadeAvoid`. -/
theorem caseB_eta_orthogonal_nu_zeta_at [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (dataM : TypeICoherent78Data M)
    (hDadeAvoid : ∀ x ∈ conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport)
    {k : Fin (dataM.n + 1)} (hk : k ≠ (dataM.h78 hG).ind1H) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j)
        ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k)) = 0 := by
  classical
  -- the kernel-index datum for `k` and its conjugate partner `k'`
  have hkne : k ≠ dataM.ind1H := by rwa [dataM.h78_ind1H_eq] at hk
  obtain ⟨k', hk'_ne, hk'⟩ := dataM.exists_conjIndex_at hG hkne
  -- engine inputs from the coherence bundle
  have hpsiZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k) ∈ ZIrr G := by
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hkne))
  have hconjZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k') ∈ ZIrr G := by
    have hk'ne_data : k' ≠ dataM.ind1H := by rw [← dataM.h78_ind1H_eq]; exact hk'_ne
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hk'ne_data))
  have hpsi1 := dataM.nu_zeta_norm_one hG hk
  have hconj1 := dataM.nu_zeta_norm_one hG hk'_ne
  have hcross := dataM.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hkne hk'_ne hk'
  have hsupp := dataM.nu_zeta_sub_conj_support_at hG hkne hk'_ne hk'
  have hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k)
        - (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k')) x = 0 := by
    intro x hx
    by_contra hval
    exact hDadeAvoid x hx (hsupp (ClassFunction.mem_support.mpr hval))
  exact eta_orthogonal_of_norm_one_pair_vanish hyp hpsiZ hconjZ hpsi1 hconj1 hcross hvanish

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), σ-decomposition ingredient**: the Fitting core `M_F`
(`dataM.kernel`) of the type-`I` maximal `M`, non-conjugate to the `W`-containing maximals
`S`, `T`, has order coprime to `p·q`.  In the Coq proof of `tiA_PWG` this is `coHp`/`coHq`
(`coprime #|H| p`, `coprime #|H| q` with `H = M_F`), derived from `FT_Dade_support_partition`:
`p, q ∈ σ(S) ∪ σ(T)` are disjoint from `σ(M)` for non-conjugate maximals (`nc.not_conj`).
Deep named §13/BG §10 obligation. -/
theorem card_kernel_coprime_pq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    {M : Subgroup G} (hMmax : M ∈ maximalSubgroups G) (dataM : TypeICoherent78Data M) :
    Nat.Coprime (Nat.card ↥dataM.kernel) (hyp.base.p * hyp.base.q) := by
  classical
  -- `M`, `S`, `T` are maximal; `M` type I, `S`/`T` type II
  have hMI : IsTypeI M := ⟨dataM.typeIHyp.typeI⟩
  have hSII : IsTypeII hyp.base.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.base.S_maximal hyp.base.S_typeP2
  have hTII : IsTypeII hyp.base.T := T_typeII hG hyp
  -- `M_F = M_σ`, `S_σ = P`, `T_σ = Q`
  have hMF : dataM.kernel = OddOrder.BG.Ch3.S10.Msigma M := by
    show dataM.typeIHyp.typeI.typeF.H = _
    rw [dataM.typeIHyp.typeI.typeF.H_eq]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hMmax (Or.inl hMI)
  have hMsS : OddOrder.BG.Ch3.S10.Msigma hyp.base.S = hyp.base.P := by
    rw [← OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hyp.base.S_maximal (Or.inr hSII)]
    exact hyp.base.P_eq_SF.symm
  have hMsT : OddOrder.BG.Ch3.S10.Msigma hyp.base.T = hyp.base.Q := by
    rw [← OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hyp.base.T_maximal (Or.inr hTII)]
    exact hyp.base.Q_eq_TF.symm
  -- `p ∈ σ(S)` (as `p = |W₂| ∣ |P| = |S_σ|`), `q ∈ σ(T)`
  have hpσS : hyp.base.p ∈ OddOrder.BG.Ch3.S10.sigma hyp.base.S := by
    rw [← OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hyp.base.S_maximal, hMsS]
    refine Nat.mem_primeFactors.mpr ⟨hyp.base.p_prime, ?_, Nat.card_pos.ne'⟩
    rw [hyp.base.p_eq_card_W2]
    exact Subgroup.card_dvd_of_le (OddOrder.Peterfalvi.S15.W2_le_P hG hyp.base)
  have hqσT : hyp.base.q ∈ OddOrder.BG.Ch3.S10.sigma hyp.base.T := by
    rw [← OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hyp.base.T_maximal, hMsT]
    refine Nat.mem_primeFactors.mpr ⟨hyp.base.q_prime, ?_, Nat.card_pos.ne'⟩
    rw [hyp.base.q_eq_card_W1]
    exact Subgroup.card_dvd_of_le (OddOrder.Peterfalvi.S15.W1_le_Q hG hyp.base)
  -- `M` is not conjugate to `S` or `T` (type I vs type non-I) ⟹ `σ`-disjointness
  have hMnS : ¬ ∃ g : G, MulAut.conj g • M = hyp.base.S :=
    OddOrder.Peterfalvi.S15.not_conj_of_isTypeI_of_isTypeNonI hG hMI hyp.base.S_maximal
      (Or.inl hSII)
  have hMnT : ¬ ∃ g : G, MulAut.conj g • M = hyp.base.T :=
    OddOrder.Peterfalvi.S15.not_conj_of_isTypeI_of_isTypeNonI hG hMI hyp.base.T_maximal
      (Or.inl hTII)
  have hdS := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hyp.base.S_maximal hMnS
  have hdT := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hyp.base.T_maximal hMnT
  -- hence `p, q ∉ σ(M) = π(|M_F|)`, so `p, q ∤ |M_F|`
  have hpMF : ¬ hyp.base.p ∣ Nat.card ↥dataM.kernel := by
    rw [hMF]; intro hdvd
    exact Set.disjoint_left.mp hdS
      ((OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hMmax hyp.base.p).mp
        (Nat.mem_primeFactors.mpr ⟨hyp.base.p_prime, hdvd, Nat.card_pos.ne'⟩)) hpσS
  have hqMF : ¬ hyp.base.q ∣ Nat.card ↥dataM.kernel := by
    rw [hMF]; intro hdvd
    exact Set.disjoint_left.mp hdT
      ((OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hMmax hyp.base.q).mp
        (Nat.mem_primeFactors.mpr ⟨hyp.base.q_prime, hdvd, Nat.card_pos.ne'⟩)) hqσT
  exact Nat.Coprime.mul_right
    (hyp.base.p_prime.coprime_iff_not_dvd.mpr hpMF).symm
    (hyp.base.q_prime.coprime_iff_not_dvd.mpr hqMF).symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), Dade-support ingredient**: every element `y` of the Dade support
`Ã(M) = ⋃_{x∈A(M)} (x·R(x))^G` has order *not* coprime to `|M_F|` (it is `π(M_F)`-singular).
Indeed `y` is conjugate to `x·r` with `x ∈ A(M) = M_F^#` (type-I, `1 ≠ x ∈ M_F`) and
`r ∈ R(x)` a signalizer commuting with `x` of order coprime to `|M_F|`, so
`1 < orderOf x ∣ orderOf y` and `orderOf x ∣ |M_F|`.  Deep named §8/§13 obligation
(the Dade signalizer `π`-part structure). -/
theorem dadeSupport_not_coprime_card_kernel [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (dataM : TypeICoherent78Data M)
    {y : G} (hy : y ∈ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport) :
    ¬ Nat.Coprime (orderOf y) (Nat.card ↥dataM.kernel) := by
  classical
  -- `y` is conjugate to `a·h` with `a ∈ A = M_F#`, `h ∈ H(a)` (the (8.14) signalizer)
  rw [dataM.h78_hyp_eq hG, OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_iff] at hy
  obtain ⟨a, h, hh, hconj⟩ := hy
  -- `a.1 ∈ M_F`, `a.1 ≠ 1` (`A = typeIA = M_F ∖ {1}`)
  have ha2 : a.1 ∈ (dataM.kernel : Set G) \ {1} := by
    rw [← dataM.typeIA_eq_sharp hG]; exact a.2
  have haK : a.1 ∈ dataM.kernel := ha2.1
  have hane : a.1 ≠ 1 := fun h1 => ha2.2 (Set.mem_singleton_iff.mpr h1)
  have hord_ne : orderOf a.1 ≠ 1 := fun h1 => hane (orderOf_eq_one_iff.mp h1)
  have hord_dvd : orderOf a.1 ∣ Nat.card ↥dataM.kernel := dataM.kernel.orderOf_dvd_natCard haK
  -- `h` commutes with `a.1`: `H(a) ≤ C_G(a.1)` by `(2.2.b)` `C_G(a.1) = H(a) ⊔ C_L(a.1)`
  have hh_cent : h ∈ Subgroup.centralizer ({a.1} : Set G) := by
    rw [(dataM.typeIHyp.dadeData.dade).centralizer_eq_sup a]
    exact Subgroup.mem_sup_left hh
  have hcomm : Commute a.1 h := (Subgroup.mem_centralizer_singleton_iff.mp hh_cent).symm
  -- `orderOf a.1` coprime `orderOf h`: `(2.2.c)` `(|H(a)|, |C_L(a.1)|) = 1`
  have hcop_orders : Nat.Coprime (orderOf a.1) (orderOf h) := by
    have hcc := (dataM.typeIHyp.dadeData.dade).centralizer_coprime a a
    have hord_h : orderOf h ∣ Nat.card ↥((dataM.typeIHyp.dadeData.dade).H a) :=
      ((dataM.typeIHyp.dadeData.dade).H a).orderOf_dvd_natCard hh
    have haCent : a.1 ∈ OddOrder.Peterfalvi.S04.centralizerIn M a.1 :=
      OddOrder.Peterfalvi.S04.mem_centralizerIn.mpr
        ⟨(dataM.typeIHyp.dadeData.dade).mem_L a.2, rfl⟩
    have hord_a : orderOf a.1 ∣ Nat.card ↥(OddOrder.Peterfalvi.S04.centralizerIn M a.1) :=
      (OddOrder.Peterfalvi.S04.centralizerIn M a.1).orderOf_dvd_natCard haCent
    exact (Nat.Coprime.coprime_dvd_right hord_a
      (Nat.Coprime.coprime_dvd_left hord_h hcc)).symm
  -- `orderOf y = orderOf(a.1·h) = orderOf a.1 · orderOf h`, so `orderOf a.1 ∣ orderOf y`
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hsemi : SemiconjBy c (a.1 * h) y := by
    change c * (a.1 * h) = y * c; rw [← hc]; group
  have hordy : orderOf y = orderOf a.1 * orderOf h := by
    rw [← SemiconjBy.orderOf_eq c hsemi,
      hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop_orders]
  have hdvd_y : orderOf a.1 ∣ orderOf y := by rw [hordy]; exact dvd_mul_right _ _
  -- `1 < orderOf a.1 ∣ gcd(orderOf y, |M_F|) = 1` is a contradiction
  intro hcop
  have hcop' : Nat.gcd (orderOf y) (Nat.card ↥dataM.kernel) = 1 := hcop
  have hgcd : orderOf a.1 ∣ Nat.gcd (orderOf y) (Nat.card ↥dataM.kernel) :=
    Nat.dvd_gcd hdvd_y hord_dvd
  rw [hcop'] at hgcd
  exact hord_ne (Nat.dvd_one.mp hgcd)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), the M-side Dade-support avoidance.**  For a type-`I` maximal
`M` not conjugate to the `W`-containing maximals `S`, `T`, the Dade support `Ã(M)` avoids the
regular-set saturation `Ŵ^G = (W ∖ (W₁ ∪ W₂))^G`.  This is the Coq `tiA_PWG`
(`'A~(L) :&: PWG = set0`, PFsection13): every `x ∈ Ŵ^G` is conjugate to a `w ∈ W`, so (as
`|W₁| = q`, `|W₂| = p` are prime and `W = W₁·W₂` commutes) `orderOf x ∣ p·q`, hence `orderOf x`
is coprime to `|M_F|` (`card_kernel_coprime_pq`); but every element of `Ã(M)` is
`π(M_F)`-singular (`dadeSupport_not_coprime_card_kernel`), a contradiction.  The two named
ingredients are the genuine BG §10-level σ-decomposition inputs. -/
theorem mSide_dadeSupport_avoids_regular [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    {M : Subgroup G} (hMmax : M ∈ maximalSubgroups G) (dataM : TypeICoherent78Data M) :
    ∀ x ∈ conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))),
      x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
  intro x hx hdade
  obtain ⟨w, ⟨hwW, _hwne⟩, g, hgx⟩ := hx
  -- `orderOf x = orderOf w` (conjugation preserves order)
  have hsemi : SemiconjBy g w x := by
    change g * w = x * g
    rw [← hgx]; group
  have hordx : orderOf x = orderOf w := (SemiconjBy.orderOf_eq g hsemi).symm
  -- decompose `w = a·b` with `a ∈ W₁`, `b ∈ W₂` inside the commutative `W`
  letI := hyp.base.W_cyclic
  letI : CommGroup ↥hyp.base.W := IsCyclic.commGroup
  have hwWmem : w ∈ hyp.base.W := hwW
  have hW1le : hyp.base.W1 ≤ hyp.base.W := by rw [hyp.base.W_eq_join]; exact le_sup_left
  have hW2le : hyp.base.W2 ≤ hyp.base.W := by rw [hyp.base.W_eq_join]; exact le_sup_right
  have hwmem : (⟨w, hwWmem⟩ : ↥hyp.base.W) ∈
      (hyp.base.W1.subgroupOf hyp.base.W) ⊔ (hyp.base.W2.subgroupOf hyp.base.W) := by
    have h1 : (hyp.base.W1 ⊔ hyp.base.W2).subgroupOf hyp.base.W = ⊤ := by
      rw [← hyp.base.W_eq_join, Subgroup.subgroupOf_self]
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, h1]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hwmem
  have hcoe : (a : G) * (b : G) = w := by
    have h := congrArg (Subtype.val) hab; simpa using h
  have haW1 : (a : G) ∈ hyp.base.W1 := Subgroup.mem_subgroupOf.mp ha
  have hbW2 : (b : G) ∈ hyp.base.W2 := Subgroup.mem_subgroupOf.mp hb
  -- `orderOf a ∣ q`, `orderOf b ∣ p` (Lagrange in the prime-order `W₁`, `W₂`)
  have haord : orderOf (a : G) ∣ hyp.base.q := by
    have h := hyp.base.W1.orderOf_dvd_natCard haW1
    rwa [← hyp.base.q_eq_card_W1] at h
  have hbord : orderOf (b : G) ∣ hyp.base.p := by
    have h := hyp.base.W2.orderOf_dvd_natCard hbW2
    rwa [← hyp.base.p_eq_card_W2] at h
  have hcomm : Commute (a : G) (b : G) := hyp.base.W1_commutes_W2 _ haW1 _ hbW2
  -- hence `orderOf x = orderOf w ∣ p·q`
  have hword : orderOf w ∣ hyp.base.p * hyp.base.q := by
    rw [← hcoe]
    refine hcomm.orderOf_mul_dvd_mul_orderOf.trans ?_
    rw [mul_comm hyp.base.p hyp.base.q]
    exact Nat.mul_dvd_mul haord hbord
  have hxord : orderOf x ∣ hyp.base.p * hyp.base.q := hordx ▸ hword
  -- `orderOf x` is coprime to `|M_F|`, contradicting `π(M_F)`-singularity of `Ã(M)`
  have hcop : Nat.Coprime (orderOf x) (Nat.card ↥dataM.kernel) :=
    Nat.Coprime.coprime_dvd_left hxord (card_kernel_coprime_pq hG hMmax dataM).symm
  exact dadeSupport_not_coprime_card_kernel hG dataM hdade hcop

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.2)/(13.19.a) consequence, the Coq `betaL_W_0`**: the coherence
residual `β_L = τ_L(Ind 1_H − φ)` (`(dataL.h78 hG).beta`) vanishes on the regular-set
saturation `Ŵ^G = (W ∖ (W₁ ∪ W₂))^G`.  `β_L` is supported in the Dade support `Ã(L)`
(`beta_support_subset_dadeSupport`), which avoids `Ŵ^G` by the fully-proven (13.19.a)
`mSide_dadeSupport_avoids_regular` (`L` is type-I, hence non-conjugate to the type-II
`W`-containing maximals `S`, `T`).  This is the first ingredient of the (14.11.2)/(13.19.c)
signed `η`-grid expansion (`lSide_signed_eta_expansion`). -/
theorem betaL_vanishes_on_regular_W [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L) :
    ∀ x ∈ conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))),
      (dataL.h78 hG).beta x = 0 := by
  intro x hx
  by_contra hval
  exact mSide_dadeSupport_avoids_regular hG hLmax dataL x hx
    ((dataL.h78 hG).beta_support_subset_dadeSupport (ClassFunction.mem_support.mpr hval))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.7) applied to `β_L`**: the grid coefficients `a_ij = ⟨β_L, η_ij⟩` of the
coherence residual satisfy the four-corner relation `a_ij + a_00 = a_i0 + a_0j`.  Immediate
from the (3.7) engine `inner_eta_grid_relation` (`S16_GridExpansion`) and
`betaL_vanishes_on_regular_W`.  This is the (3.7) linear-relation ingredient of the
(14.11.2)/(13.19.c) signed `η`-grid expansion. -/
theorem betaL_grid_relation [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L) (i : Fin hyp.base.q) (j : Fin hyp.base.p) :
    ClassFunction.inner (dataL.h78 hG).beta (hyp.base.eta i j)
        + ClassFunction.inner (dataL.h78 hG).beta
            (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩)
      = ClassFunction.inner (dataL.h78 hG).beta (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)
        + ClassFunction.inner (dataL.h78 hG).beta
            (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j) :=
  inner_eta_grid_relation hyp.base (betaL_vanishes_on_regular_W hG hLmax dataL) i j

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`β_L ∈ ℤ[Irr G]`**: the coherence residual `β_L = τ_L(Ind 1_H − ζ)` is a virtual character
(`beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible` on the bundle's `Ind 1_H`-virtuality and the
distinguished `ζ`-irreducibility).  This is the integrality input for the L-side grid coefficients
`m_ij = ⟨β_L, η_ij⟩`. -/
theorem betaL_mem_ZIrr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (dataL : TypeICoherent78Data L) :
    (dataL.h78 hG).beta ∈ ZIrr G :=
  (dataL.h78 hG).beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (dataL.h78_ind_mem_ZIrr hG) (dataL.h78_zeta_irreducible hG)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.2)/(13.19.c), integrality of the L-side grid coefficients** (Coq
`Cint_cfdot_vchar`): each `m_ij = ⟨β_L, η_ij⟩` is an integer, since both `β_L` (`betaL_mem_ZIrr`)
and `η_ij` (`eta_mem_ZIrr`) are virtual characters (`inner_mem_ZIrr_int`).  This is the fully-proven
`coeff` ingredient of the (14.11.2) grid-coefficient carrier `LSideGridCoeffData`, available to lane
c independently of the deep §13 grid-membership content. -/
theorem betaL_grid_coeff_int [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (dataL : TypeICoherent78Data L)
    (i : Fin hyp.base.q) (j : Fin hyp.base.p) :
    ∃ m : ℤ, ClassFunction.inner (dataL.h78 hG).beta (hyp.base.eta i j) = (m : ℂ) :=
  ClassFunction.inner_mem_ZIrr_int (betaL_mem_ZIrr hG dataL) (eta_mem_ZIrr hyp.base i j)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.2)/(13.19.c), the principal grid coefficient** (Coq `a00 = 1`):
`m_00 = ⟨β_L, η_00⟩ = 1`.  The principal grid member is the trivial character
`η_00 = 1_G` (`eta_principal_eq_trivial`), and the (7.8.a) Dade decomposition
`β_L = 1_G − ζ_0^ν + Δ_L` (`beta_eq_constOne_sub_zetaImage_add_delta`, PROVEN) pairs against it as
`⟨1_G, 1_G⟩ − ⟨ζ_0^ν, 1_G⟩ + ⟨Δ_L, 1_G⟩ = 1 − 0 + 0`, using `‖1_G‖² = 1`
(`constOne_inner_self_eq_one`), the (7.8.a) source orthogonality `ζ_0^ν ⊥ 1_G`
(`BetaDecomp.orth_one` at the distinguished index) and the residual orthogonality `Δ_L ⊥ 1_G`
(`delta_orth_one`).  This is the fully-proven principal-boundary ingredient of
`LSideGridCoeffData`, available to lane c independently of the deep off-principal parity
(Coq `FTtypeI_bridge_facts`). -/
theorem betaL_grid_coeff_principal_eq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (dataL : TypeICoherent78Data L) :
    ClassFunction.inner (dataL.h78 hG).beta
        (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩) = 1 := by
  -- `η_00 = 1_G = constOne`
  have heta : hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩
      = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G := by
    rw [eta_principal_eq_trivial hyp.base]
    exact ClassFunction.ext fun _ => rfl
  rw [heta, (dataL.h78 hG).beta_eq_constOne_sub_zetaImage_add_delta,
    ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one,
    (dataL.betaDecomp hG).orth_one (dataL.h78 hG).zetaDistinct
      (dataL.h78 hG).zetaDistinct_ne_ind1H,
    (dataL.h78 hG).delta_orth_one (dataL.betaDecomp hG)]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §14 Dade carrier for the L-side `η`-grid coefficients** (Peterfalvi (13.19.c),
Coq `FTtype2_support_coherence` core).  Bundles the facts about the integer grid coefficients
`m_ij = ⟨β_L, η_ij⟩` of the coherence residual `β_L = (dataL.h78 hG).beta`, from which
`lSide_delta_grid_expansion` proves the `±1` rigidity and the grid identity.  The two lane-c
available facts are proven in-place in the producer `lSideGridCoeffData`; only the S/T type-P
bridge and §13 grid content remain as the isolated gate:

* `coeff` — the coefficients are integers, `⟨β_L, η_ij⟩ = m_ij` (**PROVEN in-place**,
  `betaL_grid_coeff_int` via `inner_mem_ZIrr_int`; the witness `m` is the integer value);
* `m_principal` — the principal coefficient `m_00 = 1` (**PROVEN in-place**,
  `betaL_grid_coeff_principal_eq_one`: `η_00 = 1_G` and `β_L = 1_G − ζ_0^ν + Δ_L` pair as
  `1 − 0 + 0`);
* `m_row_odd`/`m_col_odd` — **off-principal boundary parity** (Coq `FTtypeI_bridge_facts`, the
  S/T-side type-P bridge `cycTIiso_cfdot_exchange`): `m_0j`, `m_i0` are *odd*; genuinely
  cross-lane-gated to the type-P `S`/`T` maximals (lane b's §13/§15 layer);
* `bessel` — **the (13.19.c) Bessel bound** (Coq `orthonormal_span` + `lb_b` + `ub_e`):
  `Σ_{ij} m_ij² ≤ p q`; needs the coherent-image/grid orthogonality `ζ_i^ν ⊥ η`-grid (Coq
  `o_tauLeta`) to match `β_L`'s grid projection with `(Γ_L + 1_G)`'s and apply `‖Γ_L‖² ≤ e − 1`,
  the same §13 residual content as `grid_mem`;
* `grid_mem` — **the grid membership** (Coq `Y = 0`, issue 3002): `1_G + Δ_L = Σ_{ij} m_ij η_ij`,
  i.e. `β_L + ζ_0^ν` equals its own orthogonal projection onto the `η`-grid.

These are genuine facts about the type-I maximal `L` (its Dade isometry, coherent extension, and
the S/T-partner bridge); the concrete construction of the three off-principal/grid facts is the
remaining §13/§14 obligation, isolated here away from the pure `±1` combinatorics. -/
structure LSideGridCoeffData [Finite G] (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : TypeICoherent78Data L)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) where
  /-- The integer grid coefficient `m_ij = ⟨β_L, η_ij⟩`. -/
  m : Fin hyp.base.q → Fin hyp.base.p → ℤ
  /-- `⟨β_L, η_ij⟩ = m_ij` (integrality, `inner_mem_ZIrr_int`).  **PROVEN in-place**. -/
  coeff : ∀ i j, ClassFunction.inner (dataL.h78 hG).beta (hyp.base.eta i j) = (m i j : ℂ)
  /-- **Principal coefficient** `m_00 = 1` (Coq `a00 = 1`).  **PROVEN in-place**. -/
  m_principal : m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ = 1
  /-- **Off-principal row parity** (Coq `FTtypeI_bridge_facts`, gated): `m_0j` odd. -/
  m_row_odd : ∀ j, j ≠ ⟨0, hyp.base.p_prime.pos⟩ → Odd (m ⟨0, hyp.base.q_prime.pos⟩ j)
  /-- **Off-principal column parity** (Coq `FTtypeI_bridge_facts`, gated): `m_i0` odd. -/
  m_col_odd : ∀ i, i ≠ ⟨0, hyp.base.q_prime.pos⟩ → Odd (m i ⟨0, hyp.base.p_prime.pos⟩)
  /-- **Bessel bound** (Coq `ub_e`, gated): `Σ m_ij² ≤ p q`. -/
  bessel : ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2
    ≤ (hyp.base.p * hyp.base.q : ℤ)
  /-- **Grid membership** (Coq `Y = 0`): `1_G + Δ_L = Σ m_ij η_ij`. -/
  grid_mem : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + (dataL.h78 hG).delta =
    ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j : ℂ) • hyp.base.eta i j

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), the Bessel bound `Σ m_ij² ≤ p q`** (Coq `ub_e`).  With
`m_ij = ⟨β_L, η_ij⟩` and `e_L = |L : H_L| = p q` (`hepq`), the (7.8.a) decomposition
`β_L = 1_G − ζ_0^ν + a·W + Γ_L` (`BetaDecomp.beta_eq`) *projects* onto the `η`-grid as
`⟨β_L, η_ij⟩ = ⟨1_G, η_ij⟩ + ⟨Γ_L, η_ij⟩ = ⟨1_G + Γ_L, η_ij⟩`: the distinguished image
`ζ_0^ν` and *every* member `ζ_k^ν` of the weighted sum `W` are orthogonal to the whole grid
(`caseB_eta_orthogonal_nu_zeta_at`, the Coq `o_tauLeta` for the full family, whose only input is
the (13.19.a) Dade-support avoidance `mSide_dadeSupport_avoids_regular`).  Bessel for the
orthonormal grid `{η_ij}` (`eta_orthonormal`) applied to `φ = 1_G + Γ_L` then gives
`Σ m_ij² ≤ ‖1_G + Γ_L‖² = ‖1_G‖² + ‖Γ_L‖² = 1 + ‖Γ_L‖²`, and `‖Γ_L‖² ≤ e_L − 1`
(`dataL.normEstimates.gamma_norm_sq_le`, the (7.8.b) residual bound), so
`Σ m_ij² ≤ 1 + (p q − 1) = p q`.  This is the honest (13.19.c) grid Bessel bound; the only
external datum is `hepq` (`e_L = p q`, carried by `LHypothesis` at the call site). -/
theorem betaL_grid_coeff_bessel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L)
    (hepq : (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q)
    (m : Fin hyp.base.q → Fin hyp.base.p → ℤ)
    (hcoeff : ∀ i j, ClassFunction.inner (dataL.h78 hG).beta (hyp.base.eta i j) = (m i j : ℂ)) :
    ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2
      ≤ (hyp.base.p * hyp.base.q : ℤ) := by
  classical
  haveI := dataL.kernelIn_normal
  set H78 := dataL.h78 hG with hH78
  set BD := dataL.betaDecomp hG with hBD
  -- `ζ_0^ν ⊥ η_ij` and every family member `ζ_k^ν ⊥ η_ij` (Coq `o_tauLeta`, full family).
  have hDadeAvoid := mSide_dadeSupport_avoids_regular (hyp := hyp) hG hLmax dataL
  have hetaNu : ∀ (k : Fin (dataL.n + 1)), k ≠ H78.ind1H →
      ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
        ClassFunction.inner (H78.nu (H78.hyp76.zeta k)) (hyp.base.eta i j) = 0 := by
    intro k hk i j
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      caseB_eta_orthogonal_nu_zeta_at hG hyp.base dataL hDadeAvoid hk i j, star_zero]
  -- `W = weightedNuSum ⊥ η_ij` (linear combination of the `ζ_k^ν`, `k ≠ ind1H`).
  have hWeta : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ClassFunction.inner H78.weightedNuSum (hyp.base.eta i j) = 0 := by
    intro i j
    rw [show H78.weightedNuSum
        = ∑ k ∈ (Finset.univ.erase H78.ind1H),
            (H78.hyp76.zeta k (1 : ↥L) /
              (H78.hyp76.zeta H78.zetaDistinct (1 : ↥L) *
                ClassFunction.inner (H78.hyp76.zeta k) (H78.hyp76.zeta k))) •
              H78.nu (H78.hyp76.zeta k) from rfl]
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [ClassFunction.inner_smul_left, hetaNu k (Finset.mem_erase.mp hk).1 i j, mul_zero]
  -- **The grid projection**: `⟨β_L, η_ij⟩ = ⟨1_G + Γ_L, η_ij⟩` (the `ζ_0^ν`- and `W`-parts die).
  set phi : ClassFunction G ℂ :=
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + BD.Gamma with hphi
  have hphi_coeff : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ClassFunction.inner phi (hyp.base.eta i j) = (m i j : ℂ) := by
    intro i j
    rw [← hcoeff i j, hphi,
      show H78.beta = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          - H78.nu (H78.hyp76.zeta H78.zetaDistinct)
          + (BD.a : ℂ) • H78.weightedNuSum + BD.Gamma from BD.beta_eq]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left,
      hetaNu H78.zetaDistinct H78.zetaDistinct_ne_ind1H i j, hWeta i j, mul_zero, sub_zero,
      add_zero]
  -- Pythagorean split for `φ = 1_G + Γ_L` against the orthonormal grid `{η_ij}`.
  set X : ClassFunction G ℂ :=
    ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j : ℂ) • hyp.base.eta i j with hX
  set Y : ClassFunction G ℂ := phi - X with hY
  have hXeta : ∀ (k : Fin hyp.base.q) (l : Fin hyp.base.p),
      ClassFunction.inner X (hyp.base.eta k l) = (m k l : ℂ) := by
    intro k l
    rw [hX, inner_sum_left]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun i _ hik => ?_)]
    · rw [inner_sum_left,
        Finset.sum_eq_single_of_mem l (Finset.mem_univ _) (fun j _ hjl => ?_)]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp.base,
          if_pos ⟨rfl, rfl⟩, mul_one]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp.base,
          if_neg (by rintro ⟨-, rfl⟩; exact hjl rfl), mul_zero]
    · rw [inner_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ClassFunction.inner_smul_left, eta_orthonormal hyp.base,
        if_neg (by rintro ⟨rfl, -⟩; exact hik rfl), mul_zero]
  have hsum_sq : ∀ ψ : ClassFunction G ℂ,
      (∀ (k : Fin hyp.base.q) (l : Fin hyp.base.p),
        ClassFunction.inner ψ (hyp.base.eta k l) = (m k l : ℂ)) →
      ClassFunction.inner ψ X
        = ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ) := by
    intro ψ hψ
    rw [hX, inner_sum_right]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ClassFunction.inner_smul_right, hψ i j, star_intCast]
    ring
  have hXY : ClassFunction.inner X Y = 0 := by
    have h := hsum_sq X hXeta
    have h2 : ClassFunction.inner X phi
        = ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hsum_sq phi hphi_coeff, star_intCast]
    rw [hY, ClassFunction.inner_sub_right, h2, h, sub_self]
  have hYX : ClassFunction.inner Y X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXY, star_zero]
  have hsplit : ClassFunction.inner phi phi
      = ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ)
        + ClassFunction.inner Y Y := by
    have hphiXY : phi = X + Y := by rw [hY]; abel
    calc ClassFunction.inner phi phi
        = ClassFunction.inner (X + Y) (X + Y) := by rw [← hphiXY]
      _ = ClassFunction.inner X X + ClassFunction.inner X Y
          + (ClassFunction.inner Y X + ClassFunction.inner Y Y) := by
          rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
            ClassFunction.inner_add_right]
      _ = ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ)
          + ClassFunction.inner Y Y := by
          rw [hXY, hYX, hsum_sq X hXeta]; ring
  -- `⟨Y, Y⟩ ≥ 0`, so `Σ m² ≤ ⟨φ, φ⟩` (real parts).
  have hYY_nonneg : (0 : ℝ) ≤ (ClassFunction.inner Y Y).re :=
    OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_self_re_nonneg Y
  -- `⟨φ, φ⟩ = ‖1_G‖² + ‖Γ_L‖² = 1 + ‖Γ_L‖²` (cross term `1_G ⊥ Γ_L`).
  have hone_gamma : ClassFunction.inner
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) BD.Gamma = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, BD.Gamma_orth_one,
      star_zero]
  have hphiphi : ClassFunction.inner phi phi
      = (1 : ℂ) + ClassFunction.inner BD.Gamma BD.Gamma := by
    rw [hphi, ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right,
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one,
      hone_gamma, BD.Gamma_orth_one, add_zero, zero_add]
  -- `‖Γ_L‖² ≤ e_L − 1 = p q − 1` from the (7.8.b) `NormEstimates` residual bound.
  have hGammaBound : (ClassFunction.inner BD.Gamma BD.Gamma).re
      ≤ (H78.complementIndex : ℝ) - 1 :=
    (dataL.normEstimates hG).gamma_norm_sq_le (dataL.smallIndex hG)
  -- Take real parts and cast to `ℤ`.
  have hre : ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℝ)
      + (ClassFunction.inner Y Y).re = 1 + (ClassFunction.inner BD.Gamma BD.Gamma).re := by
    have hcs := congrArg Complex.re (hsplit.symm.trans hphiphi)
    rw [Complex.add_re, Complex.add_re, Complex.intCast_re, Complex.one_re] at hcs
    exact hcs
  have hsq_le_real : ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℝ)
      ≤ (hyp.base.p * hyp.base.q : ℤ) := by
    have hepqR : (H78.complementIndex : ℝ) = ((hyp.base.p * hyp.base.q : ℤ) : ℝ) := by
      rw [hH78] at hepq ⊢; rw [hepq]; push_cast; ring
    have : ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℝ)
        ≤ 1 + (ClassFunction.inner BD.Gamma BD.Gamma).re := by linarith
    calc ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℝ)
        ≤ 1 + (ClassFunction.inner BD.Gamma BD.Gamma).re := this
      _ ≤ 1 + ((H78.complementIndex : ℝ) - 1) := by linarith
      _ = (H78.complementIndex : ℝ) := by ring
      _ = ((hyp.base.p * hyp.base.q : ℤ) : ℝ) := hepqR
  exact_mod_cast hsq_le_real

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §14 producer of the L-side grid-coefficient data** (policy-A descent).  The type-I
maximal `L` carries the (13.19.c)/(7.8) grid-coefficient package `LSideGridCoeffData`.  The
lane-c-available facts are **proven in-place** here — `coeff` (integrality, `betaL_grid_coeff_int`),
`m_principal` (`m_00 = 1`, `betaL_grid_coeff_principal_eq_one`), and `bessel` (the (13.19.c) grid
Bessel bound `Σ m² ≤ p q`, `betaL_grid_coeff_bessel`, from the full-family grid orthogonality
`caseB_eta_orthogonal_nu_zeta_at` + the (7.8.b) residual bound `‖Γ_L‖² ≤ e − 1`, using the carried
`hepq : e_L = p q`) — with the integer witness `m` taken from the proven integrality.  Only the
two off-principal parity facts remain as the isolated gate: `m_row_odd`/`m_col_odd` (the S/T type-P
partner bridge, Coq `FTtypeI_bridge_facts`) and `grid_mem` (the §13 `Y = 0` grid membership,
issue 3002), genuinely cross-lane-gated to lane b's §13/§15 type-P layer. -/
noncomputable def lSideGridCoeffData [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L) (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hepq : (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q) :
    LSideGridCoeffData hyp dataL hG where
  -- The integer coefficient is the witness of the proven integrality `betaL_grid_coeff_int`.
  m i j := Classical.choose (betaL_grid_coeff_int hG dataL i j)
  -- `coeff` is fully proven (integrality, `inner_mem_ZIrr_int`).
  coeff i j := Classical.choose_spec (betaL_grid_coeff_int hG dataL i j)
  -- `m_00 = 1` is fully proven: the chosen integer at `(0,0)` casts to `⟨β_L, η_00⟩ = 1`.
  m_principal := by
    have hspec := Classical.choose_spec
      (betaL_grid_coeff_int hG dataL
        (hyp := hyp) ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩)
    have h1 := betaL_grid_coeff_principal_eq_one (hyp := hyp) hG dataL
    -- `(m_00 : ℂ) = ⟨β_L, η_00⟩ = 1`, hence `m_00 = 1` over `ℤ`.
    have : ((Classical.choose (betaL_grid_coeff_int hG dataL
        (hyp := hyp) ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩) : ℤ) : ℂ) = 1 :=
      hspec.symm.trans h1
    exact_mod_cast this
  -- **Genuinely cross-lane-gated (Coq `FTtypeI_bridge_facts`, the S/T type-P partner bridge).**
  -- Off-principal parity `a i j ≡ 1 (mod 2)` needs the `cycTIiso_cfdot_exchange` reciprocity of the
  -- type-P `S`/`T` maximals (`hyp.base.S_typeP2`), which lives in lane b's §13/§15 layer.
  -- **Genuinely cross-lane-gated (Coq `FTtypeI_bridge_facts`, PFsection13.v:1987; issue 3002).**
  -- `m_0j = ⟨β_L, η_0j⟩ ≡ 1 (mod 2)` is the (c2) disjunct of `FTtypeI_bridge_facts` applied to the
  -- **S-side type-P partner** `StypeP` (PFsection14.v:187, `case/betaL_P: StypeP => _ _ -> //`).
  -- That bound is the type-P coherent pairing `⟨τ β_S, τ₁ φ⟩ ≡ 1 (mod 2)` on the S-side residual
  -- `β_S`, which lives in lane b's `S15_SAndT.lean`; S16 only carries an opaque `caseB_formula`.
  -- Verified c-unreachable: the only c-available parity primitive `cfdot_real_vchar_even` needs
  -- `η_0j` real (no `eta_isReal` — `η` is a cyclic-TI image, complex) and would anyway give
  -- `⟨β_L,1⟩·⟨η_0j,1⟩ = 1·0 = 0 (mod 2)` = EVEN, the *opposite* parity.
  m_row_odd := sorry
  -- Dual of `m_row_odd`, from `FTtypeI_bridge_facts` on the **T-side type-P partner** `TtypeP`
  -- (PFsection14.v:190) — same lane-b §13 gate (issue 3002).
  m_col_odd := sorry
  -- **The (13.19.c) Bessel bound `Σ m² ≤ p q`** (Coq `ub_e`), fully proven via
  -- `betaL_grid_coeff_bessel`: the (7.8.a) decomposition projects onto the `η`-grid as
  -- `⟨β_L, η_ij⟩ = ⟨1_G + Γ_L, η_ij⟩` (`caseB_eta_orthogonal_nu_zeta_at` kills the `ζ_0^ν`/`W`
  -- parts), and Bessel + `‖Γ_L‖² ≤ e − 1` gives `Σ m² ≤ 1 + (e − 1) = e = p q` (using `hepq`).
  bessel :=
    betaL_grid_coeff_bessel hG hLmax dataL hepq _
      (fun i j => Classical.choose_spec (betaL_grid_coeff_int hG dataL i j))
  -- **The deep §13 gate (issue 3002, Coq `Y = 0`, PFsection14.v:212-251).** `1_G + Δ_L = Σ m_ij η_ij`:
  -- the coherence residual equals its own orthogonal projection onto the `η`-grid, i.e. the residual
  -- `Y := (1_G + Γ_L) − Σ m_ij η_ij` is `0`.  This is the `orthogonal_split` + `leif`-equality step
  -- forced by the tightness `e = p q` (`ub_e`) **together with** each `|m_ij|² ≥ 1` (from the parities
  -- `m_row_odd`/`m_col_odd` above, `a_odd`), so `grid_mem` genuinely *depends on* the gated boundary
  -- parity.  Verified c-unreachable: the proven `NC ≤ 2` engine
  -- `grid_eq_zero_of_relation_of_card_le_two` (S16_GridExpansion) does not apply here (all `p q ≥ 15`
  -- coefficients are `±1`, so `NC = p q ≫ 2`), and the `bessel` proof only yields `⟨Y,Y⟩ ≥ 0`, not the
  -- tight `⟨Y,Y⟩ = 0`.  Mirror: the M-side `MHypothesis.betaGrid` (identical statement) is discharged
  -- by an explicit `sorry` at `exists_MHypothesis` tagged "genuine Track A obligation (issue 3002)".
  grid_mem := sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c)/(13.1.d), the L-side `η`-grid identity of the coherence residual.**
The residual `Δ_L = β_L − 1_G + ζ_0^ν` of the (7.8.a) Dade decomposition
(`beta_eq_constOne_sub_zetaImage_add_delta`, PROVEN) combines with the principal `1_G` to a
`±1`-signed sum of the whole `η`-grid: `1_G + Δ_L = Σ_{ij} ε_ij η_ij`, `ε_ij ∈ {±1}`.

This is the L-analog of the `M`-side field `MHypothesis.betaGrid` (which `betaM_expansion`
consumes), and of the Coq `FTtype2_support_coherence` core.  Here it is *proven* from the faithful
§14 grid-coefficient carrier `LSideGridCoeffData` and the PROVEN (3.7) four-corner relation
(`betaL_grid_relation`):

* the coefficients `m_ij = ⟨β_L, η_ij⟩` satisfy `m_ij + m_00 = m_i0 + m_0j` (3.7), so with the
  carried boundary parity (`m_00 = 1`, `m_0j`/`m_i0` odd) *every* `m_ij` is odd (hence `≠ 0`);
* the carried Bessel bound `Σ m_ij² ≤ p q = #grid` then sandwiches `#grid ≤ Σ m_ij² ≤ #grid`, so
  each `m_ij² = 1`, i.e. `m_ij = ±1` (`all_pm_one_and_card_of_odd_sq_sum_le`);
* the carried grid membership `1_G + Δ_L = Σ m_ij η_ij` is the displayed identity with `±1` signs.

The three deep facts are isolated in `lSideGridCoeffData`; this theorem is the honest `±1`
rigidity assembly.  The pure-algebra rearrangement into `β_L^τ = Σ ±η_ij − ε ζ_i^ν` is
`lSide_signed_eta_expansion`. -/
theorem lSide_delta_grid_expansion [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L)
    (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hepq : (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q) :
    ∃ signs : Fin hyp.base.q → Fin hyp.base.p → ℤ,
      (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
        OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + (dataL.h78 hG).delta =
          ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
            (signs i j : ℂ) • hyp.base.eta i j := by
  classical
  set i₀ : Fin hyp.base.q := ⟨0, hyp.base.q_prime.pos⟩ with hi₀
  set j₀ : Fin hyp.base.p := ⟨0, hyp.base.p_prime.pos⟩ with hj₀
  obtain ⟨m, hcoeff, hprin, hrow, hcol, hbessel, hmem⟩ :=
    lSideGridCoeffData hG hyp hLmax dataL hq3 hp5 hepq
  -- (3.7) four-corner relation on `m_ij` (from `betaL_grid_relation`, via the integrality bridge).
  have hrel : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      m i j + m i₀ j₀ = m i j₀ + m i₀ j := by
    intro i j
    have h := betaL_grid_relation hG hLmax dataL i j
    rw [hcoeff i j, hcoeff i₀ j₀, hcoeff i j₀, hcoeff i₀ j] at h
    exact_mod_cast h
  -- every coefficient is odd: `m_ij = m_i0 + m_0j − m_00` with the three boundary values odd.
  have hodd : ∀ p : Fin hyp.base.q × Fin hyp.base.p, Odd (m p.1 p.2) := by
    rintro ⟨i, j⟩
    by_cases hi : i = i₀ <;> by_cases hj : j = j₀
    · subst hi; subst hj; rw [hprin]; exact ⟨0, rfl⟩
    · subst hi; exact hrow j hj
    · subst hj; exact hcol i hi
    · -- `m_ij = m_i0 + m_0j − 1` (rel + `m_00 = 1`), sum of two odds minus odd is odd.
      have h := hrel i j
      rw [hprin] at h
      have hval : m i j = m i j₀ + m i₀ j - 1 := by omega
      obtain ⟨r, hr⟩ := hcol i hi
      obtain ⟨s, hs⟩ := hrow j hj
      exact ⟨r + s, by rw [hval, hr, hs]; ring⟩
  -- rigidity: `Σ m_ij² ≤ pq = #grid` with all odd forces each `m_ij = ±1`.
  have hcard : Fintype.card (Fin hyp.base.q × Fin hyp.base.p) = hyp.base.p * hyp.base.q := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_comm]
  have hsq : ∑ p : Fin hyp.base.q × Fin hyp.base.p, (m p.1 p.2) ^ 2
      ≤ ((hyp.base.p * hyp.base.q + 1 : ℕ) : ℤ) - 1 := by
    rw [Fintype.sum_prod_type]; push_cast; linarith [hbessel]
  have hle : ((hyp.base.p * hyp.base.q + 1 : ℕ) : ℤ)
      ≤ (Fintype.card (Fin hyp.base.q × Fin hyp.base.p) : ℤ) + 1 := by
    rw [hcard]; push_cast; omega
  obtain ⟨_, hpm⟩ := all_pm_one_and_card_of_odd_sq_sum_le
    (fun p : Fin hyp.base.q × Fin hyp.base.p => m p.1 p.2) (hyp.base.p * hyp.base.q + 1)
    hodd hsq hle
  exact ⟨m, fun i j => hpm (i, j), hmem⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`e_L = |L : H_L| = p q`** for the (14.3) L-side.  The (7.8) complement index
`complementIndex = [L : kernelIn]` of *any* coherence bundle `dataL` on `L` equals the order of
the (14.3) Frobenius complement of `L` (`Ldata.typeI_data.frobenius`), because both complement the
*same* canonical kernel `H_L = maxNilpotentNormalHall L` (`kernel_le`/`typeF.H_eq`), so both have
order `[L : H_L]`.  That complement has order `p q` by (14.3) `typeI_complement_card_eq_pq`. -/
theorem typeICoherent78_complementIndex_eq_pq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp) (dataL : TypeICoherent78Data Ldata.L) :
    (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q := by
  haveI := dataL.kernelIn_normal
  have hLeq : Ldata.typeI_data.L = Ldata.L := Ldata.typeI_data_L_eq
  -- `complementIndex = |dataL.C|` (Frobenius complement of `kernelIn`).
  have hcomplD : Nat.card ↥dataL.kernelIn * Nat.card ↥dataL.C = Nat.card ↥Ldata.L :=
    dataL.hFrob.isComplement.card_mul_card
  have hce : (dataL.h78 hG).complementIndex = Nat.card ↥dataL.C := by
    show Nat.card ↥Ldata.L / Nat.card dataL.kernel = Nat.card ↥dataL.C
    rw [show Nat.card dataL.kernel = Nat.card ↥dataL.kernelIn from
        (dataL.kernelOrder_eq hG) ▸ rfl,
      ← hcomplD, Nat.mul_div_cancel_left _ Nat.card_pos]
  -- `|kernelIn| · |Ldata-complement| = |L|` (the (14.3) Frobenius package), after transporting
  -- the cards from the ambient `typeI_data.L` to `L` and identifying the canonical kernel.
  have hcomplL0 :=
    Ldata.typeI_data.frobenius.frobenius.isComplement.card_mul_card
  have hkerDeq : dataL.kernel = maxNilpotentNormalHall Ldata.L := by
    rw [show dataL.kernel = dataL.typeIHyp.typeI.typeF.H from rfl,
      dataL.typeIHyp.typeI.typeF.H_eq]
  have hkercard : Nat.card ↥((Ldata.typeI_data.frobenius.typeI.typeF.H).subgroupOf
        Ldata.typeI_data.L)
      = Nat.card ↥dataL.kernelIn := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        Ldata.typeI_data.frobenius.typeI.typeF.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataL.kernel_le).toEquiv,
      hkerDeq, Ldata.typeI_data.frobenius.typeI.typeF.H_eq, hLeq]
  have hLcard : Nat.card ↥Ldata.typeI_data.L = Nat.card ↥Ldata.L := by rw [hLeq]
  have hcomplL : Nat.card ↥dataL.kernelIn
      * Nat.card ↥Ldata.typeI_data.frobenius.complement = Nat.card ↥Ldata.L := by
    rw [← hkercard, ← hLcard]; exact hcomplL0
  -- hence `|dataL.C| = |Ldata-complement| = p q`.
  have hCeq : Nat.card ↥dataL.C = Nat.card ↥Ldata.typeI_data.frobenius.complement :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcomplD.trans hcomplL.symm)
  rw [hce, hCeq]
  exact Ldata.typeI_complement_card_eq_pq

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), the L-side signed `η`-grid expansion.**  Under case-(b)
(`(q,p) = (3,5)`) and the two gap inequalities, (13.19.c) applied on the S- and T-sides gives
the (14.11.2)-style signed expansion `β_L^τ = Σ_{ij} ε_ij η_ij − ε ζ_i^ν` of the L-side, with
the removed unit-norm member an `L`-family coherent image (`i ≠ ind1H`; the `−ψ̄^{τ₁}`
alternative is the conjugate member `conjIndex`).

De-scaffolded (lane c, mirroring the `M`-side `betaM_expansion`): the removed member is the
distinguished coherent image `ζ_0^ν = ν(ζ_{zetaDistinct})` with `ε = 1` and
`zetaDistinct ≠ ind1H`, and the whole content is the pure-algebra rearrangement of the (7.8.a)
Dade decomposition `β_L = 1_G − ζ_0^ν + Δ_L` (`beta_eq_constOne_sub_zetaImage_add_delta`, PROVEN)
together with the `η`-grid identity `1_G + Δ_L = Σ ±η_ij` (`lSide_delta_grid_expansion`, whose
`±1` rigidity is *proven* from the (3.7) relation plus the isolated §14 grid-coefficient carrier
`lSideGridCoeffData`). -/
theorem lSide_signed_eta_expansion [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (dataL : TypeICoherent78Data nc.Ldata.L)
    (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    ∃ signs : Fin hyp.base.q → Fin hyp.base.p → ℤ,
      (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
      ∃ i : Fin (dataL.n + 1), i ≠ dataL.ind1H ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        (dataL.h78 hG).beta
          = (∑ i' : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
              (signs i' j : ℂ) • hyp.base.eta i' j)
            - (ε : ℂ) • ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)) := by
  -- `e_L = |L : H_L| = p q` (`typeICoherent78_complementIndex_eq_pq`, the (14.3) Frobenius order).
  have hepq := typeICoherent78_complementIndex_eq_pq hG nc.Ldata dataL
  obtain ⟨signs, hsigns, hgrid⟩ :=
    lSide_delta_grid_expansion hG nc.Ldata.L_maximal dataL hq3 hp5 hepq
  -- the removed member is the distinguished coherent image `ζ_0^ν` (`ε = 1`, `zetaDistinct`)
  refine ⟨signs, hsigns, (dataL.h78 hG).zetaDistinct, ?_, 1, Or.inl rfl, ?_⟩
  · -- `zetaDistinct ≠ ind1H`
    have h := (dataL.h78 hG).zetaDistinct_ne_ind1H
    rwa [dataL.h78_ind1H_eq] at h
  · -- `β_L = (1_G + Δ_L) − ζ_0^ν = Σ ±η_ij − ζ_0^ν`
    rw [Int.cast_one, one_smul, ← hgrid,
      (dataL.h78 hG).beta_eq_constOne_sub_zetaImage_add_delta]
    abel

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (14.16) expansion input** — the §13-gated character content of the case-(b)
contradiction, split into its two genuine textbook gates and the sorry-free (13.19.b) engine.
Under case-(b) (`(q,p) = (3,5)`) and the two gap inequalities:

* the L-side signed `η`-grid expansion `β_L^τ = Σ ±η_ij − ε ζ_i^ν` is the named (13.19.c)
  producer `lSide_signed_eta_expansion`;
* the M-side orthogonality `(η_ij, ψ^{τ₁}) = 0` (`ψ^{τ₁} = ζ_M^ν`) is **proven** by the
  (3.6)–(3.8)/(13.19.b) engine `caseB_eta_orthogonal_psi`, whose one residual input is the
  named (13.19.a) Dade-support avoidance `mSide_dadeSupport_avoids_regular`. -/
theorem caseB_expansion_input [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (dataL : TypeICoherent78Data nc.Ldata.L) (dataM : TypeICoherent78Data nc.Mdata.M)
    (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    ∃ signs : Fin hyp.base.q → Fin hyp.base.p → ℤ,
      (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
      ∃ i : Fin (dataL.n + 1), i ≠ dataL.ind1H ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        (dataL.h78 _hG).beta
          = (∑ i' : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
              (signs i' j : ℂ) • hyp.base.eta i' j)
            - (ε : ℂ) • ((dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta i)) ∧
        ∀ (i' : Fin hyp.base.q) (j : Fin hyp.base.p),
          ClassFunction.inner (hyp.base.eta i' j)
            ((dataM.h78 _hG).nu
              ((dataM.h78 _hG).hyp76.zeta (dataM.h78 _hG).zetaDistinct)) = 0 := by
  obtain ⟨signs, hsigns, i, hi, ε, hε, hexp⟩ :=
    lSide_signed_eta_expansion _hG dataL hq3 hp5 hhv hvu
  exact ⟨signs, hsigns, i, hi, ε, hε, hexp,
    caseB_eta_orthogonal_psi _hG hyp.base dataM
      (mSide_dadeSupport_avoids_regular _hG nc.Mdata.M_maximal dataM)⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §16 producer for the (14.16) case-(b) contradiction inputs.**  The case-(b)
pairing comes from the enriched `OrthogonalitySwitchData.caseB_pairing` ((7.9) dichotomy);
the `χ_L ⊥ ψ^{τ₁}` orthogonality is the proven (4.1) cross-orthogonality
`pair_cross_orthogonal`; the remaining (13.19.c)/(14.11.2) grid content is the named
`caseB_expansion_input`. -/
theorem caseB_contradiction_data [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseB : data.caseB)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    Nonempty (CaseBContradictionData nc) := by
  obtain ⟨hq3, hp5⟩ := data.caseB_params hcaseB
  obtain ⟨dataL, dataM, hpair⟩ := data.caseB_pairing hcaseB _hG
  obtain ⟨signs, hsigns, i, hi, ε, hε, hexp, horth⟩ :=
    caseB_expansion_input _hG dataL dataM hq3 hp5 hhv hvu
  have hjne : (dataM.h78 _hG).zetaDistinct ≠ dataM.ind1H := by
    have h := (dataM.h78 _hG).zetaDistinct_ne_ind1H
    rwa [dataM.h78_ind1H_eq] at h
  refine ⟨{
    betaL := (dataL.h78 _hG).beta
    chiL := (ε : ℂ) • ((dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta i))
    psiImg := (dataM.h78 _hG).nu ((dataM.h78 _hG).hyp76.zeta (dataM.h78 _hG).zetaDistinct)
    signs := signs
    signs_pm_one := hsigns
    betaL_expansion := hexp
    eta_orthogonal_psi := horth
    chiL_orthogonal_psi := ?_
    pairing_ne_zero := hpair }⟩
  rw [ClassFunction.inner_smul_left,
    pair_cross_orthogonal dataL dataM _hG nc.Ldata.L_maximal nc.Mdata.M_maximal
      nc.not_conj hi hjne, mul_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.16)**: character-theoretic endpoint of the exceptional
case.  The two strict gap inequalities let (13.19.c) be applied on both the
S- and T-sides, giving the same signed `eta_ij` expansion as in (14.11.2) for
`beta_L^tau`; this contradicts the nonzero pairing in case-(b) of (14.14).

De-opacified (W4 §16, lane-h): the genuine character theory (the `β_L^τ` expansion, the `η`-grid /
`χ_L` orthogonalities to `ψ^{τ₁}`, and the case-(b) pairing) is the faithful `CaseBContradictionData`;
the contradiction itself is the pure inner-product computation `(β_L^τ, ψ^{τ₁}) = (Σ ±η_ij − χ_L, ψ^{τ₁})
= Σ ±·0 − 0 = 0`, contradicting `(β_L^τ, ψ^{τ₁}) ≠ 0`. -/
theorem caseB_character_contradiction_of_gap_inequalities
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseB : data.caseB)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    False := by
  -- The (14.11.2)-style signed `eta_ij` expansion of `beta_L^tau` and its orthogonalities.
  obtain ⟨⟨betaL, chiL, psiImg, signs, _hsigns, hexp, heta_orth, hchiL_orth, hpair_ne⟩⟩ :=
    caseB_contradiction_data _hG data hcaseB hhv hvu
  -- `(beta_L^tau, psi^tau_1) = 0` by linearity + orthogonality, contradicting case-(b).
  refine hpair_ne ?_
  rw [hexp, ClassFunction.inner_sub_left, hchiL_orth, sub_zero, inner_finset_sum_left]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [inner_finset_sum_left]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [ClassFunction.inner_smul_left, heta_orth i j, mul_zero]

/-- **Peterfalvi (14.16)**: consumer form of the exceptional case-(b) branch
under `H > U`.  All numerical work in the paragraph is discharged here; only
the named character-theoretic endpoint remains as a producer. -/
theorem caseB_contradiction_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Tdata : CaseBForTData hyp)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB)
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    False := by
  have hu_full := data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB
  have hh_lower := h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
    _hG hu_full hu_dvd_h hh_mod_p hh_mod_q hu_mod_q hx_ne_one_of_quotient
  rcases data.caseB_gap_inequalities_of_h_gt_two_mul_pq_mul_u
      Tdata Sdata hcaseB hh_lower with ⟨hhv, hvu⟩
  exact data.caseB_character_contradiction_of_gap_inequalities _hG hcaseB hhv hvu

end OrthogonalitySwitchData

/-- For `p ≥ 7`, `p² ≤ 3^(p-3)`: the monotonicity input for the `p = 5` step of Peterfalvi (14.14.b).
The paper's `f(x) = 3^(x-3)/x²` is increasing for `x ≥ 2` (`f(x+1)/f(x) = 3(1 − 1/(x+1))² > 1`); this
is the integer form `p² ≤ 3^(p-3)` proved by induction from `p = 7` (`7² = 49 ≤ 81 = 3⁴`). -/
private theorem sq_le_three_pow_sub_three {p : ℕ} (hp : 7 ≤ p) : p ^ 2 ≤ 3 ^ (p - 3) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hsucc : 3 ^ (p + 1 - 3) = 3 * 3 ^ (p - 3) := by
        rw [show p + 1 - 3 = (p - 3) + 1 by omega, pow_succ]; ring
      rw [hsucc]
      calc (p + 1) ^ 2 ≤ 3 * p ^ 2 := by nlinarith [hp]
        _ ≤ 3 * 3 ^ (p - 3) := by gcongr

namespace Hypothesis

/-- **Peterfalvi (14.14.b)/(14.15) arithmetic core**: in case (b) of the orthogonality switch, the
`(β_L, ψ)`-pairing bound `(v−1)/(pq) ≤ pq−1` together with the (14.4) cyclotomic value
`v = (q^p−1)/(q−1)` and the (14.8.a) exponential comparison `q^(p+1) > p^(q+1)` force the
exceptional primes `q = 3` and `p = 5`.

Proof (Pf p.91): `(v−1)/(pq) < pq` gives `q^(p−1) ≤ v−1 < p²q²`, hence `q^(p−3) < p²`.  By (14.8.a)
`q^(p+1) > p^(q+1)` and `q < p`, one gets `q^(p−3) > p^(q−3)`, so `p^(q−3) < p²`, whence `q = 3`.
Then `3^(p−3) < p²`, contradicting `p² ≤ 3^(p−3)` for `p ≥ 7`, so `p = 5`. -/
theorem caseB_forces_q_three_and_p_five (hyp : Hypothesis (G := G))
    (hv : hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hbound : ((hyp.base.v - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ≤
      ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)) :
    hyp.base.q = 3 ∧ hyp.base.p = 5 := by
  have hp_prime := hyp.base.p_prime
  have hq_prime := hyp.base.q_prime
  have hqp : hyp.base.q < hyp.base.p := hyp.q_lt_p
  have hq3le : 3 ≤ hyp.base.q := by
    rcases hyp.base.q_odd with ⟨k, hk⟩; have := hq_prime.two_le; omega
  have hp5le : 5 ≤ hyp.base.p := by rcases hyp.base.p_odd with ⟨k, hk⟩; omega
  -- Step 1: `v − 1 < p² q²` from the case-(b) bound.
  have hpq_pos : 0 < hyp.base.p * hyp.base.q := Nat.mul_pos hp_prime.pos hq_prime.pos
  have hpqQ : (0 : ℚ) < ((hyp.base.p * hyp.base.q : ℕ) : ℚ) := by exact_mod_cast hpq_pos
  have hv1_le : (hyp.base.v - 1 : ℕ) ≤
      (hyp.base.p * hyp.base.q - 1) * (hyp.base.p * hyp.base.q) := by
    have h := (div_le_iff₀ hpqQ).mp hbound
    exact_mod_cast h
  have hv1_lt : hyp.base.v - 1 < hyp.base.p ^ 2 * hyp.base.q ^ 2 := by
    have hlt : (hyp.base.p * hyp.base.q - 1) * (hyp.base.p * hyp.base.q)
        < (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) :=
      mul_lt_mul_of_pos_right (by omega) hpq_pos
    calc hyp.base.v - 1
        ≤ (hyp.base.p * hyp.base.q - 1) * (hyp.base.p * hyp.base.q) := hv1_le
      _ < (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) := hlt
      _ = hyp.base.p ^ 2 * hyp.base.q ^ 2 := by ring
  -- Step 2: `q^(p−1) ≤ v − 1` from the geometric-sum lower bound.
  have hlow : hyp.base.q ^ (hyp.base.p - 1) ≤ hyp.base.v - 1 := by
    have h := cyclotomic_quotient_sub_one_ge_pow_pred hq_prime.two_le hp_prime.two_le
    rw [← hv] at h
    exact_mod_cast h
  -- Step 3: `q^(p−3) < p²`.
  have hqpm3 : hyp.base.q ^ (hyp.base.p - 3) < hyp.base.p ^ 2 := by
    have he : hyp.base.q ^ (hyp.base.p - 1)
        = hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have hlt : hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 2
        < hyp.base.p ^ 2 * hyp.base.q ^ 2 :=
      calc hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 2
          = hyp.base.q ^ (hyp.base.p - 1) := he.symm
        _ ≤ hyp.base.v - 1 := hlow
        _ < hyp.base.p ^ 2 * hyp.base.q ^ 2 := hv1_lt
    exact lt_of_mul_lt_mul_right hlt (Nat.zero_le _)
  -- Step 4: `p^(q−3) < q^(p−3)` from (14.8.a).
  have hkey : hyp.base.p ^ (hyp.base.q + 1) < hyp.base.q ^ (hyp.base.p + 1) := hyp.q_pow_gt_p_pow
  have hgt : hyp.base.p ^ (hyp.base.q - 3) < hyp.base.q ^ (hyp.base.p - 3) := by
    by_contra hle
    rw [not_lt] at hle
    have e1 : hyp.base.q ^ (hyp.base.p + 1)
        = hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 4 := by
      rw [← pow_add]; congr 1; omega
    have e2 : hyp.base.p ^ (hyp.base.q + 1)
        = hyp.base.p ^ (hyp.base.q - 3) * hyp.base.p ^ 4 := by
      rw [← pow_add]; congr 1; omega
    have hq4p4 : hyp.base.q ^ 4 < hyp.base.p ^ 4 := Nat.pow_lt_pow_left hqp (by norm_num)
    have hppos : 0 < hyp.base.p ^ (hyp.base.q - 3) := pow_pos hp_prime.pos _
    have h1 : hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 4
        ≤ hyp.base.p ^ (hyp.base.q - 3) * hyp.base.q ^ 4 := by gcongr
    have h2 : hyp.base.p ^ (hyp.base.q - 3) * hyp.base.q ^ 4
        < hyp.base.p ^ (hyp.base.q - 3) * hyp.base.p ^ 4 :=
      mul_lt_mul_of_pos_left hq4p4 hppos
    have hchain := lt_of_le_of_lt h1 h2
    rw [← e1, ← e2] at hchain
    omega
  -- Step 5: `q = 3`.
  have hq3 : hyp.base.q = 3 := by
    have hplt : hyp.base.p ^ (hyp.base.q - 3) < hyp.base.p ^ 2 := lt_trans hgt hqpm3
    have hexp : hyp.base.q - 3 < 2 := by
      by_contra hge
      rw [not_lt] at hge
      exact absurd hplt (not_lt.mpr (Nat.pow_le_pow_right (by omega) hge))
    rcases hyp.base.q_odd with ⟨k, hk⟩
    omega
  refine ⟨hq3, ?_⟩
  -- Step 6: `p = 5`.
  rw [hq3] at hqpm3
  by_contra hp_ne
  have hp7 : 7 ≤ hyp.base.p := by rcases hyp.base.p_odd with ⟨k, hk⟩; omega
  have := sq_le_three_pow_sub_three hp7
  omega

end Hypothesis

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.14) character dichotomy** — the genuine §7/§8 content of the orthogonality
switch.  By (8.17.c) the Dade supports `Ã₁(L)` and `Ã₁(M)` are disjoint, so by (7.9) either the
`M`-side pairing `(β_M^τ, φ^τ₁) ≠ 0` or the `L`-side pairing `(β_L^τ, ψ^τ₁) ≠ 0`.  In the first
case the (7.8.b) coherence-norm bound on the `β_M`-expansion `β_M^τ = a Σ aᵢ φᵢ^{τ₁} + Δ` gives
`Σ aᵢ² ≤ pq − 1`, i.e. `(h−1)/pq ≤ pq−1`; in the second the same estimate on the `β_L`-expansion
gives `(v−1)/pq ≤ pq−1`.  This isolates the character-theoretic input to `orthogonality_switch`;
the case-(b) passage to `q = 3`, `p = 5` is the arithmetic
`Hypothesis.caseB_forces_q_three_and_p_five`. -/
theorem orthogonality_switch_pairing_bounds [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (nc : NonConjugateHypothesis hyp) :
    (((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)) ∨
      ((∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G),
          ∃ (dataL : TypeICoherent78Data nc.Ldata.L)
            (dataM : TypeICoherent78Data nc.Mdata.M),
            ClassFunction.inner
              ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                  nc.Mdata.M_maximal nc.not_conj).first.beta)
              ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                  nc.Mdata.M_maximal nc.not_conj).secondZetaImage) ≠ 0) ∧
        (((hyp.base.v - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ≤
          ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ))) := by
  classical
  -- The two (14.14) coherence bundles, for `L ⊇ N_G(U)` and `M ⊇ N_G(V)`.
  obtain ⟨dataL⟩ := TypeICoherent78Data.nonempty _hG nc.Ldata.L_maximal nc.Ldata.isTypeI
  obtain ⟨dataM⟩ := TypeICoherent78Data.nonempty _hG nc.Mdata.M_maximal
    ⟨nc.Mdata.typeIHyp.typeI⟩
  have hnc' : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup nc.Mdata.M nc.Ldata.L :=
    fun h => nc.not_conj h.symm
  -- `L`-side sizes: `|H| = h` and `[L : H] = p q`.
  have hcardL : Nat.card ↥dataL.kernelIn = nc.h := by
    have h1 : Nat.card ↥dataL.kernelIn = Nat.card ↥dataL.kernel :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataL.kernel_le).toEquiv
    have h2 : dataL.kernel = nc.Ldata.H := by
      rw [show dataL.kernel = maxNilpotentNormalHall nc.Ldata.L from
          dataL.typeIHyp.typeI.typeF.H_eq, ← nc.Ldata.H_eq_LF]
    rw [h1, h2, nc.h_eq_card_H]
  have hidxL : (dataL.kernelIn).index = hyp.base.p * hyp.base.q := by
    have h := OddOrder.Peterfalvi.S15.typeIFrobenius_kernel_index_eq_complement
      nc.Ldata.typeI_data.frobenius
    have h2 : dataL.kernelIn
        = (maxNilpotentNormalHall nc.Ldata.L).subgroupOf nc.Ldata.L := by
      rw [show dataL.kernelIn = (dataL.typeIHyp.typeI.typeF.H).subgroupOf nc.Ldata.L
          from rfl, dataL.typeIHyp.typeI.typeF.H_eq]
    rw [h2, ← nc.Ldata.typeI_data_L_eq]
    exact h.trans nc.Ldata.typeI_complement_card_eq_pq
  -- `M`-side sizes: `|K| = v` ((14.11) `K = V`, `|V| = v·d`, `d = 1`) and `[M : K] = p q`.
  obtain ⟨hKV, hepq⟩ := K_eq_V_index_pq _hG hyp nc.Ldata nc.Mdata
  have hkerM : dataM.kernel = nc.Mdata.K := by
    rw [show dataM.kernel = maxNilpotentNormalHall nc.Mdata.M from
        dataM.typeIHyp.typeI.typeF.H_eq, ← nc.Mdata.K_eq_MF]
  have hd1 : hyp.base.d = 1 := by
    have hTII : IsTypeII hyp.base.T := T_typeII _hG hyp
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact OddOrder.Peterfalvi.S15.V_inf_centralizer_Q_eq_bot _hG hyp.base hTII
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  have hcardM : Nat.card ↥dataM.kernelIn = hyp.base.v := by
    have h1 : Nat.card ↥dataM.kernelIn = Nat.card ↥dataM.kernel :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataM.kernel_le).toEquiv
    rw [h1, hkerM, hKV, hyp.base.card_V_eq_vd, hd1, mul_one]
  have hidxM : (dataM.kernelIn).index = hyp.base.p * hyp.base.q := by
    have h1 : dataM.kernelIn = nc.Mdata.K.subgroupOf nc.Mdata.M := by
      rw [show dataM.kernelIn = (dataM.kernel).subgroupOf nc.Mdata.M from rfl, hkerM]
    rw [h1, ← nc.Mdata.e_eq_index]
    exact hepq
  -- Convert the `ℚ`-subtractions to the `ℕ`-subtraction casts of the statement.
  have hpq1 : 1 ≤ hyp.base.p * hyp.base.q :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hyp.base.p_prime.pos.ne' hyp.base.q_prime.pos.ne')
  have hv1 : 1 ≤ hyp.base.v := by
    have hVpos : 0 < Nat.card ↥hyp.base.V := Nat.card_pos
    rw [hyp.base.card_V_eq_vd, hd1, mul_one] at hVpos
    exact hVpos
  have hh1 : 1 ≤ nc.h := (nc.h_odd _hG).pos
  -- The (7.9) pairing dichotomy, with the pairing itself retained in the case-(b) branch.
  rcases pairing_dichotomy dataL dataM _hG nc.Ldata.L_maximal nc.Mdata.M_maximal
      nc.not_conj with hfirst | hsecond
  · -- `⟨β_L, ζ_M^ν⟩ ≠ 0`: the `M`-kernel Bessel bound `(v − 1)/pq ≤ pq − 1` + the pairing.
    right
    have hMK := bessel_bound_of_inner_beta_zeta_ne_zero dataM dataL _hG
      nc.Mdata.M_maximal nc.Ldata.L_maximal hnc' hfirst
    rw [dataL.complementIndex_eq _hG, hcardM, hidxM, hidxL] at hMK
    refine ⟨fun hG' => ⟨dataL, dataM, hfirst⟩, ?_⟩
    rw [Nat.cast_sub hv1, Nat.cast_sub hpq1]
    push_cast at hMK ⊢
    convert hMK using 2
  · -- `⟨β_M, ζ_L^ν⟩ ≠ 0`: the `L`-kernel Bessel bound `(h − 1)/pq ≤ pq − 1`.
    left
    have hLH := bessel_bound_of_inner_beta_zeta_ne_zero dataL dataM _hG
      nc.Ldata.L_maximal nc.Mdata.M_maximal nc.not_conj hsecond
    rw [dataM.complementIndex_eq _hG, hcardL, hidxL, hidxM] at hLH
    rw [Nat.cast_sub hh1, Nat.cast_sub hpq1]
    push_cast at hLH ⊢
    convert hLH using 2

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.14)**: either the case-(a) bound `(h − 1)/pq ≤ pq − 1` holds (the
`β_M`--`φ` pairing is nonzero), or the case-(b) exceptional primes `q = 3`, `p = 5` hold (the
`β_L`--`ψ` pairing is nonzero).

Assembled from the (7.9)+(8.17.c) character dichotomy `orthogonality_switch_pairing_bounds`, whose
two branches supply the case-(a) norm bound and the case-(b) `(v−1)/pq ≤ pq−1` bound; in case (b)
the arithmetic `caseB_forces_q_three_and_p_five` ((14.15)/(14.8.a)) turns that bound, together with
the (14.4) cyclotomic value of `v`, into `q = 3`, `p = 5`.  The abstract `caseA`/`caseB` props of
`OrthogonalitySwitchData` are taken to be the case-(a) bound and the `(q,p)=(3,5)` conclusion
themselves, so the downstream (14.15)/(14.16) machinery reads them off directly. -/
theorem orthogonality_switch [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (nc : NonConjugateHypothesis hyp) :
    ∃ data : OrthogonalitySwitchData nc, data.caseA ∨ data.caseB := by
  obtain ⟨_Tdata, _, hv⟩ := caseB_for_T _hG hyp
  refine ⟨{
    caseA := ((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
      ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)
    caseA_bound := fun h => h
    caseB := (hyp.base.q = 3 ∧ hyp.base.p = 5) ∧
      haveI := hyp.base.finiteG
      ∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G),
        ∃ (dataL : TypeICoherent78Data nc.Ldata.L) (dataM : TypeICoherent78Data nc.Mdata.M),
          ClassFunction.inner
            ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                nc.Mdata.M_maximal nc.not_conj).first.beta)
            ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                nc.Mdata.M_maximal nc.not_conj).secondZetaImage) ≠ 0
    caseB_params := fun h => h.1
    caseB_pairing := fun h => h.2 }, ?_⟩
  rcases orthogonality_switch_pairing_bounds _hG hyp nc with hA | ⟨hpair, hB⟩
  · exact Or.inl hA
  · exact Or.inr ⟨hyp.caseB_forces_q_three_and_p_five hv hB, hpair⟩

/-- **Peterfalvi (14.14)--(14.15)**: the full `u` value once the
cardinality consequences of (14.5) have been materialized.  The case-(b)
alternative of (14.14) is already full by the S-side order data; in case (a),
assuming the non-full value contradicts the fixed-point-free cardinal
congruences for `H` and `U`. -/
theorem u_final_value_of_fpf_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp)
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q]) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  rcases orthogonality_switch _hG hyp nc with ⟨data, hcase⟩
  rcases caseB_for_S _hG hyp nc.Ldata with ⟨Sdata, _hS_caseB⟩
  rcases hcase with hcaseA | hcaseB
  · by_contra hu_not_full
    exact data.caseA_contradiction_of_nonfull_fpf_card_congruences
      _hG Sdata hcaseA hu_not_full hu_dvd_h hh_mod_p hh_mod_q hu_mod_q
  · exact data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB

/-- **Peterfalvi (14.15)**: `u` has the full cyclotomic value
`(p^q - 1) / (p - 1)`.

The proof consumes the cardinal consequences of (14.5): `u ∣ h`, the two
Frobenius-kernel congruences for `h`, and the fixed-point-free cardinal
congruence for `U`.  The arithmetic contradiction is packaged in
`u_final_value_of_fpf_card_congruences`. -/
theorem u_final_value [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  rcases nc.h_modEq_one_mod_p_and_q _hG with ⟨hh_mod_p, hh_mod_q⟩
  exact u_final_value_of_fpf_card_congruences _hG hyp nc (nc.u_dvd_h _hG)
    hh_mod_p hh_mod_q (hyp.u_modEq_one_mod_q _hG)

/-- **Peterfalvi (14.16)**: in the non-conjugate case, the kernel `H` is
exactly `U`. -/
theorem H_eq_U [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp) :
    nc.Ldata.H = hyp.base.U := by
  by_contra hHU
  rcases orthogonality_switch _hG hyp nc with ⟨data, hcase⟩
  rcases caseB_for_T _hG hyp with ⟨Tdata, _hT_caseB, _hv_eq⟩
  rcases caseB_for_S _hG hyp nc.Ldata with ⟨Sdata, _hS_caseB⟩
  have hu_full := u_final_value _hG hyp nc
  rcases nc.h_modEq_one_mod_p_and_q _hG with ⟨hh_mod_p, hh_mod_q⟩
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, OddOrder.Peterfalvi.S15.c_eq_one _hG hyp.base, mul_one]
  have hU_le_H : hyp.base.U ≤ nc.Ldata.H := by
    rw [← nc.Ldata.typeI_data_H_eq]
    exact nc.Ldata.typeI_data.U_le_H
  have hx_ne_one_of_quotient :
      ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1 := by
    intro x hh_eq hx1
    have hH_card_eq_U_card : Nat.card ↥nc.Ldata.H = Nat.card ↥hyp.base.U := by
      rw [← nc.h_eq_card_H, hh_eq, hx1, mul_one, hU_card]
    have hU_eq_H : hyp.base.U = nc.Ldata.H :=
      Subgroup.eq_of_le_of_card_ge hU_le_H (le_of_eq hH_card_eq_U_card)
    exact hHU hU_eq_H.symm
  rcases hcase with hcaseA | hcaseB
  · exact data.caseA_contradiction_of_full_u_card_congruences
      _hG Sdata hcaseA hu_full (nc.u_dvd_h _hG) hh_mod_p hh_mod_q
      (hyp.u_modEq_one_mod_q _hG) hx_ne_one_of_quotient
  · exact data.caseB_contradiction_of_full_u_card_congruences
      _hG Tdata Sdata hcaseB (nc.u_dvd_h _hG) hh_mod_p hh_mod_q
      (hyp.u_modEq_one_mod_q _hG) hx_ne_one_of_quotient

/-- **Peterfalvi §8 / BG 15.7(a)**: the type-`P` Fitting core `P = S_F` is a TI-subgroup of `G`.
`S` is type-`P₂` (`S_typeP2`), so `F(S)` is TI (`fittingIsTI_of_isTypeP2`), whence the Fitting core
`S_F#` is TI (`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`; `sharpSubgroup = ·∖{1}`
matches `Subgroup.IsTI`).  Supplies the `P_isTI` field of `MHypothesis`. -/
theorem base_P_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : Subgroup.IsTI hyp.base.P := by
  rw [hyp.base.P_eq_SF]
  exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG
    hyp.base.S_maximal
    (OddOrder.BG.Ch4.S15.fittingIsTI_of_isTypeP2 hG hyp.base.S_maximal hyp.base.S_typeP2)

/-- **Peterfalvi §8, `T`-side**: the type-`P` Fitting core `Q = T_F` is a TI-subgroup of `G`.
`T`-side dual of `base_P_isTI` via `fittingIsTI_T` (`T` type II ⟹ type-`P₂`).  Supplies the `Q_isTI`
field of `MHypothesis`. -/
theorem base_Q_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTII : IsTypeII hyp.base.T) : Subgroup.IsTI hyp.base.Q := by
  rw [hyp.base.Q_eq_TF]
  exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG
    hyp.base.T_maximal (OddOrder.Peterfalvi.S15.fittingIsTI_T hG hyp.base hTII)

/-- **Peterfalvi §13 `normalizer_V` (the `W`-exceptional-set normalizer)**: every nonempty
`X ⊆ W − (W₁ ∪ W₂)` has `N_G(X) = W`.  Read off the S-side type-`P` data `Sdata.normalizer_V`
((8.8) `W = W₁ × W₂` cyclic-TI structure), reconciled to the base `W`/`W₁`/`W₂`
(`Sdata_W1_eq`/`Sdata_W2_eq`, `W_eq_join`).  Supplies `MHypothesis`'s `W_normalizer_V`. -/
theorem base_W_normalizer_V (hyp : Hypothesis (G := G)) :
    ∀ X : Set G, X.Nonempty →
      X ⊆ (hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)) →
      Subgroup.normalizer X = hyp.base.W := by
  have hWeq : hyp.base.Sdata.W = hyp.base.W := by
    rw [hyp.base.Sdata.W_eq, hyp.base.Sdata_W1_eq, hyp.base.Sdata_W2_eq]
    exact hyp.base.W_eq_join.symm
  intro X hX hXsub
  rw [← hWeq]
  refine hyp.base.Sdata.normalizer_V X hX ?_
  rw [hWeq, hyp.base.Sdata_W1_eq, hyp.base.Sdata_W2_eq]
  exact hXsub

/-- **Order factorization of the type-`P` maximal `S`**: `|P| · |U| · |W₁| = |S|`
(`S = (P ⋊ U) ⋊ W₁`, `P = S_F`, `S' = P ⋊ U`).  From the `Sdata` complement indices
`card_W1_eq_derived_index` (`|W₁| = [S:S']`) and `card_U_eq_index` (`|U| = [S':P]`) via
`Subgroup.card_mul_index`. -/
theorem base_card_S_eq [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.base.P * Nat.card ↥hyp.base.U * Nat.card ↥hyp.base.W1
      = Nat.card ↥hyp.base.S := by
  have hW1 : Nat.card ↥hyp.base.W1 = Nat.card ↥hyp.base.Sdata.W1 := by rw [hyp.base.Sdata_W1_eq]
  have hU : Nat.card ↥hyp.base.U = Nat.card ↥hyp.base.Sdata.U := by rw [hyp.base.Sdata_U_eq]
  have hP : hyp.base.P = maxNilpotentNormalHall hyp.base.S := hyp.base.P_eq_SF
  have hDle : derivedInG hyp.base.S ≤ hyp.base.S := Subgroup.map_subtype_le _
  have hPle : maxNilpotentNormalHall hyp.base.S ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU, ← hP]; exact le_sup_left
  have c1 : Nat.card ↥(derivedInG hyp.base.S) * Nat.card ↥hyp.base.Sdata.W1
      = Nat.card ↥hyp.base.S := by
    rw [hyp.base.Sdata.card_W1_eq_derived_index,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv]
    exact Subgroup.card_mul_index _
  have c2 : Nat.card ↥(maxNilpotentNormalHall hyp.base.S) * Nat.card ↥hyp.base.Sdata.U
      = Nat.card ↥(derivedInG hyp.base.S) := by
    rw [hyp.base.Sdata.card_U_eq_index,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv]
    exact Subgroup.card_mul_index _
  rw [hW1, hU, hP, ← c1, ← c2]

/-- **Peterfalvi (14.11.4)**: `|N_G(P)| = |P| · u · q`.  The Fitting core `P = S_F` is normal in
the maximal `S` and nontrivial (`W₂ ≤ P`), so `N_G(P) = S`
(`normalizer_eq_self_of_subgroupOf_normal_of_ne_bot`); then `|S| = |P|·|U|·|W₁|` (`base_card_S_eq`)
with `|U| = u·c`, `c = 1` (`S15.c_eq_one`), `|W₁| = q`.  Supplies `MHypothesis`'s
`card_normalizer_P_eq`. -/
theorem base_card_normalizer_P_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G))
      = Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q := by
  have hPne : maxNilpotentNormalHall hyp.base.S ≠ ⊥ := by
    intro hbot
    have hW2 := OddOrder.Peterfalvi.S15.W2_le_P hG hyp.base
    rw [hyp.base.P_eq_SF, hbot, le_bot_iff] at hW2
    have hp1 : hyp.base.p = 1 := by rw [hyp.base.p_eq_card_W2, hW2, Subgroup.card_bot]
    exact hyp.base.p_prime.one_lt.ne' hp1
  have hNP : Subgroup.normalizer (hyp.base.P : Set G) = hyp.base.S := by
    rw [hyp.base.P_eq_SF]
    exact OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
      hyp.base.S_maximal (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _)
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal _) hPne
  rw [hNP, ← base_card_S_eq hyp, hyp.base.card_U_eq_uc,
    OddOrder.Peterfalvi.S15.c_eq_one hG hyp.base, mul_one, hyp.base.q_eq_card_W1]

/-- **Order factorization of the type-`P` maximal `T`** (T-side dual of `base_card_S_eq`):
`|Q| · |V| · |W₂| = |T|`, from a reconciled `TypePData T` (`tpd.U = V`, `tpd.W1 = W₂`, `Q = T_F`)
via `card_W1_eq_derived_index` / `card_U_eq_index` and `Subgroup.card_mul_index`. -/
theorem base_card_T_eq [Finite G] (hyp : Hypothesis (G := G))
    (tpd : OddOrder.GroupTheory.TypePData hyp.base.T) (hU : tpd.U = hyp.base.V)
    (hW1 : tpd.W1 = hyp.base.W2) :
    Nat.card ↥hyp.base.Q * Nat.card ↥hyp.base.V * Nat.card ↥hyp.base.W2
      = Nat.card ↥hyp.base.T := by
  have hW2c : Nat.card ↥hyp.base.W2 = Nat.card ↥tpd.W1 := by rw [hW1]
  have hVc : Nat.card ↥hyp.base.V = Nat.card ↥tpd.U := by rw [hU]
  have hQ : hyp.base.Q = maxNilpotentNormalHall hyp.base.T := hyp.base.Q_eq_TF
  have hDle : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hQle : maxNilpotentNormalHall hyp.base.T ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV, ← hQ]; exact le_sup_left
  have c1 : Nat.card ↥(derivedInG hyp.base.T) * Nat.card ↥tpd.W1 = Nat.card ↥hyp.base.T := by
    rw [tpd.card_W1_eq_derived_index, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv]
    exact Subgroup.card_mul_index _
  have c2 : Nat.card ↥(maxNilpotentNormalHall hyp.base.T) * Nat.card ↥tpd.U
      = Nat.card ↥(derivedInG hyp.base.T) := by
    rw [tpd.card_U_eq_index, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv]
    exact Subgroup.card_mul_index _
  rw [hW2c, hVc, hQ, ← c1, ← c2]

/-- **Peterfalvi (14.11.4)**: `|N_G(Q)| = |Q| · v · p` (T-side dual of `base_card_normalizer_P_eq`).
`Q = T_F` is normal in the maximal `T` and nontrivial (`W₁ ≤ Q`), so `N_G(Q) = T`; then
`|T| = |Q|·|V|·|W₂|` (`base_card_T_eq`) with `|V| = v·d`, `d = 1` (`V_inf_centralizer_Q_eq_bot`,
`D = V ⊓ C_G(Q) = ⊥`), `|W₂| = p`.  Supplies `MHypothesis`'s `card_normalizer_Q_eq`. -/
theorem base_card_normalizer_Q_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTII : IsTypeII hyp.base.T) :
    Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G))
      = Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p := by
  obtain ⟨tpd, hU, hW1, hW2⟩ := OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base
  have hQne : maxNilpotentNormalHall hyp.base.T ≠ ⊥ := by
    intro hbot
    have hW1le : hyp.base.W1 ≤ maxNilpotentNormalHall hyp.base.T := by
      rw [← hW2]
      exact le_trans tpd.W2_le (le_trans inf_le_left (le_of_eq tpd.H_eq))
    rw [hbot, le_bot_iff] at hW1le
    have hq1 : hyp.base.q = 1 := by rw [hyp.base.q_eq_card_W1, hW1le, Subgroup.card_bot]
    exact hyp.base.q_prime.one_lt.ne' hq1
  have hNQ : Subgroup.normalizer (hyp.base.Q : Set G) = hyp.base.T := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
      hyp.base.T_maximal (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _)
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal _) hQne
  have hd1 : hyp.base.d = 1 := by
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact OddOrder.Peterfalvi.S15.V_inf_centralizer_Q_eq_bot hG hyp.base hTII
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  rw [hNQ, ← base_card_T_eq hyp tpd hU hW1, hyp.base.card_V_eq_vd, hd1, mul_one,
    hyp.base.p_eq_card_W2]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09 in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (7.8) for the V-side `M`** — the §7 coherence datum `S09.Hypothesis78` of the
type-I maximal subgroup `M` over `N_G(V)`, together with its structural data (maximality,
`N_G(V) ≤ M`, Fitting-kernel index `p q`).

This is the **V-side dual of `witness_L_hypothesis78`** (the (12.16) witness-side coherence):
`M`'s coherence is produced by the general type-I Frobenius engine `S14.frobenius_typeI_coherent`
(`M` is type-I Frobenius over `N_G(V)` with kernel `M_F`, from `typeII_overNormalizer_frobenius_V`),
and the (7.8) datum is assembled by the same `hypothesis78OfDade` construction (placed family
`exists_witness_placed_family`, `nu_isometry` from `coherence_extension_inner_eq_on_family`,
`hagree` from `coherence_hagree_dadeMap`).  Subsumes `exists_M_structural` and additionally supplies
the `h78` field of `MHypothesis` — the single **grid-independent** honest obligation of
`exists_MHypothesis` (the `betaGrid`/`betaM` fields remain gated on the §13 `η`-grid carrier, issue
3002). -/
theorem exists_M_hypothesis78 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTII : IsTypeII hyp.base.T) :
    ∃ (M : Subgroup G) (typeIHyp : OddOrder.Peterfalvi.S14.Hypothesis M),
      M ∈ maximalSubgroups G ∧
        Subgroup.normalizer (hyp.base.V : Set G) ≤ M ∧
          ((maxNilpotentNormalHall M).subgroupOf M).index = hyp.base.p * hyp.base.q ∧
          ∃ h78 : OddOrder.Peterfalvi.S09.Hypothesis78 G
              (OddOrder.GroupTheory.typeIA M typeIHyp.typeI) M,
            h78.hyp76.H = maxNilpotentNormalHall M ∧
              h78.hyp76.hyp71.hyp = typeIHyp.dadeData.dade ∧
              h78.hyp76.zeta h78.ind1H (1 : M)
                = (((maxNilpotentNormalHall M).subgroupOf M).index : ℂ) ∧
              ClassFunction.inner (h78.hyp76.zeta h78.zetaDistinct)
                (h78.hyp76.zeta h78.zetaDistinct) = 1 ∧
              (1 : ℝ) - (h78.complementIndex : ℝ) / (h78.kernelOrder : ℝ)
                ≤ h78.zetaNuRhoNormSq := by
  classical
  obtain ⟨vdata, _hker, _hVH⟩ :=
    OddOrder.Peterfalvi.S15.typeII_overNormalizer_frobenius_V hG hyp.base hTII
  have hMtypeI : IsTypeI vdata.L := ⟨vdata.frobenius.typeI⟩
  obtain ⟨typeIHyp⟩ :=
    OddOrder.Peterfalvi.S14.exists_typeI_hypothesis hG vdata.L_maximal hMtypeI
  have hindex : ((maxNilpotentNormalHall vdata.L).subgroupOf vdata.L).index
      = hyp.base.p * hyp.base.q := by
    rw [OddOrder.Peterfalvi.S15.typeIFrobenius_kernel_index_eq_complement vdata.frobenius]
    exact vdata.complement_card_eq_pq
  refine ⟨vdata.L, typeIHyp, vdata.L_maximal, vdata.normalizer_V_le_L, hindex, ?_⟩
  -- Coherence for `M` via the general type-I Frobenius engine: the Frobenius witness for
  -- `typeIHyp.H = M_F` comes from `vdata.frobenius` (both kernels are `maxNilpotentNormalHall M`).
  have hHeq : typeIHyp.typeI.typeF.H = vdata.frobenius.typeI.typeF.H := by
    rw [typeIHyp.typeI.typeF.H_eq, vdata.frobenius.typeI.typeF.H_eq]
  have hfrob : ∃ C : Subgroup ↥vdata.L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥vdata.L
        ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L) C :=
    ⟨vdata.frobenius.complement, by rw [hHeq]; exact vdata.frobenius.frobenius⟩
  obtain ⟨coh⟩ := OddOrder.Peterfalvi.S14.frobenius_typeI_coherent hG typeIHyp hfrob
  -- Mirror `witness_L_hypothesis78`'s `hypothesis78OfDade` assembly (generic in the hypothesis).
  have hHL : typeIHyp.typeI.typeF.H ≤ vdata.L := typeIHyp.typeI.typeF.H_le
  haveI hKnormal : ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L).Normal := by
    rw [typeIHyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal vdata.L
  have hAH : OddOrder.GroupTheory.typeIA vdata.L typeIHyp.typeI
      = (typeIHyp.typeI.typeF.H : Set G) \ {1} :=
    OddOrder.Peterfalvi.S14.Hypothesis.typeIA_eq_sharp hG typeIHyp
  have hHnorm : ∀ (l : ↥vdata.L) {h : G}, h ∈ typeIHyp.typeI.typeF.H →
      (l : G) * h * (l : G)⁻¹ ∈ typeIHyp.typeI.typeF.H := by
    intro l h hh
    have hhL : h ∈ vdata.L := hHL hh
    have hmem : (⟨h, hhL⟩ : ↥vdata.L) ∈ (typeIHyp.typeI.typeF.H).subgroupOf vdata.L :=
      (Subgroup.mem_subgroupOf).mpr hh
    have hconj := hKnormal.conj_mem ⟨h, hhL⟩ hmem l
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  obtain ⟨n, θ, ind1H, hind1H, hdeg0, htriv, hinj, hcover⟩ :=
    OddOrder.Peterfalvi.S14.exists_witness_placed_family typeIHyp
  have hSmem : ∀ i, i ≠ ind1H →
      ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
          (θ i : ClassFunction _ ℂ) ∈ typeIHyp.Sset := by
    intro i hi
    refine ⟨θ i, fun htriv_i => hi (hinj ?_), rfl⟩
    change ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ i : ClassFunction _ ℂ)
        = ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
          (θ ind1H : ClassFunction _ ℂ)
    rw [htriv_i, htriv]
  let d : Fin (n + 1) → ℂ :=
    fun i => (θ i : ClassFunction ↥((typeIHyp.typeI.typeF.H).subgroupOf vdata.L) ℂ)
      (1 : ↥((typeIHyp.typeI.typeF.H).subgroupOf vdata.L))
  have hd : ∀ i, d i = (θ i : ClassFunction ↥((typeIHyp.typeI.typeF.H).subgroupOf vdata.L) ℂ)
      (1 : ↥((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)) := fun _ => rfl
  have hdeg : ∀ i, ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ i : ClassFunction _ ℂ) (1 : ↥vdata.L)
      = d i * ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥vdata.L) := by
    intro i
    rw [ClassFunction.induce_apply_one ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ i : ClassFunction _ ℂ), hdeg0, hd i]
    ring
  have hdeg_match : ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥vdata.L)
      = ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ ind1H : ClassFunction _ ℂ) (1 : ↥vdata.L) := by
    rw [hdeg0, htriv]
    change (((typeIHyp.typeI.typeF.H).subgroupOf vdata.L).index : ℂ)
        = ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
          (trivialClassFunction ↥((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)) (1 : ↥vdata.L)
    rw [induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)]
  have psi_support : ∀ i, (ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ i : ClassFunction _ ℂ)
      - d i • ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
          (θ 0 : ClassFunction _ ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.GroupTheory.typeIA vdata.L typeIHyp.typeI) vdata.L := by
    intro i
    refine (induce_diff_support (θ i) (θ 0) (d i) (hdeg i)).trans ?_
    intro x hx
    rw [Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff] at hx
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff typeIHyp.typeI.typeF.H hAH x).mpr
      ⟨hx.1, hx.2⟩
  have hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (coh.extension (ClassFunction.induce
          (typeIHyp.typeI.typeF.H.subgroupOf vdata.L) (θ i : ClassFunction _ ℂ)))
        (coh.extension (ClassFunction.induce
          (typeIHyp.typeI.typeF.H.subgroupOf vdata.L) (θ j : ClassFunction _ ℂ)))
        = ClassFunction.inner (ClassFunction.induce
            (typeIHyp.typeI.typeF.H.subgroupOf vdata.L) (θ i : ClassFunction _ ℂ))
          (ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ j : ClassFunction _ ℂ)) :=
    fun i j hi hj => coherence_extension_inner_eq_on_family coh (hSmem i hi) (hSmem j hj)
  have hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      typeIHyp.toHypothesis71.τ ⟨ClassFunction.induce
          (typeIHyp.typeI.typeF.H.subgroupOf vdata.L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ 0 : ClassFunction _ ℂ), psi_support i⟩
        = coh.extension (ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ i : ClassFunction _ ℂ))
          - d i • coh.extension (ClassFunction.induce
            (typeIHyp.typeI.typeF.H.subgroupOf vdata.L) (θ 0 : ClassFunction _ ℂ)) := by
    intro i _ hi_ind
    obtain ⟨deg_i, -, hdeg_i_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (θ i)
    exact coherence_hagree_dadeMap typeIHyp.dadeData.dade typeIHyp.hconj coh
      (hSmem i hi_ind) (hSmem 0 (Ne.symm hind1H)) (m0 := 1) (mi := deg_i) (by norm_num)
      (by rw [hd i, hdeg_i_eq, Nat.cast_one, div_one]) (psi_support i)
  refine ⟨hypothesis78OfDade typeIHyp.toHypothesis71
    (typeIHyp.dadeData.dade.fullDadeIsometryData typeIHyp.hconj).toDadeIsometryData.isDadeIsometry
    typeIHyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv
    hdeg_match coh.extension hnu_isometry hagree, ?_, rfl, ?_, ?_, ?_⟩
  · exact typeIHyp.typeI.typeF.H_eq
  · -- **Peterfalvi (7.6)/(14.10)**: the induced principal `ζ_{ind1H} = Ind_K 1_K` has
    -- degree `[M:K]` at `1` (`θ ind1H = 1_K` + `induce_trivialChar_apply_eq_index`).
    show ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
        (θ ind1H : ClassFunction _ ℂ) (1 : vdata.L)
        = (((maxNilpotentNormalHall vdata.L).subgroupOf vdata.L).index : ℂ)
    rw [htriv, ← typeIHyp.typeI.typeF.H_eq]
    exact induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)
  · -- **Peterfalvi (7.8)**: the distinguished `ζ = ζ_0 = Ind_K θ_0` (`θ_0 ≠ 1_K`) is irreducible
    -- (Frobenius, [Is] 6.34), hence `‖ζ‖² = 1` — the `ζ_0` unit-norm input to the (7.5)/(7.8) machinery.
    obtain ⟨C, hFrobG⟩ := hfrob
    have hθ0_ne : θ 0 ≠ trivialIrreducibleCharacter
        ↥(typeIHyp.typeI.typeF.H.subgroupOf vdata.L) := by
      intro h0triv
      refine hind1H ?_
      exact (hinj (show ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ 0 : ClassFunction _ ℂ)
          = ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ ind1H : ClassFunction _ ℂ) from by rw [h0triv, htriv])).symm
    show ClassFunction.inner
        (ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
          (θ 0 : ClassFunction _ ℂ))
        (ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
          (θ 0 : ClassFunction _ ℂ)) = 1
    exact inner_self_induce_eq_one_of_frobeniusGroup hFrobG (θ 0) hθ0_ne
  · -- **Peterfalvi (7.8.b)**: the coherence-norm lower bound `1 − e/h ≤ ‖ζ_0^{νρ}‖²` for the
    -- `V`-side `M`, via the concrete §7 producer `zetaNuRhoNormSqGeOfDade` (the `V`-side dual of
    -- `witness_L_zeta_bound`): feed the Dade witness `Hypothesis78` its four genuine (7.8) inputs —
    -- `ζ_0^ν ⊥ 1_G` (`witness_L_hzeta0nu`), `‖ζ_0‖² = 1` (Frobenius), `(β, ζ_0^ν) + 1 ∈ ℤ`
    -- (`exists_betaDecomp_a`), and `2e + 1 ≤ h`
    -- (`frobenius_two_mul_card_complement_add_one_le_card_kernel`).
    obtain ⟨C, hFrobG⟩ := hfrob
    have hθ0_ne : θ 0 ≠ trivialIrreducibleCharacter
        ↥(typeIHyp.typeI.typeF.H.subgroupOf vdata.L) := by
      intro h0triv
      refine hind1H ?_
      exact (hinj (show ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ 0 : ClassFunction _ ℂ)
          = ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ ind1H : ClassFunction _ ℂ) from by rw [h0triv, htriv])).symm
    set H78 := hypothesis78OfDade typeIHyp.toHypothesis71
      (typeIHyp.dadeData.dade.fullDadeIsometryData typeIHyp.hconj).toDadeIsometryData.isDadeIsometry
      typeIHyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv
      hdeg_match coh.extension hnu_isometry hagree with hH78def
    have hKcard : Nat.card ↥(typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
        = Nat.card typeIHyp.typeI.typeF.H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
    have hKodd : Odd (Nat.card ↥(typeIHyp.typeI.typeF.H.subgroupOf vdata.L)) :=
      (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card vdata.L)).of_dvd_nat
        (Subgroup.card_subgroup_dvd_card _)
    have hCodd : Odd (Nat.card ↥C) :=
      (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card vdata.L)).of_dvd_nat
        (Subgroup.card_subgroup_dvd_card C)
    obtain ⟨a, ha⟩ := exists_betaDecomp_a H78
      (Submodule.sub_mem _
        (ClassFunction.induce_mem_ZIrr _ (θ ind1H).property.mem_ZIrr)
        (ClassFunction.induce_mem_ZIrr _ (θ 0).property.mem_ZIrr))
      (coh.extension_mem_ZIrr _ (Submodule.subset_span (hSmem 0 (Ne.symm hind1H))))
    have hsmall : H78.smallIndex := by
      have hfrobB := OddOrder.Peterfalvi.S14.frobenius_two_mul_card_complement_add_one_le_card_kernel
        hFrobG hKodd hCodd hFrobG.ne_bot_kernel
      show 2 * H78.complementIndex + 1 ≤ H78.kernelOrder
      have hke : H78.kernelOrder = Nat.card ↥(typeIHyp.typeI.typeF.H.subgroupOf vdata.L) := by
        rw [hKcard]; rfl
      have hcompl : Nat.card ↥(typeIHyp.typeI.typeF.H.subgroupOf vdata.L) * Nat.card ↥C
          = Nat.card ↥vdata.L := hFrobG.isComplement.card_mul_card
      have hce : H78.complementIndex = Nat.card ↥C := by
        show Nat.card ↥vdata.L / Nat.card typeIHyp.typeI.typeF.H = Nat.card ↥C
        rw [← hKcard, ← hcompl, Nat.mul_div_cancel_left _ Nat.card_pos]
      rw [hke, hce]; exact hfrobB
    exact zetaNuRhoNormSqGeOfDade typeIHyp.toHypothesis71
      (typeIHyp.dadeData.dade.fullDadeIsometryData typeIHyp.hconj).toDadeIsometryData.isDadeIsometry
      typeIHyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv
      hdeg_match coh.extension hnu_isometry hagree
      (OddOrder.Peterfalvi.S14.witness_L_hzeta0nu hG typeIHyp hFrobG coh (θ 0) hθ0_ne)
      (inner_self_induce_eq_one_of_frobeniusGroup hFrobG (θ 0) hθ0_ne) a ha hsmall

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.10)**: a type-I maximal subgroup `M` over `N_G(V)` together
with its Dade data exists.  Symmetric to `exists_LHypothesis`, packaging (13.17)
for the `V`-side with the Dade data and the virtual character `β_M` of (14.10).

The whole structural / σ-counting / set-theoretic content is discharged genuinely:
the type-I subgroup `M`, its `S14.Hypothesis` `typeIHyp`, and the §7 coherence datum
`h78` come from `exists_M_hypothesis78` (the V-side dual of `witness_L_hypothesis78`,
built through `typeII_overNormalizer_frobenius_V` + `frobenius_typeI_coherent`); the
`Mset`/`tau`/`tau1`/`psi`/`G0`/`betaM` data are read off `h78`; the TI / normalizer
facts are the `base_*` helpers; and the two `G0` covering facts are elementary set
algebra on the (14.11.3) complement `G₀ = G − [Ã(M) ∪ (W−(W₁∪W₂))^G ∪ (P#)^G ∪ (Q#)^G]`.

Instance coherence across the producer/consumer boundary is handled by opening
`S12.FiniteInduce` (the same scoped `Fintype`/`Invertible` instances that
`MHypothesis`'s field types and `exists_M_hypothesis78`'s existential are built with),
so no competing `Fintype.ofFinite`/`Invertible` is introduced.

Two obligations are discharged genuinely, via extra witnesses on `exists_M_hypothesis78`:
* `psi_degree_eq_e` (`ζ(1) = e = pq`): the producer witnesses `ζ_{ind1H}(1) = [M:K]`
  (`θ ind1H = 1_K` + `induce_trivialChar_apply_eq_index`), then `zeta_one_eq_ind1H_one` +
  `hindex` (`[M:K] = pq`) close it;
* `psi_tau1_norm_one` (`‖ψ^{τ₁}‖² = 1`): the producer witnesses `‖ζ‖² = 1` (the distinguished
  `ζ = Ind_K θ_0`, `θ_0 ≠ 1_K`, is Frobenius-irreducible —
  `inner_self_induce_eq_one_of_frobeniusGroup`), and `tau1 = ν` is a family isometry on it
  (`nu_isometry`).

One residual obligation remains isolated as the genuine deep §13 character content (gated on
the η-grid theory, not on this assembly): the joint existence of the `±1` signs with the
(13.1.d) η-grid expansion of `1_G + Δ` (Track A, issue 3002), consumed by the
`betaSigns`/`betaSigns_pm`/`betaGrid` fields — no specific sign choice is asserted. -/
theorem exists_MHypothesis [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (MHypothesis hyp) := by
  have hTII : IsTypeII hyp.base.T := T_typeII _hG hyp
  obtain ⟨M, typeIHyp, hM_max, hnorm_V, hindex, h78, hH_maxnilp, hhyp_dade, hdeg_ind1H, hnorm1,
      hnormSq⟩ :=
    exists_M_hypothesis78 _hG hyp hTII
  -- **Peterfalvi (13.1.d)**: the `η`-grid expansion of `1_G + Δ` with `±1` signs.  The genuine
  -- Track A obligation (issue 3002): the signs and the expansion are supplied together, so no
  -- specific (false) sign choice is asserted — only their honest joint existence is deferred.
  obtain ⟨betaSignsData, hbetaSigns_pm, hbetaGrid⟩ :
      ∃ signs : Fin hyp.base.q → Fin hyp.base.p → ℤ,
        (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
        OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + h78.delta =
          ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (signs i j : ℂ) • hyp.base.eta i j :=
    sorry
  refine ⟨{
    M := M
    K := maxNilpotentNormalHall M
    M_maximal := hM_max
    normalizer_V_le_M := hnorm_V
    K_eq_MF := rfl
    typeIHyp := typeIHyp
    h78 := h78
    Mset := Set.range h78.hyp76.zeta
    tau := h78.nu
    tau1 := h78.nu
    psi := h78.hyp76.zeta h78.zetaDistinct
    e := hyp.base.p * hyp.base.q
    k := Nat.card ↥(maxNilpotentNormalHall M)
    e_eq_index := hindex.symm
    complement_card_eq_pq := rfl
    k_eq_card_K := rfl
    psi_mem := ⟨h78.zetaDistinct, rfl⟩
    psi_degree_eq_e := ?psiDeg
    betaM := h78.beta
    betaM_formula := True
    betaM_formula_holds := trivial
    betaM_eq := rfl
    psi_tau1_eq := rfl
    betaSigns := betaSignsData
    betaSigns_pm := hbetaSigns_pm
    betaGrid := hbetaGrid
    G0 := Set.univ \ (typeIHyp.dadeData.dade.dadeSupport ∪
      (conjClassSet ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
        ∪ conjClassSet (sharpSubgroup hyp.base.P)
        ∪ conjClassSet (sharpSubgroup hyp.base.Q)))
    psi_tau1_norm_one := ?normOne
    G0_off_dadeSupport := ?offDade
    G0_orbit_cover := ?orbCover
    G0_avoid := ?avoid
    W_normalizer_V := base_W_normalizer_V hyp
    P_isTI := base_P_isTI _hG hyp
    Q_isTI := base_Q_isTI _hG hyp hTII
    card_normalizer_P_eq := base_card_normalizer_P_eq _hG hyp
    card_normalizer_Q_eq := base_card_normalizer_Q_eq _hG hyp hTII
    h78_hyp_eq := hhyp_dade
    h78_H_eq := hH_maxnilp
    h78_zetaNuRho_normSq_ge := ?normSq
  }⟩
  case offDade =>
    intro g hg hin
    exact hg.2 (Set.mem_union_left _ hin)
  -- **Peterfalvi (14.11.3)**: the concrete `G₀` avoids the three singular orbits — direct
  -- set algebra on the defining complement.
  case avoid =>
    intro g hg
    exact ⟨fun h => hg.2 (Set.mem_union_right _
        (Set.mem_union_left _ (Set.mem_union_left _ h))),
      fun h => hg.2 (Set.mem_union_right _
        (Set.mem_union_left _ (Set.mem_union_right _ h))),
      fun h => hg.2 (Set.mem_union_right _ (Set.mem_union_right _ h))⟩
  case orbCover =>
    intro g hgd hg0
    have hmem : g ∈ typeIHyp.dadeData.dade.dadeSupport ∪
        (conjClassSet ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
          ∪ conjClassSet (sharpSubgroup hyp.base.P)
          ∪ conjClassSet (sharpSubgroup hyp.base.Q)) := by
      by_contra h
      exact hg0 ⟨Set.mem_univ g, h⟩
    rcases hmem with h | h
    · exact absurd h hgd
    · exact h
  -- **Peterfalvi (7.6)/(14.10)**: `ψ(1) = ζ_{ind1H}(1) = [M:K] = e = pq` — the induced
  -- principal degree, genuinely discharged via `exists_M_hypothesis78`'s degree witness.
  case psiDeg => rw [h78.zeta_one_eq_ind1H_one, hdeg_ind1H, hindex]
  -- **Peterfalvi (7.5)/(7.8)**: `‖ψ^{τ₁}‖² = ‖ζ‖² = 1` — `τ₁ = ν` is a family isometry
  -- (`nu_isometry`, `ζ = ψ` non-`ind1H`) and `ζ` is unit-norm (`hnorm1`, Frobenius irreducible).
  case normOne =>
    rw [h78.nu_isometry h78.zetaDistinct h78.zetaDistinct h78.zetaDistinct_ne_ind1H
      h78.zetaDistinct_ne_ind1H]
    exact hnorm1
  -- **Peterfalvi (7.8.b)**: the coherence-norm lower bound, now genuinely discharged by the
  -- `exists_M_hypothesis78` witness (via the concrete §7 producer `zetaNuRhoNormSqGeOfDade`).
  case normSq => exact hnormSq

/-- **Peterfalvi (14.16)**→(14.7) bridge: if the Fitting kernel `H` of `L`
coincides with `U`, then `U` is characteristic in `H` — it is the whole of `H`,
and `⊤` is characteristic.  This is what lets the non-conjugate case `H = U` of
(14.16) feed back into (14.7). -/
theorem U_characteristic_of_H_eq_U {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp) (hHU : Ldata.H = hyp.base.U) :
    (hyp.base.U.subgroupOf Ldata.H).Characteristic := by
  have htop : hyp.base.U.subgroupOf Ldata.H = ⊤ :=
    Subgroup.subgroupOf_eq_top.mpr (le_of_eq hHU)
  rw [htop]
  exact Subgroup.topCharacteristic

/-- **Peterfalvi (14.2)**: the field-normalizer configuration follows from the
Section 16 hypotheses.

This assembles Peterfalvi's concluding paragraph "By (14.12), (14.16) and (14.7),
the proof of Theorem (14.2) is complete."  Take the type-I subgroup `L` over
`N_G(U)` ((14.3), `exists_LHypothesis`) and split on whether `U` is characteristic
in `H`:

* if it is, (14.7) `field_normalizer_of_U_characteristic` finishes;
* otherwise take the type-I subgroup `M` over `N_G(V)` ((14.10),
  `exists_MHypothesis`) and split on whether `L` is conjugate to `M`:
  * if it is, (14.12) `field_normalizer_of_L_conj_M` finishes;
  * otherwise (14.13)–(14.16) `H_eq_U` give `H = U`, so `U` is characteristic in
    `H` (`U_characteristic_of_H_eq_U`), contradicting the branch assumption. -/
theorem field_normalizer_structure [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hyp
  by_cases hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic
  · exact field_normalizer_of_U_characteristic _hG hyp Ldata hchar
  · obtain ⟨Mdata⟩ := exists_MHypothesis _hG hyp
    by_cases hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M
    · exact field_normalizer_of_L_conj_M _hG hyp Ldata Mdata hconj
    · exact absurd
        (U_characteristic_of_H_eq_U Ldata
          (H_eq_U _hG hyp
            { Ldata := Ldata, Mdata := Mdata, not_conj := hconj,
              h := Nat.card ↥Ldata.H, h_eq_card_H := rfl }))
        hchar

/-- **Peterfalvi Section 16 + BG Appendix C**: BG Appendix C turns the
field-normalizer configuration into `p <= q`, contradicting (14.1). -/
theorem nonexistence_of_G [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (bgAppendixC : FieldNormalizerData hyp → hyp.base.p ≤ hyp.base.q) :
    False := by
  rcases field_normalizer_structure hG hyp with ⟨data⟩
  exact (not_lt_of_ge (bgAppendixC data)) hyp.q_lt_p

end OddOrder.Peterfalvi.S16
