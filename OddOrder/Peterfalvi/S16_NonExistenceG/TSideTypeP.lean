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
# TSideTypeP

Prefix-split from `OddOrder.Peterfalvi.S16_NonExistenceG.SubgroupL` (2000-line limit, issue 0103 第 2
パス).
-/

/-!
# Peterfalvi (14.3)-(14.7) — the subgroup L over N_G(U)

Split from the former monolithic `OddOrder.Peterfalvi.S16_NonExistenceG` (directory split, issue
0103).
-/
namespace OddOrder.Peterfalvi.S16
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
  `|QV/Q| = |V|` (Coq `card_isog (sdprod_isog defQV)`) — the source of the abelian-quotient irr
  count.
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
index `[T:QV] = p` plugged in via `T_derived_index_eq_p`. It is **ungated** (no
`IsTypeII`/`IsTypeP2`
input, no `sorry`): the two facts entering are supplied by the caller as `𝒯`'s
conjugation-invariance and irreducible-induction (inertia `= QV`) hypotheses.  For the `calT1`
assembly `𝒯` is the non-principal inflated `Irr(QV/Q)`-family, `|𝒯| = |V| − 1`
(the `|Irr(QV/Q)| = |QV/Q| = |V|` count, gated on `V` abelian — see the blocker map on
`T_typeIII_ratio_le`), yielding `|calT1| = (|V| − 1)/p`.

The `Fintype`/`Invertible` instances are taken explicitly (satisfiable from `Finite G`) so the
`induce`-image in the statement type-checks, matching the shared-infra convention. -/
theorem calT1_image_induce_card_eq [Finite G] (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
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
  haveI : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Fintype.ofFinite _
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
  (decompose in the Frobenius complement `U ⋊ W₁`: the `W₁`-part lands in `W₁ ⊓ T' = ⊥`), and then
  in
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
    have : (⟨x, hxM'⟩ : ↥(derivedInG hyp.base.T)) ∈
        (td.typeP.H.subgroupOf (derivedInG hyp.base.T)) ⊓
        (td.typeP.U.subgroupOf (derivedInG hyp.base.T)) := by
      rw [Subgroup.mem_inf]
      exact ⟨Subgroup.mem_subgroupOf.mpr hx.1, Subgroup.mem_subgroupOf.mpr hx.2⟩
    rw [hd, Subgroup.mem_bot] at this; rw [Subgroup.mem_bot]; exact Subtype.ext_iff.mp this
  -- `(U ⊔ W₁) ⊓ T' ≤ U` (Frobenius decomposition).
  have hUW1M'_le_U : (td.typeP.U ⊔ td.typeP.W1) ⊓ derivedInG hyp.base.T ≤ td.typeP.U := by
    intro x hx; obtain ⟨hxUW1, hxM'⟩ := hx
    have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius td.typeP td.common.1
    obtain ⟨⟨u, w⟩, hgw⟩ := (hfrob.isComplement.existsUnique ⟨x, hxUW1⟩).exists
    have huU : ((u : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) ∈ td.typeP.U :=
      Subgroup.mem_subgroupOf.mp u.2
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
  have hcardM' : Nat.card ↥td.typeP.H * Nat.card ↥td.typeP.U =
      Nat.card ↥(derivedInG hyp.base.T) := by
    rw [← td.typeP.derived_complement.card_mul,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleM').toEquiv]
  have hcardM : Nat.card ↥(derivedInG hyp.base.T) * Nat.card ↥td.typeP.W1 =
      Nat.card ↥hyp.base.T := by
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
    change e x ∈ _
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
    change e uUW1 = _
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
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
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
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
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
    (mkN.comp ((derivedInG hyp.base.T).subgroupOf hyp.base.T).subtype).codRestrict Hbar
      (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩) with hq_def
  have hq : ∀ x : ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T),
      ((q x : ↥Hbar) : ↥hyp.base.T ⧸ hyp.base.Q.subgroupOf hyp.base.T) = mkN (x : ↥hyp.base.T) :=
    fun x => rfl
  have hq_surj : Function.Surjective q := by
    rintro ⟨z, hz⟩; rw [hHbar, Subgroup.mem_map] at hz
    obtain ⟨x, hxH, hxz⟩ := hz; exact ⟨⟨x, hxH⟩, Subtype.ext hxz⟩
  have hqinj : Function.Injective
      (ClassFunction.compHom q : ClassFunction ↥Hbar ℂ →
        ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ) :=
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
  set infl : IrreducibleCharacter ↥Hbar →
      IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) :=
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
      IrreducibleCharacter.inertia (G := ↥hyp.base.T)
        (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) θ =
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) := by
    intro θ hθ
    rw [h𝒯, Finset.mem_image] at hθ
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    rw [Finset.mem_filter] at hθbar
    exact inertia_inflate_eq_of_frobeniusQuotient (N := hyp.base.Q.subgroupOf hyp.base.T)
      (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) hNH hqfrob0 q hq hqinj θbar hθbar.2
  -- hconj
  have hconj : ∀ θ ∈ 𝒯, ∀ g : ↥hyp.base.T,
      IrreducibleCharacter.conjBy (G := ↥hyp.base.T)
        (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) g θ ∈ 𝒯 := by
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
      change ClassFunction.compHom q _ = ClassFunction.conjBy g (ClassFunction.compHom q _)
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
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
        T_typeIII_card_U hyp td]
    -- |filter (≠triv) univ| = |univ| - 1
    have hfilter : (Finset.univ.filter (fun θbar : IrreducibleCharacter ↥Hbar =>
        θbar ≠ trivialIrreducibleCharacter ↥Hbar)).card =
        Fintype.card (IrreducibleCharacter ↥Hbar) - 1 := by
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
* `hgalois𝒯 : θ ∈ 𝒯 ⟹ σθ ∈ 𝒯` for every coefficient automorphism `σ`, since inflation
  commutes pointwise with `mapRingEquiv` and Galois transport preserves non-principality;
and with the count `|calT1_image| = (|V| − 1)/p`.  This packages the "pure transcription" `𝒯`-build
so the (14.9) coherence carrier `horth` is dischargeable end-to-end. -/
theorem T_typeIII_calT1_family_galois [Finite G] (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
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
      (∀ (σc : ℂ ≃+* ℂ) θ, θ ∈ 𝒯 →
        IrreducibleCharacter.galoisMap σc θ ∈ 𝒯) ∧
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
  refine ⟨𝒯, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    change (ClassFunction.compHom q (θbar : ClassFunction ↥Hbar ℂ) :
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
      change (θbar : ClassFunction ↥Hbar ℂ) = trivialClassFunction ↥Hbar
      rw [← ClassFunction.conj_conj (θbar : ClassFunction ↥Hbar ℂ), hcoe]
      exact trivialClassFunction_isReal
    · -- `infl (θbar̄) = (infl θbar)^`: pointwise `compHom q θbar̄ x = star (θbar (q x))`.
      apply IrreducibleCharacter.ext
      change ClassFunction.compHom q ((θbar : ClassFunction ↥Hbar ℂ).conj)
        = (ClassFunction.compHom q (θbar : ClassFunction ↥Hbar ℂ)).conj
      ext x
      simp [ClassFunction.compHom_apply, ClassFunction.conj_apply]
  -- Arbitrary coefficient automorphisms preserve the inflated non-principal family.
  · intro σc θ hθ
    rw [h𝒯, Finset.mem_image] at hθ ⊢
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    rw [Finset.mem_filter] at hθbar
    refine ⟨IrreducibleCharacter.galoisMap σc θbar, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hcontra
      apply hθbar.2
      apply IrreducibleCharacter.ext
      ext x
      have hx := congrArg (fun c : IrreducibleCharacter ↥Hbar =>
        ((c : ClassFunction ↥Hbar ℂ) x)) hcontra
      have hx' := congrArg σc.symm hx
      simpa [IrreducibleCharacter.galoisMap,
        IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        trivialClassFunction_apply] using hx'
    · apply IrreducibleCharacter.ext
      change ClassFunction.compHom q
          (IrreducibleCharacter.galoisMap σc θbar : ClassFunction ↥Hbar ℂ) =
        ClassFunction.mapRingEquiv σc
          (ClassFunction.compHom q (θbar : ClassFunction ↥Hbar ℂ))
      ext x
      simp [IrreducibleCharacter.galoisMap, ClassFunction.compHom_apply,
        ClassFunction.mapRingEquiv_apply]
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
        change ClassFunction.compHom q _ = ClassFunction.conjBy g (ClassFunction.compHom q _)
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
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
          T_typeIII_card_U hyp td]
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

open scoped IsMulCommutative in
open scoped Classical in
/-- Compatibility projection of `T_typeIII_calT1_family_galois`, retaining the
original family interface for coherence consumers that only need conjugate closure. -/
theorem T_typeIII_calT1_family [Finite G] (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
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
  obtain ⟨𝒯, hinertia, hne, hlinear, hconj, _, hcard⟩ :=
    T_typeIII_calT1_family_galois hyp td
  exact ⟨𝒯, hinertia, hne, hlinear, hconj, hcard⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open scoped Classical in
/-- Galois closure passes from a source family to its induced family. -/
theorem inducedFamily_mapRingEquiv_mem
    {L : Type*} [Group L] [Fintype L]
    (K : Subgroup L) [Finite K] [Invertible (Nat.card K : ℂ)]
    (𝒯 : Finset (IrreducibleCharacter K))
    (hgalois : ∀ (σc : ℂ ≃+* ℂ) θ, θ ∈ 𝒯 →
      IrreducibleCharacter.galoisMap σc θ ∈ 𝒯)
    (σc : ℂ ≃+* ℂ) {ζ : ClassFunction L ℂ}
    (hζ : ζ ∈ (↑(𝒯.image (fun θ =>
      ClassFunction.induce K θ.toClassFunction)) :
        Set (ClassFunction L ℂ))) :
    ClassFunction.mapRingEquiv σc ζ ∈
      (↑(𝒯.image (fun θ => ClassFunction.induce K θ.toClassFunction)) :
        Set (ClassFunction L ℂ)) := by
  rw [Finset.mem_coe, Finset.mem_image] at hζ ⊢
  obtain ⟨θ, hθ, rfl⟩ := hζ
  refine ⟨IrreducibleCharacter.galoisMap σc θ, hgalois σc θ hθ, ?_⟩
  exact (ClassFunction.mapRingEquiv_induce σc θ.toClassFunction).symm

/-- **The intrinsic type-III kernel size bound `2p + 1 ≤ |V|`** (ungated, the crude `hcard2` input).
The intrinsic `U ⋊ W₁` Frobenius (`T_typeIII_UW1_frobenius`) has odd kernel `U` (`|U| = |V|`,
`T_typeIII_card_U`) and odd complement `W₁` (`|W₁| = p`, `T_typeIII_card_W1`); the odd-order
Frobenius
size condition `IsFrobeniusGroup.two_mul_card_complement_add_one_le_card_kernel` (`|A| ∣ |N|−1`, and
`|N|−1` even with `|A|` odd forces `|N|−1 ≥ 2|A|`) then gives `2p + 1 ≤ |V|`.

This is the **ungated** source of the `calT1` crude size bound `2 ≤ (|V|−1)/p` (`hcard2` in
`T_typeIII_ratio_le`): it needs only oddness (subgroups of the odd `G`) plus the intrinsic Frobenius
index `[T:T'] = p` — **not** the lane-b-gated `|V|`-lower-bound `v = (q^p−1)/(q−1)` (13.15).  (The
`v`-value is still needed for the *exact* count `(v−1)/p`, but the coherence input `hcard2` only
needs
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
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
      T_typeIII_card_U hyp td]
  have hcardA : Nat.card ↥(td.typeP.W1.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) = hyp.base.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv,
      T_typeIII_card_W1 hyp td]
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
    exact ⟨a.1, (Set.mem_sdiff _).mpr
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
  -- Dade supported-span inner-preservation lemma (the same brick `S14.Sset_tau_isometry_diff`
  -- uses).
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
derivedInG T`, so their differences are automatically supported in `sigmaSharp T =
(T')^#` — matching
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

end OddOrder.Peterfalvi.S16
