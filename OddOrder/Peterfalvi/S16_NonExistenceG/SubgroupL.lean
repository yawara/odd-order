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
# Peterfalvi (14.3)-(14.7) — the subgroup L over N_G(U)

Split from the former monolithic `OddOrder.Peterfalvi.S16_NonExistenceG` (directory split, issue 0103).
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

end OddOrder.Peterfalvi.S16
