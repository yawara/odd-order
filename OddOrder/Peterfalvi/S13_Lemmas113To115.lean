/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_MaximalIII_IVBasic
import OddOrder.Peterfalvi.S12_TypeVSibley

/-!
# S13_Lemmas113To115

Prefix-split from `OddOrder.Peterfalvi.S13_MaximalIII_IV` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S13
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]


/-! ## (11.3)--(11.5): commutator-chain consequences -/

/-- **Peterfalvi (11.3), the Theorem (6.3) coherence-extension input** (§13 instance): if the
sub-family `S(H₀C)` is coherent, then so is the full family `S`.

This is Peterfalvi's Theorem (6.3) applied with `(L, K, M, H, H₁) = (M, M', 1, HC, H₀C)`; its
hypotheses hold in the §13 setup ((6.3.a) `HC` nilpotent — `H = M_F` nilpotent and `C = C_U(H)`
centralizes `H`; (6.3.b) from the coherence of `S(H₀C)`; (6.3.c) from (9.6)/(11.1)).  Left as a
named obligation: the repo's §6 coherence is packaged through the `SibleyDadeHypothesis`
filtration machinery (`S08_Theorem63`), not as a standalone "subfamily-coherent ⟹ coherent"
statement, so discharging this is §6 character theory (lane-b). -/
theorem coherent_S_of_coherent_SH0C [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M)
    (_hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau hyp.base.Sset hyp.base.A0) := by
  classical
  -- the (6.3) data: `(K, H, M, H₁) = (M', HC, ⊥, H₀C)`-traces inside `↥M`
  have hHCleM : hyp.HC ≤ M := hyp.HC_le_derived.trans (Subgroup.map_subtype_le _)
  have hH0CleM : hyp.H0C ≤ M := hyp.H0C_le_derived.trans (Subgroup.map_subtype_le _)
  have hH0CleHC : hyp.H0C ≤ hyp.HC :=
    sup_le (hyp.H0_lt_H.le.trans le_sup_left) le_sup_right
  -- instances for the oracle
  haveI : IsSolvable ↥M := _hG.solvable_of_lt_top M (lt_top_iff_ne_top.mpr hyp.base.maximal.1)
  haveI : IsSolvable ↥((derivedInG M).subgroupOf M) := inferInstance
  haveI hHCnil : Group.IsNilpotent ↥(hyp.HC.subgroupOf M) := by
    haveI := hyp.HC_isNilpotent
    exact Group.nilpotent_of_surjective
      (Subgroup.subgroupOfEquivOfLe hHCleM).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hHCleM).symm.surjective
  haveI hH₁n : (hyp.H0C.subgroupOf M).Normal := hyp.H0C_subgroupOf_normal
  have hHnorm : (hyp.HC.subgroupOf M).Normal := hyp.HC_subgroupOf_normal
  -- strictness `H₀C-trace < HC-trace`
  have hH₁H : hyp.H0C.subgroupOf M < hyp.HC.subgroupOf M := by
    refine lt_of_le_of_ne (Subgroup.subgroupOf_mono M hH0CleHC) ?_
    intro heq
    have hamb : hyp.H0C = hyp.HC := by
      have h1 := congrArg (Subgroup.map M.subtype) heq
      rwa [Subgroup.map_subgroupOf_eq_of_le hH0CleM,
        Subgroup.map_subgroupOf_eq_of_le hHCleM] at h1
    exact hyp.H_not_le_H0C (hamb ▸ (le_sup_left : hyp.base.typeP.H ≤ hyp.HC))
  have hHK : hyp.HC.subgroupOf M ≤ (derivedInG M).subgroupOf M :=
    Subgroup.subgroupOf_mono M hyp.HC_le_derived
  -- numerical bound (6.3.c): `4q² + 1 < p^q`
  have hbound : 4 * ((derivedInG M).subgroupOf M).index ^ 2 + 1
      < Nat.card (↥(hyp.HC.subgroupOf M)
          ⧸ (hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)) := by
    have hidx : ((derivedInG M).subgroupOf M).index = hyp.q :=
      hyp.base.typeP.card_W1_eq_derived_index.symm
    have hcardq : Nat.card (↥(hyp.HC.subgroupOf M)
        ⧸ (hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M))
        = hyp.p ^ hyp.q := by
      rw [← Subgroup.index_eq_card,
        show ((hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)).index
          = (hyp.H0C.subgroupOf M).relIndex (hyp.HC.subgroupOf M) from rfl,
        Subgroup.relIndex_subgroupOf hHCleM]
      exact hyp.H0C_relIndex_HC _hG
    rw [hidx, hcardq]
    obtain ⟨hp', hq', hpo, hqo, hne⟩ := hyp.p_q_distinct_odd_primes _hG
    exact prime_pow_gt_four_mul_sq_add_one hp' hq' hpo hqo hne
  -- assemble via the (6.3) oracle
  have hmain := OddOrder.Peterfalvi.S08.six_three_of_six_two_oracle
    (L := M) (K := (derivedInG M).subgroupOf M) (H := hyp.HC.subgroupOf M)
    (M := ⊥) (H₁ := hyp.H0C.subgroupOf M) hHnorm bot_le hH₁H hHK
    hyp.base.tau hyp.base.A0
    (fun X => OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) X)
    ?_ (by
      show Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
        (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
          (hyp.H0C.subgroupOf M)) hyp.base.A0)
      rw [← hyp.SOf_eq]
      exact _hcoh) hbound
  · have hSset : hyp.base.Sset
        = OddOrder.Peterfalvi.S08.inducedKernelFamily
            ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
      unfold OddOrder.Peterfalvi.S12.Hypothesis.Sset
      exact OddOrder.Peterfalvi.S12.inducedFamily_eq_inducedKernelFamily_bot
    rw [hSset]
    exact hmain
  · -- the (5.6) break-member oracle `h56` = the §11 dichotomy producer
    intro A B hAnorm hBnorm hBA hAH₁ _hcentral hAcoh hBncoh
    haveI := hAnorm
    haveI := hBnorm
    haveI : (A.subgroupOf ((derivedInG M).subgroupOf M)).Normal := hAnorm.subgroupOf _
    haveI : (B.subgroupOf ((derivedInG M).subgroupOf M)).Normal := hBnorm.subgroupOf _
    have hAne : A.subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤ := by
      intro htop
      exact absurd (hHK.trans ((Subgroup.subgroupOf_eq_top.mp htop).trans hAH₁))
        (not_le_of_gt hH₁H)
    have hBne : B.subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤ := by
      intro htop
      exact absurd (hHK.trans ((Subgroup.subgroupOf_eq_top.mp htop).trans (hBA.trans hAH₁)))
        (not_le_of_gt hH₁H)
    have hAcoh' : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.base.dadeData.dade
          (hyp.base.dadeData.dade.fullDadeIsometryData hyp.base.hconj))
        (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A)
        hyp.base.A0) := hAcoh
    have hBncoh' : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.base.dadeData.dade
          (hyp.base.dadeData.dade.fullDadeIsometryData hyp.base.hconj))
        (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B)
        hyp.base.A0) := fun h => hBncoh h
    exact hyp.base.exists_source_of_coherence_dichotomy _hG
      (hyp.params_mu_eq _hG _hG.odd) hyp.params_delta_pm
      (hyp.params_delta_sign _hG _hG.odd) hyp.params_zeta_mem hyp.params_zeta_degree
      (hyp.base.isTypeIIIorIV _hG)
      (OddOrder.GroupTheory.typePNontrivialCore_of_isTypeIIIorIV
        (hyp.base.isTypeIIIorIV _hG) hyp.base.typeP)
      (OddOrder.Peterfalvi.S11.exists_chiefFactorData _hG _).choose
      hAne hBne hAcoh' hBncoh'

/-- **Peterfalvi (11.3)**: `S(H_0 C)` is not coherent.

If it were, Theorem (6.3) (`coherent_S_of_coherent_SH0C`) would make the full family `S` coherent,
contradicting Theorem (10.8) (`S12.S_not_coherent`).  The theorem is thereby reduced, with no
`sorry` of its own, to those two cited results. -/
theorem S_H0C_not_coherent [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) :
    ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) :=
  fun hcoh => OddOrder.Peterfalvi.S12.S_not_coherent _hG hyp.base
    (coherent_S_of_coherent_SH0C _hG hyp hcoh)

/-- **Peterfalvi (11.4)**: if `S(H_1)` is coherent for a normal subgroup `H_1 < M'`,
then `|M'/H_1| - 1 ≤ 2 q |U/C|` (the quotient bound from Theorem (6.2)), stated here in
the subtraction-free form `|M' : H_1| ≤ 2 q |U : C| + 1`. -/
theorem coherent_quotient_bound [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H1 : Subgroup G}
    (hyp : Hypothesis M) (hH1_norm : M ≤ Subgroup.normalizer (H1 : Set G))
    (hH1_lt : H1 < derivedInG M)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf H1) hyp.base.A0)) :
    H1.relIndex (derivedInG M) ≤ 2 * hyp.q * hyp.C.relIndex hyp.U + 1 := by
  classical
  -- normality instances for the section subgroups and their traces
  haveI hA'n : ((H1.subgroupOf M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (hH1_lt.le.trans (Subgroup.map_subtype_le _))).mpr hH1_norm
  haveI hBn : ((hyp.H0C.subgroupOf M)).Normal := hyp.H0C_subgroupOf_normal
  haveI : ((H1.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M)).Normal :=
    hA'n.subgroupOf _
  haveI : ((hyp.H0C.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M)).Normal :=
    hBn.subgroupOf _
  haveI : ((hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)).Normal :=
    hBn.subgroupOf _
  -- coherence dichotomy at the pinned family (`SOf_eq`; `tau`/`A0` are definitional)
  have hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.base.dadeData.dade
        (hyp.base.dadeData.dade.fullDadeIsometryData hyp.base.hconj))
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
        (H1.subgroupOf M)) hyp.base.A0) := by
    have h := hcoh
    rw [hyp.SOf_eq] at h
    exact h
  have hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.base.dadeData.dade
        (hyp.base.dadeData.dade.fullDadeIsometryData hyp.base.hconj))
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
        (hyp.H0C.subgroupOf M)) hyp.base.A0) := by
    have h := S_H0C_not_coherent _hG hyp
    rw [hyp.SOf_eq] at h
    exact h
  -- the (6.2) bound at `(C, D) = (HC, HC)`-traces
  have hbound := hyp.base.six_two_dichotomy_bound _hG
    (hyp.params_mu_eq _hG _hG.odd) hyp.params_delta_pm
    (hyp.params_delta_sign _hG _hG.odd) hyp.params_zeta_mem hyp.params_zeta_degree
    (hyp.base.isTypeIIIorIV _hG)
    (OddOrder.GroupTheory.typePNontrivialCore_of_isTypeIIIorIV
      (hyp.base.isTypeIIIorIV _hG) hyp.base.typeP)
    (OddOrder.Peterfalvi.S11.exists_chiefFactorData _hG _).choose
    (A' := H1.subgroupOf M) (B := hyp.H0C.subgroupOf M)
    (C := hyp.HC.subgroupOf M) (D := hyp.HC.subgroupOf M)
    (Hypothesis.trace_ne_top_of_lt_derived hH1_lt) hyp.H0C_trace_ne_top
    (Subgroup.subgroupOf_mono M
      (sup_le (hyp.H0_lt_H.le.trans le_sup_left) le_sup_right))
    (Subgroup.subgroupOf_mono M hyp.HC_le_derived)
    hyp.HC_central_condition hAcoh hBncoh
  -- the square-root factor is `√1 = 1`
  have hsq : Nat.card (↥(hyp.HC.subgroupOf M) ⧸
      (hyp.HC.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)) = 1 := by
    rw [Subgroup.subgroupOf_self]
    haveI : Subsingleton (↥(hyp.HC.subgroupOf M) ⧸ (⊤ : Subgroup ↥(hyp.HC.subgroupOf M))) :=
      QuotientGroup.subsingleton_quotient_top
    exact Nat.card_unique
  rw [hsq] at hbound
  simp only [Nat.cast_one, Real.sqrt_one, mul_one] at hbound
  -- the left side is the relative index `|M' : H₁|`
  have hL : Nat.card (↥((derivedInG M).subgroupOf M) ⧸
      (H1.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M))
      = H1.relIndex (derivedInG M) := by
    have h1 : Nat.card (↥((derivedInG M).subgroupOf M) ⧸
        (H1.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M))
        = (H1.subgroupOf M).relIndex ((derivedInG M).subgroupOf M) := rfl
    rw [h1]
    exact Subgroup.relIndex_subgroupOf (show derivedInG M ≤ M from Subgroup.map_subtype_le _)
  rw [hL] at hbound
  -- the index factor is `q·|U:C|`
  have hidx : ((hyp.HC.subgroupOf M).index : ℝ)
      = (hyp.base.w1 * hyp.C.relIndex hyp.U : ℕ) := by
    rw [hyp.HC_trace_index]
  rw [hidx] at hbound
  -- conclude over `ℕ`
  have hfinal : (H1.relIndex (derivedInG M) : ℝ)
      ≤ 2 * (hyp.base.w1 * hyp.C.relIndex hyp.U : ℕ) + 1 := by linarith
  have : H1.relIndex (derivedInG M) ≤ 2 * (hyp.base.w1 * hyp.C.relIndex hyp.U) + 1 := by
    exact_mod_cast hfinal
  calc H1.relIndex (derivedInG M) ≤ 2 * (hyp.base.w1 * hyp.C.relIndex hyp.U) + 1 := this
    _ = 2 * hyp.q * hyp.C.relIndex hyp.U + 1 := by
        change 2 * (hyp.base.w1 * hyp.C.relIndex hyp.U) + 1
          = 2 * hyp.base.w1 * hyp.C.relIndex hyp.U + 1
        ring

/-- **`HC < M'`** (sorry-free): if `HC = M'` then `U ≤ HC = H·C`; decomposing `u = a·b`
(`a ∈ H`, `b ∈ C`) along the normal `H`-factor forces `a ∈ H ∩ U = ⊥`, so `u = b ∈ C`,
contradicting `C ⊊ U` (`C_lt_U`).  The strict inclusion feeds the (11.4)/(11.5) quotient bound
and the `𝒮(HC)`-nonemptiness (`coherent_SOf_HC`). -/
theorem HC_lt_derived [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.HC < derivedInG M := by
  refine lt_of_le_of_ne hyp.HC_le_derived ?_
  intro hEq
  refine (hyp.C_lt_U).not_ge ?_
  intro u hu
  have huHC : u ∈ hyp.HC := by rw [hEq]; exact hyp.base.typeP.U_le hu
  -- decompose `u = h·c` along the normal `H`-factor inside `↥M`
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hCle : hyp.C ≤ M := (hyp.C_le_U.trans hyp.base.typeP.U_le).trans
    (Subgroup.map_subtype_le _)
  haveI hHn : ((hyp.base.typeP.H).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mpr hyp.H_normalized_by_M
  have huM : u ∈ M := (hyp.HC_le_derived.trans (Subgroup.map_subtype_le _)) huHC
  have hmem : (⟨u, huM⟩ : ↥M) ∈
      (hyp.base.typeP.H).subgroupOf M ⊔ hyp.C.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup hHle hCle]
    exact Subgroup.mem_subgroupOf.mpr huHC
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  have haH : ((a : ↥M) : G) ∈ hyp.base.typeP.H := Subgroup.mem_subgroupOf.mp ha
  have hbC : ((b : ↥M) : G) ∈ hyp.C := Subgroup.mem_subgroupOf.mp hb
  -- `a = u·b⁻¹ ∈ H ∩ U = ⊥`, so `u = b ∈ C`
  have haU : ((a : ↥M) : G) ∈ hyp.base.typeP.U := by
    have haeq : (a : ↥M) = ⟨u, huM⟩ * (b : ↥M)⁻¹ := by rw [← hab]; group
    have hcoe : ((a : ↥M) : G) = u * ((b : ↥M) : G)⁻¹ := by rw [haeq]; rfl
    rw [hcoe]
    exact Subgroup.mul_mem _ hu (Subgroup.inv_mem _ (hyp.C_le_U hbC))
  have ha1 : ((a : ↥M) : G) = 1 := by
    have := hyp.H_inf_U_eq_bot.le ⟨haH, haU⟩
    rwa [Subgroup.mem_bot] at this
  have hueq : u = ((b : ↥M) : G) := by
    have h1 : (⟨u, huM⟩ : ↥M) = a * b := hab.symm
    have h2 : u = ((a * b : ↥M) : G) := congrArg Subtype.val h1
    rw [h2]
    change ((a : ↥M) : G) * ((b : ↥M) : G) = ((b : ↥M) : G)
    rw [ha1, one_mul]
  rw [hueq]
  exact hbC

/-- **Coherence restricts to a subfamily** (Peterfalvi (5.2) monotonicity).  If `S` is coherent and
`S' ⊆ S` carries a nonzero `A`-supported witness, then `S'` is coherent with the *same* coherent
extension: the isometry (`extension_inner_eq`), `τ`-agreement (`extends_on_supported`) and
`ZIrr`-codomain (`extension_mem_ZIrr`) laws all transport along the `zSpan` / `zSupportedSpan`
monotonicity (`Submodule.span_mono` / `zSupportedSpan_mono_left`); only the `nonzero` witness must be
re-supplied for `S'`.  This extracts the restriction pattern shared by `coherent_SOf_HC` (`S(HC) ⊆
S(M'')`) and the world-bridge `𝒮(H₀C)`-coherence subset step (`sOf(H₀C) ⊆ sOf(H₀C')`, the (9.11)
`hY` route). -/
noncomputable def isCoherent_of_subset {L : Type*} [Group L] [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    {S S' : Set (ClassFunction L ℂ)} {A : Set L}
    (h : OddOrder.Peterfalvi.S07.IsCoherent τ S A) (hsub : S' ⊆ S)
    (hwit : ∃ φ : ClassFunction L ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S' A ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent τ S' A where
  nonzero := hwit
  extension := h.extension
  extension_inner_eq := fun a b ha hb =>
    h.extension_inner_eq a b (Submodule.span_mono hsub ha) (Submodule.span_mono hsub hb)
  extends_on_supported := fun a ha =>
    h.extends_on_supported a (OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left hsub ha)
  extension_mem_ZIrr := fun a ha =>
    h.extension_mem_ZIrr a (Submodule.span_mono hsub ha)

/-- **Coherence transports along a support change that shrinks the supported lattice**
(the support-side companion of `isCoherent_of_subset`: same family `S`, different support set).
If `S` is coherent on `A₁` and every `A₂`-supported lattice element is already `A₁`-supported
(`ℤ[S, A₂] ⊆ ℤ[S, A₁]`), then `S` is coherent on `A₂` with the *same* extension — only the
`nonzero` witness must be re-supplied on `A₂`.

The (9.11)/(6.8) use: the certain-type coherence (4.9)(b) lives on `A(M)`
(`supportInSubgroup (typePA M) M`) while the §10–§13 coherence interface uses
`A₀(M) ⊇ A(M)`; the column characters `μ_j` vanish off `A ∪ {1}` and `1 ∉ A₀`, so an
`A₀`-supported `ℤ[𝒯]`-combination is automatically `A`-supported and the lattices agree. -/
noncomputable def isCoherent_of_supportedSpan_le {L : Type*} [Group L] [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    {S : Set (ClassFunction L ℂ)} {A₁ A₂ : Set L}
    (h : OddOrder.Peterfalvi.S07.IsCoherent τ S A₁)
    (hle : OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A₂ ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A₁)
    (hwit : ∃ φ : ClassFunction L ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A₂ ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent τ S A₂ where
  nonzero := hwit
  extension := h.extension
  extension_inner_eq := h.extension_inner_eq
  extends_on_supported := fun a ha => h.extends_on_supported a (hle ha)
  extension_mem_ZIrr := h.extension_mem_ZIrr

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(4.9)(b) certain-type coherence, §10 interface form**: the certain-type column set
`𝒯 = certainTypeSet (hyp.toHypothesis46 …) k` is coherent for the §10 Dade map `hyp.tau` on the
§10 support `A₀(M)`.  This is the reducible-μ-side coherence input of the (9.11) `caseB`/
all-reducible assembly (issue 1019 update⁶⁰) — the §12-world analogue of the (6.8) case-(B)
`SibleyDadeHypothesis.certainTypeSet_isCoherent_tau`.

No `congrMap` seam is needed: under `toHypothesis46` the certain-type Dade map
`dadeIntegralCharacterMap h46.dade0 h46.tau` is *definitionally* `hyp.tau`
(`dade0 := hyp.dadeData.dade` and `tau := ….fullDadeIsometryData hyp.hconj` are the very
components of `S12.Hypothesis.tau`).  The support moves from `A(M)` to `A₀(M) = A(M) ∪ V^M` by
`isCoherent_of_supportedSpan_le`: every column `μ_j` vanishes off `A(M) ∪ {1}`
(`columnSum_support_subset`), so an `A₀`-supported `ℤ[𝒯]`-combination is automatically
`A(M)`-supported (`1 ∉ A₀`, `one_notMem_A0`); the `A₀`-witness is the `A(M)`-supported
`μ_{k⁻¹} − μ_k` of `certainType_nonzero`, enlarged along `A(M) ⊆ A₀(M)`. -/
noncomputable def certainTypeSet_isCoherent_A0 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M) (hodd : Odd (Nat.card G))
    [NeZero (Nat.card (hyp.toHypothesis46 hG hodd).W1)]
    {k : ((hyp.toHypothesis46 hG hodd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hodd).W1 ⊔ (hyp.toHypothesis46 hG hodd).W2)) →* ℂˣ}
    (hk : k ≠ 1) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S06.certainTypeSet (hyp.toHypothesis46 hG hodd) k) hyp.A0 := by
  haveI := hyp.finiteG
  classical
  -- (4.9)(b) on `A(M)`; the certain-type Dade map is definitionally `hyp.tau`
  have hbase : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S06.certainTypeSet (hyp.toHypothesis46 hG hodd) k)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA M hyp.typeP) M) :=
    OddOrder.Peterfalvi.S06.certainType_isCoherent (hyp.toHypothesis46 hG hodd) hk
  refine isCoherent_of_supportedSpan_le hbase ?_ ?_
  · -- `ℤ[𝒯, A₀] ⊆ ℤ[𝒯, A(M)]`: members vanish off `A(M) ∪ {1}` and `1 ∉ A₀`
    rintro φ ⟨hφspan, hφsupp⟩
    refine ⟨hφspan, ?_⟩
    have hsupp1 : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA M hyp.typeP) M ∪ {1} := by
      have hle : OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
          (OddOrder.Peterfalvi.S06.certainTypeSet (hyp.toHypothesis46 hG hodd) k) ≤
          (ClassFunction.supportedSubmodule (G := ↥M) (k := ℂ)
            (OddOrder.Peterfalvi.S04.supportInSubgroup
              (OddOrder.GroupTheory.typePA M hyp.typeP) M ∪ {1})).restrictScalars ℤ := by
        refine Submodule.span_le.mpr (fun s hs => ?_)
        obtain ⟨χ₂, hχ₂, -, rfl⟩ := hs
        simpa only [SetLike.mem_coe, Submodule.restrictScalars_mem,
            ClassFunction.mem_supportedSubmodule]
          using OddOrder.Peterfalvi.S06.columnSum_support_subset
            (hyp.toHypothesis46 hG hodd) hχ₂
      exact (ClassFunction.mem_supportedSubmodule).mp (hle hφspan)
    intro x hx
    rcases hsupp1 hx with hA | h1
    · exact hA
    · exact absurd (h1 ▸ hφsupp hx) hyp.one_notMem_A0
  · -- the `A₀`-witness: `μ_{k⁻¹} − μ_k`, `A(M)`-supported ⊆ `A₀`-supported
    obtain ⟨φ, ⟨hφspan, hφsupp⟩, hφne⟩ :=
      OddOrder.Peterfalvi.S06.certainType_nonzero (hyp.toHypothesis46 hG hodd) hk
    exact ⟨φ, ⟨hφspan, hφsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
      Set.subset_union_left)⟩, hφne⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), all-reducible corner ((9.9)(c))**: if every member of `𝒮(H₀C′)` is
reducible, the family is coherent on `A₀(M)`.  In this corner the family consists entirely of
μ-grid column sums (`reducible_mem_inducedKernelFamily_mem_certainTypeSet`, through `𝒮 ⊆ S =
inducedKernelFamily` by `sOf_subset_SOf`), i.e. it lies in the certain-type set `𝒯` at any
nonzero reference column — so the (4.9)(b) coherence `certainTypeSet_isCoherent_A0` restricts
along `isCoherent_of_subset`.  The nonzero supported witness is the conjugate difference
`ζ̄ − ζ` of any member (`hne`; conjugation preserves `𝒮(H₀C′)` by `sOf_closedUnderConjugate`,
the difference is `A₀`-supported by `inducedKernelFamily_conjDiff_support` and nonzero since odd
order admits no real characters).

This closes the base of the (9.11) `Ptype_core_coherence` induction in the corner where no
irreducible seed exists (`sOf_degreeSubfamily_isCoherent` is empty-cut there); the complementary
mixed corner proceeds by irreducible-cut base + `xAdjoinStepW_k` column-pair adjunction. -/
noncomputable def coherent_sOf_H0Cprime_of_allReducible [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {kref : Fin hyp.base.w2} (hkref : kref ≠ 0)
    (hallred : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      ¬ IsIrreducibleCharacter φ)
    (hne : (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0 := by
  haveI := hyp.base.finiteG
  classical
  -- the certain-type coherence at the reference column
  have hcohT := certainTypeSet_isCoherent_A0 hG hyp.base hG.odd
    (hyp.base.muColumnChar_ne_one hG hG.odd hkref)
  -- `𝒮(H₀C′) ⊆ 𝒯` (every member is reducible, hence a μ-grid column sum)
  have hsub : OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ⊆
      OddOrder.Peterfalvi.S06.certainTypeSet (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd kref) := by
    intro φ hφ
    have hφSK : φ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) := by
      have h := hyp.sOf_subset_SOf hyp.H0Cprime hφ
      rwa [hyp.SOf_eq] at h
    exact hyp.base.reducible_mem_inducedKernelFamily_mem_certainTypeSet hG hyp.type_alt
      (OddOrder.GroupTheory.typePNontrivialCore_of_isTypeIIIorIV hyp.type_alt hyp.base.typeP)
      (OddOrder.Peterfalvi.S11.exists_chiefFactorData hG _).choose
      hyp.params.w2_prime hkref hφSK (hallred φ hφ)
  -- the nonzero supported witness `ζ̄ − ζ` (`Prop`-confined)
  have hwit : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0 ∧ φ ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := hne
    have hζc : ζ.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime :=
      Hypothesis.sOf_closedUnderConjugate hyp.s11Setup hyp.H0Cprime hζ
    have hζSK : ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) := by
      have h := hyp.sOf_subset_SOf hyp.H0Cprime hζ
      rwa [hyp.SOf_eq] at h
    refine ⟨ζ.conj - ζ, ⟨?_, ?_⟩, ?_⟩
    · exact Submodule.sub_mem _
        (Submodule.subset_span hζc) (Submodule.subset_span hζ)
    · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
        hyp.base.mderivSharp_subset_A0 hζSK
    · intro h
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ hζSK (sub_eq_zero.mp h)
  exact isCoherent_of_subset hcohT hsub hwit

/-- **Peterfalvi (11.8): `S(HC)` is coherent** (sorry-free).  `S(HC) = SOf HC` is the subfamily of
the degree-`w₁` family `S(M'')` cut out by the *larger* kernel condition (`M'' ≤ HC`,
`secondDerived_le_HC`, so `S(HC) ⊆ S(M'')` by kernel-antitonicity), so it inherits the coherent
extension of `S(M'')` (`secondDerived_coherent`) verbatim — the isometry/`τ`-agreement/`ZIrr`-codomain
laws transport along `zSpan`/`zSupportedSpan` monotonicity.  The one genuinely new input is the
`nonzero` supported witness `ζ̄ − ζ` for a member `ζ ∈ S(HC)`: existence of `ζ` from
`inducedKernelFamily_nonempty_of_commutator_ne_top` at the proper trace `HC ⊊ M'` (`HC_lt_derived`),
its conjugate difference being `A₀`-supported (`mderivSharp_subset_A0`) and nonzero (odd order has no
real characters, `inducedKernelFamily_hasNoRealCharacters`).  This is the `S(HC)`-coherence input of
the (11.8.6) world-bridge capstone (glued with the `𝒮(H₀C)`-coherence along
`SOf_H0C_eq_SOf_HC_union_sOf`). -/
theorem coherent_SOf_HC [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.HC) hyp.base.A0) := by
  classical
  -- coherence of the larger degree-`w₁` family `S(M'')` (5.7)
  obtain ⟨hM''coh⟩ := hyp.secondDerived_coherent hG
  -- `S(HC) ⊆ S(M'')`  (`M'' ≤ HC`, kernel antitone)
  have hsub : hyp.SOf hyp.HC ⊆ hyp.SOf (secondDerivedInAmbient M) := by
    rw [hyp.SOf_eq, hyp.SOf_eq]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone
      (Subgroup.subgroupOf_mono M hyp.secondDerived_le_HC)
  -- a genuine member `ζ ∈ S(HC)` from the proper trace `HC ⊊ M'`
  haveI hHCKnorm : ((hyp.HC.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M)).Normal :=
    hyp.HC_subgroupOf_normal.subgroupOf _
  have hne : (hyp.HC.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤ := by
    rw [Ne, Subgroup.subgroupOf_eq_top]
    intro hle
    have hdle : derivedInG M ≤ M := Subgroup.map_subtype_le _
    have hMle : derivedInG M ≤ hyp.HC := fun x hx =>
      Subgroup.mem_subgroupOf.mp
        (hle (show (⟨x, hdle hx⟩ : ↥M) ∈ (derivedInG M).subgroupOf M from hx))
    exact (HC_lt_derived hyp).ne (le_antisymm hyp.HC_le_derived hMle)
  obtain ⟨ζ, hζ⟩ : (hyp.SOf hyp.HC).Nonempty := by
    rw [hyp.SOf_eq]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_nonempty_of_commutator_ne_top
      (hyp.base.commutator_quotient_ne_top hG hne)
  rw [hyp.SOf_eq] at hζ
  have hζc := OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hζ
  -- assemble the restricted coherence, reusing `S(M'')`'s coherent extension (`isCoherent_of_subset`)
  refine ⟨isCoherent_of_subset hM''coh hsub ⟨ζ.conj - ζ, ⟨?_, ?_⟩, ?_⟩⟩
  · -- `ζ̄ − ζ ∈ ℤ[S(HC)]`
    rw [hyp.SOf_eq]
    exact Submodule.sub_mem _ (Submodule.subset_span hζc) (Submodule.subset_span hζ)
  · -- `ζ̄ − ζ` is `A₀`-supported
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 hζ
  · -- `ζ̄ − ζ ≠ 0` (odd order ⇒ no real characters)
    intro h
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
      (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ hζ (sub_eq_zero.mp h)

/-- **(9.11) constant-degree base case on the kernel filtration `S(Y)`**: the degree-`d`
irreducible subfamily of `S(Y) = SOf Y` is coherent, given one degree-`d` irreducible member.
This is the `SOf`-world form of `S12.inducedFamily_degreeSubfamily_isCoherent` — the base case
of the Peterfalvi (9.11) `Ptype_core_coherence` induction at the family `S(H₀C')` (Coq: the
degree-`qa` uniform subfamily `S1` on which `uniform_degree_coherence` fires before the
conjugate-pair extension, `PFsection9.v:1538-1546`; in the Galois case the whole family).

Every `S(Y)`-member lies in the full induced family `S = S(⊥)` (`inducedKernelFamily_antitone`,
`inducedFamily_eq_inducedKernelFamily_bot`), so the ambient degree-`d` irreducible subfamily of
`S` is coherent by the R-datum-free (5.7)/Dade engine, and the `S(Y)`-cut restricts along
`isCoherent_of_subset`; the nonzero supported witness is the conjugate difference `ζ̄ − ζ` of the
given member (conjugation preserves membership, irreducibility and degree; the difference is
`A₀`-supported by `inducedKernelFamily_conjDiff_support` and nonzero since odd order admits no
real characters). -/
noncomputable def SOf_degreeSubfamily_isCoherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (Y : Subgroup G) (d : ℕ)
    (hex : ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ hyp.SOf Y ∧ IsIrreducibleCharacter ζ ∧
      ((ζ : ↥M → ℂ) 1 = (d : ℂ))) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      {φ : ClassFunction ↥M ℂ | φ ∈ hyp.SOf Y ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (d : ℂ))} hyp.base.A0 := by
  haveI := hyp.base.finiteG
  classical
  -- `S(Y) ⊆ S = S(⊥)` (the `⊥`-kernel condition is vacuous)
  have hsubfam : hyp.SOf Y ⊆ OddOrder.Peterfalvi.S12.inducedFamily M := by
    rw [hyp.SOf_eq, OddOrder.Peterfalvi.S12.inducedFamily_eq_inducedKernelFamily_bot]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
  -- the ambient degree-`d` irreducible subfamily of `S` is coherent (S12 engine); the
  -- `∃`-witness eliminations stay inside `Prop`-valued `have`s (the goal is `Type`-valued)
  have hex' : ∃ ζ : ClassFunction ↥M ℂ,
      ζ ∈ OddOrder.Peterfalvi.S12.inducedFamily M ∧ IsIrreducibleCharacter ζ ∧
      ((ζ : ↥M → ℂ) 1 = (d : ℂ)) := by
    obtain ⟨ζ, hζS, hζirr, hζ1⟩ := hex
    exact ⟨ζ, hsubfam hζS, hζirr, hζ1⟩
  have hcoh := hyp.base.inducedFamily_degreeSubfamily_isCoherent hG d hex'
  -- the `S(Y)`-cut is a subfamily of the ambient cut
  have hsub : {φ : ClassFunction ↥M ℂ | φ ∈ hyp.SOf Y ∧ IsIrreducibleCharacter φ ∧
      ((φ : ↥M → ℂ) 1 = (d : ℂ))} ⊆
      {φ : ClassFunction ↥M ℂ | φ ∈ OddOrder.Peterfalvi.S12.inducedFamily M ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))} :=
    fun φ hφ => ⟨hsubfam hφ.1, hφ.2.1, hφ.2.2⟩
  -- the nonzero supported witness `ζ̄ − ζ` for the cut (again `Prop`-confined)
  have hwit : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ hyp.SOf Y ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (d : ℂ))} hyp.base.A0 ∧ φ ≠ 0 := by
    obtain ⟨ζ, hζS, hζirr, hζ1⟩ := hex
    have hζSK : ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (Y.subgroupOf M) := by
      rwa [hyp.SOf_eq] at hζS
    have hζcS : ζ.conj ∈ hyp.SOf Y := by
      rw [hyp.SOf_eq]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hζSK
    have hζc1 : ((ζ.conj : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ) := by
      rw [ClassFunction.conj_apply, hζ1, star_natCast]
    refine ⟨ζ.conj - ζ, ⟨?_, ?_⟩, ?_⟩
    · exact Submodule.sub_mem _
        (Submodule.subset_span ⟨hζcS, hζirr.conj, hζc1⟩)
        (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
    · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
        hyp.base.mderivSharp_subset_A0 hζSK
    · intro h
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ hζSK (sub_eq_zero.mp h)
  exact isCoherent_of_subset hcoh hsub hwit

/-- **(9.11) constant-degree base case on the §9 family `𝒮(Y) = sOf`** — the form the (9.11)
`Ptype_core_coherence` induction actually consumes.  ⚠ The Coq §9 family is `S_ Y = seqIndD M' M
M`_\F Y` (third argument `H = M`_\F`, PFsection9.v:209): sources are nontrivial **on `H`** (the
`𝒳`-condition of `xiSet`), *not* merely nontrivial — so the (9.11) target is the `𝒳`-side family
`sOf`, not the kernel-filter family `SOf` (`seqIndD HU M HU` is the *§11* notation,
PFsection11.v:90; issue 1019 update⁵⁸ corrects update⁵⁰ on this point).

The degree-`d` irreducible subfamily of `𝒮(Y)` is coherent, given one degree-`d` irreducible
member: `𝒮(Y) ⊆ S(Y)` (`sOf_subset_SOf`) cuts the subfamily out of the `SOf`-version
(`SOf_degreeSubfamily_isCoherent`), and the nonzero supported witness is again the conjugate
difference `ζ̄ − ζ` (conjugation preserves `𝒮(Y)`-membership by `sOf_closedUnderConjugate`). -/
noncomputable def sOf_degreeSubfamily_isCoherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (Y : Subgroup G) (d : ℕ)
    (hex : ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y ∧
      IsIrreducibleCharacter ζ ∧ ((ζ : ↥M → ℂ) 1 = (d : ℂ))) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      {φ : ClassFunction ↥M ℂ | φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))} hyp.base.A0 := by
  haveI := hyp.base.finiteG
  classical
  -- transport the witness to the `SOf`-cut and fire the `SOf`-version
  have hexS : ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ hyp.SOf Y ∧ IsIrreducibleCharacter ζ ∧
      ((ζ : ↥M → ℂ) 1 = (d : ℂ)) := by
    obtain ⟨ζ, hζ, hi, hd⟩ := hex
    exact ⟨ζ, hyp.sOf_subset_SOf Y hζ, hi, hd⟩
  have hcoh := SOf_degreeSubfamily_isCoherent hG hyp Y d hexS
  -- the `𝒮(Y)`-cut is a subfamily of the `S(Y)`-cut
  have hsub : {φ : ClassFunction ↥M ℂ | φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))} ⊆
      {φ : ClassFunction ↥M ℂ | φ ∈ hyp.SOf Y ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (d : ℂ))} :=
    fun φ hφ => ⟨hyp.sOf_subset_SOf Y hφ.1, hφ.2.1, hφ.2.2⟩
  -- the nonzero supported witness `ζ̄ − ζ` inside the `𝒮(Y)`-cut (`Prop`-confined)
  have hwit : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y ∧
          IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))} hyp.base.A0 ∧ φ ≠ 0 := by
    obtain ⟨ζ, hζ, hζirr, hζ1⟩ := hex
    have hζc : ζ.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y :=
      Hypothesis.sOf_closedUnderConjugate hyp.s11Setup Y hζ
    have hζc1 : ((ζ.conj : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ) := by
      rw [ClassFunction.conj_apply, hζ1, star_natCast]
    have hζSK : ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (Y.subgroupOf M) := by
      have h := hyp.sOf_subset_SOf Y hζ
      rwa [hyp.SOf_eq] at h
    refine ⟨ζ.conj - ζ, ⟨?_, ?_⟩, ?_⟩
    · exact Submodule.sub_mem _
        (Submodule.subset_span ⟨hζc, hζirr.conj, hζc1⟩)
        (Submodule.subset_span ⟨hζ, hζirr, hζ1⟩)
    · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
        hyp.base.mderivSharp_subset_A0 hζSK
    · intro h
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ hζSK (sub_eq_zero.mp h)
  exact isCoherent_of_subset hcoh hsub hwit

/-- **(9.11) `hY`-route subset step**: the capstone's `𝒮(H₀C)`-coherence input (`hY`) follows from
the (9.11) coherence of the smaller-kernel family `𝒮(H₀C')` (`coherent_H0C_commutator`'s honest
target, the Coq `Ptype_core_coherence` induction) by `isCoherent_of_subset` along `𝒮(H₀C) ⊆
𝒮(H₀C')`, once a nonzero `A₀`-supported `𝒮(H₀C)` witness is supplied.  This wires the (9.11) result
to the world-bridge capstone `coherent_SOf_H0C_of_glued`'s `hY` parameter.

Two named obligations remain: `hcoh` = coherent(`𝒮(H₀C')`) (the (9.11) induction port over the
sorry-free S07/S08 engines — `coherent_subset_of_constant_degree` base + `coherentPairChain` /
`xAdjoinStepW` extension), and `hwit` = a nonzero `𝒮(H₀C)` witness (nonemptiness via
`S11.caseA_exists_irreducible_sOf_H0C` + a Clifford case split).  See issue 1019 update⁴⁵/⁴⁶. -/
noncomputable def coherent_sOf_H0C_of_coherent_sOf_H0Cprime [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0)
    (hwit : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 :=
  isCoherent_of_subset hcoh hyp.sOf_H0C_subset_sOf_H0Cprime hwit

/-- **(9.11) `hY`-route bridge, `SOf`-target form** (the Coq/authoritative intermediate).  The
capstone's `𝒮(H₀C)`-coherence input (`hY`) follows from the (9.11) coherence of the §10
`inducedKernelFamily` family `SOf(H₀C') = S_ H0C'` (Coq's `Ptype_core_coherence` target — the
`HU`-induced family that carries the S08 subcoherent/witness machinery) by `isCoherent_of_subset`
along `𝒮(H₀C) ⊆ SOf(H₀C')` (`sOf ⊆ SOf` via `sOf_subset_SOf`, then `SOf`-antitone since `H₀C' ≤
H₀C`), once a nonzero `A₀`-supported `𝒮(H₀C)` witness is supplied.  This is preferred over
`coherent_sOf_H0C_of_coherent_sOf_H0Cprime` (which threads the smaller `𝒮(H₀C')` intermediate):
the (9.11) induction naturally lands `SOf(H₀C')`, so this bridge is the direct connector. -/
noncomputable def coherent_sOf_H0C_of_coherent_SOf_H0Cprime [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (hyp.SOf hyp.H0Cprime) hyp.base.A0)
    (hwit : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 := by
  refine isCoherent_of_subset hcoh ?_ hwit
  have hSOf : hyp.SOf hyp.H0C ⊆ hyp.SOf hyp.H0Cprime := by
    rw [hyp.SOf_eq, hyp.SOf_eq]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone
      (Subgroup.subgroupOf_mono M hyp.H0Cprime_le_H0C)
  exact (hyp.sOf_subset_SOf hyp.H0C).trans hSOf

/-- **`S(HC)` is a subfamily of `SHCSet = S(M'')` = the degree-`w₁` irreducibles** (world-bridge
`S₁`-identification): every member of `S(HC)` kills `HC ⊇ M''`, so it kills `M''` and lies in
`S(M'')`, which is exactly the degree-`w₁` irreducible family `SHCSet` (`SOf_secondDerived_eq`).
Concretely `S(HC) ⊆ S(M'')` (kernel-antitone, `M'' ≤ HC`) and `S(M'') = SHCSet`.  This exhibits the
world-bridge `S₁ = S(HC)` as the uniform-degree-`q` part and lets the (11.8.6) capstone reuse the
`SHCSet` orthogonality/generation infrastructure on `S(HC)`. -/
theorem SOf_HC_subset_SHCSet [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.SOf hyp.HC ⊆ hyp.base.SHCSet := by
  have hsub : hyp.SOf hyp.HC ⊆ hyp.SOf (secondDerivedInAmbient M) := by
    rw [hyp.SOf_eq, hyp.SOf_eq]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone
      (Subgroup.subgroupOf_mono M hyp.secondDerived_le_HC)
  rwa [hyp.SOf_secondDerived_eq hG] at hsub

/-- **World-bridge source orthogonality (pairwise)**: a member of `S(HC)` is orthogonal to a member
of `𝒮(H₀C) = sOf`.  Both are `Ind_{HU}`-members of the pairwise-orthogonal §10 family
`inducedKernelFamily HU` (`sOf ⊆ SOf` via `sOf_subset_SOf`), and they are **distinct**: an
`S(HC)`-source `θ` kills `H` (`H ≤ HC ≤ Ker θ`), while an `𝒮(H₀C)`-source `χ'` lies in `𝒳`
(`H ⊄ Ker χ'`).  If `Ind θ = Ind χ'` then `θ, χ'` are `M`-conjugate (`induce_eq_induce_iff_conj`),
and `H ⊴ M` conjugation-invariance (`subsetCharacterKernel_conjBy_of_invariant`, via
`hSubgroupOfM_normal`) transports `H ≤ Ker θ` to `H ≤ Ker χ'` — contradicting `χ' ∈ 𝒳`.  This is the
`hsrc_ortho` input of the (11.8.6) world-bridge union-glue engine. -/
theorem SOf_HC_inner_sOf_H0C_eq_zero [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {x y : ClassFunction ↥M ℂ} (hx : x ∈ hyp.SOf hyp.HC)
    (hy : y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) :
    ClassFunction.inner x y = 0 := by
  classical
  have hHU : OddOrder.Peterfalvi.S11.huSub hyp.s11Setup = (derivedInG M).subgroupOf M :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf hyp.s11Setup
  -- both sit in the pairwise-orthogonal `inducedKernelFamily HU`
  have hxIKF : x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) (hyp.HC.subgroupOf M) := by
    have h := hx; rw [hyp.SOf_eq, ← hHU] at h; exact h
  have hyIKF : y ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) (hyp.H0C.subgroupOf M) := by
    have h := hyp.sOf_subset_SOf hyp.H0C hy; rw [hyp.SOf_eq, ← hHU] at h; exact h
  refine OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hxIKF hyIKF ?_
  -- distinctness `x ≠ y`
  intro hxy
  -- `H` realized inside `HU`
  have hhin : OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup
      = (hyp.H.subgroupOf M).subgroupOf (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) := by
    show (hyp.s11Setup.typeP.H.subgroupOf M).subgroupOf _
        = (hyp.base.typeP.H.subgroupOf M).subgroupOf _
    rw [hyp.setup_typeP_eq]
  -- `x`-source `θ` kills `hInHu` (`H ≤ HC`)
  obtain ⟨θ, hθne, hθker, hxeq⟩ := hxIKF
  have hHθ : (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup : Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ) := by
    rw [hhin]
    refine subset_trans (SetLike.coe_subset_coe.mpr (Subgroup.subgroupOf_mono _
      (Subgroup.subgroupOf_mono M (le_sup_left : hyp.H ≤ hyp.HC)))) hθker
  -- `y`-source `χ'` lies in `𝒳`: `¬ hInHu ⊆ Ker χ'`
  obtain ⟨χ', hχ'xiOf, hyeq⟩ := hy
  have hχ'xi : ¬ ((OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup : Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (χ' : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)) := hχ'xiOf.1
  -- `Ind θ = Ind χ'`, so the sources are `M`-conjugate
  rw [OddOrder.Peterfalvi.S11.induceHU_eq_induce] at hyeq
  have heqInd := hxeq.symm.trans (hxy.trans hyeq)
  obtain ⟨g, hg⟩ := (induce_eq_induce_iff_conj θ χ').mp heqInd
  -- `hInHu` is `M`-conjugation-invariant (`H ⊴ M`)
  have hAinv : ∀ a ∈ (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup : Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)),
      ClassFunction.conjByMulEquiv g a ∈ (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup : Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) := by
    intro a ha
    simp only [SetLike.mem_coe] at ha ⊢
    rw [OddOrder.Peterfalvi.S11.hInHu, Subgroup.mem_subgroupOf] at ha ⊢
    rw [ClassFunction.conjByMulEquiv_apply]
    exact (OddOrder.Peterfalvi.S11.hSubgroupOfM_normal hyp.s11Setup).conj_mem _ ha g
  -- transport `hInHu ⊆ Ker θ` to `hInHu ⊆ Ker (conjBy g θ) = Ker χ'`
  have hHχ' : (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup : Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.conjBy g (θ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)) :=
    OddOrder.Peterfalvi.S11.subsetCharacterKernel_conjBy_of_invariant g _ _ hAinv hHθ
  rw [← IrreducibleCharacter.coe_conjBy, hg] at hHχ'
  exact hχ'xi hHχ'

/-- **World-bridge source orthogonality (span level)** — the `hsrc_ortho` input of the (11.8.6)
union-glue engine `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`:
`ℤ[S(HC)] ⊥ ℤ[𝒮(H₀C)]`.  Bilinear extension of the pairwise `SOf_HC_inner_sOf_H0C_eq_zero`
(double `span_induction`, additivity + `ℤ`-linearity of the inner product). -/
theorem span_inner_SOf_HC_sOf_H0C_eq_zero [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {u v : ClassFunction ↥M ℂ}
    (hu : u ∈ Submodule.span ℤ (hyp.SOf hyp.HC))
    (hv : v ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C)) :
    ClassFunction.inner u v = 0 := by
  classical
  have hright : ∀ x ∈ hyp.SOf hyp.HC,
      ∀ w ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C),
      ClassFunction.inner x w = 0 := by
    intro x hx w hw
    induction hw using Submodule.span_induction with
    | mem y hy => exact SOf_HC_inner_sOf_H0C_eq_zero hyp hx hy
    | zero => rw [ClassFunction.inner_zero_right]
    | add y z _ _ ihy ihz => rw [ClassFunction.inner_add_right, ihy, ihz, add_zero]
    | smul a y _ ih =>
        rw [← Int.cast_smul_eq_zsmul ℂ a y,
          OddOrder.RepresentationTheory.inner_smul_right, ih, mul_zero]
  induction hu using Submodule.span_induction with
  | mem x hx => exact hright x hx v hv
  | zero => rw [ClassFunction.inner_zero_left]
  | add x z _ _ ihx ihz => rw [ClassFunction.inner_add_left, ihx, ihz, add_zero]
  | smul a x _ ih =>
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, ih, mul_zero]

/-- **Peterfalvi (11.8.6) world-bridge capstone (glued form)**: `S(H₀C)` is coherent, assembled from
the two side-coherences along the world-bridge decomposition `S(H₀C) = S(HC) ∪ 𝒮(H₀C)`
(`SOf_H0C_eq_SOf_HC_union_sOf`).

This is the world-bridge analogue of `S12.Hypothesis.coherent_Sset_of_glued`.  The `S07` union-glue
engine `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` is fed:
- `coh` — the degree-`q` side `S(HC)`-coherence (**landed**, `coherent_SOf_HC`);
- `hY` — the `𝒮(H₀C)`-coherence (§14-gated, (9.11) `Ptype_core_coherence` route);
- `hsrc_ortho` — the source orthogonality `ℤ[S(HC)] ⊥ ℤ[𝒮(H₀C)]` (**landed, discharged here**,
  `span_inner_SOf_HC_sOf_H0C_eq_zero`);
- the `τ₃` glue map `ν` with its `hagreeX`/`hagreeY`/`hmixed`/`hDτ`/`hgen` inputs (§14/§9-gated —
  the (6.7) image-orthogonality, (5.8) column identity, and (6.8.1) generation).

The genuine world-bridge wiring (set-decomposition rewrite + engine instantiation + the
source-orthogonality discharge) is proven here; only the §14/§9 glue inputs remain as parameters,
to be supplied once the `𝒮(H₀C)`-side character theory lands.  Downstream, `coherent(S(H₀C))` feeds
`coherent_S_of_coherent_SH0C` (**already sorry-free**) to give `coherent(S)`, contradicting (11.3). -/
noncomputable def coherent_SOf_H0C_of_glued [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.HC) hyp.base.A0)
    (hY : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0)
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G)
    (hagreeX : ∀ x ∈ hyp.SOf hyp.HC, ν x = coh.extension x)
    (hagreeY : ∀ y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C, ν y = hY.extension y)
    (hmixed : ∀ x ∈ hyp.SOf hyp.HC, ∀ y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction ↥M ℂ)) (hDτ : ∀ d ∈ D, ν d = hyp.base.tau d)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan
        (hyp.SOf hyp.HC ∪ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.SOf hyp.HC) hyp.base.A0 ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan
          (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 ∪ D)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0 := by
  haveI := hyp.base.finiteG
  rw [hyp.SOf_H0C_eq_SOf_HC_union_sOf]
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    coh hY ν hagreeX hagreeY
    (fun _ hu _ hv => span_inner_SOf_HC_sOf_H0C_eq_zero hyp hu hv) hmixed D hDτ hgen

/-- **Peterfalvi (11.5), reverse inclusion `HC ⊆ M''`** (named obligation): the coherence content
of (11.5).  Since `M'/M''` is abelian, `S(M'')` is coherent by (5.7); the quotient bound (11.4)
together with (11.1)/(9.6) then forces `M'' = HC`.  Char-gated — it bottoms out in Theorem (10.8)
via (11.3)/(11.4) — so it is left as a clean named subgroup-inclusion obligation. -/
theorem HC_le_secondDerived [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.HC ≤ secondDerivedInAmbient M := by
  classical
  rw [← Subgroup.relIndex_eq_one]
  -- `HC < M'` (else `U ≤ HC` forces `U ≤ C`, contradicting `C ⊊ U`)
  have hHCltM' : hyp.HC < derivedInG M := HC_lt_derived hyp
  -- `(11.4)` at `H₁ := M''` with `(5.7)`
  have hM''lt : secondDerivedInAmbient M < derivedInG M :=
    lt_of_le_of_lt hyp.secondDerived_le_HC hHCltM'
  have h114 := coherent_quotient_bound _hG hyp le_normalizer_secondDerived hM''lt
    (hyp.secondDerived_coherent _hG)
  -- tower `|M':M''| = X·|U:C|`
  set X := (secondDerivedInAmbient M).relIndex hyp.HC with hX
  set v := hyp.C.relIndex hyp.U with hv
  have htower : (secondDerivedInAmbient M).relIndex (derivedInG M) = X * v := by
    rw [hX, hv, ← hyp.HC_relIndex_derived]
    exact (Subgroup.relIndex_mul_relIndex (secondDerivedInAmbient M) hyp.HC (derivedInG M)
      hyp.secondDerived_le_HC hyp.HC_le_derived).symm
  rw [htower] at h114
  -- `v ≥ 2` from `C ⊊ U`
  have hvpos : v ≠ 0 := by
    intro h0
    have h2 : Nat.card ↥hyp.C * v = Nat.card ↥hyp.U := by
      have := Subgroup.card_mul_index (hyp.C.subgroupOf hyp.U)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show hyp.C ≤ hyp.U from hyp.C_le_U)).toEquiv] at this
    rw [h0, Nat.mul_zero] at h2
    exact (Nat.card_pos (α := ↥hyp.U)).ne' h2.symm
  have hvne1 : v ≠ 1 := by
    intro h1
    rw [hv, Subgroup.relIndex_eq_one] at h1
    exact hyp.C_lt_U.not_ge h1
  have hv2 : 2 ≤ v := by omega
  -- `X ≤ 2q`
  have hX2q : X ≤ 2 * hyp.q := by
    by_contra hgt
    push Not at hgt
    have hge : 2 * hyp.q + 1 ≤ X := hgt
    have h1 : (2 * hyp.q + 1) * v ≤ X * v := Nat.mul_le_mul_right v hge
    have h2 : 2 * hyp.q * v + v ≤ 2 * hyp.q * v + 1 := by
      calc 2 * hyp.q * v + v = (2 * hyp.q + 1) * v := by ring
        _ ≤ X * v := h1
        _ ≤ 2 * hyp.q * v + 1 := h114
    omega
  -- `q ∣ X − 1`, `X` and `q` odd ⟹ `X = 1`
  have hdvd : hyp.q ∣ X - 1 := hyp.q_dvd_secondDerived_relIndex_HC_sub_one _hG
  have hXodd : Odd X := by
    refine _hG.odd.of_dvd_nat ?_
    calc X ∣ Nat.card ↥hyp.HC := Subgroup.relIndex_dvd_card _ _
      _ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card hyp.HC
  have hqodd : Odd hyp.q := by
    refine _hG.odd.of_dvd_nat ?_
    calc hyp.q = Nat.card ↥hyp.base.typeP.W1 := rfl
      _ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card hyp.base.typeP.W1
  have hqpos : 0 < hyp.q := hqodd.pos
  obtain ⟨k, hk⟩ := hdvd
  have hXpos : 0 < X := hXodd.pos
  rw [Nat.odd_iff] at hXodd hqodd
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · omega
    · rw [Nat.mul_one] at hk
      omega
  · exfalso
    have h3 : hyp.q * 2 ≤ hyp.q * k := Nat.mul_le_mul_left hyp.q hk2
    have h4 : 2 * hyp.q ≤ X - 1 := by
      rw [hk]
      omega
    omega

/-- **Peterfalvi (11.5)**: the second derived subgroup is `H C`, i.e. `M'' = HC`.

`M'' ⊆ HC` is unconditional ((8.5.a), `secondDerived_le_HC`); the reverse `HC ⊆ M''` is the
coherence content carried by `HC_le_secondDerived`.  The theorem composes the two with no `sorry`
of its own. -/
theorem secondDerived_eq_HC [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    secondDerivedInAmbient M = hyp.HC :=
  le_antisymm hyp.secondDerived_le_HC (HC_le_secondDerived _hG hyp)

/-- **Peterfalvi (11.6), `C = U'`**: `U' ≤ C` is (8.5.b) (`derivedU_le_C`); conversely
`C ≤ HC = M'' ≤ H ⊔ U'` ((11.5) + `secondDerived_le_H_sup_derivedU`), and an
`H ⊔ U'`-element of `U` splits as `h·u'` with `h ∈ H ⊓ U = ⊥`, so `C ≤ U'`. -/
theorem C_eq_derivedU [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.C = derivedInG hyp.base.typeP.U := by
  refine le_antisymm ?_ hyp.derivedU_le_C
  intro c hc
  have hcM'' : c ∈ secondDerivedInAmbient M := by
    rw [secondDerived_eq_HC hG hyp]
    exact Subgroup.mem_sup_right hc
  have hcHU' : c ∈ hyp.base.typeP.H ⊔ derivedInG hyp.base.typeP.U :=
    hyp.secondDerived_le_H_sup_derivedU hcM''
  -- split `c = h·u'` and cancel the `H`-part inside `U`
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hU'le : derivedInG hyp.base.typeP.U ≤ M :=
    ((Subgroup.map_subtype_le _).trans hyp.base.typeP.U_le).trans (Subgroup.map_subtype_le _)
  obtain ⟨h, hh, u', hu', hceq⟩ :=
    exists_mul_of_mem_sup_of_normalized hHle hU'le hyp.H_normalized_by_M hcHU'
  have hhU : h ∈ hyp.base.typeP.U := by
    have h1 : h = c * u'⁻¹ := by rw [hceq]; group
    rw [h1]
    exact Subgroup.mul_mem _ (hyp.C_le_U hc)
      (Subgroup.inv_mem _ ((Subgroup.map_subtype_le _) hu'))
  have hh1 : h = 1 := by
    have := hyp.H_inf_U_eq_bot.le ⟨hh, hhU⟩
    rwa [Subgroup.mem_bot] at this
  rw [hceq, hh1, one_mul]
  exact hu'

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(9.11) mixed-corner column-pair adjunction, §12 instantiation** (issue 1019 update⁶⁶): a
coherent equal-degree irreducible family `s` (with anchor `χ₁ ∈ s`) absorbs one reducible
certain-type column pair `{μ, μ̄}` (`μ = columnSum χ₂`, `μ̄ = μ_{χ₂⁻¹}` via `columnSum_conj_eq`),
staying coherent on `A₀(M)`.  This is `xAdjoinStepW_k` instantiated at the §12 Dade data
(`τ = hyp.tau`, `A = A₀(M)`, both definitional) with `a = 1` (uniform degree: `μ(1) = χ₁(1)`).

The χ-side inner products, supports and the member-family data (`ι = ClassFunction`, `χmem = id`,
`deg ≡ 1`, `mc ≡ 1`) are discharged here from the §6 column API (`columnFamily_mu_sum_inner`,
`column_inv_ne_self`, `columnDiff_support_subset`) and the induced-family support machinery
(`inducedKernelFamily_scaledDiff_support`).  The genuinely deep inputs stay as parameters:
* `Dmem`/`Da`/`hortho_mem` — the (5.4)/(5.2.e) decomposition data (per-member ψ=0 via
  `memberExtensionDecomposition`, break via `certainTypeDecompositionDa`, cross-orthogonality =
  the §12 analogue of `certainTypeR_imageSet_orthogonal_dadeOfDiff`, a separate piece);
* `hDeg` — the (5.6.c) counting `2 < |s|` (§9 size lower bound);
* `hgen` — the supported-span generation (uniform-degree collapse, a separate piece);
* `hμ_S1`/`hμbar_S1` — `μ ⊥ s` (at the irreducible-cut specialization:
  `muGrid_inner_irr_member_eq_zero`). -/
noncomputable def adjoin_muColumnPair_of_irrFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    (S₁ : Set (ClassFunction ↥M ℂ))
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A0)
    (s : Finset (ClassFunction ↥M ℂ))
    (hsS₁ : (↑s : Set (ClassFunction ↥M ℂ)) ⊆ S₁)
    (hirr : ∀ x ∈ s, IsIrreducibleCharacter x)
    {χ₁ : ClassFunction ↥M ℂ} (hχ₁s : χ₁ ∈ s)
    {χ₂ : ((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2)) →* ℂˣ}
    (hχ₂ : χ₂ ≠ 1)
    (hdegmem : ∀ x ∈ s, x 1 = χ₁ 1)
    (hdegS₁diff : ∀ x ∈ S₁, ((x - χ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.A0)
    (hμ_S1 : ∀ x ∈ S₁, ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂) x = 0)
    (hμbar_S1 : ∀ x ∈ S₁, ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂).conj x = 0)
    (Dmem : ∀ x ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)) x 0)
    (htau1Dmem : ∀ x (hx : x ∈ s), (Dmem x hx).tau1 x = hS₁.extension x)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj))
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂) (1 • χ₁))
    (hDatau1 : Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj))
    (hortho_mem : ∀ x (hx : x ∈ s), (Dmem x hx).imageFamily.Orthogonal Da.imageFamily)
    (hdiffasuppχ : ((OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂
      - χ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.A0)
    (hμZ : OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂ ∈ ZIrr ↥M)
    (hDeg : (2 : ℝ) < s.card)
    (hdeganchor : OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂ 1
      = χ₁ 1) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪
        {OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂,
         (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂).conj})
      hyp.A0 := by
  haveI := hyp.finiteG
  classical
  -- degree symmetry of the conjugate column pair
  have hdegsym := OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
    (hyp.toHypothesis46 hG hG.odd) χ₂
  have hconjcol : (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂).conj
      = OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂⁻¹ :=
    OddOrder.Peterfalvi.S06.columnSum_conj_eq (hyp.toHypothesis46 hG hG.odd) χ₂
  -- χ-side inner products from the §6 column Gram (`⟨μ_j, μ_l⟩ = w₁·δ`)
  have hχχne : ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂)
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂) ≠ 0 := by
    rw [OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl]
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hχbarχbarne : ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂).conj
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂).conj ≠ 0 := by
    rw [hconjcol, OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl]
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hχχbar : ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂)
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂).conj = 0 := by
    rw [hconjcol, OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner]
    exact if_neg (OddOrder.Peterfalvi.S06.column_inv_ne_self
      (hyp.toHypothesis46 hG hG.odd) hχ₂).symm
  have hχbarχ : ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂).conj
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂) = 0 := by
    rw [hconjcol, OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner]
    exact if_neg (OddOrder.Peterfalvi.S06.column_inv_ne_self
      (hyp.toHypothesis46 hG hG.odd) hχ₂)
  -- χ-side support: the conjugate column difference is `A(M)`-supported, hence `A₀`-supported
  have hdiffsuppχ : (((OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂).conj
      - OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂
      : ClassFunction ↥M ℂ)).support ⊆ hyp.A0 := by
    rw [hconjcol]
    exact (OddOrder.Peterfalvi.S06.columnDiff_support_subset (hyp.toHypothesis46 hG hG.odd)
      (inv_ne_one.mpr hχ₂) hχ₂ hdegsym).trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  -- member-side: anchor differences are `A₀`-supported (from the `S₁`-level hypothesis)
  have hmemdegdiffsupp : ∀ x ∈ s,
      ((x - (1 : ℕ) • χ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.A0 := fun x hx => by
    rw [one_smul]
    exact hdegS₁diff x (hsS₁ (Finset.mem_coe.mpr hx))
  -- member-side Gram: distinct irreducibles are orthonormal (`mc ≡ 1`)
  have hmemortho : ∀ x ∈ s, ∀ y ∈ s, ClassFunction.inner x y
      = if x = y then ((1 : ℝ) : ℂ) else 0 := fun x hx y hy => by
    have h := irreducibleCharacter_inner_eq_ite ⟨x, hirr x hx⟩ ⟨y, hirr y hy⟩
    simpa [IrreducibleCharacter.ext_iff] using h
  -- `μ − χ₁` is an `A₀`-supported virtual character, so its Dade image is integral
  have hμχ₁Z : (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂
      - (1 : ℕ) • χ₁ : ClassFunction ↥M ℂ) ∈ ZIrr ↥M := by
    rw [one_smul]
    exact Submodule.sub_mem _ hμZ (hirr χ₁ hχ₁s).mem_ZIrr
  have hdiffasupp' : ((OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂
      - (1 : ℕ) • χ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.A0 := by
    rw [one_smul]; exact hdiffasuppχ
  have htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)
      (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂
        - (1 : ℕ) • χ₁) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp.dadeData.dade
      hyp.hconj hdiffasupp' hμχ₁Z
  -- the (5.6.c) weighted degree bound: `2·1 < ∑ 1²/1 = |s|`
  have hDeg' : 2 * ((1 : ℕ) : ℝ) < ∑ _x ∈ s, ((1 : ℕ) : ℝ) ^ 2 / (1 : ℝ) := by
    simpa using hDeg
  -- span generation: `ℤ[S₁] ⊆ ℤ[ℤ[S₁, A₀] ∪ {χ₁}]` (anchor differences are supported)
  have hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M) S₁ hyp.A0 ∪ {χ₁}) := by
    rw [Submodule.span_le]
    intro x hx
    have hdiff : x - χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M) S₁ hyp.A0 :=
      ⟨Submodule.sub_mem _ (Submodule.subset_span hx)
        (Submodule.subset_span (hsS₁ (Finset.mem_coe.mpr hχ₁s))), hdegS₁diff x hx⟩
    have hx' : x = (x - χ₁) + χ₁ := by abel
    rw [SetLike.mem_coe, hx']
    exact Submodule.add_mem _
      (Submodule.subset_span (Set.mem_union_left _ hdiff))
      (Submodule.subset_span (Set.mem_union_right _ rfl))
  -- span generation for the adjoined pair (`hgen`): the generic anchor-generation producer,
  -- fed the degree matching `μ(1) = 1·χ₁(1)` and `μ̄(1) = μ(1)`
  have hbar1 : (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂).conj 1
      = OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂ 1 := by
    rw [hconjcol, OddOrder.Peterfalvi.S06.columnSum_apply_one,
      OddOrder.Peterfalvi.S06.columnSum_apply_one]
    exact hdegsym
  have hchi1_ne : χ₁ 1 ≠ 0 := by
    obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ⟨χ₁, hirr χ₁ hχ₁s⟩
    rw [show χ₁ 1 = ((⟨χ₁, hirr χ₁ hχ₁s⟩ : IrreducibleCharacter ↥M) : ClassFunction ↥M ℂ) 1
      from rfl, hd1]
    exact_mod_cast hd.ne'
  have hgen := OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
    (χ := OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂)
    (chibar := (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂).conj)
    (a := 1) hSgen
    (by rw [Nat.cast_one, one_mul]; exact hdeganchor) hbar1 hchi1_ne hyp.one_notMem_A0
  -- fire the reducible-break weighted adjoin engine
  exact OddOrder.Peterfalvi.S08.xAdjoinStepW_k hyp.dadeData.dade hyp.hconj hS₁
    (OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hG.odd) χ₂) hdiffsuppχ
    hχχne hχbarχbarne hχχbar hχbarχ hμ_S1 hμbar_S1 s id (fun _ => 1) χ₁ hχ₁s
    hmemdegdiffsupp (fun x hx => hsS₁ (Finset.mem_coe.mpr hx)) (fun _ => (1 : ℝ))
    (fun _ _ => one_pos) hmemortho rfl Dmem Da hDatau1 hortho_mem htau1Dmem
    hdiffasupp' htau1_memaχ rfl hDeg' hSgen hgen

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (10.10), case (a) of Definition (8.7)** ("If case (a) of Definition (8.7)
holds, then `S` is coherent by Theorem (6.8)"): for a type-V maximal `M` whose kernel sharp
set `H^# = (M')^#` is a TI-subset, the (10.1) family `S = hyp.Sset` is coherent for the §10
Dade isometry `hyp.tau` on the support `A₀(M)`.

Assembly: the sorry-free (6.8) capstone `sibleySetup_is_coherent` applied to the case-(a)
Sibley datum `typeVSibleyDadeHypothesis` gives coherence for the Sibley–Dade map on the
`(M')^#`-support (its `S`-field is definitionally `inducedFamily M = hyp.Sset`);
`IsCoherent.congrMap` re-targets it to `hyp.tau` along the (2.11)+(2.5) agreement
`typeVSibleyDadeHypothesis_tau_agree`; `isCoherent_of_supportedSpan_le` enlarges the support
to `A₀(M)` — members `Ind_{M'}^M θ` vanish off `M'` and `1 ∉ A₀`, so an `A₀`-supported
`ℤ[S]`-combination is already `(M')^#`-supported — with the `A₀`-witness `ζ̄ − ζ` (a member
exists by (10.2), and odd order admits no real characters). -/
noncomputable def typeV_caseA_coherence [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (dV : TypeVData M)
    (hTI : IsTISubset (sharpSubgroup hyp.typeP.H)
      (Subgroup.normalizer (hyp.typeP.H : Set G))) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0 := by
  classical
  -- the (6.8) coherence on the `(M')^#`-support, for the Sibley–Dade map
  have c0 := OddOrder.Peterfalvi.S08.sibleySetup_is_coherent
    (OddOrder.Peterfalvi.S12.typeVSibleyDadeHypothesis hG hyp dV hTI)
  -- re-target to `hyp.tau` along the (2.11)+(2.5) agreement (the family and support are
  -- definitionally `hyp.Sset` and the `(M')^#`-support)
  have c1 : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S08.sharpImage ((derivedInG M).subgroupOf M)) M) :=
    c0.congrMap (fun φ hφ =>
      OddOrder.Peterfalvi.S12.typeVSibleyDadeHypothesis_tau_agree hG hyp dV hTI hφ.2)
  refine isCoherent_of_supportedSpan_le c1 ?_ ?_
  · -- `ℤ[S, A₀] ⊆ ℤ[S, (M')^#]`: members vanish off `M'`, and `1 ∉ A₀`
    haveI hHnorm : ((derivedInG M).subgroupOf M).Normal := by
      rw [show (derivedInG M).subgroupOf M = commutator ↥M by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
      infer_instance
    rintro φ ⟨hφspan, hφsupp⟩
    refine ⟨hφspan, ?_⟩
    have hsuppH : φ.support ⊆ {x : ↥M | x ∈ (derivedInG M).subgroupOf M} := by
      have hle' : OddOrder.Peterfalvi.S07.zSpan (L := ↥M) hyp.Sset ≤
          (ClassFunction.supportedSubmodule (G := ↥M) (k := ℂ)
            {x : ↥M | x ∈ (derivedInG M).subgroupOf M}).restrictScalars ℤ := by
        refine Submodule.span_le.mpr (fun s hs => ?_)
        obtain ⟨θ, -, rfl⟩ := hs
        simp only [SetLike.mem_coe, Submodule.restrictScalars_mem,
          ClassFunction.mem_supportedSubmodule]
        intro x hx
        rw [ClassFunction.mem_support] at hx
        by_contra hxH
        exact hx (ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ _ hxH)
      exact (ClassFunction.mem_supportedSubmodule).mp (hle' hφspan)
    intro x hx
    have hxA0 : x ∈ hyp.A0 := hφsupp hx
    have hx1 : x ≠ 1 := fun h => hyp.one_notMem_A0 (h ▸ hxA0)
    exact ⟨Subgroup.mem_map.mpr ⟨x, hsuppH hx, rfl⟩,
      fun hc => hx1 (Subtype.ext (Set.mem_singleton_iff.mp hc))⟩
  · -- the `A₀`-witness `ζ̄ − ζ` for a (10.2) member `ζ`
    have hHall := OddOrder.Peterfalvi.S12.typePData_W1_hall_coprime hG hyp.maximal
      (hyp.bgTypeP hG) hyp.typeP
    obtain ⟨ζ, hζmem, -, -⟩ :=
      OddOrder.Peterfalvi.S12.exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hG.odd hHall
    have hζSK : ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) ⊥ := by
      obtain ⟨θ, hθne, hζeq⟩ := hζmem
      refine ⟨θ, hθne, ?_, hζeq⟩
      intro y hy
      have hy1 : y = 1 :=
        Subtype.ext (Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp hy))
      rw [hy1]
      exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
    have hζc : ζ.conj ∈ hyp.Sset :=
      OddOrder.Peterfalvi.S12.inducedFamily_closedUnderConjugate M hζmem
    refine ⟨ζ.conj - ζ, ⟨?_, ?_⟩, ?_⟩
    · exact Submodule.sub_mem _ (Submodule.subset_span hζc) (Submodule.subset_span hζmem)
    · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
        hyp.mderivSharp_subset_A0 hζSK
    · intro h
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hyp.card_odd_of_isMinimalSimpleOdd hG) _ hζSK (sub_eq_zero.mp h)

end OddOrder.Peterfalvi.S13
