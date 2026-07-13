/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7B2_NormalJ_PComplement

/-!
# Isaacs FGT Ch.7 — §7C Thompson normal p-complement (pp. 215–219)

This leaf contains the quotient identifications and the minimum-counterexample
assembly for Thompson's normal `p`-complement theorem (Isaacs Theorem 7.1).
-/

namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section QuotientCenter

/-- Centers commute with a homomorphism that is injective on the subgroup in question.

This restricted-injectivity form applies both to embeddings into an ambient group and
to quotient maps whose kernel is disjoint from a `p`-subgroup. -/
theorem center_map_subtype_map_of_restrict_injective
    {H : Type*} [Group H] (f : G →* H) {P : Subgroup G}
    (hf : Function.Injective (f.comp P.subtype)) :
    (Subgroup.center ↥(P.map f)).map (P.map f).subtype =
      ((Subgroup.center ↥P).map P.subtype).map f := by
  ext x
  constructor
  · intro hx
    have hx_center := Subgroup.mem_center_map_subtype_iff.mp hx
    obtain ⟨z, hzP, hzx⟩ := hx_center.1
    refine ⟨z, Subgroup.mem_center_map_subtype_iff.mpr ⟨hzP, ?_⟩, hzx⟩
    intro w hw
    have hcomm_f := hx_center.2 (f w) ⟨w, hw, rfl⟩
    rw [← hzx] at hcomm_f
    have hsub :
        (f.comp P.subtype) (⟨w, hw⟩ * ⟨z, hzP⟩) =
          (f.comp P.subtype) (⟨z, hzP⟩ * ⟨w, hw⟩) := by
      change f (w * z) = f (z * w)
      simpa only [map_mul] using hcomm_f
    exact congrArg Subtype.val (hf hsub)
  · rintro ⟨z, hz, rfl⟩
    have hz_center := Subgroup.mem_center_map_subtype_iff.mp hz
    apply Subgroup.mem_center_map_subtype_iff.mpr
    refine ⟨⟨z, hz_center.1, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simpa only [map_mul] using congrArg f (hz_center.2 w hw)

/-- **Isaacs Theorem 7.1, Step 3 (center identification).**

If `N ⊴ G` is a normal `p′`-subgroup and `P` is a `p`-subgroup, then the ambient
image of `Z(P)` is carried to the ambient image of `Z(P̄)` under `G → G/N`.
The quotient map is injective on `P` because `P ∩ N = 1`; this is the center
analogue of `thompsonJ_map_of_coprime_kernel`. -/
theorem center_map_subtype_map_of_coprime_kernel
    [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P) :
    (Subgroup.center ↥(P.map (QuotientGroup.mk' N))).map
        (P.map (QuotientGroup.mk' N)).subtype =
      ((Subgroup.center ↥P).map P.subtype).map (QuotientGroup.mk' N) := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let qP : ↥P →* G ⧸ N := q.comp P.subtype
  obtain ⟨k, hP_card⟩ : ∃ k, Nat.card ↥P = p ^ k := IsPGroup.iff_card.mp hP_pgroup
  have hp_prime : p.Prime := Fact.out
  have h_coprime_PN : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by
    rw [hP_card]
    exact Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_coprime)
  have hP_inf_N : P ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard h_coprime_PN).eq_bot
  have hqP_inj : Function.Injective qP := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx_N : (x : G) ∈ N := by
      have hx' : (x : G) ∈ (QuotientGroup.mk' N).ker := hx
      rwa [QuotientGroup.ker_mk'] at hx'
    have hx_inf : (x : G) ∈ P ⊓ N := ⟨x.property, hx_N⟩
    rw [hP_inf_N, Subgroup.mem_bot] at hx_inf
    exact Subtype.ext hx_inf
  apply center_map_subtype_map_of_restrict_injective
  simpa [qP, q] using hqP_inj

end QuotientCenter

section LocalHypothesisTransport

/-- **Isaacs Theorem 7.1 hypotheses at a `p`-subgroup.**

Both the centralizer of the ambient copy of `Z(P)` and the normalizer of `J(P)`
have normal `p`-complements.  The theorem applies this condition to Sylow
subgroups; accepting an arbitrary subgroup makes its transport API reusable in
the minimum-counterexample argument. -/
def HasThompsonLocalPComplements (p : ℕ) (P : Subgroup G) : Prop :=
  OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.centralizer
        (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G)) ∧
    OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer ((Subgroup.thompsonJ P p : Subgroup G) : Set G))

/-- The two local normal-complement hypotheses are invariant under a group
isomorphism. -/
theorem HasThompsonLocalPComplements.map_mulEquiv
    {H : Type*} [Group H] [Finite G] [Finite H]
    {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : HasThompsonLocalPComplements p P) (e : G ≃* H) :
    HasThompsonLocalPComplements p (P.map e.toMonoidHom) := by
  have heP : Function.Injective (e.toMonoidHom.comp P.subtype) :=
    e.injective.comp P.subtype_injective
  have hCenter :
      (Subgroup.center ↥(P.map e.toMonoidHom)).map
          (P.map e.toMonoidHom).subtype =
        ((Subgroup.center ↥P).map P.subtype).map e.toMonoidHom :=
    center_map_subtype_map_of_restrict_injective e.toMonoidHom heP
  constructor
  · have hImage :=
      hasNormalPComplement_subgroup_map e.toMonoidHom
        (Subgroup.centralizer
          (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G)) hP.1
    have hLocalizer :
        (Subgroup.centralizer
            (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G)).map
              e.toMonoidHom =
          Subgroup.centralizer
            (((Subgroup.center ↥(P.map e.toMonoidHom)).map
              (P.map e.toMonoidHom).subtype : Subgroup H) : Set H) := by
      rw [hCenter]
      simpa only [Subgroup.coe_map] using
        (Subgroup.map_centralizer_eq_of_bijective
          (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G)
          e.toMonoidHom e.bijective)
    exact hasNormalPComplement_of_mulEquiv
      (MulEquiv.subgroupCongr hLocalizer) hImage
  · have hImage :=
      hasNormalPComplement_subgroup_map e.toMonoidHom
        (Subgroup.normalizer ((Subgroup.thompsonJ P p : Subgroup G) : Set G)) hP.2
    have hJ :
        Subgroup.thompsonJ (P.map e.toMonoidHom) p =
          (Subgroup.thompsonJ P p).map e.toMonoidHom :=
      Subgroup.thompsonJ_map_of_injective e.injective P p
    have hLocalizer :
        (Subgroup.normalizer
            ((Subgroup.thompsonJ P p : Subgroup G) : Set G)).map e.toMonoidHom =
          Subgroup.normalizer
            ((Subgroup.thompsonJ (P.map e.toMonoidHom) p : Subgroup H) : Set H) := by
      rw [hJ]
      exact Subgroup.map_normalizer_eq_of_bijective _ e.bijective
    exact hasNormalPComplement_of_mulEquiv
      (MulEquiv.subgroupCongr hLocalizer) hImage

/-- The intrinsic form of the two local hypotheses in Isaacs Theorem 7.1:
they hold at every Sylow `p`-subgroup. -/
def HasThompsonPComplementHypothesis (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ P : Sylow p G, HasThompsonLocalPComplements p (P : Subgroup G)

/-- Local normal-complement hypotheses at one Sylow subgroup propagate to all
Sylow subgroups by conjugacy. -/
theorem HasThompsonLocalPComplements.of_sylow
    [Finite G] {p : ℕ} [Fact p.Prime] (P Q : Sylow p G)
    (hP : HasThompsonLocalPComplements p (P : Subgroup G)) :
    HasThompsonLocalPComplements p (Q : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hmap :
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom = (Q : Subgroup G) := by
    change (MulAut.conj g • (P : Subgroup G)) = (Q : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hg]
  have h := hP.map_mulEquiv (MulAut.conj g)
  rw [hmap] at h
  exact h

/-- The textbook hypotheses at a chosen Sylow subgroup are equivalent to their
intrinsic all-Sylow form. -/
theorem hasThompsonPComplementHypothesis_iff
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    HasThompsonPComplementHypothesis p G ↔
      HasThompsonLocalPComplements p (P : Subgroup G) := by
  constructor
  · exact fun h => h P
  · intro h Q
    exact h.of_sylow P Q

end LocalHypothesisTransport

section MinimalCounterexampleStepOne

/-- A nontrivial `p`-subgroup whose normalizer has no normal `p`-complement. -/
def IsBadNormalizerPSubgroup (p : ℕ) (U : Subgroup G) : Prop :=
  U ≠ ⊥ ∧ IsPGroup p U ∧
    ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer (U : Set G))

/-- The order of a Sylow `p`-subgroup of `N_G(U)`, expressed intrinsically as
the `p`-part of `|N_G(U)|`. -/
noncomputable def normalizerPPart (p : ℕ) (U : Subgroup G) : ℕ :=
  p ^ (Nat.card ↥(Subgroup.normalizer (U : Set G))).factorization p

/-- `normalizerPPart` is the order of every Sylow `p`-subgroup of the
normalizer. -/
theorem normalizerPPart_eq_card_sylow
    [Finite G] {p : ℕ} [Fact p.Prime] (U : Subgroup G)
    (S : Sylow p ↥(Subgroup.normalizer (U : Set G))) :
    normalizerPPart p U =
      Nat.card (S : Subgroup ↥(Subgroup.normalizer (U : Set G))) := by
  rw [normalizerPPart, S.card_eq_multiplicity]

/-- Every `p`-subgroup of `N_G(U)` has order at most `normalizerPPart p U`. -/
theorem card_le_normalizerPPart_of_isPGroup
    [Finite G] {p : ℕ} [Fact p.Prime] (U : Subgroup G)
    {R : Subgroup ↥(Subgroup.normalizer (U : Set G))} (hR : IsPGroup p R) :
    Nat.card R ≤ normalizerPPart p U := by
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  rw [normalizerPPart_eq_card_sylow U S]
  exact Subgroup.card_le_of_le hRS

/-- **Isaacs Theorem 7.1, Step 1 (bad subgroup existence).**

If `G` has no normal `p`-complement, Frobenius' normal-complement criterion
forces some nontrivial `p`-subgroup to have a normalizer without one. -/
theorem exists_isBadNormalizerPSubgroup
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G) :
    ∃ U : Subgroup G, IsBadNormalizerPSubgroup p U := by
  by_contra hbad
  apply hG
  rw [OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer]
  intro X hXp
  exact
    OddOrder.Isaacs.Ch05.isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement
      (fun Y hY_ne hYp => by
        by_contra hNY
        exact hbad ⟨Y, hY_ne, hYp, hNY⟩)
      X hXp

/-- **Isaacs Theorem 7.1, Step 1 (lexicographic choice of `U`).**

Among all bad `p`-subgroups choose `U` first maximizing the `p`-part of
`|N_G(U)|`, then maximizing `|U|` among ties.  The witness is selected from the
finite type of subgroups, so the maximality data are constructed rather than
postulated. -/
theorem exists_lexicographically_maximal_badNormalizerPSubgroup
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G) :
    ∃ U : Subgroup G,
      IsBadNormalizerPSubgroup p U ∧
      (∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
        normalizerPPart p X ≤ normalizerPPart p U) ∧
      (∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
        normalizerPPart p X = normalizerPPart p U → Nat.card X ≤ Nat.card U) := by
  classical
  letI : Fintype (Subgroup G) := Fintype.ofFinite _
  let family : Finset (Subgroup G) :=
    Finset.univ.filter (IsBadNormalizerPSubgroup p)
  obtain ⟨U₀, hU₀⟩ := exists_isBadNormalizerPSubgroup hG
  have hU₀_mem : U₀ ∈ family :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU₀⟩
  have hfamily : family.Nonempty := ⟨U₀, hU₀_mem⟩
  obtain ⟨V, hV_mem, hV_max⟩ :=
    family.exists_max_image (normalizerPPart p) hfamily
  let tied : Finset (Subgroup G) :=
    family.filter (fun X => normalizerPPart p X = normalizerPPart p V)
  have hV_tied : V ∈ tied :=
    Finset.mem_filter.mpr ⟨hV_mem, rfl⟩
  obtain ⟨U, hU_tied, hU_max⟩ :=
    tied.exists_max_image (fun X => Nat.card X) ⟨V, hV_tied⟩
  obtain ⟨hU_mem, hU_weight⟩ := Finset.mem_filter.mp hU_tied
  have hU_bad : IsBadNormalizerPSubgroup p U :=
    (Finset.mem_filter.mp hU_mem).2
  refine ⟨U, hU_bad, ?_, ?_⟩
  · intro X hX
    have hX_mem : X ∈ family :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX⟩
    exact (hV_max X hX_mem).trans_eq hU_weight.symm
  · intro X hX hX_weight
    have hX_mem : X ∈ family :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX⟩
    have hX_tied : X ∈ tied := by
      apply Finset.mem_filter.mpr
      refine ⟨hX_mem, ?_⟩
      exact hX_weight.trans hU_weight
    exact hU_max X hX_tied

end MinimalCounterexampleStepOne

end OddOrder.Isaacs.Ch07
