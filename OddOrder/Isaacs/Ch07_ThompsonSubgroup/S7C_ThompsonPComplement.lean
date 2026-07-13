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

/-- A normal `p`-complement descends along an inclusion of finite subgroups. -/
theorem hasNormalPComplement_of_le
    [Finite G] {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hBA : B ≤ A)
    (hA : OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥A) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥B := by
  have hSub := OddOrder.Isaacs.Ch05.hasNormalPComplement_of_subgroup hA
    (B.subgroupOf A)
  exact hasNormalPComplement_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hBA) hSub

/-- A homomorphic image of a normalizer normalizes the image subgroup. -/
theorem map_normalizer_le_normalizer_map
    {A B : Type*} [Group A] [Group B] (f : A →* B) (L : Subgroup A) :
    (Subgroup.normalizer (L : Set A)).map f ≤
      Subgroup.normalizer ((L.map f : Subgroup B) : Set B) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' := Subgroup.mem_normalizer_iff.mp hx
  apply Subgroup.mem_normalizer_iff.mpr
  intro y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨x * z * x⁻¹, (hx' z).mp hz, ?_⟩
    simp only [map_mul, map_inv]
  · rintro ⟨z, hz, hz_eq⟩
    refine ⟨x⁻¹ * z * x, ?_, ?_⟩
    · apply (hx' (x⁻¹ * z * x)).mpr
      have heq : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
      rwa [heq]
    · calc
        f (x⁻¹ * z * x) = (f x)⁻¹ * f z * f x := by
          simp only [map_mul, map_inv]
        _ = y := by rw [hz_eq]; group

/-- Ambient Thompson local hypotheses descend to a subgroup containing the
same `p`-subgroup, with centers and Thompson subgroups computed internally. -/
theorem HasThompsonLocalPComplements.of_subgroup
    [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G)
    {S : Subgroup H}
    (hS : HasThompsonLocalPComplements p (S.map H.subtype)) :
    HasThompsonLocalPComplements p S := by
  have hCenter :
      (Subgroup.center ↥(S.map H.subtype)).map (S.map H.subtype).subtype =
        ((Subgroup.center ↥S).map S.subtype).map H.subtype :=
    center_map_subtype_map_of_restrict_injective H.subtype
      (H.subtype_injective.comp S.subtype_injective)
  have hJ :
      Subgroup.thompsonJ (S.map H.subtype) p =
        (Subgroup.thompsonJ S p).map H.subtype :=
    Subgroup.thompsonJ_map_of_injective H.subtype_injective S p
  constructor
  · have hC_le :
        (Subgroup.centralizer
            (((Subgroup.center ↥S).map S.subtype : Subgroup H) : Set H)).map
              H.subtype ≤
          Subgroup.centralizer
            (((Subgroup.center ↥(S.map H.subtype)).map
              (S.map H.subtype).subtype : Subgroup G) : Set G) := by
      rw [hCenter]
      simpa only [Subgroup.coe_map] using
        (Subgroup.map_centralizer_le_centralizer_image
          (((Subgroup.center ↥S).map S.subtype : Subgroup H) : Set H) H.subtype)
    have hImage := hasNormalPComplement_of_le hC_le hS.1
    exact hasNormalPComplement_of_mulEquiv
      (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).symm hImage
  · have hN_le :
        (Subgroup.normalizer
            ((Subgroup.thompsonJ S p : Subgroup H) : Set H)).map H.subtype ≤
          Subgroup.normalizer
            ((Subgroup.thompsonJ (S.map H.subtype) p : Subgroup G) : Set G) := by
      rw [hJ]
      exact map_normalizer_le_normalizer_map H.subtype _
    have hImage := hasNormalPComplement_of_le hN_le hS.2
    exact hasNormalPComplement_of_mulEquiv
      (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).symm hImage


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

/-- The normalizer of a subgroup also normalizes its Thompson subgroup. -/
theorem normalizer_le_normalizer_thompsonJ
    [Finite G] {p : ℕ} (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((Subgroup.thompsonJ S p : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hconj :
      (Subgroup.thompsonJ S p).map (MulAut.conj g).toMonoidHom =
        Subgroup.thompsonJ S p :=
    Subgroup.thompsonJ_map_conj_eq_of_mem_normalizer hg
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈
        (Subgroup.thompsonJ S p).map (MulAut.conj g).toMonoidHom :=
      ⟨x, hx, rfl⟩
    rwa [hconj] at hx'
  · intro hx
    have hx' : g * x * g⁻¹ ∈
        (Subgroup.thompsonJ S p).map (MulAut.conj g).toMonoidHom := by
      rw [hconj]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have hxy : x = y := by
      have : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      exact (mul_left_cancel (mul_right_cancel this)).symm
    rwa [hxy]

/-- Failure of a Thompson local hypothesis produces a nontrivial bad
`p`-subgroup, either the ambient center of `S` or its Thompson subgroup.  Every
subgroup normalizing `S` also normalizes the selected subgroup. -/
theorem exists_badNormalizerPSubgroup_of_not_hasThompsonLocalPComplements
    [Finite G] {p : ℕ} [Fact p.Prime] {S T : Subgroup G}
    (hS_p : IsPGroup p S) (hS_ne : S ≠ ⊥)
    (hT_norm : T ≤ Subgroup.normalizer (S : Set G))
    (hLocal : ¬ HasThompsonLocalPComplements p S) :
    ∃ X : Subgroup G,
      IsBadNormalizerPSubgroup p X ∧
        T ≤ Subgroup.normalizer (X : Set G) := by
  classical
  rw [HasThompsonLocalPComplements] at hLocal
  rcases not_and_or.mp hLocal with hCenter | hJ
  · set Z : Subgroup G := (Subgroup.center ↥S).map S.subtype with hZ_def
    have hZ_ne : Z ≠ ⊥ := by
      rw [hZ_def, Ne, Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective]
      haveI : Nontrivial ↥S := S.nontrivial_iff_ne_bot.mpr hS_ne
      exact (Subgroup.center ↥S).nontrivial_iff_ne_bot.mp hS_p.center_nontrivial
    have hZ_p : IsPGroup p Z := by
      rw [hZ_def]
      exact (hS_p.to_subgroup (Subgroup.center ↥S)).map S.subtype
    have hNZ :
        ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p
          ↥(Subgroup.normalizer (Z : Set G)) := by
      intro h
      exact hCenter
        (hasNormalPComplement_of_le
          (Subgroup.centralizer_le_normalizer (Z : Set G)) h)
    refine ⟨Z, ⟨hZ_ne, hZ_p, hNZ⟩, ?_⟩
    intro t ht
    exact Subgroup.mem_normalizer_center_map_of_mem_normalizer (hT_norm ht)
  · set J : Subgroup G := Subgroup.thompsonJ S p with hJ_def
    have hJ_ne : J ≠ ⊥ := by
      rw [hJ_def]
      exact Subgroup.thompsonJ_ne_bot hS_p hS_ne
    have hJ_p : IsPGroup p J := by
      rw [hJ_def]
      exact hS_p.of_injective
        (Subgroup.inclusion (Subgroup.thompsonJ_le S p))
        (Subgroup.inclusion_injective _)
    refine ⟨J, ⟨hJ_ne, hJ_p, hJ⟩, ?_⟩
    exact hT_norm.trans (normalizer_le_normalizer_thompsonJ S)

/-- **§7C/§7D helper** — normalizer-grows. If `D < ↑S` for a finite
`p`-group Sylow `S`, then `D` is strictly contained in `N_H(D) ⊓ ↑S`. -/
theorem lt_normalizer_inf_sylow_of_lt
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (S : Sylow p H) {D : Subgroup H} (hD_lt : D < (S : Subgroup H)) :
    D < Subgroup.normalizer D ⊓ (S : Subgroup H) := by
  classical
  haveI : Group.IsNilpotent ↥(S : Subgroup H) := S.isPGroup'.isNilpotent
  have hNC : NormalizerCondition ↥(S : Subgroup H) :=
    Group.normalizerCondition_of_isNilpotent (G := ↥(S : Subgroup H))
  have hD_le : D ≤ (S : Subgroup H) := le_of_lt hD_lt
  have hsub_lt_top : D.subgroupOf (S : Subgroup H) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact (ne_of_lt hD_lt) (le_antisymm hD_le htop)
  have hlt := hNC (D.subgroupOf (S : Subgroup H)) hsub_lt_top
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hD_le, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  refine lt_of_le_of_ne (le_inf Subgroup.le_normalizer hD_le) ?_
  intro heq
  apply ht_not
  have : (t : H) ∈ Subgroup.normalizer D ⊓ (S : Subgroup H) := ⟨ht_norm, t.2⟩
  rw [← heq] at this
  exact this

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
/-- **Isaacs Theorem 7.1, Step 1 (normalizer growth).**

The first, `normalizerPPart`, maximality condition forces the selected bad
`p`-subgroup to be normal.  If its normalizer were proper, induction would
produce a failed Thompson local hypothesis there.  A larger ambient
`p`-subgroup normalizing the corresponding center or Thompson subgroup would
then give a bad subgroup with strictly larger normalizer `p`-part. -/
theorem maximal_badNormalizer_normalizer_eq_top.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    {U : Subgroup G} (hU_bad : IsBadNormalizerPSubgroup p U)
    (hU_weight_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X ≤ normalizerPPart p U) :
    Subgroup.normalizer (U : Set G) = ⊤ := by
  classical
  set N : Subgroup G := Subgroup.normalizer (U : Set G) with hN_def
  change N = ⊤
  by_contra hN_ne_top
  have hN_card : Nat.card N < Nat.card G :=
    Subgroup.card_lt_card_of_ne_top hN_ne_top
  have hN_no_complement :
      ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p N := by
    simpa only [hN_def] using hU_bad.2.2
  have hN_not_hyp : ¬ HasThompsonPComplementHypothesis p N := by
    intro hN_hyp
    exact hN_no_complement (ih N hN_card hN_hyp)
  rw [HasThompsonPComplementHypothesis] at hN_not_hyp
  push Not at hN_not_hyp
  obtain ⟨S, hS_local_fail⟩ := hN_not_hyp
  have hU_le_N : U ≤ N := by
    rw [hN_def]
    exact Subgroup.le_normalizer
  have hUN_p : IsPGroup p (U.subgroupOf N) := hU_bad.2.1.comap_subtype
  haveI hUN_normal : (U.subgroupOf N).Normal := by
    rw [hN_def]
    exact Subgroup.normal_in_normalizer
  have hUN_le_S : U.subgroupOf N ≤ (S : Subgroup N) :=
    (OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hUN_p).trans
      (OddOrder.Isaacs.Ch01.opCore_le S)
  have hUN_ne : U.subgroupOf N ≠ ⊥ := by
    intro hUN_bot
    apply hU_bad.1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxUN : (⟨x, hU_le_N hx⟩ : N) ∈ U.subgroupOf N := hx
    rw [hUN_bot, Subgroup.mem_bot] at hxUN
    exact congrArg Subtype.val hxUN
  have hS_ne : (S : Subgroup N) ≠ ⊥ := by
    intro hS_bot
    apply hUN_ne
    apply le_antisymm
    · simpa only [hS_bot] using hUN_le_S
    · exact bot_le
  set SH : Subgroup G := (S : Subgroup N).map N.subtype with hSH_def
  have hSH_p : IsPGroup p SH := by
    rw [hSH_def]
    exact S.isPGroup'.map N.subtype
  have hSH_ne : SH ≠ ⊥ := by
    rw [hSH_def, Ne,
      Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective]
    exact hS_ne
  have hSH_local_fail : ¬ HasThompsonLocalPComplements p SH := by
    intro hSH_local
    apply hS_local_fail
    apply HasThompsonLocalPComplements.of_subgroup (G := G) N
    simpa only [hSH_def] using hSH_local
  obtain ⟨P, hSH_le_P⟩ := hSH_p.exists_le_sylow
  have hSH_lt_P : SH < (P : Subgroup G) :=
    lt_of_le_of_ne hSH_le_P (by
      intro hSH_eq_P
      apply hSH_local_fail
      rw [hSH_eq_P]
      exact hHyp P)
  set T : Subgroup G :=
    Subgroup.normalizer (SH : Set G) ⊓ (P : Subgroup G) with hT_def
  have hSH_lt_T : SH < T := by
    rw [hT_def]
    exact lt_normalizer_inf_sylow_of_lt P hSH_lt_P
  have hT_p : IsPGroup p T := by
    rw [hT_def]
    exact P.isPGroup'.to_le inf_le_right
  have hT_normalizes_SH : T ≤ Subgroup.normalizer (SH : Set G) := by
    rw [hT_def]
    exact inf_le_left
  obtain ⟨X, hX_bad, hT_normalizes_X⟩ :=
    exists_badNormalizerPSubgroup_of_not_hasThompsonLocalPComplements
      hSH_p hSH_ne hT_normalizes_SH hSH_local_fail
  have hT_sub_p :
      IsPGroup p (T.subgroupOf (Subgroup.normalizer (X : Set G))) :=
    hT_p.comap_subtype
  have hT_le_weight : Nat.card T ≤ normalizerPPart p X := by
    calc
      Nat.card T =
          Nat.card (T.subgroupOf (Subgroup.normalizer (X : Set G))) :=
        (Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hT_normalizes_X).toEquiv).symm
      _ ≤ normalizerPPart p X :=
        card_le_normalizerPPart_of_isPGroup X hT_sub_p
  have hSH_card_lt_T : Nat.card SH < Nat.card T := by
    exact Set.Finite.card_lt_card (Set.toFinite _)
      (SetLike.coe_ssubset_coe.mpr hSH_lt_T)
  have hSH_card : Nat.card SH = Nat.card (S : Subgroup N) := by
    rw [hSH_def, Subgroup.card_map_of_injective N.subtype_injective]
  have hU_weight :
      normalizerPPart p U = Nat.card (S : Subgroup N) := by
    simpa only [hN_def] using normalizerPPart_eq_card_sylow U S
  have hweight_lt : normalizerPPart p U < normalizerPPart p X := by
    calc
      normalizerPPart p U = Nat.card (S : Subgroup N) := hU_weight
      _ = Nat.card SH := hSH_card.symm
      _ < Nat.card T := hSH_card_lt_T
      _ ≤ normalizerPPart p X := hT_le_weight
  exact (not_lt_of_ge (hU_weight_max X hX_bad)) hweight_lt

/-- **Isaacs Theorem 7.1, Step 1.**

The lexicographically maximal bad `p`-subgroup is `O_p(G)`.  The first
maximality coordinate makes it normal; maximality of its order among equal
normalizer `p`-parts then identifies it with the largest normal `p`-subgroup. -/
theorem maximal_badNormalizer_eq_opCore.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    {U : Subgroup G} (hU_bad : IsBadNormalizerPSubgroup p U)
    (hU_weight_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X ≤ normalizerPPart p U)
    (hU_card_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X = normalizerPPart p U → Nat.card X ≤ Nat.card U) :
    U = OddOrder.Isaacs.Ch01.opCore p G := by
  have hNU_top :=
    maximal_badNormalizer_normalizer_eq_top hHyp ih hU_bad hU_weight_max
  haveI hU_normal : U.Normal := Subgroup.normalizer_eq_top_iff.mp hNU_top
  set O : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hO_def
  have hU_le_O : U ≤ O := by
    rw [hO_def]
    exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hU_bad.2.1
  have hO_ne : O ≠ ⊥ := by
    intro hO_bot
    apply hU_bad.1
    exact le_bot_iff.mp (hU_le_O.trans (le_of_eq hO_bot))
  have hO_p : IsPGroup p O := by
    rw [hO_def]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hNO_top : Subgroup.normalizer (O : Set G) = ⊤ := by
    apply Subgroup.normalizer_eq_top_iff.mpr
    rw [hO_def]
    exact OddOrder.Isaacs.Ch01.opCore.normal p G
  have hnormalizers :
      Subgroup.normalizer (O : Set G) = Subgroup.normalizer (U : Set G) :=
    hNO_top.trans hNU_top.symm
  have hO_no_complement :
      ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p
        ↥(Subgroup.normalizer (O : Set G)) := by
    rw [hnormalizers]
    exact hU_bad.2.2
  have hO_bad : IsBadNormalizerPSubgroup p O :=
    ⟨hO_ne, hO_p, hO_no_complement⟩
  have hweights : normalizerPPart p O = normalizerPPart p U := by
    rw [normalizerPPart, normalizerPPart, hnormalizers]
  have hO_card_le : Nat.card O ≤ Nat.card U :=
    hU_card_max O hO_bad hweights
  have hU_eq_O : U = O :=
    Subgroup.eq_of_le_of_card_ge hU_le_O hO_card_le
  simpa only [hO_def] using hU_eq_O

end MinimalCounterexampleStepOne
section MinimalCounterexampleStepTwo

/-- If one Sylow `p`-subgroup is trivial, the whole group is its own normal
`p`-complement. -/
theorem hasNormalPComplement_of_sylow_eq_bot
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP : (P : Subgroup G) = ⊥) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  refine ⟨⊤, inferInstance, fun Q => ?_⟩
  have hQP : (Q : Subgroup G) = (P : Subgroup G) :=
    P.is_maximal' Q.isPGroup' (by rw [hP]; exact bot_le)
  rw [hQP, hP]
  exact Subgroup.isComplement'_top_bot

/-- The correspondence theorem identifies normalizers after quotienting by a
normal subgroup contained in the subgroup being normalized. -/
theorem normalizer_map_quotient_eq_of_le
    [Finite G] {N : Subgroup G} [N.Normal] {X : Subgroup G} (hNX : N ≤ X) :
    Subgroup.normalizer
        ((X.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
      (Subgroup.normalizer (X : Set G)).map (QuotientGroup.mk' N) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hker : q.ker = N := QuotientGroup.ker_mk' N
  have hker_le_X : q.ker ≤ X := by simpa only [hker] using hNX
  apply Subgroup.comap_injective hq
  rw [Subgroup.comap_normalizer_eq_of_surjective _ hq]
  rw [Subgroup.comap_map_eq_self hker_le_X]
  rw [Subgroup.comap_map_eq_self (hker_le_X.trans Subgroup.le_normalizer)]

/-- For the lexicographically maximal bad subgroup `U`, every strictly larger
`p`-subgroup `X` lying in a Sylow subgroup and normalized by that Sylow subgroup
has a normalizer with a normal `p`-complement. -/
theorem hasNormalPComplement_normalizer_of_maximal_bad_lt
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {U X : Subgroup G} [U.Normal]
    (hU_bad : IsBadNormalizerPSubgroup p U)
    (hU_weight_max : ∀ Y : Subgroup G, IsBadNormalizerPSubgroup p Y →
      normalizerPPart p Y ≤ normalizerPPart p U)
    (hU_card_max : ∀ Y : Subgroup G, IsBadNormalizerPSubgroup p Y →
      normalizerPPart p Y = normalizerPPart p U → Nat.card Y ≤ Nat.card U)
    (hUX : U < X) (hXP : X ≤ (P : Subgroup G))
    (hP_normalizes_X : (P : Subgroup G) ≤ Subgroup.normalizer (X : Set G)) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer (X : Set G)) := by
  by_contra hNX
  have hX_ne : X ≠ ⊥ := by
    intro hX
    apply hU_bad.1
    exact le_bot_iff.mp (hUX.le.trans (le_of_eq hX))
  have hX_p : IsPGroup p X := P.isPGroup'.to_le hXP
  have hX_bad : IsBadNormalizerPSubgroup p X := ⟨hX_ne, hX_p, hNX⟩
  have hNU_top : Subgroup.normalizer (U : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have htop_card : Nat.card ↥(⊤ : Subgroup G) = Nat.card G :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  have hU_weight : normalizerPPart p U = Nat.card (P : Subgroup G) := by
    rw [normalizerPPart, hNU_top, htop_card, P.card_eq_multiplicity]
  have hP_sub_p :
      IsPGroup p
        ((P : Subgroup G).subgroupOf (Subgroup.normalizer (X : Set G))) :=
    P.isPGroup'.comap_subtype
  have hP_card_le : Nat.card (P : Subgroup G) ≤ normalizerPPart p X := by
    calc
      Nat.card (P : Subgroup G) =
          Nat.card
            ((P : Subgroup G).subgroupOf (Subgroup.normalizer (X : Set G))) :=
        (Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hP_normalizes_X).toEquiv).symm
      _ ≤ normalizerPPart p X :=
        card_le_normalizerPPart_of_isPGroup X hP_sub_p
  have hweight_ge : normalizerPPart p U ≤ normalizerPPart p X :=
    hU_weight.le.trans hP_card_le
  have hweight_le : normalizerPPart p X ≤ normalizerPPart p U :=
    hU_weight_max X hX_bad
  have hweights : normalizerPPart p X = normalizerPPart p U :=
    le_antisymm hweight_le hweight_ge
  have hX_card_le : Nat.card X ≤ Nat.card U :=
    hU_card_max X hX_bad hweights
  have hU_card_lt : Nat.card U < Nat.card X :=
    Set.Finite.card_lt_card (Set.toFinite _)
      (SetLike.coe_ssubset_coe.mpr hUX)
  exact (not_lt_of_ge hX_card_le) hU_card_lt

/-- **Isaacs Theorem 7.1, Step 2.**

Let `U` be the lexicographically maximal bad `p`-subgroup, already known to
be normal.  Then `G/U` has a normal `p`-complement.  For a Sylow subgroup
`P` containing `U`, every nontrivial subgroup of `P/U` used in the Thompson
local hypotheses has inverse image strictly above `U`; maximality therefore
gives a normal `p`-complement in its upstairs normalizer.  The correspondence
theorem transports this complement back to the quotient normalizer, and the
minimal-order hypothesis applies to `G/U`. -/
theorem maximal_badNormalizer_quotient_hasNormalPComplement.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    {U : Subgroup G} [U.Normal]
    (hU_bad : IsBadNormalizerPSubgroup p U)
    (hU_weight_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X ≤ normalizerPPart p U)
    (hU_card_max : ∀ X : Subgroup G, IsBadNormalizerPSubgroup p X →
      normalizerPPart p X = normalizerPPart p U → Nat.card X ≤ Nat.card U) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p (G ⧸ U) := by
  classical
  obtain ⟨P, hUP⟩ := hU_bad.2.1.exists_le_sylow
  let q : G →* G ⧸ U := QuotientGroup.mk' U
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective U
  have hker : q.ker = U := QuotientGroup.ker_mk' U
  set Pbar : Sylow p (G ⧸ U) := P.mapSurjective hq with hPbar_def
  have hPbar_coe :
      (Pbar : Subgroup (G ⧸ U)) = (P : Subgroup G).map q := by
    rw [hPbar_def, Sylow.coe_mapSurjective]
  by_cases hPbar_bot : (Pbar : Subgroup (G ⧸ U)) = ⊥
  · exact hasNormalPComplement_of_sylow_eq_bot Pbar hPbar_bot
  have hPbar_comap :
      (Pbar : Subgroup (G ⧸ U)).comap q = (P : Subgroup G) := by
    rw [hPbar_coe]
    exact Subgroup.comap_map_eq_self (by simpa only [hker] using hUP)
  have quotientNormalizer_hasNormalPComplement
      (Xbar : Subgroup (G ⧸ U)) (hXbar_ne : Xbar ≠ ⊥)
      (hXbar_le : Xbar ≤ (Pbar : Subgroup (G ⧸ U)))
      (hPbar_normalizes_Xbar :
        (Pbar : Subgroup (G ⧸ U)) ≤
          Subgroup.normalizer (Xbar : Set (G ⧸ U))) :
      OddOrder.Isaacs.Ch05.HasNormalPComplement p
        ↥(Subgroup.normalizer (Xbar : Set (G ⧸ U))) := by
    set X : Subgroup G := Xbar.comap q with hX_def
    have hUX : U < X := by
      have hcomap_lt :
          (⊥ : Subgroup (G ⧸ U)).comap q < Xbar.comap q :=
        (Subgroup.comap_lt_comap_of_surjective hq).2
          (bot_lt_iff_ne_bot.mpr hXbar_ne)
      simpa only [MonoidHom.comap_bot, hker, hX_def] using hcomap_lt
    have hXP : X ≤ (P : Subgroup G) := by
      rw [hX_def, ← hPbar_comap]
      exact Subgroup.comap_mono hXbar_le
    have hP_normalizes_X :
        (P : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
      have hcomap :
          (Pbar : Subgroup (G ⧸ U)).comap q ≤
            (Subgroup.normalizer (Xbar : Set (G ⧸ U))).comap q :=
        Subgroup.comap_mono hPbar_normalizes_Xbar
      rw [Subgroup.comap_normalizer_eq_of_surjective _ hq, hPbar_comap] at hcomap
      simpa only [hX_def] using hcomap
    have hNX :=
      hasNormalPComplement_normalizer_of_maximal_bad_lt P hU_bad
        hU_weight_max hU_card_max hUX hXP hP_normalizes_X
    have hImage :=
      hasNormalPComplement_subgroup_map q
        (Subgroup.normalizer (X : Set G)) hNX
    have hX_map : X.map q = Xbar := by
      rw [hX_def]
      exact Subgroup.map_comap_eq_self_of_surjective hq Xbar
    have hNormalizer_image :
        Subgroup.normalizer (Xbar : Set (G ⧸ U)) =
          (Subgroup.normalizer (X : Set G)).map q := by
      rw [← hX_map]
      exact normalizer_map_quotient_eq_of_le hUX.le
    exact hasNormalPComplement_of_mulEquiv
      (MulEquiv.subgroupCongr hNormalizer_image.symm) hImage
  have hcard : Nat.card (G ⧸ U) < Nat.card G :=
    Subgroup.card_quotient_lt_of_ne_bot hU_bad.1
  refine ih (G ⧸ U) hcard ?_
  rw [hasThompsonPComplementHypothesis_iff Pbar]
  set Zbar : Subgroup (G ⧸ U) :=
    (Subgroup.center ↥(Pbar : Subgroup (G ⧸ U))).map
      (Pbar : Subgroup (G ⧸ U)).subtype with hZbar_def
  set Jbar : Subgroup (G ⧸ U) :=
    Subgroup.thompsonJ (Pbar : Subgroup (G ⧸ U)) p with hJbar_def
  haveI : Nontrivial ↥(Pbar : Subgroup (G ⧸ U)) :=
    (Pbar : Subgroup (G ⧸ U)).nontrivial_iff_ne_bot.mpr hPbar_bot
  have hZbar_ne : Zbar ≠ ⊥ := by
    rw [hZbar_def, Ne,
      Subgroup.map_eq_bot_iff_of_injective _
        (Pbar : Subgroup (G ⧸ U)).subtype_injective]
    exact (Subgroup.center ↥(Pbar : Subgroup (G ⧸ U))).nontrivial_iff_ne_bot.mp
      Pbar.isPGroup'.center_nontrivial
  have hZbar_le : Zbar ≤ (Pbar : Subgroup (G ⧸ U)) := by
    rw [hZbar_def]
    exact Subgroup.map_subtype_le _
  have hPbar_normalizes_Zbar :
      (Pbar : Subgroup (G ⧸ U)) ≤
        Subgroup.normalizer (Zbar : Set (G ⧸ U)) := by
    intro g hg
    rw [hZbar_def]
    exact Subgroup.mem_normalizer_center_map_of_mem_normalizer
      (Subgroup.le_normalizer hg)
  have hNZbar := quotientNormalizer_hasNormalPComplement Zbar hZbar_ne
    hZbar_le hPbar_normalizes_Zbar
  have hCZbar :
      OddOrder.Isaacs.Ch05.HasNormalPComplement p
        ↥(Subgroup.centralizer (Zbar : Set (G ⧸ U))) :=
    hasNormalPComplement_of_le
      (Subgroup.centralizer_le_normalizer (Zbar : Set (G ⧸ U))) hNZbar
  have hJbar_ne : Jbar ≠ ⊥ := by
    rw [hJbar_def]
    exact Subgroup.thompsonJ_ne_bot Pbar.isPGroup' hPbar_bot
  have hJbar_le : Jbar ≤ (Pbar : Subgroup (G ⧸ U)) := by
    rw [hJbar_def]
    exact Subgroup.thompsonJ_le _ _
  have hPbar_normalizes_Jbar :
      (Pbar : Subgroup (G ⧸ U)) ≤
        Subgroup.normalizer (Jbar : Set (G ⧸ U)) := by
    rw [hJbar_def]
    exact Subgroup.le_normalizer.trans
      (normalizer_le_normalizer_thompsonJ (Pbar : Subgroup (G ⧸ U)))
  have hNJbar := quotientNormalizer_hasNormalPComplement Jbar hJbar_ne
    hJbar_le hPbar_normalizes_Jbar
  simpa only [HasThompsonLocalPComplements, hZbar_def, hJbar_def] using
    And.intro hCZbar hNJbar

end MinimalCounterexampleStepTwo

end OddOrder.Isaacs.Ch07
