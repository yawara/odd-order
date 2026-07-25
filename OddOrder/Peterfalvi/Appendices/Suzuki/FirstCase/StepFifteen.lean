/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepFourteenSylow
import OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear.NonsplitTorus

/-!
# Peterfalvi Part II, Ch. II, step (15): the cyclic subgroup `L` of order `9`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (15), pp. 113-114.

> **(15)** There is a subgroup `L` of `R₁` which is cyclic of order `9`, inverted by
> `s`, normalized by `V` and centralized by `W` but not by `P`. …

The subgroup is `L = C_G(st) ∩ ⟨Q₀, K, t⟩`, and Peterfalvi reads "cyclic of order `9`"
off the isomorphism `⟨Q₀, K, t⟩ ≅ PSL(2, 8)` of Ch. I §3, Lemma 4.  This file supplies
that reading: by the nonsplit torus construction the Sylow `3`-subgroups of `PSL(2, 8)`
are cyclic of order `9`, and one of them centralizes `st`; conversely `C_G(st)` is a
`3`-group by (13), so the intersection has order dividing `9`.
-/

set_option autoImplicit false

open OddOrder.GroupTheory.ProjectiveSpecialLinear

open scoped Pointwise

namespace OddOrder.Peterfalvi.Appendices.Suzuki

section GenericProduct

variable {G' : Type*} [Group G']

/-- `|A ⊔ B| = |A|·|B|` when `B` normalizes `A` and the two meet trivially. -/
theorem card_sup_eq_mul_of_le_normalizer {A B : Subgroup G'}
    (hB : ∀ b ∈ B, b ∈ Subgroup.normalizer (A : Set G')) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  classical
  have hcoe : ((A ⊔ B : Subgroup G') : Set G') = (A : Set G') * (B : Set G') :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hB
  have hmul : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
    intro x hx
    have hx' : x ∈ ((A : Set G') * (B : Set G')) := by rw [← hcoe]; exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  have hbot : B ⊓ A = ⊥ := by rw [inf_comm]; exact hinf
  have hcompl := (Subgroup.isComplement'_subgroupOf_of_disjoint_mul_eq_univ
    (le_sup_right : B ≤ A ⊔ B) (le_sup_left : A ≤ A ⊔ B) hbot hmul).card_mul
  have hAc : Nat.card ↥(A.subgroupOf (A ⊔ B)) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hBc : Nat.card ↥(B.subgroupOf (A ⊔ B)) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [← hAc, ← hBc]
  exact hcompl.symm

/-- Conjugation by an element normalizing `X` preserves the centralizer of `X`. -/
theorem conj_mem_centralizer_of_forall_mem_iff {X : Subgroup G'} {g : G'}
    (hg : ∀ y : G', y ∈ X ↔ g * y * g⁻¹ ∈ X) {c : G'}
    (hc : c ∈ Subgroup.centralizer (X : Set G')) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (X : Set G') := by
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have hx' : g⁻¹ * x * g ∈ X := by
    refine (hg (g⁻¹ * x * g)).mpr ?_
    have h1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [h1]; exact hx
  have hcx := Subgroup.mem_centralizer_iff.mp hc _ hx'
  calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcx]
    _ = (g * c * g⁻¹) * x := by group

/-- An element normalizing a subgroup normalizes its centralizer. -/
theorem mem_normalizer_centralizer_of_mem_normalizer {X : Subgroup G'} {g : G'}
    (hg : ∀ y : G', y ∈ X ↔ g * y * g⁻¹ ∈ X) (c : G') :
    c ∈ Subgroup.centralizer (X : Set G')
      ↔ g * c * g⁻¹ ∈ Subgroup.centralizer (X : Set G') := by
  have hginv : ∀ y : G', y ∈ X ↔ g⁻¹ * y * g⁻¹⁻¹ ∈ X := by
    intro y
    rw [inv_inv]
    have h1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    refine ⟨fun hy => (hg (g⁻¹ * y * g)).mpr (by rw [h1]; exact hy), fun hy => ?_⟩
    have h2 := (hg (g⁻¹ * y * g)).mp hy
    rwa [h1] at h2
  refine ⟨fun h => conj_mem_centralizer_of_forall_mem_iff hg h, fun h => ?_⟩
  have h3 := conj_mem_centralizer_of_forall_mem_iff hginv h
  have h4 : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rwa [h4] at h3

/-- Conjugation by `a` preserves commuting with `z` when `a` itself commutes with `z`. -/
theorem commute_conj_of_commute {a b z : G'} (ha : Commute a z) (hb : Commute b z) :
    Commute (a * b * a⁻¹) z :=
  Commute.mul_left (Commute.mul_left ha hb) ha.inv_left

end GenericProduct

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

include model in
/-- **`L = C_G(st) ⊓ ⟨Q₀, K, t⟩` is cyclic of order `9`** ((15), p. 113).

`⟨Q₀, K, t⟩ ≅ PSL(2, 8)` has order `504`, and its Sylow `3`-subgroups are cyclic of
order `9` (the nonsplit torus).  The one containing `st` is abelian, hence centralizes
`st`, so it lies inside `L`; and `L` is a `3`-group by (13), so `|L|` divides `9`. -/
theorem isCyclic_and_card_centralizer_inf_orderThreeGeneratedSubgroup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    IsCyclic ↥(Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t} : Set G)
        ⊓ fc.toHypothesis.orderThreeGeneratedSubgroup)
      ∧ Nat.card ↥(Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t} : Set G)
        ⊓ fc.toHypothesis.orderThreeGeneratedSubgroup) = 9 := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, hp3, -, -, -, -⟩ := fc.step_twelve model ind hB2
  set z : G := fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t with hz_def
  set L₀ : Subgroup G := fc.toHypothesis.orderThreeGeneratedSubgroup with hL₀_def
  have hstord : orderOf z = 3 := by
    rw [hz_def, fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  -- `V ≠ 1`
  have hV : fc.toHypothesis.V ≠ ⊥ := by
    intro h
    have hcard := fc.card_V_eq_card_P_mul_card_W
    rw [h, Subgroup.card_bot, fc.card_P, hp3] at hcard
    have hWpos : 0 < Nat.card ↥fc.toHypothesis.W := Nat.card_pos
    omega
  -- `⟨Q₀, K, t⟩ ≅ PSL(2, F')` with `|F'| = |Q₀| = 8`
  obtain ⟨F', _, _, _, hcardF', ⟨e⟩⟩ :=
    fc.toHypothesis.exists_orderThreeGeneratedSubgroup_mulEquiv_psl2 hstord hV ind
  have hF'8 : Nat.card F' = 8 := by
    rw [hcardF', fc.card_Q0_eq_two_pow, hp3]
    norm_num
  have hL₀card : Nat.card ↥L₀ = 504 := by
    rw [hL₀_def, Nat.card_congr e.toEquiv]
    exact natCard_projectiveSpecialLinearGroup_eq_of_card_eq_eight F' hF'8
  -- `st ∈ ⟨Q₀, K, t⟩`
  have hsQ0 : fc.toHypothesis.distinguishedInvolution ∈ fc.toHypothesis.Q0 :=
    ⟨fc.toHypothesis.distinguishedInvolution_sq,
      fc.toHypothesis.distinguishedInvolution_mem_H⟩
  have hzL₀ : z ∈ L₀ := Subgroup.mul_mem _
    (fc.toHypothesis.orderThree_Q0_le hsQ0) fc.toHypothesis.orderThree_t_mem
  -- a cyclic Sylow `3`-subgroup of `⟨Q₀, K, t⟩` containing `st`
  have hcyc9 : ∃ C : Subgroup ↥L₀, IsCyclic ↥C ∧ Nat.card ↥C = 9 :=
    exists_isCyclic_card_nine_of_mulEquiv e.symm
      (exists_isCyclic_card_nine_projectiveSpecialLinearGroup F' hF'8)
  have hxord : orderOf (⟨z, hzL₀⟩ : ↥L₀) = 3 := by
    rw [Subgroup.orderOf_mk]; exact hstord
  obtain ⟨S, hzS, hScyc, hScard⟩ :=
    exists_isCyclic_card_nine_mem hL₀card hcyc9 hxord
  -- transport `S` to a subgroup of `G`
  set S' : Subgroup G := S.map L₀.subtype with hS'_def
  have hS'card : Nat.card ↥S' = 9 := by
    rw [hS'_def, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hScard
  have hS'cyc : IsCyclic ↥S' := by
    rw [hS'_def]
    exact isCyclic_of_surjective _
      (Subgroup.equivMapOfInjective S L₀.subtype (Subgroup.subtype_injective _)).surjective
  -- `S'` is abelian and contains `st`, so it centralizes `st`; and `S' ≤ L₀`
  haveI : IsMulCommutative ↥S' := IsCyclic.isMulCommutative
  have hS'le : S' ≤ Subgroup.centralizer ({z} : Set G) ⊓ L₀ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, y.2⟩
    have hzS' : (⟨z, hzL₀⟩ : ↥L₀) ∈ S := hzS
    have := ‹IsMulCommutative ↥S'›.is_comm.comm
      (⟨L₀.subtype y, ⟨y, hy, rfl⟩⟩ : ↥S')
      (⟨z, ⟨⟨z, hzL₀⟩, hzS', rfl⟩⟩ : ↥S')
    exact congrArg Subtype.val this
  -- `L` is a `3`-group by (13), so `|L|` divides `9`
  have hcen : Subgroup.centralizer
      ((Subgroup.zpowers z : Subgroup G) : Set G)
      = Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hLp : IsPGroup 3 ↥(Subgroup.centralizer ({z} : Set G) ⊓ L₀) := by
    refine IsPGroup.to_le ?_ (inf_le_left)
    rw [← hcen]
    exact fc.isPGroup_three_centralizer_Z₁ model ind hB2
  have hLdvd : Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ L₀) ∣ 504 := by
    rw [← hL₀card]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hLnine := card_dvd_nine_of_isPGroup_three hLp hLdvd
  have hLeq : Subgroup.centralizer ({z} : Set G) ⊓ L₀ = S' :=
    (Subgroup.eq_of_le_of_card_ge hS'le
      (by rw [hS'card]; exact Nat.le_of_dvd (by norm_num) hLnine)).symm
  exact ⟨hLeq ▸ hS'cyc, hLeq ▸ hS'card⟩

include fc in
/-- **`P` normalizes `⟨Q₀, K, t⟩`** ((15), p. 113, "As `P` normalizes `⟨Q₀,K,t⟩`…").

`P ≤ V ≤ D ≤ H`: conjugation by an element of `H` preserves `Q₀ = {x ∈ H | x² = 1}`;
`K` is normal in `D` (Ch. I §2, Prop 2); and `P ≤ V = C_D(t)` centralizes `t`. -/
theorem P_le_normalizer_orderThreeGeneratedSubgroup :
    fc.P ≤ Subgroup.normalizer
      ((fc.toHypothesis.orderThreeGeneratedSubgroup : Subgroup G) : Set G) := by
  have hconj : ∀ x ∈ fc.P, ∀ y ∈ fc.toHypothesis.orderThreeGeneratedSubgroup,
      x * y * x⁻¹ ∈ fc.toHypothesis.orderThreeGeneratedSubgroup := by
    intro x hxP
    have hxV : x ∈ fc.toHypothesis.V := fc.P_le_V hxP
    have hxD : x ∈ fc.toHypothesis.D := fc.toHypothesis.V_le_D hxV
    have hxH : x ∈ fc.toHypothesis.H := fc.toHypothesis.D_le_H hxD
    have hxt : x * fc.toHypothesis.t = fc.toHypothesis.t * x :=
      fc.toHypothesis.commute_t_of_mem_V hxV
    have hsub : fc.toHypothesis.orderThreeGeneratedSubgroup
        ≤ Subgroup.comap (MulAut.conj x).toMonoidHom
          fc.toHypothesis.orderThreeGeneratedSubgroup := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro q hq
        rw [Subgroup.mem_comap]
        refine fc.toHypothesis.orderThree_Q0_le ?_
        rw [fc.toHypothesis.mem_Q0_iff] at hq ⊢
        refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hxH hq.2)
          (Subgroup.inv_mem _ hxH)⟩
        change (x * q * x⁻¹) ^ 2 = 1
        rw [pow_two]
        calc x * q * x⁻¹ * (x * q * x⁻¹) = x * (q * q) * x⁻¹ := by group
          _ = 1 := by rw [← pow_two, hq.1]; group
      · intro k hk
        rw [Subgroup.mem_comap]
        refine (le_sup_left : fc.toHypothesis.orderThreeBorel
          ≤ fc.toHypothesis.orderThreeGeneratedSubgroup) (Subgroup.mem_sup_right ?_)
        have hkD : k ∈ fc.toHypothesis.D := fc.toHypothesis.K_le_D hk
        have hn := (fc.toHypothesis.K_normal).conj_mem
          (⟨k, hkD⟩ : ↥fc.toHypothesis.D)
          (by rwa [Subgroup.mem_subgroupOf]) (⟨x, hxD⟩ : ↥fc.toHypothesis.D)
        rwa [Subgroup.mem_subgroupOf] at hn
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
        change x * fc.toHypothesis.t * x⁻¹
          ∈ fc.toHypothesis.orderThreeGeneratedSubgroup
        have h1 : x * fc.toHypothesis.t * x⁻¹ = fc.toHypothesis.t := by
          rw [hxt]; group
        rw [h1]
        exact fc.toHypothesis.orderThree_t_mem
    intro y hy
    exact hsub hy
  intro x hxP
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  refine ⟨fun hy => hconj x hxP y hy, fun hy => ?_⟩
  have h1 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
  rw [← h1]
  exact hconj x⁻¹ (Subgroup.inv_mem _ hxP) _ hy

include fc in
/-- **`Z₁ ≤ L`** ((15), p. 113): `st` centralizes itself and lies in `⟨Q₀, K, t⟩`. -/
theorem zpowers_le_centralizer_inf_orderThreeGeneratedSubgroup :
    Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
      ≤ Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t} : Set G)
        ⊓ fc.toHypothesis.orderThreeGeneratedSubgroup := by
  have hsQ0 : fc.toHypothesis.distinguishedInvolution ∈ fc.toHypothesis.Q0 :=
    ⟨fc.toHypothesis.distinguishedInvolution_sq,
      fc.toHypothesis.distinguishedInvolution_mem_H⟩
  refine Subgroup.zpowers_le.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_⟩
  exact Subgroup.mul_mem _ (fc.toHypothesis.orderThree_Q0_le hsQ0)
    fc.toHypothesis.orderThree_t_mem

include model in
/-- **`L ⊓ P = 1`** ((15), p. 113).

If not, then `P ≤ L` (as `|P| = 3` is prime), so `Z₁P ≤ L`; but `|Z₁P| = 9 = |L|`, so
`L = Z₁P` would have exponent `3`, contradicting the cyclicity of `L` of order `9`. -/
theorem inf_P_eq_bot_of_centralizer_inf_orderThreeGeneratedSubgroup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    (Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t} : Set G)
        ⊓ fc.toHypothesis.orderThreeGeneratedSubgroup) ⊓ fc.P = ⊥ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  obtain ⟨hLcyc, hLcard⟩ :=
    fc.isCyclic_and_card_centralizer_inf_orderThreeGeneratedSubgroup model ind hB2
  set L : Subgroup G := Subgroup.centralizer
    ({fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t} : Set G)
      ⊓ fc.toHypothesis.orderThreeGeneratedSubgroup with hL_def
  have hZ₁L := fc.zpowers_le_centralizer_inf_orderThreeGeneratedSubgroup
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  by_contra hy1
  -- `P = ⟨y⟩ ≤ L`
  have hPcard : Nat.card ↥fc.P = 3 := by rw [fc.card_P, hp3]
  have hyord : orderOf y = 3 := by
    have h := fc.P.orderOf_dvd_natCard hy.2
    rw [hPcard] at h
    rcases (Nat.dvd_prime (by norm_num)).mp h with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hy1
    · exact h3
  have hPL : fc.P ≤ L := by
    have hgen : Subgroup.zpowers y = fc.P :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy.2)
        (by rw [Nat.card_zpowers, hyord, hPcard])
    rw [← hgen]
    exact Subgroup.zpowers_le.mpr hy.1
  -- `L = Z₁P`, hence of exponent `3`
  have habR := fc.invImageF_mul_comm model ind hB2 hm
  have hcomm : ∀ a ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t), ∀ b ∈ fc.P, a * b = b * a := by
    intro a ha b hb
    exact habR a ((fc.zpowers_distinguishedInvolution_mul_t_le_sInvertedT model ind hB2
      hm).trans (fc.sInvertedT_spec model ind hB2 hm).1 ha) b (fc.P_le_invImageF model hb)
  have hsupL : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ⊔ fc.P = L :=
    Subgroup.eq_of_le_of_card_ge (sup_le hZ₁L hPL)
      (by rw [hLcard, fc.card_zpowers_sup_P_eq_nine model ind hB2])
  have hcube : ∀ x ∈ L, x ^ 3 = 1 := by
    intro x hx
    rw [← hsupL] at hx
    refine pow_eq_one_of_mem_sup_of_commute hcomm ?_ ?_ hx
    · intro a ha
      have h := Subgroup.orderOf_dvd_natCard _ ha
      rw [Nat.card_zpowers, fc.orderOf_st_eq_char model, fc.char_eq_p model hB2,
        hp3] at h
      exact orderOf_dvd_iff_pow_eq_one.mp h
    · intro b hb
      have h := fc.P.orderOf_dvd_natCard hb
      rw [hPcard] at h
      exact orderOf_dvd_iff_pow_eq_one.mp h
  -- but `L` is cyclic of order `9`
  obtain ⟨g, hg⟩ := hLcyc.exists_generator
  have hgtop : Subgroup.zpowers g = ⊤ := by
    rw [eq_top_iff]
    exact fun x _ => hg x
  have hgord : orderOf (g : G) = 9 := by
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers, hgtop, Subgroup.card_top, hLcard]
  have hg3 : (g : G) ^ 3 = 1 := hcube _ g.2
  have := orderOf_dvd_of_pow_eq_one hg3
  rw [hgord] at this
  omega

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
