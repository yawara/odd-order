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

/-- An element commuting with `z` normalizes `C_G(z)`. -/
theorem mem_centralizer_singleton_conj_iff {a z : G'} (ha : Commute a z) (y : G') :
    y ∈ Subgroup.centralizer ({z} : Set G')
      ↔ a * y * a⁻¹ ∈ Subgroup.centralizer ({z} : Set G') := by
  have hfwd : ∀ {b c : G'}, Commute b z → c ∈ Subgroup.centralizer ({z} : Set G') →
      b * c * b⁻¹ ∈ Subgroup.centralizer ({z} : Set G') := fun hb hc =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_conj_of_commute hb (Subgroup.mem_centralizer_singleton_iff.mp hc))
  refine ⟨fun hy => hfwd ha hy, fun hy => ?_⟩
  have h := hfwd ha.inv_left hy
  have h1 : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
  rwa [h1] at h

/-- In a cyclic group of order `p²` the elements killed by `p` lie in the subgroup
generated by the `p`-th power of a generator. -/
theorem mem_zpowers_pow_of_pow_eq_one {g x : G'} {p : ℕ} (hp : p ≠ 0)
    (hgord : orderOf g = p * p) (hx : x ∈ Subgroup.zpowers g) (hxp : x ^ p = 1) :
    x ∈ Subgroup.zpowers (g ^ p) := by
  obtain ⟨k, rfl⟩ := hx
  have h1 : g ^ (k * (p : ℤ)) = 1 := by rw [zpow_mul, zpow_natCast, hxp]
  have h2 : ((p * p : ℕ) : ℤ) ∣ k * (p : ℤ) := by
    rw [← hgord]; exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  have h3 : (p : ℤ) ∣ k := by
    have hp' : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp
    push_cast at h2
    exact (mul_dvd_mul_iff_right hp').mp (by rwa [mul_comm ((p : ℤ)) ((p : ℤ))] at h2)
  obtain ⟨m, rfl⟩ := h3
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨m, by rw [← zpow_natCast g p, ← zpow_mul]⟩

/-- In a cyclic group of order `p²` a subgroup of order `p` contains every element
killed by `p` (it is the unique such subgroup). -/
theorem mem_of_pow_eq_one_of_isCyclic_card_sq [Finite G'] {A B : Subgroup G'} {p : ℕ}
    (hp : p ≠ 0)
    (hAcyc : IsCyclic ↥A) (hAcard : Nat.card ↥A = p * p) (hBA : B ≤ A)
    (hBcard : Nat.card ↥B = p) {x : G'} (hx : x ∈ A) (hxp : x ^ p = 1) : x ∈ B := by
  classical
  obtain ⟨g, hg⟩ := hAcyc.exists_generator
  have hgord : orderOf ((g : G')) = p * p := by
    have hgtop : Subgroup.zpowers g = ⊤ := eq_top_iff.mpr fun y _ => hg y
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers, hgtop, Subgroup.card_top, hAcard]
  have hmemzp : ∀ {y : G'}, y ∈ A → y ∈ Subgroup.zpowers ((g : G')) := by
    intro y hy
    obtain ⟨k, hk⟩ := hg ⟨y, hy⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hgpord : orderOf ((g : G') ^ p) = p := by
    rw [orderOf_pow, hgord, Nat.gcd_eq_right ⟨p, rfl⟩, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hp)]
  have hBle : B ≤ Subgroup.zpowers ((g : G') ^ p) := by
    intro b hb
    refine mem_zpowers_pow_of_pow_eq_one hp hgord (hmemzp (hBA hb)) ?_
    have h := Subgroup.orderOf_dvd_natCard _ hb
    rw [hBcard] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hBeq : B = Subgroup.zpowers ((g : G') ^ p) :=
    Subgroup.eq_of_le_of_card_ge hBle (by rw [Nat.card_zpowers, hgpord, hBcard])
  rw [hBeq]
  exact mem_zpowers_pow_of_pow_eq_one hp hgord (hmemzp hx) hxp

/-- The centralizer of a union is the intersection of the centralizers. -/
theorem centralizer_union (s t : Set G') :
    Subgroup.centralizer (s ∪ t)
      = Subgroup.centralizer s ⊓ Subgroup.centralizer t := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_union]
  exact ⟨fun h => ⟨fun y hy => h y (Or.inl hy), fun y hy => h y (Or.inr hy)⟩,
    fun h y hy => hy.elim (h.1 y) (h.2 y)⟩

end GenericProduct

namespace Hypothesis

universe uG' uΩ'

variable {G : Type uG'} {Ω : Type uΩ'} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

include hyp in
/-- **`⟨Q₀, K, t⟩ ≤ C_G(W)`** (quoted in (15), p. 113: "`L ⊂ ⟨Q₀,K,t⟩ ⊂ C_G(W)`").

All three generators centralize `W`: the elements of `Q₀` are involutions of `H` and
`W = C_D(involutions of H)`; `W = C_V(K)` centralizes `K` by its very definition; and
`W ≤ V = C_D(t)` centralizes `t`. -/
theorem orderThreeGeneratedSubgroup_le_centralizer_W :
    hyp.orderThreeGeneratedSubgroup ≤ Subgroup.centralizer (hyp.W : Set G) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have h := hyp.Q0_le_centralizer_zpowers_of_mem_W hw hx
    exact Subgroup.mem_centralizer_iff.mp h w (Subgroup.mem_zpowers w)
  · intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have hxK : x ∈ hyp.KSet := by rw [← hyp.coe_K]; exact hx
    exact (Subgroup.mem_centralizer_iff.mp hw.2 x hxK).symm
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    exact hyp.commute_t_of_mem_V (hyp.W_le_V hw)

end Hypothesis

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

/-- **`L`** ((15), p. 113): the subgroup `L = C_G(st) ⊓ ⟨Q₀, K, t⟩`.

Under the isomorphism `⟨Q₀, K, t⟩ ≅ PSL(2, 8)` of Ch. I §3, Lemma 4 this is the
centralizer of a semisimple element of order `3`, that is the nonsplit maximal torus,
cyclic of order `q + 1 = 9`. -/
noncomputable def nonsplitTorus : Subgroup G :=
  Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t} : Set G)
    ⊓ fc.toHypothesis.orderThreeGeneratedSubgroup

include fc in
theorem nonsplitTorus_def :
    fc.nonsplitTorus = Subgroup.centralizer ({fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t} : Set G)
      ⊓ fc.toHypothesis.orderThreeGeneratedSubgroup := rfl

include model in
/-- **`L = C_G(st) ⊓ ⟨Q₀, K, t⟩` is cyclic of order `9`** ((15), p. 113).

`⟨Q₀, K, t⟩ ≅ PSL(2, 8)` has order `504`, and its Sylow `3`-subgroups are cyclic of
order `9` (the nonsplit torus).  The one containing `st` is abelian, hence centralizes
`st`, so it lies inside `L`; and `L` is a `3`-group by (13), so `|L|` divides `9`. -/
theorem isCyclic_and_card_nonsplitTorus
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    IsCyclic ↥fc.nonsplitTorus ∧ Nat.card ↥fc.nonsplitTorus = 9 := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  rw [fc.nonsplitTorus_def]
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
theorem zpowers_le_nonsplitTorus :
    Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
      ≤ fc.nonsplitTorus := by
  rw [fc.nonsplitTorus_def]
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
theorem nonsplitTorus_inf_P_eq_bot
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    fc.nonsplitTorus ⊓ fc.P = ⊥ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  obtain ⟨hLcyc, hLcard⟩ := fc.isCyclic_and_card_nonsplitTorus model ind hB2
  set L : Subgroup G := fc.nonsplitTorus with hL_def
  have hZ₁L := fc.zpowers_le_nonsplitTorus
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

include model in
/-- **`P` normalizes `L`** ((15), p. 113, "As `P` normalizes `⟨Q₀, K, t⟩` …").

`P` normalizes `⟨Q₀, K, t⟩` and centralizes `st` (both lie in the abelian group `R`
of (11)), hence normalizes `L = C_G(st) ⊓ ⟨Q₀, K, t⟩`. -/
theorem P_le_normalizer_nonsplitTorus
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    fc.P ≤ Subgroup.normalizer ((fc.nonsplitTorus : Subgroup G) : Set G) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  have habR := fc.invImageF_mul_comm model ind hB2 hm
  have hstR : fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t
      ∈ fc.invImageF model :=
    (fc.sInvertedT_spec model ind hB2 hm).1
      (fc.zpowers_distinguishedInvolution_mul_t_le_sInvertedT model ind hB2 hm
        (Subgroup.mem_zpowers _))
  intro x hxP
  have hxst : Commute x (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) :=
    habR x (fc.P_le_invImageF model hxP) _ hstR
  have hxL₀ := Subgroup.mem_set_normalizer_iff.mp
    (fc.P_le_normalizer_orderThreeGeneratedSubgroup hxP)
  rw [fc.nonsplitTorus_def, Subgroup.mem_set_normalizer_iff]
  intro y
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  constructor
  · rintro ⟨hy1, hy2⟩
    exact ⟨(mem_centralizer_singleton_conj_iff hxst y).mp hy1, (hxL₀ y).mp hy2⟩
  · rintro ⟨hy1, hy2⟩
    exact ⟨(mem_centralizer_singleton_conj_iff hxst y).mpr hy1, (hxL₀ y).mpr hy2⟩

include model in
/-- **`|LP| = 27`** ((15), p. 113): `|L| = 9`, `|P| = 3` and `L ⊓ P = 1`. -/
theorem card_nonsplitTorus_sup_P
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    Nat.card ↥(fc.nonsplitTorus ⊔ fc.P) = 27 := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  obtain ⟨-, hp3, -, -, -, -⟩ := fc.step_twelve model ind hB2
  obtain ⟨-, hLcard⟩ := fc.isCyclic_and_card_nonsplitTorus model ind hB2
  rw [card_sup_eq_mul_of_le_normalizer
      (fun b hb => fc.P_le_normalizer_nonsplitTorus model ind hB2 hb)
      (fc.nonsplitTorus_inf_P_eq_bot model ind hB2),
    hLcard, fc.card_P, hp3]

include model in
/-- **`L` normalizes `Z₁P`** ((15), p. 113): `Z₁P` has index `3` in the group `LP` of
order `27`, hence is normal in it. -/
theorem nonsplitTorus_le_normalizer_zpowers_sup_P
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    fc.nonsplitTorus ≤ Subgroup.normalizer
      ((Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) ⊔ fc.P : Subgroup G) : Set G) := by
  classical
  set M : Subgroup G := fc.nonsplitTorus ⊔ fc.P with hM_def
  set Z : Subgroup G := Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
    * fc.toHypothesis.t) ⊔ fc.P with hZ_def
  have hZM : Z ≤ M :=
    sup_le (fc.zpowers_le_nonsplitTorus.trans le_sup_left) le_sup_right
  have hMcard : Nat.card ↥M = 27 := fc.card_nonsplitTorus_sup_P model ind hB2
  have hZcard : Nat.card ↥Z = 9 := fc.card_zpowers_sup_P_eq_nine model ind hB2
  have hNcard : Nat.card ↥(Z.subgroupOf M) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv]; exact hZcard
  have hidx : (Z.subgroupOf M).index = 3 := by
    have h := (Z.subgroupOf M).card_mul_index
    rw [hNcard, hMcard] at h
    omega
  haveI hnorm : (Z.subgroupOf M).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hMcard]; norm_num)
  have hconj : ∀ g ∈ M, ∀ y ∈ Z, g * y * g⁻¹ ∈ Z := by
    intro g hgM y hyZ
    have h := hnorm.conj_mem ⟨y, hZM hyZ⟩ (by rwa [Subgroup.mem_subgroupOf]) ⟨g, hgM⟩
    rwa [Subgroup.mem_subgroupOf] at h
  intro x hxL
  have hxM : x ∈ M := by rw [hM_def]; exact Subgroup.mem_sup_left hxL
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  refine ⟨fun hy => hconj x hxM y hy, fun hy => ?_⟩
  have h1 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
  rw [← h1]
  exact hconj x⁻¹ (Subgroup.inv_mem _ hxM) _ hy

include model in
/-- **`L ≤ N_G(RΣ)`** ((15), p. 113): `L` normalizes `Z₁P`, hence also its centralizer
`C_G(Z₁P) = C_G(P) ⊓ C_G(st) = RΣ` (quoted in (15), proved in (14)). -/
theorem nonsplitTorus_le_normalizerRSigma
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    fc.nonsplitTorus ≤ fc.normalizerRSigma model := by
  classical
  set Z : Subgroup G := Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
    * fc.toHypothesis.t) ⊔ fc.P with hZ_def
  have hZclosure : Z = Subgroup.closure
      (({fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t} : Set G)
        ∪ (fc.P : Set G)) := by
    rw [hZ_def, Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.closure_eq]
  have hcen : Subgroup.centralizer ((Z : Subgroup G) : Set G)
      = fc.invImageF model
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) := by
    rw [← fc.centralizer_P_inf_centralizer_mul_t_eq_sup model ind hB2, hZclosure,
      Subgroup.centralizer_closure, centralizer_union, inf_comm]
  intro x hx
  have hxn : ∀ y : G, y ∈ Z ↔ x * y * x⁻¹ ∈ Z := by
    have h := Subgroup.mem_set_normalizer_iff.mp
      (fc.nonsplitTorus_le_normalizer_zpowers_sup_P model ind hB2 hx)
    simpa only [SetLike.mem_coe] using h
  change x ∈ Subgroup.normalizer (((fc.invImageF model
    ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) : Subgroup G) : Set G)
  rw [← hcen, Subgroup.mem_set_normalizer_iff]
  intro y
  simpa only [SetLike.mem_coe] using
    mem_normalizer_centralizer_of_mem_normalizer hxn y

include fc in
/-- **`L ≤ C_G(W)`** ((15), p. 113: "`L ⊂ ⟨Q₀,K,t⟩ ⊂ C_G(W)`"). -/
theorem nonsplitTorus_le_centralizer_W :
    fc.nonsplitTorus ≤ Subgroup.centralizer (fc.toHypothesis.W : Set G) :=
  le_trans (by rw [fc.nonsplitTorus_def]; exact inf_le_right)
    fc.toHypothesis.orderThreeGeneratedSubgroup_le_centralizer_W

include model in
/-- **`Z₁` is the `3`-torsion of `L`** ((15), p. 113): `L` is cyclic of order `9`, so
the elements killed by `3` form its unique subgroup of order `3`, which is `Z₁`. -/
theorem mem_zpowers_st_of_mem_nonsplitTorus_of_pow_three
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    {x : G} (hx : x ∈ fc.nonsplitTorus) (hx3 : x ^ 3 = 1) :
    x ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, hp3, -, -, -, -⟩ := fc.step_twelve model ind hB2
  obtain ⟨hLcyc, hLcard⟩ := fc.isCyclic_and_card_nonsplitTorus model ind hB2
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  -- a generator of `L`, viewed in `G`
  obtain ⟨g, hg⟩ := hLcyc.exists_generator
  have hgord : orderOf ((g : G)) = 9 := by
    have hgtop : Subgroup.zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers, hgtop, Subgroup.card_top, hLcard]
  have hmemzp : ∀ {y : G}, y ∈ fc.nonsplitTorus → y ∈ Subgroup.zpowers ((g : G)) := by
    intro y hy
    obtain ⟨k, hk⟩ := hg ⟨y, hy⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  -- `Z₁` and the `3`-torsion both sit inside `⟨g³⟩`, which has order `3`
  have hg3ord : orderOf ((g : G) ^ 3) = 3 := by
    rw [orderOf_pow, hgord]
    norm_num
  have hstmem : fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t
      ∈ Subgroup.zpowers ((g : G) ^ 3) :=
    mem_zpowers_pow_of_pow_eq_one (by norm_num) (by rw [hgord])
      (hmemzp (fc.zpowers_le_nonsplitTorus (Subgroup.mem_zpowers _)))
      (orderOf_dvd_iff_pow_eq_one.mp (by rw [hstord]))
  have hZeq : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = Subgroup.zpowers ((g : G) ^ 3) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hstmem)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hstord, hg3ord])
  rw [hZeq]
  exact mem_zpowers_pow_of_pow_eq_one (by norm_num) (by rw [hgord]) (hmemzp hx) hx3

include model in
/-- **`L ⊓ V = 1`** ((15), p. 113): a nontrivial intersection would contain the unique
subgroup `Z₁` of order `3` of `L`, but `st ∉ H ⊇ V` since `t ∉ H`. -/
theorem nonsplitTorus_inf_V_eq_bot
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    fc.nonsplitTorus ⊓ fc.toHypothesis.V = ⊥ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, hp3, -, -, -, -⟩ := fc.step_twelve model ind hB2
  obtain ⟨-, hLcard⟩ := fc.isCyclic_and_card_nonsplitTorus model ind hB2
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  -- `st ∉ V`: otherwise `t = s⁻¹(st) ∈ H`
  have hstV : fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t
      ∉ fc.toHypothesis.V := by
    intro hmem
    refine fc.toHypothesis.t_not_mem_H ?_
    have hstH : fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t
        ∈ fc.toHypothesis.H :=
      fc.toHypothesis.D_le_H (fc.toHypothesis.V_le_D hmem)
    have h1 : fc.toHypothesis.t = fc.toHypothesis.distinguishedInvolution⁻¹
        * (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) := by group
    rw [h1]
    exact Subgroup.mul_mem _
      (Subgroup.inv_mem _ fc.toHypothesis.distinguishedInvolution_mem_H) hstH
  -- no nontrivial element of `L ⊓ V` is killed by `3`
  have key : ∀ z : G, z ∈ fc.nonsplitTorus → z ∈ fc.toHypothesis.V → z ^ 3 = 1 →
      z = 1 := by
    intro z hzL hzV hz3
    by_contra hz1
    have hzZ := fc.mem_zpowers_st_of_mem_nonsplitTorus_of_pow_three model ind hB2 hzL hz3
    have hzcard : Nat.card ↥(Subgroup.zpowers z) = 3 := by
      have hdvd : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hz3
      rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hz1
      · rw [Nat.card_zpowers, h3]
    have hle : Subgroup.zpowers z ≤ Subgroup.zpowers
        (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) :=
      Subgroup.zpowers_le.mpr hzZ
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hzcard, Nat.card_zpowers, hstord])
    have hstz : fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t
        ∈ Subgroup.zpowers z := by
      rw [heq]; exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := hstz
    exact hstV (hk ▸ zpow_mem hzV k)
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx9 : x ^ 9 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard _ hx.1
    rw [hLcard] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have h3 : x ^ 3 = 1 :=
    key (x ^ 3) (pow_mem hx.1 3) (pow_mem hx.2 3) (by rw [← pow_mul]; exact hx9)
  exact key x hx.1 hx.2 h3

include model in
/-- **`V` normalizes `L`** ((15), p. 113): `W` centralizes `L` and `P` normalizes it,
and `V = WP`. -/
theorem V_le_normalizer_nonsplitTorus
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    fc.toHypothesis.V ≤ Subgroup.normalizer ((fc.nonsplitTorus : Subgroup G) : Set G) := by
  rw [← fc.W_join_P_eq_V]
  refine sup_le ?_ (fc.P_le_normalizer_nonsplitTorus model ind hB2)
  intro w hw
  refine Subgroup.centralizer_le_normalizer _ ?_
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  exact (Subgroup.mem_centralizer_iff.mp (fc.nonsplitTorus_le_centralizer_W hx) w hw).symm

include model in
/-- **`s` inverts `L`** ((15), p. 113): `s` normalizes `L` and `C_L(s) ≤ L ⊓ V = 1`, so
`x · x^s` — an `s`-fixed element of the abelian group `L` — is trivial for every
`x ∈ L`. -/
theorem conj_distinguishedInvolution_eq_inv_of_mem_nonsplitTorus
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    {x : G} (hx : x ∈ fc.nonsplitTorus) :
    fc.toHypothesis.distinguishedInvolution * x * fc.toHypothesis.distinguishedInvolution
      = x⁻¹ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨hLcyc, -⟩ := fc.isCyclic_and_card_nonsplitTorus model ind hB2
  haveI : IsMulCommutative ↥fc.nonsplitTorus := IsCyclic.isMulCommutative
  set s : G := fc.toHypothesis.distinguishedInvolution with hs_def
  have hs2 : s * s = 1 := by rw [← sq]; exact fc.toHypothesis.distinguishedInvolution_sq
  have hsQ0 : s ∈ fc.toHypothesis.Q0 :=
    ⟨fc.toHypothesis.distinguishedInvolution_sq,
      fc.toHypothesis.distinguishedInvolution_mem_H⟩
  -- `s` normalizes `L`
  have hconj : ∀ y : G, y ∈ fc.nonsplitTorus → s * y * s ∈ fc.nonsplitTorus := by
    intro y hy
    rw [fc.nonsplitTorus_def] at hy ⊢
    refine ⟨fc.toHypothesis.conj_mem_centralizer_mul_t y hy.1, ?_⟩
    have hsL₀ : s ∈ fc.toHypothesis.orderThreeGeneratedSubgroup :=
      fc.toHypothesis.orderThree_Q0_le hsQ0
    have h1 : s * y * s = s * y * s⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hs2]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hsL₀ hy.2) (Subgroup.inv_mem _ hsL₀)
  -- `y := x · x^s` is centralized by `s` and lies in `L`, hence in `L ⊓ V = 1`
  set y : G := x * (s * x * s) with hy_def
  have hyL : y ∈ fc.nonsplitTorus := Subgroup.mul_mem _ hx (hconj x hx)
  have hcomm : x * (s * x * s) = (s * x * s) * x := by
    have := ‹IsMulCommutative ↥fc.nonsplitTorus›.is_comm.comm
      (⟨x, hx⟩ : ↥fc.nonsplitTorus) (⟨s * x * s, hconj x hx⟩ : ↥fc.nonsplitTorus)
    exact congrArg Subtype.val this
  have hyfix : s * y * s = y := by
    calc s * (x * (s * x * s)) * s = (s * x * s) * x * (s * s) := by group
      _ = (s * x * s) * x := by rw [hs2, mul_one]
      _ = y := by rw [hy_def, hcomm]
  have hyV : y ∈ fc.toHypothesis.V := by
    rw [← fc.toHypothesis.centralizer_mul_t_inf_centralizer_eq_V]
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · rw [fc.nonsplitTorus_def] at hyL; exact hyL.1
    · have h1 : s * y = y * s := by
        calc s * y = s * (s * y * s) := by rw [hyfix]
          _ = (s * s) * (y * s) := by group
          _ = y * s := by rw [hs2, one_mul]
      exact h1.symm
  have hy1 : y = 1 := by
    have hmem : y ∈ fc.nonsplitTorus ⊓ fc.toHypothesis.V := ⟨hyL, hyV⟩
    rwa [fc.nonsplitTorus_inf_V_eq_bot model ind hB2, Subgroup.mem_bot] at hmem
  have hy1' : x * (s * x * s) = 1 := by rw [← hy_def]; exact hy1
  exact eq_inv_of_mul_eq_one_right hy1'

include model in
/-- **`RΣ` has exponent `3`** ((15), p. 113: `P` fails to centralize `L` "due to the
structure of `C_G(P)` (`TΣ` has exponent `3`)").

Write `x = rσ` with `r ∈ R` and `σ ∈ Σ` (the product decomposition of (11)).  The
commutator `c = ⁅σ, r⁆` lies in `⁅RΣ, RΣ⁆ = Z₁ ≤ Z(RΣ) ⊓ R` by (14), so it is killed
by `3` and commutes with `r`; conjugation by `σ` therefore sends `r` to `cr` and `cr`
to `c²r`, whence `(rσ)³ = r³c³ = 1`. -/
theorem pow_three_eq_one_of_mem_sup_invImageF_centralizer_W
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    {x : G} (hx : x ∈ (fc.invImageF model
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G)) :
    x ^ 3 = 1 := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨hpSig, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  obtain ⟨-, -, -, hSig3, -⟩ :=
    fc.card_field_eq_nine_of_p_dvd_card_centralizer_W ind model hB2 hpSig
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  have hZ₁R : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ≤ fc.invImageF model :=
    (fc.zpowers_distinguishedInvolution_mul_t_le_sInvertedT model ind hB2 hm).trans
      (fc.sInvertedT_spec model ind hB2 hm).1
  have habR := fc.invImageF_mul_comm model ind hB2 hm
  -- `Z₁` is central in `RΣ`
  have hZcen : ∀ z ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t), ∀ y ∈ (fc.invImageF model
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G),
      z * y = y * z := by
    intro z hz y hy
    have hmem : z ∈ (fc.invImageF model
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G)
          ⊓ Subgroup.centralizer (((fc.invImageF model
            ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
              : Subgroup G) : Set G) := by
      rw [fc.inf_centralizer_sup_eq_zpowers_sup_P model ind hB2]
      exact Subgroup.mem_sup_left hz
    exact (Subgroup.mem_centralizer_iff.mp hmem.2 y hy).symm
  -- decompose `x = r·σ`
  have hx' : x ∈ ((fc.invImageF model : Set G)
      * ((fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G) : Subgroup G)
        : Set G)) := by
    rw [← fc.coe_sup_invImageF_centralizer_W model]
    exact hx
  obtain ⟨r, hr, w, hw, rfl⟩ := hx'
  have hrRS : r ∈ (fc.invImageF model
    ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G) :=
    Subgroup.mem_sup_left hr
  have hwRS : w ∈ (fc.invImageF model
    ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G) :=
    Subgroup.mem_sup_right hw
  set c : G := w * r * w⁻¹ * r⁻¹ with hc_def
  have hcmem : c ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) := by
    rw [← fc.commutator_sup_eq_zpowers model ind hB2]
    exact Subgroup.commutator_mem_commutator hwRS hrRS
  have hc3 : c ^ 3 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard _ hcmem
    rw [Nat.card_zpowers, hstord] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hr3 : r ^ 3 = 1 := by
    have h := fc.pow_p_eq_one_of_mem_invImageF model ind hB2 hm hr
    rwa [hp3] at h
  have hw3 : w ^ 3 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard _ hw
    rw [hSig3] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hcomm2 : c * r = r * c := habR c (hZ₁R hcmem) r hr
  have hconj1 : w * r * w⁻¹ = c * r := by rw [hc_def]; group
  have hwc : w * c * w⁻¹ = c := by
    have h := hZcen c hcmem w hwRS
    rw [← h]; group
  have hconj2 : w * (c * r) * w⁻¹ = c * (c * r) := by
    calc w * (c * r) * w⁻¹ = (w * c * w⁻¹) * (w * r * w⁻¹) := by group
      _ = c * (c * r) := by rw [hwc, hconj1]
  have hexpand : (r * w) ^ 3
      = r * (w * r * w⁻¹) * (w * (w * r * w⁻¹) * w⁻¹) * w ^ 3 := by
    rw [pow_three', pow_three']
    group
  rw [hexpand, hconj1, hconj2, hw3, mul_one]
  calc r * (c * r) * (c * (c * r))
      = r * (r * c) * (c * (r * c)) := by rw [hcomm2]
    _ = r * (r * c) * ((c * r) * c) := by group
    _ = r * (r * c) * ((r * c) * c) := by rw [hcomm2]
    _ = (r * r) * (c * r) * (c * c) := by group
    _ = (r * r) * (r * c) * (c * c) := by rw [hcomm2]
    _ = r ^ 3 * c ^ 3 := by rw [pow_three', pow_three']; group
    _ = 1 := by rw [hr3, hc3, one_mul]

include model in
/-- **`L ⊄ RΣ`** ((15), p. 113, and quoted again in (17)): `RΣ` has exponent `3` while
`L` is cyclic of order `9`. -/
theorem not_nonsplitTorus_le_sup_invImageF_centralizer_W
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    ¬ fc.nonsplitTorus ≤ (fc.invImageF model
      ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) : Subgroup G) := by
  intro hle
  obtain ⟨hLcyc, hLcard⟩ := fc.isCyclic_and_card_nonsplitTorus model ind hB2
  obtain ⟨g, hg⟩ := hLcyc.exists_generator
  have hgord : orderOf ((g : G)) = 9 := by
    have hgtop : Subgroup.zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers, hgtop, Subgroup.card_top, hLcard]
  have h3 := fc.pow_three_eq_one_of_mem_sup_invImageF_centralizer_W model ind hB2
    (hle g.2)
  have hdvd := orderOf_dvd_of_pow_eq_one h3
  rw [hgord] at hdvd
  norm_num at hdvd

include model in
/-- **`P` does not centralize `L`** ((15), p. 113): otherwise
`L ≤ C_G(P) ⊓ C_G(st) = RΣ` by (14), contradicting `L ⊄ RΣ`. -/
theorem not_nonsplitTorus_le_centralizer_P
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    ¬ fc.nonsplitTorus ≤ Subgroup.centralizer (fc.P : Set G) := by
  intro hle
  refine fc.not_nonsplitTorus_le_sup_invImageF_centralizer_W model ind hB2 ?_
  rw [← fc.centralizer_P_inf_centralizer_mul_t_eq_sup model ind hB2]
  intro x hx
  refine ⟨hle hx, ?_⟩
  rw [fc.nonsplitTorus_def] at hx
  exact hx.1

include model in
/-- **`L ≤ R₁`** ((15), p. 113): every element of `L` is a `3`-element of `N_G(RΣ)`,
and `R₁` is by definition generated by those. -/
theorem nonsplitTorus_le_sylowThreeNormalizerRSigma
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    fc.nonsplitTorus ≤ fc.sylowThreeNormalizerRSigma model := by
  obtain ⟨-, hLcard⟩ := fc.isCyclic_and_card_nonsplitTorus model ind hB2
  intro x hx
  rw [fc.sylowThreeNormalizerRSigma_def model]
  refine Subgroup.subset_closure
    ⟨fc.nonsplitTorus_le_normalizerRSigma model ind hB2 hx, ?_⟩
  have hdvd := Subgroup.orderOf_dvd_natCard _ hx
  rw [hLcard, show (9 : ℕ) = 3 ^ 2 by norm_num] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num)).mp hdvd
  exact ⟨j, hj⟩

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
