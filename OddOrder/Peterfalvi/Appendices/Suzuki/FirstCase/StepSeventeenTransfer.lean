/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepSeventeen
import OddOrder.Isaacs.Ch10_MoreTransfer.Yoshida
import OddOrder.GroupTheory.TransferIndexTwo
import OddOrder.GroupTheory.WeaklyClosed

/-!
# Peterfalvi Part II, Ch. II, step (17): control of the `3`-transfer

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (17), p. 114.

Peterfalvi invokes the Hall–Wielandt theorem for the abelian, weakly closed subgroup
`Z₁PΣ` of the Sylow `3`-subgroup `R₂`.  Since `N_G(Z₁PΣ) = N_G(Z₁) = R₂⟨s⟩ = N_G(R₂)`
(`normalizer_sylow_eq`), what is needed is exactly that **the normaliser of a Sylow
`3`-subgroup controls the `3`-transfer**, which is the setting of Yoshida's theorem
(`OddOrder.Isaacs.Ch10.exists_surjective_wreath_of_transfer_range_lt`): control fails
only if `R₂` has a quotient isomorphic to `C₃ ≀ C₃`.

Moreover `R₂ ⊴ R₂⟨s⟩` has index `2`, so the `N`-level transfer is computed by hand
(`transfer_eq_mul_conj_of_index_two`) and no focal-subgroup machinery is needed:
a trivial transfer says that `s` inverts `R₂` modulo `⁅N, N⁆`, which for a group of
odd order forces `R₂ ≤ ⁅N, N⁆`, i.e. `3 ∤ |N^{ab}|`.

See issue 9503.
-/

set_option autoImplicit false

open scoped Pointwise commutatorElement

namespace OddOrder.Peterfalvi.Appendices.Suzuki

section /- Generic group theory -/

variable {A B : Type*} [Group A] [Group B]

/-- If the `n`-th term of the lower central series of `A` lies in the kernel of a
surjection `f : A →* B`, then the `n`-th term for `B` is trivial (so the nilpotence
class of `B` is at most `n`). -/
theorem lowerCentralSeries_eq_bot_of_le_ker (f : A →* B)
    (hf : Function.Surjective f) {n : ℕ}
    (h : Subgroup.lowerCentralSeries (⊤ : Subgroup A) n ≤ f.ker) :
    Subgroup.lowerCentralSeries (⊤ : Subgroup B) n = ⊥ := by
  have htop : (⊤ : Subgroup A).map f = ⊤ := Subgroup.map_top_of_surjective f hf
  rw [← htop, ← Subgroup.map_lowerCentralSeries, eq_bot_iff]
  refine (Subgroup.map_le_iff_le_comap).mpr ?_
  rwa [MonoidHom.comap_bot]

/-- An element of order `3` all of whose conjugates lie in `⟨z⟩` is central, provided
every element of the group has odd order: conjugation by `g` either fixes `z` or
inverts it, and inversion cannot be induced by an element of odd order. -/
theorem mem_center_of_conj_mem_zpowers_of_orderOf_eq_three {z : A} (hz : orderOf z = 3)
    (hodd : ∀ g : A, Odd (orderOf g))
    (hconj : ∀ g : A, g * z * g⁻¹ ∈ Subgroup.zpowers z) :
    z ∈ Subgroup.center A := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  -- conjugation by `g` fixes or inverts `z`
  have hcases := eq_one_or_eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three hz (hconj g)
  have hconj_eq : g * z * g⁻¹ = z := by
    rcases hcases with h1 | h2 | h3
    · exfalso
      apply hz1
      have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [this, h1]
      group
    · exact h2
    · -- `g` inverts `z`; iterating an odd number of times gives `z = z⁻¹`
      exfalso
      have hpow : ∀ n : ℕ, g ^ n * z * (g ^ n)⁻¹ = if Even n then z else z⁻¹ := by
        intro n
        induction n with
        | zero => simp
        | succ m ih =>
          have hstep : g ^ (m + 1) * z * (g ^ (m + 1))⁻¹
              = g * (g ^ m * z * (g ^ m)⁻¹) * g⁻¹ := by
            rw [pow_succ']
            group
          rw [hstep, ih]
          by_cases hm : Even m
          · rw [if_pos hm, if_neg (by simp [Nat.even_add_one, hm])]
            exact h3
          · rw [if_neg hm, if_pos (by simp [Nat.even_add_one, hm])]
            rw [show g * z⁻¹ * g⁻¹ = (g * z * g⁻¹)⁻¹ by group, h3, inv_inv]
      obtain ⟨k, hk⟩ := hodd g
      have hgn : g ^ orderOf g = 1 := pow_orderOf_eq_one g
      have hne : ¬ Even (orderOf g) := by
        rw [hk]
        simp [parity_simps]
      have hfix := hpow (orderOf g)
      rw [hgn, if_neg hne] at hfix
      simp only [one_mul, inv_one, mul_one] at hfix
      have hz2 : z * z = 1 := by
        nth_rewrite 1 [hfix]
        exact inv_mul_cancel z
      have : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
      rw [hz] at this
      omega
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [hconj_eq]

/-- If a subgroup `X` of `A` maps onto `B` and the `n`-th term of its lower central
series (computed in `A`) lies in the kernel, then the `n`-th term for `B` is trivial. -/
theorem lowerCentralSeries_eq_bot_of_subgroup_le_ker (f : A →* B) {X : Subgroup A}
    (hX : X.map f = ⊤) {n : ℕ} (h : Subgroup.lowerCentralSeries X n ≤ f.ker) :
    Subgroup.lowerCentralSeries (⊤ : Subgroup B) n = ⊥ := by
  rw [← hX, ← Subgroup.map_lowerCentralSeries, eq_bot_iff]
  refine (Subgroup.map_le_iff_le_comap).mpr ?_
  rwa [MonoidHom.comap_bot]

/-- **A nontrivial normal subgroup of a finite `p`-group meets the centre.**
The group acts on the normal subgroup by conjugation, and a `p`-group action on a
set of size divisible by `p` with a fixed point has a second fixed point. -/
theorem exists_mem_center_of_normal_ne_bot {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] (hP : IsPGroup p P) {K : Subgroup P} [K.Normal] (hK : K ≠ ⊥) :
    ∃ z : P, z ∈ K ∧ z ≠ 1 ∧ z ∈ Subgroup.center P := by
  classical
  letI : MulAction P ↥K := MulAction.compHom ↥K (MulAut.conjNormal (H := K))
  have hsmul : ∀ (g : P) (k : ↥K), ((g • k : ↥K) : P) = g * (k : P) * g⁻¹ := by
    intro g k
    exact MulAut.conjNormal_apply g k
  -- `p` divides `|K|`
  have hpK : p ∣ Nat.card ↥K := by
    obtain ⟨z₀, hz₀K, hz₀1⟩ : ∃ z ∈ K, z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hK (eq_bot_iff.mpr fun y hy => Subgroup.mem_bot.mpr (hcon y hy))
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) z₀
    have hk0 : k ≠ 0 := by
      intro h
      rw [h, pow_zero, orderOf_eq_one_iff] at hk
      exact hz₀1 hk
    have hdvd : orderOf (⟨z₀, hz₀K⟩ : ↥K) ∣ Nat.card ↥K := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hk] at hdvd
    exact dvd_trans (dvd_pow_self p hk0) hdvd
  have h1 : (1 : ↥K) ∈ MulAction.fixedPoints P ↥K := by
    intro g
    refine Subtype.ext ?_
    rw [hsmul]
    simp
  obtain ⟨b, hbfix, hb1⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥K hpK h1
  refine ⟨(b : P), b.2, ?_, ?_⟩
  · intro hb
    exact hb1 (Subtype.ext hb.symm)
  · rw [Subgroup.mem_center_iff]
    intro g
    have := hbfix g
    have hcoe : g * (b : P) * g⁻¹ = (b : P) := by
      rw [← hsmul g b, this]
    calc g * (b : P) = (g * (b : P) * g⁻¹) * g := by group
      _ = (b : P) * g := by rw [hcoe]

/-- If a subgroup `X` and the kernel of a surjection `f` generate `A`, then `X` already
maps onto `B`. -/
theorem map_eq_top_of_sup_ker_eq_top (f : A →* B) (hf : Function.Surjective f)
    {X : Subgroup A} (hX : X ⊔ f.ker = ⊤) : X.map f = ⊤ := by
  have hker : (f.ker).map f = ⊥ :=
    le_antisymm (Subgroup.map_le_iff_le_comap.mpr (by rw [MonoidHom.comap_bot])) bot_le
  calc X.map f = X.map f ⊔ (f.ker).map f := by rw [hker, sup_bot_eq]
    _ = (X ⊔ f.ker).map f := (Subgroup.map_sup _ _ _).symm
    _ = ⊤ := by rw [hX, Subgroup.map_top_of_surjective f hf]

/-- A subgroup of prime index is maximal: it generates the whole group together with
any subgroup it does not contain. -/
theorem sup_eq_top_of_index_prime {X K : Subgroup A} {p : ℕ} (hp : p.Prime)
    (hX : X.index = p) (hK : ¬ K ≤ X) : X ⊔ K = ⊤ := by
  have hle : X ≤ X ⊔ K := le_sup_left
  have hmul := Subgroup.relIndex_mul_index hle
  have hdvd : (X ⊔ K).index ∣ p := hX ▸ Subgroup.index_dvd_of_le hle
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    rw [hp', hX] at hmul
    have hone : X.relIndex (X ⊔ K) = 1 :=
      Nat.eq_of_mul_eq_mul_right hp.pos (by rw [hmul, one_mul])
    exact hK (le_trans le_sup_right (Subgroup.relIndex_eq_one.mp hone))

/-- `C₃ ≀ C₃` has order `3⁴`. -/
theorem card_wreathThree :
    Nat.card (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) = 3 ^ 4 := by
  rw [RegularWreathProduct.card]
  have h1 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [h1]
  norm_num

/-- `C₃ ≀ C₃` is a finite `3`-group, hence nilpotent. -/
theorem isNilpotent_wreathThree :
    Group.IsNilpotent (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact (IsPGroup.of_card card_wreathThree).isNilpotent

/-- **No `C₃ ≀ C₃` quotient from a subgroup of class `≤ 2` that supplements the kernel.**
If `X` supplements `ker f` and `⁅⁅X, X⁆, X⁆ ≤ ker f`, then `f` cannot be onto `C₃ ≀ C₃`,
whose nilpotence class is `3`. -/
theorem false_of_wreathThree_quotient
    (f : A →* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)))
    (hf : Function.Surjective f) {X : Subgroup A} (hX : X ⊔ f.ker = ⊤)
    (h : Subgroup.lowerCentralSeries X 2 ≤ f.ker) : False := by
  haveI := isNilpotent_wreathThree
  have hbot := lowerCentralSeries_eq_bot_of_subgroup_le_ker f
    (map_eq_top_of_sup_ker_eq_top f hf hX) h
  have hcls := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hbot
  rw [OddOrder.Isaacs.Ch10.nilpotencyClass_wreath 3] at hcls
  omega

/-- The commutator subgroup lies in every normal subgroup of prime index (the quotient
is cyclic of prime order, hence abelian). -/
theorem commutator_le_of_index_prime [Finite A] {H : Subgroup A} [H.Normal] {p : ℕ}
    [Fact p.Prime] (hH : H.index = p) : commutator A ≤ H := by
  have hQcard : Nat.card (A ⧸ H) = p := by rw [← Subgroup.index_eq_card, hH]
  haveI : IsCyclic (A ⧸ H) := isCyclic_of_prime_card hQcard
  letI : CommGroup (A ⧸ H) := IsCyclic.commGroup
  have hker := Abelianization.commutator_subset_ker (QuotientGroup.mk' H)
  rwa [QuotientGroup.ker_mk'] at hker

/-- **Two subgroups of index `3` that are abelian modulo the kernel cannot produce a
`C₃ ≀ C₃` quotient.**  The images `X̄`, `Ȳ` are abelian of index `3`, so
`⁅Q, Q⁆ ≤ X̄ ⊓ Ȳ`, while `X̄ ⊓ Ȳ` is centralised by both `X̄` and `Ȳ` and hence lies in
`Z(Q)`; the quotient would have nilpotence class at most `2`, not `3`. -/
theorem false_of_two_abelian_of_index_three
    (f : A →* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)))
    (hf : Function.Surjective f) {X Y : Subgroup A} (hXY : X ⊔ Y = ⊤)
    (hXidx : X.index = 3) (hYidx : Y.index = 3)
    (hkX : f.ker ≤ X) (hkY : f.ker ≤ Y)
    (hX : ⁅X, X⁆ ≤ f.ker) (hY : ⁅Y, Y⁆ ≤ f.ker) : False := by
  classical
  haveI := isNilpotent_wreathThree
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- the images are abelian
  have habel : ∀ {Z : Subgroup A}, ⁅Z, Z⁆ ≤ f.ker →
      ∀ a ∈ Z.map f, ∀ b ∈ Z.map f, a * b = b * a := by
    intro Z hZ a ha b hb
    have hbot : ⁅Z.map f, Z.map f⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, eq_bot_iff]
      exact Subgroup.map_le_iff_le_comap.mpr (by rwa [MonoidHom.comap_bot])
    have := Subgroup.commutator_le.mp (le_of_eq hbot) a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  -- the images have index `3`, hence are normal with abelian quotient
  have hidxX : (X.map f).index = 3 := by rw [Subgroup.index_map_eq _ hf hkX, hXidx]
  have hidxY : (Y.map f).index = 3 := by rw [Subgroup.index_map_eq _ hf hkY, hYidx]
  have hmin : (Nat.card (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))).minFac = 3 := by
    rw [card_wreathThree]
    norm_num
  haveI : (X.map f).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hidxX, hmin])
  haveI : (Y.map f).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hidxY, hmin])
  have hcommX := commutator_le_of_index_prime (H := X.map f) hidxX
  have hcommY := commutator_le_of_index_prime (H := Y.map f) hidxY
  -- the intersection is central
  have hcen : X.map f ⊓ Y.map f ≤ Subgroup.center _ := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ (X.map f) ⊔ (Y.map f) := by
      rw [← Subgroup.map_sup, hXY, Subgroup.map_top_of_surjective f hf]
      exact Subgroup.mem_top g
    have hgen : Subgroup.closure ((X.map f : Set _) ∪ (Y.map f : Set _))
        = X.map f ⊔ Y.map f := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    refine Subgroup.closure_induction (p := fun u _ => u * z = z * u) ?_ ?_ ?_ ?_
      (by rw [hgen]; exact hg)
    · rintro u (hu | hu)
      · exact habel hX u hu z hz.1
      · exact habel hY u hu z hz.2
    · group
    · intro u v _ _ hu hv
      calc u * v * z = u * (v * z) := by group
        _ = u * (z * v) := by rw [hv]
        _ = (u * z) * v := by group
        _ = (z * u) * v := by rw [hu]
        _ = z * (u * v) := by group
    · intro u _ hu
      have : u⁻¹ * (u * z) * u⁻¹ = u⁻¹ * (z * u) * u⁻¹ := by rw [hu]
      calc u⁻¹ * z = u⁻¹ * (z * u) * u⁻¹ := by group
        _ = u⁻¹ * (u * z) * u⁻¹ := by rw [this]
        _ = z * u⁻¹ := by group
  -- hence the class is at most `2`
  have hbot : Subgroup.lowerCentralSeries
      (⊤ : Subgroup (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) 2 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
      Subgroup.lowerCentralSeries_zero, eq_bot_iff, Subgroup.commutator_le]
    intro a ha b _
    have haX : a ∈ X.map f ⊓ Y.map f :=
      ⟨hcommX (by rwa [commutator_def]), hcommY (by rwa [commutator_def])⟩
    have := Subgroup.mem_center_iff.mp (hcen haX) b
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact this.symm
  have hcls := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hbot
  rw [OddOrder.Isaacs.Ch10.nilpotencyClass_wreath 3] at hcls
  omega

/-- The centre of a subgroup, viewed inside the ambient group, is the intersection of
the subgroup with its centraliser. -/
theorem map_center_subtype (H : Subgroup A) :
    (Subgroup.center ↥H).map H.subtype = H ⊓ Subgroup.centralizer (H : Set A) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨u, hu⟩)
  · rintro ⟨hxH, hxC⟩
    refine ⟨⟨x, hxH⟩, Subgroup.mem_center_iff.mpr fun u => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (u : A) u.2)

end

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

include model in
/-- **The normaliser of the Sylow `3`-subgroup has no quotient of order `3`** ((17),
p. 114), the transfer-control input of `false_of_transfer_control` (issue 9503).

The proof has two halves.

* *Yoshida.*  Unless `R₂` maps onto `C₃ ≀ C₃`, the image of the `G`-transfer to
  `R₂^{ab}` agrees with the image of the `N`-level transfer (`N = N_G(R₂)`); by (B2)
  the former is trivial, so the `N`-transfer is trivial.
* *Index two.*  `R₂ ⊴ N` with `N = R₂⟨s⟩` of index `2`, so the `N`-transfer of
  `x ∈ R₂` is `π(x)·π(x^s)` with `π : R₂ → R₂^{ab}`.  Its triviality says that
  `x·x^s ∈ ⁅N, N⁆` for all `x ∈ R₂`, and since `|R₂|` is odd this forces
  `R₂ ≤ ⁅N, N⁆`; as `[N : R₂] = 2`, the abelianisation of `N` is a `2`-group. -/
theorem not_three_dvd_card_abelianization_normalizer_sylow
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G))
    (hwreath : ∀ φ : ↥(S : Subgroup G) →*
        (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)), ¬ Function.Surjective φ) :
    ¬ (3 : ℕ) ∣ Nat.card (Abelianization
      ↥(Subgroup.normalizer (((S : Subgroup G)) : Set G))) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, hp3, -, -, -, -⟩ := fc.step_twelve model ind hB2
  have hB2' : ¬ (3 : ℕ) ∣ Nat.card (Abelianization G) := by rwa [hp3] at hB2
  set s : G := fc.toHypothesis.distinguishedInvolution with hs_def
  set N : Subgroup G := Subgroup.normalizer (((S : Subgroup G)) : Set G) with hN_def
  have hSN : (S : Subgroup G) ≤ N := Subgroup.le_normalizer
  have hNeq : N = (S : Subgroup G) ⊔ Subgroup.zpowers s :=
    fc.normalizer_sylow_eq model ind hB2 S hR₁S
  have hsN : s ∈ N := by
    rw [hNeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hsord : orderOf s = 2 :=
    orderOf_eq_prime fc.toHypothesis.distinguishedInvolution_sq
      fc.toHypothesis.distinguishedInvolution_ne_one
  have hs2 : s * s = 1 := by
    rw [← pow_two]
    exact fc.toHypothesis.distinguishedInvolution_sq
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  -- `s` is not in the `3`-group `S`
  have hsS : s ∉ (S : Subgroup G) := by
    intro hmem
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.2) (⟨s, hmem⟩ : ↥(S : Subgroup G))
    rw [Subgroup.orderOf_mk, hsord] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp at hk
    · have h1 : (3 : ℕ) ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hkpos
      omega
  -- `N = S⟨s⟩` has twice the order of `S`
  have hinf : (S : Subgroup G) ⊓ Subgroup.zpowers s = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.2) (⟨y, hy.1⟩ : ↥(S : Subgroup G))
    rw [Subgroup.orderOf_mk] at hk
    have hdvd2 : orderOf y ∣ 2 := by
      rw [← hsord]
      exact orderOf_dvd_of_mem_zpowers hy.2
    rw [hk] at hdvd2
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    · exfalso
      have h1 : (3 : ℕ) ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hkpos
      have h2 : (3 : ℕ) ^ k ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
      omega
  have hNcard : Nat.card ↥N = Nat.card ↥(S : Subgroup G) * 2 := by
    rw [hNeq, card_sup_eq_mul_of_le_normalizer (A := (S : Subgroup G)) ?_ hinf,
      Nat.card_zpowers, hsord]
    intro b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact N.zpow_mem hsN m
  -- the subgroup `H = S` of `N`, of index `2`
  set H : Subgroup ↥N := (S : Subgroup G).subgroupOf N with hH_def
  have hHcard : Nat.card ↥H = Nat.card ↥(S : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  have hScard_pos : 0 < Nat.card ↥(S : Subgroup G) := Nat.card_pos
  have hidx : H.index = 2 := by
    have h := H.card_mul_index
    rw [hHcard, hNcard] at h
    exact Nat.eq_of_mul_eq_mul_left hScard_pos h
  haveI : H.FiniteIndex := ⟨by rw [hidx]; norm_num⟩
  -- membership bookkeeping
  have hmemH : ∀ x : ↥N, x ∈ H ↔ ((x : G) ∈ (S : Subgroup G)) := fun x => Subgroup.mem_subgroupOf
  set σ : ↥N := ⟨s, hsN⟩ with hσ_def
  have hσinv : σ⁻¹ = σ := by
    refine inv_eq_of_mul_eq_one_right ?_
    ext
    exact hs2
  have hσH : σ ∉ H := by
    rw [hmemH]
    exact hsS
  have hconj : ∀ x : ↥N, x ∈ H → ∀ g : ↥N, g⁻¹ * x * g ∈ H := by
    intro x hx g
    rw [hmemH] at hx ⊢
    have hg : (g : G) ∈ Subgroup.normalizer (((S : Subgroup G)) : Set G) := g.2
    rw [Subgroup.mem_set_normalizer_iff] at hg
    have := (hg ((g : G)⁻¹ * (x : G) * (g : G))).mpr
    push_cast
    refine this ?_
    rw [show (g : G) * ((g : G)⁻¹ * (x : G) * (g : G)) * (g : G)⁻¹ = (x : G) by group]
    exact hx
  -- the coefficient map and the two transfers
  set π : ↥(S : Subgroup G) →* Abelianization ↥(S : Subgroup G) :=
    Abelianization.of with hπ_def
  set ϕ : ↥H →* Abelianization ↥(S : Subgroup G) :=
    OddOrder.GroupTheory.transferRes Subgroup.le_normalizer π with hϕ_def
  have hle : (MonoidHom.transfer π).range ≤ (MonoidHom.transfer ϕ).range := by
    rw [hϕ_def, ← OddOrder.GroupTheory.transfer_transfer Subgroup.le_normalizer π]
    exact OddOrder.GroupTheory.transfer_range_le _
  have hnotlt : ¬ (MonoidHom.transfer π).range < (MonoidHom.transfer ϕ).range := by
    intro hlt
    obtain ⟨ψ, hψ⟩ :=
      OddOrder.Isaacs.Ch10.exists_surjective_wreath_of_transfer_range_lt S hlt
    exact hwreath ψ hψ
  have hrange : (MonoidHom.transfer ϕ).range = ⊥ := by
    rw [← hle.eq_of_not_lt hnotlt]
    exact OddOrder.GroupTheory.transfer_abelianization_range_eq_bot S.2 hB2'
  have hw1 : ∀ x : ↥N, MonoidHom.transfer ϕ x = 1 := by
    intro x
    have : MonoidHom.transfer ϕ x ∈ (MonoidHom.transfer ϕ).range := ⟨x, rfl⟩
    rw [hrange, Subgroup.mem_bot] at this
    exact this
  -- a trivial transfer says that `s` inverts `S` modulo `⁅N, N⁆`
  have hcommS : (commutator ↥(S : Subgroup G)).map (Subgroup.inclusion hSN)
      ≤ commutator ↥N := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hstep : ∀ x : ↥N, x ∈ H → x * (σ * x * σ⁻¹) ∈ commutator ↥N := by
    intro x hx
    have hxS : ((x : G)) ∈ (S : Subgroup G) := (hmemH x).mp hx
    have hkey := OddOrder.GroupTheory.transfer_eq_mul_conj_of_index_two ϕ hidx hx
      (hconj x hx) hσH
    rw [hw1 x] at hkey
    have hyH : σ⁻¹ * x * σ ∈ H := hconj x hx σ
    have hyS : (((σ⁻¹ * x * σ : ↥N)) : G) ∈ (S : Subgroup G) := (hmemH _).mp hyH
    -- the transfer value is the abelianisation class of `x · x^s`
    have hprod : (⟨(x : G), hxS⟩ : ↥(S : Subgroup G))
        * ⟨((σ⁻¹ * x * σ : ↥N) : G), hyS⟩ ∈ commutator ↥(S : Subgroup G) := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul]
      exact hkey.symm
    have himg := hcommS (Subgroup.mem_map_of_mem (Subgroup.inclusion hSN) hprod)
    have hcoe : (Subgroup.inclusion hSN ((⟨(x : G), hxS⟩ : ↥(S : Subgroup G))
        * ⟨((σ⁻¹ * x * σ : ↥N) : G), hyS⟩) : ↥N) = x * (σ * x * σ⁻¹) := by
      ext
      change (x : G) * ((σ⁻¹ * x * σ : ↥N) : G) = (x : G) * ((σ * x * σ⁻¹ : ↥N) : G)
      rw [hσinv]
    rwa [hcoe] at himg
  have hodd : ∀ x : ↥N, x ∈ H → Odd (orderOf x) := by
    intro x hx
    have hxS : ((x : G)) ∈ (S : Subgroup G) := (hmemH x).mp hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.2) (⟨(x : G), hxS⟩ : ↥(S : Subgroup G))
    rw [Subgroup.orderOf_mk] at hk
    rw [← Subgroup.orderOf_coe x, hk]
    exact Odd.pow ⟨1, by norm_num⟩
  have hleC : H ≤ commutator ↥N :=
    OddOrder.GroupTheory.le_commutator_of_conj_mul_mem hodd hstep
  exact OddOrder.GroupTheory.not_dvd_card_abelianization_of_le_commutator hidx hleC
    (by norm_num) ⟨1, by norm_num⟩

include model in
/-- **`⁅W, P⁆ ≤ Σ`**: `W` is cyclic with `w⁹ = 1`, `P` normalises `W`, and `P`
centralises `W³ ≤ Σ` (`mem_sigma_of_mem_W_of_pow_three`), so the commutator
`⁅w, q⁆ = w·(w⁻¹)^q` — a product of two commuting elements of `W` — cubes to
`w³·(w⁻³)^q = 1`. -/
theorem commutatorElement_mem_sigma_of_mem_W_of_mem_P
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {w q : G}
    (hw : w ∈ fc.toHypothesis.W) (hq : q ∈ fc.P) :
    ⁅w, q⁆ ∈ fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, -, -, hWcyc, hWcard, -⟩ := fc.step_twelve model ind hB2
  have hnorm : ∀ y ∈ fc.toHypothesis.W, q * y * q⁻¹ ∈ fc.toHypothesis.W := by
    intro y hy
    have hn := fc.P_le_normalizer_W hq
    rw [Subgroup.mem_normalizer_iff] at hn
    exact (hn y).mp hy
  have hu : q * w⁻¹ * q⁻¹ ∈ fc.toHypothesis.W :=
    hnorm _ (fc.toHypothesis.W.inv_mem hw)
  have hcomm : ⁅w, q⁆ = w * (q * w⁻¹ * q⁻¹) := by
    rw [commutatorElement_def]
    group
  have hmemW : ⁅w, q⁆ ∈ fc.toHypothesis.W := by
    rw [hcomm]
    exact fc.toHypothesis.W.mul_mem hw hu
  refine fc.mem_sigma_of_mem_W_of_pow_three model ind hB2 hmemW ?_
  -- `w⁹ = 1`, so `w³` is centralised by `q`
  have hw9 : w ^ 9 = 1 := by
    have hord : orderOf (⟨w, hw⟩ : ↥fc.toHypothesis.W) ∣ Nat.card ↥fc.toHypothesis.W :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hord
    have h9 : Nat.card ↥fc.toHypothesis.W ∣ 9 := by
      rcases hWcard with h3 | h9
      · rw [h3]; norm_num
      · rw [h9]
    exact orderOf_dvd_iff_pow_eq_one.mp (hord.trans h9)
  have hw3sig : w ^ 3 ∈ fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G) := by
    refine fc.mem_sigma_of_mem_W_of_pow_three model ind hB2
      (fc.toHypothesis.W.pow_mem hw 3) ?_
    rw [← pow_mul]
    exact hw9
  have hcen : q * w ^ 3 * q⁻¹ = w ^ 3 := by
    have hqc := Subgroup.mem_centralizer_iff.mp hw3sig.2 q hq
    calc q * w ^ 3 * q⁻¹ = (w ^ 3 * q) * q⁻¹ := by rw [← hqc]
      _ = w ^ 3 := by group
  -- the two factors commute, so the cube splits
  have hcommute := mul_comm_of_mem_of_isCyclic hWcyc hw hu
  rw [hcomm, Commute.mul_pow (hcommute : Commute w (q * w⁻¹ * q⁻¹)) 3]
  have hu3 : (q * w⁻¹ * q⁻¹) ^ 3 = q * (w ^ 3)⁻¹ * q⁻¹ := by
    rw [conj_pow, ← inv_pow]
  rw [hu3, show q * (w ^ 3)⁻¹ * q⁻¹ = (q * w ^ 3 * q⁻¹)⁻¹ by group, hcen]
  exact mul_inv_cancel _

include model in
/-- **`⁅LV, LV⁆ ≤ Z₁Σ = Z(LV)`**: `L` centralises `W`, `⁅P, L⁆ ≤ Z₁` (16) and
`⁅W, P⁆ ≤ Σ`, while `L`, `W`, `P` are each abelian. -/
theorem commutator_sup_nonsplitTorus_V_le
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    ⁅fc.nonsplitTorus ⊔ fc.toHypothesis.V, fc.nonsplitTorus ⊔ fc.toHypothesis.V⁆
      ≤ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨-, -, -, hWcyc, -, -⟩ := fc.step_twelve model ind hB2
  have hLcyc := (fc.isCyclic_and_card_nonsplitTorus model ind hB2).1
  haveI : Fact (Nat.Prime fc.p) := ⟨fc.p_prime⟩
  haveI hPcyc : IsCyclic ↥fc.P := isCyclic_of_prime_card fc.card_P
  have hZLV := fc.inf_centralizer_sup_nonsplitTorus_V_eq model ind hB2
  refine commutator_le_of_generators (T := ((fc.nonsplitTorus : Set G)
    ∪ (fc.toHypothesis.W : Set G)) ∪ (fc.P : Set G)) ?_ ?_ ?_
  · rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq,
      Subgroup.closure_eq, Subgroup.closure_eq, sup_assoc, fc.W_join_P_eq_V]
  · intro x hx f hf
    have hfC : f ∈ Subgroup.centralizer ((fc.nonsplitTorus ⊔ fc.toHypothesis.V : Subgroup G)
        : Set G) := by
      have : f ∈ (fc.nonsplitTorus ⊔ fc.toHypothesis.V)
          ⊓ Subgroup.centralizer ((fc.nonsplitTorus ⊔ fc.toHypothesis.V : Subgroup G)
            : Set G) := by
        rw [hZLV]
        exact hf
      exact this.2
    have hcomm := Subgroup.mem_centralizer_iff.mp hfC x hx
    rw [hcomm, mul_inv_cancel_right]
    exact hf
  · -- the base commutators
    have hZ₁le : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) ≤ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t) ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) :=
      le_sup_left
    have hSigle : fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)
        ≤ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t) ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) :=
      le_sup_right
    have hone : ∀ a b : G, a * b = b * a → ⁅a, b⁆ ∈ Subgroup.zpowers
        (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) := by
      intro a b hab
      rw [show ⁅a, b⁆ = 1 by rw [commutatorElement_def, hab]; group]
      exact Subgroup.one_mem _
    have hLP : ∀ a ∈ fc.nonsplitTorus, ∀ b ∈ fc.P, ⁅a, b⁆ ∈ Subgroup.zpowers
        (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) := by
      intro a ha b hb
      have h := fc.commutatorElement_mem_zpowers_of_mem_P_of_mem_nonsplitTorus model ind hB2
        hb ha
      rw [show ⁅a, b⁆ = ⁅b, a⁆⁻¹ by rw [commutatorElement_def, commutatorElement_def]; group]
      exact Subgroup.inv_mem _ (hZ₁le h)
    have hWP : ∀ a ∈ fc.toHypothesis.W, ∀ b ∈ fc.P, ⁅a, b⁆ ∈ Subgroup.zpowers
        (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) := fun a ha b hb =>
      hSigle (fc.commutatorElement_mem_sigma_of_mem_W_of_mem_P model ind hB2 ha hb)
    have hinv : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.zpowers
        (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) →
        ⁅b, a⁆ ∈ Subgroup.zpowers
        (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) := by
      intro a b h
      rw [show ⁅b, a⁆ = ⁅a, b⁆⁻¹ by rw [commutatorElement_def, commutatorElement_def]; group]
      exact Subgroup.inv_mem _ h
    rintro a (ha | ha) b (hb | hb)
    · rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hone a b (mul_comm_of_mem_of_isCyclic hLcyc ha hb)
      · exact hone a b (Subgroup.mem_centralizer_iff.mp
          (fc.nonsplitTorus_le_centralizer_W ha) b hb).symm
      · exact hone a b (Subgroup.mem_centralizer_iff.mp
          (fc.nonsplitTorus_le_centralizer_W hb) a ha)
      · exact hone a b (mul_comm_of_mem_of_isCyclic hWcyc ha hb)
    · rcases ha with ha | ha
      · exact hLP a ha b hb
      · exact hWP a ha b hb
    · rcases hb with hb | hb
      · exact hinv b a (hLP b hb a ha)
      · exact hinv b a (hWP b hb a ha)
    · exact hone a b (mul_comm_of_mem_of_isCyclic hPcyc ha hb)

include model in
/-- **`LV` has nilpotence class at most `2`** ((17) support): `⁅LV, LV⁆ ≤ Z₁Σ` and
`Z₁Σ = Z(LV)` centralises `LV`, so `⁅⁅LV, LV⁆, LV⁆ = 1`. -/
theorem lowerCentralSeries_sup_nonsplitTorus_V_eq_bot
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    Subgroup.lowerCentralSeries (fc.nonsplitTorus ⊔ fc.toHypothesis.V) 2 = ⊥ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  have hZLV := fc.inf_centralizer_sup_nonsplitTorus_V_eq model ind hB2
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
    Subgroup.lowerCentralSeries_zero, eq_bot_iff]
  refine le_trans (Subgroup.commutator_mono
    (fc.commutator_sup_nonsplitTorus_V_le model ind hB2) le_rfl) ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haC : a ∈ Subgroup.centralizer ((fc.nonsplitTorus ⊔ fc.toHypothesis.V : Subgroup G)
      : Set G) := by
    have : a ∈ (fc.nonsplitTorus ⊔ fc.toHypothesis.V)
        ⊓ Subgroup.centralizer ((fc.nonsplitTorus ⊔ fc.toHypothesis.V : Subgroup G)
          : Set G) := by
      rw [hZLV]
      exact ha
    exact this.2
  have hab := Subgroup.mem_centralizer_iff.mp haC b hb
  rw [Subgroup.mem_bot, commutatorElement_def, ← hab]
  group

include model in
/-- **`R₂` has no quotient isomorphic to `C₃ ≀ C₃` when `|W| = 3`** ((17), p. 114).

Here `R₂ = R₁` has order `3⁵` and centre `Z₁` of order `3`, so a surjection onto the
group `C₃ ≀ C₃` of order `3⁴` would have kernel of order `3`, necessarily the centre
(a normal subgroup of order `3` of a group of odd order is central).  But
`⁅⁅R₁, R₁⁆, R₁⁆ ≤ ⁅Z₁ΣP, R₁⁆ ≤ Z₁` by (16), so the quotient would have nilpotence
class at most `2`, whereas `C₃ ≀ C₃` has class `3`. -/
theorem not_surjective_wreath_of_card_W_eq_three
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G))
    (hW3 : Nat.card ↥fc.toHypothesis.W = 3)
    (φ : ↥(S : Subgroup G) →*
      (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) :
    ¬ Function.Surjective φ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro hφ
  obtain ⟨-, hp3, -, -, -, hGp⟩ := fc.step_twelve model ind hB2
  set R₁ : Subgroup G := fc.sylowThreeNormalizerRSigma model with hR₁_def
  have hR₁card : Nat.card ↥R₁ = 3 ^ 5 :=
    fc.card_sylowThreeNormalizerRSigma model ind hB2
  have hScard : Nat.card ↥(S : Subgroup G) = 3 ^ 5 := by
    rw [Sylow.card_eq_multiplicity, hGp, hW3]
    norm_num
  have hSeq : (S : Subgroup G) = R₁ :=
    (Subgroup.eq_of_le_of_card_ge hR₁S (by rw [hScard, hR₁card])).symm
  -- `C₃ ≀ C₃` has order `3⁴` and nilpotence class `3`
  have hcardW : Nat.card (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) = 3 ^ 4 := by
    rw [RegularWreathProduct.card]
    have h1 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [h1]
    norm_num
  haveI : Group.IsNilpotent (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) :=
    (IsPGroup.of_card hcardW).isNilpotent
  -- the kernel has order `3`
  have hkercard : Nat.card ↥(φ.ker) = 3 := by
    have h := φ.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top, hcardW,
      hScard] at h
    have h5 : (3 : ℕ) ^ 5 = 3 * 3 ^ 4 := by norm_num
    rw [h5] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  obtain ⟨z, hzmem, hz1⟩ : ∃ z : ↥(S : Subgroup G), z ∈ φ.ker ∧ z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : φ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      exact hcon y hy
    rw [hbot, Subgroup.card_bot] at hkercard
    omega
  have hzord : orderOf z = 3 := by
    have h1 : orderOf (⟨z, hzmem⟩ : ↥(φ.ker)) ∣ Nat.card ↥(φ.ker) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hkercard] at h1
    rcases (Nat.dvd_prime (by norm_num)).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hzple : Subgroup.zpowers z ≤ φ.ker := Subgroup.zpowers_le.mpr hzmem
  have hzpcard : Nat.card ↥(Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzord]
  have hkereq : Subgroup.zpowers z = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hzple (by rw [hzpcard, hkercard])
  -- the kernel is central, hence equals the centre `Z₁` of `R₂`
  have hodd : ∀ g : ↥(S : Subgroup G), Odd (orderOf g) := by
    intro g
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.2) g
    rw [hk]
    exact Odd.pow ⟨1, by norm_num⟩
  have hconjz : ∀ g : ↥(S : Subgroup G), g * z * g⁻¹ ∈ Subgroup.zpowers z := by
    intro g
    rw [hkereq]
    exact (MonoidHom.normal_ker φ).conj_mem z hzmem g
  have hzcenter : z ∈ Subgroup.center ↥(S : Subgroup G) :=
    mem_center_of_conj_mem_zpowers_of_orderOf_eq_three hzord hodd hconjz
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  have hcentercard : Nat.card ↥(Subgroup.center ↥(S : Subgroup G)) = 3 := by
    have hmap := map_center_subtype (S : Subgroup G)
    rw [fc.inf_centralizer_sylow_eq_zpowers model ind hB2 S hR₁S] at hmap
    have hcard : Nat.card ↥((Subgroup.center ↥(S : Subgroup G)).map
        (S : Subgroup G).subtype)
        = Nat.card ↥(Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t)) := by rw [hmap]
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Nat.card_zpowers,
      hstord] at hcard
    exact hcard
  have hkercenter : φ.ker = Subgroup.center ↥(S : Subgroup G) := by
    rw [← hkereq]
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzcenter)
      (by rw [hzpcard, hcentercard])
  -- `⁅⁅R₂, R₂⁆, R₂⁆ ≤ Z₁` by (16), so the quotient has class at most `2`
  have hlcsG : (S : Subgroup G).lowerCentralSeries 2
      ≤ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
      Subgroup.lowerCentralSeries_zero, hSeq]
    refine le_trans (Subgroup.commutator_mono
      (fc.commutator_sylowThree_le_zpowers_sup_sigma_sup_P model ind hB2) le_rfl) ?_
    exact fc.commutator_zpowers_sup_sigma_sup_P_sylowThree_le model ind hB2
  have hlcs : Subgroup.lowerCentralSeries (⊤ : Subgroup ↥(S : Subgroup G)) 2 ≤ φ.ker := by
    rw [hkercenter]
    refine (Subgroup.map_le_map_iff_of_injective (Subgroup.subtype_injective _)).mp ?_
    rw [Subgroup.top_subtype_lowerCentralSeries, map_center_subtype,
      fc.inf_centralizer_sylow_eq_zpowers model ind hB2 S hR₁S]
    exact hlcsG
  have hbot := lowerCentralSeries_eq_bot_of_le_ker φ hφ hlcs
  have hcls := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hbot
  rw [OddOrder.Isaacs.Ch10.nilpotencyClass_wreath 3] at hcls
  omega

include model in
/-- **Every nontrivial normal subgroup of `R₂` contains `Z₁`** ((17) support for
`|W| = 9`): it meets the centre `Z(R₂) = Z₁` (`exists_mem_center_of_normal_ne_bot`),
which has order `3`. -/
theorem zpowers_le_map_of_normal_ne_bot
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G))
    {K : Subgroup ↥(S : Subgroup G)} [K.Normal] (hK : K ≠ ⊥) :
    Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
      ≤ K.map (S : Subgroup G).subtype := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, hp3, -, -, -, -⟩ := fc.step_twelve model ind hB2
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  obtain ⟨z, hzK, hz1, hzc⟩ := exists_mem_center_of_normal_ne_bot S.2 hK
  have hzZ : ((z : G)) ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) := by
    have hmap := map_center_subtype (S : Subgroup G)
    rw [fc.inf_centralizer_sylow_eq_zpowers model ind hB2 S hR₁S] at hmap
    have hz : (z : G) ∈ (Subgroup.center ↥(S : Subgroup G)).map
        (S : Subgroup G).subtype := ⟨z, hzc, rfl⟩
    rwa [hmap] at hz
  have hzne : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzmem : (z : G) ∈ K.map (S : Subgroup G).subtype := ⟨z, hzK, rfl⟩
  rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three hstord hzZ with h | h | h
  · exact absurd h hzne
  · rw [← h]
    exact Subgroup.zpowers_le.mpr hzmem
  · rw [show fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t = ((z : G))⁻¹ by
      rw [h, inv_inv], Subgroup.zpowers_inv]
    exact Subgroup.zpowers_le.mpr hzmem

include model in
/-- **`|W| = 9`: the kernel of a `C₃ ≀ C₃` quotient of `R₂` lies in `R₁ ⊓ LV`** ((17),
p. 114; issue 9503).

`R₁` and `LV` both have index `3` in `R₂ = S`.  If the kernel `K` avoided one of them,
that subgroup would supplement `K` and hence map *onto* `C₃ ≀ C₃`; but `⁅⁅R₁, R₁⁆, R₁⁆ ≤
Z₁ ≤ K` by (16) and `⁅⁅LV, LV⁆, LV⁆ = 1`, so the image would have nilpotence class at
most `2`, whereas `C₃ ≀ C₃` has class `3`. -/
theorem map_ker_le_inf_of_card_W_eq_nine
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G))
    (hW9 : Nat.card ↥fc.toHypothesis.W = 9)
    (φ : ↥(S : Subgroup G) →*
      (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)))
    (hφ : Function.Surjective φ) :
    (φ.ker).map (S : Subgroup G).subtype
      ≤ fc.sylowThreeNormalizerRSigma model
        ⊓ (fc.nonsplitTorus ⊔ fc.toHypothesis.V) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, -, -, -, -, hGp⟩ := fc.step_twelve model ind hB2
  have hR₁card : Nat.card ↥(fc.sylowThreeNormalizerRSigma model) = 3 ^ 5 :=
    fc.card_sylowThreeNormalizerRSigma model ind hB2
  have hLVcard : Nat.card ↥(fc.nonsplitTorus ⊔ fc.toHypothesis.V) = 3 ^ 5 := by
    rw [fc.card_sup_nonsplitTorus_V model ind hB2, hW9]
    norm_num
  have hScard : Nat.card ↥(S : Subgroup G) = 3 ^ 6 := by
    rw [Sylow.card_eq_multiplicity, hGp, hW9]
    norm_num
  have hLVS : fc.nonsplitTorus ⊔ fc.toHypothesis.V ≤ (S : Subgroup G) :=
    fc.sup_nonsplitTorus_V_le_sylow model ind hB2 S hR₁S
  -- the kernel has order `9`
  have hkercard : Nat.card ↥(φ.ker) = 9 := by
    have h := φ.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top,
      card_wreathThree, hScard] at h
    have h6 : (3 : ℕ) ^ 6 = 9 * 3 ^ 4 := by norm_num
    rw [h6] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  have hkerne : φ.ker ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hkercard
    omega
  have hZ₁ker := fc.zpowers_le_map_of_normal_ne_bot model ind hB2 S hR₁S hkerne
  -- a subgroup of order `3⁵` has index `3`
  have hidx : ∀ X : Subgroup G, X ≤ (S : Subgroup G) → Nat.card ↥X = 3 ^ 5 →
      (X.subgroupOf (S : Subgroup G)).index = 3 := by
    intro X hXS hXcard
    have h := (X.subgroupOf (S : Subgroup G)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXS).toEquiv, hXcard, hScard] at h
    omega
  -- the branch argument
  have hbranch : ∀ X : Subgroup G, X ≤ (S : Subgroup G) → Nat.card ↥X = 3 ^ 5 →
      Subgroup.lowerCentralSeries X 2 ≤ Subgroup.zpowers
        (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) →
      (φ.ker).map (S : Subgroup G).subtype ≤ X := by
    intro X hXS hXcard hlcs
    have hle : φ.ker ≤ X.subgroupOf (S : Subgroup G) := by
      by_contra hcon
      refine false_of_wreathThree_quotient φ hφ
        (sup_eq_top_of_index_prime (by norm_num) (hidx X hXS hXcard) hcon) ?_
      refine (Subgroup.map_le_map_iff_of_injective (Subgroup.subtype_injective _)).mp ?_
      rw [Subgroup.map_lowerCentralSeries, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hXS]
      exact le_trans hlcs hZ₁ker
    calc (φ.ker).map (S : Subgroup G).subtype
        ≤ (X.subgroupOf (S : Subgroup G)).map (S : Subgroup G).subtype :=
          Subgroup.map_mono hle
      _ = X ⊓ (S : Subgroup G) := Subgroup.subgroupOf_map_subtype _ _
      _ ≤ X := inf_le_left
  refine le_inf (hbranch _ hR₁S hR₁card ?_) (hbranch _ hLVS hLVcard ?_)
  · rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
      Subgroup.lowerCentralSeries_zero]
    refine le_trans (Subgroup.commutator_mono
      (fc.commutator_sylowThree_le_zpowers_sup_sigma_sup_P model ind hB2) le_rfl) ?_
    exact fc.commutator_zpowers_sup_sigma_sup_P_sylowThree_le model ind hB2
  · rw [fc.lowerCentralSeries_sup_nonsplitTorus_V_eq_bot model ind hB2]
    exact bot_le

include model in
/-- **`|W| = 9`: a `C₃ ≀ C₃` quotient of `R₂` cannot contain both `⁅R₁, R₁⁆` and
`⁅LV, LV⁆` in its kernel** ((17), p. 114; issue 9503).

`R₁` and `LV` are distinct subgroups of index `3` (as `W ≤ LV` but `W ⊄ R₁`) that
contain the kernel (`map_ker_le_inf_of_card_W_eq_nine`); if both were abelian modulo
the kernel, `false_of_two_abelian_of_index_three` would force the quotient to have
class at most `2`. -/
theorem not_and_commutator_le_map_ker_of_card_W_eq_nine
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G))
    (hW9 : Nat.card ↥fc.toHypothesis.W = 9)
    (φ : ↥(S : Subgroup G) →*
      (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)))
    (hφ : Function.Surjective φ) :
    ¬ (⁅fc.sylowThreeNormalizerRSigma model, fc.sylowThreeNormalizerRSigma model⁆
        ≤ (φ.ker).map (S : Subgroup G).subtype
      ∧ ⁅fc.nonsplitTorus ⊔ fc.toHypothesis.V, fc.nonsplitTorus ⊔ fc.toHypothesis.V⁆
        ≤ (φ.ker).map (S : Subgroup G).subtype) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rintro ⟨hcommR₁, hcommLV⟩
  obtain ⟨-, -, -, -, -, hGp⟩ := fc.step_twelve model ind hB2
  have hR₁card : Nat.card ↥(fc.sylowThreeNormalizerRSigma model) = 3 ^ 5 :=
    fc.card_sylowThreeNormalizerRSigma model ind hB2
  have hLVcard : Nat.card ↥(fc.nonsplitTorus ⊔ fc.toHypothesis.V) = 3 ^ 5 := by
    rw [fc.card_sup_nonsplitTorus_V model ind hB2, hW9]
    norm_num
  have hScard : Nat.card ↥(S : Subgroup G) = 3 ^ 6 := by
    rw [Sylow.card_eq_multiplicity, hGp, hW9]
    norm_num
  have hLVS : fc.nonsplitTorus ⊔ fc.toHypothesis.V ≤ (S : Subgroup G) :=
    fc.sup_nonsplitTorus_V_le_sylow model ind hB2 S hR₁S
  have hidx : ∀ X : Subgroup G, X ≤ (S : Subgroup G) → Nat.card ↥X = 3 ^ 5 →
      (X.subgroupOf (S : Subgroup G)).index = 3 := by
    intro X hXS hXcard
    have h := (X.subgroupOf (S : Subgroup G)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXS).toEquiv, hXcard, hScard] at h
    omega
  -- both contain the kernel
  have hkerle := fc.map_ker_le_inf_of_card_W_eq_nine model ind hB2 S hR₁S hW9 φ hφ
  have hkX : φ.ker ≤ (fc.sylowThreeNormalizerRSigma model).subgroupOf (S : Subgroup G) :=
    Subgroup.map_le_iff_le_comap.mp (le_trans hkerle inf_le_left)
  have hkY : φ.ker ≤ (fc.nonsplitTorus ⊔ fc.toHypothesis.V).subgroupOf (S : Subgroup G) :=
    Subgroup.map_le_iff_le_comap.mp (le_trans hkerle inf_le_right)
  -- they are distinct, hence generate
  have hne : ¬ ((fc.nonsplitTorus ⊔ fc.toHypothesis.V).subgroupOf (S : Subgroup G)
      ≤ (fc.sylowThreeNormalizerRSigma model).subgroupOf (S : Subgroup G)) := by
    intro hle
    refine fc.not_W_le_sylowThree_of_card_W_eq_nine model ind hB2 hW9 fun w hw => ?_
    have hwLV : w ∈ fc.nonsplitTorus ⊔ fc.toHypothesis.V :=
      Subgroup.mem_sup_right (fc.toHypothesis.W_le_V hw)
    have := hle (Subgroup.mem_subgroupOf.mpr (by exact hwLV) :
      (⟨w, hLVS hwLV⟩ : ↥(S : Subgroup G))
        ∈ (fc.nonsplitTorus ⊔ fc.toHypothesis.V).subgroupOf (S : Subgroup G))
    exact Subgroup.mem_subgroupOf.mp this
  -- transport the commutator hypotheses into `↥S`
  have hcomm : ∀ X : Subgroup G, X ≤ (S : Subgroup G) →
      ⁅X, X⁆ ≤ (φ.ker).map (S : Subgroup G).subtype →
      ⁅X.subgroupOf (S : Subgroup G), X.subgroupOf (S : Subgroup G)⁆ ≤ φ.ker := by
    intro X hXS hXcomm
    refine (Subgroup.map_le_map_iff_of_injective (Subgroup.subtype_injective _)).mp ?_
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXS]
    exact hXcomm
  exact false_of_two_abelian_of_index_three φ hφ
    (sup_eq_top_of_index_prime (by norm_num)
      (hidx _ hR₁S hR₁card) hne)
    (hidx _ hR₁S hR₁card) (hidx _ hLVS hLVcard) hkX hkY
    (hcomm _ hR₁S hcommR₁) (hcomm _ hLVS hcommLV)

include model in
/-- **The contradiction of (17), given that `R₂` has no `C₃ ≀ C₃` quotient.**

Both branches of (17) produce a quotient of order `3` of `R₂⟨s⟩`
(`three_dvd_card_abelianization_of_card_W_eq_{three,nine}`), while transfer control
(`not_three_dvd_card_abelianization_normalizer_sylow`) forbids it. -/
theorem false_of_no_wreath_quotient
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G))
    (hwreath : ∀ φ : ↥(S : Subgroup G) →*
        (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)), ¬ Function.Surjective φ) :
    False := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  refine fc.false_of_transfer_control model ind hB2 S hR₁S ?_ ?_
  · -- `N_G(Z₁ΣP) = N_G(Z₁) = R₂⟨s⟩ = N_G(R₂)`
    have hNeq : Subgroup.normalizer ((((Subgroup.zpowers
          (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t)
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))) ⊔ fc.P)
          : Subgroup G) : Set G)
        = Subgroup.normalizer (((S : Subgroup G)) : Set G) := by
      rw [← fc.normalizer_zpowers_eq_normalizer_zpowers_sup_sigma_sup_P model ind hB2
        S hR₁S, fc.normalizer_zpowers_eq_sylow_sup_zpowers model ind hB2 S hR₁S,
        fc.normalizer_sylow_eq model ind hB2 S hR₁S]
    rw [hNeq]
    exact fc.not_three_dvd_card_abelianization_normalizer_sylow model ind hB2 S hR₁S
      hwreath
  · intro hW3
    exact fc.three_dvd_card_abelianization_of_card_W_eq_three model ind hB2 S hR₁S hW3

include model in
/-- **Step (17) for `|W| = 3`: the contradiction is complete** (p. 114).

`R₂ = R₁` has no `C₃ ≀ C₃` quotient (`not_surjective_wreath_of_card_W_eq_three`), so
`N_G(R₂)` controls the `3`-transfer and (B2) rules out its quotient of order `3`. -/
theorem false_of_card_W_eq_three
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G))
    (hW3 : Nat.card ↥fc.toHypothesis.W = 3) :
    False :=
  fc.false_of_no_wreath_quotient model ind hB2 S hR₁S
    (fun φ => fc.not_surjective_wreath_of_card_W_eq_three model ind hB2 S hR₁S hW3 φ)

include model in
/-- **The contradiction of (17) from the weak closure of `Z₁`** (p. 114; issue 9503).

`Z₁ = Z(R₂)` is central in the Sylow `3`-subgroup `R₂`, so if it is weakly closed in
`R₂` then `N_G(Z₁) = R₂⟨s⟩` controls the `3`-transfer
(`OddOrder.GroupTheory.not_dvd_card_abelianization_normalizer`, i.e. Isaacs 5C.6(d) plus
the focal subgroup theorem — the form of the Hall–Wielandt theorem that (17) needs).
Hypothesis (B2) then forbids the quotient of order `3` of `R₂⟨s⟩` produced in both the
`|W| = 3` and the `|W| = 9` branch. -/
theorem false_of_isWeaklyClosed_zpowers
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) (S : Sylow 3 G)
    (hR₁S : fc.sylowThreeNormalizerRSigma model ≤ (S : Subgroup G))
    (hwc : OddOrder.GroupTheory.IsWeaklyClosed
      (Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t))
      (S : Subgroup G)) :
    False := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, hp3, -, -, hW, -⟩ := fc.step_twelve model ind hB2
  have hB2' : ¬ (3 : ℕ) ∣ Nat.card (Abelianization G) := by rwa [hp3] at hB2
  have hZeq := fc.inf_centralizer_sylow_eq_zpowers model ind hB2 S hR₁S
  have hWP : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ≤ (S : Subgroup G) := by
    rw [← hZeq]
    exact inf_le_left
  have hWZ : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ≤ Subgroup.centralizer (((S : Subgroup G)) : Set G) := by
    rw [← hZeq]
    exact inf_le_right
  have hcontrol := OddOrder.GroupTheory.not_dvd_card_abelianization_normalizer
    hWP hWZ hwc hB2'
  rw [fc.normalizer_zpowers_eq_sylow_sup_zpowers model ind hB2 S hR₁S] at hcontrol
  rcases hW with h3 | h9
  · exact hcontrol
      (fc.three_dvd_card_abelianization_of_card_W_eq_three model ind hB2 S hR₁S h3)
  · exact hcontrol
      (fc.three_dvd_card_abelianization_of_card_W_eq_nine model ind hB2 S hR₁S h9)

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
