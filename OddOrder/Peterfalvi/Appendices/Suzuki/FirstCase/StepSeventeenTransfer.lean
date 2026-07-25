/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepSeventeen
import OddOrder.Isaacs.Ch10_MoreTransfer.Yoshida
import OddOrder.GroupTheory.TransferIndexTwo

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

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
