/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepFour

/-!
# Peterfalvi Part II, Ch. II, step (5): supporting identifications

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (5), pp. 109–110.

Step (5) states: if `F` is not a field — equivalently, `C_Q(P)` is not
abelian — then `F ≅ F_{9,2}` and `Q₁ = 1`.  This leaf builds the two
identifications on which its proof (and the later steps) rest:

* `centralizer_inf_mulEquiv_units`: the book's standing identification
  `C_Q(P) ≅ F^*` — the near-field model of step (2)(b) identifies the `Q`
  of the faithful quotient `C_G(P)/N` with `F^*` (`qEquiv`), and
  `Q ⊓ C_G(P)` maps isomorphically onto that quotient `Q` because the
  kernel `N` lies in `D` and `Q ⊓ D = 1`;
* `Q1_eq_bot_of_card_two_pow`: if `|Q|` is a power of `2` then `Q₁ = 1`
  (the odd factor of the nilpotent group `Q` is trivial) — the final
  inference of step (5) from `|Q| = |C_Q(P)|^p = 8^p` (step (4)).

Everything consuming the near-field model inherits the step (2)(b)
`sorry` (issue 9318) through `exists_affineNearFieldModel`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- **The identification `C_Q(P) ≅ F^*`** (p. 109, used from step (4) on):
for any near-field model of step (2)(b), the subgroup `Q ⊓ C_G(P)` of `G`
is isomorphic to the unit group `F^*`.

`qEquiv` identifies the quotient group `Q̄ = (Q ⊓ C_G(P)) N/N` with `F^*`;
the projection `Q ⊓ C_G(P) → Q̄` is injective because the kernel `N` lies
in `D_L` (`normalCore_cH_eq_centralizer_cQ`) and `Q ⊓ D = 1`, and it is
surjective because `Q̄` is by definition the image of `Q ⊓ C_G(P)`. -/
theorem centralizer_inf_mulEquiv_units :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    ∀ {F : Type uG} [NearFields.NearField F]
      (model : NearFields.AffineNearFieldModel fc.rankOneQuotient F),
      Nonempty
        (↥(fc.toHypothesis.Q ⊓ Subgroup.centralizer (fc.P : Set G)) ≃* Fˣ) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  intro F instF model
  classical
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore
    with hNdef
  set M₀ : Subgroup G := fc.toHypothesis.Q ⊓ L with hM₀def
  have hM₀L : M₀ ≤ L := inf_le_right
  have hQbar : fc.rankOneQuotient.Q =
      (fc.toHypothesis.Q.subgroupOf L).map (QuotientGroup.mk' N) := rfl
  have hmemQ : ∀ m : ↥M₀,
      ((QuotientGroup.mk' N).comp (Subgroup.inclusion hM₀L)) m ∈
        fc.rankOneQuotient.Q := by
    intro m
    rw [hQbar]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr m.2.1)
  set ι : ↥M₀ →* Fˣ :=
    model.qEquiv.toMonoidHom.comp
      (((QuotientGroup.mk' N).comp (Subgroup.inclusion hM₀L)).codRestrict
        fc.rankOneQuotient.Q hmemQ) with hιdef
  have hιinj : Function.Injective ι := by
    intro a b hab
    have h1 : ι (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((QuotientGroup.mk' N).comp (Subgroup.inclusion hM₀L))
        (a * b⁻¹) = 1 := by
      have h2' := model.qEquiv.injective (h1.trans (map_one _).symm)
      exact congrArg Subtype.val h2'
    have h4 : Subgroup.inclusion hM₀L (a * b⁻¹) ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      exact h2
    have h5 : Subgroup.inclusion hM₀L (a * b⁻¹) ∈
        fc.toHypothesis.D.subgroupOf L := by
      have hND : N ≤ fc.toHypothesis.D.subgroupOf L := by
        rw [hNdef, fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
        exact inf_le_left
      exact hND h4
    have h6 : ((a * b⁻¹ : ↥M₀) : G) ∈
        fc.toHypothesis.Q ⊓ fc.toHypothesis.D :=
      ⟨(a * b⁻¹).2.1, Subgroup.mem_subgroupOf.mp h5⟩
    rw [fc.toHypothesis.Q_inf_D_eq_bot, Subgroup.mem_bot] at h6
    exact mul_inv_eq_one.mp (Subtype.ext h6)
  have hιsurj : Function.Surjective ι := by
    intro u
    have hmem : ((model.qEquiv.symm u : ↥fc.rankOneQuotient.Q) :
        ↥L ⧸ N) ∈ (fc.toHypothesis.Q.subgroupOf L).map
          (QuotientGroup.mk' N) := by
      rw [← hQbar]
      exact (model.qEquiv.symm u).2
    obtain ⟨x, hxQL, hx⟩ := hmem
    refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hxQL, x.2⟩, ?_⟩
    have hval : ι ⟨(x : G), Subgroup.mem_subgroupOf.mp hxQL, x.2⟩
        = model.qEquiv ⟨QuotientGroup.mk' N x, by
            rw [hQbar]; exact Subgroup.mem_map_of_mem _ hxQL⟩ := rfl
    rw [hval]
    have harg : (⟨QuotientGroup.mk' N x, by
          rw [hQbar]; exact Subgroup.mem_map_of_mem _ hxQL⟩ :
        ↥fc.rankOneQuotient.Q) = model.qEquiv.symm u :=
      Subtype.ext hx
    rw [harg, MulEquiv.apply_symm_apply]
  exact ⟨MulEquiv.ofBijective ι ⟨hιinj, hιsurj⟩⟩

/-- **The closing inference of step (5)** (p. 110): if `|Q|` is a power of
`2` then the odd factor `Q₁` of the nilpotent group `Q` is trivial
(`Q = S × Q₁` with `2 ∤ |Q₁|`). -/
theorem Q1_eq_bot_of_card_two_pow {n : ℕ}
    (h : Nat.card ↥fc.toHypothesis.Q = 2 ^ n) :
    fc.toHypothesis.Q1 = ⊥ := by
  have hdvd : Nat.card ↥fc.toHypothesis.Q1Subgroup ∣ 2 ^ n :=
    h ▸ Subgroup.card_subgroup_dvd_card fc.toHypothesis.Q1Subgroup
  have hodd : ¬ 2 ∣ Nat.card ↥fc.toHypothesis.Q1Subgroup :=
    fc.toHypothesis.two_not_dvd_card_Q1Subgroup
  have hcop : Nat.Coprime (Nat.card ↥fc.toHypothesis.Q1Subgroup) (2 ^ n) :=
    Nat.Coprime.pow_right n
      (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by
        rcases Nat.even_or_odd (Nat.card ↥fc.toHypothesis.Q1Subgroup) with
          he | ho
        · exact absurd he.two_dvd hodd
        · exact Nat.odd_iff.mp ho)))
  have hone : Nat.card ↥fc.toHypothesis.Q1Subgroup = 1 :=
    Nat.Coprime.eq_one_of_dvd hcop hdvd
  have hbot : fc.toHypothesis.Q1Subgroup = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ hone
  rw [Hypothesis.Q1, hbot, Subgroup.map_bot]

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
