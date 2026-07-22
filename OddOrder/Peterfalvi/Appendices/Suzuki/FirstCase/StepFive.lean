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

/-! ## Group-theoretic helpers for step (5)

Three self-contained inputs: the exponent of a Suzuki `2`-group (Higman —
sorried-cite until the Higman campaign lands it), the center of a
nonabelian group of order `8`, and the cyclicity of odd `p`-subgroups of
near-field unit groups (they act fixed-point-freely on `(F, +)`). -/

section StepFiveHelpers

/-- **Peterfalvi p. 110 (inside step (5)) / Appendix III (Higman)**: a
Suzuki `2`-group has exponent `4` ("`S` is then a Suzuki 2-group and so of
exponent 4").

**Sorried-cite**: the statement is Higman's theorem (a) (Appendix III,
p. 141, `S/Z(S)` and `Z(S) = Ω₁(S)` elementary abelian); the Higman
campaign (`OddOrder/Higman/Suzuki2Groups/**`) is building the proof.
Tracked in issue 2053. -/
theorem pow_four_eq_one_of_isSuzuki2Group {P : Type*} [Group P] [Finite P]
    (hP : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group P) (x : P) :
    x ^ 4 = 1 := by
  sorry

/-- A nonabelian group of order `8` has center of order `2`: the center is
nontrivial (`2`-group), proper (nonabelian), and of index `≠ 2` (a cyclic
central quotient would force commutativity). -/
theorem card_center_eq_two_of_card_eq_eight {T : Type*} [Group T] [Finite T]
    (hcard : Nat.card T = 8) (hnc : ¬ ∀ x y : T, x * y = y * x) :
    Nat.card ↥(Subgroup.center T) = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : Nat.card ↥(Subgroup.center T) ∣ 8 :=
    hcard ▸ Subgroup.card_subgroup_dvd_card _
  have h2 : IsPGroup 2 T :=
    IsPGroup.of_card (hcard.trans (by norm_num : (8 : ℕ) = 2 ^ 3))
  haveI : Nontrivial T := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hcard]; norm_num
  haveI hZnt : Nontrivial ↥(Subgroup.center T) := h2.center_nontrivial
  have hZge : 2 ≤ Nat.card ↥(Subgroup.center T) :=
    Finite.one_lt_card_iff_nontrivial.mpr hZnt
  have hne8 : Nat.card ↥(Subgroup.center T) ≠ 8 := by
    intro h8
    apply hnc
    have htop : Subgroup.center T = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (h8.trans hcard.symm)
    intro x y
    exact Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top y) x
  have hne4 : Nat.card ↥(Subgroup.center T) ≠ 4 := by
    intro h4
    apply hnc
    have hquot : Nat.card (T ⧸ Subgroup.center T) = 2 := by
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center T)
      rw [hcard, h4] at hmul
      omega
    haveI : IsCyclic (T ⧸ Subgroup.center T) := isCyclic_of_prime_card hquot
    have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center T)) (by
        rw [QuotientGroup.ker_mk'])
    exact fun x y => hcomm.is_comm.comm x y
  have hdvd' : Nat.card ↥(Subgroup.center T) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
    exact hdvd
  obtain ⟨k, hk3, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  interval_cases k
  · rw [pow_zero] at hkeq
    omega
  · rw [pow_one] at hkeq
    exact hkeq
  · rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hkeq
    exact absurd hkeq hne4
  · rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at hkeq
    exact absurd hkeq hne8

/-- Odd `q`-subgroups of the unit group of a finite near-field are cyclic:
`R` acts fixed-point-freely on `(F, +)` by right multiplication (by the
inverse, to make it a left action), and an odd `p`-group with a
fixed-point-free action on an elementary abelian group is cyclic
([H] Kapitel V, Satz 8.15-adjacent; here
`Huppert.isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian`). -/
theorem isCyclic_odd_pSubgroup_of_nearField_units {F : Type*}
    [NearFields.NearField F] [Finite F] {q : ℕ} (hq : q.Prime) (hqodd : Odd q)
    (R : Subgroup Fˣ) (hR : IsPGroup q ↥R) : IsCyclic ↥R := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Nontrivial (Multiplicative F) := inferInstanceAs (Nontrivial F)
  -- the right-multiplication-by-inverse action of `R` on `(F, +)`
  set φ : ↥R →* MulAut (Multiplicative F) :=
    { toFun := fun u => (NearFields.rightMul ((((u : Fˣ))⁻¹ : Fˣ) : F)
        (Units.ne_zero _)).toMultiplicative
      map_one' := by
        ext x
        apply Multiplicative.toAdd.injective
        change Multiplicative.toAdd x * ((((1 : ↥R) : Fˣ))⁻¹ : Fˣ) =
          Multiplicative.toAdd x
        rw [OneMemClass.coe_one, inv_one, Units.val_one, mul_one]
      map_mul' := fun u v => by
        ext x
        apply Multiplicative.toAdd.injective
        change Multiplicative.toAdd x * ((((u * v : ↥R) : Fˣ))⁻¹ : Fˣ) =
          (Multiplicative.toAdd x * (((v : Fˣ))⁻¹ : Fˣ)) *
            ((((u : Fˣ))⁻¹ : Fˣ) : F)
        rw [MulMemClass.coe_mul, mul_inv_rev, Units.val_mul, ← mul_assoc] }
    with hφdef
  have hφval : ∀ (u : ↥R) (x : Multiplicative F),
      Multiplicative.toAdd (φ u x) =
        Multiplicative.toAdd x * ((((u : Fˣ))⁻¹ : Fˣ) : F) := fun _ _ => rfl
  -- fixed-point-freeness
  have hfpf : ∀ u : ↥R, u ≠ 1 →
      OddOrder.Isaacs.Ch06.actionFixedBy φ u = ⊥ := by
    intro u hu
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hfix := (OddOrder.Isaacs.Ch06.mem_actionFixedBy).mp hx
    have hfixval : Multiplicative.toAdd x * ((((u : Fˣ))⁻¹ : Fˣ) : F) =
        Multiplicative.toAdd x := by
      rw [← hφval u x, hfix]
    by_contra hxne
    have hx0 : Multiplicative.toAdd x ≠ 0 := fun h0 =>
      hxne (Multiplicative.toAdd.injective h0)
    have hinv1 : ((((u : Fˣ))⁻¹ : Fˣ) : F) = 1 :=
      mul_left_cancel₀ hx0 (hfixval.trans (mul_one _).symm)
    have huinv : ((u : Fˣ))⁻¹ = 1 := Units.ext hinv1
    exact hu (Subtype.ext (inv_eq_one.mp huinv))
  obtain ⟨f, hf, hEA⟩ := NearFields.isElementaryAbelian_multiplicative (F := F)
  exact Huppert.isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian
    hf hR hqodd hEA φ hfpf

end StepFiveHelpers

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
