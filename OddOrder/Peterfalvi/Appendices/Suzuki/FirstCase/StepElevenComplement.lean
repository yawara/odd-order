/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepEleven

/-!
# Peterfalvi Part II, Ch. II, step (11): the complement `T = [R, s]` and regularity

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (11), pp. 111–112 — second half.

Split from `StepEleven.lean` (file-length limit): the subgroup `T` of elements of `R`
inverted by the distinguished involution, the decomposition `R = T × P`, and (in
subsequent commits, issue 2053) the `C_Q(P)·C_W(P)`-normalization of `T` and the regular
action of `C_Q(P)` on `𝒜 − {P}`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace OddOrder.Peterfalvi.Appendices.Suzuki

/-- **Conjugation fixes a subgroup iff the conjugator normalizes it** (bridge between the
pointwise `MulAut.conj`-action on subgroups and the set-normalizer; used to identify the
stabilizer in the step (12) orbit count). -/
theorem conj_smul_eq_iff_mem_normalizer {G' : Type*} [Group G'] {P : Subgroup G'} {g : G'} :
    MulAut.conj g • P = P ↔ g ∈ Subgroup.normalizer (P : Set G') := by
  constructor
  · intro h
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : (MulAut.conj g) • x ∈ MulAut.conj g • P :=
        Subgroup.smul_mem_pointwise_smul _ _ _ hx
      rw [h] at h1
      have h2 : ((MulAut.conj g) • x : G') = g * x * g⁻¹ := rfl
      rwa [h2] at h1
    · intro hx
      have h1 : g * x * g⁻¹ ∈ MulAut.conj g • P := by
        rw [h]
        exact hx
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
      have h2 : ((MulAut.conj g)⁻¹ • (g * x * g⁻¹) : G') = x := by
        have h3 : ((MulAut.conj g)⁻¹ • (g * x * g⁻¹) : G')
            = (MulAut.conj g)⁻¹ (g * x * g⁻¹) := rfl
        rw [h3, ← map_inv, MulAut.conj_apply]
        group
      rwa [h2] at h1
  · intro hg
    ext y
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h2 : ((MulAut.conj g)⁻¹ • y : G') = g⁻¹ * y * g := by
      have h3 : ((MulAut.conj g)⁻¹ • y : G') = (MulAut.conj g)⁻¹ y := rfl
      rw [h3, ← map_inv, MulAut.conj_apply]
      group
    rw [h2]
    have h3 := Subgroup.mem_set_normalizer_iff.mp hg (g⁻¹ * y * g)
    have h5 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    constructor
    · intro hy
      have h4 := h3.mp hy
      rwa [h5] at h4
    · intro hy
      refine h3.mpr ?_
      rwa [h5]

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

/-- **`T = [R, s]`** (step (11), p. 111): the subgroup of `R` cut out by the elements
inverted by the distinguished involution, packaged as a closure so the definition needs
no abelianness; once `R` is abelian (`invImageF_mul_comm`) the generating set is itself
a subgroup and `sInvertedT_spec` collapses the closure. -/
noncomputable def sInvertedT : Subgroup G :=
  Subgroup.closure {x | x ∈ fc.invImageF model ∧
    fc.toHypothesis.distinguishedInvolution * x
      * fc.toHypothesis.distinguishedInvolution⁻¹ = x⁻¹}

/-- The distinguished involution centralizes `Q`: it lies in `Q₀` (the involutions of
`H`), and `Q₀ ≤ C_G(Q)` (Ch. I §2, `Q0_le_centralizer_Q`). -/
theorem distinguishedInvolution_commute_of_mem_Q {a : G} (ha : a ∈ fc.toHypothesis.Q) :
    fc.toHypothesis.distinguishedInvolution * a
      = a * fc.toHypothesis.distinguishedInvolution := by
  have hs0 : fc.toHypothesis.distinguishedInvolution ∈ fc.toHypothesis.Q0 :=
    ⟨fc.toHypothesis.distinguishedInvolution_sq,
      fc.toHypothesis.distinguishedInvolution_mem_H⟩
  exact (Subgroup.mem_centralizer_iff.mp
    (fc.toHypothesis.Q0_le_centralizer_Q hs0) a ha).symm

include model in
/-- **Step (11), second assertion (decomposition): `R = T × P`** in existence form —
`T := {r ∈ R | s·r·s⁻¹ = r⁻¹}`, the elements inverted by the distinguished involution,
is a complement of `P` in the abelian `R`.  Mechanism: `s` centralizes `P`, so
`T ⊓ P` consists of `2`-torsion in the odd `P`; and on the translations `s` acts as
right multiplication by `u := qEquiv [s]⁻¹ ≠ 1`, whose fixed points vanish by
cancellation, making `x ↦ x·u − x` injective hence surjective on the finite `F` —
so `T` covers every translation class. -/
theorem sInvertedT_spec
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    fc.sInvertedT model ≤ fc.invImageF model ∧
      (∀ x ∈ fc.sInvertedT model, fc.toHypothesis.distinguishedInvolution * x
        * fc.toHypothesis.distinguishedInvolution⁻¹ = x⁻¹) ∧
      fc.sInvertedT model ⊔ fc.P = fc.invImageF model ∧
      fc.sInvertedT model ⊓ fc.P = ⊥ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  have hab := fc.invImageF_mul_comm model ind hB2 hm
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  set s : G := fc.toHypothesis.distinguishedInvolution with hsdef
  have hsL : s ∈ L :=
    fc.toHypothesis.distinguishedInvolution_mem_centralizer_of_le_V fc.P_le_V
  have hs2 : s * s = 1 := by
    have h := fc.toHypothesis.distinguishedInvolution_sq
    rwa [pow_two] at h
  -- `T`, the `s`-inverted subgroup of the abelian `R`.
  set T : Subgroup G :=
    { carrier := {x | x ∈ fc.invImageF model ∧ s * x * s⁻¹ = x⁻¹}
      one_mem' := ⟨(fc.invImageF model).one_mem, by simp⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨(fc.invImageF model).mul_mem ha.1 hb.1, ?_⟩
        have h1 : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        rw [h1, ha.2, hb.2, mul_inv_rev]
        exact hab _ ((fc.invImageF model).inv_mem ha.1)
          _ ((fc.invImageF model).inv_mem hb.1)
      inv_mem' := fun {a} ha => by
        refine ⟨(fc.invImageF model).inv_mem ha.1, ?_⟩
        have h1 : s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
        rw [h1, ha.2] } with hTdef
  have hTle : T ≤ fc.invImageF model := fun x hx => hx.1
  -- `T ⊓ P = ⊥`: `s` centralizes `P`, so the intersection is `2`-torsion in odd `P`.
  have hTP : T ⊓ fc.P = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxP⟩
    rw [Subgroup.mem_bot]
    have hfix : s * x * s⁻¹ = x := by
      have hc := Subgroup.mem_centralizer_iff.mp hsL x hxP
      rw [← hc]
      group
    have hxinv : x⁻¹ = x := by rw [← hxT.2, hfix]
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← hxinv]
      exact inv_mul_cancel x
    have hd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hdp : orderOf x ∣ fc.p := by
      have h1 : orderOf (⟨x, hxP⟩ : ↥fc.P) ∣ Nat.card ↥fc.P := orderOf_dvd_natCard _
      rwa [fc.card_P, Subgroup.orderOf_mk] at h1
    have hg1 : Nat.gcd 2 fc.p = 1 := by
      have h2 : ¬ (2 : ℕ) ∣ fc.p := by
        rcases fc.p_odd with ⟨k, hk⟩
        omega
      rcases (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_left 2 fc.p) with h | h
      · exact h
      · exact absurd (h ▸ Nat.gcd_dvd_right 2 fc.p) h2
    have hone : orderOf x ∣ 1 := by
      have h2 := Nat.dvd_gcd hd2 hdp
      rwa [hg1] at h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)
  -- the translation-side unit `u := qEquiv [s]⁻¹ ≠ 1`.
  have hsQ : s ∈ fc.toHypothesis.Q :=
    fc.toHypothesis.mem_Q_of_sq_eq_one_of_mem_H
      fc.toHypothesis.distinguishedInvolution_mem_H
      fc.toHypothesis.distinguishedInvolution_sq
  have hQbar : fc.rankOneQuotient.Q =
      (fc.toHypothesis.Q.subgroupOf L).map (QuotientGroup.mk' N') := rfl
  have hsbarQ : QuotientGroup.mk' N' ⟨s, hsL⟩ ∈ fc.rankOneQuotient.Q := by
    rw [hQbar]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hsQ)
  set sQ : ↥fc.rankOneQuotient.Q := ⟨QuotientGroup.mk' N' ⟨s, hsL⟩, hsbarQ⟩ with hsQdef
  set u : Fˣ := model.qEquiv sQ⁻¹ with hudef
  have hsQne : sQ ≠ 1 := by
    intro h
    have h1 : QuotientGroup.mk' N' ⟨s, hsL⟩ = 1 := congrArg Subtype.val h
    rw [QuotientGroup.mk'_apply] at h1
    have hsN : (⟨s, hsL⟩ : ↥L) ∈ N' := (QuotientGroup.eq_one_iff _).mp h1
    have hND : N' ≤ fc.toHypothesis.D.subgroupOf L := by
      rw [hN'def, fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
      exact inf_le_left
    have hsD : s ∈ fc.toHypothesis.D := Subgroup.mem_subgroupOf.mp (hND hsN)
    have hbot : s ∈ fc.toHypothesis.Q ⊓ fc.toHypothesis.D := ⟨hsQ, hsD⟩
    rw [fc.toHypothesis.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
    exact fc.toHypothesis.distinguishedInvolution_ne_one hbot
  have hune : (u : F) ≠ 1 := by
    intro h
    have h1 : u = 1 := Units.ext h
    have h2 : sQ⁻¹ = 1 := model.qEquiv.injective (by rw [← hudef, h1, map_one])
    exact hsQne (by rwa [inv_eq_one] at h2)
  -- near-field arithmetic: `x ↦ x·u − x` is injective, hence surjective.
  have hsub_mul : ∀ a b : F, (a - b) * (u : F) = a * (u : F) - b * (u : F) := by
    intro a b
    have hneg : (-b) * (u : F) = -(b * (u : F)) := by
      have h0 : (-b + b) * (u : F) = 0 := by rw [neg_add_cancel, zero_mul]
      rw [NearFields.NearField.add_mul] at h0
      exact eq_neg_of_add_eq_zero_left h0
    rw [sub_eq_add_neg, NearFields.NearField.add_mul, hneg, ← sub_eq_add_neg]
  have hψinj : Function.Injective (fun x : F => x * (u : F) - x) := by
    intro x y hxy
    simp only at hxy
    have h3 : x * (u : F) - y * (u : F) = x - y :=
      sub_eq_sub_iff_sub_eq_sub.mp hxy
    have h1 : (x - y) * (u : F) = x - y := by
      rw [hsub_mul]
      exact h3
    by_contra hne
    have hxy0 : x - y ≠ 0 := sub_ne_zero.mpr hne
    have := mul_left_cancel₀ hxy0 (h1.trans (mul_one (x - y)).symm)
    exact hune this
  haveI : Finite F := Nat.finite_of_card_ne_zero
    (by rw [hm]; exact (Nat.pow_pos fc.p_prime.pos).ne')
  have hψsurj : Function.Surjective (fun x : F => x * (u : F) - x) :=
    Finite.injective_iff_surjective.mp hψinj
  -- decomposition: `T ⊔ P = R`.
  have hsup : T ⊔ fc.P = fc.invImageF model := by
    apply le_antisymm (sup_le hTle (fc.P_le_invImageF model))
    intro r hr
    have hrL : r ∈ L := fc.invImageF_le_centralizer model hr
    obtain ⟨z', hz'⟩ := (fc.mem_invImageF_iff model hrL).mp hr
    obtain ⟨x, hx⟩ := hψsurj (Multiplicative.toAdd z')
    obtain ⟨y', hy'⟩ := QuotientGroup.mk'_surjective N'
      (model.emb (Multiplicative.ofAdd x))
    have hy'R : (y' : G) ∈ fc.invImageF model :=
      ⟨y', Subgroup.mem_comap.mpr (by rw [hy']; exact ⟨Multiplicative.ofAdd x, rfl⟩), rfl⟩
    set t₀ : G := (y' : G)⁻¹ * (s * (y' : G) * s⁻¹) with ht₀def
    have ht₀R : t₀ ∈ fc.invImageF model :=
      (fc.invImageF model).mul_mem ((fc.invImageF model).inv_mem hy'R)
        (fc.conj_mem_invImageF model hsL hy'R)
    have ht₀inv : s * t₀ * s⁻¹ = t₀⁻¹ := by
      have hexp : s * t₀ * s⁻¹
          = (s * (y' : G) * s⁻¹)⁻¹ * (s * (s * (y' : G) * s⁻¹) * s⁻¹) := by
        rw [ht₀def]; group
      have hss : s * (s * (y' : G) * s⁻¹) * s⁻¹ = (y' : G) := by
        calc s * (s * (y' : G) * s⁻¹) * s⁻¹
            = (s * s) * (y' : G) * (s * s)⁻¹ := by group
          _ = (y' : G) := by rw [hs2]; group
      rw [hexp, hss, ht₀def]
      group
    have ht₀T : t₀ ∈ T := ⟨ht₀R, ht₀inv⟩
    have ht₀L : t₀ ∈ L := fc.invImageF_le_centralizer model ht₀R
    -- the class of `t₀` is `emb (x·u − x) = z'`.
    have hclass : QuotientGroup.mk' N' ⟨t₀, ht₀L⟩ = model.emb z' := by
      have hq : QuotientGroup.mk' N' ⟨t₀, ht₀L⟩
          = (QuotientGroup.mk' N' y')⁻¹
            * (QuotientGroup.mk' N' ⟨s, hsL⟩ * QuotientGroup.mk' N' y'
              * (QuotientGroup.mk' N' ⟨s, hsL⟩)⁻¹) := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      have hconj := model.qEquiv_conj sQ (Multiplicative.toAdd (Multiplicative.ofAdd x))
      rw [hq, hy']
      have hcoe : ((sQ : ↥fc.rankOneQuotient.Q) : ↥L ⧸ N')
          = QuotientGroup.mk' N' ⟨s, hsL⟩ := rfl
      rw [← hcoe]
      rw [show Multiplicative.toAdd (Multiplicative.ofAdd x) = x from rfl] at hconj
      rw [hconj]
      rw [← map_inv, ← map_mul]
      congr 1
      have hx' : x * ((model.qEquiv sQ⁻¹ : Fˣ) : F) - x = Multiplicative.toAdd z' := hx
      have hofadd : (Multiplicative.ofAdd x)⁻¹
          * Multiplicative.ofAdd (x * ((model.qEquiv sQ⁻¹ : Fˣ) : F))
          = Multiplicative.ofAdd (x * ((model.qEquiv sQ⁻¹ : Fˣ) : F) - x) := by
        rw [← ofAdd_neg, ← ofAdd_add]
        congr 1
        abel
      rw [hofadd, hx']
      rfl
    -- `r·t₀⁻¹ ∈ N = P`, so `r ∈ T ⊔ P`.
    have hdiffQ : QuotientGroup.mk' N' ((⟨r, hrL⟩ : ↥L) * (⟨t₀, ht₀L⟩ : ↥L)⁻¹) = 1 := by
      rw [map_mul, map_inv, hclass, ← hz', mul_inv_cancel]
    have hdiffN : (⟨r, hrL⟩ : ↥L) * (⟨t₀, ht₀L⟩ : ↥L)⁻¹ ∈ N' := by
      rw [QuotientGroup.mk'_apply] at hdiffQ
      exact (QuotientGroup.eq_one_iff _).mp hdiffQ
    have hkP : r * t₀⁻¹ ∈ fc.P := by
      have hker : r * t₀⁻¹ ∈ fc.kernelN := ⟨_, hdiffN, rfl⟩
      rwa [fc.kernelN_eq_P ind] at hker
    have hre : r = (r * t₀⁻¹) * t₀ := by group
    rw [hre]
    exact Subgroup.mul_mem _ ((le_sup_right : fc.P ≤ T ⊔ fc.P) hkP)
      ((le_sup_left : T ≤ T ⊔ fc.P) ht₀T)
  have hTeq : fc.sInvertedT model = T := by
    rw [sInvertedT, ← hsdef]
    exact Subgroup.closure_eq T
  rw [hTeq]
  exact ⟨hTle, fun x hx => hx.2, hsup, hTP⟩

include model in
/-- Membership in `T` (once `R` is abelian): exactly the elements of `R` inverted by the
distinguished involution. -/
theorem mem_sInvertedT_iff
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) {x : G} :
    x ∈ fc.sInvertedT model ↔ x ∈ fc.invImageF model ∧
      fc.toHypothesis.distinguishedInvolution * x
        * fc.toHypothesis.distinguishedInvolution⁻¹ = x⁻¹ := by
  constructor
  · intro hx
    exact ⟨(fc.sInvertedT_spec model ind hB2 hm).1 hx,
      (fc.sInvertedT_spec model ind hB2 hm).2.1 x hx⟩
  · intro hx
    exact Subgroup.subset_closure hx

include model in
/-- **`C_Q(P)` normalizes `T`** (step (11), p. 112): the distinguished involution is
central in `Q`, so conjugation by `a ∈ C_Q(P)` preserves the `s`-inverted condition. -/
theorem conj_mem_sInvertedT_of_mem_Q
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) {a x : G}
    (haQ : a ∈ fc.toHypothesis.Q) (haL : a ∈ Subgroup.centralizer (fc.P : Set G))
    (hx : x ∈ fc.sInvertedT model) : a * x * a⁻¹ ∈ fc.sInvertedT model := by
  rw [fc.mem_sInvertedT_iff model ind hB2 hm] at hx ⊢
  set s : G := fc.toHypothesis.distinguishedInvolution with hsdef
  refine ⟨fc.conj_mem_invImageF model haL hx.1, ?_⟩
  have h1 : s * a = a * s := fc.distinguishedInvolution_commute_of_mem_Q haQ
  have h2 : a⁻¹ * s⁻¹ = s⁻¹ * a⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, h1]
  calc s * (a * x * a⁻¹) * s⁻¹
      = (s * a) * x * (a⁻¹ * s⁻¹) := by group
    _ = (a * s) * x * (s⁻¹ * a⁻¹) := by rw [h1, h2]
    _ = a * (s * x * s⁻¹) * a⁻¹ := by group
    _ = a * x⁻¹ * a⁻¹ := by rw [hx.2]
    _ = (a * x * a⁻¹)⁻¹ := by group

include model in
/-- **`w`-conjugates of the distinguished involution differ by `P`** ((11), the
`C_W(P)`-normalization input): the faithful quotient `H̄` has a *unique* involution
(`unique_involution_in_H`), so `[w·s·w⁻¹] = [s]` and the difference lies in `N = P`. -/
theorem exists_conj_distinguishedInvolution_mem_P
    (ind : Hypothesis.TheoremAInductionBelow G Ω) {w : G}
    (hwW : w ∈ fc.toHypothesis.W) (hwP : w ∈ Subgroup.centralizer (fc.P : Set G)) :
    ∃ y ∈ fc.P, w * fc.toHypothesis.distinguishedInvolution * w⁻¹
      = fc.toHypothesis.distinguishedInvolution * y := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  set s : G := fc.toHypothesis.distinguishedInvolution with hsdef
  have hsL : s ∈ L :=
    fc.toHypothesis.distinguishedInvolution_mem_centralizer_of_le_V fc.P_le_V
  have hs2 : s * s = 1 := by
    have h := fc.toHypothesis.distinguishedInvolution_sq
    rwa [pow_two] at h
  have hcL : w * s * w⁻¹ ∈ L := L.mul_mem (L.mul_mem hwP hsL) (L.inv_mem hwP)
  have hsQ : s ∈ fc.toHypothesis.Q :=
    fc.toHypothesis.mem_Q_of_sq_eq_one_of_mem_H
      fc.toHypothesis.distinguishedInvolution_mem_H
      fc.toHypothesis.distinguishedInvolution_sq
  -- `[s] ∈ H̄`, an involution ≠ 1.
  have hsbarQ : QuotientGroup.mk' N' ⟨s, hsL⟩ ∈ fc.rankOneQuotient.Q :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hsQ)
  have hsbarH : QuotientGroup.mk' N' ⟨s, hsL⟩ ∈ fc.rankOneQuotient.H :=
    fc.rankOneQuotient.Q_le_H hsbarQ
  have hsb2 : (QuotientGroup.mk' N' ⟨s, hsL⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have h1 : (⟨s, hsL⟩ : ↥L) ^ 2 = 1 := by
      apply Subtype.ext
      have := hs2
      rw [pow_two]
      exact this
    rw [h1, map_one]
  have hsb1 : QuotientGroup.mk' N' ⟨s, hsL⟩ ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply] at h
    have hsN : (⟨s, hsL⟩ : ↥L) ∈ N' := (QuotientGroup.eq_one_iff _).mp h
    have hND : N' ≤ fc.toHypothesis.D.subgroupOf L := by
      rw [hN'def, fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
      exact inf_le_left
    have hsD : s ∈ fc.toHypothesis.D := Subgroup.mem_subgroupOf.mp (hND hsN)
    have hbot : s ∈ fc.toHypothesis.Q ⊓ fc.toHypothesis.D := ⟨hsQ, hsD⟩
    rw [fc.toHypothesis.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
    exact fc.toHypothesis.distinguishedInvolution_ne_one hbot
  -- `[w s w⁻¹] = [w]·[s]·[w]⁻¹ ∈ H̄`, an involution ≠ 1.
  have hwD : QuotientGroup.mk' N' ⟨w, hwP⟩ ∈ fc.rankOneQuotient.D :=
    (fc.sigmaElt hwW hwP).2
  have hwH : QuotientGroup.mk' N' ⟨w, hwP⟩ ∈ fc.rankOneQuotient.H := by
    have hDH : fc.rankOneQuotient.D ≤ fc.rankOneQuotient.H := by
      rw [fc.rankOneQuotient.D_def]; exact inf_le_left
    exact hDH hwD
  have hceq : QuotientGroup.mk' N' ⟨w * s * w⁻¹, hcL⟩
      = QuotientGroup.mk' N' ⟨w, hwP⟩ * QuotientGroup.mk' N' ⟨s, hsL⟩
        * (QuotientGroup.mk' N' ⟨w, hwP⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hcbH : QuotientGroup.mk' N' ⟨w * s * w⁻¹, hcL⟩ ∈ fc.rankOneQuotient.H := by
    rw [hceq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwH hsbarH) (Subgroup.inv_mem _ hwH)
  have hcb2 : (QuotientGroup.mk' N' ⟨w * s * w⁻¹, hcL⟩) ^ 2 = 1 := by
    have hBB : QuotientGroup.mk' N' ⟨s, hsL⟩ * QuotientGroup.mk' N' ⟨s, hsL⟩ = 1 := by
      have h := hsb2
      rwa [pow_two] at h
    rw [hceq, pow_two]
    calc (QuotientGroup.mk' N' ⟨w, hwP⟩ * QuotientGroup.mk' N' ⟨s, hsL⟩
          * (QuotientGroup.mk' N' ⟨w, hwP⟩)⁻¹)
        * (QuotientGroup.mk' N' ⟨w, hwP⟩ * QuotientGroup.mk' N' ⟨s, hsL⟩
          * (QuotientGroup.mk' N' ⟨w, hwP⟩)⁻¹)
        = QuotientGroup.mk' N' ⟨w, hwP⟩
          * (QuotientGroup.mk' N' ⟨s, hsL⟩ * QuotientGroup.mk' N' ⟨s, hsL⟩)
          * (QuotientGroup.mk' N' ⟨w, hwP⟩)⁻¹ := by group
      _ = 1 := by rw [hBB, mul_one, mul_inv_cancel]
  have hcb1 : QuotientGroup.mk' N' ⟨w * s * w⁻¹, hcL⟩ ≠ 1 := by
    rw [hceq]
    intro h
    have h2 : QuotientGroup.mk' N' ⟨s, hsL⟩ = 1 := by
      have h3 := congrArg (fun z => (QuotientGroup.mk' N' ⟨w, hwP⟩)⁻¹ * z
        * QuotientGroup.mk' N' ⟨w, hwP⟩) h
      simpa [mul_assoc] using h3
    exact hsb1 h2
  -- uniqueness in `H̄` forces the classes equal.
  obtain ⟨u₀, -, hu₀uniq⟩ := model.unique_involution_in_H
  have h1 : (⟨QuotientGroup.mk' N' ⟨s, hsL⟩, hsbarH⟩ : ↥fc.rankOneQuotient.H) = u₀ := by
    apply hu₀uniq
    constructor
    · exact hsb2
    · exact fun h => hsb1 h
  have h2 : (⟨QuotientGroup.mk' N' ⟨w * s * w⁻¹, hcL⟩, hcbH⟩ :
      ↥fc.rankOneQuotient.H) = u₀ := by
    apply hu₀uniq
    constructor
    · exact hcb2
    · exact fun h => hcb1 h
  have h3 : QuotientGroup.mk' N' ⟨w * s * w⁻¹, hcL⟩ = QuotientGroup.mk' N' ⟨s, hsL⟩ :=
    congrArg Subtype.val (h2.trans h1.symm)
  -- descend: `(w s w⁻¹)·s⁻¹ ∈ N = P`.
  have hdQ : QuotientGroup.mk' N' ((⟨w * s * w⁻¹, hcL⟩ : ↥L) * (⟨s, hsL⟩ : ↥L)⁻¹) = 1 := by
    rw [map_mul, map_inv, h3, mul_inv_cancel]
  have hdN : (⟨w * s * w⁻¹, hcL⟩ : ↥L) * (⟨s, hsL⟩ : ↥L)⁻¹ ∈ N' := by
    rw [QuotientGroup.mk'_apply] at hdQ
    exact (QuotientGroup.eq_one_iff _).mp hdQ
  have hyP : w * s * w⁻¹ * s⁻¹ ∈ fc.P := by
    have hker : w * s * w⁻¹ * s⁻¹ ∈ fc.kernelN := ⟨_, hdN, rfl⟩
    rwa [fc.kernelN_eq_P ind] at hker
  refine ⟨w * s * w⁻¹ * s⁻¹, hyP, ?_⟩
  -- `w s w⁻¹ = y·s = s·y` (`s` centralizes `P ∋ y`).
  have hcs : (w * s * w⁻¹ * s⁻¹) * s = s * (w * s * w⁻¹ * s⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hsL _ hyP)
  calc w * s * w⁻¹ = (w * s * w⁻¹ * s⁻¹) * s := by group
    _ = s * (w * s * w⁻¹ * s⁻¹) := hcs

include model in
/-- **`C_W(P)` normalizes `T`** (step (11), p. 112): `w`-conjugation moves `s` only by a
`P`-correction (`exists_conj_distinguishedInvolution_mem_P`), and `P` is central in `R`,
so the `s`-inverted condition is preserved. -/
theorem conj_mem_sInvertedT_of_mem_centralizer_W
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) {w x : G}
    (hwW : w ∈ fc.toHypothesis.W) (hwP : w ∈ Subgroup.centralizer (fc.P : Set G))
    (hx : x ∈ fc.sInvertedT model) : w * x * w⁻¹ ∈ fc.sInvertedT model := by
  rw [fc.mem_sInvertedT_iff model ind hB2 hm] at hx ⊢
  set s : G := fc.toHypothesis.distinguishedInvolution with hsdef
  refine ⟨fc.conj_mem_invImageF model hwP hx.1, ?_⟩
  obtain ⟨y, hyP, hws⟩ := fc.exists_conj_distinguishedInvolution_mem_P model ind
    (fc.toHypothesis.W.inv_mem hwW)
    ((Subgroup.centralizer (fc.P : Set G)).inv_mem hwP)
  -- `w⁻¹ s w = s y` (with `(w⁻¹)⁻¹ = w`), so
  -- `s (w x w⁻¹) s⁻¹ = w (s y) x (s y)⁻¹ w⁻¹ = w (s x s⁻¹) w⁻¹` (P central in `R`).
  rw [inv_inv] at hws
  have hyx : y * x * y⁻¹ = x := by
    have hc := fc.P_le_center_invImageF model hyP hx.1
    rw [← hc]
    group
  have hkey : s * (w * x * w⁻¹) * s⁻¹ = w * ((s * y) * x * (s * y)⁻¹) * w⁻¹ := by
    have h1 : s * (w * x * w⁻¹) * s⁻¹
        = w * ((w⁻¹ * s * w) * x * (w⁻¹ * s * w)⁻¹) * w⁻¹ := by group
    rw [h1, hws]
  rw [hkey]
  have h2 : (s * y) * x * (s * y)⁻¹ = s * (y * x * y⁻¹) * s⁻¹ := by group
  rw [h2, hyx, hx.2]
  group

include model in
/-- **`↑R = ↑T·↑P`** (set product): `P` is central in `R`, hence normalizes `T`
pointwise, and `T ⊔ P = R`. -/
theorem coe_invImageF_eq_sInvertedT_mul_P
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    ((fc.invImageF model : Subgroup G) : Set G)
      = (fc.sInvertedT model : Set G) * (fc.P : Set G) := by
  obtain ⟨hTle, -, hTsup, -⟩ := fc.sInvertedT_spec model ind hB2 hm
  have hPnormT : fc.P ≤ Subgroup.normalizer ((fc.sInvertedT model : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_set_normalizer_iff]
    intro τ
    have hfix : ∀ τ' ∈ fc.sInvertedT model, y * τ' * y⁻¹ = τ' := by
      intro τ' hτ'
      have hc := fc.P_le_center_invImageF model hy (hTle hτ')
      rw [← hc]
      group
    constructor
    · intro hτ
      rw [hfix τ hτ]
      exact hτ
    · intro hτ'
      have h1 := hfix _ hτ'
      have h2 : y * τ * y⁻¹ = τ := by
        have h3 := congrArg (fun z => y⁻¹ * z * y) h1
        simpa [mul_assoc] using h3
      rw [← h2]
      exact hτ'
  rw [← hTsup]
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ hPnormT

include model in
/-- **Step (11), freeness of the `C_Q(P)`-action on `𝒜 − {P}`** (p. 112): a nonidentity
`a ∈ C_Q(P)` normalizes no order-`p` subgroup `P₁ ≤ R` outside `T` except `P` itself —
`[a, P₁] ≤ P₁ ⊓ T = ⊥` (via the `T`-normalization and `a` centralizing `R/T`), so `a`
centralizes `P₁`; but `a` is fixed-point-free on the translations, forcing `P₁ ≤ P`. -/
theorem eq_P_of_prime_order_conj_invariant
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) {a : G}
    (haQ : a ∈ fc.toHypothesis.Q) (haL : a ∈ Subgroup.centralizer (fc.P : Set G))
    (ha1 : a ≠ 1)
    {P₁ : Subgroup G} (hP₁R : P₁ ≤ fc.invImageF model)
    (hP₁c : Nat.card ↥P₁ = fc.p) (hP₁T : ¬ P₁ ≤ fc.sInvertedT model)
    (hnorm : ∀ x ∈ P₁, a * x * a⁻¹ ∈ P₁) : P₁ = fc.P := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  set T : Subgroup G := fc.sInvertedT model with hTdef
  obtain ⟨hTle, -, hTsup, -⟩ := fc.sInvertedT_spec model ind hB2 hm
  -- `P₁ ⊓ T = ⊥` (prime order + not contained).
  have hinf : P₁ ⊓ T = ⊥ := by
    have hdvd : Nat.card ↥(P₁ ⊓ T) ∣ fc.p := by
      rw [← hP₁c]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime fc.p_prime).mp hdvd with h1 | hp
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : P₁ ⊓ T = P₁ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp, hP₁c])
      exact hP₁T (heq ▸ inf_le_right)
  have hcoe := fc.coe_invImageF_eq_sInvertedT_mul_P model ind hB2 hm
  -- `a` centralizes `P₁`.
  have hcen : ∀ x ∈ P₁, a * x * a⁻¹ = x := by
    intro x hx
    have hxR : x ∈ fc.invImageF model := hP₁R hx
    have hx' : x ∈ ((T : Set G) * (fc.P : Set G)) := by
      rw [← hcoe]
      exact hxR
    obtain ⟨τ, hτ, y, hy, rfl⟩ := hx'
    have hay : a * y * a⁻¹ = y := by
      have hc := Subgroup.mem_centralizer_iff.mp haL y hy
      rw [← hc]
      group
    have hcommT : a * (τ * y) * a⁻¹ * (τ * y)⁻¹ ∈ T := by
      have hkey : a * (τ * y) * a⁻¹ * (τ * y)⁻¹
          = (a * τ * a⁻¹) * ((a * y * a⁻¹) * y⁻¹) * τ⁻¹ := by group
      rw [hkey, hay, mul_inv_cancel, mul_one]
      exact T.mul_mem
        (fc.conj_mem_sInvertedT_of_mem_Q model ind hB2 hm haQ haL hτ)
        (T.inv_mem hτ)
    have hcommP₁ : a * (τ * y) * a⁻¹ * (τ * y)⁻¹ ∈ P₁ :=
      P₁.mul_mem (hnorm _ hx) (P₁.inv_mem hx)
    have hbot : a * (τ * y) * a⁻¹ * (τ * y)⁻¹ ∈ P₁ ⊓ T := ⟨hcommP₁, hcommT⟩
    rw [hinf, Subgroup.mem_bot] at hbot
    exact mul_inv_eq_one.mp hbot
  -- `a` is fixed-point-free on the translations: `P₁ ≤ P`.
  have haLmem : a ∈ L := haL
  have habarQ : QuotientGroup.mk' N' ⟨a, haLmem⟩ ∈ fc.rankOneQuotient.Q :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr haQ)
  set aQ : ↥fc.rankOneQuotient.Q := ⟨QuotientGroup.mk' N' ⟨a, haLmem⟩, habarQ⟩ with haQdef
  have haQne : aQ ≠ 1 := by
    intro h
    have h1 : QuotientGroup.mk' N' ⟨a, haLmem⟩ = 1 := congrArg Subtype.val h
    rw [QuotientGroup.mk'_apply] at h1
    have haN : (⟨a, haLmem⟩ : ↥L) ∈ N' := (QuotientGroup.eq_one_iff _).mp h1
    have hND : N' ≤ fc.toHypothesis.D.subgroupOf L := by
      rw [hN'def, fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
      exact inf_le_left
    have haD : a ∈ fc.toHypothesis.D := Subgroup.mem_subgroupOf.mp (hND haN)
    have hbot : a ∈ fc.toHypothesis.Q ⊓ fc.toHypothesis.D := ⟨haQ, haD⟩
    rw [fc.toHypothesis.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
    exact ha1 hbot
  have huane : ((model.qEquiv aQ⁻¹ : Fˣ) : F) ≠ 1 := by
    intro h
    have h1 : model.qEquiv aQ⁻¹ = 1 := Units.ext h
    have h2 : aQ⁻¹ = 1 := model.qEquiv.injective (by rw [h1, map_one])
    exact haQne (by rwa [inv_eq_one] at h2)
  have hle : P₁ ≤ fc.P := by
    intro x hx
    have hxR : x ∈ fc.invImageF model := hP₁R hx
    have hxL : x ∈ L := fc.invImageF_le_centralizer model hxR
    obtain ⟨z', hz'⟩ := (fc.mem_invImageF_iff model hxL).mp hxR
    have hfix := hcen x hx
    have hqfix : (aQ : ↥L ⧸ N') * QuotientGroup.mk' N' ⟨x, hxL⟩ * (aQ : ↥L ⧸ N')⁻¹
        = QuotientGroup.mk' N' ⟨x, hxL⟩ := by
      have hcoeA : (aQ : ↥L ⧸ N') = QuotientGroup.mk' N' ⟨a, haLmem⟩ := rfl
      rw [hcoeA, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hfix
    have hconj := model.qEquiv_conj aQ (Multiplicative.toAdd z')
    rw [show Multiplicative.ofAdd (Multiplicative.toAdd z') = z' from rfl] at hconj
    have hz'' : model.emb (Multiplicative.ofAdd
        (Multiplicative.toAdd z' * ((model.qEquiv aQ⁻¹ : Fˣ) : F))) = model.emb z' := by
      rw [← hconj, hz', hqfix]
    have h6 := model.emb_injective hz''
    have h7 := congrArg Multiplicative.toAdd h6
    rw [show Multiplicative.toAdd (Multiplicative.ofAdd (Multiplicative.toAdd z'
      * ((model.qEquiv aQ⁻¹ : Fˣ) : F))) = Multiplicative.toAdd z'
        * ((model.qEquiv aQ⁻¹ : Fˣ) : F) from rfl] at h7
    have hz0 : Multiplicative.toAdd z' = 0 := by
      by_contra hne
      exact huane (mul_left_cancel₀ hne (h7.trans (mul_one _).symm))
    have hz1 : z' = 1 := by
      have h8 := congrArg Multiplicative.ofAdd hz0
      rwa [show Multiplicative.ofAdd (Multiplicative.toAdd z') = z' from rfl] at h8
    have hxN : (⟨x, hxL⟩ : ↥L) ∈ N' := by
      have h9 : QuotientGroup.mk' N' ⟨x, hxL⟩ = 1 := by
        rw [← hz', hz1, map_one]
      rw [QuotientGroup.mk'_apply] at h9
      exact (QuotientGroup.eq_one_iff _).mp h9
    have hker : x ∈ fc.kernelN := ⟨_, hxN, rfl⟩
    rwa [fc.kernelN_eq_P ind] at hker
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [fc.card_P, hP₁c])

/-- **Elements of `P^#` are not strongly real** (step (12) input, p. 112): a strongly
real `x ∈ P^#` has `x² ≠ 1` (odd prime order), so Lemma 3 makes `|C_G(x)|` odd — but
`C_G(x) = C_G(P)` contains the distinguished involution. -/
theorem not_isStronglyReal_of_mem_P {x : G} (hx : x ∈ fc.P) (hx1 : x ≠ 1) :
    ¬ IsStronglyReal x := by
  intro hsr
  -- `x` generates `P`, so `C_G(P) ≤ C_G(x)`.
  have hord : orderOf x = fc.p := by
    have h1 : orderOf x ∣ fc.p := by
      have h2 : orderOf (⟨x, hx⟩ : ↥fc.P) ∣ Nat.card ↥fc.P := orderOf_dvd_natCard _
      rwa [fc.card_P, Subgroup.orderOf_mk] at h2
    rcases (Nat.dvd_prime fc.p_prime).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hord] at h1
    have h6 : fc.p = 2 :=
      (Nat.prime_dvd_prime_iff_eq fc.p_prime Nat.prime_two).mp h1
    rcases fc.p_odd with ⟨k, hk⟩
    omega
  obtain ⟨-, hodd⟩ :=
    fc.toHypothesis.stronglyReal_normalForm_and_centralizer_odd hsr hx2
  -- the distinguished involution centralizes `x ∈ P`, giving even order.
  set s : G := fc.toHypothesis.distinguishedInvolution with hsdef
  have hsC : s ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp
      (fc.toHypothesis.distinguishedInvolution_mem_centralizer_of_le_V fc.P_le_V) y hx
  have hs2 : orderOf s = 2 := by
    have h1 : s ^ 2 = 1 := fc.toHypothesis.distinguishedInvolution_sq
    have h2 : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h)
        fc.toHypothesis.distinguishedInvolution_ne_one
    · exact h
  have heven : (2 : ℕ) ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := by
    have h1 : orderOf (⟨s, hsC⟩ : ↥(Subgroup.centralizer ({x} : Set G)))
        ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hs2] at h1
  rcases hodd with ⟨k, hk⟩
  omega

include model in
/-- **Elements of `T` are strongly real** (step (12) input): `x = s·(s·x)`, and `s·x`
is an involution because `s` inverts `x` — while `x ≠ s` since `|R|` is odd. -/
theorem isStronglyReal_of_mem_sInvertedT
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) {x : G}
    (hx : x ∈ fc.sInvertedT model) : IsStronglyReal x := by
  rw [fc.mem_sInvertedT_iff model ind hB2 hm] at hx
  set s : G := fc.toHypothesis.distinguishedInvolution with hsdef
  have hs2 : s * s = 1 := by
    have h := fc.toHypothesis.distinguishedInvolution_sq
    rwa [pow_two] at h
  have hsinv : s⁻¹ = s := by
    rw [← mul_one s⁻¹, ← hs2, ← mul_assoc, inv_mul_cancel, one_mul]
  -- `s x` is an involution: `(s x)² = (s x s⁻¹)·(s² x)·… = x⁻¹·x = 1`.
  have hsx2 : (s * x) * (s * x) = 1 := by
    have h1 : (s * x) * (s * x) = (s * x * s⁻¹) * ((s * s) * x) := by
      group
    rw [h1, hx.2, hs2, one_mul, inv_mul_cancel]
  -- `s x ≠ 1`: else `x = s`, but `x ∈ R` has odd order and `s` has order `2`.
  have hxo : Odd (orderOf x) := by
    have h1 : orderOf x ∣ Nat.card ↥(fc.invImageF model) := by
      have h2 : orderOf (⟨x, hx.1⟩ : ↥(fc.invImageF model))
          ∣ Nat.card ↥(fc.invImageF model) := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk] at h2
    rw [fc.card_invImageF model ind, hm, fc.card_P] at h1
    have hodd : Odd (fc.p ^ m * fc.p) := by
      rcases fc.p_odd with ⟨k, hk⟩
      exact (Odd.pow ⟨k, hk⟩).mul ⟨k, hk⟩
    exact hodd.of_dvd_nat h1
  have hsx1 : s * x ≠ 1 := by
    intro h
    have hxs : x = s := by
      have h1 : x = s⁻¹ := by
        have h2 := congrArg (fun z => s⁻¹ * z) h
        simpa [mul_assoc] using h2
      rw [h1, hsinv]
    rw [hxs] at hxo
    have h2 : orderOf s = 2 := by
      have h3 : s ^ 2 = 1 := fc.toHypothesis.distinguishedInvolution_sq
      have h4 : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one h3
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h)
          fc.toHypothesis.distinguishedInvolution_ne_one
      · exact h
    rw [h2] at hxo
    rcases hxo with ⟨k, hk⟩
    omega
  refine ⟨s, ⟨?_, fc.toHypothesis.distinguishedInvolution_ne_one⟩, s * x,
    ⟨by rw [pow_two]; exact hsx2, hsx1⟩, ?_⟩
  · rw [pow_two]
    exact hs2
  · rw [← mul_assoc, hs2, one_mul]

include model in
/-- **A conjugate of `P` meets `T` trivially** (step (12), p. 112): nonidentity elements
of `g·P·g⁻¹` are not strongly real (conjugation preserves strong reality and
`not_isStronglyReal_of_mem_P`), while nonidentity elements of `T` are. -/
theorem conj_P_inf_sInvertedT_eq_bot
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) (g : G) :
    (MulAut.conj g • fc.P) ⊓ fc.sInvertedT model = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxT⟩
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hsr : IsStronglyReal x :=
    fc.isStronglyReal_of_mem_sInvertedT model ind hB2 hm hxT
  -- transport back along the conjugation.
  obtain ⟨y, hyP, hyx⟩ := hxP
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    rw [← hyx, h]
    simp
  obtain ⟨u, hu, v, hv, huv⟩ := hsr
  have hysr : IsStronglyReal y := by
    refine ⟨g⁻¹ * u * g, ⟨?_, ?_⟩, g⁻¹ * v * g, ⟨?_, ?_⟩, ?_⟩
    · rw [pow_two]
      have h1 := hu.1
      rw [pow_two] at h1
      calc (g⁻¹ * u * g) * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
        _ = 1 := by rw [h1]; group
    · intro h
      apply hu.2
      have h2 := congrArg (fun z => g * z * g⁻¹) h
      simpa [mul_assoc] using h2
    · rw [pow_two]
      have h1 := hv.1
      rw [pow_two] at h1
      calc (g⁻¹ * v * g) * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g := by group
        _ = 1 := by rw [h1]; group
    · intro h
      apply hv.2
      have h2 := congrArg (fun z => g * z * g⁻¹) h
      simpa [mul_assoc] using h2
    · have h3 : y = g⁻¹ * x * g := by
        rw [← hyx]
        simp [MulAut.conj_apply]
        group
      rw [h3, huv]
      group
  exact fc.not_isStronglyReal_of_mem_P hyP hy1 hysr

include model in
/-- **`R` has exponent `p`** (the counting input of step (12)): the `T`-component has
exponent `p` because the translations do (`char F = p`, steps (7)/(9)) and `T ⊓ P = ⊥`;
the `P`-component because `|P| = p`. -/
theorem pow_p_eq_one_of_mem_invImageF
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) {r : G}
    (hr : r ∈ fc.invImageF model) : r ^ fc.p = 1 := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N' : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hN'def
  obtain ⟨-, -, -, hTinf⟩ := fc.sInvertedT_spec model ind hB2 hm
  have hr' : r ∈ ((fc.sInvertedT model : Subgroup G) : Set G) * (fc.P : Set G) := by
    rw [← fc.coe_invImageF_eq_sInvertedT_mul_P model ind hB2 hm]
    exact hr
  obtain ⟨τ, hτ, y, hy, rfl⟩ := hr'
  -- the `T`-component: `τ^p ∈ T ⊓ P = ⊥`.
  have hτR : τ ∈ fc.invImageF model :=
    (fc.sInvertedT_spec model ind hB2 hm).1 hτ
  have hτL : τ ∈ L := fc.invImageF_le_centralizer model hτR
  obtain ⟨z', hz'⟩ := (fc.mem_invImageF_iff model hτL).mp hτR
  have hchar := fc.char_eq_p model hB2
  have hz0 : z' ^ fc.p = 1 := by
    have h1 : fc.p • (Multiplicative.toAdd z') = 0 := by
      rw [← hchar]
      exact model.char_spec _
    have h2 : z' ^ fc.p
        = Multiplicative.ofAdd (fc.p • Multiplicative.toAdd z') := rfl
    rw [h2, h1]
    rfl
  have hτpP : τ ^ fc.p ∈ fc.P := by
    have hq : QuotientGroup.mk' N' ((⟨τ, hτL⟩ : ↥L) ^ fc.p) = 1 := by
      rw [map_pow, ← hz', ← map_pow, hz0, map_one]
    have hN : (⟨τ, hτL⟩ : ↥L) ^ fc.p ∈ N' := by
      rw [QuotientGroup.mk'_apply] at hq
      exact (QuotientGroup.eq_one_iff _).mp hq
    have hker : τ ^ fc.p ∈ fc.kernelN := ⟨_, hN, rfl⟩
    rwa [fc.kernelN_eq_P ind] at hker
  have hτp1 : τ ^ fc.p = 1 := by
    have hmem : τ ^ fc.p ∈ fc.sInvertedT model ⊓ fc.P :=
      ⟨(fc.sInvertedT model).pow_mem hτ _, hτpP⟩
    rwa [hTinf, Subgroup.mem_bot] at hmem
  -- the `P`-component: `y^p = 1` (`|P| = p`).
  have hyp1 : y ^ fc.p = 1 := by
    have h1 : (⟨y, hy⟩ : ↥fc.P) ^ Nat.card ↥fc.P = 1 := pow_card_eq_one'
    rw [fc.card_P] at h1
    have h2 := congrArg Subtype.val h1
    simpa using h2
  -- combine in the abelian `R`.
  have hcomm : Commute τ y :=
    fc.invImageF_mul_comm model ind hB2 hm τ hτR y (fc.P_le_invImageF model hy)
  rw [hcomm.mul_pow, hτp1, hyp1, one_mul]

include model in
/-- **`|T| = |F|`**: `T` complements `P` in `R` and `|R| = |F|·|P|`. -/
theorem card_sInvertedT
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    Nat.card ↥(fc.sInvertedT model) = Nat.card F := by
  obtain ⟨-, -, hTsup, hTinf⟩ := fc.sInvertedT_spec model ind hB2 hm
  set T : Subgroup G := fc.sInvertedT model with hTdef
  have hmul : ∀ x ∈ T ⊔ fc.P, ∃ a ∈ T, ∃ b ∈ fc.P, a * b = x := by
    intro x hx
    rw [hTsup] at hx
    have hx' : x ∈ ((T : Set G) * (fc.P : Set G)) := by
      rw [← fc.coe_invImageF_eq_sInvertedT_mul_P model ind hB2 hm]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  have hPb : fc.P ⊓ T = ⊥ := by rw [inf_comm]; exact hTinf
  have hc := (Subgroup.isComplement'_subgroupOf_of_disjoint_mul_eq_univ
    (le_sup_right : fc.P ≤ T ⊔ fc.P) (le_sup_left : T ≤ T ⊔ fc.P) hPb hmul).card_mul
  have hTc : Nat.card ↥(T.subgroupOf (T ⊔ fc.P)) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hPc : Nat.card ↥(fc.P.subgroupOf (T ⊔ fc.P)) = Nat.card ↥fc.P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [hTc, hPc, hTsup] at hc
  have h3 : Nat.card ↥(fc.invImageF model) = Nat.card F * Nat.card ↥fc.P :=
    fc.card_invImageF model ind
  have hPpos : 0 < Nat.card ↥fc.P := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hPpos (hc.trans h3)

include model in
/-- **Every member of `𝒜` is generated by `x₀·t` for some `t ∈ T`** (the surjectivity
half of the step (12) count `|𝒜| = p^m`): an order-`p` subgroup `P₁ ≤ R` outside `T`
meets `T` trivially, hence injects into `R/T` (of order `p`), so it hits the coset
`T·x₀` of a fixed generator `x₀` of `P`. -/
theorem exists_mem_sInvertedT_zpowers_eq_of_prime_order
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) {x₀ : G} (hx₀ : x₀ ∈ fc.P) (hx₀1 : x₀ ≠ 1)
    {P₁ : Subgroup G} (hP₁R : P₁ ≤ fc.invImageF model)
    (hP₁c : Nat.card ↥P₁ = fc.p) (hP₁T : ¬ P₁ ≤ fc.sInvertedT model) :
    ∃ t ∈ fc.sInvertedT model, x₀ * t ∈ P₁ ∧ P₁ = Subgroup.zpowers (x₀ * t) := by
  classical
  obtain ⟨hTle, -, hTsup, hTinf⟩ := fc.sInvertedT_spec model ind hB2 hm
  set R : Subgroup G := fc.invImageF model with hRdef
  set T : Subgroup G := fc.sInvertedT model with hTdef
  have hab := fc.invImageF_mul_comm model ind hB2 hm
  -- `P₁ ⊓ T = ⊥` (prime order, not contained).
  have hinf : P₁ ⊓ T = ⊥ := by
    have hdvd : Nat.card ↥(P₁ ⊓ T) ∣ fc.p := by
      rw [← hP₁c]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime fc.p_prime).mp hdvd with h1 | hp
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : P₁ ⊓ T = P₁ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp, hP₁c])
      exact hP₁T (heq ▸ inf_le_right)
  -- work inside `↥R`: `T' := T.subgroupOf R` is normal (`R` is abelian).
  set T' : Subgroup ↥R := T.subgroupOf R with hT'def
  haveI hT'n : T'.Normal := by
    constructor
    intro τ hτ g
    rw [Subgroup.mem_subgroupOf] at hτ ⊢
    have hc : (g : G) * (τ : G) = (τ : G) * (g : G) := hab _ g.2 _ τ.2
    have he : ((g * τ * g⁻¹ : ↥R) : G) = (τ : G) := by
      push_cast
      rw [hc]
      group
    rw [he]
    exact hτ
  -- the quotient `R/T'` has order `p`.
  have hcardQ : Nat.card (↥R ⧸ T') = fc.p := by
    have h1 : Nat.card ↥R = Nat.card (↥R ⧸ T') * Nat.card ↥T' :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup T'
    have h2 : Nat.card ↥T' = Nat.card ↥T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv
    have h3 : Nat.card ↥R = Nat.card F * Nat.card ↥fc.P :=
      fc.card_invImageF model ind
    -- `|T| = |F|` from `|R| = |T|·|P|` (complement) — derive via the sup/inf data.
    have h4 : Nat.card ↥T * Nat.card ↥fc.P = Nat.card ↥R := by
      have hmul : ∀ x ∈ T ⊔ fc.P, ∃ a ∈ T, ∃ b ∈ fc.P, a * b = x := by
        intro x hx
        rw [hTsup] at hx
        have hx' : x ∈ ((T : Set G) * (fc.P : Set G)) := by
          rw [← fc.coe_invImageF_eq_sInvertedT_mul_P model ind hB2 hm]
          exact hx
        obtain ⟨a, ha, b, hb, rfl⟩ := hx'
        exact ⟨a, ha, b, hb, rfl⟩
      have hPb : fc.P ⊓ T = ⊥ := by rw [inf_comm]; exact hTinf
      have hc := (Subgroup.isComplement'_subgroupOf_of_disjoint_mul_eq_univ
        (le_sup_right : fc.P ≤ T ⊔ fc.P) (le_sup_left : T ≤ T ⊔ fc.P) hPb hmul).card_mul
      have hTc : Nat.card ↥(T.subgroupOf (T ⊔ fc.P)) = Nat.card ↥T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
      have hPc : Nat.card ↥(fc.P.subgroupOf (T ⊔ fc.P)) = Nat.card ↥fc.P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
      rw [hTc, hPc] at hc
      rw [hc, hTsup]
    have h5 : Nat.card ↥T = Nat.card F := by
      have hPpos : 0 < Nat.card ↥fc.P := Nat.card_pos
      have := h4.trans h3
      exact Nat.eq_of_mul_eq_mul_right hPpos this
    rw [h2, h5] at h1
    rw [h3, fc.card_P] at h1
    have hFpos : 0 < Nat.card F := by
      rw [hm]
      exact Nat.pow_pos fc.p_prime.pos
    -- `|F|·p = |R⧸T'|·|F|` ⟹ `|R⧸T'| = p`
    have h6 : Nat.card F * fc.p = Nat.card (↥R ⧸ T') * Nat.card F := h1
    have h7 : fc.p * Nat.card F = Nat.card (↥R ⧸ T') * Nat.card F := by
      rw [mul_comm]; exact h6
    exact (Nat.eq_of_mul_eq_mul_right hFpos h7).symm
  -- the composite `P₁ → R → R⧸T'` is injective, hence bijective onto the order-`p` quotient.
  set f : ↥P₁ →* ↥R ⧸ T' :=
    (QuotientGroup.mk' T').comp (Subgroup.inclusion hP₁R) with hfdef
  have hfinj : Function.Injective f := by
    intro u v huv
    have h1 : f (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h2 : Subgroup.inclusion hP₁R (u * v⁻¹) ∈ T' := by
      have h3 : QuotientGroup.mk' T' (Subgroup.inclusion hP₁R (u * v⁻¹)) = 1 := h1
      rw [QuotientGroup.mk'_apply] at h3
      exact (QuotientGroup.eq_one_iff _).mp h3
    rw [Subgroup.mem_subgroupOf] at h2
    have h4 : ((u * v⁻¹ : ↥P₁) : G) ∈ P₁ ⊓ T := ⟨(u * v⁻¹).2, h2⟩
    rw [hinf, Subgroup.mem_bot] at h4
    have h5 : (u * v⁻¹ : ↥P₁) = 1 := Subtype.ext h4
    have h6 := congrArg (fun z => z * v) h5
    simpa using h6
  have hfsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨hfinj, by rw [hP₁c, hcardQ]⟩).2
  -- hit the coset of `x₀`.
  have hx₀R : x₀ ∈ R := fc.P_le_invImageF model hx₀
  obtain ⟨ξ, hξ⟩ := hfsurj (QuotientGroup.mk' T' ⟨x₀, hx₀R⟩)
  have hdiff : (⟨(ξ : G), hP₁R ξ.2⟩ : ↥R) * (⟨x₀, hx₀R⟩ : ↥R)⁻¹ ∈ T' := by
    have h1 : QuotientGroup.mk' T'
        ((⟨(ξ : G), hP₁R ξ.2⟩ : ↥R) * (⟨x₀, hx₀R⟩ : ↥R)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      have h2 : QuotientGroup.mk' T' (⟨(ξ : G), hP₁R ξ.2⟩ : ↥R)
          = QuotientGroup.mk' T' (⟨x₀, hx₀R⟩ : ↥R) := hξ
      rw [h2, mul_inv_cancel]
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  rw [Subgroup.mem_subgroupOf] at hdiff
  -- `t := x₀⁻¹·ξ ∈ T` (using commutativity to swap the difference side).
  have htT : x₀⁻¹ * (ξ : G) ∈ T := by
    have hd : (ξ : G) * x₀⁻¹ ∈ T := hdiff
    have hc : (ξ : G) * x₀⁻¹ = x₀⁻¹ * (ξ : G) :=
      hab _ (hP₁R ξ.2) _ ((fc.invImageF model).inv_mem hx₀R)
    rwa [hc] at hd
  refine ⟨x₀⁻¹ * (ξ : G), htT, ?_, ?_⟩
  · have : x₀ * (x₀⁻¹ * (ξ : G)) = (ξ : G) := by group
    rw [this]
    exact ξ.2
  · -- `P₁` has prime order, so any nonidentity member generates it.
    have hξP₁ : x₀ * (x₀⁻¹ * (ξ : G)) ∈ P₁ := by
      have : x₀ * (x₀⁻¹ * (ξ : G)) = (ξ : G) := by group
      rw [this]
      exact ξ.2
    have hξ1 : x₀ * (x₀⁻¹ * (ξ : G)) ≠ 1 := by
      have heq : x₀ * (x₀⁻¹ * (ξ : G)) = (ξ : G) := by group
      rw [heq]
      intro h
      -- `ξ = 1` would send `f ξ = 1 = [x₀]`, forcing `x₀ ∈ T ⊓ P = ⊥`.
      have h1 : QuotientGroup.mk' T' (⟨x₀, hx₀R⟩ : ↥R) = 1 := by
        rw [← hξ]
        have h2 : (⟨(ξ : G), hP₁R ξ.2⟩ : ↥R) = 1 := Subtype.ext h
        change QuotientGroup.mk' T' (⟨(ξ : G), hP₁R ξ.2⟩ : ↥R) = 1
        rw [h2, map_one]
      rw [QuotientGroup.mk'_apply] at h1
      have h3 : (⟨x₀, hx₀R⟩ : ↥R) ∈ T' := (QuotientGroup.eq_one_iff _).mp h1
      rw [Subgroup.mem_subgroupOf] at h3
      have h4 : x₀ ∈ fc.P ⊓ T := ⟨hx₀, h3⟩
      rw [inf_comm, hTinf] at h4
      exact hx₀1 (Subgroup.mem_bot.mp h4)
    apply le_antisymm
    · -- `P₁ ≤ zpowers`: both have order `p` and `zpowers ≤ P₁`.
      have hle : Subgroup.zpowers (x₀ * (x₀⁻¹ * (ξ : G))) ≤ P₁ :=
        (Subgroup.zpowers_le).mpr hξP₁
      have hordz : orderOf (x₀ * (x₀⁻¹ * (ξ : G))) = fc.p := by
        have h1 : orderOf (x₀ * (x₀⁻¹ * (ξ : G))) ∣ fc.p := by
          have h2 : orderOf (⟨_, hξP₁⟩ : ↥P₁) ∣ Nat.card ↥P₁ := orderOf_dvd_natCard _
          rwa [hP₁c, Subgroup.orderOf_mk] at h2
        rcases (Nat.dvd_prime fc.p_prime).mp h1 with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hξ1
        · exact h
      have hcardz : Nat.card ↥(Subgroup.zpowers (x₀ * (x₀⁻¹ * (ξ : G)))) = fc.p := by
        rw [Nat.card_zpowers, hordz]
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hP₁c, hcardz])).ge
    · exact (Subgroup.zpowers_le).mpr hξP₁

include model in
/-- `p ∤ |Q̄|` (the multiplicative part has order `|F| − 1`). -/
theorem not_p_dvd_card_rankOneQ {m : ℕ} (hm : Nat.card F = fc.p ^ m) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).Q := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  haveI : Finite F := Nat.finite_of_card_ne_zero
    (by rw [hm]; exact (Nat.pow_pos fc.p_prime.pos).ne')
  have hQcard : Nat.card ↥(fc.rankOneQuotient).Q = fc.p ^ m - 1 := by
    haveI := Fintype.ofFinite F
    haveI := Classical.decEq F
    rw [Nat.card_congr model.qEquiv.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_units, ← Nat.card_eq_fintype_card, hm]
  have hm1 : 1 ≤ m := by
    by_contra hm0
    push Not at hm0
    interval_cases m
    have h2 : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hm] at h2
    simp at h2
  rw [hQcard]
  intro hdvd
  have hple : fc.p ∣ fc.p ^ m := dvd_pow_self _ (by omega)
  have h1 : fc.p ∣ 1 := by
    have := Nat.dvd_sub hple hdvd
    rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ fc.p_prime.pos)] at this
  exact fc.p_prime.one_lt.ne' (Nat.dvd_one.mp h1)

include model in
/-- **`N_G(P) ⊊ N_G(R)` in case (10.1)** (step (12) opening, p. 112): `C_G(P) = N_G(P)`
normalizes `R`, and normalizer growth inside a Sylow `p`-subgroup of `G` produces a
`p`-subgroup of `N_G(R)` strictly larger than the full `p`-part `p^{m+1}` of `C_G(P)`. -/
theorem normalizer_P_lt_normalizer_invImageF
    (ind : Hypothesis.TheoremAInductionBelow G Ω) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m)
    (hGp : fc.p ^ (m + 2) ∣ Nat.card G) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D →
      Subgroup.normalizer (fc.P : Set G)
        < Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  intro hSigma
  -- `≤`: `N_G(P) = C_G(P)` normalizes `R`.
  have hle : Subgroup.normalizer (fc.P : Set G)
      ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) := by
    rw [fc.normalizer_P_eq_centralizer]
    intro c hc
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact fc.conj_mem_invImageF model hc hn
    · intro hn
      have h1 := fc.conj_mem_invImageF model
        ((Subgroup.centralizer (fc.P : Set G)).inv_mem hc) hn
      simpa [mul_assoc] using h1
  refine lt_of_le_of_ne hle fun heq => ?_
  -- normalizer growth inside a Sylow `p`-subgroup.
  have hcardR : Nat.card ↥(fc.invImageF model) = fc.p ^ (m + 1) := by
    rw [fc.card_invImageF model ind, hm, fc.card_P]; ring
  have hRp : IsPGroup fc.p ↥(fc.invImageF model) := IsPGroup.of_card hcardR
  obtain ⟨X, hRX⟩ := hRp.exists_le_sylow
  have hXdvd : fc.p ^ (m + 2) ∣ Nat.card ↥(X : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity]
    exact pow_dvd_pow _ ((Nat.Prime.pow_dvd_iff_le_factorization fc.p_prime
      Nat.card_pos.ne').mp hGp)
  have hRltX : fc.invImageF model < (X : Subgroup G) := by
    refine lt_of_le_of_ne hRX fun h => ?_
    rw [← h, hcardR, Nat.pow_dvd_pow_iff_le_right fc.p_prime.one_lt] at hXdvd
    omega
  have hgrow := OddOrder.BG.Ch2.S08.lt_inf_normalizer_of_isPGroup_lt
    (p := fc.p) X.isPGroup' hRltX
  set Y : Subgroup G := (X : Subgroup G) ⊓
    Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) with hYdef
  -- `Y ≤ N_G(R) = N_G(P) = C_G(P)`, but `|Y| > p^{m+1}` = full `p`-part of `|C_G(P)|`.
  have hYC : Y ≤ Subgroup.centralizer (fc.P : Set G) := by
    refine le_trans inf_le_right ?_
    rw [← heq, fc.normalizer_P_eq_centralizer]
  have hYp : IsPGroup fc.p ↥Y := X.isPGroup'.to_le inf_le_left
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hYp
  have hlt : fc.p ^ (m + 1) < Nat.card ↥Y := by
    rw [← hcardR]
    have hdvd : Nat.card ↥(fc.invImageF model) ∣ Nat.card ↥Y :=
      Subgroup.card_dvd_of_le hgrow.le
    refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) fun heq2 => ?_
    exact hgrow.ne (Subgroup.eq_of_le_of_card_ge hgrow.le heq2.ge)
  have hCeq : Nat.card ↥(Subgroup.centralizer (fc.P : Set G))
      = fc.p ^ (m + 1) * (Nat.card ↥(fc.rankOneQuotient).Q
        * Nat.card ↥(fc.rankOneQuotient).D) := by
    rw [fc.card_centralizer_P model ind, fc.card_P, hm]; ring
  have hpc : ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).Q
      * Nat.card ↥(fc.rankOneQuotient).D :=
    fun hdvd => ((fc.p_prime.dvd_mul).mp hdvd).elim
      (fc.not_p_dvd_card_rankOneQ model hm) hSigma
  have hYdvd : Nat.card ↥Y ∣ Nat.card ↥(Subgroup.centralizer (fc.P : Set G)) :=
    Subgroup.card_dvd_of_le hYC
  rw [hCeq, hj] at hYdvd
  have hpc' : Nat.Coprime fc.p (Nat.card ↥(fc.rankOneQuotient).Q
      * Nat.card ↥(fc.rankOneQuotient).D) :=
    (Nat.Prime.coprime_iff_not_dvd fc.p_prime).mpr hpc
  have hjdvd : fc.p ^ j ∣ fc.p ^ (m + 1) :=
    (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left j hpc')) hYdvd
  have hle2 : Nat.card ↥Y ≤ fc.p ^ (m + 1) := by
    rw [hj]
    exact Nat.le_of_dvd (Nat.pow_pos fc.p_prime.pos) hjdvd
  omega

include model in
/-- **`|𝒜| = p^m`** (step (12), p. 112): the order-`p` subgroups of `R` outside `T` are
parametrized bijectively by `T` via `t ↦ ⟨x₀·t⟩` (`x₀` a fixed generator of `P`), and
`|T| = |F| = p^m`. -/
theorem ncard_prime_order_not_le_sInvertedT
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) {x₀ : G} (hx₀ : x₀ ∈ fc.P) (hx₀1 : x₀ ≠ 1) :
    Set.ncard {P₁ : Subgroup G | P₁ ≤ fc.invImageF model ∧
        Nat.card ↥P₁ = fc.p ∧ ¬ P₁ ≤ fc.sInvertedT model}
      = fc.p ^ m := by
  classical
  obtain ⟨hTle, -, hTsup, hTinf⟩ := fc.sInvertedT_spec model ind hB2 hm
  have hab := fc.invImageF_mul_comm model ind hB2 hm
  set A : Set (Subgroup G) := {P₁ : Subgroup G | P₁ ≤ fc.invImageF model ∧
      Nat.card ↥P₁ = fc.p ∧ ¬ P₁ ≤ fc.sInvertedT model} with hAdef
  have hx₀R : x₀ ∈ fc.invImageF model := fc.P_le_invImageF model hx₀
  have hx₀T : x₀ ∉ fc.sInvertedT model := by
    intro h
    have h1 : x₀ ∈ fc.sInvertedT model ⊓ fc.P := ⟨h, hx₀⟩
    rw [hTinf, Subgroup.mem_bot] at h1
    exact hx₀1 h1
  have hordx₀ : orderOf x₀ = fc.p := by
    have h1 : orderOf x₀ ∣ fc.p := by
      have h2 : orderOf (⟨x₀, hx₀⟩ : ↥fc.P) ∣ Nat.card ↥fc.P := orderOf_dvd_natCard _
      rwa [fc.card_P, Subgroup.orderOf_mk] at h2
    rcases (Nat.dvd_prime fc.p_prime).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx₀1
    · exact h
  -- the parametrization `f : T → 𝒜`.
  have hgen : ∀ t : ↥(fc.sInvertedT model), Subgroup.zpowers (x₀ * (t : G)) ∈ A := by
    intro t
    have htR : (t : G) ∈ fc.invImageF model := hTle t.2
    have hxtR : x₀ * (t : G) ∈ fc.invImageF model := (fc.invImageF model).mul_mem hx₀R htR
    have hxt1 : x₀ * (t : G) ≠ 1 := by
      intro h
      have h1 : x₀ = (t : G)⁻¹ := by
        have h2 := congrArg (fun z => z * (t : G)⁻¹) h
        simpa [mul_assoc] using h2
      exact hx₀T (h1 ▸ (fc.sInvertedT model).inv_mem t.2)
    have hord : orderOf (x₀ * (t : G)) = fc.p := by
      have h1 : orderOf (x₀ * (t : G)) ∣ fc.p := orderOf_dvd_of_pow_eq_one
        (fc.pow_p_eq_one_of_mem_invImageF model ind hB2 hm hxtR)
      rcases (Nat.dvd_prime fc.p_prime).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hxt1
      · exact h
    refine ⟨(Subgroup.zpowers_le).mpr hxtR, ?_, ?_⟩
    · rw [Nat.card_zpowers, hord]
    · intro h
      have h1 : x₀ * (t : G) ∈ fc.sInvertedT model := h (Subgroup.mem_zpowers _)
      have h2 : x₀ ∈ fc.sInvertedT model := by
        have h3 := (fc.sInvertedT model).mul_mem h1 ((fc.sInvertedT model).inv_mem t.2)
        simpa [mul_assoc] using h3
      exact hx₀T h2
  set f : ↥(fc.sInvertedT model) → ↥A :=
    fun t => ⟨Subgroup.zpowers (x₀ * (t : G)), hgen t⟩ with hfdef
  have hfinj : Function.Injective f := by
    intro t t' htt'
    have h1 : Subgroup.zpowers (x₀ * (t : G)) = Subgroup.zpowers (x₀ * (t' : G)) :=
      congrArg Subtype.val htt'
    have h2 : x₀ * (t' : G) ∈ Subgroup.zpowers (x₀ * (t : G)) := by
      rw [h1]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
    have htR : (t : G) ∈ fc.invImageF model := hTle t.2
    have hcomm : Commute x₀ (t : G) := hab _ hx₀R _ htR
    have hpow : (x₀ * (t : G)) ^ k = x₀ ^ k * (t : G) ^ k := hcomm.mul_zpow k
    rw [hpow] at hk
    -- `x₀^{k−1} = t'·(t^k)⁻¹ ∈ P ⊓ T = ⊥`.
    have hsep : x₀ ^ (k - 1) = (t' : G) * ((t : G) ^ k)⁻¹ := by
      have h4 : x₀ ^ (k - 1) = x₀⁻¹ * x₀ ^ k := by
        rw [← zpow_neg_one, ← zpow_add]
        congr 1
        ring
      have h5 : x₀ ^ k = x₀ * (t' : G) * ((t : G) ^ k)⁻¹ := by
        rw [← hk]
        group
      rw [h4, h5]
      group
    have hmemP : x₀ ^ (k - 1) ∈ fc.P := Subgroup.zpow_mem _ hx₀ _
    have hmemT : x₀ ^ (k - 1) ∈ fc.sInvertedT model := by
      rw [hsep]
      exact (fc.sInvertedT model).mul_mem t'.2
        ((fc.sInvertedT model).inv_mem (Subgroup.zpow_mem _ t.2 _))
    have hone : x₀ ^ (k - 1) = 1 := by
      have h4 : x₀ ^ (k - 1) ∈ fc.sInvertedT model ⊓ fc.P := ⟨hmemT, hmemP⟩
      rwa [hTinf, Subgroup.mem_bot] at h4
    have hdvd : (fc.p : ℤ) ∣ (k - 1) := by
      rw [← hordx₀]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hone
    obtain ⟨j, hj⟩ := hdvd
    -- `t' = t^k = t·(t^p)^j = t`.
    have htp : (t : G) ^ (fc.p : ℤ) = 1 := by
      rw [zpow_natCast]
      exact fc.pow_p_eq_one_of_mem_invImageF model ind hB2 hm htR
    have ht' : (t' : G) = (t : G) := by
      have h5 : (t' : G) = x₀ ^ (k - 1) * ((t : G) ^ k) := by
        rw [hsep]
        group
      rw [hone, one_mul] at h5
      have h6 : k = 1 + fc.p * j := by omega
      rw [h5, h6, zpow_add, zpow_one, zpow_mul, htp, one_zpow, mul_one]
    exact Subtype.ext ht'.symm
  have hfsurj : Function.Surjective f := by
    rintro ⟨P₁, hP₁R, hP₁c, hP₁T⟩
    obtain ⟨t, htT, -, heq⟩ :=
      fc.exists_mem_sInvertedT_zpowers_eq_of_prime_order model ind hB2 hm
        hx₀ hx₀1 hP₁R hP₁c hP₁T
    exact ⟨⟨t, htT⟩, Subtype.ext heq.symm⟩
  have hbij : Function.Bijective f := ⟨hfinj, hfsurj⟩
  calc Set.ncard A = Nat.card ↥A := (Nat.card_coe_set_eq A).symm
    _ = Nat.card ↥(fc.sInvertedT model) :=
        (Nat.card_congr (Equiv.ofBijective f hbij)).symm
    _ = Nat.card F := fc.card_sInvertedT model ind hB2 hm
    _ = fc.p ^ m := hm

include model in
/-- **`[N_G(R) : N_G(P)] = p^m` in case (10.1)** (step (12), p. 112): the `N_G(R)`-orbit
of `P` is squeezed between the free `C_Q(P)`-suborbit through any `P₁ ≠ P`
(`1 + (p^m − 1)` members) and the parameter count `|𝒜| = p^m`; orbit–stabilizer
identifies the orbit size with the index of `N_G(P)`. -/
theorem index_normalizer_P_subgroupOf_normalizer_invImageF
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m)
    (hGp : fc.p ^ (m + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) :
    ((Subgroup.normalizer (fc.P : Set G)).subgroupOf
      (Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))).index
      = fc.p ^ m := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Finite F := Nat.finite_of_card_ne_zero
    (by rw [hm]; exact (Nat.pow_pos fc.p_prime.pos).ne')
  set NR : Subgroup G :=
    Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) with hNRdef
  have hlt := fc.normalizer_P_lt_normalizer_invImageF model ind hm hGp hSigma
  have hle : Subgroup.normalizer (fc.P : Set G) ≤ NR := hlt.le
  letI act : MulAction ↥NR (Subgroup G) :=
    MulAction.compHom _ ((MulAut.conj : G →* MulAut G).comp NR.subtype)
  -- stabilizer of `P` = `N_G(P)`.
  have hstab : MulAction.stabilizer ↥NR fc.P
      = (Subgroup.normalizer (fc.P : Set G)).subgroupOf NR := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change (MulAut.conj (n : G) • fc.P = fc.P) ↔ _
    exact conj_smul_eq_iff_mem_normalizer
  -- orbit–stabilizer.
  have horb : Nat.card (MulAction.orbit ↥NR fc.P)
      = ((Subgroup.normalizer (fc.P : Set G)).subgroupOf NR).index := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥NR fc.P), hstab,
      Subgroup.index]
  -- a nonidentity generator of `P` (for the `𝒜`-count).
  obtain ⟨x₀, hx₀P, hx₀1⟩ : ∃ x₀ ∈ fc.P, x₀ ≠ (1 : G) := by
    by_contra hall
    push Not at hall
    have h1 : fc.P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact hall x hx
    have h2 := fc.card_P
    rw [h1, Subgroup.card_bot] at h2
    exact fc.p_prime.one_lt.ne h2
  -- upper bound: the orbit sits inside `𝒜`.
  have hsub : MulAction.orbit ↥NR fc.P ⊆ {P₁ : Subgroup G |
      P₁ ≤ fc.invImageF model ∧ Nat.card ↥P₁ = fc.p ∧
        ¬ P₁ ≤ fc.sInvertedT model} := by
    rintro Q ⟨n, rfl⟩
    change MulAut.conj (n : G) • fc.P ≤ fc.invImageF model ∧ _ ∧ _
    have hcard : Nat.card ↥(MulAut.conj (n : G) • fc.P) = fc.p := by
      rw [← fc.card_P]
      exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj (n : G)) fc.P).toEquiv).symm
    refine ⟨?_, hcard, ?_⟩
    · intro x hx
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      have h2 : ((MulAut.conj (n : G))⁻¹ • x : G) = (n : G)⁻¹ * x * (n : G) := by
        have h3 : ((MulAut.conj (n : G))⁻¹ • x : G) = (MulAut.conj (n : G))⁻¹ x := rfl
        rw [h3, ← map_inv, MulAut.conj_apply]
        group
      rw [h2] at hx
      have h4 : (n : G)⁻¹ * x * (n : G) ∈ fc.invImageF model :=
        fc.P_le_invImageF model hx
      have h5 := (Subgroup.mem_set_normalizer_iff.mp n.2 ((n : G)⁻¹ * x * (n : G))).mp h4
      have h6 : (n : G) * ((n : G)⁻¹ * x * (n : G)) * (n : G)⁻¹ = x := by group
      rwa [h6] at h5
    · intro hleT
      have hbot := fc.conj_P_inf_sInvertedT_eq_bot model ind hB2 hm (n : G)
      have h1 : MulAut.conj (n : G) • fc.P
          = (MulAut.conj (n : G) • fc.P) ⊓ fc.sInvertedT model :=
        (inf_of_le_left hleT).symm
      rw [h1, hbot, Subgroup.card_bot] at hcard
      exact fc.p_prime.one_lt.ne hcard
  have hub : Nat.card (MulAction.orbit ↥NR fc.P) ≤ fc.p ^ m := by
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [fc.ncard_prime_order_not_le_sInvertedT model ind hB2 hm hx₀P hx₀1] at h1
    rwa [Nat.card_coe_set_eq]
  -- lower bound: `P` plus a free `C_Q(P)`-suborbit.
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ↥NR, (n₀ : G) ∉ Subgroup.normalizer (fc.P : Set G) := by
    by_contra hall
    push Not at hall
    refine hlt.ne (le_antisymm hle fun g hg => ?_)
    exact hall ⟨g, hg⟩
  set P₁ : Subgroup G := MulAut.conj ((n₀ : ↥NR) : G) • fc.P with hP₁def
  have hP₁orb : P₁ ∈ MulAction.orbit ↥NR fc.P := ⟨n₀, rfl⟩
  have hP₁ne : P₁ ≠ fc.P := fun h => hn₀ (conj_smul_eq_iff_mem_normalizer.mp h)
  have hP₁A := hsub hP₁orb
  -- centralizer of `P` normalizes `P` (pointwise).
  have hCle : Subgroup.centralizer (fc.P : Set G)
      ≤ Subgroup.normalizer (fc.P : Set G) := by
    intro c hc
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := Subgroup.mem_centralizer_iff.mp hc x hx
      have h2 : c * x * c⁻¹ = x := by rw [← h1]; group
      rwa [h2]
    · intro hx
      have h1 := Subgroup.mem_centralizer_iff.mp hc _ hx
      have h2 : x = c⁻¹ * (c * x * c⁻¹) * c := by group
      have h3 : c⁻¹ * (c * x * c⁻¹) * c = c * x * c⁻¹ := by
        have h4 := congrArg (fun z => c⁻¹ * z) h1
        simpa [mul_assoc] using h4
      rw [h2, h3]
      exact hx
  set CQP : Subgroup G :=
    fc.toHypothesis.Q ⊓ Subgroup.centralizer (fc.P : Set G) with hCQPdef
  obtain ⟨eu⟩ := fc.centralizer_inf_mulEquiv_units model
  have hCQPcard : Nat.card ↥CQP = fc.p ^ m - 1 := by
    haveI := Fintype.ofFinite F
    haveI := Classical.decEq F
    rw [Nat.card_congr eu.toEquiv, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, hm]
  have hmemNR : ∀ a : ↥CQP, (a : G) ∈ NR := fun a => hle (hCle a.2.2)
  set ι : ↥CQP → Subgroup G := fun a => MulAut.conj ((a : G)) • P₁ with hιdef
  have hιorb : ∀ a, ι a ∈ MulAction.orbit ↥NR fc.P := by
    intro a
    refine ⟨(⟨(a : G), hmemNR a⟩ : ↥NR) * n₀, ?_⟩
    change MulAut.conj (((⟨(a : G), hmemNR a⟩ : ↥NR) * n₀ : ↥NR) : G) • fc.P = ι a
    rw [show (((⟨(a : G), hmemNR a⟩ : ↥NR) * n₀ : ↥NR) : G)
      = (a : G) * ((n₀ : ↥NR) : G) from rfl, map_mul, mul_smul]
  have hιne : ∀ a, ι a ≠ fc.P := by
    intro a h
    have h1 : P₁ = (MulAut.conj ((a : G)))⁻¹ • fc.P := by
      rw [← h, show ι a = MulAut.conj ((a : G)) • P₁ from rfl, inv_smul_smul]
    have h2 : (MulAut.conj ((a : G)))⁻¹ • fc.P = fc.P := by
      rw [← map_inv]
      exact conj_smul_eq_iff_mem_normalizer.mpr
        ((Subgroup.normalizer (fc.P : Set G)).inv_mem (hCle a.2.2))
    exact hP₁ne (h1.trans h2)
  have hιinj : Function.Injective ι := by
    intro a a' haa'
    have h2 : (MulAut.conj ((a' : G)))⁻¹ • (MulAut.conj ((a : G)) • P₁) = P₁ := by
      have h3 : ι a = ι a' := haa'
      change (MulAut.conj ((a' : G)))⁻¹ • (ι a) = P₁
      rw [h3]
      change (MulAut.conj ((a' : G)))⁻¹ • (MulAut.conj ((a' : G)) • P₁) = P₁
      rw [inv_smul_smul]
    rw [← mul_smul, ← map_inv, ← map_mul] at h2
    by_contra hne
    have hna : ((a' : G))⁻¹ * (a : G) ≠ 1 := by
      intro h
      apply hne
      apply Subtype.ext
      have h4 := congrArg (fun z => (a' : G) * z) h
      simpa [mul_assoc] using h4
    have hmemQ : ((a' : G))⁻¹ * (a : G) ∈ fc.toHypothesis.Q :=
      fc.toHypothesis.Q.mul_mem (fc.toHypothesis.Q.inv_mem a'.2.1) a.2.1
    have hmemC : ((a' : G))⁻¹ * (a : G) ∈ Subgroup.centralizer (fc.P : Set G) :=
      (Subgroup.centralizer (fc.P : Set G)).mul_mem
        ((Subgroup.centralizer (fc.P : Set G)).inv_mem a'.2.2) a.2.2
    have hnormz := conj_smul_eq_iff_mem_normalizer.mp h2
    have hnorm' : ∀ x ∈ P₁, (((a' : G))⁻¹ * (a : G)) * x * (((a' : G))⁻¹ * (a : G))⁻¹ ∈ P₁ :=
      fun x hx => (Subgroup.mem_set_normalizer_iff.mp hnormz x).mp hx
    exact hP₁ne (fc.eq_P_of_prime_order_conj_invariant model ind hB2 hm
      hmemQ hmemC hna hP₁A.1 hP₁A.2.1 hP₁A.2.2 hnorm')
  have hlb : fc.p ^ m ≤ Nat.card (MulAction.orbit ↥NR fc.P) := by
    have hins : insert fc.P (Set.range ι) ⊆ MulAction.orbit ↥NR fc.P := by
      rintro Q hQ
      rcases Set.mem_insert_iff.mp hQ with rfl | ⟨a, rfl⟩
      · exact MulAction.mem_orbit_self _
      · exact hιorb a
    have hPnotin : fc.P ∉ Set.range ι := by
      rintro ⟨a, ha⟩
      exact hιne a ha
    have h1 : (insert fc.P (Set.range ι)).ncard ≤ (MulAction.orbit ↥NR fc.P).ncard :=
      Set.ncard_le_ncard hins (Set.toFinite _)
    have h2 : (Set.range ι).ncard = fc.p ^ m - 1 := by
      rw [← hCQPcard, ← Nat.card_coe_set_eq]
      exact (Nat.card_congr (Equiv.ofInjective ι hιinj)).symm
    have h3 : (insert fc.P (Set.range ι)).ncard = fc.p ^ m - 1 + 1 := by
      rw [Set.ncard_insert_of_notMem hPnotin (Set.toFinite _), h2]
    have hp1 : 1 ≤ fc.p ^ m := Nat.one_le_pow _ _ fc.p_prime.pos
    rw [Nat.card_coe_set_eq]
    omega
  rw [← horb]
  omega

include model in
/-- **`st ∈ T`** (Part II, Ch. II (14), "note that `Z₁ ⊂ T`"): `st` lies in `R`
(`distinguishedInvolution_mul_t_mem_invImageF`) and `s` inverts it
(`s·(st)·s⁻¹ = ts = (st)⁻¹`, both being involutions). -/
theorem distinguishedInvolution_mul_t_mem_sInvertedT
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t
      ∈ fc.sInvertedT model := by
  rw [fc.mem_sInvertedT_iff model ind hB2 hm]
  refine ⟨fc.distinguishedInvolution_mul_t_mem_invImageF model, ?_⟩
  set s := fc.toHypothesis.distinguishedInvolution with hs_def
  have hs2 : s * s = 1 := by
    rw [← sq]; exact fc.toHypothesis.distinguishedInvolution_sq
  have ht2 : fc.toHypothesis.t * fc.toHypothesis.t = 1 := by
    rw [← sq]; exact fc.toHypothesis.t_sq
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  calc s * (s * fc.toHypothesis.t) * s⁻¹
      = (s * s) * fc.toHypothesis.t * s := by rw [hsinv]; group
    _ = fc.toHypothesis.t * s := by rw [hs2, one_mul]
    _ = (s * fc.toHypothesis.t)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, hsinv]

include model in
/-- **`Z₁ ≤ T`** (Part II, Ch. II (14)): the cyclic group `Z₁ = ⟨st⟩` lies in the
`s`-inverted part `T` of `R`. -/
theorem zpowers_distinguishedInvolution_mul_t_le_sInvertedT
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ≤ fc.sInvertedT model :=
  Subgroup.zpowers_le.mpr
    (fc.distinguishedInvolution_mul_t_mem_sInvertedT model ind hB2 hm)

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
