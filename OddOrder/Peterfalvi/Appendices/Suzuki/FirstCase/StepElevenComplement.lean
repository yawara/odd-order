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

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
