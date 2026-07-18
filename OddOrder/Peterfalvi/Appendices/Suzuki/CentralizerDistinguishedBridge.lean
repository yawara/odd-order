/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerInductionBridge

/-!
# Peterfalvi Part II, Ch. I §3: distinguished elements in the centralizer quotient

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, pp. 105--106.

This file proves the distinguished-element transport used in Proposition 1(c).
The subgroup `V` centralizes not only the distinguished involution `s`, but
also its structure conjugator `r`.  Thus for `X ≤ V`, both elements belong
to `L = C_G(X)`, and their images in `L/𝒩(L)` are exactly the distinguished
pair of the quotient hypothesis.

The final generic lemma records the source's order-lifting argument.  If a
product `g = st` of involutions has prime order after quotienting by an
odd-order kernel centralized by `s`, then `g` already has that prime order:
`s` both inverts and centralizes `g^p`, forcing `g^p = 1`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open scoped Pointwise

/-! ## A generic prime-order lift across an odd kernel -/

/-- Let `s` and `t` be involutions and put `g = st`.  Suppose an odd-order
normal subgroup `N` contains `g^p`, and `s` centralizes `N`.  If `p` is
prime and `g ≠ 1`, then `g` has order `p`.

This is the order-lifting argument used in Peterfalvi Part II, Ch. I §3
Proposition 1(c), after the quotient model gives `(gN)^p = 1`. -/
theorem orderOf_mul_eq_prime_of_pow_mem_odd_kernel
    {A : Type*} [Group A] [Finite A] {N : Subgroup A}
    {s t : A} {p : ℕ} (hp : p.Prime)
    (hNodd : Odd (Nat.card N))
    (hs2 : s ^ 2 = 1) (ht2 : t ^ 2 = 1)
    (hsN : ∀ n ∈ N, Commute s n)
    (hpowN : (s * t) ^ p ∈ N) (hne : s * t ≠ 1) :
    orderOf (s * t) = p := by
  let g : A := s * t
  have hs_inv : s⁻¹ = s := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [sq] using hs2
  have ht_inv : t⁻¹ = t := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [sq] using ht2
  have hsgs : s * g * s⁻¹ = g⁻¹ := by
    dsimp only [g]
    calc
      s * (s * t) * s⁻¹ = (s * s) * t * s := by rw [hs_inv]; group
      _ = t * s := by rw [← sq, hs2, one_mul]
      _ = (s * t)⁻¹ := by rw [mul_inv_rev, hs_inv, ht_inv]
  have hconj_pow : s * g ^ p * s⁻¹ = (g ^ p)⁻¹ := by
    calc
      s * g ^ p * s⁻¹ = (s * g * s⁻¹) ^ p := conj_pow.symm
      _ = (g⁻¹) ^ p := by rw [hsgs]
      _ = (g ^ p)⁻¹ := inv_pow g p
  have hcomm : Commute s (g ^ p) := hsN _ hpowN
  have hfix : s * g ^ p * s⁻¹ = g ^ p := by
    rw [hcomm.eq, mul_inv_cancel_right]
  have hinv : g ^ p = (g ^ p)⁻¹ := hfix.symm.trans hconj_pow
  have hsq : (g ^ p) ^ 2 = 1 := by
    calc
      (g ^ p) ^ 2 = g ^ p * g ^ p := by rw [sq]
      _ = (g ^ p)⁻¹ * g ^ p := congrArg (· * g ^ p) hinv
      _ = 1 := inv_mul_cancel _
  have hpow : g ^ p = 1 :=
    eq_one_of_sq_eq_one_of_odd_card hNodd hpowN hsq
  letI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime hpow hne

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## The structure conjugator is centralized by `V` -/

/-- **Peterfalvi Part II, Ch. I §1 Proposition 5**, the structure-conjugator
companion to `V ≤ C_D(s)`: every element of `V` centralizes the unique
`r ∈ Q` in the structure equation `tst = r⁻¹tr`.

Conjugating the structure equation by `v ∈ V` leaves `t` and `s` fixed,
so `(s, rᵛ)` is another valid distinguished pair.  Uniqueness gives
`rᵛ = r`. -/
theorem V_le_centralizer_structureConjugator :
    hyp.V ≤ hyp.D ⊓ Subgroup.centralizer {hyp.structureConjugator} := by
  intro v hv
  have hvD : v ∈ hyp.D := hyp.V_le_D hv
  have hvH : v ∈ hyp.H := hyp.D_le_H hvD
  have hvt : Commute v hyp.t := hyp.commute_t_of_mem_V hv
  have hvs : Commute v hyp.distinguishedInvolution :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (hyp.V_le_centralizer_distinguishedInvolution hv).2
  have hrvQ : v⁻¹ * hyp.structureConjugator * v ∈ hyp.Q := by
    have h := hyp.Q_normal_in_H v⁻¹ (inv_mem hvH)
      hyp.structureConjugator hyp.structureConjugator_mem_Q
    rwa [inv_inv] at h
  have hfix_t : v⁻¹ * hyp.t * v = hyp.t := by
    calc
      v⁻¹ * hyp.t * v = v⁻¹ * (hyp.t * v) := by rw [mul_assoc]
      _ = v⁻¹ * (v * hyp.t) := by rw [← hvt.eq]
      _ = hyp.t := by group
  have hfix_s : v⁻¹ * hyp.distinguishedInvolution * v =
      hyp.distinguishedInvolution := by
    calc
      v⁻¹ * hyp.distinguishedInvolution * v =
          v⁻¹ * (hyp.distinguishedInvolution * v) := by rw [mul_assoc]
      _ = v⁻¹ * (v * hyp.distinguishedInvolution) := by rw [← hvs.eq]
      _ = hyp.distinguishedInvolution := by group
  have hfix_structure :
      v⁻¹ * (hyp.t * hyp.distinguishedInvolution * hyp.t) * v =
        hyp.t * hyp.distinguishedInvolution * hyp.t := by
    calc
      v⁻¹ * (hyp.t * hyp.distinguishedInvolution * hyp.t) * v =
          (v⁻¹ * hyp.t * v) *
            (v⁻¹ * hyp.distinguishedInvolution * v) *
              (v⁻¹ * hyp.t * v) := by group
      _ = hyp.t * hyp.distinguishedInvolution * hyp.t := by
        rw [hfix_t, hfix_s]
  have hconj :
      hyp.t * hyp.distinguishedInvolution * hyp.t =
        (v⁻¹ * hyp.structureConjugator * v)⁻¹ * hyp.t *
          (v⁻¹ * hyp.structureConjugator * v) := by
    calc
      hyp.t * hyp.distinguishedInvolution * hyp.t =
          v⁻¹ * (hyp.t * hyp.distinguishedInvolution * hyp.t) * v := by
            exact hfix_structure.symm
      _ = v⁻¹ *
          (hyp.structureConjugator⁻¹ * hyp.t * hyp.structureConjugator) * v := by
            rw [hyp.structure_equation]
      _ = (v⁻¹ * hyp.structureConjugator * v)⁻¹ * hyp.t *
          (v⁻¹ * hyp.structureConjugator * v) := by
            calc
              v⁻¹ *
                    (hyp.structureConjugator⁻¹ * hyp.t *
                      hyp.structureConjugator) * v =
                  (v⁻¹ * hyp.structureConjugator * v)⁻¹ *
                    (v⁻¹ * hyp.t * v) *
                      (v⁻¹ * hyp.structureConjugator * v) := by group
              _ = (v⁻¹ * hyp.structureConjugator * v)⁻¹ * hyp.t *
                  (v⁻¹ * hyp.structureConjugator * v) := by rw [hfix_t]
  have hr := (hyp.eq_distinguishedPair_of_structure
    hyp.distinguishedInvolution_mem_H hyp.distinguishedInvolution_sq
    hyp.distinguishedInvolution_ne_one hrvQ hconj).2
  refine Subgroup.mem_inf.mpr ⟨hvD, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmul : v * (v⁻¹ * hyp.structureConjugator * v) =
      v * hyp.structureConjugator := by rw [hr]
  rw [show v * (v⁻¹ * hyp.structureConjugator * v) =
      hyp.structureConjugator * v by group] at hmul
  exact hmul.symm

/-! ## Distinguished pair in the centralizer quotient -/

/-- If `X ≤ V`, the distinguished involution `s` belongs to
`L = C_G(X)`. -/
lemma distinguishedInvolution_mem_centralizer_of_le_V
    {X : Subgroup G} (hXV : X ≤ hyp.V) :
    hyp.distinguishedInvolution ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hcomm : Commute x hyp.distinguishedInvolution :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (hyp.V_le_centralizer_distinguishedInvolution (hXV hx)).2
  exact hcomm.eq

/-- If `X ≤ V`, the structure conjugator `r` belongs to
`L = C_G(X)`. -/
lemma structureConjugator_mem_centralizer_of_le_V
    {X : Subgroup G} (hXV : X ≤ hyp.V) :
    hyp.structureConjugator ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hcomm : Commute x hyp.structureConjugator :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (hyp.V_le_centralizer_structureConjugator (hXV hx)).2
  exact hcomm.eq

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c).**  The images of the
original distinguished involution `s` and structure conjugator `r` are
exactly the distinguished pair of the faithful quotient hypothesis on
`C_G(X)/𝒩(C_G(X))`. -/
theorem centralizerQuotient_distinguishedPair_eq_images
    {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    letI := hyp.centralizerQuotientMulAction hXV
    let L : Subgroup G := Subgroup.centralizer (X : Set G)
    let N : Subgroup L := (hyp.H.subgroupOf L).normalCore
    let pi : L →* (L ⧸ N) := QuotientGroup.mk' N
    let sL : L := ⟨hyp.distinguishedInvolution,
      hyp.distinguishedInvolution_mem_centralizer_of_le_V hXV⟩
    let rL : L := ⟨hyp.structureConjugator,
      hyp.structureConjugator_mem_centralizer_of_le_V hXV⟩
    let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
    pi sL = qhyp.distinguishedInvolution ∧
      pi rL = qhyp.structureConjugator := by
  letI := hyp.centralizerQuotientMulAction hXV
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup L := (hyp.H.subgroupOf L).normalCore
  let pi : L →* (L ⧸ N) := QuotientGroup.mk' N
  let sL : L := ⟨hyp.distinguishedInvolution,
    hyp.distinguishedInvolution_mem_centralizer_of_le_V hXV⟩
  let rL : L := ⟨hyp.structureConjugator,
    hyp.structureConjugator_mem_centralizer_of_le_V hXV⟩
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  let sQ : hyp.Q.subgroupOf L := ⟨sL,
    hyp.mem_Q_of_sq_eq_one_of_mem_H hyp.distinguishedInvolution_mem_H
      hyp.distinguishedInvolution_sq⟩
  let rQ : hyp.Q.subgroupOf L := ⟨rL, hyp.structureConjugator_mem_Q⟩
  have hsbarQ : pi sL ∈ qhyp.Q := by
    change pi sL ∈ (hyp.centralizerQuotientHypothesisA1 hXV).Q
    exact (hyp.centralizerQQuotientEquiv hXV sQ).2
  have hrbarQ : pi rL ∈ qhyp.Q := by
    change pi rL ∈ (hyp.centralizerQuotientHypothesisA1 hXV).Q
    exact (hyp.centralizerQQuotientEquiv hXV rQ).2
  have hsbarH : pi sL ∈ qhyp.H := qhyp.Q_le_H hsbarQ
  have hsbar2 : (pi sL) ^ 2 = 1 := by
    rw [← map_pow, show sL ^ 2 = 1 from Subtype.ext hyp.distinguishedInvolution_sq,
      map_one]
  have hsQ_ne : sQ ≠ 1 := by
    intro h
    apply hyp.distinguishedInvolution_ne_one
    exact congrArg (fun z : hyp.Q.subgroupOf L => ((z : L) : G)) h
  have hsbar1 : pi sL ≠ 1 := by
    intro h
    have heq : hyp.centralizerQQuotientEquiv hXV sQ = 1 := by
      apply Subtype.ext
      exact h
    exact hsQ_ne ((hyp.centralizerQQuotientEquiv hXV).injective
      (heq.trans (map_one (hyp.centralizerQQuotientEquiv hXV)).symm))
  have hstr : qhyp.t * pi sL * qhyp.t =
      (pi rL)⁻¹ * qhyp.t * pi rL := by
    change pi (⟨hyp.t, _⟩ : L) * pi sL * pi (⟨hyp.t, _⟩ : L) =
      (pi rL)⁻¹ * pi (⟨hyp.t, _⟩ : L) * pi rL
    rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    apply congrArg pi
    apply Subtype.ext
    exact hyp.structure_equation
  exact qhyp.eq_distinguishedPair_of_structure hsbarH hsbar2 hsbar1 hrbarQ hstr

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c), order transport.**
Let `g = st`, where `s` is the original distinguished involution.  If the
corresponding distinguished product in the faithful centralizer quotient
has `p`-th power one, then `g` itself has order `p`, for every prime `p`.
In the three source alternatives this is used with `p = 3` or `p = 5`.

The quotient relation puts `g^p` in `𝒩(L)`.  This kernel lies in the
odd-order subgroup `C_D(X)` and centralizes `C_Q(X)`, hence is centralized
by `s`.  On the other hand `s` conjugates `g = st` to `g⁻¹`.  Thus `g^p`
is both fixed and inverted by `s`, so it is the identity. -/
theorem orderOf_distinguishedInvolution_mul_t_of_quotient_pow
    {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    {p : ℕ} (hp : p.Prime)
    (hquotPow :
      letI := hyp.centralizerQuotientMulAction hXV
      let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
      (qhyp.distinguishedInvolution * qhyp.t) ^ p = 1) :
    orderOf (hyp.distinguishedInvolution * hyp.t) = p := by
  letI := hyp.centralizerQuotientMulAction hXV
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup L := (hyp.H.subgroupOf L).normalCore
  let D_L : Subgroup L := hyp.D.subgroupOf L
  let Q_L : Subgroup L := hyp.Q.subgroupOf L
  let pi : L →* (L ⧸ N) := QuotientGroup.mk' N
  let sL : L := ⟨hyp.distinguishedInvolution,
    hyp.distinguishedInvolution_mem_centralizer_of_le_V hXV⟩
  have htL : hyp.t ∈ L := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hyp.commute_t_of_mem_V (hXV hx)).eq
  let tL : L := ⟨hyp.t, htL⟩
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  have hpair := hyp.centralizerQuotient_distinguishedPair_eq_images hXV hA3
  have htbar : qhyp.t = pi tL := rfl
  have hquot : (pi (sL * tL)) ^ p = 1 := by
    rw [map_mul, hpair.1, ← htbar]
    exact hquotPow
  have hpowN : (sL * tL) ^ p ∈ N := by
    apply (QuotientGroup.eq_one_iff ((sL * tL) ^ p)).mp
    change pi ((sL * tL) ^ p) = 1
    rw [map_pow]
    exact hquot
  have hNleD : N ≤ D_L := by
    dsimp only [N, D_L, L]
    rw [hyp.normalCore_cH_eq_centralizer_cQ hXV]
    exact inf_le_left
  have hNodd : Odd (Nat.card N) :=
    (hyp.centralizerHypothesisA1 hXV).D_odd.of_dvd_nat
      (Subgroup.card_dvd_of_le hNleD)
  have hsQ : sL ∈ Q_L :=
    hyp.mem_Q_of_sq_eq_one_of_mem_H hyp.distinguishedInvolution_mem_H
      hyp.distinguishedInvolution_sq
  have hcore : N = D_L ⊓ Subgroup.centralizer (Q_L : Set L) := by
    dsimp only [N, D_L, Q_L, L]
    exact hyp.normalCore_cH_eq_centralizer_cQ hXV
  have hsN : ∀ n ∈ N, Commute sL n := by
    intro n hn
    have hnC : n ∈ Subgroup.centralizer (Q_L : Set L) := by
      rw [hcore] at hn
      exact hn.2
    change sL * n = n * sL
    exact Subgroup.mem_centralizer_iff.mp hnC sL hsQ
  have hs2 : sL ^ 2 = 1 := Subtype.ext hyp.distinguishedInvolution_sq
  have ht2 : tL ^ 2 = 1 := Subtype.ext hyp.t_sq
  have hne : sL * tL ≠ 1 := by
    intro h
    have hst : hyp.distinguishedInvolution * hyp.t = 1 :=
      congrArg (fun z : L => (z : G)) h
    have hst' : hyp.distinguishedInvolution = hyp.t⁻¹ :=
      mul_eq_one_iff_eq_inv.mp hst
    apply hyp.t_not_mem_H
    rw [hyp.t_inv_eq] at hst'
    exact hst' ▸ hyp.distinguishedInvolution_mem_H
  have hord : orderOf (sL * tL) = p :=
    orderOf_mul_eq_prime_of_pow_mem_odd_kernel hp hNodd hs2 ht2 hsN hpowN hne
  rw [← hord]
  exact orderOf_injective L.subtype L.subtype_injective (sL * tL)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
