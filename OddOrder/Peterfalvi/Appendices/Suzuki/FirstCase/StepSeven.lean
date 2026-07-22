/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepSix
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerTrichotomy

/-!
# Peterfalvi Part II, Ch. II, step (7): `N = P`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (7), p. 110.

`N` is the kernel of the action of `L = C_G(P)` on the fixed points `Ω_P`,
defined in step (2)(a).  Step (7) proves `N = P` (and `Σ ≅ C_W(P)`).

This leaf begins with the *decomposition* `N = (N ∩ W) × P`, phrased as
`N = (N ∩ W) ⊔ P`.  It is a clean consequence of step (1):

* `P ≤ N`: `P` fixes `Ω_P` pointwise, and `P` centralizes `C_Q(P) = Q_L`, so
  `P` lands in the kernel `N = C_{D_L}(Q_L)`
  (`normalCore_cH_eq_centralizer_cQ`);
* `N ≤ V`: `N ≤ C_D(P) = C_W(P) · P ≤ W · P = V` (step (1)); and
* every `n ∈ N ⊆ V` factors as `n = g·w` with `g ∈ P` and `w ∈ W`
  (`exists_decomp_of_mem_V`); since `g ∈ P ≤ N`, also `w = g⁻¹ n ∈ N`.

The reduction `N ∩ W = 1 ⟹ N = P` is then immediate.  The hard direction,
`N ∩ W = 1`, is the centralizer-trichotomy contradiction, handled separately.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- The kernel `N` of the action of `L = C_G(P)` on the fixed points `Ω_P`,
realized as a subgroup of `G` (the book's `N`, defined in step (2)(a)).  It is
`(H ∩ L).normalCore`, the kernel of `L → Sym(Ω_P)`, pushed forward along
`L ↪ G`. -/
noncomputable def kernelN : Subgroup G :=
  ((fc.toHypothesis.H.subgroupOf
      (Subgroup.centralizer (fc.P : Set G))).normalCore).map
    (Subgroup.centralizer (fc.P : Set G)).subtype

/-- `N ≤ C_G(P)`: the kernel consists of elements of `L = C_G(P)`. -/
theorem kernelN_le_centralizer :
    fc.kernelN ≤ Subgroup.centralizer (fc.P : Set G) := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- `N ≤ D`: the kernel lands in `D_L = C_D(P)`
(`normalCore_cH_eq_centralizer_cQ`). -/
theorem kernelN_le_D : fc.kernelN ≤ fc.toHypothesis.D := by
  rintro x ⟨y, hy, rfl⟩
  have hyD : y ∈ fc.toHypothesis.D.subgroupOf
      (Subgroup.centralizer (fc.P : Set G)) := by
    have hy' : y ∈ (fc.toHypothesis.D.subgroupOf
        (Subgroup.centralizer (fc.P : Set G))) ⊓
        Subgroup.centralizer
          ((fc.toHypothesis.Q.subgroupOf
            (Subgroup.centralizer (fc.P : Set G))) :
            Set ↥(Subgroup.centralizer (fc.P : Set G))) := by
      rw [← fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
      exact hy
    exact hy'.1
  exact Subgroup.mem_subgroupOf.mp hyD

/-- `N` centralizes `C_Q(P) = Q_L`: the kernel is `C_{D_L}(Q_L)`. -/
theorem kernelN_le_centralizer_cQ :
    fc.kernelN ≤ Subgroup.centralizer
      ((fc.toHypothesis.Q ⊓ Subgroup.centralizer (fc.P : Set G) : Subgroup G) :
        Set G) := by
  rintro x ⟨y, hy, rfl⟩
  have hyC : y ∈ Subgroup.centralizer
      ((fc.toHypothesis.Q.subgroupOf (Subgroup.centralizer (fc.P : Set G))) :
        Set ↥(Subgroup.centralizer (fc.P : Set G))) := by
    have hy' : y ∈ (fc.toHypothesis.D.subgroupOf
        (Subgroup.centralizer (fc.P : Set G))) ⊓
        Subgroup.centralizer
          ((fc.toHypothesis.Q.subgroupOf
            (Subgroup.centralizer (fc.P : Set G))) :
            Set ↥(Subgroup.centralizer (fc.P : Set G))) := by
      rw [← fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
      exact hy
    exact hy'.2
  rw [Subgroup.mem_centralizer_iff]
  rintro z ⟨hzQ, hzC⟩
  -- `z ∈ C_G(P)`, so `z ∈ L`, and `z ∈ Q`; apply `hyC` to `z` viewed in `L`
  have hzL : z ∈ Subgroup.centralizer (fc.P : Set G) := hzC
  have hzQL : (⟨z, hzL⟩ : ↥(Subgroup.centralizer (fc.P : Set G))) ∈
      fc.toHypothesis.Q.subgroupOf (Subgroup.centralizer (fc.P : Set G)) :=
    Subgroup.mem_subgroupOf.mpr hzQ
  have hcomm := Subgroup.mem_centralizer_iff.mp hyC _ hzQL
  exact congrArg Subtype.val hcomm

/-- **Step (7): `P ≤ N`** (p. 110).  `P` centralizes itself, so `P ≤ L`; and
in `L`, `P` lands in `C_{D_L}(Q_L) = N`: `P ≤ D`, and every element of
`Q_L = C_Q(P)` centralizes `P`. -/
theorem P_le_kernelN : fc.P ≤ fc.kernelN := by
  have hPL : fc.P ≤ Subgroup.centralizer (fc.P : Set G) := fc.P_le_centralizer
  have hstep : fc.P.subgroupOf (Subgroup.centralizer (fc.P : Set G)) ≤
      (fc.toHypothesis.H.subgroupOf
        (Subgroup.centralizer (fc.P : Set G))).normalCore := by
    rw [fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
    apply le_inf
    · exact Subgroup.comap_mono (fc.P_le_V.trans fc.toHypothesis.V_le_D)
    · intro p hp
      have hpP : (p : G) ∈ fc.P := Subgroup.mem_subgroupOf.mp hp
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      apply Subtype.ext
      have hqL : (q : G) ∈ Subgroup.centralizer (fc.P : Set G) := q.2
      have hcomm := Subgroup.mem_centralizer_iff.mp hqL (p : G) hpP
      exact hcomm.symm
  calc fc.P = (fc.P.subgroupOf (Subgroup.centralizer (fc.P : Set G))).map
        (Subgroup.centralizer (fc.P : Set G)).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hPL).symm
    _ ≤ fc.kernelN := Subgroup.map_mono hstep

/-- **Step (7): `N ≤ V`** (p. 110).  `N ≤ C_D(P) = C_W(P) · P ≤ W · P = V`. -/
theorem kernelN_le_V : fc.kernelN ≤ fc.toHypothesis.V := by
  have h1 : fc.kernelN ≤
      fc.toHypothesis.D ⊓ Subgroup.centralizer (fc.P : Set G) :=
    le_inf fc.kernelN_le_D fc.kernelN_le_centralizer
  calc fc.kernelN
      ≤ fc.toHypothesis.D ⊓ Subgroup.centralizer (fc.P : Set G) := h1
    _ = (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) ⊔ fc.P :=
        fc.D_inf_centralizer_eq_W_inf_centralizer_join_P
    _ ≤ fc.toHypothesis.V :=
        sup_le (le_trans inf_le_left fc.toHypothesis.W_le_V) fc.P_le_V

/-- **Peterfalvi Part II, Ch. II, step (7), the decomposition** (p. 110):
`N = (N ∩ W) × P`, stated as `N = (N ∩ W) ⊔ P`.

`N ≤ V` splits every `n ∈ N` as `n = g·w` with `g ∈ P` and `w ∈ W`; since
`g ∈ P ≤ N`, the factor `w = g⁻¹ n ∈ N ∩ W`. -/
theorem kernelN_eq_kernelInf_W_join_P :
    fc.kernelN = (fc.kernelN ⊓ fc.toHypothesis.W) ⊔ fc.P := by
  apply le_antisymm
  · intro n hn
    obtain ⟨g, hgP, hgw⟩ := fc.exists_decomp_of_mem_V (fc.kernelN_le_V hn)
    have hgN : g ∈ fc.kernelN := fc.P_le_kernelN hgP
    have hmem : g⁻¹ * n ∈ fc.kernelN ⊓ fc.toHypothesis.W :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hgN) hn, hgw⟩
    have hdecomp : n = g * (g⁻¹ * n) := by group
    rw [hdecomp]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hgP)
      (Subgroup.mem_sup_left hmem)
  · exact sup_le inf_le_left fc.P_le_kernelN

/-- **Step (7), the reduction** (p. 110): `N ∩ W = 1 ⟹ N = P`.  Immediate from
the decomposition `N = (N ∩ W) × P`. -/
theorem kernelN_eq_P_of_kernelInf_W_eq_bot
    (h : fc.kernelN ⊓ fc.toHypothesis.W = ⊥) : fc.kernelN = fc.P := by
  have hd := fc.kernelN_eq_kernelInf_W_join_P
  rw [h, bot_sup_eq] at hd
  exact hd

/-- **Peterfalvi Part II, Ch. II, `f = char F`** (p. 110): "Let `f` be the order
of `st`.  Thus `f` is the characteristic of `F` by (2), Chapter I §1
Proposition 4(c) and Appendix II, Proposition 1."  For any near-field model of
the `P`-centralizer quotient, the order of the global product
`s·t = distinguishedInvolution · t` equals the characteristic of `F`.

The images `s̄ = π(s)`, `t̄ = π(t)` in `L/N = C_G(P)/N` are distinct involutions
(`s ∈ Q ∖ D`, `t ∉ H ⊇ D`, `s·t⁻¹ ∉ H`), so `char = |s̄ · t̄|` by
`model.orderOf_mul_of_involutions`.  Hence `(s·t)^char ∈ N`, and the odd-kernel
bridge (`orderOf_mul_eq_prime_of_pow_mem_odd_kernel`, `s` inverts `st` and
centralizes the odd `N`) gives `|s·t| = char`.

Inherits the step (2)(b) `sorry` (issue 9318) only through a caller who supplies
the model via `exists_affineNearFieldModel`. -/
theorem orderOf_st_eq_char :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    ∀ {F : Type uG} [NearFields.NearField F]
      (model : NearFields.AffineNearFieldModel fc.rankOneQuotient F),
      orderOf (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) =
        model.char := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  intro F instF model
  classical
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hNdef
  have hsL : fc.toHypothesis.distinguishedInvolution ∈ L :=
    fc.toHypothesis.distinguishedInvolution_mem_centralizer_of_le_V fc.P_le_V
  have htL : fc.toHypothesis.t ∈ L := by
    rw [hLdef, Subgroup.mem_centralizer_iff]
    intro x hx
    exact (fc.toHypothesis.commute_t_of_mem_V (fc.P_le_V hx)).eq
  set sL : ↥L := ⟨fc.toHypothesis.distinguishedInvolution, hsL⟩ with hsLdef
  set tL : ↥L := ⟨fc.toHypothesis.t, htL⟩ with htLdef
  set pi : ↥L →* (↥L ⧸ N) := QuotientGroup.mk' N with hpidef
  have hs2 : sL ^ 2 = 1 :=
    Subtype.ext fc.toHypothesis.distinguishedInvolution_sq
  have ht2 : tL ^ 2 = 1 := Subtype.ext fc.toHypothesis.t_sq
  have hsQ : (sL : G) ∈ fc.toHypothesis.Q :=
    fc.toHypothesis.mem_Q_of_sq_eq_one_of_mem_H
      fc.toHypothesis.distinguishedInvolution_mem_H
      fc.toHypothesis.distinguishedInvolution_sq
  have hcore : N = (fc.toHypothesis.D.subgroupOf L) ⊓
      Subgroup.centralizer ((fc.toHypothesis.Q.subgroupOf L) : Set ↥L) := by
    rw [hNdef]; exact fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V
  have hNleD : N ≤ fc.toHypothesis.D.subgroupOf L := by
    rw [hcore]; exact inf_le_left
  have hNodd : Odd (Nat.card ↥N) :=
    (fc.toHypothesis.centralizerHypothesisA1 fc.P_le_V).D_odd.of_dvd_nat
      (Subgroup.card_dvd_of_le hNleD)
  have hsN : ∀ n ∈ N, Commute sL n := by
    intro n hn
    have hnC : n ∈ Subgroup.centralizer
        ((fc.toHypothesis.Q.subgroupOf L) : Set ↥L) := by
      rw [hcore] at hn; exact hn.2
    have hsQL : sL ∈ fc.toHypothesis.Q.subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr hsQ
    exact Subgroup.mem_centralizer_iff.mp hnC sL hsQL
  -- `s ∉ N` (`s ∈ Q ∩ D = 1` would force `s = 1`) and `t ∉ N` (`t ∉ H`)
  have hsN_not : sL ∉ N := by
    intro h
    have hsD : (sL : G) ∈ fc.toHypothesis.D :=
      Subgroup.mem_subgroupOf.mp (hNleD h)
    have hbot : (sL : G) ∈ fc.toHypothesis.Q ⊓ fc.toHypothesis.D := ⟨hsQ, hsD⟩
    rw [fc.toHypothesis.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
    exact fc.toHypothesis.distinguishedInvolution_ne_one hbot
  have htN_not : tL ∉ N := by
    intro h
    have htD : (tL : G) ∈ fc.toHypothesis.D :=
      Subgroup.mem_subgroupOf.mp (hNleD h)
    exact fc.toHypothesis.t_not_mem_H (fc.toHypothesis.D_le_H htD)
  have hne : sL * tL ≠ 1 := by
    intro h
    have hst : fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t = 1 := by
      have := congrArg (Subtype.val) h
      rwa [Subgroup.coe_mul, Subgroup.coe_one] at this
    have hst' : fc.toHypothesis.distinguishedInvolution = fc.toHypothesis.t⁻¹ :=
      mul_eq_one_iff_eq_inv.mp hst
    apply fc.toHypothesis.t_not_mem_H
    rw [fc.toHypothesis.t_inv_eq] at hst'
    exact hst' ▸ fc.toHypothesis.distinguishedInvolution_mem_H
  -- the images are distinct involutions of the quotient `L/N`
  have hu2 : (pi sL) ^ 2 = 1 := by rw [← map_pow, hs2, map_one]
  have hv2 : (pi tL) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hu1 : pi sL ≠ 1 := by
    rw [hpidef, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hsN_not
  have hv1 : pi tL ≠ 1 := by
    rw [hpidef, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact htN_not
  have huv : pi sL ≠ pi tL := by
    intro h
    have h1 : pi (sL * tL⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    rw [hpidef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hstD : ((sL * tL⁻¹ : ↥L) : G) ∈ fc.toHypothesis.D :=
      Subgroup.mem_subgroupOf.mp (hNleD h1)
    have hstH : ((sL * tL⁻¹ : ↥L) : G) ∈ fc.toHypothesis.H :=
      fc.toHypothesis.D_le_H hstD
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at hstH
    have htinvH : fc.toHypothesis.t⁻¹ ∈ fc.toHypothesis.H := by
      have hsinvH : fc.toHypothesis.distinguishedInvolution⁻¹ ∈ fc.toHypothesis.H :=
        fc.toHypothesis.H.inv_mem fc.toHypothesis.distinguishedInvolution_mem_H
      have : fc.toHypothesis.distinguishedInvolution⁻¹ *
          (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t⁻¹) ∈
          fc.toHypothesis.H := fc.toHypothesis.H.mul_mem hsinvH hstH
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    exact fc.toHypothesis.t_not_mem_H
      (by rw [fc.toHypothesis.t_inv_eq] at htinvH; exact htinvH)
  -- `char = |s̄ · t̄|`
  have hchar : orderOf (pi sL * pi tL) = model.char :=
    model.orderOf_mul_of_involutions (pi sL) (pi tL) hu2 hu1 hv2 hv1 huv
  have hpow1 : (pi sL * pi tL) ^ model.char = 1 := by
    rw [← hchar]; exact pow_orderOf_eq_one _
  have hpowN : (sL * tL) ^ model.char ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, ← hpidef, map_pow, map_mul]
    exact hpow1
  have hbridge : orderOf (sL * tL) = model.char :=
    orderOf_mul_eq_prime_of_pow_mem_odd_kernel
      model.char_prime hNodd hs2 ht2 hsN hpowN hne
  have htransfer := orderOf_injective L.subtype L.subtype_injective (sL * tL)
  rw [hbridge] at htransfer
  have hcoe : L.subtype (sL * tL) =
      fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t := by
    rw [map_mul]; rfl
  rwa [hcoe] at htransfer

end FirstCaseHypothesis

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G] (hyp : Hypothesis G Ω)

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c), the `|C_Q(X)|` reading**
(used in step (7), p. 110): for a nontrivial `X ≤ V` (with the induction
hypothesis and a four-subgroup in `C_G(X)`), the centralizer `C_Q(X)` is a
`2`-group, and its order is tied to the global product order
`f = |s·t| = orderOf(distinguishedInvolution · t)`:

* `PSL(2,ℓ)`: `|C_Q(X)| = |C_{Q₀}(X)|` and `f = 3`;
* `Sz(ℓ)`: `|C_Q(X)| = |C_{Q₀}(X)|²` and `f = 5`;
* `PSU(3,ℓ)`: `|C_Q(X)| = |C_{Q₀}(X)|³` and `f = 3`.

Assembled by casing the trichotomy branch. -/
theorem cQ_card_and_pGroup_of_trichotomy {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hX : X ≠ ⊥)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (ind : TheoremAInductionBelow G Ω) :
    IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) ∧
    ((Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
        Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) ∧
        orderOf (hyp.distinguishedInvolution * hyp.t) = 3) ∨
     (Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
        Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) ^ 2 ∧
        orderOf (hyp.distinguishedInvolution * hyp.t) = 5) ∨
     (Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) =
        Nat.card ↥(hyp.Q0.subgroupOf (Subgroup.centralizer (X : Set G))) ^ 3 ∧
        orderOf (hyp.distinguishedInvolution * hyp.t) = 3)) := by
  letI := hyp.centralizerQuotientMulAction hXV
  obtain ⟨tdata⟩ := hyp.centralizer_trichotomy_of_induction hXV hX hA3 ind
  refine ⟨tdata.common.cQ_isPGroup, ?_⟩
  rcases tdata.branch with ⟨data, teq, details⟩ | ⟨data, teq, details⟩ |
    ⟨data, teq, details⟩
  · exact Or.inl ⟨by rw [details.natCard_cQ_eq_field, details.natCard_cQ0_eq_field],
      details.distinguishedProduct_order⟩
  · exact Or.inr (Or.inl ⟨details.natCard_cQ_eq_cQ0_sq,
      details.distinguishedProduct_order⟩)
  · exact Or.inr (Or.inr ⟨details.natCard_cQ_eq_cQ0_cube,
      details.distinguishedProduct_order⟩)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
