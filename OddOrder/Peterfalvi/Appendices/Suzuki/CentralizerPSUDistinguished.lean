/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerDistinguishedBridge
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerPSURoot

/-!
# Peterfalvi Part II, Ch. I section 3: the distinguished PSU pair

In the PSU(3,q) alternative of Proposition 1(c), the distinguished
involution s and the fixed involution t have product of order three.
The equivalence between Q and the standard Hermitian root group does not by
itself retain this pair.  We therefore keep the ambient Sylow conjugator and
normalize the image of t while preserving the standard root subgroup.

A root translation first makes t interchange infinity and the affine
origin.  The remaining factor is in the determinant-one torus.  Weyl
conjugation acts on that torus through psuWeylParameterHom.  The involution
condition says that the torus parameter c is sent to c inverse.  Since the
torus has odd order, an odd-order square root d of c inverse provides a
final torus conjugation sending t to the standard Weyl involution.

The transported structure equation then identifies s with the canonical
central root involution.  The existing standard braid relation gives exact
order three, and the centralizer-quotient theorem lifts the cube relation
through the odd central kernel.

This is the PSU branch of T. Peterfalvi, Character Theory for the Odd Order
Theorem, Part II, Ch. I section 3, Proposition 1(c), pp. 105--106.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

open scoped Pointwise

universe u v

/-! ## Conjugations preserving the standard unitary root subgroup -/

private theorem rootHom_conj_mem_standardRootSubgroup_iff
    {n : ℕ} (a : RootGroup n) (x : standardPermGroup n) :
    rootHom n a * x * (rootHom n a)⁻¹ ∈ standardRootSubgroup n ↔
      x ∈ standardRootSubgroup n := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨a⁻¹ * b * a, ?_⟩
    calc
      rootHom n (a⁻¹ * b * a) =
          (rootHom n a)⁻¹ * rootHom n b * rootHom n a := by
        rw [map_mul, map_mul, map_inv]
      _ = x := by rw [hb]; group
  · rintro ⟨b, rfl⟩
    refine ⟨a * b * a⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv]

private theorem psuTorusHom_conj_mem_standardRootSubgroup_iff
    {n : ℕ} (c : PSUTorusParameter n) (x : standardPermGroup n) :
    psuTorusHom n c * x * (psuTorusHom n c)⁻¹ ∈
        standardRootSubgroup n ↔
      x ∈ standardRootSubgroup n := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨psuTorusScaleHom n c⁻¹ b, ?_⟩
    calc
      rootHom n (psuTorusScaleHom n c⁻¹ b) =
          psuTorusHom n c⁻¹ * rootHom n b *
            (psuTorusHom n c⁻¹)⁻¹ :=
        (psuTorusHom_mul_rootHom_mul_inv c⁻¹ b).symm
      _ = (psuTorusHom n c)⁻¹ * rootHom n b *
            psuTorusHom n c := by
        rw [map_inv, inv_inv]
      _ = x := by rw [hb]; group
  · rintro ⟨b, rfl⟩
    exact ⟨psuTorusScaleHom n c b,
      (psuTorusHom_mul_rootHom_mul_inv c b).symm⟩

private theorem standardBorel_conj_mem_standardRootSubgroup
    {n : ℕ} {b x : standardPermGroup n}
    (hb : b ∈ standardBorel n) (hx : x ∈ standardRootSubgroup n) :
    b * x * b⁻¹ ∈ standardRootSubgroup n := by
  obtain ⟨p, hp, -⟩ :=
    (mem_standardBorel_iff_existsUnique_root_torus b).mp hb
  rw [hp]
  have ht :=
    (psuTorusHom_conj_mem_standardRootSubgroup_iff p.2 x).2 hx
  have hr :=
    (rootHom_conj_mem_standardRootSubgroup_iff p.1
      (psuTorusHom n p.2 * x * (psuTorusHom n p.2)⁻¹)).2 ht
  convert hr using 1
  · group

/-! ## Odd square roots in the determinant-one torus -/

private theorem sq_pow_half_orderOf
    {A : Type*} [Group A] {a : A} (ha : Odd (orderOf a)) :
    (a ^ ((orderOf a + 1) / 2)) ^ 2 = a := by
  rw [← pow_mul]
  obtain ⟨j, hj⟩ := ha
  rw [show (orderOf a + 1) / 2 * 2 = orderOf a + 1 from by omega,
    pow_succ, pow_orderOf_eq_one, one_mul]

private theorem eq_of_sq_eq_of_odd_orderOf
    {A : Type*} [Group A] {k₁ k₂ a : A}
    (h1 : Odd (orderOf k₁)) (h2 : Odd (orderOf k₂))
    (e1 : k₁ ^ 2 = a) (e2 : k₂ ^ 2 = a) :
    k₁ = k₂ := by
  have hoa1 : orderOf a = orderOf k₁ := by
    rw [← e1]
    exact (Nat.coprime_two_right.mpr h1).orderOf_pow
  have hoa2 : orderOf a = orderOf k₂ := by
    rw [← e2]
    exact (Nat.coprime_two_right.mpr h2).orderOf_pow
  have hk1 : k₁ = a ^ ((orderOf k₁ + 1) / 2) := by
    rw [← e1, ← pow_mul]
    obtain ⟨j, hj⟩ := h1
    rw [show 2 * ((orderOf k₁ + 1) / 2) = orderOf k₁ + 1 from by omega,
      pow_succ, pow_orderOf_eq_one, one_mul]
  have hk2 : k₂ = a ^ ((orderOf k₂ + 1) / 2) := by
    rw [← e2, ← pow_mul]
    obtain ⟨j, hj⟩ := h2
    rw [show 2 * ((orderOf k₂ + 1) / 2) = orderOf k₂ + 1 from by omega,
      pow_succ, pow_orderOf_eq_one, one_mul]
  rw [hk1, hk2, ← hoa1, ← hoa2]

private theorem orderOf_psuTorus_odd
    (n : ℕ) (hn : 0 < n) (c : PSUTorusParameter n) :
    Odd (orderOf c) := by
  have hcardOdd : Odd (Nat.card (GeneralTorusParameter n)) := by
    rw [natCard_generalTorus n hn]
    exact Nat.Even.sub_odd (one_le_pow₀ one_le_two)
      (even_two.pow_of_ne_zero (by omega)) odd_one
  have horder :
      orderOf (c : GeneralTorusParameter n) = orderOf c :=
    orderOf_injective (PSUTorusParameter n).subtype
      (PSUTorusParameter n).subtype_injective c
  rw [← horder]
  exact hcardOdd.of_dvd_nat
    (orderOf_dvd_natCard (c : GeneralTorusParameter n))

namespace Hypothesis

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
  [Finite G]

/-! ## Transporting the complete pair through a PSU target -/

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSU case.**
For a concrete PSU(3,q) Theorem A target, the distinguished product s*t
has order three.

The proof retains the ambient Sylow conjugator.  Root and determinant-one
torus corrections put Q and t simultaneously into standard root/Weyl
position; the structure equation and uniqueness then determine s. -/
theorem orderOf_distinguishedInvolution_mul_t_of_psu3Target
    (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : PSU3InductionTarget (Omega := Omega) L) :
    orderOf (hyp.distinguishedInvolution * hyp.t) = 3 := by
  have hn0 : 0 < data.n := lt_trans Nat.zero_lt_one data.one_lt_n
  have hcore := hyp.Q_and_residual_of_psu3_target L hLnormal hLodd
    data.one_lt_n data.groupEquiv data.actionEquiv
      data.actionEquiv_bijective
  obtain ⟨hQp, hQL, _, _⟩ := hcore
  let P : Sylow 2 G := Classical.choose (hyp.exists_sylow_two_eq_Q hQp)
  have hP : (P : Subgroup G) = hyp.Q :=
    Classical.choose_spec (hyp.exists_sylow_two_eq_Q hQp)
  have hPL : (P : Subgroup G) ≤ L := hP ▸ hQL
  let PL : Sylow 2 L := P.subtype hPL
  let Pbar : Sylow 2 (standardPermGroup data.n) :=
    Sylow.mapEquiv data.groupEquiv PL
  let g : standardPermGroup data.n :=
    Classical.choose (MulAction.exists_smul_eq _ Pbar
      (standardRootSylow data.n hn0))
  have hg : g • Pbar = standardRootSylow data.n hn0 :=
    Classical.choose_spec (MulAction.exists_smul_eq _ Pbar
      (standardRootSylow data.n hn0))
  let e0 : L ≃* standardPermGroup data.n :=
    data.groupEquiv.trans (MulAut.conj g)
  have hPLQ : (PL : Subgroup L) = hyp.Q.subgroupOf L := by
    dsimp only [PL]
    rw [Sylow.coe_subtype]
    ext x
    change (x : G) ∈ P ↔ (x : G) ∈ hyp.Q
    exact SetLike.ext_iff.mp hP (x : G)
  have hrootEq :
      (MulAut.conj g) •
          (Pbar : Subgroup (standardPermGroup data.n)) =
        standardRootSubgroup data.n := by
    rw [← Sylow.coe_subgroup_smul, hg, coe_standardRootSylow]
  have hmem0 (x : L) :
      e0 x ∈ standardRootSubgroup data.n ↔ (x : G) ∈ hyp.Q := by
    have hmap :
        data.groupEquiv x ∈
            (Pbar : Subgroup (standardPermGroup data.n)) ↔
          x ∈ (PL : Subgroup L) := by
      dsimp only [Pbar]
      rw [Sylow.coe_mapEquiv, Subgroup.mem_map_equiv]
      simp
    constructor
    · intro hx
      change (MulAut.conj g) • data.groupEquiv x ∈
        standardRootSubgroup data.n at hx
      rw [← hrootEq, Subgroup.smul_mem_pointwise_smul_iff] at hx
      have hxPL : x ∈ (PL : Subgroup L) := hmap.mp hx
      have hxQL : x ∈ hyp.Q.subgroupOf L :=
        (SetLike.ext_iff.mp hPLQ x).mp hxPL
      exact hxQL
    · intro hx
      change (MulAut.conj g) • data.groupEquiv x ∈
        standardRootSubgroup data.n
      rw [← hrootEq, Subgroup.smul_mem_pointwise_smul_iff]
      apply hmap.mpr
      apply (SetLike.ext_iff.mp hPLQ x).mpr
      exact hx
  have hsQ : hyp.distinguishedInvolution ∈ hyp.Q :=
    hyp.mem_Q_of_sq_eq_one_of_mem_H
      hyp.distinguishedInvolution_mem_H hyp.distinguishedInvolution_sq
  have hsL : hyp.distinguishedInvolution ∈ L := hQL hsQ
  have htLmem : hyp.t ∈ L := by
    obtain ⟨c, hc⟩ := isConj_iff.mp
      (hyp.isConj_of_involutions hyp.distinguishedInvolution_sq
        hyp.distinguishedInvolution_ne_one hyp.t_sq hyp.t_ne_one)
    rw [← hc]
    exact hLnormal.conj_mem hyp.distinguishedInvolution hsL c
  let sL : L := ⟨hyp.distinguishedInvolution, hsL⟩
  let tL : L := ⟨hyp.t, htLmem⟩
  let z : standardPermGroup data.n := e0 tL
  have hz2 : z ^ 2 = 1 := by
    dsimp only [z]
    rw [← map_pow, show tL ^ 2 = 1 from Subtype.ext hyp.t_sq, map_one]
  have hforward :
      z ∈ standardBorel data.n →
        ∀ q : G, q ∈ hyp.Q → hyp.t * q * hyp.t⁻¹ ∈ hyp.Q := by
    intro hzB q hq
    let qL : L := ⟨q, hQL hq⟩
    have hqroot : e0 qL ∈ standardRootSubgroup data.n :=
      (hmem0 qL).2 hq
    have hconj :=
      standardBorel_conj_mem_standardRootSubgroup hzB hqroot
    apply (hmem0 (tL * qL * tL⁻¹)).1
    simpa only [map_mul, map_inv, z] using hconj
  have hz_not_fix :
      z • Unital.infinity data.n ≠ Unital.infinity data.n := by
    intro hzfix
    have hzB : z ∈ standardBorel data.n := by
      rw [standardBorel_eq_infinityStabilizer data.n hn0,
        MulAction.mem_stabilizer_iff]
      exact hzfix
    have htNorm : hyp.t ∈ Subgroup.normalizer (hyp.Q : Set G) := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro q
      constructor
      · exact hforward hzB q
      · intro hq
        have htwice :=
          hforward hzB (hyp.t * q * hyp.t⁻¹) hq
        have hcancel :
            hyp.t * (hyp.t * q * hyp.t⁻¹) * hyp.t⁻¹ = q := by
          rw [hyp.t_inv_eq]
          calc
            hyp.t * (hyp.t * q * hyp.t) * hyp.t =
                (hyp.t * hyp.t) * q * (hyp.t * hyp.t) := by group
            _ = q := by rw [hyp.t_mul_t, one_mul, mul_one]
        rw [hcancel] at htwice
        exact htwice
    rw [hyp.normalizer_Q_eq_H] at htNorm
    exact hyp.t_not_mem_H htNorm
  obtain ⟨u, hu⟩ : ∃ u : RootGroup data.n,
      z • Unital.infinity data.n = Unital.affine u := by
    cases hpoint : z • Unital.infinity data.n with
    | none =>
        exact (hz_not_fix (by
          simpa only [Unital.infinity] using hpoint)).elim
    | some u =>
        exact ⟨u, rfl⟩
  let a : standardPermGroup data.n := rootHom data.n u⁻¹
  let z1 : standardPermGroup data.n := (MulAut.conj a) z
  have hainf :
      (rootHom data.n u⁻¹)⁻¹ • Unital.infinity data.n =
        Unital.infinity data.n := by
    rw [← map_inv, rootHom_smul_infinity]
  have hz1inf :
      z1 • Unital.infinity data.n = Unital.origin data.n := by
    dsimp only [z1, a]
    change
      (rootHom data.n u⁻¹ * z * (rootHom data.n u⁻¹)⁻¹) •
        Unital.infinity data.n = Unital.origin data.n
    rw [mul_smul, mul_smul, hainf, hu, rootHom_smul_affine,
      inv_mul_cancel]
    rfl
  have hz1sq : z1 ^ 2 = 1 := by
    dsimp only [z1]
    rw [← map_pow, hz2, map_one]
  have hz1origin :
      z1 • Unital.origin data.n = Unital.infinity data.n := by
    have h := congrArg
      (fun q : standardPermGroup data.n =>
        q • Unital.infinity data.n) hz1sq
    simpa only [pow_two, mul_smul, hz1inf, one_smul] using h
  let h : standardPermGroup data.n := z1 * weylElement data.n
  have hfixInf : h • Unital.infinity data.n = Unital.infinity data.n := by
    dsimp only [h]
    rw [mul_smul, weylElement_smul_infinity, hz1origin]
  have hfixOrigin : h • Unital.origin data.n = Unital.origin data.n := by
    dsimp only [h]
    rw [mul_smul, weylElement_smul_origin, hz1inf]
  have hB : h ∈ standardBorel data.n := by
    rw [standardBorel_eq_infinityStabilizer data.n hn0,
      MulAction.mem_stabilizer_iff]
    exact hfixInf
  obtain ⟨p, hp, -⟩ :=
    (mem_standardBorel_iff_existsUnique_root_torus h).mp hB
  have hpLeft : p.1 = 1 := by
    have haffine :
        Unital.affine p.1 =
          Unital.affine (1 : RootGroup data.n) := by
      simpa only [hp, mul_smul, Unital.origin_eq_affine_one,
        psuTorusHom_smul_affine, map_one, rootHom_smul_affine,
        mul_one] using hfixOrigin
    exact (Unital.affine_inj).mp haffine
  let c : PSUTorusParameter data.n := p.2
  have hh : h = psuTorusHom data.n c := by
    rw [hp, hpLeft, map_one, one_mul]
  have hz1form :
      z1 = psuTorusHom data.n c * weylElement data.n := by
    calc
      z1 = (z1 * weylElement data.n) * weylElement data.n := by
        rw [mul_assoc, ← pow_two, weylElement_sq_eq_one, mul_one]
      _ = psuTorusHom data.n c * weylElement data.n := by
        change h * weylElement data.n = _
        rw [hh]
  have hcpsi :
      c * Unital.psuWeylParameterHom data.n c = 1 := by
    apply psuTorusHom_injective data.n
    rw [map_mul, map_one]
    calc
      psuTorusHom data.n c *
            psuTorusHom data.n (Unital.psuWeylParameterHom data.n c) =
          psuTorusHom data.n c *
            (weylElement data.n * psuTorusHom data.n c *
              weylElement data.n) := by
        rw [weylElement_mul_psuTorusHom_mul_weylElement]
      _ = (psuTorusHom data.n c * weylElement data.n) ^ 2 := by
        rw [pow_two]
        group
      _ = z1 ^ 2 := by rw [hz1form]
      _ = 1 := hz1sq
  have hpsi :
      Unital.psuWeylParameterHom data.n c = c⁻¹ := by
    calc
      Unital.psuWeylParameterHom data.n c =
          1 * Unital.psuWeylParameterHom data.n c := by rw [one_mul]
      _ = c⁻¹ * c * Unital.psuWeylParameterHom data.n c := by
        rw [inv_mul_cancel]
      _ = c⁻¹ * (c * Unital.psuWeylParameterHom data.n c) := by
        rw [mul_assoc]
      _ = c⁻¹ := by rw [hcpsi, mul_one]
  have hcinvOdd : Odd (orderOf c⁻¹) := by
    simpa only [orderOf_inv] using orderOf_psuTorus_odd data.n hn0 c
  let d : PSUTorusParameter data.n :=
    c⁻¹ ^ ((orderOf c⁻¹ + 1) / 2)
  have hd2 : d ^ 2 = c⁻¹ := by
    dsimp only [d]
    exact sq_pow_half_orderOf hcinvOdd
  have hpsiDSq :
      (Unital.psuWeylParameterHom data.n d) ^ 2 = c := by
    calc
      (Unital.psuWeylParameterHom data.n d) ^ 2 =
          Unital.psuWeylParameterHom data.n (d ^ 2) :=
        ((Unital.psuWeylParameterHom data.n).map_pow d 2).symm
      _ = Unital.psuWeylParameterHom data.n c⁻¹ := by rw [hd2]
      _ = (Unital.psuWeylParameterHom data.n c)⁻¹ := by
        rw [map_inv]
      _ = (c⁻¹)⁻¹ := by rw [hpsi]
      _ = c := inv_inv c
  have hdinvSq : (d⁻¹) ^ 2 = c := by
    rw [inv_pow, hd2, inv_inv]
  have hpsiD :
      Unital.psuWeylParameterHom data.n d = d⁻¹ :=
    eq_of_sq_eq_of_odd_orderOf
      (orderOf_psuTorus_odd data.n hn0
        (Unital.psuWeylParameterHom data.n d))
      (orderOf_psuTorus_odd data.n hn0 d⁻¹)
      hpsiDSq hdinvSq
  have hdcd :
      d * c * Unital.psuWeylParameterHom data.n d⁻¹ = 1 := by
    rw [map_inv, hpsiD, inv_inv]
    calc
      d * c * d = d ^ 2 * c := by
        rw [pow_two]
        ac_rfl
      _ = c⁻¹ * c := by rw [hd2]
      _ = 1 := inv_mul_cancel c
  have hnormalize :
      (MulAut.conj (psuTorusHom data.n d)) z1 =
        weylElement data.n := by
    change
      psuTorusHom data.n d * z1 * (psuTorusHom data.n d)⁻¹ =
        weylElement data.n
    rw [hz1form]
    calc
      psuTorusHom data.n d *
            (psuTorusHom data.n c * weylElement data.n) *
            (psuTorusHom data.n d)⁻¹ =
          psuTorusHom data.n d * psuTorusHom data.n c *
            weylElement data.n * (psuTorusHom data.n d)⁻¹ *
              (weylElement data.n * weylElement data.n) := by
        rw [show weylElement data.n * weylElement data.n = 1 from by
          simpa only [pow_two] using weylElement_sq_eq_one data.n, mul_one]
        group
      _ = psuTorusHom data.n d * psuTorusHom data.n c *
            (weylElement data.n * (psuTorusHom data.n d)⁻¹ *
              weylElement data.n) * weylElement data.n := by group
      _ = psuTorusHom data.n d * psuTorusHom data.n c *
            psuTorusHom data.n
              (Unital.psuWeylParameterHom data.n d⁻¹) *
                weylElement data.n := by
        rw [← map_inv,
          weylElement_mul_psuTorusHom_mul_weylElement]
      _ = psuTorusHom data.n
            (d * c * Unital.psuWeylParameterHom data.n d⁻¹) *
              weylElement data.n := by
        rw [map_mul, map_mul]
      _ = weylElement data.n := by
        rw [hdcd, map_one, one_mul]
  let e1 : L ≃* standardPermGroup data.n := e0.trans (MulAut.conj a)
  let e : L ≃* standardPermGroup data.n :=
    e1.trans (MulAut.conj (psuTorusHom data.n d))
  have hmem (x : L) :
      e x ∈ standardRootSubgroup data.n ↔ (x : G) ∈ hyp.Q := by
    change
      psuTorusHom data.n d *
            (rootHom data.n u⁻¹ * e0 x * (rootHom data.n u⁻¹)⁻¹) *
            (psuTorusHom data.n d)⁻¹ ∈ standardRootSubgroup data.n ↔
        (x : G) ∈ hyp.Q
    rw [psuTorusHom_conj_mem_standardRootSubgroup_iff,
      rootHom_conj_mem_standardRootSubgroup_iff]
    exact hmem0 x
  have het : e tL = weylElement data.n := by
    change (MulAut.conj (psuTorusHom data.n d))
      ((MulAut.conj a) (e0 tL)) = weylElement data.n
    exact hnormalize
  let sStd : standardPermGroup data.n :=
    rootHom data.n (RootGroup.centralInvolution data.n)
  have hsStdRoot : sStd ∈ standardRootSubgroup data.n :=
    ⟨RootGroup.centralInvolution data.n, rfl⟩
  have hsStdSq : sStd ^ 2 = 1 := by
    dsimp only [sStd]
    rw [← map_pow, RootGroup.centralInvolution_sq, map_one]
  have hsStdInv : sStd⁻¹ = sStd :=
    inv_eq_of_mul_eq_one_left (by
      simpa only [pow_two] using hsStdSq)
  let s0L : L := e.symm sStd
  let r0L : L := e.symm sStd
  have hes0 : e s0L = sStd := e.apply_symm_apply sStd
  have her0 : e r0L = sStd := e.apply_symm_apply sStd
  have hs0Q : (s0L : G) ∈ hyp.Q := by
    apply (hmem s0L).1
    rw [hes0]
    exact hsStdRoot
  have hr0Q : (r0L : G) ∈ hyp.Q := by
    apply (hmem r0L).1
    rw [her0]
    exact hsStdRoot
  have hs0H : (s0L : G) ∈ hyp.H := hyp.Q_le_H hs0Q
  have hs0sqL : s0L ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, hes0]
    exact hsStdSq
  have hs0sq : (s0L : G) ^ 2 = 1 :=
    congrArg (fun x : L => (x : G)) hs0sqL
  have hs0ne : (s0L : G) ≠ 1 := by
    intro hs
    apply RootGroup.centralInvolution_ne_one data.n
    apply rootHom_injective data.n
    have hsL : s0L = 1 := Subtype.ext hs
    have hmap := congrArg e hsL
    rw [hes0, map_one] at hmap
    simpa only [map_one, sStd] using hmap
  have hstructureL :
      tL * s0L * tL = r0L⁻¹ * tL * r0L := by
    apply e.injective
    simpa only [map_mul, map_inv, het, hes0, her0, hsStdInv,
      sStd] using standard_braid data.n
  have hstructure :
      hyp.t * (s0L : G) * hyp.t =
        (r0L : G)⁻¹ * hyp.t * (r0L : G) :=
    congrArg (fun x : L => (x : G)) hstructureL
  have hpair := hyp.eq_distinguishedPair_of_structure
    hs0H hs0sq hs0ne hr0Q hstructure
  have hsLs0 : sL = s0L := Subtype.ext hpair.1.symm
  have hes : e sL = sStd := by
    rw [hsLs0]
    exact e.apply_symm_apply _
  have htarget :
      orderOf (e sL * e tL) = 3 := by
    rw [hes, het]
    exact standard_st_order data.n
  have hLorder : orderOf (sL * tL) = 3 := by
    rw [← orderOf_injective e.toMonoidHom e.injective]
    change orderOf (e (sL * tL)) = 3
    rw [map_mul]
    exact htarget
  calc
    orderOf (hyp.distinguishedInvolution * hyp.t) =
        orderOf (sL * tL) :=
      orderOf_injective L.subtype L.subtype_injective (sL * tL)
    _ = 3 := hLorder

/-! ## The faithful centralizer quotient -/

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSU case.**
In the PSU branch of the induction conclusion for
C_G(X)/N(C_G(X)), the original distinguished product s*t has order
three.  The standard unitary relation proves the cube relation in the
faithful quotient, and the odd-kernel theorem lifts it back to G. -/
theorem orderOf_distinguishedInvolution_mul_t_of_centralizer_psu3Target
    (hyp : Hypothesis G Omega) {X : Subgroup G}
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    orderOf (hyp.distinguishedInvolution * hyp.t) = 3 := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  have hquotOrder :
      orderOf (qhyp.distinguishedInvolution * qhyp.t) = 3 :=
    qhyp.orderOf_distinguishedInvolution_mul_t_of_psu3Target
      result.L result.normal result.oddIndex data
  have hquotCube :
      (qhyp.distinguishedInvolution * qhyp.t) ^ 3 = 1 := by
    rw [← hquotOrder]
    exact pow_orderOf_eq_one _
  exact hyp.orderOf_distinguishedInvolution_mul_t_of_quotient_pow
    hXV hA3 Nat.prime_three hquotCube

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
