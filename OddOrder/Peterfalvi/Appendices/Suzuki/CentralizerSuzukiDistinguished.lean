/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Perfect
import OddOrder.GroupTheory.SpecificGroups.Suzuki.RootSubgroupSuzukiType
import OddOrder.GroupTheory.SylowTransport
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerDistinguishedBridge
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesisSuzuki

/-!
# Peterfalvi Part II, Ch. I section 3: the distinguished Suzuki pair

In the `Sz(q)` alternative of Proposition 1(c), the distinguished
involution `s` and the fixed involution `t` have product of order five.
An arbitrary equivalence between their Sylow `2`-subgroup carriers does not
remember this pair.  We instead retain the ambient Sylow conjugator and then
correct it inside the standard Borel subgroup.

After the first conjugation, `Q` is the standard root subgroup.  The image
of `t` cannot fix infinity: otherwise it would normalize the root subgroup,
and hence `t` would belong to `N_G(Q) = H`.  A root translation makes
`t` interchange infinity and the affine origin.  Its product with the Weyl
element then fixes both points, so the unique root--torus normal form shows
that it is a torus element.  Since the defining field has characteristic
two, the torus squaring map is bijective; a final torus conjugation sends
`t` exactly to the standard Weyl involution while preserving the root
subgroup.

The standard root involution and Weyl involution satisfy the transported
structure equation.  Uniqueness of Peterfalvi's distinguished pair therefore
identifies the transported `s` with the standard root involution.  The
concrete order-five calculation in `RootSubgroupStructure` then applies.
Finally, the centralizer-quotient theorem lifts the fifth-power relation
through the odd central kernel.

This is the Suzuki branch of T. Peterfalvi, *Character Theory for the Odd
Order Theorem*, Part II, Ch. I section 3, Proposition 1(c), pp. 105--106.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.GroupTheory.SpecificGroups.Suzuki

open scoped CharTwo Pointwise

universe u v

/-! ## Root and torus conjugation preserve the standard root subgroup -/

private theorem rootHom_conj_mem_standardRootSubgroup_iff
    {m : ℕ} (a : RootGroup m) (x : standardPermGroup m) :
    rootHom m a * x * (rootHom m a)⁻¹ ∈ standardRootSubgroup m ↔
      x ∈ standardRootSubgroup m := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨a⁻¹ * b * a, ?_⟩
    calc
      rootHom m (a⁻¹ * b * a) =
          (rootHom m a)⁻¹ * rootHom m b * rootHom m a := by
        rw [map_mul, map_mul, map_inv]
      _ = x := by rw [hb]; group
  · rintro ⟨b, rfl⟩
    refine ⟨a * b * a⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv]

private theorem torusHom_conj_mem_standardRootSubgroup_iff
    {m : ℕ} (c : TorusParameter m) (x : standardPermGroup m) :
    torusHom m c * x * (torusHom m c)⁻¹ ∈ standardRootSubgroup m ↔
      x ∈ standardRootSubgroup m := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨torusScale c⁻¹ b, ?_⟩
    calc
      rootHom m (torusScale c⁻¹ b) =
          torusHom m c⁻¹ * rootHom m b * (torusHom m c⁻¹)⁻¹ :=
        (torusHom_mul_rootHom_mul_inv c⁻¹ b).symm
      _ = (torusHom m c)⁻¹ * rootHom m b * torusHom m c := by
        rw [map_inv, inv_inv]
      _ = x := by rw [hb]; group
  · rintro ⟨b, rfl⟩
    exact ⟨torusScale c b, (torusHom_mul_rootHom_mul_inv c b).symm⟩

private theorem standardBorel_conj_mem_standardRootSubgroup
    {m : ℕ} {b x : standardPermGroup m}
    (hb : b ∈ standardBorel m) (hx : x ∈ standardRootSubgroup m) :
    b * x * b⁻¹ ∈ standardRootSubgroup m := by
  obtain ⟨p, hp, -⟩ :=
    (mem_standardBorel_iff_existsUnique_root_torus b).mp hb
  rw [hp]
  have ht := (torusHom_conj_mem_standardRootSubgroup_iff p.2 x).2 hx
  have hr :=
    (rootHom_conj_mem_standardRootSubgroup_iff p.1
      (torusHom m p.2 * x * (torusHom m p.2)⁻¹)).2 ht
  convert hr using 1; group

/-! ## The canonical standard structure equation -/

/-- The standard right-root parameter in the distinguished Suzuki structure
equation. -/
private noncomputable def standardStructureConjugatorParameter (m : ℕ) :
    RootGroup m :=
  RootGroup.mk 1 1

/-- The standard root element `r` satisfying
`w s w = r⁻¹ w r`. -/
noncomputable def standardStructureConjugator (m : ℕ) :
    standardPermGroup m :=
  rootHom m (standardStructureConjugatorParameter m)

theorem standardStructureConjugator_mem_standardRootSubgroup (m : ℕ) :
    standardStructureConjugator m ∈ standardRootSubgroup m :=
  ⟨standardStructureConjugatorParameter m, rfl⟩

private theorem standardRootParameter_ne_one (m : ℕ) :
    (RootGroup.mk 0 1 : RootGroup m) ≠ 1 := by
  intro h
  have h' := congrArg RootGroup.snd h
  simp at h'

private theorem standardRootParameter_norm (m : ℕ) :
    (RootGroup.mk 0 1 : RootGroup m).suzukiNorm = 1 := by
  change suzukiNorm m 0 1 = 1
  simp [suzukiNorm]

private theorem standardRootParameter_weylAffine (m : ℕ) :
    Ovoid.weylAffine (RootGroup.mk 0 1 : RootGroup m) =
      RootGroup.mk 1 0 := by
  ext
  · change (1 : Field m) /
      (RootGroup.mk 0 1 : RootGroup m).suzukiNorm = 1
    rw [standardRootParameter_norm, div_one]
  · change (0 : Field m) /
      (RootGroup.mk 0 1 : RootGroup m).suzukiNorm = 0
    rw [zero_div]

private theorem standardRootParameter_bruhatRightRoot (m : ℕ) :
    bruhatRightRoot (RootGroup.mk 0 1 : RootGroup m) =
      standardStructureConjugatorParameter m := by
  ext
  · change ((1 : Field m) + 0 * titsTwist m 0) /
        (RootGroup.mk 0 1 : RootGroup m).suzukiNorm = 1
    rw [zero_mul, add_zero, standardRootParameter_norm, div_one]
  · change (1 : Field m) /
        titsTwist m (RootGroup.mk 0 1 : RootGroup m).suzukiNorm = 1
    rw [standardRootParameter_norm, map_one, div_one]

private theorem standardRootParameter_bruhatTorus (m : ℕ) :
    bruhatTorus (RootGroup.mk 0 1 : RootGroup m)
      (standardRootParameter_ne_one m) = 1 := by
  apply Units.ext
  change (RootGroup.mk 0 1 : RootGroup m).suzukiNorm ^ 2 /
      titsTwist m (RootGroup.mk 0 1 : RootGroup m).suzukiNorm = 1
  rw [standardRootParameter_norm, map_one]
  norm_num

private theorem standardStructureConjugatorParameter_inv (m : ℕ) :
    (standardStructureConjugatorParameter m)⁻¹ =
      (RootGroup.mk 1 0 : RootGroup m) := by
  ext
  · rfl
  · change (1 : Field m) + 1 * titsTwist m 1 = 0
    rw [map_one, one_mul, CharTwo.add_self_eq_zero]

/-- The standard root involution, Weyl involution, and right-root element
satisfy Peterfalvi's structure equation. -/
theorem standardSuzuki_structureEquation (m : ℕ) :
    weylElement m * standardRootInvolution m * weylElement m =
      (standardStructureConjugator m)⁻¹ * weylElement m *
        standardStructureConjugator m := by
  change
    weylElement m * rootHom m (RootGroup.mk 0 1) * weylElement m =
      (rootHom m (standardStructureConjugatorParameter m))⁻¹ *
        weylElement m *
          rootHom m (standardStructureConjugatorParameter m)
  rw [weylElement_mul_rootHom_mul_weylElement
      (RootGroup.mk 0 1) (standardRootParameter_ne_one m),
    standardRootParameter_weylAffine,
    standardRootParameter_bruhatTorus, map_one, mul_one,
    standardRootParameter_bruhatRightRoot, ← map_inv,
    standardStructureConjugatorParameter_inv]

/-! ## Normalizing the ambient image of `t` -/

private noncomputable def torusSquareRoot {m : ℕ} (c : TorusParameter m) :
    TorusParameter m :=
  Units.mk0 ((frobeniusEquiv (Field m) 2).symm (c : Field m)) (by
    intro h
    apply c.ne_zero
    have h' := congrArg (frobeniusEquiv (Field m) 2) h
    simp at h')

private theorem torusSquareRoot_sq {m : ℕ} (c : TorusParameter m) :
    torusSquareRoot c ^ 2 = c := by
  apply Units.ext
  change ((frobeniusEquiv (Field m) 2).symm (c : Field m)) ^ 2 =
    (c : Field m)
  exact frobeniusEquiv_symm_pow_p (Field m) 2 (c : Field m)

namespace Hypothesis

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
  [Finite G]

/-! ## Transporting the complete pair through a Suzuki target -/

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), Suzuki case.**
For a concrete standard Suzuki Theorem A target, the distinguished product
`s*t` has order five.

The proof retains the ambient Sylow conjugator.  Root and torus corrections
then put `Q` and `t` simultaneously into standard root/Weyl position;
the structure equation and uniqueness determine `s`. -/
theorem orderOf_distinguishedInvolution_mul_t_of_suzukiTarget
    (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : SuzukiInductionTarget (Omega := Omega) L) :
    orderOf (hyp.distinguishedInvolution * hyp.t) = 5 := by
  have hcore := hyp.Q_and_residual_of_suzuki_target L hLnormal hLodd
    data.m_pos data.groupEquiv data.actionEquiv
      data.actionEquiv_bijective
  obtain ⟨hQp, hQL, _, _⟩ := hcore
  let P : Sylow 2 G := Classical.choose (hyp.exists_sylow_two_eq_Q hQp)
  have hP : (P : Subgroup G) = hyp.Q :=
    Classical.choose_spec (hyp.exists_sylow_two_eq_Q hQp)
  have hPL : (P : Subgroup G) ≤ L := hP ▸ hQL
  let PL : Sylow 2 L := P.subtype hPL
  let Pbar : Sylow 2 (standardPermGroup data.m) :=
    Sylow.mapEquiv data.groupEquiv PL
  let g : standardPermGroup data.m :=
    Classical.choose (MulAction.exists_smul_eq _ Pbar
      (standardRootSylow data.m))
  have hg : g • Pbar = standardRootSylow data.m :=
    Classical.choose_spec (MulAction.exists_smul_eq _ Pbar
      (standardRootSylow data.m))
  let e0 : L ≃* standardPermGroup data.m :=
    data.groupEquiv.trans (MulAut.conj g)
  have hPLQ : (PL : Subgroup L) = hyp.Q.subgroupOf L := by
    dsimp only [PL]
    rw [Sylow.coe_subtype]
    ext x
    change (x : G) ∈ P ↔ (x : G) ∈ hyp.Q
    exact SetLike.ext_iff.mp hP (x : G)
  have hrootEq :
      (MulAut.conj g) •
          (Pbar : Subgroup (standardPermGroup data.m)) =
        standardRootSubgroup data.m := by
    rw [← Sylow.coe_subgroup_smul, hg, coe_standardRootSylow]
  have hmem0 (x : L) :
      e0 x ∈ standardRootSubgroup data.m ↔ (x : G) ∈ hyp.Q := by
    have hmap :
        data.groupEquiv x ∈
            (Pbar : Subgroup (standardPermGroup data.m)) ↔
          x ∈ PL := by
      dsimp only [Pbar]
      rw [Sylow.coe_mapEquiv, Subgroup.mem_map_equiv,
        data.groupEquiv.symm_apply_apply]
      change x ∈ (PL : Subgroup L) ↔ x ∈ (PL : Subgroup L)
      rfl
    constructor
    · intro hx
      change (MulAut.conj g) • data.groupEquiv x ∈
        standardRootSubgroup data.m at hx
      rw [← hrootEq, Subgroup.smul_mem_pointwise_smul_iff] at hx
      have hxPL : x ∈ PL := hmap.mp hx
      have hxQL : x ∈ hyp.Q.subgroupOf L :=
        (SetLike.ext_iff.mp hPLQ x).mp hxPL
      exact hxQL
    · intro hx
      change (MulAut.conj g) • data.groupEquiv x ∈
        standardRootSubgroup data.m
      rw [← hrootEq, Subgroup.smul_mem_pointwise_smul_iff]
      apply hmap.mpr
      apply (SetLike.ext_iff.mp hPLQ x).mpr
      exact hx
  have hsQ : hyp.distinguishedInvolution ∈ hyp.Q :=
    hyp.mem_Q_of_sq_eq_one_of_mem_H
      hyp.distinguishedInvolution_mem_H hyp.distinguishedInvolution_sq
  have hrQ : hyp.structureConjugator ∈ hyp.Q :=
    hyp.structureConjugator_mem_Q
  have hsL : hyp.distinguishedInvolution ∈ L := hQL hsQ
  have hrL : hyp.structureConjugator ∈ L := hQL hrQ
  have htLmem : hyp.t ∈ L := by
    obtain ⟨c, hc⟩ := isConj_iff.mp
      (hyp.isConj_of_involutions hyp.distinguishedInvolution_sq
        hyp.distinguishedInvolution_ne_one hyp.t_sq hyp.t_ne_one)
    rw [← hc]
    exact hLnormal.conj_mem hyp.distinguishedInvolution hsL c
  let sL : L := ⟨hyp.distinguishedInvolution, hsL⟩
  let rL : L := ⟨hyp.structureConjugator, hrL⟩
  let tL : L := ⟨hyp.t, htLmem⟩
  let z : standardPermGroup data.m := e0 tL
  have hz2 : z ^ 2 = 1 := by
    dsimp only [z]
    rw [← map_pow, show tL ^ 2 = 1 from Subtype.ext hyp.t_sq, map_one]
  have hforward :
      z ∈ standardBorel data.m →
        ∀ n : G, n ∈ hyp.Q → hyp.t * n * hyp.t⁻¹ ∈ hyp.Q := by
    intro hzB n hn
    let nL : L := ⟨n, hQL hn⟩
    have hnroot : e0 nL ∈ standardRootSubgroup data.m :=
      (hmem0 nL).2 hn
    have hconj :=
      standardBorel_conj_mem_standardRootSubgroup hzB hnroot
    apply (hmem0 (tL * nL * tL⁻¹)).1
    simpa only [map_mul, map_inv, z] using hconj
  have hz_not_fix :
      z • Ovoid.infinity data.m ≠ Ovoid.infinity data.m := by
    intro hzfix
    have hzB : z ∈ standardBorel data.m := by
      rw [standardBorel_eq_infinityStabilizer,
        MulAction.mem_stabilizer_iff]
      exact hzfix
    have htNorm : hyp.t ∈ Subgroup.normalizer (hyp.Q : Set G) := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro n
      constructor
      · exact hforward hzB n
      · intro hn
        have htwice :=
          hforward hzB (hyp.t * n * hyp.t⁻¹) hn
        have hcancel :
            hyp.t * (hyp.t * n * hyp.t⁻¹) * hyp.t⁻¹ = n := by
          rw [hyp.t_inv_eq]
          calc
            hyp.t * (hyp.t * n * hyp.t) * hyp.t =
                (hyp.t * hyp.t) * n * (hyp.t * hyp.t) := by group
            _ = n := by rw [hyp.t_mul_t, one_mul, mul_one]
        rw [hcancel] at htwice
        exact htwice
    rw [hyp.normalizer_Q_eq_H] at htNorm
    exact hyp.t_not_mem_H htNorm
  obtain ⟨u, hu⟩ : ∃ u : RootGroup data.m,
      z • Ovoid.infinity data.m = Ovoid.affine u := by
    rcases Ovoid.eq_infinity_or_eq_affine
        (z • Ovoid.infinity data.m) with h | h
    · exact (hz_not_fix h).elim
    · obtain ⟨u, hu⟩ := h
      exact ⟨u, hu⟩
  let a : standardPermGroup data.m := rootHom data.m u⁻¹
  let z1 : standardPermGroup data.m := (MulAut.conj a) z
  have hainf :
      (rootHom data.m u⁻¹)⁻¹ • Ovoid.infinity data.m =
        Ovoid.infinity data.m := by
    rw [← map_inv, rootHom_smul_infinity]
  have hz1inf :
      z1 • Ovoid.infinity data.m = Ovoid.origin data.m := by
    dsimp only [z1, a]
    change
      (rootHom data.m u⁻¹ * z * (rootHom data.m u⁻¹)⁻¹) •
        Ovoid.infinity data.m = Ovoid.origin data.m
    rw [mul_smul, mul_smul, hainf, hu,
      rootHom_smul_affine, inv_mul_cancel]
    rfl
  have hz1sq : z1 ^ 2 = 1 := by
    dsimp only [z1]
    rw [← map_pow, hz2, map_one]
  have hz1origin :
      z1 • Ovoid.origin data.m = Ovoid.infinity data.m := by
    have h := congrArg
      (fun q : standardPermGroup data.m =>
        q • Ovoid.infinity data.m) hz1sq
    simpa only [pow_two, mul_smul, hz1inf, one_smul] using h
  let h : standardPermGroup data.m := z1 * weylElement data.m
  have hfixInf : h • Ovoid.infinity data.m = Ovoid.infinity data.m := by
    dsimp only [h]
    rw [mul_smul, weylElement_smul_infinity, hz1origin]
  have hfixOrigin : h • Ovoid.origin data.m = Ovoid.origin data.m := by
    dsimp only [h]
    rw [mul_smul, weylElement_smul_origin, hz1inf]
  have hB : h ∈ standardBorel data.m := by
    rw [standardBorel_eq_infinityStabilizer,
      MulAction.mem_stabilizer_iff]
    exact hfixInf
  obtain ⟨p, hp, -⟩ :=
    (mem_standardBorel_iff_existsUnique_root_torus h).mp hB
  have hpLeft : p.1 = 1 := by
    apply Ovoid.affine_injective
    simpa only [hp, borelHom_apply, mul_smul, Ovoid.origin,
      torusHom_smul_affine, map_one, rootHom_smul_affine, mul_one]
      using hfixOrigin
  let c : TorusParameter data.m := p.2
  have hh : h = torusHom data.m c := by
    rw [hp, hpLeft, map_one, one_mul]
  have hz1form :
      z1 = torusHom data.m c * weylElement data.m := by
    calc
      z1 = (z1 * weylElement data.m) * weylElement data.m := by
        rw [mul_assoc, ← pow_two, weylElement_sq_eq_one, mul_one]
      _ = torusHom data.m c * weylElement data.m := by
        change h * weylElement data.m =
          torusHom data.m c * weylElement data.m
        rw [hh]
  let d : TorusParameter data.m := torusSquareRoot c⁻¹
  have hd2 : d ^ 2 = c⁻¹ := torusSquareRoot_sq c⁻¹
  have hdcd : d * c * d = 1 := by
    calc
      d * c * d = d ^ 2 * c := by
        rw [pow_two]
        ac_rfl
      _ = c⁻¹ * c := by rw [hd2]
      _ = 1 := inv_mul_cancel c
  have hnormalize :
      (MulAut.conj (torusHom data.m d)) z1 =
        weylElement data.m := by
    have hww : weylElement data.m * weylElement data.m = 1 := by
      simpa only [pow_two] using weylElement_sq_eq_one data.m
    change
      torusHom data.m d * z1 * (torusHom data.m d)⁻¹ =
        weylElement data.m
    rw [hz1form]
    calc
      torusHom data.m d *
            (torusHom data.m c * weylElement data.m) *
            (torusHom data.m d)⁻¹ =
          torusHom data.m d * torusHom data.m c *
            weylElement data.m * (torusHom data.m d)⁻¹ *
              (weylElement data.m * weylElement data.m) := by
        rw [hww, mul_one]
        group
      _ = torusHom data.m d * torusHom data.m c *
            (weylElement data.m * (torusHom data.m d)⁻¹ *
              weylElement data.m) * weylElement data.m := by group
      _ = torusHom data.m d * torusHom data.m c *
            torusHom data.m d * weylElement data.m := by
        rw [← map_inv,
          weylElement_mul_torusHom_mul_weylElement, inv_inv]
      _ = torusHom data.m (d * c * d) * weylElement data.m := by
        rw [map_mul, map_mul]
      _ = weylElement data.m := by rw [hdcd, map_one, one_mul]
  let e1 : L ≃* standardPermGroup data.m := e0.trans (MulAut.conj a)
  let e : L ≃* standardPermGroup data.m :=
    e1.trans (MulAut.conj (torusHom data.m d))
  have hmem (x : L) :
      e x ∈ standardRootSubgroup data.m ↔ (x : G) ∈ hyp.Q := by
    change
      torusHom data.m d *
            (rootHom data.m u⁻¹ * e0 x * (rootHom data.m u⁻¹)⁻¹) *
            (torusHom data.m d)⁻¹ ∈ standardRootSubgroup data.m ↔
        (x : G) ∈ hyp.Q
    rw [torusHom_conj_mem_standardRootSubgroup_iff,
      rootHom_conj_mem_standardRootSubgroup_iff]
    exact hmem0 x
  have het : e tL = weylElement data.m := by
    change (MulAut.conj (torusHom data.m d))
      ((MulAut.conj a) (e0 tL)) = weylElement data.m
    exact hnormalize
  let s0L : L := e.symm (standardRootInvolution data.m)
  let r0L : L := e.symm (standardStructureConjugator data.m)
  have hs0Q : (s0L : G) ∈ hyp.Q := by
    apply (hmem s0L).1
    dsimp only [s0L]
    rw [e.apply_symm_apply]
    exact standardRootInvolution_mem_standardRootSubgroup data.m
  have hr0Q : (r0L : G) ∈ hyp.Q := by
    apply (hmem r0L).1
    dsimp only [r0L]
    rw [e.apply_symm_apply]
    exact standardStructureConjugator_mem_standardRootSubgroup data.m
  have hs0H : (s0L : G) ∈ hyp.H := hyp.Q_le_H hs0Q
  have hs0sqL : s0L ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    dsimp only [s0L]
    rw [e.apply_symm_apply]
    exact standardRootInvolution_sq data.m
  have hs0sq : (s0L : G) ^ 2 = 1 :=
    congrArg (fun x : L => (x : G)) hs0sqL
  have hs0ne : (s0L : G) ≠ 1 := by
    intro hs
    apply standardRootInvolution_ne_one data.m
    have hsL : s0L = 1 := Subtype.ext hs
    have hmap := congrArg e hsL
    dsimp only [s0L] at hmap
    rw [e.apply_symm_apply, map_one] at hmap
    exact hmap
  have hstructureL :
      tL * s0L * tL = r0L⁻¹ * tL * r0L := by
    apply e.injective
    simp only [map_mul, map_inv]
    dsimp only [s0L, r0L]
    rw [e.apply_symm_apply, e.apply_symm_apply, het]
    exact standardSuzuki_structureEquation data.m
  have hstructure :
      hyp.t * (s0L : G) * hyp.t =
        (r0L : G)⁻¹ * hyp.t * (r0L : G) :=
    congrArg (fun x : L => (x : G)) hstructureL
  have hpair := hyp.eq_distinguishedPair_of_structure
    hs0H hs0sq hs0ne hr0Q hstructure
  have hsLs0 : sL = s0L := Subtype.ext hpair.1.symm
  have hes : e sL = standardRootInvolution data.m := by
    rw [hsLs0]
    exact e.apply_symm_apply _
  have htarget :
      orderOf (e sL * e tL) = 5 := by
    rw [hes, het]
    exact orderOf_standardRootInvolution_mul_weylElement data.m
  have hLorder : orderOf (sL * tL) = 5 := by
    rw [← orderOf_injective e.toMonoidHom e.injective]
    change orderOf (e (sL * tL)) = 5
    rw [map_mul]
    exact htarget
  calc
    orderOf (hyp.distinguishedInvolution * hyp.t) =
        orderOf (sL * tL) :=
      orderOf_injective L.subtype L.subtype_injective (sL * tL)
    _ = 5 := hLorder

/-! ## The faithful centralizer quotient -/

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), Suzuki case.**
In the Suzuki branch of the induction conclusion for
`C_G(X)/N(C_G(X))`, the original distinguished product `s*t` has order
five.  The standard action proves the fifth-power relation in the faithful
quotient, and the odd-kernel lemma lifts it back to `G`. -/
theorem orderOf_distinguishedInvolution_mul_t_of_centralizer_suzukiTarget
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
      SuzukiInductionTarget (Omega := ↥(MulAction.fixedPoints X Omega))
        result.L) :
    orderOf (hyp.distinguishedInvolution * hyp.t) = 5 := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  have hquotOrder :
      orderOf (qhyp.distinguishedInvolution * qhyp.t) = 5 :=
    qhyp.orderOf_distinguishedInvolution_mul_t_of_suzukiTarget
      result.L result.normal result.oddIndex data
  have hquotPow :
      (qhyp.distinguishedInvolution * qhyp.t) ^ 5 = 1 := by
    rw [← hquotOrder]
    exact pow_orderOf_eq_one _
  exact hyp.orderOf_distinguishedInvolution_mul_t_of_quotient_pow
    hXV hA3 Nat.prime_five hquotPow

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
