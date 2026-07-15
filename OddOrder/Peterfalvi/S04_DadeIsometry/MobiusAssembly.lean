/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S04_InduceConjFinset

/-!
# Peterfalvi §4: Möbius orbit-averaging for the Dade isometry

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§4, pp. 10-14.

This leaf proves the orbit-averaging and Möbius-summand identities used in formula (2.10), ending
with the support-side transversal sum needed by the explicit Dade-map construction.
-/
namespace OddOrder.Peterfalvi.S04
open OddOrder.RepresentationTheory
open scoped Pointwise

variable {G : Type*} [Group G]

namespace Hypothesis
variable {A A₁ : Set G} {L : Subgroup G}

variable [Fintype G]

section SemidirectStructure
section MobiusAssembly
open scoped Classical

variable (hyp : Hypothesis G A L)


/-! #### STEP 3a: orbit-averaging the transversal sum to the powerset

The (2.10) right-hand side is a sum over the `L`-conjugacy transversal `ℬ` of an orbit-constant
summand.  We convert it to a sum over the full powerset weighted by `1/|orbit B|`. -/

/-- The conjugation orbit of `B` is contained in `A`-subsets of the same cardinality, so it is
finite; `Nat.card (orbit B) > 0`. -/
theorem card_orbit_pos (B : Finset {a : G // a ∈ A}) :
    letI := hyp.conjFinsetAction
    0 < Nat.card (MulAction.orbit L B) := by
  letI := hyp.conjFinsetAction
  letI : Finite (MulAction.orbit L B) := Set.finite_coe_iff.mpr (Set.toFinite _)
  letI : Nonempty (MulAction.orbit L B) := ⟨⟨B, MulAction.mem_orbit_self B⟩⟩
  exact Nat.card_pos

/-- **Peterfalvi (2.10), orbit-averaging.**  For any `ℂ`-valued `h` constant on `L`-conjugacy orbits
of subsets (`h (B^l) = h B`), the transversal sum equals the powerset sum weighted by inverse orbit
size:

    `∑_{C ∈ ℬ} h(rep C) = ∑_{B ⊆ A} h(B) / |orbit B|`.

Each orbit `O` contributes `∑_{B ∈ O} h(B)/|orbit B| = |O| · h(rep)/|O| = h(rep)` (the numerator is
orbit-constant and `|orbit B| = |O|` throughout `O`); partitioning the powerset sum into orbit fibers
(`Finset.sum_fiberwise_of_maps_to` along `Quotient.mk''`) collapses it to the transversal sum.  This
realizes the `1/|L:N_L(B)|` weight of (2.10) (`card_orbit_mul_card_setLStabilizer`). -/
theorem sum_transversalRep_eq_sum_div_orbit
    (h : Finset {a : G // a ∈ A} → ℂ)
    (hinv : ∀ (l : L) (B : Finset {a : G // a ∈ A}), h (hyp.conjFinset l B) = h B) :
    letI := hyp.conjFinsetAction
    letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
    letI : Fintype (Finset {a : G // a ∈ A}) := Fintype.ofFinite _
    ∑ C : hyp.conjClassQuotient, h (hyp.transversalRep C)
      = ∑ B : Finset {a : G // a ∈ A},
          h B / (Nat.card (MulAction.orbit L B) : ℂ) := by
  classical
  letI := hyp.conjFinsetAction
  letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
  letI : Fintype (Finset {a : G // a ∈ A}) := Fintype.ofFinite _
  -- `h` and `Nat.card (orbit ·)` are constant along orbits.
  have horbit_const : ∀ B : Finset {a : G // a ∈ A}, ∀ B' ∈ MulAction.orbit L B,
      h B' = h B := by
    rintro B B' ⟨l, rfl⟩
    exact hinv l B
  have hcard_const : ∀ B : Finset {a : G // a ∈ A}, ∀ B' ∈ MulAction.orbit L B,
      MulAction.orbit L B' = MulAction.orbit L B := by
    rintro B B' hB'
    exact (MulAction.orbit_eq_iff.mpr hB')
  -- partition the powerset sum into orbit fibers along `Quotient.mk''`.
  rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun B => (Quotient.mk'' B : hyp.conjClassQuotient))
      (s := Finset.univ) (t := Finset.univ)
      (fun B _ => Finset.mem_univ _)
      (f := fun B => h B / (Nat.card (MulAction.orbit L B) : ℂ))]
  refine Finset.sum_congr (by congr 1; exact Subsingleton.elim _ _) fun C _ => ?_
  -- evaluate the fiber over `C`: it is the orbit of `out C = transversalRep C`.
  set B₀ := hyp.transversalRep C with hB₀
  -- the fiber `{B | ⟦B⟧ = C}` as a Finset; on it the summand is the constant `h B₀ / |orbit B₀|`.
  have hfiber_eq : ((Finset.univ : Finset (Finset {a : G // a ∈ A})).filter
        (fun B => (Quotient.mk'' B : hyp.conjClassQuotient) = C))
      = (MulAction.orbit L B₀).toFinset := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    rw [hB₀, transversalRep]
    constructor
    · intro hB
      rw [MulAction.mem_orbit_iff]
      have : (Quotient.mk'' B : hyp.conjClassQuotient)
          = Quotient.mk'' (Quotient.out (s := MulAction.orbitRel L (Finset {a : G // a ∈ A})) C) := by
        rw [hB, Quotient.out_eq']
      exact Quotient.exact' this
    · intro hB
      have : (Quotient.mk'' B : hyp.conjClassQuotient)
          = Quotient.mk'' (Quotient.out (s := MulAction.orbitRel L (Finset {a : G // a ∈ A})) C) :=
        Quotient.sound' (by rwa [MulAction.mem_orbit_iff] at hB)
      rw [this, Quotient.out_eq']
  rw [hfiber_eq]
  -- on the orbit, the summand is constant `= h B₀ / |orbit B₀|`; there are `|orbit B₀|` terms.
  have hconst : ∀ B ∈ (MulAction.orbit L B₀).toFinset,
      h B / (Nat.card (MulAction.orbit L B) : ℂ) = h B₀ / (Nat.card (MulAction.orbit L B₀) : ℂ) := by
    intro B hB
    rw [Set.mem_toFinset] at hB
    rw [horbit_const B₀ B hB, hcard_const B₀ B hB]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  -- `|orbit B₀| · (h B₀ / |orbit B₀|) = h B₀`.
  have hcardpos : 0 < Nat.card (MulAction.orbit L B₀) := hyp.card_orbit_pos B₀
  have hcard_eq : ((MulAction.orbit L B₀).toFinset.card : ℂ)
      = (Nat.card (MulAction.orbit L B₀) : ℂ) := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
  rw [hcard_eq]
  rw [mul_div_assoc']
  rw [mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.mpr hcardpos.ne'

/-- `|H(B^l)| = |H(B)|`: conjugation by `l` is a cardinality-preserving bijection of subgroups. -/
theorem card_hIntersection_conjFinset (hconj : hyp.HConjInvariant) (l : L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    Nat.card (hIntersection hyp (hyp.conjFinset l B) (hyp.conjFinset_nonempty (l := l) hB))
      = Nat.card (hIntersection hyp B hB) := by
  rw [hyp.hIntersection_conjFinset hconj l hB]
  refine Nat.card_congr ?_
  have hsmul : ∀ z : G, ((MulAut.conj (l : G))⁻¹ • z) = (l : G)⁻¹ * z * (l : G) := by
    intro z
    rw [show ((MulAut.conj (l : G))⁻¹ • z) = (MulAut.conj (l : G))⁻¹ z from rfl,
      MulAut.conj_inv_apply]
  refine
    { toFun := fun x => ⟨(l : G)⁻¹ * (x : G) * (l : G), ?_⟩
      invFun := fun y => ⟨(l : G) * (y : G) * (l : G)⁻¹, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun y => ?_ }
  · -- `x ∈ conj•H(B) ⟹ l⁻¹·x·l ∈ H(B)`
    have hx := x.2
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hsmul] at hx
    exact hx
  · -- `y ∈ H(B) ⟹ l·y·l⁻¹ ∈ conj•H(B)`
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hsmul]
    rw [show (l : G)⁻¹ * ((l : G) * (y : G) * (l : G)⁻¹) * (l : G) = (y : G) from by group]
    exact y.2
  · apply Subtype.ext; show (l : G) * ((l : G)⁻¹ * (x : G) * (l : G)) * (l : G)⁻¹ = (x : G); group
  · apply Subtype.ext; show (l : G)⁻¹ * ((l : G) * (y : G) * (l : G)⁻¹) * (l : G) = (y : G); group

/-- The conjugation orbit element `a^l` lies in `N_L(B^l)` iff `a` lies in `N_L(B)`. -/
theorem mem_nLStabilizerIn_conjA_conjFinset (l : L)
    {a : {a : G // a ∈ A}} {B : Finset {a : G // a ∈ A}} :
    (hyp.conjA l a : G) ∈ nLStabilizerIn hyp (hyp.conjFinset l B)
      ↔ (a : G) ∈ nLStabilizerIn hyp B := by
  rw [hyp.nLStabilizerIn_conjFinset l, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rw [show ((MulAut.conj (l : G))⁻¹ • (hyp.conjA l a : G)) = (l : G)⁻¹ * (hyp.conjA l a : G)
      * (l : G) from by
    rw [show ((MulAut.conj (l : G))⁻¹ • (hyp.conjA l a : G))
        = (MulAut.conj (l : G))⁻¹ (hyp.conjA l a : G) from rfl, MulAut.conj_inv_apply]]
  rw [show (l : G)⁻¹ * (hyp.conjA l a : G) * (l : G) = (a : G) from by
    simp only [conjA_coe]; group]

/-- Conjugation `B ↦ B^l` sends `𝒫(a)` bijectively to `𝒫(a^l)`. -/
theorem mem_mobiusIndex_conjFinset (l : L)
    {a : {a : G // a ∈ A}} {B : Finset {a : G // a ∈ A}} :
    hyp.conjFinset l B ∈ hyp.mobiusIndex (hyp.conjA l a) ↔ B ∈ hyp.mobiusIndex a := by
  classical
  rw [hyp.mem_mobiusIndex, hyp.mem_mobiusIndex, conjFinset,
    Finset.image_nonempty, ← conjFinset, hyp.mem_nLStabilizerIn_conjA_conjFinset l]

/-- **Peterfalvi (2.10), conjugation-invariance of the `mobiusSummand`.**  For `l ∈ L`,

    `mobiusSummand (a^l) g (B^l) = mobiusSummand a g B`.

`|B^l| = |B|`, `H(B^l) = l·H(B)·l⁻¹` has the same cardinality, and the conjugating set
`|𝒜(g, H(B^l)·a^l)| = |𝒜(g, l·(H(B)·a)·l⁻¹)| = |𝒜(g, H(B)·a)|` by `card_conjFiber_conj_eq`. -/
theorem mobiusSummand_conjFinset (hconj : hyp.HConjInvariant) (l : L) (g : G)
    (a : {a : G // a ∈ A}) (B : Finset {a : G // a ∈ A}) :
    hyp.mobiusSummand (hyp.conjA l a) g (hyp.conjFinset l B)
      = hyp.mobiusSummand a g B := by
  classical
  by_cases hB : B.Nonempty
  · have hBl : (hyp.conjFinset l B).Nonempty := hyp.conjFinset_nonempty (l := l) hB
    rw [hyp.mobiusSummand_of_nonempty _ g hBl, hyp.mobiusSummand_of_nonempty a g hB]
    rw [hyp.conjFinset_card, hyp.card_hIntersection_conjFinset hconj l hB]
    -- only the conjugating-set cardinality remains
    congr 2
    -- `|𝒜(g, H(B^l)·a^l)| = |𝒜(g, H(B)·a)|`
    have hset : (↑(hIntersection hyp (hyp.conjFinset l B) hBl) : Set G)
          * ({(hyp.conjA l a : G)} : Set G)
        = (fun z => (l : G) * z * (l : G)⁻¹) ''
            ((↑(hIntersection hyp B hB) : Set G) * ({(a : G)} : Set G)) := by
      rw [hyp.hIntersection_conjFinset hconj l hB]
      have hsmul : ∀ z : G, ((MulAut.conj (l : G))⁻¹ • z) = (l : G)⁻¹ * z * (l : G) := by
        intro z
        rw [show ((MulAut.conj (l : G))⁻¹ • z) = (MulAut.conj (l : G))⁻¹ z from rfl,
          MulAut.conj_inv_apply]
      ext y
      simp only [Set.mem_mul, Set.mem_image, Set.mem_singleton_iff, conjA_coe,
        SetLike.mem_coe]
      constructor
      · rintro ⟨p, hp, q, rfl, rfl⟩
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hsmul] at hp
        refine ⟨(l : G)⁻¹ * p * (l : G) * (a : G),
          ⟨(l : G)⁻¹ * p * (l : G), hp, a, rfl, rfl⟩, by group⟩
      · rintro ⟨z, ⟨p, hp, q, rfl, rfl⟩, rfl⟩
        refine ⟨(l : G) * p * (l : G)⁻¹, ?_, (l : G) * (a : G) * (l : G)⁻¹, rfl, by group⟩
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hsmul,
          show (l : G)⁻¹ * ((l : G) * p * (l : G)⁻¹) * (l : G) = p from by group]
        exact hp
    rw [hset, card_conjFiber_conj_eq]
  · have hBe : ¬ (hyp.conjFinset l B).Nonempty := by
      rw [conjFinset, Finset.image_nonempty]; exact hB
    simp only [mobiusSummand, dif_neg hBe, dif_neg hB]

/-- **Peterfalvi (2.10), the `𝒫(b)`-sum is `L`-conjugation invariant.**  For `l ∈ L`,

    `∑_{B ∈ 𝒫(a^l)} mobiusSummand (a^l) g B = ∑_{B₀ ∈ 𝒫(a)} mobiusSummand a g B₀`.

The bijection `B₀ ↦ B₀^l` carries `𝒫(a)` to `𝒫(a^l)` (`mem_mobiusIndex_conjFinset`) and preserves
the summand (`mobiusSummand_conjFinset`).  This is the `b = a^x` reindex of (2.10) (lines making the
inner `𝒫(b)`-sum independent of `b ∈ a^L`). -/
theorem sum_mobiusSummand_conjFinset (hconj : hyp.HConjInvariant) (l : L) (g : G)
    (a : {a : G // a ∈ A}) :
    ∑ B ∈ hyp.mobiusIndex (hyp.conjA l a), hyp.mobiusSummand (hyp.conjA l a) g B
      = ∑ B₀ ∈ hyp.mobiusIndex a, hyp.mobiusSummand a g B₀ := by
  classical
  refine Finset.sum_bij' (fun B _ => hyp.conjFinset l⁻¹ B) (fun B₀ _ => hyp.conjFinset l B₀)
    ?_ ?_ ?_ ?_ ?_
  · -- `i : 𝒫(a^l) → 𝒫(a)`
    intro B hB
    have hmem := (hyp.mem_mobiusIndex_conjFinset l⁻¹ (a := hyp.conjA l a) (B := B)).mpr
    rw [conjA_inv_conjA] at hmem
    exact hmem hB
  · -- `j : 𝒫(a) → 𝒫(a^l)`
    intro B₀ hB₀
    exact (hyp.mem_mobiusIndex_conjFinset l (a := a) (B := B₀)).mpr hB₀
  · intro B _
    show hyp.conjFinset l (hyp.conjFinset l⁻¹ B) = B
    rw [← hyp.conjFinset_mul, mul_inv_cancel, hyp.conjFinset_one]
  · intro B₀ _
    show hyp.conjFinset l⁻¹ (hyp.conjFinset l B₀) = B₀
    rw [← hyp.conjFinset_mul, inv_mul_cancel, hyp.conjFinset_one]
  · -- summand agrees: `mobiusSummand (a^l) g B = mobiusSummand a g (B^{l⁻¹})`
    intro B hB
    show hyp.mobiusSummand (hyp.conjA l a) g B
      = hyp.mobiusSummand a g (hyp.conjFinset l⁻¹ B)
    have := hyp.mobiusSummand_conjFinset hconj l⁻¹ g (hyp.conjA l a) B
    rw [conjA_inv_conjA] at this
    exact this.symm

/-- `|N_L(B)| = |setLStabilizer B|`: `N_L(B) = setLStabilizer.map L.subtype` along the injection
`L ↪ G`, so the two cardinalities agree. -/
theorem card_nLStabilizerIn_eq (B : Finset {a : G // a ∈ A}) :
    Nat.card (nLStabilizerIn hyp B) = Nat.card (setLStabilizer hyp B) := by
  rw [nLStabilizerIn]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).symm.toEquiv

/-- The packaged summand `induceAlphaBTerm` evaluated at `g` equals the bare induced value,
independent of the carried invertibility instance (`Invertible.subsingleton`). -/
theorem induceAlphaBTerm_apply (hconj : hyp.HConjInvariant) (α : ClassFunction L ℂ)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    [inst : Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] (g : G) :
    hyp.induceAlphaBTerm hconj α ⟨B, hB⟩ g
      = ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hconj hB α) g := by
  have h : inst = invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne') :=
    Subsingleton.elim _ _
  rw [induceAlphaBTerm, h]

/-- **Peterfalvi (2.10), per-`B` weight simplification.**  For nonempty `B` and `g ∈ (aH(a))^G`, the
orbit-averaged inclusion–exclusion summand collapses, using `|orbit B|·|N_L(B)| = |L|`
(`card_orbit_mul_card_setLStabilizer`) and `|M(B)| = |H(B)|·|N_L(B)|` (`card_mBSubgroup`):

    `(-1)^{|B|}/|orbit B| · (Ind_{M(B)} α_B)(g)
      = (α(a)/|L|) · ∑_{b ∈ N_L(B) ∩ a^L} (-1)^{|B|}/|H(B)| · |𝒜(g, H(B)·b)|`.

The factor `1/(|orbit B|·|M(B)|) = 1/(|orbit B|·|H(B)|·|N_L(B)|) = 1/(|L|·|H(B)|)`. -/
theorem mobiusSummand_orbit_weighted (hconj : hyp.HConjInvariant)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)]
    {a : {a : G // a ∈ A}} {h g : G} (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g) :
    letI := hyp.conjFinsetAction
    ((-1 : ℂ) ^ B.card / (Nat.card (MulAction.orbit L B) : ℂ))
        * hyp.induceAlphaBTerm hconj (α : ClassFunction L ℂ) ⟨B, hB⟩ g
      = ((α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩ / (Nat.card L : ℂ))
          * ∑ b ∈ (Finset.univ : Finset (nLStabilizerIn hyp B)).filter
              (fun b : (nLStabilizerIn hyp B) =>
                ∃ l : L, (l : G) * a.1 * (l : G)⁻¹ = (b : G)),
            ((-1 : ℂ) ^ B.card / (Nat.card (hIntersection hyp B hB) : ℂ)) *
              ((conjFiber g ((↑(hIntersection hyp B hB) : Set G)
                * ({(b : G)} : Set G))).card : ℂ) := by
  classical
  letI := hyp.conjFinsetAction
  rw [hyp.induceAlphaBTerm_apply hconj _ hB g,
    hyp.induce_alphaB_apply_eq_alpha_mul_sum_conjL hconj hB α hh hga]
  -- abbreviations
  set p : ℂ := (-1 : ℂ) ^ B.card with hp
  set αa : ℂ := (α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩ with hαa
  set Hc : ℂ := (Nat.card (hIntersection hyp B hB) : ℂ) with hHc
  set Nc : ℂ := (Nat.card (nLStabilizerIn hyp B) : ℂ) with hNc
  set Oc : ℂ := (Nat.card (MulAction.orbit L B) : ℂ) with hOc
  -- `|M(B)| = |H(B)|·|N_L(B)|` and `|orbit B|·|N_L(B)| = |L|`.
  have hM : (Nat.card (mBSubgroup hyp B hB) : ℂ) = Hc * Nc := by
    rw [hHc, hNc]; exact_mod_cast hyp.card_mBSubgroup hconj hB
  have hON : Oc * Nc = (Nat.card L : ℂ) := by
    rw [hOc, hNc, hyp.card_nLStabilizerIn_eq B]
    exact_mod_cast hyp.card_orbit_mul_card_setLStabilizer B
  have hHne : Hc ≠ 0 := by rw [hHc]; exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hNne : Nc ≠ 0 := by rw [hNc]; exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hOne : Oc ≠ 0 := by rw [hOc]; exact Nat.cast_ne_zero.mpr (hyp.card_orbit_pos B).ne'
  -- name the inner sum `S = ∑_b |𝒜(g, H(B)b)|`.
  set S : ℂ := ∑ b ∈ (Finset.univ : Finset (nLStabilizerIn hyp B)).filter
      (fun b : (nLStabilizerIn hyp B) => ∃ l : L, (l : G) * a.1 * (l : G)⁻¹ = (b : G)),
      ((conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(b : G)} : Set G))).card : ℂ)
      with hS
  -- expand `⅟|M(B)|` and pull the per-term scalar `p/Hc` out of the RHS sum.
  rw [show (⅟(Nat.card (mBSubgroup hyp B hB) : ℂ)) = (Hc * Nc)⁻¹ from by
    rw [invOf_eq_inv, hM]]
  rw [show (∑ b ∈ (Finset.univ : Finset (nLStabilizerIn hyp B)).filter
        (fun b : (nLStabilizerIn hyp B) => ∃ l : L, (l : G) * a.1 * (l : G)⁻¹ = (b : G)),
        (p / Hc) * ((conjFiber g ((↑(hIntersection hyp B hB) : Set G)
          * ({(b : G)} : Set G))).card : ℂ)) = (p / Hc) * S from by
    rw [hS, Finset.mul_sum]]
  -- now both sides are scalar multiples of `S`; equate scalars using `Oc·Nc = |L|`.
  rw [← hON]
  field_simp

/-! #### Final assembly: the (2.10) pointwise identity and `FullDadeIsometryData`

The remaining work assembles the per-`B` weight identity `mobiusSummand_orbit_weighted` into the
(2.10) pointwise identity `α^τ(g) = -∑_{C ∈ ℬ} (-1)^{|rep C|} Ind_{M(rep C)} α_{rep C}(g)`, by
(a) orbit-averaging the transversal sum to the powerset, (b) recognizing the inner RHS term as
`mobiusSummand b g B`, (c) swapping the resulting double sum to sum over `b ∈ a^L` first, (d)
collapsing each inner `𝒫(b)`-sum to its survivor `mobiusSummand b g {b} = -|C_L(b)|`, and (e)
totalling `∑_{b ∈ a^L} |C_L(b)| = |L|` (`sum_card_centralizerIn_eq`). -/

/-- The orbit-averaging summand `(-1)^{|B|} · Ind_{M(B)} α_B(g)` (and `0` if `B` is empty),
packaged so `sum_transversalRep_eq_sum_div_orbit` applies. -/
noncomputable def mobiusTermCF (hconj : hyp.HConjInvariant) (α : ClassFunction L ℂ)
    (g : G) (B : Finset {a : G // a ∈ A}) : ℂ := by
  classical
  exact if hB : B.Nonempty then
      (-1 : ℂ) ^ B.card * hyp.induceAlphaBTerm hconj α ⟨B, hB⟩ g
    else 0

theorem mobiusTermCF_of_nonempty (hconj : hyp.HConjInvariant) (α : ClassFunction L ℂ)
    (g : G) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    hyp.mobiusTermCF hconj α g B
      = (-1 : ℂ) ^ B.card * hyp.induceAlphaBTerm hconj α ⟨B, hB⟩ g := by
  rw [mobiusTermCF, dif_pos hB]

theorem mobiusTermCF_of_not_nonempty (hconj : hyp.HConjInvariant) (α : ClassFunction L ℂ)
    (g : G) {B : Finset {a : G // a ∈ A}} (hB : ¬ B.Nonempty) :
    hyp.mobiusTermCF hconj α g B = 0 := by
  rw [mobiusTermCF, dif_neg hB]

/-- The orbit-averaging summand is `L`-conjugacy invariant: `mobiusTermCF (B^l) = mobiusTermCF B`.
Uses `conjFinset_card` (the sign `(-1)^{|B|}` is `L`-invariant) and `induceAlphaBTerm_conjFinset`
(the packaged induced summand is invariant). -/
theorem mobiusTermCF_conjFinset (hconj : hyp.HConjInvariant) (α : ClassFunction L ℂ)
    (g : G) (l : L) (B : Finset {a : G // a ∈ A}) :
    hyp.mobiusTermCF hconj α g (hyp.conjFinset l B) = hyp.mobiusTermCF hconj α g B := by
  classical
  by_cases hB : B.Nonempty
  · have hBl : (hyp.conjFinset l B).Nonempty := hyp.conjFinset_nonempty (l := l) hB
    rw [hyp.mobiusTermCF_of_nonempty hconj α g hBl, hyp.mobiusTermCF_of_nonempty hconj α g hB,
      hyp.conjFinset_card l B, hyp.induceAlphaBTerm_conjFinset hconj α l hB]
  · have hBe : ¬ (hyp.conjFinset l B).Nonempty := by
      rw [conjFinset, Finset.image_nonempty]; exact hB
    rw [mobiusTermCF, mobiusTermCF, dif_neg hBe, dif_neg hB]

/-- The `L`-orbit of the support representative `a`, as a `Finset {a : G // a ∈ A}`: the elements
`b' ∈ A` with `b' = l·a·l⁻¹` for some `l ∈ L`.  This is the fixed (`B`-independent) index over which
the inner `b`-sum of (2.10) ranges; it coincides with the support filter `Sg` of
`sum_card_centralizerIn_eq` when `g ∈ (aH(a))^G` (`mem_aOrbitFinset_iff_mem_supportFilter`). -/
noncomputable def aOrbitFinset (a : {a : G // a ∈ A}) : Finset {a : G // a ∈ A} := by
  classical
  letI : Fintype {a : G // a ∈ A} := Fintype.ofFinite _
  exact Finset.univ.filter (fun b => ∃ l : L, hyp.conjA l a = b)

theorem mem_aOrbitFinset {a b : {a : G // a ∈ A}} :
    b ∈ hyp.aOrbitFinset a ↔ ∃ l : L, hyp.conjA l a = b := by
  classical
  letI : Fintype {a : G // a ∈ A} := Fintype.ofFinite _
  simp only [aOrbitFinset, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Peterfalvi (2.10), per-`B` weight identity, inner sum over the fixed index `a^L`.**  For
`g ∈ (aH(a))^G`,

    `mobiusTermCF B / |orbit B| =
       (α(a)/|L|) · ∑_{b' ∈ a^L} (if b' ∈ N_L(B) then mobiusSummand b' g B else 0)`.

Recasting `mobiusSummand_orbit_weighted` so the inner sum ranges over the **`B`-independent** Finset
`aOrbitFinset a` (with an `if (b':G) ∈ N_L(B)` guard) instead of the `B`-dependent subtype
`N_L(B)`; this fixed index is what makes the subsequent `Finset.sum_comm` double-sum swap go
through.  The reindexing bijection sends `b : N_L(B)` with `b ∈ a^L` to `⟨b.val, _⟩ : {a // a ∈ A}`
(in `a^L ⊆ A`), and the term `(-1)^{|B|}/|H(B)| · |𝒜(g, H(B)·b)|` is `mobiusSummand b' g B`. -/
theorem mobiusTermCF_div_orbit_eq (hconj : hyp.HConjInvariant)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    {a : {a : G // a ∈ A}} {h g : G} (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g) :
    letI := hyp.conjFinsetAction
    hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g B / (Nat.card (MulAction.orbit L B) : ℂ)
      = ((α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩ / (Nat.card L : ℂ))
          * ∑ b' ∈ hyp.aOrbitFinset a,
            (if (b' : G) ∈ nLStabilizerIn hyp B then hyp.mobiusSummand b' g B else 0) := by
  classical
  letI := hyp.conjFinsetAction
  letI : Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- start from the orbit-weight identity, which sums over `b : N_L(B)` with `b ∈ a^L`.
  rw [hyp.mobiusTermCF_of_nonempty hconj _ g hB, mul_div_right_comm,
    hyp.mobiusSummand_orbit_weighted hconj α hB hh hga]
  congr 1
  -- reindex the `N_L(B)`-subtype sum to the fixed `aOrbitFinset` sum.
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
      (i := fun b hb => (⟨(b : G), by
        rw [Finset.mem_filter] at hb
        obtain ⟨l, hl⟩ := hb.2
        exact hl ▸ hyp.L_normalizes_A l a.2⟩ : {a : G // a ∈ A}))
      (j := fun b' hb' => (⟨(b' : G), by
        rw [Finset.mem_filter] at hb'
        exact hb'.2⟩ : nLStabilizerIn hyp B))
      ?_ ?_ ?_ ?_ ?_
  · -- `i b ∈ aOrbitFinset a` with `(i b : G) ∈ N_L(B)`
    intro b hb
    rw [Finset.mem_filter] at hb ⊢
    obtain ⟨l, hl⟩ := hb.2
    refine ⟨hyp.mem_aOrbitFinset.mpr ⟨l, ?_⟩, b.2⟩
    apply Subtype.ext; rw [conjA_coe]; exact hl
  · -- `j b' ∈ (univ.filter (a^L))`
    intro b' hb'
    rw [Finset.mem_filter] at hb' ⊢
    obtain ⟨l, hl⟩ := (hyp.mem_aOrbitFinset).mp hb'.1
    exact ⟨Finset.mem_univ _, l, by rw [← hyp.conjA_coe l a, hl]⟩
  · intro b _; rfl
  · intro b' _; rfl
  · -- summands agree
    intro b _
    rw [hyp.mobiusSummand_of_nonempty _ g hB]

/-- For `g ∈ (aH(a))^G` and `b' = a^l ∈ a^L`, also `g ∈ (b'H(b'))^G`: there is `x ∈ H(b')` with
`IsConj (b'·x) g`.  Transporting the witness `(a, h)` by `l`: `x = l·h·l⁻¹ ∈ H(a^l) = H(b')` by
(2.4.a), and `b'·x = l·(a·h)·l⁻¹` is `G`-conjugate to `a·h`, hence to `g`. -/
theorem exists_mem_H_isConj_of_mem_aOrbitFinset (hconj : hyp.HConjInvariant)
    {a b' : {a : G // a ∈ A}} {h g : G} (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g)
    (hb' : b' ∈ hyp.aOrbitFinset a) :
    ∃ x ∈ hyp.H b', IsConj (b'.1 * x) g := by
  obtain ⟨l, hl⟩ := hyp.mem_aOrbitFinset.mp hb'
  refine ⟨(l : G) * h * (l : G)⁻¹, ?_, ?_⟩
  · have hmem : (l : G) * h * (l : G)⁻¹ ∈ hyp.H (hyp.conjA l a) := by
      rw [hyp.mem_H_conjA_iff hconj a l]
      rw [show (l : G)⁻¹ * ((l : G) * h * (l : G)⁻¹) * (l : G) = h from by group]
      exact hh
    rwa [hl] at hmem
  · have hconjeq : b'.1 * ((l : G) * h * (l : G)⁻¹) = (l : G) * (a.1 * h) * (l : G)⁻¹ := by
      rw [← hl, conjA_coe]; group
    rw [hconjeq]
    exact (isConj_iff.mpr ⟨(l : G), rfl⟩).symm.trans hga

/-- `mobiusSummand` vanishes on the empty subset (no `a`). -/
theorem mobiusSummand_empty (a : {a : G // a ∈ A}) (g : G) :
    hyp.mobiusSummand a g (∅ : Finset {a : G // a ∈ A}) = 0 := by
  rw [mobiusSummand, dif_neg (by simp)]

/-- `mobiusTermCF` vanishes on the empty subset. -/
theorem mobiusTermCF_empty (hconj : hyp.HConjInvariant) (α : ClassFunction L ℂ) (g : G) :
    hyp.mobiusTermCF hconj α g (∅ : Finset {a : G // a ∈ A}) = 0 := by
  rw [mobiusTermCF, dif_neg (by simp)]

/-- **Peterfalvi (2.10), the support-side total.**  For `g ∈ (aH(a))^G` (witnessed by `h ∈ H(a)`,
`IsConj (a·h) g`), the transversal sum of orbit-averaging summands evaluates to `-α(a)`:

    `∑_{C ∈ ℬ} mobiusTermCF (rep C) = -α(a)`.

The proof: (1) orbit-average to the powerset (`sum_transversalRep_eq_sum_div_orbit`); (2) recast
each term via `mobiusTermCF_div_orbit_eq` to `(α(a)/|L|) · ∑_{b' ∈ a^L} [b' ∈ N_L(B)] mobiusSummand
b' g B` (handling the empty `B` separately, both sides zero); (3) swap the double sum by
`Finset.sum_comm`; (4) the inner `B`-sum over `𝒫(b')` collapses to its survivor `mobiusSummand b' g
{b'} = -|C_L(b')|` (`sum_mobiusSummand_eq_singleton` + `mobiusSummand_singleton_eq`, using
`g ∈ (b'H(b'))^G` for `b' ∈ a^L`); (5) `∑_{b' ∈ a^L} |C_L(b')| = |L|`
(`sum_card_centralizerIn_eq`), giving `(α(a)/|L|) · (-|L|) = -α(a)`. -/
theorem sum_mobiusTermCF_transversalRep_eq_neg (hconj : hyp.HConjInvariant)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    {a : {a : G // a ∈ A}} {h g : G} (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g) :
    letI := hyp.conjFinsetAction
    letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
    ∑ C : hyp.conjClassQuotient, hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g
        (hyp.transversalRep C)
      = -((α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩) := by
  classical
  letI := hyp.conjFinsetAction
  letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
  letI : Fintype {a : G // a ∈ A} := Fintype.ofFinite _
  letI : Fintype (Finset {a : G // a ∈ A}) := Fintype.ofFinite _
  set αa : ℂ := (α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩ with hαa
  -- (1) orbit-average the transversal sum to the powerset.
  rw [hyp.sum_transversalRep_eq_sum_div_orbit
    (h := fun B => hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g B)
    (fun l B => hyp.mobiusTermCF_conjFinset hconj _ g l B)]
  -- (2) recast each term; factor out `αa/|L|` over the `B`-sum.
  have hterm : ∀ B : Finset {a : G // a ∈ A},
      hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g B / (Nat.card (MulAction.orbit L B) : ℂ)
        = (αa / (Nat.card L : ℂ))
          * ∑ b' ∈ hyp.aOrbitFinset a,
            (if (b' : G) ∈ nLStabilizerIn hyp B then hyp.mobiusSummand b' g B else 0) := by
    intro B
    by_cases hB : B.Nonempty
    · exact hyp.mobiusTermCF_div_orbit_eq hconj α hB hh hga
    · -- empty `B`: both sides vanish.
      rw [Finset.not_nonempty_iff_eq_empty] at hB
      subst hB
      rw [hyp.mobiusTermCF_empty hconj, zero_div]
      rw [show (∑ b' ∈ hyp.aOrbitFinset a,
          (if (b' : G) ∈ nLStabilizerIn hyp (∅ : Finset {a : G // a ∈ A})
            then hyp.mobiusSummand b' g ∅ else 0)) = 0 from ?_, mul_zero]
      refine Finset.sum_eq_zero fun b' _ => ?_
      rw [hyp.mobiusSummand_empty, ite_self]
  rw [Finset.sum_congr rfl (fun B _ => hterm B), ← Finset.mul_sum]
  -- (3) swap the double sum: `∑_B ∑_{b'} = ∑_{b'} ∑_B`.
  rw [Finset.sum_comm]
  -- (4) collapse the inner `B`-sum over `𝒫(b')` to its survivor `-|C_L(b')|`.
  have hinner : ∀ b' ∈ hyp.aOrbitFinset a,
      (∑ B : Finset {a : G // a ∈ A},
        (if (b' : G) ∈ nLStabilizerIn hyp B then hyp.mobiusSummand b' g B else 0))
        = -((Nat.card (centralizerIn L b'.1)) : ℂ) := by
    intro b' hb'
    -- the `b'`-survivor needs `g ∈ (b'H(b'))^G`, i.e. `∃ x ∈ H(b'), IsConj (b'·x) g`.
    obtain ⟨x', hx', hgx'⟩ :=
      hyp.exists_mem_H_isConj_of_mem_aOrbitFinset hconj hh hga hb'
    -- restrict the full powerset `B`-sum to `𝒫(b')` (the `if` is `0` off it); the only difference
    -- is the empty set (in the filter via `b' ∈ N_L(∅)` but not in `mobiusIndex`), where the
    -- summand vanishes.  Then apply the survivor collapse.
    rw [← Finset.sum_filter]
    rw [show (∑ B ∈ Finset.univ.filter
          (fun B : Finset {a : G // a ∈ A} => (b' : G) ∈ nLStabilizerIn hyp B),
          hyp.mobiusSummand b' g B)
        = ∑ B ∈ hyp.mobiusIndex b', hyp.mobiusSummand b' g B from ?_]
    · rw [hyp.sum_mobiusSummand_eq_singleton hconj g b',
        hyp.mobiusSummand_singleton_eq g hx' hgx']
    · -- `∑_{mobiusIndex} = ∑_{filter}` since they differ only by `∅` (where the summand is `0`).
      refine (Finset.sum_subset ?_ ?_).symm
      · -- `mobiusIndex b' ⊆ filter`
        intro B hB
        rw [hyp.mem_mobiusIndex] at hB
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hB.2⟩
      · -- off `mobiusIndex` (i.e. `B = ∅`), the summand vanishes.
        intro B hBfilter hBnot
        rw [Finset.mem_filter] at hBfilter
        rw [hyp.mem_mobiusIndex] at hBnot
        have hBempty : ¬ B.Nonempty := fun hne => hBnot ⟨hne, hBfilter.2⟩
        rw [Finset.not_nonempty_iff_eq_empty] at hBempty
        rw [hBempty, hyp.mobiusSummand_empty]
  -- (5) combine: `∑_{b' ∈ a^L} (-|C_L(b')|) = -|L|`, giving `(αa/|L|)·(-|L|) = -αa`.
  -- evaluate the inner-collapsed sum `∑_{b' ∈ a^L} (-|C_L(b')|) = -|L|`.
  have hsum_eval :
      (∑ b' ∈ hyp.aOrbitFinset a,
        (∑ B : Finset {a : G // a ∈ A},
          (if (b' : G) ∈ nLStabilizerIn hyp B then hyp.mobiusSummand b' g B else 0)))
        = -((Nat.card L : ℂ)) := by
    rw [Finset.sum_congr rfl hinner]
    -- rewrite the `aOrbitFinset` index to the support filter `Sg` of `sum_card_centralizerIn_eq`.
    have hSg : hyp.aOrbitFinset a
        = Finset.univ.filter
          (fun b : {a : G // a ∈ A} => ∃ x ∈ hyp.H b, IsConj (b.1 * x) g) := by
      ext b'
      rw [Finset.mem_filter]
      constructor
      · intro hb'
        exact ⟨Finset.mem_univ _,
          hyp.exists_mem_H_isConj_of_mem_aOrbitFinset hconj hh hga hb'⟩
      · rintro ⟨-, x, hx, hbx⟩
        rw [hyp.mem_aOrbitFinset]
        obtain ⟨l, hl⟩ := hyp.isConj_in_L_of_mul_H a.2 b'.2 hh hx (hga.trans hbx.symm)
        exact ⟨l, Subtype.ext (by rw [conjA_coe]; exact hl)⟩
    rw [hSg, Finset.sum_neg_distrib, ← Nat.cast_sum,
      hyp.sum_card_centralizerIn_eq hconj (hyp.mem_dadeSupport_iff.mpr ⟨a, h, hh, hga⟩)]
  -- `(αa/|L|)·(-|L|) = -αa`.
  have hLne : (Nat.card L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hsum_eval]
  field_simp

end MobiusAssembly

end SemidirectStructure

end Hypothesis

end OddOrder.Peterfalvi.S04
