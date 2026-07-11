/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S04_InduceConjFinset

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S04_DadeIsometry` (2000-line limit, issue 0103 第 2 パス).
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

section DadeMap

variable {A A₁ : Set G} {L : Subgroup G}
/-- A candidate Dade map `τ : CF(L,A) → ClassFunction G`. -/
abbrev DadeMap (k : Type*) [CommRing k] (A : Set G) (L : Subgroup G) :=
  SupportedClassFunctions (G := G) k A L → ClassFunction G k

variable {k : Type*} [CommRing k]

namespace DadeMap

/-- Restrict the domain of a candidate Dade map along `A₁ ⊆ A`. -/
def restrictDomain (τ : DadeMap (G := G) k A L) (hA₁A : A₁ ⊆ A) :
    DadeMap (G := G) k A₁ L :=
  fun α => τ (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α)

@[simp] theorem restrictDomain_apply (τ : DadeMap (G := G) k A L) (hA₁A : A₁ ⊆ A)
    (α : SupportedClassFunctions (G := G) k A₁ L) :
    restrictDomain (G := G) (k := k) (L := L) τ hA₁A α =
      τ (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α) :=
  rfl

end DadeMap

section IsDadeMap

variable [Fintype G]

/-- Predicate form of Peterfalvi (2.5): a candidate map is the Dade map for
`hyp` if it has the prescribed values on conjugates of `aH(a)` and is zero off
their conjugacy-saturated union.

The uniqueness/well-definedness proof from (2.4.b) is intentionally kept out of
this predicate, so later work can either construct a map or assume one and use
these equations directly. -/
structure IsDadeMap (hyp : Hypothesis G A L) (τ : DadeMap (G := G) k A L) : Prop where
  map_eq_of_isConj_hCoset :
    ∀ (α : SupportedClassFunctions (G := G) k A L) (g : G)
      (a : {a : G // a ∈ A}) (h : G),
      h ∈ hyp.H a → IsConj (a.1 * h) g →
        τ α g = (α : ClassFunction L k) ⟨a.1, hyp.mem_L a.2⟩
  map_eq_zero_of_not_mem_dadeSupport :
    ∀ (α : SupportedClassFunctions (G := G) k A L) (g : G),
      g ∉ hyp.dadeSupport → τ α g = 0

namespace IsDadeMap

theorem map_eq_of_mem_hCoset {hyp : Hypothesis G A L} {τ : DadeMap (G := G) k A L}
    (hτ : IsDadeMap hyp τ) (α : SupportedClassFunctions (G := G) k A L)
    (a : {a : G // a ∈ A}) {g : G} (hg : g ∈ hyp.hCoset a) :
    τ α g = (α : ClassFunction L k) ⟨a.1, hyp.mem_L a.2⟩ := by
  rcases hg with ⟨h, hh, rfl⟩
  exact hτ.map_eq_of_isConj_hCoset α (a.1 * h) a h hh (IsConj.refl _)

/-- **The support of a Dade image is the thickening of the argument's support**
(the value-level converse of the (2.5) defining equations): a nonzero value `α^τ(g) ≠ 0`
exhibits a base point `a ∈ A` with `α(a) ≠ 0` and `g` conjugate into the coset `aH(a)`.
This is the *restricted* support bound `Supp(α^τ) ⊆ ⋃_{a ∈ A ∩ Supp α} (aH(a))^G` — finer
than `dadeSupport` (which unions over all of `A`), and the mechanism by which support
refinements of `α` (e.g. `A₁`-supported members of the (10.1) family) restrict the image
support (Peterfalvi (8.17)/(8.18) support geometry). -/
theorem exists_base_of_map_apply_ne_zero {hyp : Hypothesis G A L}
    {τ : DadeMap (G := G) k A L} (hτ : IsDadeMap hyp τ)
    (α : SupportedClassFunctions (G := G) k A L) {g : G} (hg : τ α g ≠ 0) :
    ∃ a : {a : G // a ∈ A}, ∃ h ∈ hyp.H a, IsConj (a.1 * h) g ∧
      (α : ClassFunction L k) ⟨a.1, hyp.mem_L a.2⟩ ≠ 0 := by
  have hgsupp : g ∈ hyp.dadeSupport := by
    by_contra hn
    exact hg (hτ.map_eq_zero_of_not_mem_dadeSupport α g hn)
  obtain ⟨a, h, hh, hconj⟩ := hyp.mem_dadeSupport_iff.mp hgsupp
  exact ⟨a, h, hh, hconj,
    fun h0 => hg ((hτ.map_eq_of_isConj_hCoset α g a h hh hconj).trans h0)⟩

/-- **Peterfalvi (2.5), uniqueness.**  The defining equations of the Dade map pin it
down completely: any two candidate maps satisfying `IsDadeMap hyp` agree.  On
`dadeSupport` both values are `α(a)` for a common witness `a` (`map_eq_of_isConj_hCoset`),
and off `dadeSupport` both vanish. -/
theorem unique {hyp : Hypothesis G A L} {τ₁ τ₂ : DadeMap (G := G) k A L}
    (h₁ : IsDadeMap hyp τ₁) (h₂ : IsDadeMap hyp τ₂) : τ₁ = τ₂ := by
  funext α
  refine ClassFunction.ext fun g => ?_
  by_cases hg : g ∈ hyp.dadeSupport
  · obtain ⟨a, h, hh, hconj⟩ := hyp.mem_dadeSupport_iff.mp hg
    rw [h₁.map_eq_of_isConj_hCoset α g a h hh hconj,
      h₂.map_eq_of_isConj_hCoset α g a h hh hconj]
  · rw [h₁.map_eq_zero_of_not_mem_dadeSupport α g hg,
      h₂.map_eq_zero_of_not_mem_dadeSupport α g hg]

theorem restrictDomain {hyp : Hypothesis G A L} {τ : DadeMap (G := G) k A L}
    (hτ : IsDadeMap hyp τ) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    IsDadeMap (hyp.restrict hA₁A hA₁_norm)
      (DadeMap.restrictDomain (G := G) (k := k) (L := L) τ hA₁A) where
  map_eq_of_isConj_hCoset α g a h hh hconj := by
    simpa using hτ.map_eq_of_isConj_hCoset
      (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α) g
      ⟨a.1, hA₁A a.2⟩ h hh hconj
  map_eq_zero_of_not_mem_dadeSupport α g hg := by
    by_cases hgsupp : g ∈ hyp.dadeSupport
    · rcases hyp.mem_dadeSupport_iff.mp hgsupp with ⟨a, h, hh, hconj⟩
      have ha_not : a.1 ∉ A₁ := by
        intro ha₁
        apply hg
        have hh' : h ∈ (hyp.restrict hA₁A hA₁_norm).H ⟨a.1, ha₁⟩ := by
          change h ∈ hyp.H ⟨a.1, hA₁A ha₁⟩
          have ha_eq : (⟨a.1, hA₁A ha₁⟩ : {a : G // a ∈ A}) = a := Subtype.ext rfl
          simpa [ha_eq] using hh
        exact (hyp.restrict hA₁A hA₁_norm).mem_dadeSupport_iff.mpr
          ⟨⟨a.1, ha₁⟩, h, hh', hconj⟩
      have hα_zero :
          (α : ClassFunction L k) ⟨a.1, hyp.mem_L a.2⟩ = 0 := by
        by_contra hne
        exact ha_not (α.property hne)
      have hmap := hτ.map_eq_of_isConj_hCoset
        (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α) g a h
        hh hconj
      rw [DadeMap.restrictDomain_apply, hmap]
      simpa using hα_zero
    · exact hτ.map_eq_zero_of_not_mem_dadeSupport
        (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α) g hgsupp

end IsDadeMap

/-- In the TI-specialized case `H(a)=1`, the Dade-map equation is simply
constant on `G`-conjugates of elements of `A`. -/
theorem map_eq_of_isConj_of_forall_H_eq_bot {hyp : Hypothesis G A L}
    {τ : DadeMap (G := G) k A L} (hτ : IsDadeMap hyp τ)
    (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥)
    (α : SupportedClassFunctions (G := G) k A L) {a g : G} (ha : a ∈ A)
    (hconj : IsConj a g) :
    τ α g = (α : ClassFunction L k) ⟨a, hyp.mem_L ha⟩ := by
  simpa using hτ.map_eq_of_isConj_hCoset α g ⟨a, ha⟩ 1
    (by simp [hH ⟨a, ha⟩]) (by simpa using hconj)

theorem map_eq_of_mem_A_of_forall_H_eq_bot {hyp : Hypothesis G A L}
    {τ : DadeMap (G := G) k A L} (hτ : IsDadeMap hyp τ)
    (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥)
    (α : SupportedClassFunctions (G := G) k A L) {a : G} (ha : a ∈ A) :
    τ α a = (α : ClassFunction L k) ⟨a, hyp.mem_L ha⟩ :=
  map_eq_of_isConj_of_forall_H_eq_bot hτ hH α ha (IsConj.refl a)

/-- In the TI-specialized case `H(a)=1`, a Dade map vanishes outside the
conjugacy-saturation of `A`. -/
theorem map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot
    {hyp : Hypothesis G A L} {τ : DadeMap (G := G) k A L} (hτ : IsDadeMap hyp τ)
    (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥)
    (α : SupportedClassFunctions (G := G) k A L) {g : G}
    (hg : g ∉ Group.conjugatesOfSet A) :
    τ α g = 0 := by
  apply hτ.map_eq_zero_of_not_mem_dadeSupport
  rwa [hyp.dadeSupport_eq_conjugatesOfSet_of_forall_H_eq_bot hH]

/-! ### The explicit Dade map of Peterfalvi (2.5)

We construct the Dade map `α ↦ α^τ` *pointwise* from its defining equations (2.5):
`α^τ(g) = α(a)` if `g` is `G`-conjugate to an element of some coset `aH(a)`, and `0`
otherwise.  Well-definedness (independence of the chosen `a`) is exactly (2.4.b).
This realizes the previously interface-only `IsDadeMap` as an honest construction;
together with `isDadeIsometry_of_isDadeMap` it gives a genuine `DadeIsometryData`.
The remaining (2.6.b) virtual-character preservation, which needs the (2.10)
inclusion–exclusion, upgrades it to a `FullDadeIsometryData`. -/

/-- The value `α^τ(g)` of the Peterfalvi (2.5) Dade map: `α(a)` when `g` is
`G`-conjugate to an element of some coset `aH(a)`, else `0`.  The chosen `a` is
irrelevant by (2.4.b) (`dadeValue_eq`). -/
noncomputable def Hypothesis.dadeValue (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L) (g : G) : k := by
  classical
  exact if hg : g ∈ hyp.dadeSupport then
      (α : ClassFunction L k)
        ⟨(hyp.mem_dadeSupport_iff.mp hg).choose.1,
          hyp.mem_L (hyp.mem_dadeSupport_iff.mp hg).choose.2⟩
    else 0

theorem Hypothesis.dadeValue_of_not_mem_dadeSupport (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L) {g : G} (hg : g ∉ hyp.dadeSupport) :
    hyp.dadeValue α g = 0 := by
  rw [Hypothesis.dadeValue, dif_neg hg]

/-- **Peterfalvi (2.5), well-definedness.**  `α^τ(g) = α(a)` whenever `g` is
`G`-conjugate to an element of `aH(a)`.  Two such base points `a, a'` are
`L`-conjugate by (2.4.b) (`isConj_in_L_of_mul_H`), and `α` is an `L`-class function. -/
theorem Hypothesis.dadeValue_eq (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L)
    {a : {a : G // a ∈ A}} {h g : G} (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g) :
    hyp.dadeValue α g = (α : ClassFunction L k) ⟨a.1, hyp.mem_L a.2⟩ := by
  classical
  have hg : g ∈ hyp.dadeSupport := hyp.mem_dadeSupport_iff.mpr ⟨a, h, hh, hga⟩
  rw [Hypothesis.dadeValue, dif_pos hg]
  set a₀ := (hyp.mem_dadeSupport_iff.mp hg).choose with ha₀
  obtain ⟨h₀, hh₀, hga₀⟩ := (hyp.mem_dadeSupport_iff.mp hg).choose_spec
  obtain ⟨l, hl⟩ := hyp.isConj_in_L_of_mul_H a₀.2 a.2 hh₀ hh (hga₀.trans hga.symm)
  refine ClassFunction.of_isConj (α : ClassFunction L k) (isConj_iff.mpr ⟨l, ?_⟩)
  exact Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact hl)

/-- The Peterfalvi (2.5) Dade map as a `ClassFunction G k`.  Conjugation invariance:
if `g` lies in `dadeSupport` it is `G`-conjugate to some `aH(a)`, hence so is
`x g x⁻¹` with the *same* `a`, so both values are `α(a)`; off `dadeSupport` both are `0`
(`dadeSupport` is conjugation-stable). -/
noncomputable def Hypothesis.dadeMapCF (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L) : ClassFunction G k :=
  ⟨hyp.dadeValue α, by
    intro g x
    by_cases hg : g ∈ hyp.dadeSupport
    · obtain ⟨a, h, hh, hga⟩ := hyp.mem_dadeSupport_iff.mp hg
      rw [hyp.dadeValue_eq α hh (hga.trans (isConj_iff.mpr ⟨x, rfl⟩)),
        hyp.dadeValue_eq α hh hga]
    · have hxg : x * g * x⁻¹ ∉ hyp.dadeSupport := by
        rw [hyp.mem_dadeSupport_conj_iff]; exact hg
      rw [hyp.dadeValue_of_not_mem_dadeSupport α hxg,
        hyp.dadeValue_of_not_mem_dadeSupport α hg]⟩

/-- **Peterfalvi (2.5).**  The explicit Dade map `τ : CF(L, A) → CF(G)`. -/
noncomputable def Hypothesis.dadeMap (hyp : Hypothesis G A L) :
    DadeMap (G := G) k A L :=
  fun α => hyp.dadeMapCF α

@[simp] theorem Hypothesis.dadeMap_apply (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L) (g : G) :
    hyp.dadeMap α g = hyp.dadeValue α g := rfl

/-- **The Dade map commutes with conjugation** (Coq `Dtau`+`cfAut` step of `GammaReal`): the
`(2.5)` map is a pointwise evaluation `α(a)` on its support and `0` off it, so `star` passes
through.  The conjugated input is supported on the same set (`conj_support`). -/
theorem Hypothesis.dadeMap_conj [StarRing k] (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L) :
    (hyp.dadeMap (k := k) α).conj
      = hyp.dadeMap (k := k)
          ⟨(α : ClassFunction (↥L) k).conj, by
            rw [ClassFunction.mem_supportedSubmodule, ClassFunction.conj_support]
            exact (ClassFunction.mem_supportedSubmodule).mp α.2⟩ := by
  ext g
  classical
  by_cases hg : g ∈ hyp.dadeSupport
  · obtain ⟨a, h, hh, hga⟩ := hyp.mem_dadeSupport_iff.mp hg
    rw [ClassFunction.conj_apply, hyp.dadeMap_apply, hyp.dadeMap_apply,
      hyp.dadeValue_eq α hh hga, hyp.dadeValue_eq _ hh hga]
    rfl
  · rw [ClassFunction.conj_apply, hyp.dadeMap_apply, hyp.dadeMap_apply,
      hyp.dadeValue_of_not_mem_dadeSupport α hg,
      hyp.dadeValue_of_not_mem_dadeSupport _ hg, star_zero]

/-- The Peterfalvi (2.5) Dade map is `k`-linear in its argument.

`dadeValue α g` is, at each `g ∈ dadeSupport`, the *evaluation* `α(a)` at a fixed base point `a`
(and `0` off the support), so it is `k`-linear in `α`: `dadeValue (c•α+β) g = c·dadeValue α g +
dadeValue β g` pointwise.  This packages the bare `DadeMap` function `hyp.dadeMap` as an honest
`k`-linear map `CF(L,A) →ₗ[k] CF(G)` — the form needed to extend it to a total integral character
map (the coherence base map `τ` of Peterfalvi (5.1)). -/
noncomputable def Hypothesis.dadeLinearMap (hyp : Hypothesis G A L) :
    SupportedClassFunctions (G := G) k A L →ₗ[k] ClassFunction G k where
  toFun := hyp.dadeMap (k := k)
  map_add' α β := by
    ext g
    classical
    by_cases hg : g ∈ hyp.dadeSupport
    · obtain ⟨a, h, hh, hga⟩ := hyp.mem_dadeSupport_iff.mp hg
      rw [ClassFunction.add_apply, hyp.dadeMap_apply, hyp.dadeMap_apply, hyp.dadeMap_apply,
        hyp.dadeValue_eq α hh hga, hyp.dadeValue_eq β hh hga, hyp.dadeValue_eq (α + β) hh hga]
      rfl
    · rw [ClassFunction.add_apply, hyp.dadeMap_apply, hyp.dadeMap_apply, hyp.dadeMap_apply,
        hyp.dadeValue_of_not_mem_dadeSupport α hg, hyp.dadeValue_of_not_mem_dadeSupport β hg,
        hyp.dadeValue_of_not_mem_dadeSupport (α + β) hg, add_zero]
  map_smul' c α := by
    ext g
    classical
    by_cases hg : g ∈ hyp.dadeSupport
    · obtain ⟨a, h, hh, hga⟩ := hyp.mem_dadeSupport_iff.mp hg
      rw [RingHom.id_apply, ClassFunction.smul_apply, hyp.dadeMap_apply, hyp.dadeMap_apply,
        hyp.dadeValue_eq α hh hga, hyp.dadeValue_eq (c • α) hh hga]
      rfl
    · rw [RingHom.id_apply, ClassFunction.smul_apply, hyp.dadeMap_apply, hyp.dadeMap_apply,
        hyp.dadeValue_of_not_mem_dadeSupport α hg,
        hyp.dadeValue_of_not_mem_dadeSupport (c • α) hg, mul_zero]

@[simp] theorem Hypothesis.dadeLinearMap_apply (hyp : Hypothesis G A L)
    (α : SupportedClassFunctions (G := G) k A L) :
    hyp.dadeLinearMap (k := k) α = hyp.dadeMap (k := k) α := rfl

/-- **Peterfalvi (2.5).**  The explicit Dade map satisfies the defining equations,
i.e. it `IsDadeMap`.  This discharges the `IsDadeMap` interface by construction. -/
theorem Hypothesis.isDadeMap_dadeMap (hyp : Hypothesis G A L) :
    IsDadeMap hyp (hyp.dadeMap (k := k)) where
  map_eq_of_isConj_hCoset α g a h hh hconj := hyp.dadeValue_eq α hh hconj
  map_eq_zero_of_not_mem_dadeSupport α g hg :=
    hyp.dadeValue_of_not_mem_dadeSupport α hg

/-- **Peterfalvi (2.11), restriction compatibility of the constructed Dade map.**  The
explicit Dade map of the restricted hypothesis `hyp.restrict` is the domain-restriction
of the explicit Dade map of `hyp`: `(α₁)^{τ₁} = (ι α₁)^τ` for `α₁ ∈ CF(L, A₁)`.

This fulfils the promise recorded at `Hypothesis.restrict` — that "the equality of the
corresponding Dade maps is stated later, once `dadeMap` is defined".  It now holds *as a
theorem about the genuine construction* (not an interface assumption): both sides satisfy
the (2.5) defining equations for `hyp.restrict` — the left by `isDadeMap_dadeMap`, the
right by `IsDadeMap.restrictDomain` applied to `hyp`'s — so they coincide by the (2.5)
uniqueness `IsDadeMap.unique`. -/
theorem Hypothesis.dadeMap_restrict (hyp : Hypothesis G A L) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    (hyp.restrict hA₁A hA₁_norm).dadeMap (k := k) =
      DadeMap.restrictDomain (G := G) (k := k) (L := L) (hyp.dadeMap (k := k)) hA₁A :=
  IsDadeMap.unique
    ((hyp.restrict hA₁A hA₁_norm).isDadeMap_dadeMap (k := k))
    (IsDadeMap.restrictDomain (hyp.isDadeMap_dadeMap (k := k)) hA₁A hA₁_norm)

/-- **Peterfalvi (2.11)**, pointwise form of `Hypothesis.dadeMap_restrict`: the restricted
Dade map evaluated at `α₁ ∈ CF(L, A₁)` is `hyp`'s Dade map at the included `α₁`. -/
theorem Hypothesis.dadeMap_restrict_apply (hyp : Hypothesis G A L) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (α : SupportedClassFunctions (G := G) k A₁ L) :
    (hyp.restrict hA₁A hA₁_norm).dadeMap (k := k) α =
      hyp.dadeMap (k := k)
        (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α) := by
  rw [hyp.dadeMap_restrict hA₁A hA₁_norm, DadeMap.restrictDomain_apply]

end IsDadeMap

/-- Peterfalvi (2.6.b): a complex Dade map sends supported virtual characters
on `L` to virtual characters of `G`.

The domain is still represented by the complex supported class-function space
`CF(L,A)`; the hypothesis says that, whenever such a supported class function
also lies in the integral lattice `ℤ[Irr L]`, its image lies in `ℤ[Irr G]`. -/
def PreservesVirtualCharacters (τ : DadeMap (G := G) ℂ A L) : Prop :=
  ∀ α : SupportedClassFunctions (G := G) ℂ A L,
    ((α : ClassFunction L ℂ) ∈ ZIrr L) → τ α ∈ ZIrr G

namespace PreservesVirtualCharacters

/-- Virtual-character preservation restricts along `A₁ ⊆ A`.

This is the `(2.6.b)` companion to the restriction statement in Peterfalvi
(2.11). -/
theorem restrictDomain {τ : DadeMap (G := G) ℂ A L}
    (hτ : PreservesVirtualCharacters (G := G) (A := A) (L := L) τ)
    (hA₁A : A₁ ⊆ A) :
    PreservesVirtualCharacters (G := G) (A := A₁) (L := L)
      (DadeMap.restrictDomain (G := G) (k := ℂ) (L := L) τ hA₁A) := by
  intro α hα
  exact hτ
    (SupportedClassFunctions.inclusion (G := G) (k := ℂ) (L := L) hA₁A α)
    (by simpa using hα)

end PreservesVirtualCharacters

/-- **Peterfalvi (2.6.b), reduced to the (2.10) identity.**  If the explicit Dade map
`hyp.dadeMap` agrees, on every supported virtual character `α ∈ ℤ[Irr L, A]`, with *some* finite
`ℤ`-linear combination of inclusion–exclusion summands `Ind_{M(B)}^G α_B` (`induceAlphaBTerm`),
then `hyp.dadeMap` preserves virtual characters, i.e. satisfies `PreservesVirtualCharacters`.

This isolates the remaining content of (2.6.b) to the (2.10) identity
`α^τ = -∑_{B ∈ ℬ} (-1)^{|B|} Ind_{M(B)} α_B` itself: once that pointwise identity is available
(with `s = ℬ` the `L`-conjugacy transversal and `c B = -(-1)^{|B|}`), this lemma upgrades the
`DadeIsometryData` to a `FullDadeIsometryData`.  Membership of the right-hand side in `ℤ[Irr G]`
is `zsmul_induceAlphaBTerm_sum_mem_ZIrr`. -/
theorem preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis G A L} (hconj : hyp.HConjInvariant)
    (hτ : ∀ α : SupportedClassFunctions (G := G) ℂ A L,
        ((α : ClassFunction L ℂ) ∈ ZIrr L) →
        ∃ (s : Finset {B : Finset {a : G // a ∈ A} // B.Nonempty})
          (c : {B : Finset {a : G // a ∈ A} // B.Nonempty} → ℤ),
          hyp.dadeMap (k := ℂ) α
            = ∑ p ∈ s, c p • hyp.induceAlphaBTerm hconj (α : ClassFunction L ℂ) p) :
    PreservesVirtualCharacters (G := G) (A := A) (L := L) (hyp.dadeMap (k := ℂ)) := by
  intro α hα
  obtain ⟨s, c, hsum⟩ := hτ α hα
  rw [hsum]
  exact hyp.zsmul_induceAlphaBTerm_sum_mem_ZIrr hconj hα s c

variable [StarRing k]
variable [Fintype G] [Fintype L]
variable [Invertible (Nat.card G : k)] [Invertible (Nat.card L : k)]

/-- The coefficient-parametric part of the Dade isometry interface:
preservation of Peterfalvi's normalized class-function inner product. -/
structure IsDadeIsometry (τ : DadeMap (G := G) k A L) : Prop where
  inner_eq :
    ∀ α β : SupportedClassFunctions (G := G) k A L,
      ClassFunction.inner (τ α) (τ β) =
        ClassFunction.inner (α : ClassFunction L k) (β : ClassFunction L k)

namespace IsDadeIsometry

/-- The inner-product part of a Dade isometry restricts along `A₁ ⊆ A`.

This is the currently formalized part of Peterfalvi (2.11). -/
theorem restrictDomain {τ : DadeMap (G := G) k A L} (hτ : IsDadeIsometry τ)
    (hA₁A : A₁ ⊆ A) :
    IsDadeIsometry (DadeMap.restrictDomain (G := G) (k := k) (L := L) τ hA₁A) where
  inner_eq α β := by
    simpa using hτ.inner_eq
      (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α)
      (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A β)

end IsDadeIsometry

/-- A bundled Dade isometry candidate relative to `hyp`.

This packages the pointwise equations from Peterfalvi (2.5) together with the
coefficient-parametric normalized inner-product part of (2.6.a).  The
complex-coefficient full bundle below adds the virtual-character preservation
property from (2.6.b). -/
structure DadeIsometryData (hyp : Hypothesis G A L) where
  toDadeMap : DadeMap (G := G) k A L
  isDadeMap : IsDadeMap hyp toDadeMap
  isDadeIsometry : IsDadeIsometry toDadeMap

namespace DadeIsometryData

variable {hyp : Hypothesis G A L}

instance : CoeFun (DadeIsometryData (G := G) (k := k) hyp)
    (fun _ => DadeMap (G := G) k A L) :=
  ⟨fun τ => τ.toDadeMap⟩

@[simp] theorem coe_mk (τ : DadeMap (G := G) k A L)
    (hmap : IsDadeMap hyp τ) (hiso : IsDadeIsometry τ) :
    ((DadeIsometryData.mk τ hmap hiso : DadeIsometryData (G := G) (k := k) hyp) :
      DadeMap (G := G) k A L) = τ :=
  rfl

/-- Restrict a bundled Dade isometry to an `L`-stable subset `A₁ ⊆ A`.

This is the bundled form of the currently available part of Peterfalvi (2.11). -/
def restrict (τ : DadeIsometryData (G := G) (k := k) hyp) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    DadeIsometryData (G := G) (k := k) (hyp.restrict hA₁A hA₁_norm) where
  toDadeMap := DadeMap.restrictDomain (G := G) (k := k) (L := L) τ.toDadeMap hA₁A
  isDadeMap := IsDadeMap.restrictDomain τ.isDadeMap hA₁A hA₁_norm
  isDadeIsometry := IsDadeIsometry.restrictDomain τ.isDadeIsometry hA₁A

@[simp] theorem restrict_toDadeMap
    (τ : DadeIsometryData (G := G) (k := k) hyp) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    (τ.restrict hA₁A hA₁_norm).toDadeMap =
      DadeMap.restrictDomain (G := G) (k := k) (L := L) τ.toDadeMap hA₁A :=
  rfl

@[simp] theorem restrict_apply
    (τ : DadeIsometryData (G := G) (k := k) hyp) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (α : SupportedClassFunctions (G := G) k A₁ L) :
    (τ.restrict hA₁A hA₁_norm).toDadeMap α =
      τ.toDadeMap (SupportedClassFunctions.inclusion (G := G) (k := k) (L := L) hA₁A α) :=
  rfl

end DadeIsometryData

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card L : ℂ)]

/-- The full complex Dade-isometry interface used by Peterfalvi after (2.6):
the Dade-map equations, normalized isometry, and preservation of virtual
characters. -/
structure FullDadeIsometryData (hyp : Hypothesis G A L) where
  toDadeIsometryData : DadeIsometryData (G := G) (k := ℂ) hyp
  preserves_virtualCharacters :
    PreservesVirtualCharacters (G := G) (A := A) (L := L) toDadeIsometryData.toDadeMap

namespace FullDadeIsometryData

variable {hyp : Hypothesis G A L}

/-- The underlying Dade map of a full complex Dade-isometry package. -/
abbrev toDadeMap (τ : FullDadeIsometryData (G := G) hyp) : DadeMap (G := G) ℂ A L :=
  τ.toDadeIsometryData.toDadeMap

instance : CoeFun (FullDadeIsometryData (G := G) hyp)
    (fun _ => DadeMap (G := G) ℂ A L) :=
  ⟨fun τ => τ.toDadeMap⟩

@[simp] theorem coe_mk (τ : DadeIsometryData (G := G) (k := ℂ) hyp)
    (hvirt : PreservesVirtualCharacters (G := G) (A := A) (L := L) τ.toDadeMap) :
    ((FullDadeIsometryData.mk τ hvirt : FullDadeIsometryData (G := G) hyp) :
      DadeMap (G := G) ℂ A L) = τ.toDadeMap :=
  rfl

theorem inner_eq (τ : FullDadeIsometryData (G := G) hyp)
    (α β : SupportedClassFunctions (G := G) ℂ A L) :
    ClassFunction.inner (τ.toDadeMap α) (τ.toDadeMap β) =
      ClassFunction.inner (α : ClassFunction L ℂ) (β : ClassFunction L ℂ) :=
  τ.toDadeIsometryData.isDadeIsometry.inner_eq α β

theorem maps_virtualCharacter (τ : FullDadeIsometryData (G := G) hyp)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    (hα : (α : ClassFunction L ℂ) ∈ ZIrr L) :
    τ.toDadeMap α ∈ ZIrr G :=
  τ.preserves_virtualCharacters α hα

/-- Restrict a full complex Dade isometry to an `L`-stable subset `A₁ ⊆ A`. -/
def restrict (τ : FullDadeIsometryData (G := G) hyp) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    FullDadeIsometryData (G := G) (hyp.restrict hA₁A hA₁_norm) where
  toDadeIsometryData := τ.toDadeIsometryData.restrict hA₁A hA₁_norm
  preserves_virtualCharacters :=
    PreservesVirtualCharacters.restrictDomain τ.preserves_virtualCharacters hA₁A

@[simp] theorem restrict_toDadeMap
    (τ : FullDadeIsometryData (G := G) hyp) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    (τ.restrict hA₁A hA₁_norm).toDadeMap =
      DadeMap.restrictDomain (G := G) (k := ℂ) (L := L) τ.toDadeMap hA₁A :=
  by simp [restrict, toDadeMap, DadeIsometryData.restrict]

@[simp] theorem restrict_apply
    (τ : FullDadeIsometryData (G := G) hyp) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (α : SupportedClassFunctions (G := G) ℂ A₁ L) :
    (τ.restrict hA₁A hA₁_norm).toDadeMap α =
      τ.toDadeMap (SupportedClassFunctions.inclusion (G := G) (k := ℂ) (L := L) hA₁A α) :=
  by simp [restrict, toDadeMap, DadeIsometryData.restrict]

end FullDadeIsometryData

section AdjointFormula

variable (hyp : Hypothesis G A L)

/-- The Peterfalvi (2.7) **adjoint averaging map**: given `χ : ClassFunction G ℂ`,
this is the function `L → ℂ` defined on `A` by `a ↦ |H(a)|⁻¹ ∑_{x ∈ H(a)} χ(ax)`,
and zero off `A`.  Classical logic is used to decide membership in `A` and to
provide a `Fintype` for `↥(hyp.H a)` from `[Fintype G]`. -/
noncomputable def adjointAverageFun (χ : ClassFunction G ℂ) : L → ℂ := by
  intro ℓ
  classical
  exact if h : (ℓ : G) ∈ A then
    (Nat.card ↥(hyp.H ⟨(ℓ : G), h⟩) : ℂ)⁻¹ *
      ∑ x : ↥(hyp.H ⟨(ℓ : G), h⟩), χ ((ℓ : G) * (x : G))
  else 0

/-- **Peterfalvi (2.7) adjoint formula.**

Given a candidate Dade map `τ` satisfying the (2.5) defining equations on the
support of `α : CF(L, A)`, a class function `χ : ClassFunction G ℂ`, and a
class function `ψ : ClassFunction L ℂ` whose values on `A` average `χ` along
the cosets `aH(a)`:

    ψ(a) = |H(a)|⁻¹ · ∑_{x ∈ H(a)} χ(ax)    (a ∈ A),

the inner products satisfy `⟨τ α, χ⟩_G = ⟨α, ψ⟩_L`.

In Peterfalvi's textbook this is proved by rewriting `⟨τ α, χ⟩_G` as a sum over
G-conjugacy class representatives of `A`, using (2.4) and the defining equation
(2.5).  The Lean statement keeps `ψ` as an explicit input; the special case
`ψ = Res_L^G χ` (with `χ` constant on each `aH(a)`) is the form used in the
proof of Theorem (2.6.a).

This lemma is Peterfalvi §4's heaviest external export: §7 (5.4), §9 (7.2.b),
§12 (9.5) ×2, §13 (10.3), §16 (14.1) ×2 all apply it directly (audit
2026-05-23). -/
theorem adjoint_formula
    (τ : DadeMap (G := G) (k := ℂ) A L) (hτ : IsDadeMap hyp τ)
    (hconj : hyp.HConjInvariant)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    (χ : ClassFunction G ℂ) (ψ : ClassFunction L ℂ)
    (hψ : ∀ a : {a : G // a ∈ A},
        ψ ⟨a.1, hyp.subset_L a.2⟩ =
          adjointAverageFun hyp χ ⟨a.1, hyp.subset_L a.2⟩) :
    ClassFunction.inner (τ α) χ =
      ClassFunction.inner (α : ClassFunction L ℂ) ψ := by
  classical
  letI : Fintype {a : G // a ∈ A} := Fintype.ofFinite _
  set aα : {a : G // a ∈ A} → ℂ :=
    fun a => (α : ClassFunction L ℂ) ⟨a.1, hyp.subset_L a.2⟩ with haα
  set F : G → ℂ := fun g => (τ α) g * star (χ g) with hF
  set M : ℂ := ∑ a : {a : G // a ∈ A}, ∑ x : hyp.H a, ∑ t : G,
      (Nat.card (hyp.H a) : ℂ)⁻¹ * aα a *
        star (χ ((t : G) * (a.1 * (x : G)) * (t : G)⁻¹)) with hM
  -- |H(a)| ≠ 0 in ℂ
  have hHne : ∀ a : {a : G // a ∈ A}, (Nat.card (hyp.H a) : ℂ) ≠ 0 := by
    intro a
    have : 0 < Nat.card (hyp.H a) := Nat.card_pos
    exact_mod_cast this.ne'
  -- the averaging value, unfolded
  have hψa : ∀ a : {a : G // a ∈ A},
      ψ ⟨a.1, hyp.subset_L a.2⟩
        = (Nat.card (hyp.H a) : ℂ)⁻¹ * ∑ x : hyp.H a, χ (a.1 * (x : G)) := by
    intro a
    rw [hψ a]
    simp only [adjointAverageFun]
    rw [dif_pos a.2]
  -- support reindexing of the L-inner sum
  have hISL : ClassFunction.innerSum (α : ClassFunction L ℂ) ψ
      = ∑ a : {a : G // a ∈ A}, aα a * star (ψ ⟨a.1, hyp.subset_L a.2⟩) := by
    rw [ClassFunction.innerSum]
    rw [← Finset.sum_subset
      (Finset.filter_subset (fun ℓ : L => (ℓ : G) ∈ A) Finset.univ)
      (fun ℓ _ hℓ => by
        have hα0 : (α : ClassFunction L ℂ) ℓ = 0 := by
          by_contra hne
          exact hℓ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, α.2 hne⟩)
        rw [hα0, zero_mul])]
    refine (Finset.sum_bij (fun a _ => (⟨a.1, hyp.subset_L a.2⟩ : L)) ?_ ?_ ?_ ?_).symm
    · intro a _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩
    · intro a _ b _ hab; exact Subtype.ext (by simpa using congrArg Subtype.val hab)
    · intro ℓ hℓ
      exact ⟨⟨ℓ.1, (Finset.mem_filter.mp hℓ).2⟩, Finset.mem_univ _, Subtype.ext rfl⟩
    · intro a _; rfl
  -- WAY 1: M = |G| · ⟨α, ψ⟩_L
  have way1 : M = (Nat.card G : ℂ) * ClassFunction.innerSum (α : ClassFunction L ℂ) ψ := by
    rw [hISL, Finset.mul_sum, hM]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hstar_psi : star (ψ ⟨a.1, hyp.subset_L a.2⟩)
        = (Nat.card (hyp.H a) : ℂ)⁻¹ * ∑ x : hyp.H a, star (χ (a.1 * (x : G))) := by
      rw [hψa a, star_mul', star_sum, star_inv₀, star_natCast]
    calc ∑ x : hyp.H a, ∑ t : G, (Nat.card (hyp.H a) : ℂ)⁻¹ * aα a *
            star (χ ((t : G) * (a.1 * (x : G)) * (t : G)⁻¹))
        = ∑ x : hyp.H a, (Nat.card G : ℂ) *
            ((Nat.card (hyp.H a) : ℂ)⁻¹ * aα a * star (χ (a.1 * (x : G)))) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          simp only [ClassFunction.conj_eq]
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
      _ = (Nat.card G : ℂ) * (aα a * star (ψ ⟨a.1, hyp.subset_L a.2⟩)) := by
          rw [hstar_psi, ← Finset.mul_sum]
          congr 1
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          ring
  -- substitution aα a = (τ α)(t (a x) t⁻¹)
  have hsub : ∀ (a : {a : G // a ∈ A}) (x : hyp.H a) (t : G),
      aα a = (τ α) ((t : G) * (a.1 * (x : G)) * (t : G)⁻¹) := by
    intro a x t
    rw [haα]
    exact (hτ.map_eq_of_isConj_hCoset α _ a (x : G) x.2
      (isConj_iff.mpr ⟨(t : G), rfl⟩)).symm
  -- WAY 2: M = |L| · ⟨τ α, χ⟩_G
  have way2 : M = (Nat.card L : ℂ) * ClassFunction.innerSum (τ α) χ := by
    have step : M = ∑ a : {a : G // a ∈ A},
        ∑ b ∈ Finset.univ.filter (fun b : G => ∃ x ∈ hyp.H a, IsConj (a.1 * x) b),
          (Nat.card (centralizerIn L a.1) : ℂ) * F b := by
      rw [hM]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have e1 : (∑ x : hyp.H a, ∑ t : G, (Nat.card (hyp.H a) : ℂ)⁻¹ * aα a *
              star (χ ((t : G) * (a.1 * (x : G)) * (t : G)⁻¹)))
          = (Nat.card (hyp.H a) : ℂ)⁻¹ *
              ∑ x : hyp.H a, ∑ t : G, F ((t : G) * (a.1 * (x : G)) * (t : G)⁻¹) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [hsub a x t, hF]
        ring
      rw [e1, hyp.fiber_regroup a F, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [← mul_assoc]
      congr 1
      rw [hyp.card_centralizer_eq a, Nat.cast_mul, ← mul_assoc,
        inv_mul_cancel₀ (hHne a), one_mul]
    rw [step]
    -- turn inner filtered sum into an if-sum, then swap
    have step2 : (∑ a : {a : G // a ∈ A},
          ∑ b ∈ Finset.univ.filter (fun b : G => ∃ x ∈ hyp.H a, IsConj (a.1 * x) b),
            (Nat.card (centralizerIn L a.1) : ℂ) * F b)
        = ∑ b : G, ∑ a : {a : G // a ∈ A},
            (if (∃ x ∈ hyp.H a, IsConj (a.1 * x) b)
              then (Nat.card (centralizerIn L a.1) : ℂ) * F b else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_filter]
    rw [step2, show (Nat.card L : ℂ) * ClassFunction.innerSum (τ α) χ
          = ∑ b : G, (Nat.card L : ℂ) * F b from by
        rw [ClassFunction.innerSum, Finset.mul_sum]]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    -- ∑_a (if Q then |C_L a| * F b else 0) = |L| * F b
    have factor : (∑ a : {a : G // a ∈ A},
          (if (∃ x ∈ hyp.H a, IsConj (a.1 * x) b)
            then (Nat.card (centralizerIn L a.1) : ℂ) * F b else 0))
        = (∑ a : {a : G // a ∈ A},
            (if (∃ x ∈ hyp.H a, IsConj (a.1 * x) b)
              then (Nat.card (centralizerIn L a.1) : ℂ) else 0)) * F b := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      split <;> simp
    rw [factor]
    by_cases hb : b ∈ hyp.dadeSupport
    · have hN : (∑ a : {a : G // a ∈ A},
            (if (∃ x ∈ hyp.H a, IsConj (a.1 * x) b)
              then (Nat.card (centralizerIn L a.1) : ℂ) else 0)) = (Nat.card L : ℂ) := by
        rw [← Finset.sum_filter, ← Nat.cast_sum, hyp.sum_card_centralizerIn_eq hconj hb]
      rw [hN, mul_comm]
    · have hF0 : F b = 0 := by
        rw [hF]
        simp only
        rw [hτ.map_eq_zero_of_not_mem_dadeSupport α b hb, zero_mul]
      rw [hF0, mul_zero, mul_zero]
  -- combine and divide by |G|, |L|
  have hcombine : (Nat.card L : ℂ) * ClassFunction.innerSum (τ α) χ
      = (Nat.card G : ℂ) * ClassFunction.innerSum (α : ClassFunction L ℂ) ψ :=
    way2.symm.trans way1
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.inner_eq_inv_card_mul_innerSum]
  calc ⅟(Nat.card G : ℂ) * ClassFunction.innerSum (τ α) χ
      = ⅟(Nat.card G : ℂ) * ⅟(Nat.card L : ℂ) *
          ((Nat.card L : ℂ) * ClassFunction.innerSum (τ α) χ) := by
        rw [mul_assoc, ← mul_assoc (⅟(Nat.card L : ℂ)), invOf_mul_self, one_mul]
    _ = ⅟(Nat.card G : ℂ) * ⅟(Nat.card L : ℂ) *
          ((Nat.card G : ℂ) * ClassFunction.innerSum (α : ClassFunction L ℂ) ψ) := by
        rw [hcombine]
    _ = ⅟(Nat.card L : ℂ) * ClassFunction.innerSum (α : ClassFunction L ℂ) ψ := by
        rw [mul_comm (⅟(Nat.card G : ℂ)) (⅟(Nat.card L : ℂ)), mul_assoc,
          ← mul_assoc (⅟(Nat.card G : ℂ)), invOf_mul_self, one_mul]

omit [Fintype L] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card L : ℂ)] in
/-- For a Dade map `τ` and `β : CF(L, A)`, the (2.7) averaging map applied to the
class function `τ β` recovers `β` on `A`.

Indeed `τ β` is constant equal to `β(a)` on the coset `aH(a)` (this is the (2.5)
defining equation `IsDadeMap.map_eq_of_mem_hCoset`), so averaging it over `H(a)`
gives back `β(a)`.  This is the computation behind Peterfalvi's remark, at the
start of the proof of (2.6.a), that "`β^τ` is constant on `aH(a)`". -/
theorem adjointAverageFun_dadeMap_eq
    (τ : DadeMap (G := G) (k := ℂ) A L) (hτ : IsDadeMap hyp τ)
    (β : SupportedClassFunctions (G := G) ℂ A L) (a : {a : G // a ∈ A}) :
    adjointAverageFun hyp (τ β) ⟨a.1, hyp.subset_L a.2⟩ =
      (β : ClassFunction L ℂ) ⟨a.1, hyp.subset_L a.2⟩ := by
  classical
  -- unfold the averaging map at `a`
  simp only [adjointAverageFun]
  rw [dif_pos a.2]
  -- `τ β` is constant `= β(a)` on the coset `a · H(a)`
  have hconst : ∀ x : ↥(hyp.H ⟨a.1, a.2⟩),
      (τ β) (a.1 * (x : G)) = (β : ClassFunction L ℂ) ⟨a.1, hyp.subset_L a.2⟩ := by
    intro x
    have hx : a.1 * (x : G) ∈ hyp.hCoset a := ⟨(x : G), x.2, rfl⟩
    simpa using hτ.map_eq_of_mem_hCoset β a hx
  have hHne : (Nat.card (hyp.H ⟨a.1, a.2⟩) : ℂ) ≠ 0 := by
    have : 0 < Nat.card (hyp.H ⟨a.1, a.2⟩) := Nat.card_pos
    exact_mod_cast this.ne'
  rw [Finset.sum_congr rfl (fun x _ => hconst x), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hHne, one_mul]

/-- **Peterfalvi (2.6.a).**  Any map `τ` satisfying the (2.5) Dade-map equations
(`IsDadeMap`) and the (2.4.a) `L`-equivariance of the subgroups `H(a)`
(`HConjInvariant`) automatically preserves Peterfalvi's normalized inner product:

    `(α^τ, β^τ)_G = (α, β)_L`    for all `α, β ∈ CF(L, A)`.

This is the textbook proof of (2.6.a): since `β^τ` is constant on each coset
`aH(a)`, the (2.7) adjoint formula with `χ = β^τ` and `ψ = β` reduces the
`G`-inner product to the `L`-inner product `(α, β)_L`.  Together with
`IsDadeMap` this upgrades a Dade map to a full `DadeIsometryData` without
assuming the isometry property separately. -/
theorem isDadeIsometry_of_isDadeMap
    (τ : DadeMap (G := G) (k := ℂ) A L) (hτ : IsDadeMap hyp τ)
    (hconj : hyp.HConjInvariant) :
    IsDadeIsometry (k := ℂ) τ where
  inner_eq α β :=
    adjoint_formula hyp τ hτ hconj α (τ β) (β : ClassFunction L ℂ)
      (fun a => (adjointAverageFun_dadeMap_eq hyp τ hτ β a).symm)

/-- Bundle a Dade map satisfying the (2.5) equations into a `DadeIsometryData`,
using `isDadeIsometry_of_isDadeMap` to supply the (2.6.a) isometry property. -/
noncomputable def DadeIsometryData.ofIsDadeMap
    (τ : DadeMap (G := G) (k := ℂ) A L) (hτ : IsDadeMap hyp τ)
    (hconj : hyp.HConjInvariant) :
    DadeIsometryData (G := G) (k := ℂ) hyp where
  toDadeMap := τ
  isDadeMap := hτ
  isDadeIsometry := isDadeIsometry_of_isDadeMap hyp τ hτ hconj

@[simp] theorem DadeIsometryData.ofIsDadeMap_toDadeMap
    (τ : DadeMap (G := G) (k := ℂ) A L) (hτ : IsDadeMap hyp τ)
    (hconj : hyp.HConjInvariant) :
    (DadeIsometryData.ofIsDadeMap hyp τ hτ hconj).toDadeMap = τ :=
  rfl

/-- **The explicit Dade isometry of Peterfalvi (2.5)–(2.6.a).**  Bundles the pointwise
Dade map `dadeMap` (satisfying the (2.5) equations, `isDadeMap_dadeMap`) with the (2.6.a)
isometry property, supplied automatically by `isDadeIsometry_of_isDadeMap`.

This realizes the previously interface-only `DadeIsometryData` as an actual construction,
relative to Hypothesis (2.2) plus the (2.4.a) `L`-equivariance `HConjInvariant`.
Virtual-character preservation (2.6.b) — which upgrades this to a `FullDadeIsometryData` —
needs the (2.10) inclusion–exclusion and is tracked separately (issue 0040). -/
noncomputable def Hypothesis.dadeIsometryData (hconj : hyp.HConjInvariant) :
    DadeIsometryData (G := G) (k := ℂ) hyp :=
  DadeIsometryData.ofIsDadeMap hyp (hyp.dadeMap (k := ℂ))
    (hyp.isDadeMap_dadeMap (k := ℂ)) hconj

@[simp] theorem Hypothesis.dadeIsometryData_toDadeMap (hconj : hyp.HConjInvariant) :
    (hyp.dadeIsometryData hconj).toDadeMap = hyp.dadeMap (k := ℂ) :=
  rfl

/-! ### Peterfalvi (2.10), the pointwise inclusion–exclusion identity and `FullDadeIsometryData`

The (2.10) identity `α^τ = -∑_{C ∈ ℬ} (-1)^{|rep C|} Ind_{M(rep C)} α_{rep C}` is now assembled from
the support-side total `sum_mobiusTermCF_transversalRep_eq_neg` and the non-support vanishing
`induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport`, then fed through the bridge
`preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum` to construct the
`FullDadeIsometryData`. -/

open scoped Classical in
/-- **Peterfalvi (2.10), the pointwise identity.**  For a supported class function `α ∈ CF(L, A)`,
the Dade map equals the negated transversal sum of orbit-averaging summands:

    `α^τ(g) = -∑_{C ∈ ℬ} mobiusTermCF (rep C) (g)`,

where `mobiusTermCF (rep C) = (-1)^{|rep C|} Ind_{M(rep C)}^G α_{rep C}`.  On the Dade support
(`g ∈ (aH(a))^G`) the transversal sum is `-α(a) = -α^τ(g)`
(`sum_mobiusTermCF_transversalRep_eq_neg`); off the support both sides vanish — `α^τ(g) = 0` by the
(2.5) definition, and each `Ind_{M(rep C)} α_{rep C}(g) = 0` by
`induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport`. -/
theorem Hypothesis.dadeMap_eq_neg_sum_mobiusTermCF (hconj : hyp.HConjInvariant)
    (α : SupportedClassFunctions (G := G) ℂ A L) :
    letI := hyp.conjFinsetAction
    letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
    hyp.dadeMap (k := ℂ) α
      = (⟨fun g => -∑ C : hyp.conjClassQuotient,
            hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g (hyp.transversalRep C),
          by
            intro g x
            classical
            simp only [neg_inj]
            refine Finset.sum_congr rfl fun C _ => ?_
            by_cases hC : (hyp.transversalRep C).Nonempty
            · letI : Invertible (Nat.card (mBSubgroup hyp (hyp.transversalRep C) hC) : ℂ) :=
                invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
              rw [hyp.mobiusTermCF_of_nonempty hconj _ g hC,
                hyp.mobiusTermCF_of_nonempty hconj _ (x * g * x⁻¹) hC]
              congr 1
              rw [hyp.induceAlphaBTerm_apply hconj _ hC, hyp.induceAlphaBTerm_apply hconj _ hC]
              exact (ClassFunction.induce (mBSubgroup hyp (hyp.transversalRep C) hC)
                (alphaB hyp hconj hC (α : ClassFunction L ℂ))).2 g x
            · rw [hyp.mobiusTermCF_of_not_nonempty hconj _ g hC,
                hyp.mobiusTermCF_of_not_nonempty hconj _ (x * g * x⁻¹) hC]⟩
          : ClassFunction G ℂ) := by
  classical
  letI := hyp.conjFinsetAction
  letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
  refine ClassFunction.ext fun g => ?_
  show hyp.dadeValue (α : SupportedClassFunctions (G := G) ℂ A L) g
    = -∑ C : hyp.conjClassQuotient,
        hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g (hyp.transversalRep C)
  by_cases hg : g ∈ hyp.dadeSupport
  · -- support side: the transversal sum is `-α(a)`.
    obtain ⟨a, h, hh, hga⟩ := hyp.mem_dadeSupport_iff.mp hg
    rw [hyp.dadeValue_eq α hh hga,
      hyp.sum_mobiusTermCF_transversalRep_eq_neg hconj α hh hga, neg_neg]
  · -- non-support side: both sides are `0`.
    rw [hyp.dadeValue_of_not_mem_dadeSupport α hg]
    rw [show (∑ C : hyp.conjClassQuotient,
          hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g (hyp.transversalRep C)) = 0 from ?_,
      neg_zero]
    refine Finset.sum_eq_zero fun C _ => ?_
    by_cases hC : (hyp.transversalRep C).Nonempty
    · letI : Invertible (Nat.card (mBSubgroup hyp (hyp.transversalRep C) hC) : ℂ) :=
        invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      rw [hyp.mobiusTermCF_of_nonempty hconj _ g hC, hyp.induceAlphaBTerm_apply hconj _ hC,
        hyp.induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport hconj hC α hg, mul_zero]
    · rw [hyp.mobiusTermCF_of_not_nonempty hconj _ g hC]

open scoped Classical in
/-- The transversal sum of `mobiusTermCF` reindexes over the `Finset` of nonempty subsets that are
their own conjugacy-class representative (`transversalRep (mk'' B) = B`), with the summand the
packaged induced character:

    `∑_{C ∈ ℬ} mobiusTermCF (rep C) (g) = ∑_{p ∈ s} (-1)^{|p.1|} · Ind_{M(p)}^G α_p (g)`,

`s` ranging over `{p : {B // B.Nonempty} // transversalRep (mk'' p.1) = p.1}` (as a `Finset`).
This converts the (2.10) identity into the `∑ c_p • induceAlphaBTerm p` shape demanded by the bridge
`preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum`.  The bijection sends a class `C` with
nonempty representative to `⟨rep C, _⟩` and back via `p ↦ mk'' p.1` (`Quotient.out_eq'`); the empty
classes contribute `0` on the left and are excluded on the right. -/
theorem Hypothesis.sum_mobiusTermCF_transversalRep_eq_sum_subtype (hconj : hyp.HConjInvariant)
    (α : SupportedClassFunctions (G := G) ℂ A L) (g : G) :
    letI := hyp.conjFinsetAction
    letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
    letI : Fintype {B : Finset {a : G // a ∈ A} // B.Nonempty} := Fintype.ofFinite _
    (∑ C : hyp.conjClassQuotient,
        hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g (hyp.transversalRep C))
      = ∑ p ∈ (Finset.univ : Finset {B : Finset {a : G // a ∈ A} // B.Nonempty}).filter
          (fun p => hyp.transversalRep (Quotient.mk'' p.1) = p.1),
          ((-1 : ℂ) ^ p.1.card) * hyp.induceAlphaBTerm hconj (α : ClassFunction L ℂ) p g := by
  classical
  letI := hyp.conjFinsetAction
  letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
  letI : Fintype {B : Finset {a : G // a ∈ A} // B.Nonempty} := Fintype.ofFinite _
  -- restrict the left sum to nonempty-rep classes (empty reps contribute `0`).
  rw [← Finset.sum_filter_of_ne (p := fun C : hyp.conjClassQuotient =>
        (hyp.transversalRep C).Nonempty) ?_]
  · -- now bijection between `{C : rep C nonempty}` and the fixed-point subtype Finset.
    refine Finset.sum_bij'
      (i := fun C hC => (⟨hyp.transversalRep C, by
          rw [Finset.mem_filter] at hC; exact hC.2⟩
        : {B : Finset {a : G // a ∈ A} // B.Nonempty}))
      (j := fun p _ => (Quotient.mk'' p.1 : hyp.conjClassQuotient))
      ?_ ?_ ?_ ?_ ?_
    · -- `i C ∈ s`
      intro C hC
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show hyp.transversalRep (Quotient.mk'' (hyp.transversalRep C)) = hyp.transversalRep C
      simp only [transversalRep, Quotient.out_eq']
    · -- `j p ∈ filter (rep nonempty)`
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hp.2]; exact p.2
    · -- left inverse: `mk'' (rep C) = C`
      intro C hC
      show Quotient.mk'' (hyp.transversalRep C) = C
      simp only [transversalRep, Quotient.out_eq']
    · -- right inverse: `⟨rep (mk'' p.1), _⟩ = p`
      intro p hp
      rw [Finset.mem_filter] at hp
      apply Subtype.ext
      exact hp.2
    · -- summand agreement
      intro C hC
      rw [Finset.mem_filter] at hC
      rw [hyp.mobiusTermCF_of_nonempty hconj _ g hC.2]
  · -- the dropped terms (empty reps) are zero: if the summand is nonzero, the rep is nonempty.
    intro C _ hC
    by_contra hne
    exact hC (hyp.mobiusTermCF_of_not_nonempty hconj _ g hne)

/-- Evaluation of a `Finset` sum of class functions is the sum of the evaluations. -/
private theorem classFunction_finset_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → ClassFunction G ℂ) (g : G) :
    (∑ p ∈ s, f p) g = ∑ p ∈ s, f p g := by
  classical
  refine s.induction_on (by simp) ?_
  intro p s' hps' ih
  rw [Finset.sum_insert hps', Finset.sum_insert hps', ClassFunction.add_apply, ih]

open scoped Classical in
/-- **Peterfalvi (2.6.b).**  The complex Dade map preserves virtual characters:
`τ : ℤ[Irr L, A] → ℤ[Irr G]`.

This is the culmination of the (2.10) inclusion–exclusion.  Feeding the pointwise identity
`α^τ = -∑_{C ∈ ℬ} (-1)^{|rep C|} Ind_{M(rep C)} α_{rep C}` (`dadeMap_eq_neg_sum_mobiusTermCF`,
reindexed over the representative subtype by `sum_mobiusTermCF_transversalRep_eq_sum_subtype`) into
the bridge `preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum`: the right-hand side is a
`ℤ`-linear combination (`c p = -(-1)^{|p.1|}`) of inclusion–exclusion summands `induceAlphaBTerm`,
each a virtual character (`induceAlphaBTerm_mem_ZIrr`), so `α^τ ∈ ℤ[Irr G]`. -/
theorem Hypothesis.preservesVirtualCharacters_dadeMap (hconj : hyp.HConjInvariant) :
    PreservesVirtualCharacters (G := G) (A := A) (L := L) (hyp.dadeMap (k := ℂ)) := by
  refine preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum hconj ?_
  intro α _
  letI := hyp.conjFinsetAction
  letI : Fintype hyp.conjClassQuotient := Fintype.ofFinite _
  letI : Fintype {B : Finset {a : G // a ∈ A} // B.Nonempty} := Fintype.ofFinite _
  refine ⟨(Finset.univ : Finset {B : Finset {a : G // a ∈ A} // B.Nonempty}).filter
      (fun p => hyp.transversalRep (Quotient.mk'' p.1) = p.1),
    fun p => -((-1 : ℤ) ^ p.1.card), ?_⟩
  refine ClassFunction.ext fun g => ?_
  rw [hyp.dadeMap_eq_neg_sum_mobiusTermCF hconj α]
  show -∑ C : hyp.conjClassQuotient,
      hyp.mobiusTermCF hconj (α : ClassFunction L ℂ) g (hyp.transversalRep C)
    = (∑ p ∈ (Finset.univ : Finset {B : Finset {a : G // a ∈ A} // B.Nonempty}).filter
        (fun p => hyp.transversalRep (Quotient.mk'' p.1) = p.1),
        (-((-1 : ℤ) ^ p.1.card)) • hyp.induceAlphaBTerm hconj (α : ClassFunction L ℂ) p) g
  rw [hyp.sum_mobiusTermCF_transversalRep_eq_sum_subtype hconj α g,
    classFunction_finset_sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  -- `(-(-1)^|p.1| • Ind p) g = -((-1)^|p.1| · Ind p g)`.
  rw [show (-((-1 : ℤ) ^ p.1.card)) • hyp.induceAlphaBTerm hconj (α : ClassFunction L ℂ) p
      = (((-((-1 : ℤ) ^ p.1.card) : ℤ) : ℂ)) • hyp.induceAlphaBTerm hconj (α : ClassFunction L ℂ) p
      from by rw [Int.cast_smul_eq_zsmul], ClassFunction.smul_apply]
  push_cast
  ring

/-- **Peterfalvi (2.6).**  The full complex Dade-isometry package: the (2.5) Dade-map equations, the
(2.6.a) normalized isometry, and the (2.6.b) virtual-character preservation, all constructed from
Hypothesis (2.2) plus the (2.4.a) `L`-equivariance `HConjInvariant`.

This is the honest construction of `FullDadeIsometryData` (no longer an interface assumption):
`toDadeIsometryData` is the `dadeIsometryData` built from the explicit (2.5) Dade map, and
`preserves_virtualCharacters` is the (2.10) inclusion–exclusion result
`preservesVirtualCharacters_dadeMap`. -/
noncomputable def Hypothesis.fullDadeIsometryData (hconj : hyp.HConjInvariant) :
    FullDadeIsometryData (G := G) hyp where
  toDadeIsometryData := hyp.dadeIsometryData hconj
  preserves_virtualCharacters := by
    rw [hyp.dadeIsometryData_toDadeMap hconj]
    exact hyp.preservesVirtualCharacters_dadeMap hconj

end AdjointFormula

end DadeMap

end OddOrder.Peterfalvi.S04

