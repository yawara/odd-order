import OddOrder.Peterfalvi.S09_NonexistenceCertain.NormalCase

/-!
# QuadraticTerm

Prefix-split from `OddOrder.Peterfalvi.S09_NonexistenceCertain.CoherenceFormula` (2000-line limit,
issue 0103 第 2 パス).
-/

/-!
# Peterfalvi (7.8) — coherence-based formula for χ^ρ

Split from the former monolithic `OddOrder.Peterfalvi.S09_NonexistenceCertain` (directory split,
issue 0103).
-/
namespace OddOrder.Peterfalvi.S09
open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)
open OddOrder.GroupTheory (IsTISubset)
open OddOrder.RepresentationTheory
open scoped Pointwise

variable {G : Type*} [Group G]


section Section_7_8

/-! ### (7.8): the coherence-based formula for `χ^ρ`

Bundles Hypothesis (7.6) with the §7 coherence input:

* The family `T = {ζ_0, ..., ζ_n}` contains the **induced principal character**
  `Ind 1_H = Ind_H^L 1_H` at some index `ind1H`.
* The remaining set `S = T \ {Ind 1_H}` is **coherent**, with isometric extension
  `ν : ℤ[S] → ℤ[Irr G]` (represented as an integral linear map on the ambient
  `ClassFunction L ℂ` space).
* There is a **distinguished** `ζ ∈ S` with `ζ(1) = (Ind 1_H)(1)` (= `e = [L:H]`);
  equivalently `(Ind 1_H − ζ)(1) = 0`, so `Ind 1_H − ζ ∈ CF(L,A)`.
* `β := τ (Ind 1_H − ζ) ∈ CF(G)` (Dade image of the supported difference).

The headline output (Peterfalvi (7.8.c), p. 40) is:

* (i)  For χ ∈ Irr(G) with `χ ⊥ S^ν`, `χ^ρ(x) = star (β, χ)_G` for every `x ∈ A`.
* (ii) `‖χ^ρ‖² = (|A|/|L|) · (β, χ)_G · star (β, χ)_G`.

(i) — `chiRho_eq_inner_beta_on_A` — is carried as the structural certificate
`chiRho_eq_inner_beta` inside `Hypothesis78` (the coherence-based derivation
from (7.7.a) is the subject of Peterfalvi (7.8.c) and is not yet formalized).
(ii) — `chiRho_norm_sq_eq_card_ratio_mul` — is then a direct corollary of (i):
the inner product is `(1/|L|) Σ_{l : L} χ^ρ(l) · star (χ^ρ(l))`; off `A` the
summands vanish, on `A` each equals `star (β,χ) · (β,χ)`, and the number of
`l ∈ L` with `(l : G) ∈ A` equals `|A|` (since `A ⊆ L`). -/

/-- **Peterfalvi (7.8) Hypothesis.**  Hypothesis (7.6) together with the
coherence input for `S = T \ {Ind 1_H}` and a distinguished `ζ ∈ S` of degree
`e = [L:H] = (Ind 1_H)(1)`.

The (7.8.c) conclusion (the pointwise identity on `A`) is carried as the
structural certificate `chiRho_eq_inner_beta`. -/
structure Hypothesis78 (G : Type*) [Group G] [Fintype G]
    (A : Set G) (L : Subgroup G) [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- The underlying Hypothesis (7.6). -/
  hyp76 : Hypothesis76 G A L
  /-- Index of the induced principal character `Ind 1_H` in `T = {ζ_0, ..., ζ_n}`. -/
  ind1H : Fin (hyp76.n + 1)
  /-- Index of the distinguished `ζ ∈ S = T \ {Ind 1_H}`. -/
  zetaDistinct : Fin (hyp76.n + 1)
  /-- `ζ ≠ Ind 1_H`, so the distinguished `ζ` lies in `S`. -/
  zetaDistinct_ne_ind1H : zetaDistinct ≠ ind1H
  /-- `ζ(1) = (Ind 1_H)(1)` (= `e = [L:H]`).  Makes the difference
  `Ind 1_H − ζ` vanish at `1`, hence supported on `A = H \ {1}`. -/
  zeta_one_eq_ind1H_one :
    hyp76.zeta zetaDistinct (1 : L) = hyp76.zeta ind1H (1 : L)
  /-- `Ind 1_H − ζ` is supported on `A`.  Carried so the supported-class-function
  `β` can be formed cleanly. -/
  diff_support : (hyp76.zeta ind1H - hyp76.zeta zetaDistinct).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  /-- The coherent isometric extension `ν : ℤ[S] → ℤ[Irr G]`, presented as an
  `ℤ`-linear map on the ambient class-function space. -/
  nu : ClassFunction L ℂ →ₗ[ℤ] ClassFunction G ℂ
  /-- `ν` is a *family* isometry: it preserves the Gram matrix of the coherent
  family `{ζ_i : i ≠ ind1H}`.  This is the genuine content of coherence (Dade);
  a *global* isometry `CF(L) → CF(G)` need not exist (it would be an isometric
  embedding, but `dim CF(L)` can exceed `dim CF(G)`). -/
  nu_isometry : ∀ i j : Fin (hyp76.n + 1), i ≠ ind1H → j ≠ ind1H →
    ClassFunction.inner (nu (hyp76.zeta i)) (nu (hyp76.zeta j)) =
      ClassFunction.inner (hyp76.zeta i) (hyp76.zeta j)
  /-- **Peterfalvi (7.8.c.i) certificate.**  For χ ∈ Irr G orthogonal to `S^ν`
  (i.e. `(χ, ν ζ_i)_G = 0` for every `i ≠ ind1H`), and `x ∈ A`,
  `χ^ρ(x) = star (β, χ)_G`, where `β = τ (Ind 1_H − ζ) ∈ CF(G)`.

  Encodes the coherence-based reduction of the (7.7.a) decomposition: under
  `χ ⊥ S^ν`, the inner products `(ψ_i^τ, χ) = (ν(ψ_i), χ)` collapse to a
  single contribution proportional to `β`. -/
  chiRho_eq_inner_beta : ∀ (χ : ClassFunction G ℂ),
    IsIrreducibleCharacter χ →
    (∀ i : Fin (hyp76.n + 1), i ≠ ind1H →
      ClassFunction.inner χ (nu (hyp76.zeta i)) = 0) →
    ∀ {x : L}, (x : G) ∈ A →
    hyp76.hyp71.chiRho χ x =
      star (ClassFunction.inner
        (hyp76.hyp71.τ
          ⟨hyp76.zeta ind1H - hyp76.zeta zetaDistinct, diff_support⟩) χ)

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype L]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- `Ind 1_H − ζ ∈ CF(L,A)`, the supported difference defining `β`. -/
noncomputable def indMinusZetaSupp (H78 : Hypothesis78 G A L) :
    OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L :=
  ⟨H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct, H78.diff_support⟩

/-- **`β = (Ind 1_H − ζ)^τ ∈ CF(G)`.** -/
noncomputable def beta (H78 : Hypothesis78 G A L) : ClassFunction G ℂ :=
  H78.hyp76.hyp71.τ H78.indMinusZetaSupp

theorem beta_def (H78 : Hypothesis78 G A L) :
    H78.beta =
      H78.hyp76.hyp71.τ
        ⟨H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct,
          H78.diff_support⟩ :=
  rfl

/-- The Dade image defining `β` is a virtual character whenever the source
difference `Ind 1_H - ζ` is a virtual character on `L`. -/
theorem beta_mem_ZIrr_of_sourceDiff_mem_ZIrr (H78 : Hypothesis78 G A L)
    (hdiffZ :
      H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L) :
    H78.beta ∈ ZIrr G := by
  have hτ : H78.hyp76.hyp71.τ = H78.hyp76.hyp71.hyp.dadeMap (k := ℂ) :=
    OddOrder.Peterfalvi.S04.IsDadeMap.unique H78.hyp76.hyp71.isDadeMap
      (H78.hyp76.hyp71.hyp.isDadeMap_dadeMap (k := ℂ))
  have hvirt :=
    (H78.hyp76.hyp71.hyp.fullDadeIsometryData
      H78.hyp76.hyp71.hConjInvariant).maps_virtualCharacter H78.indMinusZetaSupp hdiffZ
  rw [beta, hτ]
  rwa [show (H78.hyp76.hyp71.hyp.fullDadeIsometryData
        H78.hyp76.hyp71.hConjInvariant).toDadeMap =
        H78.hyp76.hyp71.hyp.dadeMap (k := ℂ) from
      H78.hyp76.hyp71.hyp.dadeIsometryData_toDadeMap H78.hyp76.hyp71.hConjInvariant] at hvirt

/-- The source difference `Ind 1_H - ζ` is virtual when the `Ind 1_H`
source term is virtual and the distinguished `ζ` is irreducible. -/
theorem sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L :=
  Submodule.sub_mem _ hindZ hzeta_irr.mem_ZIrr

/-- The source difference `Ind 1_H - ζ` is virtual when both source terms are
irreducible characters of `L`. -/
theorem sourceDiff_mem_ZIrr_of_irreducible (H78 : Hypothesis78 G A L)
    (hind_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.ind1H))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L :=
  H78.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    hind_irr.mem_ZIrr hzeta_irr

/-- Virtuality of `Ind 1_H` and irreducibility of `ζ` supply the
virtual-character input needed by the Dade bridge for `β`. -/
theorem beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.beta ∈ ZIrr G :=
  H78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr
    (H78.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible hindZ hzeta_irr)

/-- Irreducibility of the two source terms supplies the virtual-character input
needed by the Dade bridge for `β`. -/
theorem beta_mem_ZIrr_of_irreducible_sourceDiff (H78 : Hypothesis78 G A L)
    (hind_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.ind1H))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.beta ∈ ZIrr G :=
  H78.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    hind_irr.mem_ZIrr hzeta_irr

/-- The coherent source set `S = T \ {Ind 1_H}` from Peterfalvi (7.8),
presented as a set of class functions on `L`. -/
def sourceSet (H78 : Hypothesis78 G A L) : Set (ClassFunction L ℂ) :=
  {φ | ∃ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H ∧ H78.hyp76.zeta i = φ}

/-- Each non-`Ind 1_H` source character belongs to the coherent source set `S`. -/
theorem zeta_mem_sourceSet (H78 : Hypothesis78 G A L)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H) :
    H78.hyp76.zeta i ∈ H78.sourceSet :=
  ⟨i, hi, rfl⟩

/-- The distinguished `ζ` belongs to the coherent source set `S`. -/
theorem zetaDistinct_mem_sourceSet (H78 : Hypothesis78 G A L) :
    H78.hyp76.zeta H78.zetaDistinct ∈ H78.sourceSet :=
  H78.zeta_mem_sourceSet H78.zetaDistinct_ne_ind1H

/-- S09-facing constructor for the generic S08 weighted Ind-chain package.

A concrete S07 coherent witness over the source set `S = T \ {Ind 1_H}` gives
Peterfalvi's Ind-chain data with output family `χ_t = ν ζ_t`, provided the chosen
source family lies in `S` and the scaled differences lie in the supported
lattice where the coherent extension agrees with the original map `τ`. -/
noncomputable def indChainDecomposition_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    OddOrder.Peterfalvi.S08.IndChainDecomposition (L := L) (G := G) τ ζ d where
  χ t := H78.nu (ζ t)
  norm_one t := by
    rw [hnu, hcoh.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem t)), hζ_norm]
  pairwise_inner_zero t u htu := by
    rw [hnu, hcoh.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem u)), hζ_pairwise htu]
  d_zero := hd_zero
  image_eq t := by
    rw [← hcoh.extends_on_supported _ (hsupp t), LinearMap.map_sub, map_zsmul, ← hnu]

open scoped Classical in
/-- S09-facing `IndChainDecomposition` constructor from an arbitrary coherent
source family.

This is the set-parametric form of
`indChainDecomposition_of_isCoherent`: the coherent set need not be
`H78.sourceSet`.  It is the bridge used when §8 has already identified the
source family as a Sibley set `hyp.S`, while the §9 notation still wants the
output family to be exactly `χ_t = H78.nu (ζ_t)`. -/
noncomputable def indChainDecomposition_of_coherenceOn
    (H78 : Hypothesis78 G A L)
    {S : Set (ClassFunction L ℂ)} {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ S A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ S)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A_prime) :
    OddOrder.Peterfalvi.S08.IndChainDecomposition (L := L) (G := G) τ ζ d where
  χ t := H78.nu (ζ t)
  norm_one t := by
    rw [hnu, hcoh.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem t)), hζ_norm]
  pairwise_inner_zero t u htu := by
    rw [hnu, hcoh.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem u)), hζ_pairwise htu]
  d_zero := hd_zero
  image_eq t := by
    rw [← hcoh.extends_on_supported _ (hsupp t), LinearMap.map_sub, map_zsmul, ← hnu]

set_option linter.style.longLine false
open scoped Classical in
/-- **Peterfalvi (6.8.1) → (7.10), Frobenius/base-anchor form.**

The S08 Frobenius branch constructs the full Sibley coherence target from the
base-anchor common-index `X`-chain data and generator-level mixed-inner glue.
This constructor feeds that coherence witness directly into the S09
`Hypothesis78` Ind-chain package, fixing the output family as
`χ_t = H78.nu (ζ_t)` rather than leaving it as an anonymous coherence extension.

The remaining inputs are the genuine (6.6)/(6.8) payload: the `X`-chain step
data, the `ν` agreement/mixed-inner facts for the final glue, and the chosen
orthonormal source chain in the Xset/H-prime union with supported scaled differences. -/
noncomputable def
    indChainDecomposition_of_sibley_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData
    (H78 : Hypothesis78 G A L)
    {H : Subgroup L} [Invertible (Nat.card ↥H : ℂ)]
    (hyp : OddOrder.Peterfalvi.S08.SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → OddOrder.RepresentationTheory.IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      H78.nu x =
        (hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
          hF hXne hstepData).extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, H78.nu y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (H78.nu x) (H78.nu y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.Peterfalvi.S08.sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.Peterfalvi.S08.sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.Peterfalvi.S08.sharpImage H) L)))
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction ↥L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.Peterfalvi.S08.sharpImage H) L)) :
    OddOrder.Peterfalvi.S08.IndChainDecomposition (L := ↥L) (G := G) hyp.tau ζ d := by
  let hX :=
    hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
      hF hXne hstepData
  let hcoh : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.Peterfalvi.S08.sharpImage H) L) :=
    OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq
      hX hyp.coherentYset H78.nu hagreeX hagreeY
      (hyp.inner_span_Xset_Yset_eq_zero_of_frobenius hF) hmixed hgen
  exact H78.indChainDecomposition_of_coherenceOn hcoh (by rfl)
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp

set_option linter.style.longLine true

/-- H78-facing per-term Ind equation in the constructed Ind-chain package. -/
theorem indChain_image_eq_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime)
    (t : Fin n) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    τ (ζ t - (d t) • ζ 0) = data.χ t - (d t) • data.χ 0 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change τ (ζ t - (d t) • ζ 0) = data.χ t - (d t) • data.χ 0
  exact data.image_eq t

/-- H78-facing reference-index vanishing for the per-term Ind equation. -/
theorem indChain_image_eq_zero_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    τ (ζ 0 - (d 0) • ζ 0) = 0 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change τ (ζ 0 - (d 0) • ζ 0) = 0
  exact data.image_eq_zero

/-- H78-facing orthonormality formula for the Ind-chain output family. -/
theorem indChain_inner_chi_eq_ite_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime)
    (t u : Fin n) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    ClassFunction.inner (data.χ t) (data.χ u) = if t = u then 1 else 0 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change ClassFunction.inner (data.χ t) (data.χ u) = if t = u then 1 else 0
  exact data.inner_chi_eq_ite t u

/-- H78-facing coefficient recovery for the weighted output sum. -/
theorem indChain_inner_chi_weightedOutput_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime)
    (t : Fin n) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    ClassFunction.inner (data.χ t) data.weightedOutput = (d t : ℂ) := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change ClassFunction.inner (data.χ t) data.weightedOutput = (d t : ℂ)
  exact data.inner_chi_weightedOutput t

set_option linter.style.longLine false in
/-- H78-facing raw weighted Ind equation before collecting the reference term. -/
theorem indChain_image_weightedDifferenceInput_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    τ data.weightedDifferenceInput =
      ∑ t : Fin n, (d t) • (data.χ t - (d t) • data.χ 0) := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change τ data.weightedDifferenceInput =
    ∑ t : Fin n, (d t) • (data.χ t - (d t) • data.χ 0)
  exact data.image_weightedDifferenceInput

set_option linter.style.longLine false in
/-- H78-facing normalized weighted Ind equation, with the integer-square coefficient.

This consumes the same concrete S07 coherence witness as
`indChainDecomposition_of_isCoherent`, then applies the S08 weighted source-difference
image identity to the resulting Ind-chain package. -/
theorem
    indChain_image_weightedDifferenceInput_eq_weightedOutput_sub_sum_sq_smul_chi_zero_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    τ data.weightedDifferenceInput =
      data.weightedOutput - (∑ t : Fin n, (d t : ℂ) ^ 2) • data.χ 0 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change τ data.weightedDifferenceInput =
    data.weightedOutput - (∑ t : Fin n, (d t : ℂ) ^ 2) • data.χ 0
  exact data.image_weightedDifferenceInput_eq_weightedOutput_sub_sum_sq_smul_chi_zero

set_option linter.style.longLine false in
/-- H78-facing normalized weighted Ind equation, with the Parseval norm coefficient. -/
theorem
    indChain_image_weightedDifferenceInput_eq_weightedOutput_sub_norm_smul_chi_zero_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    τ data.weightedDifferenceInput =
      data.weightedOutput -
        ClassFunction.inner data.weightedOutput data.weightedOutput • data.χ 0 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change τ data.weightedDifferenceInput =
    data.weightedOutput -
      ClassFunction.inner data.weightedOutput data.weightedOutput • data.χ 0
  exact data.image_weightedDifferenceInput_eq_weightedOutput_sub_norm_smul_chi_zero

/-- H78-facing complex scalar-coefficient form for the weighted Ind-chain source
difference. -/
theorem indChain_inner_chi_zero_image_weightedDifferenceInput_eq_one_sub_norm_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput) =
      1 - ClassFunction.inner data.weightedOutput data.weightedOutput := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput) =
    1 - ClassFunction.inner data.weightedOutput data.weightedOutput
  exact data.inner_chi_zero_image_weightedDifferenceInput_eq_one_sub_norm

set_option linter.style.longLine false in
/-- H78-facing reference coefficient of the raw weighted Ind image. -/
theorem indChain_inner_chi_zero_image_weightedDifferenceInput_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput) =
      1 - ∑ t : Fin n, (d t : ℂ) ^ 2 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput) =
    1 - ∑ t : Fin n, (d t : ℂ) ^ 2
  exact data.inner_chi_zero_image_weightedDifferenceInput

/-- H78-facing complex Parseval form for the weighted output. -/
theorem indChain_weightedOutput_inner_self_eq_sum_sq_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    ClassFunction.inner data.weightedOutput data.weightedOutput =
      ∑ t : Fin n, (d t : ℂ) ^ 2 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change ClassFunction.inner data.weightedOutput data.weightedOutput =
    ∑ t : Fin n, (d t : ℂ) ^ 2
  exact data.weightedOutput_inner_self_eq_sum_sq

/-- H78-facing real Parseval form for the S08 weighted Ind-chain output.

This consumes the same concrete S07 coherence witness as
`indChainDecomposition_of_isCoherent`, then immediately applies the S08 weighted
output norm identity to the resulting Ind-chain package. -/
theorem indChain_weightedOutput_inner_self_re_eq_sum_sq_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    (ClassFunction.inner data.weightedOutput data.weightedOutput).re =
      ∑ t : Fin n, (d t : ℝ) ^ 2 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change (ClassFunction.inner data.weightedOutput data.weightedOutput).re =
    ∑ t : Fin n, (d t : ℝ) ^ 2
  exact data.weightedOutput_inner_self_re_eq_sum_sq

/-- H78-facing lower bound for the weighted output norm from the normalized
coefficient `d 0 = 1`. -/
theorem indChain_one_le_weightedOutput_inner_self_re_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    1 ≤ (ClassFunction.inner data.weightedOutput data.weightedOutput).re := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change 1 ≤ (ClassFunction.inner data.weightedOutput data.weightedOutput).re
  exact data.one_le_weightedOutput_inner_self_re

/-- H78-facing real scalar-coefficient form for the weighted Ind-chain source
difference. -/
theorem indChain_inner_chi_zero_image_weightedDifferenceInput_re_eq_one_sub_sum_sq_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    (ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput)).re =
      1 - ∑ t : Fin n, (d t : ℝ) ^ 2 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change (ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput)).re =
    1 - ∑ t : Fin n, (d t : ℝ) ^ 2
  exact data.inner_chi_zero_image_weightedDifferenceInput_re_eq_one_sub_sum_sq

/-- H78-facing nonpositivity form for the weighted Ind-chain source difference. -/
theorem indChain_inner_chi_zero_image_weightedDifferenceInput_re_nonpos_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ H78.sourceSet)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u →
      ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) H78.sourceSet A_prime) :
    let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
      hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
    (ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput)).re ≤ 0 := by
  let data := H78.indChainDecomposition_of_isCoherent hcoh hnu
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp
  change (ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput)).re ≤ 0
  exact data.inner_chi_zero_image_weightedDifferenceInput_re_nonpos

/-- If the abstract `ν` carried by `Hypothesis78` is identified with a concrete
S07 coherent extension, then `ν` sends the coherent lattice `ℤ[S]` into virtual
irreducible characters of `G`.

This is the S09-facing bridge to the real S07 coherence construction: it adds no
new field to `Hypothesis78`, but lets downstream (7.8)/(7.9) arguments use
`IsCoherent.extension_mem_ZIrr` whenever the concrete witness is available. -/
theorem nu_mem_ZIrr_of_isCoherent (H78 : Hypothesis78 G A L)
    {S : Set (ClassFunction L ℂ)} {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ S A_prime)
    (hnu : H78.nu = hcoh.extension)
    {φ : ClassFunction L ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := L) S) :
    H78.nu φ ∈ ZIrr G := by
  rw [hnu]
  exact hcoh.extension_mem_ZIrr φ hφ

/-- Generator form of `nu_mem_ZIrr_of_isCoherent`: a member of the coherent set
itself is automatically in its `ℤ`-span. -/
theorem nu_mem_ZIrr_of_isCoherent_of_mem (H78 : Hypothesis78 G A L)
    {S : Set (ClassFunction L ℂ)} {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ S A_prime)
    (hnu : H78.nu = hcoh.extension)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ S) :
    H78.nu φ ∈ ZIrr G :=
  H78.nu_mem_ZIrr_of_isCoherent hcoh hnu (Submodule.subset_span hφ)

/-- If the concrete S07 coherent witness is built over the source set
`S = T \ {Ind 1_H}`, then every non-`Ind 1_H` indexed source character has
virtual-irreducible image under `ν`. -/
theorem nu_zeta_mem_ZIrr_of_isCoherent (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H) :
    H78.nu (H78.hyp76.zeta i) ∈ ZIrr G :=
  H78.nu_mem_ZIrr_of_isCoherent_of_mem hcoh hnu (H78.zeta_mem_sourceSet hi)

/-- Distinguished-`ζ` specialization of `nu_zeta_mem_ZIrr_of_isCoherent`. -/
theorem nu_zetaDistinct_mem_ZIrr_of_isCoherent (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension) :
    H78.nu (H78.hyp76.zeta H78.zetaDistinct) ∈ ZIrr G :=
  H78.nu_zeta_mem_ZIrr_of_isCoherent hcoh hnu H78.zetaDistinct_ne_ind1H

/-- The Dade image defining `β` is supported on the corresponding Dade support. -/
theorem beta_support_subset_dadeSupport (H78 : Hypothesis78 G A L) :
    H78.beta.support ⊆ H78.hyp76.hyp71.hyp.dadeSupport := by
  intro g hg
  by_contra hnot
  exact hg (by
    rw [H78.beta_def]
    exact H78.hyp76.hyp71.isDadeMap.map_eq_zero_of_not_mem_dadeSupport
      H78.indMinusZetaSupp g hnot)

/-- The residual `Δ = β - 1_G + ζ^ν` used in Peterfalvi (7.9). -/
noncomputable def delta (H78 : Hypothesis78 G A L) : ClassFunction G ℂ :=
  H78.beta - Hypothesis71.constOne G +
    H78.nu (H78.hyp76.zeta H78.zetaDistinct)

/-- If `β` is a virtual character and `ν` is a concrete coherent extension on
`S = T \ {Ind 1_H}`, then the residual `Δ = β - 1_G + νζ` is virtual. -/
theorem delta_mem_ZIrr_of_beta_mem_ZIrr_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hbeta : H78.beta ∈ ZIrr G) :
    H78.delta ∈ ZIrr G := by
  have hconst : Hypothesis71.constOne G ∈ ZIrr G := by
    have htriv : OddOrder.RepresentationTheory.trivialClassFunction G ∈ ZIrr G :=
      OddOrder.RepresentationTheory.trivialClassFunction_isIrreducible.mem_ZIrr
    simpa [Hypothesis71.constOne, OddOrder.RepresentationTheory.trivialClassFunction]
      using htriv
  have hzeta : H78.nu (H78.hyp76.zeta H78.zetaDistinct) ∈ ZIrr G :=
    H78.nu_zetaDistinct_mem_ZIrr_of_isCoherent hcoh hnu
  simpa [delta] using Submodule.add_mem (ZIrr G)
    (Submodule.sub_mem (ZIrr G) hbeta hconst) hzeta

/-- If the `Ind 1_H` source term is virtual and the distinguished `ζ` is
irreducible, then coherence supplies the residual virtual character `Δ`. -/
theorem delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.delta ∈ ZIrr G :=
  H78.delta_mem_ZIrr_of_beta_mem_ZIrr_of_isCoherent hcoh hnu
    (H78.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible hindZ hzeta_irr)

/-- Source irreducibility and coherence supply the full virtual-character
residual `Δ = β - 1_G + νζ`. -/
theorem delta_mem_ZIrr_of_irreducible_sourceDiff_and_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hind_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.ind1H))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.delta ∈ ZIrr G :=
  H78.delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    hcoh hnu hind_irr.mem_ZIrr hzeta_irr

/-- The defining rearrangement `β = 1_G - ζ^ν + Δ`. -/
theorem beta_eq_constOne_sub_zetaImage_add_delta (H78 : Hypothesis78 G A L) :
    H78.beta =
      Hypothesis71.constOne G - H78.nu (H78.hyp76.zeta H78.zetaDistinct) +
        H78.delta := by
  rw [delta]
  abel

/-- If `χ` is orthogonal to both `1_G` and the distinguished `ζ^ν`, then
`(β,χ) = (Δ,χ)`. -/
theorem beta_inner_eq_delta_inner_of_orthogonal
    (H78 : Hypothesis78 G A L) (χ : ClassFunction G ℂ)
    (hone : ClassFunction.inner (Hypothesis71.constOne G) χ = 0)
    (hzeta : ClassFunction.inner
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) χ = 0) :
    ClassFunction.inner H78.beta χ = ClassFunction.inner H78.delta χ := by
  rw [H78.beta_eq_constOne_sub_zetaImage_add_delta, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, hone, hzeta]
  ring

/-- Right-hand variant: if `χ` is orthogonal on the left to `1_G` and the
 distinguished `ζ^ν`, then `(χ,β) = (χ,Δ)`. -/
theorem inner_beta_eq_inner_delta_of_orthogonal
    (H78 : Hypothesis78 G A L) (χ : ClassFunction G ℂ)
    (hone : ClassFunction.inner χ (Hypothesis71.constOne G) = 0)
    (hzeta : ClassFunction.inner χ
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 0) :
    ClassFunction.inner χ H78.beta = ClassFunction.inner χ H78.delta := by
  rw [H78.beta_eq_constOne_sub_zetaImage_add_delta, ClassFunction.inner_add_right,
    ClassFunction.inner_sub_right, hone, hzeta]
  ring

/-- The real norm square `‖β‖²` used in Peterfalvi (7.8.b). -/
noncomputable def betaNormSq (H78 : Hypothesis78 G A L) : ℝ :=
  (ClassFunction.inner H78.beta H78.beta).re

/-- The source-side norm square `‖Ind 1_H - ζ‖²` corresponding to `β`. -/
noncomputable def sourceDiffNormSq (H78 : Hypothesis78 G A L) : ℝ :=
  (ClassFunction.inner
    (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct)
    (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct)).re

/-- The Dade-isometry step in Peterfalvi (7.8.b): the norm of `β` equals the
norm of the source difference `Ind 1_H - ζ`.  The remaining `‖β‖² = e + 1`
calculation is therefore a source-side character computation. -/
theorem beta_inner_self_eq_sourceDiff_inner_self (H78 : Hypothesis78 G A L) :
    ClassFunction.inner H78.beta H78.beta =
      ClassFunction.inner
        (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct) := by
  simpa [beta, indMinusZetaSupp] using
    H78.hyp76.isDadeIsometry.inner_eq H78.indMinusZetaSupp H78.indMinusZetaSupp

/-- Real-valued form of `beta_inner_self_eq_sourceDiff_inner_self`. -/
theorem betaNormSq_eq_sourceDiffNormSq (H78 : Hypothesis78 G A L) :
    H78.betaNormSq = H78.sourceDiffNormSq := by
  rw [betaNormSq, sourceDiffNormSq, H78.beta_inner_self_eq_sourceDiff_inner_self]

/-- Source-side expansion of `‖Ind 1_H - ζ‖²`.  This isolates the remaining
character-theoretic facts needed to turn the source norm into `e + 1`. -/
theorem sourceDiff_inner_self_expand (H78 : Hypothesis78 G A L) :
    ClassFunction.inner
        (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct) =
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) -
        ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
          (H78.hyp76.zeta H78.ind1H) -
        ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
          (H78.hyp76.zeta H78.zetaDistinct) +
        ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
          (H78.hyp76.zeta H78.zetaDistinct) := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right]
  ring

/-- Real-valued source-side expansion corresponding to
`sourceDiff_inner_self_expand`. -/
theorem sourceDiffNormSq_expand (H78 : Hypothesis78 G A L) :
    H78.sourceDiffNormSq =
      (ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) -
        ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
          (H78.hyp76.zeta H78.ind1H) -
        ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
          (H78.hyp76.zeta H78.zetaDistinct) +
        ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
          (H78.hyp76.zeta H78.zetaDistinct)).re := by
  rw [sourceDiffNormSq, H78.sourceDiff_inner_self_expand]

/-- The weighted `S^ν`-sum occurring in Peterfalvi (7.8.a):
`Σ_{φ ∈ S} φ(1)/(e ‖φ‖²) · φ^ν`, where `S = T \ {Ind 1_H}` and
`e = ζ(1)` for the distinguished `ζ`. -/
noncomputable def weightedNuSum (H78 : Hypothesis78 G A L) : ClassFunction G ℂ :=
  ∑ i ∈ (Finset.univ.erase H78.ind1H),
    (H78.hyp76.zeta i (1 : L) /
        (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))) •
      H78.nu (H78.hyp76.zeta i)

/-- **Peterfalvi (7.8.a) target.**  The coherent images `S^ν` are orthogonal to
`1_G`, and `β` has the displayed decomposition
`β = 1_G - ζ^ν + a · Σ_{φ∈S} φ(1)/(e‖φ‖²) φ^ν + Γ`, with `a ∈ ℤ`
and `Γ` orthogonal to `S^ν ∪ {1_G}`.

This is a standalone target for the future proof of (7.8.a), not a field of
`Hypothesis78`; hence it does not add a new assumption to already-green results. -/
structure BetaDecomp (H78 : Hypothesis78 G A L) where
  /-- `S^ν ⊥ 1_G`. -/
  orth_one : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i)) (Hypothesis71.constOne G) = 0
  /-- The integer coefficient `a` in Peterfalvi (7.8.a). -/
  a : ℤ
  /-- The residual term `Γ`. -/
  Gamma : ClassFunction G ℂ
  /-- `Γ` is orthogonal to `S^ν`. -/
  Gamma_orth_nu : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
    ClassFunction.inner Gamma (H78.nu (H78.hyp76.zeta i)) = 0
  /-- `Γ` is orthogonal to `1_G`. -/
  Gamma_orth_one : ClassFunction.inner Gamma (Hypothesis71.constOne G) = 0
  /-- The displayed decomposition of `β`. -/
  beta_eq :
    H78.beta =
      Hypothesis71.constOne G - H78.nu (H78.hyp76.zeta H78.zetaDistinct) +
        (a : ℂ) • H78.weightedNuSum + Gamma

/-- Kernel order `h = |H|` for Peterfalvi (7.8.b). -/
noncomputable def kernelOrder (H78 : Hypothesis78 G A L) : ℕ :=
  Nat.card H78.hyp76.H

/-- Complement index `e = |L:H|` for Peterfalvi (7.8.b), stored as
`|L| / |H|` using the ambient normal-subgroup data. -/
noncomputable def complementIndex (H78 : Hypothesis78 G A L) : ℕ :=
  Nat.card L / Nat.card H78.hyp76.H

/-- The kernel order `h` is positive. -/
theorem kernelOrder_pos (H78 : Hypothesis78 G A L) : 0 < H78.kernelOrder := by
  rw [kernelOrder]
  exact Nat.card_pos

/-- The complement index `e = |L:H|` is positive. -/
theorem complementIndex_pos (H78 : Hypothesis78 G A L) : 0 < H78.complementIndex := by
  rw [complementIndex]
  have hH_card : Nat.card ((H78.hyp76.H).subgroupOf L) = Nat.card H78.hyp76.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe H78.hyp76.H_le_L).toEquiv
  have hdvd : Nat.card H78.hyp76.H ∣ Nat.card L := by
    rw [← hH_card]
    exact Subgroup.card_subgroup_dvd_card ((H78.hyp76.H).subgroupOf L)
  exact Nat.div_pos (Nat.le_of_dvd Nat.card_pos hdvd) Nat.card_pos

/-- Lagrange in the notation of (7.8.b): `h * e = |L|`. -/
theorem kernelOrder_mul_complementIndex_eq_card_L (H78 : Hypothesis78 G A L) :
    H78.kernelOrder * H78.complementIndex = Nat.card L := by
  rw [kernelOrder, complementIndex]
  have hH_card : Nat.card ((H78.hyp76.H).subgroupOf L) = Nat.card H78.hyp76.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe H78.hyp76.H_le_L).toEquiv
  have hdvd : Nat.card H78.hyp76.H ∣ Nat.card L := by
    rw [← hH_card]
    exact Subgroup.card_subgroup_dvd_card ((H78.hyp76.H).subgroupOf L)
  exact Nat.mul_div_cancel' hdvd

/-- Since `A = H#`, its cardinality is `h - 1`. -/
theorem card_A_eq_kernelOrder_sub_one (H78 : Hypothesis78 G A L) :
    Nat.card A = H78.kernelOrder - 1 := by
  conv_lhs => rw [H78.hyp76.A_eq_H_sharp]
  rw [kernelOrder, Nat.card_coe_set_eq]
  have hHcard : (H78.hyp76.H : Set G).ncard = Nat.card H78.hyp76.H := by
    rw [← Nat.card_coe_set_eq]
    rfl
  have h1_mem : (1 : G) ∈ (H78.hyp76.H : Set G) := H78.hyp76.H.one_mem
  rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr h1_mem) (Set.finite_singleton _),
    Set.ncard_singleton, hHcard]

/-- The local support ratio `|A|/|L|` in the `(h,e)` notation of (7.8.b). -/
theorem card_A_div_card_L_eq_kernel_sub_one_div_kernel_mul_complementIndex_complex
    (H78 : Hypothesis78 G A L) :
    (Nat.card A : ℂ) / (Nat.card L : ℂ) =
      ((H78.kernelOrder : ℂ) - 1) /
        ((H78.kernelOrder : ℂ) * (H78.complementIndex : ℂ)) := by
  have hh1 : 1 ≤ H78.kernelOrder := Nat.succ_le_of_lt H78.kernelOrder_pos
  rw [H78.card_A_eq_kernelOrder_sub_one, ← H78.kernelOrder_mul_complementIndex_eq_card_L]
  norm_num [Nat.cast_sub hh1]

/-- Real-valued form of the local support ratio `|A|/|L| = (h-1)/(he)`. -/
theorem card_A_div_card_L_eq_kernel_sub_one_div_kernel_mul_complementIndex_real
    (H78 : Hypothesis78 G A L) :
    (Nat.card A : ℝ) / (Nat.card L : ℝ) =
      ((H78.kernelOrder : ℝ) - 1) /
        ((H78.kernelOrder : ℝ) * (H78.complementIndex : ℝ)) := by
  have hh1 : 1 ≤ H78.kernelOrder := Nat.succ_le_of_lt H78.kernelOrder_pos
  rw [H78.card_A_eq_kernelOrder_sub_one, ← H78.kernelOrder_mul_complementIndex_eq_card_L]
  norm_num [Nat.cast_sub hh1]

/-- **Peterfalvi (7.8.b) source norm target.**  The remaining source-side
character computation for `‖β‖² = e + 1`, after the Dade-isometry bridge has
reduced the norm of `β` to `‖Ind 1_H - ζ‖²`.

This is standalone target data, not a field of `Hypothesis78`; completing it
requires evaluating the four source inner products isolated by
`sourceDiffNormSq_expand`. -/
structure SourceDiffNormEvaluation (H78 : Hypothesis78 G A L) : Prop where
  /-- `‖Ind 1_H - ζ‖² = e + 1`. -/
  sourceDiffNormSq_eq :
    H78.sourceDiffNormSq = (H78.complementIndex : ℝ) + 1

/-- Once the source-side norm computation is available, the beta norm identity
`‖β‖² = e + 1` follows from the Dade isometry. -/
theorem betaNormSq_eq_complementIndex_add_one (H78 : Hypothesis78 G A L)
    (hsrc : H78.SourceDiffNormEvaluation) :
    H78.betaNormSq = (H78.complementIndex : ℝ) + 1 := by
  rw [H78.betaNormSq_eq_sourceDiffNormSq, hsrc.sourceDiffNormSq_eq]

/-- The four source-side inner-product evaluations needed for
`‖Ind 1_H - ζ‖² = e + 1` imply `SourceDiffNormEvaluation`.

In the textbook proof these are the normal-subgroup character computations for
`Ind_H^L 1_H` and the chosen irreducible `ζ`: the induced principal character
has norm square `e`, it is orthogonal to `ζ` on both sides, and `ζ` has norm
one. -/
theorem sourceDiffNormEvaluation_of_inner_values (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hind_zeta :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.zetaDistinct) = 0)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1) :
    H78.SourceDiffNormEvaluation where
  sourceDiffNormSq_eq := by
    rw [H78.sourceDiffNormSq_expand, hind_norm, hzeta_ind, hind_zeta, hzeta_norm]
    simp

/-- Any indexed source character has norm one once it is known to be irreducible. -/
theorem zeta_inner_self_eq_one_of_irreducible (H78 : Hypothesis78 G A L)
    {i : Fin (H78.hyp76.n + 1)}
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) = 1 := by
  simpa using
    (OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨H78.hyp76.zeta i, hzeta_irr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter L)
      (⟨H78.hyp76.zeta i, hzeta_irr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter L))

/-- The chosen non-principal `ζ` has norm one once it is known to be irreducible. -/
theorem zetaDistinct_inner_self_eq_one_of_irreducible (H78 : Hypothesis78 G A L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1 :=
  H78.zeta_inner_self_eq_one_of_irreducible hzeta_irr

/-- Variant of `sourceDiffNormEvaluation_of_inner_values` using irreducibility of
the chosen `ζ` instead of a raw self-inner-product evaluation. -/
theorem sourceDiffNormEvaluation_of_inner_values_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hind_zeta :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.zetaDistinct) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.SourceDiffNormEvaluation :=
  H78.sourceDiffNormEvaluation_of_inner_values
    hind_norm hzeta_ind hind_zeta
    (H78.zetaDistinct_inner_self_eq_one_of_irreducible hzeta_irr)

/-- Variant using Hermitian symmetry: one orthogonality direction determines the other. -/
theorem sourceDiffNormEvaluation_of_zeta_ind_orthogonal (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1) :
    H78.SourceDiffNormEvaluation := by
  refine H78.sourceDiffNormEvaluation_of_inner_values hind_norm hzeta_ind ?_ hzeta_norm
  rw [Hypothesis71.ClassFunction.inner_symm, hzeta_ind, star_zero]

/-- Variant using one orthogonality direction and irreducibility of the chosen `ζ`. -/
theorem sourceDiffNormEvaluation_of_zeta_ind_orthogonal_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.SourceDiffNormEvaluation :=
  H78.sourceDiffNormEvaluation_of_zeta_ind_orthogonal
    hind_norm hzeta_ind
    (H78.zetaDistinct_inner_self_eq_one_of_irreducible hzeta_irr)

/-- Combined beta-norm form of `sourceDiffNormEvaluation_of_inner_values`. -/
theorem betaNormSq_eq_complementIndex_add_one_of_inner_values
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hind_zeta :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.zetaDistinct) = 0)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1) :
    H78.betaNormSq = (H78.complementIndex : ℝ) + 1 := by
  exact H78.betaNormSq_eq_complementIndex_add_one
    (H78.sourceDiffNormEvaluation_of_inner_values hind_norm hzeta_ind hind_zeta hzeta_norm)

/-- Combined beta-norm form using irreducibility of the chosen `ζ`. -/
theorem betaNormSq_eq_complementIndex_add_one_of_inner_values_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hind_zeta :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.zetaDistinct) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.betaNormSq = (H78.complementIndex : ℝ) + 1 := by
  exact H78.betaNormSq_eq_complementIndex_add_one
    (H78.sourceDiffNormEvaluation_of_inner_values_of_zeta_irreducible
      hind_norm hzeta_ind hind_zeta hzeta_irr)

/-- Combined beta-norm form using one orthogonality direction and irreducibility of `ζ`. -/
theorem betaNormSq_eq_complementIndex_add_one_of_zeta_ind_orthogonal_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.betaNormSq = (H78.complementIndex : ℝ) + 1 := by
  exact H78.betaNormSq_eq_complementIndex_add_one
    (H78.sourceDiffNormEvaluation_of_zeta_ind_orthogonal_of_zeta_irreducible
      hind_norm hzeta_ind hzeta_irr)

/-- The size hypothesis `e ≤ (h - 1) / 2`, written without division as
`2e + 1 ≤ h`. -/
noncomputable def smallIndex (H78 : Hypothesis78 G A L) : Prop :=
  2 * H78.complementIndex + 1 ≤ H78.kernelOrder

/-- Real-valued form of `smallIndex`, for the arithmetic in (7.8.b). -/
theorem smallIndex_real (H78 : Hypothesis78 G A L) (hsmall : H78.smallIndex) :
    2 * (H78.complementIndex : ℝ) + 1 ≤ (H78.kernelOrder : ℝ) := by
  rw [smallIndex] at hsmall
  exact_mod_cast hsmall

/-- The quadratic correction `u a² - 2 v a` in Peterfalvi (7.8.b), with
`u = (1/e)(1 - 1/h)` and `v = 1/h`. -/
noncomputable def normQuadraticCorrection (H78 : Hypothesis78 G A L)
    (hBD : H78.BetaDecomp) : ℝ :=
  (1 / (H78.complementIndex : ℝ)) *
      (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
    2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ)

/-- The class function `(ζ^ν)^ρ` whose norm is estimated in Peterfalvi (7.8.b). -/
noncomputable def zetaNuRho (H78 : Hypothesis78 G A L) : ClassFunction L ℂ :=
  H78.hyp76.hyp71.chiRhoCF (H78.nu (H78.hyp76.zeta H78.zetaDistinct))

/-- The real norm square `‖(ζ^ν)^ρ‖²` from Peterfalvi (7.8.b). -/
noncomputable def zetaNuRhoNormSq (H78 : Hypothesis78 G A L) : ℝ :=
  (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re

/-- The real norm square `‖Γ‖²` from Peterfalvi (7.8.b). -/
noncomputable def gammaNormSq (H78 : Hypothesis78 G A L)
    (hBD : H78.BetaDecomp) : ℝ :=
  (ClassFunction.inner hBD.Gamma hBD.Gamma).re

end Hypothesis78
end Section_7_8
end OddOrder.Peterfalvi.S09
