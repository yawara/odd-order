import OddOrder.Peterfalvi.S07_Coherence.CoherenceUnion
import OddOrder.Peterfalvi.S07_Coherence.FamilyBundleBasic

/-!
# Peterfalvi (5.6.1) family bundle + (5.1) Dade isometry base map

Split from the former monolithic `OddOrder.Peterfalvi.S07_Coherence` (directory split, issue 0103).
-/

namespace OddOrder.Peterfalvi.S07
open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

/-! ### Peterfalvi (5.1): the Dade isometry as the coherence base map `τ`

Peterfalvi (5.1) takes the coherence **base map** `τ` to be "a `ℤ`-linear isometry from `E` to
`ℤ[Irr G]`, where `Z[S,A] ⊂ E ⊂ ℤ[Irr L]`", and (5.6.3) uses `τ` *directly* on the supported
sublattice `Z[S₁, L^#]` and on the difference generators `χ − a·χ₁`, `χ − χ̄`.  In §4–§16 this `τ`
**is the Dade isometry** of §4 (`FullDadeIsometryData`).  But the §4 Dade map is a *partial, bare*
function `CF(L,A) → CF(G)` on the supported subspace, whereas `IsCoherent` consumes a *total*
`IntegralCharacterMap L G = CF(L) →ₗ[ℤ] CF(G)`.

`dadeIntegralCharacterMap` bridges the two: it lifts the §4 Dade map to a total integral character
map.  The §4 map is `ℂ`-linear on `CF(L,A)` (`Hypothesis.dadeLinearMap`); `LinearMap.exists_extend`
(splitting of subspaces over the field `ℂ`) extends it to all of `CF(L)`, and
`LinearMap.restrictScalars ℤ` reads the result as an `IntegralCharacterMap`.  The extension off the
supported subspace is irrelevant: `IsCoherent τ S A` constrains `τ` **only** on `zSupportedSpan S A
⊆ CF(L,A)` (via `extends_on_supported`), and `dadeIntegralCharacterMap_apply_of_support` shows the
lift agrees with the Dade map there.  This realizes the (5.1) base map `τ` from the actual §4 Dade
isometry — the G2.7 type-bridge. -/
section DadeBaseMap

open OddOrder.Peterfalvi.S04

variable {G : Type*} [Group G] {A : Set G} {L : Subgroup G} [Fintype G] [Fintype ↥L]
variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card L : ℂ)]

/-- The §4 Dade isometry `dade`, lifted to a *total* `ℤ`-linear `IntegralCharacterMap ↥L G`.

Built by extending the `ℂ`-linear Dade map `hyp.dadeLinearMap` (the bare §4 map repackaged as a
`ℂ`-linear map on the supported subspace `CF(L,A)`) to all of `CF(L)` via `LinearMap.exists_extend`,
then restricting scalars to `ℤ`.  Its values on the supported subspace are the Dade map's
(`dadeIntegralCharacterMap_apply_of_support`); off it they are an arbitrary linear extension, which
the coherence machinery never inspects. -/
noncomputable def dadeIntegralCharacterMap (hyp : S04.Hypothesis G A L)
    (_dade : S04.FullDadeIsometryData (G := G) hyp) :
    IntegralCharacterMap (↥L) G :=
  (Classical.choose (LinearMap.exists_extend (hyp.dadeLinearMap (k := ℂ)))).restrictScalars ℤ

/-- The defining property of `dadeIntegralCharacterMap`: on the supported subspace `CF(L,A)` it
agrees with the §4 Dade map.

For a supported class function `φ` (`φ.support ⊆ supportInSubgroup A L`, i.e. `φ ∈ CF(L,A)`), the
lift evaluates to the Dade-map image `hyp.dadeMap ⟨φ, hφ⟩` — the (5.6.3) `τ` on `Z[S,L^#]`. -/
theorem dadeIntegralCharacterMap_apply_of_support (hyp : S04.Hypothesis G A L)
    (dade : S04.FullDadeIsometryData (G := G) hyp)
    {φ : ClassFunction (↥L) ℂ} (hφ : φ.support ⊆ supportInSubgroup A L) :
    dadeIntegralCharacterMap hyp dade φ =
      hyp.dadeMap (k := ℂ)
        (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ :
          SupportedClassFunctions (G := G) ℂ A L) := by
  have hext := Classical.choose_spec (LinearMap.exists_extend (hyp.dadeLinearMap (k := ℂ)))
  have key := LinearMap.congr_fun hext
    (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ :
      SupportedClassFunctions (G := G) ℂ A L)
  simpa [dadeIntegralCharacterMap, LinearMap.restrictScalars_apply,
    Hypothesis.dadeLinearMap_apply] using key

/-- **The Dade lift commutes with conjugation on supported inputs** (Coq `Dtau` conj step of
`GammaReal`): on `CF(L, A)` the lift is the §4 Dade map (`…_apply_of_support`), which is a
pointwise evaluation and hence `star`-equivariant (`Hypothesis.dadeMap_conj`); the conjugate
input is supported on the same set. -/
theorem dadeIntegralCharacterMap_conj_of_support (hyp : S04.Hypothesis G A L)
    (dade : S04.FullDadeIsometryData (G := G) hyp)
    {φ : ClassFunction (↥L) ℂ} (hφ : φ.support ⊆ supportInSubgroup A L) :
    (dadeIntegralCharacterMap hyp dade φ).conj
      = dadeIntegralCharacterMap hyp dade φ.conj := by
  have hφc : φ.conj.support ⊆ supportInSubgroup A L := by
    rw [ClassFunction.conj_support]; exact hφ
  rw [dadeIntegralCharacterMap_apply_of_support hyp dade hφ,
    dadeIntegralCharacterMap_apply_of_support hyp dade hφc,
    hyp.dadeMap_conj]

omit [Fintype G] in
omit [Fintype ↥L] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- Every element of the integral span `ℤ[S]` of a set `S` of **supported** class functions is
itself supported.

`supportedSubmodule (supportInSubgroup A L)` is a `ℂ`-submodule of `CF(L)`; its
`restrictScalars ℤ` is a `ℤ`-submodule containing every generator `s ∈ S` (by hypothesis), hence
contains the whole `ℤ`-span `Submodule.span ℤ S = zSpan S` (`Submodule.span_le`).  This is the
lattice closure fact behind the supply-ability of the (5.4) auxiliary isometry: the difference
generators `χ − χ̄`, `χ − a·χ₁` live in `Z[S, L^#] ⊆ CF(L,A)`, so the whole sponsoring lattice
`ℤ[χ, χ̄, ψ]` is supported and the Dade isometry's `CF(L,A)` inner-preservation applies.

(The ambient `Fintype`/`Invertible` section instances are unused here — this is a pure
`ℤ`-submodule closure fact — but kept in scope for the supply-ability lemma that consumes it.) -/
theorem support_subset_of_mem_zSpan_of_supported
    {S : Set (ClassFunction (↥L) ℂ)}
    (hS : ∀ s ∈ S, s.support ⊆ supportInSubgroup A L)
    {φ : ClassFunction (↥L) ℂ} (hφ : φ ∈ zSpan (L := ↥L) S) :
    φ.support ⊆ supportInSubgroup A L := by
  have hle : zSpan (L := ↥L) S ≤
      (ClassFunction.supportedSubmodule (G := ↥L) (k := ℂ)
        (supportInSubgroup A L)).restrictScalars ℤ :=
    Submodule.span_le.mpr (fun s hs => by
      simpa only [SetLike.mem_coe, Submodule.restrictScalars_mem,
        ClassFunction.mem_supportedSubmodule] using hS s hs)
  exact (ClassFunction.mem_supportedSubmodule).mp (hle hφ)

/-- **Peterfalvi (5.1)/(5.4): the Dade base map supplies the lattice-relative isometry.**

The (5.1) coherence base map `τ = dadeIntegralCharacterMap` preserves the inner product on the
integral span `ℤ[S]` of any set `S` of **supported** class functions — exactly the
**lattice-relative** `htau1_inner_eq` shape consumed by `CharacterPsiDecomposition.ofProjection`
and `decompositionPair`.  This is the supply-ability witness for the Round-13 weakening: a *global*
`IsIntegralIsometry` on all of `CF(L)` does **not** exist in Feit–Thompson (`dim CF(L) > dim
CF(G)`), but the Dade isometry's `CF(L,A)` inner-preservation (`IsDadeIsometry.inner_eq`, the
(2.6.a) isometry property of the explicit (2.5) Dade map) *does* hand back inner-preservation on
every supported sublattice.

Proof: every `φ, ζ ∈ zSpan S` is supported (`support_subset_of_mem_zSpan_of_supported`), so
`dadeIntegralCharacterMap φ = hyp.dadeMap ⟨φ,_⟩` (`dadeIntegralCharacterMap_apply_of_support`); the
isometry property of `hyp.dadeMap` (via `hyp.dadeIsometryData`, whose `toDadeMap` *is*
`hyp.dadeMap`) closes `⟨τ φ, τ ζ⟩ = ⟨φ, ζ⟩`.

So for the running (5.4) `τ₁` *equal to* `τ` on the supported sublattice (the (5.1) base case, where
`τ₁ = τ`), `decompositionPair`'s `htau1_inner_eq` is discharged by this lemma — the per-step
`(D₀, Da)` are constructible from the Dade isometry.  (The general (5.4) `τ₁ ⊋ τ` extends this off
the support; the supported-lattice inner-preservation used by the `(5.4.b)/(5.5)/(5.6.2)` proofs is
exactly what this supplies.) -/
theorem dadeIntegralCharacterMap_inner_eq_on_supported_span
    (hyp : S04.Hypothesis G A L)
    {S : Set (ClassFunction (↥L) ℂ)}
    (hS : ∀ s ∈ S, s.support ⊆ supportInSubgroup A L)
    {φ ζ : ClassFunction (↥L) ℂ}
    (hφ : φ ∈ zSpan (L := ↥L) S) (hζ : ζ ∈ zSpan (L := ↥L) S) :
    ClassFunction.inner
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) φ)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) ζ) =
      ClassFunction.inner φ ζ := by
  have hφsupp : φ.support ⊆ supportInSubgroup A L :=
    support_subset_of_mem_zSpan_of_supported hS hφ
  have hζsupp : ζ.support ⊆ supportInSubgroup A L :=
    support_subset_of_mem_zSpan_of_supported hS hζ
  rw [dadeIntegralCharacterMap_apply_of_support hyp _ hφsupp,
    dadeIntegralCharacterMap_apply_of_support hyp _ hζsupp]
  -- The (2.6.a) isometry property of the explicit (2.5) Dade map, on the supported pair.
  have hiso := (hyp.dadeIsometryData).isDadeIsometry.inner_eq
    (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφsupp⟩ :
      S04.SupportedClassFunctions (G := G) ℂ A L)
    (⟨ζ, (ClassFunction.mem_supportedSubmodule).mpr hζsupp⟩ :
      S04.SupportedClassFunctions (G := G) ℂ A L)
  rwa [hyp.dadeIsometryData_toDadeMap] at hiso

/-- **Pair form of `dadeIntegralCharacterMap_inner_eq_on_supported_span`** (issue 0099): the Dade
base map preserves the inner product of any two **`A`-supported** class functions — no ambient
family or span membership needed (apply the span lemma to the pair `{φ, ζ}` itself).  This is the
unconditional supply for the `S07.Hypothesis.tau_isometry_diff` field in its (0099)
`zSupportedSpan` form: an instantiation site passes the supportedness halves `hφ.2`/`hζ.2` of
`ℤ[S, A]`-membership, and the `ℤ[S]` halves are not needed at all — so this works for **any**
family, mixed degrees included. -/
theorem dadeIntegralCharacterMap_inner_eq_of_supported
    (hyp : S04.Hypothesis G A L)
    {φ ζ : ClassFunction (↥L) ℂ}
    (hφ : φ.support ⊆ supportInSubgroup A L) (hζ : ζ.support ⊆ supportInSubgroup A L) :
    ClassFunction.inner
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) φ)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) ζ) =
      ClassFunction.inner φ ζ := by
  refine dadeIntegralCharacterMap_inner_eq_on_supported_span hyp
    (S := {φ, ζ}) ?_ (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · exact hφ
  · exact hζ

/-- **Inner-product preservation for the Dade base map, from any isometry datum.**  Generalises
`dadeIntegralCharacterMap_inner_eq_on_supported_span`: the lift preserves inner products on the
supported span for **any** `FullDadeIsometryData dade` — not only `hyp.fullDadeIsometryData`.
On the supported subspace the lift agrees with `hyp.dadeMap`, and `hyp.dadeMap = dade.toDadeMap`
by Dade-map uniqueness (`IsDadeMap.unique`), so the isometry `dade.inner_eq` applies.  This is what
the certain-type Dade `h.tau` (a generic `FullDadeIsometryData`, with no `HConjInvariant`) needs to
feed the (6.8.2.3) per-constituent `CharacterPsiDecomposition` via `ofProjection`. -/
theorem dadeIntegralCharacterMap_inner_eq_on_supported_span_of_data
    (hyp : S04.Hypothesis G A L) (dade : S04.FullDadeIsometryData (G := G) hyp)
    {S : Set (ClassFunction (↥L) ℂ)}
    (hS : ∀ s ∈ S, s.support ⊆ supportInSubgroup A L)
    {φ ζ : ClassFunction (↥L) ℂ}
    (hφ : φ ∈ zSpan (L := ↥L) S) (hζ : ζ ∈ zSpan (L := ↥L) S) :
    ClassFunction.inner (dadeIntegralCharacterMap hyp dade φ)
        (dadeIntegralCharacterMap hyp dade ζ) = ClassFunction.inner φ ζ := by
  have hφsupp : φ.support ⊆ supportInSubgroup A L :=
    support_subset_of_mem_zSpan_of_supported hS hφ
  have hζsupp : ζ.support ⊆ supportInSubgroup A L :=
    support_subset_of_mem_zSpan_of_supported hS hζ
  rw [dadeIntegralCharacterMap_apply_of_support hyp dade hφsupp,
    dadeIntegralCharacterMap_apply_of_support hyp dade hζsupp,
    show hyp.dadeMap (k := ℂ) = dade.toDadeMap from
      S04.IsDadeMap.unique hyp.isDadeMap_dadeMap dade.toDadeIsometryData.isDadeMap]
  exact dade.inner_eq _ _

/-- **The Dade base map sends supported virtual characters to virtual characters of `G`.**

For a supported class function `φ` (`φ.support ⊆ supportInSubgroup A L`, i.e. `φ ∈ CF(L,A)`) that is
also a virtual character of `L` (`φ ∈ ℤ[Irr L]`), the lift `dadeIntegralCharacterMap hyp dade φ`
lies in `ℤ[Irr G]`.  On the supported subspace the lift agrees with the explicit Dade map
(`dadeIntegralCharacterMap_apply_of_support`), and the §4 `FullDadeIsometryData` records the
(2.6.b) virtual-character preservation `PreservesVirtualCharacters` (`maps_virtualCharacter`).
This is the Round-B supply of the `ZIrr`-membership facts feeding `decompositionPairFromDade`. -/
theorem dadeIntegralCharacterMap_mem_ZIrr_of_supported
    (hyp : S04.Hypothesis G A L)
    {φ : ClassFunction (↥L) ℂ} (hφsupp : φ.support ⊆ supportInSubgroup A L)
    (hφZ : φ ∈ ZIrr (↥L)) :
    dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) φ ∈ ZIrr G := by
  rw [dadeIntegralCharacterMap_apply_of_support hyp _ hφsupp]
  -- `hyp.dadeMap` is the underlying `toDadeMap` of `fullDadeIsometryData`; apply (2.6.b).
  have hpv := (hyp.fullDadeIsometryData).maps_virtualCharacter
    (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφsupp⟩ :
      S04.SupportedClassFunctions (G := G) ℂ A L) hφZ
  rwa [show (hyp.fullDadeIsometryData).toDadeMap = hyp.dadeMap (k := ℂ) from
    hyp.dadeIsometryData_toDadeMap] at hpv

/-- **The Dade base map sends supported class functions to functions vanishing at `1`.**

For a supported class function `φ` (`φ ∈ CF(L,A)`), the lift `dadeIntegralCharacterMap hyp dade φ`
vanishes at the identity of `G`.  On the supported subspace the lift agrees with the explicit Dade
map `hyp.dadeMap ⟨φ,_⟩` (`dadeIntegralCharacterMap_apply_of_support`), which vanishes off
`dadeSupport` (`IsDadeMap.map_eq_zero_of_not_mem_dadeSupport`); since `1 ∉ dadeSupport`
(`one_notMem_dadeSupport`), the value at `1` is `0`.  This discharges the (1.4)
`IsometryDifferenceImagesVanishAtOne` hypothesis for the Dade map. -/
theorem dadeIntegralCharacterMap_apply_one_eq_zero
    (hyp : S04.Hypothesis G A L)
    {φ : ClassFunction (↥L) ℂ} (hφsupp : φ.support ⊆ supportInSubgroup A L) :
    (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) φ) (1 : G) = 0 := by
  rw [dadeIntegralCharacterMap_apply_of_support hyp _ hφsupp]
  exact (hyp.isDadeMap_dadeMap (k := ℂ)).map_eq_zero_of_not_mem_dadeSupport
    (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφsupp⟩ :
      S04.SupportedClassFunctions (G := G) ℂ A L)
    (1 : G) hyp.one_notMem_dadeSupport

/-- **Round B: the Dade `R(χ)` extractor.**  For an irreducible **non-real** character `χ` of `L`
whose support (and that of `χ̄`) lies in `CF(L,A)`, the orthonormal image family `R(χ)` of `χ - χ̄`
under the Dade base map `τ = dadeIntegralCharacterMap` is **constructed** from the Dade isometry
itself — no opaque `OrthonormalCharacterImageFamily` hypothesis.

The construction feeds the §3 (1.4) keystone `characterDifferenceImageOfIsometry` (which reads off
the signed-difference data `{μ, ν, ε}` from `isometry_difference_pair_structure`), then lifts the
resulting two-element `CharacterDifferenceImage` to the orthonormal family via
`CharacterDifferenceImage.toOrthonormalImage`.  Its three (1.4) hypotheses are discharged directly
from the Dade isometry on the two-element family `{χ, χ̄}`:

* **virtual-character images** — `dadeIntegralCharacterMap_mem_ZIrr_of_supported` ((2.6.b)
  `PreservesVirtualCharacters`): `(χ̄ - χ)^τ ∈ ℤ[Irr G]` since `χ̄ - χ` is supported and in
  `ℤ[Irr L]`;
* **vanish at `1`** — `dadeIntegralCharacterMap_apply_one_eq_zero` (`1 ∉ dadeSupport`): the Dade
  image vanishes off the support, hence at `1`;
* **inner-product preservation** — `dadeIntegralCharacterMap_inner_eq_on_supported_span`
  ((2.6.a) `IsDadeIsometry`): the difference generators all lie in the supported lattice
  `ℤ[χ, χ̄]`.

This is the Round-B gateway: it supplies the `imageFamily` argument of `decompositionPairFromDade`
from the real Dade τ. -/
noncomputable def dadeOrthonormalCharacterImageFamily
    (hyp : S04.Hypothesis G A L)
    (χ : IrreducibleCharacter (↥L))
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ))
    (hχsupp : (χ : ClassFunction (↥L) ℂ).support ⊆ supportInSubgroup A L)
    (hχbarsupp : (χ : ClassFunction (↥L) ℂ).conj.support ⊆ supportInSubgroup A L) :
    OrthonormalCharacterImageFamily (L := ↥L) (G := G)
      (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χ : ClassFunction (↥L) ℂ) := by
  classical
  set τ := dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) with hτ_def
  set fam : Fin 2 → IrreducibleCharacter (↥L) := conjPairFamily (L := ↥L) χ with hfam
  -- The two difference generators `χ - χ` (= 0) and `χ̄ - χ` are supported, in `ℤ[χ, χ̄]`.
  have hfam0 : (fam 0 : ClassFunction (↥L) ℂ) = (χ : ClassFunction (↥L) ℂ) := by
    simp [hfam, conjPairFamily]
  have hfam1 : (fam 1 : ClassFunction (↥L) ℂ) = (χ : ClassFunction (↥L) ℂ).conj := by
    simp [hfam, conjPairFamily]
  -- Each generator `fam i` (i.e. `χ` or `χ̄`) is supported in `CF(L,A)`.
  have hfam_supp : ∀ i, (fam i : ClassFunction (↥L) ℂ).support ⊆ supportInSubgroup A L := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [hfam0]; exact hχsupp
    · rw [hfam1]; exact hχbarsupp
  -- Each `fam i` lies in `ℤ[χ, χ̄]`.
  have hfam_zspan : ∀ i, (fam i : ClassFunction (↥L) ℂ) ∈
      zSpan (L := ↥L) ({(χ : ClassFunction (↥L) ℂ), (χ : ClassFunction (↥L) ℂ).conj} :
        Set (ClassFunction (↥L) ℂ)) := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [hfam0]; exact Submodule.subset_span (by simp)
    · rw [hfam1]; exact Submodule.subset_span (by simp)
  -- Each `irreducibleCharacterDifference fam i = (fam i) - (fam 0)` is supported in `CF(L,A)`.
  have hdiff_supp : ∀ i,
      (irreducibleCharacterDifference fam i).support ⊆ supportInSubgroup A L := fun i =>
    (ClassFunction.support_sub_subset _ _).trans
      (Set.union_subset (hfam_supp i) (hfam_supp 0))
  -- Each difference lies in `ℤ[χ, χ̄]`.
  have hdiff_zspan : ∀ i,
      irreducibleCharacterDifference fam i ∈
        zSpan (L := ↥L) ({(χ : ClassFunction (↥L) ℂ), (χ : ClassFunction (↥L) ℂ).conj} :
          Set (ClassFunction (↥L) ℂ)) := fun i =>
    Submodule.sub_mem _ (hfam_zspan i) (hfam_zspan 0)
  -- Supportedness of the two generators of `ℤ[χ, χ̄]`.
  have hSsupp : ∀ s ∈ ({(χ : ClassFunction (↥L) ℂ), (χ : ClassFunction (↥L) ℂ).conj} :
      Set (ClassFunction (↥L) ℂ)), s.support ⊆ supportInSubgroup A L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hχsupp
    · exact hχbarsupp
  -- (1.4) hypothesis (virtual): `(fam i - χ)^τ ∈ ℤ[Irr G]`.
  have hvirtual : IsometryDifferenceImagesAreVirtual (G := G) (H := ↥L) τ fam := by
    intro i
    refine dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp (hdiff_supp i) ?_
    -- `(fam i) - χ ∈ ℤ[Irr L]`: difference of two irreducibles.
    refine Submodule.sub_mem _ ?_ (fam 0).mem_ZIrr
    exact (fam i).mem_ZIrr
  -- (1.4) hypothesis (vanish at 1).
  have hzero : IsometryDifferenceImagesVanishAtOne (G := G) (H := ↥L) τ fam := by
    intro i
    exact dadeIntegralCharacterMap_apply_one_eq_zero hyp (hdiff_supp i)
  -- (1.4) hypothesis (inner product preserved): both differences live in the supported `ℤ[χ, χ̄]`.
  have hisom : ∀ i j,
      ClassFunction.inner (isometryDifferenceImage τ fam i) (isometryDifferenceImage τ fam j) =
        ClassFunction.inner (irreducibleCharacterDifference fam i)
          (irreducibleCharacterDifference fam j) := by
    intro i j
    exact dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hSsupp
      (hdiff_zspan i) (hdiff_zspan j)
  -- Assemble: the §3 keystone difference image, lifted to the orthonormal family.
  exact (characterDifferenceImageOfIsometry τ χ hreal hvirtual hzero hisom).toOrthonormalImage

/-- **The Dade `CharacterDifferenceImage` `{μ, ν, ε}` of `χ`, with only the DIFFERENCE `χ̄ − χ`
supported (X-family).**  (`.toOrthonormalImage` lifts it to the orthonormal `R(χ)`; see
`dadeOrthonormalCharacterImageFamilyOfDiff` below.)

The orthonormal image family `R(χ)` with `(χ − χ̄)^τ = ∑_{α ∈ R(χ)} α`, built from the Dade base
map — but requiring only that the *difference* `χ̄ − χ` is supported in `CF(L,A)`, **not** the
individual supports `hχsupp`/`hχbarsupp` of `dadeOrthonormalCharacterImageFamily`.  This is what the
(6.8) `X`-family needs: an induced `χ = Ind_H^L θ` has `χ(1) = |W₁|θ(1) ≠ 0`, so `χ` itself is NOT
supported (`1 ∉ A = H^#`), yet the conjugate difference `χ̄ − χ` vanishes at `1` and is supported on
`H^#`.

The Dade `CF(L,A)`-isometry is applied on the **difference set** `D = {0, χ̄ − χ}` (both supported:
`0` trivially, `χ̄ − χ` by hypothesis), into which both keystone differences
`irreducibleCharacterDifference fam i` (`= 0` for `i = 0`, `= χ̄ − χ` for `i = 1`) land — exactly
the
generators the (1.4)/(2.6.a) keystone uses.  No `χ`/`χ̄` individual support is touched.
`dadeOrthonormalCharacterImageFamily` (individual supports) is recovered as the special case where
`hdiffsupp` is derived from `hχsupp`, `hχbarsupp`. -/
noncomputable def dadeCharacterDifferenceImageOfDiff
    (hyp : S04.Hypothesis G A L)
    (χ : IrreducibleCharacter (↥L))
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ))
    (hdiffsupp : ((χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ)).support ⊆
      supportInSubgroup A L) :
    CharacterDifferenceImage (L := ↥L) (G := G)
      (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χ : ClassFunction (↥L) ℂ) := by
  classical
  set τ := dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) with hτ_def
  set fam : Fin 2 → IrreducibleCharacter (↥L) := conjPairFamily (L := ↥L) χ with hfam
  have hfam0 : (fam 0 : ClassFunction (↥L) ℂ) = (χ : ClassFunction (↥L) ℂ) := by
    simp [hfam, conjPairFamily]
  have hfam1 : (fam 1 : ClassFunction (↥L) ℂ) = (χ : ClassFunction (↥L) ℂ).conj := by
    simp [hfam, conjPairFamily]
  -- `irreducibleCharacterDifference fam i = fam i − fam 0`: `0` for `i = 0`, `χ̄ − χ` for `i = 1`.
  have hdiff0 : irreducibleCharacterDifference fam 0 = 0 := by
    simp [irreducibleCharacterDifference]
  have hdiff1 : irreducibleCharacterDifference fam 1 =
      (χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ) := by
    simp only [irreducibleCharacterDifference, hfam1, hfam0]
  -- Each keystone difference is supported in `CF(L,A)`.
  have hdiff_supp : ∀ i,
      (irreducibleCharacterDifference fam i).support ⊆ supportInSubgroup A L := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [hdiff0]; simp
    · rw [hdiff1]; exact hdiffsupp
  -- The supported difference set `D = {0, χ̄ − χ}`, and the keystone differences land in `ℤ[D]`.
  set D : Set (ClassFunction (↥L) ℂ) :=
    {(0 : ClassFunction (↥L) ℂ), (χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ)}
    with hD
  have hDsupp : ∀ s ∈ D, s.support ⊆ supportInSubgroup A L := by
    intro s hs
    simp only [hD, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · simp
    · exact hdiffsupp
  have hdiff_in_D : ∀ i, irreducibleCharacterDifference fam i ∈ zSpan (L := ↥L) D := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [hdiff0]; exact Submodule.subset_span (by simp [hD])
    · rw [hdiff1]; exact Submodule.subset_span (by simp [hD])
  -- (1.4) hypotheses, all from the difference support.
  have hvirtual : IsometryDifferenceImagesAreVirtual (G := G) (H := ↥L) τ fam := by
    intro i
    refine dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp (hdiff_supp i) ?_
    refine Submodule.sub_mem _ ?_ (fam 0).mem_ZIrr
    exact (fam i).mem_ZIrr
  have hzero : IsometryDifferenceImagesVanishAtOne (G := G) (H := ↥L) τ fam := by
    intro i
    exact dadeIntegralCharacterMap_apply_one_eq_zero hyp (hdiff_supp i)
  have hisom : ∀ i j,
      ClassFunction.inner (isometryDifferenceImage τ fam i) (isometryDifferenceImage τ fam j) =
        ClassFunction.inner (irreducibleCharacterDifference fam i)
          (irreducibleCharacterDifference fam j) := by
    intro i j
    exact dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hDsupp
      (hdiff_in_D i) (hdiff_in_D j)
  exact characterDifferenceImageOfIsometry τ χ hreal hvirtual hzero hisom

/-- **R(χ) from the Dade isometry, difference-support form**: `dadeCharacterDifferenceImageOfDiff`
lifted to the orthonormal family `R(χ) = {ε·μ, −ε·ν}` via `toOrthonormalImage`.  Requires only the
*difference* `χ̄ − χ` supported in `CF(L,A)` (the `(6.8)`/`(12.2)` X-family situation, where `χ`
itself is unsupported since `χ(1) ≠ 0`).  The underlying `{μ, ν, ε}` data is
`dadeCharacterDifferenceImageOfDiff` (consumed by the cross-`L` (4.1) orthogonality of (12.3)). -/
noncomputable def dadeOrthonormalCharacterImageFamilyOfDiff
    (hyp : S04.Hypothesis G A L)
    (χ : IrreducibleCharacter (↥L))
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ))
    (hdiffsupp : ((χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ)).support ⊆
      supportInSubgroup A L) :
    OrthonormalCharacterImageFamily (L := ↥L) (G := G)
      (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χ : ClassFunction (↥L) ℂ) :=
  (dadeCharacterDifferenceImageOfDiff hyp χ hreal hdiffsupp).toOrthonormalImage

/-- **The supported per-step decomposition `Da` of `χ − a·χ₁`, for an UNSUPPORTED `χ` (X-family).**

Builds `Da : CharacterPsiDecomposition τ χ (a·χ₁)` directly via `ofProjection` — **not**
`decompositionPair`, which also builds the `ψ=0` `D₀` requiring the unprovable `τχ ∈ ZIrr`.  This is
now constructible for an unsupported induced X-member `χ = Ind θ` thanks to the
difference-sublattice
weakening of `tau1_inner_eq_on_support`: the auxiliary isometry `τ₁ = τ` only needs
inner-preservation
on `ℤ[χ−χ̄, χ−a·χ₁]` (both supported differences — supplied by
`dadeIntegralCharacterMap_inner_eq_on_supported_span` on the difference set `{χ−χ̄, χ−a·χ₁}`), and
the
`ZIrr`-membership only on `χ − a·χ₁` (`htau1_mema`, the degree-matched difference vanishing at `1`).
`R(χ)` is the difference-support family `dadeOrthonormalCharacterImageFamilyOfDiff`. -/
noncomputable def decompositionDaFromDadeOfDiff
    (hyp : S04.Hypothesis G A L)
    (χ : IrreducibleCharacter (↥L))
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ))
    {chi1 : ClassFunction (↥L) ℂ} {a : ℕ}
    (hdiffsupp : ((χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ)).support ⊆
      supportInSubgroup A L)
    (hdiffasupp : ((χ : ClassFunction (↥L) ℂ) - a • chi1).support ⊆ supportInSubgroup A L)
    (htau1_mema : dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
      ((χ : ClassFunction (↥L) ℂ) - a • chi1) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (a • chi1 : ClassFunction (↥L) ℂ) = 0)
    (hχbaraχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj
      (a • chi1 : ClassFunction (↥L) ℂ) = 0)
    (hχχbar' : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ).conj = 0) :
    CharacterPsiDecomposition (L := ↥L) (G := G)
      (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χ : ClassFunction (↥L) ℂ) (a • chi1) := by
  classical
  set τ := dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) with hτ
  -- The difference set `{χ−χ̄, χ−a·χ₁}` is supported (`χ−χ̄` via `hdiffsupp` up to sign).
  have hSdiff : ∀ s ∈ ({(χ : ClassFunction (↥L) ℂ) - (χ : ClassFunction (↥L) ℂ).conj,
      (χ : ClassFunction (↥L) ℂ) - a • chi1} : Set (ClassFunction (↥L) ℂ)),
      s.support ⊆ supportInSubgroup A L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show (χ : ClassFunction (↥L) ℂ) - (χ : ClassFunction (↥L) ℂ).conj =
          -((χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ)) by abel,
        ClassFunction.support_neg]
      exact hdiffsupp
    · exact hdiffasupp
  exact CharacterPsiDecomposition.ofProjection
    (dadeOrthonormalCharacterImageFamilyOfDiff hyp χ hreal hdiffsupp) τ
    (fun φ ζ hφ hζ =>
      dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hSdiff hφ hζ)
    rfl htau1_mema hχaχ1 hχbaraχ1 hχχbar'

/-- **Peterfalvi (5.2.e) inner-product core for the Dade families.**

`⟨(x − x̄)^τ, (χ − χ̄)^τ⟩ = 0` whenever the four characters `x, x̄, χ, χ̄` are supported in
`CF(L,A)`
and `x, x̄` are each orthogonal to both `χ` and `χ̄`.  The Dade isometry's `CF(L,A)`
inner-preservation (`dadeIntegralCharacterMap_inner_eq_on_supported_span`) reduces it to
`⟨x − x̄, χ − χ̄⟩`, which expands to the four cross pairings — all zero.  This is the source-side
input of `orthogonal_of_signedDifference_inner_eq_zero` for the Dade `R(·)` families (feeding the
per-member `(5.2.e)` orthogonality `hmemOrtho` of `DadeChainStep`). -/
theorem dadeIntegralCharacterMap_inner_conjDifference_eq_zero
    (hyp : S04.Hypothesis G A L)
    {x χ : ClassFunction (↥L) ℂ}
    (hxsupp : x.support ⊆ supportInSubgroup A L)
    (hxbarsupp : x.conj.support ⊆ supportInSubgroup A L)
    (hχsupp : χ.support ⊆ supportInSubgroup A L)
    (hχbarsupp : χ.conj.support ⊆ supportInSubgroup A L)
    (hxχ : ClassFunction.inner x χ = 0) (hxχbar : ClassFunction.inner x χ.conj = 0)
    (hxbarχ : ClassFunction.inner x.conj χ = 0)
    (hxbarχbar : ClassFunction.inner x.conj χ.conj = 0) :
    ClassFunction.inner
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) (x - x.conj))
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) (χ - χ.conj)) = 0 := by
  classical
  have hS : ∀ s ∈ ({x, x.conj, χ, χ.conj} : Set (ClassFunction (↥L) ℂ)),
      s.support ⊆ supportInSubgroup A L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact hxsupp
    · exact hxbarsupp
    · exact hχsupp
    · exact hχbarsupp
  have hx_span : (x - x.conj) ∈
      zSpan (L := ↥L) ({x, x.conj, χ, χ.conj} : Set (ClassFunction (↥L) ℂ)) :=
    Submodule.sub_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  have hχ_span : (χ - χ.conj) ∈
      zSpan (L := ↥L) ({x, x.conj, χ, χ.conj} : Set (ClassFunction (↥L) ℂ)) :=
    Submodule.sub_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  rw [dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hS hx_span hχ_span]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    hxχ, hxχbar, hxbarχ, hxbarχbar, sub_self]

/-- **Peterfalvi (5.2.e) for the Dade `R(·)` families.**

The orthonormal image families `R(x)` and `R(χ)` produced from the Dade isometry
(`dadeOrthonormalCharacterImageFamily`) are orthogonal whenever `x, x̄` are each orthogonal to both
`χ` and `χ̄`.  Reduces — via `toOrthonormalImage_orthogonal` and
`orthogonal_of_signedDifference_inner_eq_zero` — to `⟨(x − x̄)^τ, (χ − χ̄)^τ⟩ = 0`
(`dadeIntegralCharacterMap_inner_conjDifference_eq_zero`).  This is exactly the per-member
`(5.2.e)` orthogonality `hmemOrtho` of `DadeChainStep` for members built by
`decompositionPairFromDadeOfIrreducible`. -/
theorem dadeOrthonormalCharacterImageFamily_orthogonal
    (hyp : S04.Hypothesis G A L)
    {x χ : IrreducibleCharacter (↥L)}
    (hxreal : ¬ ClassFunction.IsReal (x : ClassFunction (↥L) ℂ))
    (hxsupp : (x : ClassFunction (↥L) ℂ).support ⊆ supportInSubgroup A L)
    (hxbarsupp : (x : ClassFunction (↥L) ℂ).conj.support ⊆ supportInSubgroup A L)
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ))
    (hχsupp : (χ : ClassFunction (↥L) ℂ).support ⊆ supportInSubgroup A L)
    (hχbarsupp : (χ : ClassFunction (↥L) ℂ).conj.support ⊆ supportInSubgroup A L)
    (hxχ : ClassFunction.inner (x : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ) = 0)
    (hxχbar : ClassFunction.inner (x : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ).conj = 0)
    (hxbarχ : ClassFunction.inner (x : ClassFunction (↥L) ℂ).conj (χ : ClassFunction (↥L) ℂ) = 0)
    (hxbarχbar :
      ClassFunction.inner (x : ClassFunction (↥L) ℂ).conj (χ : ClassFunction (↥L) ℂ).conj = 0) :
    (dadeOrthonormalCharacterImageFamily hyp x hxreal hxsupp hxbarsupp).Orthogonal
      (dadeOrthonormalCharacterImageFamily hyp χ hreal hχsupp hχbarsupp) := by
  unfold dadeOrthonormalCharacterImageFamily
  refine CharacterDifferenceImage.toOrthonormalImage_orthogonal _ _
    (CharacterDifferenceImage.orthogonal_of_signedDifference_inner_eq_zero _ _ ?_)
  rw [← CharacterDifferenceImage.image_eq_signedDifference,
    ← CharacterDifferenceImage.image_eq_signedDifference]
  exact dadeIntegralCharacterMap_inner_conjDifference_eq_zero hyp
    hxsupp hxbarsupp hχsupp hχbarsupp hxχ hxχbar hxbarχ hxbarχbar

/-- **Peterfalvi (5.6.3) / Round-24 (ii): the per-step decomposition pair `(D₀, Da)`, produced
directly from the Dade isometry.**

The concrete realization of `CharacterPsiDecomposition.decompositionPair` against the (5.1) base map
`τ = dadeIntegralCharacterMap` itself (the (5.4) base case `τ₁ = τ`): from the orthonormal image
family `R(χ)`, the supported difference generators (`χ`, `χ̄`, `a·χ₁` all in `CF(L,A)`), and the two
`ZIrr`-membership facts `(χ−0)^τ, (χ−a·χ₁)^τ ∈ ℤ[Irr G]`, it builds **both** decompositions `D₀`
(`ψ = 0`) and `Da` (`ψ = a·χ₁`) sharing the one running isometry `τ`.

The previously missing lattice-relative inner-preservation input `htau1_inner_eq` is now discharged
*internally* by `dadeIntegralCharacterMap_inner_eq_on_supported_span` — the Dade isometry's
`CF(L,A)` inner-preservation specialized to the supported sponsoring lattice `ℤ[χ, χ̄, 0, a·χ₁]`.
No global `IsIntegralIsometry` is needed or available; this is exactly what the Round-13 weakening
unblocked.  The structural τ₁-agreement `Da.tau1 χ = D₀.tau1 χ` is `rfl`
(`decompositionPair_tau1_agree`), so this pair feeds `retarget_isCoherent_of_sharedDecomposition`
directly.  This closes Round-24 (ii): the per-step `(D₀, Da)` production from the Dade isometry. -/
noncomputable def decompositionPairFromDade
    (hyp : S04.Hypothesis G A L)
    {χ chi1 : ClassFunction (↥L) ℂ} {a : ℕ}
    (imageFamily : OrthonormalCharacterImageFamily (L := ↥L) (G := G)
      (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) χ)
    (hχsupp : χ.support ⊆ supportInSubgroup A L)
    (hχbarsupp : χ.conj.support ⊆ supportInSubgroup A L)
    (haχ1supp : (a • chi1 : ClassFunction (↥L) ℂ).support ⊆ supportInSubgroup A L)
    (htau1_mem0 :
      dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) (χ - 0) ∈ ZIrr G)
    (htau1_mema :
      dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) (χ - a • chi1) ∈ ZIrr G)
    (hχχ1 : ClassFunction.inner χ chi1 = 0)
    (hχbarχ1 : ClassFunction.inner χ.conj chi1 = 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0) :
    CharacterPsiDecomposition (L := ↥L) (G := G)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) χ 0 ×
      CharacterPsiDecomposition (L := ↥L) (G := G)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) χ (a • chi1) :=
  -- Every generator of the sponsoring lattice `{χ, χ̄, 0, a·χ₁}` is supported, so the Dade
  -- isometry's `CF(L,A)` inner-preservation supplies the lattice-relative `htau1_inner_eq`.
  have hS : ∀ s ∈ ({χ, χ.conj, 0, a • chi1} : Set (ClassFunction (↥L) ℂ)),
      s.support ⊆ supportInSubgroup A L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact hχsupp
    · exact hχbarsupp
    · simpa only [ClassFunction.support_zero] using Set.empty_subset _
    · exact haχ1supp
  CharacterPsiDecomposition.decompositionPair imageFamily
    (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
    (fun φ ζ hφ hζ =>
      dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hS hφ hζ)
    rfl htau1_mem0 htau1_mema hχχ1 hχbarχ1 hχχbar

/-- **Round B assembly: the fully Dade-derived per-step decomposition pair.**

The per-step `(D₀, Da)` decomposition pair produced *entirely* from the Dade isometry, taking only
the natural character-theoretic data of (6.6): `χ` an irreducible **non-real** character of `L`,
`χ₁ ∈ ℤ[Irr L]`, both `χ`, `χ̄`, `a·χ₁` supported in `CF(L,A)`, and the three orthogonality
relations.  Both the orthonormal image family `R(χ)` (via `dadeOrthonormalCharacterImageFamily`,
Round B) **and** the two `ZIrr`-membership facts `(χ−0)^τ, (χ−a·χ₁)^τ ∈ ℤ[Irr G]` (via
`dadeIntegralCharacterMap_mem_ZIrr_of_supported`, (2.6.b)) are constructed internally — no opaque
`OrthonormalCharacterImageFamily` or `ZIrr` hypotheses.  This makes the per-step `(5.6)` retarget
input fully constructive from the real Dade τ: feed the result to
`retarget_isCoherent_of_sharedDecomposition`. -/
noncomputable def decompositionPairFromDadeOfIrreducible
    (hyp : S04.Hypothesis G A L)
    (χ : IrreducibleCharacter (↥L)) {chi1 : ClassFunction (↥L) ℂ} {a : ℕ}
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ))
    (hχsupp : (χ : ClassFunction (↥L) ℂ).support ⊆ supportInSubgroup A L)
    (hχbarsupp : (χ : ClassFunction (↥L) ℂ).conj.support ⊆ supportInSubgroup A L)
    (hchi1Z : chi1 ∈ ZIrr (↥L))
    (haχ1supp : (a • chi1 : ClassFunction (↥L) ℂ).support ⊆ supportInSubgroup A L)
    (hχχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) chi1 = 0)
    (hχbarχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj chi1 = 0)
    (hχχbar : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ).conj = 0) :
    CharacterPsiDecomposition (L := ↥L) (G := G)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
        (χ : ClassFunction (↥L) ℂ) 0 ×
      CharacterPsiDecomposition (L := ↥L) (G := G)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
        (χ : ClassFunction (↥L) ℂ) (a • chi1) :=
  -- `(χ − 0)^τ ∈ ℤ[Irr G]`: `χ` itself is supported and in `ℤ[Irr L]`.
  have hmem0 : dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
      ((χ : ClassFunction (↥L) ℂ) - 0) ∈ ZIrr G :=
    dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp
      (by simpa only [sub_zero] using hχsupp) (by simpa only [sub_zero] using χ.mem_ZIrr)
  -- `(χ − a·χ₁)^τ ∈ ℤ[Irr G]`: difference of supported virtual characters.
  have hmema : dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
      ((χ : ClassFunction (↥L) ℂ) - a • chi1) ∈ ZIrr G :=
    dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp
      ((ClassFunction.support_sub_subset _ _).trans (Set.union_subset hχsupp haχ1supp))
      (Submodule.sub_mem _ χ.mem_ZIrr (nsmul_mem hchi1Z a))
  decompositionPairFromDade hyp
    (dadeOrthonormalCharacterImageFamily hyp χ hreal hχsupp hχbarsupp)
    hχsupp hχbarsupp haχ1supp hmem0 hmema hχχ1 hχbarχ1 hχχbar

open OddOrder.RepresentationTheory in
open scoped Classical in
/-- **Peterfalvi (5.6.1)→(5.6.2) at the Dade base map: the `Y`-collapse, fully discharged.**

The (5.6.2) collapse `Da.Y = a·χ₁^{τ₁}` for *any* decomposition `Da` whose auxiliary isometry is the
Dade base map (`hDa_tau1 : Da.tau1 = τ`), with **all** of the generic producer
`CharacterPsiDecomposition.Y_collapse_of_family`'s hypotheses discharged from the Dade isometry plus
the prior coherence:
* `hiso_fam`/`hiso_cross` — the running isometry on the family and the difference generators — from
  `dadeIntegralCharacterMap_inner_eq_on_supported_span` (all family members and the differences are
  supported in `CF(L,A)`);
* `hXortho` — `R(χ) ⊥ S₁^{τ₁}` ((5.5)+(5.2.e)) — from the per-member (5.5) decompositions
  (`inner_extension_member_orthogonal_imageSet`, then conjugate symmetry and
  `extends_on_supported`);
* the `ZIrr`-memberships — `χ₁^{τ₁} ∈ ℤ[Irr G]` from
`dadeIntegralCharacterMap_mem_ZIrr_of_supported`;
* the norm data `mc i = ‖χᵢ‖²` (real and positive, the latter from `χᵢ ≠ 0`), with `‖χ₁‖² ∈ ℤ`
  from `inner_mem_ZIrr_int`.

Only the genuine (6.6) source-side content remains as input: the family bundle `B` (degrees,
pairwise
orthogonality of `S₁`), the family memberships/supports/non-vanishing, the per-member family data
(`Dmem`/`hmemTau1`/`hmemOrtho`, exactly the `DadeChainStep` fields), and the degree inequality
(c). -/
theorem dade_Y_collapse_of_family
    (hyp : S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction (↥L) ℂ)}
    {χ chi1 : ClassFunction (↥L) ℂ} {a : ℕ}
    (Da : CharacterPsiDecomposition (L := ↥L) (G := G)
      (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) χ (a • chi1))
    (hDa_tau1 : Da.tau1 = dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
    {ι : Type*} {s : Finset ι} {i₁ : ι}
    (B : CharacterFamilyBundle (L := ↥L) χ chi1 (a : ℝ) s i₁)
    (hfam_mem : ∀ i ∈ s, B.chiFam i ∈ S₁)
    (hfam_ne : ∀ i ∈ s, B.chiFam i ≠ 0)
    (hfam_supp : ∀ i ∈ s, (B.chiFam i).support ⊆ supportInSubgroup A L)
    (hchi1_supp : chi1.support ⊆ supportInSubgroup A L)
    (hchi1_ZIrr : chi1 ∈ ZIrr (↥L))
    (hdiffasupp : ((χ : ClassFunction (↥L) ℂ) - a • chi1).support ⊆ supportInSubgroup A L)
    (Dmem : (x : ClassFunction (↥L) ℂ) → x ∈ S₁ →
      CharacterPsiDecomposition (L := ↥L) (G := G)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) x 0)
    (hmemTau1 : ∀ (x : ClassFunction (↥L) ℂ) (hx : x ∈ S₁),
      (Dmem x hx).tau1 = dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
    (hmemOrtho : ∀ (x : ClassFunction (↥L) ℂ) (hx : x ∈ S₁),
      (Dmem x hx).imageFamily.Orthogonal Da.imageFamily)
    (hdiff_ZIrr : Da.tau1 (χ - a • chi1) ∈ ZIrr G)
    (hdeg_c : 2 * (a : ℝ) < ∑ i ∈ s,
      ((B.ratio i : ℝ) / (ClassFunction.inner (B.chiFam i) (B.chiFam i)).re) ^ 2 *
        (ClassFunction.inner (B.chiFam i) (B.chiFam i)).re) :
    Da.Y = a • Da.tau1 chi1 := by
  classical
  -- Generator set uses the supported difference `χ − a·χ₁` (NOT bare `χ`): the isometry is only
  -- ever
  -- applied to family members and to differences, so no individual `χ`-support is needed
  -- (X-family).
  set S₀ : Set (ClassFunction (↥L) ℂ) := insert ((χ : ClassFunction (↥L) ℂ) - a • chi1)
    (insert chi1 (B.chiFam '' ↑s)) with hS₀def
  have hS₀supp : ∀ x ∈ S₀, x.support ⊆ supportInSubgroup A L := by
    intro x hx
    simp only [hS₀def, Set.mem_insert_iff, Set.mem_image, Finset.mem_coe] at hx
    rcases hx with rfl | rfl | ⟨i, hi, rfl⟩
    · exact hdiffasupp
    · exact hchi1_supp
    · exact hfam_supp i hi
  have hchi1_mem : chi1 ∈ zSpan (L := ↥L) S₀ :=
    Submodule.subset_span (by simp [hS₀def])
  have hfam_zspan : ∀ i ∈ s, B.chiFam i ∈ zSpan (L := ↥L) S₀ := fun i hi =>
    Submodule.subset_span (by
      simp only [hS₀def, Set.mem_insert_iff, Set.mem_image, Finset.mem_coe]
      exact Or.inr (Or.inr ⟨i, hi, rfl⟩))
  have hdiff_zspan : χ - a • chi1 ∈ zSpan (L := ↥L) S₀ :=
    Submodule.subset_span (by simp [hS₀def])
  have hfamdiff_zspan : ∀ i ∈ s, B.chiFam i - B.ratio i • chi1 ∈ zSpan (L := ↥L) S₀ := fun i hi =>
    Submodule.sub_mem _ (hfam_zspan i hi) (nsmul_mem hchi1_mem _)
  -- the norm function `mc i = ‖χᵢ‖²` (real and positive).
  have hself : ∀ φ : ClassFunction (↥L) ℂ,
      ClassFunction.inner φ φ = ((ClassFunction.inner φ φ).re : ℂ) := fun φ => by
    rw [inner_self_eq_realCast φ, Complex.ofReal_re]
  set mc : ι → ℝ := fun i => (ClassFunction.inner (B.chiFam i) (B.chiFam i)).re with hmcdef
  have hmc : ∀ i ∈ s, ClassFunction.inner (B.chiFam i) (B.chiFam i) = (mc i : ℂ) :=
    fun i _ => hself (B.chiFam i)
  have hmc_pos : ∀ i ∈ s, 0 < mc i := by
    intro i hi
    rcases (inner_self_re_nonneg (B.chiFam i)).lt_or_eq with h | h
    · exact h
    · exact absurd (eq_zero_of_inner_self_re_eq_zero h.symm) (hfam_ne i hi)
  have hmc1_int : ∃ z : ℤ, mc i₁ = (z : ℝ) := by
    obtain ⟨z, hz⟩ := ClassFunction.inner_mem_ZIrr_int hchi1_ZIrr hchi1_ZIrr
    refine ⟨z, ?_⟩
    have hc : (mc i₁ : ℂ) = (z : ℂ) := by
      simp only [hmcdef, B.chi1_eq]
      rw [← hself, hz]
    exact_mod_cast hc
  -- the isometry instances from the Dade base map's `CF(L,A)` inner-preservation.
  have hiso_fam : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (Da.tau1 (B.chiFam i)) (Da.tau1 (B.chiFam j)) =
        ClassFunction.inner (B.chiFam i) (B.chiFam j) := by
    intro i hi j hj
    rw [hDa_tau1]
    exact dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hS₀supp
      (hfam_zspan i hi) (hfam_zspan j hj)
  have hiso_cross : ∀ i ∈ s,
      ClassFunction.inner (Da.tau1 (χ - a • chi1)) (Da.tau1 (B.chiFam i - B.ratio i • chi1)) =
        ClassFunction.inner (χ - a • chi1) (B.chiFam i - B.ratio i • chi1) := by
    intro i hi
    rw [hDa_tau1]
    exact dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hS₀supp
      hdiff_zspan (hfamdiff_zspan i hi)
  -- `R(χ) ⊥ S₁^{τ₁}` ((5.5)+(5.2.e)): `χᵢ^{τ₁} = (Dmem χᵢ).X ∈ ℤ[R(χᵢ)] ⊥ R(χ)`.
  have hXortho : ∀ α ∈ Da.imageFamily.imageSet, ∀ i ∈ s,
      ClassFunction.inner α (Da.tau1 (B.chiFam i)) = 0 := by
    intro α hα i hi
    have hmem := hfam_mem i hi
    -- `χᵢ^{τ₁} = (Dmem χᵢ).X` by (5.5) (the `ψ = 0` decomposition collapses `Y = 0`).
    have hX : Da.tau1 (B.chiFam i) = (Dmem (B.chiFam i) hmem).X :=
      (DFunLike.congr_fun (hDa_tau1.trans (hmemTau1 (B.chiFam i) hmem).symm) (B.chiFam i)).trans
        ((Dmem (B.chiFam i) hmem).eq_sum_of_psi_eq_zero).2.1
    have h0 : ClassFunction.inner α (Dmem (B.chiFam i) hmem).X = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm,
        (Dmem (B.chiFam i) hmem).inner_X_orthogonal_imageSet_of_orthogonal Da.imageFamily
          (hmemOrtho (B.chiFam i) hmem) hα, star_zero]
    exact (congrArg (ClassFunction.inner α) hX).trans h0
  have hvc1_ZIrr : Da.tau1 chi1 ∈ ZIrr G := by
    rw [hDa_tau1]
    exact dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp hchi1_supp hchi1_ZIrr
  exact Da.Y_collapse_of_family B mc hmc hmc_pos hmc1_int hiso_fam hiso_cross hXortho hvc1_ZIrr
    hdiff_ZIrr hdeg_c

/-- **Peterfalvi (5.2.d) base coherence at the Dade base map: `{χ, χ̄}` is coherent.**

The seed `h0`/`hS₁` of every coherence chain — `coherentPairChain`, `retarget_isCoherent_fromDade`,
`peterfalvi_66_coherence_of_X_from_dade`, `coherentUnion_of_glued` — built at the real Dade `τ`.
For a non-real irreducible `χ` whose pair `{χ, χ̄}` is supported in `CF(L,A)`, the single conjugate
pair is coherent: the (5.2.d) orthonormal image family `R(χ)` (via the `ψ = 0` decomposition `D₀` of
`decompositionPairFromDadeOfIrreducible`) supplies the orthonormal target pair `{X, X̄}`
(`retargetTargetPair`), and `coherentPair` assembles `IsCoherent τ {χ, χ̄} (CF(L,A))`.  The
generation hypothesis is discharged by `zSupportedSpan_pair_subset_span` from `χ(1) ≠ 0`
(`irreducibleCharacter_apply_one_eq_pos_natCast`), `χ̄(1) = χ(1)`
(`irreducibleCharacter_conj_apply_one`), and `1 ∉ A`.

The orthonormality `{χ, χ̄}` (`hχχ`/`hχbarχbar`/`hχbarχ`/`hχχbar`) is taken as input — exactly the
(5.2)-level character data the (6.6)/(6.8) enumeration provides (the same fields as
`DadeChainStep`).
This is the missing base case: every prior coherence producer *consumed* a coherent set but none
*constructed* the seed. -/
noncomputable def coherentPair_fromDade
    (hyp : S04.Hypothesis G A L)
    (χ : IrreducibleCharacter (↥L))
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ))
    (hχsupp : (χ : ClassFunction (↥L) ℂ).support ⊆ supportInSubgroup A L)
    (hχbarsupp : (χ : ClassFunction (↥L) ℂ).conj.support ⊆ supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ) = 1)
    (hχbarχbar :
      ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj (χ : ClassFunction (↥L) ℂ).conj = 1)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj (χ : ClassFunction (↥L) ℂ) = 0)
    (hχχbar : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ).conj = 0)
    (h1notA : (1 : G) ∉ A) :
    IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      {(χ : ClassFunction (↥L) ℂ), (χ : ClassFunction (↥L) ℂ).conj} (supportInSubgroup A L) := by
  classical
  -- The `ψ = 0` decomposition `D₀` (via `decompositionPairFromDadeOfIrreducible` with `χ₁ = 0`).
  set D₀ := (decompositionPairFromDadeOfIrreducible hyp χ hreal hχsupp hχbarsupp
    (chi1 := 0) (a := 0) (Submodule.zero_mem _) (by simp) (by simp) (by simp) hχχbar).1 with hD₀
  -- The orthonormal target pair `{X, X̄}` from `R(χ)`.
  have P := D₀.retargetTargetPair hχχ hχbarχbar hχχbar hχbarχ
  refine coherentPair hχχ hχbarχbar hχχbar hχbarχ P.inner_self_X P.inner_self_conjImage
    P.inner_X_conjImage P.inner_conjImage_X P.X_mem_ZIrr P.conjImage_mem_ZIrr rfl ?_ ?_ ?_
  · -- `χ − χ̄ ≠ 0`: else `χ = χ̄` and `⟨χ, χ̄⟩ = ⟨χ, χ⟩ = 1 ≠ 0`.
    intro h
    rw [sub_eq_zero] at h
    rw [← h, hχχ] at hχχbar
    exact one_ne_zero hχχbar
  · -- support of the difference is in `CF(L,A)`.
    exact (ClassFunction.support_sub_subset _ _).trans (Set.union_subset hχsupp hχbarsupp)
  · -- generation `Z[{χ,χ̄}, A] ⊆ Z[χ − χ̄]`.
    refine zSupportedSpan_pair_subset_span ?_ (irreducibleCharacter_conj_apply_one χ) ?_
    · obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
      rw [hd1]; exact_mod_cast hd.ne'
    · intro h
      exact h1notA (by simpa using h)

open IntegralCharacterMap in
/-- **Peterfalvi (1.1)+(1.4): an equal-degree set is coherent — at the real Dade base map.**

The Dade specialization of `coherentEqualDegree`: an injective, equal-degree family
`χ : Fin n → Irr(L)` (`n ≥ 2`) of irreducible characters supported in `CF(L,A)` is coherent for the
(5.1) base map `τ = dadeIntegralCharacterMap`.  The (1.4) signed-difference family `{μⱼ, ε}` is
**constructed** by applying `isometry_difference_pair_structure` to `τ`, with its three hypotheses
discharged from the Dade isometry exactly as in `dadeOrthonormalCharacterImageFamily`:

* virtual-character images (`dadeIntegralCharacterMap_mem_ZIrr_of_supported`, (2.6.b));
* vanish at `1` (`dadeIntegralCharacterMap_apply_one_eq_zero`, `1 ∉ dadeSupport`);
* inner-product preservation on the supported lattice
  (`dadeIntegralCharacterMap_inner_eq_on_supported_span`, (2.6.a)).

The target family is `Xⱼ = ε • μⱼ` (orthonormal: `{μⱼ}` is, by `classFunction_inner_eq_if`, and
`ε² = 1`), giving the image equation `τ(χⱼ − χ₀) = Xⱼ − X₀` (= `ε•(μⱼ − μ₀)`, the signed
difference); `coherentEqualDegree` then assembles the coherence.  This is the **`h0` base of the
(6.6) equal-minimal-degree prefix and the (6.8) `Y = S(H')`**, both produced directly from the real
Dade τ with no opaque hypotheses (the equal degree and supports are the genuine (6.8) data). -/
noncomputable def coherentEqualDegree_fromDade
    (hyp : S04.Hypothesis G A L)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (χ : Fin n → IrreducibleCharacter (↥L))
    (hχinj : Function.Injective χ)
    (hdeg : ∀ j, ((χ j : ClassFunction (↥L) ℂ) : ↥L → ℂ) 1
      = ((χ 0 : ClassFunction (↥L) ℂ) : ↥L → ℂ) 1)
    (hsuppdiff : ∀ j, (irreducibleCharacterDifference χ j).support ⊆ supportInSubgroup A L)
    (h1notA : (1 : G) ∉ A) :
    IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (Set.range (fun j => (χ j : ClassFunction (↥L) ℂ))) (supportInSubgroup A L) := by
  classical
  set τ := dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) with hτ
  -- Source orthonormality from the distinct irreducible characters.
  have horthχ : ∀ i j, ClassFunction.inner ((χ i : ClassFunction (↥L) ℂ))
      ((χ j : ClassFunction (↥L) ℂ)) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [irreducibleCharacter_inner_eq_ite]
    by_cases h : i = j
    · rw [if_pos h, if_pos (congrArg χ h)]
    · rw [if_neg h, if_neg (fun he => h (hχinj he))]
  -- The supported difference generators `χⱼ − χ₀` of `ℤ[range χ]` (this is the support
  -- hypothesis directly, so the individual `χⱼ` need not be supported on `A`).
  have hdiff_supp : ∀ i, (irreducibleCharacterDifference χ i).support ⊆ supportInSubgroup A L :=
    hsuppdiff
  have hdiffSset : ∀ s ∈ Set.range (fun j => irreducibleCharacterDifference χ j),
      s.support ⊆ supportInSubgroup A L := by
    rintro s ⟨j, rfl⟩; exact hdiff_supp j
  have hdiff_zspan : ∀ i, irreducibleCharacterDifference χ i ∈
      zSpan (L := ↥L) (Set.range (fun j => irreducibleCharacterDifference χ j)) :=
    fun i => Submodule.subset_span (Set.mem_range_self i)
  -- Discharge the three (1.4) hypotheses for the Dade base map.
  have hvirtual : IsometryDifferenceImagesAreVirtual (G := G) (H := ↥L) τ χ := fun i =>
    dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp (hdiff_supp i)
      (Submodule.sub_mem _ (χ i).mem_ZIrr (χ 0).mem_ZIrr)
  have hzero : IsometryDifferenceImagesVanishAtOne (G := G) (H := ↥L) τ χ := fun i =>
    dadeIntegralCharacterMap_apply_one_eq_zero hyp (hdiff_supp i)
  have hisom : ∀ i j, ClassFunction.inner (isometryDifferenceImage τ χ i)
      (isometryDifferenceImage τ χ j) =
      ClassFunction.inner (irreducibleCharacterDifference χ i)
        (irreducibleCharacterDifference χ j) := fun i j =>
    dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hdiffSset
      (hdiff_zspan i) (hdiff_zspan j)
  -- (1.4): the signed irreducible-difference family `{μⱼ, ε}` (extracted via `Exists.choose`,
  -- as the conclusion is data in `Type`, not a `Prop`).
  have hex := isometry_difference_pair_structure (G := G) (H := ↥L) hn χ hχinj hdeg
    τ hvirtual hzero hisom
  set data := hex.choose with hdata_def
  have hdata : ∀ i, isometryDifferenceImage τ χ i = data.signedDifference i := hex.choose_spec
  -- Target family `Xⱼ = ε • μⱼ`.
  set X : Fin n → ClassFunction G ℂ := fun j => data.sign • data.classFunction j with hX
  have horthX : ∀ i j, ClassFunction.inner (X i) (X j) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    have hmul : (data.sign : ℂ) * (data.sign : ℂ) = 1 := by exact_mod_cast data.sign_mul_self
    simp only [hX]
    rw [← Int.cast_smul_eq_zsmul ℂ data.sign (data.classFunction i),
      ← Int.cast_smul_eq_zsmul ℂ data.sign (data.classFunction j),
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      star_intCast, ← mul_assoc, hmul, one_mul, data.classFunction_inner_eq_if i j]
  -- Image equation `τ(χⱼ − χ₀) = Xⱼ − X₀ = ε•(μⱼ − μ₀)`.
  have himg : ∀ j, τ ((fun k => (χ k : ClassFunction (↥L) ℂ)) j
      - (fun k => (χ k : ClassFunction (↥L) ℂ)) 0) = X j - X 0 := by
    intro j
    have hXd : X j - X 0 = data.signedDifference j := by
      change data.sign • data.classFunction j - data.sign • data.classFunction 0
        = data.sign • (data.classFunction j - data.classFunction 0)
      rw [smul_sub]
    rw [hXd]; exact hdata j
  -- The non-vanishing degree at `1` (irreducible characters have positive degree).
  have hdeg0 : ((χ 0 : ClassFunction (↥L) ℂ) : ↥L → ℂ) 1 ≠ 0 := by
    obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (χ 0)
    rw [hd1]; exact_mod_cast hd.ne'
  -- `1 ∉ supportInSubgroup A L`.
  have h1A : (1 : ↥L) ∉ supportInSubgroup A L := fun h => h1notA (by simpa using h)
  -- `Xⱼ = ε • μⱼ ∈ ℤ[Irr G]` since each `μⱼ` is irreducible and `ε = ±1`.
  have hXZ : ∀ j, X j ∈ ZIrr G := fun j => by
    simp only [hX]
    exact Submodule.smul_mem _ data.sign (data.classFunction_irreducible j).mem_ZIrr
  exact coherentEqualDegree hn horthχ horthX himg hXZ hdeg hdeg0 h1A (fun j => hdiff_supp j)

/-- **Round C: the per-step (6.6) `hstep`, discharged from the Dade isometry + prior coherence.**

One adjoining step `IsCoherent τ S₁ A → IsCoherent τ (S₁ ∪ {χ, χ̄}) A` of the (6.6)
`coherentPairChain`, run against the (5.1) base map `τ = dadeIntegralCharacterMap` **as the running
auxiliary isometry `τ₁ = τ`** itself.  This is the running-`τ₁` instantiation: rather than positing
an opaque auxiliary isometry agreeing with `τ`, it takes `τ₁ := τ` and discharges the four
agreement obligations of `retarget_isCoherent_of_sharedDecomposition` **internally**:

* `htau1_agrees : τ(χ−χ̄) = τ(χ−χ̄)` and `htau1_diff : τ(χ−a·χ₁) = τ(χ−a·χ₁)` — both `rfl`
  (the decomposition pair's `tau1` field *is* `τ`);
* `htau1_chi1 : τ χ₁ = hS₁.extension χ₁` and the per-member `hmemTau1 : (Dmem x).tau1 x =
  hS₁.extension x` — from `IsCoherent.extends_on_supported`: the running extension **agrees with the
  base map `τ` on the supported sublattice** `Z[S₁, A]`, and `χ₁`, every member `x ∈ S₁` are
  supported (`hchi1supp`, `hmemSupp`), so `(Dmem x).tau1 x = τ x = hS₁.extension x`.

The `R(χ)` family and the two `ZIrr`-membership facts are supplied by Round B
(`dadeOrthonormalCharacterImageFamily`, `dadeIntegralCharacterMap_mem_ZIrr_of_supported`); the
lattice-relative inner-preservation `htau1_inner_eq` by
`dadeIntegralCharacterMap_inner_eq_on_supported_span`.
The remaining inputs — the (5.6.2) collapse `hY`, the per-member (5.2.e) image-orthogonality
`hmemOrtho`, the source-orthogonalities `hχ_S1`/`hχbar_S1`/`hχχbar`, and the generation hypothesis
`hgen` — are the genuine per-step (6.6) character-degree content (NOT the Dade isometry's
responsibility; supplied by the (6.6) enumeration).  Each per-member decomposition `Dmem x` is
likewise produced from the Dade isometry (e.g. `decompositionPairFromDadeOfIrreducible … .1`), with
its `tau1` field equal to `τ` (`hmemTau1Base`).

This closes the running-`τ₁` instantiation: a `coherentPairChain` step is now DISCHARGED from the
real Dade τ + the prior coherence, with no opaque auxiliary-isometry agreement hypothesis. -/
noncomputable def retarget_isCoherent_fromDade
    (hyp : S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction (↥L) ℂ)} {A' : Set ↥L}
    (hS₁ : IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) S₁ A')
    (χ : IrreducibleCharacter (↥L)) {chi1 : ClassFunction (↥L) ℂ} {a : ℕ}
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ))
    (hχsupp : (χ : ClassFunction (↥L) ℂ).support ⊆ supportInSubgroup A L)
    (hχbarsupp : (χ : ClassFunction (↥L) ℂ).conj.support ⊆ supportInSubgroup A L)
    (haχ1supp : (a • chi1 : ClassFunction (↥L) ℂ).support ⊆ supportInSubgroup A L)
    (htau1_mem0 : dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
      ((χ : ClassFunction (↥L) ℂ) - 0) ∈ ZIrr G)
    (htau1_mema : dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
      ((χ : ClassFunction (↥L) ℂ) - a • chi1) ∈ ZIrr G)
    (hχχ : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ) = 1)
    (hχbarχbar :
      ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj (χ : ClassFunction (↥L) ℂ).conj = 1)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj (χ : ClassFunction (↥L) ℂ) = 0)
    (Dmem : (x : ClassFunction (↥L) ℂ) → x ∈ S₁ →
      CharacterPsiDecomposition (L := ↥L) (G := G)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) x 0)
    (hmemTau1Base : ∀ (x : ClassFunction (↥L) ℂ) (hx : x ∈ S₁),
      (Dmem x hx).tau1 = dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
    (hmemSupp : ∀ x ∈ S₁, x ∈ zSupportedSpan (L := ↥L) S₁ A')
    (hmemOrtho : ∀ (x : ClassFunction (↥L) ℂ) (hx : x ∈ S₁),
      (Dmem x hx).imageFamily.Orthogonal
        (dadeOrthonormalCharacterImageFamily hyp χ hreal hχsupp hχbarsupp))
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction (↥L) ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj x = 0)
    (hchi1 : chi1 ∈ S₁)
    (hchi1supp : chi1 ∈ zSupportedSpan (L := ↥L) S₁ A')
    (hχχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) chi1 = 0)
    (hχbarχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj chi1 = 0)
    (hχχbar' : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ).conj = 0)
    (hY :
      ((CharacterPsiDecomposition.decompositionPair
        (dadeOrthonormalCharacterImageFamily hyp χ hreal hχsupp hχbarsupp)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
        (fun φ ζ hφ hζ => dadeIntegralCharacterMap_inner_eq_on_supported_span hyp
          (by
            intro s hs
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl | rfl | rfl
            · exact hχsupp
            · exact hχbarsupp
            · simpa only [ClassFunction.support_zero] using Set.empty_subset _
            · exact haχ1supp) hφ hζ)
        rfl htau1_mem0 htau1_mema hχχ1 hχbarχ1 hχχbar').2).Y =
        a • ((CharacterPsiDecomposition.decompositionPair
        (dadeOrthonormalCharacterImageFamily hyp χ hreal hχsupp hχbarsupp)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
        (fun φ ζ hφ hζ => dadeIntegralCharacterMap_inner_eq_on_supported_span hyp
          (by
            intro s hs
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl | rfl | rfl
            · exact hχsupp
            · exact hχbarsupp
            · simpa only [ClassFunction.support_zero] using Set.empty_subset _
            · exact haχ1supp) hφ hζ)
        rfl htau1_mem0 htau1_mema hχχ1 hχbarχ1 hχχbar').2).tau1 chi1)
    (hgen : zSupportedSpan (L := ↥L) (S₁ ∪ {(χ : ClassFunction (↥L) ℂ),
        (χ : ClassFunction (↥L) ℂ).conj}) A' ⊆
      Submodule.span ℤ (zSupportedSpan (L := ↥L) S₁ A' ∪
        {(χ : ClassFunction (↥L) ℂ) - (χ : ClassFunction (↥L) ℂ).conj,
         (χ : ClassFunction (↥L) ℂ) - a • chi1})) :
    IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {(χ : ClassFunction (↥L) ℂ), (χ : ClassFunction (↥L) ℂ).conj}) A' :=
  retarget_isCoherent_of_sharedDecomposition hS₁
    (dadeOrthonormalCharacterImageFamily hyp χ hreal hχsupp hχbarsupp)
    (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
    (fun φ ζ hφ hζ => dadeIntegralCharacterMap_inner_eq_on_supported_span hyp
      (by
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl | rfl | rfl
        · exact hχsupp
        · exact hχbarsupp
        · simpa only [ClassFunction.support_zero] using Set.empty_subset _
        · exact haχ1supp) hφ hζ)
    rfl htau1_mem0 htau1_mema rfl hχχ hχbarχbar hχχbar' hχbarχ hχχ1 hχbarχ1 hχχbar'
    Dmem hmemOrtho
    -- `hmemTau1`: `(Dmem x).tau1 x = τ x = hS₁.extension x` (member supported ⇒ `extends`).
    (fun x hx => by
      rw [hmemTau1Base x hx, (hS₁.extends_on_supported x (hmemSupp x hx)).symm])
    hχ_S1 hχbar_S1 hchi1
    -- `htau1_diff`: the `Da.tau1` field is literally `τ`, so this is `rfl`.
    rfl hY
    -- `htau1_chi1`: `τ χ₁ = hS₁.extension χ₁` (χ₁ supported ⇒ `extends_on_supported`).
    (hS₁.extends_on_supported chi1 hchi1supp).symm
    hgen

open OddOrder.RepresentationTheory in
/-- **The (5.6) Dade-base coherence step for an UNSUPPORTED induced X-member (X-family).**

The X-family analogue of `retarget_isCoherent_fromDade`: adjoins `{χ, χ̄}` for an unsupported
`χ = Ind_H^L θ` (`χ(1) ≠ 0`, `1 ∉ A`), routing through the supported decomposition `Da` of the
degree-matched difference `χ − a·χ₁` (`decompositionDaFromDadeOfDiff`) into the supported-route
adapter `retarget_isCoherent_of_supportedDecomposition_and_memberFamily` — **no** `ψ=0` `D₀`, **no**
`τχ ∈ ZIrr`.  Individual supports `hχsupp`/`hχbarsupp`/`haχ1supp` are replaced by the difference
supports `hdiffsupp : (χ̄ − χ) ∈ CF(L,A)` and `hdiffasupp : (χ − a·χ₁) ∈ CF(L,A)` (both vanish at
`1`).  `htau1_diff` and `Da.tau1 = τ` are structural (`rfl`); `hY` is the (5.6.2) collapse. -/
noncomputable def retarget_isCoherent_fromDade_X
    (hyp : S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction (↥L) ℂ)} {A' : Set ↥L}
    (hS₁ : IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) S₁ A')
    (χ : IrreducibleCharacter (↥L)) {chi1 : ClassFunction (↥L) ℂ} {a : ℕ}
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ))
    (hdiffsupp : ((χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ)).support ⊆
      supportInSubgroup A L)
    (hdiffasupp : ((χ : ClassFunction (↥L) ℂ) - a • chi1).support ⊆ supportInSubgroup A L)
    (htau1_mema : dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
      ((χ : ClassFunction (↥L) ℂ) - a • chi1) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (a • chi1 : ClassFunction (↥L) ℂ) = 0)
    (hχbaraχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj
      (a • chi1 : ClassFunction (↥L) ℂ) = 0)
    (hχχ : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ) = 1)
    (hχbarχbar :
      ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj (χ : ClassFunction (↥L) ℂ).conj = 1)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj (χ : ClassFunction (↥L) ℂ) = 0)
    (hχχbar' : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ).conj = 0)
    (hchi1chi1 : ClassFunction.inner chi1 chi1 = 1)
    (Dmem : (x : ClassFunction (↥L) ℂ) → x ∈ S₁ →
      CharacterPsiDecomposition (L := ↥L) (G := G)
        (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) x 0)
    (hmemTau1Base : ∀ (x : ClassFunction (↥L) ℂ) (hx : x ∈ S₁),
      (Dmem x hx).tau1 = dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
    (hmemSupp : ∀ x ∈ S₁, x ∈ zSupportedSpan (L := ↥L) S₁ A')
    (hmemOrtho : ∀ (x : ClassFunction (↥L) ℂ) (hx : x ∈ S₁),
      (Dmem x hx).imageFamily.Orthogonal
        (dadeOrthonormalCharacterImageFamilyOfDiff hyp χ hreal hdiffsupp))
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction (↥L) ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj x = 0)
    (hchi1 : chi1 ∈ S₁)
    (hchi1supp : chi1 ∈ zSupportedSpan (L := ↥L) S₁ A')
    (hY :
      (decompositionDaFromDadeOfDiff hyp χ hreal hdiffsupp hdiffasupp htau1_mema
        hχaχ1 hχbaraχ1 hχχbar').Y =
        a • (decompositionDaFromDadeOfDiff hyp χ hreal hdiffsupp hdiffasupp htau1_mema
          hχaχ1 hχbaraχ1 hχχbar').tau1 chi1)
    (hgen : zSupportedSpan (L := ↥L) (S₁ ∪ {(χ : ClassFunction (↥L) ℂ),
        (χ : ClassFunction (↥L) ℂ).conj}) A' ⊆
      Submodule.span ℤ (zSupportedSpan (L := ↥L) S₁ A' ∪
        {(χ : ClassFunction (↥L) ℂ) - (χ : ClassFunction (↥L) ℂ).conj,
         (χ : ClassFunction (↥L) ℂ) - a • chi1})) :
    IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {(χ : ClassFunction (↥L) ℂ), (χ : ClassFunction (↥L) ℂ).conj}) A' :=
  retarget_isCoherent_of_supportedDecomposition_and_memberFamily hS₁
    (decompositionDaFromDadeOfDiff hyp χ hreal hdiffsupp hdiffasupp htau1_mema
      hχaχ1 hχbaraχ1 hχχbar')
    rfl hχχ hχbarχbar hχχbar' hχbarχ hchi1chi1
    Dmem hmemOrtho
    (fun x hx => by
      rw [hmemTau1Base x hx, (hS₁.extends_on_supported x (hmemSupp x hx)).symm])
    hχ_S1 hχbar_S1 hchi1
    rfl hY
    (hS₁.extends_on_supported chi1 hchi1supp).symm
    hgen

/-- **The genuine per-step (6.6) content, after the Dade isometry has supplied everything it can.**

`DadeChainStep hyp S₁ A χ` bundles the inputs of one (5.6) adjoining step
`IsCoherent τ S₁ A → IsCoherent τ (S₁ ∪ {↑χ, (↑χ).conj}) A` against the Dade base map
`τ = dadeIntegralCharacterMap` that are **NOT** the Dade isometry's responsibility — the genuine
character-degree content of (6.6) — leaving the Round-B/Dade-supplied parts
(`R(χ)`, the `ZIrr`-membership facts, the inner-preservation) to be filled in by `advance`.

The fields are exactly the residual hypotheses of `retarget_isCoherent_fromDade`:

* `chi1`, `a` — the distinguished member `χ₁ ∈ S₁` and the degree ratio `a` with `χ(1) = a·χ₁(1)`
  (from the (6.6) degree enumeration);
* `hreal`, `hχsupp`, `hχbarsupp`, `haχ1supp`, `hchi1Z` — `χ` non-real, the supports of `χ`, `χ̄`,
  `a·χ₁` in `CF(L,A)`, and `χ₁ ∈ ℤ[Irr L]` (so `advance` can build the `ZIrr` facts);
* `hχχ`, `hχbarχbar`, `hχbarχ`, `hχχbar'`, `hχχ1`, `hχbarχ1` — the orthonormality of `{χ, χ̄}` and
  the orthogonality of `χ`, `χ̄` to `χ₁` (the (5.2)-level relations);
* `Dmem`, `hmemTau1Base`, `hmemSupp`, `hmemOrtho`, `hχ_S1`, `hχbar_S1` — the (5.5)+(5.2.e)
  per-member image-side family of `S₁` (each `x ∈ S₁` has a decomposition with `τ₁ = τ` whose
  `R(x)` is orthogonal to `R(χ)`, every `x` supported, and `χ`, `χ̄ ⊥ S₁`);
* `hchi1`, `hchi1supp` — `χ₁ ∈ S₁` and supported;
* `hY` — the (5.6.2) collapse `Da.Y = a·χ₁^{τ₁}`.

None of these mention the Dade isometry's *image-side* structure: they are the source-side degree
and orthogonality data the (6.6) enumeration is responsible for.  `advance` adjoins the Round-B
`R(χ)` (`dadeOrthonormalCharacterImageFamily`) and the (2.6.b) `ZIrr`-membership and discharges the
step.  The (5.1) generation hypothesis is **not** a field: it is pure ℤ-module theory routed
through the difference generators (`zSupportedSpan_adjoinPair_subset_span`), discharged internally
by
`advance` from `hmemSupp` and `hchi1supp` (no (4.7) `ℤ[S, L^#] = ℤ[S, A]` needed). -/
structure DadeChainStep
    (hyp : S04.Hypothesis G A L)
    (S₁ : Set (ClassFunction (↥L) ℂ)) (A' : Set ↥L)
    (χ : IrreducibleCharacter (↥L)) where
  /-- The distinguished member `χ₁`. -/
  chi1 : ClassFunction (↥L) ℂ
  /-- The degree ratio `a` with `χ(1) = a·χ₁(1)`. -/
  a : ℕ
  /-- `χ` is non-real (Peterfalvi (1.1)). -/
  hreal : ¬ ClassFunction.IsReal (χ : ClassFunction (↥L) ℂ)
  /-- The conjugate difference `χ̄ − χ` is supported in `CF(L,A)` (vanishes at `1`).  Replaces the
  individual `χ`/`χ̄` supports — an induced X-member `χ = Ind θ` has `χ(1) ≠ 0`, so `χ` is *not*
  supported, but `χ̄ − χ` is. -/
  hdiffsupp : ((χ : ClassFunction (↥L) ℂ).conj - (χ : ClassFunction (↥L) ℂ)).support ⊆
    supportInSubgroup A L
  /-- `χ₁ ∈ ℤ[Irr L]`. -/
  hchi1Z : chi1 ∈ ZIrr (↥L)
  /-- The degree-matched difference `χ − a·χ₁` is supported in `CF(L,A)` (vanishes at `1`). -/
  hdiffasupp : ((χ : ClassFunction (↥L) ℂ) - a • chi1).support ⊆ supportInSubgroup A L
  /-- `‖χ₁‖² = 1`. -/
  hchi1chi1 : ClassFunction.inner chi1 chi1 = 1
  /-- `‖χ‖² = 1`. -/
  hχχ : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ) = 1
  /-- `‖χ̄‖² = 1`. -/
  hχbarχbar :
    ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj (χ : ClassFunction (↥L) ℂ).conj = 1
  /-- `⟨χ̄, χ⟩ = 0`. -/
  hχbarχ : ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj (χ : ClassFunction (↥L) ℂ) = 0
  /-- `⟨χ, χ̄⟩ = 0`. -/
  hχχbar' : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) (χ : ClassFunction (↥L) ℂ).conj = 0
  /-- The per-member `ψ = 0` decomposition family of `S₁` ((5.5)). -/
  Dmem : (x : ClassFunction (↥L) ℂ) → x ∈ S₁ →
    CharacterPsiDecomposition (L := ↥L) (G := G)
      (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) x 0
  /-- Each member's auxiliary isometry is the base map `τ` (running `τ₁ = τ`). -/
  hmemTau1Base : ∀ (x : ClassFunction (↥L) ℂ) (hx : x ∈ S₁),
    (Dmem x hx).tau1 = dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
  /-- Every member of `S₁` is supported. -/
  hmemSupp : ∀ x ∈ S₁, x ∈ zSupportedSpan (L := ↥L) S₁ A'
  /-- Per-member `R(x) ⊥ R(χ)` ((5.2.e)). -/
  hmemOrtho : ∀ (x : ClassFunction (↥L) ℂ) (hx : x ∈ S₁),
    (Dmem x hx).imageFamily.Orthogonal
      (dadeOrthonormalCharacterImageFamilyOfDiff hyp χ hreal hdiffsupp)
  /-- `χ ⊥ S₁`. -/
  hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction (↥L) ℂ) x = 0
  /-- `χ̄ ⊥ S₁`. -/
  hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj x = 0
  /-- `χ₁ ∈ S₁`. -/
  hchi1 : chi1 ∈ S₁
  /-- `χ₁` supported. -/
  hchi1supp : chi1 ∈ zSupportedSpan (L := ↥L) S₁ A'
  /-- `⟨χ, χ₁⟩ = 0`. -/
  hχχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ) chi1 = 0
  /-- `⟨χ̄, χ₁⟩ = 0`. -/
  hχbarχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj chi1 = 0
  /-- A finite enumeration of `S₁` carrying the (5.6.1) source family `{χᵢ}`. -/
  famS : Finset (ClassFunction (↥L) ℂ)
  /-- `famS` enumerates exactly `S₁`. -/
  famS_eq : ↑famS = S₁
  /-- The integer degree ratios `aᵢ` with `χᵢ(1) = aᵢ·χ₁(1)`. -/
  famRatio : ClassFunction (↥L) ℂ → ℕ
  /-- `a₁ = 1`. -/
  famRatio_chi1 : famRatio chi1 = 1
  /-- The degree scaling `χᵢ(1) = aᵢ·χ₁(1)` for each family member. -/
  famDegree : ∀ x ∈ famS, OddOrder.Peterfalvi.S03.characterDegree x =
    (famRatio x : ℂ) * OddOrder.Peterfalvi.S03.characterDegree chi1
  /-- `χ(1) = a·χ₁(1)`. -/
  famDegree_chi : OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction (↥L) ℂ) =
    (a : ℂ) * OddOrder.Peterfalvi.S03.characterDegree chi1
  /-- `S₁` is pairwise orthogonal ((5.2.c)). -/
  famPairwise : ∀ x ∈ famS, ∀ y ∈ famS, x ≠ y → ClassFunction.inner x y = 0
  /-- Family members are nonzero. -/
  famNe : ∀ x ∈ famS, x ≠ 0
  /-- Family members are supported in `CF(L,A)`. -/
  famSupp : ∀ x ∈ famS, x.support ⊆ supportInSubgroup A L
  /-- The (5.6) degree inequality (c): `2·a < ∑ᵢ aᵢ²/‖χᵢ‖²`. -/
  hdeg_c : 2 * (a : ℝ) < ∑ x ∈ famS,
    ((famRatio x : ℝ) / (ClassFunction.inner x x).re) ^ 2 * (ClassFunction.inner x x).re

namespace DadeChainStep

variable {hyp : S04.Hypothesis G A L}
variable {S₁ : Set (ClassFunction (↥L) ℂ)} {A' : Set ↥L} {χ : IrreducibleCharacter (↥L)}

/-- **The genuine per-step content advances coherence by one Dade step.**

Given the prior coherence `IsCoherent τ S₁ A'` and the genuine (6.6) per-step content `step`, the
adjoined set `S₁ ∪ {↑χ, (↑χ).conj}` is coherent.  This is the clean realization of one (5.6)
adjoining step against the real Dade base map: the Round-B `R(χ)` and (2.6.b) `ZIrr`-membership are
built internally, the running `τ₁ = τ` agreements are `rfl`/`extends_on_supported`, and the
genuine character data is read off `step`'s fields.  It is a single call to
`retarget_isCoherent_fromDade`. -/
noncomputable def advance (step : DadeChainStep hyp S₁ A' χ)
    (hS₁ : IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) S₁ A') :
    IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {(χ : ClassFunction (↥L) ℂ), (χ : ClassFunction (↥L) ℂ).conj}) A' := by
  have hmemS₁ : ∀ x ∈ step.famS, x ∈ S₁ := fun x hx => step.famS_eq ▸ Finset.mem_coe.mpr hx
  have hchi1mem : step.chi1 ∈ step.famS := by
    rw [← Finset.mem_coe, step.famS_eq]; exact step.hchi1
  -- The (5.6.1) source family bundle of `S₁`, with `chiFam = id` over `famS`.
  let B : CharacterFamilyBundle (L := ↥L) (χ : ClassFunction (↥L) ℂ) step.chi1 (step.a : ℝ)
      step.famS step.chi1 :=
    { i₁_mem := hchi1mem
      chiFam := id
      chi1_eq := rfl
      ratio := step.famRatio
      ratio_one := step.famRatio_chi1
      degree_eq := step.famDegree
      degree_chi := step.famDegree_chi
      chi_orthogonal := fun i hi => step.hχ_S1 i (hmemS₁ i hi)
      chiFam_pairwise := step.famPairwise }
  -- `⟨χ, a·χ₁⟩ = ⟨χ̄, a·χ₁⟩ = 0` and `(χ − a·χ₁)^τ ∈ ℤ[Irr G]` (supported difference).
  have hχaχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ)
      (step.a • step.chi1 : ClassFunction (↥L) ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ step.a step.chi1,
      OddOrder.RepresentationTheory.inner_smul_right, step.hχχ1, mul_zero]
  have hχbaraχ1 : ClassFunction.inner (χ : ClassFunction (↥L) ℂ).conj
      (step.a • step.chi1 : ClassFunction (↥L) ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ step.a step.chi1,
      OddOrder.RepresentationTheory.inner_smul_right, step.hχbarχ1, mul_zero]
  have htau1_mema : dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
      ((χ : ClassFunction (↥L) ℂ) - step.a • step.chi1) ∈ ZIrr G :=
    dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp step.hdiffasupp
      (Submodule.sub_mem _ χ.mem_ZIrr (nsmul_mem step.hchi1Z step.a))
  refine retarget_isCoherent_fromDade_X hyp hS₁ χ step.hreal step.hdiffsupp step.hdiffasupp
    htau1_mema hχaχ1 hχbaraχ1 step.hχχ step.hχbarχbar step.hχbarχ step.hχχbar' step.hchi1chi1
    step.Dmem step.hmemTau1Base step.hmemSupp step.hmemOrtho
    step.hχ_S1 step.hχbar_S1 step.hchi1 step.hchi1supp ?_
    (zSupportedSpan_adjoinPair_subset_span step.hmemSupp step.hchi1supp)
  -- The (5.6.2) collapse `hY`, proved from the family data (difference-support).
  exact dade_Y_collapse_of_family hyp
    (decompositionDaFromDadeOfDiff hyp χ step.hreal step.hdiffsupp step.hdiffasupp htau1_mema
      hχaχ1 hχbaraχ1 step.hχχbar')
    rfl B (fun i hi => hmemS₁ i hi) step.famNe
    step.famSupp (step.famSupp _ hchi1mem) step.hchi1Z step.hdiffasupp step.Dmem step.hmemTau1Base
    step.hmemOrtho htau1_mema step.hdeg_c

/-- **One `coherentPairChain` step, in the engine's accumulator shape, from the Dade isometry.**

Given the genuine per-step (6.6) content `step : DadeChainStep hyp (pairUnion S₀ pair i) A χ`
together with the requirement that the `i`-th adjoined pair is `{↑χ, (↑χ).conj}`
(`hpair0 : (pair i).1 = ↑χ`, `hpair1 : (pair i).2 = (↑χ).conj`), this produces the per-step map
`IsCoherent τ (pairUnion S₀ pair i) A → IsCoherent τ (pairUnion S₀ pair (i+1)) A` that the
`coherentPairChain` engine consumes: `advance` yields coherence of the union
`pairUnion S₀ pair i ∪ {↑χ, (↑χ).conj}`, and `pairUnion_succ_eq_union_pair` identifies that union
with the accumulator `pairUnion S₀ pair (i+1)`.

This is the `hstep` building block for `peterfalvi_66_coherence_of_X_from_dade`: each step is one
fully Dade-derived (5.6) adjoining, with the only remaining content being the source-side (6.6)
degree data packaged in `step`. -/
noncomputable def chainStepAdvance
    (hyp : S04.Hypothesis G A L)
    {S₀ : Set (ClassFunction (↥L) ℂ)} {A' : Set ↥L}
    (pair : ℕ → ClassFunction (↥L) ℂ × ClassFunction (↥L) ℂ) (i : ℕ)
    {χ : IrreducibleCharacter (↥L)}
    (hpair0 : (pair i).1 = (χ : ClassFunction (↥L) ℂ))
    (hpair1 : (pair i).2 = (χ : ClassFunction (↥L) ℂ).conj)
    (step : DadeChainStep hyp (pairUnion (L := ↥L) S₀ pair i) A' χ)
    (hS₁ : IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (pairUnion (L := ↥L) S₀ pair i) A') :
    IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (pairUnion (L := ↥L) S₀ pair (i + 1)) A' :=
  (pairUnion_succ_eq_union_pair (L := ↥L) hpair0 hpair1).symm ▸ step.advance hS₁

end DadeChainStep

/-- **Peterfalvi (6.6): `X = S − S(Z)` is coherent — instantiated at the real Dade isometry.**

The (6.6) conclusion with the coherence base map **fixed** to the genuine Dade base map
`τ = dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)`, and the per-step `hstep` of the
`coherentPairChain` engine **constructed** — no longer posited — from the Dade isometry plus the
prior step's coherence.

Compared to the abstract `peterfalvi_66_coherence_of_X`, the opaque `hstep` hypothesis is replaced
by, for each adjoined pair `i < N`:
* `hpairχ i hi` — an irreducible character `χᵢ` of `L` realizing the `i`-th pair as `{χᵢ, χ̄ᵢ}`
  (`(pair i) = (↑χᵢ, (↑χᵢ).conj)`); and
* `hstepData i hi` — the genuine per-step (6.6) degree/orthogonality content
  `DadeChainStep hyp (pairUnion S₀ pair i) A χᵢ` over the running accumulator.

Each step is then discharged by `DadeChainStep.chainStepAdvance` — one fully Dade-derived (5.6)
adjoining (`retarget_isCoherent_fromDade`): the orthonormal image `R(χᵢ)`
(`dadeOrthonormalCharacterImageFamily`, Round B), the `ZIrr`-membership of the images
(`dadeIntegralCharacterMap_mem_ZIrr_of_supported`, (2.6.b)), the inner-product preservation
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`), and the running-`τ₁ = τ` agreements
(`IsCoherent.extends_on_supported`) are all supplied internally from the Dade isometry.  The folded
chain (`coherentPairChain`) and the enumeration cover (`pairUnion_eq_of_enumCover`) then derive
`IsCoherent τ X A`.

This makes the §5/§6 coherence engine **fully constructive against the real Dade `τ`**: the only
inputs that remain are the genuine (6.6) character-degree content (the enumeration `e`, the cover
`hcoverIdx`, the base coherence `h0`, and the per-step `hstepData`/`hpairχ`), none of which is the
Dade isometry's responsibility.  It is the (6.6) coherence-of-X with its (5.6) per-step machinery
dischargeable from the Dade isometry. -/
noncomputable def peterfalvi_66_coherence_of_X_from_dade
    (hyp : S04.Hypothesis G A L) {A' : Set ↥L}
    {X S₀ : Set (ClassFunction (↥L) ℂ)}
    (hXfin : X.Finite)
    {e : Fin X.ncard → ClassFunction (↥L) ℂ} (hsurj : ∀ χ ∈ X, ∃ i, e i = χ)
    (pair : ℕ → ClassFunction (↥L) ℂ × ClassFunction (↥L) ℂ) (N : ℕ)
    (hS₀ : S₀ ⊆ X) (hpairs : ∀ j, j < N → pairSet (L := ↥L) pair j ⊆ X)
    (hcoverIdx : ∀ i : Fin X.ncard,
      e i ∈ S₀ ∨ ∃ j, j < N ∧ e i ∈ pairSet (L := ↥L) pair j)
    (h0 : IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) S₀ A')
    (hpairχ : ∀ i, i < N → IrreducibleCharacter (↥L))
    (hpair0 : ∀ (i : ℕ) (hi : i < N), (pair i).1 = ((hpairχ i hi : IrreducibleCharacter (↥L)) :
      ClassFunction (↥L) ℂ))
    (hpair1 : ∀ (i : ℕ) (hi : i < N), (pair i).2 =
      ((hpairχ i hi : IrreducibleCharacter (↥L)) : ClassFunction (↥L) ℂ).conj)
    (hstepData : ∀ (i : ℕ) (hi : i < N),
      DadeChainStep hyp (pairUnion (L := ↥L) S₀ pair i) A' (hpairχ i hi)) :
    IsCoherent (dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) X A' :=
  peterfalvi_66_coherence_of_X hXfin hsurj pair N hS₀ hpairs hcoverIdx h0
    (fun i hi hS₁ =>
      DadeChainStep.chainStepAdvance hyp pair i (hpair0 i hi) (hpair1 i hi)
        (hstepData i hi) hS₁)

end DadeBaseMap

end OddOrder.Peterfalvi.S07

