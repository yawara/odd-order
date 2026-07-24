import OddOrder.Peterfalvi.S07_Coherence.CoherenceUnion

/-!
# Peterfalvi (5.6.1) — the character family bundle

The `CharacterFamilyBundle` layer and the (5.6.1) section.

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
-/

namespace OddOrder.Peterfalvi.S07
open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]


/-! ### Peterfalvi (5.6.1): the family bundle

The (5.6) coherence-union argument carries a whole **family** `{χᵢ}_{i ∈ s} ⊆ S₁` with `χ₁` a
distinguished member, integer degree ratios `aᵢ` (`χᵢ(1) = aᵢ·χ₁(1)`, `a₁ = 1`), squared norms
`mᵢ = ‖χᵢ‖²`, and the auxiliary isometry `τ₁` on `ℤ[S₁]` extending `τ`.  The single non-trivial
fact threaded through (5.6.1)→(5.6.2) is the **cross-difference orthogonality**

`⟨(χ − a·χ₁), (χᵢ − aᵢ·χ₁)⟩ = a·aᵢ·‖χ₁‖²`  (for `i ≠ 1`),

derived from `χ ⊥ S₁` and pairwise orthogonality of `S₁`.  The bundle records the family data and
*derives* this identity (it is not posited): `crossDifference_inner` below. -/

open OddOrder.RepresentationTheory in
/-- **Peterfalvi (5.6.1) family bundle.**

Bundles the family `{χᵢ}_{i ∈ s} ⊆ S₁` (with distinguished `χ₁ = chiFam i₁`), the integer degree
ratios `ratio i = aᵢ` (`χᵢ(1) = aᵢ·χ₁(1)`, `ratio i₁ = 1`), the squared norms `normSq i = ‖χᵢ‖²`,
and the orthogonality data threaded through (5.6.1): `χ` is orthogonal to every `χᵢ` and to every
`χ̄ᵢ`, and `{χᵢ}` is pairwise orthogonal.  These are exactly the `(5.2)`-level inputs; the bundle
*derives* the cross-difference orthogonality `crossDifference_inner` rather than assuming it.

This carries no extension witness for the union `S₁ ∪ {χ, χ̄}`; it is pure source-side family data
(the `degree`, `norm` and `orthogonality` hypotheses of (5.6)), constructed from `(5.2)`. -/
structure CharacterFamilyBundle
    (chi chi1 : ClassFunction L ℂ) (a : ℝ)
    {ι : Type*} (s : Finset ι) (i₁ : ι)
    [Fintype L] [Invertible (Nat.card L : ℂ)] where
  /-- The distinguished index `i₁` lies in the family. -/
  i₁_mem : i₁ ∈ s
  /-- The characters of the family `S₁`. -/
  chiFam : ι → ClassFunction L ℂ
  /-- `χ₁ = chiFam i₁`. -/
  chi1_eq : chiFam i₁ = chi1
  /-- The integer degree ratios `aᵢ`. -/
  ratio : ι → ℕ
  /-- `a₁ = 1`. -/
  ratio_one : ratio i₁ = 1
  /-- The degree scaling `χᵢ(1) = aᵢ·χ₁(1)`, recorded via `characterDegree`. -/
  degree_eq : ∀ i ∈ s, OddOrder.Peterfalvi.S03.characterDegree (chiFam i) =
    (ratio i : ℂ) * OddOrder.Peterfalvi.S03.characterDegree chi1
  /-- The complex degree ratio `a = χ(1)/χ₁(1)`. -/
  degree_chi : OddOrder.Peterfalvi.S03.characterDegree chi =
    (a : ℂ) * OddOrder.Peterfalvi.S03.characterDegree chi1
  /-- `χ` is orthogonal to every family member. -/
  chi_orthogonal : ∀ i ∈ s, ClassFunction.inner chi (chiFam i) = 0
  /-- `{χᵢ}` is pairwise orthogonal. -/
  chiFam_pairwise : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
    ClassFunction.inner (chiFam i) (chiFam j) = 0

namespace CharacterFamilyBundle

open OddOrder.RepresentationTheory

variable {chi chi1 : ClassFunction L ℂ} {a : ℝ}
variable {ι : Type*} {s : Finset ι} {i₁ : ι}
variable [Fintype L] [Invertible (Nat.card L : ℂ)]

/-- `‖χ₁‖²` written through the bundle. -/
abbrev normSq1 (_B : CharacterFamilyBundle (L := L) chi chi1 a s i₁) : ℂ :=
  ClassFunction.inner chi1 chi1

/-- **Peterfalvi (5.6.1) cross-difference orthogonality (source side).**

For `i ∈ s` with `i ≠ i₁`, the inner product of the differences `χ − a·χ₁` and
`χᵢ − aᵢ·χ₁` equals `a·aᵢ·‖χ₁‖²`.

`⟨χ − aχ₁, χᵢ − aᵢχ₁⟩ = ⟨χ,χᵢ⟩ − aᵢ⟨χ,χ₁⟩ − a⟨χ₁,χᵢ⟩ + a·aᵢ⟨χ₁,χ₁⟩`.  The first three
inner products vanish: `⟨χ,χᵢ⟩ = ⟨χ,χ₁⟩ = 0` since `χ ⊥ S₁`, and `⟨χ₁,χᵢ⟩ = 0` since `i ≠ i₁`
and `{χᵢ}` is pairwise orthogonal.  Only `a·aᵢ·‖χ₁‖²` survives. -/
theorem crossDifference_inner (B : CharacterFamilyBundle (L := L) chi chi1 a s i₁)
    {i : ι} (hi : i ∈ s) (hii₁ : i ≠ i₁) :
    ClassFunction.inner (chi - (a : ℂ) • chi1)
        (B.chiFam i - (B.ratio i : ℂ) • chi1) =
      (a : ℂ) * (B.ratio i : ℂ) * ClassFunction.inner chi1 chi1 := by
  have hchi_i : ClassFunction.inner chi (B.chiFam i) = 0 := B.chi_orthogonal i hi
  have hchi_1 : ClassFunction.inner chi chi1 = 0 := by
    have := B.chi_orthogonal i₁ B.i₁_mem; rwa [B.chi1_eq] at this
  have h1_i : ClassFunction.inner chi1 (B.chiFam i) = 0 := by
    have := B.chiFam_pairwise i₁ B.i₁_mem i hi (fun h => hii₁ h.symm)
    rwa [B.chi1_eq] at this
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, ClassFunction.inner_smul_left,
    OddOrder.RepresentationTheory.inner_smul_right,
    OddOrder.RepresentationTheory.inner_smul_right, ClassFunction.inner_smul_left,
    hchi_i, hchi_1, h1_i]
  rw [star_natCast]
  ring

end CharacterFamilyBundle

section Peterfalvi561

open OddOrder.RepresentationTheory

variable {τ : IntegralCharacterMap L G} {χ : ClassFunction L ℂ}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- **Peterfalvi (5.6.1)→(5.6.2): the `Y`-collapse `Y = a·χ₁^{τ₁}` from the family data.**

This is the producer of the (5.6.2) collapse `Da.Y = a·χ₁^{τ₁}` (the `hY` consumed by the
per-step (5.6.3) adjoining machinery), *constructed* from the (5.6) family data rather than posited.

For the `ψ = a·χ₁` decomposition `Da : CharacterPsiDecomposition τ χ (a·χ₁)` (so
`(χ − a·χ₁)^{τ₁} = Da.X − Da.Y`, `Da.X ∈ ℤ[R(χ)]`, `Da.Y ⊥ R(χ)`), and the source-side family
bundle `B` of `S₁ = {χᵢ}` (degree ratios `aᵢ = B.ratio i`, `a₁ = 1`, pairwise orthogonal,
`χ ⊥ S₁`), the orthogonal part `Y` decomposes (5.6.1) as

`Y = a·χ₁^{τ₁} − λ·∑ᵢ (aᵢ/‖χᵢ‖²)·χᵢ^{τ₁} + Z`     (mmd L73, integer `λ`)

and then collapses (5.6.2) to `Y = a·χ₁^{τ₁}`.  The proof:

* **projection (existence half)** — `Y` projects onto the orthogonal family `vc i = χᵢ^{τ₁}`
  (orthogonal with grams `mc i = ‖χᵢ‖²` by the isometry `hiso_fam` and `B.chiFam_pairwise`) plus an
  orthogonal residual `Z` (`exists_orthogonalProjection_of_orthogonal_family`), with coefficients
  `c i = ⟨Y, χᵢ^{τ₁}⟩/‖χᵢ‖²`;
* **coefficient computation (mmd L79)** — for `i ≠ i₁`, the source cross-orthogonality
  `⟨χ−aχ₁, χᵢ−aᵢχ₁⟩ = a·aᵢ·‖χ₁‖²` (`B.crossDifference_inner`) transported through the isometry
  (`hiso_cross`) and the decomposition (`Da.tau1_image`, `Da.X ⊥ χᵢ^{τ₁}` from `hXortho`) gives
  `c i·‖χᵢ‖² = aᵢ·‖χ₁‖²·(c₁ − a)`, i.e. a single `λ` (`λ := (a − c₁)·‖χ₁‖²`) with
  `c i = a·[i=i₁] − λ·(aᵢ/‖χᵢ‖²)`;
* **integrality (mmd L83)** — `λ = a·‖χ₁‖² − ⟨Y, χ₁^{τ₁}⟩ ∈ ℤ` since `‖χ₁‖² ∈ ℤ` (`hmc1_int`) and
  `⟨Y, χ₁^{τ₁}⟩ ∈ ℤ` (both `Y` and `χ₁^{τ₁}` are virtual characters, `inner_mem_ZIrr_int`);
* **collapse** — `Y_eq_nsmul_tau1_of_lambdaForm` (the integer-forcing capstone
  `lambda_eq_zero_and_Z_eq_zero` under the degree inequality `hdeg_c`) forces `λ = 0`, `Z = 0`.

The hypotheses `hiso_fam`/`hiso_cross` (the running isometry preserves the inner product on the
family and the difference generators), `hXortho` (`R(χ) ⊥ S₁^{τ₁}`, by (5.5)+(5.2.e)), and the
`ZIrr`-memberships are exactly the (5.6) inputs; against the Dade base map they are discharged by
`dadeIntegralCharacterMap_inner_eq_on_supported_span`, the per-member (5.5) decompositions, and
`dadeIntegralCharacterMap_mem_ZIrr_of_supported`. -/
theorem CharacterPsiDecomposition.Y_collapse_of_family
    {a : ℕ} {chi1 : ClassFunction L ℂ}
    (Da : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • chi1))
    {ι : Type*} {s : Finset ι} {i₁ : ι}
    (B : CharacterFamilyBundle (L := L) χ chi1 (a : ℝ) s i₁)
    (mc : ι → ℝ)
    (hmc : ∀ i ∈ s, ClassFunction.inner (B.chiFam i) (B.chiFam i) = (mc i : ℂ))
    (hmc_pos : ∀ i ∈ s, 0 < mc i)
    (hmc1_int : ∃ z : ℤ, mc i₁ = (z : ℝ))
    (hiso_fam : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (Da.tau1 (B.chiFam i)) (Da.tau1 (B.chiFam j)) =
        ClassFunction.inner (B.chiFam i) (B.chiFam j))
    (hiso_cross : ∀ i ∈ s,
      ClassFunction.inner (Da.tau1 (χ - a • chi1))
          (Da.tau1 (B.chiFam i - B.ratio i • chi1)) =
        ClassFunction.inner (χ - a • chi1) (B.chiFam i - B.ratio i • chi1))
    (hXortho : ∀ α ∈ Da.imageFamily.imageSet, ∀ i ∈ s,
      ClassFunction.inner α (Da.tau1 (B.chiFam i)) = 0)
    (hvc1_ZIrr : Da.tau1 chi1 ∈ ZIrr G)
    (hdiff_ZIrr : Da.tau1 (χ - a • chi1) ∈ ZIrr G)
    (hdeg_c : 2 * (a : ℝ) < ∑ i ∈ s, ((B.ratio i : ℝ) / mc i) ^ 2 * mc i) :
    Da.Y = a • Da.tau1 chi1 := by
  classical
  set vc : ι → ClassFunction G ℂ := fun i => Da.tau1 (B.chiFam i) with hvc
  set rc : ι → ℝ := fun i => (B.ratio i : ℝ) / mc i with hrc
  have hnorm1 : ClassFunction.inner chi1 chi1 = (mc i₁ : ℂ) := by
    have := hmc i₁ B.i₁_mem; rwa [B.chi1_eq] at this
  have hmc_ne : ∀ i ∈ s, mc i ≠ 0 := fun i hi => ne_of_gt (hmc_pos i hi)
  have hvc1 : vc i₁ = Da.tau1 chi1 := by simp only [hvc, B.chi1_eq]
  -- (1) orthogonal family `{vc i}` with grams `mc i`.
  have horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (vc i) (vc j) = if i = j then (mc i : ℂ) else 0 := by
    intro i hi j hj
    simp only [hvc]
    rw [hiso_fam i hi j hj]
    by_cases h : i = j
    · subst h; rw [if_pos rfl]; exact hmc i hi
    · rw [if_neg h]; exact B.chiFam_pairwise i hi j hj h
  -- (2) orthogonal projection of `Y` onto the family.
  obtain ⟨c, Z, hc_def, hYsum, hZ⟩ :=
    exists_orthogonalProjection_of_orthogonal_family s vc mc Da.Y horth hmc_ne
  have hYvc : ∀ i ∈ s, ClassFunction.inner Da.Y (vc i) = c i * (mc i : ℂ) := by
    intro i hi
    rw [hc_def i hi, div_mul_cancel₀]
    exact_mod_cast hmc_ne i hi
  -- `Da.X ⊥ vc i` (from `R(χ) ⊥ S₁^{τ₁}`).
  have hXvc : ∀ i ∈ s, ClassFunction.inner Da.X (vc i) = 0 := by
    intro i hi
    rw [Da.X_eq, inner_sum_left]
    apply Finset.sum_eq_zero
    intro α hα
    rw [ClassFunction.inner_smul_left]
    simp only [hvc]
    rw [hXortho α hα i hi, mul_zero]
  -- `Da.X`, `Da.Y` are virtual characters.
  have hXmem : Da.X ∈ ZIrr G := by
    rw [Da.X_eq]
    apply Submodule.sum_mem
    intro α hα
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ (Da.coeff α) (Da.imageFamily.mem_ZIrr α hα)
  have hYeq : Da.Y = Da.X - Da.tau1 (χ - a • chi1) := by
    have h := Da.tau1_image; rw [h]; abel
  have hYmem : Da.Y ∈ ZIrr G := by
    rw [hYeq]; exact Submodule.sub_mem _ hXmem hdiff_ZIrr
  -- (3) the coefficient relation for `i ≠ i₁`.
  have hcross : ∀ i ∈ s, i ≠ i₁ →
      c i * (mc i : ℂ) = (B.ratio i : ℂ) * (mc i₁ : ℂ) * (c i₁ - (a : ℂ)) := by
    intro i hi hii₁
    have hcd := B.crossDifference_inner hi hii₁
    rw [show ((a : ℝ) : ℂ) • chi1 = a • chi1 by
          rw [Complex.ofReal_natCast, Nat.cast_smul_eq_nsmul],
        show (B.ratio i : ℂ) • chi1 = B.ratio i • chi1 from Nat.cast_smul_eq_nsmul _ _ _,
        hnorm1, ← hiso_cross i hi, Da.tau1_image,
        show Da.tau1 (B.chiFam i - B.ratio i • chi1) = vc i - B.ratio i • vc i₁ by
          rw [map_sub, map_nsmul]; simp only [hvc, B.chi1_eq],
        show (B.ratio i : ℕ) • vc i₁ = (B.ratio i : ℂ) • vc i₁ from
          (Nat.cast_smul_eq_nsmul _ _ _).symm,
        ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
        OddOrder.RepresentationTheory.inner_smul_right,
        hXvc i hi, hXvc i₁ B.i₁_mem, hYvc i hi, hYvc i₁ B.i₁_mem, star_natCast] at hcd
    push_cast at hcd ⊢
    linear_combination -hcd
  -- the (complex) `λ` and its integrality.
  set lam_c : ℂ := ((a : ℂ) - c i₁) * (mc i₁ : ℂ) with hlam_c
  obtain ⟨z, hz⟩ := hmc1_int
  obtain ⟨w, hw⟩ := ClassFunction.inner_mem_ZIrr_int hYmem hvc1_ZIrr
  have hci1 : c i₁ * (mc i₁ : ℂ) = (w : ℂ) := by
    rw [← hYvc i₁ B.i₁_mem, hvc1]; exact hw
  set lam : ℤ := (a : ℤ) * z - w with hlamdef
  have hlam_int : lam_c = (lam : ℂ) := by
    rw [hlam_c, sub_mul, hci1, hz, hlamdef]; push_cast; ring
  -- (4) the per-index coefficient form `c i = a·[i=i₁] − λ·(aᵢ/‖χᵢ‖²)`.
  have hcoeff : ∀ i ∈ s, c i = (a : ℂ) * (if i = i₁ then 1 else 0) - lam_c * (rc i : ℂ) := by
    intro i hi
    have hmci : (mc i : ℂ) ≠ 0 := by exact_mod_cast hmc_ne i hi
    have hmci1 : (mc i₁ : ℂ) ≠ 0 := by exact_mod_cast hmc_ne i₁ B.i₁_mem
    have hrc_i : (rc i : ℂ) = (B.ratio i : ℂ) / (mc i : ℂ) := by
      simp only [hrc]; push_cast; ring
    by_cases h : i = i₁
    · rw [h, if_pos rfl, mul_one, hlam_c]
      have hrc_i1 : (rc i₁ : ℂ) = 1 / (mc i₁ : ℂ) := by
        simp only [hrc, B.ratio_one]; push_cast; ring
      rw [hrc_i1]
      field_simp
      ring
    · have key := hcross i hi h
      rw [if_neg h, mul_zero, zero_sub, hlam_c, hrc_i]
      field_simp
      linear_combination key
  -- (5) assemble the λ-form and apply the collapse.
  have hYform : Da.Y =
      (a : ℂ) • Da.tau1 chi1 - lam_c • (∑ i ∈ s, (rc i : ℂ) • vc i) + Z := by
    rw [hYsum]
    congr 1
    rw [← hvc1, Finset.sum_congr rfl (fun i hi => by rw [hcoeff i hi])]
    have hsplit : ∀ i ∈ s,
        ((a : ℂ) * (if i = i₁ then (1 : ℂ) else 0) - lam_c * (rc i : ℂ)) • vc i =
          (if i = i₁ then (a : ℂ) • vc i else 0) - lam_c • ((rc i : ℂ) • vc i) := by
      intro i _
      by_cases h : i = i₁
      · rw [if_pos h, if_pos h, mul_one]; module
      · rw [if_neg h, if_neg h, mul_zero]; module
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq' s i₁,
      if_pos B.i₁_mem, ← Finset.smul_sum]
  have hψ : (ClassFunction.inner (a • chi1 : ClassFunction L ℂ) (a • chi1)).re =
      (a : ℝ) ^ 2 * mc i₁ := by
    rw [show (a • chi1 : ClassFunction L ℂ) = (a : ℂ) • chi1 from
        (Nat.cast_smul_eq_nsmul ℂ a chi1).symm, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hnorm1, star_natCast,
      show (a : ℂ) * ((a : ℂ) * (mc i₁ : ℂ)) = (((a : ℝ) ^ 2 * mc i₁ : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have hr₁ : rc i₁ * mc i₁ = 1 := by
    simp only [hrc, B.ratio_one, Nat.cast_one]
    rw [div_mul_cancel₀]
    exact hmc_ne i₁ B.i₁_mem
  rw [hlam_int] at hYform
  exact Da.Y_eq_nsmul_tau1_of_lambdaForm s i₁ B.i₁_mem lam Z vc mc rc hvc1 hYform horth hZ hψ hr₁
    hdeg_c

end Peterfalvi561


end OddOrder.Peterfalvi.S07
