/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CaseBXunionY

/-!
# Peterfalvi §8: case-(B) the textbook `X`-coherence on the certain-type columns

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, (6.8.2) (mmd `references/peterfalvi/04.8` L178-224).

This leaf builds the **textbook** `X`-coherence on the certain-type column set, whose extension sends
each column `μ_j = columnSum χ₂` to its **own `(6.8.2.3)` projection image** `X_χ` (the value
`τ(μ_j − a₀·η₁) + a₀·η₁^{τ₁}` produced by the per-constituent decomposition), **not** to the
canonical certain-type coherence image `cTE(μ_j) = δ_j ∑_i ω_{ij}^σ`.

This is the key textbook-faithful replacement for the cTE-glue base
(`coherentCertainTypeSet_union_Yset`, `S08_CaseBXunionY`).  In the cTE-glue route the `Y`-glue
diagonal demands `cTE(μ_{k0}) = X_χ` — the *over-constrained* `(6.8.2.3)` "self-vs-conjugate"
identity `T = ⟨τ(μ_j − a·η₁), cTE(μ̄_j)⟩ = 0`, which is *not* forced by the isometry structure and
is *not* established by the textbook (Peterfalvi (6.8.1) explicitly leaves `X = χ₁^{τ₁}` vs
`X = −χ₂^{τ₂}` to a relabelling, and case (B) `(6.8.2.3)` only proves `X ⊥ Y^{τ₁}`).

The textbook instead defines `τ₂` on `ℤ[X∪Y]` to coincide with `τ` on the supported lattice and to
send `η₁ ↦ Y`; the `X`-images are then *whatever the projection gives*, `τ₂(χ) = X_χ`.  Since the
coherence conditions only constrain the extension on `ℤ[certainTypeSet]` (and the columns are
linearly independent — disjoint constituent supports across distinct `W₂`-duals), this `X_χ`-valued
extension is constructible directly via `Basis.constr`, and its `(5.1)` fields reduce to the
column-level facts `hXanchored` (`(6.8.2.3)` image), `hXinner` (cross-column isometry, from the Dade
isometry of `τ`), `hXzirr` (`X_χ ∈ ℤ[Irr G]`) — **all of which are `T = 0`-free**.

Reference note: `notes/peterfalvi/s08_6_8_assembly_plan.md` (session 48 cont.⁴).
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **The basis rule for the textbook `X_χ`-extension.**  Sends the `0`-th-row certain-type
irreducible `μ_{0,χ₂}` of each column to that column's target image `Ximg χ₂`, and every other
irreducible to `0`.  The witness column `χ₂` is selected uniquely by `columnFamily_mu_injective`
(the grid `(χ₂, i) ↦ μ_{ij}` is injective, so `μ_{0,χ₂}` determines `χ₂`).

The "all on the `0`-th row" choice is one of many splittings of the column image `Ximg χ₂` across the
`w₁` constituents `{μ_{ij}}`; any splitting yields the same value on the column sum `μ_j = ∑_i μ_{ij}`,
and the coherence fields only see column-level values. -/
noncomputable def xChiExtensionFun
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ) :
    IrreducibleCharacter ↥L → ClassFunction G ℂ :=
  fun ω =>
    if hex : ∃ p : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) × Fin (Nat.card h46.W1),
        (h46.columnFamily p.1).mu p.2 = ω ∧ p.2 = 0 then Ximg hex.choose.1 else 0

/-- **The textbook `X_χ`-extension** `ν` (the case-(B) `τ₂` on the certain-type columns): the global
`ℤ`-linear `CF(L) → CF(G)` built from `xChiExtensionFun` on the basis `Irr(L)`. -/
noncomputable def xChiExtension
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G :=
  ((OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr ℂ
    (xChiExtensionFun h46 Ximg)).restrictScalars ℤ

/-- The `X_χ`-extension on the `0`-th-row certain-type irreducible: `ν(μ_{0,χ₂}) = Ximg χ₂`. -/
theorem xChiExtension_mu_zero
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    xChiExtension h46 Ximg ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ) = Ximg χ₂ := by
  classical
  rw [xChiExtension, LinearMap.restrictScalars_apply]
  conv_lhs => rw [← OddOrder.Peterfalvi.S05.irreducibleCharacterBasis_apply (G := ↥L)
    ((h46.columnFamily χ₂).mu 0)]
  rw [(OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr_basis ℂ _
    ((h46.columnFamily χ₂).mu 0), xChiExtensionFun]
  have hex : ∃ p : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) × Fin (Nat.card h46.W1),
      (h46.columnFamily p.1).mu p.2 = (h46.columnFamily χ₂).mu 0 ∧ p.2 = 0 := ⟨(χ₂, 0), rfl, rfl⟩
  rw [dif_pos hex]
  have hchoose : hex.choose = (χ₂, 0) := h46.columnFamily_mu_injective hex.choose_spec.1
  rw [hchoose]

/-- The `X_χ`-extension on a higher-row certain-type irreducible: `ν(μ_{iχ₂}) = 0` for `i ≠ 0`. -/
theorem xChiExtension_mu_ne_zero
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) {i : Fin (Nat.card h46.W1)} (hi : i ≠ 0) :
    xChiExtension h46 Ximg ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) = 0 := by
  classical
  rw [xChiExtension, LinearMap.restrictScalars_apply]
  conv_lhs => rw [← OddOrder.Peterfalvi.S05.irreducibleCharacterBasis_apply (G := ↥L)
    ((h46.columnFamily χ₂).mu i)]
  rw [(OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr_basis ℂ _
    ((h46.columnFamily χ₂).mu i), xChiExtensionFun, dif_neg]
  rintro ⟨p, heq, hp2⟩
  have hpair : p = (χ₂, i) := h46.columnFamily_mu_injective heq
  rw [hpair] at hp2
  exact hi hp2

/-- **The `X_χ`-extension on a column sum**: `ν(μ_j) = ν(∑_i μ_{ij}) = Ximg χ₂`.  Only the `0`-th-row
term survives (`xChiExtension_mu_zero`/`xChiExtension_mu_ne_zero`). -/
theorem xChiExtension_columnSum
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    xChiExtension h46 Ximg (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) = Ximg χ₂ := by
  classical
  rw [OddOrder.Peterfalvi.S06.columnSum_def, map_sum,
    Finset.sum_eq_single (0 : Fin (Nat.card h46.W1))]
  · exact xChiExtension_mu_zero h46 Ximg χ₂
  · intro i _ hi; exact xChiExtension_mu_ne_zero h46 Ximg χ₂ hi
  · intro h0; exact absurd (Finset.mem_univ _) h0

/-- **A `(5.4)` decomposition's `X`-part is a virtual character** (`D.X ∈ ℤ[Irr G]`).  Generic
brick discharging the `hXzirr` obligation of the textbook `X_χ`-coherence: `X = ∑_{α ∈ R(χ)} coeff α • α`
(`X_eq`) is a `ℤ`-combination of the orthonormal image-family members `α ∈ ZIrr G`
(`imageFamily.mem_ZIrr`).  For the column decomposition `columnDecompositionTau`, `imageFamily =
columnRFamilyTau` (`imageSet = certainTypeR.imageSet`, the signed `σ`-images), so its `X` lands in
`ZIrr G`. -/
theorem characterPsiDecomposition_X_mem_ZIrr
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G} {χ ψ : ClassFunction ↥L ℂ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ) : D.X ∈ ZIrr G := by
  rw [D.X_eq]
  exact Submodule.sum_mem _ (fun α hα => by
    rw [Int.cast_smul_eq_zsmul ℂ (D.coeff α) α]
    exact Submodule.smul_mem _ (D.coeff α) (D.imageFamily.mem_ZIrr α hα))

/-- **The cross-column isometry `hXinner` follows from the anchored image `hXanchored`** (no separate
Y-pinning argument needed).  Writing `Xⱼ = τ(μⱼ − a₀·η₁) + a₀·ν₁` (`ν₁ = η₁^{τ₁}`, from the
`(6.8.2.3)` anchored image), the Dade isometry of `τ` on the `H^#`-supported `μⱼ − a₀·η₁` plus
`Xⱼ ⊥ ν₁` (`hmix`), `column ⊥ Y`, and `‖η₁‖² = ‖ν₁‖² = 1` give
`⟨Xⱼ, Xₗ⟩ = ⟨μⱼ − a₀η₁, μₗ − a₀η₁⟩ + a₀² − a₀² − a₀² + a₀² = ⟨μⱼ, μₗ⟩`.

This is the key simplification of the case-(B) discharge: it reduces the two hard-core obligations
(`hXanchored`, `hXinner`) of `coherentCertainTypeSet_union_Yset_via_anchoredImages` to the single
`hXanchored` (the `(6.8.2.2)` aggregate `Y`-pinning); `hXinner` is then *derived*. -/
theorem xchi_inner_eq_of_anchored
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) {a₀ : ℕ}
    {Xj Xl : ClassFunction G ℂ}
    {χ₂ χ₂' : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ}
    (hanc : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁)
      = Xj - a₀ • cY.extension η₁)
    (hanc' : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂' - a₀ • η₁)
      = Xl - a₀ • cY.extension η₁)
    (hmix : ClassFunction.inner Xj (cY.extension η₁) = 0)
    (hmix' : ClassFunction.inner Xl (cY.extension η₁) = 0)
    (hsupp : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hsupp' : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂' - a₀ • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    ClassFunction.inner Xj Xl
      = ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
          (OddOrder.Peterfalvi.S06.columnSum h46 χ₂') := by
  classical
  set ν := cY.extension η₁ with hνdef
  -- `Xⱼ = τ(μⱼ − a₀η₁) + a₀·ν` (rearranged anchored image), in `ℂ`-smul form.
  have hXj : Xj = hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁) + (a₀ : ℂ) • ν := by
    rw [hanc, ← Nat.cast_smul_eq_nsmul ℂ a₀ ν]; abel
  have hXl : Xl = hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂' - a₀ • η₁) + (a₀ : ℂ) • ν := by
    rw [hanc', ← Nat.cast_smul_eq_nsmul ℂ a₀ ν]; abel
  -- norm/orthogonality scalar facts.
  have hηirr : IsIrreducibleCharacter η₁ := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hηη : ClassFunction.inner η₁ η₁ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
    rwa [if_pos rfl] at h
  have hνν : ClassFunction.inner ν ν = 1 := by
    rw [hνdef, cY.extension_inner_eq η₁ η₁ (Submodule.subset_span hη₁)
      (Submodule.subset_span hη₁), hηη]
  have hcolj : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) η₁ = 0 :=
    inner_columnSum_Yset_eq_zero hyp h46 hW1 hη₁ χ₂
  have hcoll : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂') η₁ = 0 :=
    inner_columnSum_Yset_eq_zero hyp h46 hW1 hη₁ χ₂'
  -- `⟨τⱼ, τₗ⟩ = ⟨μⱼ, μₗ⟩ + a₀²` (Dade isometry + the `H^#`-supported difference expansion).
  have hττ : ClassFunction.inner
        (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁))
        (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂' - a₀ • η₁))
      = ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
          (OddOrder.Peterfalvi.S06.columnSum h46 χ₂') + (a₀ : ℂ) ^ 2 := by
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dade hyp.hconj
        (S := ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁,
          OddOrder.Peterfalvi.S06.columnSum h46 χ₂' - a₀ • η₁} : Set (ClassFunction ↥L ℂ)))
        (by intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl; exacts [hsupp, hsupp'])
        (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))]
    simp only [← Nat.cast_smul_eq_nsmul ℂ a₀ η₁, ClassFunction.inner_sub_left,
      ClassFunction.inner_sub_right, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
    rw [hcolj, hηη, OddOrder.RepresentationTheory.inner_conj_symm
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂') η₁, hcoll, star_zero]
    ring
  -- the cross-terms `⟨τⱼ, ν⟩ = ⟨ν, τₗ⟩ = −a₀`.
  have hτjν : ClassFunction.inner
      (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁)) ν = -(a₀ : ℂ) := by
    rw [hanc]
    simp only [← Nat.cast_smul_eq_nsmul ℂ a₀ ν, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left]
    rw [hmix, hνν]; ring
  have hτlν : ClassFunction.inner
      (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂' - a₀ • η₁)) ν = -(a₀ : ℂ) := by
    rw [hanc']
    simp only [← Nat.cast_smul_eq_nsmul ℂ a₀ ν, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left]
    rw [hmix', hνν]; ring
  have hντl : ClassFunction.inner ν
      (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂' - a₀ • η₁)) = -(a₀ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hτlν, star_neg, star_natCast]
  -- assemble: `⟨Xⱼ, Xₗ⟩ = ⟨τⱼ,τₗ⟩ + a₀⟨τⱼ,ν⟩ + a₀⟨ν,τₗ⟩ + a₀²⟨ν,ν⟩`.
  rw [hXj, hXl]
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
  rw [hττ, hτjν, hντl, hνν]; ring

/-- **The textbook case-(B) `X`-coherence on the certain-type columns** (Peterfalvi (6.8.2),
`X_χ`-route).  The Sibley–Dade map `hyp.tau` is coherent on `certainTypeSet h46 k` with the extension
`ν = xChiExtension h46 Ximg` sending each column `μ_j = columnSum χ₂` to its `(6.8.2.3)` projection
image `Ximg χ₂` — **not** to the certain-type coherence image `cTE(μ_j)`.

All three coherence conditions reduce to column-level facts, free of the `T = 0` over-constraint:
* `extension_inner_eq` — the cross-column isometry `hXinner` (`⟨X_χ, X_χ'⟩ = ⟨μ_j, μ_l⟩`, which
  follows from the Dade isometry of `τ` applied to `μ_j − a₀·η₁`, `μ_l − a₀·η₁`);
* `extends_on_supported` — on the generating column differences `μ_j − μ_k`, `ν(μ_j − μ_k) =
  Ximg χ₂ − Ximg k = τ(μ_j − μ_k)` by subtracting the two `(6.8.2.3)` anchored images `hXanchored`
  (the `a₀·η₁^{τ₁}` terms cancel);
* `extension_mem_ZIrr` — `Ximg χ₂ ∈ ℤ[Irr G]` (`hXzirr`).

`hXanchored`/`hXinner`/`hXzirr` are the `(6.8.2.3)` per-column outputs (to be discharged from
`columnDecompositionTau` + the `(6.8.2.2)` aggregate `Y`-pinning); none requires `Ximg χ₂ = cTE(μ_j)`. -/
noncomputable def certainTypeSet_isCoherent_via_anchoredImages
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {k : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hk : k ≠ 1)
    {η₁ : ClassFunction ↥L ℂ} {a₀ : ℕ}
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ)
    (hXanchored : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ,
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k →
      hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁)
        = Ximg χ₂ - a₀ • cY.extension η₁)
    (hXinner : ∀ χ₂ χ₂' : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ,
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k →
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂' ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k →
      ClassFunction.inner (Ximg χ₂) (Ximg χ₂')
        = ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
            (OddOrder.Peterfalvi.S06.columnSum h46 χ₂'))
    (hXzirr : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, Ximg χ₂ ∈ ZIrr G) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S06.certainTypeSet h46 k)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) where
  nonzero := OddOrder.Peterfalvi.S06.certainType_nonzero h46 hk
  extension := xChiExtension h46 Ximg
  extension_inner_eq := by
    intro φ ψ hφ hψ
    rw [OddOrder.Peterfalvi.S07.zSpan] at hφ hψ
    induction hφ, hψ using Submodule.span_induction₂ with
    | mem_mem u v hu hv =>
        obtain ⟨χ₂, hne₂, hdeg₂, rfl⟩ := hu
        obtain ⟨χ₂', hne₂', hdeg₂', rfl⟩ := hv
        rw [xChiExtension_columnSum, xChiExtension_columnSum]
        exact hXinner χ₂ χ₂' ⟨χ₂, hne₂, hdeg₂, rfl⟩ ⟨χ₂', hne₂', hdeg₂', rfl⟩
    | zero_left v _ => rw [map_zero, ClassFunction.inner_zero_left, ClassFunction.inner_zero_left]
    | zero_right u _ => rw [map_zero, ClassFunction.inner_zero_right, ClassFunction.inner_zero_right]
    | add_left u₁ u₂ v _ _ _ ih₁ ih₂ =>
        rw [map_add, ClassFunction.inner_add_left, ClassFunction.inner_add_left, ih₁, ih₂]
    | add_right u v₁ v₂ _ _ _ ih₁ ih₂ =>
        rw [map_add, ClassFunction.inner_add_right, ClassFunction.inner_add_right, ih₁, ih₂]
    | smul_left r u v _ _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ r (xChiExtension h46 Ximg u),
          ← Int.cast_smul_eq_zsmul ℂ r u,
          ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, ih]
    | smul_right r u v _ _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ r (xChiExtension h46 Ximg v),
          ← Int.cast_smul_eq_zsmul ℂ r v,
          OddOrder.RepresentationTheory.inner_smul_right,
          OddOrder.RepresentationTheory.inner_smul_right, ih]
  extends_on_supported := by
    intro φ hφ
    refine OddOrder.Peterfalvi.S07.IntegralCharacterMap.eq_on_zSpan_of_eq_on ?_
      (OddOrder.Peterfalvi.S06.mem_span_columnDiff_of_mem_zSupportedSpan h46 k hφ)
    rintro _ ⟨f, ⟨χ₂, hχ₂, hdeg, rfl⟩, rfl⟩
    have e1 := hXanchored χ₂ (OddOrder.Peterfalvi.S06.columnSum_mem_certainTypeSet h46 hχ₂ hdeg)
    have e2 := hXanchored k (OddOrder.Peterfalvi.S06.columnSum_mem_certainTypeSet h46 hk rfl)
    have hrhs : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - OddOrder.Peterfalvi.S06.columnSum h46 k) = Ximg χ₂ - Ximg k := by
      have hsplit : OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - OddOrder.Peterfalvi.S06.columnSum h46 k
          = (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁)
            - (OddOrder.Peterfalvi.S06.columnSum h46 k - a₀ • η₁) := by abel
      rw [hsplit, map_sub, e1, e2]; abel
    rw [hrhs, map_sub, xChiExtension_columnSum, xChiExtension_columnSum]
  extension_mem_ZIrr := by
    intro φ hφ
    rw [OddOrder.Peterfalvi.S07.zSpan] at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨χ₂, -, -, rfl⟩ := hx
        rw [xChiExtension_columnSum]; exact hXzirr χ₂
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul a x _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ a ih

/-- **Grid glue map for an arbitrary `X`-target map** `νX`.  The general form of
`exists_glue_nu_columnSum_Yset` (`S08_CaseBXunionY`): from the orthonormal grid family `{μ_{ij}}`
and the orthonormal `Y`-family, glue *any* two `IntegralCharacterMap`s `νX` (on the columns) and
`coherentYset.extension` (on `Y`) into a single map `ν` that agrees with `νX` on every column sum
`μ_j = columnSum χ₂` (by linearity, since `ν = νX` on each grid member `μ_{ij}`) and with
`coherentYset.extension` on `Y`.

`exists_integralCharacterMap_glue_of_orthonormal` requires only the *sources* (`grid`, `Y`) to be
orthonormal; the target maps are arbitrary.  Instantiated with `νX = xChiExtension h46 Ximg` this
produces the textbook glue (`ν(μ_j) = Ximg χ₂`), avoiding the cTE-image entirely. -/
theorem exists_glue_nu_columnSum_Yset_via_map
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (νX : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G) :
    ∃ ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G,
      (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ,
        ν (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) = νX (OddOrder.Peterfalvi.S06.columnSum h46 χ₂))
      ∧ (∀ y ∈ hyp.Yset, ν y = cY.extension y) := by
  classical
  haveI : Finite ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :=
    SibleyDadeHypothesis.finite_linearCharacters_of_finite
  have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  set grid : Set (ClassFunction ↥L ℂ) :=
    Set.range (fun p : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) × Fin (Nat.card h46.W1) =>
      ((h46.columnFamily p.1).mu p.2 : ClassFunction ↥L ℂ)) with hgrid
  have hXfin : grid.Finite := Set.finite_range _
  have hXorth : ∀ x ∈ grid, ∀ x' ∈ grid,
      ClassFunction.inner x x' = if x = x' then (1 : ℂ) else 0 := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact hinner _ _ ((h46.columnFamily p.1).mu p.2).property
      ((h46.columnFamily q.1).mu q.2).property
  have hYorth : ∀ y ∈ hyp.Yset, ∀ y' ∈ hyp.Yset,
      ClassFunction.inner y y' = if y = y' then (1 : ℂ) else 0 :=
    fun y hy y' hy' => hinner _ _ (hyp.isIrreducibleCharacter_of_mem_Yset hy)
      (hyp.isIrreducibleCharacter_of_mem_Yset hy')
  have hXY : ∀ x ∈ grid, ∀ y ∈ hyp.Yset, ClassFunction.inner x y = 0 := by
    rintro _ ⟨p, rfl⟩ y hy
    exact inner_columnFamily_mu_Yset_eq_zero hyp h46 hW1 hy p.1 p.2
  obtain ⟨ν, hνgrid, hνY⟩ :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthonormal
    hXfin hyp.Yset_finite hXorth hYorth hXY νX cY.extension
  refine ⟨ν, fun χ₂ => ?_, hνY⟩
  rw [OddOrder.Peterfalvi.S06.columnSum_def]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun i _ => hνgrid _ ⟨(χ₂, i), rfl⟩

/-- **(6.8.2) case-(B) `certainTypeSet ⊔ Y` base union — T=0-free, textbook route.**  The
`X_χ`-coherence replacement for `coherentCertainTypeSet_union_Yset`: glues the textbook column
coherence `certainTypeSet_isCoherent_via_anchoredImages` (extension `= Ximg`, the `(6.8.2.3)`
projection images) with `Y` through the §7 diagonal-aware engine.

The cross-diagonal agreement `hDτ` (`ν(μ_{k0} − a₀·η₁) = τ(μ_{k0} − a₀·η₁)`) is now **immediate**
from `hXanchored` (the `(6.8.2.3)` anchored image `τ(μ_{k0} − a₀·η₁) = Ximg k0 − a₀·η₁^{τ₁}`): since
`ν(μ_{k0}) = Ximg k0` (not `cTE(μ_{k0})`), the diagonal holds **by construction**, with **no `T = 0`
identity** `Ximg = cTE` required.  This is the precise sense in which the textbook route dissolves
the `hanchored` over-constraint.

`hXmixed` is the `(6.8.2.3)` seam orthogonality `X_χ ⊥ Y^{τ₁}` (`⟨Ximg χ₂, η^{τ₁}⟩ = 0`), another
genuine `(6.8.2.3)` output.  All four `X_χ`-hypotheses are to be discharged from `columnDecompositionTau`
+ the `(6.8.2.2)` aggregate `Y`-pinning. -/
noncomputable def coherentCertainTypeSet_union_Yset_via_anchoredImages
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    (hHK : h46.K = H) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {k : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hk : k ≠ 1)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {k0 : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ}
    (hk0mem : OddOrder.Peterfalvi.S06.columnSum h46 k0
      ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k)
    {a₀ : ℕ}
    (ha₀ : (OddOrder.Peterfalvi.S06.columnSum h46 k0 : ClassFunction ↥L ℂ) 1 = (a₀ : ℂ) * η₁ 1)
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ)
    (hXanchored : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ,
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k →
      hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁)
        = Ximg χ₂ - a₀ • cY.extension η₁)
    (hXinner : ∀ χ₂ χ₂' : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ,
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k →
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂' ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k →
      ClassFunction.inner (Ximg χ₂) (Ximg χ₂')
        = ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
            (OddOrder.Peterfalvi.S06.columnSum h46 χ₂'))
    (hXzirr : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, Ximg χ₂ ∈ ZIrr G)
    (hXmixed : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (Ximg χ₂) (cY.extension y) = 0) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S06.certainTypeSet h46 k ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  -- the textbook column coherence `cX` (extension `= Ximg`, T=0-free).
  set cX := certainTypeSet_isCoherent_via_anchoredImages hyp h46 cY hk Ximg hXanchored hXinner hXzirr
    with hcX
  -- the glue map `ν` agreeing with `xChiExtension` (`= cX.extension`) on columns and `cY` on `Y`.
  have hspec := (exists_glue_nu_columnSum_Yset_via_map hyp h46 hW1 cY (xChiExtension h46 Ximg)).choose_spec
  set ν := (exists_glue_nu_columnSum_Yset_via_map hyp h46 hW1 cY (xChiExtension h46 Ximg)).choose
    with hνdef
  have hνcol : ∀ χ₂, ν (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) = Ximg χ₂ := by
    intro χ₂; rw [hspec.1 χ₂, xChiExtension_columnSum]
  have hνY := hspec.2
  -- `hagreeX`: on the columns, `ν = cX.extension` (both are `xChiExtension`, hence `= Ximg`).
  have hagreeX : ∀ x ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k, ν x = cX.extension x := by
    rintro x ⟨χ₂, -, -, rfl⟩
    rw [hνcol χ₂]
    change Ximg χ₂ = xChiExtension h46 Ximg (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
    rw [xChiExtension_columnSum]
  -- `hsrc_ortho`: column ⊥ `Y` at the source level.
  have hpair : ∀ χ ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k, ∀ η ∈ hyp.Yset,
      ClassFunction.inner χ η = 0 := by
    rintro χ ⟨χ₂, -, -, rfl⟩ η hη
    exact inner_columnSum_Yset_eq_zero hyp h46 hW1 hη χ₂
  -- `hmixed`: `⟨ν x, ν y⟩ = ⟨x, y⟩` (both vanish — `Ximg ⊥ Y^{τ₁}` and column ⊥ `Y`).
  have hmixed : ∀ x ∈ OddOrder.Peterfalvi.S06.certainTypeSet h46 k, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y := by
    rintro x ⟨χ₂, -, -, rfl⟩ y hy
    rw [hνcol χ₂, hνY y hy, hXmixed χ₂ y hy, inner_columnSum_Yset_eq_zero hyp h46 hW1 hy χ₂]
  -- `hDτ`: the cross-diagonal agreement — **immediate from `hXanchored`, no `T = 0`**.
  have hDτ : ∀ d ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 k0 - a₀ • η₁} :
        Set (ClassFunction ↥L ℂ)), ν d = hyp.tau d := by
    intro d hd
    rw [Set.mem_singleton_iff] at hd
    subst hd
    rw [hXanchored k0 hk0mem, map_sub, map_nsmul, hνcol k0, hνY η₁ hη₁]
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    cX cY ν hagreeX hνY
    (inner_eq_zero_of_mem_span_of_pairwise_orthogonal hpair) hmixed
    {OddOrder.Peterfalvi.S06.columnSum h46 k0 - a₀ • η₁} hDτ
    (hgen_withDiagonal_certainTypeSet hyp h46 hHK hk0mem hη₁ ha₀)

end OddOrder.Peterfalvi.S08
