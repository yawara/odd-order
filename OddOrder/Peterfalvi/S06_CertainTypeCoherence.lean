/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S06_CertainTypeConjugation
import OddOrder.Peterfalvi.S07_Coherence

/-!
# Peterfalvi (4.9)(b): coherence of the certain-type characters

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000),
§4, p. 24, Theorem (4.9).

Theorem (4.9) packages the certain-type Dade data into a **coherent isometry**.  Fix a column
`k` (`0 < k < w₂`) and let `𝒯 = {μ_j | 0 < j < w₂, μ_j(1) = μ_k(1)}` be the set of certain-type
column characters of `L` with the same degree as `μ_k`.  Part (b) asserts that the `ℤ`-linear map
`Z[𝒯] → Z[Irr G]` sending `μ_j ↦ δ_k ∑_{0≤i<w₁} ω_{ij}^σ` is an isometry agreeing with the Dade
map `τ` on `Z[𝒯, A]`.  In the language of `S07.IsCoherent`, this is exactly a coherent extension
of `τ` on the certain-type set, the input the §8 case-B coherence capstone consumes.

This file builds the **global extension map** underlying (4.9)(b):

* `columnSum h χ₂` — the certain-type column character `μ_j = ∑_{0≤i<w₁} μ_{ij}` (Peterfalvi
  (4.5.a)).
* `certainTypeExtension h` — the global `ℤ`-linear `ν : CF(L) → CF(G)` defined on the basis
  `Irr(L)` by sending each certain-type irreducible `μ_{ij}` to `δ_j ω_{ij}^σ` (and every other
  irreducible to `0`).  Built via `Module.Basis.constr` on `irreducibleCharacterBasis`, restricted
  to `ℤ`-scalars.  Well-definedness of the per-element rule rests on `columnFamily_mu_injective`
  (the global certain-type family `(χ₂, i) ↦ μ_{ij}` is injective).
* `certainTypeExtension_mu` / `certainTypeExtension_columnSum` — the defining values
  `ν(μ_{ij}) = δ_j ω_{ij}^σ` and `ν(μ_j) = δ_j ∑_i ω_{ij}^σ`.

The five `IsCoherent` fields (nonzero / isometry / `τ`-agreement / `ZIrr`-codomain) are proved in
later sections from this map together with `certainType_omega_sum_isometry` (4.9)(b)-isometry,
`certainType_diff_dade_sum_eq` (4.8 summed identity), and `certainType_columnSum_conj_ne`
((4.9)(a) nonvanishing).

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md`.
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype ↥L]
variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-! ### The certain-type column character `μ_j` and the extension map `ν` -/

/-- **The certain-type column character** `μ_j = ∑_{0≤i<w₁} μ_{ij}` (Peterfalvi (4.5.a)).  This is
the character `μ_j` appearing in Theorem (4.9); `certainType_columnSum_conj` identifies its complex
conjugate as the column `μ_{j'}`, and `columnFamily_mu_sum_inner` gives its Gram matrix
`⟨μ_j, μ_k⟩ = w₁·δ_{jk}`. -/
noncomputable def columnSum (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) : ClassFunction ↥L ℂ :=
  ∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)

theorem columnSum_def (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    columnSum h χ₂ = ∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) :=
  rfl

open scoped Classical in
/-- **The per-basis rule of the coherent extension.**  On the irreducible `ω`, return the signed
`σ`-image `δ_j ω_{ij}^σ` if `ω = μ_{ij}` is a certain-type character, and `0` otherwise.  The
choice of witness `(χ₂, i)` is irrelevant by `columnFamily_mu_injective`. -/
noncomputable def certainTypeExtensionFun (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)] :
    IrreducibleCharacter ↥L → ClassFunction G ℂ :=
  fun ω =>
    if hex : ∃ p : ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) × Fin (Nat.card h.W1),
        (h.columnFamily p.1).mu p.2 = ω then
      (h.columnFamily hex.choose.1).sign • certainTypeOmegaSigma h hex.choose.1 hex.choose.2
    else 0

/-- **The coherent extension `ν` of Peterfalvi (4.9)(b).**  The global `ℤ`-linear map
`CF(L) → CF(G)` sending each certain-type irreducible `μ_{ij}` to `δ_j ω_{ij}^σ` (every other
irreducible to `0`), built on the basis `Irr(L)` (`irreducibleCharacterBasis`) and restricted to
`ℤ`-scalars to land in `S07.IntegralCharacterMap`. -/
noncomputable def certainTypeExtension (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)] :
    S07.IntegralCharacterMap ↥L G :=
  ((S05.irreducibleCharacterBasis (G := ↥L)).constr ℂ (certainTypeExtensionFun h)).restrictScalars ℤ

/-- **Defining value of `ν` on a certain-type irreducible**: `ν(μ_{ij}) = δ_j ω_{ij}^σ`.  The basis
rule `certainTypeExtensionFun` selects the unique witness `(χ₂, i)` by
`columnFamily_mu_injective`. -/
theorem certainTypeExtension_mu (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    certainTypeExtension h ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
      = (h.columnFamily χ₂).sign • certainTypeOmegaSigma h χ₂ i := by
  classical
  rw [certainTypeExtension, LinearMap.restrictScalars_apply]
  conv_lhs => rw [← S05.irreducibleCharacterBasis_apply (G := ↥L) ((h.columnFamily χ₂).mu i)]
  rw [(S05.irreducibleCharacterBasis (G := ↥L)).constr_basis ℂ _ ((h.columnFamily χ₂).mu i),
    certainTypeExtensionFun]
  have hex : ∃ p : ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) × Fin (Nat.card h.W1),
      (h.columnFamily p.1).mu p.2 = (h.columnFamily χ₂).mu i := ⟨(χ₂, i), rfl⟩
  rw [dif_pos hex]
  have hchoose : hex.choose = (χ₂, i) := h.columnFamily_mu_injective hex.choose_spec
  rw [hchoose]

/-- **Defining value of `ν` on the column sum**: `ν(μ_j) = δ_j ∑_{0≤i<w₁} ω_{ij}^σ`. -/
theorem certainTypeExtension_columnSum (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    certainTypeExtension h (columnSum h χ₂)
      = (h.columnFamily χ₂).sign • ∑ i, certainTypeOmegaSigma h χ₂ i := by
  rw [columnSum_def, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => certainTypeExtension_mu h χ₂ i

/-! ### The certain-type set `𝒯` and the `ZIrr`-codomain field -/

/-- **The certain-type set** `𝒯 = {μ_j | 0 < j < w₂, μ_j(1) = μ_k(1)}` of Peterfalvi (4.9): the
column characters `μ_j` from nontrivial `W₂`-columns (`χ₂ ≠ 1`) whose degree matches the fixed
reference column `k`. -/
noncomputable def certainTypeSet (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (k : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) : Set (ClassFunction ↥L ℂ) :=
  {f | ∃ χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
    (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily k).mu i : ClassFunction ↥L ℂ) 1) ∧ f = columnSum h χ₂}

/-- A column character `μ_j` with `χ₂ ≠ 1` and `μ_j(1) = μ_k(1)` lies in `𝒯`.  The degree condition
is the column-sum degree equality `∑_i μ_{ij}(1) = ∑_i μ_{ik}(1)` (`= μ_j(1) = μ_k(1)`). -/
theorem columnSum_mem_certainTypeSet (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {k χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily k).mu i : ClassFunction ↥L ℂ) 1)) :
    columnSum h χ₂ ∈ certainTypeSet h k :=
  ⟨χ₂, hχ₂, hdeg, rfl⟩

/-- **The `σ`-image `ω_{ij}^σ` is a virtual character.**  `ω_{ij}^σ = σ_G(ω(P_{ij}))` and `σ_G` maps
`ZIrr(W) → ZIrr(G)` (`sigma_mem_ZIrr`); the source `ω(P_{ij})` is irreducible. -/
theorem certainTypeOmegaSigma_mem_ZIrr (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    certainTypeOmegaSigma h χ₂ i ∈ ZIrr G := by
  rw [certainTypeOmegaSigma]
  exact (ticVdiff h).sigma_mem_ZIrr rfl (ticVdiffFullDadeApplication h)
    ((ticVdiff h).omega (omegaProdCharTic h χ₂ i)).mem_ZIrr

/-- `ν(μ_j) ∈ ZIrr G`: the column-sum image `δ_j ∑_i ω_{ij}^σ` is a `ℤ`-combination of the virtual
characters `ω_{ij}^σ`. -/
theorem certainTypeExtension_columnSum_mem_ZIrr (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    certainTypeExtension h (columnSum h χ₂) ∈ ZIrr G := by
  rw [certainTypeExtension_columnSum]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun i _ => certainTypeOmegaSigma_mem_ZIrr h χ₂ i)

/-- **Peterfalvi (4.9)(b), `ZIrr`-codomain (`IsCoherent.extension_mem_ZIrr`)**: `ν` carries the
coherent lattice `Z[𝒯]` into `Z[Irr G]`.  By `span_induction`: generators `μ_j ∈ 𝒯` map into `ZIrr`
(`certainTypeExtension_columnSum_mem_ZIrr`); `ZIrr` is closed under `0`, `+`, `ℤ•`. -/
theorem certainTypeExtension_mem_ZIrr (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (k : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ S07.zSpan (certainTypeSet h k)) :
    certainTypeExtension h φ ∈ ZIrr G := by
  rw [S07.zSpan] at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨χ₂, _, _, rfl⟩ := hx
      exact certainTypeExtension_columnSum_mem_ZIrr h χ₂
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ a ih

/-! ### The isometry field -/

/-- **Generator-level isometry**: `⟨ν(μ_j), ν(μ_l)⟩ = ⟨μ_j, μ_l⟩`.  Pulling out the signs gives
`δ_j δ_l ⟨∑ω_{ij}^σ, ∑ω_{il}^σ⟩ = δ_j δ_l ⟨μ_j, μ_l⟩` (`certainType_omega_sum_isometry`).  When
`χ₂ = χ₂'` the two signs coincide and `δ_j² = 1`; when `χ₂ ≠ χ₂'` the Gram entry
`⟨μ_j, μ_l⟩ = 0` (`columnFamily_mu_sum_inner`) absorbs the signs.  No degree hypothesis is needed. -/
theorem certainTypeExtension_columnSum_inner (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ClassFunction.inner (certainTypeExtension h (columnSum h χ₂))
        (certainTypeExtension h (columnSum h χ₂'))
      = ClassFunction.inner (columnSum h χ₂) (columnSum h χ₂') := by
  rw [certainTypeExtension_columnSum, certainTypeExtension_columnSum,
    ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂).sign (∑ i, certainTypeOmegaSigma h χ₂ i),
    ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂').sign (∑ i, certainTypeOmegaSigma h χ₂' i),
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, star_intCast,
    certainType_omega_sum_isometry, columnSum_def, columnSum_def, columnFamily_mu_sum_inner]
  by_cases hχ : χ₂ = χ₂'
  · subst hχ
    rw [if_pos rfl]
    rcases (h.columnFamily χ₂).sign_eq with hs | hs <;> rw [hs] <;> push_cast <;> ring
  · rw [if_neg hχ, mul_zero, mul_zero]

/-- **Peterfalvi (4.9)(b), isometry (`IsCoherent.extension_inner_eq`)**: `ν` preserves the inner
product on `Z[𝒯]`.  By `span_induction₂` over both arguments: generators `μ_j, μ_l ∈ 𝒯` are handled
by `certainTypeExtension_columnSum_inner`; the additive/`ℤ•` cases use bilinearity of `⟨·,·⟩` and
`ℤ`-linearity of `ν`. -/
theorem certainTypeExtension_inner_eq (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (k : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    {φ ψ : ClassFunction ↥L ℂ} (hφ : φ ∈ S07.zSpan (certainTypeSet h k))
    (hψ : ψ ∈ S07.zSpan (certainTypeSet h k)) :
    ClassFunction.inner (certainTypeExtension h φ) (certainTypeExtension h ψ)
      = ClassFunction.inner φ ψ := by
  rw [S07.zSpan] at hφ hψ
  induction hφ, hψ using Submodule.span_induction₂ with
  | mem_mem u v hu hv =>
      obtain ⟨χ₂, _, _, rfl⟩ := hu
      obtain ⟨χ₂', _, _, rfl⟩ := hv
      exact certainTypeExtension_columnSum_inner h χ₂ χ₂'
  | zero_left v hv => rw [map_zero, ClassFunction.inner_zero_left, ClassFunction.inner_zero_left]
  | zero_right u hu => rw [map_zero, ClassFunction.inner_zero_right, ClassFunction.inner_zero_right]
  | add_left u₁ u₂ v hu₁ hu₂ hv ih₁ ih₂ =>
      rw [map_add, ClassFunction.inner_add_left, ClassFunction.inner_add_left, ih₁, ih₂]
  | add_right u v₁ v₂ hu hv₁ hv₂ ih₁ ih₂ =>
      rw [map_add, ClassFunction.inner_add_right, ClassFunction.inner_add_right, ih₁, ih₂]
  | smul_left r u v hu hv ih =>
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ r (certainTypeExtension h u),
        ← Int.cast_smul_eq_zsmul ℂ r u,
        ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, ih]
  | smul_right r u v hu hv ih =>
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ r (certainTypeExtension h v),
        ← Int.cast_smul_eq_zsmul ℂ r v,
        OddOrder.RepresentationTheory.inner_smul_right,
        OddOrder.RepresentationTheory.inner_smul_right, ih]

/-! ### Support of the certain-type column characters (Peterfalvi (4.7)) -/

/-- **`μ_j` vanishes off `A ∪ {1}`** (Peterfalvi (4.7)).  `μ_j = Ind_K^L χ_j` (`(4.5.a)`
`induce_restrict_certainType_eq`, `chiRestrict = Res_K μ_{0j}`); the induced character vanishes
outside `A ∪ {1}` for a nontrivial column `χ₂ ≠ 1`
(`induce_chiRestrict_apply_eq_zero_of_not_mem_union`). -/
theorem columnSum_apply_eq_zero_of_not_mem (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    {z : ↥L} (hz : (L.subtype z) ∉ A ∪ ({1} : Set G)) :
    (columnSum h χ₂ : ClassFunction ↥L ℂ) z = 0 := by
  have hbridge : columnSum h χ₂
      = ClassFunction.induce h.K (h.chiRestrict χ₂ : ClassFunction ↥h.K ℂ) := by
    rw [columnSum_def, ← h.induce_restrict_certainType_eq χ₂, h.coe_chiRestrict χ₂]
  rw [hbridge]
  exact induce_chiRestrict_apply_eq_zero_of_not_mem_union h hχ₂ hz

/-- **`Supp μ_j ⊆ supportInSubgroup A L ∪ {1}`** (Peterfalvi (4.7), set form).  The support of the
certain-type column character sits inside the certain subgroup `A` together with the identity. -/
theorem columnSum_support_subset (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    (columnSum h χ₂).support ⊆ S04.supportInSubgroup A L ∪ {1} := by
  intro z hz
  rw [ClassFunction.mem_support] at hz
  by_contra hzn
  refine hz (columnSum_apply_eq_zero_of_not_mem h hχ₂ ?_)
  rw [Set.mem_union] at hzn
  push_neg at hzn
  obtain ⟨hzA, hz1⟩ := hzn
  rintro (hA | h1)
  · exact hzA (by rwa [S04.mem_supportInSubgroup])
  · exact hz1 (Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp h1)))

/-- Evaluation of the column sum at `1`: `μ_j(1) = ∑_i μ_{ij}(1)` (the column degree). -/
theorem columnSum_apply_one (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    (columnSum h χ₂ : ClassFunction ↥L ℂ) 1
      = ∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1 := by
  rw [columnSum_def]
  exact map_sum (AddMonoidHom.mk' (fun φ : ClassFunction ↥L ℂ => φ (1 : ↥L)) (fun _ _ => rfl))
    (fun i => ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)) Finset.univ

/-- **Column sign equality from equal degree** (Peterfalvi (4.8) step (1), column form).  If two
certain-type columns have the same degree `∑_i μ_{ij}(1) = ∑_i μ_{ik}(1)`, their signs coincide
(reduce to the per-row `(4.8)` sign equality at any row via the degree bridge). -/
theorem certainType_columnSign_eq (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ}
    (hdeg : (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)) :
    (h.columnFamily χ₂).sign = (h.columnFamily χ₂').sign :=
  certainType_sign_eq_of_degree_eq h χ₂ χ₂' 0
    (forall_columnFamily_mu_apply_one_eq_of_sum_eq h χ₂ χ₂' hdeg 0)

/-- **`Supp(μ_j − μ_k) ⊆ supportInSubgroup A L`** for same-degree certain-type columns.  Both
`μ_j, μ_k` vanish off `A ∪ {1}` ((4.7) `columnSum_support_subset`); the difference additionally
vanishes at `1` (equal degree), so its support sits inside the certain subgroup `A`. -/
theorem columnDiff_support_subset (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (hdeg : (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)) :
    (columnSum h χ₂ - columnSum h χ₂').support ⊆ S04.supportInSubgroup A L := by
  intro z hz
  rw [ClassFunction.mem_support, ClassFunction.sub_apply] at hz
  by_contra hzA
  rw [S04.mem_supportInSubgroup] at hzA
  by_cases hz1 : z = 1
  · subst hz1
    exact hz (by rw [columnSum_apply_one, columnSum_apply_one, hdeg, sub_self])
  · have hnm : L.subtype z ∉ A ∪ ({1} : Set G) := by
      rintro (hA | h1)
      · exact hzA hA
      · exact hz1 (Subtype.ext (Set.mem_singleton_iff.mp h1))
    rw [columnSum_apply_eq_zero_of_not_mem h hχ₂ hnm,
      columnSum_apply_eq_zero_of_not_mem h hχ₂' hnm, sub_zero] at hz
    exact hz rfl

/-! ### The `τ`-agreement field -/

/-- **Generator-level `τ`-agreement** (Peterfalvi (4.8)/(4.9)): on a certain-type difference
`μ_j − μ_k` (same degree), the coherent extension `ν` agrees with the Dade map
`τ = dadeIntegralCharacterMap`.  Both sides equal `δ_j ∑_i (ω_{ij}^σ − ω_{ik}^σ)`:

* RHS: `μ_j − μ_k` is supported on `A ⊆ A₀` (`columnDiff_support_subset`), so
  `τ(μ_j − μ_k) = h.dade0.dadeMap ⟨·⟩` (`dadeIntegralCharacterMap_apply_of_support`)
  `= h.tau.toDadeMap ⟨·⟩` (`IsDadeMap.unique`) `= δ_j ∑(ω^σ − ω^σ)`
  (`certainType_diff_dade_sum_eq`, after identifying `⟨μ_j − μ_k, _⟩ = ∑ certainTypeDiffSupported`);
* LHS: `ν(μ_j − μ_k) = δ_j ∑ω_{ij}^σ − δ_k ∑ω_{ik}^σ`, and `δ_j = δ_k` (`certainType_columnSign_eq`). -/
theorem certainTypeExtension_columnDiff_eq_dade (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (hdeg : (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)) :
    certainTypeExtension h (columnSum h χ₂ - columnSum h χ₂')
      = S07.dadeIntegralCharacterMap h.dade0 h.tau (columnSum h χ₂ - columnSum h χ₂') := by
  by_cases hχeq : χ₂ = χ₂'
  · subst hχeq; rw [sub_self, map_zero, map_zero]
  -- both sides equal `δ_j • ∑_i (ω_{ij}^σ − ω_{ik}^σ)`
  have hdi := forall_columnFamily_mu_apply_one_eq_of_sum_eq h χ₂ χ₂' hdeg
  have hsupp : (columnSum h χ₂ - columnSum h χ₂').support ⊆
      S04.supportInSubgroup
        (A ∪ {g : G | ∃ l : G, l ∈ L ∧ ∃ v ∈ h.tic.V, g = l * v * l⁻¹}) L :=
    (columnDiff_support_subset h hχ₂ hχ₂' hdeg).trans
      (S04.supportInSubgroup_mono Set.subset_union_left)
  have hval : ((∑ i, certainTypeDiffSupported h hχ₂ hχ₂' i (hdi i) :
        OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
          (A ∪ {g : G | ∃ l : G, l ∈ L ∧ ∃ v ∈ h.tic.V, g = l * v * l⁻¹}) L) :
        ClassFunction ↥L ℂ)
      = columnSum h χ₂ - columnSum h χ₂' := by
    rw [AddSubmonoidClass.coe_finset_sum, columnSum_def, columnSum_def, ← Finset.sum_sub_distrib]
    rfl
  have hLHS : certainTypeExtension h (columnSum h χ₂ - columnSum h χ₂')
      = (h.columnFamily χ₂).sign •
          ∑ i, (certainTypeOmegaSigma h χ₂ i - certainTypeOmegaSigma h χ₂' i) := by
    rw [map_sub, certainTypeExtension_columnSum, certainTypeExtension_columnSum,
      ← certainType_columnSign_eq h hdeg, ← smul_sub, ← Finset.sum_sub_distrib]
  rw [hLHS,
    S07.dadeIntegralCharacterMap_apply_of_support h.dade0 h.tau hsupp,
    S04.IsDadeMap.unique (k := ℂ) h.dade0.isDadeMap_dadeMap h.tau.toDadeIsometryData.isDadeMap,
    ← certainType_diff_dade_sum_eq h hχeq hχ₂ hχ₂' hdi]
  congr 1
  exact Subtype.ext hval

/-- **`Z[𝒯, A]` is generated by the differences `μ_j − μ_k`** (Peterfalvi (4.9)(b) proof).  Every
`A`-supported element of `Z[𝒯]` is a `ℤ`-combination of `{μ_j − μ_k | μ_j ∈ 𝒯}`.  Decompose
`Z[𝒯] ≤ D ⊔ ℤ·μ_k` (each `μ_j = (μ_j − μ_k) + μ_k`); the difference lattice `D` vanishes at `1`
(every `μ_j ∈ 𝒯` has degree `μ_j(1) = μ_k(1)`), so for an `A`-supported `φ = δ + n·μ_k` (with
`δ ∈ D`) the degree `φ(1) = n·μ_k(1)` is `0` (as `1 ∉ A`), forcing `n = 0` (`μ_k(1) ≠ 0`). -/
theorem mem_span_columnDiff_of_mem_zSupportedSpan (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (k : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ S07.zSupportedSpan (certainTypeSet h k) (S04.supportInSubgroup A L)) :
    φ ∈ Submodule.span ℤ ((fun f => f - columnSum h k) '' (certainTypeSet h k)) := by
  classical
  obtain ⟨hφspan, hφsupp⟩ := hφ
  set D := Submodule.span ℤ ((fun f => f - columnSum h k) '' (certainTypeSet h k)) with hD
  set ev1 : ClassFunction ↥L ℂ →+ ℂ :=
    AddMonoidHom.mk' (fun ψ => ψ (1 : ↥L)) (fun _ _ => rfl) with hev1
  have mem_apply_one : ∀ f ∈ certainTypeSet h k, ev1 f = ev1 (columnSum h k) := by
    rintro f ⟨χ₂, _, hdeg, rfl⟩
    show (columnSum h χ₂ : ClassFunction ↥L ℂ) 1 = (columnSum h k : ClassFunction ↥L ℂ) 1
    rw [columnSum_apply_one, columnSum_apply_one]; exact hdeg
  -- the common degree `μ_k(1) ≠ 0`
  have d_ne : ev1 (columnSum h k) ≠ 0 := by
    show (columnSum h k : ClassFunction ↥L ℂ) 1 ≠ 0
    rw [columnSum_apply_one]
    obtain ⟨d₀, hd₀pos, hd₀⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily k).mu 0)
    have hsum : ∑ i, ((h.columnFamily k).mu i : ClassFunction ↥L ℂ) 1
        = (Nat.card h.W1 : ℂ) * (d₀ : ℂ) := by
      rw [Finset.sum_congr rfl (fun i _ => columnFamily_mu_apply_one_eq h k i), hd₀,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum]
    exact mul_ne_zero (by exact_mod_cast NeZero.ne (Nat.card h.W1))
      (by exact_mod_cast hd₀pos.ne')
  -- the difference lattice `D` vanishes at `1`
  have hD_vanish : ∀ δ ∈ D, ev1 δ = 0 := by
    intro δ hδ
    induction hδ using Submodule.span_induction with
    | mem x hx => obtain ⟨f, hf, rfl⟩ := hx; rw [map_sub, mem_apply_one f hf, sub_self]
    | zero => exact map_zero ev1
    | add x y _ _ ihx ihy => rw [map_add, ihx, ihy, add_zero]
    | smul a x _ ih => rw [map_zsmul, ih, smul_zero]
  -- `Z[𝒯] ≤ D ⊔ ℤ·μ_k`
  have hspan_le : Submodule.span ℤ (certainTypeSet h k)
      ≤ D ⊔ Submodule.span ℤ {columnSum h k} := by
    rw [Submodule.span_le]
    intro f hf
    rw [show f = (f - columnSum h k) + columnSum h k from (sub_add_cancel f _).symm]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.subset_span ⟨f, hf, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span rfl))
  -- decompose `φ = y + n·μ_k`
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hspan_le hφspan)
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hz
  -- `φ(1) = 0` (supported off `1`)
  have hφ1 : ev1 φ = 0 := by
    show φ (1 : ↥L) = 0
    by_contra hne
    have h1mem : (1 : ↥L) ∈ S04.supportInSubgroup A L :=
      hφsupp (ClassFunction.mem_support.mpr hne)
    rw [S04.mem_supportInSubgroup] at h1mem
    exact h.dade0.ne_one (Set.subset_union_left h1mem) (by simp)
  -- `0 = ev1 φ = n • ev1 μ_k`, force `n = 0`
  rw [← hyz, map_add, hD_vanish y hy, zero_add, map_zsmul] at hφ1
  have hn : n = 0 := by
    rcases smul_eq_zero.mp hφ1 with hn | hd
    · exact hn
    · exact absurd hd d_ne
  rw [← hyz, hn, zero_smul, add_zero]
  exact hy

/-- **Peterfalvi (4.9)(b), `τ`-agreement (`IsCoherent.extends_on_supported`)**: on the supported
lattice `Z[𝒯, A]`, the coherent extension `ν` coincides with the Dade map `τ`.  Reduce to the
generating differences `μ_j − μ_k` (`mem_span_columnDiff_of_mem_zSupportedSpan`), where `ν = τ`
(`certainTypeExtension_columnDiff_eq_dade`), and extend over the `ℤ`-span (`eq_on_zSpan_of_eq_on`). -/
theorem certainTypeExtension_eq_dade_of_mem_zSupportedSpan (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {k : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hk : k ≠ 1)
    {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ S07.zSupportedSpan (certainTypeSet h k) (S04.supportInSubgroup A L)) :
    certainTypeExtension h φ = S07.dadeIntegralCharacterMap h.dade0 h.tau φ := by
  refine S07.IntegralCharacterMap.eq_on_zSpan_of_eq_on ?_
    (mem_span_columnDiff_of_mem_zSupportedSpan h k hφ)
  rintro _ ⟨f, ⟨χ₂, hχ₂, hdeg, rfl⟩, rfl⟩
  exact certainTypeExtension_columnDiff_eq_dade h hχ₂ hk hdeg

/-! ### The nonzero field and the `IsCoherent` capstone -/

/-- **Degree of the conjugate column** `μ_{k⁻¹}(1) = μ_k(1)`.  The conjugate column character is the
complex conjugate `μ_{k⁻¹} = mapRingEquiv conj μ_k` (`certainType_columnSum_conj`), and the degree
`μ_k(1) = ∑_i μ_{ik}(1)` is a sum of positive integers, hence fixed by complex conjugation. -/
theorem columnSum_inv_apply_one (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (k : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    (∑ i, ((h.columnFamily k⁻¹).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily k).mu i : ClassFunction ↥L ℂ) 1) := by
  rw [← columnSum_apply_one, ← columnSum_apply_one]
  have h1 : columnSum h k⁻¹
      = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (columnSum h k) := by
    rw [columnSum_def, columnSum_def, ← certainType_columnSum_conj]
  rw [h1, ClassFunction.mapRingEquiv_apply, columnSum_apply_one, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily k).mu i)
  rw [hd, map_natCast]

/-- **Peterfalvi (4.9)(a)/(b), nonzero (`IsCoherent.nonzero`)**: `μ̄_k − μ_k` is a nonzero element of
`Z[𝒯, A]`.  Both `μ̄_k = μ_{k⁻¹}` and `μ_k` lie in `𝒯` (`k⁻¹ ≠ 1`, same degree by
`columnSum_inv_apply_one`); the difference is `A`-supported (`columnDiff_support_subset`) and nonzero
(`certainType_columnSum_conj_ne`, `μ̄_k ≠ μ_k`). -/
theorem certainType_nonzero (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {k : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hk : k ≠ 1) :
    ∃ φ : ClassFunction ↥L ℂ,
      φ ∈ S07.zSupportedSpan (certainTypeSet h k) (S04.supportInSubgroup A L) ∧ φ ≠ 0 := by
  have hk_inv : k⁻¹ ≠ 1 := fun heq => hk (inv_eq_one.mp heq)
  refine ⟨columnSum h k⁻¹ - columnSum h k, ⟨?_, ?_⟩, ?_⟩
  · exact Submodule.sub_mem _
      (Submodule.subset_span (columnSum_mem_certainTypeSet h hk_inv (columnSum_inv_apply_one h k)))
      (Submodule.subset_span (columnSum_mem_certainTypeSet h hk rfl))
  · exact columnDiff_support_subset h hk_inv hk (columnSum_inv_apply_one h k)
  · rw [sub_ne_zero]
    intro heq
    refine certainType_columnSum_conj_ne h hk ?_
    rw [certainType_columnSum_conj, ← columnSum_def, ← columnSum_def]
    exact heq

/-- **Peterfalvi Theorem (4.9)(b) — the certain-type coherence.**  The Dade map
`τ = dadeIntegralCharacterMap h.dade0 h.tau` is *coherent* on the certain-type set
`𝒯 = {μ_j | μ_j(1) = μ_k(1)}`: the global `ℤ`-linear extension `ν = certainTypeExtension h`
(`μ_{ij} ↦ δ_j ω_{ij}^σ`) is an isometry on `Z[𝒯]` agreeing with `τ` on `Z[𝒯, A]` and landing in
`ℤ[Irr G]`, and `Z[𝒯, A] ≠ 0`.  This is the (4.9) input the §8 case-B coherence capstone consumes. -/
noncomputable def certainType_isCoherent (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {k : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hk : k ≠ 1) :
    S07.IsCoherent (S07.dadeIntegralCharacterMap h.dade0 h.tau)
      (certainTypeSet h k) (S04.supportInSubgroup A L) where
  nonzero := certainType_nonzero h hk
  extension := certainTypeExtension h
  extension_inner_eq := fun _ _ hφ hψ => certainTypeExtension_inner_eq h k hφ hψ
  extends_on_supported := fun _ hφ => certainTypeExtension_eq_dade_of_mem_zSupportedSpan h hk hφ
  extension_mem_ZIrr := fun _ hφ => certainTypeExtension_mem_ZIrr h k hφ

end OddOrder.Peterfalvi.S06
