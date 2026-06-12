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

end OddOrder.Peterfalvi.S06
