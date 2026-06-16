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
    {k : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hk : k ≠ 1)
    {η₁ : ClassFunction ↥L ℂ} {a₀ : ℕ}
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ)
    (hXanchored : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
      (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
        = (∑ i, ((h46.columnFamily k).mu i : ClassFunction ↥L ℂ) 1) →
      hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a₀ • η₁)
        = Ximg χ₂ - a₀ • hyp.coherentYset.extension η₁)
    (hXinner : ∀ χ₂ χ₂' : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ,
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
        obtain ⟨χ₂, -, -, rfl⟩ := hu
        obtain ⟨χ₂', -, -, rfl⟩ := hv
        rw [xChiExtension_columnSum, xChiExtension_columnSum]
        exact hXinner χ₂ χ₂'
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
    have e1 := hXanchored χ₂ hχ₂ hdeg
    have e2 := hXanchored k hk rfl
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

end OddOrder.Peterfalvi.S08
