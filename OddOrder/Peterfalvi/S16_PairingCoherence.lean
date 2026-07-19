/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S14_MaximalI
import OddOrder.Peterfalvi.S09_ParityPrimitive
import OddOrder.Peterfalvi.S09_FrobeniusConjIndex
import OddOrder.Peterfalvi.S09_FrobeniusCrossOrtho

/-!
# Peterfalvi (14.14), coherence pairing data for a type-I pair

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Section 16, p. 90, proof of (14.14).

The (14.14) orthogonality switch compares the two non-conjugate type-I maximal
subgroups `L ⊇ N_G(U)` and `M ⊇ N_G(V)` of Hypothesis (14.13) through the (7.9)
dichotomy `(β_M^τ, φ^{τ₁}) ≠ 0 ∨ (β_L^τ, ψ^{τ₁}) ≠ 0`.  Both sides carry the same
§7 coherence package — the (12.1) Dade setup, the type-I Frobenius kernel, the
(12.6) coherence, and the placed induced family `{ζ_i = Ind_H^L θ_i}` — which this
file bundles as `TypeICoherent78Data` and turns into the `S09.Hypothesis78`
interface (via `hypothesis78OfDade`), mirroring for an *arbitrary* such subgroup
what `exists_M_hypothesis78` (`S16_NonExistenceG`) assembles for the `V`-side `M`.

Main definitions and results:

* `TypeICoherent78Data` — the single-subgroup assembly bundle.
* `TypeICoherent78Data.h78` — the induced `S09.Hypothesis78` over the type-I
  support `A(L) = typeIA L`.
* `TypeICoherent78Data.h78_hyp_eq` — its (7.1) layer is the (8.15) Dade data of
  the bundle (definitional).
* `TypeICoherent78Data.exists_conjIndex` /`zeta_ne_conj`/`nu_zeta_sub_conj_support`
  — the conjugate-index inputs of the (7.9) cross-orthogonality
  (`zetaImage_cross_eq_zero_of_conjIndex`), non-family forms of the
  `S09_FrobeniusConjIndex` lemmas.
* `hypothesis79_of_nonconjugate` — the two-subgroup `S09.Hypothesis79`, with
  Dade-support disjointness supplied by Peterfalvi (8.17.c)
  (`ftThickenedSupport_A1_disjoint_of_nonconjugate`) through the faithful-support
  bridge `dadeSupport_eq_ftThickenedSupport`.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Peterfalvi.S09
open OddOrder.Peterfalvi.S09.Cert
open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

/-- **The (14.14) single-side coherence bundle** for a type-I Frobenius maximal
subgroup `L`: the (12.1) Dade setup `S14.Hypothesis` (type-I data + (8.15) Dade
support data), a Frobenius-complement witness for the Fitting kernel
`H = L_F`, the (12.6) coherence of the induced family, and a placed enumeration
`θ : Fin (n+1) → Irr H` of the distinct induced characters with the distinguished
member at `0` and `Ind 1_H` at `ind1H`.  From these the §7 interface
`S09.Hypothesis78` and all its (7.9) inputs are *derived* (no further character
theory is posited). -/
structure TypeICoherent78Data [Finite G] (L : Subgroup G) where
  /-- The (12.1) type-I Dade setup of `L`. -/
  typeIHyp : OddOrder.Peterfalvi.S14.Hypothesis L
  /-- A Frobenius complement for the kernel `H = L_F` in `L`. -/
  C : Subgroup ↥L
  /-- `L` is a Frobenius group with kernel `H = L_F` and complement `C`. -/
  hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
    ((typeIHyp.typeI.typeF.H).subgroupOf L) C
  /-- The (12.6) coherence of the induced family `S` over the support `A(L)`. -/
  coh : OddOrder.Peterfalvi.S07.IsCoherent typeIHyp.tau typeIHyp.Sset typeIHyp.A
  /-- Size parameter of the placed induced family. -/
  n : ℕ
  /-- The placed enumeration of `Irr H` inducing the distinct induced characters. -/
  θ : Fin (n + 1) → IrreducibleCharacter ↥((typeIHyp.typeI.typeF.H).subgroupOf L)
  /-- Index of the induced principal character `Ind 1_H`. -/
  ind1H : Fin (n + 1)
  /-- The distinguished member sits at `0 ≠ ind1H`. -/
  ind1H_ne_zero : ind1H ≠ 0
  /-- The distinguished member has degree `e = [L : H]`. -/
  deg0 : ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf L)
      (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
    = (((typeIHyp.typeI.typeF.H).subgroupOf L).index : ℂ)
  /-- `θ ind1H = 1_H`. -/
  triv : θ ind1H = trivialIrreducibleCharacter ↥((typeIHyp.typeI.typeF.H).subgroupOf L)
  /-- The induced characters of the enumeration are distinct. -/
  inj : Function.Injective (fun i =>
    ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf L)
      (θ i : ClassFunction _ ℂ))
  /-- The enumeration covers all induced characters. -/
  cover : ∀ φ : IrreducibleCharacter ↥((typeIHyp.typeI.typeF.H).subgroupOf L),
    ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf L)
        (φ : ClassFunction _ ℂ) ∈
      Set.range (fun i =>
        ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf L)
          (θ i : ClassFunction _ ℂ))
  /-- **The (8.3)/(12.1) support shape `A(L) = typeIA = H^#`** — carried as a discharged
  field: the producer (`nonempty`) proves it from the (12.7) Frobenius structure
  (`S14.Hypothesis.typeIA_eq_sharp`), whose Type-V exclusion input is the axiom-clean
  `no_typeV_maximal_unconditional` (issue 9087).  Bundling it here keeps the member
  theorems (`h78`, `psi_support`, …) free of the (10.10) hypothesis. -/
  typeIA_eq : typeIA L typeIHyp.typeI = (typeIHyp.typeI.typeF.H : Set G) \ {1}

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

/-- The Fitting kernel `H = L_F` of the bundle. -/
abbrev kernel : Subgroup G := data.typeIHyp.typeI.typeF.H

/-- The kernel viewed inside `L`. -/
abbrev kernelIn : Subgroup ↥L := (data.kernel).subgroupOf L

/-- The `i`-th induced character `ζ_i = Ind_H^L θ_i`. -/
noncomputable abbrev zeta (i : Fin (data.n + 1)) : ClassFunction ↥L ℂ :=
  ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ)

theorem kernel_le : data.kernel ≤ L := data.typeIHyp.typeI.typeF.H_le

theorem kernelIn_normal : (data.kernelIn).Normal := by
  have h : data.kernelIn = (maxNilpotentNormalHall L).subgroupOf L := by
    rw [show data.kernelIn = (data.typeIHyp.typeI.typeF.H).subgroupOf L from rfl,
      data.typeIHyp.typeI.typeF.H_eq]
  rw [h]
  exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L

theorem kernel_conj_mem : ∀ (l : ↥L) {h : G}, h ∈ data.kernel →
    (l : G) * h * (l : G)⁻¹ ∈ data.kernel := by
  haveI := data.kernelIn_normal
  intro l h hh
  have hhL : h ∈ L := data.kernel_le hh
  have hmem : (⟨h, hhL⟩ : ↥L) ∈ data.kernelIn := Subgroup.mem_subgroupOf.mpr hh
  have hconj := data.kernelIn_normal.conj_mem ⟨h, hhL⟩ hmem l
  rw [Subgroup.mem_subgroupOf] at hconj
  simpa using hconj

/-- The type-I support is the sharp kernel: `A(L) = H \ {1}` (Peterfalvi (12.1)). -/
theorem typeIA_eq_sharp : typeIA L data.typeIHyp.typeI = (data.kernel : Set G) \ {1} :=
  data.typeIA_eq

/-- `θ 0 ≠ 1_H` (the distinguished member is not the induced principal). -/
theorem theta_zero_ne_trivial :
    data.θ 0 ≠ trivialIrreducibleCharacter ↥data.kernelIn := by
  intro h0
  refine data.ind1H_ne_zero ?_
  exact (data.inj (show data.zeta 0 = data.zeta data.ind1H by
    change ClassFunction.induce data.kernelIn ((data.θ 0 : ClassFunction _ ℂ))
      = ClassFunction.induce data.kernelIn ((data.θ data.ind1H : ClassFunction _ ℂ))
    rw [h0, data.triv])).symm

/-- `θ i ≠ 1_H` for `i ≠ ind1H`. -/
theorem theta_ne_trivial {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    data.θ i ≠ trivialIrreducibleCharacter ↥data.kernelIn := by
  intro h
  refine hi (data.inj ?_)
  change ClassFunction.induce data.kernelIn ((data.θ i : ClassFunction _ ℂ))
    = ClassFunction.induce data.kernelIn ((data.θ data.ind1H : ClassFunction _ ℂ))
  rw [h, data.triv]

/-- Each non-`ind1H` member of the placed family lies in the coherent source
family `S`. -/
theorem zeta_mem_Sset {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    data.zeta i ∈ data.typeIHyp.Sset :=
  ⟨data.θ i, data.theta_ne_trivial hi, rfl⟩

/-- The degree coefficients `d_i = θ_i(1)`. -/
noncomputable def d (i : Fin (data.n + 1)) : ℂ :=
  (data.θ i : ClassFunction ↥data.kernelIn ℂ) (1 : ↥data.kernelIn)

/-- `ζ_i(1) = d_i · ζ_0(1)`. -/
theorem zeta_deg (i : Fin (data.n + 1)) :
    data.zeta i (1 : ↥L) = data.d i * data.zeta 0 (1 : ↥L) := by
  haveI := data.kernelIn_normal
  rw [show data.zeta i (1 : ↥L)
      = ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) from rfl,
    ClassFunction.induce_apply_one data.kernelIn (data.θ i : ClassFunction _ ℂ),
    show data.zeta 0 (1 : ↥L)
      = ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
    data.deg0, d]
  ring

/-- `ζ_0(1) = ζ_{ind1H}(1)` (both are `[L:H]`). -/
theorem zeta_deg_match :
    data.zeta 0 (1 : ↥L) = data.zeta data.ind1H (1 : ↥L) := by
  haveI := data.kernelIn_normal
  change ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L)
    = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ) (1 : ↥L)
  rw [data.deg0, data.triv]
  change (((data.kernelIn).index : ℂ))
    = ClassFunction.induce data.kernelIn (trivialClassFunction ↥data.kernelIn) (1 : ↥L)
  rw [induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)]

/-- `ψ_i = ζ_i − d_i ζ_0` is supported on `A(L)`. -/
theorem psi_support (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (i : Fin (data.n + 1)) :
    (data.zeta i - data.d i • data.zeta 0).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
  haveI := data.kernelIn_normal
  refine (induce_diff_support (data.θ i) (data.θ 0) (data.d i) (data.zeta_deg i)).trans ?_
  intro x hx
  rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hx
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) x).mpr ⟨hx.1, hx.2⟩

/-- The coherent extension preserves inner products on the placed family. -/
theorem nu_isometry (i j : Fin (data.n + 1)) (hi : i ≠ data.ind1H)
    (hj : j ≠ data.ind1H) :
    ClassFunction.inner (data.coh.extension (data.zeta i))
        (data.coh.extension (data.zeta j))
      = ClassFunction.inner (data.zeta i) (data.zeta j) :=
  coherence_extension_inner_eq_on_family data.coh (data.zeta_mem_Sset hi)
    (data.zeta_mem_Sset hj)

/-- The coherence agreement `τ(ψ_i) = ν ζ_i − d_i ν ζ_0` on the supported lattice. -/
theorem hagree (hG : OddOrder.BG.IsMinimalSimpleOdd G) (i : Fin (data.n + 1))
    (_hi0 : i ≠ 0) (hi : i ≠ data.ind1H) :
    data.typeIHyp.toHypothesis71.τ ⟨data.zeta i - data.d i • data.zeta 0,
        data.psi_support hG i⟩
      = data.coh.extension (data.zeta i)
        - data.d i • data.coh.extension (data.zeta 0) := by
  obtain ⟨deg_i, -, hdeg_i_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (data.θ i)
  exact coherence_hagree_dadeMap data.typeIHyp.dadeData.dade data.typeIHyp.hconj data.coh
    (data.zeta_mem_Sset hi) (data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero))
    (m0 := 1) (mi := deg_i) (by norm_num)
    (by rw [show data.d i
        = (data.θ i : ClassFunction ↥data.kernelIn ℂ) (1 : ↥data.kernelIn) from rfl,
      hdeg_i_eq, Nat.cast_one, div_one]) (data.psi_support hG i)

/-- **The §7 coherence interface `S09.Hypothesis78`** of the bundle (Peterfalvi
(7.8) for `L`), over the type-I support `A(L) = typeIA L`.  Assembled by
`hypothesis78OfDade` exactly as in `exists_M_hypothesis78`. -/
noncomputable def h78 (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    Hypothesis78 G (typeIA L data.typeIHyp.typeI) L :=
  letI := data.kernelIn_normal
  hypothesis78OfDade data.typeIHyp.toHypothesis71
    (data.typeIHyp.dadeData.dade.fullDadeIsometryData
      data.typeIHyp.hconj).toDadeIsometryData.isDadeIsometry
    data.kernel data.kernel_le data.kernel_conj_mem (data.typeIA_eq_sharp)
    data.θ data.inj data.cover data.d (data.psi_support hG) data.zeta_deg
    data.ind1H data.ind1H_ne_zero data.triv data.zeta_deg_match
    data.coh.extension data.nu_isometry (data.hagree hG)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- The (7.1) layer of `h78` is the bundled (8.15) Dade data (definitional). -/
theorem h78_hyp_eq :
    (data.h78 hG).hyp76.hyp71.hyp = data.typeIHyp.dadeData.dade := rfl

/-- The zeta family of `h78` is the placed induced family (definitional). -/
theorem h78_zeta_eq (i : Fin (data.n + 1)) :
    (data.h78 hG).hyp76.zeta i = data.zeta i := rfl

/-- The distinguished index of `h78` is `0` (definitional). -/
theorem h78_zetaDistinct_eq : (data.h78 hG).zetaDistinct = 0 := rfl

/-- The principal index of `h78` is `ind1H` (definitional). -/
theorem h78_ind1H_eq : (data.h78 hG).ind1H = data.ind1H := rfl

/-- The coherent extension of `h78` is the bundle's coherence extension
(definitional). -/
theorem h78_nu_eq : (data.h78 hG).nu = data.coh.extension := rfl

/-- The kernel of `h78`'s (7.6) layer is the Fitting kernel (definitional). -/
theorem h78_H_eq : (data.h78 hG).hyp76.H = data.kernel := rfl

/-- **The distinguished `ζ_0` is irreducible** (Frobenius kernel induction,
[Is] Thm 6.34). -/
theorem h78_zeta_irreducible :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct) := by
  haveI := data.kernelIn_normal
  rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ 0)
    data.theta_zero_ne_trivial

/-- **The induced principal `ζ_{ind1H} = Ind 1_H` is a virtual character.** -/
theorem h78_ind_mem_ZIrr :
    (data.h78 hG).hyp76.zeta (data.h78 hG).ind1H ∈ ZIrr ↥L := by
  haveI := data.kernelIn_normal
  rw [data.h78_ind1H_eq, data.h78_zeta_eq]
  exact ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr

/-! ## The (7.9) conjugate-index inputs

Non-family forms of the `S09_FrobeniusConjIndex` lemmas: the coherent source set is the
(12.1) family `S`, the conjugate `ζ̄_0` is a family member (`conjPerm` + `cover`), the
distinguished `ζ_0` is not real (odd order), and the difference `ζ_0^ν − ζ̄_0^ν` is a Dade
image supported in the Dade support. -/

/-- **The `(7.8)` coherent source set equals the (12.1) family `S`.** -/
theorem h78_sourceSet_eq : (data.h78 hG).sourceSet = data.typeIHyp.Sset := by
  haveI := data.kernelIn_normal
  ext φ
  constructor
  · rintro ⟨idx, hidx, rfl⟩
    exact data.zeta_mem_Sset hidx
  · rintro ⟨θ', hθ'_ne, rfl⟩
    obtain ⟨j, hj⟩ := data.cover θ'
    have hj' : data.zeta j = ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ) := hj
    refine ⟨j, ?_, hj'⟩
    intro hjind
    apply induce_ne_trivialChar_induce data.kernelIn θ' hθ'_ne
    rw [← hj', show j = data.ind1H from hjind]
    change ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
      = ClassFunction.induce data.kernelIn
        ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
          ClassFunction _ ℂ)
    rw [data.triv]

/-- **The bundle coherence as an `IsCoherent` over the `(7.8)` `sourceSet`** (transport along
`h78_sourceSet_eq`, keeping the same extension `ν`). -/
noncomputable def isCoherentSourceSet :
    OddOrder.Peterfalvi.S07.IsCoherent data.typeIHyp.tau (data.h78 hG).sourceSet
      data.typeIHyp.A where
  nonzero := (data.h78_sourceSet_eq hG).symm ▸ data.coh.nonzero
  extension := data.coh.extension
  extension_inner_eq := fun φ ψ hφ hψ => data.coh.extension_inner_eq φ ψ
    (data.h78_sourceSet_eq hG ▸ hφ) (data.h78_sourceSet_eq hG ▸ hψ)
  extends_on_supported := fun φ hφ => data.coh.extends_on_supported φ
    (data.h78_sourceSet_eq hG ▸ hφ)
  extension_mem_ZIrr := fun φ hφ => data.coh.extension_mem_ZIrr φ
    (data.h78_sourceSet_eq hG ▸ hφ)

/-- The `h78` extension is the transported coherence extension (definitional). -/
theorem h78_nu_eq_isCoherentSourceSet :
    (data.h78 hG).nu = (data.isCoherentSourceSet hG).extension := rfl

/-- **The conjugate `ζ̄_0` is a family member**: there is `j₁ ≠ ind1H` with
`ζ_{j₁} = ζ̄_0` (`conjPerm` of the distinguished source is covered). -/
theorem exists_conjIndex :
    ∃ j₁, j₁ ≠ (data.h78 hG).ind1H ∧
      (data.h78 hG).hyp76.zeta j₁
        = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
  haveI := data.kernelIn_normal
  have hconj_eq : ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj
      = ClassFunction.induce data.kernelIn
          ((IrreducibleCharacter.conjPerm _ (data.θ 0)) : ClassFunction _ ℂ) := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq, conj_induce]
    exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe (data.θ 0)).symm
  obtain ⟨j₁, hj₁_range⟩ := data.cover (IrreducibleCharacter.conjPerm _ (data.θ 0))
  have hj₁_conj : (data.h78 hG).hyp76.zeta j₁
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [data.h78_zeta_eq, hconj_eq]; exact hj₁_range
  refine ⟨j₁, ?_, hj₁_conj⟩
  intro hj1
  apply data.ind1H_ne_zero
  have hzeta_inj : Function.Injective (data.h78 hG).hyp76.zeta := data.inj
  refine (hzeta_inj ?_).symm
  -- `ζ_{ind1H}` is real (`Ind 1_H`), and `ζ_{ind1H} = ζ_{j₁} = ζ̄_0`.
  have e1 : (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [← show j₁ = (data.h78 hG).ind1H from hj1]; exact hj₁_conj
  have e2 : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  calc (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)
      = ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj := by
        rw [e1, ClassFunction.conj_conj]
    _ = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := e2

/-- **The distinguished `ζ_0` is not real** (odd order): it is a nontrivial irreducible
(degree `[L:H] > 1`) of the odd-order group `L`. -/
theorem h78_zeta_ne_conj (hodd : Odd (Nat.card G)) :
    (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
      ≠ ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
  haveI := data.kernelIn_normal
  have hirr := data.h78_zeta_irreducible hG
  have hodd_L : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  -- The kernel is proper (complement nontrivial), so `[L:H] > 1`.
  have hK_ne_top : data.kernelIn ≠ ⊤ := by
    intro hKtop
    refine data.hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := data.hFrob.isComplement.disjoint
    rw [show (data.typeIHyp.typeI.typeF.H).subgroupOf L = data.kernelIn from rfl, hKtop]
      at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < (data.kernelIn).index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  have hdeg : (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct) (1 : ↥L)
      = ((data.kernelIn).index : ℂ) := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
    exact data.deg0
  have hne_triv : (⟨(data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct), hirr⟩ :
      IrreducibleCharacter ↥L) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)
        = trivialClassFunction ↥L := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : (((data.kernelIn).index : ℂ)) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    exact absurd (by exact_mod_cast hone : (data.kernelIn).index = 1) (by omega)
  intro h
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv h.symm

/-- **`ζ_0 − ζ̄_0` is supported on `A(L)`** (equal degree; both vanish off `H`). -/
theorem zeta_sub_conj_support (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {j₁ : Fin (data.n + 1)}
    (hj₁ : (data.h78 hG).hyp76.zeta j₁
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj) :
    ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
        - (data.h78 hG).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
  haveI := data.kernelIn_normal
  have hdeg : (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct) (1 : ↥L)
      = ((data.kernelIn).index : ℂ) := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
    exact data.deg0
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, hj₁, ClassFunction.conj_apply] at hx
  refine (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) x).mpr ⟨?_, ?_⟩
  · -- `x ∈ kernelIn`: else `ζ_0 x = 0`, so the difference vanishes.
    by_contra hxH
    apply hx
    rw [(data.h78 hG).hyp76.zeta_eq_zero_of_not_mem_H _ x hxH, star_zero, sub_zero]
  · -- `x ≠ 1`: at `1`, `ζ_0(1) = [L:H]` is real.
    intro hx1
    apply hx
    rw [hx1, hdeg]
    simp

/-- **`ζ_0^ν − ζ̄_0^ν` is supported in the Dade support** (the coherent extension agrees
with the Dade isometry on the equal-degree difference). -/
theorem nu_zeta_sub_conj_support (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {j₁ : Fin (data.n + 1)} (hj₁ne_ind : j₁ ≠ (data.h78 hG).ind1H)
    (hj₁ : (data.h78 hG).hyp76.zeta j₁
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj) :
    ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct)
        - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta j₁)).support
      ⊆ (data.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
  haveI := data.kernelIn_normal
  have hzd_mem : (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
      ∈ data.typeIHyp.Sset := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
    exact data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero)
  have hj₁_mem : (data.h78 hG).hyp76.zeta j₁ ∈ data.typeIHyp.Sset := by
    rw [data.h78_zeta_eq]
    exact data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hj₁ne_ind)
  have hsupp' : ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
        - (1 : ℂ) • (data.h78 hG).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
    rw [one_smul]; exact data.zeta_sub_conj_support hG hj₁
  have hagree := coherence_hagree_dadeMap data.typeIHyp.dadeData.dade data.typeIHyp.hconj
    data.coh hzd_mem hj₁_mem (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  have heq : (data.h78 hG).nu ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct)
      - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta j₁)
      = (data.typeIHyp.dadeData.dade.fullDadeIsometryData data.typeIHyp.hconj).toDadeMap
          ⟨_, (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [data.h78_nu_eq,
      ← one_smul ℂ (data.coh.extension ((data.h78 hG).hyp76.zeta j₁))]
    exact hagree.symm
  rw [heq]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_contra hgnot
  have hdade := (data.typeIHyp.dadeData.dade.fullDadeIsometryData
    data.typeIHyp.hconj).toDadeIsometryData.isDadeMap
  exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)

/-! ## The (7.8.a) `BetaDecomp` and the (7.9) delta reality -/

/-- `‖ζ_0‖² = 1` (Frobenius irreducibility of the distinguished induced member). -/
theorem zeta_zero_norm_one :
    ClassFunction.inner (data.zeta 0) (data.zeta 0) = 1 := by
  haveI := data.kernelIn_normal
  exact inner_self_induce_eq_one_of_frobeniusGroup data.hFrob (data.θ 0)
    data.theta_zero_ne_trivial

/-- **The (7.8.a) `BetaDecomp` of the bundle** — via the concrete Dade-family constructor
`betaDecompOfDade`, with `ζ_0^ν ⊥ 1_G` from `witness_L_hzeta0nu` (odd order) and the
integer `a` from `exists_betaDecomp_a`. -/
noncomputable def betaDecomp (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).BetaDecomp :=
  letI := data.kernelIn_normal
  betaDecompOfDade data.typeIHyp.toHypothesis71
    (data.typeIHyp.dadeData.dade.fullDadeIsometryData
      data.typeIHyp.hconj).toDadeIsometryData.isDadeIsometry
    data.kernel data.kernel_le data.kernel_conj_mem (data.typeIA_eq_sharp)
    data.θ data.inj data.cover data.d (data.psi_support hG) data.zeta_deg
    data.ind1H data.ind1H_ne_zero data.triv data.zeta_deg_match
    data.coh.extension data.nu_isometry (data.hagree hG)
    (OddOrder.Peterfalvi.S14.witness_L_hzeta0nu hG data.typeIHyp data.hFrob data.coh
      (data.typeIA_eq_sharp) (data.θ 0) data.theta_zero_ne_trivial)
    data.zeta_zero_norm_one
    (Classical.choose (exists_betaDecomp_a (data.h78 hG)
      (Submodule.sub_mem _
        (ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr)
        (ClassFunction.induce_mem_ZIrr _ (data.θ 0).property.mem_ZIrr))
      (data.coh.extension_mem_ZIrr _ (Submodule.subset_span
        (data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero))))))
    (Classical.choose_spec (exists_betaDecomp_a (data.h78 hG)
      (Submodule.sub_mem _
        (ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr)
        (ClassFunction.induce_mem_ZIrr _ (data.θ 0).property.mem_ZIrr))
      (data.coh.extension_mem_ZIrr _ (Submodule.subset_span
        (data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero))))))

/-- **Members of `ℤ[S]` vanishing at `1` are `A(L)`-supported** (the `hspan` input of
`extension_mapRingEquiv_comm`): each `Ind θ ∈ S` vanishes off the normal kernel
(`Sset_vanishes_off_H`), so `ℤ[S] ⊆ {ψ | supp ψ ⊆ H}` by span induction; vanishing at `1`
then lands the support in `H^# = A(L)`. -/
theorem zSpan_Sset_support_subset (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan data.typeIHyp.Sset) (h1 : φ 1 = 0) :
    φ.support ⊆ data.typeIHyp.A := by
  haveI := data.kernelIn_normal
  -- `ℤ[S] ⊆ {ψ | ψ.support ⊆ kernelIn}` by span induction.
  have hsuppH : ∀ ψ ∈ OddOrder.Peterfalvi.S07.zSpan data.typeIHyp.Sset,
      ψ.support ⊆ (data.kernelIn : Set ↥L) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        intro g hg
        rw [ClassFunction.mem_support] at hg
        by_contra hgK
        exact hg (OddOrder.Peterfalvi.S14.Sset_vanishes_off_H data.typeIHyp hx
          (fun hmem => hgK (Subgroup.mem_subgroupOf.mpr hmem)))
    | zero => intro g hg; rw [ClassFunction.mem_support] at hg; exact absurd rfl hg
    | add x y _ _ hx hy =>
        intro g hg
        rcases ClassFunction.support_add_subset x y hg with h | h
        · exact hx h
        · exact hy h
    | smul c x _ hx =>
        intro g hg
        refine hx ?_
        rw [ClassFunction.mem_support] at hg ⊢
        intro hxg
        apply hg
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hxg, mul_zero]
  intro g hg
  have hgH : g ∈ data.kernelIn := hsuppH φ hφ hg
  have hg1 : g ≠ 1 := by
    rintro rfl; exact (ClassFunction.mem_support.mp hg) h1
  change g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) g).mpr ⟨hgH, hg1⟩

/-- **The family `S` consists of irreducibles** (Frobenius kernel induction). -/
theorem Sset_subset_irreducible :
    data.typeIHyp.Sset ⊆ irreducibleCharacters ↥L := by
  haveI := data.kernelIn_normal
  rintro φ ⟨θ', hθ'_ne, rfl⟩
  exact mem_irreducibleCharacters.mpr
    (isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob θ' hθ'_ne)

/-- **The family `S` is closed under complex conjugation** (`Ind θ̄ = (Ind θ)‾`, and
`θ̄ ≠ 1` for `θ ≠ 1`). -/
theorem Sset_closedUnderConjugate {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ data.typeIHyp.Sset) :
    ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv φ ∈ data.typeIHyp.Sset := by
  haveI := data.kernelIn_normal
  obtain ⟨θ', hθ'_ne, rfl⟩ := hφ
  have hbridge : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      (ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ))
      = (ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ)).conj := by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  rw [hbridge, conj_induce]
  refine ⟨IrreducibleCharacter.conjPerm _ θ', ?_, ?_⟩
  · -- `θ̄' ≠ 1`: conjugating `θ̄' = 1` gives `θ' = 1̄ = 1`.
    intro hconj_triv
    refine hθ'_ne (IrreducibleCharacter.ext ?_)
    have hcoe := congrArg IrreducibleCharacter.toClassFunction hconj_triv
    rw [show (IrreducibleCharacter.conjPerm _ θ').toClassFunction
        = (θ' : ClassFunction ↥data.kernelIn ℂ).conj
      from IrreducibleCharacter.conjPerm_apply_coe θ'] at hcoe
    calc (θ' : ClassFunction ↥data.kernelIn ℂ)
        = ((θ' : ClassFunction ↥data.kernelIn ℂ).conj).conj := (ClassFunction.conj_conj _).symm
      _ = ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
            ClassFunction _ ℂ).conj := by rw [hcoe]
      _ = ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
            ClassFunction _ ℂ) := trivialClassFunction_isReal
  · exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe θ').symm

/-- **The coherent extension commutes with complex conjugation on `S`**
(Peterfalvi (5.9)(a) via `extension_mapRingEquiv_comm`). -/
theorem coherence_extension_conj (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ data.typeIHyp.Sset)
    (h2 : ∃ ψ ∈ data.typeIHyp.Sset, ψ ≠ χ) :
    (data.coh.extension χ).conj = data.coh.extension χ.conj := by
  have hbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hbridgeL : ∀ X : ClassFunction ↥L ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  rw [hbridgeG (data.coh.extension χ), hbridgeL χ]
  exact data.coh.extension_mapRingEquiv_comm subset_rfl data.Sset_subset_irreducible
    (fun φ hφ h1 => data.zSpan_Sset_support_subset hG hφ h1)
    Complex.conjAe.toRingEquiv (fun φ hφ => data.Sset_closedUnderConjugate hφ)
    (fun φ hφ => data.coh.extension_mem_ZIrr φ (Submodule.subset_span hφ)) hχS h2

/-- **`β̄ − β = ζ_0^ν − ζ̄_0^ν`** (the `hbeta_conj_sub` input of `delta_isReal`). -/
theorem beta_conj_sub (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).beta.conj - (data.h78 hG).beta
      = (data.h78 hG).nu ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct)
        - (data.h78 hG).nu
            ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
  classical
  haveI := data.kernelIn_normal
  set hyp := data.typeIHyp.dadeData.dade with hhyp
  set hconj := data.typeIHyp.hconj with hhconj
  set dade := hyp.fullDadeIsometryData hconj with hdade
  obtain ⟨j₁, hj₁ne, hj₁⟩ := data.exists_conjIndex hG
  -- `ζ_ind = Ind 1_H` is real.
  have hind_real : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  -- `S`-memberships of `ζ_0` and `ζ̄_0 = ζ_{j₁}`.
  have hzd_mem : (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
      ∈ data.typeIHyp.Sset := data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero)
  have hj₁_mem : (data.h78 hG).hyp76.zeta j₁ ∈ data.typeIHyp.Sset :=
    data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hj₁ne)
  have hsupp' : ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
        - (1 : ℂ) • (data.h78 hG).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
    rw [one_smul]; exact data.zeta_sub_conj_support hG hj₁
  have hagree := coherence_hagree_dadeMap hyp hconj data.coh hzd_mem hj₁_mem
    (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  -- `dade.toDadeMap` on supported functions is the ℤ-linear `dadeIntegralCharacterMap`.
  have hbridge : ∀ (φ : ClassFunction ↥L ℂ)
      (hφ : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (typeIA L data.typeIHyp.typeI) L),
      dade.toDadeMap ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
        = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade φ := by
    intro φ hφ
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp dade hφ]
    rfl
  have hiz_supp : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)
        - (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L :=
    (data.h78 hG).diff_support
  have hbeta_eq : (data.h78 hG).beta
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade
          ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)
            - (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)) := by
    rw [← hbridge _ hiz_supp]; rfl
  have hconjbridgeL : ∀ X : ClassFunction ↥L ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hconjbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hLHS : (data.h78 hG).beta.conj - (data.h78 hG).beta
      = dade.toDadeMap ⟨(data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)
          - (1 : ℂ) • (data.h78 hG).hyp76.zeta j₁,
          (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [hbridge _ hsupp', hbeta_eq,
      hconjbridgeG (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade _),
      ← OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm hyp dade
        Complex.conjAe.toRingEquiv hiz_supp, ← hconjbridgeL, ← map_sub]
    congr 1
    rw [one_smul, ClassFunction.conj_sub, hind_real, ← hj₁]
    abel
  rw [hLHS, hagree, ← hj₁, data.h78_nu_eq, one_smul]

/-- **The (7.9) residual `Δ = β − 1_G + ζ_0^ν` is real** (odd order). -/
theorem delta_isReal (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ClassFunction.IsReal (data.h78 hG).delta := by
  obtain ⟨j₁, hj₁ne, hj₁⟩ := data.exists_conjIndex hG
  have hzd_mem : (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
      ∈ data.typeIHyp.Sset := data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero)
  have hj₁_mem : (data.h78 hG).hyp76.zeta j₁ ∈ data.typeIHyp.Sset :=
    data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hj₁ne)
  have h2 : ∃ ψ ∈ data.typeIHyp.Sset,
      ψ ≠ (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct :=
    ⟨_, hj₁_mem, by rw [hj₁]; exact (data.h78_zeta_ne_conj hG hG.odd).symm⟩
  have hnu_conj : ((data.h78 hG).nu
        ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct)).conj
      = (data.h78 hG).nu
        ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [data.h78_nu_eq]
    exact data.coherence_extension_conj hG hzd_mem h2
  exact _root_.OddOrder.Peterfalvi.S09.delta_isReal (data.h78 hG) hnu_conj
    (data.beta_conj_sub hG)

/-- **The residual `Δ` is a virtual character** (coherence + irreducible sources). -/
theorem delta_mem_ZIrr (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).delta ∈ ZIrr G :=
  (data.h78 hG).delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    (data.isCoherentSourceSet hG) rfl (data.h78_ind_mem_ZIrr hG)
    (data.h78_zeta_irreducible hG)

/-- **The §4 Dade support of the bundle is the faithful thickened support**
`Ã(L) = ⋃_{x ∈ A(L)} (x·R(x))^G` (via the (8.15) faithful data). -/
theorem dadeSupport_eq (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).hyp76.hyp71.hyp.dadeSupport
      = OddOrder.Peterfalvi.S10.ftThickenedSupport L (typeIA L data.typeIHyp.typeI) := by
  rw [data.h78_hyp_eq hG]
  exact data.typeIHyp.dadeData.dadeSupport_eq_ftThickenedSupport

/-- **The type-I support is the `A₁`-support**: `A(L) = A₁(L) = (L_F)^#` (both are the
sharp Fitting kernel). -/
theorem typeIA_eq_A1 (_hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    typeIA L data.typeIHyp.typeI = A1 L PeterfalviType.I := by
  rw [data.typeIA_eq_sharp]
  change (data.kernel : Set G) \ {1} = sharpSubgroup (maxNilpotentNormalHall L)
  rw [show data.kernel = maxNilpotentNormalHall L from data.typeIHyp.typeI.typeF.H_eq]
  rfl

/-! ## General-index conjugate data (for the family-wide cross-orthogonality)

The (14.14) Bessel step pairs `β_M` against the *whole* `L`-family `{φ_i^ν}`, which
needs `⟨φ_i^ν, χ_j^ν⟩ = 0` for **all** index pairs — the general-index form of the
distinguished-`ζ` cross-orthogonality.  The conjugate-index mechanism generalizes
verbatim: `ζ̄_i` is a family member, distinct from `ζ_i` (odd order), with the
`ν`-difference supported in the Dade support. -/

/-- **The conjugate of any nontrivial family member is a family member**:
for `i ≠ ind1H` there is `i' ≠ ind1H` with `ζ_{i'} = ζ̄_i`. -/
theorem exists_conjIndex_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    ∃ i', i' ≠ (data.h78 hG).ind1H ∧
      (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj := by
  haveI := data.kernelIn_normal
  have hconj_eq : ((data.h78 hG).hyp76.zeta i).conj
      = ClassFunction.induce data.kernelIn
          ((IrreducibleCharacter.conjPerm _ (data.θ i)) : ClassFunction _ ℂ) := by
    rw [data.h78_zeta_eq, conj_induce]
    exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe (data.θ i)).symm
  obtain ⟨i', hi'_range⟩ := data.cover (IrreducibleCharacter.conjPerm _ (data.θ i))
  have hi'_conj : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj := by
    rw [data.h78_zeta_eq, hconj_eq]; exact hi'_range
  refine ⟨i', ?_, hi'_conj⟩
  intro hi'1
  -- else `ζ̄_i = ζ_{ind1H} = Ind 1_H` is real, so `ζ_i = Ind 1_H`, contra `i ≠ ind1H`.
  have hind_real : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  refine hi (data.inj ?_)
  have h1 : ((data.h78 hG).hyp76.zeta i).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    rw [← hi'_conj, hi'1]
  calc (data.h78 hG).hyp76.zeta i
      = (((data.h78 hG).hyp76.zeta i).conj).conj := (ClassFunction.conj_conj _).symm
    _ = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by rw [h1, hind_real]

/-- **No nontrivial family member is real** (odd order): `ζ_i ≠ ζ̄_i` for `i ≠ ind1H`. -/
theorem zeta_ne_conj_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hodd : Odd (Nat.card G)) :
    (data.h78 hG).hyp76.zeta i ≠ ((data.h78 hG).hyp76.zeta i).conj := by
  haveI := data.kernelIn_normal
  have hirr : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
    rw [data.h78_zeta_eq]
    exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
      (data.theta_ne_trivial hi)
  have hodd_L : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hK_ne_top : data.kernelIn ≠ ⊤ := by
    intro hKtop
    refine data.hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := data.hFrob.isComplement.disjoint
    rw [show (data.typeIHyp.typeI.typeF.H).subgroupOf L = data.kernelIn from rfl, hKtop]
      at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < (data.kernelIn).index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  -- `ζ_i(1) = [L:H]·θ_i(1) ≥ [L:H] > 1`, so `ζ_i` is nontrivial.
  obtain ⟨di, hdi_pos, hdi⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (data.θ i)
  have hdeg : (data.h78 hG).hyp76.zeta i (1 : ↥L)
      = ((data.kernelIn).index : ℂ) * (di : ℂ) := by
    rw [data.h78_zeta_eq]
    change ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) = _
    rw [ClassFunction.induce_apply_one, hdi]
  have hne_triv : (⟨(data.h78 hG).hyp76.zeta i, hirr⟩ :
      IrreducibleCharacter ↥L) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : (data.h78 hG).hyp76.zeta i = trivialClassFunction ↥L := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : ((data.kernelIn).index : ℂ) * (di : ℂ) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    have : (data.kernelIn).index * di = 1 := by exact_mod_cast hone
    have h1 : (data.kernelIn).index = 1 := by
      rcases Nat.eq_one_of_mul_eq_one_right this with h; omega
    omega
  intro h
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv h.symm

/-- **`ζ_i − ζ̄_i` is supported on `A(L)`** for any `i ≠ ind1H`. -/
theorem zeta_sub_conj_support_at (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {i i' : Fin (data.n + 1)}
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ((data.h78 hG).hyp76.zeta i - (data.h78 hG).hyp76.zeta i').support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
  haveI := data.kernelIn_normal
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, hi', ClassFunction.conj_apply] at hx
  refine (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) x).mpr ⟨?_, ?_⟩
  · by_contra hxH
    apply hx
    rw [(data.h78 hG).hyp76.zeta_eq_zero_of_not_mem_H _ x hxH, star_zero, sub_zero]
  · intro hx1
    apply hx
    rw [hx1]
    -- `ζ_i(1)` is real (`induce_apply_one_star`).
    have hreal : star ((data.h78 hG).hyp76.zeta i (1 : ↥L))
        = (data.h78 hG).hyp76.zeta i (1 : ↥L) := by
      rw [data.h78_zeta_eq]
      exact induce_apply_one_star data.kernelIn (data.θ i)
    rw [hreal, sub_self]

/-- **`ζ_i^ν − ζ̄_i^ν` is supported in the Dade support** for any `i ≠ ind1H`. -/
theorem nu_zeta_sub_conj_support_at (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {i i' : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hi'_ne : i' ≠ (data.h78 hG).ind1H)
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
        - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')).support
      ⊆ (data.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
  haveI := data.kernelIn_normal
  have hzi_mem : (data.h78 hG).hyp76.zeta i ∈ data.typeIHyp.Sset := by
    rw [data.h78_zeta_eq]; exact data.zeta_mem_Sset hi
  have hi'_mem : (data.h78 hG).hyp76.zeta i' ∈ data.typeIHyp.Sset := by
    rw [data.h78_zeta_eq]
    exact data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hi'_ne)
  have hsupp' : ((data.h78 hG).hyp76.zeta i
        - (1 : ℂ) • (data.h78 hG).hyp76.zeta i').support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
    rw [one_smul]; exact data.zeta_sub_conj_support_at hG hi'
  have hagree := coherence_hagree_dadeMap data.typeIHyp.dadeData.dade data.typeIHyp.hconj
    data.coh hzi_mem hi'_mem (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  have heq : (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
      - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')
      = (data.typeIHyp.dadeData.dade.fullDadeIsometryData data.typeIHyp.hconj).toDadeMap
          ⟨_, (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [data.h78_nu_eq,
      ← one_smul ℂ (data.coh.extension ((data.h78 hG).hyp76.zeta i'))]
    exact hagree.symm
  rw [heq]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_contra hgnot
  have hdade := (data.typeIHyp.dadeData.dade.fullDadeIsometryData
    data.typeIHyp.hconj).toDadeIsometryData.isDadeMap
  exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)

/-- **Each `ζ_i^ν` (`i ≠ ind1H`) is a unit-norm virtual character.** -/
theorem nu_zeta_norm_one {i : Fin (data.n + 1)} (hi : i ≠ (data.h78 hG).ind1H) :
    ClassFunction.inner ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i))
      ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)) = 1 := by
  haveI := data.kernelIn_normal
  rw [(data.h78 hG).nu_isometry i i hi hi]
  have hirr : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
    rw [data.h78_zeta_eq]
    exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
      (data.theta_ne_trivial (by rw [← data.h78_ind1H_eq hG]; exact hi))
  exact IsIrreducibleCharacter.inner_self_eq_one hirr

/-- **Each nontrivial family member induces irreducibly** (general-index form of
`h78_zeta_irreducible`). -/
theorem zeta_irreducible_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
  haveI := data.kernelIn_normal
  rw [data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
    (data.theta_ne_trivial hi)

/-- **`⟨ζ_i^ν, ζ̄_i^ν⟩ = 0`**: the conjugate pair is orthonormal (`ν`-isometry +
distinct irreducibles). -/
theorem nu_zeta_inner_nu_conj_eq_zero (hodd : Odd (Nat.card G))
    {i i' : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hi'_ne : i' ≠ (data.h78 hG).ind1H)
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ClassFunction.inner ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i))
      ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')) = 0 := by
  rw [(data.h78 hG).nu_isometry i i' hi hi'_ne]
  have hirr_i := data.zeta_irreducible_at hG hi
  have hirr_i' : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i') :=
    data.zeta_irreducible_at hG (by rw [← data.h78_ind1H_eq hG]; exact hi'_ne)
  have hne : (data.h78 hG).hyp76.zeta i ≠ (data.h78 hG).hyp76.zeta i' := by
    rw [hi']
    exact data.zeta_ne_conj_at hG hi hodd
  have h := irreducibleCharacter_inner_eq_ite
    (⟨_, hirr_i⟩ : IrreducibleCharacter ↥L) ⟨_, hirr_i'⟩
  rwa [if_neg (fun heq => hne (congrArg Subtype.val heq))] at h

/-- **Existence of the bundle for any type-I maximal subgroup** (Peterfalvi (12.1) +
(12.6) + (12.7)): the Dade setup from `exists_typeI_hypothesis`, the Frobenius witness
from the headline (12.7) `typeI_frobenius`, the coherence from
`frobenius_typeI_coherent`, and the placed family from
`exists_witness_placed_family`. -/
theorem nonempty (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {L : Subgroup G}
    (hLmax : L ∈ maximalSubgroups G) (hLtypeI : IsTypeI L) :
    Nonempty (TypeICoherent78Data L) := by
  classical
  obtain ⟨typeIHyp⟩ := OddOrder.Peterfalvi.S14.exists_typeI_hypothesis hG hLmax hLtypeI
  obtain ⟨fdata, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV hLmax hLtypeI
  -- Transport the Frobenius witness to `typeIHyp`'s kernel (both are `L_F`).
  have hHeq : fdata.typeI.typeF.H = typeIHyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, typeIHyp.typeI.typeF.H_eq]
  have hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((typeIHyp.typeI.typeF.H).subgroupOf L) fdata.complement := by
    rw [← hHeq]; exact fdata.frobenius
  obtain ⟨coh⟩ := OddOrder.Peterfalvi.S14.frobenius_typeI_coherent hG typeIHyp
    ⟨fdata.complement, hFrob⟩
  obtain ⟨n, θ, ind1H, hind1H, hdeg0, htriv, hinj, hcover⟩ :=
    OddOrder.Peterfalvi.S14.exists_witness_placed_family typeIHyp
  exact ⟨{ typeIHyp := typeIHyp
           C := fdata.complement
           hFrob := hFrob
           coh := coh
           n := n
           θ := θ
           ind1H := ind1H
           ind1H_ne_zero := hind1H
           deg0 := hdeg0
           triv := htriv
           inj := hinj
           cover := hcover
           typeIA_eq :=
             OddOrder.Peterfalvi.S14.Hypothesis.typeIA_eq_sharp hG hnoV typeIHyp }⟩

end TypeICoherent78Data

section Pairing

variable [Finite G] {L M : Subgroup G}
variable (dataL : TypeICoherent78Data L) (dataM : TypeICoherent78Data M)
variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- **The two-subgroup (7.9) datum for a non-conjugate type-I pair** (Peterfalvi (14.14)
setup).  Bundles the two `Hypothesis78`s with the Dade-support disjointness, which is
Peterfalvi (8.17.c) (`ftThickenedSupport_A1_disjoint_of_nonconjugate`) after the
faithful-support and `A₁`-support bridges. -/
noncomputable def hypothesis79OfNonconjugate
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M) :
    Hypothesis79 G (typeIA L dataL.typeIHyp.typeI) L
      (typeIA M dataM.typeIHyp.typeI) M where
  odd_card := hG.odd
  first := dataL.h78 hG
  second := dataM.h78 hG
  dadeSupport_disjoint := by
    rw [dataL.dadeSupport_eq hG, dataM.dadeSupport_eq hG, dataL.typeIA_eq_A1 hG,
      dataM.typeIA_eq_A1 hG]
    exact OddOrder.Peterfalvi.S10.ftThickenedSupport_A1_disjoint_of_nonconjugate hG hL hM
      (show OddOrder.GroupTheory.HasPeterfalviType OddOrder.GroupTheory.PeterfalviType.I L from
        ⟨dataL.typeIHyp.typeI⟩)
      (show OddOrder.GroupTheory.HasPeterfalviType OddOrder.GroupTheory.PeterfalviType.I M from
        ⟨dataM.typeIHyp.typeI⟩) hnc

/-- **The (7.9) cross-orthogonality for the pair**: `⟨ζ_L^ν, ζ_M^ν⟩ = 0`, via the
conjugate-index mechanism of both sides. -/
theorem hypothesis79OfNonconjugate_zetaImage_cross_eq_zero
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M) :
    ClassFunction.inner
        (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).firstZetaImage
        (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).secondZetaImage = 0 := by
  obtain ⟨j₁, hj₁ne, hj₁⟩ := dataL.exists_conjIndex hG
  obtain ⟨j₂, hj₂ne, hj₂⟩ := dataM.exists_conjIndex hG
  exact (hypothesis79OfNonconjugate dataL dataM hG hL hM
      hnc).zetaImage_cross_eq_zero_of_conjIndex
    (dataL.isCoherentSourceSet hG) rfl (dataM.isCoherentSourceSet hG) rfl
    (dataL.h78_zeta_irreducible hG) (dataM.h78_zeta_irreducible hG)
    hj₁ne hj₁ (dataL.h78_zeta_ne_conj hG hG.odd)
    hj₂ne hj₂ (dataM.h78_zeta_ne_conj hG hG.odd)
    (dataL.nu_zeta_sub_conj_support hG hj₁ne hj₁)
    (dataM.nu_zeta_sub_conj_support hG hj₂ne hj₂)

/-- **The `(Δ_L, Δ_M)` cross term is an even integer** (Peterfalvi (7.9) parity): both
residuals are real virtual characters orthogonal to `1_G`, so `cfdot_real_vchar_even`
applies with vanishing trivial components. -/
theorem hypothesis79OfNonconjugate_delta_cross_even
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M) :
    ∃ z : ℤ,
      ClassFunction.inner
          (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).first.delta
          (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).second.delta = (z : ℂ) ∧
        Even z := by
  obtain ⟨m, a, b, hm, ha, hb, heven⟩ := cfdot_real_vchar_even hG.odd
    (dataL.delta_mem_ZIrr hG) (dataL.delta_isReal hG)
    (dataM.delta_mem_ZIrr hG) (dataM.delta_isReal hG)
  refine ⟨m, hm.symm, ?_⟩
  -- `a = ⟨Δ_L, 1_G⟩ = 0` (`delta_orth_one`), so `Even (m − a·b) = Even m`.
  have ha0 : a = 0 := by
    have h := (dataL.h78 hG).delta_orth_one (dataL.betaDecomp hG)
    rw [show (trivialIrreducibleCharacter G : ClassFunction G ℂ)
        = Hypothesis71.constOne G from rfl, h] at ha
    exact_mod_cast ha
  rw [ha0] at heven
  simpa using heven

/-- **Family-wide cross-orthogonality** (Peterfalvi's "(4.1): `ℒ^{τ₁}` is orthogonal to
`ℳ^{τ₁}`"): `⟨φ_i^ν, χ_j^ν⟩ = 0` for **every** pair of nontrivial family indices.  Each
side pairs with its conjugate member (equal degree, distinct by odd order), the two
`ν`-differences are Dade images in the disjoint supports, and
`orthonormal_vchar_diff_ortho` concludes. -/
theorem pair_cross_orthogonal
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M)
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H)
    {j : Fin (dataM.n + 1)} (hj : j ≠ dataM.ind1H) :
    ClassFunction.inner ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i))
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta j)) = 0 := by
  obtain ⟨i', hi'ne, hi'⟩ := dataL.exists_conjIndex_at hG hi
  obtain ⟨j', hj'ne, hj'⟩ := dataM.exists_conjIndex_at hG hj
  have hi_h78 : i ≠ (dataL.h78 hG).ind1H := by
    rw [dataL.h78_ind1H_eq]; exact hi
  have hj_h78 : j ≠ (dataM.h78 hG).ind1H := by
    rw [dataM.h78_ind1H_eq]; exact hj
  refine orthonormal_vchar_diff_ortho
    ((dataL.h78 hG).nu_zeta_mem_ZIrr_of_isCoherent (dataL.isCoherentSourceSet hG) rfl hi_h78)
    ((dataL.h78 hG).nu_zeta_mem_ZIrr_of_isCoherent (dataL.isCoherentSourceSet hG) rfl hi'ne)
    ((dataM.h78 hG).nu_zeta_mem_ZIrr_of_isCoherent (dataM.isCoherentSourceSet hG) rfl hj_h78)
    ((dataM.h78 hG).nu_zeta_mem_ZIrr_of_isCoherent (dataM.isCoherentSourceSet hG) rfl hj'ne)
    (dataL.nu_zeta_norm_one hG hi_h78) (dataL.nu_zeta_norm_one hG hi'ne)
    (dataM.nu_zeta_norm_one hG hj_h78) (dataM.nu_zeta_norm_one hG hj'ne)
    (dataL.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hi hi'ne hi')
    (dataM.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hj hj'ne hj')
    ?_ ?_ ?_
  · -- The two `ν`-differences live in the disjoint Dade supports.
    apply ClassFunction.inner_eq_zero_of_disjoint_support
    rw [Set.disjoint_left]
    intro g hg₁ hg₂
    exact Set.disjoint_left.mp
      (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).dadeSupport_disjoint
      (dataL.nu_zeta_sub_conj_support_at hG hi hi'ne hi' hg₁)
      (dataM.nu_zeta_sub_conj_support_at hG hj hj'ne hj' hg₂)
  · -- Equal degrees on the `L`-side: the difference vanishes at `1 ∉ Ã(L)`.
    have hz : ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)
        - (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i')) (1 : G) = 0 := by
      by_contra h
      exact (dataL.h78 hG).hyp76.hyp71.hyp.one_notMem_dadeSupport
        (dataL.nu_zeta_sub_conj_support_at hG hi hi'ne hi'
          (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz
  · -- Equal degrees on the `M`-side.
    have hz : ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta j)
        - (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta j')) (1 : G) = 0 := by
      by_contra h
      exact (dataM.h78 hG).hyp76.hyp71.hyp.one_notMem_dadeSupport
        (dataM.nu_zeta_sub_conj_support_at hG hj hj'ne hj'
          (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz

/-- **The Peterfalvi (7.9) dichotomy for a non-conjugate type-I pair**:
`(β_L, ζ_M^ν) ≠ 0 ∨ (β_M, ζ_L^ν) ≠ 0`.  This is the character-theoretic heart of the
(14.14) orthogonality switch. -/
theorem pairing_dichotomy
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M) :
    (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).conclusion :=
  (hypothesis79OfNonconjugate dataL dataM hG hL hM
      hnc).conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity
    (dataL.isCoherentSourceSet hG) rfl (dataM.isCoherentSourceSet hG) rfl
    (dataL.h78_ind_mem_ZIrr hG) (dataL.h78_zeta_irreducible hG)
    (dataM.h78_ind_mem_ZIrr hG) (dataM.h78_zeta_irreducible hG)
    (dataL.betaDecomp hG) (dataM.betaDecomp hG)
    (hypothesis79OfNonconjugate_zetaImage_cross_eq_zero dataL dataM hG hL hM hnc)
    (hypothesis79OfNonconjugate_delta_cross_even dataL dataM hG hL hM hnc)

end Pairing

end OddOrder.Peterfalvi.S16
