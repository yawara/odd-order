/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.MaximalSubgroupType

/-!
# Conjugation-invariance of the maximal-subgroup types

The Peterfalvi maximal-subgroup taxonomy (`IsTypeF`, `IsTypeI`, ..., `IsTypeV`) is
defined intrinsically from a subgroup `M ≤ G` via constructions — the Fitting kernel
`maxNilpotentNormalHall M`, complements, centralizers, exponents, ranks — that are all
natural under automorphisms of `G`.  This file makes that precise: every type predicate
is invariant under the pointwise action of `MulAut G`, so in particular conjugate maximal
subgroups have the same Peterfalvi type.

The driving application (Peterfalvi (13.17.b), `OddOrder.Peterfalvi.S15`) is the
non-conjugacy of a type-`I` subgroup `L` to the type-II subgroups `S`, `T`: if `conj g • L`
were `S`, then `S` would be type `I` (`isTypeI_pointwise_smul`), contradicting
`not_isTypeI_of_isTypeNonI`.

## Main results

* `isTypeF_pointwise_smul`, `isTypeI_pointwise_smul`, ... — each type predicate transfers
  along `φ : MulAut G`.
* A reusable equivariance toolkit (`card_pointwise_smul`, `isFrobeniusGroup_map_of_mulEquiv`,
  `isTISubset_pointwise_smul`, `rank_map_of_mulEquiv`, ...) phrased for the general
  pointwise `MulAut G` action; reusable across the §16 conjugacy arguments.
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Equivariance toolkit for `MulAut G`

The pointwise action `φ • K = K.map (φ : G →* G)` of `φ : MulAut G` on `Subgroup G`
preserves all the structural data the type predicates are built from. These lemmas are
phrased for a general `φ : MulAut G` (so `MulAut.conj g` is a special case) and are
reusable. -/

section Toolkit

variable (φ : MulAut G)

/-- The restricted isomorphism `↥K ≃* ↥(φ • K)` induced by `φ : MulAut G`. -/
noncomputable def conjSubgroupEquiv (K : Subgroup G) : ↥K ≃* ↥(φ • K) :=
  (Subgroup.equivMapOfInjective K (φ : G →* G) φ.injective).trans
    (MulEquiv.subgroupCongr (pointwise_mulAut_smul_eq_map φ K).symm)

/-- `|φ • K| = |K|`: the pointwise `MulAut` action preserves cardinality. -/
theorem card_pointwise_smul (K : Subgroup G) :
    Nat.card ↥(φ • K) = Nat.card ↥K := by
  rw [pointwise_mulAut_smul_eq_map]; exact Subgroup.card_map_of_injective φ.injective

/-- The pointwise `MulAut` action preserves the trivial subgroup test. -/
@[simp] theorem pointwise_smul_eq_bot_iff {K : Subgroup G} :
    φ • K = ⊥ ↔ K = ⊥ := by
  rw [pointwise_mulAut_smul_eq_map, Subgroup.map_eq_bot_iff_of_injective _ φ.injective]

/-- `IsCyclic` transfers along the pointwise `MulAut` action. -/
theorem isCyclic_pointwise_smul {K : Subgroup G} (h : IsCyclic ↥K) :
    IsCyclic ↥(φ • K) :=
  isCyclic_of_surjective _ (conjSubgroupEquiv φ K).surjective

/-- `IsMulCommutative` transfers along any group isomorphism. -/
theorem isMulCommutative_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsMulCommutative A) : IsMulCommutative B :=
  ⟨⟨fun a b => e.symm.injective (by rw [map_mul, map_mul, h.is_comm.comm])⟩⟩

/-- `IsMulCommutative` transfers along the pointwise `MulAut` action. -/
theorem isMulCommutative_pointwise_smul {K : Subgroup G} (h : IsMulCommutative ↥K) :
    IsMulCommutative ↥(φ • K) :=
  isMulCommutative_of_mulEquiv (conjSubgroupEquiv φ K) h

/-- `Monoid.exponent` is invariant under any group isomorphism. -/
theorem exponent_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Monoid.exponent A = Monoid.exponent B :=
  Monoid.exponent_eq_of_mulEquiv e

/-- `Monoid.exponent` is invariant under the pointwise `MulAut` action. -/
theorem exponent_pointwise_smul (K : Subgroup G) :
    Monoid.exponent ↥(φ • K) = Monoid.exponent ↥K :=
  (exponent_of_mulEquiv (conjSubgroupEquiv φ K)).symm

/-- The coercion of `φ • K` to a set is the `φ`-image of `K`. -/
theorem coe_pointwise_smul (K : Subgroup G) :
    ((φ • K : Subgroup G) : Set G) = φ '' (K : Set G) := by
  rw [pointwise_mulAut_smul_eq_map]; exact Subgroup.coe_map _ _

/-- The pointwise `MulAut` action commutes with the centralizer of a set. -/
theorem centralizer_pointwise_smul (X : Set G) :
    φ • Subgroup.centralizer X = Subgroup.centralizer (φ '' X) := by
  rw [pointwise_mulAut_smul_eq_map]
  exact Subgroup.map_centralizer_eq_of_bijective X (φ : G →* G) φ.bijective

/-- The pointwise `MulAut` action commutes with the normalizer of a subgroup. -/
theorem normalizer_pointwise_smul (H : Subgroup G) :
    φ • Subgroup.normalizer (H : Set G) = Subgroup.normalizer ((φ • H : Subgroup G) : Set G) := by
  rw [pointwise_mulAut_smul_eq_map φ (Subgroup.normalizer (H : Set G)),
    show (φ • H : Subgroup G) = H.map (φ : G →* G) from pointwise_mulAut_smul_eq_map φ H]
  exact Subgroup.map_normalizer_eq_of_bijective H φ.bijective

/-- `sharpSubgroup` (nonidentity elements) is equivariant under the pointwise `MulAut` action. -/
theorem image_sharpSubgroup (H : Subgroup G) :
    φ '' sharpSubgroup H = sharpSubgroup (φ • H) := by
  unfold sharpSubgroup
  rw [Set.image_diff φ.injective, coe_pointwise_smul]
  congr 1
  rw [Set.image_singleton, map_one]

/-- `IsTISubset` transfers along the pointwise `MulAut` action. -/
theorem isTISubset_pointwise_smul {A : Set G} {L : Subgroup G} (h : IsTISubset A L) :
    IsTISubset (φ '' A) (φ • L) := by
  rintro g ⟨a', ⟨a, ha, rfl⟩, b, hb, hgb⟩
  rw [pointwise_mulAut_smul_eq_map]
  refine ⟨φ.symm g, h (φ.symm g) ⟨a, ha, ?_⟩, φ.apply_symm_apply g⟩
  -- `hgb : φ b = g * φ a * g⁻¹`; apply `φ⁻¹` to read off the conjugate of `a` by `φ.symm g`.
  have hconj : φ.symm g * a * (φ.symm g)⁻¹ = b := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, φ.apply_symm_apply]
    exact hgb.symm
  rw [hconj]; exact hb

end Toolkit

/-! ### Transfer of structural predicates along a group isomorphism

These lemmas transfer the `subgroupOf`-level data of `TypeFData` — complements, normality,
the Frobenius witness, rank — along an arbitrary `MulEquiv`.  Combined with
`map_subgroupMap_subgroupOf` (which identifies `(K.subgroupOf M).map (φ.subgroupMap M)` with
`(φ • K).subgroupOf (φ • M)`) they discharge the relative fields of the type data. -/

section TransferAlongMulEquiv

variable {A B : Type*} [Group A] [Group B]

/-- `IsComplement'` transfers along a group isomorphism (finite source). -/
theorem isComplement'_map_of_mulEquiv [Finite A] (e : A ≃* B) {N K : Subgroup A}
    (h : N.IsComplement' K) :
    (N.map (e : A →* B)).IsComplement' (K.map (e : A →* B)) := by
  haveI : Finite B := Finite.of_equiv A e.toEquiv
  rw [Subgroup.isComplement'_iff_card_mul_and_disjoint] at h ⊢
  obtain ⟨hcard, hdisj⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, Subgroup.card_map_of_injective e.injective,
      ← Nat.card_congr e.toEquiv]
    exact hcard
  · rw [disjoint_iff, ← Subgroup.map_inf_eq N K (e : A →* B) e.injective, disjoint_iff.mp hdisj,
      Subgroup.map_bot]

/-- `IsFrobeniusGroup` transfers along a group isomorphism (finite source). -/
theorem isFrobeniusGroup_map_of_mulEquiv [Finite A] (e : A ≃* B) {N K : Subgroup A}
    (h : Ch06.IsFrobeniusGroup A N K) :
    Ch06.IsFrobeniusGroup B (N.map (e : A →* B)) (K.map (e : A →* B)) := by
  refine ⟨h.isNormal.map (e : A →* B) e.surjective, isComplement'_map_of_mulEquiv e h.isComplement,
    mt (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h.ne_bot_kernel,
    mt (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h.ne_bot_complement, ?_⟩
  intro a ha hane n hn hnne
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨n₀, hn₀, rfl⟩ := Subgroup.mem_map.mp hn
  have ha₀ne : a₀ ≠ 1 := fun h => hane (by rw [h, map_one])
  have hn₀ne : n₀ ≠ 1 := fun h => hnne (by rw [h, map_one])
  intro hcontra
  apply h.conj_frobenius a₀ ha₀ ha₀ne n₀ hn₀ hn₀ne
  apply e.injective
  rw [map_mul, map_mul, map_inv]
  exact hcontra

/-- The `p`-rank is invariant under a group isomorphism (finite source). -/
theorem pRank_eq_of_mulEquiv [Finite A] (e : A ≃* B) (p : ℕ) :
    pRank A p = pRank B p := by
  haveI : Finite B := Finite.of_equiv A e.toEquiv
  exact le_antisymm (pRank_le_of_injective (f := e.toMonoidHom) e.injective)
    (pRank_le_of_injective (f := e.symm.toMonoidHom) e.symm.injective)

/-- The group rank `r(G)` is invariant under a group isomorphism (finite source). -/
theorem rank_of_mulEquiv [Finite A] (e : A ≃* B) : rank A = rank B :=
  iSup_congr fun p => pRank_eq_of_mulEquiv e p.1

end TransferAlongMulEquiv

section OpiCore

variable [Finite G] (φ : MulAut G)

/-- **`opiCoreInG` is `MulAut`-equivariant**: `φ • O_π(H) = O_π(φ • H)`.  The `π`-core
`oPiCore π ↥H` is characteristic, so the iso `↥H ≃* ↥(φ•H)` induced by `φ` carries it onto
`oPiCore π ↥(φ•H)`. -/
theorem opiCoreInG_pointwise_smul (π : Set ℕ) (H : Subgroup G) :
    φ • opiCoreInG π H = opiCoreInG π (φ • H) := by
  have hHmap : H.map (φ : G →* G) = φ • H := (pointwise_mulAut_smul_eq_map φ H).symm
  let e : ↥H ≃* ↥(φ • H) :=
    (Subgroup.equivMapOfInjective H (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hHmap)
  have hcomp : (φ • H).subtype.comp (e : ↥H →* ↥(φ • H)) = (φ : G →* G).comp H.subtype := by
    ext x; rfl
  calc φ • opiCoreInG π H
      = (opiCoreInG π H).map (φ : G →* G) := pointwise_mulAut_smul_eq_map φ _
    _ = ((Ch03.oPiCore π ↥H).map H.subtype).map (φ : G →* G) := rfl
    _ = (Ch03.oPiCore π ↥H).map ((φ : G →* G).comp H.subtype) := by rw [Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥H).map ((φ • H).subtype.comp (e : ↥H →* ↥(φ • H))) := by rw [hcomp]
    _ = ((Ch03.oPiCore π ↥H).map (e : ↥H →* ↥(φ • H))).map (φ • H).subtype := by
        rw [← Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥(φ • H)).map (φ • H).subtype := by
        rw [Ch03.oPiCore.map_eq_of_mulEquiv]
    _ = opiCoreInG π (φ • H) := rfl

end OpiCore

/-! ### `subgroupOf`-level transfers

The relative fields of `TypeFData` (`complement`, `U1_normal`) involve `subgroupOf`-subgroups
inside `↥M`/`↥U`.  These lemmas combine `map_subgroupMap_subgroupOf` with the `MulEquiv`-transfer
toolkit to move them along `φ`. -/

section SubgroupOfTransfer

variable [Finite G] (φ : MulAut G)

/-- `IsComplement'` of `subgroupOf`-subgroups transfers along the pointwise `MulAut` action. -/
theorem isComplement'_subgroupOf_pointwise_smul {H U M : Subgroup G}
    (h : Subgroup.IsComplement' (H.subgroupOf M) (U.subgroupOf M)) :
    Subgroup.IsComplement' ((φ • H).subgroupOf (φ • M)) ((φ • U).subgroupOf (φ • M)) := by
  rw [show (φ • H : Subgroup G) = H.map (φ : G →* G) from pointwise_mulAut_smul_eq_map φ H,
    show (φ • U : Subgroup G) = U.map (φ : G →* G) from pointwise_mulAut_smul_eq_map φ U,
    show (φ • M : Subgroup G) = M.map (φ : G →* G) from pointwise_mulAut_smul_eq_map φ M,
    ← map_subgroupMap_subgroupOf, ← map_subgroupMap_subgroupOf]
  exact isComplement'_map_of_mulEquiv (φ.subgroupMap M) h

/-- Normality of a `subgroupOf`-subgroup transfers along the pointwise `MulAut` action. -/
theorem normal_subgroupOf_pointwise_smul {N U : Subgroup G} (h : (N.subgroupOf U).Normal) :
    ((φ • N).subgroupOf (φ • U)).Normal := by
  rw [show (φ • N : Subgroup G) = N.map (φ : G →* G) from pointwise_mulAut_smul_eq_map φ N,
    show (φ • U : Subgroup G) = U.map (φ : G →* G) from pointwise_mulAut_smul_eq_map φ U,
    ← map_subgroupMap_subgroupOf]
  exact h.map (φ.subgroupMap U : ↥U →* ↥(U.map (φ : G →* G))) (φ.subgroupMap U).surjective

/-- The Frobenius witness `IsFrobeniusGroup ↥(H ⊔ U0) (H.subgroupOf _) (U0.subgroupOf _)` transfers
along the pointwise `MulAut` action. -/
theorem isFrobeniusGroup_subgroupOf_pointwise_smul {H U0 : Subgroup G}
    (h : Ch06.IsFrobeniusGroup ↥(H ⊔ U0) (H.subgroupOf (H ⊔ U0)) (U0.subgroupOf (H ⊔ U0))) :
    Ch06.IsFrobeniusGroup ↥(φ • H ⊔ φ • U0)
      ((φ • H).subgroupOf (φ • H ⊔ φ • U0)) ((φ • U0).subgroupOf (φ • H ⊔ φ • U0)) := by
  have e := isFrobeniusGroup_map_of_mulEquiv (φ.subgroupMap (H ⊔ U0)) h
  rw [map_subgroupMap_subgroupOf, map_subgroupMap_subgroupOf,
    ← pointwise_mulAut_smul_eq_map φ H, ← pointwise_mulAut_smul_eq_map φ U0,
    ← pointwise_mulAut_smul_eq_map φ (H ⊔ U0), Subgroup.smul_sup] at e
  exact e

/-- The centralizer-bound field of `TypeFData` transfers along the pointwise `MulAut` action. -/
theorem inf_centralizer_le_pointwise_smul {H U U1 : Subgroup G}
    (h : ∀ x ∈ H, x ≠ 1 → U ⊓ Subgroup.centralizer ({x} : Set G) ≤ U1) :
    ∀ x ∈ φ • H, x ≠ 1 → (φ • U) ⊓ Subgroup.centralizer ({x} : Set G) ≤ φ • U1 := by
  intro x hx hxne
  rw [pointwise_mulAut_smul_eq_map] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hyne : y ≠ 1 := fun hy1 => hxne (by rw [← hyx, hy1, map_one])
  have hxset : ({x} : Set G) = φ '' ({y} : Set G) := by rw [Set.image_singleton, ← hyx]; rfl
  rw [hxset, ← centralizer_pointwise_smul, ← Subgroup.smul_inf]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (h y hy hyne)

end SubgroupOfTransfer

/-! ## Conjugation transfer of the type data and predicates -/

variable [Finite G]

/-- **`TypeFData` is automorphism-equivariant.**  All structural data of a type-`F` subgroup
transfers along `φ : MulAut G`, giving type-`F` data for `φ • M`. -/
def TypeFData.conj (φ : MulAut G) {M : Subgroup G} (data : TypeFData M) :
    TypeFData (φ • M) where
  H := φ • data.H
  U := φ • data.U
  U1 := φ • data.U1
  U0 := φ • data.U0
  H_eq := by rw [data.H_eq, maxNilpotentNormalHall_pointwise_smul]
  H_nontrivial := mt (pointwise_smul_eq_bot_iff φ).mp data.H_nontrivial
  U_nontrivial := mt (pointwise_smul_eq_bot_iff φ).mp data.U_nontrivial
  H_le := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.H_le
  U_le := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.U_le
  U1_le := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.U1_le
  U0_le := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.U0_le
  complement := isComplement'_subgroupOf_pointwise_smul φ data.complement
  U1_normal := normal_subgroupOf_pointwise_smul φ data.U1_normal
  U1_commutative := isMulCommutative_pointwise_smul φ data.U1_commutative
  centralizer_le_U1 := inf_centralizer_le_pointwise_smul φ data.centralizer_le_U1
  exponent_eq := by rw [exponent_pointwise_smul, exponent_pointwise_smul]; exact data.exponent_eq
  frobenius_HU0 := isFrobeniusGroup_subgroupOf_pointwise_smul φ data.frobenius_HU0

/-- **`TypeIData` is automorphism-equivariant.** -/
def TypeIData.conj (φ : MulAut G) {M : Subgroup G} (data : TypeIData M) :
    TypeIData (φ • M) where
  typeF := data.typeF.conj φ
  alternative := by
    rcases data.alternative with h | h | h
    · left
      have hti := isTISubset_pointwise_smul φ h
      rwa [image_sharpSubgroup, normalizer_pointwise_smul] at hti
    · right; left
      refine ⟨isMulCommutative_pointwise_smul φ h.1, ?_⟩
      show rank ↥(φ • data.typeF.H) = 2
      rw [← rank_of_mulEquiv (conjSubgroupEquiv φ data.typeF.H)]; exact h.2
    · right; right
      obtain ⟨h1, p, hp, hpmem, hcyc⟩ := h
      have hcard : Nat.card ↥(φ • data.typeF.H) = Nat.card ↥data.typeF.H := card_pointwise_smul φ _
      show (∀ q : ℕ, q.Prime → q ∈ (Nat.card ↥(φ • data.typeF.H)).primeFactors →
          Monoid.exponent ↥(φ • data.typeF.U) ∣ q - 1) ∧
        ∃ q : ℕ, q.Prime ∧ q ∈ (Nat.card ↥(φ • data.typeF.H)).primeFactors ∧
          IsCyclic ↥(opiCoreInG {q}ᶜ (φ • data.typeF.H))
      refine ⟨fun q hq hqmem => ?_, p, hp, by rwa [hcard], ?_⟩
      · rw [exponent_pointwise_smul]; exact h1 q hq (by rwa [hcard] at hqmem)
      · rw [← opiCoreInG_pointwise_smul]; exact isCyclic_pointwise_smul φ hcyc

/-- **`IsTypeI` is invariant under the pointwise `MulAut` action.** -/
theorem isTypeI_pointwise_smul (φ : MulAut G) {M : Subgroup G} (h : IsTypeI M) :
    IsTypeI (φ • M) :=
  ⟨h.some.conj φ⟩

/-- **Conjugate subgroups have the same type I status**: if `L` is type I and `conj g • L = M`,
then `M` is type I.  The Peterfalvi (13.17.b) input ruling out conjugacy of a type-`I` subgroup to
the type-II subgroups `S`, `T`. -/
theorem isTypeI_of_conj {L M : Subgroup G} (h : IsTypeI L) {g : G}
    (hconj : MulAut.conj g • L = M) : IsTypeI M :=
  hconj ▸ isTypeI_pointwise_smul (MulAut.conj g) h

end OddOrder.GroupTheory
