import OddOrder.Peterfalvi.S14_MaximalI.RhoConstancy

/-!
# Peterfalvi §14 — Frobenius structure: opening layer

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
-/

namespace OddOrder.Peterfalvi.S14
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ## (12.6)--(12.7): type-I Frobenius structure -/

/-- Carrier for Peterfalvi (12.7): a type-I maximal subgroup is Frobenius with
kernel `M_F`. -/
structure TypeIFrobeniusData (M : Subgroup G) where
  typeI : TypeIData M
  complement : Subgroup ↥M
  kernel_eq_MF : Prop
  kernel_eq_MF_holds : kernel_eq_MF
  frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
    ↥M (typeI.typeF.H.subgroupOf M) complement

/-- **Transporting a §4 Dade datum along an equality of its support set preserves the Dade isometry
`dadeIntegralCharacterMap`.**  The isometry's codomain `IntegralCharacterMap ↥L G` does not mention
the support `A`, so rewriting `A` to `A'` in the datum leaves the map unchanged (`subst` + `rfl`).
This lets the (6.8) `SibleyDadeHypothesis` (Dade datum on `sharpImage H`) carry *exactly* the (12.1)
isometry `hyp.tau` (Dade datum on `A(L)`) after the ambient identification `sharpImage H = A(L)` —
the map is an *arbitrary* linear extension off the supported lattice
(`dadeIntegralCharacterMap_apply_of_support`), so only the identical datum (transported), not a
re-construction via `of_isTISubset`, reproduces `hyp.tau`. -/
theorem hconj_transport_ambient {L : Subgroup G} [Fintype G] {A A' : Set G} (hEq : A = A')
    (dade : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : dade.HConjInvariant) :
    (hEq ▸ dade : OddOrder.Peterfalvi.S04.Hypothesis G A' L).HConjInvariant := by
  subst hEq; exact hconj

theorem dadeIntegralCharacterMap_transport_ambient {L : Subgroup G} [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {A A' : Set G} (hEq : A = A')
    (dade : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : dade.HConjInvariant)
    (hconj' : (hEq ▸ dade : OddOrder.Peterfalvi.S04.Hypothesis G A' L).HConjInvariant) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hEq ▸ dade)
        ((hEq ▸ dade).fullDadeIsometryData hconj')
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap dade
        (dade.fullDadeIsometryData hconj) := by
  subst hEq; rfl

/-- **The centralizer-support of `N^#` collapses to `N^#` for a Frobenius `L` with kernel `N`.**
The (12.1) type-I Dade support is `A(L) = centralizerSupport (N^#) L`; when `L` is a Frobenius group
with kernel `N` (`N.subgroupOf L`), the extra centralizer condition is vacuous — a `y` centralizing
a nontrivial `x ∈ N` lands in the kernel `N` (`IsFrobeniusGroup.centralizer_kernel_le`), so the
support is just `N^#`.  This is the **non-circular** upstream twin of the §16
`centralizerSupport_sharpSubgroup_eq_of_frobenius`: it takes the Frobenius structure as a hypothesis
(supplied for the (12.16) witness by (12.10) `witness_L_frobenius`) rather than routing through the
final (12.7), so it is available before the minimal-counterexample machinery. -/
theorem centralizerSupport_sharp_eq_of_frobenius [Finite G] {M N : Subgroup G} {C : Subgroup ↥M}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (N.subgroupOf M) C) (hNM : N ≤ M) :
    OddOrder.GroupTheory.centralizerSupport (OddOrder.GroupTheory.sharpSubgroup N) M
      = OddOrder.GroupTheory.sharpSubgroup N := by
  ext y
  simp only [OddOrder.GroupTheory.centralizerSupport, OddOrder.GroupTheory.sharpSubgroup,
    Set.mem_setOf_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyM, hy1, x, ⟨hxN, hx1⟩, hyx⟩
    have hxM : x ∈ M := hNM hxN
    have hxMsub : (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M := (Subgroup.mem_subgroupOf).mpr hxN
    have hx1' : (⟨x, hxM⟩ : ↥M) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hycomm : (⟨y, hyM⟩ : ↥M) ∈ Subgroup.centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyx ⊢
      exact Subtype.ext hyx
    have hyN : (⟨y, hyM⟩ : ↥M) ∈ N.subgroupOf M :=
      hfrob.centralizer_kernel_le _ hxMsub hx1' hycomm
    exact ⟨(Subgroup.mem_subgroupOf).mp hyN, hy1⟩
  · rintro ⟨hyN, hy1⟩
    refine ⟨hNM hyN, hy1, y, ⟨hyN, hy1⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]

/-- **Ambient match for the (6.8) Sibley setup**: the `H^#`-image `sharpImage (H.subgroupOf L)` of
the Fitting kernel (`H = L_F`), pushed back to `G`, is exactly the type-I Dade support
`A(L) = typeIA L`.  Here `A(L) = centralizerSupport (H^#) L` (`typeIA` def) collapses to `H^#` for
the **Frobenius** `L` (`centralizerSupport_sharp_eq_of_frobenius`, non-circular from `hfrob`), and
`(H.subgroupOf L).map L.subtype = H ⊓ L = H` (`subgroupOf_map_subtype`, `H ≤ L`) matches the two
`H^#` descriptions.  This is the ambient identification that lets the (6.8) `SibleyDadeHypothesis`
(Dade datum on `sharpImage H`) reuse the (12.1) datum `hyp.dadeData.dade` (on `A(L)`), preserving
the isometry `hyp.tau` exactly. -/
theorem sharpImage_H_subgroupOf_eq_typeIA [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L) = typeIA L hyp.typeI := by
  have hmap : (hyp.H.subgroupOf L).map L.subtype = hyp.typeI.typeF.H := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hyp.typeI.typeF.H_le
  rw [show typeIA L hyp.typeI
        = OddOrder.GroupTheory.centralizerSupport
          (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H) L from rfl,
    centralizerSupport_sharp_eq_of_frobenius (N := hyp.typeI.typeF.H) hfrob hyp.typeI.typeF.H_le]
  simp only [OddOrder.Peterfalvi.S08.sharpImage, OddOrder.GroupTheory.sharpSubgroup, hmap]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Structural input for Peterfalvi (12.6) — TI-kernel Frobenius case (6.8)(c1).**

For the (6.8) case-(c1) route, `L` is Frobenius **and** `H^#` is a TI-subset of `G`
(Peterfalvi (6.8)(a) requires *both*: being Frobenius is (c1), but the ambient TI-ness is a
separate hypothesis).  Under TI, the §4 Dade datum's local subgroups vanish
(`dade.H a = ⊥`), which is exactly the `SibleyDadeHypothesis.dade_H_eq_bot` field, so a
`SibleyTarget` is available.

**Note (2026-07-01, issue 2032):** the earlier `_hfrob`-only signature was *unsound* — the (12.16)
witness `L` is Frobenius but its `H^#` is **not** TI in `G` (Peterfalvi (12.10): "By (12.9), `H^#`
is
not a TI-subset of `G`"), so `dade_H_eq_bot` fails there.  The `_hTI` hypothesis restores soundness;
the witness (non-TI) is handled by the case-(b)/(c) routes of `frobenius_typeI_coherent`, not by
this
TI-only carrier.

**Construction (2026-07-14, carve-out issue 9077)**: kernel `H = (L_F).subgroupOf L`; the Frobenius
witness supplies the split/nontriviality fields, `L_F = maxNilpotentNormalHall` the nilpotency.  The
TI bound `N_G(H)` collapses to `L` through the (8.15) normalizer identification
`hyp.dadeData.normalizer_eq` (`N_G(A(L)) = L`) and `A(L) = H^#` for Frobenius `L`
(`typeIA_eq_sharp_of_frobenius`, `normalizer_sharpSubgroup`).  The §4 Dade datum is the (12.1)
`hyp.dadeData.dade` recoordinated along `sharpImage H = A(L)`
(`sharpImage_H_subgroupOf_eq_typeIA`), so the Sibley map *is* `hyp.tau` exactly
(`dadeIntegralCharacterMap_transport_ambient`), and its local subgroups vanish by the (2.3) reverse
direction (`H_eq_bot_of_isTISubset`).  The `hodd` hypothesis feeds `card_L_odd` (Peterfalvi works
throughout with odd-order `G`; the earlier `hodd`-less signature was statement-level unprovable —
counter-model `G = S₄`, `L = S₃` — cf. the `hG.odd`-fed `card_L_odd` of
`typeVSibleyDadeHypothesis`; faithfulness fix approved by issue 9077 HUB RULING #4′). -/
noncomputable def sibleyTarget_frobI [Fintype G] {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)] (hyp : Hypothesis L)
    (hodd : Odd (Nat.card G))
    (_hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C)
    (_hTI : OddOrder.GroupTheory.IsTISubset
      (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H)
      (Subgroup.normalizer (hyp.typeI.typeF.H : Set G))) :
    CoherenceWiring.SibleyTarget hyp.tau hyp.Sset hyp.A := by
  -- Reconcile the four instance binders with the scoped `FiniteInduce` instances baked into
  -- `hyp.tau`/`hyp.Sset`/`hyp.A` (all four classes are subsingletons; `Finite G` proofs are
  -- definitionally irrelevant), so the whole construction lives in one instance world.
  rename_i iFG iFL iIL iIG
  haveI hFin : Finite G := hyp.finiteG
  obtain rfl : iFG = OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype :=
    Subsingleton.elim _ _
  obtain rfl : iFL = OddOrder.Peterfalvi.S12.FiniteInduce.finiteSubFintype L :=
    Subsingleton.elim _ _
  obtain rfl : iIL = OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvC L :=
    Subsingleton.elim _ _
  obtain rfl : iIG = OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG :=
    Subsingleton.elim _ _
  -- The target lives in `Type`, so extract the Frobenius complement by choice.
  let C : Subgroup ↥L := _hfrob.choose
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C :=
    _hfrob.choose_spec
  -- Support-set identifications: `sharpImage ((L_F).subgroupOf L) = A(L) (= (L_F)^#)`.
  have hset : OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L)
      = typeIA L hyp.typeI := sharpImage_H_subgroupOf_eq_typeIA hyp hfrob
  have hEq : typeIA L hyp.typeI
      = OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L) := hset.symm
  -- `A(L) = (L_F)^#` for the Frobenius `L` (the non-circular upstream twin of
  -- `typeIA_eq_sharp_of_frobenius`, which is defined only later in this file).
  have hsharp : typeIA L hyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H :=
    centralizerSupport_sharp_eq_of_frobenius hfrob hyp.typeI.typeF.H_le
  -- The (6.8.a) TI in the `L`-relative form: the TI bound `N_G(H)` collapses to `L`
  -- through the (8.15) normalizer identification `N_G(A(L)) = L`.
  have hNeq : Subgroup.normalizer (hyp.typeI.typeF.H : Set G) = L := by
    rw [← OddOrder.Peterfalvi.S12.normalizer_sharpSubgroup, ← hsharp]
    exact hyp.dadeData.normalizer_eq
  have hTI_L : OddOrder.GroupTheory.IsTISubset
      (OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L)) L := by
    rw [hset, hsharp]
    exact _hTI.mono hNeq.le
  -- The (12.1) Dade datum recoordinated to the Sibley support: the *identical* datum
  -- transported along `hEq`, so the Dade isometry is preserved exactly.
  have hconj' : (hEq ▸ hyp.dadeData.dade :
      OddOrder.Peterfalvi.S04.Hypothesis G
        (OddOrder.Peterfalvi.S08.sharpImage (hyp.H.subgroupOf L)) L).HConjInvariant :=
    hconj_transport_ambient hEq hyp.dadeData.dade hyp.hconj
  have hoddL : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  refine
    { H := hyp.H.subgroupOf L
      invH := inferInstance
      sib :=
        { W1 := C
          H_ne_bot := hfrob.ne_bot_kernel
          H_normal := hfrob.isNormal
          H_nilpotent := ?_
          split := hfrob.isComplement
          W1_nontrivial := hfrob.ne_bot_complement
          card_L_odd := hoddL
          H_sharp_ti := hTI_L
          dade := hEq ▸ hyp.dadeData.dade
          hconj := hconj'
          dade_H_eq_bot := fun a =>
            OddOrder.Peterfalvi.S04.Hypothesis.H_eq_bot_of_isTISubset _ hTI_L a
          S := hyp.Sset
          S_eq := rfl
          cases := Or.inl hfrob }
      tau_eq :=
        dadeIntegralCharacterMap_transport_ambient hEq hyp.dadeData.dade hyp.hconj hconj'
      S_eq := rfl
      A0_eq := by rw [hset]; rfl }
  -- `H = L_F` is nilpotent: `maxNilpotentNormalHall` nilpotency transported to the
  -- `↥L`-coordinate along `subgroupOfEquivOfLe`.
  haveI : Group.IsNilpotent ↥(hyp.typeI.typeF.H) := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.H_le).symm

/-- **Lattice-relative `xFamily_inner`** — the (5.7) `X`-family orthonormality `⟨Xᵢ, Xⱼ⟩ = ⟨χᵢ, χⱼ⟩`
(`Xⱼ = β − τ(χ₀ − χⱼ)`) **without a global isometry**.  `S07.xFamily_inner` (S07:472) uses the
isometry only on the supported differences `χ₀ − χⱼ` (S07:487); this variant takes exactly that
lattice-relative fact `hdiff`, so it applies to the Feit–Thompson **Dade** map (which is *not* a
global `IsIntegralIsometry` — `dim CF(L) > dim CF(G)` — but *is* isometric on the `A(L)`-supported
differences).  Identical proof, sourcing the difference inner product from `hdiff`.  This is the one
place the (5.7) equal-degree coherence used the global isometry (issue 9001), so it is the
load-bearing
step for a Dade-compatible `frobenius_typeI_coherent_of_abelianKernel`. -/
theorem xFamily_inner_dade {L : Subgroup G} [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G} {n : ℕ} [NeZero n]
    (χ : Fin n → ClassFunction ↥L ℂ) (β : ClassFunction G ℂ)
    (hdiff : ∀ i j, ClassFunction.inner (τ (χ 0 - χ i)) (τ (χ 0 - χ j))
      = ClassFunction.inner (χ 0 - χ i) (χ 0 - χ j))
    (hββ : ClassFunction.inner β β = 1)
    (hB : ∀ j, ClassFunction.inner β (τ (χ 0 - χ j)) = 1 - ClassFunction.inner (χ 0) (χ j))
    (i j : Fin n) :
    ClassFunction.inner (β - τ (χ 0 - χ i)) (β - τ (χ 0 - χ j))
      = ClassFunction.inner (χ i) (χ j) := by
  have hχ00 : ClassFunction.inner (χ 0) (χ 0) = 1 := by
    have h := hB 0; rw [sub_self, map_zero, ClassFunction.inner_zero_right] at h
    linear_combination h
  have hai : ClassFunction.inner (τ (χ 0 - χ i)) β = 1 - ClassFunction.inner (χ i) (χ 0) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hB i, star_sub, star_one,
      ← OddOrder.RepresentationTheory.inner_conj_symm]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    hββ, hB j, hai, hdiff i j, ClassFunction.inner_sub_left,
    ClassFunction.inner_sub_right, ClassFunction.inner_sub_right, hχ00]
  ring

/-- **Peterfalvi (12.1) support `A(L) = H^#` from a Frobenius witness** — the
Frobenius-parameterized core of `typeIA_eq_sharp` (below), factored out so the (12.6) case-(b)
coherence assembly can cite it
with the `hfrob` it already has (the full `typeIA_eq_sharp` derives `hfrob` from `typeI_frobenius`,
which is defined later).  Since `L` is Frobenius with kernel `H`, the centralizer of any `x ∈ H^#`
lies in `H` (`IsFrobeniusGroup.centralizer_kernel_le`), so the `A(L)`-support (`centralizerSupport`
of `H^#`) is exactly `H^#`. -/
theorem Hypothesis.typeIA_eq_sharp_of_frobenius [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C) :
    OddOrder.GroupTheory.typeIA L hyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H := by
  change OddOrder.GroupTheory.centralizerSupport
      (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H) L
    = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H
  ext y
  simp only [OddOrder.GroupTheory.centralizerSupport, OddOrder.GroupTheory.sharpSubgroup,
    Set.mem_setOf_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyL, hy1, x, ⟨hxN, hx1⟩, hyx⟩
    have hxL : x ∈ L := hyp.typeI.typeF.H_le hxN
    have hxsub : (⟨x, hxL⟩ : ↥L) ∈ hyp.typeI.typeF.H.subgroupOf L :=
      (Subgroup.mem_subgroupOf).mpr hxN
    have hx1' : (⟨x, hxL⟩ : ↥L) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hycomm : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyx ⊢
      exact Subtype.ext hyx
    have hyN : (⟨y, hyL⟩ : ↥L) ∈ hyp.typeI.typeF.H.subgroupOf L :=
      hfrob.centralizer_kernel_le _ hxsub hx1' hycomm
    exact ⟨(Subgroup.mem_subgroupOf).mp hyN, hy1⟩
  · rintro ⟨hyN, hy1⟩
    refine ⟨hyp.typeI.typeF.H_le hyN, hy1, y, ⟨hyN, hy1⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` members are irreducible characters of `L`** — the crux of the (12.6)
case-(b) reduction: for a Frobenius `L` with kernel `H`, `Ind_H^L θ` (`θ ≠ 1`) is irreducible
(`isIrreducibleCharacter_induce_of_frobeniusGroup`).  This feeds the unit-norm, orthogonality, and
`ZIrr`-membership inputs of `coherent_of_constant_degree`. -/
theorem Sset_isIrreducibleCharacter [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    IsIrreducibleCharacter χ := by
  classical
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  exact isIrreducibleCharacter_induce_of_frobeniusGroup hfrob θ hθ_ne

/-- **A Frobenius `S`-member is its own constituent.**  In the Frobenius witness case `χ ∈ S` is
irreducible (`Sset_isIrreducibleCharacter`), so its `(12.2.a)` decomposition `χ = ∑_{S(χ)} φ` is a
single term: there is `φ ∈ data.constituents` with `↑φ = χ`.  Feeds the (12.5) orthogonality
`⟨ψ, coh.extension χ⟩ = 0` via `inner_psi_coherent_extension_eq_zero` (which is stated per
constituent). -/
theorem Sset_self_mem_constituents [Finite G] {L : Subgroup G} [Finite ↥L]
    [Invertible (Nat.card ↥L : ℂ)] (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) (data : CharacterDecompositionData hyp χ) :
    ∃ φ : IrreducibleCharacter ↥L, (φ : ClassFunction ↥L ℂ) = χ ∧ φ ∈ data.constituents := by
  classical
  haveI : Fintype ↥L := Fintype.ofFinite _
  haveI := hyp.finiteG
  have hirr : IsIrreducibleCharacter χ := Sset_isIrreducibleCharacter hyp hfrob hχ
  obtain ⟨φ₀, hφ₀⟩ := data.constituents_nonempty
  have hone : ClassFunction.inner (φ₀ : ClassFunction ↥L ℂ) χ = 1 := by
    conv_lhs => rw [data.decomp]
    rw [inner_sum_right, Finset.sum_eq_single φ₀]
    · rw [irreducibleCharacter_inner_eq_ite, if_pos rfl]
    · intro φ _ hφne; rw [irreducibleCharacter_inner_eq_ite, if_neg (Ne.symm hφne)]
    · intro h; exact absurd hφ₀ h
  refine ⟨φ₀, ?_, hφ₀⟩
  by_contra hne'
  have h0 : ClassFunction.inner (φ₀ : ClassFunction ↥L ℂ) χ = 0 := by
    have hite := irreducibleCharacter_inner_eq_ite φ₀ (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)
    rwa [if_neg (fun h => hne' (by rw [h]))] at hite
  rw [hone] at h0
  exact one_ne_zero h0

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (12.5) orthogonality provision** (Frobenius case): `ψ ⊥ R(χ)` for all `χ ∈ S` gives
`⟨ψ, coh.extension χ⟩ = 0` for each `χ ∈ S`.  The `S`-member `χ` is its own constituent
(`Sset_self_mem_constituents`), so `inner_psi_coherent_extension_eq_zero` applies directly.  This is
the `horth1`/`horth2` input of the `θ`-coefficient equality
`chiRhoCF_restrict_inner_eq_of_equal_degree` in the (12.5) `DpsiH` wiring. -/
theorem Sset_inner_coherent_extension_eq_zero {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) {psi : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner psi α = 0)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    ClassFunction.inner psi (coh.extension χ) = 0 := by
  obtain ⟨φ, hφeq, hφmem⟩ := Sset_self_mem_constituents hyp hfrob hχ (data χ hχ)
  rw [← hφeq]
  exact inner_psi_coherent_extension_eq_zero hyp coh (data χ hχ) hφmem
    (by rw [hφeq]; exact hχ) (horth χ hχ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5)** (Frobenius witness case): a class function `ψ` orthogonal to every type-I
family `R(χ)` has `ρ`-image `ψ^ρ = chiRhoCF ψ` **constant on `H − H'`**.  Reduces to the generic
`DpsiH` core `constant_off_normal_of_inner_block_const` at ambient `↥(H.subgroupOf L)` with
`H_core = commutator`: `hcoeff` from the `θ`-coefficient equality
`chiRhoCF_restrict_inner_eq_of_equal_degree` (with orthogonality from
`Sset_inner_coherent_extension_eq_zero` and equal degree from
`commutator_induce_constituents_apply_one_eq`), `hmult` from
`inner_induce_constituent_eq_of_apply_one_eq`, and the `x ∉ commutator ↔ h ∉ H'` translation from
`mem_commutator_subgroupOf_iff`. -/
theorem rho_constant_on_H_minus_Hprime {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1}) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) {psi : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner psi α = 0) :
    ∀ h1 : G, ∀ (hh1 : h1 ∈ hyp.H), h1 ∉ hyp.Hprime → ∀ h2 : G, ∀ (hh2 : h2 ∈ hyp.H),
      h2 ∉ hyp.Hprime →
      (hyp.toHypothesis71.chiRhoCF psi) ⟨h1, hyp.typeI.typeF.H_le hh1⟩
        = (hyp.toHypothesis71.chiRhoCF psi) ⟨h2, hyp.typeI.typeF.H_le hh2⟩ := by
  haveI := hyp.finiteG
  classical
  intro h1 hh1 hh1' h2 hh2 hh2'
  have hHL : hyp.typeI.typeF.H ≤ L := hyp.typeI.typeF.H_le
  haveI : Fintype (IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L)) := Fintype.ofFinite _
  set g : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ :=
    ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L) (hyp.toHypothesis71.chiRhoCF psi)
    with hg
  set x : ↥((hyp.typeI.typeF.H).subgroupOf L) :=
    ⟨⟨h1, hHL hh1⟩, Subgroup.mem_subgroupOf.mpr hh1⟩ with hx_def
  set y : ↥((hyp.typeI.typeF.H).subgroupOf L) :=
    ⟨⟨h2, hHL hh2⟩, Subgroup.mem_subgroupOf.mpr hh2⟩ with hy_def
  have hx : x ∉ commutator ↥((hyp.typeI.typeF.H).subgroupOf L) := fun hxc =>
    hh1' ((mem_commutator_subgroupOf_iff hHL x).mp hxc)
  have hy : y ∉ commutator ↥((hyp.typeI.typeF.H).subgroupOf L) := fun hyc =>
    hh2' ((mem_commutator_subgroupOf_iff hHL y).mp hyc)
  have hgx : g x = (hyp.toHypothesis71.chiRhoCF psi) ⟨h1, hHL hh1⟩ := by
    rw [hg, ClassFunction.restrict_apply]
  have hgy : g y = (hyp.toHypothesis71.chiRhoCF psi) ⟨h2, hHL hh2⟩ := by
    rw [hg, ClassFunction.restrict_apply]
  rw [← hgx, ← hgy]
  refine constant_off_normal_of_inner_block_const g ?_ ?_ hx hy
  · intro θ₁ θ₂ ρ hne1 hne2 hlo1 hlo2
    have hdeg := commutator_induce_constituents_apply_one_eq ρ θ₁ θ₂ hlo1 hlo2
    have hχ₁mem : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ₁ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∈ hyp.Sset := by
      simp only [Hypothesis.Sset, Set.mem_setOf_eq]; exact ⟨θ₁, hne1, rfl⟩
    have hχ₂mem : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ₂ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∈ hyp.Sset := by
      simp only [Hypothesis.Sset, Set.mem_setOf_eq]; exact ⟨θ₂, hne2, rfl⟩
    have hχ₁mem' := hχ₁mem
    have hdegχ : (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ₁ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) (1 : ↥L)
        = (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ₂ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) (1 : ↥L) := by
      rw [ClassFunction.induce_apply_one, ClassFunction.induce_apply_one, hdeg]
    have horth1 := Sset_inner_coherent_extension_eq_zero hyp coh hfrob data horth hχ₁mem
    have horth2 := Sset_inner_coherent_extension_eq_zero hyp coh hfrob data horth hχ₂mem
    have hθc := chiRhoCF_restrict_inner_eq_of_equal_degree hyp coh hχ₁mem hχ₂mem hdegχ hAH
      horth1 horth2 rfl rfl
    have hfin : ClassFunction.inner (θ₁ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) g
        = ClassFunction.inner (θ₂ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) g := by
      rw [hg]; exact hθc
    rw [inner_conj_symm (θ₁ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) g,
      inner_conj_symm (θ₂ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) g, hfin]
  · intro θ₁ θ₂ ρ hlo1 hlo2
    exact inner_induce_constituent_eq_of_apply_one_eq hlo1 hlo2
      (commutator_induce_constituents_apply_one_eq ρ θ₁ θ₂ hlo1 hlo2)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` has no real characters** ((5.2) input for case (b)/(12.6)).  Each
member is a Frobenius-induced irreducible (`frobenius_induce_char_singleton`), non-real by the odd
order of `L` (`not_isReal_of_ne_trivial_of_odd_card'`). -/
theorem Sset_hasNoRealCharacters [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.Sset := by
  classical
  intro χ hχ
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  obtain ⟨ξ, hξcoe, hξreal, _⟩ := frobenius_induce_char_singleton hodd hfrob θ hθ_ne
  rw [← hξcoe]; exact hξreal

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` is pairwise orthogonal** ((5.2) input for case (b)/(12.6)).  Each
member is an irreducible character of `L` (Frobenius induction), so two distinct members are
orthogonal by row orthogonality (`irreducibleCharacter_inner_eq_ite`). -/
theorem Sset_pairwiseOrthogonal [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C) :
    OddOrder.Peterfalvi.S03.PairwiseOrthogonal hyp.Sset := by
  classical
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  intro χ ψ hχ hψ hne
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hχ hψ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  obtain ⟨θ', hθ'_ne, rfl⟩ := hψ
  obtain ⟨ξ, hξcoe, _, _⟩ := frobenius_induce_char_singleton hodd hfrob θ hθ_ne
  obtain ⟨ξ', hξ'coe, _, _⟩ := frobenius_induce_char_singleton hodd hfrob θ' hθ'_ne
  rw [← hξcoe, ← hξ'coe, irreducibleCharacter_inner_eq_ite, if_neg]
  intro h
  exact hne (by rw [← hξcoe, ← hξ'coe, h])

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` members are unit-norm** (the `hirr` input of (5.7)/(12.6) case (b)).
Each `Ind_H^L θ` (`θ ≠ 1`) is a Frobenius-induced irreducible, so `‖Ind_H^L θ‖² = 1`
(`inner_self_induce_eq_one_of_frobeniusGroup`, the inertia-`H` norm computation). -/
theorem Sset_inner_self_eq_one [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    ClassFunction.inner χ χ = 1 := by
  classical
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  exact inner_self_induce_eq_one_of_frobeniusGroup hfrob θ hθ_ne

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` members share the degree `[L:H]`** (the `hconst`/`hdeg0` input of
(5.7)/(12.6) case (b)).  With `H = L_F` abelian (Def (8.3) case (b)), every `θ ∈ Irr H` is linear
(`θ(1) = 1`, `IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative`; commutativity transfers
to `H.subgroupOf L` by the `subgroupOf_isMulCommutative` instance), so
`(Ind_H^L θ)(1) = [L:H]·θ(1) = [L:H]` (`induce_apply_one`). -/
theorem Sset_apply_one_eq_index [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    (χ : ↥L → ℂ) 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  classical
  haveI : IsMulCommutative ↥hyp.typeI.typeF.H := hab
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  rw [ClassFunction.induce_apply_one, θ.isIrreducible.apply_one_eq_one_of_isMulCommutative, mul_one]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`S(H′)` is constant-degree** (the (5.7) input for `hcoh` of the (6.5.c) engine, without
assuming `H` abelian).  Every member of `S(⁅K,K⁆)` (`K = (L_F).subgroupOf L`) is `Ind_K^L θ` with
`⁅K,K⁆ ⊆ Ker θ`; then `θ` factors through the abelian `K/⁅K,K⁆`, so `θ(1) = 1`
(`apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient`) and `Ind θ (1) = |L:K|`.
This is Peterfalvi's `η_j(1) = |W₁|` for the `Y = S(H′)` family — the subfamily replacement for the
case-(b) `Sset_apply_one_eq_index` (which needs all of `H` abelian). -/
theorem SsubFiltration_commutator_apply_one_eq_index [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    (χ : ↥L → ℂ) 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  classical
  simp only [Hypothesis.SsubFiltration, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, _hθ_ne, hker, rfl⟩ := hχ
  have hθ1 : (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) 1 = 1 := by
    haveI : IsMulCommutative (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
        commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) :=
      inferInstanceAs (IsMulCommutative (Abelianization ↥((hyp.typeI.typeF.H).subgroupOf L)))
    refine
      apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
      (N := commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) θ ?_
    rw [← OddOrder.Peterfalvi.S08.commutator_subgroupOf_self ((hyp.typeI.typeF.H).subgroupOf L)]
    exact hker
  rw [ClassFunction.induce_apply_one, hθ1, mul_one]

open OddOrder.Peterfalvi.S09.Cert in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness member differences are `A(L)`-supported** (the `hsuppdiff` input of (5.7)/(12.6) case
(b), and the support that lets the Dade isometry apply — `tau_isometry_diff`).  Two members
`a, b ∈ S = {Ind_H^L θ}` both vanish off `H` (`Sset_vanishes_off_H`) and share the degree `[L:H]`
(`Sset_apply_one_eq_index`), so `a − b` vanishes off `H` and at `1`, i.e. is supported in
`A(L) = H^# = supportInSubgroup (H \ {1}) L`. -/
theorem Sset_diff_supported [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b : ClassFunction ↥L ℂ} (ha : a ∈ hyp.Sset) (hb : b ∈ hyp.Sset) :
    (a - b).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  intro x hx
  have hx0 : (a - b) x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply] at hx0
  have hxH : (x : G) ∈ hyp.H := by
    by_contra h
    exact hx0 (by rw [Sset_vanishes_off_H hyp ha h, Sset_vanishes_off_H hyp hb h, sub_zero])
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hx0 (by
      rw [Sset_apply_one_eq_index hyp hab ha, Sset_apply_one_eq_index hyp hab hb, sub_self])
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr
    ⟨Subgroup.mem_subgroupOf.mpr hxH, hx1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **A member's conjugate-difference `χ̄ − χ` is `A(L)`-supported** (any `χ ∈ S`, no
constant-degree needed) — the per-member support field of the (5.6) family enumeration (h56).  Off
`H` both `χ` and `χ̄` vanish (`Sset_vanishes_off_H`); at `1`, `χ̄(1) = χ(1)` because `χ(1)` is a
(real) natural degree
(`χ` irreducible), so `χ̄ − χ` is supported on `H^# = A(L)`. -/
theorem Sset_conjDiff_supported [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  intro x hx
  have hx0 : (χ.conj - χ) x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply, ClassFunction.conj_apply] at hx0
  have hxH : (x : G) ∈ hyp.H := by
    by_contra h
    apply hx0
    rw [Sset_vanishes_off_H hyp hχ h]; simp
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hx0
    obtain ⟨n, -, hn1, -⟩ :=
      (Sset_isIrreducibleCharacter hyp hfrob hχ).exists_natDegree_charValue_one_dvd_card
    rw [hn1, star_natCast, sub_self]
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr
    ⟨Subgroup.mem_subgroupOf.mpr hxH, hx1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Orthonormal enumeration of a coherent `S₁ ⊆ S`** — the witness analogue of the Sibley
`exists_sMemberOrthonormalFamily`, the family-enumeration input of the (5.6) break bound (h56).
Members of `S₁` are irreducible (`Sset_isIrreducibleCharacter`), so `exists_finEnum_irreducible`
lists them as `χmem : Fin k → Irr L`; the per-member fields are the witness `Sset` facts (no-real,
`Sset_conjDiff_supported`, pairwise/self orthonormality), `hS₁conj` supplies `χ̄ ∈ S₁`. -/
theorem Sset_exists_orthonormalFamily [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ)) ∧
      (∀ j, ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁) ∧
      (∀ j, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0) ∧
      (∀ i j, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ) = if i = j then (1 : ℂ) else 0) := by
  have hS₁irr : ∀ φ ∈ S₁, IsIrreducibleCharacter φ :=
    fun φ hφ => Sset_isIrreducibleCharacter hyp hfrob (hS₁sub hφ)
  obtain ⟨k, χmem, hχinj, hrange⟩ :=
    OddOrder.Peterfalvi.S08.exists_finEnum_irreducible hS₁fin hS₁irr
  have hmemS1 : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j; rw [← hrange]; exact Set.mem_range_self j
  refine ⟨k, χmem, hχinj, hrange, ?_, ?_, hmemS1, ?_, ?_, ?_⟩
  · intro j
    exact Sset_hasNoRealCharacters hyp hodd hfrob (hS₁sub (hmemS1 j))
  · intro j
    exact Sset_conjDiff_supported hyp hfrob hAH (hS₁sub (hmemS1 j))
  · intro j
    exact hS₁conj (hmemS1 j)
  · intro j
    have hχS := hS₁sub (hmemS1 j)
    have hne : (χmem j : ClassFunction ↥L ℂ) ≠ (χmem j : ClassFunction ↥L ℂ).conj :=
      fun h => (Sset_hasNoRealCharacters hyp hodd hfrob hχS) h.symm
    exact Sset_pairwiseOrthogonal hyp hodd hfrob hχS (Sset_closedUnderConjugate hyp hχS) hne
  · intro i j
    rw [OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite (χmem i) (χmem j)]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · rw [if_neg (fun he => h (hχinj he)), if_neg h]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **A member's degree is `d·|L:K|`** (`d = θ(1)` the source degree) — the integer degree-ratio
input of the (5.6) degree data (h56).  `χ = Ind_K^L θ` has `χ(1) = |L:K|·θ(1)` (`induce_apply_one`),
`θ(1)` a positive natural (`θ` irreducible). -/
theorem Sset_charValue_one_eq_mul_index [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    ∃ d : ℕ, 0 < d ∧
      (χ : ↥L → ℂ) 1 = (d : ℂ) * (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  classical
  simp only [Hypothesis.Sset, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, -, rfl⟩ := hχ
  obtain ⟨d, hd0, hd1, -⟩ := θ.isIrreducible.exists_natDegree_charValue_one_dvd_card
  refine ⟨d, hd0, ?_⟩
  rw [ClassFunction.induce_apply_one, hd1]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **A scaled difference `χ − m·χ′` is `A(L)`-supported** when `χ(1) = m·χ′(1)` (any `χ, χ′ ∈ S`) —
the per-member scaled-difference support of the (5.6) degree data (h56).  Off `H` both vanish
(`Sset_vanishes_off_H`); at `1` the degree relation makes it vanish; so it is supported on
`H^# = A(L)`. -/
theorem Sset_scaledDiff_supported [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (_hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) (hχ' : χ' ∈ hyp.Sset) {m : ℕ}
    (hdeg : (χ : ↥L → ℂ) 1 = (m : ℂ) * (χ' : ↥L → ℂ) 1) :
    (χ - m • χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  rw [show (m • χ' : ClassFunction ↥L ℂ) = (m : ℂ) • χ' from
    (Nat.cast_smul_eq_nsmul ℂ m χ').symm]
  intro x hx
  have hx0 : (χ - (m : ℂ) • χ') x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply, ClassFunction.smul_apply] at hx0
  have hxH : (x : G) ∈ hyp.H := by
    by_contra h
    apply hx0
    rw [Sset_vanishes_off_H hyp hχ h, Sset_vanishes_off_H hyp hχ' h]; ring
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hx0
    rw [hdeg]; ring
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr
    ⟨Subgroup.mem_subgroupOf.mpr hxH, hx1⟩

/-- **Degree data for an enumerated `S`-family** — the witness analogue of the Sibley
`exists_sMemberDegreeData`, the integer-degree-ratio input of the (5.6) break bound (h56).  Against
a minimal-degree anchor `χmem i₁` of degree `|L:K|`, each member has an integer ratio
`deg j = χmem j(1)/|L:K|` (`Sset_charValue_one_eq_mul_index`), `deg i₁ = 1`, and the scaled
difference `χmem j − deg j·χmem i₁` is `A(L)`-supported (`Sset_scaledDiff_supported`). -/
theorem Sset_exists_degreeData [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L} {i₁ : Fin k}
    (hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Sset)
    (hanchordeg : (χmem i₁ : ClassFunction ↥L ℂ) 1 =
      (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ)) :
    ∃ deg : Fin k → ℕ, deg i₁ = 1 ∧ (∀ j, 0 < deg j) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1) ∧
      (∀ j, ((χmem j : ClassFunction ↥L ℂ) - deg j • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L) := by
  choose deg hdeg_pos hdeg_eq using fun j => Sset_charValue_one_eq_mul_index hyp (hmemS j)
  have hdeg_eq' : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 =
      (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 := fun j => by
    rw [hdeg_eq j, hanchordeg]
  refine ⟨deg, ?_, hdeg_pos, hdeg_eq', fun j =>
    Sset_scaledDiff_supported hyp hfrob hAH (hmemS j) (hmemS i₁) (hdeg_eq' j)⟩
  have h := hdeg_eq i₁
  rw [hanchordeg] at h
  have hidx_ne : (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have hdeg1 : (deg i₁ : ℂ) = 1 := mul_right_cancel₀ hidx_ne (by rw [one_mul]; exact h.symm)
  exact_mod_cast hdeg1



end OddOrder.Peterfalvi.S14
