import OddOrder.Peterfalvi.S14_MaximalI.RhoConstancy

/-!
# Peterfalvi (12.6)-(12.7) — type-I Frobenius structure

Split from the former monolithic `OddOrder.Peterfalvi.S14_MaximalI` (directory split, issue 0103).
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
witness `L` is Frobenius but its `H^#` is **not** TI in `G` (Peterfalvi (12.10): "By (12.9), `H^#` is
not a TI-subset of `G`"), so `dade_H_eq_bot` fails there.  The `_hTI` hypothesis restores soundness;
the witness (non-TI) is handled by the case-(b)/(c) routes of `frobenius_typeI_coherent`, not by this
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
place the (5.7) equal-degree coherence used the global isometry (issue 9001), so it is the load-bearing
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

/-- **Peterfalvi (12.1) support `A(L) = H^#` from a Frobenius witness** — the Frobenius-parameterized
core of `typeIA_eq_sharp` (below), factored out so the (12.6) case-(b) coherence assembly can cite it
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
theorem Sset_isIrreducibleCharacter [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
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
theorem Sset_self_mem_constituents [Finite G] {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card ↥L : ℂ)] (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) (data : CharacterDecompositionData hyp χ) :
    ∃ φ : IrreducibleCharacter ↥L, (φ : ClassFunction ↥L ℂ) = χ ∧ φ ∈ data.constituents := by
  classical
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
    refine OddOrder.RepresentationTheory.apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
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
/-- **A member's conjugate-difference `χ̄ − χ` is `A(L)`-supported** (any `χ ∈ S`, no constant-degree
needed) — the per-member support field of the (5.6) family enumeration (h56).  Off `H` both `χ` and
`χ̄` vanish (`Sset_vanishes_off_H`); at `1`, `χ̄(1) = χ(1)` because `χ(1)` is a (real) natural degree
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
`exists_sMemberDegreeData`, the integer-degree-ratio input of the (5.6) break bound (h56).  Against a
minimal-degree anchor `χmem i₁` of degree `|L:K|`, each member has an integer ratio
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

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Break-pair fields for `{ψ, ψ̄}`** — the witness analogue of the Sibley `sBreakPair_fields`, the
per-`ψ` inputs the (5.6) bound `coherentDegreeSumBound_of_not_coherent` consumes (in its argument
order): non-realness, conjugate-difference support, the `{ψ, ψ̄}` orthonormality, and the
orthogonality of `ψ`, `ψ̄` to every member of `S₁` (distinct irreducibles, since `ψ, ψ̄ ∉ S₁`). -/
theorem Sset_breakPair_fields [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.Sset)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁) :
    ¬ ClassFunction.IsReal ψ ∧
    (ψ.conj - ψ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∧
    ClassFunction.inner ψ ψ = 1 ∧
    ClassFunction.inner ψ.conj ψ.conj = 1 ∧
    ClassFunction.inner ψ ψ.conj = 0 ∧
    ClassFunction.inner ψ.conj ψ = 0 ∧
    (∀ x ∈ S₁, ClassFunction.inner ψ x = 0) ∧
    (∀ x ∈ S₁, ClassFunction.inner ψ.conj x = 0) := by
  have hψconjS := Sset_closedUnderConjugate hyp hψS
  have hne : ψ ≠ ψ.conj := fun h => (Sset_hasNoRealCharacters hyp hodd hfrob hψS) h.symm
  refine ⟨Sset_hasNoRealCharacters hyp hodd hfrob hψS,
    Sset_conjDiff_supported hyp hfrob hAH hψS,
    Sset_inner_self_eq_one hyp hfrob hψS,
    Sset_inner_self_eq_one hyp hfrob hψconjS,
    Sset_pairwiseOrthogonal hyp hodd hfrob hψS hψconjS hne,
    Sset_pairwiseOrthogonal hyp hodd hfrob hψconjS hψS (fun h => hne h.symm), ?_, ?_⟩
  · intro x hx
    have hxne : ψ ≠ x := by rintro rfl; exact hψnotS1 hx
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      ⟨ψ, Sset_isIrreducibleCharacter hyp hfrob hψS⟩
      ⟨x, Sset_isIrreducibleCharacter hyp hfrob (hS₁sub hx)⟩
    rwa [if_neg (fun he => hxne
      (congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) he))] at hite
  · intro x hx
    have hxne : ψ.conj ≠ x := by rintro rfl; exact hψcnotS1 hx
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      ⟨ψ.conj, Sset_isIrreducibleCharacter hyp hfrob hψconjS⟩
      ⟨x, Sset_isIrreducibleCharacter hyp hfrob (hS₁sub hx)⟩
    rwa [if_neg (fun he => hxne
      (congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) he))] at hite

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (6.2) member-family degree-sum bound over the witness `τ`** — the witness analogue
of the Sibley `sMember_degreeSumBound_of_not_coherent`, feeding the (5.6) core
`coherentDegreeSumBound_of_not_coherent` (over `hyp.dadeData.dade`, the same Dade datum as
`hyp.tau`).  Assembled from the six witness member-family helpers + the abstract §7 generation
bridges.  If `S₁` (coherent, containing a degree-`|L:K|` anchor `χ₁`) breaks against `{ψ, ψ̄}`, then
`∑ⱼ degⱼ² ≤ 2a` where `χmemⱼ(1) = degⱼ·χ₁(1)`, `ψ(1) = a·χ₁(1)`. -/
theorem Sset_degreeSumBound_of_not_coherent [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.Sset) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj}) hyp.A)) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L) (deg : Fin k → ℕ) (a : ℕ),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (deg j : ℂ) * χ₁ 1) ∧
      ψ 1 = (a : ℂ) * χ₁ 1 ∧
      ∑ j : Fin k, ((deg j : ℝ)) ^ 2 ≤ 2 * (a : ℝ) := by
  classical
  obtain ⟨k, χmem, hχinj, hrange, hmemreal, hmemdiffsupp, hmemS1, hmembarS1, hmemconjortho,
      hmemortho⟩ := Sset_exists_orthonormalFamily hyp hodd hfrob hAH hS₁sub hS₁conj hS₁fin
  have hχ₁range : χ₁ ∈ Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) := by
    rw [hrange]; exact hχ₁S₁
  obtain ⟨i₁, hi₁eq0⟩ := hχ₁range
  have hi₁eq : (χmem i₁ : ClassFunction ↥L ℂ) = χ₁ := hi₁eq0
  have hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Sset := fun j => hS₁sub (hmemS1 j)
  have hanchordeg : (χmem i₁ : ClassFunction ↥L ℂ) 1 =
      (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by rw [hi₁eq]; exact hχ₁deg
  obtain ⟨deg, hdeg_i₁, _hdeg_pos, hdeg_eq, hmemdegdiffsupp⟩ :=
    Sset_exists_degreeData hyp hfrob hAH hmemS hanchordeg
  obtain ⟨hrealψ, hdiffsuppψ, hψψ, hψbarψbar, hψψbar, hψbarψ, hψ_S1, hψbar_S1⟩ :=
    Sset_breakPair_fields hyp hodd hfrob hAH hψS hS₁sub hψnotS1 hψcnotS1
  obtain ⟨a, _ha_pos, hψratio0⟩ := Sset_charValue_one_eq_mul_index hyp hψS
  have hψratio : ψ 1 = (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 := by rw [hψratio0, ← hanchordeg]
  have hdiffasuppψ : (ψ - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L :=
    Sset_scaledDiff_supported hyp hfrob hAH hψS (hmemS i₁) hψratio
  have htau1ψ : hyp.tau (ψ - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hyp.hconj hdiffasuppψ
      (Submodule.sub_mem _ (IrreducibleCharacter.mem_ZIrr ⟨ψ, hψirr⟩)
        (nsmul_mem (IrreducibleCharacter.mem_ZIrr (χmem i₁)) a))
  have hcover : ∀ x ∈ S₁, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧
      (χmem j : ClassFunction ↥L ℂ) = x := by
    intro x hx; rw [← hrange] at hx; obtain ⟨j, hj⟩ := hx; exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen := OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
    (s := (Finset.univ : Finset (Fin k))) (χmem := fun j => (χmem j : ClassFunction ↥L ℂ))
    (deg := deg) (i₁ := i₁) hcover (Finset.mem_univ i₁) (fun j _ => hmemS1 j)
    (fun j _ => hmemdegdiffsupp j)
  have hbar1 : ψ.conj 1 = ψ 1 := by
    rw [ClassFunction.conj_apply]
    obtain ⟨n, -, hn1, -⟩ := hψirr.exists_natDegree_charValue_one_dvd_card
    rw [hn1, star_natCast]
  have hchi1_ne : (χmem i₁ : ClassFunction ↥L ℂ) 1 ≠ 0 := by
    rw [hanchordeg]; exact Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L :=
    one_not_mem_supportInSubgroup_sharp hyp.typeI.typeF.H hAH
  have hgen := OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
    (χ := ψ) (chibar := ψ.conj) (chi1 := (χmem i₁ : ClassFunction ↥L ℂ)) (a := a)
    hSgen hψratio hbar1 hchi1_ne h1A
  refine ⟨k, χmem, deg, a, hχinj, hrange, fun j => by rw [hdeg_eq j, hi₁eq],
    by rw [hψratio, hi₁eq], ?_⟩
  have hbound := OddOrder.Peterfalvi.S08.coherentDegreeSumBound_of_not_coherent
    hyp.dadeData.dade hyp.hconj hS₁coh ⟨ψ, hψirr⟩ hrealψ hdiffsuppψ hψψ hψbarψbar hψψbar hψbarψ
    hψ_S1 hψbar_S1 (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁)
    (fun j _ => hmemreal j) (fun j _ => hmemdiffsupp j) (fun j _ => hmemdegdiffsupp j)
    (fun j _ => hmemS1 j) (fun j _ => hmembarS1 j) (fun j _ => hmemconjortho j)
    (fun i _ j _ => by rw [hmemortho i j]; rcases eq_or_ne i j with h | h <;> simp [h])
    hdiffasuppψ htau1ψ hdeg_i₁ hSgen hgen hnc
  simpa using hbound

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (6.2) member-family degree-square bound** (real form, witness `τ`) — rescales
`Sset_degreeSumBound_of_not_coherent`'s `∑ⱼ degⱼ² ≤ 2a` by the anchor degree `χ₁(1)` into the
character-degree-square sum `∑ⱼ (χⱼ(1).re)² ≤ 2·ψ(1).re·χ₁(1).re`.  Mirror of the Sibley
`sMember_degreeSqReBound_of_not_coherent`. -/
theorem Sset_degreeSqReBound_of_not_coherent [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.Sset) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj}) hyp.A)) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁) ∧
      ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 ≤ 2 * (ψ 1).re * (χ₁ 1).re := by
  obtain ⟨k, χmem, deg, a, hχinj, hrange, hdeg_eq, hψ_eq, hbound⟩ :=
    Sset_degreeSumBound_of_not_coherent hyp hodd hfrob hAH hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁
      hχ₁deg hψS hψirr hψnotS1 hψcnotS1 hnc
  have hmemS1 : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j; rw [← hrange]; exact ⟨j, rfl⟩
  refine ⟨k, χmem, hχinj, hrange, hmemS1, ?_⟩
  have hdegre : ∀ j, ((χmem j : ClassFunction ↥L ℂ) 1).re = (deg j : ℝ) * (χ₁ 1).re := by
    intro j; rw [hdeg_eq j, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
  have hψre : (ψ 1).re = (a : ℝ) * (χ₁ 1).re := by
    rw [hψ_eq, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
  have hre_nonneg : (0 : ℝ) ≤ (χ₁ 1).re ^ 2 := sq_nonneg _
  calc ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2
      = ∑ j : Fin k, ((deg j : ℝ) * (χ₁ 1).re) ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hdegre j]
    _ = (χ₁ 1).re ^ 2 * ∑ j : Fin k, (deg j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
    _ ≤ (χ₁ 1).re ^ 2 * (2 * (a : ℝ)) := mul_le_mul_of_nonneg_left hbound hre_nonneg
    _ = 2 * ((a : ℝ) * (χ₁ 1).re) * (χ₁ 1).re := by ring
    _ = 2 * (ψ 1).re * (χ₁ 1).re := by rw [hψre]

/-- **The witness kernel `K = (L_F).subgroupOf L` is normal in `↥L`** — `L_F = maxNilpotentNormalHall L`
whose `subgroupOf L` is normal (`maxNilpotentNormalHall_subgroupOf_normal`).  Needed by the (6.2) B2
degree-sum identity and the (6.5) engine's `hHnorm`. -/
theorem typeF_H_subgroupOf_normal [Finite G] {L : Subgroup G} (hyp : Hypothesis L) :
    ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
  rw [hyp.typeI.typeF.H_eq]
  exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open scoped Classical in
/-- **Peterfalvi (6.2) B2 — the `S(A)` degree-square identity** (witness form).  Mirror of the Sibley
`sum_re_sq_induce_kernelFilter_eq`: over the witness kernel `K = (L_F).subgroupOf L`, the filtered
induced family `{Ind_K^L θ | A ⊆ Ker θ, θ ≠ 1}` has degree-square sum `|L:K|·(|K:A| − 1)`, via the
abstract B2 `sum_div_normSq_induce_kernelFilter_eq` and that each member is irreducible (`‖·‖² = 1`,
`χ(1)` a real natural). -/
theorem Sset_sum_re_sq_induce_kernelFilter_eq [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    {A : Subgroup ↥L} [A.Normal] :
    ∑ χ ∈ (Finset.univ.filter
        (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (↑(A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
              Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
            OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))).image
        (fun θ => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction),
        ((χ 1).re) ^ 2
      = (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
        ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
          A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1) := by
  haveI := hyp.finiteG
  haveI : ((hyp.typeI.typeF.H).subgroupOf L).Normal := typeF_H_subgroupOf_normal hyp
  have hB2 := OddOrder.Peterfalvi.S08.sum_div_normSq_induce_kernelFilter_eq (G := ↥L)
    (H := (hyp.typeI.typeF.H).subgroupOf L) (A := A)
  have hsummand : ∀ χ ∈ (Finset.univ.filter
      (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
        (↑(A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
            Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))).image
      (fun θ => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction),
      χ 1 ^ 2 / ClassFunction.inner χ χ = ((((χ 1).re) ^ 2 : ℝ) : ℂ) := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    have hθne : θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) :=
      (Finset.mem_filter.mp hθ).2.2
    have hχS : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∈ hyp.Sset := by
      simp only [Hypothesis.Sset, Set.mem_setOf_eq]; exact ⟨θ, hθne, rfl⟩
    have hirr := Sset_isIrreducibleCharacter hyp hfrob hχS
    have hinner : ClassFunction.inner
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ))
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) = 1 := by
      simpa using OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
        (⟨_, hirr⟩ : IrreducibleCharacter ↥L) ⟨_, hirr⟩
    obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
    rw [hinner, div_one, hn1, Complex.natCast_re]; push_cast; ring
  have key : ((∑ χ ∈ (Finset.univ.filter
        (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (↑(A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
              Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
            OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))).image
        (fun θ => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction),
        ((χ 1).re) ^ 2 : ℝ) : ℂ)
      = (((((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
        ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
          A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1)) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hsummand χ hχ).symm), hB2]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open scoped Classical in
/-- **Peterfalvi (6.2) per-step index bound** (witness form) — if `S(A) ⊆ S₁` (coherent, with a
degree-`|L:K|` anchor `χ₁`) breaks against `{ψ, ψ̄}`, then `|K:A| − 1 ≤ 2·ψ(1).re`.  The `S(A)`
degree-square sum `|L:K|·(|K:A|−1)` (B2, `Sset_sum_re_sq_induce_kernelFilter_eq`) is bounded by the
full enumerated `S₁`-family sum, which the (5.6) bound `Sset_degreeSqReBound_of_not_coherent` caps by
`2·ψ(1).re·χ₁(1).re`; dividing by `χ₁(1).re = |L:K|`.  Mirror of `sMember_index_le_two_psi`. -/
theorem Sset_index_le_two_psi [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {A : Subgroup ↥L} [A.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hSA_S1 : hyp.SsubFiltration A ⊆ S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.Sset) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj}) hyp.A)) :
    (Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
  obtain ⟨k, χmem, hχinj, hrange, hmemS1, hfambound⟩ :=
    Sset_degreeSqReBound_of_not_coherent hyp hodd hfrob hAH hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁
      hχ₁deg hψS hψirr hψnotS1 hψcnotS1 hnc
  have hcfinj : Function.Injective (fun j => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hB2 := Sset_sum_re_sq_induce_kernelFilter_eq hyp hfrob (A := A)
  set SA := (Finset.univ.filter
      (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
        (↑(A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
            Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))).image
      (fun θ => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction)
    with hSAdef
  have hsub : SA ⊆ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hSAdef] at hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨-, hker, hne⟩ := Finset.mem_filter.mp hθ
    apply hSA_S1
    simp only [Hypothesis.SsubFiltration, Set.mem_setOf_eq]
    exact ⟨θ, hne, hker, rfl⟩
  have hchain : (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
      ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
        A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1) ≤
      2 * (ψ 1).re * (χ₁ 1).re := by
    rw [← hB2]
    calc ∑ χ ∈ SA, ((χ 1).re) ^ 2
        ≤ ∑ χ ∈ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset, ((χ 1).re) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ = ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 :=
          OddOrder.Peterfalvi.S08.sum_toFinset_range_eq hcfinj (fun χ => (χ 1).re ^ 2)
      _ ≤ 2 * (ψ 1).re * (χ₁ 1).re := hfambound
  have hχ₁re : (χ₁ 1).re = (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) := by
    rw [hχ₁deg, Complex.natCast_re]
  rw [hχ₁re] at hchain
  have hidx_pos : (0 : ℝ) < (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have key : (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
      ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
        A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1) ≤
      (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) * (2 * (ψ 1).re) := by
    calc (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
          ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
            A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1)
        ≤ 2 * (ψ 1).re * (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) := hchain
      _ = (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) * (2 * (ψ 1).re) := by ring
  exact le_of_mul_le_mul_left key hidx_pos

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`Sset` is finite** — a subset of the (finite) range of `θ ↦ Ind_K^L θ`. -/
theorem Sset_finite [Finite G] {L : Subgroup G} (hyp : Hypothesis L) : hyp.Sset.Finite := by
  haveI := hyp.finiteG
  haveI := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L))
  have hsub : hyp.Sset ⊆ Set.range
      (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
        ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction) := by
    rintro χ ⟨θ, _, rfl⟩; exact ⟨θ, rfl⟩
  exact (Set.finite_range _).subset hsub

/-- **Every filtration level `S(A)` is finite** (subset of the finite `Sset`) — the finiteness input
of `exists_coherentBreakPair` (h56). -/
theorem SsubFiltration_finite [Finite G] {L : Subgroup G} (hyp : Hypothesis L) (A : Subgroup ↥L) :
    (hyp.SsubFiltration A).Finite :=
  (Sset_finite hyp).subset hyp.SsubFiltration_subset_Sset

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Every filtration level `S(A)` is closed under conjugation** (kernel preserved by
`characterKernel_conj`) — the conjugation-closure input of `exists_coherentBreakPair` (h56).  General
`A` version of `SsubFiltration_commutator_closedUnderConjugate`. -/
theorem SsubFiltration_closedUnderConjugate [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (A : Subgroup ↥L) : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.SsubFiltration A) := by
  classical
  intro χ hχ
  simp only [Hypothesis.SsubFiltration, Set.mem_setOf_eq] at hχ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hχ
  refine ⟨⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
    θ.isIrreducible.conj⟩, ?_, ?_, ?_⟩
  · intro h
    apply hθ_ne
    have hcoe : (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj
        = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) := by
      simpa using congrArg
        (fun c : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (c : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) h
    apply Subtype.ext
    change (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
      = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L)
    rw [← ClassFunction.conj_conj
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), hcoe]
    exact trivialClassFunction_isReal
  · rw [show ((⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
          θ.isIrreducible.conj⟩ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L)) :
          ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
        = (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj from rfl,
      OddOrder.Peterfalvi.S03.characterKernel_conj]
    exact hker
  · rw [hφeq]
    simpa using ClassFunction.induce_conj ((hyp.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Every filtration level `S(A)` has no real characters** — the no-real input of
`exists_coherentBreakPair` (h56).  Each `S(A)` member is a non-real `Sset` member. -/
theorem SsubFiltration_hasNoRealCharacters [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (A : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.SsubFiltration A) := by
  intro χ hχ
  exact Sset_hasNoRealCharacters hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hχ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`S(A)` contains a member of degree `|L:K|`** (the anchor `χ₁` of the (6.2) index bound).  When
`K/(A.subgroupOf K)` is not perfect, it has a nontrivial degree-`1` character trivial on `A`
(`exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top`); its induction
`Ind_K^L θ ∈ S(A)` has degree `|L:K|·1 = |L:K|` (`induce_apply_one`). -/
theorem exists_mem_SsubFiltration_degree_index [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {A : Subgroup ↥L} [A.Normal]
    (h : commutator (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) ≠ ⊤) :
    ∃ φ, φ ∈ hyp.SsubFiltration A ∧
      φ 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  haveI := hyp.finiteG
  haveI : (A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)).Normal := (‹A.Normal›).subgroupOf _
  obtain ⟨θ, hθne, hθker, hθdeg⟩ :=
    OddOrder.Peterfalvi.S08.exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top
      (A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) h
  refine ⟨ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction, ?_, ?_⟩
  · simp only [Hypothesis.SsubFiltration, Set.mem_setOf_eq]; exact ⟨θ, hθne, hθker, rfl⟩
  · rw [ClassFunction.induce_apply_one, hθdeg, mul_one]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (6.2) index bound = h56** (witness form, `∃θ`) — the (5.6) break-member oracle the
(6.5) engine `nonempty_coherent_SOf_bot_of_index_dvd` consumes.  If `S(A) ⊆ S(B)` (`A`-filtration
inside `B`-filtration), `K/(A.subgroupOf K)` not perfect (`hAcomm`), `S(A)` coherent and `S(B)` not,
then a break member `ψ = Ind_K^L θ ∈ S(B)` (`B ⊆ Ker θ`) satisfies `|K:A| − 1 ≤ 2·ψ(1).re`.  Combines
`exists_coherentBreakPair`, the degree-`|L:K|` anchor (`exists_mem_SsubFiltration_degree_index`), and
`Sset_index_le_two_psi`.  Mirror of the Sibley `six_two_index_bound`. -/
theorem Sset_six_two_index_bound [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {A B : Subgroup ↥L} [A.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : commutator (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) ≠ ⊤)
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A) hyp.A))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B) hyp.A)) :
    ∃ θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L),
      (↑(B.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
          Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
      (Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
        A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1 ≤
        2 * (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) 1).re := by
  obtain ⟨S₁, ψ, hS₁conj, hAS₁, hS₁B, hψB, hψnotS1, hψcnotS1, hS₁coh, hncoh⟩ :=
    OddOrder.Peterfalvi.S08.exists_coherentBreakPair hyp.tau hAB (SsubFiltration_finite hyp B)
      (SsubFiltration_closedUnderConjugate hyp B)
      (SsubFiltration_hasNoRealCharacters hyp hodd hfrob B)
      (fun φ hφ => Sset_isIrreducibleCharacter hyp hfrob (hyp.SsubFiltration_subset_Sset hφ))
      (SsubFiltration_closedUnderConjugate hyp A) hSAcoh hSBncoh
  obtain ⟨χ₁, hχ₁SA, hχ₁deg⟩ := exists_mem_SsubFiltration_degree_index hyp hAcomm
  have hψS : ψ ∈ hyp.Sset := hyp.SsubFiltration_subset_Sset hψB
  have hbound := Sset_index_le_two_psi hyp hodd hfrob hAH
    (hS₁B.trans hyp.SsubFiltration_subset_Sset) hS₁conj ((SsubFiltration_finite hyp B).subset hS₁B)
    hAS₁ hS₁coh.some (hAS₁ hχ₁SA) hχ₁deg hψS (Sset_isIrreducibleCharacter hyp hfrob hψS)
    hψnotS1 hψcnotS1 hncoh
  simp only [Hypothesis.SsubFiltration, Set.mem_setOf_eq] at hψB
  obtain ⟨θ, hθne, hθker, hψeq⟩ := hψB
  refine ⟨θ, hθker, ?_⟩
  rw [hψeq] at hbound
  exact hbound

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **`S(H′)` member differences are `A(L)`-supported** — the `hab`-free subfamily analogue of
`Sset_diff_supported` for the (6.5.c) `hcoh`.  Members of `S(⁅K,K⁆)` vanish off `H` (as `Sset`
members, `Sset_vanishes_off_H`) and share the constant degree `|L:K|` at `1`
(`SsubFiltration_commutator_apply_one_eq_index`, replacing the case-(b) `Sset_apply_one_eq_index`
that needs `H` abelian), so their difference is supported on `H^# = A(L)`. -/
theorem SsubFiltration_commutator_diff_supported [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b : ClassFunction ↥L ℂ}
    (ha : a ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hb : b ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    (a - b).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  intro x hx
  have hx0 : (a - b) x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply] at hx0
  have haS : a ∈ hyp.Sset := hyp.SsubFiltration_subset_Sset ha
  have hbS : b ∈ hyp.Sset := hyp.SsubFiltration_subset_Sset hb
  have hxH : (x : G) ∈ hyp.H := by
    by_contra h
    exact hx0 (by rw [Sset_vanishes_off_H hyp haS h, Sset_vanishes_off_H hyp hbS h, sub_zero])
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hx0 (by
      rw [SsubFiltration_commutator_apply_one_eq_index hyp ha,
          SsubFiltration_commutator_apply_one_eq_index hyp hb, sub_self])
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr
    ⟨Subgroup.mem_subgroupOf.mpr hxH, hx1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The witness Dade map is a difference-isometry on `S(H′)`** (`hab`-free), mirroring
`Sset_tau_isometry_diff` via `SsubFiltration_commutator_diff_supported`.  Standalone member-difference
fact; the `S07.Hypothesis` field is discharged in its (0099) `zSupportedSpan` form via
`dadeIntegralCharacterMap_inner_eq_of_supported`. -/
theorem SsubFiltration_commutator_tau_isometry_diff [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b c d : ClassFunction ↥L ℂ}
    (ha : a ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hb : b ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hc : c ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hd : d ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    ClassFunction.inner (hyp.tau (a - b)) (hyp.tau (c - d))
      = ClassFunction.inner (a - b) (c - d) := by
  have hS : ∀ s ∈ ({a - b, c - d} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact SsubFiltration_commutator_diff_supported hyp hAH ha hb
    · exact SsubFiltration_commutator_diff_supported hyp hAH hc hd
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hyp.hconj hS (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The witness Dade map is a difference-isometry on `S`** (issue 9001).  For members
`a, b, c, d ∈ S`, both differences are `A(L)`-supported (`Sset_diff_supported`), so the genuine §10
Dade isometry preserves their inner product (`dadeIntegralCharacterMap_inner_eq_on_supported_span`).
No global isometry is used.  Standalone member-difference fact; the `S07.Hypothesis` field is
discharged in its (0099) `zSupportedSpan` form via
`dadeIntegralCharacterMap_inner_eq_of_supported`. -/
theorem Sset_tau_isometry_diff [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b c d : ClassFunction ↥L ℂ} (ha : a ∈ hyp.Sset) (hb : b ∈ hyp.Sset)
    (hc : c ∈ hyp.Sset) (hd : d ∈ hyp.Sset) :
    ClassFunction.inner (hyp.tau (a - b)) (hyp.tau (c - d))
      = ClassFunction.inner (a - b) (c - d) := by
  have hS : ∀ s ∈ ({a - b, c - d} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Sset_diff_supported hyp hab hAH ha hb
    · exact Sset_diff_supported hyp hab hAH hc hd
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hyp.hconj hS (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness member differences map into `ℤ[Irr G]`** — the `hZIrr` input of
`coherent_of_constant_degree`.  Each member is irreducible (`Sset_isIrreducibleCharacter`), so
`a − b ∈ ℤ[Irr L]`, and it is `A(L)`-supported (`Sset_diff_supported`), so the Dade image is a
virtual character of `G` (`dadeIntegralCharacterMap_mem_ZIrr_of_supported`). -/
theorem Sset_tau_diff_mem_ZIrr [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b : ClassFunction ↥L ℂ} (ha : a ∈ hyp.Sset) (hb : b ∈ hyp.Sset) :
    hyp.tau (a - b) ∈ ZIrr G := by
  refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dadeData.dade hyp.hconj (Sset_diff_supported hyp hab hAH ha hb) ?_
  exact Submodule.sub_mem _
    (IrreducibleCharacter.mem_ZIrr ⟨a, Sset_isIrreducibleCharacter hyp hfrob ha⟩)
    (IrreducibleCharacter.mem_ZIrr ⟨b, Sset_isIrreducibleCharacter hyp hfrob hb⟩)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.2.d) difference image for a witness member** — the `difference_image` field of the
`S07.Hypothesis`.  Each `χ ∈ S` is a non-real irreducible (`Sset_isIrreducibleCharacter`,
`Sset_hasNoRealCharacters`) whose conjugate-difference `χ̄ − χ` is `A(L)`-supported
(`Sset_diff_supported`), so the genuine Dade map sends `χ − χ̄` to a signed difference of two
irreducibles of `G` (`dadeCharacterDifferenceImageOfDiff`). -/
noncomputable def Sset_differenceImage [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage hyp.tau χ :=
  OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff hyp.dadeData.dade hyp.hconj
    ⟨χ, Sset_isIrreducibleCharacter hyp hfrob hχ⟩
    (Sset_hasNoRealCharacters hyp hodd hfrob hχ)
    (Sset_diff_supported hyp hab hAH (Sset_closedUnderConjugate hyp hχ) hχ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.2.e) orthogonality of witness difference images** — the
`difference_images_orthogonal` field.  For members `φ, χ ∈ S` with `⟨φ,χ⟩ = ⟨φ,χ̄⟩ = 0`, the signed
Dade images `(φ−φ̄)^τ`, `(χ−χ̄)^τ` are orthogonal: the conjugate-differences are `A(L)`-supported, so
the Dade isometry (`Sset_tau_isometry_diff`) reduces the pairing to the source
`⟨φ−φ̄, χ−χ̄⟩`, which expands to the four cross terms — all zero by orthogonality and irreducibility
(`Sset_pairwiseOrthogonal`, `Sset_inner_self_eq_one`). -/
theorem Sset_differenceImages_orthogonal [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {φ χ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Sset) (hχ : χ ∈ hyp.Sset)
    (h1 : ClassFunction.inner φ χ = 0) (h2 : ClassFunction.inner φ χ.conj = 0) :
    (Sset_differenceImage hyp hodd hfrob hab hAH hφ).Orthogonal
      (Sset_differenceImage hyp hodd hfrob hab hAH hχ) := by
  have hφc := Sset_closedUnderConjugate hyp hφ
  have hχc := Sset_closedUnderConjugate hyp hχ
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.orthogonal_of_signedDifference_inner_eq_zero
    _ _ ?_
  rw [← (Sset_differenceImage hyp hodd hfrob hab hAH hφ).image_conjugateDifference,
      ← (Sset_differenceImage hyp hodd hfrob hab hAH hχ).image_conjugateDifference]
  change ClassFunction.inner (hyp.tau (φ - φ.conj)) (hyp.tau (χ - χ.conj)) = 0
  rw [Sset_tau_isometry_diff hyp hab hAH hφ hφc hχ hχc]
  have hne1 : φ.conj ≠ χ := by
    intro heq
    have hcc : χ.conj = φ := by rw [← heq, ClassFunction.conj_conj]
    rw [hcc, Sset_inner_self_eq_one hyp hfrob hφ] at h2
    exact one_ne_zero h2
  have hne2 : φ.conj ≠ χ.conj := by
    intro heq
    have hpc : φ = χ := by
      have h := congrArg ClassFunction.conj heq
      rwa [ClassFunction.conj_conj, ClassFunction.conj_conj] at h
    rw [hpc, Sset_inner_self_eq_one hyp hfrob hχ] at h1
    exact one_ne_zero h1
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    h1, h2, Sset_pairwiseOrthogonal hyp hodd hfrob hφc hχ hne1,
    Sset_pairwiseOrthogonal hyp hodd hfrob hφc hχc hne2]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`S(H′)` is closed under conjugation** — the `conjugate_closed` field for the subfamily
`S07.Hypothesis`.  Mirrors `Sset_closedUnderConjugate` (`χ.conj = Ind_K^L θ̄`, `θ̄ ≠ 1`), with the
extra `S(H′)`-kernel condition preserved because `Ker θ̄ = Ker θ` (`characterKernel_conj`). -/
theorem SsubFiltration_commutator_closedUnderConjugate [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    χ.conj ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆ := by
  classical
  simp only [Hypothesis.SsubFiltration, Set.mem_setOf_eq] at hχ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hχ
  refine ⟨⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
    θ.isIrreducible.conj⟩, ?_, ?_, ?_⟩
  · intro h
    apply hθ_ne
    have hcoe : (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj
        = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) := by
      simpa using congrArg
        (fun c : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (c : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) h
    apply Subtype.ext
    change (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
      = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L)
    rw [← ClassFunction.conj_conj
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), hcoe]
    exact trivialClassFunction_isReal
  · rw [show ((⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
          θ.isIrreducible.conj⟩ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L)) :
          ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
        = (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj from rfl,
      OddOrder.Peterfalvi.S03.characterKernel_conj]
    exact hker
  · rw [hφeq]
    simpa using ClassFunction.induce_conj ((hyp.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`S(H′)` member differences map into `ℤ[Irr G]`** — the `hZIrr` input for the subfamily
`coherent_of_constant_degree`.  `hab`-free mirror of `Sset_tau_diff_mem_ZIrr` via
`SsubFiltration_commutator_diff_supported`; irreducibility is inherited from `Sset`. -/
theorem SsubFiltration_commutator_tau_diff_mem_ZIrr [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b : ClassFunction ↥L ℂ}
    (ha : a ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hb : b ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    hyp.tau (a - b) ∈ ZIrr G := by
  refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dadeData.dade hyp.hconj (SsubFiltration_commutator_diff_supported hyp hAH ha hb) ?_
  exact Submodule.sub_mem _
    (IrreducibleCharacter.mem_ZIrr
      ⟨a, Sset_isIrreducibleCharacter hyp hfrob (hyp.SsubFiltration_subset_Sset ha)⟩)
    (IrreducibleCharacter.mem_ZIrr
      ⟨b, Sset_isIrreducibleCharacter hyp hfrob (hyp.SsubFiltration_subset_Sset hb)⟩)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.2.d) difference image for an `S(H′)` member** — the `difference_image` field, `hab`-free
mirror of `Sset_differenceImage` via `SsubFiltration_commutator_diff_supported` and the subfamily
conjugation-closure. -/
noncomputable def SsubFiltration_commutator_differenceImage [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage hyp.tau χ :=
  OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff hyp.dadeData.dade hyp.hconj
    ⟨χ, Sset_isIrreducibleCharacter hyp hfrob (hyp.SsubFiltration_subset_Sset hχ)⟩
    (Sset_hasNoRealCharacters hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hχ))
    (SsubFiltration_commutator_diff_supported hyp hAH
      (SsubFiltration_commutator_closedUnderConjugate hyp hχ) hχ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.2.e) orthogonality of `S(H′)` difference images** — the `difference_images_orthogonal`
field, `hab`-free mirror of `Sset_differenceImages_orthogonal`. -/
theorem SsubFiltration_commutator_differenceImages_orthogonal [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {φ χ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hχ : χ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (h1 : ClassFunction.inner φ χ = 0) (h2 : ClassFunction.inner φ χ.conj = 0) :
    (SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hφ).Orthogonal
      (SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hχ) := by
  have hφc := SsubFiltration_commutator_closedUnderConjugate hyp hφ
  have hχc := SsubFiltration_commutator_closedUnderConjugate hyp hχ
  have hφS := hyp.SsubFiltration_subset_Sset hφ
  have hχS := hyp.SsubFiltration_subset_Sset hχ
  have hφcS := hyp.SsubFiltration_subset_Sset hφc
  have hχcS := hyp.SsubFiltration_subset_Sset hχc
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.orthogonal_of_signedDifference_inner_eq_zero
    _ _ ?_
  rw [← (SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hφ).image_conjugateDifference,
      ← (SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hχ).image_conjugateDifference]
  change ClassFunction.inner (hyp.tau (φ - φ.conj)) (hyp.tau (χ - χ.conj)) = 0
  rw [SsubFiltration_commutator_tau_isometry_diff hyp hAH hφ hφc hχ hχc]
  have hne1 : φ.conj ≠ χ := by
    intro heq
    have hcc : χ.conj = φ := by rw [← heq, ClassFunction.conj_conj]
    rw [hcc, Sset_inner_self_eq_one hyp hfrob hφS] at h2
    exact one_ne_zero h2
  have hne2 : φ.conj ≠ χ.conj := by
    intro heq
    have hpc : φ = χ := by
      have h := congrArg ClassFunction.conj heq
      rwa [ClassFunction.conj_conj, ClassFunction.conj_conj] at h
    rw [hpc, Sset_inner_self_eq_one hyp hfrob hχS] at h1
    exact one_ne_zero h1
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    h1, h2, Sset_pairwiseOrthogonal hyp hodd hfrob hφcS hχS hne1,
    Sset_pairwiseOrthogonal hyp hodd hfrob hφcS hχcS hne2]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6) case (b): abelian rank-2 kernel → equal-degree coherence (5.7).**
When `H = L_F` is abelian (Def (8.3) case (b)), every `θ ∈ Irr H` is linear, so every member
`Ind_H^L θ ∈ S` has the same degree `[L:H]`; `S` is then coherent by (5.7).  The witness
`S07.Hypothesis hyp.Sset hyp.A` is assembled from the ten witness lemmas above (all seven §5.2 fields
plus the `coherent_of_constant_degree` inputs), and the coherence is produced by the now
lattice-relative `coherent_of_constant_degree` (issue 9001, no global isometry needed).  Nonemptiness
of `S` (`hcard`) comes from the nontrivial abelian kernel `H` having a nontrivial irreducible `θ`,
whose induced pair `{Ind θ, Ind θ̄}` is two distinct non-real members. -/
theorem frobenius_typeI_coherent_of_abelianKernel [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hyp : Hypothesis L)
    (hfrob' : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C)
    (hab' : IsMulCommutative ↥hyp.typeI.typeF.H ∧ rank ↥hyp.typeI.typeF.H = 2) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  classical
  obtain ⟨C, hfrob⟩ := hfrob'
  have hab := hab'.1
  have hodd : Odd (Nat.card ↥L) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  have hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1} :=
    hyp.typeIA_eq_sharp_of_frobenius hfrob
  -- `S` is finite: a subset of the (finite) range of `θ ↦ Ind_H^L θ`.
  have hSfin : hyp.Sset.Finite := by
    haveI := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L))
    have hsub : hyp.Sset ⊆ Set.range
        (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction) := by
      rintro χ ⟨θ, _, rfl⟩
      refine ⟨θ, ?_⟩
      rfl
    exact (Set.finite_range _).subset hsub
  -- the abelian kernel is nontrivial, so it has a nontrivial irreducible `θ`.
  have hHsub_ne : ((hyp.typeI.typeF.H).subgroupOf L) ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    intro hdisj
    have h := disjoint_iff.mp hdisj
    rw [inf_of_le_left hyp.typeI.typeF.H_le] at h
    exact hyp.typeI.typeF.H_nontrivial h
  haveI : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hHsub_ne
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥((hyp.typeI.typeF.H).subgroupOf L))
  haveI : Nontrivial (ConjClasses ↥((hyp.typeI.typeF.H).subgroupOf L)) :=
    ⟨ConjClasses.mk g, ConjClasses.mk 1,
      fun h => hg (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h))⟩
  haveI := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L))
  haveI : Nontrivial (IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L)) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (by rw [card_irreducibleCharacter_eq]; exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  obtain ⟨θ, hθ⟩ := exists_ne (trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))
  set χ0 := ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction with hχ0
  have hχ0S : χ0 ∈ hyp.Sset := by
    simp only [hχ0, Hypothesis.Sset, Set.mem_setOf_eq]
    refine ⟨θ, hθ, ?_⟩
    rfl
  have hχ0cS : χ0.conj ∈ hyp.Sset := Sset_closedUnderConjugate hyp hχ0S
  have hne : χ0 ≠ χ0.conj := fun h => (Sset_hasNoRealCharacters hyp hodd hfrob hχ0S) h.symm
  have hcard : 2 ≤ hyp.Sset.ncard := by
    calc 2 = ({χ0, χ0.conj} : Set (ClassFunction ↥L ℂ)).ncard := (Set.ncard_pair hne).symm
      _ ≤ hyp.Sset.ncard :=
          Set.ncard_le_ncard (by rintro x (rfl | rfl); exacts [hχ0S, hχ0cS]) hSfin
  -- assemble the §5.2 hypothesis and invoke the equal-degree coherence producer.
  refine OddOrder.Peterfalvi.S07.coherent_of_constant_degree
    { tau := hyp.tau
      tau_isometry_diff := fun _ _ hφ hψ =>
        OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
          hyp.dadeData.dade hyp.hconj hφ.2 hψ.2
      conjugate_closed := Sset_closedUnderConjugate hyp
      no_real_characters := Sset_hasNoRealCharacters hyp hodd hfrob
      pairwise_orthogonal := Sset_pairwiseOrthogonal hyp hodd hfrob
      difference_image := fun _ hχ => Sset_differenceImage hyp hodd hfrob hab hAH hχ
      difference_images_orthogonal := fun _ _ hφ hχ h1 h2 =>
        Sset_differenceImages_orthogonal hyp hodd hfrob hab hAH hφ hχ h1 h2 }
    hSfin hcard ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun ζ hζ => Sset_inner_self_eq_one hyp hfrob hζ
  · exact fun a ha b hb => Sset_tau_diff_mem_ZIrr hyp hfrob hab hAH ha hb
  · exact fun a ha b hb => by
      rw [Sset_apply_one_eq_index hyp hab ha, Sset_apply_one_eq_index hyp hab hb]
  · exact fun a ha => by
      rw [Sset_apply_one_eq_index hyp hab ha]
      exact Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  · exact OddOrder.Peterfalvi.S09.Cert.one_not_mem_supportInSubgroup_sharp hyp.typeI.typeF.H hAH
  · exact fun a ha b hb => Sset_diff_supported hyp hab hAH ha hb

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.RepresentationTheory in
/-- **`S(H′)` is coherent** — the `hcoh` input of the (6.5.c) engine
`nonempty_coherent_SOf_bot_of_index_dvd`.  `S(⁅K,K⁆)` (`K = (L_F).subgroupOf L`) is a
constant-degree family of degree `|L:K|` (`SsubFiltration_commutator_apply_one_eq_index`), coherent
by (5.7).  All seven §5.2 fields hold `hab`-free (the subfamily lemmas above); `2 ≤ |S(H′)|` because
the nontrivial abelianization `K/⁅K,K⁆` (`K` nilpotent nontrivial) has a nontrivial character whose
inflation `θ0` gives a member `Ind θ0` and its (distinct) conjugate. -/
theorem SsubFiltration_commutator_coherent [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    [Group.IsNilpotent ↥((hyp.typeI.typeF.H).subgroupOf L)] :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.SsubFiltration ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
      hyp.A) := by
  classical
  haveI := hyp.finiteG
  -- `S(H′) ⊆ Sset` is finite.
  have hSsetfin : hyp.Sset.Finite := by
    haveI := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L))
    have hsub : hyp.Sset ⊆ Set.range
        (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction) := by
      rintro χ ⟨θ, _, rfl⟩; exact ⟨θ, rfl⟩
    exact (Set.finite_range _).subset hsub
  have hSfin : (hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆).Finite :=
    hSsetfin.subset hyp.SsubFiltration_subset_Sset
  -- `K` is nontrivial.
  have hHsub_ne : ((hyp.typeI.typeF.H).subgroupOf L) ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    intro hdisj
    have h := disjoint_iff.mp hdisj
    rw [inf_of_le_left hyp.typeI.typeF.H_le] at h
    exact hyp.typeI.typeF.H_nontrivial h
  haveI : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hHsub_ne
  -- `K/⁅K,K⁆` is nontrivial (`K` nilpotent nontrivial is not perfect).
  have hcomm_lt : commutator ↥((hyp.typeI.typeF.H).subgroupOf L) < ⊤ :=
    IsSolvable.commutator_lt_top_of_nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L)
  haveI : Nontrivial (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) := by
    rw [QuotientGroup.nontrivial_iff]; exact hcomm_lt.ne
  -- a nontrivial character of the abelianization, inflated to a member `θ0` of `S(H′)`.
  haveI := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
    commutator ↥((hyp.typeI.typeF.H).subgroupOf L))
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
    commutator ↥((hyp.typeI.typeF.H).subgroupOf L))
  haveI : Nontrivial (ConjClasses (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      commutator ↥((hyp.typeI.typeF.H).subgroupOf L))) :=
    ⟨ConjClasses.mk g, ConjClasses.mk 1,
      fun h => hg (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h))⟩
  haveI : Nontrivial (IrreducibleCharacter (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      commutator ↥((hyp.typeI.typeF.H).subgroupOf L))) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (by rw [card_irreducibleCharacter_eq]
          exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  obtain ⟨χbar, hχbar⟩ := exists_ne (trivialIrreducibleCharacter
    (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸ commutator ↥((hyp.typeI.typeF.H).subgroupOf L)))
  have hθ0ne : inflate (commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) χbar
      ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) := fun h =>
    hχbar (inflate_injective (N := commutator ↥((hyp.typeI.typeF.H).subgroupOf L))
      (h.trans (inflate_trivial (N := commutator ↥((hyp.typeI.typeF.H).subgroupOf L))).symm))
  set χ0 := ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
    ((inflate (commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) χbar).toClassFunction) with hχ0def
  have hχ0S : χ0 ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆ := by
    simp only [Hypothesis.SsubFiltration, Set.mem_setOf_eq]
    refine ⟨inflate (commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) χbar, hθ0ne, ?_, rfl⟩
    rw [OddOrder.Peterfalvi.S08.commutator_subgroupOf_self]
    exact subset_characterKernel_inflate (commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) χbar
  have hχ0cS := SsubFiltration_commutator_closedUnderConjugate hyp hχ0S
  have hne : χ0 ≠ χ0.conj := fun h =>
    (Sset_hasNoRealCharacters hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hχ0S)) h.symm
  have hcard : 2 ≤ (hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆).ncard := by
    calc 2 = ({χ0, χ0.conj} : Set (ClassFunction ↥L ℂ)).ncard := (Set.ncard_pair hne).symm
      _ ≤ _ := Set.ncard_le_ncard (by rintro x (rfl | rfl); exacts [hχ0S, hχ0cS]) hSfin
  refine OddOrder.Peterfalvi.S07.coherent_of_constant_degree
    { tau := hyp.tau
      tau_isometry_diff := fun _ _ hφ hψ =>
        OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
          hyp.dadeData.dade hyp.hconj hφ.2 hψ.2
      conjugate_closed := fun _ hχ => SsubFiltration_commutator_closedUnderConjugate hyp hχ
      no_real_characters := fun _ hχ =>
        Sset_hasNoRealCharacters hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hχ)
      pairwise_orthogonal := fun _ _ hφ hχ hne =>
        Sset_pairwiseOrthogonal hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hφ)
          (hyp.SsubFiltration_subset_Sset hχ) hne
      difference_image := fun _ hχ =>
        SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hχ
      difference_images_orthogonal := fun _ _ hφ hχ h1 h2 =>
        SsubFiltration_commutator_differenceImages_orthogonal hyp hodd hfrob hAH hφ hχ h1 h2 }
    hSfin hcard ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun ζ hζ => Sset_inner_self_eq_one hyp hfrob (hyp.SsubFiltration_subset_Sset hζ)
  · exact fun a ha b hb => SsubFiltration_commutator_tau_diff_mem_ZIrr hyp hfrob hAH ha hb
  · exact fun a ha b hb => by
      rw [SsubFiltration_commutator_apply_one_eq_index hyp ha,
        SsubFiltration_commutator_apply_one_eq_index hyp hb]
  · exact fun a ha => by
      rw [SsubFiltration_commutator_apply_one_eq_index hyp ha]
      exact Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  · exact OddOrder.Peterfalvi.S09.Cert.one_not_mem_supportInSubgroup_sharp hyp.typeI.typeF.H hAH
  · exact fun a ha b hb => SsubFiltration_commutator_diff_supported hyp hAH ha hb

/-- **The witness kernel `K = (L_F).subgroupOf L` is nilpotent** — the `[IsNilpotent ↥K]` input of
`SsubFiltration_commutator_coherent` (and the (6.5) engine).  `L_F = maxNilpotentNormalHall L` is
nilpotent (`maxNilpotentNormalHall_isNilpotent`), and `K ≃* L_F` (`subgroupOfEquivOfLe`, `L_F ≤ L`)
transfers nilpotency. -/
theorem typeF_H_subgroupOf_isNilpotent [Finite G] {L : Subgroup G} (hyp : Hypothesis L) :
    Group.IsNilpotent ↥((hyp.typeI.typeF.H).subgroupOf L) := by
  haveI := hyp.finiteG
  haveI : Group.IsNilpotent ↥(hyp.typeI.typeF.H) := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.H_le).symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6) case (c): cyclic-quotient kernel → (6.5.c) coherence.** `sorry`-free.
Def (8.3) case (c): `exp(U) ∣ p − 1` for every `p ∣ |H|`; `S` is coherent by (6.5.c).

The proof feeds the abstract (6.5.c) engine `S08.nonempty_coherent_SOf_bot_of_index_dvd` on the
witness filtration `S(A) = SsubFiltration A` (`SOf`), `τ = tau`, `A0 = A`, kernel `K = (L_F).subgroupOf L`:
* **abelian branch** (`K` commutative): `⁅K,K⁆ = ⊥`, so `S(⁅K,K⁆) = S(⊥) = S` is coherent directly
  by `hcoh` (the `S(H′)` coherence `SsubFiltration_commutator_coherent`);
* **non-abelian branch**: the engine derives "`K` is a `p`-group" internally (6.5.b) from the
  Frobenius structure and the (6.3) index bound, then closes by the (6.5.c) arithmetic; its two
  genuine character-theoretic inputs are `hcoh` and the **(5.6) break-member oracle**
  `Sset_six_two_index_bound` (`h56`).
The divisibility `[L:H] ∣ p − 1` (`hdvd`) comes from `_hexp`: the odd Frobenius complement `C` is a
Z-group (`S10.isZGroup_of_isFrobeniusGroup_of_odd`), Schur–Zassenhaus makes `C ≃ U`, so `U` is a
Z-group and `[L:H] = |U| = exp(U)` (Def (8.3.c)). Closes issue 2032 / hub issue 9001. -/
theorem frobenius_typeI_coherent_of_cyclicQuotient [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hyp : Hypothesis L)
    (_hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C)
    (_hexp : (∀ p : ℕ, p.Prime → p ∈ (Nat.card ↥hyp.typeI.typeF.H).primeFactors →
        Monoid.exponent hyp.typeI.typeF.U ∣ p - 1) ∧
      ∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥hyp.typeI.typeF.H).primeFactors ∧
        IsCyclic ↥(OddOrder.GroupTheory.opiCoreInG {p}ᶜ hyp.typeI.typeF.H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  classical
  haveI := hyp.finiteG
  obtain ⟨C, hfrob⟩ := _hfrob
  have hfrobK : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((hyp.typeI.typeF.H).subgroupOf L) C := hfrob
  have hodd : Odd (Nat.card ↥L) := _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  have hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1} :=
    hyp.typeIA_eq_sharp_of_frobenius hfrobK
  haveI hKnilp : Group.IsNilpotent ↥((hyp.typeI.typeF.H).subgroupOf L) :=
    typeF_H_subgroupOf_isNilpotent hyp
  haveI hKnorm : ((hyp.typeI.typeF.H).subgroupOf L).Normal := typeF_H_subgroupOf_normal hyp
  haveI hKntriv : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L) := by
    rw [Subgroup.nontrivial_iff_ne_bot, Ne, Subgroup.subgroupOf_eq_bot]
    intro hdisj
    have h := disjoint_iff.mp hdisj
    rw [inf_of_le_left hyp.typeI.typeF.H_le] at h
    exact hyp.typeI.typeF.H_nontrivial h
  -- `⁅K,K⁆ ⊊ K` (nontrivial nilpotent kernel is not perfect).
  have hH'lt : (⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆
      : Subgroup ↥L) < (hyp.typeI.typeF.H).subgroupOf L := by
    have h1 : _root_.commutator ↥((hyp.typeI.typeF.H).subgroupOf L) < ⊤ :=
      IsSolvable.commutator_lt_top_of_nontrivial _
    rw [← OddOrder.Peterfalvi.S08.commutator_subgroupOf_self] at h1
    refine lt_of_le_of_ne (Subgroup.commutator_le_left _ _) (fun heq => ?_)
    rw [heq, Subgroup.subgroupOf_self] at h1
    exact lt_irrefl _ h1
  have hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.SsubFiltration ⁅(hyp.typeI.typeF.H).subgroupOf L,
        (hyp.typeI.typeF.H).subgroupOf L⁆) hyp.A) :=
    SsubFiltration_commutator_coherent hyp hodd hfrobK hAH
  -- `[L:H] ∣ p − 1` for every prime `p ∣ |H|`: the complement `C` is an odd Frobenius complement,
  -- hence a Z-group; by Schur–Zassenhaus `C ≃ U`, so `U` is a Z-group and
  -- `[L:H] = |U| = exp(U)` (Def (8.3.c), `_hexp`).
  have hdvd : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥((hyp.typeI.typeF.H).subgroupOf L) →
      ((hyp.typeI.typeF.H).subgroupOf L).index ∣ p - 1 := by
    have hCodd : Odd (Nat.card ↥C) := Odd.of_dvd_nat hodd C.card_subgroup_dvd_card
    haveI hZC : _root_.IsZGroup ↥C :=
      OddOrder.Peterfalvi.S10.isZGroup_of_isFrobeniusGroup_of_odd hfrobK hCodd
    have hN : Nat.Coprime (Nat.card ↥((hyp.typeI.typeF.H).subgroupOf L))
        ((hyp.typeI.typeF.H).subgroupOf L).index := by
      rw [hfrobK.isComplement.symm.index_eq_card]
      exact hfrobK.coprime_card_kernel_complement
    obtain ⟨n, -, hconj⟩ := Subgroup.IsComplement'.exists_conj_of_coprime hN
      (Or.inl inferInstance) hfrobK.isComplement hyp.typeI.typeF.complement
    have e := Subgroup.equivMapOfInjective C (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
    rw [hconj] at e
    haveI hZUsub : _root_.IsZGroup ↥((hyp.typeI.typeF.U).subgroupOf L) :=
      _root_.IsZGroup.of_injective (f := e.symm.toMonoidHom) e.symm.injective
    haveI hZU : _root_.IsZGroup ↥(hyp.typeI.typeF.U) :=
      _root_.IsZGroup.of_injective
        (f := (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.U_le).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.U_le).symm.injective
    have hidxU : ((hyp.typeI.typeF.H).subgroupOf L).index = Nat.card ↥(hyp.typeI.typeF.U) := by
      rw [hyp.typeI.typeF.complement.symm.index_eq_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.U_le).toEquiv]
    have hexpU : Monoid.exponent ↥(hyp.typeI.typeF.U) = Nat.card ↥(hyp.typeI.typeF.U) :=
      _root_.IsZGroup.exponent_eq_card (G := ↥hyp.typeI.typeF.U)
    intro p hp hpK
    have hpH : p ∣ Nat.card ↥(hyp.typeI.typeF.H) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.H_le).toEquiv] at hpK
    have hmem : p ∈ (Nat.card ↥(hyp.typeI.typeF.H)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpH, Nat.card_pos.ne'⟩
    have hdvd1 := _hexp.1 p hp hmem
    rwa [hidxU, ← hexpU]
  by_cases hnonab : ¬ ∀ a b : ↥((hyp.typeI.typeF.H).subgroupOf L), a * b = b * a
  · -- **Non-abelian branch:** the genuine (6.5.c) contradiction via the engine.
    rw [← hyp.SsubFiltration_bot]
    refine OddOrder.Peterfalvi.S08.nonempty_coherent_SOf_bot_of_index_dvd hKnorm hyp.tau hyp.A
      hyp.SsubFiltration
      hfrobK hnonab hodd hdvd hH'lt hcoh
      (fun A B _ _ hBA hAle _ hSAcoh hSBncoh =>
        Sset_six_two_index_bound hyp hodd hfrobK hAH (hyp.SsubFiltration_antitone hBA)
          ?_ hSAcoh hSBncoh)
    · -- `commutator (K / A) ≠ ⊤` from `A ≤ ⁅K,K⁆ < K` (nilpotent quotient not perfect).
      have hnle : ¬ ((hyp.typeI.typeF.H).subgroupOf L) ≤ A :=
        fun hle => lt_irrefl _ (lt_of_le_of_lt (le_trans hle hAle) hH'lt)
      have hAne : A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L) ≠ ⊤ := by
        rw [Ne, Subgroup.subgroupOf_eq_top]; exact hnle
      haveI : Nontrivial (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
          A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :=
        Subgroup.nontrivial_quotient_of_ne_top hAne
      exact (IsSolvable.commutator_lt_top_of_nontrivial _).ne
  · -- **Abelian branch:** `⁅K,K⁆ = ⊥`, so `S(⁅K,K⁆) = S(⊥) = Sset` is coherent by `hcoh`.
    push Not at hnonab
    have hcomm_bot : (⁅(hyp.typeI.typeF.H).subgroupOf L,
        (hyp.typeI.typeF.H).subgroupOf L⁆ : Subgroup ↥L) = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro p hp q hq
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
      have h := hnonab ⟨p, hp⟩ ⟨q, hq⟩
      have h3 := Subtype.ext_iff.mp h
      simpa [commute_iff_eq] using h3
    rw [← hyp.SsubFiltration_bot, ← hcomm_bot]
    exact hcoh

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6)**: if `L` is Frobenius with kernel `H = L_F`, then `S` is coherent.

The textbook proof **case-splits** on the type-I trichotomy `Definition (8.3)` (carried by
`hyp.typeI.alternative`): (a) `H^#` TI in `G` → (6.8) (`sibleyTarget_frobI`); (b) `H` abelian rank 2
→ equal-degree (5.7) (`frobenius_typeI_coherent_of_abelianKernel`); (c) `|L/H| ∣ p−1` → (6.5.c)
(`frobenius_typeI_coherent_of_cyclicQuotient`).  The (12.16) witness lands in case (b) or (c)
(Peterfalvi (12.10): its `H^#` is *not* TI), so the (6.8) route alone is insufficient — the earlier
single-`sibleyTarget_frobI` proof was unsound (issue 2032).  This assembly carries no `sorry` of its
own.  Cases (b) `frobenius_typeI_coherent_of_abelianKernel` and (c)
`frobenius_typeI_coherent_of_cyclicQuotient` are now `sorry`-free; the only residual gap is in case
(a), the sorried (6.8) target `sibleyTarget_frobI` (the (8.18.c) obligation
`nonconjugate_diffImage_inner_zero` itself is proven since the (12.3) bar-trick descent,
2026-07-03). -/
theorem frobenius_typeI_coherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hyp : Hypothesis L)
    (hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  rcases hyp.typeI.alternative with hTI | hab | hexp
  · exact CoherenceWiring.coherent_of_sibleyTarget (sibleyTarget_frobI hyp hG.odd hfrob hTI)
  · exact frobenius_typeI_coherent_of_abelianKernel hG hyp hfrob hab
  · exact frobenius_typeI_coherent_of_cyclicQuotient hG hyp hfrob hexp

/-- **Frobenius realization bridge for type `F`** (the (8.2.b) consumer behind (12.10)/(12.16)).
A type-`F` maximal `M` whose complement `U` is a **Z-group** (every Sylow subgroup cyclic) is a
Frobenius group with kernel `M_F`.  By `IsZGroup.exponent_eq_card`, `|U| = exp(U)`, so Peterfalvi
(8.2.b) (`S10.typeF_frobenius_of_card_eq_exponent`) applies.  `sorry`-free + axiom-clean. -/
theorem typeF_frobenius_of_isZGroup_complement [Finite G] {M : Subgroup G}
    (data : TypeFData M) (hZ : _root_.IsZGroup ↥data.U) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.H.subgroupOf M) (data.U.subgroupOf M) := by
  haveI := hZ
  exact OddOrder.Peterfalvi.S10.typeF_frobenius_of_card_eq_exponent data
    (_root_.IsZGroup.exponent_eq_card (G := ↥data.U)).symm

/-- **Frobenius realization bridge for type I** (the `kernel = M_F` form consumed by (12.10)).
A type-I maximal `M` whose complement `U = M/M_F` is a **Z-group** is a Frobenius group with kernel
`M_F = typeF.H`.  Wraps `typeF_frobenius_of_isZGroup_complement` on `data.typeF`. -/
theorem typeI_frobenius_of_isZGroup_complement [Finite G] {M : Subgroup G}
    (data : TypeIData M) (hZ : _root_.IsZGroup ↥data.typeF.U) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.typeF.H.subgroupOf M)
      (data.typeF.U.subgroupOf M) :=
  typeF_frobenius_of_isZGroup_complement data.typeF hZ

/-! The headline **(12.7)** (`typeI_frobenius`: every type-I maximal is a Frobenius group with
kernel `M_F`) is proved at the end of this section, after the minimal-counterexample machinery
(12.8)–(12.16) on which it depends: the `π = ∅` case is the easy direction
`typeI_frobenius_of_pi_empty`, and `π = ∅` itself (`pi_empty`) is the content of (12.16). -/

end OddOrder.Peterfalvi.S14
